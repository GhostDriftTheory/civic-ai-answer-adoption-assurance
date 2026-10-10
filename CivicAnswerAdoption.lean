import Std

/-!
# 自治体AI・回答採用アシュアランス：判定モデルの形式検証

Copyright © 2026 AI Assurance, Inc. All rights reserved.
利用条件はリポジトリの README.md「著作権・利用条件」に従います。

## 対応と検証範囲
`poc.py` の `worst`、`Engine.eligibility`、R01–R08、許可操作、
再検証時の判定保持、回答案ファイルの出力条件に対応する純粋なモデルです。
モデル内の定理は、個別テストだけでなく、型で表される全入力を対象とします。

`Input` は Python の入力検査を通過した入力から得る観測値です。
資料の版・値・ハッシュ・テンプレート文の一致などは観測の境界に置きます。
観測値の抽出、SHA-256の実装・衝突耐性、JSONの解析・正規化、ファイルI/O、
Pythonインタプリタそのものを形式証明した、という意味ではありません。

`.github/workflows/lean.yml` は既存Pythonを実行し、判定結果をコピーするのでなく
入力・資料から観測値を組み立て、Leanモデルによる8条件・7主張・判定・許可操作と
照合します。その具体的な一致命題もLeanに検査させます。
Pythonとの全入力に対する意味的同値性は、この照合試験とは別の証明課題です。
既存Python・HTMLの実行経路にLean検証器を挿入する変更は行いません。

制度・自治体・相談者は架空。PASSは職員確認用の回答案だけです。
実在制度の適合、情報源・人物・時刻の認証、自然文全般の正しさ、法的適合性、
実運用のプライバシーや、外部システムの全実行経路は本モデルの保証対象外です。

## 再検証
リポジトリ直下で `lake build`。Pythonとの照合はGitHub Actionsで実行します。
外部Leanライブラリへの依存はありません。ツールチェーンは版固定です。
-/

set_option autoImplicit false
set_option warningAsError true

namespace CivicAnswerAdoption

inductive Status where
  | PASS | HOLD | REJECT
  deriving DecidableEq, Repr

/-- cases.json の要求・資料・主張定義を結ぶ既存Pythonの固定参照値。 -/
def referenceSHA256 : String :=
  "8e185f953e419889d20347181b3827294ba47353801eb74f68193e7e02a45a14"

def employeeLimit : Nat := 20

/-- Python `worst` と同じ優先順。空リスト単体はPASS。外側は必ず8条件。 -/
def worst (xs : List Status) : Status :=
  if Status.REJECT ∈ xs then .REJECT
  else if Status.HOLD ∈ xs then .HOLD
  else .PASS

theorem worst_reject_iff (xs : List Status) :
    worst xs = .REJECT ↔ Status.REJECT ∈ xs := by
  by_cases hr : Status.REJECT ∈ xs <;>
    by_cases hh : Status.HOLD ∈ xs <;> simp [worst, hr, hh]

theorem worst_hold_iff (xs : List Status) :
    worst xs = .HOLD ↔ Status.REJECT ∉ xs ∧ Status.HOLD ∈ xs := by
  by_cases hr : Status.REJECT ∈ xs <;>
    by_cases hh : Status.HOLD ∈ xs <;> simp [worst, hr, hh]

theorem worst_pass_iff_no_blockers (xs : List Status) :
    worst xs = .PASS ↔ Status.REJECT ∉ xs ∧ Status.HOLD ∉ xs := by
  by_cases hr : Status.REJECT ∈ xs <;>
    by_cases hh : Status.HOLD ∈ xs <;> simp [worst, hr, hh]

theorem worst_pass_iff (xs : List Status) :
    worst xs = .PASS ↔ ∀ s ∈ xs, s = Status.PASS := by
  constructor
  · intro h s hs
    have hn := (worst_pass_iff_no_blockers xs).mp h
    cases s with
    | PASS => rfl
    | HOLD => exact False.elim (hn.2 hs)
    | REJECT => exact False.elim (hn.1 hs)
  · intro h
    apply (worst_pass_iff_no_blockers xs).mpr
    constructor
    · intro hm
      have bad := h Status.REJECT hm
      cases bad
    · intro hm
      have bad := h Status.HOLD hm
      cases bad

/-- 不整合のある検査集合に検査結果を追加しても、REJECTは消えない。 -/
theorem append_cannot_remove_reject (xs ys : List Status)
    (h : worst xs = .REJECT) : worst (xs ++ ys) = .REJECT := by
  apply (worst_reject_iff (xs ++ ys)).mpr
  exact List.mem_append.mpr (Or.inl ((worst_reject_iff xs).mp h))

/-- 追加した検査に保留・不採用が含まれるなら、全体をPASSにできない。 -/
theorem appended_blocker_prevents_pass (xs ys : List Status)
    (s : Status) (hm : s ∈ ys) (hb : s ≠ .PASS) :
    worst (xs ++ ys) ≠ .PASS := by
  intro h
  exact hb ((worst_pass_iff (xs ++ ys)).mp h s
    (List.mem_append.mpr (Or.inr hm)))

def checked (b : Bool) : Status := if b then .PASS else .REJECT

theorem checked_pass_iff (b : Bool) : checked b = .PASS ↔ b = true := by
  cases b <;> decide

inductive Eligibility where
  | candidate | needsReview | outOfScope
  deriving DecidableEq, Repr

structure Applicant where
  establishment : Option Bool
  employees : Option Nat
  taxArrears : Option Bool
  duplicate : Option Bool
  deriving DecidableEq, Repr

def applicantMissing (a : Applicant) : Bool :=
  a.establishment.isNone || a.employees.isNone ||
    a.taxArrears.isNone || a.duplicate.isNone

def knownFailure (a : Applicant) : Bool :=
  decide (a.establishment = some false) ||
    (match a.employees with
      | none => false
      | some n => decide (employeeLimit < n)) ||
    decide (a.taxArrears = some true) || decide (a.duplicate = some true)

/-- 対象外の既知条件が優先。未確認を対象候補に読み替えない。 -/
def eligibility (a : Applicant) : Eligibility :=
  if knownFailure a then .outOfScope
  else if applicantMissing a then .needsReview
  else .candidate

theorem known_failure_is_out_of_scope (a : Applicant)
    (h : knownFailure a = true) : eligibility a = .outOfScope := by
  simp [eligibility, h]

theorem employees_over_limit_are_out_of_scope (a : Applicant) (n : Nat)
    (he : a.employees = some n) (hn : employeeLimit < n) :
    eligibility a = .outOfScope := by
  apply known_failure_is_out_of_scope a
  simp [knownFailure, he, hn]

/-- R03では既知の対象外条件があっても、必要属性の不足が残ればHOLD。 -/
def applicantCheck (a : Applicant) (claimed : Eligibility) : Status :=
  if applicantMissing a then .HOLD
  else if eligibility a = claimed then .PASS else .REJECT

theorem applicant_pass_iff (a : Applicant) (claimed : Eligibility) :
    applicantCheck a claimed = .PASS ↔
      applicantMissing a = false ∧ eligibility a = claimed := by
  cases hm : applicantMissing a <;>
    by_cases he : eligibility a = claimed <;> simp [applicantCheck, hm, he]

/-- 選択された資料IDごとの観測。欠落資料もpresent=falseとして残す。 -/
structure SourceObservation where
  present : Bool
  catalogued : Bool
  versionMatches : Bool
  yearMatches : Bool
  startsByDate : Bool
  endsAfterDate : Bool
  contentMatches : Bool
  deriving DecidableEq, Repr

def freshness (s : SourceObservation) : Status :=
  if s.present then
    checked (s.catalogued && s.versionMatches && s.yearMatches &&
      s.startsByDate && s.endsAfterDate)
  else .HOLD

def sourceBinding (s : SourceObservation) : Status :=
  if s.present then checked s.contentMatches else .HOLD

theorem freshness_pass_iff (s : SourceObservation) :
    freshness s = .PASS ↔ s.present = true ∧ s.catalogued = true ∧
      s.versionMatches = true ∧ s.yearMatches = true ∧
      s.startsByDate = true ∧ s.endsAfterDate = true := by
  cases s with
  | mk present catalogued version year starts ends content =>
    cases present <;> cases catalogued <;> cases version <;> cases year <;>
      cases starts <;> cases ends <;> cases content <;> decide

theorem source_binding_pass_iff (s : SourceObservation) :
    sourceBinding s = .PASS ↔ s.present = true ∧ s.contentMatches = true := by
  cases s with
  | mk present catalogued version year starts ends content =>
    cases present <;> cases catalogued <;> cases version <;> cases year <;>
      cases starts <;> cases ends <;> cases content <;> decide

/-- 参照・値・内容識別値の原子的照合結果。判定そのものは含めない。 -/
structure ClaimEvidence where
  bindingPresent : Bool
  sourceAvailable : Bool
  sectionMatches : Bool
  valueMatches : Bool
  hashBindingPresent : Bool
  hashSourceAvailable : Bool
  hashMatches : Bool
  deriving DecidableEq, Repr

def traceRule (e : ClaimEvidence) (pending : Bool) : Status :=
  if e.bindingPresent then
    if e.sourceAvailable then
      if e.sectionMatches then
        if e.valueMatches then (if pending then .HOLD else .PASS)
        else .REJECT
      else .REJECT
    else .HOLD
  else .HOLD

theorem trace_pass_iff (e : ClaimEvidence) (pending : Bool) :
    traceRule e pending = .PASS ↔
      e.bindingPresent = true ∧ e.sourceAvailable = true ∧
      e.sectionMatches = true ∧ e.valueMatches = true ∧ pending = false := by
  cases e with
  | mk bound available sectionOK value hashBound hashAvailable hashMatches =>
    cases bound <;> cases available <;> cases sectionOK <;> cases value <;>
      cases hashBound <;> cases hashAvailable <;> cases hashMatches <;>
      cases pending <;> decide

def claimBinding (e : ClaimEvidence) : Status :=
  if e.hashBindingPresent then
    if e.hashSourceAvailable then checked e.hashMatches else .HOLD
  else .HOLD

theorem claim_binding_pass_iff (e : ClaimEvidence) :
    claimBinding e = .PASS ↔ e.hashBindingPresent = true ∧
      e.hashSourceAvailable = true ∧ e.hashMatches = true := by
  cases e with
  | mk bound available sectionOK value hashBound hashAvailable hashMatches =>
    cases bound <;> cases available <;> cases sectionOK <;> cases value <;>
      cases hashBound <;> cases hashAvailable <;> cases hashMatches <;> decide

/-- 固定7主張。空の主張集合を「全部通過」と扱う構成にしない。 -/
structure Claims where
  municipality : ClaimEvidence
  maxYen : ClaimEvidence
  rate : ClaimEvidence
  deadline : ClaimEvidence
  eligibility : ClaimEvidence
  conditions : ClaimEvidence
  awardGuarantee : ClaimEvidence
  deriving DecidableEq, Repr

def Claims.toList (c : Claims) : List ClaimEvidence :=
  [c.municipality, c.maxYen, c.rate, c.deadline,
    c.eligibility, c.conditions, c.awardGuarantee]

structure DataSettings where
  synthetic : Bool
  classificationAllowed : Bool
  templateOnly : Bool
  networkDisabled : Bool
  sourcesAllowed : Bool
  deriving DecidableEq, Repr

def dataCheck (d : DataSettings) : Status :=
  checked (d.synthetic && d.classificationAllowed && d.templateOnly &&
    d.networkDisabled && d.sourcesAllowed)

theorem data_pass_iff (d : DataSettings) :
    dataCheck d = .PASS ↔ d.synthetic = true ∧ d.classificationAllowed = true ∧
      d.templateOnly = true ∧ d.networkDisabled = true ∧ d.sourcesAllowed = true := by
  cases d with
  | mk synthetic classification template network sources =>
    cases synthetic <;> cases classification <;> cases template <;>
      cases network <;> cases sources <;> decide

structure Workflow where
  staffDraftOnly : Bool
  humanConfirmation : Bool
  externalSend : Bool
  automaticAward : Bool
  deriving DecidableEq, Repr

def workflowCheck (w : Workflow) : Status :=
  checked (w.staffDraftOnly && w.humanConfirmation &&
    !w.externalSend && !w.automaticAward)

theorem workflow_pass_iff (w : Workflow) :
    workflowCheck w = .PASS ↔
      w.staffDraftOnly = true ∧ w.humanConfirmation = true ∧
      w.externalSend = false ∧ w.automaticAward = false := by
  cases w with
  | mk draft human external automatic =>
    cases draft <;> cases human <;> cases external <;> cases automatic <;> decide

def mandatoryCheck (present award : Bool) : Status := checked (present && !award)

theorem mandatory_pass_iff (present award : Bool) :
    mandatoryCheck present award = .PASS ↔ present = true ∧ award = false := by
  cases present <;> cases award <;> decide

structure Input where
  targetMatches : Bool
  selectedSourceTargetsMatch : Bool
  selectedSources : List SourceObservation
  primarySourceSelected : Bool
  applicant : Applicant
  claimedEligibility : Eligibility
  claims : Claims
  mandatoryConditionsPresent : Bool
  awardGuarantee : Bool
  dataSettings : DataSettings
  workflow : Workflow
  textMatches : Bool
  deriving DecidableEq, Repr

/-- eligibility主張の期待値と未確認性は、Pythonの判定でなく本モデルで計算。 -/
def normalizedClaims (x : Input) : List (ClaimEvidence × Bool) :=
  let e := { x.claims.eligibility with
    valueMatches := decide (eligibility x.applicant = x.claimedEligibility) }
  [(x.claims.municipality, false), (x.claims.maxYen, false),
    (x.claims.rate, false), (x.claims.deadline, false),
    (e, decide (eligibility x.applicant = .needsReview)),
    (x.claims.conditions, false), (x.claims.awardGuarantee, false)]

def claimResults (x : Input) : List Status :=
  (normalizedClaims x).map (fun p => traceRule p.1 p.2)

def freshnessCheck (x : Input) : Status :=
  worst (x.selectedSources.map freshness ++
    (if x.primarySourceSelected then [] else [.HOLD]))

def integrityCheck (x : Input) : Status :=
  worst (x.selectedSources.map sourceBinding ++
    (x.claims.toList.map claimBinding ++
    (if x.textMatches then [] else [.REJECT])))

/-- 順序は既存の R01, R02, ..., R08 と一致。 -/
def checks (x : Input) : List Status :=
  [checked (x.targetMatches && x.selectedSourceTargetsMatch),
    freshnessCheck x,
    applicantCheck x.applicant x.claimedEligibility,
    worst (claimResults x),
    mandatoryCheck x.mandatoryConditionsPresent x.awardGuarantee,
    dataCheck x.dataSettings,
    workflowCheck x.workflow,
    integrityCheck x]

def decision (x : Input) : Status := worst (checks x)

theorem exactly_eight_checks (x : Input) : (checks x).length = 8 := by rfl

theorem exactly_seven_claims (x : Input) : (normalizedClaims x).length = 7 := by rfl

/-- 中核：PASSの必要十分条件は、固定8条件の全通過。 -/
theorem adoption_iff_all_checks_pass (x : Input) :
    decision x = .PASS ↔ ∀ s ∈ checks x, s = Status.PASS :=
  worst_pass_iff (checks x)

theorem pass_requires_check (x : Input) (s : Status)
    (h : decision x = .PASS) (hm : s ∈ checks x) : s = .PASS :=
  (adoption_iff_all_checks_pass x).mp h s hm

theorem reject_overrides_hold (x : Input) (h : Status.REJECT ∈ checks x) :
    decision x = .REJECT := (worst_reject_iff (checks x)).mpr h

theorem pass_requires_applicant (x : Input) (h : decision x = .PASS) :
    applicantMissing x.applicant = false ∧
      eligibility x.applicant = x.claimedEligibility := by
  apply (applicant_pass_iff x.applicant x.claimedEligibility).mp
  exact pass_requires_check x _ h (by simp [checks])

/-- データ区分等の申告条件の充足。実データの個人情報検出を意味しない。 -/
theorem pass_requires_data_settings (x : Input) (h : decision x = .PASS) :
    x.dataSettings.synthetic = true ∧ x.dataSettings.classificationAllowed = true ∧
      x.dataSettings.templateOnly = true ∧ x.dataSettings.networkDisabled = true ∧
      x.dataSettings.sourcesAllowed = true := by
  apply (data_pass_iff x.dataSettings).mp
  exact pass_requires_check x _ h (by simp [checks])

/-- 選択した全資料について、存在・採用対象版・年度・期間の充足が必要。 -/
theorem pass_requires_current_source (x : Input) (h : decision x = .PASS)
    (s : SourceObservation) (hm : s ∈ x.selectedSources) :
    s.present = true ∧ s.catalogued = true ∧ s.versionMatches = true ∧
      s.yearMatches = true ∧ s.startsByDate = true ∧ s.endsAfterDate = true := by
  have hc : freshnessCheck x = .PASS := pass_requires_check x _ h (by simp [checks])
  apply (freshness_pass_iff s).mp
  apply (worst_pass_iff _).mp hc (freshness s)
  exact List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨s, hm, rfl⟩))

/-- 内容識別値による固定資料との一致が必要。発行者の認証とは別。 -/
theorem pass_requires_source_binding (x : Input) (h : decision x = .PASS)
    (s : SourceObservation) (hm : s ∈ x.selectedSources) :
    s.present = true ∧ s.contentMatches = true := by
  have hc : integrityCheck x = .PASS := pass_requires_check x _ h (by simp [checks])
  apply (source_binding_pass_iff s).mp
  apply (worst_pass_iff _).mp hc (sourceBinding s)
  exact List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨s, hm, rfl⟩))

theorem pass_requires_claim_hash_binding (x : Input) (h : decision x = .PASS)
    (e : ClaimEvidence) (hm : e ∈ x.claims.toList) :
    e.hashBindingPresent = true ∧ e.hashSourceAvailable = true ∧ e.hashMatches = true := by
  have hc : integrityCheck x = .PASS := pass_requires_check x _ h (by simp [checks])
  apply (claim_binding_pass_iff e).mp
  apply (worst_pass_iff _).mp hc (claimBinding e)
  exact List.mem_append.mpr (Or.inr (List.mem_append.mpr
    (Or.inl (List.mem_map.mpr ⟨e, hm, rfl⟩))))

theorem pass_requires_workflow (x : Input) (h : decision x = .PASS) :
    x.workflow.staffDraftOnly = true ∧ x.workflow.humanConfirmation = true ∧
      x.workflow.externalSend = false ∧ x.workflow.automaticAward = false := by
  apply (workflow_pass_iff x.workflow).mp
  exact pass_requires_check x _ h (by simp [checks])

theorem pass_requires_mandatory_conditions (x : Input) (h : decision x = .PASS) :
    x.mandatoryConditionsPresent = true ∧ x.awardGuarantee = false := by
  apply (mandatory_pass_iff x.mandatoryConditionsPresent x.awardGuarantee).mp
  exact pass_requires_check x _ h (by simp [checks])

theorem pass_requires_all_claim_results (x : Input) (h : decision x = .PASS) :
    ∀ s ∈ claimResults x, s = Status.PASS := by
  apply (worst_pass_iff (claimResults x)).mp
  exact pass_requires_check x _ h (by simp [checks])

/-- 各主張について、根拠の存在・参照箇所・値一致・未確認なしが必要。 -/
theorem pass_requires_each_claim (x : Input) (h : decision x = .PASS)
    (e : ClaimEvidence) (pending : Bool) (hm : (e, pending) ∈ normalizedClaims x) :
    e.bindingPresent = true ∧ e.sourceAvailable = true ∧
      e.sectionMatches = true ∧ e.valueMatches = true ∧ pending = false := by
  apply (trace_pass_iff e pending).mp
  apply pass_requires_all_claim_results x h (traceRule e pending)
  exact List.mem_map.mpr ⟨(e, pending), hm, rfl⟩

theorem missing_binding_blocks_adoption (x : Input) (e : ClaimEvidence)
    (pending : Bool) (hm : (e, pending) ∈ normalizedClaims x)
    (hb : e.bindingPresent = false) : decision x ≠ .PASS := by
  intro h
  have good := (pass_requires_each_claim x h e pending hm).1
  simp [hb] at good

theorem missing_applicant_blocks_adoption (x : Input)
    (hm : applicantMissing x.applicant = true) : decision x ≠ .PASS := by
  intro h
  have good := (pass_requires_applicant x h).1
  simp [hm] at good

theorem forbidden_workflow_rejects (x : Input)
    (hw : workflowCheck x.workflow = .REJECT) : decision x = .REJECT := by
  apply reject_overrides_hold x
  simp [checks, hw]

/-- 表示文と構造化主張の不一致は、他の条件にかかわらずREJECT。 -/
theorem text_mismatch_rejects (x : Input) (ht : x.textMatches = false) :
    decision x = .REJECT := by
  have hi : integrityCheck x = .REJECT := by
    apply (worst_reject_iff _).mpr
    simp [ht]
  apply reject_overrides_hold x
  simp [checks, hi]

inductive Action where
  | none | staffReview | externalSend | administrativeAward
  deriving DecidableEq, Repr

def permittedAction (s : Status) : Action :=
  if s = .PASS then .staffReview else .none

theorem action_never_external_send (s : Status) :
    permittedAction s ≠ .externalSend := by cases s <;> decide

theorem action_never_administrative_award (s : Status) :
    permittedAction s ≠ .administrativeAward := by cases s <;> decide

theorem staff_review_iff_pass (s : Status) :
    permittedAction s = .staffReview ↔ s = .PASS := by cases s <;> decide

/-- 再検証記録の論理部分。暗号・原文・メタデータ・詳細な根拠記述の照合は境界の観測値。 -/
structure RecordView where
  integrityOK : Bool
  policyOK : Bool
  metadataOK : Bool
  evidenceDetailsOK : Bool
  recordedDecision : Status
  recordedChecks : List Status
  recordedAction : Action
  recordedUnresolved : List Status
  deriving DecidableEq, Repr

def unresolved (x : Input) : List Status :=
  (checks x).filter (fun s => decide (s ≠ Status.PASS))

def reverify (x : Input) (r : RecordView) : Bool :=
  decide (r.integrityOK = true ∧ r.policyOK = true ∧ r.metadataOK = true ∧
    r.evidenceDetailsOK = true ∧ r.recordedDecision = decision x ∧ r.recordedChecks = checks x ∧
    r.recordedAction = permittedAction (decision x) ∧
    r.recordedUnresolved = unresolved x)

theorem reverify_preserves_decision (x : Input) (r : RecordView)
    (h : reverify x r = true) : r.recordedDecision = decision x :=
  (of_decide_eq_true h).2.2.2.2.1

theorem reverify_preserves_checks (x : Input) (r : RecordView)
    (h : reverify x r = true) : r.recordedChecks = checks x :=
  (of_decide_eq_true h).2.2.2.2.2.1

theorem reverify_preserves_action (x : Input) (r : RecordView)
    (h : reverify x r = true) : r.recordedAction = permittedAction (decision x) :=
  (of_decide_eq_true h).2.2.2.2.2.2.1

theorem changed_decision_fails_reverification (x : Input) (r : RecordView)
    (hn : r.recordedDecision ≠ decision x) : reverify x r = false := by
  cases hv : reverify x r with
  | false => rfl
  | true => exact False.elim (hn (reverify_preserves_decision x r hv))

/-- 4つの境界照合が成立した、整合的な抽象記録。署名等を生成する関数ではない。 -/
def consistentRecord (x : Input) : RecordView :=
  { integrityOK := true, policyOK := true, metadataOK := true, evidenceDetailsOK := true,
    recordedDecision := decision x, recordedChecks := checks x,
    recordedAction := permittedAction (decision x), recordedUnresolved := unresolved x }

theorem consistent_record_reverifies (x : Input) :
    reverify x (consistentRecord x) = true := by simp [reverify, consistentRecord]

/-- Python save_record の「PASSかつメモリ上・保存後の双方で再検証成立」に対応。 -/
def draftAllowed (s : Status) (memoryReplay diskReplay : Bool) : Bool :=
  decide (s = .PASS) && memoryReplay && diskReplay

theorem draft_allowed_iff (s : Status) (memoryReplay diskReplay : Bool) :
    draftAllowed s memoryReplay diskReplay = true ↔
      s = .PASS ∧ memoryReplay = true ∧ diskReplay = true := by
  cases s <;> cases memoryReplay <;> cases diskReplay <;> decide

/-- 再検証成立はHOLD/REJECTをPASSに変えず、回答案の出力許可にもならない。 -/
theorem reverification_does_not_upgrade (x : Input) (h : decision x ≠ .PASS) :
    reverify x (consistentRecord x) = true ∧
      draftAllowed (decision x) true true = false := by
  constructor
  · exact consistent_record_reverifies x
  · simp [draftAllowed, h]

end CivicAnswerAdoption
