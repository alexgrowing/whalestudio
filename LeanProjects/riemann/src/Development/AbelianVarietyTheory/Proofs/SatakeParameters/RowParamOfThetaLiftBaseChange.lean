import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsobaricDiscreteSelfDualStrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.RowThetaParam

section Gen

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

theorem lpSum_zero_left {w : PlE H} (a : A.LP w) : A.lpSum (A.lpZero w) a = a := by
  rw [A.lpSum_comm, A.lpSum_zero]

theorem isoLoc_cons (p : Part A.CG) (L : List (Part A.CG)) (w : PlE H) :
    isoLoc N A (p :: L) w = A.lpSum (spehLoc N A p w) (isoLoc N A L w) := rfl

theorem isoLoc_nil (w : PlE H) : isoLoc N A [] w = A.lpZero w := rfl

theorem isoLoc_append (L L' : List (Part A.CG)) (w : PlE H) :
    isoLoc N A (L ++ L') w = A.lpSum (isoLoc N A L w) (isoLoc N A L' w) := by
  induction L with
  | nil => rw [List.nil_append, isoLoc_nil, lpSum_zero_left]
  | cons p L ih => rw [List.cons_append, isoLoc_cons, isoLoc_cons, ih, A.lpSum_assoc]

theorem isoLoc_perm {L L' : List (Part A.CG)} (h : L.Perm L') (w : PlE H) :
    isoLoc N A L w = isoLoc N A L' w := by
  induction h with
  | nil => rfl
  | cons p _ ih => rw [isoLoc_cons, isoLoc_cons, ih]
  | swap p q L =>
    rw [isoLoc_cons, isoLoc_cons, isoLoc_cons, isoLoc_cons, ← A.lpSum_assoc, ← A.lpSum_assoc,
      A.lpSum_comm (spehLoc N A q w)]
  | trans _ _ ih1 ih2 => rw [ih1, ih2]

theorem lpChar_zero (hLP : SumRepresentations.At.TieLP N A)
    (hC : ∀ w (a b c : A.LP w), A.lpSum a c = A.lpSum b c → a = b) {w : PlE H} (χ : A.LP w)
    (hχ : A.lpDim χ = 1) : A.lpChar (A.lpZero w) χ = A.lpZero w := by
  have h1 := (hLP w (A.lpZero w) (A.lpZero w) χ χ 0 hχ hχ).1
  rw [A.lpSum_zero] at h1
  symm
  apply hC w _ _ (A.lpChar (A.lpZero w) χ)
  rw [lpSum_zero_left, ← h1]

theorem foldr_tw (hLP : SumRepresentations.At.TieLP N A)
    (hC : ∀ w (a b c : A.LP w), A.lpSum a c = A.lpSum b c → a = b) {a : ℕ} (π : A.CG a) (χ : A.CG 1)
    (w : PlE H) {α : Type} (c : α → ℝ) (l : List α) :
    l.foldr (fun k acc => A.lpSum (A.lpTw (A.locG (A.tw π χ) w) (c k)) acc) (A.lpZero w) =
      A.lpChar (l.foldr (fun k acc => A.lpSum (A.lpTw (A.locG π w) (c k)) acc) (A.lpZero w))
        (A.locG χ w) := by
  have hd : A.lpDim (A.locG χ w) = 1 := A.locG_dim χ w
  induction l with
  | nil => exact (lpChar_zero N A hLP hC _ hd).symm
  | cons k l ih =>
    simp only [List.foldr_cons]
    rw [ih, A.locG_tw, (hLP w _ _ _ _ (c k) hd hd).1, (hLP w (A.locG π w) (A.locG π w) _ _ (c k) hd hd).2.1]

theorem spehLoc_tw (hLP : SumRepresentations.At.TieLP N A)
    (hC : ∀ w (a b c : A.LP w), A.lpSum a c = A.lpSum b c → a = b) (p : Part A.CG) (χ : A.CG 1)
    (w : PlE H) :
    spehLoc N A ⟨p.a, A.tw p.π χ, p.d⟩ w = A.lpChar (spehLoc N A p w) (A.locG χ w) := by
  unfold spehLoc
  exact foldr_tw N A hLP hC p.π χ w (fun k => ((p.d : ℝ) - 1) / 2 - k) _

theorem isoLoc_twistIso (hLP : SumRepresentations.At.TieLP N A)
    (hC : ∀ w (a b c : A.LP w), A.lpSum a c = A.lpSum b c → a = b) (L : List (Part A.CG)) (χ : A.CG 1)
    (w : PlE H) :
    isoLoc N A (twistIso N A L χ) w = A.lpChar (isoLoc N A L w) (A.locG χ w) := by
  have hd : A.lpDim (A.locG χ w) = 1 := A.locG_dim χ w
  induction L with
  | nil => exact (lpChar_zero N A hLP hC _ hd).symm
  | cons p L ih =>
    show A.lpSum (spehLoc N A ⟨p.a, A.tw p.π χ, p.d⟩ w) (isoLoc N A (twistIso N A L χ) w) = _
    rw [ih, spehLoc_tw N A hLP hC, isoLoc_cons, (hLP w _ _ _ _ 0 hd hd).1]

theorem eta_pair (w : PlE H) :
    A.lpChar (A.locG A.etaT w) (A.locG A.etaTinv w) = A.lpUnr w {1} ∧
    A.lpChar (A.locG A.etaTinv w) (A.locG A.etaT w) = A.lpUnr w {1} := by
  have hu := A.etaT_unr w
  obtain ⟨hu', hf'⟩ := A.etaTinv_def w
  have hcard := A.frobEig_card _ hu
  rw [A.locG_dim] at hcard
  obtain ⟨b, hb⟩ := Multiset.card_eq_one.1 hcard
  have hb0 : b ≠ 0 := by
    intro h
    apply A.frobEig_ne_zero _ hu
    rw [hb, h]
    exact Multiset.mem_singleton_self 0
  rw [hb, Multiset.map_singleton] at hf'
  have d1 := A.locG_dim A.etaT w
  have d2 := A.locG_dim A.etaTinv w
  constructor
  · have hun := A.unr_char _ _ d2 hu hu'
    rw [A.unr_eq_lpUnr _ hun, A.frobEig_char _ _ b⁻¹ hu hu' d2 hf', hb, Multiset.map_singleton,
      mul_inv_cancel₀ hb0]
  · have hun := A.unr_char _ _ d1 hu' hu
    rw [A.unr_eq_lpUnr _ hun, A.frobEig_char _ _ b hu' hu d1 hb, hf', Multiset.map_singleton,
      inv_mul_cancel₀ hb0]

theorem lpChar_eta_inv (hLP : SumRepresentations.At.TieLP N A) {w : PlE H} (a : A.LP w) :
    A.lpChar (A.lpChar a (A.locG A.etaT w)) (A.locG A.etaTinv w) = a ∧
    A.lpChar (A.lpChar a (A.locG A.etaTinv w)) (A.locG A.etaT w) = a := by
  have d1 := A.locG_dim A.etaT w
  have d2 := A.locG_dim A.etaTinv w
  constructor
  · rw [(hLP w a a _ _ 0 d1 d2).2.2.2.1, (eta_pair N A w).1, (hLP w a a _ _ 0 d1 d2).2.2.2.2.1]
  · rw [(hLP w a a _ _ 0 d2 d1).2.2.2.1, (eta_pair N A w).2, (hLP w a a _ _ 0 d2 d1).2.2.2.2.1]

theorem tw_eta_inv (hLP : SumRepresentations.At.TieLP N A)
    (hC : ∀ w (a b c : A.LP w), A.lpSum a c = A.lpSum b c → a = b)
    (hAN : ∀ Pa Pa' : List (Part A.CG), (∀ p ∈ Pa, 1 ≤ p.a ∧ p.d = 1) → (∀ p ∈ Pa', 1 ≤ p.a ∧ p.d = 1) →
      (∀ᶠ w in Filter.cofinite, isoLoc N A Pa w = isoLoc N A Pa' w) → Pa.Perm Pa')
    {a : ℕ} (ha : 1 ≤ a) (π : A.CG a) : A.tw (A.tw π A.etaT) A.etaTinv = π := by
  have h := hAN [⟨a, A.tw (A.tw π A.etaT) A.etaTinv, 1⟩] [⟨a, π, 1⟩]
    (by simp [ha]) (by simp [ha]) (Filter.Eventually.of_forall fun w => by
      show isoLoc N A (twistIso N A (twistIso N A [⟨a, π, 1⟩] A.etaT) A.etaTinv) w = _
      rw [isoLoc_twistIso N A hLP hC, isoLoc_twistIso N A hLP hC, (lpChar_eta_inv N A hLP _).1])
  rw [List.singleton_perm_singleton] at h
  injection h with _ h2

theorem twistIso_eta_inv (hLP : SumRepresentations.At.TieLP N A)
    (hC : ∀ w (a b c : A.LP w), A.lpSum a c = A.lpSum b c → a = b)
    (hAN : ∀ Pa Pa' : List (Part A.CG), (∀ p ∈ Pa, 1 ≤ p.a ∧ p.d = 1) → (∀ p ∈ Pa', 1 ≤ p.a ∧ p.d = 1) →
      (∀ᶠ w in Filter.cofinite, isoLoc N A Pa w = isoLoc N A Pa' w) → Pa.Perm Pa')
    (L : List (Part A.CG)) (hL : ∀ p ∈ L, 1 ≤ p.a) :
    twistIso N A (twistIso N A L A.etaT) A.etaTinv = L := by
  induction L with
  | nil => rfl
  | cons p L ih =>
    show (⟨p.a, A.tw (A.tw p.π A.etaT) A.etaTinv, p.d⟩ : Part A.CG) :: twistIso N A (twistIso N A L A.etaT) A.etaTinv = p :: L
    rw [ih (fun q hq => hL q (List.mem_cons_of_mem _ hq)),
      tw_eta_inv N A hLP hC hAN (hL p List.mem_cons_self)]

theorem isBCV_of_perm {i : N.Loc} {P : A.AV i} {Pa Pa' : List (Part A.CG)} (h : Pa.Perm Pa')
    (hB : IsBCV N A i P Pa) : IsBCV N A i P Pa' := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hB
  refine ⟨fun p hp => h1 p (h.mem_iff.2 hp), (h.map _).nodup_iff.1 h2, ?_, fun w hw => ?_,
    fun w hw => ?_, fun τ => ?_⟩
  · unfold rankIso at h3 ⊢
    rw [← (h.map _).sum_eq]
    exact h3
  · rw [← isoLoc_perm N A h]
    exact h4 w hw
  · rw [← isoLoc_perm N A h]
    exact h5 w hw
  · rw [← h6 τ]
    unfold isoInf
    exact ((h.map _).sum_eq).symm

end Gen

theorem param_of_theta (D : D7) (h0 : SumRepresentations.tie0 D) (h3 : SumRepresentations.adm3 D) (h4 : SumRepresentations.ArchimedeanSignatureMatching D) (h5 : SumRepresentations.adm5 D)
    (i : D.nd.Loc) (σ : D.what₂.FT) (P : D.naut.AV i) (Pa : List (Part D.naut.CG))
    (hθ : thetaOf D.nd D.naut i σ P) (hB : IsBCV D.nd D.naut i P Pa)
    (hm : (⟨1, D.naut.tw (D.naut.muC i) D.naut.etaTinv, D.R.t⟩ : Part D.naut.CG) ∈ Pa) :
    ∃ Sig, HasParamW D.nd D.naut i σ Sig ∧
      IsBCV D.nd D.naut i P (twistIso D.nd D.naut (Sig ++ [muPart D.nd D.naut i]) D.naut.etaTinv) := by
  have hLP : SumRepresentations.At.TieLP D.nd D.naut := h0.1
  have hC := h4.2.2
  have hAN := h5.1
  obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem hm
  set m : Part D.naut.CG := ⟨1, D.naut.tw (D.naut.muC i) D.naut.etaTinv, D.R.t⟩ with hmdef
  set L := l₁ ++ l₂ with hLdef
  have hperm : (l₁ ++ m :: l₂).Perm (L ++ [m]) :=
    List.perm_middle.trans (List.perm_append_singleton _ _).symm
  have hLmem : ∀ p ∈ L, p ∈ l₁ ++ m :: l₂ := fun p hp => by
    rcases List.mem_append.1 hp with h | h
    · exact List.mem_append_left _ h
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)
  have hL : ∀ p ∈ L, 1 ≤ p.a ∧ 1 ≤ p.d := fun p hp =>
    ⟨(hB.1 p (hLmem p hp)).1, (hB.1 p (hLmem p hp)).2.1⟩
  have hB' := isBCV_of_perm D.nd D.naut hperm hB
  refine ⟨twistIso D.nd D.naut L D.naut.etaT, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
    exact hL q hq
  · have hr := hB'.2.2.1
    have e1 : rankIso D.nd D.naut (twistIso D.nd D.naut L D.naut.etaT) = rankIso D.nd D.naut L := by
      unfold rankIso twistIso
      rw [List.map_map]
      rfl
    rw [e1]
    unfold rankIso at hr ⊢
    rw [List.map_append, List.sum_append] at hr
    simp only [hmdef, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, one_mul, add_zero] at hr
    have : D.R.nV = D.R.r + D.R.t := rfl
    omega
  · intro w hw
    have e1 := h3 i σ P hθ w hw
    rw [← hB'.2.2.2.1 w hw, isoLoc_append, (hLP w (D.naut.locW i σ w) (spehLoc D.nd D.naut (muPart D.nd D.naut i) w)
      (D.naut.locG D.naut.etaTinv w) (D.naut.locG D.naut.etaTinv w) 0 (D.naut.locG_dim _ w) (D.naut.locG_dim _ w)).1]
      at e1
    have e2 : isoLoc D.nd D.naut [m] w =
        D.naut.lpChar (spehLoc D.nd D.naut (muPart D.nd D.naut i) w) (D.naut.locG D.naut.etaTinv w) := by
      rw [isoLoc_cons, isoLoc_nil, D.naut.lpSum_zero]
      exact spehLoc_tw D.nd D.naut hLP hC (muPart D.nd D.naut i) D.naut.etaTinv w
    rw [e2] at e1
    have e3 := hC w _ _ _ e1
    rw [isoLoc_twistIso D.nd D.naut hLP hC, e3, (lpChar_eta_inv D.nd D.naut hLP _).2]
  · have e : twistIso D.nd D.naut (twistIso D.nd D.naut L D.naut.etaT ++ [muPart D.nd D.naut i])
        D.naut.etaTinv = L ++ [m] := by
      rw [show twistIso D.nd D.naut (twistIso D.nd D.naut L D.naut.etaT ++ [muPart D.nd D.naut i])
          D.naut.etaTinv = twistIso D.nd D.naut (twistIso D.nd D.naut L D.naut.etaT) D.naut.etaTinv ++
            twistIso D.nd D.naut [muPart D.nd D.naut i] D.naut.etaTinv from List.map_append ..,
        twistIso_eta_inv D.nd D.naut hLP hC hAN L (fun p hp => (hL p hp).1)]
      rfl
    rw [e]
    exact hB'

end GlobalTheory.RowThetaParam
