import Formalism.PieriBlockIdeals.StatementLR
import Formalism.PieriBlockIdeals.PieriColumnMinors.DividedPowerZeroZeroVector

open MvPolynomial

noncomputable section

namespace Formalism.CohomologicalDescent.LR

open Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.Symmetrization Formalism.CohomologicalDescent.BinaryFormsExample

theorem formB_apply (p q w : ℕ) (lam2 : Fin q → ℕ) (x y : VQ p q w lam2) :
    formB p q w lam2 x y = fockQ (x : MvPolynomial (Fin (p + q) × Fin (p + q)) ℚ) y /
      fockQ (hw ℚ le_rfl (LD.blockWt p q w lam2)) (hw ℚ le_rfl (LD.blockWt p q w lam2)) := rfl

theorem hw_norm_pos {r : ℕ} (ν : Fin r → ℕ) : 0 < fockQ (hw ℚ le_rfl ν) (hw ℚ le_rfl ν) :=
  (fockQPos _ (hw ℚ le_rfl ν) (hw ℚ le_rfl ν)).2 (hwNe ℚ r r le_rfl ν)

theorem real_contragredient : RealContra := by
  intro p q w lam2 a b x y
  show formB p q w lam2 (EV p q w lam2 a b x) y = formB p q w lam2 x (EV p q w lam2 b a y)
  rw [formB_apply, formB_apply, EV_coe, EV_coe, fock_der]

theorem real_nondegenerate : RealNondeg := by
  intro p q w lam2 v hv
  have h := hv v
  rw [formB_apply, div_eq_zero_iff] at h
  rcases h with h | h
  · by_contra hne
    have hne' : (v : MvPolynomial (Fin (p + q) × Fin (p + q)) ℚ) ≠ 0 := fun h0 => hne (Subtype.ext h0)
    exact absurd h (ne_of_gt ((fockQPos _ (v : MvPolynomial (Fin (p + q) × Fin (p + q)) ℚ) v).2 hne'))
  · exact absurd h (ne_of_gt (hw_norm_pos _))

theorem idx_surj (p q : ℕ) : Function.Surjective (idx p q) := finSumFinEquiv.surjective

theorem coeff_der_diag {r n : ℕ} (a : Fin r) (f : MvPolynomial (Fin r × Fin n) ℚ) (m : Fin r × Fin n →₀ ℕ) :
    coeff m (der r n a a f) = ((Finsupp.weight (rowW r n) m a : ℕ) : ℚ) * coeff m f := by
  rw [← rowDiv_one, lgraded_coeff_euler, lgraded_weight_rowW]

theorem der_diag_iff {r n : ℕ} (f : MvPolynomial (Fin r × Fin n) ℚ) (μ : Fin r → ℕ) :
    IsWeightedHomogeneous (rowW r n) f μ ↔ ∀ a, der r n a a f = (μ a : ℚ) • f := by
  constructor
  · intro h a
    ext m
    rw [coeff_der_diag, coeff_smul, smul_eq_mul]
    by_cases hm : coeff m f = 0
    · rw [hm, mul_zero, mul_zero]
    · rw [h hm]
  · intro h m hm
    funext a
    have h1 := congrArg (coeff m) (h a)
    rw [coeff_der_diag, coeff_smul, smul_eq_mul] at h1
    exact_mod_cast mul_right_cancel₀ hm h1

theorem mem_wt (p q w : ℕ) (lam2 : Fin q → ℕ) (v : VQ p q w lam2) (κ : Fin p ⊕ Fin q → ℤ) :
    v ∈ (rationalBlockModuleSetting p q w lam2).wt κ ↔ ∀ a, EV p q w lam2 a a v = (κ a : ℚ) • v := by
  simp only [HidaSetting.wt, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.one_apply, sub_eq_zero]
  rfl

theorem real_weight : RealWeight := by
  intro p q w lam2 v μ
  rw [mem_wt, der_diag_iff]
  constructor
  · intro h a
    apply Subtype.ext
    rw [EV_coe, h]
    simp
  · intro h a
    obtain ⟨a', rfl⟩ := idx_surj p q a
    have h1 := congrArg Subtype.val (h a')
    rw [EV_coe] at h1
    rw [h1]
    simp

theorem rowNu_self {r : ℕ} (ν : Fin r → ℕ) : rowNu (r := r) ν = ν := by
  funext a
  simp [rowNu, a.isLt]

theorem hw_rowHom {r : ℕ} (ν : Fin r → ℕ) (hν : Antitone ν) :
    IsWeightedHomogeneous (rowW r r) (hw ℚ le_rfl ν) ν := by
  have h := hwRowWeight ℚ r r le_rfl ν hν
  rwa [rowNu_self] at h

theorem der_hw_raise {r : ℕ} (ν : Fin r → ℕ) (a b : Fin r) (hab : a < b) : der r r a b (hw ℚ le_rfl ν) = 0 := by
  rw [← rowDiv_one]
  exact hwRaise ℚ r r le_rfl ν a b 1 hab le_rfl

theorem der_hw_lower {r : ℕ} (ν : Fin r → ℕ) (hν : Antitone ν) (a b : Fin r) (hab : a < b) (he : ν a = ν b) :
    der r r b a (hw ℚ le_rfl ν) = 0 := by
  by_contra hne
  have hpos := (fockQPos _ (der r r b a (hw ℚ le_rfl ν)) (der r r b a (hw ℚ le_rfl ν))).2 hne
  have hc := der_comm (n := r) a b b a (hw ℚ le_rfl ν)
  simp only [if_true, der_hw_raise ν a b hab, map_zero, sub_zero] at hc
  have hd := (der_diag_iff _ _).1 (hw_rowHom ν hν)
  rw [fock_der, hc, hd a, hd b, he, sub_self] at hpos
  have h0 : fockQ (hw ℚ le_rfl ν) (0 : MvPolynomial (Fin r × Fin r) ℚ) = 0 := by
    have := fock_smul_right (0 : ℚ) (hw ℚ le_rfl ν) (0 : MvPolynomial (Fin r × Fin r) ℚ)
    simpa using this
  rw [h0] at hpos
  exact lt_irrefl _ hpos

def hwV (p q w : ℕ) (lam2 : Fin q → ℕ) (ha : Antitone lam2) (hb : ∀ b, lam2 b ≤ w) : VQ p q w lam2 :=
  ⟨hw ℚ le_rfl (LD.blockWt p q w lam2), hwMem ℚ _ _ le_rfl _ (LD.ld_blockWt_anti p q w lam2 ha hb)⟩

theorem hwV_mem (p q w : ℕ) (lam2 : Fin q → ℕ) (ha : Antitone lam2) (hb : ∀ b, lam2 b ≤ w) :
    hwV p q w lam2 ha hb ∈ W0 p q w lam2 := by
  have hanti := LD.ld_blockWt_anti p q w lam2 ha hb
  rw [mem_orthogonal_frame_iff]
  refine ⟨fun α a => Subtype.ext ?_, fun α β => Subtype.ext ?_⟩
  · rw [EV_coe]
    refine der_hw_raise _ _ _ ?_
    show (Fin.castAdd q α) < (Fin.natAdd p a)
    rw [Fin.lt_def]
    simp only [Fin.val_castAdd, Fin.val_natAdd]
    omega
  · rw [EV_coe]
    have hval : ∀ γ : Fin p, LD.blockWt p q w lam2 (Fin.castAdd q γ) = w := fun γ => Fin.append_left _ _ γ
    show der _ _ (Fin.castAdd q α) (Fin.castAdd q β) (hw ℚ le_rfl (LD.blockWt p q w lam2)) = _
    rcases lt_trichotomy α β with h | h | h
    · rw [if_neg (ne_of_lt h)]
      exact der_hw_raise _ _ _ (by rw [Fin.lt_def] at h ⊢; simpa using h)
    · subst h
      rw [if_pos rfl, (der_diag_iff _ _).1 (hw_rowHom _ hanti), hval]
      rfl
    · rw [if_neg (ne_of_gt h)]
      exact der_hw_lower _ hanti _ _ (by rw [Fin.lt_def] at h ⊢; simpa using h) (by rw [hval, hval])

theorem closed_of_stable (p q w : ℕ) (lam2 : Fin q → ℕ) (U : Submodule ℚ (VQ p q w lam2))
    (hU : ∀ a b, ∀ x ∈ U, EV p q w lam2 a b x ∈ U) :
    RowDivClosed (U.map (dualWeyl ℚ (p + q) (p + q) (LD.blockWt p q w lam2)).subtype) := by
  intro a b k
  refine closed_of_der a b _ ?_ k
  obtain ⟨a', rfl⟩ := idx_surj p q a
  obtain ⟨b', rfl⟩ := idx_surj p q b
  rintro f ⟨x, hx, rfl⟩
  exact ⟨EV p q w lam2 a' b' x, hU a' b' x hx, rfl⟩

theorem top_of_stable (p q w : ℕ) (lam2 : Fin q → ℕ) (ha : Antitone lam2) (hb : ∀ b, lam2 b ≤ w)
    (U : Submodule ℚ (VQ p q w lam2)) (hU : ∀ a b, ∀ x ∈ U, EV p q w lam2 a b x ∈ U) (hne : U ≠ ⊥) : U = ⊤ := by
  have hanti := LD.ld_blockWt_anti p q w lam2 ha hb
  have hcl := closed_of_stable p q w lam2 U hU
  have hle : U.map (dualWeyl ℚ (p + q) (p + q) (LD.blockWt p q w lam2)).subtype ≤
      dualWeyl ℚ (p + q) (p + q) (LD.blockWt p q w lam2) := by
    rintro f ⟨x, _, rfl⟩
    exact x.2
  have hne' : U.map (dualWeyl ℚ (p + q) (p + q) (LD.blockWt p q w lam2)).subtype ≠ ⊥ := by
    intro h0
    apply hne
    rw [eq_bot_iff]
    intro x hx
    have hx' : (x : MvPolynomial (Fin (p + q) × Fin (p + q)) ℚ) ∈
        U.map (dualWeyl ℚ (p + q) (p + q) (LD.blockWt p q w lam2)).subtype := ⟨x, hx, rfl⟩
    rw [h0, Submodule.mem_bot] at hx'
    rw [Submodule.mem_bot]
    exact Subtype.ext hx'
  have hhw := hwInClosed _ _ le_rfl _ hanti _ hle hcl hne'
  have heq := closedEqNabla _ _ le_rfl _ hanti _ hle hcl hhw
  rw [eq_top_iff]
  intro x _
  have hx : (x : MvPolynomial (Fin (p + q) × Fin (p + q)) ℚ) ∈
      U.map (dualWeyl ℚ (p + q) (p + q) (LD.blockWt p q w lam2)).subtype := by
    rw [heq]; exact x.2
  obtain ⟨y, hy, hyx⟩ := hx
  have : y = x := Subtype.ext hyx
  rwa [← this]

theorem hwV_ne (p q w : ℕ) (lam2 : Fin q → ℕ) (ha : Antitone lam2) (hb : ∀ b, lam2 b ≤ w) :
    hwV p q w lam2 ha hb ≠ 0 := fun h => hwNe ℚ _ _ le_rfl _ (congrArg Subtype.val h)

theorem real_generated : RealGenerated := by
  intro p q w lam2 ha hb U hW hU
  refine top_of_stable p q w lam2 ha hb U hU ?_
  intro h0
  have h1 : hwV p q w lam2 ha hb ∈ U := hW (hwV_mem p q w lam2 ha hb)
  rw [h0, Submodule.mem_bot] at h1
  exact hwV_ne p q w lam2 ha hb h1

theorem real_irreducible : RealIrred := by
  intro p q w lam2 ha hb Z hZ hst hne h hh
  have hanti := LD.ld_blockWt_anti p q w lam2 ha hb
  let SZ : HidaSetting ℚ (VQ p q w lam2) (Fin p) (Fin q) :=
    { E := EV p q w lam2
      comm := EV_comm p q w lam2
      W := Z
      w := (w : ℚ)
      kill := fun α a u hu => ((mem_orthogonal_frame_iff p q w lam2 u).1 (hZ hu)).1 α a
      scal := fun α β u hu => ((mem_orthogonal_frame_iff p q w lam2 u).1 (hZ hu)).2 α β
      stab := hst }
  have hgen : Generated SZ := by
    intro U hW hU
    refine top_of_stable p q w lam2 ha hb U hU ?_
    intro h0
    apply hne
    rw [eq_bot_iff, ← h0]
    exact hW
  have hwt : h ∈ SZ.wt fun a => (LD.blockWt p q w lam2 (idx p q a) : ℤ) := by
    have := (real_weight p q w lam2 h (LD.blockWt p q w lam2)).1 (by rw [hh]; exact hw_rowHom _ hanti)
    exact this
  have hsum : ∑ α : Fin p, ((LD.blockWt p q w lam2 (idx p q (Sum.inl α)) : ℕ) : ℤ) + ((0 : ℕ) : ℤ) =
      (Fintype.card (Fin p) : ℤ) * (w : ℤ) := by
    have hval : ∀ γ : Fin p, LD.blockWt p q w lam2 (idx p q (Sum.inl γ)) = w := fun γ => Fin.append_left _ _ γ
    simp [hval]
  have h1 := depth_of_weight_holds ℚ (VQ p q w lam2) (Fin p) (Fin q) SZ w 0 rfl hgen _ h hwt hsum
  rw [(depth_span_holds ℚ (VQ p q w lam2) (Fin p) (Fin q) SZ).1] at h1
  exact h1

end Formalism.CohomologicalDescent.LR
