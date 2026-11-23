import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.VacConj
variable {D : D7}
theorem inv_neg' {n : ℕ} (A : Matrix (Fin n) (Fin n) D.host.E) : (-A)⁻¹ = -A⁻¹ := by
  by_cases h : IsUnit A.det
  · exact Matrix.inv_eq_left_inv (by rw [neg_mul_neg, Matrix.nonsing_inv_mul A h])
  · have h' : ¬ IsUnit (-A).det := by
      rw [Matrix.det_neg]
      intro hu
      exact h (isUnit_of_mul_isUnit_right hu)
    rw [Matrix.nonsing_inv_apply_not_isUnit _ h, Matrix.nonsing_inv_apply_not_isUnit _ h', neg_zero]

theorem star_char' {R : Type} [CommRing R] (ψ : AddChar R ℂ) (h : ∀ x, ‖ψ x‖ = 1) (x : R) :
    star (ψ (-x)) = ψ x := by
  have h1 : ψ (-x) * ψ x = 1 := by rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
  have h2 : star (ψ (-x)) * ψ (-x) = 1 := by
    rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, h]; simp
  calc star (ψ (-x)) = star (ψ (-x)) * (ψ (-x) * ψ x) := by rw [h1, mul_one]
    _ = ψ x := by rw [← mul_assoc, h2, one_mul]

theorem hO_neg (S T : HSp D) (x y : WO S T) : hO (negSp S) T x y = -hO S T x y := by
  unfold hO
  rw [negSp_gram, inv_neg']
  simp only [Matrix.neg_apply, map_neg, neg_mul, Finset.sum_neg_distrib]

theorem symplOH_neg (S T : HSp D) (x y : WO S T) : symplOH (negSp S) T x y = -symplOH S T x y := by
  unfold symplOH symplO
  rw [hO_neg, mul_neg, map_neg, mul_neg]

theorem heisO_conj (ψ : AddChar (AF D.host.F) ℂ) (hψ : ∀ x, ‖ψ x‖ = 1) (S T : HSp D) (u : WO S T) (f : WO S T → ℂ) :
    heisO ψ S T u (fun w => starRingEnd ℂ (f w)) = fun w => starRingEnd ℂ (heisO ψ (negSp S) T u f w) := by
  funext w
  simp only [heisO, symplOH_neg, map_mul]
  rw [← Complex.star_def, star_char' ψ hψ]

theorem lineAt_neg {θ : InfFam D} (hθ : IsInfFam θ) {m n : ℕ} (τ : D.what₂.Tau) (z : Matrix (Fin m) (Fin n) ℂ) (t : ℝ) :
    lineAt θ τ (-z) t = lineAt θ τ z (-t) := by
  have hL : IsLineAt θ τ z (lineAt θ τ z) := Classical.epsilon_spec (GlobalTheory.RealLineAt.lineAt_exists D θ hθ m n τ z)
  have hL0 : IsLineAt θ τ (-z) (lineAt θ τ (-z)) :=
    Classical.epsilon_spec (GlobalTheory.RealLineAt.lineAt_exists D θ hθ m n τ (-z))
  have hN : IsLineAt θ τ (-z) (-lineAt θ τ z) := by
    refine ⟨continuous_neg.comp hL.1, fun t => ?_, fun t τ' => ?_⟩
    · rw [AddMonoidHom.neg_apply, Matrix.map_neg _ (fun a => RingHom.map_neg (finPart D) a), hL.2.1 t, neg_zero]
    · have := hL.2.2 t τ'
      have e : compAt θ τ' ((-lineAt θ τ z) t) = -compAt θ τ' (lineAt θ τ z t) := by
        unfold compAt
        rw [AddMonoidHom.neg_apply, Matrix.map_neg _ (fun a => by rw [RingHom.map_neg, RingHom.map_neg])]
      rw [e, this]
      split_ifs <;> simp
  rw [GlobalTheory.RealLineAt.lineAt_unique D θ hθ m n τ (-z) _ _ hL0 hN]
  simp

theorem dRho_neg {θ : InfFam D} (hθ : IsInfFam θ) {m n : ℕ} (hs : Mx D m n → (Mx D m n → ℂ) → (Mx D m n → ℂ))
    (τ : D.what₂.Tau) (z : Matrix (Fin m) (Fin n) ℂ) (f : Mx D m n → ℂ) (x : Mx D m n) :
    Formalism.IndefR.Datum.dRho hs θ τ (-z) f x = -Formalism.IndefR.Datum.dRho hs θ τ z f x := by
  unfold Formalism.IndefR.Datum.dRho
  simp_rw [lineAt_neg hθ]
  rw [deriv_comp_neg (f := fun t => hs (lineAt θ τ z t) f x), neg_zero]

theorem dRho_conj (ψ : AddChar (AF D.host.F) ℂ) (hψ : ∀ x, ‖ψ x‖ = 1) (θ : InfFam D) (S T : HSp D) (τ : D.what₂.Tau)
    (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (f : WO S T → ℂ) (x : WO S T) :
    Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z (fun w => starRingEnd ℂ (f w)) x =
      starRingEnd ℂ (Formalism.IndefR.Datum.dRho (heisO ψ (negSp S) T) θ τ z f x) := by
  unfold Formalism.IndefR.Datum.dRho
  simp_rw [heisO_conj ψ hψ]
  exact deriv.star

theorem cplxO_neg {m n : ℕ} (sS : Matrix (Fin n) (Fin n) ℂ) (sT : Matrix (Fin m) (Fin m) ℂ) (z : Matrix (Fin m) (Fin n) ℂ) :
    cplxO (-sS) sT z = -cplxO sS sT z := by
  unfold cplxO
  rw [Matrix.mul_neg, smul_neg]

theorem latO_le (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) : latO S T LS LT P ≤ latO (negSp S) T LS LT P := by
  unfold latO
  rw [AddSubgroup.closure_le]
  rintro w ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩
  rw [← neg_neg (Matrix.of _)]
  refine neg_mem (AddSubgroup.subset_closure ⟨α, hα, hP, a, ha, s, hs, t, ht, ?_⟩)
  funext i j
  simp [negSp_gram, Finset.sum_neg_distrib, TensorProduct.tmul_neg]

end GlobalTheory.VacConj

namespace GlobalTheory.VacConj

theorem isVacO_conj_negSp {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D)
    (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (f : WO (negSp S) T → ℂ) :
    IsVacO ψ θ (negSp S) T (fun τ => -sS τ) sT LS LT f → IsVacO ψ θ S T sS sT LS LT (fun w => starRingEnd ℂ (f w)) := by
  rintro ⟨hψ, hv⟩
  have hn : ∀ x, ‖ψ x‖ = 1 := hψ.1.2.1
  have hθ : IsInfFam θ := hv.inf
  refine ⟨hψ, ⟨hθ, ⟨fun γ w => ?_, ?_, ?_, ?_⟩, ⟨fun u hu => ?_, fun e he u hu hh => ?_⟩, fun τ z => ?_, ?_⟩⟩
  · have h := hv.theta.quasi γ w
    show starRingEnd ℂ (f (ratW T S γ + w)) = _
    rw [show f (ratW T S γ + w) = _ from h, map_mul, symplOH_neg, ← Complex.star_def, star_char' ψ hn]
    rfl
  · obtain ⟨U, hU, hUf⟩ := hv.theta.level
    exact ⟨U, hU, fun u hu hu' => by rw [heisO_conj ψ hn, hUf u hu hu']⟩
  · exact Complex.continuous_conj.comp hv.theta.cont
  · intro k L hL hL' w
    exact (Complex.conjCLE.contDiff.comp (hv.theta.smooth k L hL hL' w) :)
  · rw [heisO_conj ψ hn, hv.lat.1 u (latO_le S T LS LT _ hu)]
  · rw [heisO_conj ψ hn, hv.lat.2 e he u (latO_le S T LS LT _ hu) hh]
  · funext x
    have h := congrFun (hv.fock τ z) x
    simp only [annih, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h ⊢
    rw [cplxO_neg, dRho_neg hθ] at h
    rw [dRho_conj ψ hn, dRho_conj ψ hn]
    have h' := congrArg (starRingEnd ℂ) h
    simp only [map_add, map_mul, map_neg, Complex.conj_I, map_zero] at h'
    linear_combination h'
  · obtain ⟨h1, h2⟩ := hv.norm
    refine ⟨h1, fun p hp => ?_⟩
    have := h2 p hp
    unfold nrm2 at this ⊢
    simp only [Complex.norm_conj]
    exact this

end GlobalTheory.VacConj
