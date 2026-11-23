import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FRatioSelf
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAffCoverSpec
import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCotangentBasis
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HomeomorphZeroSet

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.JacSpan

theorem ker_le_span_sup {A : Type} [CommRing A] [Algebra ℂ A] (e : A →+* ℂ)
    (he : ∀ c : ℂ, e (algebraMap ℂ A c) = c) {d : ℕ} (δ : Fin d → A →+ ℂ)
    (hmul : ∀ b f g, δ b (f * g) = e f * δ b g + e g * δ b f)
    (hc : ∀ b (c : ℂ), δ b (algebraMap ℂ A c) = 0) (g : Fin d → A)
    (hgs : ∀ a : A, e a = 0 → ∃ c : Fin d → ℂ, a - ∑ j, c j • g j ∈ RingHom.ker e ^ 2)
    (φ : Fin d → A) (hdet : (Matrix.of fun a b => δ b (φ a)).det ≠ 0) :
    RingHom.ker e ≤ Ideal.span (Set.range fun j => φ j - algebraMap ℂ A (e (φ j))) ⊔
      RingHom.ker e ^ 2 := by
  classical
  have hsq : ∀ b, ∀ x ∈ RingHom.ker e ^ 2, δ b x = 0 := by
    intro b x hx
    rw [pow_two] at hx
    refine Submodule.mul_induction_on hx (fun x hx y hy => ?_) (fun x y hx hy => ?_)
    · rw [hmul, RingHom.mem_ker.1 hx, RingHom.mem_ker.1 hy, zero_mul, zero_mul, add_zero]
    · rw [map_add, hx, hy, add_zero]
  have hsmul : ∀ b (c : ℂ) (x : A), δ b (c • x) = c * δ b x := by
    intro b c x
    rw [Algebra.smul_def, hmul, hc, he, mul_zero, add_zero]
  set φ' : Fin d → A := fun j => φ j - algebraMap ℂ A (e (φ j)) with hφ'
  have hφ'e : ∀ j, e (φ' j) = 0 := fun j => by simp only [hφ', map_sub, he, sub_self]
  choose C hC using fun j => hgs (φ' j) (hφ'e j)
  let M : Matrix (Fin d) (Fin d) ℂ := Matrix.of fun k b => δ b (g k)
  have hJ : (Matrix.of fun a b => δ b (φ a)) = Matrix.of C * M := by
    ext a b
    have h1 := hsq b _ (hC a)
    rw [map_sub, map_sum] at h1
    simp only [hsmul] at h1
    have h2 : δ b (φ' a) = δ b (φ a) := by simp only [hφ', map_sub, hc, sub_zero]
    rw [Matrix.of_apply, Matrix.mul_apply, ← h2]
    simp only [M, Matrix.of_apply]
    linear_combination h1
  have hdetC : (Matrix.of C).det ≠ 0 := by
    rw [hJ, Matrix.det_mul] at hdet
    exact left_ne_zero_of_mul hdet
  have hu : IsUnit (Matrix.of C).det := isUnit_iff_ne_zero.2 hdetC
  intro a ha
  obtain ⟨β, hβ⟩ := hgs a (RingHom.mem_ker.1 ha)
  set γ := Matrix.vecMul β (Matrix.of C)⁻¹ with hγdef
  have hγ : Matrix.vecMul γ (Matrix.of C) = β := by
    rw [hγdef, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hu, Matrix.vecMul_one]
  have hsum : ∑ j, γ j • ∑ k, C j k • g k = ∑ k, β k • g k := by
    rw [← hγ]
    simp only [Finset.smul_sum, smul_smul, Matrix.vecMul, dotProduct, Finset.sum_smul,
      Matrix.of_apply]
    exact Finset.sum_comm
  have hspan : ∑ j, γ j • φ' j ∈ Ideal.span (Set.range φ') :=
    Ideal.sum_mem _ fun j _ => Submodule.smul_of_tower_mem _ _ (Ideal.subset_span ⟨j, rfl⟩)
  have hrest : a - ∑ j, γ j • φ' j ∈ RingHom.ker e ^ 2 := by
    have h3 : a - ∑ j, γ j • φ' j =
        (a - ∑ k, β k • g k) - ∑ j, γ j • (φ' j - ∑ k, C j k • g k) := by
      rw [← hsum]
      simp only [smul_sub, Finset.sum_sub_distrib]
      abel
    rw [h3]
    exact sub_mem hβ (Ideal.sum_mem _ fun j _ => Submodule.smul_of_tower_mem _ _ (hC j))
  have h4 : a = (a - ∑ j, γ j • φ' j) + ∑ j, γ j • φ' j := by abel
  rw [h4]
  exact add_mem (Ideal.mem_sup_right hrest) (Ideal.mem_sup_left hspan)

end GlobalTheory.JacSpan

open GlobalTheory.ChartGlue in

theorem GlobalTheory.JacSpan.ker_le_span_jac : ∀ (X : Scheme.{0}) (p : X ⟶ Sp ℂ) (d : ℕ) [SmoothOfRelativeDimension d p] (U : X.Opens), IsAffineOpen U →
    ∀ (ch : GlobalTheory.AlgChart p (RingHom.id ℂ) d) (φ : Fin d → Γ(X, U)) (z : GlobalTheory.CxPts p (RingHom.id ℂ))
      (_hzc : z ∈ ch.e.source) (hz : z ∈ GlobalTheory.CxPts.ptsIn p (RingHom.id ℂ) U), (ch.jacMat φ z).det ≠ 0 →
      RingHom.ker (GlobalTheory.CxPts.evHom hz) ≤
        Ideal.span (Set.range fun j => φ j - ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U (GlobalTheory.CxPts.evHom hz (φ j))) ⊔
          RingHom.ker (GlobalTheory.CxPts.evHom hz) ^ 2 := by
  intro X p d _ U hU ch φ z hzc hz hdet
  obtain ⟨g, _, hgs, _⟩ := GlobalTheory.CotDim.exists_cotangent_basis X p d U hU z hz
  have hd : ∀ f : Γ(X, U), DifferentiableAt ℂ (CxPts.ev p (RingHom.id ℂ) U f ∘ ch.e.symm) (ch.e z) :=
    fun f => ch.differentiableAt_ev f hzc hz
  have hn : ∀ᶠ v in nhds (ch.e z), ch.e.symm v ∈ CxPts.ptsIn p (RingHom.id ℂ) U :=
    Filter.eventually_of_mem ((isOpen_over ch.e (CxPts.isOpen_ptsIn U)).mem_nhds
      (mem_over ch.e hzc hz)) fun _ h => h.2
  let δ : Fin d → Γ(X, U) →+ ℂ := fun b => AddMonoidHom.mk' (fun f =>
      fderiv ℂ (CxPts.ev p (RingHom.id ℂ) U f ∘ ch.e.symm) (ch.e z) (EuclideanSpace.single b 1))
    (fun f g => by
      have e : CxPts.ev p (RingHom.id ℂ) U (f + g) ∘ ch.e.symm =
          (CxPts.ev p (RingHom.id ℂ) U f ∘ ch.e.symm) + (CxPts.ev p (RingHom.id ℂ) U g ∘ ch.e.symm) :=
        funext fun v => CxPts.ev_add _ _ _
      simp only [e, fderiv_add (hd f) (hd g), ContinuousLinearMap.add_apply])
  have hmul : ∀ b (f g : Γ(X, U)), δ b (f * g) =
      CxPts.evHom hz f * δ b g + CxPts.evHom hz g * δ b f := by
    intro b f g
    have e : CxPts.ev p (RingHom.id ℂ) U (f * g) ∘ ch.e.symm =
        (CxPts.ev p (RingHom.id ℂ) U f ∘ ch.e.symm) * (CxPts.ev p (RingHom.id ℂ) U g ∘ ch.e.symm) :=
      funext fun v => CxPts.ev_mul _ _ _
    simp only [δ, AddMonoidHom.mk'_apply, e, fderiv_mul (hd f) (hd g), Function.comp_apply,
      ch.e.left_inv hzc, CxPts.ev_eq hz, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul]
  have hc : ∀ b (c : ℂ), δ b (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U c) = 0 := by
    intro b c
    have e : CxPts.ev p (RingHom.id ℂ) U (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U c) ∘ ch.e.symm
        =ᶠ[nhds (ch.e z)] fun _ => c := hn.mono fun v hv => CxPts.ev_algX hv c
    simp only [δ, AddMonoidHom.mk'_apply]
    rw [e.fderiv_eq]
    simp
  exact GlobalTheory.JacSpan.ker_le_span_sup (A := GlobalTheory.CechDR.Sec p U) (CxPts.evHom hz)
    (fun c => (CxPts.ev_eq hz _).symm.trans (CxPts.ev_algX hz c)) δ hmul hc g hgs φ hdet
