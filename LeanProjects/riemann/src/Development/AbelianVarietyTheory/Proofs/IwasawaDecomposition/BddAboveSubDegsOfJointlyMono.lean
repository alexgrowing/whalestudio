import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.QCoh (IsFiniteQC)

namespace GlobalTheory.VB

variable {k : Type} [Field k] {C : Scheme.{0}} [Algebra k Γ(C, ⊤)] [IsIntegral C]

theorem IsProjCurve.bddAbove_subDegs_of_kernel (hC : IsProjCurve k C) {B Q : C.Modules}
    [IsFiniteQC Q] (p : B ⟶ Q) (hK : BddAbove (subDegs k (kernel p)))
    (hQ : BddAbove (subDegs k Q)) : BddAbove (subDegs k B) := by
  have := hC.isNoetherian
  obtain ⟨a, ha⟩ := hK
  obtain ⟨b, hb⟩ := hQ
  refine ⟨a + b, ?_⟩
  rintro _ ⟨G, i, hi, rfl⟩
  have := hi.mono
  have := hi.isFiniteQC
  let q : G ⟶ Q := i ≫ p
  have hKG : IsFiniteQC (kernel q) := .of_mono (kernel.ι q)
  have hm : Mono (Abelian.factorThruCoimage q) := inferInstance
  have hc : IsFiniteQC (cokernel (kernel.ι q)) := .of_mono (Abelian.factorThruCoimage q)
  let j : kernel q ⟶ kernel p := kernel.lift p (kernel.ι q ≫ i) (by
    rw [Category.assoc]; exact kernel.condition q)
  have hj : Mono j := mono_of_mono_fac (kernel.lift_ι p (kernel.ι q ≫ i) _)
  have h₁ : deg k (kernel q) ≤ a := ha (IsCohSub.deg_mem (i := j) ⟨hj, hKG⟩)
  have h₂ : deg k (cokernel (kernel.ι q)) ≤ b :=
    hb (IsCohSub.deg_mem (i := Abelian.factorThruCoimage q) ⟨hm, hc⟩)
  rw [hC.deg_cokernel] at h₂
  omega

theorem IsProjCurve.bddAbove_subDegs_of_jointly_mono (hC : IsProjCurve k C) {D : C.Modules}
    [IsFiniteQC D] (hD : BddAbove (subDegs k D)) (n : ℕ) :
    ∀ (Z : C.Modules) [IsFiniteQC Z] (ψ : Fin n → (Z ⟶ D)),
      (∀ (W : C.Modules) (g : W ⟶ Z), (∀ j, g ≫ ψ j = 0) → g = 0) →
      BddAbove (subDegs k Z) := by
  have := hC.isNoetherian
  induction n with
  | zero =>
    intro Z _ ψ h
    have hZ : IsZero Z := (IsZero.iff_id_eq_zero Z).2 (h Z (𝟙 Z) fun j => j.elim0)
    refine ⟨0, ?_⟩
    rintro _ ⟨G, i, hi, rfl⟩
    have := hi.mono
    exact (deg_eq_zero_of_isZero k (hZ.of_mono i)).le
  | succ n ih =>
    intro Z _ ψ h
    have : IsFiniteQC (kernel (ψ 0)) := .of_mono (kernel.ι (ψ 0))
    refine hC.bddAbove_subDegs_of_kernel (ψ 0)
      (ih (kernel (ψ 0)) (fun j => kernel.ι (ψ 0) ≫ ψ j.succ) fun W g hg => ?_) hD
    have h0 : g ≫ kernel.ι (ψ 0) = 0 := h W _ fun j => by
      refine Fin.cases ?_ (fun j => ?_) j
      · rw [Category.assoc, kernel.condition, comp_zero]
      · rw [Category.assoc]; exact hg j
    exact (cancel_mono (kernel.ι (ψ 0))).1 (h0.trans (zero_comp).symm)

theorem dualMap_sum {F G : C.Modules} {ι : Type} (s : Finset ι) (f : ι → (F ⟶ G)) :
    dualMap (∑ j ∈ s, f j) = ∑ j ∈ s, dualMap (f j) :=
  map_sum (AddMonoidHom.mk' (dualMap (F := F) (G := G)) dualMap_add) f s

theorem bddAbove_subDegs_of_isVB : ∀ (k : Type) [Field k] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)]
    [IsIntegral C], IsProjCurve k C → ∀ (F : C.Modules) (r : ℕ), IsVB F r →
    BddAbove (subDegs k F) := by
  intro k _ C _ _ hC F r hF
  obtain ⟨_, A, hA⟩ := isProper_and_exists_isAmpleLB_of_isProjOver hC.isProjOver
  have := hF.isFiniteQC
  have := hF.dual.isFiniteQC
  obtain ⟨m, n, φ, hφ⟩ := (hA.eventually_exists_epi_sigma (dual F)).exists
  have hL := Twist.isLB_lbZPow hA.isLB (-m)
  have hT := isVB_toMod hL
  let T := GlobalTheory.LB.toMod (lbZPow A (-m))
  have hD : IsVB (dual T) 1 := hT.dual
  have := hD.isFiniteQC
  have := Abelian.hasFiniteBiproducts (C := C.Modules)
  let φ' : (⨁ fun _ : Fin n => T) ⟶ dual F := (biproduct.isoCoproduct _).hom ≫ φ
  have hφ' : Epi φ' := inferInstance
  have hb := hF.isIso_toBidual_of_local_frames
  refine hC.bddAbove_subDegs_of_jointly_mono (hC.isMaxSubDeg_of_rank_one hD).bddAbove n F
    (fun j => cartierDualToBidual F ≫ dualMap (biproduct.ι (fun _ : Fin n => T) j ≫ φ')) fun W g hg => ?_
  have h0 : (g ≫ cartierDualToBidual F) ≫ dualMap φ' = 0 := by
    rw [← Category.comp_id ((g ≫ cartierDualToBidual F) ≫ dualMap φ'), ← dualMap_id,
      ← biproduct.total, dualMap_sum, Preadditive.comp_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    have := hg j
    rw [dualMap_comp, dualMap_comp] at *
    simp only [Category.assoc] at *
    rw [reassoc_of% this, zero_comp]
  have h1 : g ≫ cartierDualToBidual F = 0 := (cancel_mono (dualMap φ')).1 (h0.trans zero_comp.symm)
  exact (cancel_mono (cartierDualToBidual F)).1 (h1.trans zero_comp.symm)

end GlobalTheory.VB
