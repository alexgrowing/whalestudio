import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GenHom
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedIdealPowerLeSections
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GeneratedSubsheafLeOfTwistedSectionMem

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE GlobalTheory.CompanionTheory.GE.TwGen

namespace GlobalTheory.CompanionTheory.GE.TwGen

theorem mem_twSecs_of_mem_twPow {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {X : Scheme.{0}} [X.Over (Spec (.of A))] (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X) (P : X.Modules)
    (n : ℤ) (m : ℕ) : twPow I H n P m ⊆ twSecs H n (powSub I P m) := by
  letI : Algebra A Γ(X, ⊤) := GroundTheory.Arith.SchemeCoh.overAlgebra (CommRingCat.of A)
  have fac : ∀ a ∈ I ^ m, ∃ ψ : P ⟶ GroundTheory.Arith.SchemeCoh.idealPow I P m,
      ψ ≫ GroundTheory.Arith.SchemeCoh.idealPowι I P m = GroundTheory.Arith.SchemeCoh.smulHom P (algebraMap A Γ(X, ⊤) a) := by
    intro a ha
    rw [← GroundTheory.Arith.SchemeCoh.span_idealGen (I ^ m)] at ha
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun A).mp ha
    let u : P ⟶ ⨁ fun _ : Fin (GroundTheory.Arith.SchemeCoh.idealGenNum (I ^ m)) => P :=
      biproduct.lift fun k => GroundTheory.Arith.SchemeCoh.smulHom P (algebraMap A Γ(X, ⊤) (c k))
    have hu : u ≫ GroundTheory.Arith.SchemeCoh.idealSumMap P (I ^ m) = GroundTheory.Arith.SchemeCoh.smulHom P (algebraMap A Γ(X, ⊤) a) := by
      rw [← hc]
      simp only [u, GroundTheory.Arith.SchemeCoh.idealSumMap, biproduct.lift_desc, GroundTheory.Arith.SchemeCoh.smulHom_comp_smulHom, map_sum, GroundTheory.Arith.SchemeCoh.smulHom_sum,
        smul_eq_mul, map_mul]
    refine ⟨kernel.lift (cokernel.π (GroundTheory.Arith.SchemeCoh.idealSumMap P (I ^ m))) (u ≫ GroundTheory.Arith.SchemeCoh.idealSumMap P (I ^ m))
      (by rw [Category.assoc, cokernel.condition, comp_zero]), ?_⟩
    rw [← hu]
    exact kernel.lift_ι _ _ _
  have act : ∀ (r : Γ(X, ⊤)) (s : Γ(GlobalTheory.twistZ P H n, ⊤)),
      ConcreteCategory.hom (Scheme.Modules.Hom.app (GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (GroundTheory.Arith.SchemeCoh.smulHom P r)) ⊤) s
        = GroundTheory.Arith.SchemeCoh.restrictTop ⊤ r • s := by
    intro r s
    rw [GlobalTheory.Twist.sec_ext_iff]
    intro i
    rw [GlobalTheory.Twist.coord_map_app, GroundTheory.Arith.SchemeCoh.smulHom_app_apply, GlobalTheory.Twist.coord_smul]
    congr 1
    exact (GroundTheory.Arith.SchemeCoh.restrictTop_restrict _ r).symm
  have base : ∀ a ∈ I ^ m, ∀ s : Γ(GlobalTheory.twistZ P H n, ⊤), GroundTheory.Arith.SchemeCoh.toFunctions (X := X) ⊤ a • s ∈ Set.range
      (ConcreteCategory.hom (Scheme.Modules.Hom.app (GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (powSub I P m).arrow) ⊤)) := by
    intro a ha s
    obtain ⟨ψ, hψ⟩ := fac a ha
    have e : (ψ ≫ (Subobject.underlyingIso (GroundTheory.Arith.SchemeCoh.idealPowι I P m)).inv) ≫ (powSub I P m).arrow
        = GroundTheory.Arith.SchemeCoh.smulHom P (algebraMap A Γ(X, ⊤) a) := by
      show (ψ ≫ (Subobject.underlyingIso (GroundTheory.Arith.SchemeCoh.idealPowι I P m)).inv) ≫ (Subobject.mk (GroundTheory.Arith.SchemeCoh.idealPowι I P m)).arrow = _
      rw [Category.assoc, Subobject.underlyingIso_arrow, hψ]
    refine ⟨ConcreteCategory.hom (Scheme.Modules.Hom.app (GlobalTheory.Twist.map (GlobalTheory.lbZPow H n)
      (ψ ≫ (Subobject.underlyingIso (GroundTheory.Arith.SchemeCoh.idealPowι I P m)).inv)) ⊤) s, ?_⟩
    have h2 := act (algebraMap A Γ(X, ⊤) a) s
    rw [← e] at h2
    erw [GlobalTheory.Twist.map_comp, Scheme.Modules.Hom.comp_app] at h2
    try erw [ConcreteCategory.comp_apply] at h2
    exact h2
  let K : Ideal Γ(X, ⊤) :=
    { carrier := {r | ∀ s : Γ(GlobalTheory.twistZ P H n, ⊤), r • s ∈ Set.range
        (ConcreteCategory.hom (Scheme.Modules.Hom.app (GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (powSub I P m).arrow) ⊤))}
      add_mem' := by
        intro x y hx hy s
        obtain ⟨u, hu⟩ := hx s
        obtain ⟨v, hv⟩ := hy s
        exact ⟨u + v, by rw [map_add, hu, hv, add_smul]⟩
      zero_mem' := by
        intro s
        exact ⟨0, by rw [map_zero, zero_smul]⟩
      smul_mem' := by
        intro t x hx s
        obtain ⟨u, hu⟩ := hx (t • s)
        exact ⟨u, by rw [hu, smul_eq_mul, mul_comm, mul_smul]⟩ }
  have hJ : Ideal.map (GroundTheory.Arith.SchemeCoh.toFunctions (X := X) ⊤) (I ^ m) ≤ K := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    exact base a ha
  intro c hc
  simp only [twPow, SetLike.mem_coe] at hc
  refine Submodule.smul_induction_on (p := fun x => x ∈ Set.range
      (ConcreteCategory.hom (Scheme.Modules.Hom.app (GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (powSub I P m).arrow) ⊤)))
    hc ?_ ?_
  · intro r hr s _
    exact hJ hr s
  · intro x y hx hy
    obtain ⟨u, hu⟩ := hx
    obtain ⟨v, hv⟩ := hy
    exact ⟨u + v, by rw [map_add, hu, hv]⟩

theorem genSub_le_powSub : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {X : Scheme.{0}} [X.Over (Spec (.of A))] {H : ReciprocityTheory.ChartRestriction.G.Semi.LB X} (hH : H.IsLB)
    {P : X.Modules}, P.IsQuasicoherent → ∀ (n : ℤ) (m : ℕ) (c : Γ(GlobalTheory.twistZ P H n, ⊤)),
    c ∈ twPow I H n P m → genSub hH n c ≤ powSub I P m := by
  intro A _ _ I X _ H hH P _ n m c hc
  exact genSub_le hH (powSub I P m) n c (mem_twSecs_of_mem_twPow I H P n m hc)

end GlobalTheory.CompanionTheory.GE.TwGen
