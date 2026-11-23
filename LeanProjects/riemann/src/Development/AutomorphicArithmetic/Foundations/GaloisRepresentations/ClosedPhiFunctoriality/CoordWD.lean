import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.IntBasisAlt
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong GlobalTheory.WeilDeligne Matrix
open scoped Formalism.Per NNReal
open UpperTheory.Gal.ClosedPhiFromClosedTrace

private theorem letter_lift {LL U D : Type} [Field LL] [Field U] [AddCommGroup D] [Module LL D]
    (m : U →+* Module.End LL D) (F : Type) [Field F] [Algebra LL F] (τ : U →+* F)
    {B M : Type} [CommRing B] [AddCommGroup M] [Module B M] (κ : F →+* B) (f : D →+ M)
    (hL : ∀ (r : LL) (x : D), f (r • x) = κ (algebraMap LL F r) • f x)
    (hU : ∀ (u : U) (x : D), f (m u x) = κ (τ u) • f x) :
    ∃ ψ : Letter m F τ →+ M, (∀ (c : F) (y : Letter m F τ), ψ (c • y) = κ c • ψ y) ∧
      ∀ x : D, ψ (letterMk m F τ x) = f x := by
  letI : Module F M := Module.compHom M κ
  have hsm : ∀ (c : F) (y : M), c • y = κ c • y := fun _ _ => rfl
  let f₂ : F →+ D →+ M := AddMonoidHom.mk' (fun c =>
      (DistribMulAction.toAddMonoidHom M (κ c)).comp f)
    (fun c c' => by
      ext x
      simp [add_smul])
  have hf₂ : ∀ c x, f₂ c x = κ c • f x := fun _ _ => rfl
  let g : F ⊗[LL] D →+ M := TensorProduct.liftAddHom f₂ fun r c x => by
    rw [hf₂, hf₂, hL, Algebra.smul_def, map_mul, mul_comm, mul_smul, smul_comm]
  have hg : ∀ c x, g (c ⊗ₜ x) = κ c • f x := fun _ _ => rfl
  have hgs : ∀ (c : F) (y : F ⊗[LL] D), g (c • y) = κ c • g y := fun c y => by
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [smul_add, map_add, map_add, smul_add, hx, hy]
    | tmul c' x => rw [TensorProduct.smul_tmul', hg, hg, smul_eq_mul, map_mul, mul_smul]
  let gL : F ⊗[LL] D →ₗ[F] M := { toFun := g, map_add' := g.map_add, map_smul' := hgs }
  have hk : letterKer m F τ ≤ LinearMap.ker gL := iSup_le fun u => by
    rintro _ ⟨y, rfl⟩
    rw [LinearMap.mem_ker]
    change g _ = 0
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]
    | tmul c x =>
      simp only [LinearMap.sub_apply, LinearMap.baseChange_tmul, LinearMap.smul_apply, LinearMap.id_apply,
        map_sub, hgs, hg, hU]
      rw [smul_comm, sub_self]
  let ψL : Letter m F τ →ₗ[F] M := (letterKer m F τ).liftQ gL hk
  refine ⟨ψL.toAddMonoidHom, fun c y => ψL.map_smul c y, fun x => ?_⟩
  change g (1 ⊗ₜ x) = f x
  rw [hg, map_one, one_smul]

private theorem coord_smul {l : ℕ} [Fact l.Prime] {P : LocPrime l} {L : FinExt l} {a : ℕ}
    {ψ₀ : (Fin a → ↥L.1) ⊗[ℚ_[l]] Bst P →+ (Fin a → OB P)} (h : IsCoord P L ψ₀) (c : ↥L.1)
    (y : (Fin a → ↥L.1) ⊗[ℚ_[l]] Bst P) :
    ψ₀ (c • y) = (((c : Om l) ⊗ₜ 1 : OB P)) • ψ₀ y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [smul_add, map_add, map_add, smul_add, hx, hy]
  | tmul v b =>
    funext i
    rw [TensorProduct.smul_tmul', h, Pi.smul_apply, Pi.smul_apply, h, smul_eq_mul, smul_eq_mul,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    rfl

private theorem coord_mulV {l : ℕ} [Fact l.Prime] {P : LocPrime l} {L : FinExt l} {a : ℕ}
    {ψ₀ : (Fin a → ↥L.1) ⊗[ℚ_[l]] Bst P →+ (Fin a → OB P)} (h : IsCoord P L ψ₀) (c : ↥(MaximalUnramifiedExtension l))
    (y : (Fin a → ↥L.1) ⊗[ℚ_[l]] Bst P) :
    ψ₀ (GlobalTheory.Pst.mulV P ↥L.1 (Fin a → ↥L.1) c y) = (((c : Om l) ⊗ₜ 1 : OB P)) • ψ₀ y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, map_add, smul_add, hx, hy]
  | tmul v b =>
    funext i
    rw [GlobalTheory.Pst.mulV_tmul, h, Pi.smul_apply, h, smul_eq_mul,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← Algebra.smul_def, ← TensorProduct.smul_tmul]
    rfl

private noncomputable def kap {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ) : ℂ →+* OB P :=
  (Algebra.TensorProduct.includeLeftRingHom : Om l →+* OB P).comp ι.symm.toRingHom

private theorem kap_apply {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ) (z : Om l) :
    kap P ι (ι z) = (z ⊗ₜ 1 : OB P) := by
  change ((ι.symm (ι z) ⊗ₜ 1 : OB P)) = _
  rw [RingEquiv.symm_apply_apply]

section
variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {K L : FinExt l} {a : ℕ}
  (R : Representation ↥L.1 ↥(GK K) (Fin a → ↥L.1))
  (ψ₀ : (Fin a → ↥L.1) ⊗[ℚ_[l]] Bst P →+ (Fin a → OB P))

set_option synthInstance.maxHeartbeats 400000 in

private noncomputable def fD : ↥(GlobalTheory.Pst.Dpst P R) →+ (Fin a → OB P) :=
  { toFun := fun x => ψ₀ x.1, map_zero' := ψ₀.map_zero, map_add' := fun x y => ψ₀.map_add x.1 y.1 }

set_option synthInstance.maxHeartbeats 400000 in
private theorem fD_smul (h : IsCoord P L ψ₀) (ι : Om l ≃+* ℂ) (r : ↥L.1) (x : ↥(GlobalTheory.Pst.Dpst P R)) :
    fD R ψ₀ (r • x) = kap P ι (ι (r : Om l)) • fD R ψ₀ x := by
  exact (coord_smul h r x.1).trans
    (congrArg (fun t : OB P => t • ψ₀ x.1) (kap_apply P ι (r : Om l)).symm)

set_option synthInstance.maxHeartbeats 400000 in
private theorem fD_mul (h : IsCoord P L ψ₀) (ι : Om l ≃+* ℂ) (u : ↥(MaximalUnramifiedExtension l)) (x : ↥(GlobalTheory.Pst.Dpst P R)) :
    fD R ψ₀ (GlobalTheory.Pst.mulD P R u x) = kap P ι (ι (u : Om l)) • fD R ψ₀ x := by
  exact (coord_mulV h u x.1).trans
    (congrArg (fun t : OB P => t • ψ₀ x.1) (kap_apply P ι (u : Om l)).symm)

end

set_option synthInstance.maxHeartbeats 400000 in
theorem UpperTheory.Gal.ClosedPhiFromClosedTrace.coordWD_holds :
    CoordWD := by
  intro l _ P ι K L a R ψ₀ h
  obtain ⟨ψ, h1, h2⟩ := @letter_lift ↥L.1 ↥(MaximalUnramifiedExtension l) ↥(GlobalTheory.Pst.Dpst P R) _ _ _ _ (GlobalTheory.Pst.mulD P R) ℂ _ (GlobalTheory.Pst.algC ι L)
    (GlobalTheory.Pst.urC ι) (OB P) (Fin a → OB P) _ _ _ (kap P ι) (fD R ψ₀)
    (fun r x => fD_smul R ψ₀ h ι r x) (fun u x => fD_mul R ψ₀ h ι u x)
  exact ⟨ψ, h1, h2⟩
