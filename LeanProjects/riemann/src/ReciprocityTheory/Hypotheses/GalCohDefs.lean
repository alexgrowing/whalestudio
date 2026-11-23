import ReciprocityTheory.GaloisValuations.ContinuousConstSMulQuotient
import ReciprocityTheory.GaloisValuations.Global

noncomputable section

open NumberField IsDedekindDomain Representation

namespace ReciprocityTheory.Gal

open Formalism.ConjugateSelfDual

instance (priority := 100) continuousConstSMul_of_discrete {R M : Type*} [SMul R M]
    [TopologicalSpace M] [DiscreteTopology M] : ContinuousConstSMul R M :=
  ⟨fun _ => continuous_of_discreteTopology⟩

section Coeff

variable {R : Type*} [CommRing R] {Γ : Type*} [Group Γ]
  {M : Type*} [AddCommGroup M] [Module R M]

def charRep (χ : Γ →* Rˣ) : Representation R Γ R where
  toFun g := ((χ g : Rˣ) : R) • LinearMap.id
  map_one' := by ext; simp
  map_mul' g h := by ext; simp [mul_comm]

@[simp] theorem charRep_apply (χ : Γ →* Rˣ) (g : Γ) (x : R) :
    charRep χ g x = ((χ g : Rˣ) : R) * x := rfl

variable (R M) in

def TDual := Module.Dual R M

instance : AddCommGroup (TDual R M) := inferInstanceAs (AddCommGroup (Module.Dual R M))
instance : Module R (TDual R M) := inferInstanceAs (Module R (Module.Dual R M))
instance : TopologicalSpace (TDual R M) := ⊥
instance : DiscreteTopology (TDual R M) := ⟨rfl⟩
instance : FunLike (TDual R M) M R := inferInstanceAs (FunLike (M →ₗ[R] R) M R)

def TDual.mk (φ : M →ₗ[R] R) : TDual R M := φ

@[simp] theorem TDual.mk_apply (φ : M →ₗ[R] R) (m : M) : TDual.mk φ m = φ m := rfl

@[simp] theorem TDual.add_apply (φ ψ : TDual R M) (m : M) : (φ + ψ) m = φ m + ψ m := rfl

@[simp] theorem TDual.smul_apply (c : R) (φ : TDual R M) (m : M) : (c • φ) m = c * φ m := rfl

@[ext] theorem TDual.ext {φ ψ : TDual R M} (h : ∀ m, φ m = ψ m) : φ = ψ := LinearMap.ext h

def twDual (χ : Γ →* Rˣ) (rho : Representation R Γ M) : Representation R Γ (TDual R M) where
  toFun g :=
    { toFun := fun φ => TDual.mk (((χ g : Rˣ) : R) • ((φ : M →ₗ[R] R) ∘ₗ rho g⁻¹))
      map_add' := fun φ ψ => by
        ext m
        show ((χ g : Rˣ) : R) * (φ (rho g⁻¹ m) + ψ (rho g⁻¹ m)) =
          ((χ g : Rˣ) : R) * φ (rho g⁻¹ m) + ((χ g : Rˣ) : R) * ψ (rho g⁻¹ m)
        ring
      map_smul' := fun c φ => by
        ext m
        show ((χ g : Rˣ) : R) * (c * φ (rho g⁻¹ m)) = c * (((χ g : Rˣ) : R) * φ (rho g⁻¹ m))
        ring }
  map_one' := by ext φ m; simp; rfl
  map_mul' g h := by
    ext φ m
    show _ * φ (rho (g * h)⁻¹ m) = _ * (_ * φ (rho h⁻¹ (rho g⁻¹ m)))
    rw [mul_inv_rev, map_mul rho, Module.End.mul_apply, map_mul χ, Units.val_mul, mul_assoc]

@[simp] theorem twDual_apply (χ : Γ →* Rˣ) (rho : Representation R Γ M) (g : Γ) (φ : TDual R M)
    (m : M) : twDual χ rho g φ m = ((χ g : Rˣ) : R) * φ (rho g⁻¹ m) := rfl

def evalPair : M →ₗ[R] TDual R M →ₗ[R] R := LinearMap.applyₗ

@[simp] theorem evalPair_apply (m : M) (φ : TDual R M) : evalPair m φ = φ m := rfl

theorem evalPair_equiv (χ : Γ →* Rˣ) (rho : Representation R Γ M) (g : Γ) (m : M)
    (φ : TDual R M) : evalPair (rho g m) (twDual χ rho g φ) = charRep χ g (evalPair m φ) := by
  have e : rho g⁻¹ (rho g m) = m := by
    first
      | exact Representation.inv_self_apply rho g m
      | rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
      | rw [← LinearMap.mul_apply, ← map_mul, inv_mul_cancel, map_one, LinearMap.one_apply]
  rw [evalPair_apply, twDual_apply, charRep_apply, evalPair_apply, e]

end Coeff

section Cup

variable {R : Type*} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
  {Γ : Type*} [Group Γ] {M : Type*} [AddCommGroup M] [Module R M]
  [TopologicalSpace M] [DiscreteTopology M]

theorem ContAction.comp' [TopologicalSpace Γ] {D : Type*} [Group D] [TopologicalSpace D]
    {rho : Representation R Γ M} (h : ContAction rho) {φ : D →* Γ} (hφ : Continuous φ) :
    ContAction (rho.comp φ) := by
  exact Continuous.comp (show Continuous (fun p : Γ × M => rho p.1 p.2) from h)
    ((hφ.comp continuous_fst).prodMk continuous_snd)

variable {D : Type*} [Group D] [TopologicalSpace D]
  (χ : Γ →* Rˣ) (rho : Representation R Γ M) (φ : D →* Γ)

def cupH0H2TwistedDual : H0 (rho.comp φ) →ₗ[R] H2 ((twDual χ rho).comp φ) →ₗ[R] H2 ((charRep χ).comp φ) :=
  cupProductH0H2 (rho.comp φ) ((twDual χ rho).comp φ) ((charRep χ).comp φ) evalPair
    continuous_of_discreteTopology (fun g x y => evalPair_equiv χ rho (φ g) x y)

def cup20 : H2 (rho.comp φ) →ₗ[R] H0 ((twDual χ rho).comp φ) →ₗ[R] H2 ((charRep χ).comp φ) :=
  cupProductH2H0 (rho.comp φ) ((twDual χ rho).comp φ) ((charRep χ).comp φ) evalPair
    continuous_of_discreteTopology (fun g x y => evalPair_equiv χ rho (φ g) x y)

def cupH1H1TwistedDual (hrho : ContAction (rho.comp φ)) :
    H1 ((twDual χ rho).comp φ) →ₗ[R] H1 (rho.comp φ) →ₗ[R] H2 ((charRep χ).comp φ) :=
  cupProductH1H1 ((twDual χ rho).comp φ) (rho.comp φ) ((charRep χ).comp φ) evalPair.flip
    continuous_of_discreteTopology (fun g y x => evalPair_equiv χ rho (φ g) x y) hrho

def perpCond {I : Type*} {D : I → Type*} [∀ i, Group (D i)] [∀ i, TopologicalSpace (D i)]
    (phi : ∀ i, D i →* Γ) (hrho : ∀ i, ContAction (rho.comp (phi i)))
    (L : ∀ i, Submodule R (H1 (rho.comp (phi i)))) :
    ∀ i, Submodule R (H1 ((twDual χ rho).comp (phi i))) :=
  fun i => ⨅ x ∈ L i, LinearMap.ker ((cupH1H1TwistedDual χ rho (phi i) (hrho i)).flip x)

theorem mem_perpCond {I : Type*} {D : I → Type*} [∀ i, Group (D i)] [∀ i, TopologicalSpace (D i)]
    (phi : ∀ i, D i →* Γ) (hrho : ∀ i, ContAction (rho.comp (phi i)))
    (L : ∀ i, Submodule R (H1 (rho.comp (phi i)))) (i : I) (y : H1 ((twDual χ rho).comp (phi i))) :
    y ∈ perpCond χ rho phi hrho L i ↔ ∀ x ∈ L i, cupH1H1TwistedDual χ rho (phi i) (hrho i) y x = 0 := by
  show y ∈ ⨅ x ∈ L i, LinearMap.ker ((cupH1H1TwistedDual χ rho (phi i) (hrho i)).flip x) ↔ _
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.flip_apply]

end Cup

section Field

variable {F Ω : Type*} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]

def locDeg (v : HeightOneSpectrum (𝓞 F)) : ℕ :=
  v.asIdeal.ramificationIdx ℤ * v.asIdeal.inertiaDeg ℤ

def IsCCAt (w : InfinitePlace F) (c : G F Ω) : Prop :=
  ∃ j : Ω →+* ℂ, (∀ x, j (c x) = starRingEnd ℂ (j x)) ∧
    InfinitePlace.mk (j.comp (algebraMap F Ω)) = w

variable (F Ω) (l : ℕ) [Fact l.Prime] (r : ℕ)

abbrev muRep : Representation (ZMod (l ^ r)) (G F Ω) (ZMod (l ^ r)) := charRep (cycMod F Ω l r)

variable {F Ω l r} in

abbrev tateDual {M : Type*} [AddCommGroup M] [Module (ZMod (l ^ r)) M]
    (rho : Representation (ZMod (l ^ r)) (G F Ω) M) :
    Representation (ZMod (l ^ r)) (G F Ω) (TDual (ZMod (l ^ r)) M) :=
  twDual (cycMod F Ω l r) rho

end Field

end ReciprocityTheory.Gal
