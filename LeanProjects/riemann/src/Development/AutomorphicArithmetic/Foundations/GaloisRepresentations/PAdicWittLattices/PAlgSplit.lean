import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.SplitsBasic
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsEvaluation
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.TensorHomExt
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

namespace UpperTheory.Gal.G3.AlgebraSplitting

private noncomputable def sec {A A' C J : Type} [CommRing A] [CommRing A'] [CommRing C] [Algebra A A'] [Algebra A C]
    (τ : J → (A' →ₐ[A] C)) : C ⊗[A] A' →ₐ[C] (J → C) :=
  Pi.algHom C (fun _ => C) fun j =>
    Algebra.TensorProduct.lift (AlgHom.id C C) (τ j) fun _ _ => Commute.all _ _

private lemma sec_tmul {A A' C J : Type} [CommRing A] [CommRing A'] [CommRing C] [Algebra A A'] [Algebra A C]
    (τ : J → (A' →ₐ[A] C)) (c : C) (b : A') (j : J) : sec τ (c ⊗ₜ b) j = c * τ j b := by
  simp [sec]

private lemma tensor_hom_ext {A A' C Ω : Type} [CommRing A] [CommRing A'] [CommRing C] [Algebra A A'] [Algebra A C]
    [CommRing Ω] {u v : C ⊗[A] A' →+* Ω} (h₁ : ∀ c : C, u (c ⊗ₜ 1) = v (c ⊗ₜ 1))
    (h₂ : ∀ b : A', u (1 ⊗ₜ b) = v (1 ⊗ₜ b)) : u = v :=
  _root_.UpperTheory.Reformulated.B.Qk54.tensor_hom_ext h₁ h₂

private lemma exists_eval {C Ω J : Type} [CommRing C] [Field Ω] [Fintype J] (f : (J → C) →+* Ω) :
    ∃ j, ∀ v : J → C, f v = f (algebraMap C (J → C) (v j)) :=
  _root_.UpperTheory.Reformulated.B.ExistsEvaluation.exists_eval f

private lemma bij_of_pts (hiso : AlgIsoPts) {C D E : Type} [CommRing C] [CommRing D] [CommRing E] [Algebra C D]
    [Algebra C E] [Algebra.Etale C D] [Algebra.Etale C E] (φ : D →ₐ[C] E)
    (pts : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : D →+* Ω), ∃! y : E →+* Ω, y.comp (φ : D →+* E) = x) :
    Function.Bijective φ := by
  letI : Algebra D E := (φ : D →+* E).toAlgebra
  haveI : IsScalarTower C D E := IsScalarTower.of_algebraMap_eq' (φ.comp_algebraMap).symm
  haveI : Algebra.Etale D E := Algebra.Etale.of_restrictScalars C D E
  exact hiso D E pts

end UpperTheory.Gal.G3.AlgebraSplitting

open UpperTheory.Gal.G3.AlgebraSplitting in
theorem UpperTheory.Gal.G3.pAlgSplit :
    AlgIsoPts → AlgSplit := by
  intro hiso A A' C _ _ _ _ _ _ J _ τ h
  refine ⟨AlgEquiv.ofBijective (sec τ) (bij_of_pts hiso (sec τ) ?_), fun b j => ?_⟩
  swap
  · simp [sec_tmul]
  intro Ω _ _ x
  let x₀ : C →+* Ω := x.comp (Algebra.TensorProduct.includeLeftRingHom)
  let y₀ : A' →+* Ω := x.comp (Algebra.TensorProduct.includeRight : A' →ₐ[A] C ⊗[A] A').toRingHom
  have hx₀ : ∀ c, x₀ c = x (c ⊗ₜ 1) := fun _ => rfl
  have hy₀ : ∀ b, y₀ b = x (1 ⊗ₜ b) := fun _ => rfl
  have compat : y₀.comp (algebraMap A A') = x₀.comp (algebraMap A C) := by
    ext a
    simp only [RingHom.comp_apply, hx₀, hy₀]
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  obtain ⟨j, hj, huniq⟩ := h Ω x₀ y₀ compat
  have hτ : ∀ b, x₀ (τ j b) = y₀ b := fun b => congrArg (fun f : A' →+* Ω => f b) hj
  refine ⟨x₀.comp (Pi.evalRingHom (fun _ => C) j), ?_, ?_⟩
  · apply tensor_hom_ext
    · intro c
      simp [sec_tmul, hx₀]
    · intro b
      have := hτ b
      simp only [RingHom.comp_apply, RingHom.coe_coe, Pi.evalRingHom_apply, sec_tmul, one_mul]
      rw [this, hy₀]
  · intro y' hy'
    have hy'd : ∀ d, y' (sec τ d) = x d := fun d => congrArg (fun f : C ⊗[A] A' →+* Ω => f d) hy'
    obtain ⟨j', hj'⟩ := exists_eval y'
    have hal : ∀ c : C, y' (algebraMap C (J → C) c) = x₀ c := by
      intro c
      rw [hx₀, ← hy'd]
      congr 1
      funext i
      simp [sec_tmul]
    have hy'e : ∀ v : J → C, y' v = x₀ (v j') := fun v => by rw [hj', hal]
    have hjj : j' = j := by
      apply huniq
      ext b
      have := hy'e (sec τ (1 ⊗ₜ b))
      rw [hy'd, sec_tmul, one_mul] at this
      simpa [hy₀] using this.symm
    subst hjj
    ext v
    simp [hy'e]
