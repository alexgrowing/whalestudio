import Mathlib

namespace GlobalTheory.SecondComponentSum

theorem snd_eq_sum {k A : Type} [CommRing k] [CommRing A] [Algebra k A] {D : ℕ}
    (f : Fin D → A) (B : Module.Basis (Fin D) A Ω[A⁄k])
    (hB : ∀ i : Fin D, B i = KaehlerDifferential.D k A (f i))
    {K : Type} [Field K] (θ : A →+* DualNumber K)
    (hθ : ∀ a : k, TrivSqZeroExt.snd (θ (algebraMap k A a)) = (0 : K)) (s : A) :
    TrivSqZeroExt.snd (θ s) = ∑ b : Fin D, TrivSqZeroExt.snd (θ (f b)) *
      TrivSqZeroExt.fst (θ ((LinearMap.compDer (Module.Basis.coord B b)
        (KaehlerDifferential.D k A)) s)) := by
  classical

  let φ : A →+* K := (TrivSqZeroExt.fstHom K K K).toRingHom.comp θ
  let _ : Module A K := Module.compHom K φ
  let _ : Module k K := Module.compHom K (φ.comp (algebraMap k A))
  have : IsScalarTower k A K := ⟨fun c a x => by
    change φ (c • a) * x = φ (algebraMap k A c) * (φ a * x)
    rw [Algebra.smul_def, map_mul, mul_assoc]⟩
  have hsmul : ∀ (a : A) (x : K), a • x = TrivSqZeroExt.fst (θ a) * x := fun _ _ => rfl
  have hsndmul : ∀ a b : A, TrivSqZeroExt.snd (θ (a * b)) =
      TrivSqZeroExt.fst (θ a) * TrivSqZeroExt.snd (θ b) +
        TrivSqZeroExt.snd (θ a) * TrivSqZeroExt.fst (θ b) := by
    intro a b
    rw [map_mul, TrivSqZeroExt.snd_mul, smul_eq_mul, op_smul_eq_mul]
  let ℓ : A →ₗ[k] K :=
    { toFun := fun a => TrivSqZeroExt.snd (θ a)
      map_add' := fun a b => by
        simp only [map_add, TrivSqZeroExt.snd_add]
      map_smul' := fun c a => by
        change TrivSqZeroExt.snd (θ (c • a)) = φ (algebraMap k A c) * TrivSqZeroExt.snd (θ a)
        rw [Algebra.smul_def, hsndmul, hθ, zero_mul, add_zero]
        rfl }
  let d : Derivation k A K := Derivation.mk' ℓ fun a b => by
    change TrivSqZeroExt.snd (θ (a * b)) = TrivSqZeroExt.fst (θ a) * TrivSqZeroExt.snd (θ b) +
      TrivSqZeroExt.fst (θ b) * TrivSqZeroExt.snd (θ a)
    rw [hsndmul, mul_comm (TrivSqZeroExt.snd (θ a))]

  have key := congrArg d.liftKaehlerDifferential (B.sum_repr (KaehlerDifferential.D k A s))
  rw [Derivation.liftKaehlerDifferential_comp_D, map_sum] at key
  change d s = _
  rw [← key]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [LinearMap.map_smul, hB, Derivation.liftKaehlerDifferential_comp_D, hsmul, mul_comm]
  rfl

end GlobalTheory.SecondComponentSum
