import Development.AbelianVarietyTheory.Definitions.Divisors.IsFlatLift
open GlobalTheory GlobalTheory.DI

namespace GlobalTheory.DI.FrobeniusTwistSmul

def FrobTw (K : Type) (p : ℕ) (W : Type) : Type := W

section
variable (K : Type) [CommRing K] (p : ℕ) [Fact p.Prime] [CharP K p] (W : Type) [AddCommGroup W] [Module K W]

instance : AddCommGroup (FrobTw K p W) := inferInstanceAs (AddCommGroup W)

instance : Module K (FrobTw K p W) := @Module.compHom K K W _ _ _ _ (frobenius K p)

theorem frobTw_smul (c : K) (x : FrobTw K p W) :
    c • x = ((c ^ p • (show W from x) : W) : FrobTw K p W) := by
  show (frobenius K p c) • (show W from x) = _
  rw [frobenius_def]

end

theorem main : ∀ {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] {W : Type} [AddCommGroup W] [Module K W] (p : ℕ) [Fact p.Prime] [CharP K p] (g : ∀ a : ℕ, (Fin a → V) → W), (∀ a v k x y, g a (Function.update v k (x + y)) = g a (Function.update v k x) + g a (Function.update v k y)) → (∀ a v k (c : K) x, g a (Function.update v k (c • x)) = c ^ p • g a (Function.update v k x)) → (∀ a v k l, k ≠ l → v k = v l → g a v = 0) → ∃ Φ : ExteriorAlgebra K V →+ W, ∀ (c : K) (a : ℕ) (v : Fin a → V), Φ (c • ExteriorAlgebra.ιMulti K a v) = c ^ p • g a v := by
  intro K _ V _ _ W _ _ p _ _ g hadd hsmul halt
  let f : ∀ a : ℕ, V [⋀^Fin a]→ₗ[K] FrobTw K p W := fun a =>
    { toFun := fun v => (g a v : FrobTw K p W)
      map_update_add' := fun m i x y => by
        obtain rfl : ‹DecidableEq (Fin a)› = instDecidableEqFin a := Subsingleton.elim _ _
        exact hadd a m i x y
      map_update_smul' := fun m i c x => by
        obtain rfl : ‹DecidableEq (Fin a)› = instDecidableEqFin a := Subsingleton.elim _ _
        exact (hsmul a m i c x).trans (frobTw_smul K p W c (g a (Function.update m i x))).symm
      map_eq_zero_of_eq' := fun v i j h hij => halt a v i j hij h }
  refine ⟨(ExteriorAlgebra.liftAlternating (R := K) (M := V) (N := FrobTw K p W) f).toAddMonoidHom, ?_⟩
  intro c a v
  show (ExteriorAlgebra.liftAlternating (R := K) (M := V) (N := FrobTw K p W) f) (c • ExteriorAlgebra.ιMulti K a v) = _
  rw [LinearMap.map_smul, ExteriorAlgebra.liftAlternating_apply_ιMulti, frobTw_smul]
  rfl

end GlobalTheory.DI.FrobeniusTwistSmul
