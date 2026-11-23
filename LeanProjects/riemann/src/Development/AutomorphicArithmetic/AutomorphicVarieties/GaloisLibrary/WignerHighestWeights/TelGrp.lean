import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.IsAlgIsoRefl
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualInfinitesimalCharacterRegular
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

private theorem rp_comm {X M : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup M] [Module ℂ M]
    (κ : Module.End ℂ M) (g : X → X) :
    ∀ (n : ℕ) (b : Fin n → X →ₗ[ℂ] Module.End ℂ M), (∀ i y, κ * b i y = b i (g y) * κ) →
      ∀ x : Fin n → X, κ * rp n b x = rp n b (fun i => g (x i)) * κ := by
  intro n
  induction n with
  | zero => intro b _ x; rw [rp_zero, rp_zero, mul_one, one_mul]
  | succ n ih =>
    intro b hb x
    have h := ih (Fin.tail b) (fun i y => hb i.succ y) (Fin.tail x)
    rw [rp_succ, rp_succ, ← mul_assoc, h, mul_assoc, hb, ← mul_assoc]
    rfl

theorem UpperTheory.V.AlgRepEndIrreducible.telGrp :
    ∀ (X M : Type) [AddCommGroup X] [Module ℂ X] [AddCommGroup M] [Module ℂ M] (n : ℕ) (a b : Fin n → X →ₗ[ℂ] Module.End ℂ M) (κ : Module.End ℂ M) (g : X → X),
      (∀ i y, κ * a i y = a i (g y) * κ) → (∀ i y, κ * b i y = b i (g y) * κ) →
      ∀ f f' : X →ₗ[ℂ] M, (∀ y, κ (f y) = f' (g y)) → ∀ x : Fin n → X, κ (tel n a b f x) = tel n a b f' fun i => g (x i) := by
  intro X M _ _ _ _ n
  induction n with
  | zero => intro a b κ g _ _ f f' _ x; rw [tel_zero, tel_zero, map_zero]
  | succ n ih =>
    intro a b κ g ha hb f f' hf x
    have h1 := ih (Fin.tail a) (Fin.tail b) κ g (fun i y => ha i.succ y) (fun i y => hb i.succ y) f f' hf (Fin.tail x)
    have h2 := LinearMap.congr_fun (rp_comm κ g n (Fin.tail b) (fun i y => hb i.succ y) (Fin.tail x)) (f (x 0))
    have h3 := LinearMap.congr_fun (ha 0 (x 0)) (tel n (Fin.tail a) (Fin.tail b) f (Fin.tail x))
    simp only [Module.End.mul_apply] at h2 h3
    rw [tel_succ, tel_succ, map_add, h2, h3, h1, hf]
    rfl
