import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.IsAlgIsoRefl
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualInfinitesimalCharacterRegular
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

private theorem rpDer {X M : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup M] [Module ℂ M]
    (D : Module.End ℂ M) (g : X → X) (n : ℕ) :
    ∀ (b : Fin n → X →ₗ[ℂ] Module.End ℂ M), (∀ i y, D * b i y - b i y * D = b i (g y)) → ∀ x : Fin n → X,
      D * rp n b x = rp n b x * D + ∑ k, rp n b (Function.update x k (g (x k))) := by
  induction n with
  | zero => intro b _ x; simp [rp_zero]
  | succ n ih =>
    intro b hb x
    have h1 := ih (Fin.tail b) (fun i y => hb i.succ y) (Fin.tail x)
    have h0 : D * b 0 (x 0) = b 0 (x 0) * D + b 0 (g (x 0)) := by rw [← hb]; abel
    rw [Fin.sum_univ_succ]
    simp only [rp_succ, Fin.tail_update_zero, Fin.tail_update_succ, Function.update_self,
      Function.update_of_ne (Fin.succ_ne_zero _).symm]
    rw [← mul_assoc, h1, add_mul, mul_assoc, h0, Finset.sum_mul, mul_add, mul_assoc, add_assoc]
    rfl

theorem UpperTheory.V.AlgRepEndIrreducible.telDer :
    ∀ (X M : Type) [AddCommGroup X] [Module ℂ X] [AddCommGroup M] [Module ℂ M] (n : ℕ) (a b : Fin n → X →ₗ[ℂ] Module.End ℂ M) (D : Module.End ℂ M) (g : X → X),
      (∀ i y, D * a i y - a i y * D = a i (g y)) → (∀ i y, D * b i y - b i y * D = b i (g y)) →
      ∀ f f' : X →ₗ[ℂ] M, (∀ y, D (f y) = f' y + f (g y)) → ∀ x : Fin n → X,
        D (tel n a b f x) = tel n a b f' x + ∑ k, tel n a b f (Function.update x k (g (x k))) := by
  intro X M _ _ _ _ n
  induction n with
  | zero => intro a b D g _ _ f f' _ x; simp [tel_zero]
  | succ n ih =>
    intro a b D g ha hb f f' hf x
    have h1 := ih (Fin.tail a) (Fin.tail b) D g (fun i y => ha i.succ y) (fun i y => hb i.succ y) f f' hf (Fin.tail x)
    have h2 := rpDer D g n (Fin.tail b) (fun i y => hb i.succ y) (Fin.tail x)
    have h0 : ∀ m, D (a 0 (x 0) m) = a 0 (x 0) (D m) + a 0 (g (x 0)) m := by
      intro m
      rw [← ha]
      simp
    have h3 : ∀ m, D (rp n (Fin.tail b) (Fin.tail x) m) = rp n (Fin.tail b) (Fin.tail x) (D m) +
        ∑ k : Fin n, rp n (Fin.tail b) (Function.update (Fin.tail x) k (g (x k.succ))) m := by
      intro m
      have := LinearMap.congr_fun h2 m
      simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.sum_apply] at this
      exact this
    have h4 : D (tel n (Fin.tail a) (Fin.tail b) f (Fin.tail x)) = tel n (Fin.tail a) (Fin.tail b) f' (Fin.tail x) +
        ∑ k : Fin n, tel n (Fin.tail a) (Fin.tail b) f (Function.update (Fin.tail x) k (g (x k.succ))) := h1
    rw [Fin.sum_univ_succ]
    simp only [tel_succ, Fin.tail_update_zero, Fin.tail_update_succ, Function.update_self,
      Function.update_of_ne (Fin.succ_ne_zero _).symm]
    rw [map_add, h0, h3, h4, hf, map_add, map_add, map_sum, Finset.sum_add_distrib]
    abel
