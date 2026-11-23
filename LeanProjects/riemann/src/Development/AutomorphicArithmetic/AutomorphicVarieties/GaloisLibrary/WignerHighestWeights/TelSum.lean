import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.IsAlgIsoRefl
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualInfinitesimalCharacterRegular
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

private theorem UpperTheory.V.AlgRepEndIrreducible.telSum_commute_rp {X M : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup M] [Module ℂ M]
    (T : Module.End ℂ M) : ∀ (n : ℕ) (b : Fin n → X →ₗ[ℂ] Module.End ℂ M), (∀ j y, Commute T (b j y)) →
      ∀ x : Fin n → X, Commute T (rp n b x) := by
  intro n
  induction n with
  | zero => intro b _ x; rw [rp_zero]; exact Commute.one_right T
  | succ n ih =>
    intro b h x
    rw [rp_succ]
    exact (ih (Fin.tail b) (fun j y => h j.succ y) (Fin.tail x)).mul_right (h 0 (x 0))

theorem UpperTheory.V.AlgRepEndIrreducible.telSum :
    ∀ (X M : Type) [AddCommGroup X] [Module ℂ X] [AddCommGroup M] [Module ℂ M] (n : ℕ) (a b : Fin n → X →ₗ[ℂ] Module.End ℂ M),
      (∀ i j x y, Commute (a i x) (b j y)) → ∀ (m : M) (f : X →ₗ[ℂ] M), (∀ i y, f y = a i y m - b i y m) →
      ∀ x : Fin n → X, tel n a b f x = (List.ofFn fun i => a i (x i)).prod m - rp n b x m := by
  intro X M _ _ _ _ n
  induction n with
  | zero =>
    intro a b _ m f _ x
    rw [tel_zero, rp_zero]
    simp
  | succ n ih =>
    intro a b hc m f hf x
    have h1 := ih (Fin.tail a) (Fin.tail b) (fun i j u v => hc i.succ j.succ u v) m f (fun i y => hf i.succ y)
      (Fin.tail x)
    have h2 : Commute (a 0 (x 0)) (rp n (Fin.tail b) (Fin.tail x)) :=
      UpperTheory.V.AlgRepEndIrreducible.telSum_commute_rp _ n _ (fun j y => hc 0 j.succ (x 0) y) _
    have h3 : a 0 (x 0) (rp n (Fin.tail b) (Fin.tail x) m) = rp n (Fin.tail b) (Fin.tail x) (a 0 (x 0) m) :=
      LinearMap.congr_fun h2.eq m
    rw [tel_succ, rp_succ, h1, hf 0 (x 0), List.ofFn_succ, List.prod_cons, map_sub, map_sub, h3,
      Module.End.mul_apply, Module.End.mul_apply]
    simp only [Fin.tail]
    abel
