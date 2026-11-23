import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.AffineSplittingSpan.RowExact
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.AffineSplittingSpan.CoreSteps

noncomputable section

namespace PositivityTheory.KB.SplitAffineSpectral.PolynomialPseudoInverse

open NormTraceLemmas

variable {P Q : Type} [Group P] [Group Q]

theorem pow_slice (t : P) {a b : ℕ} (n : ℕ) (x : Bi P Q a b) (x' : Fin a → Q) :
    ((TcL t a b ^ n) x) x' = (mapOp (fun y => t⁻¹ * y * t) b ^ n) (x x') := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, Module.End.mul_apply, ih, pow_succ, Module.End.mul_apply]
    rfl

theorem aeval_slice (t : P) {a b : ℕ} (f : Polynomial ℝ) (x : Bi P Q a b) (x' : Fin a → Q) :
    (Polynomial.aeval (TcL t a b) f x) x' = Polynomial.aeval (mapOp (fun y => t⁻¹ * y * t) b) f (x x') := by
  induction f using Polynomial.induction_on' with
  | add p r hp hr =>
    simp only [map_add, LinearMap.add_apply, Pi.add_apply, hp, hr]
  | monomial n c =>
    simp only [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply,
      Pi.smul_apply, pow_slice]

theorem pinv_Tc (pr : P →* Q) (s : Q →* P) (hs : ∀ g, pr (s g) = g) (u : Q) (hu : ∀ g, g * u = u * g)
    {a b : ℕ} {F : Bi P Q a b} (hF : PInv pr F) : PInv pr (Tc (s u) F) := by
  intro g x y
  have hp : pr ((s u)⁻¹ * g * s u) = pr g := by
    rw [map_mul, map_mul, map_inv, hs, mul_assoc, hu (pr g), inv_mul_cancel_left]
  have key := hF ((s u)⁻¹ * g * s u) x (fun j => (s u)⁻¹ * y j * s u)
  rw [hp] at key
  show F (fun i => pr g * x i) (fun j => (s u)⁻¹ * (g * y j) * s u) = F x (fun j => (s u)⁻¹ * y j * s u)
  rw [← key]
  congr 1
  funext j
  group

def pinvT (pr : P →* Q) (a b : ℕ) : Submodule ℝ (Bi P Q a b) where
  carrier := {F | PInv pr F}
  add_mem' := fun {F G} hF hG g x y => by
    change F _ _ + G _ _ = F x y + G x y
    rw [hF g x y, hG g x y]
  zero_mem' := fun _ _ _ => rfl
  smul_mem' := fun c F hF g x y => by
    change c • F _ _ = c • F x y
    rw [hF g x y]

theorem pinv_aeval (pr : P →* Q) (s : Q →* P) (hs : ∀ g, pr (s g) = g) (u : Q) (hu : ∀ g, g * u = u * g)
    {a b : ℕ} (f : Polynomial ℝ) {F : Bi P Q a b} (hF : PInv pr F) :
    PInv pr (Polynomial.aeval (TcL (s u) a b) f F) := by
  have hpow : ∀ n : ℕ, PInv pr ((TcL (s u) a b ^ n) F) := by
    intro n
    induction n with
    | zero => simpa using hF
    | succ n ih =>
      rw [pow_succ', Module.End.mul_apply]
      exact pinv_Tc pr s hs u hu ih
  induction f using Polynomial.induction_on' with
  | add p r hp hr =>
    rw [map_add, LinearMap.add_apply]
    exact (pinvT pr a b).add_mem hp hr
  | monomial n c =>
    rw [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply]
    exact (pinvT pr a b).smul_mem c (hpow n)

end PositivityTheory.KB.SplitAffineSpectral.PolynomialPseudoInverse

namespace PositivityTheory.KB.SplitAffineSpectral.NormTraceLemmas

open PolynomialPseudoInverse

variable {P Q : Type} [Group P] [Group Q]

theorem colKill (pr : P →* Q) (s : Q →* P) (hs : ∀ g, pr (s g) = g) (u : Q) (hu : ∀ g, g * u = u * g)
    (q : ℕ) (f : Polynomial ℝ)
    (hf : ∀ c : (Fin (q + 2) → P) → ℝ, InvS (pr.ker : Set P) c → dc c = 0 →
      ∃ e : (Fin (q + 1) → P) → ℝ, InvS (pr.ker : Set P) e ∧
        Polynomial.aeval (mapOp (fun y => (s u)⁻¹ * y * s u) (q + 2)) f c = dc e)
    {a : ℕ} (x : Bi P Q (a + 1) (q + 2)) (hx : PInv pr x) (hv : dv x = 0) :
    ∃ E : Bi P Q (a + 1) (q + 1), PInv pr E ∧ Polynomial.aeval (TcL (s u) (a + 1) (q + 2)) f x = dv E := by
  have hX : PInv pr (Polynomial.aeval (TcL (s u) (a + 1) (q + 2)) f x) :=
    pinv_aeval pr s hs u hu f hx
  have hinv : ∀ z : Fin (a + 1) → Q, InvS (pr.ker : Set P) (x z) := by
    intro z g hg y
    have hg' : pr g = 1 := hg
    have h := hx g z y
    simpa [hg'] using h
  have hdz : ∀ z : Fin (a + 1) → Q, dc (x z) = 0 := fun z => congrFun hv z
  choose e he1 he2 using fun z => hf (x z) (hinv z) (hdz z)
  refine ⟨fun x' y => e (fun i => (x' 0)⁻¹ * x' i) (fun j => (s (x' 0))⁻¹ * y j), ?_, ?_⟩
  · intro g x' y
    show e (fun i => (pr g * x' 0)⁻¹ * (pr g * x' i)) (fun j => (s (pr g * x' 0))⁻¹ * (g * y j))
      = e (fun i => (x' 0)⁻¹ * x' i) (fun j => (s (x' 0))⁻¹ * y j)
    have hn : (fun i => (pr g * x' 0)⁻¹ * (pr g * x' i)) = fun i => (x' 0)⁻¹ * x' i := by
      funext i
      group
    rw [hn]
    have hk : (s (x' 0))⁻¹ * (s (pr g))⁻¹ * g * s (x' 0) ∈ (pr.ker : Set P) := by
      show pr ((s (x' 0))⁻¹ * (s (pr g))⁻¹ * g * s (x' 0)) = 1
      simp only [map_mul, map_inv, hs]
      group
    rw [← he1 _ _ hk (fun j => (s (x' 0))⁻¹ * y j)]
    congr 1
    funext j
    rw [map_mul]
    group
  · funext x' y
    have hpr : pr (s (x' 0))⁻¹ = (x' 0)⁻¹ := by rw [map_inv, hs]
    calc Polynomial.aeval (TcL (s u) (a + 1) (q + 2)) f x x' y
        = Polynomial.aeval (TcL (s u) (a + 1) (q + 2)) f x (fun i => pr (s (x' 0))⁻¹ * x' i)
            (fun j => (s (x' 0))⁻¹ * y j) := (hX (s (x' 0))⁻¹ x' y).symm
      _ = Polynomial.aeval (mapOp (fun y => (s u)⁻¹ * y * s u) (q + 2)) f (x (fun i => (x' 0)⁻¹ * x' i))
            (fun j => (s (x' 0))⁻¹ * y j) := by
          rw [hpr, aeval_slice]
      _ = dc (e (fun i => (x' 0)⁻¹ * x' i)) (fun j => (s (x' 0))⁻¹ * y j) := by
          rw [he2]
      _ = _ := rfl

end PositivityTheory.KB.SplitAffineSpectral.NormTraceLemmas

end
