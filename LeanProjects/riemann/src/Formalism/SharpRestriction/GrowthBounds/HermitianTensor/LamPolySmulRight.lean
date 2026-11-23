import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.CloudIsoDef
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.Tensor
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.TensorKP
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.FunctorComparisonOfSingleWeight

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames Formalism.GradedWeylDivisibility MvPolynomial Formalism.MainNotions.G.LatticeSystems

def PosOK {p n' : ℕ} (R : RS p n') (m : ℕ) (lam mu mup ze lo lo' : Fin (m + 1) → ℤ) (d : ℚ) (κ : ℕ) : Prop :=
  ∃ abelian₂ : MvPolynomial (Bool × (Fin (m + 1) × Fin (m + 1))) R.Kf →ₗ[R.Kf] MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf,
    (∀ v ∈ dualWeyl R.Kf (m + 1) (m + 1) (nuOf lam), ∀ t ∈ dualWeyl R.Kf (m + 1) (m + 1) (nuOf lo'),
      abelian₂ (blockEmb R.Kf true v * blockEmb R.Kf false t) ∈ dualWeyl R.Kf (m + 1) (m + 1) (nuOf mup)) ∧
    (∀ Λ : Submodule R.O (Fin (m + 1) → R.Kf), IsLattice R.O Λ → ∀ v ∈ H0 R.O m lam Λ, ∀ t ∈ H0 R.O m lo' Λ,
      abelian₂ (blockEmb R.Kf true v * blockEmb R.Kf false t) ∈ H0 R.O m mup Λ) ∧
    ∀ g : Matrix (Fin (m + 1)) (Fin (m + 1)) R.Kf, IsUnit g.det →
      ∃ (nb : ℕ) (z0 : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf)
        (s s' : Fin nb → MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf) (ka : Fin nb → ℕ),
        (nb : ℚ) = d ∧ (∀ b, ka b ≤ κ) ∧
        (∀ a' b, ∀ F ∈ dualWeyl R.Kf (m + 1) (m + 1) (nuOf mu),
          abelian₂ (blockEmb R.Kf true (F * s b) * blockEmb R.Kf false (s' a')) =
            if a' = b then ((p : R.Kf) ^ ka b) • (z0 * F) else 0) ∧
        ∀ c : R.Kf, c ≠ 0 →
          (c ^ (ze 0)) • z0 ∈ H0 R.O m ze (colSpan R.O (g * lb_D _ 1 c)) ∧
          (¬ ∃ z' ∈ H0 R.O m ze (colSpan R.O (g * lb_D _ 1 c)), (c ^ (ze 0)) • z0 = R.w • z') ∧
          (∀ b, (c ^ (lo 0)) • s b ∈ H0 R.O m lo (colSpan R.O (g * lb_D _ 1 c))) ∧
          (∀ a', (c ^ (lo' 0)) • s' a' ∈ H0 R.O m lo' (colSpan R.O (g * lb_D _ 1 c)))

section Gen

variable {K : Type} [Field K] {S α : Type} [Fintype S]

theorem prod_bE_smul {k n : ℕ} (a : S → K) (f : S → MvPolynomial (Fin k × Fin n) K) :
    ∏ s, blockEmb K s (a s • f s) = (∏ s, a s) • ∏ s, blockEmb K s (f s) := by
  simp only [Algebra.smul_def, map_mul, AlgHom.commutes, Finset.prod_mul_distrib, map_prod]

def renB (K : Type) [Field K] (S α : Type) (b : Bool) : MvPolynomial (S × α) K →ₐ[K] MvPolynomial (S × (Bool × α)) K :=
  rename fun x => (x.1, (b, x.2))

theorem renB_prod {k n : ℕ} (v t : S → MvPolynomial (Fin k × Fin n) K) :
    renB K S (Fin k × Fin n) true (∏ s, blockEmb K s (v s)) * renB K S (Fin k × Fin n) false (∏ s, blockEmb K s (t s)) =
      ∏ s, rename (fun x : Bool × (Fin k × Fin n) => (s, x)) (blockEmb K true (v s) * blockEmb K false (t s)) := by
  simp only [map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun s _ => ?_
  simp only [renB, blockEmb, map_mul, rename_rename]
  try rfl

end Gen

section LamPoly

variable {K : Type} [Field K] {S : Type} [Fintype S] {k n : ℕ}

def lamPoly (T : MvPolynomial (S × (Bool × (Fin k × Fin n))) K →ₗ[K] MvPolynomial (S × (Fin k × Fin n)) K)
    (V W : MvPolynomial (S × (Fin k × Fin n)) K) : MvPolynomial (S × (Fin k × Fin n)) K :=
  T (renB K S (Fin k × Fin n) true V * renB K S (Fin k × Fin n) false W)

variable (T : MvPolynomial (S × (Bool × (Fin k × Fin n))) K →ₗ[K] MvPolynomial (S × (Fin k × Fin n)) K)

theorem lamPoly_add_left (V V' W) : lamPoly T (V + V') W = lamPoly T V W + lamPoly T V' W := by
  unfold lamPoly
  rw [map_add, add_mul, map_add]

theorem lamPoly_add_right (V W W') : lamPoly T V (W + W') = lamPoly T V W + lamPoly T V W' := by
  unfold lamPoly
  rw [map_add, mul_add, map_add]

theorem lamPoly_smul_left (c : K) (V W) : lamPoly T (c • V) W = c • lamPoly T V W := by
  unfold lamPoly
  rw [map_smul, smul_mul_assoc, map_smul]

theorem lamPoly_smul_right (c : K) (V W) : lamPoly T V (c • W) = c • lamPoly T V W := by
  unfold lamPoly
  rw [map_smul, mul_smul_comm, map_smul]

theorem lamPoly_zero_left (W) : lamPoly T 0 W = 0 := by
  simp [lamPoly]

theorem lamPoly_zero_right (V) : lamPoly T V 0 = 0 := by
  simp [lamPoly]

variable (L : S → MvPolynomial (Bool × (Fin k × Fin n)) K →ₗ[K] MvPolynomial (Fin k × Fin n) K)
  (hT : ∀ Q : S → MvPolynomial (Bool × (Fin k × Fin n)) K,
    T (∏ s, rename (fun x => (s, x)) (Q s)) = ∏ s, blockEmb K s (L s (Q s)))

include hT in
theorem lamPoly_prod (v t : S → MvPolynomial (Fin k × Fin n) K) :
    lamPoly T (∏ s, blockEmb K s (v s)) (∏ s, blockEmb K s (t s)) =
      ∏ s, blockEmb K s (L s (blockEmb K true (v s) * blockEmb K false (t s))) := by
  unfold lamPoly
  rw [renB_prod, hT]

include hT in

theorem lamPoly_mem {A : Type} [CommRing A] [Algebra A K] (Mv Mt Mr : S → Submodule A (MvPolynomial (Fin k × Fin n) K))
    (h : ∀ s, ∀ v ∈ Mv s, ∀ t ∈ Mt s, L s (blockEmb K true v * blockEmb K false t) ∈ Mr s) :
    ∀ V ∈ tensorLat A K Mv, ∀ W ∈ tensorLat A K Mt, lamPoly T V W ∈ tensorLat A K Mr := by
  intro V hV W hW
  induction hV using Submodule.span_induction with
  | mem V hV0 =>
    induction hW using Submodule.span_induction with
    | mem W hW0 =>
      obtain ⟨F, hF, rfl⟩ := hV0
      obtain ⟨G, hG, rfl⟩ := hW0
      rw [lamPoly_prod T L hT]
      exact Submodule.subset_span ⟨fun s => L s (blockEmb K true (F s) * blockEmb K false (G s)),
        fun s => h s _ (hF s) _ (hG s), rfl⟩
    | zero => rw [lamPoly_zero_right]; exact Submodule.zero_mem _
    | add W W' _ _ h1 h2 => rw [lamPoly_add_right]; exact Submodule.add_mem _ h1 h2
    | smul a W _ h1 =>
      rw [← algebraMap_smul K a W, lamPoly_smul_right, algebraMap_smul]
      exact Submodule.smul_mem _ a h1
  | zero => rw [lamPoly_zero_left]; exact Submodule.zero_mem _
  | add V V' _ _ h1 h2 => rw [lamPoly_add_left]; exact Submodule.add_mem _ h1 h2
  | smul a V _ h1 =>
    rw [← algebraMap_smul K a V, lamPoly_smul_left, algebraMap_smul]
    exact Submodule.smul_mem _ a h1

end LamPoly

theorem cbNuOf_add {m : ℕ} (a b : Fin (m + 1) → ℤ) (ha : Antitone a) (hb : Antitone b) :
    nuOf (a + b) = nuOf a + nuOf b := by
  funext t
  simp only [nuOf, Pi.add_apply]
  have h1 : a (Fin.last m) ≤ a t := ha (Fin.le_last t)
  have h2 : b (Fin.last m) ≤ b t := hb (Fin.le_last t)
  omega

theorem Ar_one {n' m : ℕ} (X : Fin n' → Fin (m + 1) → ℤ) : Ar 1 X = ∑ s, lamAt X s 0 := by
  unfold Ar
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.sum_eq_single_of_mem (0 : Fin (m + 1)) (by simp)]
  intro b hb hb0
  exfalso
  apply hb0
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
  exact Fin.ext (by rw [Fin.val_zero]; omega)

theorem famD_lat (O : Type) {Kf : Type} [CommRing O] [Field Kf] [Algebra O Kf] {n' k : ℕ}
    (gs : Fin n' → Matrix (Fin k) (Fin k) Kf) (hgs : ∀ s, IsUnit (gs s).det) (c : Kf) (hc : c ≠ 0) (s : Fin n') :
    IsLattice O (famD O gs c s) :=
  ⟨gs s * lb_D k 1 c, by rw [Matrix.det_mul]; exact (hgs s).mul (lb_D_det k 1 c hc), rfl⟩

end Formalism.MainNotions.flipOneThree.Pf

end
