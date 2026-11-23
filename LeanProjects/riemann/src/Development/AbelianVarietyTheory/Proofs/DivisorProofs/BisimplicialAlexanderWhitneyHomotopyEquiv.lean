import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTotalBiChains
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AwOCommDStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalDifferentialEval
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalDifferentialEval
open CategoryTheory Limits Opposite AlgebraicTopology GlobalTheory.EZ
universe u v

noncomputable section
namespace GlobalTheory.EZ.AWEq

open Finset HomologicalComplex₂

set_option backward.isDefEq.respectTransparency false

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteCoproducts C]
  (Y : SimplicialObject (SimplicialObject C))

theorem awop' : ∀ (n a b : ℕ), a + b = n → dD (n + 1) n ≫ awO n a b = ∑ x ∈ Finset.HasAntidiagonal.antidiagonal (n + 1), awO (n + 1) x.1 x.2 ≫ dT x.1 x.2 a b := GlobalTheory.T.dD_comp_awO_eq_sum_awO_comp_dT
theorem evd' : ∀ {C : Type u} [Category.{v} C] [Preadditive C] (Y : SimplicialObject (SimplicialObject C)) (n : ℕ), (ev Y).map (dD (n + 1) n) = (diagCx Y).d (n + 1) n := @GlobalTheory.T.diagonal_differential_eval
theorem totd' : ∀ {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteCoproducts C] (Y : SimplicialObject (SimplicialObject C)) (a b k : ℕ) (h : a + b = k + 1), (dbl Y).ιTotal (ComplexShape.down ℕ) a b (k + 1) (by simpa only [ComplexShape.π_def] using h) ≫ (tot Y).d (k + 1) k = ∑ x ∈ (Finset.HasAntidiagonal.antidiagonal k).attach, (ev Y).map (dT a b x.1.1 x.1.2) ≫ (dbl Y).ιTotal (ComplexShape.down ℕ) x.1.1 x.1.2 k (by simpa only [ComplexShape.π_def] using Finset.HasAntidiagonal.mem_antidiagonal.1 x.2) := @GlobalTheory.T.total_differential_eval

abbrev ιz (a b n : ℕ) : ((dbl Y).X a).X b ⟶ (tot Y).X n := (dbl Y).ιTotalOrZero (ComplexShape.down ℕ) a b n

theorem ιz_eq (a b n : ℕ) (h : a + b = n) :
    ιz Y a b n = (dbl Y).ιTotal (ComplexShape.down ℕ) a b n (by simpa only [ComplexShape.π_def] using h) :=
  (dbl Y).ιTotalOrZero_eq _ _ _ _ _

theorem ιz_ne (a b n : ℕ) (h : a + b ≠ n) : ιz Y a b n = 0 :=
  (dbl Y).ιTotalOrZero_eq_zero _ _ _ _ (by simpa only [ComplexShape.π_def] using h)

theorem dT_eq_zero (a b a' b' : ℕ) (h : a + b ≠ a' + b' + 1) : dT a b a' b' = 0 := by
  unfold dT dH dV
  rw [if_neg (by omega), if_neg (by omega), smul_zero, add_zero]

theorem awF_eq (n : ℕ) :
    awF Y n = ∑ x ∈ antidiagonal n, (ev Y).map (awO n x.1 x.2) ≫ ιz Y x.1 x.2 n := by
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, ← Fin.sum_univ_eq_sum_range]
  unfold awF
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [ιz_eq Y _ _ _ (by omega)]

theorem ιz_d (a b k : ℕ) :
    ιz Y a b (k + 1) ≫ (tot Y).d (k + 1) k =
      ∑ x ∈ antidiagonal k, (ev Y).map (dT a b x.1 x.2) ≫ ιz Y x.1 x.2 k := by
  by_cases h : a + b = k + 1
  · rw [ιz_eq Y _ _ _ h, totd' Y a b k h, ← Finset.sum_attach (antidiagonal k)]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [ιz_eq Y _ _ _ (Finset.HasAntidiagonal.mem_antidiagonal.1 x.2)]
  · rw [ιz_ne Y _ _ _ h, zero_comp]
    refine (Finset.sum_eq_zero fun x hx => ?_).symm
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    rw [dT_eq_zero _ _ _ _ (by omega), Functor.map_zero, zero_comp]

def shufF (G : ∀ a b n : ℕ, bo a b ⟶ bo n n) (n : ℕ) : (tot Y).X n ⟶ (diagCx Y).X n :=
  (dbl Y).totalDesc (c₁₂ := ComplexShape.down ℕ) (fun a b _ => (ev Y).map (G a b n))

theorem ιz_shufF (G : ∀ a b n : ℕ, bo a b ⟶ bo n n) (a b n : ℕ) (h : a + b = n) :
    ιz Y a b n ≫ shufF Y G n = (ev Y).map (G a b n) := by
  rw [ιz_eq Y _ _ _ h, shufF, ι_totalDesc]

theorem shufF_comm (G : ∀ a b n : ℕ, bo a b ⟶ bo n n)
    (hG : ∀ a b n : ℕ, a + b = n + 1 → G a b (n + 1) ≫ dD (n + 1) n =
      ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, dT a b x.1 x.2 ≫ G x.1 x.2 n) (n : ℕ) :
    (tot Y).d (n + 1) n ≫ shufF Y G n = shufF Y G (n + 1) ≫ (diagCx Y).d (n + 1) n := by
  refine total.hom_ext (K := dbl Y) (c₁₂ := ComplexShape.down ℕ) (fun a b h => ?_)
  simp only [ComplexShape.π_def] at h
  rw [← ιz_eq Y _ _ _ h, ← Category.assoc, ιz_d, Preadditive.sum_comp, ← Category.assoc, ιz_shufF Y G _ _ _ h,
    ← evd', ← Functor.map_comp, hG a b n h, Functor.map_sum]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [Category.assoc, ιz_shufF Y G _ _ _ (Finset.HasAntidiagonal.mem_antidiagonal.1 hx), Functor.map_comp]

end GlobalTheory.EZ.AWEq

noncomputable section
namespace GlobalTheory.EZ.AWEq

open Finset HomologicalComplex₂

set_option backward.isDefEq.respectTransparency false

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteCoproducts C]
  (Y : SimplicialObject (SimplicialObject C))

theorem awF_comm (n : ℕ) : awF Y (n + 1) ≫ (tot Y).d (n + 1) n = (diagCx Y).d (n + 1) n ≫ awF Y n := by
  rw [awF_eq, awF_eq, Preadditive.sum_comp, Preadditive.comp_sum, ← evd']
  simp_rw [Category.assoc, ιz_d, Preadditive.comp_sum]
  simp_rw [← Category.assoc, ← Functor.map_comp]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y hy => ?_
  rw [awop' n y.1 y.2 (Finset.HasAntidiagonal.mem_antidiagonal.1 hy), Functor.map_sum, Preadditive.sum_comp]

theorem awF_shufF (G : ∀ a b n : ℕ, bo a b ⟶ bo n n) (n : ℕ) :
    awF Y n ≫ shufF Y G n = (ev Y).map (∑ x ∈ antidiagonal n, awO n x.1 x.2 ≫ G x.1 x.2 n) := by
  rw [awF_eq, Preadditive.sum_comp, Functor.map_sum]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [Category.assoc, ιz_shufF Y G _ _ _ (Finset.HasAntidiagonal.mem_antidiagonal.1 hx), Functor.map_comp]

theorem idc_self (n : ℕ) : idc n n = 𝟙 _ := by
  ext j
  simp [idc, clampHom]
  exact Nat.le_of_lt_succ j.2

theorem ev_idO_self (a b : ℕ) : (ev Y).map (idO a b a b) = 𝟙 _ := by
  rw [idO, if_pos ⟨rfl, rfl⟩, ev_map_bop, idc_self, idc_self]
  simp
  rfl

theorem sum_idO (a b n : ℕ) (h : a + b = n) :
    ∑ y ∈ antidiagonal n, (ev Y).map (idO a b y.1 y.2) ≫ ιz Y y.1 y.2 n = ιz Y a b n := by
  rw [Finset.sum_eq_single (a, b)]
  · rw [ev_idO_self, Category.id_comp]
  · intro y _ hy
    rw [idO, if_neg (fun h' => hy (Prod.ext h'.1.symm h'.2.symm)), Functor.map_zero, zero_comp]
  · intro hy
    exact absurd (Finset.HasAntidiagonal.mem_antidiagonal.2 h) hy

def homD (H : ∀ n m : ℕ, bo n n ⟶ bo m m) (i j : ℕ) : (diagCx Y).X i ⟶ (diagCx Y).X j :=
  if i + 1 = j then (ev Y).map (H i j) else 0

def homT (K : ∀ a b a' b' : ℕ, bo a b ⟶ bo a' b') (i j : ℕ) : (tot Y).X i ⟶ (tot Y).X j :=
  if i + 1 = j then
    (dbl Y).totalDesc (c₁₂ := ComplexShape.down ℕ)
      (fun a b _ => ∑ x ∈ antidiagonal j, (ev Y).map (K a b x.1 x.2) ≫ ιz Y x.1 x.2 j)
  else 0

theorem ιz_homT (K : ∀ a b a' b' : ℕ, bo a b ⟶ bo a' b') (a b n : ℕ) (h : a + b = n) :
    ιz Y a b n ≫ homT Y K n (n + 1) =
      ∑ x ∈ antidiagonal (n + 1), (ev Y).map (K a b x.1 x.2) ≫ ιz Y x.1 x.2 (n + 1) := by
  rw [homT, if_pos rfl, ιz_eq Y _ _ _ h, ι_totalDesc]

theorem ιz_dNext (K : ∀ a b a' b' : ℕ, bo a b ⟶ bo a' b') (a b n : ℕ) (h : a + b = n) :
    ιz Y a b n ≫ dNext n (homT Y K) =
      ∑ x ∈ antidiagonal n, ∑ j ∈ antidiagonal (n - 1),
        (ev Y).map (dT a b j.1 j.2 ≫ K j.1 j.2 x.1 x.2) ≫ ιz Y x.1 x.2 n := by
  cases n with
  | zero =>
    rw [Homotopy.dNext_zero_chainComplex, Limits.comp_zero]
    refine (Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun j hj => ?_).symm
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hj
    rw [dT_eq_zero _ _ _ _ (by omega), Limits.zero_comp, Functor.map_zero, Limits.zero_comp]
  | succ m =>
    rw [Homotopy.dNext_succ_chainComplex, ← Category.assoc, ιz_d, Preadditive.sum_comp, Nat.add_sub_cancel]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Category.assoc, ιz_homT Y K _ _ _ (Finset.HasAntidiagonal.mem_antidiagonal.1 hj), Preadditive.comp_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Category.assoc, ← Functor.map_comp]

end GlobalTheory.EZ.AWEq

noncomputable section
namespace GlobalTheory.EZ.AWEq

open Finset HomologicalComplex₂

set_option backward.isDefEq.respectTransparency false

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteCoproducts C]
  (Y : SimplicialObject (SimplicialObject C))

def awC : diagCx Y ⟶ tot Y where
  f := awF Y
  comm' := by
    rintro i j (rfl : j + 1 = i)
    exact awF_comm Y j

def shufC (G : ∀ a b n : ℕ, bo a b ⟶ bo n n)
    (hG : ∀ a b n : ℕ, a + b = n + 1 → G a b (n + 1) ≫ dD (n + 1) n =
      ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, dT a b x.1 x.2 ≫ G x.1 x.2 n) : tot Y ⟶ diagCx Y where
  f := shufF Y G
  comm' := by
    rintro i j (rfl : j + 1 = i)
    exact (shufF_comm Y G hG j).symm

def htpyD (G : ∀ a b n : ℕ, bo a b ⟶ bo n n)
    (hG : ∀ a b n : ℕ, a + b = n + 1 → G a b (n + 1) ≫ dD (n + 1) n =
      ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, dT a b x.1 x.2 ≫ G x.1 x.2 n)
    (H : ∀ n m : ℕ, bo n n ⟶ bo m m)
    (hH : ∀ n : ℕ, ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, awO n x.1 x.2 ≫ G x.1 x.2 n =
      𝟙 (bo n n) + H n (n + 1) ≫ dD (n + 1) n + dD n (n - 1) ≫ H (n - 1) n) :
    Homotopy (awC Y ≫ shufC Y G hG) (𝟙 (diagCx Y)) where
  hom := homD Y H
  zero i j hij := if_neg hij
  comm n := by
    rw [HomologicalComplex.comp_f, HomologicalComplex.id_f, Homotopy.prevD_chainComplex]
    change awF Y n ≫ shufF Y G n = _
    rw [awF_shufF, hH n]
    simp only [Functor.map_add, Functor.map_id, Functor.map_comp]
    rw [evd', homD, if_pos rfl, show (ev Y).map (𝟙 (bo n n)) = 𝟙 ((diagCx Y).X n) from (ev Y).map_id _]
    cases n with
    | zero =>
      rw [Homotopy.dNext_zero_chainComplex]
      have : dD 0 (0 - 1) = 0 := by simp [dD]
      rw [this, Functor.map_zero, zero_comp, add_zero]
      abel
    | succ m =>
      rw [Homotopy.dNext_succ_chainComplex, Nat.add_sub_cancel, evd', homD, if_pos rfl]
      abel

def htpyT (G : ∀ a b n : ℕ, bo a b ⟶ bo n n)
    (hG : ∀ a b n : ℕ, a + b = n + 1 → G a b (n + 1) ≫ dD (n + 1) n =
      ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, dT a b x.1 x.2 ≫ G x.1 x.2 n)
    (K : ∀ a b a' b' : ℕ, bo a b ⟶ bo a' b')
    (hK : ∀ a b a' b' : ℕ, a' + b' = a + b → G a b (a + b) ≫ awO (a + b) a' b' = idO a b a' b' +
      ∑ x ∈ Finset.HasAntidiagonal.antidiagonal (a + b + 1), K a b x.1 x.2 ≫ dT x.1 x.2 a' b' +
      ∑ x ∈ Finset.HasAntidiagonal.antidiagonal (a + b - 1), dT a b x.1 x.2 ≫ K x.1 x.2 a' b') :
    Homotopy (shufC Y G hG ≫ awC Y) (𝟙 (tot Y)) where
  hom := homT Y K
  zero i j hij := if_neg hij
  comm n := by
    rw [HomologicalComplex.comp_f, HomologicalComplex.id_f, Homotopy.prevD_chainComplex]
    change shufF Y G n ≫ awF Y n = _
    refine total.hom_ext (K := dbl Y) (c₁₂ := ComplexShape.down ℕ) (fun a b h => ?_)
    simp only [ComplexShape.π_def] at h
    rw [← ιz_eq Y _ _ _ h]
    subst h

    rw [← Category.assoc, ιz_shufF Y G _ _ _ rfl, awF_eq, Preadditive.comp_sum]
    simp_rw [← Category.assoc, ← Functor.map_comp]
    rw [Finset.sum_congr rfl fun y hy => by
      rw [hK a b y.1 y.2 (Finset.HasAntidiagonal.mem_antidiagonal.1 hy)]]
    simp_rw [Functor.map_add, Preadditive.add_comp, Finset.sum_add_distrib, sum_idO Y a b _ rfl,
      Functor.map_sum, Preadditive.sum_comp]

    simp only [Preadditive.comp_add, Category.comp_id]
    rw [← Category.assoc, ιz_homT Y K a b _ rfl, Preadditive.sum_comp]
    simp_rw [Category.assoc, ιz_d, Preadditive.comp_sum, ← Category.assoc, ← Functor.map_comp]
    rw [Finset.sum_comm (s := antidiagonal (a + b + 1))]
    rw [ιz_dNext Y K a b _ rfl, show ιz Y a b (a + b) ≫ 𝟙 ((tot Y).X (a + b)) = ιz Y a b (a + b) from Category.comp_id _]
    abel

end GlobalTheory.EZ.AWEq

namespace GlobalTheory.EZ

open GlobalTheory.EZ.AWEq

theorem awHomotopyEquiv : ∀ {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteCoproducts C] (Y : SimplicialObject (SimplicialObject C)) (G : ∀ a b n : ℕ, bo a b ⟶ bo n n) (H : ∀ n m : ℕ, bo n n ⟶ bo m m) (K : ∀ a b a' b' : ℕ, bo a b ⟶ bo a' b'), G 0 0 0 = 𝟙 (bo 0 0) → (∀ a b n : ℕ, a + b = n + 1 → G a b (n + 1) ≫ dD (n + 1) n = ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, dT a b x.1 x.2 ≫ G x.1 x.2 n) → (∀ n : ℕ, ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, awO n x.1 x.2 ≫ G x.1 x.2 n = 𝟙 (bo n n) + H n (n + 1) ≫ dD (n + 1) n + dD n (n - 1) ≫ H (n - 1) n) → (∀ a b a' b' : ℕ, a' + b' = a + b → G a b (a + b) ≫ awO (a + b) a' b' = idO a b a' b' + ∑ x ∈ Finset.HasAntidiagonal.antidiagonal (a + b + 1), K a b x.1 x.2 ≫ dT x.1 x.2 a' b' + ∑ x ∈ Finset.HasAntidiagonal.antidiagonal (a + b - 1), dT a b x.1 x.2 ≫ K x.1 x.2 a' b') → ∃ e : HomotopyEquiv (diagCx Y) (tot Y), ∀ n : ℕ, e.hom.f n = awF Y n := by
  intro C _ _ _ Y G H K _ hG hH hK
  exact ⟨HomotopyEquiv.mk (awC Y) (shufC Y G hG) (htpyD Y G hG H hH) (htpyT Y G hG K hK), fun _ => rfl⟩

end GlobalTheory.EZ
