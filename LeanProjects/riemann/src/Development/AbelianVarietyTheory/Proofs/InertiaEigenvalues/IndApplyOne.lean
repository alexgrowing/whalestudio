import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BrauerDegreeZero
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.VirtualCharactersMulComapConjIndLinear

noncomputable section
open GlobalTheory.BI

namespace GlobalTheory.BrauerZero

def D0 (G : Type) [Group G] : AddSubgroup (G → ℂ) :=
  AddSubgroup.closure {f | ∃ (H : Subgroup G) (χ : H →* ℂˣ),
    f = ind H (fun h => (χ h : ℂ)) - ind H (fun _ => 1)}

theorem ind_sub {G : Type} [Group G] [Finite G] (T : Subgroup G) (a b : T → ℂ) :
    ind T (a - b) = ind T a - ind T b :=
  (indAddHomComplex T).map_sub a b

theorem ind_const {G : Type} [Group G] [Finite G] (T : Subgroup G) (c : ℂ) (g : G) :
    ind T (fun _ => c) g = c * ind T (fun _ => 1) g := by
  classical
  haveI := Fintype.ofFinite G
  simp only [ind, finsum_eq_sum_of_fintype, ext0]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  split_ifs <;> ring

theorem ind_apply_one {G : Type} [Group G] [Finite G] (T : Subgroup G) (ψ : T → ℂ) :
    ind T ψ 1 = (T.index : ℂ) * ψ 1 := by
  classical
  haveI := Fintype.ofFinite G
  have h1 : ∀ x : G, ext0 T ψ (x⁻¹ * 1 * x) = ψ 1 := fun x => by
    have e : x⁻¹ * 1 * x = 1 := by group
    simp only [ext0, e, dif_pos T.one_mem]
    rfl
  simp only [ind, finsum_eq_sum_of_fintype]
  rw [Finset.sum_congr rfl (fun x _ => h1 x), Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Nat.card_eq_fintype_card, ← T.card_mul_index]
  have : (Nat.card T : ℂ) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := T)).ne'
  push_cast
  field_simp

theorem ind_top {G : Type} [Group G] [Finite G] (F : G → ℂ) (hF : ∀ g x : G, F (x⁻¹ * g * x) = F g) :
    ind (⊤ : Subgroup G) (fun h => F h) = F := by
  classical
  haveI := Fintype.ofFinite G
  funext g
  simp only [ind, finsum_eq_sum_of_fintype, ext0, Subgroup.mem_top, dite_true, hF]
  have hc : Nat.card {x : G // True} = Nat.card G := Nat.card_congr (Equiv.subtypeUnivEquiv (fun _ => trivial))
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card, hc]
  have : (Nat.card G : ℂ) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := G)).ne'
  field_simp

theorem indFun_eq_ind {G : Type} [Group G] [Fintype G] (H : Subgroup G) (f : H → ℂ) :
    GlobalTheory.Published.indFun H f = ind H f := by
  classical
  funext g
  simp only [GlobalTheory.Published.indFun, ind, finsum_eq_sum_of_fintype, ext0]

end GlobalTheory.BrauerZero
