import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CxPts GlobalTheory.Cartier

namespace GlobalTheory.VolBr

structure IsBallFam {G : Type} [AddCommGroup G] (Λ : AddSubgroup G) (B : ℝ → Set G) : Prop where

  subset : ∀ r, B r ⊆ Λ

  zero_mem : ∀ r, 0 ≤ r → (0 : G) ∈ B r

  sub_mem : ∀ r r' x y, x ∈ B r → y ∈ B r' → x - y ∈ B (r + r')

  nsmul_iff : ∀ (n : ℕ) (r : ℝ) (x : G), 0 < n → x ∈ Λ → (n • x ∈ B (n * r) ↔ x ∈ B r)

theorem isBallFam_int : IsBallFam (⊤ : AddSubgroup ℤ) fun r => {x | |(x : ℝ)| ≤ r} where
  subset _ _ _ := AddSubgroup.mem_top _
  zero_mem r hr := by simpa using hr
  sub_mem r r' x y hx hy := by
    simp only [Set.mem_setOf_eq, Int.cast_sub] at hx hy ⊢
    exact (abs_sub _ _).trans (add_le_add hx hy)
  nsmul_iff n r x hn _ := by
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    simp only [Set.mem_setOf_eq, nsmul_eq_mul, Int.cast_mul, Int.cast_natCast, abs_mul, Nat.abs_cast]
    exact ⟨fun h => le_of_mul_le_mul_left h hn', fun h => mul_le_mul_of_nonneg_left h hn'.le⟩

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

structure Pair (p : X ⟶ Sp k) where

  L : HermLB p

  A : HermLB p

  r : L.B.ι → X.functionFieldˣ

  r' : A.B.ι → X.functionFieldˣ

  hr : IsRatSec L.B r

  hr' : IsRatSec A.B r'

theorem exists_pair (L A : HermLB p) : ∃ P : Pair p, P.L = L ∧ P.A = A := by
  obtain ⟨r, hr⟩ := exists_isRatSec L.isLB
  obtain ⟨r', hr'⟩ := exists_isRatSec A.isLB
  exact ⟨⟨L, A, r, r', hr, hr'⟩, rfl, rfl⟩

namespace Pair

variable (P : Pair p)

def loc (a b : ℤ) (f : X.functionField) (i : P.L.B.ι) (j : P.A.B.ι) : X.functionField :=
  f * (P.r i : X.functionField) ^ a * (P.r' j : X.functionField) ^ b

def H (a b : ℤ) : AddSubgroup X.functionField where
  carrier := {f | ∀ (x : X) i j, x ∈ P.L.B.U i → x ∈ P.A.B.U j → RegAt x (P.loc a b f i j)}
  zero_mem' x i j _ _ := ⟨0, by simp [loc]⟩
  add_mem' {f g} hf hg x i j hi hj := by
    obtain ⟨u, hu⟩ := hf x i j hi hj
    obtain ⟨v, hv⟩ := hg x i j hi hj
    exact ⟨u + v, by rw [map_add, hu, hv]; simp only [loc]; ring⟩
  neg_mem' {f} hf x i j hi hj := by
    obtain ⟨u, hu⟩ := hf x i j hi hj
    exact ⟨-u, by rw [map_neg, hu]; simp only [loc]; ring⟩

def nu (a b : ℤ) (σ : k →+* ℂ) (y : CxPts p σ) (f : X.functionField) : ℝ :=
  ‖ratVal (P.loc a b f (pick (P.L.φ σ).isLB y) (pick (P.A.φ σ).isLB y)) y‖ *
    Real.exp (-(a * (P.L.φ σ).φ (pick (P.L.φ σ).isLB y) y + b * (P.A.φ σ).φ (pick (P.A.φ σ).isLB y) y) / 2)

def Bl (a b : ℤ) (R : ℝ) : Set X.functionField :=
  {f | f ∈ P.H a b ∧ ∀ (σ : k →+* ℂ) (y : CxPts p σ), P.nu a b σ y f ≤ R}

def lc (a b : ℤ) (R : ℝ) : ℝ := Real.log ((P.Bl a b R).ncard : ℝ)

def Rep (a b : ℤ) (M : HermLB p) : Prop :=
  ∃ ρ : M.B.ι → X.functionFieldˣ, IsRatSec M.B ρ ∧
    (∀ (x : X) c i j, x ∈ M.B.U c → x ∈ P.L.B.U i → x ∈ P.A.B.U j →
      UnitAt x ((ρ c : X.functionField) / P.loc a b 1 i j)) ∧
    ∀ (σ : k →+* ℂ) (y : CxPts p σ) c i j, y ∈ ptsIn p σ (M.B.U c) → y ∈ ptsIn p σ (P.L.B.U i) →
      y ∈ ptsIn p σ (P.A.B.U j) →
      Real.log ‖ratVal ((ρ c : X.functionField) / P.loc a b 1 i j) y‖ - (M.φ σ).φ c y / 2 =
        -(a * (P.L.φ σ).φ i y + b * (P.A.φ σ).φ j y) / 2

structure Good (D : ℕ) (b : ℕ) (s t : X.functionField) : Prop where

  ample : IsAmpleLB P.A.B

  nef : P.A.IsNef D

  pos : 0 < b

  s_mem : s ∈ P.Bl 0 1 1

  s_ne : s ≠ 0

  t_mem : t ∈ P.Bl (-1) b 1

  t_ne : t ≠ 0

  reg : ∀ (x : X) i j, x ∈ P.L.B.U i → x ∈ P.A.B.U j → ∀ g : X.functionField, RegAt x g →
    RegAt x (g * P.loc (-1) b t i j / P.loc 0 1 s i j) → RegAt x (g / P.loc 0 1 s i j)

end Pair

namespace IntExample

open GlobalTheory.Points GlobalTheory.CechPic

theorem ratVal_nat {σ : k →+* ℂ} (y : CxPts p σ) (n : ℕ) : ratVal (n : X.functionField) y = n := by
  have h : genericPoint X ∈ (⊤ : X.Opens) := trivial
  have e : (n : X.functionField) = fnOf ⊤ h (n : Γ(X, ⊤)) := (map_natCast _ n).symm
  rw [e, ratVal_fnOf mem_ptsIn_top h, ev_eq mem_ptsIn_top, map_natCast]

theorem isRatSec_one : IsRatSec (LB.triv X) fun _ => 1 := by
  intro i j h
  simp [LB.triv]

def pair : Pair (𝟙 (Sp ℤ)) :=
  ⟨ArithBase.trivShift 0, ArithBase.trivShift (Real.log 3), fun _ => 1, fun _ => 1, isRatSec_one, isRatSec_one⟩

theorem isNef_trivShift (t : ℝ) (ht : 0 ≤ t) : (ArithBase.trivShift t).IsNef 0 := by
  classical
  refine (HermLB.IsArithHeight.isNef_iff ArithBase.isArithVar_int
    (ArithBase.isArithHeight_trivShift t)).2 ⟨?_, ?_⟩
  · exact (HermLB.isNef_triv (𝟙 (Sp ℤ)) 0).semiPos.shift (fun _ => t) (fun _ => rfl)
  · intro Z i _ _ _
    dsimp only
    split_ifs
    · exact ht
    · exact Real.log_natCast_nonneg _

theorem loc_eq (a b : ℤ) (f) (i j) : pair.loc a b f i j = f := by
  show f * (((1 : (Sp ℤ).functionFieldˣ)) : (Sp ℤ).functionField) ^ a *
    (((1 : (Sp ℤ).functionFieldˣ)) : (Sp ℤ).functionField) ^ b = f
  simp

private theorem pair_L_phi_apply_eq_zero (σ : ℤ →+* ℂ) (i) (y : CxPts (𝟙 (Sp ℤ)) σ) :
    (pair.L.φ σ).φ i y = 0 + 2 * 0 := rfl

private theorem pair_A_phi_apply_eq_two_log_three (σ : ℤ →+* ℂ) (i) (y : CxPts (𝟙 (Sp ℤ)) σ) :
    (pair.A.φ σ).φ i y = 0 + 2 * Real.log 3 := rfl

theorem nu_nat (a b : ℤ) (σ) (y) (n : ℕ) : pair.nu a b σ y n = n * Real.exp (-(b * Real.log 3)) := by
  simp only [Pair.nu, loc_eq, ratVal_nat, Complex.norm_natCast, pair_L_phi_apply_eq_zero, pair_A_phi_apply_eq_two_log_three]
  congr 2
  ring

theorem regAt_nat (x : Sp ℤ) (n : ℕ) : RegAt x (n : (Sp ℤ).functionField) :=
  ⟨n, map_natCast _ n⟩

theorem charZero_functionField : CharZero (Sp ℤ).functionField := by
  have h : genericPoint (Sp ℤ) ∈ (⊤ : (Sp ℤ).Opens) := trivial
  let f : ℤ →+* (Sp ℤ).functionField :=
    (fnOf ⊤ h).comp (Scheme.ΓSpecIso (CommRingCat.of ℤ)).inv.hom
  have hf : Function.Injective f := by
    intro a b hab
    have h1 := fnOf_injective ⊤ h hab
    simpa using congrArg (Scheme.ΓSpecIso (CommRingCat.of ℤ)).hom.hom h1
  exact charZero_of_injective_ringHom hf

private theorem nonempty_cxPts_spec_int : Nonempty (CxPts (𝟙 (Sp ℤ)) (Int.castRingHom ℂ)) :=
  ⟨CxPts.ofHom (p := 𝟙 (Sp ℤ)) (U := ⊤) (isAffineOpen_top (Sp ℤ))
    ((Int.castRingHom ℂ).comp (Scheme.ΓSpecIso (CommRingCat.of ℤ)).hom.hom)
    (fun a => by simp only [eq_intCast, map_intCast])⟩

theorem nat_mem_Bl_iff (a : ℤ) (n : ℕ) : (n : (Sp ℤ).functionField) ∈ pair.Bl a 1 1 ↔ n ≤ 3 := by
  have key : ∀ σ y, pair.nu a 1 σ y n = n / 3 := by
    intro σ y
    rw [nu_nat, Int.cast_one, one_mul, Real.exp_neg, Real.exp_log (by norm_num), div_eq_mul_inv]
  have hH : (n : (Sp ℤ).functionField) ∈ pair.H a 1 := fun x i j _ _ => by
    rw [loc_eq]
    exact regAt_nat x n
  constructor
  · rintro ⟨-, h⟩
    obtain ⟨y⟩ := nonempty_cxPts_spec_int
    have h1 := h (Int.castRingHom ℂ) y
    rw [key, div_le_one (by norm_num)] at h1
    exact_mod_cast h1
  · intro hn
    refine ⟨hH, fun σ y => ?_⟩
    rw [key, div_le_one (by norm_num)]
    exact_mod_cast hn

theorem good : pair.Good 0 1 (2 : ℕ) (3 : ℕ) where
  ample :=
    { isLB := LB.isLB_triv _
      compactSpace := inferInstance
      exists_affine := fun x => by
        refine ⟨1, le_rfl, powSecMk (L := LB.triv (Sp ℤ)) 1 (fun _ => 1) (fun i j => by simp [LB.triv]),
          ?_, isAffineOpen_nonzeroLocus (isLB_lbPow (LB.isLB_triv _) 1) _⟩
        erw [nonzeroLocus_powSecMk]
        simp [LB.triv, Scheme.basicOpen_of_isUnit] }
  nef := isNef_trivShift _ (Real.log_nonneg (by norm_num))
  pos := one_pos
  s_mem := (nat_mem_Bl_iff 0 2).2 (by norm_num)
  s_ne := by
    haveI := charZero_functionField
    exact Nat.cast_ne_zero.2 two_ne_zero
  t_mem := (nat_mem_Bl_iff (-1) 3).2 le_rfl
  t_ne := by
    haveI := charZero_functionField
    exact Nat.cast_ne_zero.2 (by norm_num)
  reg := by
    intro x i j _ _ g hg h
    haveI := charZero_functionField
    simp only [loc_eq] at h ⊢
    obtain ⟨u, hu⟩ := h
    obtain ⟨v, hv⟩ := hg
    refine ⟨u - v, ?_⟩
    rw [map_sub, hu, hv]
    push_cast
    ring

theorem not_good : ¬ pair.Good 0 1 (2 : ℕ) (4 : ℕ) := fun h => by
  have h1 := (nat_mem_Bl_iff (-1) 4).1 h.t_mem
  omega

private theorem trivShift_phi_apply_eq_two_mul (t : ℝ) (σ : ℤ →+* ℂ) (c) (y : CxPts (𝟙 (Sp ℤ)) σ) :
    ((ArithBase.trivShift t).φ σ).φ c y = 0 + 2 * t := rfl

theorem rep (a b : ℤ) : pair.Rep a b (ArithBase.trivShift (b * Real.log 3)) := by
  refine ⟨fun _ => 1, isRatSec_one, fun x c i j _ _ _ => ?_, fun σ y c i j _ _ _ => ?_⟩
  · rw [loc_eq]
    simpa using unitAt_one x
  · rw [loc_eq, trivShift_phi_apply_eq_two_mul, pair_L_phi_apply_eq_zero, pair_A_phi_apply_eq_two_log_three]
    have h1 : ratVal (((1 : (Sp ℤ).functionFieldˣ) : (Sp ℤ).functionField) / 1) y = 1 := by
      rw [Units.val_one, div_one, ← Nat.cast_one, ratVal_nat, Nat.cast_one]
    rw [h1, norm_one, Real.log_one]
    ring

end IntExample

end GlobalTheory.VolBr
