import Mathlib
import GroundTheory.AutomorphicForms.StrongApproximationSLDoubleCoset
import GroundTheory.GlobalFields.IdeleGroups.Rational
import GroundTheory.GlobalFields.Adele.Discrete

open NumberField IsDedekindDomain Topology Filter Set Matrix
open GroundTheory.Global GroundTheory.Global.IdeleGroup

namespace GroundTheory.Automorphic

noncomputable section

namespace GL2Classical

open AdelicGLn

set_option linter.unusedSectionVars false

local notation "𝔸f" => FiniteAdeleRing (𝓞 ℚ) ℚ

theorem exists_int_of_mem_integralFiniteAdeles {x : ℚ}
    (hx : algebraMap ℚ 𝔸f x ∈ integralFiniteAdeles (𝓞 ℚ) ℚ) : ∃ m : ℤ, x = m := by
  obtain ⟨z, hz⟩ := exists_eq_of_forall_mem_adicCompletionIntegers ℚ x fun v => hx v
  refine ⟨Rat.ringOfIntegersEquiv z, ?_⟩
  rw [Rat.ringOfIntegersEquiv_apply_coe, ← hz]

theorem intCast_mem_integralFiniteAdeles (m : ℤ) :
    (m : 𝔸f) ∈ integralFiniteAdeles (𝓞 ℚ) ℚ :=
  intCast_mem _ m

def levelIdeal (N : ℕ) : Set 𝔸f :=
  {x | ∃ t ∈ integralFiniteAdeles (𝓞 ℚ) ℚ, x = (N : 𝔸f) * t}

def levelUnit (N : ℕ) [NeZero N] : 𝔸fˣ :=
  FiniteAdeleRing.unitEmbedding (𝓞 ℚ) ℚ (Units.mk0 (N : ℚ) (Nat.cast_ne_zero.2 (NeZero.ne N)))

theorem coe_levelUnit (N : ℕ) [NeZero N] : (levelUnit N : 𝔸f) = N := by
  rw [levelUnit, FiniteAdeleRing.unitEmbedding_apply, Units.val_mk0, map_natCast]

theorem mem_levelIdeal_iff (N : ℕ) [NeZero N] (x : 𝔸f) :
    x ∈ levelIdeal N ↔ ((levelUnit N)⁻¹ : 𝔸fˣ) * x ∈ integralFiniteAdeles (𝓞 ℚ) ℚ := by
  constructor
  · rintro ⟨t, ht, rfl⟩
    rwa [← coe_levelUnit N, ← mul_assoc, Units.inv_mul, one_mul]
  · intro h
    refine ⟨_, h, ?_⟩
    rw [← coe_levelUnit N, ← mul_assoc, Units.mul_inv, one_mul]

theorem isOpen_levelIdeal (N : ℕ) [NeZero N] : IsOpen (levelIdeal N) := by
  have : levelIdeal N = (fun x : 𝔸f => ((levelUnit N)⁻¹ : 𝔸fˣ) * x) ⁻¹'
      (integralFiniteAdeles (𝓞 ℚ) ℚ : Set 𝔸f) := by
    ext x
    exact mem_levelIdeal_iff N x
  rw [this]
  exact isOpen_integralFiniteAdeles.preimage (continuous_const.mul continuous_id)

theorem zero_mem_levelIdeal (N : ℕ) : (0 : 𝔸f) ∈ levelIdeal N :=
  ⟨0, zero_mem _, by rw [mul_zero]⟩

theorem mul_add_mul_mem_levelIdeal {N : ℕ} {a b x y : 𝔸f}
    (ha : a ∈ integralFiniteAdeles (𝓞 ℚ) ℚ) (hb : b ∈ integralFiniteAdeles (𝓞 ℚ) ℚ)
    (hx : x ∈ levelIdeal N) (hy : y ∈ levelIdeal N) : a * x + b * y ∈ levelIdeal N := by
  obtain ⟨s, hs, rfl⟩ := hx
  obtain ⟨t, ht, rfl⟩ := hy
  exact ⟨a * s + b * t, add_mem (mul_mem ha hs) (mul_mem hb ht), by ring⟩

theorem mul_mem_levelIdeal {N : ℕ} {a x : 𝔸f}
    (ha : a ∈ integralFiniteAdeles (𝓞 ℚ) ℚ) (hx : x ∈ levelIdeal N) : a * x ∈ levelIdeal N := by
  simpa using mul_add_mul_mem_levelIdeal ha (zero_mem _) hx (zero_mem_levelIdeal N)

theorem exists_int_of_mem_levelIdeal (N : ℕ) [NeZero N] {x : ℚ}
    (hx : algebraMap ℚ 𝔸f x ∈ levelIdeal N) : ∃ m : ℤ, x = N * m := by
  rw [mem_levelIdeal_iff] at hx
  have hN : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  have : (((levelUnit N)⁻¹ : 𝔸fˣ) : 𝔸f) * algebraMap ℚ 𝔸f x = algebraMap ℚ 𝔸f (x / N) := by
    rw [levelUnit, ← map_inv, FiniteAdeleRing.unitEmbedding_apply, ← map_mul, Units.val_inv_eq_inv_val,
      Units.val_mk0, div_eq_mul_inv, mul_comm]
  rw [this] at hx
  obtain ⟨m, hm⟩ := exists_int_of_mem_integralFiniteAdeles hx
  refine ⟨m, ?_⟩
  rw [← hm]
  field_simp

variable (N : ℕ) [NeZero N]

def Gamma0Level : Subgroup (FiniteAdelicGL ℚ 2) where
  carrier := {g | g ∈ integralFiniteGL ℚ 2 ∧ (g : Matrix (Fin 2) (Fin 2) 𝔸f) 1 0 ∈ levelIdeal N}
  one_mem' := ⟨one_mem _, by simpa using zero_mem_levelIdeal N⟩
  mul_mem' {g h} hg hh := by
    refine ⟨mul_mem hg.1 hh.1, ?_⟩
    have hgi := ((mem_integralFiniteGL_iff ℚ 2).1 hg.1).1
    have hhi := ((mem_integralFiniteGL_iff ℚ 2).1 hh.1).1
    rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]
    rw [show (g : Matrix (Fin 2) (Fin 2) 𝔸f) 1 1 * (h : Matrix (Fin 2) (Fin 2) 𝔸f) 1 0 =
        (g : Matrix (Fin 2) (Fin 2) 𝔸f) 1 1 * (h : Matrix (Fin 2) (Fin 2) 𝔸f) 1 0 from rfl]
    exact mul_add_mul_mem_levelIdeal (hhi 0 0) (hgi 1 1) hg.2 hh.2
  inv_mem' {g} hg := by
    refine ⟨inv_mem hg.1, ?_⟩
    have hdet : ((Matrix.GeneralLinearGroup.det g)⁻¹ : 𝔸fˣ).val ∈ integralFiniteAdeles (𝓞 ℚ) ℚ := by
      have h2 := ((mem_integralFiniteGL_iff ℚ 2).1 hg.1).2
      have := det_mem_of_forall_mem (integralFiniteAdeles (𝓞 ℚ) ℚ) h2
      rwa [← Matrix.GeneralLinearGroup.val_det_apply, map_inv] at this
    have hinv : ((g⁻¹ : FiniteAdelicGL ℚ 2) : Matrix (Fin 2) (Fin 2) 𝔸f) 1 0 =
        ((Matrix.GeneralLinearGroup.det g)⁻¹ : 𝔸fˣ).val *
          (-(g : Matrix (Fin 2) (Fin 2) 𝔸f) 1 0) := by
      rw [Matrix.coe_units_inv, Matrix.inv_def, Matrix.adjugate_fin_two,
        ← Matrix.GeneralLinearGroup.val_det_apply, Ring.inverse_unit]
      simp
    rw [hinv]
    refine mul_mem_levelIdeal hdet ?_
    obtain ⟨t, ht, h⟩ := hg.2
    exact ⟨-t, neg_mem ht, by rw [h, mul_neg]⟩

theorem mem_Gamma0Level {g : FiniteAdelicGL ℚ 2} :
    g ∈ Gamma0Level N ↔
      g ∈ integralFiniteGL ℚ 2 ∧ (g : Matrix (Fin 2) (Fin 2) 𝔸f) 1 0 ∈ levelIdeal N :=
  Iff.rfl

theorem Gamma0Level_le_integralFiniteGL : Gamma0Level N ≤ integralFiniteGL ℚ 2 := fun _ h => h.1

theorem isOpen_Gamma0Level : IsOpen (Gamma0Level N : Set (FiniteAdelicGL ℚ 2)) := by
  have : (Gamma0Level N : Set (FiniteAdelicGL ℚ 2)) = (integralFiniteGL ℚ 2 : Set _) ∩
      (fun g : FiniteAdelicGL ℚ 2 => (g : Matrix (Fin 2) (Fin 2) 𝔸f) 1 0) ⁻¹' levelIdeal N := rfl
  rw [this]
  exact (isOpen_integralFiniteGL ℚ 2).inter ((isOpen_levelIdeal N).preimage
    ((Units.continuous_val (M := Matrix (Fin 2) (Fin 2) 𝔸f)).matrix_elem 1 0))

theorem Gamma0Level_one : Gamma0Level 1 = integralFiniteGL ℚ 2 := by
  refine le_antisymm (Gamma0Level_le_integralFiniteGL 1) fun g hg => ⟨hg, ?_⟩
  exact ⟨_, ((mem_integralFiniteGL_iff ℚ 2).1 hg).1 1 0, by rw [Nat.cast_one, one_mul]⟩

theorem diagonalGL_mem_Gamma0Level {a : 𝔸fˣ} (ha : a ∈ finiteLevel 0) :
    diagonalGL (Pi.mulSingle (0 : Fin 2) a) ∈ Gamma0Level N := by
  rw [mem_finiteLevel] at ha
  have hv : ∀ v, (a : 𝔸f) v ∈ v.adicCompletionIntegers ℚ ∧
      ((a⁻¹ : 𝔸fˣ) : 𝔸f) v ∈ v.adicCompletionIntegers ℚ := by
    intro v
    have := ha v
    rw [Pi.zero_apply, unitsLevel_zero, Submonoid.mem_units_iff] at this
    refine ⟨this.1, ?_⟩
    have h := this.2
    rwa [← map_inv] at h
  have key : ∀ b : 𝔸fˣ, (∀ v, (b : 𝔸f) v ∈ v.adicCompletionIntegers ℚ) →
      ∀ i j, ((diagonalGL (Pi.mulSingle (0 : Fin 2) b) : FiniteAdelicGL ℚ 2) :
        Matrix (Fin 2) (Fin 2) 𝔸f) i j ∈ integralFiniteAdeles (𝓞 ℚ) ℚ := by
    intro b hb i j
    rw [coe_diagonalGL, Matrix.diagonal_apply]
    split_ifs with hij
    · rw [Pi.mulSingle_apply]
      split_ifs
      · exact hb
      · exact one_mem _
    · exact zero_mem _
  refine ⟨?_, ?_⟩
  · rw [mem_integralFiniteGL_iff, ← map_inv]
    refine ⟨key a fun v => (hv v).1, ?_⟩
    rw [← Pi.mulSingle_inv]
    exact key a⁻¹ fun v => (hv v).2
  · rw [coe_diagonalGL, Matrix.diagonal_apply_ne _ (by decide)]
    exact zero_mem_levelIdeal N

theorem finiteLevel_le_map_det :
    finiteLevel 0 ≤ (Gamma0Level N).map
      (Matrix.GeneralLinearGroup.det : FiniteAdelicGL ℚ 2 →* 𝔸fˣ) := fun a ha =>
  ⟨_, diagonalGL_mem_Gamma0Level N ha, det_diagonalGL_mulSingle (n := 2) two_pos a⟩

theorem unitEmbedding_range_sup_finiteLevel :
    (FiniteAdeleRing.unitEmbedding (𝓞 ℚ) ℚ).range ⊔ finiteLevel 0 = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have := RationalIdeles.subsingleton_classGroup
  have h := (finiteQuotientEquivClassGroup ℚ).injective
    (Subsingleton.elim ((finiteQuotientEquivClassGroup ℚ) (QuotientGroup.mk x))
      ((finiteQuotientEquivClassGroup ℚ) 1))
  rwa [QuotientGroup.eq_one_iff] at h

theorem detClassSubgroup_Gamma0Level : detClassSubgroup ℚ 2 (Gamma0Level N) = ⊤ := by
  rw [eq_top_iff, ← unitEmbedding_range_sup_finiteLevel]
  exact sup_le le_sup_left ((finiteLevel_le_map_det N).trans le_sup_right)

theorem exists_eq_finiteDiagonal_mul (g : FiniteAdelicGL ℚ 2) :
    ∃ γ : GL (Fin 2) ℚ, ∃ u ∈ Gamma0Level N, g = finiteDiagonal ℚ 2 γ * u := by
  obtain ⟨γ, u, hu, h⟩ := exists_eq_finiteDiagonal_mul_mul (K := ℚ) (n := 2) two_pos
    (isOpen_Gamma0Level N) (g := 1) (g' := g)
    (by rw [detClassSubgroup_Gamma0Level]; exact Subgroup.mem_top _)
  exact ⟨γ, u, hu, by rw [h, mul_one]⟩

theorem exists_int_entries {γ : GL (Fin 2) ℚ} (h : finiteDiagonal ℚ 2 γ ∈ Gamma0Level N) :
    ∃ A : Matrix (Fin 2) (Fin 2) ℤ, ∀ i j, (A i j : ℚ) = γ i j := by
  have hi := ((mem_integralFiniteGL_iff ℚ 2).1 h.1).1
  choose A hA using fun i j => exists_int_of_mem_integralFiniteAdeles (hi i j)
  exact ⟨Matrix.of A, fun i j => (hA i j).symm⟩

theorem exists_int_of_finiteDiagonal_mem {γ : GL (Fin 2) ℚ}
    (h : finiteDiagonal ℚ 2 γ ∈ Gamma0Level N) :
    ∃ A : Matrix (Fin 2) (Fin 2) ℤ, (∀ i j, (A i j : ℚ) = γ i j) ∧ (N : ℤ) ∣ A 1 0 ∧
      (A.det = 1 ∨ A.det = -1) := by
  obtain ⟨A, hA⟩ := exists_int_entries N h
  obtain ⟨B, hB⟩ := exists_int_entries N (γ := γ⁻¹) (by rw [map_inv]; exact inv_mem h)
  refine ⟨A, hA, ?_, ?_⟩
  · obtain ⟨m, hm⟩ := exists_int_of_mem_levelIdeal N (x := γ 1 0) h.2
    refine ⟨m, ?_⟩
    have := hA 1 0
    rw [hm] at this
    exact_mod_cast this
  · have hAB : A * B = 1 := by
      have hmap : (Int.castRingHom ℚ).mapMatrix (A * B) = (Int.castRingHom ℚ).mapMatrix 1 := by
        rw [map_mul, map_one]
        have e1 : (Int.castRingHom ℚ).mapMatrix A = (γ : Matrix (Fin 2) (Fin 2) ℚ) := by
          ext i j; exact hA i j
        have e2 : (Int.castRingHom ℚ).mapMatrix B = ((γ⁻¹ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) := by
          ext i j; exact hB i j
        rw [e1, e2, Units.mul_inv]
      exact Matrix.ext fun i j => Int.cast_injective (α := ℚ)
        (show (((A * B) i j : ℤ) : ℚ) = (((1 : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : ℚ) from
          congrFun (congrFun hmap i) j)
    have hdet : A.det * B.det = 1 := by rw [← Matrix.det_mul, hAB, Matrix.det_one]
    exact Int.eq_one_or_neg_one_of_mul_eq_one hdet

end GL2Classical

end

end GroundTheory.Automorphic
