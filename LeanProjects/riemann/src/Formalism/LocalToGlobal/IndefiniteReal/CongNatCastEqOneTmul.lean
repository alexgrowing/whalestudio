import Formalism.LocalToGlobal.IndefiniteReal.PrincipalLevelFrame
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Levelaf

noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct

namespace Formalism.IndefR.principalLevelFrame

section Cong

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

local notation3 "L⁺" => NumberField.maximalRealSubfield L

theorem cong_natCast_eq_tmul_one (k : ℕ) : (k : ReciprocityTheory.Aut.AL L) = (k : L) ⊗ₜ[L⁺] (1 : ReciprocityTheory.Aut.AFplus L) := by
  rw [← Algebra.TensorProduct.includeLeftRingHom_apply, map_natCast]

theorem cong_natCast_eq_one_tmul (k : ℕ) : (k : ReciprocityTheory.Aut.AL L) = (1 : L) ⊗ₜ[L⁺] (k : ReciprocityTheory.Aut.AFplus L) := by
  rw [← Algebra.TensorProduct.includeRight_apply, map_natCast]

theorem cong_adele_nat_denom (a : ReciprocityTheory.Aut.AFplus L) :
    ∃ k : ℕ, 0 < k ∧ ∀ v, ((k : ReciprocityTheory.Aut.AFplus L) * a) v ∈ v.adicCompletionIntegers L⁺ := by
  obtain ⟨d, hd0, hd⟩ := Formalism.UG.P.levelaf_adele_denom (F := L⁺) a
  set k := Ideal.absNorm (Ideal.span {d}) with hk
  have hk0 : k ≠ 0 := by
    rw [hk, Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact hd0
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {d}))
  refine ⟨k, Nat.pos_of_ne_zero hk0, ?_⟩
  have e : (k : ReciprocityTheory.Aut.AFplus L) * a =
      algebraMap (𝓞 L⁺) (ReciprocityTheory.Aut.AFplus L) c * (algebraMap (𝓞 L⁺) (ReciprocityTheory.Aut.AFplus L) d * a) := by
    rw [← mul_assoc, ← map_mul, hc, map_natCast]
  have hm : (k : ReciprocityTheory.Aut.AFplus L) * a ∈ Formalism.UG.intAd L⁺ := by
    rw [e]
    exact Subring.mul_mem _ (Formalism.UG.P.levelaf_int_mem c) hd
  exact hm

theorem cong_nat_denom (x : ReciprocityTheory.Aut.AL L) : ∃ d : ℕ, 0 < d ∧ (d : ReciprocityTheory.Aut.AL L) * x ∈ ReciprocityTheory.Aut.ALint L := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨1, one_pos, by rw [mul_zero]; exact Subring.zero_mem _⟩
  | tmul l a =>
    have halg : Algebra.IsAlgebraic ℤ L :=
      (IsFractionRing.comap_isAlgebraic_iff (A := ℤ) (K := ℚ)).2 inferInstance
    obtain ⟨m, hm0, hm⟩ := (halg.1 l).exists_integral_multiple
    obtain ⟨k, hk0, hk⟩ := cong_adele_nat_denom a
    refine ⟨m.natAbs * k, Nat.mul_pos (Int.natAbs_pos.2 hm0) hk0, ?_⟩
    have hint : IsIntegral ℤ ((m.natAbs : L) * l) := by
      have e : (m.natAbs : L) * l = ((m.sign : ℤ) : L) * (m • l) := by
        rw [zsmul_eq_mul, ← mul_assoc, ← Int.cast_mul, ← Int.cast_natCast, Int.sign_mul_self_eq_natAbs]
      rw [e]
      exact IsIntegral.mul isIntegral_algebraMap hm
    have e2 : ((m.natAbs * k : ℕ) : ReciprocityTheory.Aut.AL L) * (l ⊗ₜ[L⁺] a) =
        (((m.natAbs : L) * l) ⊗ₜ[L⁺] (1 : ReciprocityTheory.Aut.AFplus L)) *
          ((1 : L) ⊗ₜ[L⁺] ((k : ReciprocityTheory.Aut.AFplus L) * a)) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, Nat.cast_mul, cong_natCast_eq_tmul_one m.natAbs,
        cong_natCast_eq_one_tmul k, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
        Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    rw [e2]
    refine Subring.mul_mem _ (Subring.subset_closure (Or.inl ⟨⟨_, hint⟩, rfl⟩))
      (Subring.subset_closure (Or.inr ⟨_, hk, rfl⟩))
  | add x y hx hy =>
    obtain ⟨dx, hx0, hx⟩ := hx
    obtain ⟨dy, hy0, hy⟩ := hy
    refine ⟨dx * dy, Nat.mul_pos hx0 hy0, ?_⟩
    have e : ((dx * dy : ℕ) : ReciprocityTheory.Aut.AL L) * (x + y) =
        (dy : ReciprocityTheory.Aut.AL L) * ((dx : ReciprocityTheory.Aut.AL L) * x) + (dx : ReciprocityTheory.Aut.AL L) * ((dy : ReciprocityTheory.Aut.AL L) * y) := by
      push_cast; ring
    rw [e]
    exact Subring.add_mem _ (Subring.mul_mem _ (natCast_mem _ _) hx) (Subring.mul_mem _ (natCast_mem _ _) hy)

theorem cong_dvd_mem {x : ReciprocityTheory.Aut.AL L} {d e : ℕ} (hx : (d : ReciprocityTheory.Aut.AL L) * x ∈ ReciprocityTheory.Aut.ALint L) (hde : d ∣ e) :
    (e : ReciprocityTheory.Aut.AL L) * x ∈ ReciprocityTheory.Aut.ALint L := by
  obtain ⟨c, rfl⟩ := hde
  rw [Nat.cast_mul, mul_comm (d : ReciprocityTheory.Aut.AL L), mul_assoc]
  exact Subring.mul_mem _ (natCast_mem _ _) hx

end Cong

theorem congConj_holds (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) : CongConj L n := by
  classical
  intro h N hN
  choose D hD0 hD using fun x : ReciprocityTheory.Aut.AL L => cong_nat_denom (L := L) x
  set H : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL L) := (h.1 : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL L)) with hH
  set Hi : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL L) :=
    ((h⁻¹ : Formalism.AUTREP.GAf L n).1 : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL L)) with hHi
  set d : ℕ := ∏ i, ∏ j, (D (H i j) * D (Hi i j)) with hd
  have hd0 : 0 < d := Finset.prod_pos fun i _ => Finset.prod_pos fun j _ => Nat.mul_pos (hD0 _) (hD0 _)
  have hdv : ∀ i j, D (H i j) * D (Hi i j) ∣ d := fun i j =>
    dvd_trans (Finset.dvd_prod_of_mem (fun j => D (H i j) * D (Hi i j)) (Finset.mem_univ j))
      (Finset.dvd_prod_of_mem (fun i => ∏ j, D (H i j) * D (Hi i j)) (Finset.mem_univ i))
  have hHd : ∀ i j, (d : ReciprocityTheory.Aut.AL L) * H i j ∈ ReciprocityTheory.Aut.ALint L := fun i j =>
    cong_dvd_mem (hD _) (dvd_trans (dvd_mul_right _ _) (hdv i j))
  have hHid : ∀ i j, (d : ReciprocityTheory.Aut.AL L) * Hi i j ∈ ReciprocityTheory.Aut.ALint L := fun i j =>
    cong_dvd_mem (hD _) (dvd_trans (dvd_mul_left _ _) (hdv i j))
  refine ⟨N * d * d, Nat.mul_pos (Nat.mul_pos hN hd0) hd0, ?_⟩
  intro κ hκ
  choose Y hYm hYe using hκ.2
  set K : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL L) := (κ.1 : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL L)) with hK
  have hprod : ((h⁻¹ * κ * h : Formalism.AUTREP.GAf L n).1 : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL L)) = Hi * K * H := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul]
  have hHiH : Hi * H = 1 := by
    rw [hHi, hH, ← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, Units.val_one]
  have hKY : K - 1 = ((N * d * d : ℕ) : ReciprocityTheory.Aut.AL L) • Matrix.of Y := by
    ext k l
    rw [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    exact hYe k l
  set Z : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL L) :=
    ((d : ReciprocityTheory.Aut.AL L) • Hi) * Matrix.of Y * ((d : ReciprocityTheory.Aut.AL L) • H) with hZ
  have hZm : ∀ i j, Z i j ∈ ReciprocityTheory.Aut.ALint L := by
    intro i j
    simp only [hZ, Matrix.mul_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    exact Subring.sum_mem _ fun l _ => Subring.mul_mem _
      (Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hHid i k) (hYm k l)) (hHd l j)
  have hmain : Hi * K * H - 1 = (N : ReciprocityTheory.Aut.AL L) • Z := by
    have e1 : Hi * K * H - 1 = Hi * (K - 1) * H := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hHiH]
    rw [e1, hKY, hZ, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, smul_smul]
    congr 1
    push_cast
    ring
  have hentry : ∀ i j, (Hi * K * H) i j - (1 : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL L)) i j =
      (N : ReciprocityTheory.Aut.AL L) * Z i j := by
    intro i j
    rw [← Matrix.sub_apply, hmain, Matrix.smul_apply, smul_eq_mul]
  refine ⟨fun i j => ?_, fun i j => ⟨Z i j, hZm i j, by rw [hprod]; exact hentry i j⟩⟩
  show ((h⁻¹ * κ * h : Formalism.AUTREP.GAf L n).1 : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL L)) i j ∈ ReciprocityTheory.Aut.ALint L
  rw [hprod]
  have e : (Hi * K * H) i j = (1 : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL L)) i j + (N : ReciprocityTheory.Aut.AL L) * Z i j := by
    rw [← hentry i j]; ring
  rw [e, Matrix.one_apply]
  refine Subring.add_mem _ ?_ (Subring.mul_mem _ (natCast_mem _ _) (hZm i j))
  split_ifs
  · exact Subring.one_mem _
  · exact Subring.zero_mem _

end Formalism.IndefR.principalLevelFrame
