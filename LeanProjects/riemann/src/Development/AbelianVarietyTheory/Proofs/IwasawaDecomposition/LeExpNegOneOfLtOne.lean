import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DatVtEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FramesStdMatched
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteImageHeckeSetSplitPlaceCosets
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.MtIn
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TSetDenom

open GlobalTheory.TSetFinCong (IntM)

section Local

variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} {n : ℕ}

theorem le_exp_neg_one_of_lt_one {x : WithZero (Multiplicative ℤ)} (hx : x < 1) : x ≤ WithZero.exp (-1) := by
  by_cases h0 : x = 0
  · rw [h0]; exact zero_le'
  · rw [← WithZero.exp_log h0] at hx ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hx
    rw [WithZero.exp_le_exp]
    omega

theorem int_of_double_coset (ϖ : v.adicCompletion F) (k : ℕ) (hϖ : Valued.v ϖ ≤ 1)
    (a b g : GL (Fin n) (v.adicCompletion F))
    (ha : a ∈ Formalism.UG.GLint (Fin n) (v.adicCompletionIntegers F).toSubring)
    (hb : b ∈ Formalism.UG.GLint (Fin n) (v.adicCompletionIntegers F).toSubring)
    (hg : (g : Matrix (Fin n) (Fin n) (v.adicCompletion F)) =
      (a : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * Formalism.UG.diagJ n ϖ k * (b : Matrix (Fin n) (Fin n) (v.adicCompletion F))) :
    (∀ i j, Valued.v ((g : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j) ≤ 1) ∧
      ∀ i j, Valued.v (ϖ * ((g⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j) ≤ 1 := by
  obtain ⟨ia, ia'⟩ := GlobalTheory.TSetFin.glint_int ha
  obtain ⟨ib, ib'⟩ := GlobalTheory.TSetFin.glint_int hb
  set D := Formalism.UG.diagJ n ϖ k
  let D' : Matrix (Fin n) (Fin n) (v.adicCompletion F) := Matrix.diagonal fun i => if (i : ℕ) < k then 1 else ϖ
  have hDD : D' * D = ϖ • (1 : Matrix (Fin n) (Fin n) (v.adicCompletion F)) := by
    simp only [D', D, Formalism.UG.diagJ, Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases h : i = j
    · subst h; simp only [Matrix.diagonal_apply_eq, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
      split_ifs <;> simp
    · simp [Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]
  have hD : IntM D := GlobalTheory.TSetFinCong.IntM.diagonal fun i => by
    show Valued.v (if (i : ℕ) < k then ϖ else 1) ≤ 1
    split_ifs <;> simp [hϖ]
  have hD' : IntM D' := GlobalTheory.TSetFinCong.IntM.diagonal fun i => by
    show Valued.v (if (i : ℕ) < k then 1 else ϖ) ≤ 1
    split_ifs <;> simp [hϖ]
  have haa : ((a⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * a = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hbb : ((b⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * b = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hgg : (g : Matrix (Fin n) (Fin n) (v.adicCompletion F)) *
      ((g⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hgi : ϖ • ((g⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) =
      ((b⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * D' *
        ((a⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) := by
    have h1 : ((b⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * D' *
        ((a⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * g = ϖ • 1 := by
      rw [hg]
      calc _ = ((b⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * (D' *
            ((((a⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * a) * D)) * b := by
            simp only [Matrix.mul_assoc]
        _ = ϖ • 1 := by rw [haa, Matrix.one_mul, hDD, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hbb]
    calc ϖ • ((g⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F))
        = (ϖ • 1) * ((g⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) := by
          rw [Matrix.smul_mul, Matrix.one_mul]
      _ = _ := by rw [← h1, Matrix.mul_assoc _ (g : Matrix (Fin n) (Fin n) (v.adicCompletion F)), hgg, Matrix.mul_one]
  refine ⟨?_, fun i j => ?_⟩
  · rw [hg]; exact GlobalTheory.TSetFinCong.IntM.mul (GlobalTheory.TSetFinCong.IntM.mul (show IntM _ from ia) hD) (show IntM _ from ib)
  · have h := GlobalTheory.TSetFinCong.IntM.mul (GlobalTheory.TSetFinCong.IntM.mul (show IntM _ from ib') hD') (show IntM _ from ia') i j
    rw [← hgi, Matrix.smul_apply, smul_eq_mul] at h
    exact h

theorem exists_char (v : HeightOneSpectrum (𝓞 F)) :
    ∃ p : ℕ, p.Prime ∧ ((p : 𝓞 F) ∈ v.asIdeal) ∧ ∃ a : ℕ, Nat.card (𝓞 F ⧸ v.asIdeal) = p ^ a := by
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field _
  haveI : Finite (𝓞 F ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot
  letI := Fintype.ofFinite (𝓞 F ⧸ v.asIdeal)
  obtain ⟨a, hp, hcard⟩ := FiniteField.card (𝓞 F ⧸ v.asIdeal) (ringChar (𝓞 F ⧸ v.asIdeal))
  refine ⟨ringChar (𝓞 F ⧸ v.asIdeal), hp, ?_, a, by rw [Nat.card_eq_fintype_card, hcard]⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact ringChar.Nat.cast_ringChar

end Local

section Glob

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

open ReciprocityTheory.Aut

local notation3 "L⁺" => maximalRealSubfield L

theorem conj_entry (x : GA L n) (i j : Fin n) :
    conjAL L ((x.1 : Matrix (Fin n) (Fin n) (AL L)) i j) =
      (((x⁻¹ : GA L n).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) j i := by
  have hm := x.2
  simp only [ReciprocityTheory.Aut.GA, ReciprocityTheory.Aut.UGroup, Subgroup.mem_mk] at hm
  have h1 : ((x.1⁻¹ : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) = conjT (conjAL L) x.1 :=
    Units.inv_eq_of_mul_eq_one_right hm
  simp only [InvMemClass.coe_inv, h1, conjT, Matrix.transpose_apply, Matrix.map_apply]

theorem natCast_mul_mem (s : SplitPlace L) (c : ℕ) (x : GA L n) (hx : TrivOutside {s.v} x)
    (h1 : ∀ i j, Valued.v ((c : s.v.adicCompletion L⁺) *
      ((s.loc n x : GL (Fin n) (s.v.adicCompletion L⁺)) : Matrix (Fin n) (Fin n) (s.v.adicCompletion L⁺)) i j) ≤ 1)
    (h2 : ∀ i j, Valued.v ((c : s.v.adicCompletion L⁺) *
      ((s.loc n x⁻¹ : GL (Fin n) (s.v.adicCompletion L⁺)) : Matrix (Fin n) (Fin n) (s.v.adicCompletion L⁺)) i j) ≤ 1)
    (i j : Fin n) : (c : AL L) * (x.1 : Matrix (Fin n) (Fin n) (AL L)) i j ∈ ALint L := by
  obtain ⟨e, he, he'⟩ := GlobalTheory.SplitSep.exists_sep L s
  have hc1 : Valued.v (c : s.v.adicCompletion L⁺) ≤ 1 := GlobalTheory.TSetFinCong.natCast_le_one s.v c
  have hone : ∀ i j, s.proj ((1 : Matrix (Fin n) (Fin n) (AL L)) i j) =
      (1 : Matrix (Fin n) (Fin n) (s.v.adicCompletion L⁺)) i j := by
    intro i j; by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  have hconj1 : conjAL L ((1 : Matrix (Fin n) (Fin n) (AL L)) i j) = (1 : Matrix (Fin n) (Fin n) (AL L)) j i := by
    by_cases hij : i = j
    · subst hij; simp
    · simp [Matrix.one_apply_ne hij, Matrix.one_apply_ne (Ne.symm hij)]
  have hdel : ∀ i j, Valued.v ((c : s.v.adicCompletion L⁺) * (1 : Matrix (Fin n) (Fin n) (s.v.adicCompletion L⁺)) i j) ≤ 1 := by
    intro i j; rw [Valuation.map_mul]; refine mul_le_one' hc1 ?_; by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  have hz : (c : AL L) * (x.1 : Matrix (Fin n) (Fin n) (AL L)) i j - (c : AL L) * (1 : Matrix (Fin n) (Fin n) (AL L)) i j ∈ ALint L := by
    apply GlobalTheory.TSetFin.mem_ALint_of_local s e he he'
    · intro w hw
      have := congrFun (congrFun (hx w (by simpa using hw)) i) j
      simp only [Matrix.map_apply] at this
      rw [map_sub, map_mul, map_mul, this]
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
    · rw [map_sub, map_mul, map_mul, map_natCast, hone]
      exact (Valuation.map_sub _ _ _).trans (max_le (h1 i j) (hdel i j))
    · rw [map_sub, map_mul, map_mul, map_natCast, conj_entry x i j, hconj1, map_sub, map_mul, map_mul, map_natCast, hone]
      exact (Valuation.map_sub _ _ _).trans (max_le (h2 j i) (hdel j i))
  have hd : (c : AL L) * (1 : Matrix (Fin n) (Fin n) (AL L)) i j ∈ ALint L :=
    Subring.mul_mem _ (natCast_mem (ALint L) c)
      (by by_cases hij : i = j <;> simp [Matrix.one_apply, hij, Subring.one_mem, Subring.zero_mem])
  simpa using add_mem hz hd

theorem tSet_denom (s : SplitPlace L) (ϖ : s.v.adicCompletion L⁺) (k : ℕ) (hϖ : Formalism.AUTREP.IsUnif L s.v ϖ)
    (p : ℕ) (hp : ((p : ℕ) : 𝓞 L⁺) ∈ s.v.asIdeal) (x : Formalism.AUTREP.GAf L n) (hx : x ∈ Formalism.AUTREP.tSet L n s ϖ k)
    (i j : Fin n) :
    (p : AL L) * (x.1 : Matrix (Fin n) (Fin n) (AL L)) i j ∈ ALint L ∧
      (p : AL L) * (((x⁻¹ : GA L n).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) i j ∈ ALint L := by
  obtain ⟨htriv, a, ha, b, hb, hg⟩ := hx
  have hunif : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hϖ
  have hϖ1 : Valued.v ϖ ≤ 1 := by
    rw [hunif, ← WithZero.exp_zero, WithZero.exp_le_exp]; norm_num
  have hϖ0 : ϖ ≠ 0 := by
    intro h; rw [h, Valuation.map_zero] at hunif; exact WithZero.coe_ne_zero hunif.symm
  obtain ⟨h1, h2⟩ := int_of_double_coset ϖ k hϖ1 a b _ ha hb hg
  have hpv : Valued.v (p : s.v.adicCompletion L⁺) ≤ WithZero.exp (-1) := by
    refine le_exp_neg_one_of_lt_one ?_
    have e : (p : s.v.adicCompletion L⁺) = algebraMap L⁺ (s.v.adicCompletion L⁺) (((p : ℕ) : 𝓞 L⁺) : L⁺) := by simp
    rw [e, adic_valued_algebraMap]
    exact (s.v.valuation_lt_one_iff_mem (K := L⁺) _).2 hp
  have ht : Valued.v ((p : s.v.adicCompletion L⁺) / ϖ) ≤ 1 := by
    rw [map_div₀, hunif]; exact div_le_one_of_le₀ hpv zero_le'
  have hpe : (p : s.v.adicCompletion L⁺) = (p : s.v.adicCompletion L⁺) / ϖ * ϖ := (div_mul_cancel₀ _ hϖ0).symm
  have hc1 : Valued.v (p : s.v.adicCompletion L⁺) ≤ 1 := GlobalTheory.TSetFinCong.natCast_le_one s.v p
  have A1 : ∀ i j, Valued.v ((p : s.v.adicCompletion L⁺) *
      ((s.loc n x : GL (Fin n) (s.v.adicCompletion L⁺)) : Matrix (Fin n) (Fin n) (s.v.adicCompletion L⁺)) i j) ≤ 1 :=
    fun i j => by rw [Valuation.map_mul]; exact mul_le_one' hc1 (h1 i j)
  have A2 : ∀ i j, Valued.v ((p : s.v.adicCompletion L⁺) *
      ((s.loc n x⁻¹ : GL (Fin n) (s.v.adicCompletion L⁺)) : Matrix (Fin n) (Fin n) (s.v.adicCompletion L⁺)) i j) ≤ 1 :=
    fun i j => by
      rw [map_inv, hpe, mul_assoc, Valuation.map_mul]; exact mul_le_one' ht (h2 i j)
  exact ⟨natCast_mul_mem s p x htriv A1 A2 i j,
    natCast_mul_mem s p x⁻¹ (GlobalTheory.TSetFin.triv_inv htriv) A2 (fun i j => by rw [inv_inv]; exact A1 i j) i j⟩

end Glob

theorem tSet_denominator : ∀ (D : D7) (n : ℕ) (s : ReciprocityTheory.Aut.SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)) (k : ℕ), Formalism.AUTREP.IsUnif D.host.E s.v ϖ → ∃ p : ℕ, p.Prime ∧ s.Above p ∧ (∃ a, s.q = p ^ a) ∧ ∀ x ∈ Formalism.AUTREP.tSet D.host.E n s ϖ k, ∀ a b, (p : EAf D) * (km D n x).val a b ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ∧ (p : EAf D) * (km D n x⁻¹).val a b ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  intro D n s ϖ k hϖ
  obtain ⟨p, hp, hmem, a, ha⟩ := exists_char s.v
  refine ⟨p, hp, hmem, ⟨a, ha⟩, fun x hx i j => ?_⟩
  obtain ⟨k1, k2⟩ := tSet_denom s ϖ k hϖ p hmem x hx i j
  exact ⟨(GlobalTheory.StdFrameExist.mem_ALint_iff (D := D) _).1 k1, (GlobalTheory.StdFrameExist.mem_ALint_iff (D := D) _).1 k2⟩

end GlobalTheory.TSetDenom
