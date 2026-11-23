import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LanglandsSquareIntegrable
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPurelyImaginaryElement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHermNDSmulSkewForm
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
open Formalism.UG (cT)
open Matrix

noncomputable section

namespace GlobalTheory.FlagRad

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

omit [NumberField E] in

theorem mulVec_initCols_mem {n r : ℕ} (X : Matrix (Fin n) (Fin r) E) (m : Fin r) (A : Set (Fin r))
    (a : Fin (m.val + 1) → AF F ⊗[F] E) (ha : ∀ l, a l ≠ 0 → Fin.castLE m.2 l ∈ A) :
    adMat F (GlobalTheory.StdPar.initCols X m) *ᵥ a ∈ GlobalTheory.StdPar.colSpan F X A := by
  rw [Matrix.mulVec_eq_sum]
  refine sum_mem fun l _ => ?_
  by_cases h : a l = 0
  · simp [h]
  · rw [op_smul_eq_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ha l h, rfl⟩)

theorem exists_of_card_lt {r : ℕ} (S : Finset (Fin r)) {a b : ℕ}
    (h : (S.filter fun k => k.val < a).card < (S.filter fun k => k.val < b).card) :
    ∃ k ∈ S, a ≤ k.val ∧ k.val < b := by
  by_contra hc
  push_neg at hc
  refine absurd h (not_lt.2 (Finset.card_le_card fun k hk => ?_))
  simp only [Finset.mem_filter] at hk ⊢
  exact ⟨hk.1, not_le.1 fun h' => absurd hk.2 (not_lt.2 (hc k hk.1 h'))⟩

open GlobalTheory.StdPar in

theorem unipFlag_le_unip (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (hJ : IsHermND σ J) (r : ℕ)
    (X Y : Matrix (Fin n) (Fin r) E) (hW : IsWittFrame σ J X Y) (S : Finset (Fin r)) (m : Fin r) (hmS : m ∈ S)
    (hm : ∀ k ∈ S, k ≤ m) :
    GlobalTheory.UAut.unipFlag σ J (GlobalTheory.StdPar.initCols X m) (fun i => (S.filter fun k => k.val < i.val).card) ≤
      GlobalTheory.StdPar.unip σ J X S := by
  set C := initCols X m with hCdef
  set d : Fin (m.val + 1) → ℕ := fun i => (S.filter fun k => k.val < i.val).card with hd
  have hσ : ∀ x, σ (σ x) = x := GlobalTheory.SiegelSet.sigma_sigma h
  have hC : IsIsoCols σ J C := isIsoCols_of_isWittFrame hW hσ hJ m.2
  have memS : ∀ g ∈ unipFlag σ J C d, g ∈ unipSet σ J C d := fun g hg => (mem_unipFlag hJ hσ hC d).1 hg

  have stab : ∀ g ∈ unipSet σ J C d, ∀ A : Set (Fin r), (∀ i ∈ A, i.val ≤ m.val) →
      (∀ l l' : Fin (m.val + 1), Fin.castLE m.2 l ∈ A → d l' < d l → Fin.castLE m.2 l' ∈ A) →
      ∀ y ∈ colSpan F X A, (matHom _ σ J g).1 *ᵥ y ∈ colSpan F X A := by
    intro g hg A hA1 hA2 y hy
    have hle : colSpan F X A ≤ (colSpan F X A).comap (matHom _ σ J g).1.mulVecLin := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨i, hi, rfl⟩
      obtain ⟨a, ha0, ha⟩ := hg.1 ⟨i.val, Nat.lt_succ_of_le (hA1 i hi)⟩
      have ha' : ((matHom _ σ J g).1 - 1) *ᵥ (adMat F X)ᵀ i = adMat F C *ᵥ a := ha
      have e : (matHom _ σ J g).1 *ᵥ (adMat F X)ᵀ i = (adMat F X)ᵀ i + ((matHom _ σ J g).1 - 1) *ᵥ (adMat F X)ᵀ i := by
        rw [Matrix.sub_mulVec, Matrix.one_mulVec, add_sub_cancel]
      show (matHom _ σ J g).1 *ᵥ (adMat F X)ᵀ i ∈ colSpan F X A
      rw [e, ha']
      refine add_mem (Submodule.subset_span ⟨i, hi, rfl⟩) (GlobalTheory.FlagRad.mulVec_initCols_mem X m A a fun l' hl' => ?_)
      exact hA2 ⟨i.val, Nat.lt_succ_of_le (hA1 i hi)⟩ l' hi (not_le.1 fun h' => hl' (ha0 l' h'))
    exact hle hy
  have inv_app : ∀ (g : GAd σ J) y, (matHom _ σ J g⁻¹).1 *ᵥ (matHom _ σ J g).1 *ᵥ y = y := fun g y => by
    rw [mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, one_mulVec]
  intro g hg
  have hg1 := memS g hg
  have hg2 := memS g⁻¹ (inv_mem hg)
  have iffPart : ∀ A : Set (Fin r), (∀ i ∈ A, i.val ≤ m.val) →
      (∀ l l' : Fin (m.val + 1), Fin.castLE m.2 l ∈ A → d l' < d l → Fin.castLE m.2 l' ∈ A) →
      ∀ y, y ∈ colSpan F X A ↔ (matHom _ σ J g).1 *ᵥ y ∈ colSpan F X A := fun A hA1 hA2 y =>
    ⟨stab g hg1 A hA1 hA2 y, fun hy => by
      have := stab g⁻¹ hg2 A hA1 hA2 _ hy
      rwa [inv_app] at this⟩
  have e1 : {i | ∃ k ∈ S, i ≤ k} = {i | i ≤ m} :=
    Set.ext fun i => ⟨fun ⟨k, hk, hik⟩ => hik.trans (hm k hk), fun hi => ⟨m, hmS, hi⟩⟩
  have hB1 : ∀ i ∈ {i : Fin r | i ≤ m}, i.val ≤ m.val := fun i hi => hi
  have hB2 : ∀ l l' : Fin (m.val + 1), Fin.castLE m.2 l ∈ {i : Fin r | i ≤ m} → d l' < d l →
      Fin.castLE m.2 l' ∈ {i : Fin r | i ≤ m} := fun l l' _ _ => Nat.le_of_lt_succ l'.2
  have sub_app : ∀ y, (matHom _ σ J g).1 *ᵥ y - y = ((matHom _ σ J g).1 - 1) *ᵥ y := fun y => by
    simp [Matrix.sub_mulVec]
  refine ⟨Subgroup.mem_iInf.2 fun j => ⟨iffPart _ ?_ ?_, fun y hy => ?_⟩, ?_⟩
  · rintro i ⟨k, hk, hik, -⟩
    exact hik.trans (hm k hk)
  · rintro l l' ⟨k, hk, hlk, hkj⟩ hdl
    obtain ⟨k', hk', h1, h2⟩ := GlobalTheory.FlagRad.exists_of_card_lt S hdl
    refine ⟨k', hk', h1, ?_⟩
    rw [Fin.le_def] at hlk
    rw [Fin.lt_def] at hkj ⊢
    simp only [Fin.coe_castLE] at hlk
    omega
  ·
    have hle : colSpan F X {j} ≤ (colSpan F X {i | ∃ k ∈ S, i ≤ k ∧ k < j}).comap
        ((matHom _ σ J g).1 - 1).mulVecLin := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨i, hi', rfl⟩
      have hij : i = j := hi'
      simp only [SetLike.mem_coe, Submodule.mem_comap, Matrix.mulVecLin_apply]
      by_cases hi : i.val ≤ m.val
      · obtain ⟨a, ha0, ha⟩ := hg1.1 ⟨i.val, Nat.lt_succ_of_le hi⟩
        have e : ((matHom _ σ J g).1 - 1) *ᵥ (adMat F X)ᵀ i = adMat F C *ᵥ a := ha
        rw [e]
        refine GlobalTheory.FlagRad.mulVec_initCols_mem X m _ a fun l' hl' => ?_
        obtain ⟨k, hk, h1, h2⟩ := GlobalTheory.FlagRad.exists_of_card_lt S (not_le.1 fun h' => hl' (ha0 l' h'))
        refine ⟨k, hk, h1, ?_⟩
        rw [Fin.lt_def, ← hij]
        exact h2
      · have hx : (cT (σ : E →+* E) C * J) *ᵥ (fun k => X k i) = 0 :=
          funext fun l => congrFun (congrFun hW.xx (l.castLE m.2)) i
        obtain ⟨a, ha⟩ := hg1.2 _ hx
        have e : ((matHom _ σ J g).1 - 1) *ᵥ (adMat F X)ᵀ i = adMat F C *ᵥ a := ha
        rw [e]
        refine GlobalTheory.FlagRad.mulVec_initCols_mem X m _ a fun l' _ => ⟨m, hmS, Nat.le_of_lt_succ l'.2, ?_⟩
        rw [Fin.lt_def, ← hij]
        omega
    rw [sub_app]
    exact hle hy
  · rw [e1]
    refine ⟨iffPart _ hB1 hB2, fun y hy => ?_⟩
    set T := cT (σ : E →+* E) (initCols X m) * J
    have hT : T * initCols Y m = 1 := Matrix.ext fun i j =>
      (congrFun (congrFun hW.xy (i.castLE m.2)) (j.castLE m.2)).trans (by simp [Matrix.one_apply])
    have hQ : T * (1 - initCols Y m * T) = 0 := by
      rw [Matrix.mul_sub, ← Matrix.mul_assoc, hT, Matrix.one_mul, Matrix.mul_one, sub_self]
    have hy' : y = adMat F (1 - initCols Y m * T) *ᵥ y := by
      rw [adMat, Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_mul, sub_mulVec,
        one_mulVec, ← mulVec_mulVec, mem_colPerp_iff.1 hy, mulVec_zero, sub_zero]
    have : (matHom _ σ J g).1 *ᵥ y - y = ((matHom _ σ J g).1 - 1).mulVecLin y := by simp [sub_mulVec]
    rw [this, hy', mulVec_eq_sum, map_sum]
    refine sum_mem fun j _ => ?_
    rw [op_smul_eq_smul, map_smul]
    obtain ⟨a, ha⟩ := hg1.2 (fun i => (1 - initCols Y m * T : Matrix (Fin n) (Fin n) E) i j)
      (funext fun i => congrFun (congrFun hQ i) j)
    exact Submodule.smul_mem _ _ (mem_colSpan_iff.2 ⟨a, ha.symm⟩)

end GlobalTheory.FlagRad
