import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.SubtractOf

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso tw)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.TP.Sub

namespace UpperTheory.Gal.TP.Sub.PFrobSub

private theorem prod_scale {K : Type} [Field K] {c : K} (hc : c ≠ 0) (x : K) (S : Multiset K) :
    c ^ Multiset.card S * (S.map fun z => x / c - z).prod = (S.map fun z => x - z * c).prod := by
  induction S using Multiset.induction_on with
  | empty => simp
  | cons a S ih =>
    have e : c * (x / c - a) = x - a * c := by
      field_simp
    rw [Multiset.card_cons, Multiset.map_cons, Multiset.map_cons, Multiset.prod_cons, Multiset.prod_cons, ← ih, ← e]
    ring

private theorem charpoly_smul_eq {K : Type} [Field K] [Infinite K] {n : ℕ} (M : Matrix (Fin n) (Fin n) K) {c : K}
    (hc : c ≠ 0) (S : Multiset K) (h : M.charpoly = (S.map fun z => X - C z).prod) :
    (c • M).charpoly = (S.map fun z => X - C (z * c)).prod := by
  apply Polynomial.funext
  intro x
  have hn : Multiset.card S = n := by
    have := congrArg Polynomial.natDegree h
    rw [Matrix.charpoly_natDegree_eq_dim, Polynomial.natDegree_multiset_prod_X_sub_C_eq_card] at this
    simpa using this.symm
  have key : Matrix.scalar (Fin n) x - c • M = c • (Matrix.scalar (Fin n) (x / c) - M) := by
    rw [smul_sub]
    congr 1
    ext i j
    simp [Matrix.diagonal_apply]
    split_ifs <;> field_simp
  rw [Matrix.eval_charpoly, key, Matrix.det_smul, ← Matrix.eval_charpoly, h, Fintype.card_fin, ← hn,
    Polynomial.eval_multiset_prod, Polynomial.eval_multiset_prod, Multiset.map_map, Multiset.map_map]
  simp only [Function.comp_def, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  exact prod_scale hc x S

private theorem sumRep_left {Γ k : Type} [Group Γ] [Field k] {a b : ℕ} (r : Γ →* GL (Fin a) k) (s : Γ →* GL (Fin b) k)
    (g : Γ) (i j : Fin a) :
    (sumRep r s g : Matrix (Fin (a + b)) (Fin (a + b)) k) (Fin.castAdd b i) (Fin.castAdd b j) =
      (r g : Matrix (Fin a) (Fin a) k) i j := by
  simp [sumRep, Formalism.MainNotions.SumRepresentations.At.blkHom]
  rfl

private theorem characterAsRankOneRep_entry {Γ k : Type} [Group Γ] [Field k] (μ : Γ →* kˣ) (g : Γ) :
    (rk1 μ g : Matrix (Fin 1) (Fin 1) k) 0 0 = (μ g : k) := by
  unfold rk1
  simp

end UpperTheory.Gal.TP.Sub.PFrobSub

open UpperTheory.Gal.TP.Sub.PFrobSub in
theorem UpperTheory.Gal.TP.Sub.frobSub_holds :
    CpFacts → FrobSub := by
  intro h E Ω _ _ _ _ _ l _ ι a w S c μ hμ
  have hc : ∀ A, IsPlaceOver A w → ∀ σ : G E Ω, IsFrob A (normV w) σ →
      ι.toRingHom (μ σ⁻¹ : Qbar l) = c := by
    intro A hA σ hσ
    have h1 := (hμ A hA).2 σ hσ
    have h2 := (h (G E Ω) (Qbar l) 1 1).2.1 μ σ⁻¹
    unfold cp at h2
    rw [h2] at h1
    simpa using h1
  refine ⟨fun s hs => ?_, fun s hs => ?_⟩
  · intro A hA
    obtain ⟨hI, hF⟩ := hs A hA
    refine ⟨fun σ hσ => ?_, fun σ hσ => ?_⟩
    · have e := hI σ hσ
      ext i j
      have hij := sumRep_left s (rk1 μ) σ i j
      rw [e] at hij
      rw [← hij]
      simp [Matrix.one_apply]
    · have e := hF σ hσ
      have h3 := (h (G E Ω) (Qbar l) a 1).1 s (rk1 μ) σ⁻¹
      have h4 := (h (G E Ω) (Qbar l) 1 1).2.1 μ σ⁻¹
      unfold cp at h3 h4
      rw [h3, Polynomial.map_mul, h4] at e
      simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C] at e
      rw [hc A hA σ hσ, Multiset.map_add, Multiset.prod_add, Multiset.map_singleton,
        Multiset.prod_singleton] at e
      exact mul_right_cancel₀ (Polynomial.X_sub_C_ne_zero c) e
  · intro A hA
    obtain ⟨hI, hF⟩ := hs A hA
    obtain ⟨hIμ, -⟩ := hμ A hA
    refine ⟨fun σ hσ => ?_, fun σ hσ => ?_⟩
    · have e1 := hI σ hσ
      have e2 : (μ σ : Qbar l) = 1 := by
        rw [← characterAsRankOneRep_entry μ σ, hIμ σ hσ]
        simp
      ext i j
      rw [UpperTheory.V.Af.tw_val, e1, e2]
      simp
    · have e := hF σ hσ
      have hc' := hc A hA σ hσ
      have hc0 : c ≠ 0 := by
        rw [← hc']
        simp
      rw [UpperTheory.V.Af.tw_val, ← Matrix.charpoly_map]
      rw [← Matrix.charpoly_map] at e
      have hm : ((μ σ⁻¹ : Qbar l) • (s σ⁻¹ : Matrix (Fin a) (Fin a) (Qbar l))).map ι.toRingHom =
          c • (s σ⁻¹ : Matrix (Fin a) (Fin a) (Qbar l)).map ι.toRingHom := by
        rw [← hc']
        ext i j
        simp
      rw [hm, Multiset.map_map]
      exact charpoly_smul_eq _ hc0 S e
