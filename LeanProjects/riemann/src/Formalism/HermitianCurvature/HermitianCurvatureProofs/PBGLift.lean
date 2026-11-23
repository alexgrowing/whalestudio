import Formalism.HermitianCurvature.StatementHeads
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBGWaveMain

open Matrix Finset
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBG

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

theorem nice_mono {k ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] {Bs : B.RealPlaceData k ρ Wp Wq} {ε ε' : ℝ} {F : B.Mat k ρ → (Wq →L[ℂ] Wp)}
    (h : JC.NiceCoef Bs ε F) (hε : ε' ≤ ε) : JC.NiceCoef Bs ε' F :=
  ⟨h.1, h.2.1, fun g hg hne => hε.trans (h.2.2 g hg hne)⟩

theorem poly_coeff_unique {V : Type} [AddCommGroup V] [Module ℂ V] (n : ℕ) (A B : Fin n → V)
    (h : ∀ y : ℝ, ∑ l : Fin n, ((y : ℂ) ^ (l : ℕ)) • A l = ∑ l : Fin n, ((y : ℂ) ^ (l : ℕ)) • B l) : A = B := by
  set τ : Fin n → ℂ := fun i => (((i : ℕ) : ℝ) : ℂ) with hτdef
  have hτ : Function.Injective τ := by
    intro a b hab
    simp only [hτdef, Complex.ofReal_inj, Nat.cast_inj] at hab
    exact Fin.ext hab
  have key : ∀ (C : Fin n → V) (l : Fin n),
      C l = ∑ i : Fin n, (Matrix.vandermonde τ)⁻¹ l i • ∑ m : Fin n, (τ i ^ (m : ℕ)) • C m := by
    intro C l
    simp only [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul]
    simp only [vand_row τ hτ l, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  funext l
  rw [key A l, key B l]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  exact h ((i : ℕ) : ℝ)

section lift

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem sum_pad {V : Type} [AddCommGroup V] [Module ℂ V] {d n : ℕ} (hdn : d ≤ n) (c : Fin (d + 1) → V) (y : ℂ) :
    ∑ m : Fin (d + 1), (y ^ (m : ℕ)) • c m =
      ∑ l : Fin (n + 1), (y ^ (l : ℕ)) • (if hl : (l : ℕ) ≤ d then c ⟨l, by omega⟩ else 0) := by
  classical
  have e := Finset.sum_map (Finset.univ : Finset (Fin (d + 1))) (Fin.castLEEmb (by omega : d + 1 ≤ n + 1))
    (fun l : Fin (n + 1) => (y ^ (l : ℕ)) • (if hl : (l : ℕ) ≤ d then c ⟨l, by omega⟩ else 0))
  symm
  rw [← Finset.sum_subset (Finset.subset_univ ((Finset.univ : Finset (Fin (d + 1))).map
    (Fin.castLEEmb (by omega : d + 1 ≤ n + 1)))) ?_, e]
  · apply Finset.sum_congr rfl
    intro m _
    simp only [Fin.castLEEmb_apply, Fin.val_castLE]
    rw [dif_pos (by omega)]
  · intro l _ hl
    rw [dif_neg, smul_zero]
    intro hle
    apply hl
    rw [Finset.mem_map]
    exact ⟨⟨l, by omega⟩, Finset.mem_univ _, Fin.ext (by simp)⟩

theorem reduceJ {k r : ℕ} (T : D.LevTower k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (j s : ℕ) (hj : j ≤ r)
    (h : C.LPt) (τ : ℂ) (ha : D.ptSize (h ++ [(s, τ)]) = j) (hs : s ≤ j)
    (hSP : SlicePoly T F j hj (h ++ [(s, τ)]) ha) (hLD : LiftDeg T F j s hj h τ ha)
    (w' : List C.Letter) (hN : ∃ ε, ∀ a', JC.NiceCoef (T.bs j) ε (KB.slv T F j hj w' (h ++ [(s, τ)]) ha a'))
    (b : Bool) (δ : ℝ) :
    ∃ E : Fin (j + 1) → Wd.Ix (Fin w'.length) → B.Mat k (r - j) → (Wq →L[ℂ] Wp),
      (∀ l, ∃ ε, ∀ a', JC.NiceCoef (T.bs j) ε (E l a')) ∧ (∀ l : Fin (j + 1), j - s < (l : ℕ) → E l = 0) ∧
      E ⟨j - s, by omega⟩ = cLift s τ b • KB.slv T F j hj w' (h ++ [(s, τ)]) ha ∧
      ∀ (y : ℝ) (a' : Wd.Ix (Fin w'.length)), ∀ g ∈ JF.Om k (r - j) (T.bs j).z (T.bs j).z',
        B.JF (T.bs j) (KB.slv T F j hj ((b, y + δ) :: w') (h ++ [(s, τ)]) ha (Fin.cons 1 a')) g =
          B.JF (T.bs j) ((∑ l : Fin (j + 1), ((y : ℂ) ^ (l : ℕ)) • E l) a') g := by
  classical
  obtain ⟨C1, -, hC1n, hC1⟩ := hSP w' b δ 1
  obtain ⟨εN, hεN⟩ := hN
  set E : Fin (j + 1) → Wd.Ix (Fin w'.length) → B.Mat k (r - j) → (Wq →L[ℂ] Wp) := fun l =>
    if (l : ℕ) < j - s then C1 l else if (l : ℕ) = j - s then cLift s τ b • KB.slv T F j hj w' (h ++ [(s, τ)]) ha
    else 0 with hE

  choose εC hεC using hC1n
  set ε0 : ℝ := min εN (Finset.univ.inf' Finset.univ_nonempty εC) with hε0
  have hC1n' : ∀ l a', JC.NiceCoef (T.bs j) ε0 (C1 l a') := fun l a' =>
    nice_mono (hεC l a') ((min_le_right _ _).trans (Finset.inf'_le _ (Finset.mem_univ l)))
  have hNn' : ∀ a', JC.NiceCoef (T.bs j) ε0 (KB.slv T F j hj w' (h ++ [(s, τ)]) ha a') := fun a' =>
    nice_mono (hεN a') (min_le_left _ _)
  have hEn : ∀ l a', JC.NiceCoef (T.bs j) ε0 (E l a') := by
    intro l a'
    simp only [hE]
    split_ifs
    · exact hC1n' l a'
    · exact Formalism.FourierDecayAlt.P.JCx2.mn_nice_smul _ (hNn' a')
    · exact Formalism.FourierDecayAlt.P.JCx2.mn_nice_zero
  refine ⟨E, fun l => ⟨ε0, hEn l⟩, fun l hl => ?_, ?_, fun y a' g hg => ?_⟩
  · simp only [hE]; rw [if_neg (by omega), if_neg (by omega)]
  · simp only [hE]; rw [if_neg (by simp), if_pos (by simp)]
  ·
    have hsum : ∀ (y : ℝ) (V : Fin (j + 1) → Wd.Ix (Fin w'.length) → B.Mat k (r - j) → (Wq →L[ℂ] Wp)),
        (∀ l, JC.NiceCoef (T.bs j) ε0 (V l a')) →
        B.JF (T.bs j) ((∑ l : Fin (j + 1), ((y : ℂ) ^ (l : ℕ)) • V l) a') g =
          ∑ l : Fin (j + 1), ((y : ℂ) ^ (l : ℕ)) • B.JF (T.bs j) (V l a') g := by
      intro y V hV
      have e1 : (∑ l : Fin (j + 1), ((y : ℂ) ^ (l : ℕ)) • V l) a' = ∑ l : Fin (j + 1), ((y : ℂ) ^ (l : ℕ)) • V l a' := by
        simp [Finset.sum_apply]
      rw [e1, Formalism.FourierDecayAlt.P.JCx2.bc_JF_sum Finset.univ (fun l : Fin (j + 1) => ((y : ℂ) ^ (l : ℕ)) • V l a')
        (fun l _ => Formalism.FourierDecayAlt.P.JCx2.mn_nice_smul _ (hV l)) hg]
      apply Finset.sum_congr rfl
      intro l _
      exact Formalism.FourierDecayAlt.P.JCx2.bc_JF_smul _ _ _
    have hgGV : g ∈ B.GV k (r - j) := hg.1

    have hL : ∀ y' : ℝ, B.JF (T.bs j) (KB.slv T F j hj ((b, y' + δ) :: w') (h ++ [(s, τ)]) ha (Fin.cons 1 a')) g =
        ∑ l : Fin (j + 1), ((y' : ℂ) ^ (l : ℕ)) • B.JF (T.bs j) (C1 l a') g := by
      intro y'
      rw [Formalism.FourierDecayAlt.P.JCx2.sq_jf_congr (T.bs j) (fun g' hg' => hC1 y' a' g' hg') hgGV]
      exact hsum y' C1 (fun l => hC1n' l a')
    obtain ⟨c, hcl, hcy⟩ := hLD w' a' b δ g hg
    have hcomp := poly_coeff_unique (j + 1) (fun l => B.JF (T.bs j) (C1 l a') g)
      (fun l => if hl : (l : ℕ) ≤ j - s then c ⟨l, by omega⟩ else 0) (fun y' => by
        rw [← hL y', hcy y', sum_pad (n := j) (by omega) c (y' : ℂ)])
    rw [hL y, hsum y E (fun l => hEn l a')]
    apply Finset.sum_congr rfl
    intro l _
    congr 1
    have hcl' := congrFun hcomp l
    by_cases h1 : (l : ℕ) < j - s
    · simp only [hE, if_pos h1]
    · rw [show B.JF (T.bs j) (C1 l a') g = _ from hcl']
      by_cases h2 : (l : ℕ) = j - s
      · simp only [hE, if_neg h1, if_pos h2]
        rw [dif_pos (by omega)]
        have e3 : (⟨(l : ℕ), by omega⟩ : Fin (j - s + 1)) = Fin.last (j - s) := Fin.ext (by simp [h2])
        rw [e3, hcl]
        exact (Formalism.FourierDecayAlt.P.JCx2.bc_JF_smul _ _ _).symm
      · simp only [hE, if_neg h1, if_neg h2]
        rw [dif_neg (by omega)]
        exact (Formalism.FourierDecayAlt.P.JCx2.bc_JF_zero g).symm

theorem nice_lincomb {k ρ : ℕ} {Bs : B.RealPlaceData k ρ Wp Wq} {S ι : Type} [Fintype S] [Fintype ι] [Nonempty ι]
    (V : ι → Wd.Ix S → B.Mat k ρ → (Wq →L[ℂ] Wp)) (hV : ∀ l, ∃ ε, ∀ a, JC.NiceCoef Bs ε (V l a)) (c : ι → ℂ) :
    ∃ ε, ∀ a, JC.NiceCoef Bs ε ((∑ l, c l • V l) a) := by
  classical
  choose ε hε using hV
  refine ⟨Finset.univ.inf' Finset.univ_nonempty ε, fun a => ?_⟩
  have e : (∑ l, c l • V l) a = fun g => ∑ l, c l • V l a g := by
    funext g; simp [Finset.sum_apply]
  rw [e]
  exact Formalism.FourierDecayAlt.P.JCx2.mn_nice_sum Finset.univ (fun l g => c l • V l a g)
    (fun l _ => Formalism.FourierDecayAlt.P.JCx2.mn_nice_smul _ (nice_mono (hε l a) (Finset.inf'_le _ (Finset.mem_univ l))))

end lift

end Formalism.FourierDecayAlt.P.PBG
