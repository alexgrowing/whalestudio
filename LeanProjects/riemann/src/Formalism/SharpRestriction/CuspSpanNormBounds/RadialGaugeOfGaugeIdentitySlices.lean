import Formalism.SharpRestriction.CuspSpanNormBounds.DiagonalEntryIdentity
import Formalism.SharpRestriction.CuspSpanNormBounds.FamilyBlockLiftEstimate
import Formalism.SharpRestriction.CuspSpanNormBounds.OscillatoryIntegralBounds
import Formalism.HermitianCurvature.StatementWd
import Formalism.SharpRestriction.CuspSpanNormBounds.PExtra
import Formalism.SharpRestriction.CuspSpanNormBounds.BlockEstimateTheorem
import Formalism.SharpRestriction.CuspSpanNormBounds.RadialLemmaE
import Formalism.SharpRestriction.CuspSpanNormBounds.ChoiceOfModulusAndDiscriminant
import Formalism.SharpRestriction.CuspSpanNormBounds.RadialRules
import Formalism.SharpRestriction.CuspSpanNormBounds.LevelRaisingOperators
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdjointnessPolynomiallyBounded
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationContinuousOnInvertible
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HaarUniquenessConjugation
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormBallVolumes
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SettingConstruction
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HaarScaling
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactGroupHaarExists
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationInvarianceEverySetting
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DilationScalesHeisenbergMeasure
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LemmaBOfComponents
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ChangeOfVariablesXy
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TransferProductMonic
import Formalism.HermitianCurvature.StatementB
import Formalism.RealPlaceAnalysis.FinalF
import Formalism.FormalDegreeBessel.FinalG
import Formalism.SharpRestriction.CuspSpanNormBounds.PSDKOnOfPSDK
import Formalism.HermitianCurvature.StatementTC
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RecursionWithDensities

section PartSl1

namespace Formalism.MainNotions.BridgeLemma₅

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.TopsChoicePartA Formalism.MainNotions.S.UnitaryLevelOperators Matrix

section Head

variable (k j r' : ℕ)

def slMid (p : Fin (2 * (j + r') + k + 1)) : Prop := j ≤ p.val ∧ p.val < 2 * r' + k + 1 + j

def slMidS (v : Fin (2 * (j + r') + k + 1) → ℂ) : Prop := ∀ p, ¬ slMid k j r' p → v p = 0

def slDn (v : Fin (2 * (j + r') + k + 1) → ℂ) : Fin (2 * r' + k + 1) → ℂ := fun p => v (levPos k j r' p)

variable {k j r'}

theorem sl_sum_mid (f : Fin (2 * (j + r') + k + 1) → ℂ) (hf : ∀ p, ¬ slMid k j r' p → f p = 0) :
    ∑ p, f p = ∑ p', f (levPos k j r' p') := by
  classical
  let e : Fin (2 * r' + k + 1) ↪ Fin (2 * (j + r') + k + 1) :=
    ⟨levPos k j r', fun a b hab => by
      have := congrArg Fin.val hab
      simp only [levPos] at this
      exact Fin.ext (by omega)⟩
  have h1 : ∑ p', f (levPos k j r' p') = ∑ p ∈ Finset.univ.map e, f p := by
    rw [Finset.sum_map]; rfl
  rw [h1]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro p _ hp
  apply hf
  intro hm
  apply hp
  rw [Finset.mem_map]
  refine ⟨⟨p.val - j, by have := hm.1; have := hm.2; omega⟩, Finset.mem_univ _, ?_⟩
  apply Fin.ext
  show p.val - j + j = p.val
  have := hm.1; omega

variable (z z' : Fin (2 * (j + r') + k + 1) → ℂ) (h : Matrix (Fin j) (Fin j) ℂ)
  (g : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ)

end Head

end Formalism.MainNotions.BridgeLemma₅

end PartSl1

section PartSl2

namespace Formalism.MainNotions.BridgeLemma₅

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.TopsChoicePartA Formalism.MainNotions.S.UnitaryLevelOperators Matrix

def slicesOpen (Cs : ℝ) : Prop :=
  ∀ (Lt : Lev) (u u' : Fin (Lt.k0 + 1) → ℝ) (j r' : ℕ) (hj : j + r' = Lt.r) (hd : Point ℂ j), Lt.Std → Lt.HC u u' →
    ((∀ b ∈ hd.1, b.2 = 1) →
    ∀ (h : Lt.Haar) (h' : (Lt.down j r' hj).Haar) (A : ℝ) (mm : ℕ) (F : Lt.GF), h.Ok → h'.Ok → Lt.CC A mm F →
      0 ≤ A / (Cs * ((Lt.r : ℝ) + 1) ^ 2) -
        Cs * (((2 * Lt.r + Lt.k0 + 2 : ℕ) : ℝ) ^ 2 + ((Lt.r : ℝ) + 1) * mm) →
      ∃ Fh : (Lt.down j r' hj).GF,
        (Lt.down j r' hj).CC (A / (Cs * ((Lt.r : ℝ) + 1) ^ 2) -
          Cs * (((2 * Lt.r + Lt.k0 + 2 : ℕ) : ℝ) ^ 2 + ((Lt.r : ℝ) + 1) * mm)) mm Fh ∧
        ∀ c : Fin r' → ℂ, (∀ a, c a ≠ 0) → ∀ μ ∈ UH (Hb (Lt.k0 + 1)),
          lJ (Lt.down j r' hj) h' Fh (bigCell (Lt.k0 + 1) r' c μ) =
            lJ Lt h F (headLt Lt j r' hj (ptMat hd) (bigCell (Lt.k0 + 1) r' c μ)))

end Formalism.MainNotions.BridgeLemma₅

end PartSl2

section PartSl3

namespace Formalism.MainNotions.BridgeLemma₅

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.TopsChoicePartA Formalism.MainNotions.S.UnitaryLevelOperators Formalism.MainNotions.S.GramWordSpace Matrix

def slicesOrbOpen (Cs : ℝ) : Prop :=
  ∀ (k0 r : ℕ) (L : LocBessel (k0 + 1) r) (μsec : Sec k0) (j : ℕ) (hj : j ≤ r) (hd : Point ℂ j),
    L.c = cStd → (levOf L μsec).Std →
    ∀ (h' : (lev L μsec j hj).Haar) (A : ℝ) (mm : ℕ) (F : GFn L), h'.Ok → (levOf L μsec).CC A mm F →
      0 ≤ A / (Cs * ((r : ℝ) + 1) ^ 2) - Cs * (((2 * r + k0 + 2 : ℕ) : ℝ) ^ 2 + ((r : ℝ) + 1) * mm) →
      ∃ Fh : (lev L μsec j hj).GF,
        (lev L μsec j hj).CC (A / (Cs * ((r : ℝ) + 1) ^ 2) -
          Cs * (((2 * r + k0 + 2 : ℕ) : ℝ) ^ 2 + ((r : ℝ) + 1) * mm)) mm Fh ∧
        ((∃ ε : ℝ, 0 < ε ∧ SuppGe (levOf L μsec) ε F) → ∃ ε' : ℝ, 0 < ε' ∧ SuppGe (lev L μsec j hj) ε' Fh) ∧
        ∀ x ∈ (lev L μsec j hj).BD,
          lJ (lev L μsec j hj) h' Fh ((lev L μsec j hj).pt x) = sliceJ L μsec j hj F hd ((lev L μsec j hj).pt x)

end Formalism.MainNotions.BridgeLemma₅

end PartSl3

section PartT22

namespace Formalism.MainNotions.BridgeLemma₅

open Formalism.REAL Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.TopsChoicePartA Formalism.MainNotions.S.UnitaryLevelOperators Matrix

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section Homog

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def tHom (T : (Matrix (Fin n) (Fin n) ℂ → E) → (Matrix (Fin n) (Fin n) ℂ → E)) : Prop :=
  ∀ (a : ℂ) (f : Matrix (Fin n) (Fin n) ℂ → E), T (a • f) = a • T f

end Homog

section Classes

end Classes

def SliceImg : Prop :=
  ∀ (L : Lev) (pb : Mat L.k0 (L.r + 1) → (L.Wp →L[ℂ] L.Wp)) (pb' : Mat L.k0 (L.r + 1) → (L.Wq →L[ℂ] L.Wq)),
    L.Std → (L.up pb pb').Std → L.Compat pb pb' → ∀ φ ∈ (L.up pb pb').Img, ∀ c : ℂ, c ≠ 0 →
      (fun y : Fin (L.r + 1) → ℂ => φ (Fin.cons c y)) ∈ L.Img

end Formalism.MainNotions.BridgeLemma₅

end PartT22

section PartT22b

namespace Formalism.MainNotions.BridgeLemma₅

open Formalism.REAL Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.TopsChoicePartA Formalism.MainNotions.S.UnitaryLevelOperators Matrix

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

end Formalism.MainNotions.BridgeLemma₅

end PartT22b

section PartBlk

namespace Formalism.MainNotions.BridgeLemma₅

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.TopsChoicePartA Formalism.MainNotions.S.UnitaryLevelOperators Matrix

section GlobalTheory

variable {k j r' : ℕ}

instance slMid_dec (p : Fin (2 * (j + r') + k + 1)) : Decidable (slMid k j r' p) :=
  inferInstanceAs (Decidable (_ ∧ _))

def blockEmbedding (o : Matrix (Fin (2 * (j + r') + k + 1)) (Fin (2 * (j + r') + k + 1)) ℂ)
    (g : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ) :
    Matrix (Fin (2 * (j + r') + k + 1)) (Fin (2 * (j + r') + k + 1)) ℂ := fun p q =>
  if hp : slMid k j r' p then
    (if hq : slMid k j r' q then g ⟨p.val - j, by have := hp.1; have := hp.2; omega⟩
      ⟨q.val - j, by have := hq.1; have := hq.2; omega⟩ else 0)
  else (if slMid k j r' q then 0 else o p q)

def slOut (o o' : Matrix (Fin (2 * (j + r') + k + 1)) (Fin (2 * (j + r') + k + 1)) ℂ) :
    Matrix (Fin (2 * (j + r') + k + 1)) (Fin (2 * (j + r') + k + 1)) ℂ := fun p q =>
  ∑ s, if slMid k j r' s then 0 else o p s * o' s q

theorem sl_mid_lev (p : Fin (2 * r' + k + 1)) : slMid k j r' (levPos k j r' p) := by
  have := p.isLt
  exact ⟨by simp only [levPos]; omega, by simp only [levPos]; omega⟩

theorem sl_mid_eq (p : Fin (2 * (j + r') + k + 1)) (hp : slMid k j r' p) :
    ∃ p' : Fin (2 * r' + k + 1), p = levPos k j r' p' :=
  ⟨⟨p.val - j, by have := hp.1; have := hp.2; omega⟩, Fin.ext (by have := hp.1; simp only [levPos]; omega)⟩

variable (o o' : Matrix (Fin (2 * (j + r') + k + 1)) (Fin (2 * (j + r') + k + 1)) ℂ)
  (g g' : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ)

theorem block_embedding_middle_middle (p q : Fin (2 * r' + k + 1)) : blockEmbedding o g (levPos k j r' p) (levPos k j r' q) = g p q := by
  simp only [blockEmbedding, dif_pos (sl_mid_lev p), dif_pos (sl_mid_lev q)]
  congr 1 <;> (apply Fin.ext; simp [levPos])

theorem level_statement_of_open_part (p q : Fin (2 * (j + r') + k + 1)) (hp : slMid k j r' p) (hq : ¬ slMid k j r' q) :
    blockEmbedding o g p q = 0 := by
  simp only [blockEmbedding, dif_pos hp, dif_neg hq]

theorem block_embedding_outer_middle (p q : Fin (2 * (j + r') + k + 1)) (hp : ¬ slMid k j r' p) (hq : slMid k j r' q) :
    blockEmbedding o g p q = 0 := by
  simp only [blockEmbedding, dif_neg hp, if_pos hq]

theorem block_embedding_outer_outer (p q : Fin (2 * (j + r') + k + 1)) (hp : ¬ slMid k j r' p) (hq : ¬ slMid k j r' q) :
    blockEmbedding o g p q = o p q := by
  simp only [blockEmbedding, dif_neg hp, if_neg hq]

theorem block_embedding_ext {M : Matrix (Fin (2 * (j + r') + k + 1)) (Fin (2 * (j + r') + k + 1)) ℂ}
    (hmm : ∀ p q, M (levPos k j r' p) (levPos k j r' q) = g p q)
    (hmo : ∀ p q, slMid k j r' p → ¬ slMid k j r' q → M p q = 0)
    (hom : ∀ p q, ¬ slMid k j r' p → slMid k j r' q → M p q = 0)
    (hoo : ∀ p q, ¬ slMid k j r' p → ¬ slMid k j r' q → M p q = o p q) : M = blockEmbedding o g := by
  ext p q
  by_cases hp : slMid k j r' p <;> by_cases hq : slMid k j r' q
  · obtain ⟨p', rfl⟩ := sl_mid_eq p hp
    obtain ⟨q', rfl⟩ := sl_mid_eq q hq
    rw [hmm, block_embedding_middle_middle]
  · rw [hmo p q hp hq, level_statement_of_open_part o g p q hp hq]
  · rw [hom p q hp hq, block_embedding_outer_middle o g p q hp hq]
  · rw [hoo p q hp hq, block_embedding_outer_outer o g p q hp hq]

theorem sl_sum_split (F : Fin (2 * (j + r') + k + 1) → ℂ) :
    ∑ s, F s = ∑ s', F (levPos k j r' s') + ∑ s, if slMid k j r' s then 0 else F s := by
  have h1 : ∑ s', F (levPos k j r' s') = ∑ s, if slMid k j r' s then F s else 0 := by
    rw [sl_sum_mid (fun s => if slMid k j r' s then F s else 0) (fun p hp => if_neg hp)]
    exact Finset.sum_congr rfl fun s _ => (if_pos (sl_mid_lev s)).symm
  rw [h1, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases hs : slMid k j r' s
  · rw [if_pos hs, if_pos hs, add_zero]
  · rw [if_neg hs, if_neg hs, zero_add]

theorem block_embedding_mul : blockEmbedding o g * blockEmbedding o' g' = blockEmbedding (slOut o o') (g * g') := by
  apply block_embedding_ext
  · intro p q
    rw [Matrix.mul_apply, sl_sum_split, Matrix.mul_apply]
    rw [Finset.sum_eq_zero (s := Finset.univ) (f := fun s => if slMid k j r' s then 0 else
      blockEmbedding o g (levPos k j r' p) s * blockEmbedding o' g' s (levPos k j r' q)), add_zero]
    · exact Finset.sum_congr rfl fun s _ => by rw [block_embedding_middle_middle, block_embedding_middle_middle]
    · intro s _
      by_cases hs : slMid k j r' s
      · exact if_pos hs
      · rw [if_neg hs, level_statement_of_open_part o g _ s (sl_mid_lev p) hs, zero_mul]
  · intro p q hp hq
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro s _
    by_cases hs : slMid k j r' s
    · rw [level_statement_of_open_part o' g' s q hs hq, mul_zero]
    · rw [level_statement_of_open_part o g p s hp hs, zero_mul]
  · intro p q hp hq
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro s _
    by_cases hs : slMid k j r' s
    · rw [block_embedding_outer_middle o g p s hp hs, zero_mul]
    · rw [block_embedding_outer_middle o' g' s q hs hq, mul_zero]
  · intro p q hp hq
    rw [Matrix.mul_apply]
    simp only [slOut]
    refine Finset.sum_congr rfl fun s _ => ?_
    by_cases hs : slMid k j r' s
    · rw [if_pos hs, block_embedding_outer_middle o g p s hp hs, zero_mul]
    · rw [if_neg hs, block_embedding_outer_outer o g p s hp hs, block_embedding_outer_outer o' g' s q hs hq]

theorem block_embedding_congr (h : ∀ p q, ¬ slMid k j r' p → ¬ slMid k j r' q → o p q = o' p q) : blockEmbedding o g = blockEmbedding o' g := by
  apply block_embedding_ext
  · intro p q; exact block_embedding_middle_middle o g p q
  · intro p q hp hq; exact level_statement_of_open_part o g p q hp hq
  · intro p q hp hq; exact block_embedding_outer_middle o g p q hp hq
  · intro p q hp hq; rw [block_embedding_outer_outer o g p q hp hq, h p q hp hq]

theorem sl_iota_blk : ιLev k j r' g = blockEmbedding 1 g := by
  apply block_embedding_ext
  · intro p q
    have hp := sl_mid_lev (j := j) p
    have hq := sl_mid_lev (j := j) q
    simp only [slMid] at hp hq
    simp only [ιLev, dif_pos hp, dif_pos hq]
    congr 1 <;> (apply Fin.ext; simp [levPos])
  · intro p q hp hq
    simp only [slMid] at hp hq
    simp only [ιLev, dif_pos hp, dif_neg hq]
  · intro p q hp hq
    have hne : p ≠ q := fun h => hp (h ▸ hq)
    simp only [slMid] at hp
    simp only [ιLev, dif_neg hp, if_neg hne]
  · intro p q hp _
    simp only [slMid] at hp
    simp only [ιLev, dif_neg hp, Matrix.one_apply]

theorem sl_head_blk (h : Matrix (Fin j) (Fin j) ℂ) : headEl k j r' h g = blockEmbedding (headEl k j r' h 0) g := by
  apply block_embedding_ext
  · intro p q
    have hp := sl_mid_lev (j := j) p
    have hq := sl_mid_lev (j := j) q
    simp only [slMid] at hp hq
    have h1 : ¬ (levPos k j r' q).val < j := by omega
    simp only [headEl, dif_neg h1, dif_pos hq.2, dif_pos hp]
    congr 1 <;> (apply Fin.ext; simp [levPos])
  · intro p q hp hq
    simp only [slMid] at hp hq
    by_cases h1 : q.val < j
    · have h2 : ¬ (2 * (j + r') + k + 1 - j ≤ p.val) := by omega
      simp only [headEl, dif_pos h1, dif_neg h2]
    · have h2 : ¬ q.val < 2 * r' + k + 1 + j := by omega
      have h3 : ¬ p.val < j := by omega
      simp only [headEl, dif_neg h1, dif_neg h2, dif_neg h3]
  · intro p q hp hq
    simp only [slMid] at hp hq
    have h1 : ¬ q.val < j := by omega
    simp only [headEl, dif_neg h1, dif_pos hq.2, dif_neg hp]
  · intro p q hp hq
    simp only [slMid] at hp hq
    by_cases h1 : q.val < j
    · simp only [headEl, dif_pos h1]
    · have h2 : ¬ q.val < 2 * r' + k + 1 + j := by omega
      simp only [headEl, dif_neg h1, dif_neg h2]

theorem slOut_one_left (p q : Fin (2 * (j + r') + k + 1)) (hp : ¬ slMid k j r' p) : slOut 1 o p q = o p q := by
  classical
  simp only [slOut, Matrix.one_apply]
  rw [Finset.sum_eq_single p]
  · rw [if_neg hp, if_pos rfl, one_mul]
  · intro s _ hs
    by_cases hm : slMid k j r' s
    · exact if_pos hm
    · rw [if_neg hm, if_neg (Ne.symm hs), zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem slOut_one_right (p q : Fin (2 * (j + r') + k + 1)) (hq : ¬ slMid k j r' q) : slOut o 1 p q = o p q := by
  classical
  simp only [slOut, Matrix.one_apply]
  rw [Finset.sum_eq_single q]
  · rw [if_neg hq, if_pos rfl, mul_one]
  · intro s _ hs
    by_cases hm : slMid k j r' s
    · exact if_pos hm
    · rw [if_neg hm, if_neg hs, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem sl_iota_head (h : Matrix (Fin j) (Fin j) ℂ) (n n' : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ) :
    ιLev k j r' n * headEl k j r' h g * ιLev k j r' n' = headEl k j r' h (n * g * n') := by
  rw [sl_iota_blk, sl_iota_blk, sl_head_blk, sl_head_blk (n * g * n'), block_embedding_mul, block_embedding_mul]
  apply block_embedding_congr
  intro p q hp hq
  rw [slOut_one_right _ p q hq, slOut_one_left _ p q hp]

end GlobalTheory

end Formalism.MainNotions.BridgeLemma₅

end PartBlk

section PartLv

namespace Formalism.MainNotions.BridgeLemma₅

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.TopsChoicePartA Formalism.MainNotions.S.UnitaryLevelOperators Matrix

section Lv

variable {k j r' : ℕ}

end Lv

end Formalism.MainNotions.BridgeLemma₅

end PartLv

section PartHd

namespace Formalism.MainNotions.BridgeLemma₅

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.TopsChoicePartA Formalism.MainNotions.S.UnitaryLevelOperators Matrix
open scoped ContDiff

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section Hd

variable {k r' : ℕ}

def hdF : Fin (2 * (1 + r') + k + 1) := ⟨0, by omega⟩
def hdL : Fin (2 * (1 + r') + k + 1) := ⟨2 * (1 + r') + k, by omega⟩

def hdC (c : ℂ) : Matrix (Fin 1) (Fin 1) ℂ := fun _ _ => c

variable (c : ℂ) (g : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ)

end Hd

end Formalism.MainNotions.BridgeLemma₅

end PartHd

section PartBc

namespace Formalism.MainNotions.BridgeLemma₅

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.TopsChoicePartA Formalism.MainNotions.S.UnitaryLevelOperators Matrix

variable {k r' : ℕ}

end Formalism.MainNotions.BridgeLemma₅

end PartBc

section PartSlI

namespace Formalism.MainNotions.BridgeLemma₅

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.TopsChoicePartA Formalism.MainNotions.S.UnitaryLevelOperators Matrix
open scoped ContDiff

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section Cast

variable {k j r' R : ℕ}

def cM (hR : R = j + r') (M : Matrix (Fin (2 * (j + r') + k + 1)) (Fin (2 * (j + r') + k + 1)) ℂ) :
    Matrix (Fin (2 * R + k + 1)) (Fin (2 * R + k + 1)) ℂ :=
  fun p q => M (Fin.cast (by omega) p) (Fin.cast (by omega) q)

def cV (hR : R = j + r') (v : Fin (2 * (j + r') + k + 1) → ℂ) : Fin (2 * R + k + 1) → ℂ :=
  fun p => v (Fin.cast (by omega) p)

theorem c_mul (hR : R = j + r') (h : Matrix (Fin j) (Fin j) ℂ)
    (n g n' : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ) :
    cM hR (ιLev k j r' n) * cM hR (headEl k j r' h g) * cM hR (ιLev k j r' n') =
      cM hR (headEl k j r' h (n * g * n')) := by
  subst hR; exact sl_iota_head g h n n'

end Cast

section Cast1

variable {k r' R : ℕ}

end Cast1

end Formalism.MainNotions.BridgeLemma₅

end PartSlI

section PartSlJ

namespace Formalism.MainNotions.BridgeLemma₅

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.TopsChoicePartA Formalism.MainNotions.S.UnitaryLevelOperators Matrix
open scoped ContDiff

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

end Formalism.MainNotions.BridgeLemma₅

end PartSlJ

section PartRp

namespace Formalism.MainNotions.BridgeLemma₅

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.TopsChoicePartA Formalism.MainNotions.S.UnitaryLevelOperators Matrix

end Formalism.MainNotions.BridgeLemma₅

end PartRp

section PartWdAll

noncomputable section PartWd1

namespace Formalism.MainNotions.BridgeLemma₅

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.TopsChoicePartA

section WdAbstract

variable {m : ℕ} {E : Type*} [AddCommGroup E] [Module ℂ E]

def wdNice (D : Set (Fin m → ℂ)) (O : Op m E) : Prop :=
  LocalOn D O ∧ ∀ x ∈ D, O 0 x = 0

theorem wdNice.comp {D : Set (Fin m → ℂ)} {O P : Op m E} (hO : wdNice D O) (hP : wdNice D P) :
    wdNice D (fun f => O (P f)) :=
  ⟨fun φ ψ h x hx => hO.1 _ _ (fun y hy => hP.1 φ ψ h y hy) x hx,
   fun x hx => by
    have := hO.1 (P 0) 0 (fun y hy => by simpa using hP.2 y hy) x hx
    show O (P 0) x = 0
    rw [this]; exact hO.2 x hx⟩

theorem wdNice.sum {D : Set (Fin m → ℂ)} {ι : Type*} (s : Finset ι) {O : ι → Op m E} (h : ∀ i ∈ s, wdNice D (O i)) :
    wdNice D (fun f => ∑ i ∈ s, O i f) :=
  ⟨fun φ ψ hφ x hx => by
    simp only [Finset.sum_apply]
    exact Finset.sum_congr rfl fun i hi => (h i hi).1 φ ψ hφ x hx,
   fun x hx => by
    simp only [Finset.sum_apply]
    exact Finset.sum_eq_zero fun i hi => (h i hi).2 x hx⟩

def wdNiceMod (D : Set (Fin m → ℂ)) {n : ℕ} (M : Mod m E n) : Prop :=
  (∀ α β, wdNice D (M.RR α β)) ∧ ∀ Y a b, wdNice D (M.TT Y a b)

def wdOff (w : Word) (Y : ℂ) : Prop :=
  ∀ l ∈ w, Y - (l.2 : ℂ) ≠ 1 ∧ (l.2 : ℂ) - Y ≠ 1

def wdCol (D : Set (Fin m → ℂ)) (O : Op m E) {n : ℕ} (M : Mod m E n) (Y : ℂ) : Prop :=
  ∀ (γ : AuxiliarySlotStates n) (f : (Fin m → ℂ) → E), ∀ x ∈ D, M.TT Y (0, γ) (0, e1s n) f x = if γ = e1s n then O f x else 0

def wdProd (Q : ℂ → Matrix (Fin 2) (Fin 2) (Op m E)) : Word → Op m E
  | [] => idOp
  | l :: w => fun φ => wdProd Q w (Q (l.2 : ℂ) 0 0 φ)

end WdAbstract

end Formalism.MainNotions.BridgeLemma₅

end PartWd1

noncomputable section PartWd2

namespace Formalism.MainNotions.BridgeLemma₅

open Formalism.REAL Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.TopsChoicePartA
open scoped ContDiff

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section WdZero

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

variable {Eop : Fin n → Fin n → (Matrix (Fin n) (Fin n) ℂ → E) → (Matrix (Fin n) (Fin n) ℂ → E)}

end WdZero

theorem wd_zero_mem_KKop (L : Lev) : (0 : L.GF) ∈ L.KKop := by
  refine ⟨⟨fun g₀ _ => ⟨Set.univ, 0, isOpen_univ, Set.mem_univ _, contDiffOn_const, fun _ _ _ => rfl⟩, ?_, ?_⟩,
    1, one_pos, fun g hg => absurd rfl hg⟩
  · intro g _ n _ n' _; simp
  · intro g _ h _ h' _; simp

theorem wd_B_zero (L : Lev) : L.B 0 = 0 := by
  funext x; simp [Lev.B, Btr]

end Formalism.MainNotions.BridgeLemma₅

end PartWd2

noncomputable section PartWd3

namespace Formalism.MainNotions.BridgeLemma₅

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.TopsChoicePartA

section WdScalars

variable {m : ℕ} {E : Type*} [AddCommGroup E] [Module ℂ E]

def wdPre (n : ℕ) : Word → List (Formalism.FourierDecayAlt.Wd.Letter ℂ ℕ)
  | [] => []
  | l :: Ls => ⟨l.1, Ls.length + n, (l.2 : ℂ)⟩ :: wdPre n Ls

def wdFac (Y : ℝ) : Word → ℝ
  | [] => 1
  | l :: w => wdFac Y w * (if l.1 then (Y - l.2 + 1) / (Y - l.2) else (l.2 - Y) / (l.2 - Y - 1))

end WdScalars

section WdKap

open Formalism.FourierDecayAlt.Wd

variable {S : Type}

def wdF (L : List (Formalism.FourierDecayAlt.Wd.Letter ℂ S)) (Y : ℂ) : ℂ := (L.map fun l => (Y - l.pt + 1) / (Y - l.pt)).prod

end WdKap

end Formalism.MainNotions.BridgeLemma₅

end PartWd3

noncomputable section PartWd4

namespace Formalism.MainNotions.BridgeLemma₅

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.TopsChoicePartA Formalism.MainNotions.S.UnitaryLevelOperators

def stDualListOn (P : Word → Prop) (C Co Cd : ℝ) : Prop :=
  ∀ (L : Lev) (u u' : Fin (L.k0 + 1) → ℝ) (I : Set ℝ), HypC L u u' I →
    ∀ R, L.IsRadQQ R → ∀ (h : L.Haar) (A : ℝ) (mm : ℕ), h.Ok →
    ∀ (w Ls : Word), P Ls → Big C L (Ls ++ w).length A mm → (∀ l ∈ Ls, l.1 = true) →
      (Ls ++ w).Pairwise (fun a b => 3 ≤ |a.2 - b.2|) →
      (∀ i : Fin (Ls ++ w).length, (∑ j : Fin (Ls ++ w).length,
        if j = i then 0 else 1 / |((Ls ++ w).get i).2 - ((Ls ++ w).get j).2|) ≤ Co) →
      (∀ l ∈ Ls, (L.wmod R (sCut u u' I) u u' w).q (l.2 : ℂ) ≠ 0) →
      L.PosOn (L.ImgK h A mm) (modL false (L.wmod R (sCut u u' I) u u' w) Ls).RR →
      ∀ x₁ x₂ : AuxiliarySlotStates (Ls ++ w).length → L.PF, (∀ α, x₁ α ∈ L.ImgK h A mm) → (∀ α, x₂ α ∈ L.ImgK h A mm) →
        Complex.normSq (L.form (JL (L.wmod R (sCut u u' I) u u' w).RR Ls) x₁ x₂) ≤
          Cd ^ Ls.length * (L.form (modL false (L.wmod R (sCut u u' I) u u' w) Ls).RR x₁ x₁).re *
            (L.form (modL true (L.wmod R (sCut u u' I) u u' w) Ls).RR x₂ x₂).re /
              (Ls.map fun l => ((L.wmod R (sCut u u' I) u u' w).q (l.2 : ℂ)).re).prod

end Formalism.MainNotions.BridgeLemma₅

end PartWd4

noncomputable section PartWd6

namespace Formalism.MainNotions.BridgeLemma₅

open Formalism.REAL Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.TopsChoicePartA
open scoped ContDiff

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def wdQQStable (L : Lev) : Prop := ∀ (Y : ℂ) (a b : Fin 2), ∀ J ∈ L.KKop, L.QQ Y a b J ∈ L.KKop

theorem wd_KKop_add (L : Lev) {J₁ J₂ : L.GF} (h₁ : J₁ ∈ L.KKop) (h₂ : J₂ ∈ L.KKop) : J₁ + J₂ ∈ L.KKop := by
  obtain ⟨⟨s₁, n₁, w₁⟩, ε₁, e₁, k₁⟩ := h₁
  obtain ⟨⟨s₂, n₂, w₂⟩, ε₂, e₂, k₂⟩ := h₂
  refine ⟨⟨fun g₀ hg => ?_, fun g hg n hn n' hn' => ?_, fun g hg h hh h' hh' => ?_⟩, min ε₁ ε₂, lt_min e₁ e₂,
    fun g hg => ?_⟩
  · obtain ⟨U₁, F₁, o₁, m₁, c₁, a₁⟩ := s₁ g₀ hg
    obtain ⟨U₂, F₂, o₂, m₂, c₂, a₂⟩ := s₂ g₀ hg
    exact ⟨U₁ ∩ U₂, F₁ + F₂, o₁.inter o₂, ⟨m₁, m₂⟩,
      (c₁.mono Set.inter_subset_left).add (c₂.mono Set.inter_subset_right),
      fun g hgU hgH => by simp [a₁ g hgU.1 hgH, a₂ g hgU.2 hgH]⟩
  · simp only [Pi.add_apply, n₁ g hg n hn n' hn', n₂ g hg n hn n' hn', smul_add]
  · simp only [Pi.add_apply, w₁ g hg h hh h' hh', w₂ g hg h hh h' hh', ContinuousLinearMap.add_comp,
      ContinuousLinearMap.comp_add]
  · by_cases h1 : J₁ g = 0
    · have h2 : J₂ g ≠ 0 := fun h2 => hg (by simp [h1, h2])
      exact le_trans (min_le_right _ _) (k₂ g h2)
    · exact le_trans (min_le_left _ _) (k₁ g h1)

theorem wd_B_add (L : Lev) (J₁ J₂ : L.GF) : L.B (J₁ + J₂) = L.B J₁ + L.B J₂ := by
  funext x
  by_cases hx : x ∈ BDom (L.k0 + 1) L.r L.z L.z' <;> simp [Lev.B, Btr, hx]

theorem wd_Img_zero (L : Lev) : (0 : L.PF) ∈ L.Img := ⟨0, wd_zero_mem_KKop L, (wd_B_zero L).symm⟩

theorem wd_Img_add (L : Lev) {φ ψ : L.PF} (h₁ : φ ∈ L.Img) (h₂ : ψ ∈ L.Img) : φ + ψ ∈ L.Img := by
  obtain ⟨J₁, k₁, rfl⟩ := h₁
  obtain ⟨J₂, k₂, rfl⟩ := h₂
  exact ⟨J₁ + J₂, wd_KKop_add L k₁ k₂, (wd_B_add L J₁ J₂).symm⟩

def wdPin (L : Lev) (O O' : L.POp) : Prop :=
  LocalOn L.BD O ∧ LocalOn L.BD O' ∧ ∀ φ ∈ L.Img, ∃ ψ ∈ L.Img, ∀ x ∈ L.BD, O φ x = ψ x ∧ O' φ x = ψ x

theorem wdPin.comp {L : Lev} {O O' P P' : L.POp} (hO : wdPin L O O') (hP : wdPin L P P') :
    wdPin L (fun f => O (P f)) (fun f => O' (P' f)) := by
  refine ⟨fun φ ψ h x hx => hO.1 _ _ (fun y hy => hP.1 φ ψ h y hy) x hx,
    fun φ ψ h x hx => hO.2.1 _ _ (fun y hy => hP.2.1 φ ψ h y hy) x hx, fun φ hφ => ?_⟩
  obtain ⟨ψ, hψ, e⟩ := hP.2.2 φ hφ
  obtain ⟨χ, hχ, e'⟩ := hO.2.2 ψ hψ
  exact ⟨χ, hχ, fun x hx => ⟨(hO.1 _ ψ (fun y hy => (e y hy).1) x hx).trans (e' x hx).1,
    (hO.2.1 _ ψ (fun y hy => (e y hy).2) x hx).trans (e' x hx).2⟩⟩

theorem wdPin.sum {L : Lev} {ι : Type*} [Fintype ι] {O O' : ι → L.POp} (h : ∀ i, wdPin L (O i) (O' i)) :
    wdPin L (fun f => ∑ i, O i f) (fun f => ∑ i, O' i f) := by
  refine ⟨fun φ ψ hφ x hx => ?_, fun φ ψ hφ x hx => ?_, fun φ hφ => ?_⟩
  · simp only [Finset.sum_apply]
    exact Finset.sum_congr rfl fun i _ => (h i).1 φ ψ hφ x hx
  · simp only [Finset.sum_apply]
    exact Finset.sum_congr rfl fun i _ => (h i).2.1 φ ψ hφ x hx
  · choose ψ hψ using fun i => (h i).2.2 φ hφ
    refine ⟨∑ i, ψ i, Finset.sum_induction _ (· ∈ L.Img) (fun _ _ => wd_Img_add L) (wd_Img_zero L) fun i _ => (hψ i).1,
      fun x hx => ?_⟩
    simp only [Finset.sum_apply]
    exact ⟨Finset.sum_congr rfl fun i _ => ((hψ i).2 x hx).1, Finset.sum_congr rfl fun i _ => ((hψ i).2 x hx).2⟩

def wdPinMod (L : Lev) {n : ℕ} (M M' : Mod (L.r + 1) L.Hom n) : Prop :=
  (∀ α β, wdPin L (M.RR α β) (M'.RR α β)) ∧ ∀ Y a b, wdPin L (M.TT Y a b) (M'.TT Y a b)

end Formalism.MainNotions.BridgeLemma₅

end PartWd6

noncomputable section PartWd8

namespace Formalism.MainNotions.BridgeLemma₅

open Formalism.REAL Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.TopsChoicePartA
open scoped ContDiff

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section WdHom

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

variable {Eop : Fin n → Fin n → (Matrix (Fin n) (Fin n) ℂ → E) → (Matrix (Fin n) (Fin n) ℂ → E)}

end WdHom

def wdHom (L : Lev) (O : L.POp) : Prop :=
  wdPin L O O ∧ ∀ (c : ℂ), ∀ φ ∈ L.Img, ∀ x ∈ L.BD, O (c • φ) x = c • O φ x

theorem wdHom.comp {L : Lev} {O P : L.POp} (hO : wdHom L O) (hP : wdHom L P) : wdHom L (fun f => O (P f)) := by
  refine ⟨hO.1.comp hP.1, fun c φ hφ x hx => ?_⟩
  obtain ⟨ψ, hψ, e⟩ := hP.1.2.2 φ hφ
  have h1 : O (P (c • φ)) x = O (c • ψ) x :=
    hO.1.1 _ _ (fun y hy => by rw [hP.2 c φ hφ y hy, (e y hy).1]; rfl) x hx
  have h2 : O (P φ) x = O ψ x := hO.1.1 _ _ (fun y hy => (e y hy).1) x hx
  show O (P (c • φ)) x = c • O (P φ) x
  rw [h1, h2, hO.2 c ψ hψ x hx]

theorem wdHom.sum {L : Lev} {ι : Type*} [Fintype ι] {O : ι → L.POp} (h : ∀ i, wdHom L (O i)) :
    wdHom L (fun f => ∑ i, O i f) := by
  refine ⟨wdPin.sum fun i => (h i).1, fun c φ hφ x hx => ?_⟩
  simp only [Finset.sum_apply, Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ => (h i).2 c φ hφ x hx

def wdHomMod (L : Lev) {n : ℕ} (M : Mod (L.r + 1) L.Hom n) : Prop :=
  (∀ α β, wdHom L (M.RR α β)) ∧ ∀ Y a b, wdHom L (M.TT Y a b)

end Formalism.MainNotions.BridgeLemma₅

end PartWd8

noncomputable section PartWd7

namespace Formalism.MainNotions.BridgeLemma₅

open Formalism.MainNotions.S Formalism.MainNotions.S.TopsChoicePartA

def wdS (Y : ℝ) (w : Word) : ℝ := (w.map fun l => 1 / |Y - l.2|).sum

end Formalism.MainNotions.BridgeLemma₅

end PartWd7

noncomputable section PartWd5

namespace Formalism.MainNotions.BridgeLemma₅

open Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.UnitaryLevelOperators

def stCOpen (C : ℝ) : Prop := stC_module C ∧ stC_rrherm C ∧ stC_tele ∧ stC_dual C ∧ cuspSpanWaveCondition

end Formalism.MainNotions.BridgeLemma₅

end PartWd5

end PartWdAll

section PartLc

namespace Formalism.MainNotions.BridgeLemma₅

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.TopsChoicePartA Formalism.MainNotions.S.UnitaryLevelOperators Matrix

end Formalism.MainNotions.BridgeLemma₅

end PartLc

section PartFrAll

section PartFr1

namespace Formalism.MainNotions.BridgeLemma₅

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.TopsChoicePartA Formalism.MainNotions.S.LevR

def frPos (z : ℂ) : Prop := ∃ t : ℝ, 0 < t ∧ z = (t : ℂ)

theorem frPos.mul {z w : ℂ} (h : frPos z) (h' : frPos w) : frPos (z * w) := by
  obtain ⟨t, ht, rfl⟩ := h
  obtain ⟨s, hs, rfl⟩ := h'
  exact ⟨t * s, mul_pos ht hs, by push_cast; rfl⟩

theorem frPos.div {z w : ℂ} (h : frPos z) (h' : frPos w) : frPos (z / w) := by
  obtain ⟨t, ht, rfl⟩ := h
  obtain ⟨s, hs, rfl⟩ := h'
  exact ⟨t / s, div_pos ht hs, by push_cast; rfl⟩

theorem frPos.one : frPos 1 := ⟨1, one_pos, by simp⟩

def frFar (w : List (Bool × ℝ)) (t : ℝ) : Prop := ∀ a ∈ w, 1 < |t - a.2|

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {B : Base E} {r : ℕ} (C : Ctx B r)

structure frQRec (q0 : ℂ → ℂ) : Prop where
  nil : ∀ Y, C.qw [] Y = q0 Y
  plus : ∀ (ya : ℝ) (w : List (Bool × ℝ)) (Y : ℂ),
    C.qw ((true, ya) :: w) Y = C.qw w Y * ((Y - (ya : ℂ)) + 1) / (Y - (ya : ℂ))
  minus : ∀ (yb : ℝ) (w : List (Bool × ℝ)) (Y : ℂ),
    C.qw ((false, yb) :: w) Y = C.qw w Y * ((yb : ℂ) - Y) / (((yb : ℂ) - Y) - 1)

variable {C}

end Abstract

end Formalism.MainNotions.BridgeLemma₅

end PartFr1

section PartFr2

namespace Formalism.MainNotions.BridgeLemma₅

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.TopsChoicePartA Formalism.MainNotions.S.LevR Formalism.MainNotions.InterlacingSignCuts

end Formalism.MainNotions.BridgeLemma₅

end PartFr2

section PartFr3

namespace Formalism.MainNotions.BridgeLemma₅

open Polynomial Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.I

section Ring

variable {A : Type} [Ring A] [Algebra ℂ A] {r : ℕ}

noncomputable def frEv (Y : ℂ) : A[X] →+* A :=
  Polynomial.eval₂RingHom' (RingHom.id A) (algebraMap ℂ A Y) (fun a => (Algebra.commutes Y a).symm)

theorem frEv_apply (Y : ℂ) (P : A[X]) : frEv Y P = P.eval₂ (RingHom.id A) (algebraMap ℂ A Y) := rfl

@[simp] theorem frEv_X (Y : ℂ) : frEv (A := A) Y X = algebraMap ℂ A Y := by simp [frEv_apply]

@[simp] theorem frEv_C (Y : ℂ) (a : A) : frEv Y (C a) = a := by simp [frEv_apply]

def frEx (f : Fin r → A) : ℕ → A := fun n => if h : n - 1 < r then f ⟨n - 1, h⟩ else 0

end Ring

end Formalism.MainNotions.BridgeLemma₅

end PartFr3

section PartFr4

namespace Formalism.MainNotions.BridgeLemma₅

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.TopsChoicePartA Formalism.MainNotions.S.LevR Formalism.MainNotions.S.UnitaryLevelOperators Formalism.MainNotions.LevelRaisingOperators
open scoped ContDiff

section Transfer

variable {m : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {U : Set (Fin m → ℂ)}

open Classical in

noncomputable def frOp (U : Set (Fin m → ℂ)) (a : Module.End ℂ (SmU U E)) : Op m E := fun φ =>
  if h : ContDiffOn ℝ ∞ φ U then
    (a ⟨U.indicator φ, h.congr (fun _ hy => Set.indicator_of_mem hy _), fun _ hy => Set.indicator_of_notMem hy _⟩).1
  else 0

end Transfer

section Level

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {B : Base E} {r : ℕ}

variable (C : Ctx B r) (Γ : GCtx E r)

def frLev0Open (h : (Fin (r + 1) → ℂ) → E →L[ℂ] E) (SS : Fin B.k0 → (Fin (r + 1) → ℂ) → E →L[ℂ] E) : Prop :=
  (∀ n (hn : n ≤ r), ∀ Y : ℂ,
    let u := Y + ((Γ.nV : ℂ) - 1) / 2
    Γ.cminor n hn u ∈ Γ.PolyInv ∧ Γ.Rad (Γ.cminor n hn u) (DnVn n hn Y 0) ∧
    (∀ hn1 : n + 1 ≤ r, Γ.Rad (Γ.cminor n hn u) (DnVn (n + 1) hn1 Y 1))) ∧
  (∀ Y : ℂ, ∃ Θ ∈ Γ.PolyInv, Γ.Rad Θ (Rhat r C.Q Y)) ∧
  (∀ l, SSnat (SS l) ∈ C.AA) ∧ (∀ Y : ℂ, R0 r B.T B.T' h Y ∈ C.AA) ∧
  (∀ Y : ℂ, NoPoleRho B Y →
    C.OpEq (R0 r B.T B.T' h Y)
      (mulE (xInvFib B.rhoP C.P Y) ∘ Rhat r C.Q Y -
        ∑ l, mulE (shInv B.rhoP C.P l Y) ∘ SSnat (SS l) ∘ Ahat r Y)) ∧
  (∀ Y : ℂ, NoPoleRho B Y →
    C.OpEq (mulE (xInvFib B.rhoP C.P Y) ∘ C.RhatV Y)
      (weightedMirrorLevelOperator r B.T B.T' (C.fstar h) Y +
        ∑ l, mulE (shInv B.rhoP C.P l Y) ∘ (mulF (fun x => Dr x / star (Dr x)) ∘ mulE (C.fstar (SS l))) ∘ AhatV r Y))

def frFrameROpen (okF : ℕ → Prop) (h : (Fin (r + 1) → ℂ) → E →L[ℂ] E)
    (SS : Fin B.k0 → (Fin (r + 1) → ℂ) → E →L[ℂ] E) : Prop :=
  ∀ w : List (Bool × ℝ), Admissible B.I w →
    (okF w.length → ∀ φ ψ : (Fin w.length → Fin 2) → (Fin (r + 1) → ℂ) → E, (∀ s, φ s ∈ C.clsF) → (∀ s, ψ s ∈ C.clsF) →
      C.form (C.RR w) φ ψ = C.bsum (C.aapp (C.dM w) (C.aapp (C.F h SS w) φ)) (C.aapp (C.F h SS w) ψ)) ∧
    (∀ Y : ℂ, NoPoleRho B Y → OffPoles w Y →
      AEq C (C.amul (C.F h SS w) (C.TT w Y 1 1)) (C.amul (C.alm (mulF C.gg) (C.toAM (C.xM w Y))) (C.F h SS w)) ∧
      AEq C (C.amul (C.F h SS w) (C.TT w Y 1 0))
        (C.amul (C.alm (mulF C.gg) (C.toAM (C.xM w Y))) (C.amul (C.lfr h SS w Y) (C.F h SS w))) ∧
      (∀ s t, mulE (C.ee SS w Y s t) ∈ C.AA))

end Level

def frLevelOpen (C Cv C1 C2 : ℝ) : Prop :=
  ∀ (Lt : Lev) (u u' : Fin (Lt.k0 + 1) → ℝ) (I : Set ℝ) (hr : Lt.r + 0 = Lt.r),
    HypC Lt u u' I → HypC (Lt.down Lt.r 0 hr) u u' I →
    ∀ R : ℂ → Matrix (Fin 2) (Fin 2) (Lt.down Lt.r 0 hr).POp, (Lt.down Lt.r 0 hr).IsRadQQ R →
    ∃ (h : (Fin 1 → ℂ) → Lt.Hom →L[ℂ] Lt.Hom) (SS : Fin Lt.k0 → (Fin 1 → ℂ) → Lt.Hom →L[ℂ] Lt.Hom),
      (∀ (hh : (Lt.down Lt.r 0 hr).Haar) (A : ℝ) (mm : ℕ), hh.Ok → Big C Lt 0 A mm →
        stLevR (ctxR Lt u u' I hr R ((Lt.down Lt.r 0 hr).ImgK hh A mm)) h SS) ∧
      frLev0Open (ctx0 Lt u u' I hr R) (gctxOf Lt) (pullZ h) (fun l => pullZ (SS l)) ∧
      RulesOpen Lt h SS ∧
      stProd (ctx0 Lt u u' I hr R) Cv (pullZ h) (fun l => pullZ (SS l)) ∧
      (∀ (hh : (Lt.down Lt.r 0 hr).Haar) (A : ℝ) (mm : ℕ), hh.Ok →
        frFrameROpen (ctxR Lt u u' I hr R ((Lt.down Lt.r 0 hr).ImgK hh A mm)) (fun N => Big C Lt N A mm) h SS) ∧
      stFrameG (ctxR Lt u u' I hr R (Lt.down Lt.r 0 hr).Img) (ctx0 Lt u u' I hr R) (Lt.liftDown Lt.r 0 hr)
        pullZ h SS ∧
      stRes (ctxR Lt u u' I hr R (Lt.down Lt.r 0 hr).Img) C1 C2 SS

end Formalism.MainNotions.BridgeLemma₅

end PartFr4

section PartFr5

namespace Formalism.MainNotions.BridgeLemma₅

open Polynomial Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.TopsChoicePartA Formalism.MainNotions.S.LevR Formalism.MainNotions.S.UnitaryLevelOperators

section Rat

variable {V : Type} [Ring V] [Algebra ℂ V]

theorem frEv_map (Y : ℂ) (p : ℂ[X]) : frEv Y (p.map (algebraMap ℂ V)) = algebraMap ℂ V (p.eval Y) := by
  rw [frEv_apply, Polynomial.eval₂_map, RingHom.id_comp, Polynomial.eval₂_at_apply]

noncomputable def frPi (Γ : Finset ℂ) : ℂ[X] := ∏ γ ∈ Γ, (X - C γ)

theorem frPi_eval (Γ : Finset ℂ) (Y : ℂ) : (frPi Γ).eval Y = ∏ γ ∈ Γ, (Y - γ) := by
  simp [frPi, Polynomial.eval_prod]

def frSR (Γ : Finset ℂ) (f : ℂ → V) : Prop :=
  ∃ N : V[X], ∀ Y ∉ Γ, (∏ γ ∈ Γ, (Y - γ)) • f Y = frEv Y N

theorem frSR.congr {Γ : Finset ℂ} {f g : ℂ → V} (h : frSR Γ f) (e : ∀ Y, g Y = f Y) : frSR Γ g := by
  obtain ⟨N, hN⟩ := h
  exact ⟨N, fun Y hY => by rw [e, hN Y hY]⟩

theorem frSR.mono {Γ Γ' : Finset ℂ} {f : ℂ → V} (h : frSR Γ f) (hs : Γ ⊆ Γ') : frSR Γ' f := by
  obtain ⟨N, hN⟩ := h
  refine ⟨(frPi (Γ' \ Γ)).map (algebraMap ℂ V) * N, fun Y hY => ?_⟩
  rw [map_mul, frEv_map, frPi_eval, ← hN Y (fun h => hY (hs h)), ← Finset.prod_sdiff hs, mul_smul, Algebra.smul_def]

theorem frSR.add {Γ : Finset ℂ} {f g : ℂ → V} (h : frSR Γ f) (h' : frSR Γ g) : frSR Γ (fun Y => f Y + g Y) := by
  obtain ⟨N, hN⟩ := h
  obtain ⟨N', hN'⟩ := h'
  exact ⟨N + N', fun Y hY => by rw [smul_add, hN Y hY, hN' Y hY, map_add]⟩

theorem frSR.mulL {Γ : Finset ℂ} {f : ℂ → V} (a : V) (h : frSR Γ f) : frSR Γ (fun Y => a * f Y) := by
  obtain ⟨N, hN⟩ := h
  exact ⟨C a * N, fun Y hY => by rw [map_mul, frEv_C, ← hN Y hY, mul_smul_comm]⟩

theorem frSR.mulR {Γ : Finset ℂ} {f : ℂ → V} (b : V) (h : frSR Γ f) : frSR Γ (fun Y => f Y * b) := by
  obtain ⟨N, hN⟩ := h
  exact ⟨N * C b, fun Y hY => by rw [map_mul, frEv_C, ← hN Y hY, smul_mul_assoc]⟩

theorem frSR.const (Γ : Finset ℂ) (a : V) : frSR Γ (fun _ => a) :=
  ⟨(frPi Γ).map (algebraMap ℂ V) * C a, fun Y _ => by
    rw [map_mul, frEv_map, frPi_eval, frEv_C, Algebra.smul_def]⟩

theorem frSR.smul {Γ : Finset ℂ} {f : ℂ → V} (c : ℂ) (h : frSR Γ f) : frSR Γ (fun Y => c • f Y) :=
  (h.mulL (algebraMap ℂ V c)).congr fun Y => by rw [Algebra.smul_def]

theorem frSR.neg {Γ : Finset ℂ} {f : ℂ → V} (h : frSR Γ f) : frSR Γ (fun Y => -f Y) :=
  (h.smul (-1)).congr fun Y => by simp

theorem frSR.sub {Γ : Finset ℂ} {f g : ℂ → V} (h : frSR Γ f) (h' : frSR Γ g) : frSR Γ (fun Y => f Y - g Y) :=
  (h.add h'.neg).congr fun Y => by rw [sub_eq_add_neg]

theorem frSR.sum {Γ : Finset ℂ} {ι : Type*} (s : Finset ι) {f : ι → ℂ → V} (h : ∀ i ∈ s, frSR Γ (f i)) :
    frSR Γ (fun Y => ∑ i ∈ s, f i Y) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using frSR.const Γ (0 : V)
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i s)).add (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem frSR.quot {Γ : Finset ℂ} {f : ℂ → V} (h : frSR Γ f) {y : ℂ} (hy : y ∉ Γ) (c : V) :
    frSR (insert y Γ) (fun Y => (Y - y)⁻¹ • (f Y - c)) := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N - (frPi Γ).map (algebraMap ℂ V) * C c, fun Y hY => ?_⟩
  have h1 : Y ≠ y := fun e => hY (e ▸ Finset.mem_insert_self _ _)
  have h2 : Y ∉ Γ := fun e => hY (Finset.mem_insert_of_mem e)
  rw [Finset.prod_insert hy, map_sub, map_mul, frEv_map, frPi_eval, frEv_C, ← hN Y h2, smul_smul,
    mul_right_comm, mul_inv_cancel₀ (sub_ne_zero.2 h1), one_mul, smul_sub, Algebra.smul_def, Algebra.smul_def]

theorem frSR.frac {Γ : Finset ℂ} {y : ℂ} (hy : y ∈ Γ) (a : V) : frSR Γ (fun Y => (Y - y)⁻¹ • a) := by
  rw [← Finset.insert_erase hy]
  exact ((frSR.const (Γ.erase y) (0 : V)).quot (Finset.notMem_erase y Γ) (-a)).congr fun Y => by simp

end Rat

section Ee

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {B : Base E} {r : ℕ} (C : Ctx B r)
  (SS : Fin B.k0 → (Fin (r + 1) → ℂ) → E →L[ℂ] E)

noncomputable def frGam (Γ0 : Finset ℂ) : List (Bool × ℝ) → Finset ℂ
  | [] => Γ0
  | a :: w => insert (a.2 : ℂ) (frGam Γ0 w)

variable {C SS}

end Ee

end Formalism.MainNotions.BridgeLemma₅

end PartFr5

section PartFr6

namespace Formalism.MainNotions.BridgeLemma₅

open Polynomial Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.TopsChoicePartA Formalism.MainNotions.S.LevR Formalism.MainNotions.S.UnitaryLevelOperators Formalism.MainNotions.LevelRaisingOperators

section Res

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {B : Base E} {r : ℕ} (C : Ctx B r)

def frLines : Prop :=
  ∀ x ∈ C.Dom, ∃ Sx : Finset B.Rho, (∀ ρ ∉ Sx, C.P ρ x = 0) ∧ ∀ ρ ∈ Sx, B.IsType ρ

variable {C}

variable (C)

def frResOpen (C1 C2 : ℝ) (SS : Fin B.k0 → (Fin (r + 1) → ℂ) → E →L[ℂ] E) : Prop :=
  ∀ w : List (Bool × ℝ), Admissible B.I w → Ctx.IsPlus w → (∀ a ∈ w, a.2 ∈ mid3 B) →
    (6 ≤ lenI B → (w.length : ℝ) ≤ lenI B →
      (∀ i : Fin w.length, (∑ j : Fin w.length, if j = i then 0 else 1 / |(w.get i).2 - (w.get j).2|) ≤ C1) →
      ∀ Y Y' : ℝ, Y ∈ mid3 B → Y' ∈ mid3 B → (∀ a ∈ w, 2 < |Y - a.2| ∧ 2 < |Y' - a.2|) →
      (w.map fun a => 1 / |Y - a.2|).sum ≤ C1 → (w.map fun a => 1 / |Y' - a.2|).sum ≤ C1 →
      ∀ x ∈ C.Dom, ∀ v : (Fin w.length → Fin 2) → E,
        wnormSq C (fun s ρ => C.cw w s ρ * C.xw w Y s ρ) x
            (fun s => ∑ t, (C.ee SS w Y s t x - C.ee SS w Y' s t x) (v t)) ≤
          (C2 * |Y - Y'| * ((B.k0 + 1 : ℝ) / lenI B + (w.map fun a => 1 / (|Y - a.2| * |Y' - a.2|)).sum)) ^ 2 *
            wnormSq C (fun s ρ => C.cw w s ρ * C.qw w Y / C.xw w ((Y : ℂ) + 1) s ρ) x v)

end Res

def frLevelOpen2 (C Cv C1 C2 : ℝ) : Prop :=
  ∀ (Lt : Lev) (u u' : Fin (Lt.k0 + 1) → ℝ) (I : Set ℝ) (hr : Lt.r + 0 = Lt.r),
    HypC Lt u u' I → HypC (Lt.down Lt.r 0 hr) u u' I →
    ∀ R : ℂ → Matrix (Fin 2) (Fin 2) (Lt.down Lt.r 0 hr).POp, (Lt.down Lt.r 0 hr).IsRadQQ R →
    ∃ (h : (Fin 1 → ℂ) → Lt.Hom →L[ℂ] Lt.Hom) (SS : Fin Lt.k0 → (Fin 1 → ℂ) → Lt.Hom →L[ℂ] Lt.Hom),
      (∀ (hh : (Lt.down Lt.r 0 hr).Haar) (A : ℝ) (mm : ℕ), hh.Ok → Big C Lt 0 A mm →
        stLevR (ctxR Lt u u' I hr R ((Lt.down Lt.r 0 hr).ImgK hh A mm)) h SS) ∧
      frLev0Open (ctx0 Lt u u' I hr R) (gctxOf Lt) (pullZ h) (fun l => pullZ (SS l)) ∧
      RulesOpen Lt h SS ∧
      stProd (ctx0 Lt u u' I hr R) Cv (pullZ h) (fun l => pullZ (SS l)) ∧
      (∀ (hh : (Lt.down Lt.r 0 hr).Haar) (A : ℝ) (mm : ℕ), hh.Ok →
        frFrameROpen (ctxR Lt u u' I hr R ((Lt.down Lt.r 0 hr).ImgK hh A mm)) (fun N => Big C Lt N A mm) h SS) ∧
      stFrameG (ctxR Lt u u' I hr R (Lt.down Lt.r 0 hr).Img) (ctx0 Lt u u' I hr R) (Lt.liftDown Lt.r 0 hr)
        pullZ h SS ∧
      frResOpen (ctxR Lt u u' I hr R (Lt.down Lt.r 0 hr).Img) C1 C2 SS

def frLinesAll : Prop :=
  ∀ (Lt : Lev) (u u' : Fin (Lt.k0 + 1) → ℝ) (I : Set ℝ) (hr : Lt.r + 0 = Lt.r), HypC (Lt.down Lt.r 0 hr) u u' I →
    ∀ R : ℂ → Matrix (Fin 2) (Fin 2) (Lt.down Lt.r 0 hr).POp, frLines (ctxR Lt u u' I hr R (Lt.down Lt.r 0 hr).Img)

end Formalism.MainNotions.BridgeLemma₅

end PartFr6

section PartFr7

namespace Formalism.MainNotions.BridgeLemma₅

end Formalism.MainNotions.BridgeLemma₅

end PartFr7

section PartFr8

namespace Formalism.MainNotions.BridgeLemma₅

open Formalism.MainNotions

def LevelAdmissibleOpen (D : Formalism.BasicNotions.D7) (CB Ca : ℝ) : Prop :=
  RadialRules.adm1 D CB ∧ RadialRules.adm2 D CB ∧ RadialRules.adm5 D ∧ RadialRules.adm6 D ∧
    (RadialRules.RulesGauge D ∧ RadialRules.ResidueBoundAlt D Ca ∧ RadialRules.RulesCapelli D ∧ RadialRules.RadialRulesCombined D) ∧
    RadialRules.adm8 D ∧ RadialRules.adm9 D Ca ∧ RadialRules.adm10 D CB

end Formalism.MainNotions.BridgeLemma₅

end PartFr8

section PartFr9

namespace Formalism.MainNotions.BridgeLemma₅

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.TopsChoicePartA Formalism.MainNotions.S.LevR Formalism.MainNotions.S.UnitaryLevelOperators

def frLinesU : Prop :=
  ∀ (L : Lev) (u u' : Fin (L.k0 + 1) → ℝ) (I : Set ℝ), HypC L u u' I → ∀ x ∈ L.BD, ∀ ρ : Fin L.k0 → ℝ,
    L.lineP (L.pt x) ρ ≠ 0 → Interlace u ρ

end Formalism.MainNotions.BridgeLemma₅

end PartFr9

end PartFrAll

section PartLb1

namespace Formalism.MainNotions.BridgeLemma₅

open Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.TopsChoicePartA

end Formalism.MainNotions.BridgeLemma₅

end PartLb1

section PartLb2

open MeasureTheory

namespace Formalism.MainNotions.BridgeLemma₅

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.TopsChoicePartA

noncomputable def lbE (r : ℕ) : (Fin (r + 1) → ℂ) ≃ᵐ (Fin r → ℂ) × ℂ :=
  (MeasurableEquiv.piFinSuccAbove (fun _ => ℂ) (Fin.last r)).trans MeasurableEquiv.prodComm

end Formalism.MainNotions.BridgeLemma₅

end PartLb2

section PartLb3

open MeasureTheory

namespace Formalism.MainNotions.BridgeLemma₅

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.TopsChoicePartA

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def abstractSettingExists : Prop :=
  ∀ L : Lev, L.Std → ∀ u u', L.HC u u' → ∀ h : L.Haar, h.Ok →
    ∃ D : Formalism.FourierDecayAlt.B.RealPlaceData (L.k0 + 1) L.r L.Wp L.Wq, D.z = L.z ∧ D.z' = L.z' ∧ D.π = L.π ∧ D.π' = L.π' ∧
      D.μW = h.μW ∧ D.μN = h.μN ∧ D.μW' = h.μW' ∧ D.μsec = L.μsec

def lbCCIncl (CB : ℝ) : Prop :=
  ∀ (L : Lev) (A : ℝ) (mm : ℕ), Big CB L 0 A mm →
    ∃ A' K : ℝ, 2 * ((2 * L.r + (L.k0 + 1) + 1 : ℕ) : ℝ) ^ 2 < A' ∧ ∀ (F : L.GF) (ν : ℝ), L.CC A mm F →
      (∀ w : List (Fin (2 * L.r + (L.k0 + 1) + 1) × Fin (2 * L.r + (L.k0 + 1) + 1)), w.length ≤ mm →
        ∀ g ∈ UH (Hpk (L.k0 + 1) L.r), (1 + Lev.matNorm g) ^ A * ‖L.Eword w F g‖ ≤ ν) →
      Formalism.FourierDecayAlt.B.CCle A' 5 F (K * ν)

end Formalism.MainNotions.BridgeLemma₅

end PartLb3

section PartLb4

open MeasureTheory

namespace Formalism.MainNotions.BridgeLemma₅

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.TopsChoicePartA

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem lb_haarG : Formalism.FourierDecayAlt.B2.HaarGExists :=
  (Formalism.FourierDecayAlt.P.group_measure_from_diagonal Formalism.REAL.uJEmb Formalism.REAL.unimodular Formalism.REAL.ballFinite Formalism.REAL.volGrowth
    Formalism.QuantumDeterminants.hpkFacts Formalism.QuantumDeterminants.uHConj Formalism.FourierDecayAlt.P.haar_measure_unique_up_to_scalar Formalism.FourierDecayAlt.P.unitary_group_closed).1

def lbHaarUp : Prop :=
  (∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (μ : Measure (Mt k r)), inWb k r z → 0 < Tz k r z →
    Formalism.MainNotions.S.IsHaarOn (UWset k r z) μ → Formalism.FourierDecayAlt.B.IsHaarOn (UWset k r z) μ) ∧
  ∀ (k r : ℕ) (μ : Measure (Mt k r)), Formalism.MainNotions.S.IsHaarOn (Nset k r) μ → Formalism.FourierDecayAlt.B.IsHaarOn (Nset k r) μ

def lbRepOfHC : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (u : Fin k → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)), inWb k r z → 0 < Tz k r z →
    Formalism.MainNotions.S.IsHCTypeW k r z u π →
      IsCRepOn (UWset k r z) π ∧ (∀ h ∈ UWset k r z, ∀ v, ‖π h v‖ = ‖v‖) ∧ ContinuousOn π (UWset k r z)

end Formalism.MainNotions.BridgeLemma₅

end PartLb4

section PartLb5

namespace Formalism.MainNotions.BridgeLemma₅

open Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.TopsChoicePartA

structure LemmaBOpen (CB : ℝ) : Prop where

  xi : Formalism.FourierDecayAlt.B.XiExists

  intNorm : Formalism.FourierDecayAlt.B2.IntNormB

  haarUp : lbHaarUp

  repOfHC : lbRepOfHC

  ccIncl : lbCCIncl CB

  adj : LemmaBAdj CB

  rad : LemmaBRad CB

  int : LemmaBInt CB

end Formalism.MainNotions.BridgeLemma₅

end PartLb5

section PartLb6

namespace Formalism.MainNotions.BridgeLemma₅

open Formalism.QuantumDeterminants Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.TopsChoicePartA

def lbPair (CB : ℝ) (L : Lev) (M : ℕ) (F F' : L.GF) : Prop :=
  ∃ (A : ℝ) (mm : ℕ), Big CB L M A mm ∧ L.CC A mm F ∧ L.CC A mm F' ∧ ∃ ε : ℝ, 0 < ε ∧ SuppGe L ε F ∧ SuppGe L ε F'

noncomputable def lbWave (L : Lev) (h : L.Haar) (s : ℂ) (F F' : L.GF) : ℂ :=
  lbeta L h (fun g => fsC s (Zhat (L.k0 + 1) L.r L.z L.z' g 0 0) • F g) F'

def lbSmoothStep (CB : ℝ) : Prop :=
  ∀ (L : Lev) (u u' : Fin (L.k0 + 1) → ℝ) (I : Set ℝ), HypC L u u' I → 0 < L.r → ∀ h : L.Haar, h.Ok →
    ∀ (M : ℕ) (F F' : L.GF), lbPair CB L (M + 1) F F' →
      ∃ (N : ℕ) (G G' : Fin N → L.GF), (∀ i, lbPair CB L M (G i) (G' i)) ∧
        ∀ s : ℂ, s * lbWave L h s F F' = ∑ i, lbWave L h s (G i) (G' i)

def lbSmoothBase (CB : ℝ) : Prop :=
  ∀ (L : Lev) (u u' : Fin (L.k0 + 1) → ℝ) (I : Set ℝ), HypC L u u' I → 0 < L.r → ∀ h : L.Haar, h.Ok →
    ∀ F F' : L.GF, lbPair CB L 0 F F' → ∃ C : ℝ, ∀ s : ℂ, ‖lbWave L h s F F'‖ ≤ C

end Formalism.MainNotions.BridgeLemma₅

end PartLb6

section PartLb7

open MeasureTheory

namespace Formalism.MainNotions.BridgeLemma₅

open Formalism.QuantumDeterminants Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.TopsChoicePartA

end Formalism.MainNotions.BridgeLemma₅

end PartLb7

section PartTaAll

section PartTa1

open NumberField Finset Filter Topology
open scoped nonZeroDivisors ComplexConjugate ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₅

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalFrameAxioms Formalism.FourierDecayAlt.TA Formalism.MainNotions.InterlacingSignCuts

attribute [local instance] Classical.propDecidable

theorem ta_restrict {α : Type*} {S : Set α} {K : α → α → ℂ} (h : PSDKOn S K) :
    PSDK (fun p q => if p ∈ S ∧ q ∈ S then K p q else 0) := by
  intro X a
  have h1 := h (X.filter (· ∈ S)) a (fun p hp => (Finset.mem_filter.1 hp).2)
  refine le_of_le_of_eq h1 ?_
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases hp : p ∈ S
  · rw [if_pos hp, Finset.sum_filter]
    refine Finset.sum_congr rfl fun q _ => ?_
    by_cases hq : q ∈ S <;> simp [hp, hq]
  · rw [if_neg hp]
    symm
    refine Finset.sum_eq_zero fun q _ => ?_
    simp [hp]

theorem ta_pull {α β : Type} {S : Set β} {K : β → β → ℂ} (hK : PSDKOn S K) (P : Finset α) (φ : α → β) (ψ : β → α)
    (hψ : ∀ x ∈ P, ψ (φ x) = x) (hS : ∀ x ∈ P, φ x ∈ S) : PSDOn P (fun x y => K (φ y) (φ x)) := by
  have h1 := pull_psd (ta_restrict hK) P φ ψ hψ
  refine ⟨fun x hx y hy => ?_, fun a => ?_⟩
  · have := h1.1 x hx y hy
    simpa [hS x hx, hS y hy] using this
  · refine le_of_le_of_eq (h1.2 a) ?_
    congr 1
    refine Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => ?_
    simp [hS x hx, hS y hy]

theorem ta_psdk_const {α : Type*} (c : ℂ) (hc : 0 ≤ c) : PSDK (fun _ _ : α => c) := by
  intro X a
  have e : ∑ p ∈ X, ∑ q ∈ X, star (a p) * c * a q = c * (star (∑ p ∈ X, a p) * ∑ q ∈ X, a q) := by
    rw [star_sum, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun q _ => by ring
  rw [e]
  exact mul_nonneg hc (star_mul_self_nonneg _)

section Sets

variable (D : D7)

def taSg (Sg' : ℕ → ℕ → Finset D.host.E) : ℕ → ℕ → Finset D.host.E := fun i s => Sg' (i + s - 1) s

theorem ta_inProd_append (Sg : ℕ → ℕ → Finset D.host.E) : ∀ (l : List (D.host.E × ℕ)) (a : ℕ) (t : D.host.E) (s : ℕ),
    InProd D Sg a l → t ∈ Sg (a + (l.map Prod.snd).sum + 1) s → InProd D Sg a (l ++ [(t, s)])
  | [], a, t, s, _, h => by
      refine ⟨?_, trivial⟩
      simpa using h
  | (t', s') :: l, a, t, s, h, h2 => by
      refine ⟨h.1, ta_inProd_append Sg l (a + s') t s h.2 ?_⟩
      have e : a + s' + (l.map Prod.snd).sum + 1 = a + (((t', s') :: l).map Prod.snd).sum + 1 := by
        simp only [List.map_cons, List.sum_cons]; omega
      rw [e]; exact h2

theorem ta_inProd_PT (Sg' : ℕ → ℕ → Finset D.host.E) (hNZ : NZSg Sg') :
    ∀ n p, p ∈ PT Sg' n → InProd D (taSg D Sg') 0 (sw p) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro p hp
    cases n with
    | zero =>
      simp [PT] at hp; subst hp; exact trivial
    | succ n =>
      obtain ⟨m, hm, h, hh, t, ht, rfl⟩ := (Formalism.FourierDecayAlt.P.TA1.mem_PT_succ Sg' n p).1 hp
      have h0 := ih m (by omega) h hh
      have hpt := Formalism.FourierDecayAlt.P.TA1.isPt_PT Sg' hNZ m h hh
      have e : sw (ext h (n + 1 - m) t) = sw h ++ [(t, n + 1 - m)] := by simp [sw, Formalism.FourierDecayAlt.TA.ext]
      rw [e]
      refine ta_inProd_append D _ _ _ _ _ h0 ?_
      rw [(sw_ok hpt).2]
      show t ∈ Sg' (0 + m + 1 + (n + 1 - m) - 1) (n + 1 - m)
      have e2 : 0 + m + 1 + (n + 1 - m) - 1 = n + 1 := by omega
      rw [e2]; exact ht

theorem ta_heads (Sg' : ℕ → ℕ → Finset D.host.E) (hNZ : NZSg Sg') (n : ℕ) (p : Pt D.host.E) (hp : p ∈ PT Sg' n) :
    ph n p ∈ headsOf D (taSg D Sg') n := by
  show InProd D (taSg D Sg') 0 (ph n p).1
  rw [ph_val (Formalism.FourierDecayAlt.P.TA1.isPt_PT Sg' hNZ n p hp)]
  exact ta_inProd_PT D Sg' hNZ n p hp

end Sets

section Axioms

variable {D : D7} {L : LatticeDataWithDual D} {Kd : KernelData D} (Lv : ℕ → AddSubgroup D.host.E)

theorem axK_of_ArithAxF (h : ArithAxF D L Kd) : AxK (taData D L Kd Lv) := by
  refine ⟨h.1 _ _, fun i hi P hP => ?_⟩
  exact pull_psd (h.2.1 i hi) P (ph i) unsw (fun x hx => unsw_ph (hP x hx))

theorem axE_of_ArithAxF (h : ArithAxF D L Kd) : AxE (taData D L Kd Lv) := fun i h1 h2 => h.2.2.1 i h1 h2

theorem arithmetic_axiom_of_family (h : ArithAxF D L Kd) : KernelSupport (taData D L Kd Lv) := by
  intro i s hs hsi hi p p' t t' hp hp' ht ht' hor
  obtain ⟨j, rfl⟩ : ∃ j, i = j + s := ⟨i - s, by omega⟩
  rw [Nat.add_sub_cancel] at hp hp'
  show Kd.K (j + s) (ph (j + s) (ext p' s t')) (ph (j + s) (ext p s t)) = 0
  rw [ph_ext D hp hs ht, ph_ext D hp' hs ht']
  by_contra hne
  have h2 := h.2.2.2.1 j s hs hi (ph j p') (ph j p) t' t ht' ht hne
  by_cases htop : j + s = D.R.rS + 1 ∧ s = 1
  · rw [if_pos htop] at h2
    rcases hor with hor | hor
    · apply hor
      show _ ∈ (if j + s = D.R.rS + 1 ∧ s = 1 then (⊤ : AddSubgroup D.host.E) else _)
      rw [if_pos htop]; exact AddSubgroup.mem_top _
    · exact hor.2.2 h2.symm
  · rw [if_neg htop] at h2
    rcases hor with hor | hor
    · apply hor
      show _ ∈ (if j + s = D.R.rS + 1 ∧ s = 1 then (⊤ : AddSubgroup D.host.E) else _)
      rw [if_neg htop, Nat.add_sub_cancel, Submodule.mem_toAddSubgroup]
      have := (L.La' (j + 1) s).neg_mem h2
      have e : 1 / t - 1 / t' = -(t'⁻¹ - t⁻¹) := by simp only [one_div]; ring
      rw [e]; exact this
    · exact htop ⟨hor.1, hor.2.1⟩

theorem domAfterA_of_ArithAxF (h : ArithAxF D L Kd) : Formalism.FourierDecayAlt.TC.DomAfterA (taData D L Kd Lv) := by
  intro Sg' hNZ
  obtain ⟨Th, hTh⟩ := h.2.2.2.2 (taSg D Sg')
  refine ⟨fun i s t p p' => Th (i - s) s t (ph (i - s) p') (ph (i - s) p), ?_⟩
  intro i s hs hsi hi
  obtain ⟨j, rfl⟩ : ∃ j, i = j + s := ⟨i - s, by omega⟩
  obtain ⟨hdom, hper, _, hsum⟩ := hTh j s hs hi
  have e : j + s - s = j := by omega
  have hPt : ∀ x ∈ PT Sg' j, IsPt j x := fun x hx => Formalism.FourierDecayAlt.P.TA1.isPt_PT Sg' hNZ j x hx
  have hHd : ∀ x ∈ PT Sg' j, ph j x ∈ headsOf D (taSg D Sg') j := fun x hx => ta_heads D Sg' hNZ j x hx
  have hSg : ∀ t, t ∈ Sg' (j + s) s → t ∈ taSg D Sg' (j + 1) s := by
    intro t ht
    show t ∈ Sg' (j + 1 + s - 1) s
    have e2 : j + 1 + s - 1 = j + s := by omega
    rw [e2]; exact ht
  refine ⟨fun t ht => ?_, fun t ht t' ht' hl p hp p' hp' => ?_, fun R hRS hR => ?_⟩
  · have ht0 : t ≠ 0 := hNZ _ _ t ht
    show PSDOn (PT Sg' (j + s - s)) (fun p p' => Th (j + s - s) s t (ph (j + s - s) p') (ph (j + s - s) p) -
      Kd.K (j + s) (ph (j + s) (ext p' s t)) (ph (j + s) (ext p s t)))
    rw [e]
    have h1 := ta_pull (hdom t ht0 (hSg t ht)) (PT Sg' j) (ph j) unsw (fun x hx => unsw_ph (hPt x hx)) hHd
    refine ⟨fun x hx y hy => ?_, fun a => ?_⟩
    · have := h1.1 x hx y hy
      beta_reduce at this ⊢
      rw [ph_ext D (hPt x hx) hs ht0, ph_ext D (hPt y hy) hs ht0]
      exact this
    · have := h1.2 a
      refine le_of_le_of_eq this ?_
      congr 1
      refine Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => ?_
      beta_reduce
      rw [ph_ext D (hPt x hx) hs ht0, ph_ext D (hPt y hy) hs ht0]
  · show Th (j + s - s) s t (ph (j + s - s) p') (ph (j + s - s) p) = Th (j + s - s) s t' (ph (j + s - s) p') (ph (j + s - s) p)
    have hl' : t - t' ∈ L.La (j + 1) s := by
      have : t - t' ∈ (L.La (j + s - s + 1) s).toAddSubgroup := hl
      rwa [e, Submodule.mem_toAddSubgroup] at this
    rw [e] at hp hp' ⊢
    have := hper t' (t - t') hl' (ph j p') (hHd p' hp') (ph j p) (hHd p hp)
    rwa [add_sub_cancel] at this
  · show PSDOn (PT Sg' (j + s - s)) (fun p p' => ((1 + Kd.e (j + s) : ℝ) : ℂ) * Kd.K (j + s - s) (ph (j + s - s) p') (ph (j + s - s) p) -
      ∑ t ∈ R, Th (j + s - s) s t (ph (j + s - s) p') (ph (j + s - s) p))
    have hR' : ∀ t ∈ R, ∀ t' ∈ R, t - t' ∈ L.La (j + 1) s → t = t' := fun t ht t' ht' hm => by
      refine hR t ht t' ht' ?_
      show t - t' ∈ (L.La (j + s - s + 1) s).toAddSubgroup
      rw [e, Submodule.mem_toAddSubgroup]; exact hm
    rw [e]
    have h1 := ta_pull (hsum R hR') (PT Sg' j) (ph j) unsw (fun x hx => unsw_ph (hPt x hx)) hHd
    have e2 : ((1 + Kd.e (j + s) : ℝ) : ℂ) = 1 + (Kd.e (j + s) : ℂ) := by push_cast; ring
    rw [e2]
    exact h1

end Axioms

def taKer0 (D : D7) (e : ℕ → ℝ) : KernelData D where
  K := fun i _ _ => if i = 0 then 1 else 0
  Th := fun _ _ _ _ _ => 0
  e := e

theorem ta_arith0 (D : D7) (L : LatticeDataWithDual D) (e : ℕ → ℝ) (he : ∀ i, 1 ≤ i → i ≤ D.R.rS + 1 → 0 ≤ e i ∧ e i ≤ 1) :
    ArithAx D L (taKer0 D e) := by
  refine ⟨fun p q => by simp [taKer0], fun i _ => ?_, he, ?_, ?_⟩
  · show PSDK (fun _ _ => if i = 0 then (1 : ℂ) else 0)
    exact ta_psdk_const _ (by split_ifs <;> simp)
  · intro j s hs _ h h' t t' ht ht' hne
    exfalso; apply hne
    show (if j + s = 0 then (1 : ℂ) else 0) = 0
    rw [if_neg (by omega)]
  · intro j s hs hjs
    refine ⟨fun t ht => ?_, fun t l _ => rfl, fun t => ta_psdk_const 0 le_rfl, fun X _ => ?_⟩
    · show PSDK (fun _ _ => (0 : ℂ) - (if j + s = 0 then (1 : ℂ) else 0))
      rw [if_neg (by omega)]
      exact ta_psdk_const _ (by simp)
    · show PSDK (fun _ _ => (1 + (e (j + s) : ℂ)) * (if j = 0 then (1 : ℂ) else 0) - ∑ _t ∈ X, (0 : ℂ))
      refine ta_psdk_const _ ?_
      have h1 : (0 : ℂ) ≤ 1 + (e (j + s) : ℂ) := by
        have := (he (j + s) (by omega) hjs).1
        have h2 : (0 : ℝ) ≤ 1 + e (j + s) := by linarith
        exact_mod_cast h2
      split_ifs <;> simp [h1]

end Formalism.MainNotions.BridgeLemma₅

end

end PartTa1

section PartTa2

open NumberField Finset Filter Topology
open scoped nonZeroDivisors ComplexConjugate ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₅

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalFrameAxioms Formalism.MainNotions.InterlacingSignCuts

theorem ta_psdk_hsInner {Wp Wq : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] : PSDK (fun A B : Wq →L[ℂ] Wp => hsInner A B) := by
  intro X a
  have e : ∑ p ∈ X, ∑ q ∈ X, star (a p) * hsInner p q * a q =
      ∑ i, ⟪∑ q ∈ X, star (a q) • q (stdOrthonormalBasis ℂ Wq i),
        ∑ p ∈ X, star (a p) • p (stdOrthonormalBasis ℂ Wq i)⟫_ℂ := by
    simp only [hsInner, sum_inner, inner_sum, inner_smul_left, inner_smul_right, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_congr rfl (fun p _ => Finset.sum_comm), Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    simp only [Complex.star_def, Complex.conj_conj]
    ring
  rw [e]
  refine Finset.sum_nonneg fun i _ => ?_
  rw [inner_self_eq_norm_sq_to_K]
  have h : (0 : ℂ) ≤ ((‖∑ q ∈ X, star (a q) • q (stdOrthonormalBasis ℂ Wq i)‖ ^ 2 : ℝ) : ℂ) :=
    Complex.zero_le_real.2 (sq_nonneg _)
  rw [Complex.ofReal_pow] at h
  exact h

section Lattices

variable (D : D7)

def taLv (δ : D.host.E) (L : LatticeDataWithDual D) (i : ℕ) : AddSubgroup D.host.E where
  carrier := dualPsi D δ (L.La i 1)
  zero_mem' := fun c _ => ⟨0, by simp⟩
  add_mem' := by
    intro a b ha hb c hc
    obtain ⟨z, hz⟩ := ha c hc
    obtain ⟨w, hw⟩ := hb c hc
    exact ⟨z + w, by rw [add_mul, add_div, map_add, hz, hw]; push_cast; ring⟩
  neg_mem' := by
    intro a ha c hc
    obtain ⟨z, hz⟩ := ha c hc
    exact ⟨-z, by rw [neg_mul, neg_div, map_neg, hz]; push_cast; ring⟩

theorem ta_ne_of_full (M : Submodule ℤ D.host.E) (hM : FullLat D M) (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)
    (h : (M : Set D.host.E) ⊆ (I : Set D.host.E)) : I ≠ 0 := by
  rintro rfl
  have h0 : ∀ x ∈ (M : Set D.host.E), x = 0 := fun x hx => (FractionalIdeal.mem_zero_iff _).1 (h hx)
  have h1 : Submodule.span ℚ (M : Set D.host.E) = ⊥ := Submodule.span_eq_bot.2 h0
  rw [hM.2] at h1
  exact top_ne_bot h1

theorem ta_dual_ne (δ : D.host.E) (hδ : δ ≠ 0) (M : Submodule ℤ D.host.E) (hM : M.FG) :
    ∃ l ∈ dualPsi D δ M, l ≠ 0 := by
  obtain ⟨S, hS⟩ := hM
  let d : ℕ := ∏ c ∈ S, (Algebra.trace ℚ D.host.E c).den
  have hd : d ≠ 0 := Finset.prod_ne_zero_iff.2 fun c _ => (Algebra.trace ℚ D.host.E c).den_nz
  refine ⟨δ * (d : D.host.E), ?_, mul_ne_zero hδ (by exact_mod_cast hd)⟩
  have key : ∀ c : D.host.E, δ * (d : D.host.E) * c / δ = (d : ℚ) • c := by
    intro c
    rw [Algebra.smul_def, map_natCast]
    field_simp
  intro c hc
  rw [← hS] at hc
  rw [key, map_smul]
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨e, he⟩ : (Algebra.trace ℚ D.host.E c).den ∣ d := Finset.dvd_prod_of_mem _ hc
    refine ⟨(Algebra.trace ℚ D.host.E c).num * e, ?_⟩
    rw [smul_eq_mul, he]
    push_cast
    have := Rat.mul_den_eq_num (Algebra.trace ℚ D.host.E c)
    calc ((Algebra.trace ℚ D.host.E c).den : ℚ) * (e : ℚ) * Algebra.trace ℚ D.host.E c
        = (Algebra.trace ℚ D.host.E c * ((Algebra.trace ℚ D.host.E c).den : ℚ)) * e := by ring
      _ = ((Algebra.trace ℚ D.host.E c).num : ℚ) * e := by rw [this]
  | zero => exact ⟨0, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨z, hz⟩ := ha
    obtain ⟨w, hw⟩ := hb
    exact ⟨z + w, by rw [map_add, smul_add, hz, hw]; push_cast; ring⟩
  | smul n a _ ha =>
    obtain ⟨z, hz⟩ := ha
    refine ⟨n * z, ?_⟩
    rw [map_zsmul, smul_comm, hz]
    simp

variable {D}

structure SzPos (C1 C2 N T T' : ℝ) (δ : D.host.E) (x : D.what₂.Tau → LocalDataRealPlace D) : Prop where
  x_pos : ∀ i v, 0 < szX D C1 C2 N T T' δ x i v
  l_pos : ∀ b s v, 0 < szL D C1 C2 N T T' δ x b s v
  p_pos : ∀ b v, 0 < szP D C1 C2 N T T' δ x b v

theorem szOK_of_LatAx {C1 C2 N T T' : ℝ} {δ : D.host.E} {x : D.what₂.Tau → LocalDataRealPlace D} {L : LatticeDataWithDual D}
    (hδ : δ ≠ 0) (hL : LatAx D δ L) (hp : SzPos C1 C2 N T T' δ x) : SzOK D C1 C2 N T T' δ x L (taLv D δ L) where
  x_pos := hp.x_pos
  l_pos := hp.l_pos
  p_pos := hp.p_pos
  aaV_ne := by
    intro b s hbs h0
    obtain ⟨_, hF, _, _, hdual, _⟩ := hL.2 b s hbs
    obtain ⟨l, hl, hl0⟩ := ta_dual_ne D δ hδ (L.La b s) hF.1
    have := hdual hl
    rw [h0] at this
    exact hl0 ((FractionalIdeal.mem_zero_iff _).1 this)
  aaP_ne := by
    intro b s hbs
    obtain ⟨_, _, hF', _, _, hlift⟩ := hL.2 b s hbs
    exact ta_ne_of_full D _ hF' _ hlift
  lift_mem := by
    intro b s hbs l hl
    obtain ⟨_, _, _, _, _, hlift⟩ := hL.2 b s hbs
    exact hlift hl
  dual_mem := by
    intro i h1 h2 l hl
    obtain ⟨_, _, _, _, hdual, _⟩ := hL.2 i 1 ⟨h1, le_rfl, by omega⟩
    exact hdual hl

end Lattices

end Formalism.MainNotions.BridgeLemma₅

end

end PartTa2

section PartTa3

open NumberField Finset Filter Topology
open scoped nonZeroDivisors ComplexConjugate ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₅

theorem ta_reductionAfter : Formalism.FourierDecayAlt.TC.ReductionAfter := Formalism.FourierDecayAlt.P.reduction_after

end Formalism.MainNotions.BridgeLemma₅

end

end PartTa3

section PartTa3b

open NumberField Finset Filter Topology

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₅

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.LocalFrameAxioms Formalism.MainNotions.InterlacingSignCuts

theorem ta_q_ne {k n : ℕ} (hkn : k ≤ n) (u u' : Fin k → ℝ) (lam : Fin n → ℝ) (T T' : ℝ) (hT : 0 < T) (hT' : 0 < T')
    (I : Set ℝ) (hcut : IsCutS u u' I) (h1 : InterlaceS hkn u lam) (h2 : InterlaceS hkn u' lam) (Y : ℝ) (hY : Y ∈ I) :
    qPoly T T' u u' (Y : ℂ) ≠ 0 := by
  cases k with
  | zero => obtain ⟨l, _⟩ := hcut; exact l.elim0
  | succ k0 =>
    have hI : ∀ w : Fin (k0 + 1) → ℝ, InterlaceS hkn w lam →
        TopsChoicePartA.Interlace w (fun j : Fin k0 => lam ⟨j.1, by omega⟩) := by
      intro w hw j
      have := hw.1 j.1 (by omega)
      exact ⟨this.1, this.2⟩
    have h := (stA_signs_of_core k0 u u' T T' I hT hT' hcut ⟨_, hI u h1, hI u' h2⟩).2 Y hY
    intro h0
    rw [h0] at h
    simp at h

theorem ta_supBe_pos (D : D7) (ka T T' : ℝ) (x : LocalDataRealPlace D) (hka : 0 < ka) (a' b' : ℝ) (hab : a' < b')
    (hq : ∀ Y ∈ Set.Icc a' b', qPoly T T' x.u x.u' (Y : ℂ) ≠ 0) : 0 < supBe D ka T T' x (Set.Icc a' b') := by
  unfold supBe
  have hcont : ContinuousOn (beS ka D.R.rS x.lam T T' x.u x.u') (Set.Icc a' b') := by
    unfold beS
    refine ContinuousOn.mul continuousOn_const
      (Real.continuous_sqrt.comp_continuousOn (ContinuousOn.norm (ContinuousOn.div ?_ ?_ hq)))
    · unfold capP; fun_prop
    · unfold qPoly; fun_prop
  have hbdd : BddAbove (beS ka D.R.rS x.lam T T' x.u x.u' '' Set.Icc a' b') :=
    (isCompact_Icc.image_of_continuousOn hcont).bddAbove
  have hZ : ((Set.range fun s => -x.lam s) ∪ (Set.range fun s => -x.lam s - 1)).Finite :=
    (Set.finite_range _).union (Set.finite_range _)
  obtain ⟨Y, hY, hYZ⟩ := ((Set.Icc_infinite hab).sdiff hZ).nonempty
  have hP : ∀ y : ℝ, (∀ s, y ≠ -x.lam s) → capP (fun s => (x.lam s : ℂ)) (y : ℂ) ≠ 0 := by
    intro y hy
    unfold capP
    refine Finset.prod_ne_zero_iff.2 fun s _ h0 => hy s ?_
    have h3 : ((y + x.lam s : ℝ) : ℂ) = 0 := by push_cast; exact h0
    have h4 := Complex.ofReal_eq_zero.1 h3
    linarith
  have h1 := hP Y (fun s h => hYZ (Or.inl ⟨s, h.symm⟩))
  have h2 : capP (fun s => (x.lam s : ℂ)) ((Y : ℂ) + 1) ≠ 0 := by
    have := hP (Y + 1) (fun s h => hYZ (Or.inr ⟨s, by show -x.lam s - 1 = Y; linarith⟩))
    simpa using this
  have hpos : 0 < beS ka D.R.rS x.lam T T' x.u x.u' Y := by
    unfold beS
    exact mul_pos (zpow_pos hka _) (Real.sqrt_pos.2 (norm_pos_iff.2 (div_ne_zero (mul_ne_zero h1 h2) (hq Y hY))))
  exact lt_of_lt_of_le hpos (le_csSup hbdd ⟨Y, hY, rfl⟩)

end Formalism.MainNotions.BridgeLemma₅

end

end PartTa3b

section PartTa4

open NumberField Finset Filter Topology
open scoped nonZeroDivisors ComplexConjugate ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₅

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.LocalFrameAxioms Formalism.FourierDecayAlt.TA Formalism.MainNotions.InterlacingSignCuts

attribute [local instance] Classical.propDecidable

def ThmAHyp (D : D7) (C : ℝ) (Kst : ℕ) (δ : D.host.E) (T T' : ℝ) (x : D.what₂.Tau → LocalDataRealPlace D) (L : LatticeDataWithDual D) (Kd : KernelData D)
    (B : D.what₂.Tau → LocBessel D.R.k D.R.rS)
    (f : ∀ v, Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ → ((B v).Wq →L[ℂ] (B v).Wp))
    (μsec : D.what₂.Tau → ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ) : Prop :=
  4 ≤ Kst ∧ 1 ≤ D.host.v ∧ PsiAx D δ ∧ LatAx D δ L ∧ FrameAx D δ L B ∧ ArithAxF D L Kd ∧
    (∀ v, LocMatch D T T' (x v) (B v) ∧ IsKFinCoefH (B v).σ (f v) ∧
      IsSection D.R.k D.R.rS (B v).z (B v).z' (μsec v)) ∧
    (∀ v, InterlaceS (k_le_nS D) (x v).u (x v).lam ∧ InterlaceS (k_le_nS D) (x v).u' (x v).lam) ∧
    (∀ v, (x v).u ≠ (x v).u') ∧
    (∀ v, GapAtLeast (epsSH D.R) (x v).lam
      (C * (D.R.m : ℝ) ^ ((9 : ℝ) / 2) * (Nlet D Kst * (D.R.r : ℝ) ^ 2 + (D.R.r : ℝ) ^ 3))) ∧
    (∀ v, IsCutS (x v).u (x v).u' (Set.Icc (x v).a (x v).b)) ∧
    (∀ v, (x v).a ≤ (x v).a1 ∧ (x v).a1 ≤ (x v).b1 ∧ (x v).b1 ≤ (x v).b ∧
      Nlet D Kst ^ 3 / 2 ≤ (x v).b1 - (x v).a1) ∧
    (∀ v, C * ((D.R.k : ℝ) * Nlet D Kst * ((D.R.rS : ℝ) + 1) ^ 2 +
        Nlet D Kst ^ 2 * ((D.R.rS : ℝ) + 1) ^ 2 + Nlet D Kst ^ 3) ≤ (x v).b - (x v).a)

theorem szPos_of_ThmAHyp {D : D7} {C : ℝ} {Kst : ℕ} {δ : D.host.E} {T T' : ℝ} {x : D.what₂.Tau → LocalDataRealPlace D} {L : LatticeDataWithDual D}
    {Kd : KernelData D} {B : D.what₂.Tau → LocBessel D.R.k D.R.rS}
    {f : ∀ v, Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ → ((B v).Wq →L[ℂ] (B v).Wp)}
    {μsec : D.what₂.Tau → ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ} (hC : 0 < C)
    (h : ThmAHyp D C Kst δ T T' x L Kd B f μsec) : SzPos C C (Nlet D Kst) T T' δ x := by
  obtain ⟨h1, _, h3, _, _, _, h7, h8, _, _, h11, h12, h13⟩ := h
  have hK0 : (0 : ℝ) < (Kst : ℝ) := by exact_mod_cast (by omega : 0 < Kst)
  have hN : 0 < Nlet D Kst := by unfold Nlet; positivity
  have hT : ∀ v : D.what₂.Tau, 0 < T := fun v => (h7 v).1.2.2.2.1 ▸ (B v).hz.2
  have hT' : ∀ v : D.what₂.Tau, 0 < T' := fun v => (h7 v).1.2.2.2.2.1 ▸ (B v).hz'.2
  have hka : ∀ v, 0 < kaV D δ v := fun v =>
    div_pos (by positivity) (norm_pos_iff.2 ((map_ne_zero (plEmb D v)).2 h3.1))
  have hba : ∀ v, 0 < (x v).b - (x v).a := fun v => lt_of_lt_of_le (by positivity) (h13 v)
  have hq : ∀ v, ∀ Y ∈ Set.Icc (x v).a (x v).b, qPoly T T' (x v).u (x v).u' (Y : ℂ) ≠ 0 := fun v Y hY =>
    ta_q_ne (k_le_nS D) (x v).u (x v).u' (x v).lam T T' (hT v) (hT' v) _ (h11 v) (h8 v).1 (h8 v).2 Y hY
  have hs : ∀ v, 0 < supBe D (kaV D δ v) T T' (x v) (Set.Icc (x v).a (x v).b) := fun v =>
    ta_supBe_pos D _ T T' (x v) (hka v) _ _ (by linarith [hba v]) (hq v)
  have hs1 : ∀ v, 0 < supBe D (kaV D δ v) T T' (x v) (Set.Icc (x v).a1 (x v).b1) := fun v => by
    obtain ⟨e1, _, e3, e4⟩ := h12 v
    have e5 : 0 < Nlet D Kst ^ 3 / 2 := by positivity
    refine ta_supBe_pos D _ T T' (x v) (hka v) _ _ (by linarith) fun Y hY => hq v Y ⟨le_trans e1 hY.1, le_trans hY.2 e3⟩
  refine ⟨fun i v => ?_, fun b s v => ?_, fun b v => ?_⟩
  · unfold szX xSz
    refine mul_pos (mul_pos hC ?_) (pow_pos (div_pos (mul_pos (mul_pos hC (hka v)) hN) (hba v)) _)
    split_ifs
    · exact hs1 v
    · exact hs v
  · unfold szL LamSz
    exact mul_pos (mul_pos hC (hs v)) (pow_pos (div_pos (mul_pos (mul_pos hC (hka v)) hN) (hba v)) _)
  · unfold szP LamPSz
    exact Real.sqrt_pos.2 (mul_pos (mul_pos (mul_pos (mul_pos hC (hs v)) (pow_pos (hka v) _))
      (Real.rpow_pos_of_pos (mul_pos (hT v) (hT' v)) _)) (pow_pos (div_pos (mul_pos hC hN) (hba v)) _))

def ThmAOpen (D : D7) (C C' C4 : ℝ) (Kst : ℕ) (Vm : ValMap D.R.k D.R.rS) : Prop :=
  ∀ (δ : D.host.E) (T T' : ℝ) (x : D.what₂.Tau → LocalDataRealPlace D) (L : LatticeDataWithDual D) (Kd : KernelData D)
    (B : D.what₂.Tau → LocBessel D.R.k D.R.rS)
    (f : ∀ v, Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ → ((B v).Wq →L[ℂ] (B v).Wp))
    (μsec : D.what₂.Tau → ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ),
    ThmAHyp D C Kst δ T T' x L Kd B f μsec → C' ≤ ThS D C C (Nlet D Kst) T T' δ x L →
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H)
      (Wv : Point D.host.E (D.R.rS + 1) → H),
      (∀ p q, ⟪Wv p, Wv q⟫_ℂ = ((Real.sqrt (ptWeightG D L.ρ T T' q.1) : ℝ) : ℂ) * ((Real.sqrt (ptWeightG D L.ρ T T' p.1) : ℝ) : ℂ) *
        ∏ v, hsInner (Vm.V (B v) (f v) (locBlocks D L.ρ v q.1)) (Vm.V (B v) (f v) (locBlocks D L.ρ v p.1))) ∧
      ∃ (Wd : Type) (_ : Fintype Wd) (len : Wd → ℕ) (Pat1 : Type) (pat1 : ℕ → D.host.E → Pat1)
        (pat3 : ℕ → ℕ → D.host.E → D.host.E → (D.what₂.Tau → Option Bool)) (Φ : ℝ → Wd → Pt D.host.E → H)
        (tr : ℝ → ℕ → Wd → Finset (Pt D.host.E) → (Pt D.host.E → Pt D.host.E → ℂ) → D.host.E → ℂ) (w0 : Wd) (jn : ℝ),
        (∀ eps : ℝ, 0 < eps → ∀ i ∈ Icc 1 (D.R.rS + 1),
          LevelEst len Kst (taData D L Kd (taLv D δ L)) (Φ eps) (tr eps i) (pat1 i) (pat3 i)
            (prof1 D C C (Nlet D Kst) T T' δ x Kst i) (prof3 D C C (Nlet D Kst) T T' δ x Kst i)
            (bdB D C C (Nlet D Kst) T T' δ x L C4 i) i) ∧
        (∀ w, len w ≤ 4 * Kst * (D.R.rS + 1) → Tendsto (fun eps => ‖Φ eps w []‖ ^ 2) (𝓝[>] 0) (𝓝 jn)) ∧
        len w0 = 0 ∧
        (∀ p, IsPt (D.R.rS + 1) p → ∀ᶠ eps in 𝓝[>] (0 : ℝ), Φ eps w0 p = Wv (ph (D.R.rS + 1) p)) ∧
        ENNReal.ofReal jn ≤ jNorm2One (fun v => (B v).Wq →L[ℂ] (B v).Wp) (fun _ => hsNormSq) D.R.k D.R.rS T T' L.κ
          (fun v p => (B v).J (f v) (bigCell D.R.k D.R.rS p.1 (μsec v p.2)))

end Formalism.MainNotions.BridgeLemma₅

end

end PartTa4

section PartTa5

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₅

open Formalism.BasicNotions Formalism.MainNotions.S

end Formalism.MainNotions.BridgeLemma₅

end

end PartTa5

section PartTa6

open NumberField Finset Filter Topology
open scoped nonZeroDivisors ComplexConjugate ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₅

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalFrameAxioms Formalism.MainNotions.InterlacingSignCuts

attribute [local instance] Classical.propDecidable

section Ultra

variable (D : D7)

variable {D}

end Ultra

end Formalism.MainNotions.BridgeLemma₅

end

end PartTa6

end PartTaAll

section PartA0

namespace Formalism.MainNotions.BridgeLemma₅

open Formalism.MainNotions Formalism.MainNotions.S

theorem PX_germ_of_core : ∃ C : ℝ, ∀ C₁ ≥ C, ∀ C₂ ≥ C, PX.germ C₁ C₂ :=
  InterlacingSignCuts.Gm.stGerm_of_core' Formalism.FourierDecayAlt.P.germExpansion_true

noncomputable def CGerm : ℝ := PX_germ_of_core.choose

structure OpenGroupStatements (CB Co Cd Cs : ℝ) : Prop where
  lemmaB : PX.lemmaB CB
  dualList : stDualListOn (fun Ls => Ls.length ≠ 1) CB Co Cd
  slices : slicesOpen Cs
  slicesOrb : slicesOrbOpen Cs
  smooth : PX.smooth CB
  lettersExist : PX.lettersExist

structure KnownLiterature : Prop where
  capEig : UnitaryLevelOperators.stCapEig
  markovMid : InterlacingSignCuts.VMarkovMid
  besselModel_unique : UnitaryLevelOperators.stJSZ
  qBranch : UnitaryLevelOperators.stQ_branch
  qWigner : UnitaryLevelOperators.stQ_wigner
  tensorDS : ∀ D, OnePlaceEstimates.adm18 D
  tensorDSd : ∀ D, OnePlaceEstimates.DualTranslationPrinciple D
  kTypes : ∀ D, OnePlaceEstimates.adm20 D

end Formalism.MainNotions.BridgeLemma₅

end PartA0
