import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.TwistedConjugationNorms.LocalMatchingOfAssemblyHypotheses
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryLevelSubgroupProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBallSubset
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG GlobalTheory.CuspRep
open PositivityTheory.Rg.Bc.ArchbcB.B.M4 PositivityTheory.Rg.Bc.ArchbcB.B.M4.Tw
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.IwFacts

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem v_thetaGL_apply (w : Pl E) (a : ℕ) (g : GLw a w) (i j : Fin a) :
    Valued.v ((thetaGL a (cj w) g).val i j) = Valued.v ((g⁻¹).val j.rev i.rev) := by
  rw [GlobalTheory.ThetaPull.thetaGL_apply, map_mul, GlobalTheory.PrincCong.v_cj, map_pow, Valuation.map_neg, map_one, one_pow, one_mul]

theorem thetaGL_mem_KGL (w : Pl E) (a : ℕ) {k : GLw a w} (hk : k ∈ GlobalTheory.LFun.KGL w a) :
    thetaGL a (cj w) k ∈ GlobalTheory.LFun.KGL w a := by
  obtain ⟨h1, h2⟩ := (GlobalTheory.CompanionTheory.IwEntries.mem_KGL_iff w a k).1 hk
  refine (GlobalTheory.CompanionTheory.IwEntries.mem_KGL_iff w a _).2 ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [v_thetaGL_apply]
    exact h2 _ _
  · rw [← map_inv, v_thetaGL_apply, inv_inv]
    exact h1 _ _

theorem thetaGL_mem_iwGL (w : Pl E) (a : ℕ) {k : GLw a w} (hk : k ∈ iwGL a w) :
    thetaGL a (cj w) k ∈ iwGL a w := by
  obtain ⟨h1, h2, -⟩ := ((GlobalTheory.CompanionTheory.IwEntries.iwGL_KGL_entries E w a k).1).1 hk
  obtain ⟨-, -, h3⟩ := ((GlobalTheory.CompanionTheory.IwEntries.iwGL_KGL_entries E w a k⁻¹).1).1 (inv_mem hk)
  refine ((GlobalTheory.CompanionTheory.IwEntries.iwGL_KGL_entries E w a _).1).2 ⟨fun i j => ?_, fun i j => ?_, fun i j hij => ?_⟩
  · rw [v_thetaGL_apply]
    exact h2 _ _
  · rw [← map_inv, v_thetaGL_apply, inv_inv]
    exact h1 _ _
  · rw [v_thetaGL_apply]
    exact h3 _ _ (Fin.rev_lt_rev.2 hij)

theorem isCompact_support_dcos (w : Pl E) (a : ℕ) (t : GLw a w) :
    IsCompact {g : GLw a w | dcos a w t g ≠ 0} := by
  have hI : IsCompact (iwGL a w : Set (GLw a w)) :=
    GlobalTheory.SmGL.IwahoriOnto.isCompact_iwahori (w.adicCompletion E) (Fin a)
  have hS : IsCompact ((fun p : GLw a w × GLw a w => p.1 * t * p.2) ''
      ((iwGL a w : Set (GLw a w)) ×ˢ (iwGL a w : Set (GLw a w)))) :=
    (hI.prod hI).image ((continuous_fst.mul continuous_const).mul continuous_snd)
  convert hS using 1
  ext g
  simp only [Set.mem_setOf_eq, dcos, Set.mem_image, Set.mem_prod, SetLike.mem_coe, Prod.exists]
  constructor
  · intro h
    by_contra hn
    refine h (if_neg ?_)
    rintro ⟨x, hx, y, hy, rfl⟩
    exact hn ⟨x, y, ⟨hx, hy⟩, rfl⟩
  · rintro ⟨x, y, ⟨hx, hy⟩, rfl⟩
    rw [if_pos ⟨x, hx, y, hy, rfl⟩]
    exact one_ne_zero

theorem iw_facts : P_iw_facts := by
  intro E _ _ _ w hw a t
  have hth : thL a w = thetaGL a (cj w) := by
    unfold thL
    rw [if_neg hw]
  have hKo : IsOpen (GlobalTheory.LFun.KGL w a : Set (GLw a w)) := by
    rw [GlobalTheory.CompanionTheory.IwLevels.KGL_eq_KO]
    exact GlobalTheory.SplitFlip.isOpen_KO
  have hKc := GlobalTheory.CompanionTheory.IwLevels.isCompact_KGL w a
  have hIo : IsOpen (iwGL a w : Set (GLw a w)) :=
    GlobalTheory.SmGL.IwahoriOnto.isOpen_iwahori (w.adicCompletion E) (Fin a)
  have hIK := GlobalTheory.CompanionTheory.IwLevels.iwGL_le_KGL w a
  refine ⟨hKo, hKc, fun k hk => ?_, ⟨hIo, hIK, fun k hk => ?_⟩, ⟨hIo, hIK, fun k hk => hk⟩,
    GlobalTheory.CompanionTheory.IwLevels.relIndex_ne_zero hIo hKc, isCompact_support_dcos w a t⟩
  · rw [hth]
    exact thetaGL_mem_KGL w a hk
  · rw [hth]
    exact thetaGL_mem_iwGL w a hk

end GlobalTheory.CompanionTheory.IwFacts
