import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceConjugationPropertiesCmFieldStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwahoriAndMaximalCompactCriteria
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryIwahoriFacts
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.IwLevels

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem KGL_eq_KO (w : Pl E) (n : ℕ) :
    GlobalTheory.LFun.KGL w n = GlobalTheory.SplitWeil.KO (w.adicCompletion E) (Fin n) := by
  ext g
  rw [GlobalTheory.CompanionTheory.IwEntries.mem_KGL_iff, GlobalTheory.CompanionTheory.IwEntries.mem_KO_iff]

theorem isCompact_KGL (w : Pl E) (n : ℕ) : IsCompact (GlobalTheory.LFun.KGL w n : Set (GLw n w)) := by
  rw [KGL_eq_KO]
  exact GlobalTheory.SplitFlip.isCompact_KO

theorem iwGL_le_KGL (w : Pl E) (n : ℕ) : iwGL n w ≤ GlobalTheory.LFun.KGL w n := by
  rw [KGL_eq_KO]
  exact GlobalTheory.SmGL.iwahori_le_KO _ _

theorem isClosed_UL {w : Pl E} (hw : ¬ IsSplitAt w) (n : ℕ) (hc : Continuous (cj w)) :
    IsClosed (UL n w : Set (GLw n w)) := by
  rw [GlobalTheory.CompanionTheory.UnitaryWitt.UL_eq_of_not_split hw]
  exact GlobalTheory.CompanionTheory.UnitaryWitt.isClosed_UJ_one n hc

theorem isOpen_KL (n : ℕ) (w : Pl E) : IsOpen (KL n w : Set (UL n w)) := by
  have h : IsOpen (GlobalTheory.LFun.KGL w n : Set (GLw n w)) := by
    rw [KGL_eq_KO]
    exact GlobalTheory.SplitFlip.isOpen_KO
  exact h.preimage (continuous_subtype_val (p := (· ∈ UL n w)))

theorem isCompact_KL {w : Pl E} (hw : ¬ IsSplitAt w) (n : ℕ) (hc : Continuous (cj w)) :
    IsCompact (KL n w : Set (UL n w)) :=
  (isClosed_UL hw n hc).isClosedEmbedding_subtypeVal.isCompact_preimage (isCompact_KGL w n)

theorem isOpen_iwU (n : ℕ) (w : Pl E) (b : GLw n w) : IsOpen (iwU n w b : Set (UL n w)) := by
  have ho : IsOpen (iwGL n w : Set (GLw n w)) :=
    GlobalTheory.SmGL.IwahoriOnto.isOpen_iwahori (w.adicCompletion E) (Fin n)
  have hcont : Continuous fun γ : UL n w => b⁻¹ * γ.1 * b :=
    (continuous_const.mul continuous_subtype_val).mul continuous_const
  have e : (iwU n w b : Set (UL n w)) = (fun γ : UL n w => b⁻¹ * γ.1 * b) ⁻¹' (iwGL n w : Set (GLw n w)) := by
    ext γ
    exact GlobalTheory.CompanionTheory.UnitaryWitt.mem_iwU_iff n w b γ
  rw [e]
  exact ho.preimage hcont

theorem iwU_le_KL (n : ℕ) (w : Pl E) (b : GLw n w) (hb : b ∈ GlobalTheory.LFun.KGL w n) :
    iwU n w b ≤ KL n w := by
  intro γ hγ
  have h1 := iwGL_le_KGL w n ((GlobalTheory.CompanionTheory.UnitaryWitt.mem_iwU_iff n w b γ).1 hγ)
  have h2 : γ.1 = b * (b⁻¹ * γ.1 * b) * b⁻¹ := by group
  rw [KL, Subgroup.mem_subgroupOf, h2]
  exact mul_mem (mul_mem hb h1) (inv_mem hb)

theorem relIndex_ne_zero {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {H K : Subgroup G}
    (hH : IsOpen (H : Set G)) (hK : IsCompact (K : Set G)) : H.relIndex K ≠ 0 := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  let U : OpenSubgroup K := ⟨H.subgroupOf K, hH.preimage continuous_subtype_val⟩
  haveI : Finite (K ⧸ (U : Subgroup K)) := Subgroup.quotient_finite_of_isOpen _ U.isOpen
  exact Subgroup.index_ne_zero_of_finite

theorem isCompact_support_fU {w : Pl E} (hw : ¬ IsSplitAt w) (n : ℕ) (b : GLw n w)
    (ϖ : (w.adicCompletion E)ˣ) (l : Fin (n / 2) → ℤ) (hc : Continuous (cj w)) :
    IsCompact {g : UL n w | fU n w b ϖ l g ≠ 0} := by
  set t : GLw n w := b * tdiag ϖ (wexp n l) * b⁻¹ with ht
  have hI : IsCompact (iwU n w b : Set (UL n w)) :=
    GlobalTheory.CompanionTheory.UnitaryWitt.isCompact_iwU hw n b hc
  have hS : IsCompact ((fun p : UL n w × UL n w => p.1.1 * t * p.2.1) ''
      ((iwU n w b : Set (UL n w)) ×ˢ (iwU n w b : Set (UL n w)))) :=
    (hI.prod hI).image (((continuous_subtype_val.comp continuous_fst).mul continuous_const).mul
      (continuous_subtype_val.comp continuous_snd))
  have e : {g : UL n w | fU n w b ϖ l g ≠ 0} = Subtype.val ⁻¹'
      ((fun p : UL n w × UL n w => p.1.1 * t * p.2.1) ''
        ((iwU n w b : Set (UL n w)) ×ˢ (iwU n w b : Set (UL n w)))) := by
    ext γ
    simp only [Set.mem_setOf_eq, fU, Set.mem_preimage, Set.mem_image, Set.mem_prod, SetLike.mem_coe]
    constructor
    · intro h
      by_contra hn
      refine h (if_neg ?_)
      rintro ⟨x, hx, z, hz, e⟩
      exact hn ⟨(x, z), ⟨hx, hz⟩, e.symm⟩
    · rintro ⟨⟨x, z⟩, ⟨hx, hz⟩, e⟩
      rw [if_pos ⟨x, hx, z, hz, e.symm⟩]
      exact one_ne_zero
  rw [e]
  exact (isClosed_UL hw n hc).isClosedEmbedding_subtypeVal.isCompact_preimage hS

theorem levels_unitary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (n : ℕ) (b : GLw n w), IsWitt n w b → ∀ (ϖ : (w.adicCompletion E)ˣ) (l : Fin (n / 2) → ℤ), IsUnifAt ϖ → Cone l → IsOpen (KL n w : Set (UL n w)) ∧ IsCompact (KL n w : Set (UL n w)) ∧ IsLevel (MonoidHom.id _) (KL n w) (iwU n w b) ∧ (iwU n w b).relIndex (KL n w) ≠ 0 ∧ IsCompact {g : UL n w | fU n w b ϖ l g ≠ 0} := by
  intro E _ _ _ hU w hw n b hb ϖ l _ _
  have hc : Continuous (cj w) := (GlobalTheory.T.placeConjugation_properties_cmField E hU w).1
  exact ⟨isOpen_KL n w, isCompact_KL hw n hc,
    ⟨isOpen_iwU n w b, iwU_le_KL n w b hb.1, fun k hk => hk⟩,
    relIndex_ne_zero (isOpen_iwU n w b) (isCompact_KL hw n hc),
    isCompact_support_fU hw n b ϖ l hc⟩

end GlobalTheory.CompanionTheory.IwLevels
