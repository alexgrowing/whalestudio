import Development.AbelianVarietyTheory.Definitions.Divisors.ScalesBy
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.EisensteinResidue
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.EisensteinMaximalParabolic
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StabilizerInductionLaw
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AnisotropicCoreWittFrame
import Development.AbelianVarietyTheory.Counterexamples.AnisotropicRankZero.WittSphericalSectionLeftInvariantRationalParabol
open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch GlobalTheory.ResidueEisenstein
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ResidueDictionary

theorem dict : ∀ (D : D7) (V V₀ : HSp D) (r : ℕ) (d : HypDec V V₀ (r + 1)), IsAniso V₀ → ∀ l : Lvl V, l.Good → HasIw d l.K → DataJ D.sp.cm.sig V.gram d.e d.e' l.L l.c (fun g => (iwAbs (absDet d) l.K g : ℝ)) ∧ (∃ T, IsRepsJ D.sp.cm.sig V.gram d.e T) ∧ ∀ T, IsRepsJ D.sp.cm.sig V.gram d.e T → ∀ (g : GA D V) (s : ℂ), sphericalEisensteinSeriesOnGroup d l.K g s = ∑' t : T, (((iwAbs (absDet d) l.K (t.1.1 * g) : ℝ≥0) : ℝ) : ℂ) ^ (s + ((V.rank : ℂ) - (r + 1)) / 2) := by
  intro D V V₀ r d hA l hl hIw
  have hsc : ∀ q : stab d, ScalesBy D.sp.cm.sig V.gram d.e (q : GA D V) (onX d q) := fun q => mul_jX d q
  have hstab := (GlobalTheory.EisCont.parFlag_stab_leftInv D V V₀ (r + 1) d).2.2.1
  have hiff : ∀ x : GA D V, (∃ β, ScalesBy D.sp.cm.sig V.gram d.e x β) ↔ x ∈ stab d := fun x =>
    ⟨fun ⟨β, e⟩ => (hstab x β e).1, fun hx => ⟨_, hsc ⟨x, hx⟩⟩⟩
  have htriv := GlobalTheory.Doubling.triv_of_isCompact (isClosed_stab d) (continuous_absDet d) hl.isCompact_K

  have hmk : ∀ t γ : GQ V, GlobalTheory.AutomorphicL2Unitary.mk ((stab d).subgroupOf (GQ V)) t = GlobalTheory.AutomorphicL2Unitary.mk ((stab d).subgroupOf (GQ V)) γ ↔
      ((γ * t⁻¹ : GQ V) : GA D V) ∈ stab d := fun t γ => by
    rw [GlobalTheory.AutomorphicL2Unitary.mk_eq_iff]
    constructor
    · rintro ⟨δ, hδ⟩
      have : (γ * t⁻¹ : GQ V) = δ := by rw [← hδ]; group
      rw [this]; exact δ.2
    · intro h
      exact ⟨⟨γ * t⁻¹, h⟩, by simp⟩
  refine ⟨⟨isCMExt_host D, GlobalTheory.Doubling.isHermND_gram V, GlobalTheory.WittFrameOfDec.isWittFrame_of_hypDec D V V₀ _ d hA, hl.1,
    fun g => ?_, fun p β e k hk => ?_⟩, ?_, fun T hT g s => ?_⟩
  · obtain ⟨q, k, hk, rfl⟩ := hIw g
    exact ⟨q, onX d q, hsc q, k, hk, rfl⟩
  · obtain ⟨hp, rfl⟩ := hstab p β e
    have := iwAbs_mul_of_triv htriv ⟨p, hp⟩ hk
    rw [this]
    rfl
  · refine ⟨Set.range fun q : GlobalTheory.AutomorphicL2Unitary.Quot ((stab d).subgroupOf (GQ V)) => (q.out : GQ V), fun γ => ?_⟩
    refine ⟨(GlobalTheory.AutomorphicL2Unitary.mk ((stab d).subgroupOf (GQ V)) γ).out, ⟨⟨_, rfl⟩, (hiff _).2 ((hmk _ _).1 (Quotient.out_eq _))⟩, ?_⟩
    rintro t' ⟨⟨q, rfl⟩, ht'⟩
    have e := (hmk q.out γ).2 ((hiff _).1 ht')
    have e2 : q = GlobalTheory.AutomorphicL2Unitary.mk ((stab d).subgroupOf (GQ V)) γ := (Quotient.out_eq q).symm.trans e
    subst e2
    rfl
  · have hbij : Function.Bijective fun t : T => GlobalTheory.AutomorphicL2Unitary.mk ((stab d).subgroupOf (GQ V)) (t.1 : GQ V) := by
      constructor
      · rintro ⟨t, ht⟩ ⟨t', ht'⟩ e
        have e' := (hmk _ _).1 e
        obtain ⟨u, -, hu⟩ := hT t'
        have h1 := hu t' ⟨ht', (hiff _).2 (by simp)⟩
        have h2 := hu t ⟨ht, (hiff _).2 e'⟩
        exact Subtype.ext (h2.trans h1.symm)
      · intro q
        induction q using Quotient.inductionOn with
        | h γ =>
          obtain ⟨t, ⟨ht, hs⟩, -⟩ := hT γ
          exact ⟨⟨t, ht⟩, (hmk _ _).2 ((hiff _).1 hs)⟩
    change cosetSum (stab d) (GQ V) (sphericalSectionIwasawa d l.K s) g = _
    rw [GlobalTheory.Eis.cosetSum_eq_tsum (GlobalTheory.AnisotropicResidueNonvanishing.witt_spherical_section_left_invariant_rational_parabolic d l hl hIw s) hbij g]
    refine tsum_congr fun t => ?_
    simp only [sphericalSectionIwasawa, npow, rhoH]
    congr 1
    push_cast
    ring

end GlobalTheory.ResidueDictionary
