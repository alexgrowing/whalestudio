import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteTwistFrameExtraExcludedOverSmallPrimes
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertialOrderFifteenCharAuxiliaryPrimeSpec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousInfIdele
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HostCmEmbeddingProperties
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.GalChar Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR GlobalTheory.HeckeGal

noncomputable section

namespace GlobalTheory.EtaUnitArg

theorem denseRange_atInf_single {L : Type} [Field L] [NumberField L] (w : InfinitePlace L) :
    DenseRange (atInf w : Lˣ → (w.Completion)ˣ) := by
  classical
  have hs : Function.Surjective (fun u : ∀ v : InfinitePlace L, (v.Completion)ˣ => u w) := fun z =>
    ⟨Function.update (1 : ∀ v : InfinitePlace L, (v.Completion)ˣ) w z, by simp⟩
  exact hs.denseRange.comp (GlobalTheory.InfTypeLocal.denseRange_atInf L) (continuous_apply w)

open Classical in
theorem locInf_eq {L : Type} [Field L] [NumberField L] (w : InfinitePlace L) (z : (w.Completion)ˣ) :
    Units.map (Formalism.L2.NC.locInf w) z = infIdele L w z := by
  apply Units.ext
  rfl

theorem etaT_isUnitArg : ∀ {R : Ranks} (H : Host R) (χ : HChar H.E), IsEtaT H χ → ∀ (h : Formalism.L2.NC.HC H.E), h.χ = (χ : Ideles H.E →* ℂˣ) → ∀ (g : R.Psi), h.IsUnitArg (H.emb (g : R.GG)) := by
  intro R H χ hχ h hh g f hf hfE z
  obtain ⟨c, -, hcm, -⟩ := GlobalTheory.Mem.HostCM.host_cm R H
  have hloc := (GlobalTheory.InfTypeLocal.infType_iff_local H.E (R.Psi) (embPsi H) hcm.bij χ.1 χ.2.1
    (fun _ => 1)).1 (fun k => hχ.inf k) g
  have key : (fun z : ((InfinitePlace.mk (H.emb (g : R.GG))).Completion)ˣ =>
      ((χ.1 (infIdele H.E _ z) : ℂˣ) : ℂ)) =
      fun z : ((InfinitePlace.mk (H.emb (g : R.GG))).Completion)ˣ =>
        f (z : (InfinitePlace.mk (H.emb (g : R.GG))).Completion) /
          ((‖f (z : (InfinitePlace.mk (H.emb (g : R.GG))).Completion)‖ : ℝ) : ℂ) := by
    refine (denseRange_atInf_single _).equalizer ?_ ?_ ?_
    · exact Units.continuous_val.comp (χ.2.1.comp (GlobalTheory.InfTypeLocal.continuous_infIdele _ _))
    · have h1 := hf.comp Units.continuous_val
      have h2 : ∀ u : ((InfinitePlace.mk (H.emb (g : R.GG))).Completion)ˣ,
          f (u : (InfinitePlace.mk (H.emb (g : R.GG))).Completion) ≠ 0 := fun u =>
        (_root_.map_ne_zero _).2 u.ne_zero
      exact h1.div (Complex.continuous_ofReal.comp h1.norm) fun u => by exact_mod_cast norm_ne_zero_iff.2 (h2 u)
    · funext k
      have e : f ((atInf _ k : ((InfinitePlace.mk (H.emb (g : R.GG))).Completion)ˣ) :
          (InfinitePlace.mk (H.emb (g : R.GG))).Completion) = H.emb (g : R.GG) k := hfE k
      simp only [Function.comp_apply]
      rw [e]
      have := hloc k
      exact this.trans (zpow_one _)
  rw [locInf_eq, hh]
  exact congrFun key z

end GlobalTheory.EtaUnitArg
