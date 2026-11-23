import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIntegerUnitSplitPlaceConjugatePrime

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.SplitPlaceConj

theorem isSplitPl_w : ∀ (D : D7) (s : SplitPlace D.host.E), IsSplitPl D.host s.w := by
  intro D s
  have hc : ∀ z : D.host.E, IsCMField.complexConj D.host.E z = D.host.conj z := by
    intro z
    apply D.host.φ₀.injective
    rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply]
  obtain ⟨e, he, he'⟩ := GlobalTheory.SplitSep.exists_sep D.host.E s
  let c : 𝓞 D.host.E →+* 𝓞 D.host.E :=
    RingOfIntegers.mapRingHom (IsCMField.complexConj D.host.E : D.host.E →+* D.host.E)
  have hce : ((c e : 𝓞 D.host.E) : D.host.E) = IsCMField.complexConj D.host.E (e : D.host.E) := rfl
  refine ⟨c e, (s.split_mem_ideal _).2 (by rw [hce]; exact he'), fun y hy hm => ?_⟩
  have hye : (y : D.host.E) = (e : D.host.E) := by
    rw [hy, hce, ← hc, IsCMField.complexConj_apply_apply]
  have h1 := (s.split_mem_ideal y).1 hm
  rw [hye, he] at h1
  exact lt_irrefl _ h1

end GlobalTheory.SplitPlaceConj
