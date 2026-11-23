import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcXOmVTop
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.MultiplicityGExists

noncomputable section

namespace Formalism.L2.SG.Pf.NcX.OmVSt

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct

theorem unramAt_of_cm {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : Formalism.BasicNotions.CMData F E) (v : HeightOneSpectrum (𝓞 F)) : UnramAt (E := E) v := by
  intro P hP hP0 _
  classical
  haveI : Algebra.IsQuadraticExtension F E := ⟨hc.deg2⟩
  let c : Gal(E/F) := AlgEquiv.ofRingEquiv (f := starRingAut) (fun r => (hc.fixed (algebraMap F E r)).2 ⟨r, rfl⟩)
  haveI : P.LiesOver (P.under (𝓞 F)) := ⟨rfl⟩
  have hp0 : P.under (𝓞 F) ≠ ⊥ := Ideal.IsIntegral.comap_ne_bot (𝓞 F) hP0
  have hcard : Nat.card (P.inertia Gal(E/F)) = P.ramificationIdx (𝓞 F) := by
    rw [Ideal.card_inertia_eq_ramificationIdxIn (G := Gal(E/F)) (P.under (𝓞 F)) P,
      Ideal.ramificationIdxIn_eq_ramificationIdx (P.under (𝓞 F)) P Gal(E/F)]
  by_contra hne
  have hG : Nat.card Gal(E/F) = 2 := by
    first
      | (rw [IsGalois.card_aut_eq_finrank]; exact hc.deg2)
      | (rw [Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank]; exact hc.deg2)
  haveI : Fact (Nat.card Gal(E/F)).Prime := ⟨by rw [hG]; exact Nat.prime_two⟩
  have htop : P.inertia Gal(E/F) = ⊤ := by
    rcases Subgroup.eq_bot_or_eq_top_of_prime_card (P.inertia Gal(E/F)) with h | h
    · exfalso
      apply hne
      rw [← hcard, h]
      simp
    · exact h
  have hcI : c ∈ P.inertia Gal(E/F) := htop ▸ Subgroup.mem_top c
  obtain ⟨θ, t, ht, hθ⟩ := hc.cmUnram.2.2 P (hP.isMaximal hP0)
  apply hθ
  have h1 := hcI θ
  have e : c • θ = t := by
    apply RingOfIntegers.coe_injective
    rw [ht]
    rfl
  rw [e] at h1
  have : θ - t = -(t - θ) := by ring
  rw [this]
  exact P.neg_mem h1

variable {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ)

theorem omega_standard_holds : OmVStd X ψ := by
  intro h1 h2
  refine ⟨?_, ?_, h1, h2⟩
  · unfold IsCMExt
    refine ⟨X.B.I.cm.totReal, X.B.I.cm.cmUnram.1, X.B.I.cm.deg2, ?_⟩
    exact fun τ x => X.B.I.cm.cmUnram.2.1 τ x
  · unfold IsHermND
    have hH := X.B.I.J_herm
    unfold Formalism.UG.IsHerm at hH
    refine ⟨fun i j => ?_, X.B.I.J_det⟩
    have h3 := congrFun (congrFun hH i) j
    exact h3

theorem omega_lattice_holds : OmVLat X := ⟨X.B.I.L, ⟨X.B.I.L_fg, X.B.I.L_span⟩, rfl⟩

theorem omega_unramified_holds : OmVUnram X := fun v => unramAt_of_cm X.B.I.cm v

end Formalism.L2.SG.Pf.NcX.OmVSt
