import Mathlib
import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.IsQg
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalGaloisCompatibility.ToralDeRham.AwayEqOfPlainTor
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalGaloisCompatibility.ToralDeRham.ToralGalois2
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalGaloisCompatibility.ToralDeRham.RcUnlinkedChars
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PlainTorExistsChars
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalGaloisCompatibility.ToralDeRham.FrobeniusCharpolyOfUnlinkedUnramifiedSupport
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalGaloisCompatibility.ToralDeRham.ToralAboveOfHolds
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DeRhamDescends
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.JumpsDescend
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeaklyAttachedGaloisRepresentationBaseChangeRest
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalIndepBridge
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalGaloisCompatibility.Chl

open GlobalTheory.RoadU

namespace GalTw
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.DeRhamOfPlainTorus

theorem deRham_of_plainTor (hI : UpperTheory.Gal.ToralGalois.Inq) (hS : SphericalLevelCondition .all .dR) (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω]
    [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ) (hn : 1 ≤ n) (π : CuspSub E n)
    (χ : HChar (maximalRealSubfield E)) (hsc : InScope .all l π χ) (r : G E Ω →* GL (Fin n) (Qbar l)) (hw : Weak π ι r)
    (w : HeightOneSpectrum (𝓞 E)) (σ : SmIrr (GL (Fin n) (w.adicCompletion E))) (hσ : π.IsLocComp w σ)
    (hp : PlainTor (algNorm σ)) : ClauseAt .dR π ι r w := by
  intro P AI hT A hA O _ _ _ Bw hj
  have : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  obtain ⟨ξ, hξ, hs, hu⟩ := GlobalTheory.RoadU.plainTor_exists_chars (w.adicCompletion E) (algNorm σ) hp
  obtain ⟨a, ha⟩ := GlobalTheory.localArtinExists_holds E Ω A w hA
  obtain ⟨M, _, _, _, _, _, _, _, u, h', PM, χ', hsc', hlift, -, B, hB, -⟩ :=
    GlobalTheory.RoadU.exists_sph_lift_of_toral hI Ω E l ι n hn π χ hsc r hw w A hA σ hσ ξ hξ hs hu a ha (frob hA)
      (by rw [deg_frob]; exact one_ne_zero)
  have hwM : Weak PM ι (resTo M r) := GlobalTheory.GalCut.weak_comp_res E M Ω l ι n π PM hlift r hw
  have hcl : ClauseAt .dR PM ι (resTo M r) u := hS M Ω l ι n hn PM χ' hsc' (resTo M r) hwM u trivial B hB
  obtain ⟨O', _, _, _, Bw', hj', hjj, hdesc⟩ :=
    GlobalTheory.DRDescent.deRham_descends E M Ω A w u hA h' l P AI hT n r hw.1 O Bw hj
  obtain ⟨hdR, hjump⟩ := hcl P AI hT A h' O' Bw' hj'
  refine ⟨hdesc hdR, ?_⟩
  intro τ LL' τ' hind J hJ
  obtain ⟨φ, hφ⟩ := IntermediateField.exists_algHom_of_splits
    (fun s : Om l => ⟨Algebra.IsIntegral.isIntegral s, IsAlgClosed.splits _⟩)
    ((IntermediateField.val LL'.1).comp τ')
  have hφx : ∀ x : E, φ (Bw.j (algebraMap E Ω x)) = τ x := by
    intro x
    have := congrArg (fun f => f ⟨Bw.j (algebraMap E Ω x), Bw.j_E x⟩) hφ
    simp only [AlgHom.comp_apply, IntermediateField.val_mk] at this
    rw [this, hind x]
    rfl
  let LL'' : FinExt l := ⟨Bw'.Kw.1.map φ, inferInstance⟩
  let τ'' : ↥Bw'.Kw.1 →ₐ[ℚ_[l]] ↥LL''.1 := (IntermediateField.equivMap Bw'.Kw.1 φ).toAlgHom
  let τL : M →+* Om l := φ.toRingHom.comp (Bw'.j.comp (algebraMap M Ω))
  have hτL : τL.comp (algebraMap E M) = τ := by
    ext x
    show φ (Bw'.j (algebraMap M Ω (algebraMap E M x))) = τ x
    rw [← IsScalarTower.algebraMap_apply E M Ω, hjj, hφx]
  have hind' : IsInduced Bw' τL τ'' := fun x => rfl
  have hJ' : J.map (fun n : ℤ => (n : ℂ)) =
      ((CG.mk PM).infChar (ι.toRingHom.comp τL)).map (fun z => ((n : ℂ) - 1) / 2 - z) := by
    rw [hlift.inf, RingHom.comp_assoc, hτL, hJ]
  exact GlobalTheory.JumpsDescend.jumps_descend E M Ω A w u hA h' l P AI hT n r hw.1 O Bw O' Bw' hj hj' hjj τ τL hτL J
    (hjump τL LL'' τ'' hind' J hJ')

theorem galoisCompat_unlinkedSupport_of_spherical : UpperTheory.Gal.ToralGalois.Inq → GlobalTheory.RoadU.CoreAll → GlobalTheory.DeRhamOfPlainTorus.R1 := by
  intro hI hC E Ω _ _ _ _ _ _ l _ ι n hn π χ hπ r hr w σ hσ hp
  refine ⟨fun hl A h => GlobalTheory.RoadU.away_eq_of_plainTor hI (GlobalTheory.RoadU.toralGal_of_holds hI (hC.2 .unr))
    E Ω l ι n hn π χ hπ r hr w hl A h σ hσ hp,
    fun hl => ⟨deRham_of_plainTor hI (hC.2 .dR) E Ω l ι n hn π χ hπ r hr w σ hσ hp, fun P AI hT A h O _ _ _ Bw hj => ?_⟩⟩
  have : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  obtain ⟨ξ, hξ, hs, hu⟩ := GlobalTheory.RoadU.plainTor_exists_chars (w.adicCompletion E) (algNorm σ) hp
  have key := fun a ha => GlobalTheory.RoadU.toralAbove_of_holds hI (hC.2 .crys) (hC.2 .phi) E Ω l ι n hn π χ hπ r hr w hl A h σ hσ
    ξ hξ hs hu a ha P AI hT O Bw hj
  obtain ⟨a0, ha0⟩ := GlobalTheory.localArtinExists_holds E Ω A w h
  refine ⟨(key a0 ha0).1, (key a0 ha0).2.1, ?_⟩
  rintro rc ⟨a, ha, H⟩ g
  exact ((key a ha).2.2 g).trans
    ((GlobalTheory.RoadU.UnlinkedChars.rc_unlinked_chars hI Ω E w A h a ha rc H (algNorm σ) n ξ hξ hs hu).2 g).symm

end GlobalTheory.DeRhamOfPlainTorus

end
