import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CyclicStrongAtCusp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFormsFiniteGL
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InfiniteQuadraticCMGoodBaseChangeSplit
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PolarizedPairBaseChangePolarizedSameWeight
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeaklyAttachedGaloisRepresentationBaseChangeRest
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPlaceNormVEq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.QuadLift
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.UnrDescent

theorem main : Inputs → SphericalLevelCondition .good .unr → SphericalLevelCondition .all .unr := by
  intro hI hG E Ω _ _ _ _ _ _ l _ ι a ha π χ hsc r hr w _ B hB hl A h
  have hAF := GlobalTheory.automorphicFormsFiniteGL
  obtain ⟨Q, hQdec, hQsplit, hQram, hQgood⟩ := (GlobalTheory.GalCut.infinite_qcm_split_good hAF E Ω l a π w).nonempty
  obtain ⟨P, hP⟩ := GlobalTheory.QuadLiftBridge.quadLift hI.ac hI.js E Q.K Q.two a ha π hQram
  obtain ⟨⟨χ', hsc'⟩, -⟩ := GlobalTheory.LiftPolar.main hAF hI.js hI.gk E Q.K l a ha π χ P hP hsc.all
  have hscG : InScope .good l P χ' := ⟨hsc'.1, hsc'.2.1, hQgood P hP⟩
  have hrP : Weak P ι (r.comp (UpperTheory.V.Af.Bc.res E Ω Q.K)) := GlobalTheory.GalCut.weak_comp_res E Q.K Ω l ι a π P hP r hr
  obtain ⟨w', hunder, h', hN⟩ := GlobalTheory.PlaceNormDec.exists_place_normV_eq E Ω Q w A h (hQdec A h)
  have hB' : (CG.mk P).HasSat w' B := by
    have e := hP.sat w' 1 B (by rw [pow_one, hunder, hN]) (hunder ▸ hB)
    simpa using e
  have hlw : ((l : ℕ) : 𝓞 Q.K) ∉ w'.asIdeal := by
    intro hw
    apply hl
    have e1 := (h ((l : ℕ) : 𝓞 E))
    have e2 := (h' ((l : ℕ) : 𝓞 Q.K))
    simp only [map_natCast] at e1 e2
    exact e1.1 (e2.2 hw)
  have hcl := hG Q.K Ω l ι a ha P χ' hscG (r.comp (UpperTheory.V.Af.Bc.res E Ω Q.K)) hrP w' (hQsplit w' hunder) B hB' hlw A h'
  rw [hN] at hcl
  refine ⟨fun s hs => ?_, fun σ hσ => ?_⟩
  · obtain ⟨s', rfl⟩ := hQdec A h (Ine_le_Dec A hs)
    exact hcl.1 s' hs
  · obtain ⟨σ', rfl⟩ := hQdec A h hσ.1
    have e := hcl.2 σ' hσ
    rw [← map_inv]
    exact e

end GlobalTheory.UnrDescent
