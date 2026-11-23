import Formalism.AdmissibleDesigns.CycMatchRec
import Formalism.SharpRestriction.LevelLetterCocycles.IsobaricMultiplicityOne

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Classical Topology

namespace Formalism.MainNotions.N.KBKa

open Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.N.KHf

section HK

variable {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
  {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [IsDomain O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  (Bw : LocBridge l E Ω Gw O) [TopologicalSpace (FractionRing O)] [IsTopologicalAddGroup (FractionRing O)]

theorem homeoK_of (hF : IsOpenEmbedding (algebraMap O (FractionRing O))) : HomeoK (eK Bw) := by
  have hG := (T2.litGoodO l Bw.LL)
  have hOpen : IsOpen ((OL Bw.LL : Subalgebra ℤ_[l] (Br.LLw Bw)) : Set (Br.LLw Bw)) := by
    have h := hG.2.2.2.2
    rwa [show Set.range (algebraMap ↥(OL Bw.LL) ↥Bw.LL.1) = ((OL Bw.LL : Subalgebra ℤ_[l] (Br.LLw Bw)) : Set (Br.LLw Bw))
      from Subtype.range_coe] at h
  have hOL : IsOpenEmbedding (Subtype.val : ↥(OL Bw.LL) → Br.LLw Bw) := hOpen.isOpenEmbedding_subtypeVal
  constructor
  · refine continuous_of_continuousAt_zero (eK Bw) ?_
    have hc : Continuous fun x : O => eK Bw (algebraMap O (FractionRing O) x) := by
      have h1 : (fun x : O => eK Bw (algebraMap O (FractionRing O) x)) = fun x => ((Bw.eO x : ↥(OL Bw.LL)) : Br.LLw Bw) :=
        funext fun x => Br.toLLK_alg Bw x
      rw [h1]
      exact continuous_subtype_val.comp Bw.eO_cont
    show Filter.Tendsto (eK Bw) (𝓝 0) (𝓝 (eK Bw 0))
    rw [← map_zero (algebraMap O (FractionRing O)), ← hF.map_nhds_eq, Filter.tendsto_map'_iff]
    exact hc.tendsto 0
  · refine continuous_of_continuousAt_zero (eK Bw).symm ?_
    have hc : Continuous fun y : ↥(OL Bw.LL) => (eK Bw).symm (y : Br.LLw Bw) := by
      have h1 : (fun y : ↥(OL Bw.LL) => (eK Bw).symm (y : Br.LLw Bw)) =
          fun y => algebraMap O (FractionRing O) (Bw.eO.symm y) := by
        funext y
        apply (eK Bw).injective
        rw [RingEquiv.apply_symm_apply, eK_apply, Br.toLLK_alg, RingEquiv.apply_symm_apply]
        rfl
      rw [h1]
      exact hF.continuous.comp Bw.eO_symm_cont
    show Filter.Tendsto (eK Bw).symm (𝓝 0) (𝓝 ((eK Bw).symm 0))
    rw [show (0 : Br.LLw Bw) = ((0 : ↥(OL Bw.LL)) : Br.LLw Bw) from rfl, ← hOL.map_nhds_eq,
      Filter.tendsto_map'_iff]
    exact hc.tendsto 0

end HK

section Final

open NumberField IsDedekindDomain

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  [TopologicalSpace (FractionRing (D.nd.O i))] [IsTopologicalAddGroup (FractionRing (D.nd.O i))]
  [ContinuousSMul (D.nd.O i) (FractionRing (D.nd.O i))] [IsDiscreteValuationRing (D.nd.O i)]

theorem bKa_pi (n n' : Type) [Fintype n] [Fintype n']
    (Dat : ∀ w, Formalism.RepresentationBoundsCohomology.LOC.LatData (D.nd.O i) ↥(Γn i dc w) (n → FractionRing (D.nd.O i))
      (n' → FractionRing (D.nd.O i)))
    [∀ w, Module (FractionRing (D.nd.O i)) (ReciprocityTheory.Gal.H1 (Dat w).ρT)]
    [∀ w, IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) (ReciprocityTheory.Gal.H1 (Dat w).ρT)]
    [∀ w, Module (FractionRing (D.nd.O i)) (ReciprocityTheory.Gal.H1 (Dat w).ρT')]
    [∀ w, IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) (ReciprocityTheory.Gal.H1 (Dat w).ρT')]
    (hBK : LargeLevelLemmas.BlochKatoAnnihilators i) (hG : K.SelfGood i) {w : ℕ} (hw : w ∈ K.rowsN i dc)
    (hreal : Formalism.RepresentationBoundsCohomology.FIN.RealLat (Dat w))
    (hε : ∀ g : ↥(Γn i dc w), (Dat w).ε g = epsU D.nd i (g : GE D.nd))
    (hF : IsOpenEmbedding (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))))
    (hdr : ∀ hn : K.plOf i dc w ∈ placesOver D.host.E (D.nd.l i),
      IsDR (Br.PD D.loc D.nbr i _ hn) (repL (eK (D.nbr i _ hn)) (Dat w).ρT (Br.iota D.nbr i _ hn))) :
    BKa i dc (fun _ => n → FractionRing (D.nd.O i)) (fun _ => n' → FractionRing (D.nd.O i)) Dat w :=
  bk_a_of_admitted_bk_a i dc _ _ Dat hBK hG hw hreal
    (rowIn_of i dc _ _ Dat hε (fun hn => ⟨homeoK_of (D.nbr i _ hn) hF,
      topMatch_pi (eK (D.nbr i _ hn)) n (homeoK_of (D.nbr i _ hn) hF),
      topMatch_pi (eK (D.nbr i _ hn)) n' (homeoK_of (D.nbr i _ hn) hF)⟩) hdr)

end Final

end Formalism.MainNotions.N.KBKa
