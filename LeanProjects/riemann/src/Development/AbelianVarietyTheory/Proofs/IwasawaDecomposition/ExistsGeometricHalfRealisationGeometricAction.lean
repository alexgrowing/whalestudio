import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelActionCuspFormRepresentation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidualCharacterDetValuesMemCoeffField
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JEvExists
import Formalism.LocalToGlobal.UnitaryNorms.CharTied
import Formalism.LocalRingCardinality.DataKap
import Formalism.LocalToGlobal.ProjectiveLattices.HasDataCondition
import Formalism.LocalToGlobal.ProjectiveLattices.RecCond
import Formalism.LocalToGlobal.ProjectiveLattices.ParCanon
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RealGeo.Half

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

set_option maxHeartbeats 1600000 in

theorem preChar_updFW {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    (nW : Fin D.R.m → ℕ) (FW : ∀ i, Arith.FormsL D.what₂.LL Ks (Fin (nW i) → D.what₂.LL) (fun σ => (R.HW i σ).H) G)
    (h : PreChar R) : PreChar (updFW R nW FW) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  refine ⟨h1, h2, h3, h4, ?_, ?_, ?_, ?_⟩
  · exact ⟨h5.1, h5.2, h5.3, h5.4, h5.5, h5.6, h5.7, h5.8⟩
  · exact ⟨h6.1, h6.2, h6.3, h6.4, h6.5, h6.6, h6.7, h6.8, h6.9, h6.10, h6.11, h6.12, h6.13, h6.14, h6.15, h6.16, h6.17,
      h6.18, h6.19, h6.20, h6.21⟩
  · exact ⟨h7.1, h7.2, h7.3, h7.4, h7.5, h7.6, h7.7, h7.8, h7.9, h7.10, h7.11⟩
  · exact ⟨h8.1, h8.2, h8.3, h8.4, h8.5, h8.6, h8.7⟩

variable (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1))
  (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)

section Upd

variable (nW : Fin D.R.m → ℕ) (FW : ∀ i, Arith.FormsL D.what₂.LL T.Q.c.F (Fin (nW i) → D.what₂.LL) (fun σ => (R.HW i σ).H) G)

set_option maxHeartbeats 1600000 in

def updO {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0} (O : OMDat T.toCore R i Tp tup) :
    OMDat T.toCore (updFW R nW FW) i Tp tup := { O with }

variable (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0))

set_option maxHeartbeats 1600000 in
theorem omPins_upd (i : Fin D.R.m) (h : OMPins T R κ v₀ O i) :
    OMPins T (updFW R nW FW) κ v₀ (fun i => updO T R nW FW (O i)) i := by
  refine ⟨h.1, ?_⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h.2
  refine ⟨⟨h1.field, h1.std, ?_, h1.c0, h1.lev⟩, fun t => ⟨(h2 t).reps, (h2 t).B, (h2 t).xi, (h2 t).phi, (h2 t).half⟩,
    h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  exact h1.v0

set_option maxHeartbeats 1600000 in
theorem fired_upd (ph : Fin D.R.m → ℂ) (h : Fired T R κ v₀ O ph) :
    Fired T (updFW R nW FW) κ v₀ (fun i => updO T R nW FW (O i)) ph :=
  ⟨fun i => h.1 i, fun i σ hσ hV => h.2 i σ hσ hV⟩

end Upd

variable (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0))

set_option maxHeartbeats 1600000 in

def tieGeo (h : TieIn T R κ v₀) : FWTie T (geoR T R κ v₀ O) κ v₀ :=
  let t := tieN T R κ v₀ (nTop T κ) h (hasB_nTop T h.laws κ)
  { alg_eq := t.alg_eq, e := t.e, ks := t.ks, kap := t.kap, pt := t.pt, nrm_eq := t.nrm_eq, laws := t.laws, chiR := t.chiR,
    hv₀ := t.hv₀, x0 := t.x0, ev0 := t.ev0, ev := t.ev }

set_option maxHeartbeats 1600000 in
theorem barTie_tieGeo (h : TieIn T R κ v₀) : BarTie (tieGeo T R κ v₀ O h) :=
  fun i σ hσ hV => barTie_tieN T R κ v₀ (nTop T κ) h (hasB_nTop T h.laws κ) i σ hσ hV

set_option maxHeartbeats 1600000 in
theorem rhoGeo_tieGeo (h : TieIn T R κ v₀) (hp : ∀ i, OMPins T R κ v₀ O i) :
    RhoGeo (tieGeo T R κ v₀ O h) (fun i => updO T R _ _ (O i)) := by
  intro i
  have hb := hasB_nTop T h.laws κ i
  refine ⟨fun hk g f => ?_, fun hk g => ?_⟩
  · have hex := GlobalTheory.LevelRep.exists_cusp_rep T κ i (O i).lev2 h.laws (hp i).2.act.1 hk
    refine ⟨hk g f f.2, ?_⟩
    have e1 : geoRho T R κ O i = rhoB D.what₂.LL hb.some hex.choose := dif_pos ⟨hb, hex⟩
    have e2 : (⟨_, hk g f f.2⟩ : Cu T κ i) = hex.choose g f := Subtype.ext (hex.choose_spec g f).symm
    show crdOr T.Q.c.F D.what₂.LL (Cu T κ i) (nTop T κ i) ⟨_, hk g f f.2⟩ =
      geoRho T R κ O i g (crdOr T.Q.c.F D.what₂.LL (Cu T κ i) (nTop T κ i) f)
    rw [e1, e2, crdOr_eq hb, rhoB_crd]
  · have e1 : geoRho T R κ O i = 1 := dif_neg fun h' => hk fun g f hf => by
      have h1 := h'.2.choose_spec g ⟨f, hf⟩
      have h2 := (h'.2.choose g ⟨f, hf⟩).2
      rw [h1] at h2
      exact h2
    show geoRho T R κ O i g = 1
    rw [e1]
    rfl

set_option maxHeartbeats 1600000 in
theorem chiIs_chiTop_of_tie (hL : R.toLevCh.Is A.μ0) (h : TieIn T R κ v₀) (i : Fin D.R.m) : ChiIs R i (chiTop R i) := by
  choose y ha using GlobalTheory.ChiDetValues.chiC_mem_coeff T R κ v₀ hL h i
  have hne : ∀ g, algebraMap T.Q.c.F D.what₂.LL (y g) ≠ 0 := fun g h0 => (chiC R i g).ne_zero (by rw [← ha, h0, map_zero])
  have hex : ∃ chi, ChiIs R i chi :=
    ⟨MonoidHom.mk' (fun g => Units.mk0 _ (hne g)) fun g g' => Units.ext (D.what₂.embLL.injective (by
      simp only [Units.val_mk0, Units.val_mul, map_mul, ha, chiC_mul])), ha⟩
  rw [chiTop, dif_pos hex]
  exact hex.choose_spec

end GlobalTheory.RealGeo.Half

namespace GlobalTheory.RealGeo

set_option maxHeartbeats 1600000 in

theorem exists_geoHalf_geoR : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : Fin D.R.m → ℂ), PreChar R → TieIn T R κ v₀ → (∀ i, OMPins T R κ v₀ O i) → Fired T R κ v₀ O ph → ∃ B : GeoHalf T (geoR T R κ v₀ O) ph, B.κ = κ ∧ B.v₀ = v₀ ∧ Fired T (geoR T R κ v₀ O) B.κ B.v₀ B.O ph ∧ PreChar (geoR T R κ v₀ O) ∧ (geoR T R κ v₀ O).grp_chiW := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ O ph hc ht hp hf
  have hf' := Half.fired_upd T R κ v₀ (nTop T κ) (formsGeo T R κ v₀ O) O ph hf
  refine ⟨⟨κ, v₀, Half.tieGeo T R κ v₀ O ht, Half.barTie_tieGeo T R κ v₀ O ht, fun i => Half.updO T R _ _ (O i),
    fun i => Half.omPins_upd T R κ v₀ _ _ O i (hp i), Half.rhoGeo_tieGeo T R κ v₀ O ht hp,
    fun i σ hσ hV _ => hf'.2 i σ hσ hV, fun i _ => ⟨ph i, hf'.1 i⟩, fun i _ _ => hf'.1 i⟩,
    rfl, rfl, hf', Half.preChar_updFW R _ _ hc, fun i g => ?_⟩
  exact (Half.chiIs_chiTop_of_tie T R κ v₀ hc.lev ht i g).trans (Units.coe_prod _ _)

end GlobalTheory.RealGeo
