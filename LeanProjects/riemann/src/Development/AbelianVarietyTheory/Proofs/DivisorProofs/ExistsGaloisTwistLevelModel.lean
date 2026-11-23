import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecializationMapCompUniversalSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithTopOfAdelicIsoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionOfDivisorIsoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicIsoSymmStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CorrespondenceStatementStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedPointRelationFieldExtStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagTorusComponentPointRelationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagTorusPointRelationConverseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedRelationValuationExtendsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedIsoGenericRelationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericRelationUnitSymmetricStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagComponentTriEquationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedGenericRelationExponentsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedGenericRelationDegreesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TriEquationLogIndependent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedLogPushforwardStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedGenericRelationMetric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPullbackRadiusDataStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAuxiliaryMetricPullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedHodgeMetricOffBoundaryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedMetricAtAllRadiiStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagPoly GlobalTheory.FlagAr Filter Topology
open CategoryTheory

namespace GlobalTheory.ShFam.GalCarry

section Free

open AlgebraicGeometry Limits GlobalTheory.Toroidal GlobalTheory.ProjVar GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo

theorem arTop_eq {F : Type} [Field F] [NumberField F] {C : CxSt F} {Y Y' : Var F} {A : Adl C Y} {A' : Adl C Y'}
    {φ : Y.X ≅ Y'.X} {ψ : Y'.Fn →+* Y.Fn} {u : Y.Fnˣ} (h : AdlIso A A' φ ψ u) : A.arTop = A'.arTop := by
  have hd : A.deg = A'.deg := by
    rw [Adl.deg, Adl.deg, GlobalTheory.T.intersection_of_divisor_iso F Y Y' _ _ φ ψ u h.1, h.2.1, h.1.2.2.1]
  obtain ⟨ψ', u', h'⟩ := GlobalTheory.T.adelic_iso_symm F C Y Y' A A' φ ψ u h
  have e : A.IsArTop = A'.IsArTop := funext fun t =>
    propext ⟨GlobalTheory.T.arith_top_of_adelic_iso F C Y' Y A' A φ.symm ψ' u' h' hd.symm t, GlobalTheory.T.arith_top_of_adelic_iso F C Y Y' A A' φ ψ u h hd t⟩
  unfold Adl.arTop
  rw [e]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem exists_locRel {O : Type} [CommRing O] {β : O →+* c.F} {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β} (T : Tw Z)
    {F : Type} [Field F] {e : F ≃+* c.F} {σ : c.F →+* ℂ} {N : ℕ} {U : Formalism.L2.PjFree.Unf Xo c σ N} (Φ : FlagTor Z e U) :
    ∃ a : U.Comp ≃ U.Comp, ∀ k, ∃ φ ψ t₀, T.LocRel (Φ.C k) (Φ.C (a k)) φ ψ t₀ := by
  haveI : CharZero F := RingHom.charZero e.toRingHom
  obtain ⟨a, ha⟩ := GlobalTheory.T.correspondence_statement F U.Comp U.Comp (fun i => (Φ.C i).Y) (fun i => (Φ.C i).Y)
    (fun K _ i i' p p' => T.PtRel (Φ.C i) (Φ.C i') p p')
    (fun K _ i i' p p' h => by
      rw [← (Φ.C i').π_str, ← (Φ.C i).π_str, ← Category.assoc, h.1]
      simp only [Category.assoc, reassoc_of% T.g_str])
    (fun K K' _ _ ν i i' p p' => GlobalTheory.T.twisted_point_relation_field_ext E H Dw l Xo c O β Z T F e _ _ K K' ν p p')
    (fun K _ _ i p => GlobalTheory.T.flag_torus_component_point_relation E H Dw l Xo c O β Z T F e σ N U Φ K i p)
    (fun K _ _ i p => GlobalTheory.T.flag_torus_point_relation_converse E H Dw l Xo c O β Z T F e σ N U Φ K i p)
    (fun V _ _ _ L _ ν k _ r i i' q q' => GlobalTheory.T.twisted_relation_valuation_extends E H Dw l Xo c O β Z T F e _ _ V L ν k r q q')
  refine ⟨a, fun k => ?_⟩
  obtain ⟨φ, hφ⟩ := ha k
  obtain ⟨ψ, t₀, h⟩ := GlobalTheory.T.twisted_iso_generic_relation E H Dw l Xo c O β Z T F e _ _ φ hφ
  exact ⟨φ, ψ, t₀, GlobalTheory.T.generic_relation_unit_symmetric E H Dw l Xo c O β Z T F e _ _ φ ψ t₀ h⟩

theorem parOf_sym {O : Type} [CommRing O] {β : O →+* c.F} {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β} (T : Tw Z)
    {R : Option ℝ} {w : Sym E →₀ ℤ} (hw : ∀ a ∈ w.support, a.2.1 = R) : parOf (w.mapDomain T.sym) = parOf w := by
  have hi : Function.Injective T.sym := by
    rintro ⟨b, r, x⟩ ⟨b', r', x'⟩ h
    simp only [Tw.sym, Prod.mk.injEq] at h
    refine Prod.ext h.1 (Prod.ext h.2.1 (Sum.map_injective.2 ⟨?_, Function.injective_id⟩ h.2.2))
    rintro ⟨τ, k⟩ ⟨τ', k'⟩ h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (T.embEquiv.injective h.1) h.2
  have hs := Finsupp.mapDomain_support_of_injective hi w
  unfold parOf
  by_cases h : w.support.Nonempty
  · have h' : (w.mapDomain T.sym).support.Nonempty := hs ▸ h.image _
    rw [dif_pos h, dif_pos h', hw _ h.choose_spec]
    obtain ⟨a, ha, e⟩ := Finset.mem_image.1 (hs.le h'.choose_spec)
    rw [← e]
    exact hw a ha
  · rw [dif_neg h, dif_neg fun h' => h (Finset.image_nonempty.1 (hs ▸ h'))]

end Free

theorem carry : Hypotheses2 → HypothesesH → ∀ (D : D7) (O : Setup D), O.Core → ∀ h ∈ D.R.Psi,
    (∀ g ∈ D.R.Psi,
      ∃ (σ : 𝓞 D.host.E ≃+* 𝓞 D.host.E) (r : (O.S.Xo O.κ.l).XF O.κ.c ≅ (O.S.Xo O.κ.l).XF O.κ.c),
        (∀ a : 𝓞 D.host.E, ((σ a : 𝓞 D.host.E) : D.host.E) = D.host.sigmaOf g (a : D.host.E)) ∧
        σ O.A.H.w0 = O.A.H.w0 ∧ Nonempty (GlobalTheory.ShFam.TwMap σ O.s.T.Z.oF.t O.s.T.Z.oF.t r.hom) ∧
        r.hom ≫ CategoryTheory.Limits.pullback.snd _ _ = CategoryTheory.Limits.pullback.snd _ _) →
    ∀ x : GlobalTheory.ShFam.ToroidalCompactificationData O.s, ∃ (x' : GlobalTheory.ShFam.ToroidalCompactificationData O.s) (e : O.s.Comp ≃ O.s.Comp),
      ∀ (k : O.s.Comp) (R : Option ℝ) (w : GlobalTheory.ShFam.Pad.Sym D.host.E →₀ ℤ),
        (∀ a ∈ w.support, a.2.2.isLeft = true ∧ a.2.1 = R) →
        (GlobalTheory.ShFam.Pad.adlOf (O.Φ.C k) (GlobalTheory.ShFam.metsOf x O.Φ k) w).arTop =
          (GlobalTheory.ShFam.Pad.adlOf (O.Φ.C (e k)) (GlobalTheory.ShFam.metsOf x' O.Φ (e k))
            (w.mapDomain fun a => (a.1, a.2.1,
              Sum.map (fun p => (p.1.comp ((D.host.sigmaOf h : D.host.E ≃ₐ[ℚ] D.host.E) : D.host.E →+* D.host.E), p.2)) id
                a.2.2))).arTop := by
  intro _ _ D O _ h hh htw x
  obtain ⟨σ, r, hσ, hw0, ⟨ν⟩, hr⟩ := htw h hh
  obtain ⟨T, hT⟩ := exists_tw O.s.isRec.stable (D.host.sigmaOf h) σ hσ hw0 r ν hr
  obtain ⟨x₁, h₁⟩ := GlobalTheory.T.exists_pullback_radius_data _ _ _ _ _ _ _ _ _ T x
  obtain ⟨x₂, h₂⟩ := GlobalTheory.T.exists_auxiliary_metric_pullback _ _ _ _ _ _ _ _ _ T x
  let x' : GlobalTheory.ShFam.ToroidalCompactificationData O.s := { x₁ with met := x₂.met, met_smooth := x₂.met_smooth, met_conj := x₂.met_conj }
  have hm := GlobalTheory.T.twisted_metric_at_all_radii D _ _ _ _ _ O.s T x x' h₁ h₂ (GlobalTheory.T.twisted_hodge_metric_off_boundary D _ _ _ _ _ O.s T x x')
  obtain ⟨a, ha⟩ := exists_locRel T O.Φ
  refine ⟨x', a.symm, fun k R w hw => ?_⟩
  obtain ⟨k, rfl⟩ := a.surjective k
  rw [a.symm_apply_apply, ← hT]
  obtain ⟨φ, ψ, t₀, hl⟩ := ha k
  have hw₁ := fun b hb => (hw b hb).1
  have hn := T.expo_sym hw₁
  have he := GlobalTheory.T.flag_component_tri_equation _ _ _ _ _ _ _ _ _ _ _ (O.Φ.C k)
  refine (arTop_eq (A := Pad.adlOf (O.Φ.C k) (metsOf x' O.Φ k) (w.mapDomain T.sym)) (φ := φ) (ψ := ψ)
    (u := prodPow t₀ (Pad.expo _ w)) ⟨?_, rfl, rfl, fun s p p' hp g hg => ?_, ?_⟩).symm
  · exact GlobalTheory.T.twisted_generic_relation_exponents _ _ _ _ _ _ _ _ _ T _ _ _ _ φ ψ t₀ _ _ he hl ((O.Φ.dim_eq _).trans (O.Φ.dim_eq _).symm) hn
  · have := GlobalTheory.T.twisted_generic_relation_degrees _ _ _ _ _ _ _ _ _ T _ _ _ _ φ ψ t₀ _ _ s _ _ hl hn (hm _ (Pad.parOf w)) p p' hp g hg
    rw [← parOf_sym T fun b hb => (hw b hb).2] at this
    conv_rhs at this => rw [parOf_sym T fun b hb => (hw b hb).2]
    exact this
  · exact GlobalTheory.T.twisted_generic_relation_metric _ _ _ _ _ _ _ _ _ T _ _ _ _ φ ψ t₀ w (GlobalTheory.T.twisted_log_pushforward _ _ _ _ _ _ _ T)
      (GlobalTheory.T.tri_equation_log_independent _ _ _ _ _ _ _ _ _ _ he) he hl hw₁

end GlobalTheory.ShFam.GalCarry
