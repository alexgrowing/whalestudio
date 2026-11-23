import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.Definitions.Divisors.AdjKltOfLtDisc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStalkEquivOfFromSpecStalk
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KltAlongPlaceNeighboursRingEquiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscrepancyFormulaDivisor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalTopFormPullbackBijectiveBirational
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitAtFnOfOfNotMem
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.CanonicalDivisorBirationalCompare
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldPair.AdjUp

theorem regAt_map {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (s : Y ⟶ X) [IsDominant s]
    (z : Y) {f : X.functionField} (h : RegAt (s z) f) : RegAt z (functionFieldMap s f) := by
  obtain ⟨a, rfl⟩ := h
  exact ⟨s.stalkMap z a, (functionFieldMap_algebraMap s z a).symm⟩

theorem scheme_ord_zero {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] (z : Y) :
    Scheme.ord (0 : Y.functionField) z = 0 := by
  unfold Scheme.ord
  split_ifs <;> simp

theorem place_ord_eq {k : Type} [Field k] {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y]
    {q : Y ⟶ Sp k} {E : DivOver q} {z : Y} (h : E.IsAt z) (f : Y.functionField) :
    (placeEquiv q E).ord f = Scheme.ord f z := by
  by_cases hf : f = 0
  · subst hf
    rw [scheme_ord_zero]
    simp [Place.ord]
  · exact h.ord_eq (Units.mk0 f hf)

theorem ring_eq_of_isAt {k : Type} [Field k] {Y : Scheme.{0}} [IsIntegral Y] {q : Y ⟶ Sp k}
    {E F : DivOver q} {z : Y} (hE : E.IsAt z) (hF : F.IsAt z) :
    (placeEquiv q E).ring = (placeEquiv q F).ring :=
  SetLike.ext fun f => (hE f).trans (hF f).symm

def stalkEquiv {Y : Scheme.{0}} [IsIntegral Y] (w : Y) : Y.presheaf.stalk w ≃+* locRing w :=
  RingEquiv.ofBijective (algebraMap (Y.presheaf.stalk w) Y.functionField).rangeRestrict
    ⟨fun _ _ e => IsFractionRing.injective _ Y.functionField (congrArg Subtype.val e),
      RingHom.rangeRestrict_surjective _⟩

theorem stalkEquiv_apply {Y : Scheme.{0}} [IsIntegral Y] (w : Y) (a : Y.presheaf.stalk w) :
    ((stalkEquiv w a : locRing w) : Y.functionField) = algebraMap _ Y.functionField a := rfl

theorem map_maximalIdeal_equiv {R R' : Type*} [CommRing R] [CommRing R'] [IsLocalRing R]
    [IsLocalRing R'] (φ : R ≃+* R') :
    (IsLocalRing.maximalIdeal R).map φ = IsLocalRing.maximalIdeal R' := by
  ext a
  rw [Ideal.mem_map_of_equiv, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  constructor
  · rintro ⟨b, hb, rfl⟩ h
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hb
    exact hb ((isUnit_map_iff φ b).1 h)
  · intro ha
    refine ⟨φ.symm a, ?_, by simp⟩
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro h
    exact ha (by simpa using h.map φ)

end GlobalTheory.FieldPair.AdjUp

open GlobalTheory.FieldPair.AdjUp in

theorem GlobalTheory.FieldPair.mult_lt_of_adjKlt : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (x : Fin n → X.functionField) (m : ℕ) (g : X.functionFieldˣ) (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (s : Y ⟶ X) [IsDominant s] (K : CartierDiv Y) (B : Closeds Y) (y : X) (σ : Y) (S : DivOver p) (S' : DivOver (s ≫ p)), TrBasis (Cartier.constFn p) x → 0 < m → IsLogRes p n (dForm (Cartier.constFn p) x) m (CartierDiv.principal g) s K B → DivOver.Over s S' S → S'.IsAt σ → (pullCart s (CartierDiv.principal g) - m • K).mult σ = m → AdjKlt (Cartier.constFn p) n (locRing y) (placeEquiv p S) (dForm (Cartier.constFn p) x) (Finsupp.single (g : X.functionField) (1 / (m : ℚ))) → ∀ v w : Y, v ≠ σ → v ⤳ w → σ ⤳ w → s w ⤳ y → (pullCart s (CartierDiv.principal g) - m • K).mult v < m := by
  intro X _ _ p n _ _ x m g Y _ _ s _ K B y σ S S' hx hm hres hover hσ hmσ hadj v w hvσ hvw hσw hwy
  by_cases hv0 : (pullCart s (CartierDiv.principal g) - m • K).mult v ≤ 0
  · exact lt_of_le_of_lt hv0 (by exact_mod_cast hm)
  have hv0' : (pullCart s (CartierDiv.principal g) - m • K).mult v ≠ 0 := by omega
  haveI := hres.smooth
  haveI := SmoothOfRelativeDimension.smooth n (s ≫ p)
  haveI : GlobalTheory.IsNormalScheme Y := Discrepancy.CanonIso.isNormalScheme_of_smooth' (s ≫ p)
  have hmσ0 : (pullCart s (CartierDiv.principal g) - m • K).mult σ ≠ 0 := by
    rw [hmσ]; exact_mod_cast hm.ne'
  have hvB : v ∈ B := hres.supp (CartierDiv.mem_supp_of_mult_ne_zero hv0')
  have hσB : σ ∈ B := hres.supp (CartierDiv.mem_supp_of_mult_ne_zero hmσ0)
  have hv1 := CartierDiv.coheight_eq_one_of_mult_ne_zero hv0'
  have hσ1 := hσ.coheight_eq_one
  obtain ⟨w', t, u, hw'w, hvw', hσw', hdim, hspan, htσ, huv, hB⟩ :=
    GlobalTheory.SncMeet.exists_meet_point Y (s ≫ p) n B hres.snc v σ w hvB hσB hv1 hσ1 hvσ hvw hσw
  obtain ⟨Ev, hEv⟩ := DivOver.exists_isAt_of_coheight_eq_one (p := s ≫ p) hv1
  let e : X.functionField ≃+* Y.functionField := RingEquiv.ofBijective (functionFieldMap s) hres.bir
  have hc : ∀ a, e (Cartier.constFn p a) = Cartier.constFn (s ≫ p) a := fun a =>
    RingHom.congr_fun (EtaleKlt.functionFieldMap_comp_constFn p s) a
  have hadj' := GlobalTheory.FieldPair.adjKlt_ringEquiv (Cartier.constFn p) (Cartier.constFn (s ≫ p)) e hc n x (locRing y)
    (Finsupp.single (g : X.functionField) (1 / (m : ℚ))) (placeEquiv p S) (placeEquiv (s ≫ p) S') hx
    (fun a => (hover a).symm) hadj
  rw [Finsupp.mapDomain_single] at hadj'
  have hη : dForm (Cartier.constFn (s ≫ p)) (e ∘ x) =
      EtaleKlt.ratPull p s n (dForm (Cartier.constFn p) x) := by
    rw [EtaleKlt.ratPull, formMap_dForm]
    rfl
  have hη0 : EtaleKlt.ratPull p s n (dForm (Cartier.constFn p) x) ≠ 0 := fun h0 =>
    hadj.form_ne_zero ((EtaleKlt.ratPull_bijective_of_birational ℂ X Y p s hres.bir n).1
      (h0.trans (map_zero _).symm))
  rw [hη] at hadj'
  unfold AdjKlt at hadj'
  have hdisc : ∀ (P : DivOver (s ≫ p)) (z : Y), P.IsAt z →
      (placeEquiv (s ≫ p) P).disc (EtaleKlt.ratPull p s n (dForm (Cartier.constFn p) x))
        (Finsupp.single (e g) (1 / (m : ℚ))) =
        -((pullCart s (CartierDiv.principal g) - m • K).mult z : ℚ) / m := by
    intro P z hP
    have h1 := disc_placeEquiv P (EtaleKlt.ratPull p s n (dForm (Cartier.constFn p) x)) m (fnPull s g)
    exact h1.trans (discrep_isAt_eq_neg_mult ℂ Y (s ≫ p) n _ hη0 K _ m hm hres.div P z (fnPull s g) hP
      (isEqn_pullCart s (CartierDiv.isEqn_principal g (s z))))
  have hTQ : (locRing y).map e.toRingHom ≤ locRing w' := by
    rintro _ ⟨a, ha, rfl⟩
    have h1 : s w' ⤳ y := (hw'w.map s.continuous).trans hwy
    exact regAt_map s w' (regAt_of_specializes h1 ha)
  have hQ := isLocModel_locRing (p := s ≫ p) w'
  have key := hadj'.2.2 (locRing w') hQ (stalkEquiv w' t) (stalkEquiv w' u) (placeEquiv (s ≫ p) Ev) hTQ
    ?_ ?_ ((isPrimeOf_placeEquiv S' w').2 ⟨σ, hσw', hσ⟩) ((isPrimeOf_placeEquiv Ev w').2 ⟨v, hvw', hEv⟩)
    (by rw [stalkEquiv_apply, place_ord_eq hσ]; exact htσ)
    (by rw [stalkEquiv_apply, place_ord_eq hEv]; exact huv) ?_
  · rw [hdisc Ev v hEv] at key
    have hm' : (0 : ℚ) < m := by exact_mod_cast hm
    rw [lt_div_iff₀ hm'] at key
    have : ((pullCart s (CartierDiv.principal g) - m • K).mult v : ℚ) < m := by linarith
    exact_mod_cast this
  · have h1 : Ideal.span {stalkEquiv w' t, stalkEquiv w' u} = (Ideal.span {t, u}).map (stalkEquiv w') := by
      rw [Ideal.map_span]; simp [Set.image_insert_eq]
    rw [h1, hspan]
    haveI := hQ.isLocalRing
    exact map_maximalIdeal_equiv _
  · exact (ringKrullDim_eq_of_ringEquiv (stalkEquiv w')).symm.trans hdim
  · intro P hP h1 h2
    obtain ⟨P₀, rfl⟩ := (placeEquiv (s ≫ p)).surjective P
    obtain ⟨z, hzw', hz⟩ := (isPrimeOf_placeEquiv P₀ w').1 hP
    rw [hdisc P₀ z hz]
    have hz1 := hz.coheight_eq_one
    have hzσ : z ≠ σ := by rintro rfl; exact h1 (ring_eq_of_isAt hz hσ)
    have hzv : z ≠ v := by rintro rfl; exact h2 (ring_eq_of_isAt hz hEv)
    have hzB : z ∉ B := fun hzB => (hB z hzB hz1 hzw').elim hzv hzσ
    have h0 : (pullCart s (CartierDiv.principal g) - m • K).mult z = 0 := by
      by_contra h0
      exact hzB (hres.supp (CartierDiv.mem_supp_of_mult_ne_zero h0))
    rw [h0]
    simp
