import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.NumericalH1Condition
import Formalism.LocalToGlobal.ProjectiveLattices.HeightF1OfData
import Formalism.LocalToGlobal.ProjectiveLattices.DivFinOfLawA3
import Formalism.LocalToGlobal.ProjectiveLattices.CompTie
import Formalism.LocalToGlobal.ProjectiveLattices.CuspidalL2Subspace
import Formalism.LocalToGlobal.ProjectiveLattices.FnTrdegOf
import Formalism.LocalToGlobal.ProjectiveLattices.CrudeVal
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.NotOverAndTriv
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsFrameShiftFrShFin
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.KapFgTrdeg
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.MemRangeOfIsAlgebraicRatFun
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.NumericalConsequencesOfPins

noncomputable section

namespace GlobalTheory.HeightDefinite.Ties

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0 Formalism.L2.Pj GlobalTheory.Height.OrderTieGuards

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem ordTieOn_of_valued {h : GenFrEx Xo c} {δ : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → Ix Dw → ℤ}
    {PY : HeightOneSpectrum (𝓞 c.F) → Type}
    {lies : ∀ la (T : CDVR) (ι : c.F →+* T.Fr), IntFr Xo c T ι → PY la → Prop}
    (hl : LiesTotal Xo c (trivialClassCondition Xo c) PY lies)
    (hv : ∀ (Z : Comp Xo c) (v : AddValuation (Om Z) (WithTop ℤ)), IsNormDiscrete v →
      ((∃ la, IsOver (K := c.F) v la) ∨ IsTrivOn c.F v) →
      ∃ (T : CDVR) (ψ : Om Z →+* T.Fr) (y : IntFr Xo c T (ψ.comp (algebraMap c.F (Om Z)))),
        (∀ a : Om Z, a ≠ 0 → ((vV T.V (ψ a) : ℤ) : WithTop ℤ) = v a) ∧
        ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c), f ∈ sec Xo c a n → (evI y f = 0 ↔ evC h Z f = 0) ∧
          (evC h Z f ≠ 0 → ordC (δ Z v) v (wtZ a n) (valC h a n f Z) = vV T.V (evI y f))) :
    OrdTieOn h δ (trivialClassCondition Xo c) PY lies := by
  intro Z v la hd ho
  obtain ⟨T, ψ, y, hψ, hy⟩ := hv Z v hd (Or.inl ⟨la, ho⟩)
  obtain ⟨hpos, hres⟩ := restrict_eq hd ho
  obtain ⟨e, he⟩ := Int.eq_ofNat_of_zero_le hpos.le
  have he0 : 0 < e := by omega
  have hO : OverLa la T.V (ψ.comp (algebraMap c.F (Om Z))) e := by
    refine ⟨he0, fun a => ?_⟩
    by_cases ha : a = 0
    · subst ha; simp [vV, vLa]
    · have := (hψ _ ((map_ne_zero (algebraMap c.F (Om Z))).2 ha)).trans (hres a ha)
      rw [he] at this
      exact_mod_cast this
  obtain ⟨η, hη⟩ := hl la T _ e hO y trivial
  refine ⟨PtV.mk la hO y trivial η hη, fun a n f hf h0 => ?_, fun a n f hf h0 _ => ?_⟩
  · change _ = _ * nval T.V e (evI y f)
    rw [nval_of_ne (fun hz => h0 ((hy a n f hf).1.1 hz)), (hy a n f hf).2 h0, he, ← EReal.coe_mul,
      EReal.coe_eq_coe_iff]
    have : (e : ℝ) ≠ 0 := by exact_mod_cast he0.ne'
    push_cast
    field_simp
  · change nval T.V e (evI y f) = ⊤
    rw [(hy a n f hf).1.2 h0, nval_zero]

end

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj

theorem exists_unit_of_vV_eq_zero (T : CDVR) {x : T.Fr} (hx : x ≠ 0) (h0 : vV T.V x = 0) :
    ∃ u : T.Vˣ, algebraMap T.V T.Fr (u : T.V) = x := by
  have hne : valV T.V x ≠ 0 := valV_ne_zero hx
  have h1 : valV T.V x = 1 := by
    have h2 : WithZero.log (valV T.V x) = 0 := by simpa [vV] using h0
    rw [← WithZero.exp_log hne, h2, WithZero.exp_zero]
  obtain ⟨z, hz⟩ : ∃ z : T.V, algebraMap T.V T.Fr z = x := by
    obtain ⟨z, hz | hz⟩ := ValuationRing.isInteger_or_isInteger T.V x |>.elim
      (fun ⟨z, hz⟩ => (⟨z, Or.inl hz⟩ : ∃ z : T.V, algebraMap T.V T.Fr z = x ∨ algebraMap T.V T.Fr z = x⁻¹))
      (fun ⟨z, hz⟩ => ⟨z, Or.inr hz⟩)
    · exact ⟨z, hz⟩
    · have hz1 : (IsDiscreteValuationRing.maximalIdeal T.V).valuation T.Fr (algebraMap T.V T.Fr z) = 1 := by
        rw [hz, map_inv₀]
        change (valV T.V x)⁻¹ = 1
        rw [h1, inv_one]
      have hzn := (HeightOneSpectrum.valuation_eq_one_iff_notMem _).1 hz1
      have hu : IsUnit z := by
        by_contra hn
        exact hzn ((IsLocalRing.mem_maximalIdeal z).2 hn)
      obtain ⟨u, rfl⟩ := hu
      refine ⟨(u⁻¹ : T.Vˣ), ?_⟩
      rw [map_units_inv, hz, inv_inv]
  have hz1 : (IsDiscreteValuationRing.maximalIdeal T.V).valuation T.Fr (algebraMap T.V T.Fr z) = 1 := by
    rw [hz]; exact h1
  have hzn := (HeightOneSpectrum.valuation_eq_one_iff_notMem _).1 hz1
  have hu : IsUnit z := by
    by_contra hn
    exact hzn ((IsLocalRing.mem_maximalIdeal z).2 hn)
  obtain ⟨u, rfl⟩ := hu
  exact ⟨u, hz⟩

theorem exists_frameShift_ordTies : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → (∀ p : ℕ, p.Prime → l.GoodAt p) → l.A = 1 → ∀ [Fintype (Comp Xo c)] (h : GenFrEx Xo c), ∃ δ : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → Ix Dw → ℤ, OrdTieQ h δ ∧ OrdTieQZ h δ ∧ (∀ (PY : HeightOneSpectrum (𝓞 c.F) → Type) (lies : ∀ la (T' : CDVR) (ι : c.F →+* T'.Fr), IntFr Xo c T' ι → PY la → Prop), LiesTotal Xo c (trivialClassCondition Xo c) PY lies → OrdTieOn h δ (trivialClassCondition Xo c) PY lies ∧ OrdTie h δ (trivialClassCondition Xo c) PY lies) ∧ ∀ d : ReciprocityTheory.ChartRestriction.G.T0.Data c.F (Comp Xo c) (fun Z => Om Z) (WTZ E) (fun Z => AC Z), DivFin d → FrShFin d δ := by
  intro E _ _ _ H Dw l Xo c hpq hgood hA _ h
  obtain ⟨δ, hv, hfin⟩ := GlobalTheory.Reg.exists_frameShift_frShFin E H Dw l Xo c hpq hgood hA h
  have hQZ : OrdTieQZ h δ := by
    intro Z v hd ht
    obtain ⟨T, ψ, y, hψ, hy⟩ := hv Z v hd (Or.inr ht)
    have htriv : trivCls Xo c T _ y := by
      intro a ha
      have ha' : algebraMap c.F (Om Z) a ≠ 0 := (map_ne_zero _).2 ha
      refine exists_unit_of_vV_eq_zero T ((map_ne_zero _).2 ha) ?_
      have := (hψ _ ha').trans (ht a ha)
      exact_mod_cast this
    refine ⟨⟨T, _, y, htriv⟩, fun a n f hf h0 => ?_, fun a n f hf h0 => ?_⟩
    · change _ = nval T.V 1 (evI y f)
      rw [nval_of_ne (fun hz => h0 ((hy a n f hf).1.1 hz)), (hy a n f hf).2 h0]
      simp
    · change nval T.V 1 (evI y f) = ⊤
      rw [(hy a n f hf).1.2 h0, nval_zero]
  refine ⟨δ, fun Z v hd ht => ?_, hQZ, fun PY lies hl => ?_, fun d hD => hfin d hD⟩
  · obtain ⟨q, hq, -⟩ := hQZ Z v hd ht
    exact ⟨q, hq⟩
  · have hOn := ordTieOn_of_valued hl hv
    exact ⟨hOn, hOn.ordTie⟩

theorem ordTies_of_pins : ∀ (D : D7) (Q : Par D), Q.Pins → ∀ j, InR D j → ∀ [Fintype (Comp (Q.Xo j) Q.c)] (h : GenFrEx (Q.Xo j) Q.c), KapFG (Q.Xo j) Q.c ∧ (∃ d, KapTrdeg (Q.Xo j) Q.c d ∧ d + Nat.card (FlagVar (Q.Dw j)) = WeightFamilies.dimY D j) ∧ FnTrdeg (Q.Xo j) Q.c (WeightFamilies.dimY D j) ∧ CompNe (Q.Xo j) Q.c ∧ ∃ δ : ∀ Z : Comp (Q.Xo j) Q.c, AddValuation (Om Z) (WithTop ℤ) → Ix (Q.Dw j) → ℤ, OrdTieQ h δ ∧ OrdTieQZ h δ ∧ OrdTieOn h δ (trivialClassCondition (Q.Xo j) Q.c) (fun _ => Unit) (fun _ _ _ _ _ => True) ∧ OrdTie h δ (trivialClassCondition (Q.Xo j) Q.c) (fun _ => Unit) (fun _ _ _ _ _ => True) ∧ ∀ d : ReciprocityTheory.ChartRestriction.G.T0.Data Q.c.F (Comp (Q.Xo j) Q.c) (fun Z => Om Z) (WTZ D.host.E) (fun Z => AC Z), DivFin d → FrShFin d δ := by
  intro D Q hP j hj _ h
  obtain ⟨hgood, hA, -, -, -, -, hrk⟩ := GlobalTheory.PinNum.numerics_of_pins D Q hP
  obtain ⟨hr, hr1, hdim⟩ := hrk j hj
  have h1 : 1 ≤ (Q.Dw j).p + (Q.Dw j).q := hr ▸ hr1
  obtain ⟨hfg, htr⟩ := GlobalTheory.Reg.kap_fg_trdeg _ _ (Q.Dw j) Q.l (Q.Xo j) Q.c
  obtain ⟨δ, hq, hqz, hon, hfin⟩ := exists_frameShift_ordTies _ _ (Q.Dw j) Q.l (Q.Xo j) Q.c h1 hgood hA h
  have hl : LiesTotal (Q.Xo j) Q.c (trivialClassCondition (Q.Xo j) Q.c) (fun _ => Unit) (fun _ _ _ _ _ => True) := by
    unfold LiesTotal
    intros
    exact ⟨(), trivial⟩
  obtain ⟨ho, ht⟩ := hon _ _ hl
  exact ⟨hfg, ⟨_, htr, hdim⟩, hdim ▸ fnTrdeg_of _ _ _ htr,
    (GlobalTheory.GeomIrr.compNe_and_exists_fnAlgClosed _ _ (Q.Dw j) Q.l (Q.Xo j) Q.c h1).1, δ, hq, hqz, ho, ht, hfin⟩

end GlobalTheory.HeightDefinite.Ties
