import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.GenericFrameIntegralOffFinitelyManyFunctions
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsModelChartGenericPointComponent
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsGlobalModelGoodLevelAllPrimes
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IntegralOfFramedPointOverIntegral
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FramedPointsLiftToLevelCover
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelMapsClosed
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsModuliSchemePolarizedAbelianLevel
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramedPointBaseChangeAlgebraMap
import Formalism.LocalToGlobal.ProjectiveLattices.LocFrLoc
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.Frames GlobalTheory.AllWt

noncomputable section

namespace GlobalTheory.FlatLine.Spread

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

def Spreads {R : Type} [Field R] [Algebra c.F R] (y : FrPt Xo c R) : Prop :=
  ∃ S : Finset R, (∀ s ∈ S, s ≠ 0) ∧ ∀ (T : CDVR) (io : c.F →+* T.Fr), letI := io.toAlgebra
    ∀ ψ : R →ₐ[c.F] T.Fr, (∀ s ∈ S, vV T.V (ψ s) = 0) → ∀ z : FrPt Xo c T.Fr, FrMap ψ y z → Integral T io z

theorem discrete_XF (hq : Dw.q = 0) : DiscreteTopology (Xo.XF c) := by
  have hd : Dw.dim = 0 := by simp [Datum.dim, hq]
  have h0 : SmoothOfRelativeDimension 0 Xo.s := hd ▸ Xo.smooth
  have h1 : Etale Xo.s := (Etale.iff_smoothOfRelativeDimension_zero _).2 h0
  let f := pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)
  have h2 : Etale f := inferInstance
  have h3 : LocallyQuasiFinite f := GlobalTheory.TangentCrit.locallyQuasiFinite_of_formallyUnramified f
  have s₀ : Sp c.F := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum c.F)
  have h4 := f.isDiscrete_preimage_singleton s₀
  have h5 : f ⁻¹' {s₀} = Set.univ :=
    Set.eq_univ_of_forall fun x => Subsingleton.elim (α := PrimeSpectrum c.F) _ _
  rw [h5] at h4
  exact isDiscrete_univ_iff.1 h4

theorem exists_genPt_eq (hq : Dw.q = 0) (ξ : Xo.XF c) : ∃ Z : Comp Xo c, genPt Z = ξ := by
  have := discrete_XF (Xo := Xo) (c := c) hq
  refine ⟨⟨irreducibleComponent ξ, irreducibleComponent_mem_irreducibleComponents ξ⟩, ?_⟩
  set Z : Comp Xo c := ⟨irreducibleComponent ξ, irreducibleComponent_mem_irreducibleComponents ξ⟩
  have h1 : IsGenericPoint (genPt Z) (Z : Set (Xo.XF c)) :=
    (Z.2.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ Z.2))
  exact (h1.specializes mem_irreducibleComponent).eq

theorem spreads_of_model (hq : Dw.q = 0) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) {R : Type} [Field R]
    [Algebra c.F R] (y : FrPt Xo c R) : Spreads y := by
  have hT := GlobalTheory.abelianSchemeLaws_all.2.secTwist
  have hbc : FrBC Xo c := fun S K _ _ _ _ ψ y =>
    GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.abelianSchemeLaws_all.1.secBaseChange E H Dw l Xo c S K ψ y
  obtain ⟨Z, hZ⟩ := exists_genPt_eq hq (ptF y (IsLocalRing.closedPoint R))
  obtain ⟨M, hM⟩ := GlobalTheory.GenericChart.exists_chart_genPt hT E H Dw l Xo c Y Z
  obtain ⟨f, hf, -⟩ := GlobalTheory.ModelPoints.existsUnique_chartHom M.hU R (ptF y ≫ Y.j) (by
    show Y.j (ptF y _) ∈ M.U
    rw [← hZ]; exact hM)
  have hs : ptF y ≫ pullback.snd _ _ = spMap (algebraMap c.F R) := pullback.lift_snd _ _ _
  obtain ⟨Λ⟩ := GlobalTheory.Reg.MChart.nonempty_lift E H Dw l Xo c _ _ Y M R f (ptF y) hs hf.symm
  have ex : ptF y ≫ pullback.fst _ _ = y.x := pullback.lift_fst _ _ _
  rw [ex] at Λ
  exact GenInt.exists_finset_of_lift hT hbc M f y Λ

theorem Spreads.of_x_eq {R : Type} [Field R] [Algebra c.F R] {y₀ y : FrPt Xo c R} (h : Spreads y₀)
    (hx : y.x = y₀.x) : Spreads y := by
  classical
  obtain ⟨S, hS, H₀⟩ := h
  obtain ⟨k, a, hk, hchg⟩ := (GlobalTheory.Frames.frChg_exists_unique E H Dw l Xo c R y₀ y).1 hx
  let S₀ : Finset R := S ∪
    Finset.univ.biUnion (fun τ : E →+* ℂ =>
      Finset.univ.image fun p : Fin (Dw.mult τ) × Fin (Dw.mult τ) => k τ p.1 p.2) ∪
    Finset.univ.image (fun τ : E →+* ℂ => (k τ).det) ∪ {(a : R)}
  refine ⟨S₀.filter (· ≠ 0), fun s hs => (Finset.mem_filter.1 hs).2, fun T io => ?_⟩
  let _ := io.toAlgebra
  intro ψ hψ z hz
  have hin : ∀ s ∈ S₀, ∃ v, algebraMap T.V T.Fr v = ψ s := fun s hs => by
    by_cases h0 : s = 0
    · exact ⟨0, by rw [h0, map_zero, map_zero]⟩
    · exact Formalism.L2.PjFree.mem_range_of_vV_nonneg (hψ s (Finset.mem_filter.2 ⟨hs, h0⟩)).ge
  have hun : ∀ s ∈ S₀, IsUnit s → ∀ v, algebraMap T.V T.Fr v = ψ s → IsUnit v := fun s hs h0 v hv =>
    GenInt.isUnit_of_vV T v (by rw [hv]; exact (h0.map ψ).ne_zero)
      (by rw [hv]; exact hψ s (Finset.mem_filter.2 ⟨hs, h0.ne_zero⟩))
  choose k₀ hk₀ using fun τ j i => hin (k τ j i) (by
    simp only [S₀, Finset.mem_union, Finset.mem_biUnion]
    exact .inl (.inl (.inr ⟨τ, Finset.mem_univ _, Finset.mem_image.2 ⟨(j, i), Finset.mem_univ _, rfl⟩⟩)))
  have ha : (a : R) ∈ S₀ := by simp [S₀]
  obtain ⟨a₀, ha₀⟩ := hin a ha
  obtain ⟨a₁, rfl⟩ := hun a ha a.isUnit a₀ ha₀
  have ek : ∀ τ, (Matrix.of (k₀ τ)).map (algebraMap T.V T.Fr) = (k τ).map ψ :=
    fun τ => Matrix.ext fun j i => hk₀ τ j i
  obtain ⟨z₀, hz₀⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.abelianSchemeLaws_all.1.secBaseChange
    E H Dw l Xo c R T.Fr ψ y₀
  have hi₀ : Integral T io z₀ := H₀ T io ψ (fun s hs => hψ s (Finset.mem_filter.2 ⟨by
    simp only [S₀, Finset.mem_union]; exact .inl (.inl (.inl hs)), hS s hs⟩)) z₀ hz₀
  have hc := (GlobalTheory.Frames.ChgBC.frChg_baseChange E H Dw l Xo c R T.Fr ψ y₀ y z₀ z k a hchg hz₀).1 hz
  refine GenInt.integral_chg T io z₀ z (fun τ => Matrix.of (k₀ τ)) a₁ (fun τ => ?_) ?_ hi₀
  · refine hun (k τ).det ?_ (hk τ) _ ?_
    · simp only [S₀, Finset.mem_union]
      exact .inl (.inr (Finset.mem_image_of_mem _ (Finset.mem_univ τ)))
    · rw [RingHom.map_det, RingHom.mapMatrix_apply, ek]
      exact (ψ.toRingHom.map_det (k τ)).symm
  · rw [funext ek, ha₀]
    exact hc

theorem Spreads.of_frOver {n : ℕ} (d : DeltaDat Xo c n) {R : Type} [Field R] [Algebra c.F R] [Algebra d.c₂.F R]
    (hc : ∀ a : c.F, algebraMap d.c₂.F R (d.eF a) = algebraMap c.F R a) {y : FrPt Xo c R}
    {y₂ : FrPt d.Xo₂ d.c₂ R} (h : Spreads y) (ho : FrOver d y₂ y) : Spreads y₂ := by
  obtain ⟨S, hS, H₀⟩ := h
  refine ⟨S, hS, fun T io₂ => ?_⟩
  letI := io₂.toAlgebra
  intro ψ₂ hψ z₂ hz₂
  let io : c.F →+* T.Fr := io₂.comp d.eF.toRingEquiv.toRingHom
  letI := io.toAlgebra
  let ψ : R →ₐ[c.F] T.Fr :=
    { ψ₂.toRingHom with commutes' := fun a => (congrArg ψ₂ (hc a).symm).trans (ψ₂.commutes _) }
  obtain ⟨z, hz⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.abelianSchemeLaws_all.1.secBaseChange
    E H Dw l Xo c R T.Fr ψ y
  have hi : Integral T io z := H₀ T io ψ hψ z hz
  have ho' : FrOver d z₂ z := GlobalTheory.FrameLift.frOver_map d (ψ := ψ) (ψ₂ := ψ₂) rfl ho hz hz₂
  exact GlobalTheory.PlaceInt.integral_of_frOver E H Dw l Xo c n d T io io₂
    ⟨z, GlobalTheory.Frames.allTest_of_secBaseChange GlobalTheory.abelianSchemeLaws_all.1.secBaseChange E H Dw l Xo c _ z, hi⟩
    (fun _ => rfl) z₂ ho'

theorem exists_coeff_of_dvd {l₁ : Level H} (hl : l₁.Dvd l) (c : Coeff l) : ∃ c₁ : Coeff l₁, c.F = c₁.F := by
  have hM : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  have h' : l₁.M' ∣ l.M' := Nat.lcm_dvd (hl.1.trans (Nat.dvd_lcm_left _ _)) (hl.2.2.trans (Nat.dvd_lcm_right _ _))
  have hp : 0 < l.M' := Nat.lcm_pos hM l.A_pos
  refine ⟨⟨c.F, c.fin, c.conj, ?_, ?_⟩, rfl⟩
  · rw [← Moduli.LevelAction.zeta_pow_div hp h']; exact pow_mem c.zeta_mem _
  · refine le_trans ?_ c.le
    rw [KA, IntermediateField.adjoin_le_iff]
    rintro x (rfl | rfl)
    · exact (baseKA l).ρ.2
    · rw [← Moduli.LevelAction.zeta_pow_div l.A_pos hl.2.2]
      exact pow_mem (baseKA l).ζ.2 _

theorem spreads (hq : Dw.q = 0) (hp : 1 ≤ Dw.p) (hg : ∀ p : ℕ, p.Prime → l.GoodAt p) {R : Type} [Field R]
    [Algebra c.F R] (y : FrPt Xo c R) : Spreads y := by
  have hr : 1 ≤ Dw.p + Dw.q := hp.trans (Nat.le_add_right _ _)
  let l₁ : Level H := { l with A := 1, A_pos := one_pos }
  have hl : l₁.Dvd l := ⟨dvd_rfl, le_rfl, one_dvd _⟩
  obtain ⟨Xo₁⟩ := GlobalTheory.Moduli.moduli_scheme_exists E H Dw l₁ hr
  obtain ⟨c₁, hF⟩ := exists_coeff_of_dvd hl c
  obtain ⟨-, ⟨Y⟩⟩ := GlobalTheory.Reg.modelAt_and_nonempty_global_model E H Dw l₁ Xo₁ c₁ hr hg rfl
  obtain ⟨r, jK, m, hj, hrs, -⟩ := GlobalTheory.levelMaps_closed GlobalTheory.abelianSchemeLaws_all.1 E H Dw hr l₁ l Xo₁ Xo hl
  let d : DeltaDat Xo₁ c₁ 0 :=
    { pd := 1, I := ⊤, l₂ := l, Xo₂ := Xo, c₂ := c, hF := hF, r := r, m := m,
      nab₂ := fun _ _ _ _ => 0, cδ := 0, φδ := 0 }
  letI : Algebra d.c₂.F R := ‹Algebra c.F R›
  letI : Algebra c₁.F R := ((algebraMap c.F R).comp d.eF.toRingEquiv.toRingHom).toAlgebra
  obtain ⟨y₁, hy₁⟩ := exists_frPt_local (Xo := Xo₁) (c := c₁) (L := R) GlobalTheory.abelianSchemeLaws_all.2.secTwist
    (y.x ≫ r) (by
      rw [Category.assoc, hrs, ← Category.assoc, y.x_over, sOf, sOf, Formalism.L2.PjFree.spMap_comp']
      refine congrArg spMap (RingHom.ext fun a => ?_)
      exact congrArg (algebraMap c.F R) (Subtype.ext (hj a)))
  obtain ⟨y₂, hx, ho⟩ := GlobalTheory.FrameLift.exists_frOver d (fun _ => rfl) y₁ y.x hy₁.symm y.x_over
  exact (Spreads.of_frOver d (fun _ => rfl) (spreads_of_model hq Y y₁) ho).of_x_eq hx.symm

end GlobalTheory.FlatLine.Spread

namespace GlobalTheory.FlatLine

open ReciprocityTheory.ChartRestriction.G.FD in

theorem exists_finset_integral_of_definite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), Dw.q = 0 → 1 ≤ Dw.p → (∀ p : ℕ, p.Prime → l.GoodAt p) → ∀ y₀ : FrPt Xo c c.F, ∃ S : Finset c.F, (∀ s ∈ S, s ≠ 0) ∧ ∀ (T : CDVR) (io : c.F →+* T.Fr), letI := io.toAlgebra; (∀ s ∈ S, vV T.V (io s) = 0) → ∀ z : FrPt Xo c T.Fr, FrMap (Algebra.ofId c.F T.Fr) y₀ z → Integral T io z := by
  intro E _ _ _ H Dw l Xo c hq hp hg y₀
  obtain ⟨S, hS, h⟩ := Spread.spreads hq hp hg y₀
  exact ⟨S, hS, fun T io => letI := io.toAlgebra; fun hs z hz => h T io (Algebra.ofId c.F T.Fr) hs z hz⟩

end GlobalTheory.FlatLine
