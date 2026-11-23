import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThProps
import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.ChartLawPf
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenOfRangeGenericSubset
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SemiAbelianModelDeterminedByGenericFibre
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsIntegralChartIntegralFramedPoint
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramedPointBaseChangeAlgebraMap
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.EvaluationLawsGenericFramesAtlasHold
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcFramedPointIntegralOpenDisc
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstantArcEigenbasisFlatBaseChange
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PolarisationSectionGeneratesOfSpecialFibre
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.IntegralThetaSectionExistsAndBaseChange
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.FiniteExtensionRamificationEmbedding
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecUnitClosedFibre
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSemiAbelianModelPadicPrincipallyPolarised

noncomputable section

namespace GlobalTheory.IntegralExt

section Lie

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Matrix GlobalTheory.BasisUniv

theorem eigenbasis_baseChange {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {V S : Type} [CommRing V] [IsLocalRing V] [IsNoetherianRing V] [CommRing S] (f : V →+* S) (hflat : f.Flat)
    (G : SAB H (Sp V)) (G' : SAB H (Sp S)) (m : SABMap G' G (spMap f)) (ρ : 𝓞 E → V) {n : ℕ}
    (v₀ : Fin n → (epsR V ⟶ G.G)) (h₁ : ∀ k, IsTangent (v₀ k))
    (h₂ : ∀ k x, (v₀ k ≫ G.act.act x).left = spMap (epsScaleR (ρ x)) ≫ (v₀ k).left)
    (h₃ : ∀ w : epsR V ⟶ G.G, IsTangent w → (∀ x, (w ≫ G.act.act x).left = spMap (epsScaleR (ρ x)) ≫ w.left) →
      ∃! cf : Fin n → V, IsLieComb cf v₀ w) :
    ∃ u : Fin n → (epsR S ⟶ G'.G), (∀ k, (u k).left ≫ m.φ = spMap (dualMap f) ≫ (v₀ k).left) ∧
      (∀ k, IsTangent (u k)) ∧
      (∀ k x, (u k ≫ G'.act.act x).left = spMap (epsScaleR (f (ρ x))) ≫ (u k).left) ∧
      ∀ w : epsR S ⟶ G'.G, IsTangent w →
        (∀ x, (w ≫ G'.act.act x).left = spMap (epsScaleR (f (ρ x))) ≫ w.left) →
        ∃! cf : Fin n → S, IsLieComb cf u w := by
  have hsm : Smooth G.G.hom := G.semi.smooth
  have hmon : ∀ x, IsMonHom (G.act.act x) := G.act.hom
  have hmon' : ∀ x, IsMonHom (G'.act.act x) := G'.act.hom
  obtain ⟨g, v, hv⟩ := Chart.exists_isLieBasis G.G hsm
  obtain ⟨d, y, hy⟩ := Chart.univChartLoc G.G
  obtain ⟨d', y', hy'⟩ := exists_chart_of_pullback f m.cart
  choose U hU using fun k => (hv.2 _ (h₁ k)).exists
  choose M hM using fun x i => (hv.2 (v i ≫ G.act.act x)
    ((Chart.isTan_iff _).1 (Chart.isTan_comp ((Chart.isTan_iff _).2 (hv.1 i)) _))).exists
  choose u hu using fun k => exists_lift f m.cart (v₀ k)
  choose v' hv' using fun j => exists_lift f m.cart (v j)
  have hb' : IsLieBasis v' := Chart.isLieBasis_baseChange f m.cart hv hv'
  have hU' : ∀ k, IsLieComb (fun j => f (U k j)) v' (u k) := fun k =>
    Chart.comb_baseChange f m.cart (hU k) hv' (hu k)
  have hMR : ∀ x i, IsLieComb (Matrix.of (M x) i) v (v i ≫ G.act.act x) := hM
  have hM' : ∀ x i, IsLieComb ((Matrix.of (M x)).map f i) v' (v' i ≫ G'.act.act x) := fun x i =>
    Chart.comb_baseChange f m.cart (hM x i) hv' (by
      rw [Over.comp_left, Category.assoc, m.act, ← Category.assoc, hv', Category.assoc, Over.comp_left])
  have hUe : ∀ k x, U k ᵥ* Matrix.of (M x) = ρ x • U k := fun k x =>
    (eig_iff hy hv _ (hMR x) (hU k) _).1 (h₂ k x)
  refine ⟨u, hu, fun k => isTangent_of_comb hy' hb'.1 (hU' k), fun k x => ?_, fun w hw hwe => ?_⟩
  · refine (eig_iff hy' hb' _ (hM' x) (hU' k) _).2 ?_
    funext j
    have := congrArg f (congrFun (hUe k x) j)
    simpa [Matrix.vecMul, dotProduct] using this
  · obtain ⟨z, hz, -⟩ := hb'.2 w hw
    simp only [comb_iff hy' hb' hU' hz]
    let _ := f.toAlgebra
    have : Module.Flat V S := hflat
    refine (GlobalTheory.commonEigenvectors_flat_baseChange V (𝓞 E) g n (fun x => Matrix.of (M x)) ρ).1 V U hUe
      (fun s hs => ?_) S z (fun x => (eig_iff hy' hb' _ (hM' x) hz _).1 (hwe x))
    simp only [Algebra.algebraMap_self, RingHom.id_apply, RingHom.coe_id, Matrix.map_id] at hs ⊢
    have hc : IsLieComb s v (Chart.prodPts s v) := (Chart.isLieComb_iff _ _ _).2 rfl
    have := h₃ _ (isTangent_of_comb hy hv.1 hc) (fun x => (eig_iff hy hv _ (hMR x) hc _).2 (hs x))
    simpa only [comb_iff hy hv hU hc] using this

end Lie

section Int

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open scoped CategoryTheory.Obj
open GlobalTheory.ArcQ GlobalTheory.ArcQ.DiscInt GlobalTheory.Frames GlobalTheory.Reg.ChartInhab GlobalTheory.Reg.LiftUnique

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem exists_eigenvalue (T : CDVR) (io : c.F →+* T.Fr) (τ : E →+* ℂ) (a : 𝓞 E) :
    ∃ z : T.V, algebraMap T.V T.Fr z = io (embK c τ a) := by
  have h : IsIntegral T.V ((io.comp (embK c τ)) a) :=
    (RingOfIntegers.isIntegral a).map_of_comp_eq (algebraMap ℤ T.V) _ (RingHom.ext_int _ _)
  exact IsIntegrallyClosed.isIntegral_iff.1 h

theorem exists_nonzero_of_generator (T : CDVR) (G : SAB H (Sp T.V)) (t : SAB H (Sp T.Fr)) {x : Sp T.Fr ⟶ Xo.X}
    (m1 : SABMap t Xo.univ.t x) (m2 : SABMap t G (spMap (algebraMap T.V T.Fr))) (θ : LB.Sec G.PP.L)
    (hθ : ∀ σ : LB.Sec G.PP.L, ∃! a : T.V, ∀ i,
      σ.f i = resG G.G.left le_top ((G.G.hom).appTop.hom (toΓ T.V a)) * θ.f i) (s : Sp T.V) :
    ∃ g : G.G.left, G.G.hom g = s ∧ g ∈ nonzeroLocus θ := by
  obtain ⟨L₁, L₂, -⟩ := GlobalTheory.firstFiveLaws
  have hprop : IsProper t.G.hom := MorphismProperty.of_isPullback (P := @IsProper) m1.cart.1 Xo.univ.proper
  obtain ⟨ψ, -⟩ := GlobalTheory.semiAbelian_model_determined_by_generic_fibre E H T.V inferInstance G G t hprop m2 m2
  have hp := GlobalTheory.UnifAfterExt.polAt_of_sabMap ψ m2 m1 Xo.univ.proper Xo.univ.ample Xo.univ.ktriv (jK T.V) (𝟙 _)
    ((Category.comp_id _).trans (Category.id_comp _).symm)
  obtain ⟨σ, hσ⟩ := GlobalTheory.ThetaDvr.thetaNZ_of_polAt L₁ L₂ E H T.V G hp
  obtain ⟨g, i, hg, hi⟩ := hσ s
  obtain ⟨a, ha, -⟩ := hθ σ
  rw [ha i, Scheme.basicOpen_mul] at hi
  exact ⟨g, hg, TopologicalSpace.Opens.mem_iSup.2 ⟨i, hi.2⟩⟩

theorem integral_baseChange (T T' : CDVR) (io : c.F →+* T.Fr) (io' : c.F →+* T'.Fr) (f : T.V →+* T'.V)
    (hf : Function.Injective f) :
    letI := io.toAlgebra
    letI := io'.toAlgebra
    ∀ (ψ : T.Fr →ₐ[c.F] T'.Fr), (∀ a, ψ (algebraMap T.V T.Fr a) = algebraMap T'.V T'.Fr (f a)) →
      ∀ (y : FrPt Xo c T.Fr) (y' : FrPt Xo c T'.Fr), FrMap ψ y y' → Integral T io y → Integral T' io' y' := by
  letI := io.toAlgebra
  letI := io'.toAlgebra
  intro ψ hψ y y' hm hy
  obtain ⟨L₁, L₂, -⟩ := GlobalTheory.firstFiveLaws
  obtain ⟨G, t, m1, m2, ⟨ub, h₁, h₂, h₃, h₄⟩, θ, hθ, w1, w2, σ, s1, θ2, a1, a2, a3, a4, a5, a6⟩ := hy
  obtain ⟨hx, hu, pm, hs, hb, ha⟩ := hm
  obtain ⟨G', ⟨m⟩⟩ : ∃ G' : SAB H (Sp T'.V), Nonempty (SABMap G' G (spMap f)) := by
    obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull (spMap f) G
    exact ⟨_, ⟨m⟩⟩
  obtain ⟨t', ⟨n⟩⟩ : ∃ t' : SAB H (Sp T'.Fr), Nonempty (SABMap t' t (spMap ψ.toRingHom)) := by
    obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull (spMap ψ.toRingHom) t
    exact ⟨_, ⟨m⟩⟩
  have hι : ψ.toRingHom.comp (algebraMap T.V T.Fr) = (algebraMap T'.V T'.Fr).comp f := RingHom.ext hψ
  have hio : spMap (algebraMap T'.V T'.Fr) ≫ spMap f = spMap ψ.toRingHom ≫ spMap (algebraMap T.V T.Fr) := by
    rw [← sp_comp, ← sp_comp, hι]
  obtain ⟨w0, r0⟩ := exists_rigIso n
  obtain ⟨m1', e₁, -⟩ := exists_comp_rig m1 n y'.x hx a1 r0
  obtain ⟨m2', e₂, -⟩ := exists_comp_rig m2 n _ hio a2 r0
  have T₀ := (FrUniq.tie_iff m1 m2 θ y.s).1 ⟨w1, w2, σ, s1, θ2, a1, a2, a3, a4, a5, a6⟩
  have T₁ := FrUniq.tie_pull m1 m2 θ y.s n m1' m2' hx hio e₁ e₂ y'.s pm hs hb (fun Z r z j hz => by
    have hle := FramedBaseChange.chart_le pm hs (fun _ => j)
    rw [← ha _ hle, gs_appLE pm _ _ hle r z hz]) T₀
  obtain ⟨w1', w2', σ', s1', θ2', r1, r2, i1, i2, p2, hg⟩ := (FrUniq.tie_iff m1' m2' θ y'.s).2 T₁
  obtain ⟨m', e₃⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ m m2'
  obtain ⟨θ', w', hnz, r', i'⟩ := sec_cancel m m' m2' rfl e₃ θ w2' σ' θ2' r2 i2 p2
  choose ρ hρ using exists_eigenvalue (c := c) T io
  have eig : ∀ (T : CDVR) (io : c.F →+* T.Fr) (G : SAB H (Sp T.V)) (τ : E →+* ℂ) (ρ : 𝓞 E → T.V),
      (∀ x, algebraMap T.V T.Fr (ρ x) = io (embK c τ x)) → ∀ w : epsR T.V ⟶ G.G,
      IsEigV c io G τ w ↔ ∀ x : 𝓞 E, (w ≫ G.act.act x).left = spMap (epsScaleR (ρ x)) ≫ w.left :=
    fun T io G τ ρ hρ w => ⟨fun h x => h x _ (hρ x), fun h x s hs => by
      obtain rfl : s = ρ x := IsFractionRing.injective T.V T.Fr (hs.trans (hρ x).symm)
      exact h x⟩
  have hρ' : ∀ τ x, algebraMap T'.V T'.Fr (f (ρ τ x)) = io' (embK c τ x) := fun τ x => by
    rw [← hψ, hρ]
    exact ψ.commutes _
  choose u k₁ k₂ k₃ k₄ using fun τ => eigenbasis_baseChange f (flat_of_injective f hf) G G' m (ρ τ) (ub τ)
    (fun k => (isTan_iff _).1 (h₁ τ k)) (fun k => (eig T io G τ _ (hρ τ) _).1 (h₂ τ k))
    (fun w hw he => h₃ τ w ((isTan_iff _).2 hw) ((eig T io G τ _ (hρ τ) _).2 he))
  refine ⟨G', t', m1', m', ⟨u, fun τ i => (isTan_iff _).2 (k₂ τ i), fun τ i => (eig T' io' G' τ _ (hρ' τ) _).2 (k₃ τ i),
    fun τ w h1 h2 => k₄ τ w ((isTan_iff _).1 h1) ((eig T' io' G' τ _ (hρ' τ) w).1 h2), fun τ i => ?_⟩, θ',
    GlobalTheory.GenDvr.generates_of_nonzero_on_special_fibre L₁ L₂ E H Dw l Xo c T' G' t' y'.x m1' m' θ'
      (hnz _ (exists_nonzero_of_generator T G t m1 m2 θ hθ _)),
    w1', w', σ', s1', thfPull G'.PP.L m'.φ θ', r1, r', i1, i', fun _ _ => rfl, hg⟩
  obtain ⟨q, q1, q2⟩ := h₄ τ i
  have ub₀ : (ub τ i).left ≫ G.G.hom = spMap (algebraMap T.V (DualNumber T.V)) := Over.w (ub τ i)
  have ub₁ : (u τ i).left ≫ G'.G.hom = spMap (algebraMap T'.V (DualNumber T'.V)) := Over.w (u τ i)
  have hpre : IsPreimmersion (spMap (algebraMap T.V T.Fr)) := IsPreimmersion.of_isLocalization (nonZeroDivisors T.V)
  have qb : q ≫ t.G.hom = spMap (algebraMap T.Fr (DualNumber T.Fr)) := by
    rw [← cancel_mono (spMap (algebraMap T.V T.Fr)), Category.assoc, ← m2.cart.1.w, ← Category.assoc, q2,
      Category.assoc, ub₀, dual_alg]
  have cnd : (spMap (dualMap ψ.toRingHom) ≫ q) ≫ t.G.hom =
      spMap (algebraMap T'.Fr (DualNumber T'.Fr)) ≫ spMap ψ.toRingHom := by
    rw [Category.assoc, qb, dual_alg]
  have p1 := n.cart.1.lift_fst _ _ cnd
  have p2 := n.cart.1.lift_snd _ _ cnd
  refine ⟨n.cart.1.lift _ _ cnd, ?_, ?_⟩
  · rw [e₁, ← Category.assoc, p1, Category.assoc, q1, hu]
  · apply m.cart.1.hom_ext
    · rw [Category.assoc, Category.assoc, k₁, ← e₃, e₂, ← Category.assoc, p1, Category.assoc, q2, ← Category.assoc,
        ← Category.assoc, ← dual_comp, ← dual_comp, hι]
    · rw [Category.assoc, Category.assoc, m'.cart.1.w, ← Category.assoc, p2, ub₁, dual_alg]

theorem exists_unif_of_split (T T' : CDVR) (f : T.V →+* T'.V) (ψ : T.Fr →+* T'.Fr)
    (hψ : ∀ a, ψ (algebraMap T.V T.Fr a) = algebraMap T'.V T'.Fr (f a))
    {G : SAB H (Sp T.V)} {t : SAB H (Sp T.Fr)} {x : Sp T.Fr ⟶ Xo.X} (m1 : SABMap t Xo.univ.t x)
    (m2 : SABMap t G (spMap (algebraMap T.V T.Fr))) {G' : SAB H (Sp T'.V)} {t' : SAB H (Sp T'.Fr)}
    {x' : Sp T'.Fr ⟶ Xo.X} (hx : x' = spMap ψ ≫ x) (m1' : SABMap t' Xo.univ.t x')
    (m2' : SABMap t' G' (spMap (algebraMap T'.V T'.Fr)))
    (hS : ∃ S : SplitExt (Sp (ResidueField T'.V)), S.IsGt ((Over.pullback (spMap (residue T'.V))).obj
      ((Over.pullback (spMap f)).obj G.G))) :
    ∃ P : PELUnif (maximalIdeal T'.V) G', P.TorsionIso := by
  subst hx
  have hι : ψ.comp (algebraMap T.V T.Fr) = (algebraMap T'.V T'.Fr).comp f := RingHom.ext hψ
  have hio : spMap (algebraMap T'.V T'.Fr) ≫ spMap f = spMap ψ ≫ spMap (algebraMap T.V T.Fr) := by
    rw [← sp_comp, ← sp_comp, hι]
  obtain ⟨tP, ⟨mP⟩⟩ : ∃ tP : SAB H (Sp T'.V), Nonempty (SABMap tP G (spMap f)) := by
    obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull (spMap f) G
    exact ⟨_, ⟨m⟩⟩
  obtain ⟨n, -⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ m1 m1'
  obtain ⟨w0, r0⟩ := exists_rigIso n
  obtain ⟨w2, r2⟩ := exists_rigIso m2
  obtain ⟨k, -, -⟩ := exists_comp_rig m2 n _ hio r2 r0
  obtain ⟨mK, -⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ mP k
  have hprop : IsProper t'.G.hom := MorphismProperty.of_isPullback (P := @IsProper) m1'.cart.1 Xo.univ.proper
  obtain ⟨j, -⟩ := GlobalTheory.semiAbelian_model_determined_by_generic_fibre E H T'.V inferInstance G' tP t' hprop m2' mK
  have hp := GlobalTheory.UnifAfterExt.polAt_of_sabMap j mK m1' Xo.univ.proper Xo.univ.ample Xo.univ.ktriv (jK T'.V) (𝟙 _)
    ((Category.comp_id _).trans (Category.id_comp _).symm)
  obtain ⟨S, hS⟩ := hS
  obtain ⟨e, he, -⟩ := grpPullback_iso
    ((isGrpPullback_pullback _ (spMap (residue T'.V))).comp (isGrpPullback_pullback G.G (spMap f)))
    ((isGrpPullback_pullback _ (spMap (residue T'.V))).comp ((j.cart.comp mP.cart).congr (Category.id_comp _) rfl))
  obtain ⟨-, P, -, hP⟩ := GlobalTheory.UnifAfterExt.isOpen_and_uniformised T'.V inferInstance G' hp ⟨S, isGt_of_iso e hS⟩
  exact ⟨P, hP⟩

end Int

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
open IsDedekindDomain

theorem exists_ext_chart_unif : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l),
 letI := H.starRing
 ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (la : HeightOneSpectrum (𝓞 c.F)) (e : ℕ), OverLa la T.V io e → y.IsAlg → ∃ (T' : CDVR) (φ : T.Fr →+* T'.Fr) (y' : IntFr Xo c T' (φ.comp io)) (e' : ℕ), φ.Finite ∧ OverLa la T'.V (φ.comp io) e' ∧ y'.IsAlg ∧ (∀ a : T.V, ∃ b : T'.V, algebraMap T'.V T'.Fr b = φ (algebraMap T.V T.Fr a)) ∧ (letI := io.toAlgebra; letI := (φ.comp io).toAlgebra; FrMap ({ φ with commutes' := fun _ => rfl } : T.Fr →ₐ[c.F] T'.Fr) y.1 y'.1) ∧ (∀ f : Rul Xo c, IsNatural (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f → evI y' f = φ (evI y f) ∧ nval T'.V e' (evI y' f) = nval T.V e (evI y f)) ∧ ∃ C : IntegralChartA3 Xo c T' (φ.comp io) y', FrTrunc C.I.G (𝟙 (Sp T'.V)) (chD C.ch) C.xT C.eT ∧ ∃ P : PELUnif (maximalIdeal T'.V) C.I.G, P.TorsionIso := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro T io y la e ho hy
  have : Finite (ResidueField T.V) := hy
  obtain ⟨hL, -⟩ := GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c
  obtain ⟨G, t, m1, m2, -⟩ := y.2.2
  obtain ⟨W, _, _, _, hc, _, hf, hi, hr, hS⟩ := GlobalTheory.UnifAfterExt.exists_split_baseChange T.V G.G G.semi
  have hz : CharZero W := charZero_of_injective_ringHom hi
  let T' : Formalism.L2.Pj.CDVR := { V := W }
  obtain ⟨φ, r, hr0, hφ, hv, -⟩ := GlobalTheory.EtaVal.finite_extension_ramification_embedding T T' (algebraMap T.V W) hi
    (RingHom.finite_algebraMap.2 hf)
  letI := io.toAlgebra
  letI := (φ.comp io).toAlgebra
  let ψ : T.Fr →ₐ[c.F] T'.Fr := { φ with commutes' := fun _ => rfl }
  obtain ⟨z, hz⟩ := hL.bc _ _ ψ y.1
  let y' : IntFr Xo c T' (φ.comp io) :=
    ⟨z, hL.test _ z, integral_baseChange T T' io (φ.comp io) _ hi ψ hφ y.1 z hz y.2.2⟩
  obtain ⟨C, hC⟩ := (GlobalTheory.IntChartExists.intChart_exists E H Dw l Xo c).2.2 (fun _ => rfl) T' _ y'
  refine ⟨T', φ, y', r * e, ?_, ho.bc φ hr0 hv, hr, fun a => ⟨_, (hφ a).symm⟩, hz, fun f hf => ?_, C, hC,
    exists_unif_of_split T T' _ φ hφ m1 m2 hz.1 C.I.m1 C.I.m2 hS⟩
  · letI := φ.toAlgebra
    exact GlobalTheory.SS.finiteDimensional_of_finite_of_isFractionRing T.V T.Fr W T'.Fr (RingHom.ext fun a => (hφ a).symm)
  · have h : evI y' f = φ (evI y f) := by
      have h1 := y.2.1
      have h2 := y'.2.1
      show evalAt _ _ f z = φ (evalAt _ _ f y.1)
      unfold evalAt
      rw [dif_pos h1, dif_pos h2]
      exact hL.wd f hf _ _ _ _ _ _ _ z h2.choose_spec.choose_spec.choose_spec
        (Formalism.L2.Pj.frMap_trans (Xo := Xo) (c := c) _ _ _ _ ψ _ y.1 z h1.choose_spec.choose_spec.choose_spec hz)
    exact ⟨h, h ▸ nval_bc φ hr0 hv e _⟩

end GlobalTheory.IntegralExt
