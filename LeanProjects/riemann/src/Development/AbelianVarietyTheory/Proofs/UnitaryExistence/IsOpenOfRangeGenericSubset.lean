import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.BetaAtSymm
import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFiniteEtaleLocalSurjectiveOfIsSeparable
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsPrincipalIdealRingOfIsLocalization
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSplitExtIsGtOfTorusExtension
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CoordOfHasWeight
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFiniteTorusExtensionOfModel
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPolAVGenericFibreOfTriple
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PelTrivialisationIsUnitOnAbelianLocus
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPelUniformisationCompleteDvrStatement

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.UnifAfterExt

theorem exists_finite_split {k : Type} [Field k] (G : Over (Sp k)) [GrpObj G] (hG : IsSemiAbelian G) :
    ∃ (k' : Type) (_ : Field k') (_ : Algebra k k'), FiniteDimensional k k' ∧
      ∃ S : SplitExt (Sp k'), S.IsGt ((Over.pullback (spMap (algebraMap k k'))).obj G) := by
  have := hG.smooth
  obtain ⟨k', hk, T⟩ := exists_finite_torusExtension k (AlgebraicClosure k) G
    inferInstance hG.quasiCompact hG.separated (hG.fibres _ _)
  have := hG.comm
  exact ⟨k', inferInstance, inferInstance, hk, exists_splitExt_isGt_of_torusExtension _ _ T⟩

theorem exists_split_baseChange (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [IsAdicComplete (maximalIdeal W) W] [Finite (ResidueField W)] (G : Over (Sp W)) [GrpObj G]
    (hG : IsSemiAbelian G) :
    ∃ (W' : Type) (_ : CommRing W') (_ : IsDomain W') (_ : IsDiscreteValuationRing W')
      (_ : IsAdicComplete (maximalIdeal W') W') (_ : Algebra W W'),
      Module.Finite W W' ∧ Function.Injective (algebraMap W W') ∧ Finite (ResidueField W') ∧
      ∃ S : SplitExt (Sp (ResidueField W')), S.IsGt ((Over.pullback (spMap (residue W'))).obj
        ((Over.pullback (spMap (algebraMap W W'))).obj G)) := by
  have h₀ : IsSemiAbelian ((Over.pullback (spMap (residue W))).obj G) := IsSemiAbelian.pullback _ G hG
  obtain ⟨k', _, _, hk, E, ⟨d⟩⟩ := exists_finite_split _ h₀
  obtain ⟨W', i1, i2, i3, i4, i5, hf, hi, hl, -, e, he⟩ := GlobalTheory.unramExt W k'
  have hfk : Finite k' := Module.finite_of_finite (ResidueField W)
  refine ⟨W', i1, i2, i3, i4, i5, hf, hi, Finite.of_equiv _ e.symm.toEquiv, ?_⟩
  have key : (e.symm.toRingHom.comp (algebraMap (ResidueField W) k')).comp (residue W) =
      (residue W').comp (algebraMap W W') :=
    RingHom.ext fun v => e.symm_apply_eq.2 (he v).symm
  obtain ⟨j, hj, -⟩ := grpPullback_iso
    (((isGrpPullback_pullback _ (spMap e.symm.toRingHom)).comp
      ((isGrpPullback_pullback _ (spMap (algebraMap (ResidueField W) k'))).comp
        (isGrpPullback_pullback G (spMap (residue W))))).congr
      (f' := spMap (residue W') ≫ spMap (algebraMap W W'))
      (by rw [← Category.assoc, ← spMap_comp, ← spMap_comp, ← spMap_comp, key]) rfl)
    ((isGrpPullback_pullback _ (spMap (residue W'))).comp (isGrpPullback_pullback G (spMap (algebraMap W W'))))
  exact ⟨_, isGt_of_iso j (GtBaseChange.isGt_extBC (spMap e.symm.toRingHom) E _ d)⟩

theorem exists_generic_square {V W : Type} [CommRing V] [IsDomain V] [CommRing W] [IsDomain W] (f : V →+* W)
    (hf : Function.Injective f) :
    ∃ g : Sp (FractionRing W) ⟶ Sp (FractionRing V), jK W ≫ spMap f = g ≫ jK V := by
  have hinj : Function.Injective ((algebraMap W (FractionRing W)).comp f) := (IsFractionRing.injective W _).comp hf
  let g : FractionRing V →+* FractionRing W := IsFractionRing.lift hinj
  have hg : ∀ r, g (algebraMap _ _ r) = algebraMap W _ (f r) := fun r => IsFractionRing.lift_algebraMap hinj r
  clear_value g
  have e : spMap g ≫ jK V = jK W ≫ spMap f := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext hg))
  exact ⟨_, e.symm⟩

theorem isOpen_of_range_generic_subset (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (U : Set (Sp V)) (hU : Set.range (jK V) ⊆ U) : IsOpen U := by
  have hgen : ∀ x : Sp V, x ≠ closedPoint V → x ∈ U := fun x hx => by
    have h0 : x.asIdeal = ⊥ := by
      by_contra hne
      exact hx (PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal (x.isPrime.isMaximal hne)))
    refine hU ⟨(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing V)), PrimeSpectrum.ext ?_⟩
    rw [h0]
    exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective V (FractionRing V))
  by_cases hc : (closedPoint V : Sp V) ∈ U
  · have : U = Set.univ := Set.eq_univ_of_forall fun x => by
      by_cases hx : x = closedPoint V
      · exact hx ▸ hc
      · exact hgen x hx
    rw [this]; exact isOpen_univ
  · have : U = {(closedPoint V : Sp V)}ᶜ := Set.ext fun x => ⟨fun hx h => hc (h ▸ hx), hgen x⟩
    rw [this]
    exact (IsLocalRing.isClosed_singleton_closedPoint V).isOpen_compl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem polAt_of_sabMap {S S' X : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {f : S' ⟶ S} (m : SABMap t' t f)
    {K K' : Type} [Field K] [Field K'] {tK : SAB H (Sp K)} {j : Sp K ⟶ S} (mK : SABMap tK t j)
    {u : SAB H X} {x : Sp K ⟶ X} (mx : SABMap tK u x) (hp : IsProper u.G.hom) (ha : RelAmple u.G u.PP.L)
    (hk : KTriv u.G u.PP.L) (j' : Sp K' ⟶ S') (g : Sp K' ⟶ Sp K) (h : j' ≫ f = g ≫ j) : GlobalTheory.LN.PolAt t' j' := by
  obtain ⟨PP', cub, sym, adj, prim, m₂, hm₂⟩ := sabPull Out.CubePf.cubePull j' t'
  obtain ⟨n, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m m₂
  have cancel : ∀ (t₂ : SAB H (Sp K')) (p : Sp K' ⟶ S) (_ : p = g ≫ j) (_ : SABMap t₂ t p),
      Nonempty (SABMap t₂ u (g ≫ x)) := by
    intro t₂ p hp n
    subst hp
    exact ⟨(sabComp pullCubComp E H _ _ _ _ _ _ _ _ mx
      (sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ mK n).choose).choose⟩
  obtain ⟨m₃⟩ := cancel _ _ h n
  have h₂ : LBIso PP'.L (t'.PP.L.pull m₂.φ) := m₂.lin.imp fun _ h => h.1
  rw [hm₂] at h₂
  have h₃ : LBIso PP'.L (u.PP.L.pull m₃.φ) := m₃.lin.imp fun _ h => h.1
  have hL := LB.isLB_pull t'.PP.isLB (pullback.fst t'.G.hom j')
  exact ⟨MorphismProperty.of_isPullback (P := @IsProper) m₃.cart.1 hp,
    amplePt _ _ (g ≫ x) _ _ m₃.φ m₃.cart _ _ u.PP.isLB hL
      (LBIso.trans hL PP'.isLB (LB.isLB_pull u.PP.isLB _) h₂.symm h₃) ha hk⟩

theorem isOpen_and_uniformised (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [hz : CharZero W]
    (hc : IsAdicComplete (maximalIdeal W) W) (t : SAB H (Sp W)) (hp : GlobalTheory.LN.PolAt t (jK W))
    (hS : ∃ S : SplitExt (Sp (ResidueField W)), S.IsGt ((Over.pullback (spMap (residue W))).obj t.G)) :
    IsOpen (abLocus t.G) ∧ UniformisationConclusion t (abLocus t.G) := by
  obtain ⟨L₁, L₂, L₃, L₄, L₅⟩ := GlobalTheory.firstFiveLaws
  have hW : GlobalTheory.LN.CDvr W := ⟨inferInstance, hc, hz⟩
  have hadm : GlobalTheory.LN.admitted W (maximalIdeal W) := by
    refine ⟨⟨inferInstance, inferInstance, inferInstance, inferInstance⟩, hc, hz, inferInstance, ?_⟩
    letI := Ideal.Quotient.field (maximalIdeal W)
    infer_instance
  have ho := isOpen_of_range_generic_subset W _ (abLocusOne _ _ t.semi _ _ hp.1)
  obtain ⟨A, -, gen, hg, hw, -⟩ := GlobalTheory.LN.exists_polAV_of_polAt L₁ L₂ E H W t hp
  obtain ⟨P, -, -, hP⟩ := GlobalTheory.T.exists_pel_uniformisation_complete_dvr E H W hW t A gen hg hw hS
  exact ⟨ho, P, GlobalTheory.psiUnitOn_abLocus_pel L₁ L₂ L₃ L₄ L₅ E H W _ hadm t P hP ho, hP⟩

theorem exists_finite_ext_uniformised : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (T : Formalism.L2.Pj.CDVR) (t : SAB H (Sp T.V)) (tK : SAB H (Sp T.Fr)) (_ : SABMap tK t (jK T.V)) (x : Sp T.Fr ⟶ Xo.X) (_ : SABMap tK Xo.univ.t x), T.FinRes → ∃ (T' : Formalism.L2.Pj.CDVR) (φ : T.V →+* T'.V) (t' : SAB H (Sp T'.V)) (_ : SABMap t' t (spMap φ)), Function.Injective φ ∧ φ.Finite ∧ T'.FinRes ∧ IsOpen (abLocus t'.G) ∧ UniformisationConclusion t' (abLocus t'.G) := by
  intro E _ _ _ H Dw l Xo T t tK mK x mx hT
  have : Finite (ResidueField T.V) := hT
  obtain ⟨W, _, _, _, hc, _, hf, hi, hr, hS⟩ := exists_split_baseChange T.V t.G t.semi
  have hz : CharZero W := charZero_of_injective_ringHom hi
  obtain ⟨t', m, hS'⟩ : ∃ (t' : SAB H (Sp W)) (_ : SABMap t' t (spMap (algebraMap T.V W))),
      ∃ S : SplitExt (Sp (ResidueField W)), S.IsGt ((Over.pullback (spMap (residue W))).obj t'.G) := by
    obtain ⟨PP', cub, sym, adj, prim, m, -⟩ := sabPull Out.CubePf.cubePull (spMap (algebraMap T.V W)) t
    exact ⟨_, m, hS⟩
  obtain ⟨gam, hsq⟩ := exists_generic_square (algebraMap T.V W) hi
  have hp := polAt_of_sabMap m mK mx Xo.univ.proper Xo.univ.ample Xo.univ.ktriv (jK W) gam hsq
  obtain ⟨ho, hN⟩ := isOpen_and_uniformised W hc t' hp hS'
  exact ⟨{ V := W }, algebraMap T.V W, t', m, hi, RingHom.finite_algebraMap.2 hf, hr, ho, hN⟩

end GlobalTheory.UnifAfterExt
