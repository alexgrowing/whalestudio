import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DvrArcExtensionOfMonoStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleBaseOfCompleteNormalLocalCharZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolynomialSupportHolds
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ArcDataPsiValuationEqHalfForm
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordOfIsPullDegId
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelMapFiniteEtaleSurjective
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.ValuationFormPsiBalancedSymmetricPeriodForm
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPsiCoordOfIsPsiCoord
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordExistsUniqueUpToUnitLocal
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LinearUniformisationTorsionIsomorphism
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabDescentOfFieldExtension
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef
open scoped CategoryTheory.Obj BigOperators
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ArcExtForm

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

open GlobalTheory.UT GlobalTheory.Ex GlobalTheory.OneBasis ReciprocityTheory.ChartRestriction.G.DVR in

theorem exists_lin_q_eq (Y : Model Xo c β) {O' : Type} [CommRing O'] [IsDomain O'] {b : O →+* O'}
    (a : ArcIn D l β O' b) {W : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (f : O' →+* W) (u : W)
    (χ : Sp W ⟶ Y.X) (hfi : Function.Injective f) (h : Y.HasArcData a (maximalIdeal W) f u χ) :
    ∃ (t : SAB H (Sp W)) (_ : SABMap t Y.t χ) (P : PELUnif (maximalIdeal W) t) (e : a.D₀.X ≃ₗ[𝓞 E] P.D.toPre.X),
      ∀ (ϖ : W) (Q : P.D.toPre.X → ℤ) (w : ℕ), Irreducible ϖ → QForm.IsQ P.D.toPre ϖ Q →
        HasVal ϖ (algebraMap W (FractionRing W) u) w → ∀ y, Q (e y) = w * (a.be y y / 2) := by
  obtain ⟨t, m, P, φ, he, w, e, -, -, -, -, hc, hG⟩ := h
  refine ⟨t, m, P, e, fun ϖ Q n hϖ hQ hu y => ?_⟩
  let F := AlgebraicClosure (FractionRing W)
  let g : W →+* F := (algebraMap (FractionRing W) F).comp (algebraMap W _)
  have hg : Function.Injective g :=
    (algebraMap (FractionRing W) F).injective.comp (IsFractionRing.injective _ _)
  have hgf : Function.Injective (g.comp f) := hg.comp hfi
  let alg : Algebra (FractionRing O') F := (IsFractionRing.lift (K := FractionRing O') hgf).toAlgebra
  have hF : ∀ x, @algebraMap (FractionRing O') F _ _ alg (algebraMap O' _ x) =
      algebraMap (FractionRing W) F (algebraMap W _ (f x)) := fun x =>
    IsFractionRing.lift_algebraMap hgf x
  have z : Sp F := (default : PrimeSpectrum F)
  obtain ⟨j, hj⟩ := exists_chart P.D.toPre.P.isLB ((P.D.toPre.c (e y)).left (cpt W))
  obtain ⟨v, hv⟩ := GlobalTheory.ArcPsiVal.psi_value a f u P.D.toPre φ w y (e y) (hc y) F hF ((hG F _ hF rfl).1 y) z j hj
  obtain ⟨d, hd, hd'⟩ := GlobalTheory.ArcPsiVal.value_of_qVal P.D.toPre ϖ (e y) _ (hQ (e y)) F z j hj
  have e1 := (toStk z).injective (hd'.symm.trans hv)
  rw [← map_zpow₀, ← map_mul] at e1
  have e2 := (algebraMap (FractionRing W) F).injective e1
  obtain ⟨s, hs⟩ := hu
  refine hasVal_unique hϖ hd ⟨s ^ (a.be y y / 2) * v, ?_⟩
  rw [e2, hs, mul_zpow, ← zpow_mul, Units.val_mul, map_mul, _root_.mul_assoc]
  congr 2
  exact (map_zpow (((algebraMap W (FractionRing W)) : W →* FractionRing W).comp (Units.coeHom W)) s _).symm

theorem closed_not_mem_abLocus (Y : Model Xo c β) (T : CDVR) (y : Sp T.V ⟶ Y.X) (t : SAB H (Sp T.V))
    (m : SABMap t Y.t y) (P : PELUnif (maximalIdeal T.V) t) (hn : Nontrivial P.D.toPre.X) :
    y (closedPoint T.V) ∉ abLocus Y.t.G := by
  intro h
  have h' := (abLocus_pullback abLocusOne Y.t.semi m.cart.1 (closedPoint T.V)).1 h
  exact not_subsingleton_iff_nontrivial.2 hn ((closed_mem_abLocus_iff T P).1 h')

theorem exists_base (X : GMod Xo c) (W : Type) [CommRing W] [IsDomain W] (y : Sp W ⟶ X.X)
    (hr : Set.range (jK W ≫ y) ⊆ Set.range X.j) :
    ∃ (b : 𝓞 c.F →+* W) (io : c.F →+* FractionRing W) (z : Sp (FractionRing W) ⟶ Xo.XF c),
      (algebraMap W (FractionRing W)).comp b = io.comp (algebraMap (𝓞 c.F) c.F) ∧ y ≫ X.s = spMap b ∧
      z ≫ pullback.snd _ _ = spMap io ∧ z ≫ X.j = spMap (algebraMap W (FractionRing W)) ≫ y := by
  haveI := c.fin
  haveI : NumberField c.F := {}
  have hβ : IsDedFrac (algebraMap (𝓞 c.F) c.F) := ⟨⟨inferInstance, inferInstance⟩, inferInstance,
    (inferInstance : IsFractionRing (𝓞 c.F) c.F)⟩
  obtain ⟨-, -, -, h₂, h₃, -, -⟩ := GlobalTheory.ModelRelCompare.densePart X hβ
  obtain ⟨z, hz⟩ := GlobalTheory.HomExt.exists_lift_of_range_subset X.j (jK W ≫ y) hr
  let b : 𝓞 c.F →+* W := (Spec.preimage (y ≫ X.s)).hom
  let io : c.F →+* FractionRing W := (Spec.preimage (z ≫ pullback.snd _ _)).hom
  have hb : spMap b = y ≫ X.s := by
    show Spec.map (CommRingCat.ofHom (Spec.preimage (y ≫ X.s)).hom) = _
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  have hio : spMap io = z ≫ pullback.snd _ _ := by
    show Spec.map (CommRingCat.ofHom (Spec.preimage (z ≫ pullback.snd _ _)).hom) = _
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  have hjs : X.j ≫ X.s = pullback.snd _ _ ≫ spMap (algebraMap (𝓞 c.F) c.F) := by
    show (X.jQ ≫ pullback.fst _ _) ≫ X.s = _
    rw [Category.assoc, pullback.condition, ← Category.assoc, X.jQ_over]
  refine ⟨b, io, z, ?_, hb.symm, hio.symm, hz⟩
  have key : Spec.map (CommRingCat.ofHom b ≫ CommRingCat.ofHom (algebraMap W (FractionRing W))) =
      Spec.map (CommRingCat.ofHom (algebraMap (𝓞 c.F) c.F) ≫ CommRingCat.ofHom io) := by
    rw [Spec.map_comp, Spec.map_comp]
    change spMap (algebraMap W (FractionRing W)) ≫ spMap b = spMap io ≫ spMap (algebraMap (𝓞 c.F) c.F)
    rw [hb, hio, Category.assoc]
    change jK W ≫ y ≫ X.s = _
    rw [← Category.assoc, ← hz, Category.assoc, hjs]
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective key)

theorem eq_of_diag {X Y : Type} [AddCommGroup X] [AddCommGroup Y] (A : LinearMap.BilinForm ℤ X)
    (B : LinearMap.BilinForm ℤ Y) (e : X →+ Y) (k : ℤ) (hA : ∀ u v, A u v = A v u) (hB : ∀ u v, B u v = B v u)
    (h : ∀ u, A u u = k * B (e u) (e u)) (u v : X) : A u v = k * B (e u) (e v) := by
  have h1 := h (u + v)
  simp only [map_add, LinearMap.add_apply] at h1
  have h2 : 2 * A u v = 2 * (k * B (e u) (e v)) := by
    linear_combination h1 - h u - h v - hA v u + k * hB (e v) (e u)
  exact mul_left_cancel₀ two_ne_zero h2

end GlobalTheory.ArcExtForm

namespace GlobalTheory.ArcExtForm

open ReciprocityTheory.ChartRestriction.G.DVR in

theorem exists_arcData_mul_ram : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (X : GMod Xo c) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ ϖ : W, Irreducible ϖ → ∀ (y : Sp W ⟶ X.X) (t : SAB H (Sp W)) (_ : SABMap t X.t y) (P : PELUnif (maximalIdeal W) t), Set.range (jK W ≫ y) ⊆ Set.range X.j → ∀ be ∈ levelForms H 1 P.D.toPre.X, IsMonomial P.D.toPre ![ϖ] ![be] → Nontrivial P.D.toPre.X → ∃ (T' : CDVR) (g : W →+* T'.V) (ϖ' : T'.V) (k : ℕ) (b' : 𝓞 c.F →+* T'.V) (a : ArcIn D l (algebraMap (𝓞 c.F) c.F) T'.V b') (e' : a.D₀.X ≃ₗ[𝓞 E] P.D.toPre.X), Function.Injective g ∧ IsLocalHom g ∧ Irreducible ϖ' ∧ 0 < k ∧ Associated (g ϖ) (ϖ' ^ k) ∧ (spMap g ≫ y) ≫ X.s = spMap b' ∧ Set.range (jK T'.V ≫ spMap g ≫ y) ⊆ Set.range X.j ∧ X.HasArcData a (Ideal.span {ϖ'}) (RingHom.id T'.V) ϖ' (spMap g ≫ y) ∧ ∀ u v, a.be u v = (k : ℤ) * be (e' u) (e' v) := by
  intro E _ _ _ H D l Xo c X W _ _ _ hW ϖ hϖ y t m P hr be hbe hmon hnt
  obtain ⟨h1, h2, h3⟩ := hW
  let T : CDVR := { V := W }
  have hCN : IsCN W := ⟨inferInstance, inferInstance, h2, h3⟩
  have hTor : P.TorsionIso :=
    GlobalTheory.FlatTors.torsionIso_holds E H W (maximalIdeal W) (admissibleBase_of_completeNormalLocalCharZero hCN) t P
  obtain ⟨b₀, io, z, k1, k2, k3, k5⟩ := exists_base X W y hr
  have hc : y (closedPoint W) ∉ abLocus X.t.G := closed_not_mem_abLocus X T y t m P hnt
  haveI := c.fin
  haveI : NumberField c.F := {}
  have hmono : Mono (spMap (algebraMap (𝓞 c.F) c.F)) := by
    have : Epi (CommRingCat.ofHom (algebraMap (𝓞 c.F) c.F)) := IsLocalization.epi (nonZeroDivisors (𝓞 c.F)) c.F
    exact Scheme.Spec.map_mono (CommRingCat.ofHom _).op
  obtain ⟨T', g, ϖ', a, hi, hl, hϖ', hA⟩ :=
    GlobalTheory.T.dvr_arc_extension_of_mono E H D l Xo c _ _ X hmono T io b₀ y z k1 k2 k3 k5 t m P hTor hc

  have hg0 : g ϖ ≠ 0 := (map_ne_zero_iff g hi).2 hϖ.ne_zero
  obtain ⟨k, hk⟩ := IsDiscreteValuationRing.associated_pow_irreducible hg0 hϖ'
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · subst h0
      rw [pow_zero] at hk
      exact absurd (isUnit_of_map_unit g ϖ (associated_one_iff_isUnit.1 hk)) hϖ.not_isUnit
    · exact h0

  have hs : (spMap g ≫ y) ≫ X.s = spMap (g.comp b₀) := by
    rw [Category.assoc, k2]; exact (spMap_comp b₀ g).symm
  let gW : W →+* T'.Fr := (algebraMap T'.V T'.Fr).comp g
  have hj : Function.Injective gW := (IsFractionRing.injective T'.V T'.Fr).comp hi
  obtain ⟨f, hf⟩ : ∃ f : FractionRing W →+* T'.Fr, f.comp (algebraMap W (FractionRing W)) = gW :=
    ⟨IsFractionRing.lift (A := W) (K := FractionRing W) hj, RingHom.ext (IsFractionRing.lift_algebraMap (A := W) (K := FractionRing W) hj)⟩
  have hrange : Set.range (jK T'.V ≫ spMap g ≫ y) ⊆ Set.range X.j := by
    have e : jK T'.V ≫ spMap g ≫ y = spMap f ≫ jK W ≫ y := by
      show spMap (algebraMap T'.V T'.Fr) ≫ spMap g ≫ y = spMap f ≫ spMap (algebraMap W (FractionRing W)) ≫ y
      rw [← Category.assoc, ← Category.assoc, ← spMap_comp, ← spMap_comp, hf]
    rw [e]
    rintro _ ⟨p, rfl⟩
    exact hr ⟨spMap f p, (Scheme.Hom.comp_apply _ _ _).symm⟩

  have hmax : maximalIdeal T'.V = Ideal.span {ϖ'} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ').1 hϖ'
  have hA' := hA
  rw [← hmax] at hA'
  obtain ⟨t', m', P', e, hq⟩ := exists_lin_q_eq X a (RingHom.id _) ϖ' _ Function.injective_id hA'
  obtain ⟨Q', -, hQ', -⟩ := GlobalTheory.ValForm.main E H T'.V t' P' ϖ' hϖ' _ (fun _ => rfl)
  have hq' : ∀ y, Q' (e y) = a.be y y / 2 := fun y => by
    have := hq ϖ' Q' 1 hϖ' hQ' ⟨1, by simp⟩ y
    simpa using this

  have hCN' : IsCN T'.V := ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩
  obtain ⟨t'', m'', P'', e'', -, hpc⟩ := pullSt E H W T'.V g t P hCN hCN' hi hl hTor
  obtain ⟨n₁, -⟩ := GlobalTheory.LevelCover.sab_comp m'' m (e := spMap g ≫ y) rfl
  obtain ⟨m₃, -⟩ := GlobalTheory.LevelCover.sab_cancel m' n₁ (𝟙 _) (Category.id_comp _)
  obtain ⟨e₃, he₃⟩ := GlobalTheory.SameCoord.exists_equiv_psiCoord E H T'.V t' t'' m₃ P' P'' hCN'.1 hCN'.2.1 hCN'.2.2.1
  let e' : a.D₀.X ≃ₗ[𝓞 E] P.D.toPre.X := e.trans (e₃.trans e'')
  have hdiag : ∀ y, a.be y y = (k : ℤ) * be (e' y) (e' y) := by
    intro y
    obtain ⟨u, n, hn, hpsi⟩ := hmon (e' y)
    simp only [Fin.prod_univ_one, Matrix.cons_val_zero] at hn hpsi
    obtain ⟨u₂, hu₂⟩ := hpc (e₃ (e y)) _ hpsi
    obtain ⟨r', hr'⟩ := (GlobalTheory.PeriodFormCompare.exists_psiCoord_iff P'.D.toPre (e y)).2
      (GlobalTheory.PeriodFormCompare.psiIn_top P'.D (e y))
    have hv' := GlobalTheory.ValForm.hasVal_coord (hQ' (e y)) hr'
    obtain ⟨u₃, hu₃⟩ := he₃ (e y) r' hr'
    obtain ⟨v, hvv⟩ := GlobalTheory.PsiCoordLocal.exists_unit_of_coord hu₃ hu₂

    have hass : Associated r' (ϖ' ^ (k * n 0)) := by
      have a1 : Associated r' (↑u₂ * g (↑u * ϖ ^ n 0)) := by
        rw [hvv, ← mul_assoc]
        exact associated_unit_mul_right _ _ ((v * u₃).isUnit)
      have a2 : Associated (↑u₂ * g (↑u * ϖ ^ n 0)) ((g ϖ) ^ n 0) := by
        rw [map_mul, map_pow, ← mul_assoc]
        exact associated_unit_mul_left _ _ (u₂.isUnit.mul (u.isUnit.map g))
      exact (a1.trans a2).trans (by rw [pow_mul]; exact hk.pow_pow)
    obtain ⟨w, hw⟩ := hass.symm
    have hval : HasVal ϖ' (algebraMap T'.V (FractionRing T'.V) r') ((k * n 0 : ℕ) : ℤ) :=
      ⟨w, by rw [← hw, map_mul, map_pow, zpow_natCast]⟩
    have key := hasVal_unique hϖ' hval hv'
    rw [hq'] at key
    obtain ⟨d, hd⟩ : (2 : ℤ) ∣ a.be y y := (Dvd.intro _ rfl : (2 : ℤ) ∣ 2 * (l.M' : ℤ)).trans (a.be_dvd y y)
    have hn0 := hn 0
    simp only [Matrix.cons_val_zero] at hn0
    rw [hn0, hd]
    rw [hd, Int.mul_ediv_cancel_left _ two_ne_zero] at key
    push_cast at key
    rw [← key]
    ring
  refine ⟨T', g, ϖ', k, g.comp b₀, a, e', hi, hl, hϖ', hkpos, hk, hs, hrange, hA, fun u v => ?_⟩
  exact eq_of_diag a.be be e'.toAddMonoidHom k a.be_symm ((mem_levelForms.1 hbe).1) hdiag u v

end GlobalTheory.ArcExtForm
