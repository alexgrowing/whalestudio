import Mathlib
import Development.AbelianVarietyTheory.Definitions.RegularCharts.Reframe
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.EigenBasisIffTangentBasis
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LieBasisIffTangentBasisPullbackUniversal
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsTangentVectorBasisAtPointBaseChange
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueScaledBaseChangeFibreSection
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFibreSectionNowhereZeroOfPullbackTriple
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FibreSectionGeneratesOfNowhereZeroNoetherianBase
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsChartEigenframe
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsRegularRingOfSmooth
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FinrankOfIsSecBasis
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsOfH0EqOneClosedFields
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsBasisOfFormEq
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsRegularOfSupportDimQuotientAddLengthLe

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.Frames

namespace GlobalTheory.LocalFrame

theorem secBaseChange_of_secTwist (hT : Out.SecTwistSt) : Out.SecBaseChangeSt := by
  refine (GlobalTheory.AbLaw.AllLaws.laws_of_h0_eq_one fun K _ _ P => ?_).1.secBaseChange
  obtain ⟨b, hb⟩ := GlobalTheory.PowBasis.exists_basis_pow hT P 1 le_rfl K (𝟙 _)
  have : Nontrivial Γ((Over.mk (𝟙 (Spec (CommRingCat.of K)))).left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toEquiv.nontrivial
  exact (GlobalTheory.SecTwist.finrank_of_isSecBasis P.A P.L _ _ b hb).trans (one_pow _)

theorem exists_away_isDomain {R : Type} [CommRing R] [IsNoetherianRing R] (q : Ideal R) [q.IsPrime]
    [IsDomain (Localization.AtPrime q)] : ∃ g ∉ q, IsDomain (Localization.Away g) := by
  classical
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian (RingHom.ker (algebraMap R (Localization.AtPrime q))))
  have h1 : ∀ a : s, ∃ m : q.primeCompl, (m : R) * a = 0 := fun a =>
    (IsLocalization.map_eq_zero_iff q.primeCompl (Localization.AtPrime q) (a : R)).1
      (by rw [← RingHom.mem_ker, ← hs]; exact Submodule.subset_span a.2)
  choose m hm using h1
  let g : q.primeCompl := ∏ a, m a
  have hg : ∀ a ∈ RingHom.ker (algebraMap R (Localization.AtPrime q)), (g : R) * a = 0 := by
    intro a ha
    rw [← hs] at ha
    induction ha using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨r, hr⟩ : (m ⟨a, ha⟩ : R) ∣ (g : R) := by
        simp only [g, Submonoid.coe_finset_prod]
        exact Finset.dvd_prod_of_mem (fun a => (m a : R)) (Finset.mem_univ _)
      rw [hr, mul_right_comm, hm ⟨a, ha⟩, zero_mul]
    | zero => exact mul_zero _
    | add a b _ _ ha hb => rw [mul_add, ha, hb, add_zero]
    | smul r a _ ha => rw [smul_eq_mul, mul_left_comm, ha, mul_zero]
  refine ⟨g, g.2, ?_⟩
  have hu : IsUnit (algebraMap R (Localization.AtPrime q) g) := IsLocalization.map_units _ g
  let f : Localization.Away (g : R) →+* Localization.AtPrime q := IsLocalization.Away.lift (g : R) hu
  refine Function.Injective.isDomain f ((injective_iff_map_eq_zero f).2 fun x hx => ?_)
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj (g : R) x
  have h2 : algebraMap R (Localization.AtPrime q) a = 0 := by
    rw [← IsLocalization.Away.lift_eq (S := Localization.Away (g : R)) (g : R) hu a, ← ha, map_mul]
    exact (congrArg (· * _) hx).trans (zero_mul _)
  have hu' : IsUnit (algebraMap R (Localization.Away (g : R)) g) := IsLocalization.Away.algebraMap_isUnit _
  have h3 : algebraMap R (Localization.Away (g : R)) a = 0 := by
    rw [← hu'.mul_right_eq_zero, ← map_mul, hg a h2, map_zero]
  rw [h3] at ha
  exact (hu'.pow n).mul_left_eq_zero.1 ha

theorem isTypeFn_fst {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (Dw : Datum H) {g : ℕ}
    (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) : IsTypeFn H Dw.p Dw.q (fun j => (e j).1) := by
  intro τ
  have hcard : Nat.card {i // (e i).1 = τ} = Dw.mult τ := by
    have e2 : {i // (e i).1 = τ} ≃ {s : Σ τ : E →+* ℂ, Fin (Dw.mult τ) // s.1 = τ} :=
      e.subtypeEquiv (fun _ => Iff.rfl)
    have e3 : {s : Σ τ : E →+* ℂ, Fin (Dw.mult τ) // s.1 = τ} ≃ Fin (Dw.mult τ) := Equiv.sigmaSubtype τ
    rw [Nat.card_congr (e2.trans e3), Nat.card_eq_fintype_card, Fintype.card_fin]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · refine hcard.trans ?_
    unfold Datum.mult
    rw [if_pos h]
  · refine hcard.trans ?_
    unfold Datum.mult
    rw [if_neg h]

theorem spMap_spMap {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R' →+* R'')
    (g : R →+* R') : spMap f ≫ spMap g = spMap (f.comp g) := by
  unfold spMap
  rw [← Spec.map_comp]
  rfl

theorem dualMap_comp_epsMul {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) (a : S) :
    (dualMap ψ).comp (epsMul a) = (epsMul (ψ a)).comp (dualMap ψ) := by
  ext s <;> simp [dualMap, epsMul, TrivSqZeroExt.algebraMap_eq_inl]

theorem isEigAt_pull {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T]
    (ψ : S →+* T) (hψ : ∀ a, ψ (algebraMap c.F S a) = algebraMap c.F T a) (τ : E →+* ℂ)
    {v : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (hv : IsEigAt c τ v) :
    IsEigAt c τ (spMap (dualMap ψ) ≫ v) := by
  intro a
  rw [Category.assoc, hv a, ← Category.assoc, spMap_spMap, dualMap_comp_epsMul, ← spMap_spMap,
    Category.assoc, hψ]

theorem smooth_of_chart {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {R : Type} [CommRing R] [Algebra c.F R] (j : Sp R ⟶ Xo.XF c)
    [IsOpenImmersion j] (hs : j ≫ pullback.snd _ _ = spMap (algebraMap c.F R)) : Algebra.Smooth c.F R := by
  have := Xo.smooth
  have : Smooth Xo.s := SmoothOfRelativeDimension.smooth Dw.dim Xo.s
  have h : Smooth (spMap (algebraMap c.F R)) := by rw [← hs]; infer_instance
  have h' := (HasRingHomProperty.Spec_iff (P := @Smooth)).1 h
  exact RingHom.smooth_algebraMap.1 h'

theorem exists_integral_chart_frame : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ p : Xo.XF c, ∃ (A : Type) (_ : CommRing A) (_ : IsDomain A) (_ : Algebra c.F A) (j : Sp A ⟶ Xo.XF c) (y : FrPt Xo c A), IsOpenImmersion j ∧ p ∈ Set.range j ∧ j ≫ pullback.snd _ _ = spMap (algebraMap c.F A) ∧ Algebra.Smooth c.F A ∧ y.x = j ≫ pullback.fst _ _ := by
  intro hT E _ _ _ H Dw l Xo c z
  classical
  have hS := secBaseChange_of_secTwist hT
  let e := (Fintype.equivFin (Σ τ : E →+* ℂ, Fin (Dw.mult τ))).symm
  obtain ⟨R, _, _, jR, o, v, th, hft, hred, hjR, ⟨q, hq⟩, hs, ⟨m⟩, hv, hev, hth, -⟩ :=
    GlobalTheory.ModuliChart.exists_chart_eigenframe hS E H Dw l Xo c _ _ (isTypeFn_fst Dw e) z
  let x : Sp R ⟶ Xo.X := jR ≫ pullback.fst _ _
  have hb : TanBasis x (fun i => (v i).left ≫ m.cm.F) :=
    ((GlobalTheory.Frames.lieBasis_iff_tanBasis E H Dw l Xo R x o.t.G m.cm.F m.cart).2 _ v).1 hv
  let u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber R) ⟶ Xo.univ.t.G.left) :=
    fun τ i => (v (e.symm ⟨τ, i⟩)).left ≫ m.cm.F
  have heig : ∀ τ i, IsEigAt c τ (u τ i) := by
    intro τ i a
    have h := hev (e.symm ⟨τ, i⟩) a
    simp only [Equiv.apply_symm_apply] at h
    have h' : (v (e.symm ⟨τ, i⟩)).left ≫ (o.t.act.act a).left =
      spMap (epsMul (algebraMap c.F R (embK c τ a))) ≫ (v (e.symm ⟨τ, i⟩)).left := h
    show ((v (e.symm ⟨τ, i⟩)).left ≫ m.cm.F) ≫ _ = _ ≫ (v (e.symm ⟨τ, i⟩)).left ≫ m.cm.F
    rw [Category.assoc, ← m.act a, ← Category.assoc, h', Category.assoc]
  obtain ⟨s, hsn⟩ := GlobalTheory.SecTransport.exists_sec_nonzero E H Dw l Xo R x o.t m.toSABMap th hth
  have hsm : Algebra.Smooth c.F R := smooth_of_chart jR hs
  have hreg : IsRegularRing R := GlobalTheory.isRegularRing_of_smooth c.F R
  have hq' : q.asIdeal.IsPrime := q.isPrime
  have hdom : IsDomain (Localization.AtPrime q.asIdeal) := GlobalTheory.isDomain_of_isRegularLocalRing _
  obtain ⟨g, hg, hA⟩ := exists_away_isDomain q.asIdeal
  let A := Localization.Away g
  let ψ : R →+* A := algebraMap R A
  have hψ : ∀ a, ψ (algebraMap c.F R a) = algebraMap c.F A a := fun a =>
    (IsScalarTower.algebraMap_apply c.F R A a).symm
  have hopen : IsOpenImmersion (spMap ψ) := inferInstanceAs
    (IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away g)))))
  have hsA : (spMap ψ ≫ jR) ≫ pullback.snd _ _ = spMap (algebraMap c.F A) := by
    rw [Category.assoc, hs, spMap_spMap]
  let x' : Sp A ⟶ Xo.X := spMap ψ ≫ x
  let u' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber A) ⟶ Xo.univ.t.G.left) :=
    fun τ i => spMap (dualMap ψ) ≫ u τ i
  have hbA := GlobalTheory.Frames.tanBasis_baseChange E H Dw l Xo R A ψ x _ _ hb
  have htan : ∀ τ i, IsTanAt x' (u' τ i) := fun τ i => hbA.1 _
  have heig' : ∀ τ i, IsEigAt c τ (u' τ i) := fun τ i => isEigAt_pull ψ hψ τ (heig τ i)
  have hb' : TanBasis x' (fun j => u' (e j).1 (e j).2) := by
    have : (fun j => u' (e j).1 (e j).2) = fun i => spMap (dualMap ψ) ≫ (v i).left ≫ m.cm.F := by
      funext j
      show _ ≫ (v (e.symm (e j))).left ≫ m.cm.F = _
      rw [Equiv.symm_apply_apply]
    rw [this]; exact hbA
  have hbasis := (GlobalTheory.Frames.eigBasis_iff_tanBasis E H Dw l Xo c A x' u' _ e htan heig').2 hb'
  obtain ⟨s', hs', -⟩ := GlobalTheory.Frames.SecPull.existsUnique_secBC E H Dw l Xo R A ψ 1 x x' rfl s
  have hgen := GlobalTheory.FrameGenerator.secGen_of_secNZ_baseChange hS E H Dw l Xo R x s hsn A ψ x' s' rfl hs'
  have hx : x' ≫ Xo.s = sOf c A := by
    have h1 : x' ≫ Xo.s =
        ((spMap ψ ≫ jR) ≫ pullback.snd _ _) ≫ spMap (IntermediateField.inclusion c.le).toRingHom := by
      simp only [x', x, Category.assoc]
      rw [pullback.condition]
    rw [h1, hsA, sOf, spMap_spMap]
  refine ⟨A, inferInstance, hA, inferInstance, spMap ψ ≫ jR, ⟨x', hx, u', htan, heig', hbasis, s', hgen⟩,
    inferInstance, ?_, hsA, smooth_of_chart _ hsA, (Category.assoc _ _ _).symm⟩
  have hr : q ∈ Set.range (PrimeSpectrum.comap ψ) := by
    rw [PrimeSpectrum.localization_away_comap_range A g]
    exact hg
  obtain ⟨q', hq''⟩ := hr
  refine ⟨q', ?_⟩
  exact (Scheme.Hom.comp_apply _ _ _).trans ((congrArg jR hq'').trans hq)

end GlobalTheory.LocalFrame
