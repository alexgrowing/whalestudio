import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.PairingSsNu
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.MonomialNorms
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.DualNumberRingHomExt
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.LiePush
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasisBaseChange
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.CmHostUnitAddConjEqOne
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SplitTorusToAbelianVarietyConst
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsSmulPtSmulPt
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsLocalRingDual
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcDatumArcLieBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj Formalism.L2.Pj.QAt Formalism.L2.Pj.abelian₂ Formalism.L2.LamCM Formalism.MainNotions Formalism.BasicNotions
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke

namespace GlobalTheory.CuspFamilyCompare

section Pairing

variable {E : Type} [Field E] [NumberField E] {X : Type} [AddCommGroup X] [Module (𝓞 E) X]

theorem cmHostUnit_add_conj_eq_one [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) : H.w0 + H.bar H.w0 = 1 :=
  ReciprocityTheory.ChartRestriction.G.PullbackSections.CVA.cmHostUnit_add_conj_eq_one H

theorem pairE_add (ξ : Module.Dual ℤ X) (x y : X) :
    SemisimplePairingSeparation.pairE E ξ (x + y) = SemisimplePairingSeparation.pairE E ξ x + SemisimplePairingSeparation.pairE E ξ y := by
  simp only [SemisimplePairingSeparation.pairE, smul_add, map_add, Int.cast_add, mul_add, Finset.sum_add_distrib]

theorem trace_pairE (ξ : Module.Dual ℤ X) (x : X) (b : 𝓞 E) :
    Algebra.trace ℚ E (SemisimplePairingSeparation.pairE E ξ x * b) = ((ξ (b • x) : ℤ) : ℚ) := by
  classical
  have hk : ∀ k, Algebra.trace ℚ E (SemisimplePairingSeparation.pairE E ξ x * integralBasis E k) =
      ((ξ ((RingOfIntegers.basis E k) • x) : ℤ) : ℚ) := fun k => by
    unfold SemisimplePairingSeparation.pairE
    rw [Finset.sum_mul, map_sum, Finset.sum_eq_single k]
    · have h := (Algebra.traceForm ℚ E).apply_dualBasis_left (traceForm_nondegenerate ℚ E) (integralBasis E) k k
      rw [Algebra.traceForm_apply, if_pos rfl] at h
      rw [mul_right_comm, mul_comm, ← zsmul_eq_mul, map_zsmul, h]; simp
    · intro i _ hi
      have h := (Algebra.traceForm ℚ E).apply_dualBasis_left (traceForm_nondegenerate ℚ E) (integralBasis E) i k
      rw [Algebra.traceForm_apply, if_neg (by first | exact hi | exact hi.symm)] at h
      rw [mul_right_comm, mul_comm, ← zsmul_eq_mul, map_zsmul, h]; simp
    · simp
  have hb : b ∈ Submodule.span ℤ (Set.range (RingOfIntegers.basis E)) := by
    rw [(RingOfIntegers.basis E).span_eq]; trivial
  induction hb using Submodule.span_induction with
  | mem _ h => obtain ⟨k, rfl⟩ := h; rw [← hk k, integralBasis_apply]
  | zero => simp
  | add a b _ _ ha hb => rw [add_smul, map_add, Int.cast_add, ← ha, ← hb, ← map_add, ← mul_add]; simp
  | smul n a _ ha =>
    have e : ((n • a : 𝓞 E) : E) = n • (a : E) := map_zsmul (algebraMap (𝓞 E) E) n a
    rw [smul_assoc, map_zsmul ξ, e, mul_smul_comm, map_zsmul, ha]
    simp

theorem pairE_smul (ξ : Module.Dual ℤ X) (a : 𝓞 E) (x : X) :
    SemisimplePairingSeparation.pairE E ξ (a • x) = (a : E) * SemisimplePairingSeparation.pairE E ξ x := by
  have h : Algebra.traceForm ℚ E (SemisimplePairingSeparation.pairE E ξ (a • x) - (a : E) * SemisimplePairingSeparation.pairE E ξ x) = 0 :=
    (integralBasis E).ext fun k => by
      have h1 := trace_pairE ξ (a • x) (RingOfIntegers.basis E k)
      have h2 := trace_pairE ξ x (RingOfIntegers.basis E k * a)
      rw [mul_smul, ← h1] at h2
      rw [Algebra.traceForm_apply, sub_mul, map_sub, integralBasis_apply, LinearMap.zero_apply, sub_eq_zero]
      refine h2.symm.trans (congrArg _ ?_)
      push_cast
      ring
  exact sub_eq_zero.1 ((traceForm_nondegenerate ℚ E).1 _ fun y => by rw [h]; rfl)

end Pairing

theorem isHolTo_ex {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
    {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l} {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
    (F : FamilyUnif Xo σ ty) (i : Fin F.n) {P : (F.Di i).La →+ (Fin g → ℂ)} (hP : IsPeriod (F.Di i) ty P) :
    IsHolTo Set.univ (fun z => (F.ex i P z).left) := by
  have h := (F.hol i 0 Set.univ (fun _ => P) isOpen_univ ⟨fun _ _ => hP, fun _ => differentiableOn_const _⟩).2
  exact HolHom.isHolTo_of_holAt isOpen_univ fun z _ =>
    (HolHom.holAt_of_isHolTo h (z := (0, z)) ⟨trivial, trivial⟩).precomp (k := fun z => (0, z)) (by fun_prop)

theorem exp_unique {S : Scheme.{0}} {G : Over S} [GrpObj G] {y : Sp ℂ ⟶ S} {g : ℕ}
    {e e' : (Fin g → ℂ) → (Over.mk y ⟶ G)} (he : ∀ z w, e (z + w) = e z * e w) (he' : ∀ z w, e' (z + w) = e' z * e' w)
    (hol : IsHolTo Set.univ (fun z => (e z).left)) (hol' : IsHolTo Set.univ (fun z => (e' z).left))
    (u : Fin g → (Sp (DualNumber ℂ) ⟶ G.left)) (hd : ∀ i, IsDerivAt0 (fun z => (e z).left) (Pi.single i 1) (u i))
    (hd' : ∀ i, IsDerivAt0 (fun z => (e' z).left) (Pi.single i 1) (u i)) : e = e' := by
  have h0 : e 0 = e' 0 := (HolHom.map_zero_eq_one he).trans (HolHom.map_zero_eq_one he').symm
  refine HolHom.eq_of_fderiv_eq he he' hol hol' fun U hU f => ContinuousLinearMap.coe_injective ((Pi.basisFun ℂ _).ext fun i => ?_)
  rw [Pi.basisFun_apply]
  exact (((HolHom.isDerivAt0_iff _ _ _).1 (hd i)).2 U hU f).symm.trans
    (((HolHom.isDerivAt0_iff _ _ _).1 (hd' i)).2 U (h0 ▸ hU :) f)

theorem isDerivAt0_comp {X : Scheme.{0}} {g g' : ℕ} {e : (Fin g → ℂ) → (Sp ℂ ⟶ X)} (hol : IsHolTo Set.univ e)
    (ρ : (Fin g' → ℂ) →L[ℂ] (Fin g → ℂ)) {w : Fin g' → ℂ} {u : Sp (DualNumber ℂ) ⟶ X} (h : IsDerivAt0 e (ρ w) u) :
    IsDerivAt0 (fun z => e (ρ z)) w u := by
  rw [HolHom.isDerivAt0_iff] at h ⊢
  refine ⟨h.1.trans (congrArg e (map_zero ρ).symm), fun U hU f => ?_⟩
  have hU' : ⊤ ≤ e 0 ⁻¹ᵁ U := by simpa only [map_zero] using hU
  have h1 : HasFDerivAt (fun t => valAt' (e t) U f) (fderiv ℂ (fun t => valAt' (e t) U f) 0) (ρ 0) := by
    rw [map_zero]; exact ((HolHom.holAt_of_isHolTo hol (Set.mem_univ 0) U hU').2 f).hasFDerivAt
  exact (h.2 U hU' f).trans (congrArg (· w) (h1.comp 0 ρ.hasFDerivAt).fderiv).symm

theorem congr_of_exp {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
    {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l} {σ : KA l →+* ℂ} {g g' : ℕ} {ty : Fin g' → (E →+* ℂ)}
    (F : FamilyUnif Xo σ ty) (i : Fin F.n) {Pm : (F.Di i).La →+ (Fin g' → ℂ)} (hper : IsPeriod (F.Di i) ty Pm)
    (ρ : (Fin g' → ℂ) →L[ℂ] (Fin g → ℂ)) {y : Sp ℂ ⟶ Xo.X} (h : y = F.u i Pm)
    (ex : (Fin g → ℂ) → (Over.mk y ⟶ Xo.univ.t.G)) (u : Fin g' → (Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left))
    (b1 : ∀ z w, ex (z + w) = ex z * ex w) (b2 : IsHolTo Set.univ (fun z => (ex z).left))
    (b3 : ∀ m, IsDerivAt0 (fun z => (ex z).left) (ρ (Pi.single m 1)) (u m))
    (b4 : ∀ m, IsDerivAt0 (fun z => (F.ex i Pm z).left) (Pi.single m 1) (u m))
    (n : ℕ) (hn : n ≠ 0) (s : 𝟙_ _ ⟶ Xo.univ.t.G) (a b : (F.Di i).La)
    (c1 : toUnit _ ≫ s = ex ((n : ℂ)⁻¹ • ρ (Pm a))) (c2 : toUnit _ ≫ s = F.ex i Pm ((n : ℂ)⁻¹ • Pm b)) :
    ∃ w, b = a + n • w := by
  subst h
  have E : (fun z => ex (ρ z)) = F.ex i Pm :=
    exp_unique (fun z w => by rw [map_add, b1]) (F.ex_add _ _ hper)
      (HolHom.isHolTo_of_holAt isOpen_univ fun z _ =>
        (HolHom.holAt_of_isHolTo b2 (Set.mem_univ (ρ z))).precomp ρ.differentiableAt) (isHolTo_ex F _ hper)
      u (fun m => isDerivAt0_comp b2 ρ (b3 m)) b4
  have c3 : F.ex i Pm ((n : ℂ)⁻¹ • Pm a) = F.ex i Pm ((n : ℂ)⁻¹ • Pm b) := by
    rw [← c2, c1, ← map_smul ρ]
    exact (congrFun E _).symm
  have c4 : F.ex i Pm ((n : ℂ)⁻¹ • Pm b - (n : ℂ)⁻¹ • Pm a) = 1 := by
    have := F.ex_add _ _ hper ((n : ℂ)⁻¹ • Pm b - (n : ℂ)⁻¹ • Pm a) ((n : ℂ)⁻¹ • Pm a)
    rw [sub_add_cancel, c3] at this
    exact mul_eq_right.1 this.symm
  obtain ⟨w, hw⟩ := (F.ex_ker _ _ hper _).1 c4
  refine ⟨w, hper.2.1 ?_⟩
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn
  rw [map_add, map_nsmul, hw, ← Nat.cast_smul_eq_nsmul ℂ, smul_sub, smul_smul, smul_smul, mul_inv_cancel₀ hn', one_smul,
    one_smul, add_sub_cancel]

theorem exists_isMarkingAt {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}
    {U : Unf Xo c σ r} (hU : IsUnf U) (k : U.Comp) (x : (U.X k).dom) :
    ∃ (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (t : Dw.La → (U.X k).Λ), SemisimplePairingSeparation.IsMarkingAt U k x e t := by
  obtain ⟨g, e, F, ik, φ, hEF, h⟩ := hU.2.2.2.2.2
  obtain ⟨Pm, h⟩ := h k x
  exact ⟨g, e, _, F, ik k, φ k, Pm, hEF k, h.1, h.2.1, h.2.2.1, h.2.2.2.1, fun _ => rfl⟩

section Tangent

open GlobalTheory.ArcQ GlobalTheory.TorusTangent ReciprocityTheory.ChartRestriction.G.DVR

variable {K : Type} [Field K] {D₀ : Out.DegPre K}

theorem gtTanR_of_torus {ν : Out.GtPt D₀ (epsR K)} {a : D₀.X → K} (h : SemisimplePairingSeparation.IsTorusTan D₀ ν a) : GtTanR ν := by
  obtain ⟨hb, h⟩ := h
  obtain ⟨g₀, h₀, v₀⟩ := TorusTangent.exists_pt (D := D₀) (T := Over.mk (𝟙 (Sp K))) (fun _ => 1)
    fun _ _ => (_root_.mul_one _).symm
  refine ⟨g₀, ⟨h₀, fun x => corr_of_val D₀.P.isLB fun y J hJ => ?_⟩, ?_, fun x => corr_of_val D₀.P.isLB fun y J hJ => ?_⟩
  · rw [v₀ x _ _ y J hJ, map_one, val_one]
  · rw [h₀, hb, zeroT_left, zeroT_left, ← Category.assoc]
    exact congrArg (· ≫ eSec D₀.P.A) fst_inl.symm
  · obtain ⟨c, hc⟩ := exists_hasVal ν hb x
    obtain ⟨I, hI⟩ := exists_good' (D := D₀) (cpt (DualNumber K))
    have m : ⊤ ≤ LB.wchart D₀.P.L (Out.DegPre.gtφT D₀ (epsR K) ν.b x) _ :=
      (top_le_iff_cpt (𝟙 (Sp (DualNumber K))) _).2 (hI.mem (Out.DegPre.gtφT D₀ (epsR K) ν.b x) (𝟙 (Sp (DualNumber K))))
    have e := h x _ (fun a b e => congrArg (fun q => I (𝟙 _ ≫ q)) e) m
    have e' : valR (𝟙 _) ⊤ c.val = TrivSqZeroExt.inl 1 + TrivSqZeroExt.inr (a x) :=
      (toStkA_injective ((toStkA_valR _ _ _ m _).trans
        ((congrArg Units.val (hc _ _ _ I hI)).trans (toStkA_valR _ _ _ le_top _).symm))).symm.trans e
    refine (v₀ x _ _ y J hJ).trans (Units.ext (Eq.trans ?_
      (hasVal_spMap hc (TrivSqZeroExt.fstHom K K K).toRingHom hJ).symm))
    rw [e', map_one]
    simp

theorem gtTanR_of_dsDiv {n : ℕ} {s : ∀ Z : Over (Sp K), (Z ⟶ D₀.P.A) → Out.GtPt D₀ Z} (hs : SemisimplePairingSeparation.IsLiftOver D₀ n s)
    {w : epsR K ⟶ D₀.P.A} (hw : IsTangent w) {ν : Out.GtPt D₀ (epsR K)} (h : SemisimplePairingSeparation.IsDsDiv D₀ n s w ν) : GtTanR ν := by
  let r : K := (n : K)⁻¹
  let sc : epsR K ⟶ epsR K := Over.homMk (spMap (epsScaleR r)) ((Geo.Tor.spMap_comp _ _).symm.trans
    (congrArg spMap (RingHom.ext fun a => by ext <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl])))
  let z : Over.mk (𝟙 (Sp K)) ⟶ epsR K := Over.homMk (spMap (TrivSqZeroExt.fstHom K K K).toRingHom)
    ((Geo.Tor.spMap_comp _ _).symm.trans ((congrArg spMap (RingHom.ext fun _ => rfl)).trans (Spec.map_id (CommRingCat.of K))))
  have hz : z ≫ sc ≫ w = 1 := by
    apply Over.OverMorphism.ext
    have e : spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ spMap (epsScaleR r) =
        spMap (TrivSqZeroExt.fstHom K K K).toRingHom :=
      (Geo.Tor.spMap_comp _ _).symm.trans (congrArg spMap (RingHom.ext fun x => by simp [epsScaleR]))
    show spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ spMap (epsScaleR r) ≫ w.left = _
    rw [← Category.assoc, e, hw]
    exact (Category.id_comp _).symm
  obtain rfl : ν = s _ (sc ≫ w) := TorusModel.isPull_unique (k := sc) h (hs.2.2 _ _ sc w)
  have e := hs.2.2 _ _ z (sc ≫ w)
  rw [hz] at e
  refine ⟨s _ 1, ⟨(hs.1 _ _).trans (one_pow n), fun χ => corr_of_val D₀.P.isLB fun y J hJ => ?_⟩, e⟩
  have a : Out.GtPt.IsAdd (s (Over.mk (𝟙 (Sp K))) 1) (s _ 1) (s _ (1 * 1)) := hs.2.1 _ 1 1
  have e := ((TorusModel.isAdd_iff _ _ _).1 a).2 χ y J hJ
  have C := isCub_cubV D₀.cub hJ
  rw [_root_.mul_one, hs.1, one_pow] at e
  exact (mul_eq_left.1 ((congrArg _ (C.face₃ _ _)).trans (_root_.mul_one _) |>.symm.trans e).symm).trans (val_one _).symm

variable [NumberField K]

theorem isTangent_of_factor {A₀ B : Out.PolAV (Sp (𝓞 K))} {x : KeyIn K} {φx : x.P.A.left ⟶ A₀.A.left}
    {φ₀ : D₀.P.A.left ⟶ B.A.left} (hx : IsGrpPullback x.P.A A₀.A (gmap K) φx)
    (h₀ : IsGrpPullback D₀.P.A B.A (gmap K) φ₀) (ph : A₀.A ⟶ B.A) [IsMonHom ph] {v : epsR K ⟶ x.P.A} (hv : IsTangent v)
    {w : epsR K ⟶ D₀.P.A} (h : w.left ≫ φ₀ = v.left ≫ φx ≫ ph.left) : IsTangent w := by
  rw [Chart.tan_push h₀, h, ← MonObj.one_comp (X := Over.mk (gmap K)) ph, Over.comp_left, ← (Chart.tan_push hx v).1 hv]
  simp only [Category.assoc]

end Tangent

theorem exists_integral_point : ∀ (K : Type) [Field K] [NumberField K] (X : Over (Sp (𝓞 K))), IsProper X.hom → ∀ x : Sp K ⟶ X.left, x ≫ X.hom = gmap K → ∃ s : 𝟙_ (Over (Sp (𝓞 K))) ⟶ X, x = gmap K ≫ s.left := by
  intro K _ _ X hX x hx
  let R : CommRingCat.{0} := CommRingCat.of (𝓞 K)
  have hZ : ∀ z : Spec R, ValuationRing ((Spec R).presheaf.stalk z) := fun z => by
    letI : Algebra (𝓞 K) ((Spec R).presheaf.stalk z) := StructureSheaf.stalkAlgebra (𝓞 K) z
    have : z.asIdeal.IsPrime := PrimeSpectrum.isPrime (R := 𝓞 K) z
    have : IsLocalization.AtPrime ((Spec R).presheaf.stalk z) z.asIdeal := StructureSheaf.IsLocalization.to_stalk (𝓞 K) z
    have hd : IsDedekindDomain ((Spec R).presheaf.stalk z) := IsLocalization.AtPrime.isDedekindDomain (𝓞 K) z.asIdeal _
    exact ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain ((Spec R).presheaf.stalk z)).out 2 1).1 hd
  obtain ⟨e, he⟩ := IsGenericPointHom.fractionField (𝓞 K) K
  obtain ⟨U, hU, f, h1, h2⟩ := spread_out_of_isGermInjective' (𝟙 (Spec R)) X.hom (x := genericPoint _) (e.inv ≫ x)
    (by rw [Category.assoc, hx, Category.comp_id, Iso.inv_comp_eq]; exact he.symm)
  have : Nonempty U.toScheme := ⟨⟨_, hU⟩⟩
  have : X.left.IsSeparated := ⟨by
    rw [← terminal.comp_from X.hom]
    infer_instance⟩
  obtain ⟨g, g1, g2⟩ := TorusConst.exists_extension hZ U.ι (𝟙 _) X.hom f h2
  refine ⟨Over.homMk g g2, ?_⟩
  rw [Iso.inv_comp_eq, ← g1, ← Category.assoc (U.fromSpecStalkOfMem _ _), Scheme.Opens.fromSpecStalkOfMem_ι,
    ← Category.assoc, he] at h1
  exact h1

theorem exists_keyPB_of_same : ∀ (K : Type) [Field K] (D₀ : Out.DegPre K) (th : D₀.P.L.Sec) (x : KeyIn K) (ψ : D₀.P.A.left ⟶ x.P.A.left), GlobalTheory.IndefiniteRowSideFullHecke.SemisimplePairingSeparation.IsSameAV D₀ th x ψ → ∃ (hg : 1 ≤ D₀.P.g) (hth : ∀ s : Sp K, ∃ z : D₀.P.A.left, D₀.P.A.hom z = s ∧ z ∈ Out.nonzeroLocus th) (v : Fin D₀.P.g → (epsR K ⟶ D₀.P.A)) (hv : IsLieBasis v) (e : D₀.P.g = x.P.g), (∀ i, (v i).left ≫ ψ = (x.v (i.cast e)).left) ∧ KeyPB ⟨D₀.P, hg, D₀.rig, D₀.rig_gen, th, hth, v, hv⟩ x (RingHom.id K) := by
  rintro K _ D₀ th x ψ ⟨he, w, hp, hw, hr, hs⟩
  have e0 : spMap (RingHom.id K) = 𝟙 (Sp K) := Spec.map_id _
  have e1 : spMap (Chart.dualMapR (RingHom.id K)) = 𝟙 _ := by
    have : Chart.dualMapR (RingHom.id K) = RingHom.id _ := RingHom.ext fun a => by ext <;> simp [Chart.dualMapR]
    rw [this]
    exact Spec.map_id _
  have h : IsGrpPullback D₀.P.A x.P.A (spMap (RingHom.id K)) ψ := hp.congr e0.symm rfl
  have e : D₀.P.g = x.P.g := H1.dim_unique D₀.P.A.hom D₀.P.smoothDim
    ((smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hp.1 x.P.smoothDim)
    (eSec D₀.P.A (IsLocalRing.closedPoint K))
  have := x.P.isAb.smooth
  have sq : ∀ i, (x.v i).left ≫ x.P.A.hom = (epsR K).hom ≫ 𝟙 _ := fun i => by rw [Over.w, Category.comp_id]
  let v' : Fin x.P.g → (epsR K ⟶ D₀.P.A) := fun i => Over.homMk (hp.1.lift _ _ (sq i)) (hp.1.lift_snd _ _ _)
  have hv' : ∀ i, (v' i).left ≫ ψ = (x.v i).left := fun i => hp.1.lift_fst _ _ _
  have hv'' : ∀ i, (v' i).left ≫ ψ = spMap (Chart.dualMapR (RingHom.id K)) ≫ (x.v i).left := fun i => by
    rw [e1, Category.id_comp, hv']
  have hb : ∀ {n : ℕ} (e : n = x.P.g), IsLieBasis fun i : Fin n => v' (i.cast e) := fun e => by
    subst e
    exact Chart.isLieBasis_baseChange _ h x.basis hv''
  have hth : ∀ s : Sp K, ∃ z : D₀.P.A.left, D₀.P.A.hom z = s ∧ z ∈ Out.nonzeroLocus th := fun s => by
    obtain ⟨z, hz, hz'⟩ := x.th_ne s
    obtain ⟨y, rfl, hy⟩ := Scheme.exists_preimage_of_isPullback hp.1 z s hz
    obtain ⟨k, hk, u⟩ := (mem_nonzeroLocus _ _).1 hz'
    obtain ⟨i, hi⟩ := exists_chart D₀.P.isLB y
    refine ⟨y, hy, (mem_nonzeroLocus _ _).2 ⟨i, hi, ?_⟩⟩
    have hle : (x.P.L.pull ψ).U (fun _ => k) ⊓ D₀.P.L.U i ≤ ψ ⁻¹ᵁ x.P.L.U k := fun z hz => mem_pull.1 hz.1
    have hy' : y ∈ (x.P.L.pull ψ).U (fun _ => k) ⊓ D₀.P.L.U i := ⟨mem_pull.2 hk, hi⟩
    have u₁ : IsUnit (gs ψ y _ (x.th.f k)) := by rw [gs_stalkMap ψ y _ hk]; exact u.map _
    have a := congrArg (gs (𝟙 _) y _) (hs (fun _ => k) i hle)
    rw [gs_appLE ψ _ _ hle (𝟙 _) y hy', gs_mul _ y _ hy', gs_res _ y _ hy', Category.id_comp] at a
    exact isUnit_of_mul_isUnit_right (a ▸ u₁)
  refine ⟨e ▸ x.g_pos, hth, _, hb e, e, fun i => hv' _, ψ, e0 ▸ he, w, e, Chart.dualMapR (RingHom.id K), h, hw, ?_, hs,
    fun a => ?_, ?_, fun i => hv'' _⟩
  · have : ∀ (f : Sp K ⟶ Sp K) (hf : f = 𝟙 _) (he' : eSec D₀.P.A ≫ ψ = f ≫ eSec x.P.A),
        LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec D₀.P.A) (fun _ => 1)) D₀.rig
          (rigPullOf ψ f he' x.P.L x.rig) := by
      rintro _ rfl _
      exact hr
    exact this _ e0 _
  · ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  · ext <;> simp [Chart.dualMapR]

theorem fibre_transport : ∀ (K : Type) [Field K] [NumberField K] (B : Out.PolAV (Sp (𝓞 K))) (x x' : KeyIn K) (φ : x.P.A.left ⟶ B.A.left) (ψ : x'.P.A.left ⟶ x.P.A.left) (e : x'.P.g = x.P.g) (Tl abelian₂ : MLine K), IsGrpPullback x'.P.A x.P.A (𝟙 _) ψ → LBIso x'.P.L (x.P.L.pull ψ) → (∀ i, (x'.v i).left ≫ ψ = (x.v (i.cast e)).left) → KeyPB x' x (RingHom.id K) → (IsFibreOf B x (gmap K) φ → IsFibreOf B x' (gmap K) (ψ ≫ φ)) ∧ (∀ p, KeyLocAt x Tl abelian₂ p → KeyLocAt x' Tl abelian₂ p) ∧ (∀ σ, KeyArchAt x Tl abelian₂ σ → KeyArchAt x' Tl abelian₂ σ) ∧ ∀ p, (∃ M, IsModelAt B x φ p M ∧ IsLocGen p M.det abelian₂.I) → ∃ M, IsModelAt B x' (ψ ≫ φ) p M ∧ IsLocGen p M.det abelian₂.I := by
  intro K _ _ B x x' φ ψ e Tl abelian₂ hp hw hv hk
  refine ⟨fun h => ⟨(hp.comp h.1).congr (Category.id_comp _) rfl, ?_⟩, ?_, ?_, ?_⟩
  · exact hw.trans x'.P.isLB (pull_isLB x.P.isLB ψ) (pull_isLB B.isLB _)
      (LBIso.chartPull (chartPullPull x.P.L ψ ψ rfl) (chartPullSame B.L _ (fun _ => φ) _ ψ fun _ => rfl) h.2)
  · rintro p ⟨K', i1, i2, R, i3, i4, i5, i6, i7, f, y, a, d, ca, cd, ua, ud, h1, h2⟩
    exact ⟨K', i1, i2, R, i3, i4, i5, i6, i7, f, y, a, d, ca, cd, ua, ud, KeyCancel.keyPB_cancel _ _ _ x x' y _ f hk h1, h2⟩
  · rintro σ ⟨xσ, u, Hm, W, χ, θ, Fd, h1, h2⟩
    exact ⟨xσ, u, Hm, W, χ, θ, Fd, KeyCancel.keyPB_cancel _ _ _ x x' xσ _ σ hk h1, h2⟩
  · rintro p ⟨M, ⟨R, i1, i2, i3, i4, i5, ρ, xR, φR, hg, h1, h2, h3, h4, h5⟩, hl⟩
    have hd : (M.submatrix (finCongr e) (finCongr e)).det = M.det := Matrix.det_submatrix_equiv_self _ _
    refine ⟨M.submatrix (finCongr e) (finCongr e), ⟨R, i1, i2, i3, i4, i5, ρ, xR, φR, hg.trans e.symm, h1, h2, h3,
      hd ▸ h4, fun k => ?_⟩, hd ▸ hl⟩
    obtain ⟨wK, c1, c2⟩ := h5 (k.cast e)
    have sq : wK.left ≫ x.P.A.hom = (epsR K).hom ≫ 𝟙 _ := by rw [Over.w, Category.comp_id]
    let w' : epsR K ⟶ x'.P.A := Over.homMk (hp.1.lift _ _ sq) (hp.1.lift_snd _ _ _)
    have hw' : w'.left ≫ ψ = wK.left := hp.1.lift_fst _ _ _
    refine ⟨w', ?_, by rw [← Category.assoc, hw', c2]; rfl⟩
    have gen : ∀ {n : ℕ} (e : n = x.P.g) (v' : Fin n → (epsR K ⟶ x'.P.A))
        (_ : ∀ i, (v' i).left ≫ ψ = (x.v (i.cast e)).left) (c : Fin x.P.g → K), IsLieComb c x.v wK →
        IsLieComb (fun i => c (i.cast e)) v' w' := by
      rintro _ rfl v' hv' c hc
      have e0 : spMap (RingHom.id K) = 𝟙 (Sp K) := Spec.map_id _
      have e1 : spMap (Chart.dualMapR (RingHom.id K)) = 𝟙 _ := by
        have : Chart.dualMapR (RingHom.id K) = RingHom.id _ := RingHom.ext fun a => by ext <;> simp [Chart.dualMapR]
        rw [this]
        exact Spec.map_id _
      exact Chart.comb_baseChange (RingHom.id K) (hp.congr e0.symm rfl) hc
        (fun i => by rw [e1, Category.id_comp]; exact hv' i) (by rw [e1, Category.id_comp, hw'])
    exact gen e x'.v hv _ c1

theorem letters_tangent : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (c : Coeff l) (n' f : ℕ) (La : ℝ) (o : GlobalTheory.IndefiniteRowSideFullHecke.SemisimplePairingSeparation.CMObj Dw c) (a : GlobalTheory.IndefiniteRowSideFullHecke.SemisimplePairingSeparation.InputOver o) (th : a.D₀.P.L.Sec) (ψ : letI := H.starRing; a.D₀.P.A.left ⟶ o.xB.P.A.left) (ξ : Module.Dual ℤ a.D₀.X) (e : letI := H.starRing; ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR o.K₁)), (letI := H.starRing; LamObjGood o f La) → (letI := H.starRing; GlobalTheory.IndefiniteRowSideFullHecke.SemisimplePairingSeparation.IsSameAV a.D₀ th o.xB ψ) → GlobalTheory.IndefiniteRowSideFullHecke.SemisimplePairingSeparation.AreLetters n' o a ψ ξ e → ∀ τ k, GlobalTheory.ArcQ.GtTanR (e τ k) := by
  rintro E _ _ _ H Dw l c n' f La o a th ψ ξ e hg ⟨he, w, hp, -⟩ ⟨s, hs, h1, h2⟩ τ k
  letI := H.starRing
  have h₀ : IsGrpPullback a.D₀.P.A o.B.A (gmap o.K₁) (ψ ≫ o.φB) :=
    (hp.comp hg.2.2.2.1.1).congr (Category.id_comp _) rfl
  have hi : IsIsogSum o := hg.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  by_cases hτ : τ (H.rt : E) = H.rt0
  · obtain ⟨m, hm⟩ := o.τΨ.surjective ⟨τ, hτ⟩
    obtain rfl : (o.τΨ m).1 = τ := congrArg Subtype.val hm
    obtain ⟨ε, a1, a2⟩ := h1 m
    obtain ⟨_ | i, rfl⟩ := ε.surjective k
    · exact gtTanR_of_torus a1
    · obtain ⟨v, b1, b2⟩ := a2 i
      have := hi.1 i
      exact gtTanR_of_dsDiv hs (isTangent_of_factor hg.2.2.2.2.1.1 h₀ (o.φΨ i) (o.xΨ.basis.1 m) b1) b2
  · obtain ⟨m, hm⟩ := o.τ'.surjective ⟨τ, hτ⟩
    obtain rfl : (o.τ' m).1 = τ := congrArg Subtype.val hm
    obtain ⟨ε, a1, a2⟩ := h2 m
    obtain ⟨_ | i, rfl⟩ := ε.surjective k
    · exact gtTanR_of_torus a1
    · obtain ⟨v, b1, b2⟩ := a2 i
      have := hi.2.1 i
      exact gtTanR_of_dsDiv hs (isTangent_of_factor hg.2.2.2.2.2.1.1 h₀ (o.φ' i) (o.x'.basis.1 m) b1) b2

theorem isMotiveOf_reindex : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (c : Coeff l) (K : Type) [Field K] (bF : c.F →+* K) (a : ArcIn Dw l (RingHom.id c.F) K bF) (σ : K →+* ℂ) (r : ℕ) (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (ξ : Fin r → E) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (P₀ : (Fin r → E) → Fin g → ℂ) (t : Dw.La → X.Λ) (y : X.Λ →ₗ[𝓞 E] a.D₀.X) (ex : letI := GlobalTheory.IndefiniteRowSideFullHecke.SemisimplePairingSeparation.fracAlg σ; (Fin g → ℂ) → Out.GtPtF a.D₀ ℂ), GlobalTheory.IndefiniteRowSideFullHecke.SemisimplePairingSeparation.IsMotiveOf a σ X ξ ty P₀ t y ex → ∀ (g' : ℕ) (π : Fin g' ≃ Fin g), GlobalTheory.IndefiniteRowSideFullHecke.SemisimplePairingSeparation.IsMotiveOf a σ X ξ (fun m => ty (π m)) (fun v m => P₀ v (π m)) t y (fun z => ex (fun m => z (π.symm m))) := by
  intro E _ _ _ H Dw l c K _ bF a σ r X ξ g ty P₀ t y ex h g' π
  letI := SemisimplePairingSeparation.fracAlg σ
  obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13⟩ := h
  let ρ : (Fin g' → ℂ) → (Fin g → ℂ) := fun z m => z (π.symm m)
  have hρ : Differentiable ℂ ρ := by fun_prop
  have e1 : ∀ v, ρ (fun m => P₀ v (π m)) = P₀ v := fun v => funext fun m => congrArg (P₀ v) (π.apply_symm_apply m)
  have e2 : ∀ (s : ℂ) v, ρ (s • fun m => P₀ v (π m)) = s • P₀ v := fun s v => congrArg (s • ·) (e1 v)
  refine ⟨m1, m2, fun z z' => m3 (ρ z) (ρ z'), fun q => ?_, fun x z => ?_, ?_, fun χ jj => ?_, fun z => ?_, fun v => ?_,
    fun v hv s => ?_, fun k v v' z hk hv hv' hz => ?_, fun v => ?_, fun v hv => ?_⟩
  · obtain ⟨z, rfl⟩ := m4 q
    exact ⟨fun m => z (π m), congrArg ex (funext fun m => congrArg z (π.apply_symm_apply m))⟩
  · have := m5 x (ρ z)
    simpa only [Equiv.apply_symm_apply] using this
  · exact HolHom.isHolTo_of_holAt isOpen_univ fun z _ =>
      (HolHom.holAt_of_isHolTo m6 (Set.mem_univ (ρ z))).precomp (hρ z)
  · exact (m7 χ jj).comp hρ.differentiableOn fun z hz => hz
  · refine (m8 (ρ z)).trans (exists_congr fun v => and_congr Iff.rfl ⟨fun h => funext fun m => ?_, fun h => ?_⟩)
    · exact (congrArg z (π.symm_apply_apply m).symm).trans (congrFun h (π m))
    · rw [h, e1]
  · have := m9 v
    rw [← e1 v] at this
    exact this
  · have := m10 v hv s
    rw [← e2 s v] at this
    exact this
  · have := m11 k v v' z hk hv hv' hz
    rw [← e2 _ v, ← e2 _ v'] at this
    exact this
  · obtain ⟨q, h1, h2, h3⟩ := m12 v
    exact ⟨q, h1, h2.trans (congrArg ex (e2 _ _).symm), h3⟩
  · obtain ⟨q, h1, h2, h3⟩ := m13 v hv
    exact ⟨q, h1, h2.trans (congrArg ex (e2 _ _).symm), h3⟩

theorem isMotiveOf_remark : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (c : Coeff l) (K : Type) [Field K] (bF : c.F →+* K) (a : ArcIn Dw l (RingHom.id c.F) K bF) (σ : K →+* ℂ) (r : ℕ) (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (ξ : Fin r → E) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (P₀ : (Fin r → E) → Fin g → ℂ) (t : Dw.La → X.Λ) (y : X.Λ →ₗ[𝓞 E] a.D₀.X) (ex : letI := GlobalTheory.IndefiniteRowSideFullHecke.SemisimplePairingSeparation.fracAlg σ; (Fin g → ℂ) → Out.GtPtF a.D₀ ℂ), GlobalTheory.IndefiniteRowSideFullHecke.SemisimplePairingSeparation.IsMotiveOf a σ X ξ ty P₀ t y ex → (∀ v w, P₀ (v + w) = P₀ v + P₀ w) → ∀ t' : Dw.La → X.Λ, (∀ v, ∃ w : X.Λ, t' v = t v + l.A • w) → (∀ v ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La), ∃ w : X.Λ, t' v = t v + l.M • w) → GlobalTheory.IndefiniteRowSideFullHecke.SemisimplePairingSeparation.IsMotiveOf a σ X ξ ty P₀ t' y ex := by
  intro E _ _ _ H Dw l c K _ bF a σ r X ξ g ty P₀ t y ex h hP t' c1 c2
  letI := SemisimplePairingSeparation.fracAlg σ
  obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13⟩ := h
  let Q : (Fin r → E) →+ (Fin g → ℂ) := AddMonoidHom.mk' P₀ hP
  have key : ∀ (k : ℕ) (_ : k ≠ 0) (u w : X.Λ) (q : Out.QkPt a.D₀ ℂ k), q.y = y u → q.g = ex ((k : ℂ)⁻¹ • P₀ u) →
      ∃ q₂ : Out.QkPt a.D₀ ℂ k, q₂.y = y (u + k • w) ∧ q₂.g = ex ((k : ℂ)⁻¹ • P₀ (u + k • w : X.Λ)) ∧
        Out.QkPt.Equiv a.D₀ ℂ q₂ q := fun k hk u w q h1 h2 => by
    have hk' : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk
    have e : (k : ℂ)⁻¹ • P₀ (u + k • w : X.Λ) = (k : ℂ)⁻¹ • P₀ u + P₀ w := by
      have : P₀ (u + k • w : X.Λ) = P₀ u + k • P₀ w := by
        show Q ((u : Fin r → E) + k • (w : Fin r → E)) = Q u + k • Q w
        rw [map_add, map_nsmul]
      rw [this, smul_add, ← Nat.cast_smul_eq_nsmul ℂ k (P₀ w), smul_smul, inv_mul_cancel₀ hk', one_smul]
    refine ⟨TorusExt.qkShift a.bimult q (y w), ?_, ?_,
      TorusExt.equiv_symm a.bimult (TorusExt.equiv_qkShift a.bimult q (y w))⟩
    · show q.y + k • y w = _
      rw [map_add, map_nsmul, h1]
    · rw [e]
      refine Eq.symm (((TorusExt.isAdd_iff_eq _ _ _).1 (m3 _ _)).trans ?_)
      rw [← h2, (TorusExt.isIota_iff_eq a.bimult _ _).1 (m9 w)]
      rfl
  refine ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, fun v => ?_, fun v hv => ?_⟩
  · obtain ⟨q, h1, h2, h3⟩ := m12 v
    obtain ⟨w, hw⟩ := c1 v
    obtain ⟨q₂, a1, a2, a3⟩ := key _ l.A_pos.ne' _ w q h1 h2
    rw [hw]
    exact ⟨q₂, a1, a2, fun q' hq => TorusExt.equiv_trans a.bimult a3 (h3 q' hq)⟩
  · obtain ⟨q, h1, h2, h3⟩ := m13 v hv
    obtain ⟨w, hw⟩ := c2 v hv
    obtain ⟨q₂, a1, a2, a3⟩ := key _ (by have := l.three_le; omega) _ w q h1 h2
    rw [hw]
    exact ⟨q₂, a1, a2, fun q' hq => TorusExt.equiv_trans a.bimult a3 (h3 q' hq)⟩

theorem markingAt_of_marking : ∀ (D : D7) (T : Core D) (j : ℕ) (σ : T.Q.c.F →+* ℂ) (k : (T.U j σ).Comp) (x : ((T.U j σ).X k).dom) (g : ℕ) (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin ((T.Q.Dw j).mult τ)) (t : (T.Q.Dw j).La →ₗ[𝓞 D.host.E] ((T.U j σ).X k).Λ), IsUnf (T.U j σ) → GlobalTheory.IndefiniteRowSideFullHecke.MonomialNorms.IsMarking k x e t → ∃ (g' : ℕ) (e' : Fin g' ≃ Σ τ : D.host.E →+* ℂ, Fin ((T.Q.Dw j).mult τ)) (t' : (T.Q.Dw j).La → ((T.U j σ).X k).Λ), GlobalTheory.IndefiniteRowSideFullHecke.SemisimplePairingSeparation.IsMarkingAt (T.U j σ) k x e' t' ∧ (∀ v, ∃ w : ((T.U j σ).X k).Λ, t' v = t v + T.Q.l.A • w) ∧ ∀ v ∈ T.Q.l.Mb.map (T.Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) (T.Q.Dw j).La), ∃ w : ((T.U j σ).X k).Λ, t' v = t v + T.Q.l.M • w := by
  intro D T j σ k x g e t hU hm
  obtain ⟨ex, a1, a2, a3, -, a5, a6⟩ := hm
  obtain ⟨g', e', t', hm'⟩ := exists_isMarkingAt hU k x
  refine ⟨g', e', t', hm', ?_⟩
  obtain ⟨F, i, φ, Pm, -, hP, hper, hu, hd, ht⟩ := hm'
  let π : Fin g' ≃ Fin g := e'.trans e.symm
  let ρ : (Fin g' → ℂ) →L[ℂ] (Fin g → ℂ) := ContinuousLinearMap.pi fun m => ContinuousLinearMap.proj (π.symm m)
  have hρ : ∀ z m, ρ z m = z (π.symm m) := fun _ _ => rfl
  have hv : ∀ a, MonomialNorms.perVec (σ := σ) _ e x.1 (φ a : Fin D.R.r → D.host.E) = ρ (Pm a) := fun a => funext fun m => by
    rw [hρ, hP]
    show perFr _ _ _ (relab _ σ (e m).1) (e m).2 =
      perFr _ _ _ (relab _ σ (e' (e'.symm (e m))).1) (e' (e'.symm (e m))).2
    rw [Equiv.apply_symm_apply]
  have b3 : ∀ m, IsDerivAt0 (fun z => (ex z).left) (ρ (Pi.single m 1)) (((T.U j σ).un k x).u (e' m).1 (e' m).2) := fun m => by
    have : ρ (Pi.single m 1) = Pi.single (e.symm ⟨(e' m).1, (e' m).2⟩) 1 := funext fun m' => by
      rw [hρ, Pi.single_apply, Pi.single_apply]
      exact if_congr (π.symm_apply_eq) rfl rfl
    rw [this]
    exact a3 _ _
  have b4 : ∀ m, IsDerivAt0 (fun z => (F.ex i Pm z).left) (Pi.single m 1)
      (((T.U j σ).un k x).u (e' m).1 (e' m).2) := fun m => by
    have := hd (e' m).1 (e' m).2
    rwa [Sigma.eta, Equiv.symm_apply_apply] at this
  have key := congr_of_exp F i hper ρ hu ex _ a1 a2 b3 b4
  have fin : ∀ (n : ℕ) v w, F.t i v = φ.symm (t v) + n • w → φ (F.t i v) = t v + n • φ w :=
    fun n v w h => by rw [h, map_add, map_nsmul, LinearEquiv.apply_symm_apply]
  have hv' : ∀ v, MonomialNorms.perVec (σ := σ) _ e x.1 (t v : Fin D.R.r → D.host.E) = ρ (Pm (φ.symm (t v))) := fun v => by
    rw [← hv, LinearEquiv.apply_symm_apply]
  refine ⟨fun v => ?_, fun v hm => ?_⟩
  · obtain ⟨w, hw⟩ := key _ T.Q.l.A_pos.ne' _ _ _ ((a5 v).trans (by rw [hv'])) (F.ex_etaA _ _ hper v)
    exact ⟨_, (ht v).trans (fin _ _ _ hw)⟩
  · obtain ⟨w, hw⟩ := key _ (by have := T.Q.l.three_le; omega) _ _ _ ((a6 v hm).trans (by rw [hv']))
      (F.ex_eta _ _ hper v hm)
    exact ⟨_, (ht v).trans (fin _ _ _ hw)⟩

theorem marking_of_markingAt : ∀ (D : D7) (T : Core D) (j : ℕ) (σ : T.Q.c.F →+* ℂ) (k : (T.U j σ).Comp) (x : ((T.U j σ).X k).dom) (g : ℕ) (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin ((T.Q.Dw j).mult τ)) (t : (T.Q.Dw j).La → ((T.U j σ).X k).Λ), GlobalTheory.IndefiniteRowSideFullHecke.SemisimplePairingSeparation.IsMarkingAt (T.U j σ) k x e t → ∃ t' : (T.Q.Dw j).La →ₗ[𝓞 D.host.E] ((T.U j σ).X k).Λ, (∀ v, t' v = t v) ∧ GlobalTheory.IndefiniteRowSideFullHecke.MonomialNorms.IsMarking k x e t' := by
  rintro D T j σ k x g e t ⟨F, i, φ, Pm, -, hP, hper, hu, hd, ht⟩
  have hv : ∀ a, MonomialNorms.perVec (σ := σ) _ e x.1 (φ a : Fin D.R.r → D.host.E) = Pm a := fun a => funext fun m => (hP a m).symm
  have key : ∀ (y : Sp ℂ ⟶ (T.Q.Xo j).X) (h : y = F.u i Pm), ∃ ex : (Fin g → ℂ) → (Over.mk y ⟶ (T.Q.Xo j).univ.t.G),
      (∀ z, (ex z).left = (F.ex i Pm z).left) ∧ (∀ z w, ex (z + w) = ex z * ex w) ∧ (∀ z, ex z = 1 ↔ z ∈ Pm.range) ∧
      (∀ a, toUnit _ ≫ (T.Q.Xo j).univ.etaA a = ex ((T.Q.l.A : ℂ)⁻¹ • Pm (F.t i a))) ∧
      ∀ a ∈ T.Q.l.Mb.map (T.Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) (T.Q.Dw j).La),
        toUnit _ ≫ (T.Q.Xo j).univ.eta a = ex ((T.Q.l.M : ℂ)⁻¹ • Pm (F.t i a)) := by
    rintro _ rfl
    exact ⟨F.ex i Pm, fun _ => rfl, F.ex_add i Pm hper, F.ex_ker i Pm hper, F.ex_etaA i Pm hper, F.ex_eta i Pm hper⟩
  obtain ⟨ex, h1, h2, h3, h4, h5⟩ := key _ hu
  have h1' : (fun z => (ex z).left) = fun z => (F.ex i Pm z).left := funext h1
  refine ⟨φ.toLinearMap ∘ₗ F.t i, fun v => (ht v).symm, ex, h2, h1' ▸ isHolTo_ex F i hper, fun τ n => h1' ▸ hd τ n,
    fun z => (h3 z).trans ⟨?_, ?_⟩, fun a => (h4 a).trans (by rw [← hv]; rfl), fun a ha => (h5 a ha).trans (by rw [← hv]; rfl)⟩
  · rintro ⟨a, rfl⟩
    exact ⟨φ a, (φ a).2, (hv a).symm⟩
  · rintro ⟨v, hv', rfl⟩
    obtain ⟨a, ha⟩ := φ.surjective ⟨v, hv'⟩
    exact ⟨a, by rw [← hv, ha]⟩

theorem torsionParam_transfer : ∀ (E : Type) [Field E] [NumberField E] [StarRing (𝓞 E)] (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (𝔄 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (A₀ : Out.PolAV (Sp (𝓞 K))) (oa : A₀.OAct (𝓞 E)) (x : KeyIn K) (φ : x.P.A.left ⟶ A₀.A.left), IsGrpPullback x.P.A A₀.A (gmap K) φ → letI := GlobalTheory.IndefiniteRowSideFullHecke.SemisimplePairingSeparation.fracAlg σ; (∀ κ, GlobalTheory.IndefiniteRowSideFullHecke.MonomialNorms.IsTorsionParam 𝔄 oa.act x φ κ → ∃ pa, GlobalTheory.IndefiniteRowSideFullHecke.SemisimplePairingSeparation.IsTorsionParam σ A₀ oa 𝔄 pa ∧ ∀ a, (pa a).left = (κ a).left ≫ φ) ∧ ∀ pa, GlobalTheory.IndefiniteRowSideFullHecke.SemisimplePairingSeparation.IsTorsionParam σ A₀ oa 𝔄 pa → ∃ κ, GlobalTheory.IndefiniteRowSideFullHecke.MonomialNorms.IsTorsionParam 𝔄 oa.act x φ κ ∧ ∀ a, (pa a).left = (κ a).left ≫ φ := by
  intro E _ _ _ K _ _ σ 𝔄 A₀ oa x φ hφ
  letI := SemisimplePairingSeparation.fracAlg σ
  have hb : (Out.TF (R := K) ℂ).hom ≫ gmap K = (SemisimplePairingSeparation.cPt σ).hom := by
    show (Spec.map _ ≫ Spec.map _) ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext a
    exact IsFractionRing.lift_algebraMap (K := FractionRing K) (g := σ) σ.injective _
  have key : ∀ (y : Sp ℂ ⟶ Sp (𝓞 K)) (_ : (Out.TF (R := K) ℂ).hom ≫ gmap K = y),
      ∃ β : (Out.TF (R := K) ℂ ⟶ x.P.A) ≃* (Over.mk y ⟶ A₀.A), ∀ z, (β z).left = z.left ≫ φ := by
    rintro _ rfl
    let f : (Out.TF (R := K) ℂ ⟶ x.P.A) →* (Over.mk ((Out.TF (R := K) ℂ).hom ≫ gmap K) ⟶ A₀.A) :=
      MonoidHom.mk' (fun z => pushPt hφ.1.w z) fun z z' => Over.OverMorphism.ext (hφ.2 _ z z' _ _ rfl rfl).symm
    refine ⟨MulEquiv.ofBijective f ⟨fun z z' h => Over.OverMorphism.ext (hφ.1.hom_ext (congrArg (·.left) h)
      ((Over.w z).trans (Over.w z').symm)), fun w => ?_⟩, fun _ => rfl⟩
    exact ⟨Over.homMk (hφ.1.lift w.left _ (Over.w w)) (hφ.1.lift_snd _ _ _), Over.OverMorphism.ext (hφ.1.lift_fst _ _ _)⟩
  obtain ⟨β, hβ⟩ := key _ hb
  have iff : ∀ κ, MonomialNorms.IsTorsionParam 𝔄 oa.act x φ κ ↔ SemisimplePairingSeparation.IsTorsionParam σ A₀ oa 𝔄 (fun a => β (κ a)) := fun κ => by
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      refine ⟨fun a b => (congrArg β (h1 a b)).trans (map_mul β _ _), fun b a => Over.OverMorphism.ext ?_,
        fun a => (β.map_eq_one_iff).trans (h2 a), fun z n hn hz => ?_⟩
      · rw [Over.comp_left, hβ, hβ, h4, Category.assoc]
      · obtain ⟨z', rfl⟩ := β.surjective z
        obtain ⟨a, rfl⟩ := h3 z' n hn (β.map_eq_one_iff.1 (by rw [map_pow]; exact hz))
        exact ⟨a, rfl⟩
    · rintro ⟨h1, h4, h2, h3⟩
      refine ⟨fun a b => β.injective ((h1 a b).trans (map_mul β _ _).symm), fun a => (β.map_eq_one_iff).symm.trans (h2 a),
        fun z n hn hz => ?_, fun b a => ?_⟩
      · obtain ⟨a, ha⟩ := h3 (β z) n hn (by rw [← map_pow, hz, map_one])
        exact ⟨a, β.injective ha⟩
      · have := congrArg (·.left) (h4 b a)
        simpa only [Over.comp_left, hβ, Category.assoc] using this
  refine ⟨fun κ h => ⟨_, (iff κ).1 h, fun a => hβ _⟩, fun pa h => ⟨fun a => β.symm (pa a), (iff _).2 ?_, fun a => ?_⟩⟩
  · simpa only [MulEquiv.apply_symm_apply] using h
  · rw [← hβ, MulEquiv.apply_symm_apply]

theorem isExponent_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] (g : ℕ) (ξ : Module.Dual ℤ X) (be : LinearMap.BilinForm ℤ X), (∀ y z, be y z = be z y) → (∀ (a : 𝓞 E) y z, be (a • y) z = be y (H.bar a • z)) → ∀ (ν : E) (j : ℤ), GlobalTheory.IndefiniteRowSideFullHecke.MonomialNorms.IsExponent g ξ be ν j ↔ ∃ χ : X × X →₀ ℤ, GlobalTheory.IndefiniteRowSideFullHecke.SemisimplePairingSeparation.ssNu E g ξ χ = ν ∧ GlobalTheory.IndefiniteRowSideFullHecke.SemisimplePairingSeparation.ssPair g be χ = j := by
  intro E _ _ _ H X _ _ g ξ be hs ha ν j
  classical
  have hw : H.w0 + H.bar H.w0 = 1 := cmHostUnit_add_conj_eq_one H
  have hw' : (H.w0 : E) + cc (H.w0 : E) = 1 := by
    have := congrArg (algebraMap (𝓞 E) E) hw
    rw [map_add, map_one] at this
    rw [cc, ← H.bar_eq]
    exact this
  have ccm : ∀ a b : E, cc (a * b) = cc a * cc b := fun a b => map_mul (IsCMField.complexConj E) a b
  have cca : ∀ a b : E, cc (a + b) = cc a + cc b := fun a b => map_add (IsCMField.complexConj E) a b
  have hbe : ∀ x, be x x = 2 * be x (H.w0 • x) := fun x => by
    have h1 : be x (H.bar H.w0 • x) = be x (H.w0 • x) := by rw [← ha, hs]
    calc be x x = be x ((H.w0 + H.bar H.w0) • x) := by rw [hw, one_smul]
      _ = _ := by rw [add_smul, map_add, h1]; ring
  let N : (X →₀ ℤ) →+ E := Finsupp.liftAddHom fun x => (zmultiplesHom E (MonomialNorms.nrm (MonomialNorms.pairE ξ x)))
  let B : (X →₀ ℤ) →+ ℚ := Finsupp.liftAddHom fun x => (zmultiplesHom ℚ (((be x x : ℤ) : ℚ) / 2))
  let N' : (X × X →₀ ℤ) →+ E := Finsupp.liftAddHom fun p => zmultiplesHom E
    (SemisimplePairingSeparation.pairE E ξ p.1 * cc (SemisimplePairingSeparation.pairE E ξ p.2) + cc (SemisimplePairingSeparation.pairE E ξ p.1) * SemisimplePairingSeparation.pairE E ξ p.2)
  let B' : (X × X →₀ ℤ) →+ ℚ := Finsupp.liftAddHom fun p => zmultiplesHom ℚ ((be p.1 p.2 : ℤ) : ℚ)
  have hN : ∀ n : X →₀ ℤ, ∑ x ∈ n.support, (n x : E) * MonomialNorms.nrm (MonomialNorms.pairE ξ x) = N n := fun n => by
    simp [N, Finsupp.sum]
  have hB : ∀ n : X →₀ ℤ, ∑ x ∈ n.support, (n x : ℚ) * (((be x x : ℤ) : ℚ) / 2) = B n := fun n => by
    simp [B, Finsupp.sum]
  have hN' : ∀ χ, SemisimplePairingSeparation.ssNu E g ξ χ = (g : E)⁻¹ * N' χ := fun χ => by simp [N', SemisimplePairingSeparation.ssNu, Finsupp.sum, mul_add]
  have hB' : ∀ χ, SemisimplePairingSeparation.ssPair g be χ = (g : ℚ)⁻¹ * B' χ := fun χ => by simp [B', SemisimplePairingSeparation.ssPair, Finsupp.sum]
  have k1 : ∀ n : X →₀ ℤ, ∃ χ, N' χ = N n ∧ B' χ = B n := fun n => by
    induction n using Finsupp.induction_linear with
    | zero => exact ⟨0, by simp, by simp⟩
    | add f f' h h' =>
      obtain ⟨a, a1, a2⟩ := h
      obtain ⟨b, b1, b2⟩ := h'
      exact ⟨a + b, by rw [map_add, map_add, a1, b1], by rw [map_add, map_add, a2, b2]⟩
    | single x m =>
      refine ⟨Finsupp.single (x, H.w0 • x) m, ?_, ?_⟩
      · simp only [N, N', Finsupp.liftAddHom_apply_single, zmultiplesHom_apply, pairE_smul, MonomialNorms.nrm, ccm]
        congr 1
        show _ = SemisimplePairingSeparation.pairE E ξ x * cc (SemisimplePairingSeparation.pairE E ξ x)
        linear_combination (SemisimplePairingSeparation.pairE E ξ x * cc (SemisimplePairingSeparation.pairE E ξ x)) * hw'
      · simp only [B, B', Finsupp.liftAddHom_apply_single, zmultiplesHom_apply]
        rw [hbe x]
        push_cast
        congr 1
        ring
  have k2 : ∀ χ : X × X →₀ ℤ, ∃ n, N n = N' χ ∧ B n = B' χ := fun χ => by
    induction χ using Finsupp.induction_linear with
    | zero => exact ⟨0, by simp, by simp⟩
    | add f f' h h' =>
      obtain ⟨a, a1, a2⟩ := h
      obtain ⟨b, b1, b2⟩ := h'
      exact ⟨a + b, by rw [map_add, map_add, a1, b1], by rw [map_add, map_add, a2, b2]⟩
    | single p m =>
      refine ⟨Finsupp.single (p.1 + p.2) m - Finsupp.single p.1 m - Finsupp.single p.2 m, ?_, ?_⟩
      · simp only [N, N', map_sub, Finsupp.liftAddHom_apply_single, zmultiplesHom_apply, MonomialNorms.nrm, zsmul_eq_mul]
        have e : MonomialNorms.pairE (E := E) ξ = SemisimplePairingSeparation.pairE E ξ := rfl
        rw [e, pairE_add, cca]
        ring
      · simp only [B, B', map_sub, Finsupp.liftAddHom_apply_single, zmultiplesHom_apply, zsmul_eq_mul, map_add,
          LinearMap.add_apply, hs p.2 p.1]
        push_cast
        ring
  unfold MonomialNorms.IsExponent
  simp only [hN, hB, hN', hB']
  constructor
  · rintro ⟨n, h1, h2⟩
    obtain ⟨χ, a1, a2⟩ := k1 n
    exact ⟨χ, by rw [a1, h1], by rw [a2, h2]⟩
  · rintro ⟨χ, h1, h2⟩
    obtain ⟨n, a1, a2⟩ := k2 χ
    exact ⟨n, by rw [a1, h1], by rw [a2, h2]⟩

section Exponents

variable {E : Type} [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) {X : Type} [AddCommGroup X]
  [Module (𝓞 E) X] {g : ℕ} {ξ : Module.Dual ℤ X} {be : LinearMap.BilinForm ℤ X}

theorem separates_iff (hs : ∀ y z, be y z = be z y) (ha : ∀ (a : 𝓞 E) y z, be (a • y) z = be y (H.bar a • z))
    (ν : E) (j : ℤ) :
    MonomialNorms.Separates g ξ be ν j ↔ ∃ χ₀, SemisimplePairingSeparation.ssNu E g ξ χ₀ = ν ∧ SemisimplePairingSeparation.Separates E g ξ be χ₀ j := by
  have h := isExponent_iff E H X g ξ be hs ha
  constructor
  · rintro ⟨h1, h2, h3⟩
    obtain ⟨χ₀, rfl, hj⟩ := (h _ _).1 h2
    exact ⟨χ₀, rfl, h1, hj, fun χ hχ hp => h3 _ hχ ((h _ _).2 ⟨χ, rfl, hp⟩)⟩
  · rintro ⟨χ₀, rfl, h1, hj, h3⟩
    refine ⟨h1, (h _ _).2 ⟨χ₀, rfl, hj⟩, fun ν hν he => ?_⟩
    obtain ⟨χ, rfl, hp⟩ := (h _ _).1 he
    exact h3 χ hν hp

theorem emb_cc (τ : E →+* ℂ) (a : E) : τ (cc a) = starRingEnd ℂ (τ a) := IsCMField.complexEmbedding_complexConj E τ a

theorem emb_ssNu (χ : X × X →₀ ℤ) (τ : E →+* ℂ) :
    (((τ (SemisimplePairingSeparation.ssNu E g ξ χ)).re : ℝ) : ℂ) = τ (SemisimplePairingSeparation.ssNu E g ξ χ) := by
  rw [← Complex.conj_eq_iff_re]
  simp only [SemisimplePairingSeparation.ssNu, Finsupp.sum, map_mul, map_sum, map_add, map_inv₀, map_natCast, map_intCast, emb_cc,
    Complex.conj_conj]
  congr 1
  exact Finset.sum_congr rfl fun p _ => by ring

theorem labK_conjEmb {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} (c : Coeff l) (K : Type) [Field K] [Algebra c.F K]
    (τ : E →+* ℂ) (a : E) : labK c K (conjEmb τ) a = labK c K τ (cc a) :=
  congrArg (algebraMap c.F K) (Subtype.ext (emb_cc τ a).symm)

theorem EFf_swap {r : ℕ} (Z : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (v w : Fin r → E) :
    EFf Z.ξ0 Z.Gm v w = -EFf Z.ξ0 Z.Gm w v := by
  have h1 : cc (herm Z.Gm w v) = herm Z.Gm v w := by
    have hG : ∀ a b, IsCMField.complexConj E (Z.Gm a b) = Z.Gm b a := Z.Gm_herm
    simp only [herm, cc, map_sum, map_mul, IsCMField.complexConj_apply_apply, hG]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  have h2 : ∀ a : E, Algebra.trace ℚ E (cc a) = Algebra.trace ℚ E a := fun a =>
    Algebra.trace_eq_of_algEquiv ((IsCMField.complexConj E).restrictScalars ℚ) a
  have h3 : IsCMField.complexConj E Z.ξ0 = -Z.ξ0 := Z.ξ0_im
  rw [EFf, EFf, ← h2 (-Z.ξ0 * herm Z.Gm w v), ← h1, ← map_neg]
  congr 1
  simp only [cc, map_mul, map_neg, h3]
  ring

theorem perFr_add {r : ℕ} (Z : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x : Frame Z.Ψ r) (v w : Fin r → E) (τ : E →+* ℂ) (i : ℕ) :
    perFr Z x (v + w) τ i = perFr Z x v τ i + perFr Z x w τ i := by
  have e : ∀ τ : E →+* ℂ, Data.emb τ (v + w) = Data.emb τ v + Data.emb τ w := fun τ => funext fun a => map_add τ _ _
  unfold perFr
  split_ifs
  · rw [e, Matrix.mulVec_add]; rfl
  · simp
  · simp only [e, hermC, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]
  · simp
  · simp

end Exponents

section Fibre

variable {K : Type} [Field K]

theorem exists_isSameAV (D₀ : Out.DegPre K) (th : D₀.P.L.Sec) (x : KeyIn K) {Y : Scheme.{0}} (φ : x.P.A.left ⟶ Y)
    (φ₀ : D₀.P.A.left ⟶ Y) (hx : ∃ hg hth v hv, x = ⟨D₀.P, hg, D₀.rig, D₀.rig_gen, th, hth, v, hv⟩) (h : HEq φ₀ φ) :
    ∃ ψ : D₀.P.A.left ⟶ x.P.A.left, ψ ≫ φ = φ₀ ∧ SemisimplePairingSeparation.IsSameAV D₀ th x ψ := by
  obtain ⟨hg, hth, v, hv, rfl⟩ := hx
  obtain rfl := eq_of_heq h
  refine ⟨𝟙 _, Category.id_comp _, ?_⟩
  let L : RigLB D₀.P.A := ⟨D₀.P.L, D₀.rig, D₀.P.isLB, D₀.rig_gen⟩
  have : IsMonHom (Iso.refl D₀.P.A).hom := inferInstanceAs (IsMonHom (𝟙 _))
  refine ⟨(Category.comp_id _).trans (Category.id_comp _).symm, isoPullId (idIso D₀.P.L) rfl,
    isGrpPullback_of_iso (Iso.refl D₀.P.A),
    (isGen_iff _).2 (isoPullId_pgen (idIso_isGen D₀.P.isLB) rfl), isoPullId_maps (idIso_maps L) rfl rfl _,
    fun j i h => fn_ext fun y hy => ?_⟩
  have hj : y ∈ D₀.P.L.U (j PUnit.unit) := mem_pull.1 hy.1
  refine (gs_appLE (𝟙 _) _ _ h (𝟙 _) y hy _).trans ?_
  rw [Category.id_comp, gs_compat th (𝟙 _) y hj hy.2, gs_mul _ y _ hy, gs_res _ y _ hy]
  exact congrArg (· * _) ((gs_unit _ y _ hy _).trans
    (congrArg Units.val (gw_isoPullId (idIso D₀.P.L) rfl (𝟙 _) y _ i hj hy.2))).symm

variable [NumberField K] {D₀ : Out.DegPre K}

theorem isEtaLetter_iff (n : ℕ) (s : ∀ Z : Over (Sp K), (Z ⟶ D₀.P.A) → Out.GtPt D₀ Z) {A₀ B : Out.PolAV (Sp (𝓞 K))}
    (x : KeyIn K) {φx : x.P.A.left ⟶ A₀.A.left} {φ₀ : D₀.P.A.left ⟶ B.A.left}
    (hx : φx ≫ A₀.A.hom = x.P.A.hom ≫ gmap K) (h₀ : IsPullback φ₀ D₀.P.A.hom B.A.hom (gmap K)) (ph : A₀.A ⟶ B.A)
    (v : epsR K ⟶ x.P.A) (w : Out.GtPt D₀ (epsR K)) :
    MonomialNorms.IsEtaLetter n s x φx φ₀ ph v w ↔
      ∃ v' : epsR K ⟶ D₀.P.A, v'.left ≫ φ₀ = v.left ≫ φx ≫ ph.left ∧ SemisimplePairingSeparation.IsDsDiv D₀ n s v' w := by
  constructor
  · rintro ⟨f, hf, hw⟩
    exact ⟨v ≫ f, by rw [Over.comp_left, Category.assoc, hf], hw⟩
  · rintro ⟨v', hv, hw⟩
    have sq : (φx ≫ ph.left) ≫ B.A.hom = x.P.A.hom ≫ gmap K := by rw [Category.assoc, Over.w, hx]
    let f : x.P.A ⟶ D₀.P.A := Over.homMk (h₀.lift _ _ sq) (h₀.lift_snd _ _ _)
    have hf : f.left ≫ φ₀ = φx ≫ ph.left := h₀.lift_fst _ _ _
    have e : v ≫ f = v' := Over.OverMorphism.ext (h₀.hom_ext (by rw [Over.comp_left, Category.assoc, hf, hv])
      (by rw [Over.w, Over.w]))
    exact ⟨f, hf, e ▸ hw⟩

end Fibre

theorem blocks_eq {a b n p : ℕ} (ε : Fin a ⊕ Fin b ≃ Fin n) (h1 : ∀ i, (ε (.inl i) : ℕ) = i)
    (h2 : ∀ i, (ε (.inr i) : ℕ) = p + i) : n = a + b := by
  simpa using (Fintype.card_congr ε).symm

variable {D : D7} {T : Core D} {j : ℕ}

section Family

variable {n' : ℕ} {La c₁ : ℝ}

abbrev withFibre (o : MonomialNorms.CMObj T j) (x : KeyIn o.fld) (φ : x.P.A.left ⟶ o.abB.A.left) : MonomialNorms.CMObj T j :=
  letI := T.Q.H.starRing
  LamObj.mk o.K₁ o.B o.oa o.AΨ o.oaΨ o.A' o.oa' o.φΨ o.φ' o.hΨ o.h' x o.xΨ o.x' φ o.φΨg o.φ'g o.τΨ o.τ' o.ℓΨ o.ℓ' o.Tl
    o.LamL

theorem trace_cast (ν : D.host.E) :
    (((Algebra.trace ℚ D.host.E ν / 2 : ℚ)) : ℝ) = (Algebra.trace ℚ D.host.E ν : ℝ) / 2 := by
  push_cast; rfl

theorem letters_iff (o : MonomialNorms.CMObj T j) (d : ArcDatumAt T j o.fld) (ξ : Module.Dual ℤ d.a.D₀.X)
    (ψ : letI := T.Q.H.starRing; d.a.D₀.P.A.left ⟶ o.xB.P.A.left) (φ₀ : d.a.D₀.P.A.left ⟶ o.abB.A.left)
    (hφ : letI := T.Q.H.starRing; ψ ≫ o.φB = φ₀)
    (h₀ : IsPullback φ₀ d.a.D₀.P.A.hom o.abB.A.hom (gmap o.fld))
    (hΨ : letI := T.Q.H.starRing; o.φΨg ≫ o.AΨ.A.hom = o.xΨ.P.A.hom ≫ gmap o.fld)
    (h' : letI := T.Q.H.starRing; o.φ'g ≫ o.A'.A.hom = o.x'.P.A.hom ≫ gmap o.fld) :
    letI := T.Q.H.starRing
    (∃ s : ∀ Z : Over (Sp o.fld), (Z ⟶ d.a.D₀.P.A) → Out.GtPt d.a.D₀ Z, MonomialNorms.IsSectionOver d.a.D₀ n' s ∧
      (∀ (τ : D.host.E →+* ℂ) (h : τ (T.Q.H.rt : D.host.E) = T.Q.H.rt0),
        ∃ ε : Option (Fin ((T.Q.Dw j).p - 1)) ≃ Fin ((T.Q.Dw j).mult τ),
          MonomialNorms.IsTorusTangent (D₀ := d.a.D₀) (d.e τ (ε none))
            (fun χ => labK T.Q.c o.fld (conjEmb τ) (MonomialNorms.pairE ξ χ)) ∧
          ∀ i, MonomialNorms.IsEtaLetter n' s o.xΨ o.φΨg φ₀ (o.φΨ i) (o.xΨ.v (o.τΨ.symm ⟨τ, h⟩)) (d.e τ (ε (some i)))) ∧
      ∀ (τ : D.host.E →+* ℂ) (h : τ (T.Q.H.rt : D.host.E) ≠ T.Q.H.rt0),
        ∃ ε : Option (Fin ((T.Q.Dw j).q - 1)) ≃ Fin ((T.Q.Dw j).mult τ),
          MonomialNorms.IsTorusTangent (D₀ := d.a.D₀) (d.e τ (ε none))
            (fun χ => labK T.Q.c o.fld (conjEmb τ) (MonomialNorms.pairE ξ χ)) ∧
          ∀ i, MonomialNorms.IsEtaLetter n' s o.x' o.φ'g φ₀ (o.φ' i) (o.x'.v (o.τ'.symm ⟨τ, h⟩)) (d.e τ (ε (some i)))) ↔
      SemisimplePairingSeparation.AreLetters n' o d.a ψ ξ d.e := by
  letI := T.Q.H.starRing
  subst hφ
  have lab : ∀ τ, (fun χ => labK T.Q.c o.fld (conjEmb τ) (MonomialNorms.pairE ξ χ)) =
      fun χ => labK T.Q.c o.fld τ (cc (SemisimplePairingSeparation.pairE D.host.E ξ χ)) := fun τ => funext fun χ => labK_conjEmb _ _ _ _ _
  refine exists_congr fun s => and_congr Iff.rfl (and_congr ⟨fun h m => ?_, fun h τ hτ => ?_⟩
    ⟨fun h m => ?_, fun h τ hτ => ?_⟩)
  · obtain ⟨ε, h1, h2⟩ := h (o.τΨ m).1 (o.τΨ m).2
    rw [lab] at h1
    refine ⟨ε, h1, fun i => ?_⟩
    have := (isEtaLetter_iff n' s o.xΨ hΨ h₀ _ _ _).1 (h2 i)
    rwa [Subtype.coe_eta, Equiv.symm_apply_apply] at this
  · obtain ⟨m, hm⟩ := o.τΨ.surjective ⟨τ, hτ⟩
    obtain rfl : (o.τΨ m).1 = τ := congrArg Subtype.val hm
    obtain ⟨ε, h1, h2⟩ := h m
    rw [lab]
    refine ⟨ε, h1, fun i => (isEtaLetter_iff n' s o.xΨ hΨ h₀ _ _ _).2 ?_⟩
    rw [Subtype.coe_eta, Equiv.symm_apply_apply]
    exact h2 i
  · obtain ⟨ε, h1, h2⟩ := h (o.τ' m).1 (o.τ' m).2
    rw [lab] at h1
    refine ⟨ε, h1, fun i => ?_⟩
    have := (isEtaLetter_iff n' s o.x' h' h₀ _ _ _).1 (h2 i)
    rwa [Subtype.coe_eta, Equiv.symm_apply_apply] at this
  · obtain ⟨m, hm⟩ := o.τ'.surjective ⟨τ, hτ⟩
    obtain rfl : (o.τ' m).1 = τ := congrArg Subtype.val hm
    obtain ⟨ε, h1, h2⟩ := h m
    rw [lab]
    refine ⟨ε, h1, fun i => (isEtaLetter_iff n' s o.x' h' h₀ _ _ _).2 ?_⟩
    rw [Subtype.coe_eta, Equiv.symm_apply_apply]
    exact h2 i

theorem fibre_of_same {o : MonomialNorms.CMObj T j} {D₀ : Out.DegPre o.fld} {th : D₀.P.L.Sec} {f : ℕ}
    {ψ : letI := T.Q.H.starRing; D₀.P.A.left ⟶ o.xB.P.A.left}
    (hg : letI := T.Q.H.starRing; LamObjGood o f La) (hs : letI := T.Q.H.starRing; SemisimplePairingSeparation.IsSameAV D₀ th o.xB ψ) :
    letI := T.Q.H.starRing
    IsGrpPullback D₀.P.A o.B.A (gmap o.K₁) (ψ ≫ o.φB) := by
  letI := T.Q.H.starRing
  obtain ⟨he, w, hp, -⟩ := hs
  exact (hp.comp hg.2.2.2.1.1).congr (Category.id_comp _) rfl

theorem builtFrom_of_built {o : MonomialNorms.CMObj T j} {d : ArcDatumAt T j o.fld} {ξ : Module.Dual ℤ d.a.D₀.X}
    {ν : D.host.E} {φ₀ : d.a.D₀.P.A.left ⟶ o.abB.A.left} (h : MonomialNorms.Built n' La c₁ o d ξ ν φ₀) :
    letI := T.Q.H.starRing
    ∃ ψ χ₀, ψ ≫ o.φB = φ₀ ∧ SemisimplePairingSeparation.ssNu D.host.E T.Q.l.M ξ χ₀ = ν ∧ SemisimplePairingSeparation.BuiltFrom n' La c₁ o d ψ ξ χ₀ := by
  letI := T.Q.H.starRing
  obtain ⟨hg, hx, hφ, hact, -, hrk, hξ, hn, hc, hτ, hsep, htr, hlet, -, harc⟩ := h
  obtain ⟨ψ, hψ, hs⟩ := exists_isSameAV d.a.D₀ d.th o.xB o.φB φ₀ hx hφ
  obtain ⟨χ₀, hν, hsep'⟩ := (separates_iff T.Q.H d.a.be_symm d.a.be_adj _ _).1 hsep
  subst hψ hν
  refine ⟨ψ, χ₀, rfl, rfl, ⟨hn, hg, hs, fun x => (hact x).trans (Category.assoc _ _ _), hrk, hξ, ⟨hc, hτ⟩, hsep',
    (trace_cast _).trans_le htr⟩, ?_, harc⟩
  exact (letters_iff o d ξ ψ _ rfl (fibre_of_same hg hs).1 hg.2.2.2.2.1.1.1.w hg.2.2.2.2.2.1.1.1.w).1 hlet

set_option maxHeartbeats 1600000 in

theorem built_of_builtFrom (h1 : Out.Laws) (h2 : Out.Laws2) {o : MonomialNorms.CMObj T j} {d : ArcDatumAt T j o.fld}
    {ψ : letI := T.Q.H.starRing; d.a.D₀.P.A.left ⟶ o.xB.P.A.left} {ξ : Module.Dual ℤ d.a.D₀.X}
    {χ₀ : d.a.D₀.X × d.a.D₀.X →₀ ℤ} (h : SemisimplePairingSeparation.BuiltFrom n' La c₁ o d ψ ξ χ₀) :
    letI := T.Q.H.starRing
    ∃ x φ, MonomialNorms.Built n' La c₁ (withFibre o x φ) d ξ (SemisimplePairingSeparation.ssNu D.host.E T.Q.l.M ξ χ₀) (ψ ≫ o.φB) := by
  letI := T.Q.H.starRing
  obtain ⟨⟨hn, hg, hs, hact, hrk, hξ, ⟨hc, hτ⟩, hsep, htr⟩, hlet, harc⟩ := h
  obtain ⟨g1, g2, v, hv, e, hve, hk⟩ := exists_keyPB_of_same _ d.a.D₀ d.th o.xB ψ hs
  have hp := fibre_of_same hg hs
  have ht := letters_tangent _ _ _ _ _ n' _ La o d.a d.th ψ ξ d.e hg hs hlet
  have hl := (letters_iff o d ξ ψ _ rfl hp.1 hg.2.2.2.2.1.1.1.w hg.2.2.2.2.2.1.1.1.w).2 hlet
  obtain ⟨he, w, hψ, hw, -⟩ := hs
  obtain ⟨f1, f2, f3, f4⟩ := fibre_transport _ o.B o.xB ⟨d.a.D₀.P, g1, d.a.D₀.rig, d.a.D₀.rig_gen, d.th, g2, v, hv⟩ o.φB ψ e
    o.Tl o.LamL hψ ⟨w, hw⟩ hve hk
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23⟩ := hg
  have := o.B.isAb.proper
  refine ⟨⟨d.a.D₀.P, g1, d.a.D₀.rig, d.a.D₀.rig_gen, d.th, g2, v, hv⟩, ψ ≫ o.φB,
    ⟨a1, a2, a3, f1 a4, a5, a6, a7, a8, e.trans a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20,
      fun p => f2 p (a21 p), fun σ => f3 σ (a22 σ), fun p => f4 p (a23 p)⟩,
    ⟨g1, g2, v, hv, rfl⟩, HEq.rfl, fun x => (hact x).trans (Category.assoc _ _ _).symm, fun y => ?_, hrk, hξ, hn, hc, hτ,
    (separates_iff T.Q.H d.a.be_symm d.a.be_adj _ _).2 ⟨χ₀, rfl, hsep⟩, (trace_cast _).symm.trans_le htr, hl,
    GlobalTheory.ArcQ.arcDatum_arcLieBasis h1 h2 _ _ _ _ _ _ _
      ⟨d.Wp, d.Y, d.a, d.χ, d.W, d.e, d.yF, d.th, d.arcDatum_isArc_point_basis, d.isArc3, d.μ, d.jj⟩ ht, harc⟩
  refine exists_integral_point _ o.B.A this _ ?_
  rw [Category.assoc, hp.1.w, ← Category.assoc, Over.w]
  exact Category.id_comp _

theorem inFamily_iff (h1 : Out.Laws) (h2 : Out.Laws2) (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra T.Q.c.F K₁]
    (d : ArcDatumAt T j K₁) : MonomialNorms.InFamily T j n' La c₁ K₁ d ↔ SemisimplePairingSeparation.InFam n' La c₁ d := by
  letI := T.Q.H.starRing
  constructor
  · rintro ⟨o, d', e1, e2, e3, e4, ξ, ν, φ₀, h⟩
    obtain ⟨ψ, χ₀, -, -, hb⟩ := builtFrom_of_built h
    subst e1
    obtain rfl := eq_of_heq e2
    obtain rfl := eq_of_heq e3
    obtain rfl := eq_of_heq e4
    exact ⟨o.B, o.oa, o.AΨ, o.oaΨ, o.A', o.oa', o.φΨ, o.φ', o.hΨ, o.h', o.xB, o.xΨ, o.x', o.φB, o.φΨg, o.φ'g, o.τΨ,
      o.τ', o.ℓΨ, o.ℓ', o.Tl, o.LamL, ψ, ξ, χ₀, hb⟩
  · rintro ⟨B, oa, AΨ, oaΨ, A', oa', φΨ, φ', hΨ, h', xB, xΨ, x', φB, φΨg, φ'g, τΨ, τ', ℓΨ, ℓ', Tl, LamL, ψ, ξ, χ₀, h⟩
    obtain ⟨x, φ, hb⟩ := built_of_builtFrom h1 h2 h
    exact ⟨withFibre _ x φ, d, rfl, HEq.rfl, HEq.rfl, HEq.rfl, _, _, _, hb⟩

end Family

section Comparison₂

variable {σ : T.Q.c.F →+* ℂ} {k : (T.U j σ).Comp} {x : ((T.U j σ).X k).dom} {ξ : Fin D.R.r → D.host.E}
  {ν : ((T.U j σ).X k).Ψ → ℝ} {lam : Fin (D.R.r - 2) → Fin D.R.r → D.host.E}

theorem eTwoPi_eq (q : ℚ) (n : ℕ) :
    eTwoPi (-((q : ℂ) / n)) = Complex.exp (-(2 * Real.pi * Complex.I) * (q : ℂ) / n) := by
  unfold eTwoPi
  congr 1
  ring

set_option maxHeartbeats 1600000 in

theorem tiedAt_iff (hU : IsUnf (T.U j σ)) {o : MonomialNorms.CMObj T j} {d : ArcDatumAt T j o.fld}
    (ψ : letI := T.Q.H.starRing; d.a.D₀.P.A.left ⟶ o.xB.P.A.left) (ξ₁ : Module.Dual ℤ d.a.D₀.X)
    (χ₀ : d.a.D₀.X × d.a.D₀.X →₀ ℤ) (σ₁ : o.fld →+* ℂ)
    (hΨ : letI := T.Q.H.starRing; IsGrpPullback o.xΨ.P.A o.AΨ.A (gmap o.K₁) o.φΨg)
    (h' : letI := T.Q.H.starRing; IsGrpPullback o.x'.P.A o.A'.A (gmap o.K₁) o.φ'g) :
    letI := T.Q.H.starRing
    MonomialNorms.TiedAt o d ξ₁ (SemisimplePairingSeparation.ssNu D.host.E T.Q.l.M ξ₁ χ₀) (ψ ≫ o.φB) σ₁ k x ξ ν lam ↔
      SemisimplePairingSeparation.TiedAt D.host.AA (T.U j σ) k x ξ ν lam o d.a ψ ξ₁ χ₀ σ₁ := by
  letI := T.Q.H.starRing
  letI := SemisimplePairingSeparation.fracAlg σ₁
  have hp : ((T.U j σ).X k).p0 = (T.Q.Dw j).q := (hU.2.1 k).1
  obtain ⟨tΨ1, tΨ2⟩ := torsionParam_transfer D.host.E o.K₁ σ₁ D.host.AA o.AΨ o.oaΨ o.xΨ o.φΨg hΨ
  obtain ⟨t'1, t'2⟩ := torsionParam_transfer D.host.E o.K₁ σ₁ D.host.AA o.A' o.oa' o.x' o.φ'g h'
  constructor
  · rintro ⟨hσ, g, e, s₀, P₀, y, ex, t, rfl, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, hm, m12, m13, hξ, hν,
      ε, κΨ, κ', e1, e2, kΨ, k', lΨ, l'⟩
    have mot : SemisimplePairingSeparation.IsMotiveOf d.a σ₁ ((T.U j σ).X k) ξ (fun m => relab T.Q.c σ (e m).1)
        (MonomialNorms.perVec (σ := σ) ((T.U j σ).X k) e (((T.U j σ).X k).flow ξ s₀ x.1)) t y ex := by
      refine ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9, ?_, fun n v v' z hn hv hv' hz =>
        m11 n v v' z hn hv hv' (hz.trans (eTwoPi_eq _ _).symm), m12, m13⟩
      rintro ⟨v, hv⟩ ⟨b, rfl⟩ s
      exact m10 b hv s
    obtain ⟨g', e', t', hm', c1, c2⟩ := markingAt_of_marking D T j σ k x g e t hU hm
    have mot' := isMotiveOf_remark _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mot
      (fun v w => funext fun i => perFr_add _ _ _ _ _ _) t' c1 c2
    have mot'' := isMotiveOf_reindex _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mot' g' (e'.trans e.symm)
    obtain ⟨paΨ, pΨ, qΨ⟩ := tΨ1 κΨ kΨ
    obtain ⟨pa', p', q'⟩ := t'1 κ' k'
    have ety : (fun m => relab T.Q.c σ (e ((e'.trans e.symm) m)).1) = fun m => relab T.Q.c σ (e' m).1 :=
      funext fun m => by rw [Equiv.trans_apply, Equiv.apply_symm_apply]
    refine ⟨hσ, g', e', t', s₀, _, y, _, paΨ, pa', hm', fun v m => ?_, ety ▸ mot'', fun v => ?_, fun τ => ?_, pΨ, p',
      blocks_eq ε e1 e2, fun i m hi => ?_, fun i m hi => ?_⟩
    · show perFr _ _ v (relab T.Q.c σ (e (e.symm (e' m))).1) (e (e.symm (e' m))).2 = _
      rw [Equiv.apply_symm_apply]
    · rw [hξ v, EFf_swap, neg_neg]
    · exact Complex.ofReal_injective ((hν τ).trans (emb_ssNu χ₀ τ.1).symm)
    · obtain rfl : m = ε (.inl i) := Fin.ext (hi.trans (e1 i).symm)
      refine ⟨(l' i).1, fun b => ?_⟩
      simp only [Equiv.apply_symm_apply]
      rw [Over.comp_left, q', Category.assoc]
      exact (l' i).2 b
    · obtain rfl : m = ε (.inr i) := Fin.ext (by rw [hi, e2, hp])
      refine ⟨(lΨ i).1, fun b => ?_⟩
      simp only [Equiv.apply_symm_apply]
      rw [Over.comp_left, qΨ, Category.assoc]
      exact (lΨ i).2 b
  · rintro ⟨hσ, g, e, t, s₀, P₀, y, ex, paΨ, pa', hm, hP, mot, hξ, hν, pΨ, p', hr, l', lΨ⟩
    obtain ⟨t', ht, hm'⟩ := marking_of_markingAt D T j σ k x g e t hm
    obtain rfl : t = t' := funext fun v => (ht v).symm
    obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13⟩ := mot
    obtain ⟨κΨ, kΨ, qΨ⟩ := tΨ2 paΨ pΨ
    obtain ⟨κ', k', q'⟩ := t'2 pa' p'
    let ε : Fin ((T.Q.Dw j).q - 1) ⊕ Fin ((T.Q.Dw j).p - 1) ≃ Fin (D.R.r - 2) :=
      finSumFinEquiv.trans (finCongr hr.symm)
    have e1 : ∀ i, (ε (.inl i) : ℕ) = i := fun i => rfl
    have e2 : ∀ i, (ε (.inr i) : ℕ) = (T.Q.Dw j).q - 1 + i := fun i => rfl
    refine ⟨hσ, g, e, s₀, P₀, y, ex, t', funext fun v => funext fun m => hP v m, m1, m2, m3, m4, m5, m6, m7, m8, m9,
      fun a ha w => m10 ⟨_, ha⟩ ⟨a, rfl⟩ w,
      fun n v v' z hn hv hv' hz => m11 n v v' z hn hv hv' (hz.trans (eTwoPi_eq _ _)), hm', m12, m13,
      fun v => ?_, fun τ => ?_, ε, κΨ, κ', e1, fun i => by rw [e2, hp], kΨ, k', fun i => ⟨(lΨ i _ (e2 i)).1, fun b => ?_⟩,
      fun i => ⟨(l' i _ (e1 i)).1, fun b => ?_⟩⟩
    · rw [hξ v, EFf_swap]
    · rw [hν τ]; exact emb_ssNu χ₀ τ.1
    · rw [← (lΨ i _ (e2 i)).2 b, Over.comp_left, qΨ, Category.assoc]
    · rw [← (l' i _ (e1 i)).2 b, Over.comp_left, q', Category.assoc]

end Comparison₂

section Claims

def HasMember (n' : ℕ) (La c₁ : ℝ) (Wp : ValuationSubring ℂ) (Y : Model (T.Q.Xo j) T.Q.c (T.Q.c.V Wp).subtype)
    {σ : T.Q.c.F →+* ℂ} (k : (T.U j σ).Comp) (x : ((T.U j σ).X k).dom) (ξ : Fin D.R.r → D.host.E)
    (ν : ((T.U j σ).X k).Ψ → ℝ) (lam : Fin (D.R.r - 2) → Fin D.R.r → D.host.E) : Prop :=
  letI := T.Q.H.starRing
  ∃ (o : SemisimplePairingSeparation.CMObj (T.Q.Dw j) T.Q.c) (d : ArcDatumAt T j o.K₁) (ψ : _) (ξ' : _) (χ₀ : _) (σ₁ : _),
    (⟨d.Wp, d.Y⟩ : Σ W : ValuationSubring ℂ, Model (T.Q.Xo j) T.Q.c (T.Q.c.V W).subtype) = ⟨Wp, Y⟩ ∧
    (∀ mu, SemisimplePairingSeparation.BuiltFrom n' La c₁ o { d with «μ» := mu } ψ ξ' χ₀) ∧
    SemisimplePairingSeparation.TiedAt D.host.AA (T.U j σ) k x ξ ν lam o d.a ψ ξ' χ₀ σ₁

variable {n' : ℕ} {La c₁ : ℝ} {Wp : ValuationSubring ℂ} {Y : Model (T.Q.Xo j) T.Q.c (T.Q.c.V Wp).subtype}
  {σ : T.Q.c.F →+* ℂ} {k : (T.U j σ).Comp} {x : ((T.U j σ).X k).dom} {ξ : Fin D.R.r → D.host.E}
  {ν : ((T.U j σ).X k).Ψ → ℝ} {lam : Fin (D.R.r - 2) → Fin D.R.r → D.host.E}

theorem hasMember_of_tied (hU : IsUnf (T.U j σ)) (h : MonomialNorms.HasTiedMember n' La c₁ Wp Y k x ξ ν lam) :
    HasMember n' La c₁ Wp Y k x ξ ν lam := by
  letI := T.Q.H.starRing
  obtain ⟨o, d, ξ₁, ν₁, φ₀, σ₁, e1, e2, hb, ht⟩ := h
  obtain ⟨ψ, χ₀, rfl, rfl, hb'⟩ := builtFrom_of_built hb
  exact ⟨o, d, ψ, ξ₁, χ₀, σ₁, Sigma.ext e1 e2, fun _ => hb',
    (tiedAt_iff hU ψ ξ₁ χ₀ σ₁ hb.1.2.2.2.2.1.1 hb.1.2.2.2.2.2.1.1).1 ht⟩

set_option maxHeartbeats 1600000 in
theorem tied_of_hasMember (h1 : Out.Laws) (h2 : Out.Laws2) (hU : IsUnf (T.U j σ))
    (h : HasMember n' La c₁ Wp Y k x ξ ν lam) : MonomialNorms.HasTiedMember n' La c₁ Wp Y k x ξ ν lam := by
  letI := T.Q.H.starRing
  obtain ⟨o, d, ψ, ξ₁, χ₀, σ₁, e, hb, ht⟩ := h
  have hb' : SemisimplePairingSeparation.BuiltFrom n' La c₁ o d ψ ξ₁ χ₀ := hb d.«μ»
  obtain ⟨x', φ, hb''⟩ := built_of_builtFrom h1 h2 hb'
  obtain ⟨e1, e2⟩ := Sigma.ext_iff.1 e
  have ht' := (tiedAt_iff hU ψ ξ₁ χ₀ σ₁ hb'.1.2.1.2.2.2.2.1.1 hb'.1.2.1.2.2.2.2.2.1.1).2 ht
  exact ⟨withFibre o x' φ, d, ξ₁, _, _, σ₁, e1, e2, hb'', ht'⟩

theorem cuspDataOn_iff : SemisimplePairingSeparation.CuspDataOn T j σ k n' La c₁ ξ x ν lam ↔
    GoodEmb T.Q.c σ ∧ ∃ Xx : DataX D.host.E D.R.r, MonomialNorms.IsComponentData k Xx ∧
      MonomialNorms.CuspGeom ((T.U j σ).X k) Xx.L' n' La ξ x.1 lam ∧ ∑ τ, ν τ ≤ c₁ ∧
      ∃ (la : Wt ((T.U j σ).X k).Ψ D.R.r) (P : Frame ((T.U j σ).X k).Ψ D.R.r → ℂ), P ∈ ((T.U j σ).X k).SS la ∧
        (∀ gm ∈ ((T.U j σ).X k).Γ, (∀ v ∈ ((T.U j σ).X k).Λ, ∃ w ∈ ((T.U j σ).X k).Λ,
          Matrix.mulVec (gm : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) v - v = (Xx.g : D.host.E) • w) →
          ((T.U j σ).X k).χ la gm = 1) ∧ ((T.U j σ).X k).fj la ξ ν P x.1 ≠ 0 := by
  refine and_congr Iff.rfl (exists_congr fun Xx => ⟨?_, ?_⟩)
  · rintro ⟨a1, a2, a3, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12⟩
    exact ⟨⟨a1, a2, a3⟩, ⟨b2, b3, b1, b5, b6, b7, b8, b9, b10, b11⟩, b4, a2 ▸ b12⟩
  · rintro ⟨⟨a1, a2, a3⟩, ⟨b2, b3, b1, b5, b6, b7, b8, b9, b10, b11⟩, b4, b12⟩
    exact ⟨a1, a2, a3, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, a2 ▸ b12⟩

theorem memberExists_of_existsMember (h : MonomialNorms.ExistsMemberOfCuspData) (D : D7) (T : Core D) (j : ℕ) :
    SemisimplePairingSeparation.MemberExists T j := by
  intro hT hj Wp Y hY σ k n' La c₁ ξ x ν lam hd
  obtain ⟨hσ, Xx, hX, hg, hc, la, P, hP, hχ, hne⟩ := cuspDataOn_iff.1 hd
  exact hasMember_of_tied (hT.unf j hj σ hσ) (h D T j hT hj Wp Y hY σ hσ k Xx hX n' La c₁ ξ x ν lam la P hP hχ hg hne hc)

theorem realized_of_memberExists (h1 : Out.Laws) (h2 : Out.Laws2)
    (h : ∀ (D : D7) (T : Core D) (j : ℕ), SemisimplePairingSeparation.MemberExists T j) : MonomialNorms.ExistsMemberOfCuspData := by
  intro D T j hT hj Wp Y hY σ hσ k Xx hX n' La c₁ ξ x ν lam la P hP hχ hg hne hc
  exact tied_of_hasMember h1 h2 (hT.unf j hj σ hσ)
    (h D T j hT hj Wp Y hY σ k n' La c₁ ξ x ν lam (cuspDataOn_iff.2 ⟨hσ, Xx, hX, hg, hc, la, P, hP, hχ, hne⟩))

theorem inputExists_of_memberExists
    (hY : LawsCore T → InR D j → ∃ (Wp : ValuationSubring ℂ) (Y : Model (T.Q.Xo j) T.Q.c (T.Q.c.V Wp).subtype), Y.N4)
    (h : SemisimplePairingSeparation.MemberExists T j) : SemisimplePairingSeparation.InputExists T j := by
  intro hT hj σ k n' La c₁ ξ x ν lam hd
  obtain ⟨Wp, Y, hN⟩ := hY hT hj
  obtain ⟨o, d, ψ, ξ', χ₀, σ₁, -, hb, ht⟩ := h hT hj Wp Y hN σ k n' La c₁ ξ x ν lam hd
  obtain ⟨b1, b2, -⟩ := hb d.«μ»
  exact ⟨o, d.a, d.th, d.jj, ψ, ξ', χ₀, σ₁, b1, ⟨d.e, b2⟩, ht⟩

def ModelsExist : Prop :=
  ∀ (D : D7) (T : Core D) (j : ℕ), LawsCore T → InR D j →
    ∃ (Wp : ValuationSubring ℂ) (Y : Model (T.Q.Xo j) T.Q.c (T.Q.c.V Wp).subtype), Y.N4

theorem modelsExist (hN : N1ab) (hP : PartI) : ModelsExist := by
  classical
  intro D T j hT hj
  have hr : 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q := by
    obtain ⟨hp, -⟩ := hT.pins.2.2.2 j hj
    have hk := D.R.m_add_three_le_k
    obtain ⟨h1, h2⟩ := hj
    rw [hp]
    simp only [Ranks.sigW]
    omega
  obtain ⟨XoF, hX⟩ : ∃ XoF : ∀ l' : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level T.Q.H, Moduli (T.Q.Dw j) l', XoF T.Q.l = T.Q.Xo j :=
    ⟨fun l' => if h : l' = T.Q.l then h ▸ T.Q.Xo j else Classical.choice (hN _ _ _ l' hr), by simp⟩
  obtain ⟨Y, hY, -⟩ := hP.2 _ _ _ hr XoF
  have hne : (Ideal.span {((2 : ℕ) : (⊥ : Subring ℂ))}) ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    intro hu
    obtain ⟨v, hv⟩ := hu.exists_right_inv
    obtain ⟨n, hn⟩ := Subring.mem_bot.1 v.2
    have h1 : (((2 : ℕ) : ℤ) * n : ℤ) = 1 := by
      have := congrArg Subtype.val hv
      simp only [Subring.coe_mul, Subring.coe_natCast, Subring.coe_one] at this
      rw [← hn] at this
      exact_mod_cast this
    omega
  obtain ⟨W, -, hW⟩ := Ideal.image_subset_nonunits_valuationSubring _ hne
  have hW' : ((2 : ℕ) : ℂ) ∈ W.nonunits := hW ⟨(2 : ℕ), Ideal.mem_span_singleton_self _, map_natCast (⊥ : Subring ℂ).subtype 2⟩
  have hg : T.Q.l.GoodAt 2 := by
    unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level.GoodAt
    rw [Nat.factorization_eq_zero_of_not_dvd (Nat.two_dvd_ne_zero.2 (Nat.odd_iff.1 T.Q.l.odd)), pow_zero, Nat.div_one]
    exact T.Q.l.three_le
  rw [← hX]
  exact ⟨W, Y 2 W Nat.prime_two hW' ⟨T.Q.l, T.Q.c, hg⟩, ((hY 2 W Nat.prime_two hW').2 _).2.2⟩

end Claims

theorem main (h1 : Out.Laws) (h2 : Out.Laws2) :
    (∀ (D : D7) (T : Core D) (j n' : ℕ) (La c₁ : ℝ) (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra T.Q.c.F K₁]
      (d : ArcDatumAt T j K₁), MonomialNorms.InFamily T j n' La c₁ K₁ d ↔ SemisimplePairingSeparation.InFam n' La c₁ d) ∧
    (∀ (D : D7) (T : Core D) (j n' : ℕ) (La c₁ : ℝ) (Wp : ValuationSubring ℂ)
      (Y : Model (T.Q.Xo j) T.Q.c (T.Q.c.V Wp).subtype) (σ : T.Q.c.F →+* ℂ) (k : (T.U j σ).Comp)
      (x : ((T.U j σ).X k).dom) (ξ : Fin D.R.r → D.host.E) (ν : ((T.U j σ).X k).Ψ → ℝ)
      (lam : Fin (D.R.r - 2) → Fin D.R.r → D.host.E), IsUnf (T.U j σ) →
      (MonomialNorms.HasTiedMember n' La c₁ Wp Y k x ξ ν lam ↔ HasMember n' La c₁ Wp Y k x ξ ν lam)) ∧
    (MonomialNorms.ExistsMemberOfCuspData ↔ ∀ (D : D7) (T : Core D) (j : ℕ), SemisimplePairingSeparation.MemberExists T j) ∧
    (SemisimplePairingSeparation.CuspFamilySt → MonomialNorms.ExistsMemberOfCuspData) ∧
    (N1ab → PartI → (MonomialNorms.ExistsMemberOfCuspData ↔ SemisimplePairingSeparation.CuspFamilySt)) ∧
    (N1ab → PartI → MonomialNorms.SupportSt → MonomialNorms.ExistsMemberSt → SemisimplePairingSeparation.CuspFamilySt) := by
  have a : SemisimplePairingSeparation.CuspFamilySt → MonomialNorms.ExistsMemberOfCuspData := fun h =>
    realized_of_memberExists h1 h2 fun D T j => (h D T j).2
  have b : ModelsExist → MonomialNorms.ExistsMemberOfCuspData → SemisimplePairingSeparation.CuspFamilySt := fun hY h D T j =>
    ⟨inputExists_of_memberExists (hY D T j) (memberExists_of_existsMember h D T j), memberExists_of_existsMember h D T j⟩
  exact ⟨fun _ _ _ _ _ _ K₁ _ _ _ d => inFamily_iff h1 h2 K₁ d,
    fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ hU => ⟨hasMember_of_tied hU, tied_of_hasMember h1 h2 hU⟩,
    ⟨memberExists_of_existsMember, realized_of_memberExists h1 h2⟩, a, fun hN hP => ⟨b (modelsExist hN hP), a⟩,
    fun hN hP hs h => b (modelsExist hN hP) (MonomialNorms.realized_of h hs)⟩

end GlobalTheory.CuspFamilyCompare
