import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SysExOfPol
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsLocalExtension
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabDescentOfFieldExtension
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LineBundleIsoOfAmpleDeterminantFrames
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.ValuationFormPsiBalancedSymmetricPeriodForm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsProperSemiAbelianTripleOfAbelianLocusEqUniv
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorRef

section Form

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_periodForm {W : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [CharZero W]
    [IsAdicComplete (maximalIdeal W) W] {t : SAB H (Sp W)}
    (P : PELUnif (maximalIdeal W) t) {ϖ : W} (hϖ : Irreducible ϖ) :
    ∃ be ∈ levelForms H 1 P.D.toPre.X, IsMonomial P.D.toPre ![ϖ] ![be] ∧ ∀ y, y ≠ 0 → 0 < be y y := by
  letI := H.starRing
  choose Q hQ using QForm.exists_QVal hϖ P.D
  have hQ' : QForm.IsQ P.D.toPre ϖ Q := hQ
  have hex : ∀ χ, ∃ r, PsiCoord P.D.toPre χ r := fun χ =>
    ((GlobalTheory.PsiCoordLocal.main W P.D inferInstance χ).1).imp fun _ h => h.1
  have h0 : ∀ a, 0 ≤ Q a := fun a => by
    by_cases ha : a = 0
    · rw [ha, QForm.Q_zero hϖ P.D hQ']
    · exact zero_le_one.trans (QForm.Q_pos hϖ P.D hQ' ha)
  let be : LinearMap.BilinForm ℤ P.D.toPre.X :=
    LinearMap.mk₂ ℤ (fun a b => QForm.bHom hϖ P.D hQ' a b)
      (fun a a' b => by simp only [map_add, AddMonoidHom.add_apply])
      (fun c a b => by simp only [map_zsmul, AddMonoidHom.smul_apply, smul_eq_mul, zsmul_eq_mul, Int.cast_id])
      (fun a b b' => by simp only [map_add])
      (fun c a b => by simp only [map_zsmul, smul_eq_mul, zsmul_eq_mul, Int.cast_id])
  have hbe : ∀ a b, be a b = QForm.bOf P.D.toPre Q a b := fun _ _ => rfl
  refine ⟨be, ⟨fun a b => ?_, fun x a b => ?_, fun a b => ?_⟩, fun y => ?_, fun y hy => ?_⟩
  · rw [hbe, hbe, QForm.bOf_comm]
  · rw [hbe, hbe]
    exact QForm.bOf_balance hϖ P.D GlobalTheory.allSixLaws.1 P.oD hQ' x a b
  · simp
  · obtain ⟨r, hr⟩ := hex y
    obtain ⟨u, hu⟩ := GlobalTheory.ValForm.hasVal_coord (hQ y) hr
    obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (h0 y)
    rw [hn, zpow_natCast, ← map_pow, ← map_mul] at hu
    have e : r = u * ϖ ^ n := (IsFractionRing.injective W (FractionRing W) hu).trans (_root_.mul_comm _ _)
    refine ⟨u, fun _ => n, fun i => ?_, ?_⟩
    · have : i = 0 := Subsingleton.elim _ _
      subst this
      show be y y = _
      rw [hbe, ← QForm.two_Q_eq hϖ P.D hQ', hn]
    · simpa [e] using hr
  · rw [hbe, ← QForm.two_Q_eq hϖ P.D hQ']
    have := QForm.Q_pos hϖ P.D hQ' hy
    omega

end Form

theorem mem_support_iff_of_idlAlong {X : Scheme.{0}} (J : X.IdealSheafData) {W : Type} [CommRing W] [IsDomain W]
    [IsLocalRing W] (χ : Sp W ⟶ X) {ϖ : W} (hϖ : Irreducible ϖ) {n : ℕ} (h : idlAlong J χ = Ideal.span {ϖ ^ n}) :
    χ (closedPoint W : Sp W) ∈ J.support ↔ n ≠ 0 := by
  refine (mem_support_iff_stalkId J _).trans (not_congr ?_)
  unfold idlAlong at h
  constructor
  · intro hne
    rw [hne, Ideal.map_top] at h
    have hu : IsUnit (ϖ ^ n) := Ideal.span_singleton_eq_top.1 h.symm
    by_contra hn
    exact hϖ.not_isUnit ((isUnit_pow_iff hn).1 hu)
  · rintro rfl
    by_contra hne
    rw [pow_zero, Ideal.span_singleton_one] at h
    have hle : (FinalTheorems.stalkId J (χ (closedPoint W : Sp W))).map (Scheme.stalkClosedPointTo χ).hom ≤ maximalIdeal W := by
      rw [Ideal.map_le_iff_le_comap]
      intro a ha hua
      have : IsUnit a := isUnit_of_map_unit (Scheme.stalkClosedPointTo χ).hom a hua
      exact hne (Ideal.eq_top_of_isUnit_mem _ ha this)
    rw [h] at hle
    exact (maximalIdeal.isMaximal W).ne_top (top_le_iff.1 hle)

section Trait

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_unif_ext (T : CDVR) (t : SAB H (Sp T.V)) (hp : PolAt t (jK T.V)) :
    ∃ (T' : CDVR) (φ : T.V →+* T'.V) (t' : SAB H (Sp T'.V)), Function.Injective φ ∧ IsLocalHom φ ∧
      Nonempty (SABMap t' t (spMap φ)) ∧ Nonempty (PELUnif (maximalIdeal T'.V) t') := by
  let F := AlgebraicClosure (FractionRing T.V)
  have hF : Function.Injective (algebraMap T.V F) := by
    rw [IsScalarTower.algebraMap_eq T.V (FractionRing T.V) F]
    exact (algebraMap (FractionRing T.V) F).injective.comp (IsFractionRing.injective T.V _)
  have : FaithfulSMul T.V F := (faithfulSMul_iff_algebraMap_injective _ _).2 hF
  have : Algebra.IsAlgebraic T.V F := (IsFractionRing.comap_isAlgebraic_iff (K := FractionRing T.V)).2 inferInstance
  obtain ⟨W, hd, hc, hf, hs⟩ := GlobalTheory.Ex.UnifModel.exists_split T.V F t.G t.semi
  have hi : Function.Injective (algebraMap T.V W) := fun _ _ h => hF (congrArg (fun z : W => (z : F)) h)
  have hz : CharZero W := charZero_of_injective_ringHom hi
  have : FaithfulSMul T.V W := (faithfulSMul_iff_algebraMap_injective _ _).2 hi
  have hl : IsLocalHom (algebraMap T.V W) := inferInstance
  obtain ⟨PP', cub, sym, adj, prim, m, -⟩ := sabPull CubePf.cubePull (spMap (algebraMap T.V W)) t
  have j : Function.Injective ((algebraMap W (FractionRing W)).comp (algebraMap T.V W)) :=
    (IsFractionRing.injective W _).comp hi
  let g : FractionRing T.V →+* FractionRing W := IsFractionRing.lift j
  have hp' := GlobalTheory.DatUniq.polAt_pull m hp (jK W) (spMap g)
    ((GlobalTheory.Ex.UnifModel.spMap_comp (IsFractionRing.lift_algebraMap j)).trans
      (GlobalTheory.Ex.UnifModel.spMap_comp fun _ => rfl).symm)
  obtain ⟨P, -⟩ := GlobalTheory.LN.uDvrSt_holds E H W ⟨hd, hc, hz⟩ _ hp' hs
  exact ⟨{ V := W }, algebraMap T.V W, _, hi, hl, ⟨m⟩, ⟨P⟩⟩

theorem closed_mem_abLocus_iff (T : CDVR) {t : SAB H (Sp T.V)} (P : PELUnif (maximalIdeal T.V) t) :
    (closedPoint T.V : Sp T.V) ∈ abLocus t.G ↔ Subsingleton P.D.toPre.X := by
  constructor
  · intro hc
    have hmax : (maximalIdeal T.V ^ (0 + 1)).IsMaximal := by
      rw [zero_add, pow_one]; infer_instance
    have hF : IsField (T.V ⧸ maximalIdeal T.V ^ (0 + 1)) := (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).1 hmax
    have hle : maximalIdeal T.V ^ (0 + 1) ≤ (closedPoint T.V).asIdeal := by
      rw [zero_add, pow_one]; exact le_rfl
    obtain ⟨q, hq⟩ : closedPoint T.V ∈ Set.range (PrimeSpectrum.comap
        (Ideal.Quotient.mk (maximalIdeal T.V ^ (0 + 1)))) := by
      rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]
      exact hle
    let g := P.U.gt 0
    have m : Mono g.i := ⟨fun a b h => g.isKernel.hom_ext h (toUnit_unique _ _)⟩
    have hq' : thick T.V (maximalIdeal T.V) 0 q ∈ abLocus t.G := by
      rw [← hq] at hc; exact hc
    exact ArcNotAbelian.subsingleton_of_mem_abLocus t.G t.semi _ hF _ q hq' P.D.toPre.X g.i g.i_hom
  · intro hs K _ _ s _
    have := (isAbelianScheme_of_unif_of_subsingleton GlobalTheory.allSixLaws.1 GlobalTheory.allSixLaws.2.1 T.V T.cpl P.D P.A t.G t.semi
      P.U hs).proper
    infer_instance

variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

theorem charZero_of_point {K : CommRingCat.{0}} [Nontrivial K] (y : Spec K ⟶ Xo.XF c) : CharZero K := by
  let f := Spec.preimage (y ≫ pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom))
  exact charZero_of_injective_ringHom f.hom.injective

open GlobalTheory.HomExt in

theorem exists_base_trait (Z : Model Xo c β) (hβ : IsDedFrac β) (x : Z.X) :
    ∃ (T : CDVR) (χ : Sp T.V ⟶ Z.X) (y : Sp (FractionRing T.V) ⟶ Xo.XF c),
      χ (closedPoint T.V : Sp T.V) = x ∧ y ≫ Z.j = jK T.V ≫ χ := by
  by_cases hx : x ∈ Set.range Z.j
  · obtain ⟨u, rfl⟩ := hx
    let K := (Xo.XF c).residueField u
    have : CharZero K := charZero_of_point ((Xo.XF c).fromSpecResidueField u)
    obtain ⟨h₁, h₂, h₃⟩ := (GlobalTheory.FrameCmp.cDvr_powerSeries K : CDvr (PowerSeries K))
    let a : Sp (PowerSeries K) ⟶ Xo.XF c := spMap (PowerSeries.C (R := K)) ≫ (Xo.XF c).fromSpecResidueField u
    refine ⟨{ V := PowerSeries K }, a ≫ Z.j, jK _ ≫ a, ?_, Category.assoc _ _ _⟩
    exact (Scheme.Hom.comp_apply a Z.j _).trans (congrArg Z.j ((Scheme.Hom.comp_apply _ _ _).trans
      (Scheme.fromSpecResidueField_apply u _)))
  · obtain ⟨h₁, -, -, _, _, _, _⟩ := GlobalTheory.ModelRelCompare.densePart Z hβ
    obtain ⟨ξ, hξ, hs⟩ := exists_mem_genericPoints_specializes x
    have hξ' := genericPoints_subset_range_of_isDominant Z.j hξ
    have hne : ξ ≠ x := fun e => hx (e ▸ hξ')
    obtain ⟨W, _, _, _, a, h₀, h₁⟩ := exists_complete_discreteValuationRing_of_specializes hs hne
    obtain ⟨y, hy⟩ := exists_lift_of_range_subset Z.j
      (spMap (algebraMap W (FractionRing W)) ≫ a) (by
        rintro _ ⟨t, rfl⟩
        have : spMap (algebraMap W (FractionRing W)) t = (⊥ : PrimeSpectrum W) := by
          apply PrimeSpectrum.ext
          change Ideal.comap (algebraMap W (FractionRing W)) t.asIdeal = ⊥
          rw [@Ideal.eq_bot_of_prime _ _ t.asIdeal t.isPrime]
          exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective _ _)
        rw [Scheme.Hom.comp_apply, this]
        exact h₀ ▸ hξ')
    have hc : CharZero (FractionRing W) := charZero_of_point (K := .of (FractionRing W)) y
    have hc' : CharZero W := ⟨fun p q e => Nat.cast_injective (R := FractionRing W) (by
      simpa using congrArg (algebraMap W (FractionRing W)) e)⟩
    exact ⟨{ V := W }, a, y, h₁, hy⟩

theorem exists_trait (Z : Model Xo c β) (hβ : IsDedFrac β) (x : Z.X) :
    ∃ (T : CDVR) (χ : Sp T.V ⟶ Z.X) (t : SAB H (Sp T.V)) (_ : SABMap t Z.t χ) (_ : PELUnif (maximalIdeal T.V) t),
      χ (closedPoint T.V : Sp T.V) = x ∧ Set.range (jK T.V ≫ χ) ⊆ Set.range Z.j := by
  obtain ⟨T, χ, y, hx, hy⟩ := exists_base_trait Z hβ x
  obtain ⟨_, _, _, _, _, m, -⟩ := sabPull CubePf.cubePull χ Z.t
  have hp := GlobalTheory.GoodTrait.polAt_of_point Z m (jK T.V) y hy
  obtain ⟨T', φ, t', hi, hl, ⟨m'⟩, ⟨P⟩⟩ := exists_unif_ext T _ hp
  obtain ⟨n, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m m'
  have j : Function.Injective ((algebraMap T'.V (FractionRing T'.V)).comp φ) :=
    (IsFractionRing.injective T'.V _).comp hi
  let g : FractionRing T.V →+* FractionRing T'.V := IsFractionRing.lift j
  have e : jK T'.V ≫ spMap φ = spMap g ≫ jK T.V :=
    (GlobalTheory.Ex.UnifModel.spMap_comp fun _ => rfl).trans
      (GlobalTheory.Ex.UnifModel.spMap_comp (IsFractionRing.lift_algebraMap j)).symm
  refine ⟨T', spMap φ ≫ χ, t', n, P, ?_, ?_⟩
  · exact (Scheme.Hom.comp_apply (spMap φ) χ _).trans ((congrArg χ (comap_closedPoint φ)).trans hx)
  · rintro _ ⟨p, rfl⟩
    refine ⟨(spMap g ≫ y) p, ?_⟩
    rw [← Scheme.Hom.comp_apply, Category.assoc, hy, ← Category.assoc, ← e, Category.assoc]

end Trait

theorem polSuppSt : PolSuppSt := by
  intro E _ _ _ H D l Xo c O _ β Z BD φ hβ hpos hdiv x
  obtain ⟨T, χ, t, m, P, rfl, hr⟩ := exists_trait Z hβ x
  have hW : CDvr T.V := ⟨T.dvr, T.cpl, T.ch0⟩
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible T.V
  obtain ⟨be, hbe, hmon, hpd⟩ := exists_periodForm P hϖ
  obtain ⟨n, hn, hid⟩ := hdiv T.V hW ϖ hϖ χ t m P hr be hbe hmon
  refine (mem_support_iff_of_idlAlong BD.idealSheaf χ hϖ hid).trans ?_
  refine Iff.trans ?_ (not_congr (abLocus_pullback abLocusOne Z.t.semi m.cart.1 _)).symm
  refine Iff.trans ?_ (not_congr (closed_mem_abLocus_iff T P)).symm
  constructor
  · intro hn0 hs
    apply hn0
    have h0 : φ.evalZ be = 0 := φ.eval_of_subsingleton _
    rw [h0] at hn
    exact_mod_cast hn
  · intro hs hn0
    have hnt : Nontrivial P.D.toPre.X := not_subsingleton_iff_nontrivial.1 hs
    have := hpos P.D.toPre.X be hbe hpd
    rw [← hn, hn0] at this
    simp at this

end GlobalTheory.TorRef
