import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorsExt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtIffOfSpecializes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryTraitLabelsSurjectiveKernel
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorusTorsionPointStandardAlternatingForm
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLabelMapTorsionCharacters
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LineBundleSymmetryHypothesisBaseChange
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAdaptedBasisTestLattice
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsMulPowMemOOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UTorsClosed
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianHomExtensionHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGrpPullbackGenMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndCharExistsOfIsMonHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLabOntoAndKer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BetaPos
import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftValuationSubring
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AssociatedPsiCoordinatesOfTauUnits
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreIsoSpecialisesToFieldPoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDvrFactorPointPadicAlgClosure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeOfUniformisationEqModelLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonPullbackSemiAbelianDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabelCongruenceEndoAllAlgClosedFields
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormTauLineBundleCoordinateEqExpStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.FibLat
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
open GlobalTheory.Poinc.Eq8 GlobalTheory.TorusPart GlobalTheory.ZM GlobalTheory.SiegelTor

noncomputable section

namespace GlobalTheory.UPoinc.GFibCentre

theorem exists_endo_pull {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {G' : Over S'} [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (w : G ⟶ G) (hw : IsMonHom w) :
    ∃ w' : G' ⟶ G', IsMonHom w' ∧ w'.left ≫ φ = φ ≫ w.left := by
  obtain ⟨w', hw', pa⟩ := GlobalTheory.SymBaseChange.exists_endo h w
  refine ⟨w', hw', ?_⟩
  have := congrArg (fun z => z.left) (pa (𝟙 _))
  simpa [pushPt] using this

theorem exists_unit_pow_eq {o : Type} [CommRing o] [IsDomain o] {L : ℕ} (hL : 0 < L) {ζ ξ : o}
    (hζ : IsPrimitiveRoot ζ L) (hξ : IsPrimitiveRoot ξ L) : ∃ k : ZMod L, IsUnit k ∧ ζ ^ k.val = ξ := by
  haveI : NeZero L := ⟨hL.ne'⟩
  obtain ⟨i, hi, rfl⟩ := hζ.eq_pow_of_pow_eq_one hξ.pow_eq_one
  refine ⟨i, (ZMod.isUnit_iff_coprime i L).2 ((hζ.pow_iff_coprime hL i).1 hξ), ?_⟩
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt hi]

theorem latAt_rescale {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M : RatModel o Ω} {G : Over M.Z} [GrpObj G]
    {I T : Type} {f : I → (G ⟶ G)} {gγ : T → (Over.mk M.pt ⟶ G)} {L : ℕ} {X : Type} [AddCommGroup X]
    {m : I → X →+ X} {c : T → X →+ ZMod L} {w : M.Z} (ζ : oˣ) (hζ : ζ ^ L = 1) (k : ZMod L)
    (h : LatAt f gγ (ζ ^ k.val) L m c w) :
    LatAt f gγ ζ L m (fun t => (AddMonoidHom.mulLeft k).comp (c t)) w := by
  obtain ⟨κ, _, s, a, G₀, _, φ, tι, h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨κ, _, s, a, G₀, _, φ, tι, h1, h2, h3, h4, h5, fun t => ?_⟩
  obtain ⟨z, hz, hv⟩ := h6 t
  refine ⟨z, fun χ => (hz χ).trans (congrArg unitOn ?_), hv⟩
  have hu : (Units.map a.toMonoidHom ζ) ^ L = 1 := by rw [← map_pow, hζ, map_one]
  show _ = Units.map a.toMonoidHom ζ ^ (k * c t χ).val
  rw [map_pow, ← pow_mul, ZMod.val_mul, ← pow_eq_pow_mod _ hu]

theorem ratHull_le_O_of_point {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) {K : Type} [Field K]
    [CharZero K] (s : Sp K ⟶ M.Z) (R : Subalgebra o Ω) (h : R ≤ M.O (s (closedPoint K))) :
    ratHull R ≤ M.O (s (closedPoint K)) := by
  intro x hx
  obtain ⟨n, hn, hnx⟩ := mem_ratHull.1 hx
  have hu : IsUnit (n : M.O (s (closedPoint K))) := by
    rw [← RatModel.isUnit_valLoc_iff s rfl, map_intCast]
    exact IsUnit.mk0 _ (Int.cast_ne_zero.2 hn)
  obtain ⟨h1, h2⟩ := (RatModel.isUnit_O_iff _).1 hu
  have e : ((n : M.O (s (closedPoint K))) : Ω) = n := by simp
  rw [e] at h1 h2
  have := mul_mem h2 (h hnx)
  rwa [inv_mul_cancel_left₀ h1] at this

theorem sc_ne_zero {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}
    {Xo : Moduli D l} {cf : Coeff l} {C : UCompact Xo cf} {X : USetup C} {p : ℕ} [Fact p.Prime] {z : X.M.Z}
    (ct : UCTrait X p z) : ct.sc ≠ 0 := by
  have h0 : algebraMap ct.T.V (FractionRing ct.T.V) ct.T.ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective ct.T.V (FractionRing ct.T.V))).2 ct.T.irr.ne_zero
  have h1 : ‖ct.ι (algebraMap ct.T.V (FractionRing ct.T.V) ct.T.ϖ)‖ < 1 := by
    by_contra hge
    have h2 : ‖ct.ι ((algebraMap ct.T.V (FractionRing ct.T.V) ct.T.ϖ)⁻¹)‖ ≤ 1 := by
      rw [map_inv₀, norm_inv]
      exact inv_le_one_of_one_le₀ (not_lt.1 hge)
    obtain ⟨v, hv⟩ := (ct.int _).1 h2
    refine ct.T.irr.not_isUnit (IsUnit.of_mul_eq_one v (IsFractionRing.injective ct.T.V (FractionRing ct.T.V) ?_))
    rw [map_mul, hv, map_one, mul_inv_cancel₀ h0]
  exact neg_ne_zero.2 (Real.log_neg (norm_pos_iff.2 ((map_ne_zero ct.ι).2 h0)) h1).ne

theorem exists_factor_pull {S S' S'' : Scheme.{0}} {A : Over S} [GrpObj A] {B : Over S'} [GrpObj B] {A' : Over S''}
    [GrpObj A'] {f : S' ⟶ S} {g : S'' ⟶ S'} {h : S'' ⟶ S} {α : B.left ⟶ A.left} {φ : A'.left ⟶ A.left}
    (hα : IsGrpPullback B A f α) (hφ : IsGrpPullback A' A h φ) (e : g ≫ f = h) :
    ∃ ψ : A'.left ⟶ B.left, IsGrpPullback A' B g ψ ∧ ψ ≫ α = φ := by
  have w : φ ≫ A.hom = (A'.hom ≫ g) ≫ f := by rw [Category.assoc, e]; exact hφ.1.w
  exact ⟨hα.1.lift _ _ w, hα.cancel (hφ.congr e.symm (hα.1.lift_fst _ _ w).symm) (hα.1.lift_snd _ _ w),
    hα.1.lift_fst _ _ w⟩

theorem comp_hom_eq_id {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {R : Subalgebra o Ω}
    (frac : ∀ x : Ω, ∃ a ∈ R, ∃ b ∈ R, x = a / b) {A : Over (Sp R)} [GrpObj A] {A₀ : Over (Sp Ω)} [GrpObj A₀]
    {α : A₀.left ⟶ A.left} (hα : IsGrpPullback A₀ A (spMap R.val.toRingHom) α) (b : baseOver (Sp R) ⟶ A)
    (w : Sp Ω ⟶ A₀.left) (hw : w ≫ α = spMap R.val.toRingHom ≫ b.left) : w ≫ A₀.hom = 𝟙 _ := by
  obtain ⟨σ, hσ⟩ := exists_spMap (w ≫ A₀.hom)
  have e₁ : σ.comp R.val.toRingHom = R.val.toRingHom := ringHom_eq_of_spMap (by
    rw [← spMap_comp', ← hσ, Category.assoc, ← hα.1.w, ← Category.assoc, hw, Category.assoc, Over.w]
    exact Category.comp_id _)
  have e₂ : σ = RingHom.id _ := RingHom.ext fun x => by
    obtain ⟨a, ha, b, hb, rfl⟩ := frac x
    rw [map_div₀, show σ a = a from DFunLike.congr_fun e₁ ⟨a, ha⟩, show σ b = b from DFunLike.congr_fun e₁ ⟨b, hb⟩]
    rfl
  rw [hσ, e₂]
  exact Spec.map_id _

theorem exists_ratLift_val {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] [CharZero Ω] (M : RatModel o Ω) {K K' : Type}
    [Field K] [Field K'] [CharZero K'] (κ : K →+* K') (s : Sp K' ⟶ M.Z) (R : Subalgebra o Ω)
    (h : ratHull R ≤ M.O (s (closedPoint K'))) (yK : R →+* K) (hy : ∀ x : R, κ (yK x) = M.val s x) :
    ∃ y₁ : ratHull R →+* K, y₁.comp (toRat R) = yK ∧ ∀ x : ratHull R, κ (y₁ x) = M.val s x := by
  haveI : CharZero K := RingHom.charZero κ
  obtain ⟨y₁, hy₁, -⟩ := existsUnique_ratLift R (K := K) (fun n hn => IsUnit.mk0 _ (Int.cast_ne_zero.2 hn)) yK
  refine ⟨y₁, hy₁, fun x => ?_⟩
  obtain ⟨n, hn, hx⟩ := mem_ratHull.1 x.2
  have e₁ : toRat R ⟨_, hx⟩ = (n : ratHull R) * x := Subtype.ext (by simp)
  have e₂ : κ (yK ⟨_, hx⟩) = n * κ (y₁ x) := by
    rw [← hy₁, RingHom.comp_apply, e₁, map_mul, map_mul, map_intCast, map_intCast]
  have e₃ : (⟨(n : Ω) * x, h (le_ratHull R hx)⟩ : M.O (s (closedPoint K'))) = n * ⟨x, h x.2⟩ := Subtype.ext (by simp)
  have e₄ := RatModel.valLoc_eq_val s (specializes_refl _) ⟨(n : Ω) * x, h (le_ratHull R hx)⟩
  have e₅ := RatModel.valLoc_eq_val s (specializes_refl _) ⟨(x : Ω), h x.2⟩
  refine mul_left_cancel₀ (Int.cast_ne_zero.2 hn : (n : K') ≠ 0) ?_
  rw [← e₂, hy]
  refine e₄.symm.trans ?_
  rw [e₃, map_mul, map_intCast, e₅]

theorem char_eq_bar_smul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (X₀ : Type) [AddCommGroup X₀] [Module (𝓞 E) X₀] (be : LinearMap.BilinForm ℤ X₀), be ∈ levelForms H 1 X₀ → ∀ sc : ℝ, sc ≠ 0 → ∀ j : u.D.toPre.X ≃+ X₀, (∀ χ, l.q χ = sc * (be (j χ) (j χ) : ℝ) / 2) → ∀ (a : 𝓞 E) (eA : u.A.A ⟶ u.A.A), (∀ (m : ℕ) (pk pk' : QkPt u.D.toPre (PadicAlgCl p) m) (x x' : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A), 1 ≤ m → QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk x → QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk' x' → x'.left = x.left ≫ eA.left → CongMod m (j pk'.y) (a • j pk.y)) → ∀ (F : u.G ⟶ u.G), IsMonHom F → eA.left ≫ genMap u.U = genMap u.U ≫ F.left → ∀ m : u.D.toPre.X →+ u.D.toPre.X, EndChar u.U F m → ∀ χ, j (m χ) = H.bar a • j χ := by
  intro E _ _ _ H o Ω _ _ _ S ρ p _ y₀ u l X₀ _ _ be hbe sc hsc j hq a eA hlab F hF hgen m hm χ
  have hCZ : CharZero u.V :=
    RingHom.charZero ((algebraMap (FractionRing u.V) (PadicAlgCl p)).comp (algebraMap u.V (FractionRing u.V)))
  have hBase : GlobalTheory.Mum.Base u.V := ⟨⟨inferInstance, inferInstance, inferInstance, u.complete⟩, hCZ⟩
  let s : u.D.toPre.X →+ u.D.toPre.X :=
    (j.symm.toAddMonoidHom.comp (DistribSMul.toAddMonoidHom X₀ a)).comp j.toAddMonoidHom
  have hs : ∀ x, j (s x) = a • j x := fun x => j.apply_symm_apply _
  have hlab' : ∀ (k : ℕ) (pk pk' : QkPt u.D.toPre (PadicAlgCl p) k) (x x' : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A),
      1 ≤ k → QkToAkU u.U.toUnifPre (PadicAlgCl p) k pk x → QkToAkU u.U.toUnifPre (PadicAlgCl p) k pk' x' →
      x'.left = x.left ≫ eA.left → CongMod k pk'.y (s pk.y) := by
    intro k pk pk' x x' hk hx hx' hxx
    obtain ⟨w, hw⟩ := hlab k pk pk' x x' hk hx hx' hxx
    refine ⟨j.symm w, j.injective ?_⟩
    rw [map_add, map_nsmul, AddEquiv.apply_symm_apply, hs, hw]
  have hT := GlobalTheory.LabelTransfer.main o Ω S ρ p y₀ u eA s hlab'
  haveI : Mono (jK u.V) := GlobalTheory.PolDeg.Wit.mono_jK
  haveI : Mono (genMap u.U) := by unfold genMap; infer_instance
  have hTor := GlobalTheory.Poinc.TorEnd.torMatch_of_endChar u.V hBase u.G u.semi u.D u.A u.U F hF m hm
  have hmain := GlobalTheory.TauFormHom.main u.V hBase inferInstance u.G u.semi u.D u.A u.U u.G u.semi u.D u.A u.U F hF m s hTor
    (by
      intro F' _ _ _ k hk q q' a a' hqa hqa' haa
      have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.2 (by rintro rfl; simp at hk)
      have ha : a.left = a'.left ≫ eA.left := by
        rw [← cancel_mono (genMap u.U), haa, Category.assoc, hgen]
      exact hT F' k hk1 hk q q' a a' hqa hqa' ha)
  have hunit : ∀ w : u.Vˣ, ‖algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V _ (w : u.V))‖ = 1 := by
    intro w
    have h1 := (u.norm_le (algebraMap u.V _ (w : u.V))).2 ⟨w, rfl⟩
    have h2 := (u.norm_le (algebraMap u.V _ ((w⁻¹ : u.Vˣ) : u.V))).2 ⟨_, rfl⟩
    have h3 : ‖algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V _ (w : u.V))‖ *
        ‖algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V _ ((w⁻¹ : u.Vˣ) : u.V))‖ = 1 := by
      rw [← norm_mul, ← map_mul, ← map_mul, Units.mul_inv, map_one, map_one, norm_one]
    have h4 := norm_nonneg (algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V _ ((w⁻¹ : u.Vˣ) : u.V)))
    have h5 := norm_nonneg (algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V _ (w : u.V)))
    nlinarith
  have hpol : ∀ a' b, l.q (s a' + b) - l.q (s a') - l.q b = l.q (a' + m b) - l.q a' - l.q (m b) := by
    intro a' b
    obtain ⟨x, hx⟩ := GlobalTheory.PsiFromTau.exists_isTauCoord u.V u.D.toPre (s a') b
    obtain ⟨x', hx'⟩ := GlobalTheory.PsiFromTau.exists_isTauCoord u.V u.D.toPre a' (m b)
    obtain ⟨w, hw⟩ := hmain a' b x x' hx hx'
    have n₁ := GlobalTheory.T.norm_tauLineBundleCoordinate_eq_exp o Ω S ρ p y₀ u l (s a') b x hx
    have n₂ := GlobalTheory.T.norm_tauLineBundleCoordinate_eq_exp o Ω S ρ p y₀ u l a' (m b) x' hx'
    rw [hw, map_mul, norm_mul, hunit, _root_.one_mul, n₂] at n₁
    have := Real.exp_injective n₁
    linarith
  have hadj : ∀ y : X₀, be y (j (m χ) - H.bar a • j χ) = 0 := by
    intro y
    have h := hpol (j.symm y) χ
    rw [hq, hq, hq, hq, hq, hq, map_add, map_add, hs, AddEquiv.apply_symm_apply] at h
    simp only [map_add, LinearMap.add_apply, AddEquiv.apply_symm_apply] at h
    rw [hbe.1 (j χ) (a • y), hbe.1 (j (m χ)) y, hbe.2.1 a y (j χ)] at h
    push_cast at h
    have h' : sc * (be y (j (m χ)) : ℝ) = sc * (be y (H.bar a • j χ) : ℝ) := by linarith
    rw [map_sub, sub_eq_zero]
    exact_mod_cast mul_left_cancel₀ hsc h'
  by_contra hne
  have hw0 : j.symm (j (m χ) - H.bar a • j χ) ≠ 0 := fun h => hne (sub_eq_zero.1 (j.symm.map_eq_zero_iff.1 h))
  have hfin : {x | ¬ (1 : ℝ) ≤ l.q x}.Finite := Filter.eventually_cofinite.1 (l.pos.eventually_ge_atTop 1)
  refine Set.infinite_of_injective_forall_mem (f := fun n : ℤ => n • j.symm (j (m χ) - H.bar a • j χ))
    (smul_left_injective ℤ hw0) (fun n => ?_) hfin
  show ¬ (1 : ℝ) ≤ l.q _
  rw [hq, map_zsmul, j.apply_symm_apply, map_zsmul (be _), hadj]
  norm_num

theorem latAt_of_uTest_over : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (Y : RatModel o Ω), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Y.Z → ∀ (G : Over Y.Z) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (R₁ : Subalgebra o Ω) (hR₁ : S.R ≤ R₁) (B : Over (Sp R₁)) [GrpObj B], IsSemiAbelian B → ∀ (bB : B.left ⟶ ρ.P.A.left), IsGrpPullback B ρ.P.A (spMap (Subalgebra.inclusion hR₁).toRingHom) bB → ∀ (A₀ : Over (Sp Ω)) [GrpObj A₀] (a₁ : A₀.left ⟶ B.left) (ψ : A₀.left ⟶ G.left), IsGrpPullback A₀ B (spMap R₁.val.toRingHom) a₁ → IsGrpPullback A₀ G Y.pt ψ → ∀ (I : Type) (e : I → (B ⟶ B)), (∀ i, IsMonHom (e i)) → ∀ (f : I → (G ⟶ G)), (∀ i, ∃ e₀ : A₀ ⟶ A₀, e₀.left ≫ a₁ = a₁ ≫ (e i).left ∧ e₀.left ≫ ψ = ψ ≫ (f i).left) → ∀ (H : AddSubgroup S.Gam) (gγ : S.perp H → (Over.mk Y.pt ⟶ G)), (∀ t, ∃ w : Sp Ω ⟶ A₀.left, w ≫ A₀.hom = 𝟙 _ ∧ w ≫ a₁ ≫ bB = spMap S.R.val.toRingHom ≫ (ρ.pt t.1).left ∧ w ≫ ψ = (gγ t).left) → ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ Y.Z), R₁ ≤ Y.O ((gPt p ≫ y) (closedPoint (PadicAlgCl p))) → ∀ (y₀ : S.R →+* PadicAlgCl p), (∀ a : S.R, y₀ a = Y.val (gPt p ≫ y) a) → ∀ (u : ρ.UTest p y₀) (l : u.Lab) (yK₁ : R₁ →+* FractionRing u.V), yK₁.comp (Subalgebra.inclusion hR₁).toRingHom = u.yK → (∀ a : R₁, algebraMap (FractionRing u.V) (PadicAlgCl p) (yK₁ a) = Y.val (gPt p ≫ y) a) → ∀ (φB : u.A.A.left ⟶ B.left), IsGrpPullback u.A.A B (spMap yK₁) φB → φB ≫ bB = u.φ → ∀ (ζ : oˣ), (ζ : o) = S.ζ ^ (S.r * S.N) → l.yy.ker = H → (∀ t : S.perp H, ExtNear (gγ t) (y (cPt p))) → ∃ (m : I → u.D.toPre.X →+ u.D.toPre.X) (c : S.perp H → u.D.toPre.X →+ ZMod (S.r * S.N)), (∀ i, ∃ (F : u.G ⟶ u.G) (eA : u.A.A ⟶ u.A.A), IsMonHom F ∧ eA.left ≫ φB = φB ≫ (e i).left ∧ eA.left ≫ genMap u.U = genMap u.U ≫ F.left ∧ EndChar u.U F (m i)) ∧ (∀ t b α, l.yy b = QuotientAddGroup.mk α → c t α = eStd S.g _ t.1 b) ∧ LatAt f gγ ζ (S.r * S.N) m c (y (cPt p)) := by
  intro o Ω _ _ _ hA S ρ Y hY G _ _ hG R₁ hR₁ B _ hB₁ bB hbB A₀ _ a₁ ψ ha₁ hψ I e he f hef H gγ hγ p _ y hR y₀ hy₀ u l yK₁ hyK₁
    hy₁ φB hφB hφBb ζ hζ hH hext
  subst hH
  haveI := hA.ded
  have hL : 0 < S.r * S.N := Nat.mul_pos S.r_pos (by have := S.N_ge; omega)
  have hζ1 : ζ ^ (S.r * S.N) = 1 := Units.ext (by
    rw [Units.val_pow_eq_pow_val, hζ, ← pow_mul, ← pow_two, S.prim.pow_eq_one]; rfl)
  haveI : CharZero u.V := RingHom.charZero
    ((algebraMap (FractionRing u.V) (PadicAlgCl p)).comp (algebraMap u.V (FractionRing u.V)))
  have hB : GlobalTheory.Mum.Base u.V := ⟨⟨inferInstance, inferInstance, inferInstance, u.complete⟩, inferInstance⟩
  have hgen := GlobalTheory.TauFormHom.isGrpPullback_genMap u.U
  choose eA heA heA' using fun i => exists_endo_pull hφB (e i) (he i)
  choose F hF using fun i => (GlobalTheory.Published.SemiAbelianHomExtension.fractionField_of_isGrpPullback
    GlobalTheory.semiAbelianHomExtension_holds u.semi u.semi hgen hgen (eA i)).exists
  choose m hm using fun i => endChar_exists_of_isMonHom u.V hB u.G u.semi u.D u.A u.U (F i) (hF i).1
  choose c hc using fun t : S.perp l.yy.ker => PerpTorus.exists_form S l.yy l.yy_onto t.1 t.2
  refine ⟨m, c, fun i => ⟨F i, eA i, (hF i).1, heA' i, (hF i).2, hm i⟩, hc, ?_⟩
  obtain ⟨V', _, _, _, fV, fK, κ', iV, ξ, hfV, hfK, hκ, hiV, hiκ, hξ⟩ :=
    GlobalTheory.ValPt.exists_dvr_factor o Ω Y p u.V u.complete (algebraMap _ _) u.norm_le y
  let jV := algebraMap V' (FractionRing V')
  have hcl : ξ (closedPoint V') = y (cPt p) := by
    rw [← hξ]
    exact (congrArg ξ (IsLocalRing.comap_closedPoint iV)).symm
  have hg : gPt p ≫ y = spMap κ' ≫ spMap jV ≫ ξ := by
    rw [← hξ, ← Category.assoc, ← Category.assoc, spMap_comp', spMap_comp']
    congr 2
    exact RingHom.ext hiκ
  have hpt : (gPt p ≫ y) (closedPoint (PadicAlgCl p)) = (spMap jV ≫ ξ) (closedPoint (FractionRing V')) := by
    rw [hg]
    exact congrArg (spMap jV ≫ ξ) (Subsingleton.elim (α := PrimeSpectrum (FractionRing V')) _ _)
  rw [hpt] at hR
  have hyK : ∀ x : R₁, (fK.comp yK₁) x = Y.val (spMap jV ≫ ξ) x := fun x => κ'.injective (by
    have e₁ := RatModel.val_spMap_comp κ' (spMap jV ≫ ξ) (specializes_refl _) ⟨x.1, hR x.2⟩
    rw [RatModel.valLoc_eq_val] at e₁
    rw [← e₁, ← hg, ← hy₁]
    exact DFunLike.congr_fun hκ (yK₁ x))
  have hα := isGrpPullback_pullback u.A.A (spMap fK)
  obtain ⟨Ψ, hΨ, hΨe, hΨp⟩ := GlobalTheory.Poinc.Spread.spread_fibre o Ω Y hY G hG R₁ B hB₁ A₀ a₁ ψ ha₁ hψ
    _ _ hR _ hyK _ _ ((hα.comp hφB).congr (spMap_comp' _ _) rfl)
  have hj : spMap fK ≫ jK u.V = spMap (jV.comp fV) := (spMap_comp' _ _).trans (congrArg spMap (RingHom.ext hfK))
  obtain ⟨G', _, β, β', ω, hβ, hβ', hω, hωβ, hωβ', hend⟩ := exists_common_pullback_dvr Y.Z G hG u.V u.G u.semi V' fV ξ _ _ Ψ
    ((hα.comp hgen).congr hj rfl) hΨ
  obtain ⟨a, ha⟩ := exists_spMap (ξ ≫ Y.s)
  rw [← hcl] at hext ⊢
  obtain ⟨xx, hxx, hsurj⟩ := LabelMap.exists_lift_points u.cart (TFK (R := u.V) (PadicAlgCl p)) ρ.pt ρ.pt_add
  have hy : (TFK (R := u.V) (PadicAlgCl p)).hom ≫ spMap u.yK = spMap y₀ := (spMap_comp' _ _).trans (congrArg spMap u.fac)
  have hsurj' := hsurj (S.r * S.N) fun z hz =>
    (ρ.pt_bij (PadicAlgCl p) _ z hz).exists.imp fun a ha => congrArg (fun w => w.left) ha
  have hx : ∀ b, (xx (Multiplicative.ofAdd b)).left ≫ u.φ = spMap y₀ ≫ (ρ.pt b).left := fun b => by
    rw [← hy]; exact (hxx b _).2 rfl
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := GlobalTheory.allSixLaws
  have tor := PerpCharacter.exists_torus_point_eStd ⟨h1, h2, h3, h4, h5⟩ uTors_closed o Ω S ρ p y₀ u l
    (fun b => xx (Multiplicative.ofAdd b)) hx (fun b b' => by rw [ofAdd_add, map_mul])
    (fun z hz => (hsurj' z hz).imp fun _ h => h.symm)
  refine latAt_of_unif o Ω Y G hG I _ f _ ζ _ hL hζ1 u.V hB u.G u.semi u.D u.A u.U F m hm V' fV hfV ξ a ha G' β β' hβ hβ'
    (fun i => ?_) (PadicAlgCl p) (κ'.comp jV) (κ'.injective.comp (IsFractionRing.injective V' _))
    (by rw [← hκ]; ext x; simp [jV, hfK]) c fun t => ⟨hext t, ?_⟩
  · obtain ⟨eK, -, heK⟩ := exists_endo_pull hα (eA i) (heA i)
    obtain ⟨e₀, h₀, h₀'⟩ := hef i
    refine hend (F i) (f i) eK ?_ (hΨe (e i) (f i) e₀ h₀ h₀' eK ?_)
    · rw [← Category.assoc, heK, Category.assoc, (hF i).2, Category.assoc]
    · rw [← Category.assoc, heK, Category.assoc, heA', Category.assoc]
  · obtain ⟨q, τ, hq, hτ, hqx, hv⟩ := tor t.1 t.2
    have hw : (xx (Multiplicative.ofAdd t.1)).left ≫ u.A.A.hom = spMap κ' ≫ spMap fK := by
      rw [Over.w, spMap_comp', hκ]; rfl
    let xK : Sp (PadicAlgCl p) ⟶ ((Over.pullback (spMap fK)).obj u.A.A).left := pullback.lift _ _ hw
    have hx₁ : xK ≫ pullback.fst u.A.A.hom (spMap fK) = (xx (Multiplicative.ofAdd t.1)).left := pullback.lift_fst _ _ _
    have hx₂ : xK ≫ ((Over.pullback (spMap fK)).obj u.A.A).hom = spMap κ' := pullback.lift_snd _ _ _
    refine ⟨q, τ, _, xK ≫ ω, hq, hτ, hqx, fun χ => ?_, ?_, ?_, ?_⟩
    · obtain ⟨b, hb⟩ := l.yy_onto (QuotientAddGroup.mk χ)
      rw [hv b χ hb, hc t b χ hb, hy₀, hζ, ← pow_mul]
      have : (gPt p ≫ y) ≫ Y.s = spMap ((κ'.comp jV).comp a) := by
        rw [hg, Category.assoc, Category.assoc, ha, spMap_comp', spMap_comp']
      exact RatModel.val_algebraMap this _
    · rw [Category.assoc, hω, ← Category.assoc, hx₂, spMap_comp']
    · rw [Category.assoc, hωβ, ← Category.assoc, hx₁]
    · obtain ⟨v, hv'⟩ := ExtNear.exists_valAt ξ (hext t)
      obtain ⟨w, hw₁, hw₂, hw₃⟩ := hγ t
      have hv₂ := hv'.comp (spMap (κ'.comp jV))
      have hbw : (spMap (Subalgebra.inclusion hR₁).toRingHom ≫ (ρ.pt t.1).left) ≫ ρ.P.A.hom =
          𝟙 _ ≫ spMap (Subalgebra.inclusion hR₁).toRingHom := by
        rw [Category.assoc, Over.w, Category.id_comp]
        exact Category.comp_id _
      obtain ⟨b, hb₁, hb₂⟩ : ∃ b : Sp R₁ ⟶ B.left, b ≫ bB = spMap (Subalgebra.inclusion hR₁).toRingHom ≫ (ρ.pt t.1).left ∧
          b ≫ B.hom = 𝟙 _ := ⟨hbB.1.lift _ _ hbw, hbB.1.lift_fst _ _ _, hbB.1.lift_snd _ _ _⟩
      have hwb : w ≫ a₁ = spMap R₁.val.toRingHom ≫ b := by
        refine hbB.1.hom_ext ?_ ?_
        · rw [Category.assoc, hw₂, Category.assoc, hb₁, ← Category.assoc, spMap_comp']
          rfl
        · rw [Category.assoc, ha₁.1.w, ← Category.assoc, hw₁, Category.assoc, hb₂, Category.id_comp, Category.comp_id]
      rw [Category.assoc, hωβ', hΨp b (gγ t) w hb₂ hw₁ hwb hw₃ _ xK (spMap (κ'.comp jV) ≫ v) ?_ ?_]
      · exact hv₂
      · refine hbB.1.hom_ext ?_ ?_
        · simp only [Category.assoc]
          rw [hφBb, hb₁, ← Category.assoc, hx₁, hx, ← Category.assoc, hx₂, ← Category.assoc, ← Category.assoc, spMap_comp',
            spMap_comp', ← RingHom.comp_assoc, hκ, RingHom.comp_assoc, hyK₁, u.fac]
        · simp only [Category.assoc]
          rw [hb₂, Category.comp_id, hφB.1.w, ← Category.assoc _ u.A.A.hom, pullback.condition, Category.assoc, spMap_comp']
          rfl
      · rw [← Category.assoc, hx₂, ← Category.assoc, spMap_comp']
        exact hv₂

theorem latAt_centre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf) (X : USetup C) (wi : UWit X) (Y : RatModel X.o₁ X.Ω₁) (U₀ : Y.Z.Opens) (EE : Y.Lat X.S.J) (FinalForm : ZHOut X.ρ Y U₀ EE) (q : Y.Z ⟶ X.M.Z), X.S.Over₀ Y U₀ → X.S.IsEE Y U₀ EE → IsProper q → Y.pt ≫ q = X.M.pt → ∀ (p : ℕ) [Fact p.Prime] (z : X.M.Z) (f : 𝓞 E → (FinalForm.G ⟶ FinalForm.G)) (gγ : X.S.TT X.M z → (Over.mk Y.pt ⟶ FinalForm.G)), GlobalTheory.UPoinc.GFib.IsEndoExt X wi FinalForm f → GlobalTheory.UPoinc.GFib.IsTorsExt X wi FinalForm q z gγ → ∀ ζ : X.o₁ˣ, IsPrimitiveRoot (ζ : X.o₁) (X.S.r * X.S.N) → ∃ (s : ZMod (X.S.r * X.S.N)) (σ : 𝓞 E → 𝓞 E), IsUnit s ∧ Function.Surjective σ ∧ ∀ (ct : UCTrait X p z) (y : Sp (OO p) ⟶ Y.Z), y ≫ q = ct.y → ∀ (yy : X.S.Gam →+ ModN (X.S.r * X.S.N) ct.T.P.D.toPre.X), UIsLabW X wi ct yy → ∃ c : X.S.TT X.M z → ct.T.P.D.toPre.X →+ ZMod (X.S.r * X.S.N), LatAt f gγ ζ (X.S.r * X.S.N) (fun a => DistribSMul.toAddMonoidHom ct.T.P.D.toPre.X (σ a)) c (y (cPt p)) ∧ ∀ (a : X.S.Gam) (v : ct.T.P.D.toPre.X) (t : X.S.TT X.M z), yy a = QuotientAddGroup.mk v → c t v = s * eStd X.S.g _ (t : X.S.Gam) a := by
  intro E _ _ _ H Dw hpq l Xo cf C X wi Y U₀ EE FinalForm q hO _ _ hpt p _ z f gγ hf hg ζ hζ
  haveI := X.ar.ded
  haveI := X.ar.char
  have hL : 0 < X.S.r * X.S.N := Nat.mul_pos X.S.r_pos (by have := X.S.N_ge; omega)
  have hζp : IsPrimitiveRoot (X.S.ζ ^ (X.S.r * X.S.N)) (X.S.r * X.S.N) := X.S.prim.pow (pow_pos hL 2) (pow_two _)
  obtain ⟨k, hk, hkζ⟩ := exists_unit_pow_eq hL hζ hζp
  have hζ1 : ζ ^ (X.S.r * X.S.N) = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val]; exact hζ.pow_eq_one)
  refine ⟨k, H.bar, hk, H.bar.surjective, fun ct y hy yy hl => ?_⟩
  obtain ⟨-, hker⟩ := uIsLab_onto_and_ker E H Dw hpq l Xo cf C X p z ct yy hl.uIsLab
  obtain ⟨c₀, hc₀, R', fg, frac, hth, hev, ρ', u', -, -, -, hR', G, _, α, β, hα, hβ, -, ⟨mw, hmw, hmwβ, hpts⟩, y₀, hy₀, u,
    lb, j, hjq, hyy, hmat⟩ := hl
  have key : ∀ b mu, yy b = QuotientAddGroup.mk mu ↔ lb.yy b = QuotientAddGroup.mk (j.symm mu) := fun b mu => by
    refine ⟨fun h => ?_, fun h => by rw [hyy b _ h, j.apply_symm_apply]⟩
    obtain ⟨χ, hχ⟩ := QuotientAddGroup.mk_surjective (lb.yy b)
    obtain ⟨v, hv⟩ := QuotientAddGroup.eq.1 ((hyy b χ hχ.symm).symm.trans h)
    rw [← hχ]
    refine QuotientAddGroup.eq.2 ⟨j.symm v, j.injective ?_⟩
    simp only [nsmulAddMonoidHom_apply] at hv ⊢
    rw [map_nsmul, j.apply_symm_apply, hv, map_add, map_neg, j.apply_symm_apply]
  have hker' : lb.yy.ker = X.S.HH X.M z := by
    rw [← hker]
    ext b
    have := key b 0
    rw [map_zero] at this
    exact this.symm
  have hr : Set.range Y.pt ⊆ Set.range U₀.ι := by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact Y.top_le_preimage_pt hO.ne (x := w) trivial
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : Sp X.Ω₁ ⟶ U₀.toScheme, x₀ ≫ U₀.ι = Y.pt :=
    ⟨IsOpenImmersion.lift U₀.ι Y.pt hr, IsOpenImmersion.lift_fac _ _ _⟩
  have hw : wi.α ≫ X.ρ.P.A.hom = (wi.G.hom ≫ x₀) ≫ FinalForm.u₀ := by
    rw [Category.assoc, FinalForm.u₀_gen x₀ hx₀]
    exact wi.hα.1.w
  have hψ : IsGrpPullback wi.G FinalForm.G Y.pt (pullback.lift wi.α (wi.G.hom ≫ x₀) hw ≫ FinalForm.φ) :=
    (((isGrpPullback_pullback X.ρ.P.A FinalForm.u₀).cancel
      (wi.hα.congr (FinalForm.u₀_gen x₀ hx₀).symm (pullback.lift_fst _ _ hw).symm) (pullback.lift_snd _ _ hw)).comp
      FinalForm.cart).congr hx₀ rfl
  have hsemi : IsSemiAbelian G :=
    isSemiAbelian_of_isAbelianScheme _ (PolPull.isAbelianScheme_of_isGrpPullback ρ'.P.isAb hα)
  choose e he heβ using fun a : 𝓞 E => exists_endo_pull hβ (Xo.univ.t.act.act a) inferInstance
  have hef : ∀ a, ∃ e₀ : wi.G ⟶ wi.G, e₀.left ≫ mw = mw ≫ (e a).left ∧
      e₀.left ≫ pullback.lift wi.α (wi.G.hom ≫ x₀) hw ≫ FinalForm.φ =
        (pullback.lift wi.α (wi.G.hom ≫ x₀) hw ≫ FinalForm.φ) ≫ (f a).left := fun a => by
    obtain ⟨e₀, -, he₀⟩ := exists_endo_pull hmw (e a) (he a)
    refine ⟨e₀, he₀, ((hf a).2 x₀ hx₀ hw e₀ ?_).trans (Category.assoc _ _ _).symm⟩
    rw [← hmwβ, ← Category.assoc, he₀, Category.assoc, heβ, Category.assoc]
  have hγ : ∀ t : X.S.TT X.M z, ∃ w : Sp X.Ω₁ ⟶ wi.G.left, w ≫ wi.G.hom = 𝟙 _ ∧
      w ≫ mw ≫ α = spMap R'.val.toRingHom ≫ (ρ'.pt t.1).left ∧
      w ≫ pullback.lift wi.α (wi.G.hom ≫ x₀) hw ≫ FinalForm.φ = (gγ t).left := fun t => by
    obtain ⟨w, hw₁, hw₂⟩ := hpts t.1
    have h1 : w ≫ wi.G.hom = 𝟙 _ := comp_hom_eq_id X.S.frac wi.hα _ w hw₁
    exact ⟨w, h1, hw₂, (hg t).2.1 x₀ hx₀ hw w h1 hw₁⟩
  have hyz : q (y (cPt p)) = z := by rw [← ct.cen, ← hy]; rfl
  have hom : X.M.IsHom Y (AlgHom.id _ _) q :=
    hpt.trans ((Category.id_comp _).symm.trans (congrArg (· ≫ X.M.pt) (Spec.map_id _).symm))
  have hcy : gPt p ≫ ct.y = (gPt p ≫ y) ≫ q := by rw [Category.assoc, hy]
  rw [hcy] at hR' hy₀
  have hR₁ : ratHull R' ≤ Y.O ((gPt p ≫ y) (closedPoint (PadicAlgCl p))) :=
    ratHull_le_O_of_point Y (gPt p ≫ y) R' fun x hx => hom.map_mem_O (hR' hx)
  have hy₀' : ∀ x : R', y₀ x = Y.val (gPt p ≫ y) x := fun x => (hy₀ x).trans (hom.val_comp _ _ (hR' x.2))
  obtain ⟨yK₁, hyK₁, hval⟩ := exists_ratLift_val Y (algebraMap (FractionRing u.V) (PadicAlgCl p)) (gPt p ≫ y) R' hR₁ u.yK
    fun x => (DFunLike.congr_fun u.fac x).trans (hy₀' x)
  obtain ⟨φB, hφ, hφ₁⟩ := exists_factor_pull (g := spMap yK₁) hα u.cart ((spMap_comp' _ _).trans (congrArg spMap hyK₁))
  obtain ⟨m, c, hm, hc, hlat⟩ := latAt_of_uTest_over X.o₁ X.Ω₁ (X.S.rechart c₀ hc₀ R' fg frac hth hev) ρ' Y hO.normal FinalForm.G FinalForm.semi
    (ratHull R') (le_ratHull R') G hsemi α hα wi.G mw _ hmw hψ (𝓞 E) e he f hef (X.S.HH X.M z) gγ hγ p y hR₁ y₀ hy₀' u lb
    yK₁ hyK₁ hval φB hφ hφ₁ (ζ ^ k.val) ((Units.val_pow_eq_pow_val _ _).trans hkζ) hker' fun t => (hg t).2.2 _ hyz
  have hchar : ∀ a χ, j (m a χ) = H.bar a • j χ := fun a χ => by
    obtain ⟨F, eA, hF, heA, hgen, hEC⟩ := hm a
    refine char_eq_bar_smul E H _ _ _ ρ' p y₀ u lb _ ct.T.be ct.T.lev ct.sc (sc_ne_zero ct) j hjq a eA ?_ F hF hgen (m a) hEC χ
    intro n pk pk' x x' hn hx hx' hxx
    refine hmat n a pk pk' x x' (x.left ≫ φB) (x'.left ≫ φB) hn hx hx' ?_ ?_ ?_
    · rw [Category.assoc, hφ₁]
    · rw [Category.assoc, hφ₁]
    · rw [hxx, Category.assoc, Category.assoc, Category.assoc, ← Category.assoc eA.left, heA, Category.assoc, heβ]
  refine ⟨fun t => (AddMonoidHom.mulLeft k).comp ((c t).comp j.symm.toAddMonoidHom),
    latAt_rescale ζ hζ1 k (hlat.equiv j hchar fun t χ => congrArg (c t) (j.symm_apply_apply χ)), fun a v t h => ?_⟩
  exact congrArg (k * ·) (hc t a _ ((key a v).1 h))

end GlobalTheory.UPoinc.GFibCentre
