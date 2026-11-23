import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFgSubalgebraSpecFactorThroughOpenStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniversalBasisMoveBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSymplecticLevelBaseChangePolarisedAbelianStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorsionPointsOfSquareLevelStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSymLiftGlobalStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsTorsFrameOfSymLiftStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNormalisedMulPullIsoOriginStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SpanTranslatesMultiplicationPullbackThetaStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGoodTorsionTranslateGeometricPointStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ClosureZmodPowEqTopOfMeetsTorsionCosetsStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsMonomialMatricesProjectiveRepStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsOperators
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LineBundleSymmetryHypothesisBaseChange
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverMove
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnivBasis
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ThetaReal

noncomputable section
namespace GlobalTheory.ThetaReal

theorem exists_nsmul_eq {κ : Type} {r N : ℕ} (h : 1 ≤ r * N) (a : κ → ZMod (r * N)) (ha : N • a = 0) :
    ∃ c : κ → ZMod (r * N), a = r • c := by
  haveI : NeZero (r * N) := ⟨by omega⟩
  have hN : 0 < N := Nat.pos_of_mul_pos_left h
  have key : ∀ i, r ∣ (a i).val := fun i => by
    have e : ((N * (a i).val : ℕ) : ZMod (r * N)) = 0 := by
      rw [Nat.cast_mul, ZMod.natCast_zmod_val, ← nsmul_eq_mul]
      exact congrFun ha i
    rw [ZMod.natCast_eq_zero_iff, mul_comm N] at e
    exact Nat.dvd_of_mul_dvd_mul_right hN e
  choose c hc using key
  refine ⟨fun i => (c i : ZMod (r * N)), funext fun i => ?_⟩
  rw [Pi.smul_apply, nsmul_eq_mul, ← Nat.cast_mul, ← hc, ZMod.natCast_zmod_val]

theorem fn_hom {R : Type} [CommRing R] (v : Γ((baseOver (Sp R)).left, ⊤)) :
    fn ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom v) = v :=
  (Scheme.ΓSpecIso (CommRingCat.of R)).hom_inv_id_apply v

theorem fn_injective {R : Type} [CommRing R] :
    Function.Injective (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom :=
  (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv).1

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

theorem isNoetherian_of_fg [ArithBase o Ω] {R : Subalgebra o Ω} (h : R.FG) : IsNoetherianRing R := by
  have := ArithBase.ded (o := o) (Ω := Ω)
  exact isNoetherianRing_of_fg h

theorem algebraMap_injective [ArithBase o Ω] (R : Subalgebra o Ω) : Function.Injective (algebraMap o R) :=
  fun _ _ h => ArithBase.inj (o := o) (Ω := Ω) (congrArg Subtype.val h)

theorem prim_iff [ArithBase o Ω] (R : Subalgebra o Ω) (ze : oˣ) (q : ℕ) :
    IsPrimitiveRoot (unitOn (Units.map (algebraMap o R).toMonoidHom ze)) q ↔ IsPrimitiveRoot (ze : o) q := by
  rw [← IsPrimitiveRoot.coe_units_iff]
  exact IsPrimitiveRoot.map_iff_of_injective
    (f := (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.comp (algebraMap o R))
    (fn_injective.comp (algebraMap_injective R))

theorem exists_real_of_univBasis (hL : Laws) [ArithBase o Ω] (R : Subalgebra o Ω) (fg : R.FG)
    (frac : ∀ x : Ω, ∃ a ∈ R, ∃ b ∈ R, x = a / b) (P : PolAV (Sp R)) (n k j : ℕ) (ze : oˣ) (hp : n.Prime)
    (ho : Odd n) (hk : 2 ≤ k) (hj : 1 ≤ j) (hu : IsUnit (n : o)) (hS : HypS P.A P.L)
    (lev : Out.Level P ((n ^ j * (n ^ k) ^ 2) ^ 2) (unitOn (Units.map (algebraMap o R).toMonoidHom ze)))
    (th : LB.Sec (LPow P.A P.L 1 (baseOver (Sp R)))) (hth : UnivBasis P 1 (fun _ : Fin 1 => SecM.ofSec P.A th))
    (b : Fin (((n ^ k) ^ 2) ^ P.g) → SecM P.A P.L ((n ^ k) ^ 2 : ℕ) (baseOver (Sp R)))
    (hb : UnivBasis P ((n ^ k) ^ 2 : ℕ) b) {R₀ : Subalgebra o Ω} (h : R₀ ≤ R) (P₀ : PolAV (Sp R₀))
    (φ : P.A.left ⟶ P₀.A.left) (hg : P.g = P₀.g)
    (hφ : IsGrpPullback P.A P₀.A (spMap (Subalgebra.inclusion h).toRingHom) φ) (hiso : LBIso P.L (P₀.L.pull φ))
    (x₀ : Fin (2 * P₀.g) → (baseOver (Sp R₀) ⟶ P₀.A))
    (hx₀ : ∀ (i : Fin (2 * P₀.g)) (i' : Fin (2 * P.g)), (i : ℕ) = i' →
      (lev.pt i').left ≫ φ = spMap (Subalgebra.inclusion h).toRingHom ≫ (x₀ i).left) :
    ∃ (S : ThetaSys o Ω) (ρ : S.Real) (h : R₀ ≤ S.R) (φ : ρ.P.A.left ⟶ P₀.A.left), S.ζ = ze ∧ S.N = (n ^ k) ^ 2 ∧
      S.r = n ^ j ∧ S.g = P₀.g ∧ IsGrpPullback ρ.P.A P₀.A (spMap (Subalgebra.inclusion h).toRingHom) φ ∧
      LBIso ρ.P.L (P₀.L.pull φ) ∧ ∀ (i : Fin S.g) (i₁ i₂ : Fin (2 * P₀.g)), (i₁ : ℕ) = i → (i₂ : ℕ) = i + P₀.g →
      (ρ.pt (Pi.single (.inl i) 1)).left ≫ φ =
        spMap (Subalgebra.inclusion h).toRingHom ≫ (x₀ i₁ ^ (S.r * S.N)).left ∧
      (ρ.pt (Pi.single (.inr i) 1)).left ≫ φ =
        spMap (Subalgebra.inclusion h).toRingHom ≫ (x₀ i₂ ^ (S.r * S.N)).left := by
  haveI := isNoetherian_of_fg fg
  haveI : IsAffine (baseOver (Sp R)).left := inferInstanceAs (IsAffine (Sp R))
  have hn2 : 2 ≤ n := hp.two_le
  have hn1 : 1 ≤ n := by omega
  have hm1 : 1 ≤ n ^ k := Nat.one_le_pow _ _ hn1
  have hr1 : 1 ≤ n ^ j := Nat.one_le_pow _ _ hn1
  have hN2 : 2 ≤ (n ^ k) ^ 2 := by
    have : n ^ 1 ≤ n ^ k := Nat.pow_le_pow_right hn1 (by omega)
    nlinarith
  have hM : n ^ j * (n ^ k) ^ 2 = n ^ (j + 2 * k) := by ring
  have hM1 : 1 ≤ n ^ j * (n ^ k) ^ 2 := hM ▸ Nat.one_le_pow _ _ hn1
  have hMo : Odd (n ^ j * (n ^ k) ^ 2) := hM ▸ ho.pow
  let f : o →+* Γ((baseOver (Sp R)).left, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.comp (algebraMap o R)
  have hf : Function.Injective f := fn_injective.comp (algebraMap_injective R)
  haveI : Nontrivial Γ((baseOver (Sp R)).left, ⊤) := (fn_injective (R := R)).nontrivial
  have un : ∀ q e : ℕ, q = n ^ e → IsUnit (q : Γ(Sp R, ⊤)) := fun q e hq => by
    have := (hu.pow e).map f
    rw [map_pow, map_natCast] at this
    rw [hq, Nat.cast_pow]
    exact this
  have prim : IsPrimitiveRoot (ze : o) ((n ^ j * (n ^ k) ^ 2) ^ 2) := (prim_iff R ze _).1 lev.prim
  obtain ⟨pt, hadd, hbij, hweil, hdiv, hnorm⟩ := GlobalTheory.T.exists_torsionPoints_of_squareLevel_alt hL _ P _ _ hM1 (un _ _ hM) lev
  obtain ⟨h0, hsm⟩ := pt_nsmul pt hadd
  obtain ⟨rig, hrig⟩ := P.rigid
  have hfr : ∀ a, ∃ τ, IsTorsFrame P rig (n ^ j * (n ^ k) ^ 2) (pt a) τ := fun a => by
    obtain ⟨y, hy, e⟩ := hdiv a
    obtain ⟨θ, hθ⟩ := GlobalTheory.T.exists_symLift_of_pow_eq_one hL _ P _ hMo.pow (un _ ((j + 2 * k) * 2) (by rw [hM, pow_mul])) _ y hy
    exact GlobalTheory.T.exists_isTorsFrame_of_symLift' hL _ P rig hrig _ hMo _ y _ hy e θ hθ
  choose fr hfr using hfr
  have tors : ∀ a, pt (n ^ j • a) ^ ((n ^ k) ^ 2) = 1 := fun a => by
    rw [← hsm, smul_smul, mul_comm ((n ^ k) ^ 2) (n ^ j), nsmul_self, h0]
  choose U hU using fun a => GlobalTheory.T.exists_symLift_of_pow_eq_one hL _ P _ ho.pow.pow (un _ (k * 2) (pow_mul _ _ _).symm) _ _ (tors a)
  obtain ⟨α, hα, hαn⟩ := GlobalTheory.T.exists_normalised_mulPull_iso_origin hL _ P rig hrig (n ^ k) _ rfl (baseOver (Sp R))
  obtain ⟨s₀, hs₀⟩ := VVRank.exists_isTwistPull P.A (ψ := mulT P.A (baseOver (Sp R)) (n ^ k)) (hm := lift_snd _ _)
    (b := 1) P.isLB hα th
  obtain ⟨u, u₁, u₂, u₃, u₄, u₅⟩ := exists_operators hL P rfl ho.pow (un _ _ hM) _ pt hadd hweil U hU hα hs₀
  have hspan := GlobalTheory.T.span_translates_multiplicationPullback_theta hL _ P (n ^ k) _ rfl hm1 (un _ _ rfl) th hth _ b hb α hα s₀ hs₀ _ U
    (fun a => SecM.toSec P.A (u a (SecM.ofSec P.A s₀))) (fun K _ _ x z hz => by
      obtain ⟨a, ha, uniq⟩ := hbij K x z (by rw [mul_comm, pow_mul, hz, one_pow])
      obtain ⟨a₀, -, uniq₀⟩ := hbij K x 1 (one_pow _)
      have e : (n ^ k) ^ 2 • a = 0 := (uniq₀ _ (by beta_reduce; rw [hsm, MonObj.comp_pow, ha, hz])).trans
        (uniq₀ _ (by beta_reduce; rw [h0, MonObj.comp_one])).symm
      obtain ⟨c, rfl⟩ := exists_nsmul_eq hM1 a e
      exact ⟨c, by rw [(hU c).pt_eq, ha]⟩) (fun a => (u₁ _ _ _).2 rfl)
  obtain ⟨bb, -⟩ := hb.exists_basis
  obtain ⟨J, _, ρ, s, i₀, hcard, hi₀, ρ₁, ρ₂, ρ₃, ρ₄, ρ₅⟩ := GlobalTheory.T.exists_monomial_matrices_projectiveRep o _ _ f hf P.g (n ^ k) (n ^ j) _ rfl hm1 hr1
    ze _ (Nat.one_le_pow _ _ hM1) prim.pow_eq_one bb u (SecM.ofSec P.A s₀) u₂
    (fun a b => (u₃ a b).imp fun e he v => (he v).trans (congrArg (· • _) (map_pow f _ _).symm)) u₄ u₅ hspan
  choose v hv using fun a => ThetaPtExist.exists_isValueAt P.isLB th (pt a) (fr a) (hfr a).2.1
  choose w hw using fun a i => (hL.evVal _ P ((n ^ k) ^ 2) (pt a) (fr a) (hfr a).2.1 (SecM.toSec P.A (s i))).exists
  let ev : Γ((baseOver (Sp R)).left, ⊤) → R := (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom
  have good : ∀ a, ∃ y, n • y = 0 ∧ a + y ∈ {a | (ev (v a) : Ω) ≠ 0} := fun a => by
    let K := AlgebraicClosure Ω
    let x : Sp K ⟶ Sp R := spMap ((algebraMap Ω K).comp R.val.toRingHom)
    have := ArithBase.char (o := o) (Ω := Ω)
    obtain ⟨y, hy, H⟩ := GlobalTheory.T.exists_good_torsion_translate_geometricPoint hL _ P K x n hn2 (Nat.cast_ne_zero.2 (by omega)) th hth
      ((Over.homMk x (by simp) : Over.mk x ⟶ baseOver (Sp R)) ≫ pt a)
    obtain ⟨c, hc, -⟩ := hbij K x y (by rw [hM, show j + 2 * k = (j + 2 * k - 1) + 1 by omega, pow_succ', pow_mul, hy,
      one_pow])
    obtain ⟨a₀, -, uniq₀⟩ := hbij K x 1 (one_pow _)
    refine ⟨c, (uniq₀ _ (by beta_reduce; rw [hsm, MonObj.comp_pow, hc, hy])).trans
      (uniq₀ _ (by beta_reduce; rw [h0, MonObj.comp_one])).symm, fun e => ?_⟩
    refine H (pt (a + c)) (fr _) (v _) (by rw [hadd, MonObj.comp_mul, hc]) (hfr _).2.1 (hv _) ?_
    have e' : ev (v (a + c)) = 0 := Subtype.ext e
    exact (fn_hom _).symm.trans ((congrArg fn e').trans (map_zero _))
  obtain ⟨c₁, hc₁⟩ := hth.exists_basis
  let S : ThetaSys o Ω :=
    { g := P.g, N := (n ^ k) ^ 2, r := n ^ j, N_ge := hN2, r_pos := hr1, ζ := ze, prim := prim
      unit := by rw [hM, Nat.cast_pow]; exact hu.pow _
      J := J, ne := ⟨i₀⟩, ρ := ρ, ρ_one := ρ₁, ρ_mul := ρ₂, ρ_add := ρ₃
      th := fun a => ev (v a), ev := fun a i => ev (w a i), R := R, fg := fg, frac := frac
      th_mem := fun a => (ev (v a)).2, ev_mem := fun a i => (ev (w a i)).2
      supp := GlobalTheory.T.closure_zmodPow_eq_top_of_meets_torsion_cosets _ n (j + 2 * k) _ hn1 (by omega) hM _ good
      th_ne := by
        obtain ⟨y, -, hy⟩ := good 0
        exact ⟨_, hy⟩ }
  let ρ' : S.Real :=
    { P := P, g_eq := rfl, hypS := hS, n := n, n_prime := hp, n_odd := ho, k := k, two_le := hk, N_eq := rfl
      r_eq := ⟨j, hj, rfl⟩, card := hcard, pt := pt, pt_add := hadd, pt_bij := hbij
      weil := fun a b c hc => by
        have e : unitOn c = unitOn (Units.map (algebraMap o R).toMonoidHom ze) ^
            (n ^ j * (n ^ k) ^ 2 * (eStd P.g _ a b).val) := Units.ext
          ((congrArg fn hc).trans ((map_pow f _ _).trans (Units.val_pow_eq_pow_val (unitOn (Units.map (algebraMap o R).toMonoidHom ze)) _).symm))
        rw [e]
        exact hweil a b
      rig := rig, rig_gen := hrig, th₁ := th
      th₁_basis := fun σ => by
        have := existsUnique_of_basis c₁ σ
        simp only [hc₁] at this
        exact this
      fr := fr, fr_tors := hfr
      th_val := fun a => (fn_hom (v a)).symm ▸ hv a
      s := fun i => SecM.toSec P.A (s i)
      s_basis := existsUnique_of_basis s
      ev_val := fun i a => (congrArg (IsValueAt _ _ _ _ _ _) (fn_hom (w a i))).mpr (hw a i)
      i₀ := i₀, α := α, α_gen := hα, α_norm := hαn
      s_zero := by
        have e : SecM.toSec P.A (s i₀) = s₀ := by rw [hi₀]; rfl
        exact e ▸ hs₀
      U := U, U_sym := hU
      U_act := fun a i σ H => (sum_iff σ s _).2 (((u₁ _ _ _).1 H).symm.trans (ρ₄ a i))
      orbit := ρ₅ }
  refine ⟨S, ρ', h, φ, rfl, rfl, rfl, hg, hφ, hiso, fun i i₁ i₂ e₁ e₂ => ?_⟩
  obtain ⟨q₁, q₂⟩ := hnorm i ⟨i₁, by have := i₁.2; omega⟩ ⟨i₂, by have := i₂.2; omega⟩ e₁
    (e₂.trans (congrArg (_ + ·) hg.symm))
  have key : ∀ (i : Fin (2 * P₀.g)) (i' : Fin (2 * P.g)) (q : ℕ), (i : ℕ) = i' →
      (lev.pt i' ^ q).left ≫ φ = spMap (Subalgebra.inclusion h).toRingHom ≫ (x₀ i ^ q).left := fun i i' q e =>
    (ThetaPtMove.over_pow hφ (T := baseOver (Sp R)) (T₀ := baseOver (Sp R₀)) _
      ((Category.comp_id _).trans (Category.id_comp _).symm) (hx₀ i i' e).symm q).symm
  exact ⟨(congrArg (fun z => z.left ≫ φ) q₁).trans (key _ _ _ rfl),
    (congrArg (fun z => z.left ≫ φ) q₂).trans (key _ _ _ rfl)⟩

end GlobalTheory.ThetaReal

open GlobalTheory.ThetaReal in

theorem GlobalTheory.ThetaReal.exists_thetaSys_real : Laws → Laws2 → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (R : Subalgebra o Ω), R.FG → (∀ x : Ω, ∃ a ∈ R, ∃ b ∈ R, x = a / b) → ∀ (P : PolAV (Sp R)) (n k j : ℕ) (ze : oˣ), n.Prime → Odd n → 2 ≤ k → 1 ≤ j → IsUnit (n : o) → HypS P.A P.L → ∀ lev : Out.Level P ((n ^ j * (n ^ k) ^ 2) ^ 2) (unitOn (Units.map (algebraMap o R).toMonoidHom ze)), ∃ (S : ThetaSys o Ω) (ρ : S.Real) (h : R ≤ S.R) (φ : ρ.P.A.left ⟶ P.A.left), S.ζ = ze ∧ S.N = (n ^ k) ^ 2 ∧ S.r = n ^ j ∧ S.g = P.g ∧ IsGrpPullback ρ.P.A P.A (spMap (Subalgebra.inclusion h).toRingHom) φ ∧ LBIso ρ.P.L (P.L.pull φ) ∧ ∀ (i : Fin S.g) (i₁ i₂ : Fin (2 * P.g)), (i₁ : ℕ) = i → (i₂ : ℕ) = i + P.g → (ρ.pt (Pi.single (.inl i) 1)).left ≫ φ = spMap (Subalgebra.inclusion h).toRingHom ≫ (lev.pt i₁ ^ (S.r * S.N)).left ∧ (ρ.pt (Pi.single (.inr i) 1)).left ≫ φ = spMap (Subalgebra.inclusion h).toRingHom ≫ (lev.pt i₂ ^ (S.r * S.N)).left := by
  intro hL hL₂ o Ω _ _ _ _ R fg frac P n k j ze hp ho hk hj hu hS lev
  haveI := isNoetherian_of_fg fg
  let p : Sp R := (⊥ : PrimeSpectrum R)
  obtain ⟨V₁, m₁, b₁, hb₁⟩ := exists_univBasis hL₂.secBaseChangeAny P 1 le_rfl p
  obtain ⟨V₂, m₂, b₂, hb₂⟩ := exists_univBasis hL₂.secBaseChangeAny P ((n ^ k) ^ 2)
    (Nat.one_le_pow _ _ (Nat.one_le_pow _ _ hp.pos)) p
  obtain ⟨R', h, fg', τ, hτ⟩ := GlobalTheory.T.exists_fg_subalgebra_spec_factor_through_open o Ω R fg (V₁ ⊓ V₂) ⟨p, m₁, m₂⟩
  haveI := isNoetherian_of_fg fg'
  obtain ⟨P', φ, hg, hφ, hiso⟩ := exists_isPolFibre hL.polBaseChange (Subalgebra.inclusion h).toRingHom P
  have hiso' := LBIso.symm hiso
  have w : ∀ (V : (Sp R).Opens) (hV : V₁ ⊓ V₂ ≤ V), (τ ≫ (Sp R).homOfLE hV) ≫ (overRes (T := baseOver (Sp R)) V).hom =
      spMap (Subalgebra.inclusion h).toRingHom := fun V hV => by
    change (τ ≫ (Sp R).homOfLE hV) ≫ V.ι ≫ 𝟙 _ = _
    rw [Category.comp_id, Category.assoc, Scheme.homOfLE_ι, hτ]
  obtain ⟨c₁, hc₁⟩ := GlobalTheory.T.universalBasis_move_baseChange _ _ _ P P' φ hφ hiso' _ _ _ _ (w V₁ inf_le_left) b₁ hb₁
  obtain ⟨c₂, hc₂⟩ := GlobalTheory.T.universalBasis_move_baseChange _ _ _ P P' φ hφ hiso' _ _ _ _ (w V₂ inf_le_right) b₂ hb₂
  obtain ⟨lev', hlev⟩ := GlobalTheory.T.exists_symplecticLevel_baseChange_polarisedAbelian hL _ _ _ P P' φ hφ hiso' hg _ _
    (unitOn (Units.map (algebraMap o R').toMonoidHom ze))
    (congrArg (fun q => q.hom (algebraMap o R ze))
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (Subalgebra.inclusion h).toRingHom))).symm
    ((prim_iff R' ze _).2 ((prim_iff R ze _).1 lev.prim)) lev
  haveI hU : Unique (Fin (1 ^ P.g)) := by rw [one_pow]; infer_instance
  let e := finCongr (congrArg (((n ^ k) ^ 2) ^ ·) hg)
  refine exists_real_of_univBasis hL R' fg' (fun x => ?_) P' n k j ze hp ho hk hj hu
    (SymBaseChange.hypS_baseChange _ _ _ _ _ φ _ _ P.isLB P'.isLB hφ hiso' hS) lev' (SecM.toSec P'.A (c₁ hU.default))
    hc₁.unique (fun i => c₂ (e i)) (fun T _ u => ?_) h P φ hg hφ hiso' lev.pt hlev
  · obtain ⟨a, ha, b, hb, e⟩ := frac x
    exact ⟨a, h ha, b, h hb, e⟩
  · obtain ⟨c, hc⟩ := hc₂ T u
    exact ⟨c.reindex e.symm, fun i => by rw [Module.Basis.reindex_apply, hc, Equiv.symm_symm]⟩

end
