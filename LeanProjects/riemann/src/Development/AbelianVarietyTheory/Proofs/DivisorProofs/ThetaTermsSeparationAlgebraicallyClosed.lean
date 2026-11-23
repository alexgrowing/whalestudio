import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantToUnitLeft
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueScalar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SepAtBIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGeneratorThetaConstantsOverAlgClosedExtens
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaPtEqUnitMulTh
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.Sep.TorsValue

open GlobalTheory.UT GlobalTheory.UT.SymFrame GlobalTheory.FieldBaseChange GlobalTheory.TorRef

def cH {R : Type} [CommRing R] {Z : Scheme.{0}} (π : Z ⟶ Spec (CommRingCat.of R)) (z : Z) : R →+* Z.presheaf.stalk z :=
  ((Z.presheaf.germ ⊤ z trivial).hom.comp π.appTop.hom).comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom

theorem constVal_eq {R : Type} [CommRing R] {Z : Scheme.{0}} (π : Z ⟶ Spec (CommRingCat.of R)) (z : Z) (c : R) :
    constVal π z c = cH π z c := gs_eq π z ⊤ trivial _

theorem gs_top_eq {R : Type} [CommRing R] {Z : Scheme.{0}} (π : Z ⟶ Spec (CommRingCat.of R)) (z : Z)
    (a : Γ(Spec (CommRingCat.of R), ⊤)) :
    gs π z ⊤ a = cH π z ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom a) := by
  rw [← constVal_eq, constVal, ← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply]

theorem cH_specMap {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') (z : Spec (CommRingCat.of R')) (c : R) :
    cH (Spec.map (CommRingCat.ofHom φ)) z c = cH (𝟙 _) z (φ c) := by
  rw [← constVal_eq, ← constVal_eq, ← constVal_specMap, Category.id_comp]

theorem exists_const_sec {R : Type} [CommRing R] {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K]
    {φ : K → (Spec (CommRingCat.of R) ⟶ X)} {ε : K → ℤ}
    (h : ∀ (U : Type) [CommGroup U] (h : (Spec (CommRingCat.of R) ⟶ X) → U), ∏ k, h (φ k) ^ ε k = 1)
    (s : LB.Sec (LB.LinComb L φ ε)) :
    ∃ a : R, ∀ (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of R)) (z : Z) (J), Good L z J → sval s r z J = cH r z a := by
  obtain ⟨s', hs'⟩ := exists_sec hL (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim)
    (fun U _ h' => (h U h').trans (Fintype.prod_empty _).symm) s
  have le : (⊤ : (Spec (CommRingCat.of R)).Opens) ≤ LB.wchart L (K := PEmpty) PEmpty.elim PEmpty.elim :=
    (wchart_empty _).ge
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom
    (((Spec (CommRingCat.of R)).presheaf.map (homOfLE le).op).hom (s'.f PEmpty.elim)), fun Z r z J hJ => ?_⟩
  rw [← hs' Z r z J hJ, sval_of s' r z J PEmpty.elim (fun k => k.elim), ← gs_top_eq]
  exact (gs_res r z le trivial _).symm

theorem exists_root_of_pow_eq {K : Type} [Field K] {M : ℕ} (hM : 1 ≤ M) {c d : K} (h : c ^ M = d ^ M) :
    ∃ ζ : K, ζ ^ M = 1 ∧ c = ζ * d := by
  by_cases hd : d = 0
  · subst hd
    rw [zero_pow (by omega)] at h
    exact ⟨1, one_pow _, by rw [pow_eq_zero_iff (by omega)] at h; simp [h]⟩
  · exact ⟨c / d, by rw [div_pow, h, div_self (pow_ne_zero _ hd)], by field_simp⟩

variable {V : Type} [CommRing V] [IsDomain V] {D : DegPre V}

theorem prod_famB {T : Over (Spec (CommRingCat.of V))} (p : T ⟶ D.P.A) {U : Type} [CommGroup U]
    (h : (T.left ⟶ D.P.A.left) → U) : ∏ i, h (p.left ≫ D.famφB 0 i) ^ DegPre.famε 1 i = h p.left := by
  rw [Fin.prod_univ_four]
  have e₀ : p.left ≫ D.famφB 0 0 = p.left := Category.comp_id _
  have e₁ : p.left ≫ D.famφB 0 1 = p.left := by
    refine (Over.comp_left _ _ _ p (padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ D.c 0))).symm.trans (congrArg (fun q : T ⟶ D.P.A => q.left) ?_)
    rw [ThetaOne.c_zero, MonObj.comp_one]
    exact (congrArg (p ≫ ·) (_root_.mul_one (𝟙 D.P.A))).trans (Category.comp_id p)
  have e₂ : D.famφB 0 2 = D.famφB 0 3 := by
    show (toUnit D.P.A ≫ D.c 0).left = (toUnit D.P.A ≫ η[D.P.A]).left
    rw [ThetaOne.c_zero, eta_eq]
  rw [e₀, e₁, e₂]
  simp [DegPre.famε]

theorem exists_kap_of_torsFrame {N : ℕ} {ρ₀ : LB.Gen (D.P.L.pull (eSec D.P.A))} (hρ : ρ₀.IsGen)
    {T : Over (Spec (CommRingCat.of V))} {x : T ⟶ D.P.A} {τ} (H : IsTorsFrame D.P ρ₀ N x τ) :
    ∃ κ : LB.Gen (kapLB D (𝟙 D.P.A ^ N) (N ^ 2) 1), Normd κ ∧ ∀ z J, Good D.P.L z J →
      val τ (𝟙 _) z J ^ (N ^ 2) = val κ x.left z J *
        val (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) ρ₀ T.hom z J ^ (N ^ 2) := by
  obtain ⟨-, -, α, hα, hn, hc⟩ := H
  have ra := grep_gen (Y := D.P.A) α hα (𝟙 _)
  have rr := grep_gen (Y := D.P.A) (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) ρ₀ hρ D.P.A.hom
  obtain ⟨κ, hκ, vκ⟩ := ((ra.mul rr).mul (rr.pow (N ^ 2)).inv).normd
    ![𝟙 _, (𝟙 D.P.A ^ N).left, (1 : D.P.A ⟶ D.P.A).left] ![((N ^ 2 : ℕ) : ℤ), -((1 : ℕ) : ℤ), ((1 : ℕ) : ℤ) - ((N ^ 2 : ℕ) : ℤ)]
    (fun U _ h => by
      rw [Fin.prod_univ_three, Fin.prod_univ_two, Fintype.prod_unique]
      show h (𝟙 _ ≫ 𝟙 _) ^ ((N : ℤ) ^ 2) * h (𝟙 _ ≫ (𝟙 D.P.A ^ N).left) ^ (-1 : ℤ) * h (1 : D.P.A ⟶ D.P.A).left ^ (1 : ℤ) *
        ((h (1 : D.P.A ⟶ D.P.A).left ^ (1 : ℤ)) ^ (N ^ 2))⁻¹ = h (𝟙 _) ^ ((N ^ 2 : ℕ) : ℤ) *
          h (𝟙 D.P.A ^ N).left ^ (-((1 : ℕ) : ℤ)) * h (1 : D.P.A ⟶ D.P.A).left ^ (((1 : ℕ) : ℤ) - ((N ^ 2 : ℕ) : ℤ))
      rw [Category.id_comp, Category.id_comp]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      push_cast
      module)
    (fun y J hJ => by
      have q₁ := val_corr hJ hn (𝟙 _)
      rw [val_pull hJ, val_mul hJ, val_inv, Category.id_comp] at q₁
      have p₁ : val (rigPow D.P.A D.P.L ρ₀ ((N : ℤ) ^ 2)) (𝟙 _) y J =
        val (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) ρ₀ (𝟙 _) y J ^ ((N : ℤ) ^ 2) := map_zpow _ _ _
      rw [p₁] at q₁
      beta_reduce
      rw [Category.comp_id, Over.w, ← eta_eq]
      change val α (eSec D.P.A) y J * val ρ₀ (𝟙 _) y J * (val ρ₀ (𝟙 _) y J ^ (N ^ 2))⁻¹ = 1
      rw [q₁, ← Nat.cast_pow, zpow_natCast]
      simp [mul_comm])
  refine ⟨κ, hκ, fun z J hJ => ?_⟩
  have q₂ := val_corr hJ hc (𝟙 _)
  rw [val_mul hJ, val_pull hJ, ThetaCompare.val_rigT _ _ hJ, Category.id_comp] at q₂
  have p₂ : val (powFrame D.P.A D.P.L x τ ((N : ℤ) ^ 2)) (𝟙 _) z J = val τ (𝟙 _) z J ^ ((N : ℤ) ^ 2) := map_zpow _ _ _
  replace p₂ := p₂.trans ((congrArg _ (Nat.cast_pow N 2).symm).trans (zpow_natCast _ _))
  rw [p₂, zpow_one] at q₂
  have v := vκ T x z J hJ
  beta_reduce at v
  rw [Category.comp_id, Over.w] at v
  rw [q₂]
  exact ((congrArg (· * _) v).trans (inv_mul_cancel_right _ _)).symm

theorem toUnit_left' (T : Over (Spec (CommRingCat.of V))) : (toUnit T).left = T.hom :=
  (Category.comp_id _).symm.trans (Over.w (toUnit T))

theorem cH_gen (z : (TF (R := V) (FractionRing V)).left) (a : V) :
    cH (toUnit (TF (R := V) (FractionRing V))).left z a = CoefBasic.cstH z (algebraMap V (FractionRing V) a) := by
  rw [Frames.toUnit_left_eq]
  exact cH_specMap _ z a

theorem exists_integral_frame [IsLocalRing V] [IsNoetherianRing V] [IsIntegrallyClosed V] {N : ℕ} (hN : 1 ≤ N)
    (g : GtPtF D (FractionRing V)) (b : 𝟙_ (Over (Spec (CommRingCat.of V))) ⟶ D.P.A)
    (hgb : g.b = toUnit _ ≫ b) (ho : ∃ o, GtPtF.IsNsmul N g o ∧ o.IsZero)
    (w : Frm D (FractionRing V) 1 g.b)
    (hw : w.IsGen ∧ ∀ κ : LB.Gen (kapLB D (𝟙 D.P.A ^ N) (N ^ 2) 1), Normd κ → ∀ z J, Good D.P.L z J →
      val w (𝟙 _) z J ^ (N ^ 2) * val κ g.b.left z J = 1) :
    ∃ (t : LB.Gen (LB.LinComb D.P.L ![(η[D.P.A]).left, b.left] (DegPre.lineε 1))) (u : V), t.IsGen ∧
      (∀ z J, Good D.P.L z J → (val w (𝟙 _) z J).val = cst (FractionRing V) z (algebraMap V (FractionRing V) u) *
        (val t (toUnit (TF (R := V) (FractionRing V))).left z J).val) ∧
      ∀ κ : LB.Gen (kapLB D (𝟙 D.P.A ^ N) (N ^ 2) 1), Normd κ → ∀ (T : Over (Spec (CommRingCat.of V))) (z : T.left) (J),
        Good D.P.L z J → (cH (toUnit T).left z u * (val t (toUnit T).left z J).val) ^ (N ^ 2) *
          (val κ (toUnit T ≫ b).left z J).val = 1 := by
  obtain ⟨t, ht⟩ := exists_gen_of_local D.P.L D.P.isLB ![(η[D.P.A]).left, b.left] (DegPre.lineε 1)
  obtain ⟨u, hu, hκ⟩ := Frames.frame_unit hN g b hgb ho w hw t ht
  have hbN := (Frames.torsion_of_nsmul g b hgb ho).2
  refine ⟨t, u, ht, hu, fun κ hκn T z J hJ => ?_⟩
  obtain ⟨s, hs, vs⟩ := (((grep_gen t ht (𝟙 _)).pow (N ^ 2)).mul (grep_kap κ hκn.1 b)).out D.P.isLB (K := PEmpty)
    PEmpty.elim PEmpty.elim (fun U _ h => by
      rw [Fin.prod_univ_two, hbN, ← eta_eq, Fintype.prod_empty]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, DegPre.lineε, Category.id_comp]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow, ofMul_one]
      rw [← natCast_zsmul]
      push_cast
      module)
  obtain ⟨a, ha⟩ := exists_const_sec D.P.isLB (fun U _ h => Fintype.prod_empty _) (Geo.Tor.genSec s hs)
  have key : ∀ (T : Over (Spec (CommRingCat.of V))) (z : T.left) (J), Good D.P.L z J →
      (val t (toUnit T).left z J).val ^ (N ^ 2) * (val κ (toUnit T ≫ b).left z J).val = cH (toUnit T).left z a :=
    fun T z J hJ => by
      have v := vs T (toUnit T) z J hJ
      beta_reduce at v
      rw [Category.comp_id] at v
      rw [← ha _ _ z J hJ, sval_genSec s hs _ z hJ, v, Units.val_mul, Units.val_pow_eq_pow_val]
  have hua : (u : V) ^ (N ^ 2) * a = 1 := by
    obtain ⟨y⟩ := CoefBasic.exists_pt (R := V) (F := FractionRing V)
    obtain ⟨I, hI⟩ := CoefBasic.exists_good' D.P.isLB y
    have e₁ := hκ κ hκn y I hI
    have e₂ := key _ y I hI
    rw [← hgb, cH_gen] at e₂
    rw [Units.val_mul, Units.val_pow_eq_pow_val, mul_comm (val κ g.b.left y I).val, e₂, CoefBasic.cst_eq, ← map_pow,
      ← map_mul, ← map_one (CoefBasic.cstH y)] at e₁
    exact IsFractionRing.injective V (FractionRing V) (by rw [map_mul, map_pow, CoefBasic.cstH_inj y e₁, map_one])
  rw [mul_pow, _root_.mul_assoc, key T z J hJ, ← map_pow, ← map_mul, hua, map_one]

theorem exists_integral_value (θ : D.SecB 1 0) (b : 𝟙_ (Over (Spec (CommRingCat.of V))) ⟶ D.P.A)
    (t : LB.Gen (LB.LinComb D.P.L ![(η[D.P.A]).left, b.left] (DegPre.lineε 1))) (ht : t.IsGen) :
    ∃ a : V, ∀ (T : Over (Spec (CommRingCat.of V))) (z : T.left) (J), Good D.P.L z J →
      sval θ (toUnit T ≫ b).left z J * (val t (toUnit T).left z J).val =
        cH (toUnit T).left z a * (rigV D T.hom z J).val := by
  let t' := LB.mulGen D.P.L _ _ _ _ t (LB.invGen D.P.L (fun _ : PUnit => eSec D.P.A) (fun _ => 1) D.rig)
  have ht' : t'.IsGen := mulGen_isGen _ _ _ _ _ _ _ ht (invGen_isGen _ _ _ _ D.rig_gen)
  obtain ⟨a, ha⟩ := exists_const_sec D.P.isLB (fun U _ h => by
    rw [Fintype.prod_sum_type, Fintype.prod_sum_type, Fin.prod_univ_two]
    refine (congrArg₂ (· * ·) (prod_famB b h) rfl).trans ?_
    simp [DegPre.lineε, eSec]) (pullMulSec θ b.left t' ht')
  refine ⟨a, fun T z J hJ => ?_⟩
  have e := ha _ (toUnit T).left z J hJ
  rw [sval_pullMulSec _ _ _ _ _ _ hJ, val_mul hJ, val_inv] at e
  rw [← e, ← toUnit_left' T, Units.val_mul, _root_.mul_assoc, _root_.mul_assoc]
  refine congrArg₂ (· * ·) rfl ?_
  exact ((congrArg (_ * ·) (Units.inv_mul _)).trans (_root_.mul_one _)).symm

theorem integral_terms [IsLocalRing V] [IsNoetherianRing V] [IsIntegrallyClosed V] {N : ℕ} (hN : 1 ≤ N)
    (θ : SecOver D.P.A.hom (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1)))
    (hθ : ∀ th : Fam D (FractionRing V) 1, ∃ l : FractionRing V,
      famProj D (FractionRing V) 1 0 th = l • ThetaOne.termF D (FractionRing V) 1 0 θ)
    {X C : Type} [AddCommGroup X] (e : X ≃+ D.X) (Tm : X → C → V) (hT : IsThetaTerms D N e Tm) :
    ∃ (b : C → (𝟙_ (Over (Sp V)) ⟶ D.P.A)) (a₁ : V),
      (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Sp V) (p : Over.mk x ⟶ D.P.A), p ^ N = 1 →
        ∃ c, p = toUnit _ ≫ b c) ∧
      ∀ c, ∃ (t : LB.Gen (LB.LinComb D.P.L ![(η[D.P.A]).left, (b c).left] (DegPre.lineε 1))) (u : V),
        (∀ κ : LB.Gen (kapLB D (𝟙 D.P.A ^ N) (N ^ 2) 1), Normd κ → ∀ (T : Over (Spec (CommRingCat.of V))) (z : T.left) (J),
          Good D.P.L z J → (cH (toUnit T).left z u * (val t (toUnit T).left z J).val) ^ (N ^ 2) *
            (val κ (toUnit T ≫ b c).left z J).val = 1) ∧
        ∀ (T : Over (Spec (CommRingCat.of V))) (z : T.left) (J), Good D.P.L z J →
          sval θ (toUnit T ≫ b c).left z J * (cH (toUnit T).left z u * (val t (toUnit T).left z J).val) =
            cH (toUnit T).left z (Tm 0 c * a₁) * (rigV D T.hom z J).val := by
  obtain ⟨th, g, b, w, h₁, h₂, h₃, h₄, h₅, c₁, h₆⟩ := hT
  obtain ⟨l, hl⟩ := hθ th
  choose t u ht hu hκ using fun c => exists_integral_frame hN (g c) (b c) (h₁ c) (h₂ c) (w c) (h₄ c)
  choose a ha using fun c => exists_integral_value θ (b c) (t c) (ht c)
  have gen : ∀ c, algebraMap V (FractionRing V) (Tm 0 c) = l * algebraMap V (FractionRing V) (u c * a c) := fun c => by
    obtain ⟨y⟩ := CoefBasic.exists_pt (R := V) (F := FractionRing V)
    obtain ⟨I, hI⟩ := CoefBasic.exists_good' D.P.isLB y
    have e₀ := h₅ 0 c
    rw [map_zero] at e₀
    have e₁ := e₀ y I hI
    have e₂ : sval (th.s 0) (lift (𝟙 (TF (R := V) (FractionRing V))) (g c).b).left y I =
        CoefBasic.cstH y l * sval θ (toUnit _ ≫ b c).left y I := by
      refine (congrArg (fun s : FamTerm D (FractionRing V) 1 0 => sval s _ y I) hl).trans
        ((sval_smul' hI _ l _).trans (congrArg₂ (· * ·) ?_ ((sval_pullOver _ _ θ _ hI).trans ?_)))
      · rw [famBase, ← Over.comp_left, lift_fst]
        exact CoefBasic.cst_eq y l
      · rw [← Over.comp_left, lift_snd, h₁]
    have e₃ := ha c _ y I hI
    rw [e₂, val_corr hI (g c).s_zero, val_one, Units.val_one, _root_.mul_one, hu c y I hI, pow_one, CoefBasic.cst_eq,
      CoefBasic.cst_eq] at e₁
    rw [cH_gen] at e₃
    apply CoefBasic.cstH_inj y
    apply (rigV D (TF (R := V) (FractionRing V)).hom y I).isUnit.mul_right_cancel
    rw [e₁, map_mul, map_mul, map_mul]
    linear_combination (CoefBasic.cstH y l * CoefBasic.cstH y (algebraMap V (FractionRing V) (u c))) * e₃
  refine ⟨b, u c₁ * a c₁, h₃, fun c => ⟨t c, u c, hκ c, fun T z J hJ => ?_⟩⟩
  have r : Tm 0 c * (u c₁ * a c₁) = u c * a c := IsFractionRing.injective V (FractionRing V) (by
    have g₁ := gen c₁
    rw [h₆, map_one] at g₁
    rw [map_mul, gen c]
    linear_combination (- algebraMap V (FractionRing V) (u c * a c)) * g₁)
  rw [r, map_mul]
  linear_combination (cH (toUnit T).left z (u c)) * ha c T z J hJ

omit [IsDomain V] in

def kH {K : Type} [CommRing K] (ev : V →+* K) (z : (Over.mk (spMap ev)).left) :
    K →+* (Over.mk (spMap ev)).left.presheaf.stalk z := cH (𝟙 (Sp K)) z

theorem exists_scalar (θ : SecOver D.P.A.hom (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))) {K : Type} [CommRing K]
    (ev : V →+* K) (hθ : ThetaOne.OneBasisAt D ev (ThetaOne.pullTo D ev θ))
    (th : LB.Sec (LPow D.P.A D.P.L ((1 : ℕ) : ℤ) (Over.mk (spMap ev)))) :
    ∃ r : K, ∀ (x : Over.mk (spMap ev) ⟶ D.P.A) (z : (Over.mk (spMap ev)).left) (J), Good D.P.L z J →
      sval (φ := fun _ : Fin 1 => (snd (Over.mk (spMap ev)) D.P.A).left) (ε := fun _ => ((1 : ℕ) : ℤ)) th
        (ptSecT D.P.A x).left z J = kH ev z r * sval θ x.left z J := by
  obtain ⟨s, hs⟩ := exists_sec D.P.isLB (φ := fun _ : Fin 1 => (snd (Over.mk (spMap ev)) D.P.A).left)
    (ε := fun _ => ((1 : ℕ) : ℤ)) (φ' := fun i => (snd (Over.mk (spMap ev)) D.P.A).left ≫ D.famφB 0 i)
    (ε' := DegPre.famε 1) (fun U _ h => by
      rw [prod_famB, Fin.prod_univ_one, Nat.cast_one, zpow_one]) th
  obtain ⟨r, hr, -⟩ := hθ s
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom (r 0), fun x z J hJ => ?_⟩
  rw [← hs _ _ z J hJ]
  have hy := hJ.mem (fun i => (snd (Over.mk (spMap ev)) D.P.A).left ≫ D.famφB 0 i) (ptSecT D.P.A x).left
  refine (congrArg (gs _ z _) ((hr _).trans (Fin.sum_univ_one _))).trans ((gs_mul _ z _ hy _ _).trans
    (congrArg₂ (· * ·) ?_ ?_))
  · refine (gs_res _ z _ hy _).trans ((gs_pull _ (fst (Over.mk (spMap ev)) D.P.A).left z ⊤ trivial _).trans ?_)
    rw [← Over.comp_left, ptSecT, lift_fst]
    exact gs_top_eq (𝟙 (Sp K)) z _
  · refine (sval_pullOver _ _ θ _ hJ).trans ?_
    rw [← Over.comp_left, ptSecT, lift_snd]

end GlobalTheory.Poinc.Sep.TorsValue

namespace GlobalTheory.Poinc.Sep.TorsValue

open GlobalTheory.UT GlobalTheory.UT.SymFrame GlobalTheory.FieldBaseChange GlobalTheory.TorRef

theorem value_eq_root_mul_term {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] (hV : IsCN V) (D : DegPre V) {N : ℕ}
    (hN : 1 ≤ N) {X C : Type} [AddCommGroup X] (e : X ≃+ D.X) (Tm : X → C → V) (hT : IsThetaTerms D N e Tm)
    {K : Type} [Field K] [IsAlgClosed K] (ev : V →+* K) (ρ₀ : LB.Gen (D.P.L.pull (eSec D.P.A))) (hρ : ρ₀.IsGen)
    (th : LB.Sec (LPow D.P.A D.P.L ((1 : ℕ) : ℤ) (Over.mk (spMap ev)))) :
    ∃ lam : K, ∀ (x : Over.mk (spMap ev) ⟶ D.P.A)
      (τ : LB.Gen (LB.LinComb D.P.L (Y := (Over.mk (spMap ev)).left) (K := Fin 1) (fun _ => x.left) (fun _ => 1))) (c : K),
      IsTorsFrame D.P ρ₀ N x τ →
      IsValueAt D.P.A D.P.L ((1 : ℕ) : ℤ) th x (powFrame D.P.A D.P.L x τ ((1 : ℕ) : ℤ))
        ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom c) →
      ∃ (c₀ : C) (ζ : K), ζ ^ (N ^ 2) = 1 ∧ c = ζ * (lam * ev (Tm 0 c₀)) := by
  haveI : IsNoetherianRing V := hV.1
  haveI : IsIntegrallyClosed V := hV.2.1
  obtain ⟨θ, hθ₁, -, hθ₂, -⟩ := ThetaOne.main hV D
  obtain ⟨b, a₁, hb, hc⟩ := integral_terms hN θ (fun th' => (hθ₂ _ th').exists) e Tm hT
  obtain ⟨r, hr⟩ := exists_scalar θ ev (hθ₁ K ev _ (ThetaOne.isPullSecLC_pullTo D ev θ)) th
  obtain ⟨δ, hδ⟩ := Geo.Tor.exists_ratio D.P.isLB (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) rfl D.rig ρ₀
    D.rig_gen hρ
  refine ⟨r * ev a₁ * ev ((Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom δ.val), fun x τ c hτ hv => ?_⟩
  obtain ⟨c₀, rfl⟩ := hb K (spMap ev) x hτ.1
  obtain ⟨t, u, hκ, hθ⟩ := hc c₀
  obtain ⟨κ, hκn, hτκ⟩ := exists_kap_of_torsFrame hρ hτ
  refine ⟨c₀, exists_root_of_pow_eq (Nat.one_le_pow _ _ hN) ?_⟩
  let z : (Over.mk (spMap ev)).left := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K)
  obtain ⟨J, hJ⟩ := CoefBasic.exists_good' D.P.isLB z
  have k : ∀ a : V, cH (toUnit (Over.mk (spMap ev))).left z a = kH ev z (ev a) := fun a => by
    rw [toUnit_left']; exact cH_specMap ev z a
  have e₁ := (ThetaCompare.sval_valueAt hv hJ).symm.trans (hr _ z J hJ)
  have p : val (powFrame D.P.A D.P.L (toUnit _ ≫ b c₀) τ ((1 : ℕ) : ℤ)) (𝟙 _) z J = val τ (𝟙 _) z J :=
    (map_zpow _ _ _).trans (zpow_one _)
  rw [p] at e₁
  have q : kH ev z c = gs (𝟙 (Over.mk (spMap ev)).left) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom c) :=
    (constVal_eq (𝟙 (Sp K)) z c).symm
  rw [← q] at e₁
  have e₂ := hθ _ z J hJ
  have e₃ := hκ κ hκn _ z J hJ
  have e₄ := congrArg Units.val (hτκ z J hJ)
  have e₅ : (rigV D (Over.mk (spMap ev)).hom z J).val =
      kH ev z (ev ((Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom δ.val)) *
        (val (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) ρ₀ (Over.mk (spMap ev)).hom z J).val := by
    refine (congrArg Units.val (hδ _ _ z J hJ)).trans (congrArg (· * _) ?_)
    exact (gs_unit _ z ⊤ trivial δ).symm.trans ((gs_top_eq _ z _).trans (cH_specMap ev z _))
  rw [k, k, e₅] at e₂
  rw [k] at e₃
  apply (kH ev z).injective
  have alg : ∀ {S : Type} [CommRing S] (M : ℕ) (τ κ ρ : Sˣ) (c r θ t T δ : S), c * τ = r * θ → θ * t = T * (δ * ρ) →
      t ^ M * κ = 1 → (τ ^ M).val = (κ * ρ ^ M).val → c ^ M = (r * δ * T) ^ M := by
    intro S _ M τ κ ρ c r θ t T δ a₁ a₂ a₃ a₄
    rw [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val] at a₄
    have a₅ : c * (τ * t) = r * δ * T * ρ := by linear_combination t * a₁ + r * a₂
    have a₆ : (τ * t) ^ M = ρ ^ M := by rw [mul_pow, a₄]; linear_combination (ρ : S) ^ M * a₃
    apply (ρ.isUnit.pow M).mul_right_cancel
    rw [← mul_pow (r * δ * T), ← a₅, mul_pow c, a₆]
  refine (map_pow _ _ _).trans ((alg _ _ _ _ _ _ _ _ _ _ e₁ e₂ e₃ e₄).trans ?_)
  simp only [map_pow, map_mul]
  congr 1
  ring

end GlobalTheory.Poinc.Sep.TorsValue

section
open NumberField ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open GlobalTheory GlobalTheory.USep

theorem GlobalTheory.Poinc.Sep.TorsValue.values_in_torsFrames : ∀ (m : ℕ), Odd m → 3 ≤ m → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → IsUnit (m : V₁) → ∀ (D : DegPre V₁) (X C : Type) [AddCommGroup X] (e : X ≃+ D.X) (u : X → C → V₁) (mo : X → V₁), (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → GlobalTheory.Poinc.Sep.IsThetaTerms D (m ^ 2) e (fun mu c => u mu c * mo mu) → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (ρ₀ : LB.Gen (D.P.L.pull (eSec D.P.A))), ρ₀.IsGen → ∀ (th : LB.Sec (LPow D.P.A D.P.L ((1 : ℕ) : ℤ) (Over.mk (spMap ev)))), IsGenSec D.P.A D.P.L ((1 : ℕ) : ℤ) th → ∃ (M : ℕ) (lam : K), 1 ≤ M ∧ ∀ (x : Over.mk (spMap ev) ⟶ D.P.A) (τ : LB.Gen (LB.LinComb D.P.L (Y := (Over.mk (spMap ev)).left) (K := Fin 1) (fun _ => x.left) (fun _ => 1))) (c : K), IsTorsFrame D.P ρ₀ (m ^ 2) x τ → IsValueAt D.P.A D.P.L ((1 : ℕ) : ℤ) th x (powFrame D.P.A D.P.L x τ ((1 : ℕ) : ℤ)) (GlobalTheory.Ex.fnOf c) → ∃ (c₀ : C) (ζ : K), ζ ^ M = 1 ∧ c = lam * ζ * ev (u 0 c₀) := by
  intro m _ hm V₁ _ _ _ hV _ D X C _ e u mo _ hT K _ _ ev ρ₀ hρ th _
  have hN : 1 ≤ m ^ 2 := Nat.one_le_pow _ _ (by omega)
  obtain ⟨lam, h⟩ := GlobalTheory.Poinc.Sep.TorsValue.value_eq_root_mul_term hV D hN e _ hT ev ρ₀ hρ th
  refine ⟨(m ^ 2) ^ 2, lam * ev (mo 0), Nat.one_le_pow _ _ hN, fun x τ c hτ hv => ?_⟩
  obtain ⟨c₀, ζ, hζ, hc⟩ := h x τ c hτ hv
  exact ⟨c₀, ζ, hζ, by rw [hc, map_mul]; ring⟩

end
