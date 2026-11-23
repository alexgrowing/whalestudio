import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsReps
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LFunctionEquationGlobal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitPlaceDegreeOneEmbedding
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralBasisLocalIntegrality
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNumeratorIdealOfAntiInvariantDivisor
import GroundTheory.HeightsAndTheta.Theta.AlgebraicHecke.Characters
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel
open GroundTheory.Global.AdicLiesOver
open GlobalTheory.CompanionTheory.FexTheta

noncomputable section
namespace GlobalTheory.CompanionTheory.KOneReps
variable {K : Type} [Field K] [NumberField K]

theorem ord_eq_neg_log (w : HeightOneSpectrum (𝓞 K)) {x : w.adicCompletion K} (hx : x ≠ 0) :
    ord x = -WithZero.log (Valued.v x) := by
  have A : ∀ {y : w.adicCompletion K}, normalizedValuation (w.adicCompletion K) y ≤ 1 ↔ Valued.v y ≤ 1 :=
    fun {y} => normalizedValuation_le_one_iff.trans (GlobalTheory.CompanionTheory.IntCoord.mem_O_iff w y)
  have E : (normalizedValuation (w.adicCompletion K)).IsEquiv
      (Valued.v : Valuation (w.adicCompletion K) (WithZero (Multiplicative ℤ))) :=
    Valuation.isEquiv_iff_val_le_one.2 A
  obtain ⟨π, hπ⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective K w (WithZero.exp (-1 : ℤ))
  obtain ⟨z, hz⟩ := exists_normalizedValuation_eq (w.adicCompletion K) (-1)
  have hπ0 : π ≠ 0 := by
    rintro rfl
    exact WithZero.exp_ne_zero (hπ.symm.trans (map_zero _))
  have hlt : WithZero.exp (-1 : ℤ) < 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  have hπn : normalizedValuation (w.adicCompletion K) π = WithZero.exp (-1 : ℤ) := by
    have hne : normalizedValuation (w.adicCompletion K) π ≠ 0 := by simpa using hπ0
    apply le_antisymm
    · have h1 : normalizedValuation (w.adicCompletion K) π < 1 := E.lt_one_iff_lt_one.2 (hπ ▸ hlt)
      rw [← WithZero.exp_log hne] at h1 ⊢
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h1
      rw [WithZero.exp_le_exp]
      omega
    · have h1 : Valued.v z < 1 := E.lt_one_iff_lt_one.1 (hz ▸ hlt)
      have hz0 : Valued.v z ≠ 0 := by
        have : z ≠ 0 := by
          rintro rfl
          exact WithZero.exp_ne_zero (hz.symm.trans (map_zero _))
        simpa using this
      have h2 : Valued.v z ≤ Valued.v π := by
        rw [hπ]
        rw [← WithZero.exp_log hz0] at h1 ⊢
        rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h1
        rw [WithZero.exp_le_exp]
        omega
      rw [← hz]
      exact E.le_iff_le.2 h2
  have hv0 : Valued.v x ≠ 0 := by simpa using hx
  set n : ℤ := WithZero.log (Valued.v x) with hn
  have hvx : Valued.v x = WithZero.exp n := (WithZero.exp_log hv0).symm
  have h1 : Valued.v (x * π ^ n) = 1 := by
    rw [map_mul, map_zpow₀, hπ, hvx, ← WithZero.exp_zsmul, ← WithZero.exp_add, ← WithZero.exp_zero]
    congr 1
    simp
  have h2 : normalizedValuation (w.adicCompletion K) (x * π ^ n) = 1 := E.eq_one_iff_eq_one.2 h1
  rw [map_mul, map_zpow₀, hπn, ← WithZero.exp_zsmul] at h2
  have hne : normalizedValuation (w.adicCompletion K) x ≠ 0 := by simpa using hx
  rw [← WithZero.exp_log hne, ← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_inj] at h2
  rw [ord]
  simp at h2
  omega

theorem order_degreeOneEmbedding_valuation (h2 : Module.finrank ℚ K = 2) (v : Pl) (w₁ w₂ : PlK K)
    [w₁.asIdeal.LiesOver v.asIdeal] [w₂.asIdeal.LiesOver v.asIdeal] (hne : w₁ ≠ w₂) {ξ : K} (hξ : ξ ≠ 0) :
    dg1 v w₁ ξ ≠ 0 ∧ ord (dg1 v w₁ ξ) = -WithZero.log (w₁.valuation K ξ) := by
  obtain ⟨h1, e⟩ := GlobalTheory.CompanionTheory.SplitLift.split_place_degreeOne_embedding K h2 v w₁ w₂ hne
  have hb := GlobalTheory.CompanionTheory.BaseChangeFunctionalEquation.algebraMap_bijective v w₁ h1
  have ea := e ξ
  set a := dg1 v w₁ ξ with ha
  have hv : Valued.v (algebraMap (Qv v) (Kv K w₁) a) = w₁.valuation K ξ := by
    rw [ea]; exact GlobalTheory.CompanionTheory.IntCoord.val_alg w₁ ξ
  have hξ' : w₁.valuation K ξ ≠ 0 := by simpa using hξ
  have ha0 : a ≠ 0 := by
    rintro h
    rw [h, map_zero, map_zero] at hv
    exact hξ' hv.symm
  refine ⟨ha0, ?_⟩
  rw [valued_algebraMap_adicCompletion] at hv
  set r := w₁.asIdeal.ramificationIdx (𝓞 ℚ) with hr
  have hr1 : r = 1 := by
    obtain ⟨π, hπ⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective K w₁ (WithZero.exp (-1 : ℤ))
    obtain ⟨b, rfl⟩ := hb.2 π
    rw [valued_algebraMap_adicCompletion, ← hr] at hπ
    have hb0 : Valued.v b ≠ 0 := by
      intro h
      rw [h] at hπ
      rcases Nat.eq_zero_or_pos r with h0 | h0
      · rw [h0, pow_zero] at hπ
        rw [← WithZero.exp_zero, WithZero.exp_inj] at hπ
        omega
      · rw [zero_pow h0.ne'] at hπ
        exact WithZero.exp_ne_zero hπ.symm
    rw [← WithZero.exp_log hb0, ← WithZero.exp_nsmul, WithZero.exp_inj] at hπ
    have hd : (r : ℤ) ∣ 1 := ⟨-WithZero.log (Valued.v b), by simp at hπ; linarith⟩
    have := Int.natCast_dvd_natCast.1 (by simpa using hd : (r : ℤ) ∣ ((1 : ℕ) : ℤ))
    exact Nat.dvd_one.1 this
  rw [hr1, pow_one] at hv
  rw [ord_eq_neg_log v ha0, hv]

theorem absNorm_eq_of_liesOver (h2 : Module.finrank ℚ K = 2) (v : Pl) (w₁ w₂ : PlK K)
    [w₁.asIdeal.LiesOver v.asIdeal] [w₂.asIdeal.LiesOver v.asIdeal] :
    Ideal.absNorm w₁.asIdeal = Ideal.absNorm w₂.asIdeal := by
  haveI : Algebra.IsQuadraticExtension ℚ K := ⟨h2⟩
  haveI : IsGalois ℚ K := inferInstance
  haveI : IsGaloisGroup Gal(K/ℚ) (𝓞 ℚ) (𝓞 K) := IsGaloisGroup.of_isFractionRing _ _ _ ℚ K
  rw [Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver w₁.asIdeal v.asIdeal v.isPrime v.ne_bot,
    Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver w₂.asIdeal v.asIdeal v.isPrime v.ne_bot,
    Ideal.inertiaDeg'_eq_inertiaDeg, Ideal.inertiaDeg'_eq_inertiaDeg,
    Ideal.inertiaDeg_eq_of_isGaloisGroup v.asIdeal w₁.asIdeal w₂.asIdeal Gal(K/ℚ)]

open scoped nonZeroDivisors
variable {c : HeckeCharacter K} {v : Pl}

def pr (w : PlK K) : (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  Units.mk0 ((w.asIdeal : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)
    (FractionalIdeal.coeIdeal_ne_zero.2 w.ne_bot)

def p1 : LM c v → PlK K
  | LM.sp w₁ _ _ => w₁
  | LM.ns w .. => w

def gen : LM c v → (FractionalIdeal (𝓞 K)⁰ K)ˣ
  | LM.sp w₁ w₂ _ => pr w₁ / pr w₂
  | LM.ns .. => 1

def Idl (M : ∀ v : Pl, LM c v) (m : Pl →₀ ℤ) : (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  m.prod fun v n => gen (M v) ^ n

theorem Idl_add (M : ∀ v : Pl, LM c v) (a b : Pl →₀ ℤ) : Idl M (a + b) = Idl M a * Idl M b := by
  classical
  exact Finsupp.prod_add_index' (fun _ => zpow_zero _) (fun _ _ _ => zpow_add _ _ _)

theorem Idl_neg (M : ∀ v : Pl, LM c v) (a : Pl →₀ ℤ) : Idl M (-a) = (Idl M a)⁻¹ := by
  have h : Idl M (a + -a) = 1 := by
    rw [add_neg_cancel]; exact Finsupp.prod_zero_index
  rw [Idl_add] at h
  exact eq_inv_of_mul_eq_one_right h

theorem first_place_lies_over (L : LM c v) : (p1 L).asIdeal.LiesOver v.asIdeal := by
  cases L with
  | @sp w₁ w₂ i₁ i₂ Φ => exact i₁
  | @ns w i σ η Φ => exact i

theorem order_unit_split_datum_valuation (h2 : Module.finrank ℚ K = 2) (L : LM c v) (hok : L.ok) (hs : L.IsSp) (κ : Kˣ) :
    ord ((k1 L κ : (Qv v)ˣ) : Qv v) = -WithZero.log ((p1 L).valuation K (κ : K)) := by
  cases L with
  | @sp w₁ w₂ i₁ i₂ Φ =>
    obtain ⟨h0, h⟩ := order_degreeOneEmbedding_valuation h2 v w₁ w₂ hok.1 κ.ne_zero
    have : ((k1 (LM.sp w₁ w₂ Φ : LM c v) κ : (Qv v)ˣ) : Qv v) = dg1 v w₁ (κ : K) := by
      have h0' : e1 (LM.sp w₁ w₂ Φ : LM c v) (κ : K) ≠ 0 := h0
      simp only [k1, dif_neg h0', Units.val_mk0]
      rfl
    rw [this, h]
    rfl
  | @ns w i σ η Φ => exact hs.elim

theorem order_unit_field_datum_zero (L : LM c v) (hs : ¬ L.IsSp) (κ : Kˣ) : ord ((k1 L κ : (Qv v)ˣ) : Qv v) = 0 := by
  cases L with
  | @sp w₁ w₂ i₁ i₂ Φ => exact absurd trivial hs
  | @ns w i σ η Φ =>
    have h0 : e1 (LM.ns w σ η Φ : LM c v) (κ : K) ≠ 0 := one_ne_zero
    have : ((k1 (LM.ns w σ η Φ : LM c v) κ : (Qv v)ˣ) : Qv v) = 1 := by
      simp only [k1, dif_neg h0, Units.val_mk0]
      rfl
    rw [this]
    simp [ord]

theorem vK_support_finite (h2 : Module.finrank ℚ K = 2) (M : ∀ v : Pl, LM c v) (hM : ∀ v, (M v).ok) (κ : Kˣ) :
    (Function.support fun v : Pl => ord ((k1 (M v) κ : (Qv v)ˣ) : Qv v)).Finite := by
  have hS : {w : PlK K | w.valuation K (κ : K) ≠ 1}.Finite := by
    have h1 := HeightOneSpectrum.Support.finite (𝓞 K) (κ : K)
    have h2 := HeightOneSpectrum.Support.finite (𝓞 K) ((κ⁻¹ : Kˣ) : K)
    refine (h1.union h2).subset fun w hw => ?_
    rcases lt_or_gt_of_ne hw with h | h
    · right
      show 1 < w.valuation K ((κ⁻¹ : Kˣ) : K)
      rw [Units.val_inv_eq_inv_val, map_inv₀]
      exact (one_lt_inv₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 κ.ne_zero))).2 h
    · left; exact h
  have hU := hS.biUnion (t := fun w : PlK K => {v : Pl | w.asIdeal.LiesOver v.asIdeal}) fun w _ => by
    refine Set.Subsingleton.finite fun a ha b hb => ?_
    have ha' : w.asIdeal.LiesOver a.asIdeal := ha
    have hb' : w.asIdeal.LiesOver b.asIdeal := hb
    exact HeightOneSpectrum.ext (ha'.over.trans hb'.over.symm)
  refine hU.subset fun v hv => ?_
  by_cases hs : (M v).IsSp
  · have h := order_unit_split_datum_valuation h2 (M v) (hM v) hs κ
    have hv' : ord ((k1 (M v) κ : (Qv v)ˣ) : Qv v) ≠ 0 := hv
    refine Set.mem_biUnion (x := p1 (M v)) ?_ (first_place_lies_over (M v))
    intro h1
    rw [h1] at h
    simp at h
    exact hv' h
  · exact absurd (order_unit_field_datum_zero (M v) hs κ) hv

theorem vK_apply (h2 : Module.finrank ℚ K = 2) (M : ∀ v : Pl, LM c v) (hM : ∀ v, (M v).ok) (κ : Kˣ) (v : Pl) :
    vK M κ v = ord ((k1 (M v) κ : (Qv v)ˣ) : Qv v) := by
  rw [vK, dif_pos (vK_support_finite h2 M hM κ)]
  rfl

theorem vK_mul (h2 : Module.finrank ℚ K = 2) (M : ∀ v : Pl, LM c v) (hM : ∀ v, (M v).ok) (κ κ' : Kˣ) :
    vK M (κ * κ') = vK M κ + vK M κ' := by
  ext v
  rw [Finsupp.add_apply, vK_apply h2 M hM, vK_apply h2 M hM, vK_apply h2 M hM]
  by_cases hs : (M v).IsSp
  · rw [order_unit_split_datum_valuation h2 _ (hM v) hs, order_unit_split_datum_valuation h2 _ (hM v) hs, order_unit_split_datum_valuation h2 _ (hM v) hs, Units.val_mul, map_mul,
      WithZero.log_mul (by simp) (by simp)]
    ring
  · rw [order_unit_field_datum_zero _ hs, order_unit_field_datum_zero _ hs, order_unit_field_datum_zero _ hs]
    rfl

theorem vK_mem (h2 : Module.finrank ℚ K = 2) (M : ∀ v : Pl, LM c v) (hM : ∀ v, (M v).ok) (κ : Kˣ) :
    vK M κ ∈ Tm M := by
  intro v hv
  by_contra hs
  exact hv ((vK_apply h2 M hM κ v).trans (order_unit_field_datum_zero _ hs κ))

def vKim (h2 : Module.finrank ℚ K = 2) (M : ∀ v : Pl, LM c v) (hM : ∀ v, (M v).ok) : AddSubgroup (Pl →₀ ℤ) where
  carrier := {a | ∃ κ ∈ K1 K, a = vK M κ}
  zero_mem' := ⟨1, one_mem _, by
    have h := vK_mul h2 M hM 1 1
    rw [mul_one] at h
    exact (left_eq_add.1 h).symm⟩
  add_mem' := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a * b, mul_mem ha hb, (vK_mul h2 M hM a b).symm⟩
  neg_mem' := by
    rintro _ ⟨a, ha, rfl⟩
    refine ⟨a⁻¹, inv_mem ha, ?_⟩
    have h := vK_mul h2 M hM a a⁻¹
    have h1 : vK M (1 : Kˣ) = 0 := by
      have h := vK_mul h2 M hM 1 1
      rw [mul_one] at h
      exact (left_eq_add.1 h)
    rw [mul_inv_cancel, h1] at h
    exact neg_eq_of_add_eq_zero_right h.symm

theorem reps_of_finite {G C : Type} [AddCommGroup G] [Finite C] (T A : AddSubgroup G) (hAT : A ≤ T) (f : G → C)
    (h : ∀ m ∈ T, ∀ m' ∈ T, f m = f m' → m - m' ∈ A) :
    ∃ R : Finset G, (∀ r ∈ R, r ∈ T) ∧ ∀ m ∈ T, ∃! r, r ∈ R ∧ ∃ a ∈ A, m = r + a := by
  classical
  set A' : AddSubgroup T := A.addSubgroupOf T with hA'
  have key : ∀ x y : T, (QuotientAddGroup.mk x : T ⧸ A') = QuotientAddGroup.mk y ↔ (y : G) - x ∈ A := by
    intro x y
    rw [QuotientAddGroup.eq, hA', AddSubgroup.mem_addSubgroupOf]
    simp [sub_eq_neg_add]
  let s : C → T ⧸ A' := fun x => if hx : ∃ m : T, f m = x then QuotientAddGroup.mk hx.choose else 0
  have hs : Function.Surjective s := by
    intro q
    induction q using QuotientAddGroup.induction_on with
    | H m =>
      have hx : ∃ m' : T, f m' = f m := ⟨m, rfl⟩
      refine ⟨f m, ?_⟩
      simp only [s, dif_pos hx]
      exact (key _ _).2 (h _ m.2 _ hx.choose.2 hx.choose_spec.symm)
  haveI : Finite (T ⧸ A') := Finite.of_surjective s hs
  haveI : Fintype (T ⧸ A') := Fintype.ofFinite _
  refine ⟨Finset.univ.image fun q : T ⧸ A' => ((Quotient.out q : T) : G), ?_, ?_⟩
  · intro r hr
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hr
    exact (Quotient.out q : T).2
  · intro m hm
    have hq : (QuotientAddGroup.mk (Quotient.out (QuotientAddGroup.mk ⟨m, hm⟩ : T ⧸ A') : T) : T ⧸ A') =
        QuotientAddGroup.mk ⟨m, hm⟩ := QuotientAddGroup.out_eq' _
    refine ⟨((Quotient.out (QuotientAddGroup.mk ⟨m, hm⟩ : T ⧸ A') : T) : G),
      ⟨Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩, _, (key _ _).1 hq, by abel⟩, ?_⟩
    rintro r ⟨hr, a, ha, hma⟩
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hr
    have h1 : (QuotientAddGroup.mk (Quotient.out q : T) : T ⧸ A') = q := QuotientAddGroup.out_eq' _
    have h2' : q = QuotientAddGroup.mk ⟨m, hm⟩ := by
      rw [← h1]
      exact (key _ _).2 (by simpa [hma] using ha)
    rw [h2']

theorem liesOver_unique (w : PlK K) {a b : Pl} (ha : w.asIdeal.LiesOver a.asIdeal)
    (hb : w.asIdeal.LiesOver b.asIdeal) : a = b :=
  HeightOneSpectrum.ext (ha.over.trans hb.over.symm)

theorem count_gen_self (L : LM c v) (hok : L.ok) (hs : L.IsSp) :
    FractionalIdeal.count K (p1 L) (gen L : FractionalIdeal (𝓞 K)⁰ K) = 1 := by
  cases L with
  | @sp w₁ w₂ i₁ i₂ Φ =>
    have e : (gen (LM.sp w₁ w₂ Φ : LM c v) : FractionalIdeal (𝓞 K)⁰ K) =
        (pr w₁ : FractionalIdeal (𝓞 K)⁰ K) * (pr w₂ : FractionalIdeal (𝓞 K)⁰ K)⁻¹ := by
      simp [gen, div_eq_mul_inv]
    have e1 : p1 (LM.sp w₁ w₂ Φ : LM c v) = w₁ := rfl
    rw [e, e1, FractionalIdeal.count_mul K w₁ (pr w₁).ne_zero (inv_ne_zero (pr w₂).ne_zero),
      FractionalIdeal.count_inv]
    have a1 : FractionalIdeal.count K w₁ (pr w₁ : FractionalIdeal (𝓞 K)⁰ K) = 1 :=
      FractionalIdeal.count_self K w₁
    have a2 : FractionalIdeal.count K w₁ (pr w₂ : FractionalIdeal (𝓞 K)⁰ K) = 0 :=
      FractionalIdeal.count_maximal_coprime K w₁ (Ne.symm hok.1)
    rw [a1, a2]
    simp
  | @ns w i σ η Φ => exact hs.elim

theorem count_gen_other {v' : Pl} (L : LM c v') (w : PlK K) (hw : w.asIdeal.LiesOver v.asIdeal) (hv : v' ≠ v) :
    FractionalIdeal.count K w (gen L : FractionalIdeal (𝓞 K)⁰ K) = 0 := by
  cases L with
  | @sp w₁ w₂ i₁ i₂ Φ =>
    have e : (gen (LM.sp w₁ w₂ Φ : LM c v') : FractionalIdeal (𝓞 K)⁰ K) =
        (pr w₁ : FractionalIdeal (𝓞 K)⁰ K) * (pr w₂ : FractionalIdeal (𝓞 K)⁰ K)⁻¹ := by
      simp [gen, div_eq_mul_inv]
    rw [e, FractionalIdeal.count_mul K w (pr w₁).ne_zero (inv_ne_zero (pr w₂).ne_zero),
      FractionalIdeal.count_inv]
    have a1 : FractionalIdeal.count K w (pr w₁ : FractionalIdeal (𝓞 K)⁰ K) = 0 :=
      FractionalIdeal.count_maximal_coprime K w (fun h => hv (liesOver_unique w (h ▸ i₁) hw))
    have a2 : FractionalIdeal.count K w (pr w₂ : FractionalIdeal (𝓞 K)⁰ K) = 0 :=
      FractionalIdeal.count_maximal_coprime K w (fun h => hv (liesOver_unique w (h ▸ i₂) hw))
    rw [a1, a2]
    simp
  | @ns w' i σ η Φ =>
    simp [gen, FractionalIdeal.count_one]

theorem absNorm_gen (h2 : Module.finrank ℚ K = 2) (L : LM c v) :
    FractionalIdeal.absNorm (gen L : FractionalIdeal (𝓞 K)⁰ K) = 1 := by
  cases L with
  | @sp w₁ w₂ i₁ i₂ Φ =>
    have e : (gen (LM.sp w₁ w₂ Φ : LM c v) : FractionalIdeal (𝓞 K)⁰ K) =
        (pr w₁ : FractionalIdeal (𝓞 K)⁰ K) / (pr w₂ : FractionalIdeal (𝓞 K)⁰ K) := by
      simp [gen]
    have a (w : PlK K) : FractionalIdeal.absNorm (pr w : FractionalIdeal (𝓞 K)⁰ K) = (Ideal.absNorm w.asIdeal : ℚ) :=
      FractionalIdeal.coeIdeal_absNorm _
    rw [e, map_div₀, a, a, absNorm_eq_of_liesOver h2 v w₁ w₂]
    refine div_self ?_
    exact_mod_cast fun h => w₂.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  | @ns w i σ η Φ => simp [gen]

theorem count_Idl (M : ∀ v : Pl, LM c v) (hM : ∀ v, (M v).ok) (v : Pl) (hs : (M v).IsSp) (d : Pl →₀ ℤ) :
    FractionalIdeal.count K (p1 (M v)) (Idl M d : FractionalIdeal (𝓞 K)⁰ K) = d v := by
  classical
  induction d using Finsupp.induction_linear with
  | zero =>
    have : Idl M (0 : Pl →₀ ℤ) = 1 := Finsupp.prod_zero_index
    rw [this]
    simp [FractionalIdeal.count_one]
  | add a b ha hb =>
    rw [Idl_add, Units.val_mul, FractionalIdeal.count_mul K _ (Idl M a).ne_zero (Idl M b).ne_zero, ha, hb]
    rfl
  | single v' n =>
    have e : Idl M (Finsupp.single v' n) = gen (M v') ^ n := Finsupp.prod_single_index (zpow_zero _)
    rw [e, Units.val_zpow_eq_zpow_val, FractionalIdeal.count_zpow]
    by_cases hv : v' = v
    · subst hv
      rw [count_gen_self _ (hM _) hs]
      simp
    · rw [count_gen_other _ _ (first_place_lies_over (M v)) hv, Finsupp.single_eq_of_ne (Ne.symm hv)]
      simp

theorem absNorm_Idl (h2 : Module.finrank ℚ K = 2) (M : ∀ v : Pl, LM c v) (d : Pl →₀ ℤ) :
    FractionalIdeal.absNorm (Idl M d : FractionalIdeal (𝓞 K)⁰ K) = 1 := by
  classical
  induction d using Finsupp.induction_linear with
  | zero =>
    have : Idl M (0 : Pl →₀ ℤ) = 1 := Finsupp.prod_zero_index
    rw [this]
    simp
  | add a b ha hb => rw [Idl_add, Units.val_mul, map_mul, ha, hb, one_mul]
  | single v' n =>
    have e : Idl M (Finsupp.single v' n) = gen (M v') ^ n := Finsupp.prod_single_index (zpow_zero _)
    rw [e, Units.val_zpow_eq_zpow_val, map_zpow₀, absNorm_gen h2, one_zpow]

theorem exists_of_principal (h2 : Module.finrank ℚ K = 2) (hc : IsTotallyComplex K) (M : ∀ v : Pl, LM c v)
    (hM : ∀ v, (M v).ok) (d : Pl →₀ ℤ) (hd : d ∈ Tm M) (h : ClassGroup.mk K (Idl M d) = 1) :
    ∃ κ ∈ K1 K, d = vK M κ := by
  obtain ⟨β, hβ⟩ := (FractionalIdeal.isPrincipal_iff _).1 (ClassGroup.mk_eq_one_iff.1 h)
  have hβ0 : β ≠ 0 := by
    rintro rfl
    rw [FractionalIdeal.spanSingleton_zero] at hβ
    exact (Idl M d).ne_zero hβ
  have hN : Algebra.norm ℚ β = 1 := by
    have h1 := absNorm_Idl h2 M d
    rw [hβ, FractionalIdeal.absNorm_span_singleton (𝓞 K)] at h1
    have h3 := GroundTheory.Heights₂.Theta.algebraNorm_pos hβ0
    rwa [abs_of_pos h3] at h1
  refine ⟨Units.mk0 β hβ0, ?_, ?_⟩
  · rw [K1, MonoidHom.mem_ker]
    exact Units.ext hN
  · ext v
    rw [vK_apply h2 M hM]
    by_cases hs : (M v).IsSp
    · rw [order_unit_split_datum_valuation h2 _ (hM v) hs, Units.val_mk0, GlobalTheory.NumeratorIdeal.valuation_eq_count K _ hβ0,
        WithZero.log_exp, neg_neg, ← hβ, count_Idl M hM v hs]
    · rw [order_unit_field_datum_zero _ hs]
      by_contra h0
      exact hs (hd v h0)

theorem exists_isReps : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → IsTotallyComplex K →
    ∀ (c : HeckeCharacter K) (M : ∀ v : Pl, LM c v), AdmM M → ∃ R : Finset (Pl →₀ ℤ), IsReps M R := by
  intro K _ _ h2 hc c M hA
  have hM := hA.1
  obtain ⟨R, h1, h3⟩ := reps_of_finite (Tm M) (vKim h2 M hM)
    (by rintro _ ⟨κ, -, rfl⟩; exact vK_mem h2 M hM κ) (fun m => ClassGroup.mk K (Idl M m))
    (by
      intro m hm m' hm' e
      refine exists_of_principal h2 hc M hM _ (sub_mem hm hm') ?_
      have e' : ClassGroup.mk K (Idl M m) = ClassGroup.mk K (Idl M m') := e
      rw [sub_eq_add_neg, Idl_add, Idl_neg, map_mul, map_inv, e', mul_inv_cancel])
  refine ⟨R, h1, fun m hm => ?_⟩
  obtain ⟨r, ⟨hr, a, ⟨κ, hκ, rfl⟩, e⟩, hu⟩ := h3 m hm
  exact ⟨r, ⟨hr, κ, hκ, e⟩, fun r' ⟨hr', κ', hκ', e'⟩ => hu r' ⟨hr', _, ⟨κ', hκ', rfl⟩, e'⟩⟩

end GlobalTheory.CompanionTheory.KOneReps
