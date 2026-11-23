import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CharZeroFunctionField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingKrullDimRingOfIntegers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfIntersectionLowerHeight

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ProjSpace

namespace GlobalTheory.VolBr.Model

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

theorem ratVal_add {σ : k →+* ℂ} {y : CxPts p σ} {f g : X.functionField} (hf : RegAt (under y) f)
    (hg : RegAt (under y) g) : ratVal (f + g) y = ratVal f y + ratVal g y := by
  obtain ⟨U, hU, a, rfl⟩ := hf.exists_fnOf
  obtain ⟨W, hW, b, rfl⟩ := hg.exists_fnOf
  have hy : y ∈ ptsIn p σ (U ⊓ W) := mem_ptsIn.2 ⟨hU, hW⟩
  rw [← fnOf_resG (inf_le_left : U ⊓ W ≤ U) (gen_mem (memInf hU hW)),
    ← fnOf_resG (inf_le_right : U ⊓ W ≤ W) (gen_mem (memInf hU hW)), ← map_add,
    ratVal_fnOf hy, ratVal_fnOf hy, ratVal_fnOf hy, ev_add]

theorem ratVal_intCast_mul {σ : k →+* ℂ} {y : CxPts p σ} {f : X.functionField} (hf : RegAt (under y) f) (n : ℤ) :
    RegAt (under y) ((n : X.functionField) * f) ∧ ratVal ((n : X.functionField) * f) y = n * ratVal f y := by
  have h : (n : X.functionField) = fnOf ⊤ (Opens.mem_top _) (n : Γ(X, ⊤)) := (map_intCast _ n).symm
  have hr : RegAt (under y) (n : X.functionField) := ⟨n, map_intCast _ n⟩
  refine ⟨hr.mul hf, ?_⟩
  rw [ratVal_mul hr hf, h, ratVal_fnOf mem_ptsIn_top, ev_eq mem_ptsIn_top, map_intCast]

theorem isBallFam_Bl (P : Pair p) (a b : ℤ) : IsBallFam (P.H a b) (P.Bl a b) where
  subset _ _ h := h.1
  zero_mem r hr := ⟨zero_mem _, fun σ y => by
    have := (ratVal_intCast_mul (y := y) (regAt_zero _) 0).2
    simp only [Int.cast_zero, zero_mul] at this
    simpa [Pair.nu, Pair.loc, this] using hr⟩
  sub_mem r r' f g hf hg := ⟨sub_mem hf.1 hg.1, fun σ y => by
    have hi := mem_ptsIn.1 (mem_pick (P.L.φ σ).isLB y)
    have hj := mem_ptsIn.1 (mem_pick (P.A.φ σ).isLB y)
    have h₁ := hf.1 _ _ _ hi hj
    obtain ⟨h₂, h₃⟩ := ratVal_intCast_mul (hg.1 _ _ _ hi hj) (-1)
    refine le_trans ?_ (add_le_add (hf.2 σ y) (hg.2 σ y))
    have e : ∀ i j, P.loc a b (f - g) i j = P.loc a b f i j + ((-1 : ℤ) : X.functionField) * P.loc a b g i j := by
      intro i j; simp only [Pair.loc]; push_cast; ring
    simp only [Pair.nu]
    rw [e, ratVal_add h₁ h₂, h₃, ← add_mul]
    refine mul_le_mul_of_nonneg_right ((norm_add_le _ _).trans (le_of_eq ?_)) (Real.exp_pos _).le
    simp⟩
  nsmul_iff n r f hn hf := by
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have e (σ) (y : CxPts p σ) : P.nu a b σ y (n • f) = n * P.nu a b σ y f := by
      have hi := mem_ptsIn.1 (mem_pick (P.L.φ σ).isLB y)
      have hj := mem_ptsIn.1 (mem_pick (P.A.φ σ).isLB y)
      have e : ∀ i j, P.loc a b (n • f) i j = ((n : ℤ) : X.functionField) * P.loc a b f i j := by
        intro i j; simp only [Pair.loc, nsmul_eq_mul]; push_cast; ring
      simp only [Pair.nu]
      rw [e, (ratVal_intCast_mul (hf _ _ _ hi hj) n).2, norm_mul]
      simp [mul_assoc]
    exact ⟨fun h => ⟨hf, fun σ y => (mul_le_mul_iff_right₀ hn').1 (e σ y ▸ h.2 σ y)⟩,
      fun h => ⟨nsmul_mem hf n, fun σ y => e σ y ▸ (mul_le_mul_iff_right₀ hn').2 (h.2 σ y)⟩⟩

theorem div_eq {B : LB X} {r : B.ι → X.functionFieldˣ} (hr : IsRatSec B r) {i j : B.ι}
    (h : genericPoint X ∈ B.U i ⊓ B.U j) :
    (r i : X.functionField) / r j = fnOf _ h (B.g i j : Γ(X, B.U i ⊓ B.U j)) := by
  rw [hr i j h, mul_div_cancel_right₀ _ (r j).ne_zero]

theorem rep_fst (P : Pair p) : P.Rep 1 0 P.L := by
  have e (c i j) : (P.r c : X.functionField) / P.loc 1 0 1 i j = P.r c / P.r i := by simp [Pair.loc]
  refine ⟨P.r, P.hr, fun x c i j hc hi _ => ?_, fun σ y c i j hc hi _ => ?_⟩
  · rw [e, div_eq P.hr (gen_mem (memInf hc hi))]
    exact unitAt_fnOf (memInf hc hi) _ _
  · have h := mem_ptsIn_inf.2 ⟨hc, hi⟩
    rw [e, div_eq P.hr (gen_mem (mem_ptsIn.1 h)), ratVal_fnOf h, (P.L.φ σ).trans c i y hc hi, Real.log_pow, CxPts.gv]
    push_cast
    ring

section Two

variable (A : HermLB p) (u : A.B.Sec) (hu : genericPoint X ∈ nonzeroLocus u)

abbrev dbl : Pair p := ⟨A, A, ratOfSec u hu, ratOfSec u hu, isRatSec_ratOfSec u hu, isRatSec_ratOfSec u hu⟩

variable {A u hu}

theorem unitAt_zpow {x : X} {f : X.functionField} (h : UnitAt x f) (a : ℤ) : UnitAt x (f ^ a) := by
  have key (n : ℕ) : UnitAt x (f ^ n) := by
    induction n with
    | zero => simpa using unitAt_one x
    | succ n ih => rw [pow_succ]; exact ih.mul h
  rcases a with n | n
  · simpa using key n
  · simpa using (key (n + 1)).inv

theorem loc_dbl (t : X.functionField) (a b : ℤ) (hab : a + b = 1) (i j : A.B.ι) : (dbl A u hu).loc a b t i j =
      t * ratOfSec u hu j * ((ratOfSec u hu i : X.functionField) / ratOfSec u hu j) ^ a := by
  have h0 := (ratOfSec u hu j).ne_zero
  obtain rfl : b = 1 - a := by omega
  simp only [Pair.loc, div_zpow, zpow_sub₀ h0, zpow_one]
  field_simp

theorem unitAt_div {x : X} {i j : A.B.ι} (hi : x ∈ A.B.U i) (hj : x ∈ A.B.U j) :
    UnitAt x ((ratOfSec u hu i : X.functionField) / ratOfSec u hu j) := by
  rw [div_eq (isRatSec_ratOfSec u hu) (gen_mem (memInf hi hj))]
  exact unitAt_fnOf (memInf hi hj) _ _

theorem mem_Bl {v : A.B.Sec} (hv : v ∈ A.smallSec) {t : X.functionField}
    (ht : ∀ i (h : genericPoint X ∈ A.B.U i), t * ratOfSec u hu i = fnOf _ h (v.f i)) (a b : ℤ) (hab : a + b = 1) :
    t ∈ (dbl A u hu).Bl a b 1 := by
  refine ⟨fun x i j hi hj => ?_, fun σ y => ?_⟩
  · rw [loc_dbl t a b hab, ht j (gen_mem hj)]
    exact (regAt_fnOf hj _ _).mul (unitAt_zpow (unitAt_div hi hj) a).regAt
  · have hi := mem_pick (A.φ σ).isLB y
    have h := hv σ y
    rw [Weight.nsq, secVal_apply] at h
    rw [Pair.nu, loc_dbl t a b hab, div_self (Units.ne_zero _), one_zpow, mul_one, ht _ (gen_mem (mem_ptsIn.1 hi)),
      ratVal_fnOf hi, ← add_mul, ← Int.cast_add, hab, Int.cast_one, one_mul]
    refine (pow_le_one_iff_of_nonneg (by positivity) two_ne_zero).1 (le_of_eq_of_le ?_ h)
    rw [mul_pow, ← Real.exp_nat_mul]
    congr 2
    push_cast
    ring

theorem good_dbl {D : ℕ} (hA : IsAmpleLB A.B) (hN : A.IsNef D) (hs : u ∈ A.smallSec) {v : A.B.Sec} (hv : v ∈ A.smallSec)
    (hv0 : genericPoint X ∈ nonzeroLocus v) (hc : ∀ x, x ∈ nonzeroLocus u ∨ x ∈ nonzeroLocus v) :
    ∃ t, (∀ i (h : genericPoint X ∈ A.B.U i), t * ratOfSec u hu i = fnOf _ h (v.f i)) ∧ (dbl A u hu).Good D 2 1 t := by
  obtain ⟨c, hc0⟩ := exists_chart A.isLB (genericPoint X)
  have ht : ∀ i (h : genericPoint X ∈ A.B.U i),
      ((ratOfSec v hv0 c : X.functionField) / ratOfSec u hu c) * ratOfSec u hu i = fnOf _ h (v.f i) := by
    intro i h
    have := (ratOfSec u hu c).ne_zero
    rw [← val_ratOfSec (hs := hv0) h, isRatSec_ratOfSec u hu i c ⟨h, hc0⟩, isRatSec_ratOfSec v hv0 i c ⟨h, hc0⟩]
    field_simp
  have h1 : ∀ i (h : genericPoint X ∈ A.B.U i), 1 * (ratOfSec u hu i : X.functionField) = fnOf _ h (u.f i) :=
    fun i h => (one_mul _).trans (val_ratOfSec h)
  refine ⟨_, ht, hA, hN, two_pos, mem_Bl hs h1 0 1 rfl, one_ne_zero, mem_Bl hv ht (-1) _ rfl,
    div_ne_zero (Units.ne_zero _) (Units.ne_zero _), fun x i j hi hj g hg h => ?_⟩
  rw [loc_dbl _ (-1) _ rfl, ht j (gen_mem hj)] at h
  rcases hc x with hx | hx
  · rw [loc_dbl _ 0 1 rfl, h1 j (gen_mem hj), zpow_zero, mul_one, div_eq_mul_inv]
    exact hg.mul ((unitAt_fnOf_iff hj _ _).2 ((mem_nonzeroLocus_iff u j hj).1 hx)).inv.regAt
  · have hw := ((unitAt_fnOf_iff hj (gen_mem hj) _).2 ((mem_nonzeroLocus_iff v j hj).1 hx)).mul
      (unitAt_zpow (unitAt_div (u := u) (hu := hu) hi hj) (-1))
    have := h.mul hw.inv.regAt
    rwa [mul_div_right_comm, mul_inv_cancel_right₀ hw.ne_zero] at this

theorem not_good_dbl {D : ℕ} (h0 : nonzeroLocus u ≠ ⊤) : ¬ (dbl A u hu).Good D 2 1 1 := fun h => h0 <| by
  refine top_le_iff.1 fun x _ => ?_
  obtain ⟨j, hj⟩ := exists_chart A.isLB x
  have hr := h.reg x j j hj hj 1 (unitAt_one x).regAt
  rw [loc_dbl _ (-1) _ rfl, loc_dbl _ 0 1 rfl, div_self (Units.ne_zero _), one_zpow, one_zpow] at hr
  simp only [one_mul, mul_one, div_self (Units.ne_zero (ratOfSec u hu j)), one_div] at hr
  have := hr (unitAt_one x).regAt
  rw [val_ratOfSec (gen_mem hj)] at this
  exact (mem_nonzeroLocus_iff u j hj).2 ((unitAt_fnOf_iff hj (gen_mem hj) _).1
    ((unitAt_iff (fnOf_sec_ne_zero hu _)).2 ⟨regAt_fnOf hj _ _, this⟩))

end Two

omit [IsIntegral X] in

theorem isNef_of_small {D : ℕ} (hX : IsArithVar p D) (L : HermLB p) (hs : L.SemiPos D) (hf : ArInt.NefFib L)
    (hg : ∀ x : X, ∃ u ∈ L.smallSec, x ∈ nonzeroLocus u) : L.IsNef D where
  semiPos := hs
  vertical := hf
  horizontal Z i _ _ _ hc hd := by
    have hZ : IsArithVar (i ≫ p) 0 := hX.of_isClosedImmersion i hc hd
    obtain ⟨u, hu, ha⟩ := hg (i (genericPoint Z))
    have hgen : genericPoint Z ∈ nonzeroLocus (GlobalTheory.secPull u i) := by
      rw [GlobalTheory.nonzeroLocus_secPull]; exact ha
    have h0 : ∀ σ (y : CxPts (i ≫ p) σ), y ∈ ptsIn _ σ (nonzeroLocus (GlobalTheory.secPull u i)) := fun σ y => by
      refine mem_ptsIn.2 ?_
      have key : ∀ y : Sp ℂ ⟶ Z, y (IsLocalRing.closedPoint ℂ) = genericPoint Z := fun y =>
        GlobalTheory.HtSelfInter.eq_genericPoint hZ (Scheme.SpecToEquivOfField ℂ Z y).2.hom.charZero
      rw [key]
      exact hgen
    refine ⟨_, isRatSec_ratOfSec _ hgen, ?_⟩
    rw [HermLB.curveDeg_sec i u hgen h0]
    refine sub_nonneg.2 (le_trans (b := 0) ?_ ?_)
    · refine finsum_induction (· ≤ (0 : ℝ)) le_rfl (fun _ _ => add_nonpos) fun σ =>
        finsum_induction (· ≤ (0 : ℝ)) le_rfl (fun _ _ => add_nonpos) fun y => ?_
      exact div_nonpos_of_nonpos_of_nonneg (Real.log_nonpos (Weight.nsq_nonneg _ _ _) (hu σ _)) zero_le_two
    · exact finsum_nonneg fun z =>
        mul_nonneg (Int.cast_nonneg (mult_divOfSec_nonneg z)) (Real.log_natCast_nonneg _)

theorem isNef_hermitianTwistingSheaf (N : ℕ) : (hermitianTwistingSheaf ℤ N).IsNef N :=
  have := Geo.Tor.isProper_str ℤ N
  isNef_of_small (isArithVar_int N) _ (HermLB.semiPos_fs _ _ _ _ _ _)
    (ProjModel.nefFib_of_isAmpleLB (hermitianTwistingSheaf ℤ N) (isAmple_projective_O_one ℤ N)) fun x =>
    have ⟨a, ha⟩ := Opens.mem_iSup.1 ((iSup_nonzeroLocus_coord ℤ N).ge (Opens.mem_top x))
    ⟨_, ProjModel.coord_mem_smallSec ℤ N a, ha⟩

local instance isIntegral_line : IsIntegral (PSpace ℤ 1) := isIntegral_of_isDomain ℤ 1

attribute [local instance] MvPolynomial.gradedAlgebra in

theorem gen_mem_coord (a : Fin 2) : genericPoint (PSpace ℤ 1) ∈ nonzeroLocus (coord ℤ 1 a) := by
  let η : ProjectiveSpectrum (grading ℤ 1) := ⟨⊥, Ideal.isPrime_bot, fun h =>
    MvPolynomial.X_ne_zero _ (h (HomogeneousIdeal.mem_irrelevant_of_mem _ one_pos (X_mem ℤ 1 0)))⟩
  rw [nonzeroLocus_coord]
  exact gen_mem (x := η) fun h => MvPolynomial.X_ne_zero a h

theorem coord_ne_top : nonzeroLocus (coord ℤ 1 1) ≠ ⊤ := by
  intro h
  rw [nonzeroLocus_coord] at h
  have h1 : (PSpace ℤ 1).basicOpen (ratio ℤ 1 0 1) = chart ℤ 1 0 :=
    basicOpen_ratioOn.trans ((congrArg (_ ⊓ ·) h).trans (inf_top_eq _))
  have h2 : IsUnit (ratio ℤ 1 0 1) := (PSpace ℤ 1).toRingedSpace.isUnit_of_isUnit_germ _ _ fun x hx =>
    ((PSpace ℤ 1).mem_basicOpen _ x hx).1 (h1.ge hx)
  rw [← chartAlgEquiv_X ℤ 1 0 ⟨1, by decide⟩] at h2
  have h3 := (h2.map (chartAlgEquiv ℤ 1 0).symm).map MvPolynomial.constantCoeff
  rw [AlgEquiv.symm_apply_apply, MvPolynomial.constantCoeff_X] at h3
  exact not_isUnit_zero h3

theorem exists_good : IsArithVar (PSpace.str ℤ 1) 1 ∧ ∃ (P : Pair (PSpace.str ℤ 1)) (t : (PSpace ℤ 1).functionField),
    P.L = hermitianTwistingSheaf ℤ 1 ∧ P.A = hermitianTwistingSheaf ℤ 1 ∧ P.Good 1 2 1 t ∧ ¬ P.Good 1 2 1 1 := by
  obtain ⟨t, -, ht⟩ := good_dbl (A := hermitianTwistingSheaf ℤ 1) (u := coord ℤ 1 1) (hu := gen_mem_coord 1) (isAmple_projective_O_one ℤ 1)
    (isNef_hermitianTwistingSheaf 1) (ProjModel.coord_mem_smallSec ℤ 1 1) (ProjModel.coord_mem_smallSec ℤ 1 0) (gen_mem_coord 0)
    fun x => by
      obtain ⟨a, ha⟩ := Opens.mem_iSup.1 ((iSup_nonzeroLocus_coord ℤ 1).ge (Opens.mem_top x))
      fin_cases a
      · exact .inr ha
      · exact .inl ha
  exact ⟨isArithVar_int 1, _, t, rfl, rfl, ht, not_good_dbl coord_ne_top⟩

section IntValues

open IntExample

theorem exists_int_of_regAt {f : (Sp ℤ).functionField} (h : ∀ x, RegAt x f) : ∃ n : ℤ, f = n := by
  obtain ⟨a, ha⟩ := exists_fnOf_eq (U := ⊤) trivial fun x _ => h x
  obtain ⟨n, rfl⟩ := ArithBase.surjective_intCast (𝟙 (Sp ℤ)) a
  exact ⟨n, ha.symm.trans (map_intCast _ n)⟩

theorem ratVal_int {σ : k →+* ℂ} (y : CxPts p σ) (n : ℤ) : ratVal (n : X.functionField) y = n := by
  have := (ratVal_intCast_mul (y := y) (unitAt_one _).regAt n).2
  have e := ratVal_nat y 1
  rw [Nat.cast_one, Nat.cast_one] at e
  rwa [mul_one, e, mul_one] at this

theorem nu_int (a b : ℤ) (σ) (y) (n : ℤ) : pair.nu a b σ y n = |(n : ℝ)| * Real.exp (-(b * Real.log 3)) := by
  rw [Pair.nu, loc_eq, ratVal_int]
  have : ∀ (t : ℝ) i, ((ArithBase.trivShift t).φ σ).φ i y = 0 + 2 * t := fun _ _ => rfl
  simp only [pair, this]
  congr 2
  · simp
  · ring

def intPt : CxPts (𝟙 (Sp ℤ)) (Int.castRingHom ℂ) :=
  ⟨Spec.map (CommRingCat.ofHom (Int.castRingHom ℂ)), Category.comp_id _⟩

theorem Bl_one (a : ℤ) : pair.Bl a 1 1 = (fun n : ℤ => (n : (Sp ℤ).functionField)) '' Set.Icc (-3) 3 := by
  have e (n : ℤ) (σ) (y : CxPts (𝟙 (Sp ℤ)) σ) : pair.nu a 1 σ y n ≤ 1 ↔ n ∈ Set.Icc (-3 : ℤ) 3 := by
    rw [nu_int, Int.cast_one, one_mul, Real.exp_neg, Real.exp_log (by norm_num), ← div_eq_mul_inv,
      div_le_one (by norm_num), Set.mem_Icc, ← abs_le]
    exact_mod_cast Iff.rfl
  ext f
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨n, rfl⟩ := exists_int_of_regAt (f := f) fun x => by
      have := h.1 x PUnit.unit PUnit.unit trivial trivial
      erw [loc_eq] at this
      exact this
    exact ⟨n, (e n _ intPt).1 (h.2 _ _), rfl⟩
  · rintro ⟨n, hn, rfl⟩
    exact ⟨fun x i j _ _ => by rw [loc_eq]; exact ⟨n, map_intCast _ n⟩, fun σ y => (e n σ y).2 hn⟩

theorem lc_one (a : ℤ) : pair.lc a 1 1 = Real.log 7 := by
  have := charZero_functionField
  rw [Pair.lc, Bl_one, Set.ncard_image_of_injective _ Int.cast_injective, ← Finset.coe_Icc, Set.ncard_coe_finset,
    Int.card_Icc]
  norm_num [show Int.toNat 7 = 7 from rfl]

theorem rep_iff (a b : ℤ) (t : ℝ) : pair.Rep a b (ArithBase.trivShift t) ↔ t = b * Real.log 3 := by
  refine ⟨fun ⟨ρ, _, hu, hn⟩ => ?_, fun h => h ▸ rep a b⟩
  have := charZero_functionField
  have hu' (x) : UnitAt x (ρ PUnit.unit : (Sp ℤ).functionField) := by
    have := hu x PUnit.unit PUnit.unit PUnit.unit trivial trivial trivial
    erw [loc_eq] at this
    rwa [div_one] at this
  obtain ⟨m, hm⟩ := exists_int_of_regAt fun x => (hu' x).regAt
  obtain ⟨m', hm'⟩ := exists_int_of_regAt fun x => (hu' x).inv.regAt
  have h1 : m * m' = 1 := by
    have : ((m * m' : ℤ) : (Sp ℤ).functionField) = (1 : ℤ) := by
      push_cast; rw [← hm, ← hm', mul_inv_cancel₀ (Units.ne_zero _)]
    exact Int.cast_injective this
  have h := hn _ intPt PUnit.unit PUnit.unit PUnit.unit mem_ptsIn_top mem_ptsIn_top mem_ptsIn_top
  erw [loc_eq] at h
  rw [div_one] at h
  erw [hm] at h
  rw [ratVal_int] at h
  change _ - (0 + 2 * t) / 2 = -(a * (0 + 2 * (0 : ℝ)) + b * (0 + 2 * Real.log 3)) / 2 at h
  have h0 : Real.log ‖(m : ℂ)‖ = 0 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one h1 with rfl | rfl <;> simp
  rw [h0] at h
  linarith

theorem not_good_two_two : ¬ pair.Good 0 1 (2 : ℕ) (2 : ℕ) := fun h => by
  have := charZero_functionField
  obtain ⟨n, hn⟩ := exists_int_of_regAt (f := 1 / (2 : ℕ)) fun x => by
    have hr := h.reg x PUnit.unit PUnit.unit trivial trivial 1 (unitAt_one x).regAt
    erw [loc_eq, loc_eq] at hr
    rw [one_mul, div_self h.s_ne] at hr
    exact hr (unitAt_one x).regAt
  have h2 : ((2 * n : ℤ) : (Sp ℤ).functionField) = (1 : ℤ) := by
    push_cast at *; rw [← hn]; norm_num
  have := Int.cast_injective h2
  omega

end IntValues

theorem nu_sq_of_rep (P : Pair p) {a b : ℤ} {M : HermLB p} (h : P.Rep a b M) :
    ∃ ρ : M.B.ι → X.functionFieldˣ, IsRatSec M.B ρ ∧ ∀ (v : M.B.Sec) (f : X.functionField),
      (∀ c (hc : genericPoint X ∈ M.B.U c), f * ρ c = fnOf _ hc (v.f c)) →
      f ∈ P.H a b ∧ ∀ σ (y : CxPts p σ), P.nu a b σ y f ^ 2 = (M.φ σ).nsq (secVal p σ v) y := by
  obtain ⟨ρ, hρ, hu, hn⟩ := h
  have e (f) (c i j) : P.loc a b f i j = f * ρ c * ((ρ c : X.functionField) / P.loc a b 1 i j)⁻¹ := by
    have := (ρ c).ne_zero
    simp only [Pair.loc]
    field_simp
  refine ⟨ρ, hρ, fun v f hf => ⟨fun x i j hi hj => ?_, fun σ y => ?_⟩⟩
  · obtain ⟨c, hc⟩ := exists_chart M.isLB x
    rw [e f c, hf c (gen_mem hc)]
    exact (regAt_fnOf hc _ _).mul (hu x c i j hc hi hj).inv.regAt
  · have hc := mem_pick (M.φ σ).isLB y
    have hi := mem_pick (P.L.φ σ).isLB y
    have hj := mem_pick (P.A.φ σ).isLB y
    have hU := hu _ _ _ _ (mem_ptsIn.1 hc) (mem_ptsIn.1 hi) (mem_ptsIn.1 hj)
    have hN := hn σ y _ _ _ hc hi hj
    have hinv := ratVal_mul hU.regAt hU.inv.regAt
    have e1 := IntExample.ratVal_nat y 1
    rw [Nat.cast_one, Nat.cast_one] at e1
    rw [mul_inv_cancel₀ hU.ne_zero, e1] at hinv
    have hne := ratVal_ne_zero hU
    rw [Weight.nsq, secVal_apply, Pair.nu, e f (pick (M.φ σ).isLB y), hf _ (gen_mem (mem_ptsIn.1 hc)),
      ratVal_mul (regAt_fnOf (mem_ptsIn.1 hc) _ _) hU.inv.regAt, ratVal_fnOf hc, ← hN,
      (eq_inv_of_mul_eq_one_right hinv.symm), Real.exp_sub, Real.exp_log (norm_pos_iff.2 hne), norm_mul, norm_inv,
      mul_assoc, ← mul_div_assoc, inv_mul_cancel₀ (norm_ne_zero_iff.2 hne), mul_pow, one_div, ← Real.exp_neg,
      ← Real.exp_nat_mul]
    congr 2
    push_cast
    ring

theorem not_isBallFam_discrete :
    ¬ IsBallFam (⊤ : AddSubgroup ℤ) fun r => {x | if x = 0 then 0 ≤ r else 1 ≤ r} := fun h => by
  have := (h.nsmul_iff 2 (1 / 2) 1 two_pos trivial).1 (by norm_num)
  norm_num at this

end GlobalTheory.VolBr.Model
