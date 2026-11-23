import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SizeAt
import Development.AbelianVarietyTheory.Definitions.Divisors.TieTest
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NuHTwisted
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsNormSubEqOne

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop NumberField IsDedekindDomain
open GlobalTheory.FunObj.SqNum (nuH halfRank IsTor)
open GlobalTheory.CMVal GlobalTheory.HeckeGal

noncomputable section

namespace GlobalTheory.TwistValBound

section Additive

variable {K L : Type} [Field K] [Field L]

theorem add_zpow (v : K → ℤ) (hv : ∀ x y, x ≠ 0 → y ≠ 0 → v (x * y) = v x + v y) {x : K} (hx : x ≠ 0) (n : ℤ) :
    v (x ^ n) = n * v x := by
  let φ : Kˣ →* Multiplicative ℤ := MonoidHom.mk' (fun a => Multiplicative.ofAdd (v a)) fun a b => by
    rw [Units.val_mul, hv _ _ a.ne_zero b.ne_zero, ofAdd_add]
  have h := congrArg Multiplicative.toAdd (map_zpow φ (Units.mk0 x hx) n)
  simpa [φ] using h

theorem proportional (f : K →+* L) (v : K → ℤ) (v' : L → ℤ)
    (hv : ∀ x y, x ≠ 0 → y ≠ 0 → v (x * y) = v x + v y)
    (hv' : ∀ x y, x ≠ 0 → y ≠ 0 → v' (x * y) = v' x + v' y)
    (h : ∀ x, x ≠ 0 → 0 ≤ v x → 0 ≤ v' (f x)) {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    v' (f x) * v y = v x * v' (f y) := by
  have key : ∀ a b : ℤ, a * v x + b * v y = 0 → 0 ≤ a * v' (f x) + b * v' (f y) := by
    intro a b hab
    have h1 := h (x ^ a * y ^ b) (mul_ne_zero (zpow_ne_zero _ hx) (zpow_ne_zero _ hy)) (by
      rw [hv _ _ (zpow_ne_zero _ hx) (zpow_ne_zero _ hy), add_zpow v hv hx, add_zpow v hv hy, hab])
    have hfx : f x ≠ 0 := (map_ne_zero f).2 hx
    have hfy : f y ≠ 0 := (map_ne_zero f).2 hy
    rwa [map_mul, map_zpow₀, map_zpow₀, hv' _ _ (zpow_ne_zero _ hfx) (zpow_ne_zero _ hfy),
      add_zpow v' hv' hfx, add_zpow v' hv' hfy] at h1
  have h1 := key (v y) (-v x) (by ring)
  have h2 := key (-v y) (v x) (by ring)
  linarith

end Additive

section Ord

variable (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

def ordR (a : R) : ℕ := (IsDiscreteValuationRing.addVal R a).toNat

def ordK (x : FractionRing R) : ℤ :=
  (ordR R (IsLocalization.surj (nonZeroDivisors R) x).choose.1 : ℤ) -
    (ordR R ((IsLocalization.surj (nonZeroDivisors R) x).choose.2 : R) : ℤ)

variable {R}

theorem ordR_mul {a b : R} (ha : a ≠ 0) (hb : b ≠ 0) : ordR R (a * b) = ordR R a + ordR R b := by
  unfold ordR
  rw [AddValuation.map_mul, ENat.toNat_add (by simpa [IsDiscreteValuationRing.addVal_eq_top_iff] using ha) (by simpa [IsDiscreteValuationRing.addVal_eq_top_iff] using hb)]

theorem ordR_eq_zero_iff {a : R} (ha : a ≠ 0) : ordR R a = 0 ↔ IsUnit a := by
  unfold ordR
  rw [ENat.toNat_eq_zero, IsDiscreteValuationRing.addVal_eq_zero_iff]
  simp [ha, IsDiscreteValuationRing.addVal_eq_top_iff]

theorem dvd_of_ordR_le {a b : R} (ha : a ≠ 0) (hb : b ≠ 0) (h : ordR R b ≤ ordR R a) : b ∣ a := by
  unfold ordR at h
  rw [← IsDiscreteValuationRing.addVal_le_iff_dvd]
  rw [← ENat.coe_toNat (n := IsDiscreteValuationRing.addVal R a) (by simpa [IsDiscreteValuationRing.addVal_eq_top_iff] using ha),
    ← ENat.coe_toNat (n := IsDiscreteValuationRing.addVal R b) (by simpa [IsDiscreteValuationRing.addVal_eq_top_iff] using hb)]
  exact_mod_cast h

theorem ordK_eq {x : FractionRing R} (hx : x ≠ 0) {a b : R} (hb : b ≠ 0)
    (h : x * algebraMap R _ b = algebraMap R _ a) : ordK R x = (ordR R a : ℤ) - ordR R b := by
  have hinj := IsFractionRing.injective R (FractionRing R)
  have hp := (IsLocalization.surj (nonZeroDivisors R) x).choose_spec
  unfold ordK
  set p := (IsLocalization.surj (nonZeroDivisors R) x).choose
  have hp2 : (p.2 : R) ≠ 0 := nonZeroDivisors.coe_ne_zero _
  have hne : ∀ {c d : R}, d ≠ 0 → x * algebraMap R _ d = algebraMap R _ c → c ≠ 0 := by
    rintro c d hd hcd rfl
    rw [map_zero] at hcd
    exact mul_ne_zero hx ((map_ne_zero_iff _ hinj).2 hd) hcd
  have he : p.1 * b = a * p.2 := hinj (by rw [map_mul, map_mul, ← hp, ← h]; ring)
  have h2 := congrArg (ordR R) he
  rw [ordR_mul (hne hp2 hp) hb, ordR_mul (hne hb h) hp2] at h2
  omega

theorem ordK_algebraMap {a : R} (ha : a ≠ 0) : ordK R (algebraMap R (FractionRing R) a) = ordR R a := by
  rw [ordK_eq ((map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 ha) (a := a) one_ne_zero
    (by simp), (ordR_eq_zero_iff one_ne_zero).2 isUnit_one]
  simp

theorem exists_frac {x : FractionRing R} (hx : x ≠ 0) :
    ∃ a b : R, a ≠ 0 ∧ b ≠ 0 ∧ x * algebraMap R _ b = algebraMap R _ a := by
  obtain ⟨⟨a, b⟩, h⟩ := IsLocalization.surj (nonZeroDivisors R) x
  have hb : (b : R) ≠ 0 := nonZeroDivisors.coe_ne_zero _
  refine ⟨a, b, ?_, hb, h⟩
  rintro rfl
  simp only [map_zero] at h
  exact mul_ne_zero hx ((map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 hb) h

theorem ordK_mul (x y : FractionRing R) (hx : x ≠ 0) (hy : y ≠ 0) : ordK R (x * y) = ordK R x + ordK R y := by
  obtain ⟨a, b, ha, hb, h⟩ := exists_frac hx
  obtain ⟨c, d, hc, hd, h'⟩ := exists_frac hy
  rw [ordK_eq hx hb h, ordK_eq hy hd h', ordK_eq (mul_ne_zero hx hy) (a := a * c) (mul_ne_zero hb hd)
    (by rw [map_mul, map_mul, ← h, ← h']; ring), ordR_mul ha hc, ordR_mul hb hd]
  push_cast
  ring

theorem ordK_nonneg_of_mem {x : FractionRing R} (hx : x ≠ 0)
    (h : x ∈ (algebraMap R (FractionRing R)).range) : 0 ≤ ordK R x := by
  obtain ⟨a, rfl⟩ := h
  rw [ordK_algebraMap (by rintro rfl; simp at hx)]
  positivity

theorem mem_of_ordK_nonneg {x : FractionRing R} (hx : x ≠ 0) (h0 : 0 ≤ ordK R x) :
    x ∈ (algebraMap R (FractionRing R)).range := by
  obtain ⟨a, b, ha, hb, h⟩ := exists_frac hx
  rw [ordK_eq hx hb h] at h0
  obtain ⟨c, rfl⟩ := dvd_of_ordR_le ha hb (by omega)
  refine ⟨c, ?_⟩
  rw [map_mul, mul_comm] at h
  exact (mul_left_cancel₀ ((map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 hb) h).symm

theorem vK_eq (l : ℕ) (x : FractionRing R) :
    BlochKatoReduction.Gen.vK R l x = (ordK R x : ℝ) / (ordR R (l : R) : ℝ) := by
  unfold BlochKatoReduction.Gen.vK BlochKatoReduction.Gen.nval ordK ordR
  push_cast
  ring

theorem ordR_pos {a : R} (ha : a ≠ 0) (hu : ¬ IsUnit a) : (0 : ℝ) < ordR R a := by
  exact_mod_cast Nat.pos_of_ne_zero fun h => hu ((ordR_eq_zero_iff ha).1 h)

theorem vK_map {S : Type} [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    (f : FractionRing R →+* FractionRing S) (g : R →+* S)
    (hfg : ∀ a, f (algebraMap R _ a) = algebraMap S _ (g a)) (l : ℕ)
    (hR0 : (l : R) ≠ 0) (hR : ¬ IsUnit (l : R)) (hS0 : (l : S) ≠ 0) (hS : ¬ IsUnit (l : S))
    {x : FractionRing R} (hx : x ≠ 0) : BlochKatoReduction.Gen.vK S l (f x) = BlochKatoReduction.Gen.vK R l x := by
  have h := proportional f (ordK R) (ordK S) ordK_mul ordK_mul (fun y hy h0 => by
      obtain ⟨a, rfl⟩ := mem_of_ordK_nonneg hy h0
      exact ordK_nonneg_of_mem ((map_ne_zero f).2 hy) ⟨g a, (hfg a).symm⟩) hx
    ((map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 hR0)
  rw [hfg, map_natCast g, ordK_algebraMap hR0, ordK_algebraMap hS0] at h
  rw [vK_eq, vK_eq, div_eq_div_iff (ordR_pos hS0 hS).ne' (ordR_pos hR0 hR).ne']
  exact_mod_cast h

theorem vK_mul (l : ℕ) {x y : FractionRing R} (hx : x ≠ 0) (hy : y ≠ 0) :
    BlochKatoReduction.Gen.vK R l (x * y) = BlochKatoReduction.Gen.vK R l x + BlochKatoReduction.Gen.vK R l y := by
  rw [vK_eq, vK_eq, vK_eq, ordK_mul x y hx hy]
  push_cast
  ring

theorem vK_unit (l : ℕ) (u : Rˣ) : BlochKatoReduction.Gen.vK R l (algebraMap R (FractionRing R) (u : R)) = 0 := by
  rw [vK_eq, ordK_algebraMap u.ne_zero, (ordR_eq_zero_iff u.ne_zero).2 u.isUnit]
  simp

end Ord

theorem vw_eq_vAdd {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) {x : K} (hx : x ≠ 0) :
    Formalism.DivisionValues.vw w x = vAdd w x := by
  have h : w.valuation K x = WithZero.exp (-Formalism.DivisionValues.vw w x) := GlobalTheory.Idele.valuation_eq_exp_neg_count w hx
  rw [vAdd, h, WithZero.log_exp, neg_neg]

theorem vw_mul {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (x y : K) (hx : x ≠ 0)
    (hy : y ≠ 0) : Formalism.DivisionValues.vw w (x * y) = Formalism.DivisionValues.vw w x + Formalism.DivisionValues.vw w y := by
  rw [vw_eq_vAdd w hx, vw_eq_vAdd w hy, vw_eq_vAdd w (mul_ne_zero hx hy), vAdd, vAdd, vAdd, map_mul,
    WithZero.log_mul ((Valuation.ne_zero_iff _).2 hx) ((Valuation.ne_zero_iff _).2 hy)]
  ring

theorem vw_le_of_bound : ∀ {D : D7} (nch : NChoice D) (w : D.what₂.places.Pl) (N0 : D.ntw.Tw → ℕ) (lam : D.ntw.abelian₂ (nch.twI w)) (a : ℤ)
    (u : (nch.Oe w)ˣ) (z : D.what₂.LL),
    BlochKatoReduction.Gen.partC N0 (nch.twI w) (nch.Q w) (nch.k' w) (nch.psi' w ^ a) (twEps D (nch.twI w)) →
    nch.embW w z * nch.kMapE w (BlochKatoReduction.Gen.kMap D.ntw (nch.twI w) (nch.k' w) (∑ δ, D.ntw.th (nch.twI w) ∅ lam δ)) =
      algebraMap (nch.Oe w) (FractionRing (nch.Oe w)) (u : nch.Oe w) *
        nch.kMapE w (BlochKatoReduction.Gen.thEval D.ntw (nch.twI w) (nch.Q w) lam (nch.k' w)
          (BlochKatoReduction.Gen.psiAt (D.ntw.sideL (nch.twI w) lam) (nch.psi' w ^ a))) →
    (Formalism.DivisionValues.vw (D.plEq w) z : ℝ) ≤ (Formalism.DivisionValues.vw (D.plEq w) ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) : ℝ) / ((D.what₂.places.resChar w : ℕ) : ℝ) ^ 2 := by
  intro D nch w N0 lam a u z hC hid
  obtain ⟨hne, -, hle⟩ := hC lam
  set T := BlochKatoReduction.Gen.thEval D.ntw (nch.twI w) (nch.Q w) lam (nch.k' w)
    (BlochKatoReduction.Gen.psiAt (D.ntw.sideL (nch.twI w) lam) (nch.psi' w ^ a)) with hT
  unfold BlochKatoReduction.Gen.c0 twEps at hle
  set S := ∑ δ, D.ntw.th (nch.twI w) ∅ lam δ with hS
  have hl := nch.twI_l w
  set l := D.what₂.places.resChar w with hldef
  have hlp : l.Prime := D.what₂.places.resChar_prime w
  have hlL : (l : D.what₂.LL) ≠ 0 := Nat.cast_ne_zero.mpr hlp.ne_zero
  have hlE : (l : nch.Oe w) ≠ 0 := by
    intro h
    have h1 := congrArg (algebraMap (nch.Oe w) (FractionRing (nch.Oe w))) h
    rw [map_natCast, map_zero, ← map_natCast (nch.embW w)] at h1
    exact hlL ((map_eq_zero _).1 h1)
  have hlk : (l : D.ntw.Ok (nch.twI w) (nch.k' w)) ≠ 0 := by
    intro h
    have h1 := congrArg (algebraMap (D.ntw.Ok (nch.twI w) (nch.k' w)) (nch.Oe w)) h
    rw [map_natCast, map_zero] at h1
    exact hlE h1
  have hlO : (l : D.ntw.O (nch.twI w)) ≠ 0 := by
    intro h
    have h1 := congrArg (algebraMap (D.ntw.O (nch.twI w)) (D.ntw.Ok (nch.twI w) (nch.k' w))) h
    rw [map_natCast, map_zero] at h1
    exact hlk h1
  have huO : ¬ IsUnit (l : D.ntw.O (nch.twI w)) := by
    have := D.ntw.O_l (nch.twI w)
    rw [hl] at this
    exact (IsLocalRing.mem_maximalIdeal _).1 this
  have huk : ¬ IsUnit (l : D.ntw.Ok (nch.twI w) (nch.k' w)) := by
    haveI := D.ntw.Ok_fin (nch.twI w) (nch.k' w)
    haveI : FaithfulSMul (D.ntw.O (nch.twI w)) (D.ntw.Ok (nch.twI w) (nch.k' w)) :=
      (faithfulSMul_iff_algebraMap_injective _ _).2 (D.ntw.Ok_inj _ _)
    intro h
    rw [← map_natCast (algebraMap (D.ntw.O (nch.twI w)) (D.ntw.Ok (nch.twI w) (nch.k' w)))] at h
    exact huO (IsUnit.of_map _ _ h)
  have huE : ¬ IsUnit (l : nch.Oe w) := by
    haveI := nch.Oe_loc w
    intro h
    rw [← map_natCast (algebraMap (D.ntw.Ok (nch.twI w) (nch.k' w)) (nch.Oe w))] at h
    exact huk (IsUnit.of_map _ _ h)
  have hu0 : algebraMap (nch.Oe w) (FractionRing (nch.Oe w)) (u : nch.Oe w) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 u.ne_zero
  have hT0 : nch.kMapE w T ≠ 0 := (map_ne_zero _).2 hne
  have hprod := mul_ne_zero hu0 hT0
  rw [← hid] at hprod
  have hz0 : z ≠ 0 := (map_ne_zero _).1 (left_ne_zero_of_mul hprod)
  have hS1 : BlochKatoReduction.Gen.kMap D.ntw (nch.twI w) (nch.k' w) S ≠ 0 := (map_ne_zero _).1 (right_ne_zero_of_mul hprod)
  have hS0 : S ≠ 0 := (map_ne_zero _).1 hS1
  have hE : ∀ {x}, x ≠ 0 → BlochKatoReduction.Gen.vK (nch.Oe w) l (nch.kMapE w x) =
      BlochKatoReduction.Gen.vK (D.ntw.Ok (nch.twI w) (nch.k' w)) l x := fun hx =>
    vK_map (nch.kMapE w) (algebraMap _ _) (fun b => by
      unfold NChoice.kMapE IsFractionRing.map
      exact IsLocalization.map_eq _ b) l hlk huk hlE huE hx
  have hk : BlochKatoReduction.Gen.vK (D.ntw.Ok (nch.twI w) (nch.k' w)) l (BlochKatoReduction.Gen.kMap D.ntw (nch.twI w) (nch.k' w) S) =
      BlochKatoReduction.Gen.vK (D.ntw.O (nch.twI w)) l S :=
    vK_map _ (algebraMap _ _) (fun b => IsFractionRing.lift_algebraMap _ b) l hlO huO hlk huk hS0
  have hv := congrArg (BlochKatoReduction.Gen.vK (nch.Oe w) l) hid
  rw [vK_mul l (left_ne_zero_of_mul hprod) (right_ne_zero_of_mul hprod), vK_mul l hu0 hT0, vK_unit,
    hE hS1, hE hne, hk] at hv
  rw [hl] at hle
  have hz : BlochKatoReduction.Gen.vK (nch.Oe w) l (nch.embW w z) ≤ ((l : ℝ) ^ 2)⁻¹ := by linarith
  have hp := proportional (nch.embW w) (Formalism.DivisionValues.vw (D.plEq w)) (ordK (nch.Oe w)) (vw_mul _) ordK_mul
    (fun y hy h0 => ordK_nonneg_of_mem ((map_ne_zero _).2 hy) ((nch.embW_w w y).1 (by
      rw [D.val_eq w y hy, ← vw_eq_vAdd _ hy]
      exact_mod_cast h0))) hz0 hlL
  rw [map_natCast, ← map_natCast (algebraMap (nch.Oe w) (FractionRing (nch.Oe w))), ordK_algebraMap hlE] at hp
  have hvl : 0 ≤ Formalism.DivisionValues.vw (D.plEq w) (l : D.what₂.LL) := by
    have h := D.what₂.places.val_resChar w
    rw [D.val_eq w _ hlL, ← vw_eq_vAdd _ hlL] at h
    have h1 : Formalism.DivisionValues.vw (D.plEq w) (l : D.what₂.LL) = (D.what₂.places.ramIdx w : ℤ) := WithTop.coe_injective h
    rw [h1]
    positivity
  have hpos := ordR_pos hlE huE
  have hp' : (Formalism.DivisionValues.vw (D.plEq w) z : ℝ) =
      BlochKatoReduction.Gen.vK (nch.Oe w) l (nch.embW w z) * (Formalism.DivisionValues.vw (D.plEq w) (l : D.what₂.LL) : ℝ) := by
    rw [vK_eq, div_mul_eq_mul_div, eq_div_iff hpos.ne']
    exact_mod_cast hp.symm
  rw [hp', div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_right hz (by exact_mod_cast hvl)

end GlobalTheory.TwistValBound

end
