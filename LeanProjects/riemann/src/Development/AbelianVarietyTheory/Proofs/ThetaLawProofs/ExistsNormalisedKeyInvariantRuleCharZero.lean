import Mathlib
import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KaRuleK
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.StalkOfAppLEEq
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.DualNumberRingHomExt
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyPBRing
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ThetaLawSymplecticNormalForm
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyRuleCharHalfOfCharZero
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MemNonzeroLocusConstMul
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsEllipticKeyDataValueEqDiscriminantStatement
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyPBPair
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsRescale

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

noncomputable section
namespace GlobalTheory.KeyNormRule

def HasValue (g n : ℕ) (ka : KeyIn ℂ → ℂˣ) (a₀ : ℂ) : Prop :=
  ∀ (x : KeyIn ℂ) (τ Mx : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (a b : Fin x.P.g → ℂ) (c₀ : ℂ), x.P.g = g →
    charHalf x.P.g a b → c₀ ≠ 0 → Mx.det ≠ 0 → NormalAt x τ Mx a b c₀ →
    (ka x : ℂ) = a₀ * (Mx.det ^ 4 / c₀ ^ 8) ^ n

theorem dim_of_keyPB {R R' : Type} [CommRing R] [CommRing R'] {x' : KeyIn R'} {x : KeyIn R} {f : R →+* R'}
    (h : KeyPB x' x f) : x'.P.g = x.P.g := by
  obtain ⟨_, _, _, hg, -⟩ := h
  exact hg

theorem HasValue.holo {g n : ℕ} {ka : KeyIn ℂ → ℂˣ} {a₀ : ℂ} (h : HasValue g n ka a₀) (a b : Fin g → ℂ)
    (hab : charHalf g a b) : ∃ U : Matrix (Fin g) (Fin g) ℂ → ℂ, Key.IsHoloSiegel g U ∧
      ∀ (x : KeyIn ℂ) (h : x.P.g = g) (τ : Matrix (Fin x.P.g) (Fin x.P.g) ℂ),
        NormalAt x τ 1 (fun i => a (i.cast h)) (fun i => b (i.cast h)) 1 →
        (ka x : ℂ) = U (τ.submatrix (Fin.cast h.symm) (Fin.cast h.symm)) :=
  ⟨fun _ => a₀, differentiableOn_const _, fun x hx τ hn => by
    simpa using h x τ 1 _ _ 1 hx ⟨fun i => hab.1 _, fun i => hab.2 _⟩ one_ne_zero (by simp) hn⟩

theorem exists_rule_sq (hinv : Key.Chi.InversionStatement) {g c M : ℕ}
    {ka : ∀ (K : Type) [Field K] [CharZero K], KeyIn K → Kˣ} (hka : KaRuleK (2 * g) c M ka) {a₀ : ℂ}
    (ha : ∀ (x : KeyIn ℂ) (τ Mx : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (c₀ : ℂ), x.P.g = 2 * g → c₀ ≠ 0 → Mx.det ≠ 0 →
      NormalAt x τ Mx 0 0 c₀ → (ka ℂ x : ℂ) = a₀ * (Mx.det ^ 4 / c₀ ^ 8) ^ c) :
    ∃ kb, KaRuleK g (2 * c) M kb ∧ HasValue g (2 * c) (kb ℂ) a₀ := by
  obtain ⟨hH, hF, hU, -⟩ := hka
  have hex : ∀ (R : Type) [CommRing R] (x : KeyIn R), ∃ y, IsKeyPow y x 2 :=
    fun R _ x => exists_isKeyPow R x 2 (by norm_num)
  choose sq hsq using hex
  have hdim : ∀ {R : Type} [CommRing R] {x y : KeyIn R}, x.P.g = g → IsKeyPow y x 2 → y.P.g = 2 * g :=
    fun hx hy => hx ▸ hy.dim_eq
  have indep : ∀ (K : Type) [Field K] [CharZero K] (x y : KeyIn K), x.P.g = g → IsKeyPow y x 2 →
      (ka K (sq K x) : K) = ka K y := fun K _ _ x y hx hy =>
    hF K K (RingHom.id K) y (sq K x) (hdim hx hy)
      (keyPB_of_isKeyPow K K (RingHom.id K) x y x (sq K x) 2 (GlobalTheory.keyPB_id K x) hy (hsq K x))
  have hval : HasValue g (2 * c) (fun x => ka ℂ (sq ℂ x)) a₀ := by
    intro x τ Mx a b c₀ hx hab hc hM hn₀
    obtain ⟨n, rfl⟩ := exists_int_half hab.1
    obtain ⟨n', rfl⟩ := exists_int_half hab.2
    have hy := hsq ℂ x
    obtain ⟨e, τ', M', hd, hn⟩ :=
      normalAt_pow x _ 2 τ Mx (fun i => (n i : ℝ) / 2) (fun i => (n' i : ℝ) / 2) c₀ hy hn₀
    obtain ⟨sp, hsp, hlaw⟩ := exists_thetaLaw_zero_of_even hinv _ _ _ (even_dot_double e n n')
    obtain ⟨M'', c', hc', hq, hn'⟩ := GlobalTheory.SpMove.normalAt_spAct (sq ℂ x) τ' M' (c₀ ^ 2) sp _ _ 0 0 hsp hlaw
      (pow_ne_zero _ hc) (by simpa using hn)
    have hq' : M''.det ^ 4 / c' ^ 8 = (Mx.det ^ 4 / c₀ ^ 8) ^ 2 := by rw [hq, hd]; ring
    have hM'' : M''.det ≠ 0 := fun h => by
      rw [h] at hq'
      exact pow_ne_zero 2 (div_ne_zero (pow_ne_zero 4 hM) (pow_ne_zero 8 hc)) (by rw [← hq']; simp)
    have := ha (sq ℂ x) _ M'' c' (hdim hx hy) hc' hM'' (by simpa [Pi.zero_def] using hn')
    rw [hq', ← pow_mul] at this
    exact this
  refine ⟨fun K _ _ x => ka K (sq K x), ⟨?_, ?_, ?_, hval.holo⟩, hval⟩
  · intro K _ _ P hg rig hr th hth v hv th' hth' v' hv' a Mx hP h₁ h₂
    have hy := hsq K ⟨P, hg, rig, hr, th, hth, v, hv⟩
    obtain ⟨t, ht, w, hw, M', hp, ht', hw', hd⟩ :=
      GlobalTheory.PowChange.isKeyPow_change K P hg rig hr th hth v hv th' hth' v' hv' a Mx 2 _ h₁ h₂ hy
    have key := hH K _ (sq K ⟨P, hg, rig, hr, th, hth, v, hv⟩).g_pos _
      (sq K ⟨P, hg, rig, hr, th, hth, v, hv⟩).rig_gen _ (sq K ⟨P, hg, rig, hr, th, hth, v, hv⟩).th_ne _
      (sq K ⟨P, hg, rig, hr, th, hth, v, hv⟩).basis t ht w hw (a ^ 2) M' (hdim hP hy) ht' hw'
    dsimp only
    rw [indep K ⟨P, hg, rig, hr, th', hth', v', hv'⟩ _ hP hp]
    rw [hd, ← pow_mul, ← pow_mul] at key
    rw [show 8 * (2 * c) = 2 * (8 * c) by ring, show 4 * (2 * c) = 2 * (4 * c) by ring]
    exact key
  · intro K K' _ _ _ _ f x x' hx h
    exact hF K K' f _ _ (hdim hx (hsq K x)) (keyPB_of_isKeyPow K K' f x _ x' _ 2 h (hsq K x) (hsq K' x'))
  · intro R K _ _ _ _ _ _ _ x xK hx hM h
    obtain ⟨u, hu, hu'⟩ := hU R K (sq R x) (sq K xK) (hdim hx (hsq R x)) hM
      (keyPB_of_isKeyPow R K _ x _ xK _ 2 h (hsq R x) (hsq K xK))
    exact ⟨u, hu, fun k _ _ r xk hr hk =>
      hu' k r (sq k xk) hr (keyPB_of_isKeyPow R k r x _ xk _ 2 hk (hsq R x) (hsq k xk))⟩

theorem exists_test (hT : ThetaUnifAV) {g n : ℕ} (hg : 1 ≤ g) {ka : KeyIn ℂ → ℂˣ} {a₀ : ℂ} (h : HasValue g n ka a₀)
    {S : Type} [CommRing S] (W : WeierstrassCurve S) [W.IsElliptic] (s : S →+* ℂ) :
    ∃ (y : KeyIn S) (z : KeyIn ℂ), y.P.g = g ∧ KeyPB z y s ∧ (ka z : ℂ) = a₀ * s W.Δ ^ (g * n) := by
  obtain ⟨x, hx, hxv⟩ := GlobalTheory.T.exists_ellipticKeyData_value_eq_discriminant hT S W
  obtain ⟨y, hy⟩ := exists_isKeyPow S x g hg
  obtain ⟨x', hx'⟩ := exists_keyPB_ring x s
  obtain ⟨z, hz⟩ := exists_isKeyPow ℂ x' g hg
  obtain ⟨⟨τ, Mx, a, b, c, hab, hc, hM, hn₀⟩, -⟩ := GlobalTheory.KeyNormalExists.exists_normalAt hT x'
  have hΔ := hxv s x' τ Mx a b c hx' hab hc hn₀
  obtain ⟨m, rfl⟩ := exists_int_half hab.1
  obtain ⟨m', rfl⟩ := exists_int_half hab.2
  obtain ⟨e, τ', M', hd, hn⟩ :=
    normalAt_pow x' z g τ Mx (fun i => (m i : ℝ) / 2) (fun i => (m' i : ℝ) / 2) c hz hn₀
  refine ⟨y, z, by rw [hy.dim_eq, hx, Nat.mul_one], keyPB_of_isKeyPow S ℂ s x y x' z g hx' hy hz, ?_⟩
  rw [h z τ' M' _ _ _ (by rw [hz.dim_eq, dim_of_keyPB hx', hx, Nat.mul_one]) ⟨fun i => hab.1 _, fun i => hab.2 _⟩
    (pow_ne_zero _ hc) (by rw [hd]; exact pow_ne_zero _ hM) hn, ← hΔ, hd, pow_mul]
  congr 2
  ring

theorem const_rat_unit (hT : ThetaUnifAV) {g n M : ℕ} (hg : 1 ≤ g)
    {ka : ∀ (K : Type) [Field K] [CharZero K], KeyIn K → Kˣ} (hka : KaRuleK g n M ka) {a₀ : ℂ}
    (h : HasValue g n (ka ℂ) a₀) (W : WeierstrassCurve ℤ) (hW : W.Δ ≠ 0) :
    ∃ r : ℚ, r ≠ 0 ∧ (r : ℂ) = a₀ ∧ ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K]
      [CharZero K] [Algebra R K] [IsFractionRing R K], IsUnit (M : R) → IsUnit (W.Δ : R) →
      ∃ w : Rˣ, algebraMap R K w = (r : K) := by
  obtain ⟨-, hF, hU, -⟩ := hka
  let S := Localization.Away W.Δ
  have hext : ∀ {T : Type} [CommRing T] (f f' : S →+* T), f = f' := fun f f' =>
    IsLocalization.ringHom_ext (Submonoid.powers W.Δ) (RingHom.ext_int _ _)
  have hlift : ∀ {T : Type} [CommRing T], IsUnit (W.Δ : T) → Nonempty (S →+* T) := fun {T} _ hu =>
    ⟨IsLocalization.Away.lift (g := Int.castRingHom T) W.Δ hu⟩
  haveI : (W.map (algebraMap ℤ S)).IsElliptic :=
    ⟨by rw [WeierstrassCurve.map_Δ]; exact IsLocalization.Away.algebraMap_isUnit W.Δ⟩
  have hQ : (W.Δ : ℚ) ≠ 0 := Int.cast_ne_zero.2 hW
  obtain ⟨i⟩ := hlift (T := ℚ) hQ.isUnit
  obtain ⟨y, z, hy, hz, hv⟩ := exists_test hT hg h (W.map (algebraMap ℤ S)) ((Rat.castHom ℂ).comp i)
  obtain ⟨yQ, hyQ⟩ := exists_keyPB_ring y i
  have hyQg : yQ.P.g = g := (dim_of_keyPB hyQ).trans hy
  rw [hF ℚ ℂ (Rat.castHom ℂ) yQ z hyQg (GlobalTheory.KeyCancel.keyPB_cancel _ _ _ y yQ z _ _ hyQ hz),
    WeierstrassCurve.map_Δ, eq_intCast (algebraMap ℤ S), map_intCast, eq_ratCast] at hv
  have hC : (W.Δ : ℂ) ≠ 0 := Int.cast_ne_zero.2 hW
  refine ⟨(ka ℚ yQ : ℚ) / (W.Δ : ℚ) ^ (g * n), div_ne_zero (Units.ne_zero _) (pow_ne_zero _ hQ), ?_, ?_⟩
  · push_cast
    rw [hv, mul_div_cancel_right₀ _ (pow_ne_zero _ hC)]
  · intro R K _ _ _ _ _ _ _ hM hΔ
    obtain ⟨j⟩ := hlift hΔ
    obtain ⟨yR, hyR⟩ := exists_keyPB_ring y j
    obtain ⟨yK, hyK⟩ := exists_keyPB_ring yQ (Rat.castHom K)
    have hyK' := GlobalTheory.keyPB_trans _ _ _ y yQ yK _ _ hyQ hyK
    rw [hext ((Rat.castHom K).comp i) ((algebraMap R K).comp j)] at hyK'
    obtain ⟨u, hu, -⟩ := hU R K yR yK ((dim_of_keyPB hyR).trans hy) hM
      (GlobalTheory.KeyCancel.keyPB_cancel _ _ _ y yR yK _ _ hyR hyK')
    rw [hF ℚ K _ yQ yK hyQg hyK, eq_ratCast] at hu
    have hK : (W.Δ : K) ≠ 0 := Int.cast_ne_zero.2 hW
    refine ⟨u * hΔ.unit⁻¹ ^ (g * n), ?_⟩
    have e : algebraMap R K (hΔ.unit⁻¹ : Rˣ) = (W.Δ : K)⁻¹ := by
      rw [map_units_inv, IsUnit.unit_spec, map_intCast]
    rw [Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow, e, ← hu, Rat.cast_div, Rat.cast_pow,
      Rat.cast_intCast, inv_pow, div_eq_mul_inv]

theorem rule_div {g n M : ℕ} {ka : ∀ (K : Type) [Field K] [CharZero K], KeyIn K → Kˣ} (hka : KaRuleK g n M ka)
    {r : ℚ} (hr : r ≠ 0) (h : HasValue g n (ka ℂ) r)
    (hu : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K]
      [CharZero K] [Algebra R K] [IsFractionRing R K], IsUnit (M : R) → ∃ w : Rˣ, algebraMap R K w = (r : K)) :
    ∃ κ, KaRuleK g n M κ ∧ HasValue g n (κ ℂ) 1 := by
  obtain ⟨hH, hF, hU, -⟩ := hka
  let κ : ∀ (K : Type) [Field K] [CharZero K], KeyIn K → Kˣ :=
    fun K _ _ x => ka K x * (Units.mk0 (r : K) (Rat.cast_ne_zero.2 hr))⁻¹
  have hκ : ∀ (K : Type) [Field K] [CharZero K] (x : KeyIn K), (κ K x : K) = ka K x * (r : K)⁻¹ :=
    fun K _ _ x => by simp [κ]
  have hval : HasValue g n (κ ℂ) 1 := fun x τ Mx a b c₀ h₁ h₂ h₃ h₄ h₅ => by
    have : (r : ℂ) ≠ 0 := Rat.cast_ne_zero.2 hr
    rw [hκ, h x τ Mx a b c₀ h₁ h₂ h₃ h₄ h₅]
    field_simp
  refine ⟨κ, ⟨?_, ?_, ?_, hval.holo⟩, hval⟩
  · intro K _ _ P hg rig hrig th hth v hv th' hth' v' hv' a Mx hP h₁ h₂
    rw [hκ, hκ, ← _root_.mul_assoc, ← _root_.mul_assoc,
      hH K P hg rig hrig th hth v hv th' hth' v' hv' a Mx hP h₁ h₂]
  · intro K K' _ _ _ _ f x x' hx hp
    rw [hκ, hκ, hF K K' f x x' hx hp, map_mul, map_inv₀, map_ratCast]
  · intro R K _ _ _ _ _ _ _ x xK hx hM hp
    obtain ⟨u, hu₁, hu₂⟩ := hU R K x xK hx hM hp
    obtain ⟨w, hw⟩ := hu R K hM
    have hw' : (w : R) * (r.den : R) = (r.num : R) := IsFractionRing.injective R K (by
      rw [map_mul, hw, map_natCast, map_intCast]
      exact_mod_cast Rat.mul_den_eq_num r)
    refine ⟨u * w⁻¹, ?_, fun k _ _ ρ xk hρ hk => ?_⟩
    · rw [hκ, hu₁, Units.val_mul, map_mul, map_units_inv, hw]
    · have e : ρ w = (r : k) := by
        have := congrArg ρ hw'
        rw [map_mul, map_natCast, map_intCast] at this
        rw [Rat.cast_def, eq_div_iff (Nat.cast_ne_zero.2 r.den_ne_zero), this]
      rw [hκ, hu₂ k ρ xk hρ hk, Units.val_mul, map_mul, map_units_inv, e]

theorem exists_normalised_rule : Out.Laws → ThetaUnifAV → Key.Chi.InversionStatement → Key.PhHoloStatement → GlobalTheory.TorusAlgebraic → ∀ (g c M : ℕ), 1 ≤ g → KaRule (2 * g) c M → ∃ κ, KaRuleK g (2 * c) M κ ∧ ∀ (x : KeyIn ℂ) (τ Mx : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (a b : Fin x.P.g → ℂ) (c₀ : ℂ), x.P.g = g → charHalf x.P.g a b → c₀ ≠ 0 → Mx.det ≠ 0 → NormalAt x τ Mx a b c₀ → (κ ℂ x : ℂ) = (Mx.det ^ 4 / c₀ ^ 8) ^ (2 * c) := by
  intro hL hT hinv hP hA g c M hg hR
  obtain ⟨ka, hka⟩ := GlobalTheory.KeyGalDesc.exists_kaRuleK hL.polBaseChange _ _ _ hR
  obtain ⟨a₀, ha⟩ := GlobalTheory.KeyConst.exists_const hT hinv hP hA _ c M ka (by omega) hka
  obtain ⟨kb, hkb, hv⟩ := exists_rule_sq hinv hka ha
  obtain ⟨r, hr, rfl, h₃⟩ := const_rat_unit hT hg hkb hv (WeierstrassCurve.ofJ0 ℤ)
    (by rw [WeierstrassCurve.ofJ0_Δ]; norm_num)
  obtain ⟨r', -, e, h₂⟩ := const_rat_unit hT hg hkb hv (WeierstrassCurve.ofJ1728 ℤ)
    (by rw [WeierstrassCurve.ofJ1728_Δ]; norm_num)
  obtain rfl : r' = r := Rat.cast_injective e
  obtain ⟨κ, hκ, hκv⟩ := rule_div hkb hr hv fun R K _ _ _ _ _ _ _ hM => by
    rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (3 : R) with h | h
    · refine h₃ R K hM ?_
      rw [WeierstrassCurve.ofJ0_Δ]
      convert (h.pow 3).neg using 1
      norm_num
    · refine h₂ R K hM ?_
      rw [WeierstrassCurve.ofJ1728_Δ]
      convert (h.pow 6).neg using 1
      norm_num
  exact ⟨κ, hκ, fun x τ Mx a b c₀ h₁ h₂ h₃ h₄ h₅ => by
    rw [hκv x τ Mx a b c₀ h₁ h₂ h₃ h₄ h₅, _root_.one_mul]⟩

end GlobalTheory.KeyNormRule
end
