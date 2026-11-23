import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFrameIff
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorsionPointPrimitiveComponentValuationZerStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CoeffRecoveryByTorsionAverages
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GtOntoDivisibleKernel
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTorsionIdentificationWithPairingStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SectionValueAtTorsionPointEqSumTermsStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValueAtFormalTorsion
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis

noncomputable section
namespace GlobalTheory.OneBasis.UnitValue
open GlobalTheory.TorusExt GlobalTheory.UT.WeightValue GlobalTheory.UT.CoefBasic

theorem not_all_ne_zero {F : Type} [Field F] [IsAlgClosed F] [CharZero F] {v : AddValuation F (WithTop ℚ)} {X : Type}
    [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] {n : ℕ} (hn : 2 ≤ n) (hvn : v (n : F) = 0) {a : X → F}
    (ha : NullV v a) (h0 : ∀ χ, 0 ≤ v (a χ)) {α : X} (hα : v (a α) = 0)
    (H : ∀ t : Multiplicative X →* Fˣ, (∃ k, t ^ n ^ k = 1) →
      ∃ S, SumV v (fun χ => (t (Multiplicative.ofAdd χ)).val * a χ) S ∧ v S ≠ 0) : False := by
  classical
  choose! S hS hS0 using H
  have hroot : ∀ (t : Multiplicative X →* Fˣ) (k : ℕ), t ^ n ^ k = 1 → ∀ χ, v (t χ).val = 0 ∧ v ((t χ)⁻¹).val = 0 := by
    intro t k ht χ
    have e : t χ ^ n ^ k = 1 := by rw [← MonoidHom.pow_apply, ht, MonoidHom.one_apply]
    have hN : 0 < n ^ k := pow_pos (by omega) k
    exact ⟨GlobalTheory.TorsRecov.val_eq_zero_of_pow v _ _ hN (by rw [← Units.val_pow_eq_pow_val, e, Units.val_one]),
      GlobalTheory.TorsRecov.val_eq_zero_of_pow v _ _ hN (by rw [← Units.val_pow_eq_pow_val, inv_pow, e, inv_one, Units.val_one])⟩
  have hpos : ∀ (t : Multiplicative X →* Fˣ) (k : ℕ), t ^ n ^ k = 1 → 0 < v (S t) := fun t k ht =>
    lt_of_le_of_ne (le_of_sumV (q := 0) (hS t ⟨k, ht⟩) fun χ => by
      rw [v.map_mul, (hroot t k ht _).1, zero_add]; exact h0 χ) (hS0 t ⟨k, ht⟩).symm
  obtain ⟨k, hk⟩ := GlobalTheory.coeff_recovery_by_torsion_averages F v X n hn hvn a ha S hS (fun _ => α)
    (fun _ => ⟨0, by simp⟩) (a α) (Or.inl ⟨α, fun _ => ⟨0, by simp⟩, rfl⟩) 1
  have h1 := hk k le_rfl
  have hN : 0 < n ^ k := pow_pos (by omega) k
  haveI : Finite {t : Multiplicative X →* Fˣ // t ^ n ^ k = 1} :=
    Nat.finite_of_card_ne_zero (by
      rw [GlobalTheory.TorsRecov.card_tors F X _ hN]; exact pow_ne_zero _ hN.ne')
  letI := Fintype.ofFinite {t : Multiplicative X →* Fˣ // t ^ n ^ k = 1}
  rw [finsum_eq_sum_of_fintype] at h1
  have h2 : 0 < v (((n : F) ^ (k * Module.finrank ℤ X))⁻¹ * ∑ t : {t : Multiplicative X →* Fˣ // t ^ n ^ k = 1},
      ((t.1 (Multiplicative.ofAdd α))⁻¹).val * S t.1) := by
    rw [v.map_mul, GlobalTheory.TorsRecov.val_inv_pow v _ _ hvn, zero_add]
    refine v.map_lt_sum WithTop.zero_ne_top fun t _ => ?_
    rw [v.map_mul, (hroot t.1 k t.2 _).2, zero_add]
    exact hpos t.1 k t.2
  have h3 := v.map_lt_add (lt_of_lt_of_le (by exact_mod_cast (zero_lt_one : (0 : ℚ) < 1)) h1) h2
  rw [sub_add_cancel, hα] at h3
  exact lt_irrefl _ h3

section
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V} {hϖ : Irreducible ϖ}
  {D : DegData V (maximalIdeal V)}
  {F : Type} [Field F] [Algebra (FractionRing V) F] {v : AddValuation F (WithTop ℚ)} {hv : ValOver ϖ F v}

theorem exists_frm_zero (k : ℕ) (g : GtPtF D.toPre F) : ∃ w : Frm D.toPre F k g.b, w.IsGen ∧ GenV hϖ hv w 0 := by
  obtain ⟨w, hw⟩ := (coef_basic V D.toPre F k g).1
  obtain ⟨r, φ₀, hφ, t₀, ht₀, x, hx, e⟩ := CoefVal.exists_genV_frm (hϖ := hϖ) (hv := hv) hw
  have hx0 : x ≠ 0 := v.ne_top_iff.1 (by rw [hx]; exact WithTop.coe_ne_top)
  obtain ⟨w', hw', e'⟩ := TorsionValue.exists_frm_scale w hw (inv_ne_zero hx0)
  refine ⟨w', hw', φ₀, hφ, t₀, ht₀, 1, v.map_one, fun z J hJ => ?_⟩
  rw [e' z J hJ, e z J hJ, ← _root_.mul_assoc, cst_eq, cst_eq, cst_eq, ← map_mul, inv_mul_cancel₀ hx0]

theorem exists_frm_cast {k : ℕ} {b b' : TF (R := V) F ⟶ D.toPre.P.A} (hb : b' = b) (w : Frm D.toPre F k b) (hw : w.IsGen)
    (h0 : GenV hϖ hv w 0) : ∃ w' : Frm D.toPre F k b', w'.IsGen ∧ GenV hϖ hv w' 0 ∧
      ∀ z J, Good D.toPre.P.L z J → val w' (𝟙 _) z J = val w (𝟙 _) z J := by
  subst hb
  exact ⟨w, hw, h0, fun _ _ _ => rfl⟩

end

attribute [local instance] gtGroup in

theorem exists_unit_value : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ w₀ ρ, NormW U.toUnifPre w₀ ρ → ∀ k n : ℕ, 4 ≤ k → n.Prime → IsUnit (n : V) → ∀ (t : SecA A F k) (s : Fam D.toPre F k) (α : D.toPre.X), U.ExpandsF F k w₀ t s → IntGe D v s 0 → (∀ q : ℚ, 0 < q → ¬ VGe D F v k α (s.s α) q) → ∃ (j : ℕ) (x : TFK (R := V) F ⟶ A.A), 2 ≤ j ∧ FromGt U.toUnifPre (n ^ j) x ∧ ∀ e (c : F), IsTorsFrame A ρ (n ^ j) x e → ValAt t x e c → v c = 0 := by
  intro hL hT hVR hTW hUU V _ _ _ _ hcpl ϖ hϖ D Q hQ F _ _ _ v hv A G _ _ hG U w₀ ρ hN k n hk hn hnV t s α hts hint hprim
  by_contra hcon
  have hk1 : 1 ≤ k := by omega
  have hA : AdmBase V (maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hcpl⟩
  have : CharZero (FractionRing V) := IsFractionRing.charZero V
  have : CharZero F := (algebraMap (FractionRing V) F).charZero_iff (algebraMap (FractionRing V) F).injective |>.1 this
  obtain ⟨i, g, o, ho, hgo, hg⟩ := GlobalTheory.T.exists_torsion_point_primitive_component_valuation_zero hL hT hVR hTW hUU V hcpl ϖ hϖ D Q hQ F v hv k n hk hn hnV s α
    (hint α) hprim
  have hgi : n ^ i • g = 0 := ((isNsmul_iff_eq _ _ _).1 hgo).symm.trans ((isZero_iff_eq _).1 ho)
  obtain ⟨w, hw, hw0⟩ := exists_frm_zero (hϖ := hϖ) (hv := hv) k g
  have hB := D.tau_bimult
  have hgV : ∀ χ, GenV hϖ hv (g.s χ) 0 := fun χ => by
    have e := CoefVal.gtV_qk (hϖ := hϖ) (hv := hv) hVR hQ (Nat.one_le_pow i n hn.pos)
      (qkMk hB 0 g (hgi.trans (map_zero _).symm)) χ
    simpa only [qkMk_y, qkMk_g, bOf_zero_left hϖ hQ, Int.cast_zero, zero_div] using e
  have hvn : v (n : F) = 0 := by
    have e := GC.v_alg_unit hv hnV.unit
    rwa [IsUnit.unit_spec, map_natCast, map_natCast] at e
  refine not_all_ne_zero (v := v) (a := coef s g w) (α := α) hn.two_le hvn
    (((CoefVal.main hL hT hVR hTW hUU V hcpl ϖ hϖ D Q hQ F v hv g).2.2.2.2.2.2 k hk1 w s hw).1)
    (fun χ => by simpa using CoefVal.le_v_coef hw (hint χ) (hgV χ) hw0) (hg w hw hw0) ?_
  rintro τ ⟨m, hm⟩
  have hj : 1 ≤ n ^ (i + m + 2) := Nat.one_le_pow _ n hn.pos
  let p : QkPt D.toPre F (n ^ (i + m + 2)) := qkMk hB 0 (g + torusPt D.toPre F (Additive.ofMul τ)) (by
    have e₁ : n ^ (i + m + 2) • g = 0 := by rw [add_assoc, pow_add, mul_comm, mul_smul, hgi, smul_zero]
    have e₂ : τ ^ n ^ (i + m + 2) = 1 := by
      rw [show i + m + 2 = m + (i + 2) by ring, pow_add, pow_mul, hm, one_pow]
    rw [smul_add, e₁, ← map_nsmul, ← ofMul_pow, e₂, ofMul_one, map_zero, map_zero, add_zero])
  obtain ⟨f, hf, -⟩ := GlobalTheory.T.uniformisation_torsion_identification_with_pairing hL V (maximalIdeal V) hA D A G hG U F _ hj
  have hx : QkToAkU U.toUnifPre F _ p (f p) := (hf p _).2 rfl
  have hex : ∃ e c, IsTorsFrame A ρ (n ^ (i + m + 2)) (f p) e ∧ ValAt t (f p) e c ∧ v c ≠ 0 := by
    by_contra h
    refine hcon ⟨i + m + 2, f p, by omega, ⟨p, rfl, hx⟩, fun e c he hc => ?_⟩
    by_contra h'
    exact h ⟨e, c, he, hc, h'⟩
  obtain ⟨e, c, he, hc, hc0⟩ := hex
  obtain ⟨w₁, hw₁, hv₁, hsum⟩ := GlobalTheory.T.section_value_at_torsionPoint_eq_sum_terms hL hT hVR hTW hUU V hcpl ϖ hϖ D Q hQ F v hv A G hG U w₀ ρ hN _ hj p _ hx e he
  have hv₁ : GenV hϖ hv w₁ 0 := by
    have e0 : ((Q p.y : ℚ) / ((n ^ (i + m + 2) : ℕ) : ℚ) ^ 2) = 0 := by
      rw [show p.y = 0 from rfl, QForm.Q_zero hϖ D hQ]; simp
    rwa [e0] at hv₁
  obtain ⟨w₂, hw₂, hwv⟩ := exists_pow k (line_exp k) w₁ hw₁
  have hw₂0 : GenV hϖ hv w₂ 0 := genV_pow k (line_exp k) hv₁ fun z J _ => hwv _ _ z J
  have hS : SumV v (coef s p.g w₂) c := hsum k hk1 w₂ ⟨hw₂, fun z J _ => hwv _ _ z J⟩ t s c hts hc
  have hb : p.g.b = g.b := by
    show (g + torusPt D.toPre F (Additive.ofMul τ)).b = g.b
    rw [add_b, torusPt_b, _root_.mul_one]
  obtain ⟨w', hw', hw'0, hww⟩ := exists_frm_cast hb w hw hw0
  obtain ⟨u, hu, huv, huc⟩ := ((coef_basic V D.toPre F k p.g).2.2 w₂ hw₂).2.2.1 w' hw'
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 (v.ne_top_iff.2 hu)
  have r0 : r = 0 := by
    have := CoefVal.sep D
    exact CoefVal.genV_unique D.toPre.P.isLB (genV_smul hw₂0 hr.symm huv) hw'0
  have hu0 : v u = 0 := by rw [← hr, r0]; rfl
  have htr := ((coef_basic V D.toPre F k g).2.2 w hw).2.2.2 τ _ p.g w'
    ((isTor_iff _ _).2 (isTorusPtF_torusPt τ)) ((isAdd_iff_eq _ _ _).2 rfl) hww s
  refine ⟨u * c, ?_, by rwa [v.map_mul, hu0, zero_add]⟩
  have := sumV_mul hS hu0
  simpa only [← huc, htr] using this

end GlobalTheory.OneBasis.UnitValue
end
