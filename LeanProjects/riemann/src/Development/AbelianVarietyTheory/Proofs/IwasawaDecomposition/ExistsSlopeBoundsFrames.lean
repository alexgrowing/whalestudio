import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdmissibleRepresentationFactorisation
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrameCombinationCoeffUnique
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntOIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeC

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open ReciprocityTheory.ChartRestriction.G.PullbackSections
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.ShFam.Pad.LieScale

section Norms

variable {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C]

theorem norm_sum_le_of_le {ι : Type} (s : Finset ι) (g : ι → C) {b : ℝ} (hb : 0 ≤ b) (h : ∀ i ∈ s, ‖g i‖ ≤ b) :
    ‖∑ i ∈ s, g i‖ ≤ b := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hb
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le (h a (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi)))

theorem norm_natCast_le_one' (n : ℕ) : ‖(n : C)‖ ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ih (by simp))

theorem norm_intCast_le_one' (n : ℤ) : ‖(n : C)‖ ≤ 1 := by
  cases n with
  | ofNat n => simpa using norm_natCast_le_one' (C := C) n
  | negSucc n => rw [Int.cast_negSucc, norm_neg]; exact norm_natCast_le_one' _

theorem norm_le_one_of_isIntegral {z : C} (hz : IsIntegral ℤ z) : ‖z‖ ≤ 1 := by
  by_contra h
  push_neg at h
  obtain ⟨Q, hQm, hQ⟩ := hz
  rw [hQm.as_sum] at hQ
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finset_sum, Polynomial.eval₂_mul,
    Polynomial.eval₂_C] at hQ
  have e : z ^ Q.natDegree = -∑ i ∈ Finset.range Q.natDegree, (algebraMap ℤ C) (Q.coeff i) * z ^ i :=
    eq_neg_of_add_eq_zero_left hQ
  rcases Nat.eq_zero_or_pos Q.natDegree with h0 | h0
  · rw [h0] at e
    simp at e
  have hs : ‖∑ i ∈ Finset.range Q.natDegree, (algebraMap ℤ C) (Q.coeff i) * z ^ i‖ ≤ ‖z‖ ^ (Q.natDegree - 1) := by
    refine norm_sum_le_of_le _ _ (by positivity) fun i hi => ?_
    rw [norm_mul, norm_pow, algebraMap_int_eq, eq_intCast]
    have hi' : i ≤ Q.natDegree - 1 := by have := Finset.mem_range.1 hi; omega
    calc ‖((Q.coeff i : ℤ) : C)‖ * ‖z‖ ^ i ≤ 1 * ‖z‖ ^ i := by gcongr; exact norm_intCast_le_one' _
      _ ≤ ‖z‖ ^ (Q.natDegree - 1) := by rw [one_mul]; exact pow_le_pow_right₀ h.le hi'
  rw [← norm_neg, ← e, norm_pow] at hs
  have : ‖z‖ ^ Q.natDegree = ‖z‖ ^ (Q.natDegree - 1) * ‖z‖ := by
    rw [← pow_succ]; congr 1; omega
  rw [this] at hs
  have hp : 0 < ‖z‖ ^ (Q.natDegree - 1) := by positivity
  nlinarith

theorem norm_aeval_le_one (R : Polynomial ℤ) {z : C} (hz : ‖z‖ ≤ 1) : ‖Polynomial.aeval z R‖ ≤ 1 := by
  rw [Polynomial.aeval_eq_sum_range]
  refine norm_sum_le_of_le _ _ zero_le_one fun i _ => ?_
  rw [zsmul_eq_mul, norm_mul, norm_pow]
  exact mul_le_one₀ (norm_intCast_le_one' _) (by positivity) (pow_le_one₀ (norm_nonneg _) hz)

theorem norm_coeff_zero_le {z : C} (R : Polynomial ℤ) (hR : Polynomial.aeval z R = 0) (hz : ‖z‖ ≤ 1) :
    ‖((R.coeff 0 : ℤ) : C)‖ ≤ ‖z‖ := by
  have e := congrArg (Polynomial.aeval z) (Polynomial.divX_mul_X_add R)
  rw [map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C, hR, algebraMap_int_eq, eq_intCast] at e
  have e2 : ((R.coeff 0 : ℤ) : C) = -(Polynomial.aeval z R.divX * z) := by linear_combination e
  rw [e2, norm_neg, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (norm_aeval_le_one _ hz)

theorem one_le_norm_natCast {p : ℕ} (hp : p.Prime) (hpC : ‖(p : C)‖ = (p : ℝ)⁻¹) {b : ℕ} (hb : ¬ p ∣ b) :
    1 ≤ ‖(b : C)‖ := by
  have hcop : Nat.Coprime b p := ((Nat.Prime.coprime_iff_not_dvd hp).2 hb).symm
  have e : (b : ℤ) * Nat.gcdA b p + (p : ℤ) * Nat.gcdB b p = 1 := by
    have := Nat.gcd_eq_gcd_ab b p
    rw [hcop.gcd_eq_one] at this
    exact_mod_cast this.symm
  have e' : (b : C) * (Nat.gcdA b p : C) + (p : C) * (Nat.gcdB b p : C) = 1 := by
    have := congrArg (Int.cast : ℤ → C) e
    push_cast at this
    exact this
  have h1 : (1 : ℝ) ≤ max ‖(b : C)‖ (p : ℝ)⁻¹ := by
    calc (1 : ℝ) = ‖(1 : C)‖ := norm_one.symm
      _ = ‖(b : C) * (Nat.gcdA b p : C) + (p : C) * (Nat.gcdB b p : C)‖ := by rw [e']
      _ ≤ max ‖(b : C) * (Nat.gcdA b p : C)‖ ‖(p : C) * (Nat.gcdB b p : C)‖ := IsUltrametricDist.norm_add_le_max _ _
      _ ≤ max ‖(b : C)‖ (p : ℝ)⁻¹ := by
        rw [norm_mul, norm_mul, hpC]
        exact max_le_max (mul_le_of_le_one_right (norm_nonneg _) (norm_intCast_le_one' _))
          (mul_le_of_le_one_right (by positivity) (norm_intCast_le_one' _))
  have hp1 : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
  rcases le_max_iff.1 h1 with h | h
  · exact h
  · linarith

end Norms

theorem exists_exp {K : Type} [Field K] [CharZero K] {p : ℕ} (hp : p.Prime) {γ : K} (h0 : γ ≠ 0)
    (hi : IsIntegral ℤ γ) : ∃ e : ℕ, ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C],
      ‖(p : C)‖ = (p : ℝ)⁻¹ → ∀ f : K →+* C, ‖f γ‖⁻¹ ≤ (p : ℝ) ^ e := by
  have ha : (minpoly ℤ γ).coeff 0 ≠ 0 := by
    intro h
    have hq := minpoly.coeff_zero_ne_zero (A := ℚ) (IsIntegral.tower_top hi) h0
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hi, Polynomial.coeff_map, h, map_zero] at hq
    exact hq rfl
  obtain ⟨e, b, hb, hab⟩ := Nat.exists_eq_pow_mul_and_not_dvd (Int.natAbs_ne_zero.2 ha) p hp.ne_one
  refine ⟨e, fun C _ _ hpC f => ?_⟩
  have hz : Polynomial.aeval (f γ) (minpoly ℤ γ) = 0 := by
    rw [show f γ = f.toIntAlgHom γ from rfl, Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
  have h1 := norm_coeff_zero_le (minpoly ℤ γ) hz (norm_le_one_of_isIntegral (hi.map f.toIntAlgHom))
  have h2 : ‖(((minpoly ℤ γ).coeff 0 : ℤ) : C)‖ = ‖((((minpoly ℤ γ).coeff 0).natAbs : ℕ) : C)‖ := by
    rcases Int.natAbs_eq ((minpoly ℤ γ).coeff 0) with h | h
    · conv_lhs => rw [h]
      simp
    · conv_lhs => rw [h]
      simp
  rw [h2, hab, Nat.cast_mul, Nat.cast_pow, norm_mul, norm_pow, hpC] at h1
  have h3 := one_le_norm_natCast hp hpC hb
  have hpos : 0 < ‖f γ‖ := norm_pos_iff.2 ((map_ne_zero f).2 h0)
  have hpp : (0 : ℝ) < (p : ℝ) ^ e := pow_pos (by exact_mod_cast hp.pos) e
  have h4 : ((p : ℝ) ^ e)⁻¹ ≤ ‖f γ‖ := by
    rw [← inv_pow]
    calc ((p : ℝ)⁻¹) ^ e = ((p : ℝ)⁻¹) ^ e * 1 := (mul_one _).symm
      _ ≤ ((p : ℝ)⁻¹) ^ e * ‖(b : C)‖ := by gcongr
      _ ≤ ‖f γ‖ := h1
  rw [inv_le_comm₀ hpos hpp]
  exact h4

section BaseChange

open MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  (t : SAB H X) {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S') (x : Sp S ⟶ X)

def bcT (v : TanM x t.G) : TanM (spMap φ ≫ x) t.G :=
  GlobalTheory.LieMet.tanOf (GlobalTheory.LieMet.isTan_map φ rfl (GlobalTheory.LieMet.isTan_tv v))

theorem bcT_sum {m : ℕ} (a : Fin m → S) (u : Fin m → TanM x t.G) :
    bcT t φ x (∑ i, a i • u i) = ∑ i, φ (a i) • bcT t φ x (u i) := by
  have h := (GlobalTheory.LieMet.isComb_iff u a (∑ i, a i • u i)).2 rfl
  have h2 := GlobalTheory.LatDRFree.comb_map t φ h
  exact (GlobalTheory.LieMet.isComb_iff (fun i => bcT t φ x (u i)) (fun i => φ (a i)) _).1 h2

theorem bcT_act (a : 𝓞 E) (v : TanM x t.G) :
    bcT t φ x (actR (x0 := x) t.act a v) = actR (x0 := spMap φ ≫ x) t.act a (bcT t φ x v) :=
  GlobalTheory.LieMet.tan_ext (Category.assoc _ _ _).symm

theorem bcT_aeval (α : 𝓞 E) (Q : Polynomial S) (v : TanM x t.G) :
    bcT t φ x (Polynomial.aeval (actR (x0 := x) t.act α) Q v) =
      Polynomial.aeval (actR (x0 := spMap φ ≫ x) t.act α) (Q.map φ) (bcT t φ x v) := by
  have hn : Q.natDegree < Q.natDegree + 1 := Nat.lt_succ_self _
  have hn' : (Q.map φ).natDegree < Q.natDegree + 1 := lt_of_le_of_lt Polynomial.natDegree_map_le hn
  rw [Polynomial.aeval_eq_sum_range' hn, Polynomial.aeval_eq_sum_range' hn']
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, ← map_pow, Finset.sum_range,
    Polynomial.coeff_map]
  rw [bcT_sum]
  simp only [bcT_act]

end BaseChange

section Main

open MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

open Classical in

theorem integral_prod_sub {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {l : Level H} (c : Coeff l) (α : 𝓞 E) (σ : E →+* ℂ) :
    _root_.IsIntegral ℤ (∏ τ ∈ Finset.univ.erase σ, (embK c σ α - embK c τ α)) := by
  refine Finset.prod_induction _ (_root_.IsIntegral ℤ) (fun _ _ => IsIntegral.mul) isIntegral_one fun τ _ => ?_
  have hα : _root_.IsIntegral ℤ α := Algebra.IsIntegral.isIntegral α
  exact (hα.map (embK c σ).toIntAlgHom).sub (hα.map (embK c τ).toIntAlgHom)

theorem scale : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)
    {l : Level H} (c : Coeff l) {X : Scheme.{0}} (t : SAB H X) (p : ℕ), p.Prime → ∃ m : ℕ, ∀ (C : Type)
    [NontriviallyNormedField C] [IsUltrametricDist C], ‖(p : C)‖ = (p : ℝ)⁻¹ → ∀ (f : c.F →+* C) (x : Sp C ⟶ X)
    (u : Vecs Dw t C), GlobalTheory.LocM.IsFrame t f x u → ∀ (j : Fin (letters Dw).length), ∃ a : ℝ, 1 ≤ a ∧ a ≤ (p : ℝ) ^ m ∧
      ∀ r ∈ Guard.grSet t x (latDR t x) (fun i => u ((letters Dw).get i).1 ((letters Dw).get i).2) j,
        a * r ∈ Guard.grSet t x (latDR t x) (u ((letters Dw).get j).1) ((letters Dw).get j).2 := by
  intro E i1 i2 i3 H Dw l c X t p hp
  classical
  have : CharZero c.F := RingHom.charZero c.F.val.toRingHom
  obtain ⟨α, hinj, -, -⟩ :=
    exists_sepElt (E := E) (F := c.F) c.F.val.toRingHom (embK c) (fun τ a => embK_coe c τ a)
  let gm : (E →+* ℂ) → c.F := fun σ => ∏ τ ∈ Finset.univ.erase σ, (embK c σ α - embK c τ α)
  have hgm0 : ∀ σ, gm σ ≠ 0 := fun σ => Finset.prod_ne_zero_iff.2 fun τ hτ =>
    sub_ne_zero.2 fun h => (Finset.ne_of_mem_erase hτ) (hinj h).symm
  choose e he using fun σ => exists_exp hp (hgm0 σ) (integral_prod_sub c α σ)
  refine ⟨∑ σ, e σ, fun C _ _ hpC f x u hu j => ?_⟩
  let eq := Equiv.ofBijective _ (GlobalTheory.Proof.frame_combination_coeff_unique.get_bijective Dw)
  have hget : ∀ i, eq i = (letters Dw).get i := fun _ => rfl
  generalize hy : (letters Dw).get j = y
  obtain ⟨σ, k⟩ := y
  have hj : eq.symm ⟨σ, k⟩ = j := by rw [← hy]; exact eq.symm_apply_apply j
  have hfgm : f (gm σ) ≠ 0 := (map_ne_zero f).2 (hgm0 σ)
  have hn1 : ‖f (gm σ)‖ ≤ 1 := norm_le_one_of_isIntegral ((integral_prod_sub c α σ).map f.toIntAlgHom)
  have hpos : 0 < ‖f (gm σ)‖ := norm_pos_iff.2 hfgm
  refine ⟨‖f (gm σ)‖⁻¹, (one_le_inv₀ hpos).2 hn1, (he σ C hpC f).trans
    (pow_le_pow_right₀ (by exact_mod_cast hp.one_lt.le) (Finset.single_le_sum (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ σ))), ?_⟩
  rintro r ⟨cg, hcg0, hcgz, ⟨w, ⟨xO, rfl, vO, hvO, rfl⟩, hc⟩, rfl⟩

  let xC := spMap (intO C).subtype ≫ xO
  let ρ := actR (x0 := xC) (S := C) t.act
  let U : GlobalTheory.ShFam.Pad.Letter Dw → TanM xC t.G := fun y => GlobalTheory.LieMet.tanOf (hu.1 y.1 y.2).1
  have hU : ∀ y (a : 𝓞 E), ρ a (U y) = f (embK c y.1 a) • U y := fun y a =>
    GlobalTheory.LieMet.tan_ext ((hu.1 y.1 y.2).2 a)
  let lam : (E →+* ℂ) → intO C := fun τ => ⟨f (embK c τ α), norm_le_one_of_isIntegral
    (((Algebra.IsIntegral.isIntegral (R := ℤ) α).map (embK c τ).toIntAlgHom).map f.toIntAlgHom)⟩
  let Q : Polynomial (intO C) := ∏ τ ∈ Finset.univ.erase σ, (Polynomial.X - Polynomial.C (lam τ))
  let wv : TanM xC t.G := bcT t (intO C).subtype xO (GlobalTheory.LieMet.tanOf hvO)
  have hw : wv = ∑ i, cg i • U ((letters Dw).get i) :=
    (GlobalTheory.LieMet.isComb_iff (fun i => U ((letters Dw).get i)) cg wv).1 hc
  have hval : ∀ y : GlobalTheory.ShFam.Pad.Letter Dw, Polynomial.aeval (ρ α) (Q.map (intO C).subtype) (U y) =
      (if y.1 = σ then f (gm σ) else 0) • U y := by
    intro y
    rw [aevalS_eig (ρ α) (hU y α)]
    congr 1
    simp only [Q, Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, map_prod, map_sub,
      Polynomial.aeval_X, Polynomial.aeval_C]
    split_ifs with h
    · subst h
      simp only [gm, map_prod, map_sub]
      rfl
    · exact Finset.prod_eq_zero (Finset.mem_erase.2 ⟨h, Finset.mem_univ _⟩) (sub_self _)

  have hg2 : ∀ y, (letters Dw).get (eq.symm y) = y := fun y => eq.apply_symm_apply y
  let cf : Fin (Dw.mult σ) → C := fun i => f (gm σ) * cg (eq.symm ⟨σ, i⟩)
  have hsum : Polynomial.aeval (ρ α) (Q.map (intO C).subtype) wv = ∑ i, cf i • U ⟨σ, i⟩ := by
    rw [hw, map_sum]
    simp only [map_smul, hval]
    rw [← Equiv.sum_comp eq.symm]
    simp only [hg2]
    rw [Fintype.sum_sigma, Finset.sum_eq_single σ]
    · refine Finset.sum_congr rfl fun i _ => ?_
      dsimp only
      rw [if_pos rfl, smul_smul, mul_comm]
    · intro τ _ hτ
      exact Finset.sum_eq_zero fun i _ => by dsimp only; rw [if_neg hτ, zero_smul, smul_zero]
    · intro h
      exact absurd (Finset.mem_univ σ) h
  refine ⟨cf, ?_, ?_, ⟨_, ?_, (GlobalTheory.LieMet.isComb_iff (fun i => U ⟨σ, i⟩) cf _).2 hsum⟩, ?_⟩
  · show f (gm σ) * cg (eq.symm ⟨σ, k⟩) ≠ 0
    rw [hj]
    exact mul_ne_zero hfgm hcg0
  · intro i hi
    show f (gm σ) * cg (eq.symm ⟨σ, i⟩) = 0
    rw [hcgz _ ?_, mul_zero]
    by_contra hle
    push_neg at hle
    rcases hle.lt_or_eq with hlt | heq
    · have h1 := List.pairwise_iff_get.1 (GlobalTheory.Proof.frame_combination_coeff_unique.pairwise_letters Dw) _ _ hlt
      rw [hg2, hy] at h1
      have h3 : (i : ℕ) < k := h1 rfl
      have h4 : (k : ℕ) < i := Fin.lt_iff_val_lt_val.1 hi
      omega
    · have h1 := congrArg eq heq
      rw [Equiv.apply_symm_apply, hget, hy] at h1
      have h2 : i = k := eq_of_heq (Sigma.mk.inj_iff.1 h1).2
      exact absurd hi (by rw [h2]; exact lt_irrefl _)
  · exact ⟨xO, rfl, (tv (Polynomial.aeval (actR (x0 := xO) t.act α) Q (GlobalTheory.LieMet.tanOf hvO))).left,
      GlobalTheory.LieMet.isTan_tv _, congrArg (fun z => (tv z).left) (bcT_aeval t (intO C).subtype xO α Q _)⟩
  · show ‖f (gm σ)‖⁻¹ * ‖cg j‖⁻¹ = ‖f (gm σ) * cg (eq.symm ⟨σ, k⟩)‖⁻¹
    rw [hj, norm_mul, mul_inv]

end Main

end GlobalTheory.ShFam.Pad.LieScale
