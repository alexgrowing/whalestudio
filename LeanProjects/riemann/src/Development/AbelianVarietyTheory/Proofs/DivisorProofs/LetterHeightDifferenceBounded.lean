import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelSt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdmissibleRepresentationFactorisation
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSlopeBoundsFrames
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameBaseChangeRingHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightComparisonLocalGreen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteSetResidueLogBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogGreenDifferenceDeterminantLe

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.ShFam.Pad.LieScale GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.Cartier
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.ConcatStep

theorem exists_nat_le {K : Type} [Field K] [CharZero K] {γ : K} (h0 : γ ≠ 0) (hi : IsIntegral ℤ γ) :
    ∃ n : ℕ, n ≠ 0 ∧ ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] (f : K →+* C),
      ‖(n : C)‖ ≤ ‖f γ‖ := by
  have ha : (minpoly ℤ γ).coeff 0 ≠ 0 := by
    intro h
    have hq := minpoly.coeff_zero_ne_zero (A := ℚ) (IsIntegral.tower_top hi) h0
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hi, Polynomial.coeff_map, h, map_zero] at hq
    exact hq rfl
  refine ⟨_, Int.natAbs_ne_zero.2 ha, fun C _ _ f => ?_⟩
  have hz : Polynomial.aeval (f γ) (minpoly ℤ γ) = 0 := by
    rw [show f γ = f.toIntAlgHom γ from rfl, Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
  have h1 := norm_coeff_zero_le (minpoly ℤ γ) hz (norm_le_one_of_isIntegral (hi.map f.toIntAlgHom))
  have h2 : ‖(((minpoly ℤ γ).coeff 0 : ℤ) : C)‖ = ‖((((minpoly ℤ γ).coeff 0).natAbs : ℕ) : C)‖ := by
    rcases Int.natAbs_eq ((minpoly ℤ γ).coeff 0) with h | h
    · conv_lhs => rw [h]
      simp
    · conv_lhs => rw [h]
      simp
  rwa [h2] at h1

theorem log_le_of_mul_norm_le {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C] {p N : ℕ} (hp : p.Prime)
    (hpC : ‖(p : C)‖ = (p : ℝ)⁻¹) (hN : N ≠ 0) {a : ℝ} (h1 : 1 ≤ a) (ha : a * ‖(N : C)‖ ≤ 1) :
    Real.log a ≤ if p ∈ N.primeFactors then Real.log N else 0 := by
  split_ifs with h
  · obtain ⟨e, b, hb, hab⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN p hp.ne_one
    have h3 := one_le_norm_natCast hp hpC hb
    have hb1 : (1 : ℝ) ≤ b := by
      have : b ≠ 0 := by rintro rfl; exact hb (dvd_zero _)
      exact_mod_cast Nat.one_le_iff_ne_zero.2 this
    have hpp : (0 : ℝ) < (p : ℝ) ^ e := pow_pos (by exact_mod_cast hp.pos) e
    refine Real.log_le_log (by linarith) ?_
    rw [hab, Nat.cast_mul, Nat.cast_pow, norm_mul, norm_pow, hpC, inv_pow] at ha
    rw [hab, Nat.cast_mul, Nat.cast_pow]
    have h4 : a * ((p : ℝ) ^ e)⁻¹ ≤ 1 := by
      refine le_trans ?_ ha
      gcongr
      exact le_mul_of_one_le_right (by positivity) h3
    rw [← div_eq_mul_inv, div_le_one hpp] at h4
    nlinarith
  · have hd : ¬ p ∣ N := fun hd => h (Nat.mem_primeFactors.2 ⟨hp, hd, hN⟩)
    have h3 := one_le_norm_natCast hp hpC hd
    exact Real.log_nonpos (by linarith) (by nlinarith)

theorem abs_log_sInf_sub_le {A B : Set ℝ} {a : ℝ} (h1 : 1 ≤ a) (hA : ∀ r ∈ A, 0 ≤ r) (hBA : B ⊆ A)
    (hAB : ∀ r ∈ A, a * r ∈ B) : |Real.log (sInf A) - Real.log (sInf B)| ≤ Real.log a := by
  have hl : 0 ≤ Real.log a := Real.log_nonneg h1
  rcases A.eq_empty_or_nonempty with rfl | hne
  · rw [Set.subset_empty_iff.1 hBA, sub_self, abs_zero]
    exact hl
  have hBne : B.Nonempty := let ⟨r, hr⟩ := hne; ⟨_, hAB r hr⟩
  have e1 : sInf A ≤ sInf B := csInf_le_csInf ⟨0, hA⟩ hBne hBA
  have e2 : sInf B ≤ a * sInf A := by
    rw [← div_le_iff₀' (by linarith)]
    refine le_csInf hne fun r hr => ?_
    rw [div_le_iff₀' (by linarith)]
    exact csInf_le ⟨0, fun s hs => hA s (hBA hs)⟩ (hAB r hr)
  rcases (le_csInf hne hA).eq_or_lt with h0 | h0
  · have : sInf B = sInf A := le_antisymm (by rw [← h0] at e2 ⊢; simpa using e2) e1
    rw [this, sub_self, abs_zero]
    exact hl
  · have f1 := Real.log_le_log h0 e1
    have f2 := Real.log_le_log (h0.trans_le e1) e2
    rw [Real.log_mul (by linarith) h0.ne'] at f2
    rw [abs_le]
    constructor <;> linarith

section Main

open MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

theorem scale_unif {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    (Dw : Datum H) {l : Level H} (c : Coeff l) : ∃ N : ℕ, N ≠ 0 ∧ ∀ {X : Scheme.{0}} (t : SAB H X) (C : Type)
    [NontriviallyNormedField C] [IsUltrametricDist C] (f : c.F →+* C) (x : Sp C ⟶ X)
    (u : Vecs Dw t C), GlobalTheory.LocM.IsFrame t f x u → ∀ (j : Fin (letters Dw).length), ∃ a : ℝ, 1 ≤ a ∧
      a * ‖(N : C)‖ ≤ 1 ∧
      ∀ r ∈ Guard.grSet t x (latDR t x) (fun i => u ((letters Dw).get i).1 ((letters Dw).get i).2) j,
        a * r ∈ Guard.grSet t x (latDR t x) (u ((letters Dw).get j).1) ((letters Dw).get j).2 := by
  classical
  have : CharZero c.F := RingHom.charZero c.F.val.toRingHom
  obtain ⟨α, hinj, -, -⟩ :=
    exists_sepElt (E := E) (F := c.F) c.F.val.toRingHom (embK c) (fun τ a => embK_coe c τ a)
  let gm : (E →+* ℂ) → c.F := fun σ => ∏ τ ∈ Finset.univ.erase σ, (embK c σ α - embK c τ α)
  have hgm0 : ∀ σ, gm σ ≠ 0 := fun σ => Finset.prod_ne_zero_iff.2 fun τ hτ =>
    sub_ne_zero.2 fun h => (Finset.ne_of_mem_erase hτ) (hinj h).symm
  choose e he0 he using fun σ => exists_nat_le (hgm0 σ) (integral_prod_sub c α σ)
  refine ⟨∏ σ, e σ, Finset.prod_ne_zero_iff.2 fun σ _ => he0 σ, fun {X} t C _ _ f x u hu j => ?_⟩
  let eq := Equiv.ofBijective _ (GlobalTheory.Proof.frame_combination_coeff_unique.get_bijective Dw)
  have hget : ∀ i, eq i = (letters Dw).get i := fun _ => rfl
  generalize hy : (letters Dw).get j = y
  obtain ⟨σ, k⟩ := y
  have hj : eq.symm ⟨σ, k⟩ = j := by rw [← hy]; exact eq.symm_apply_apply j
  have hfgm : f (gm σ) ≠ 0 := (map_ne_zero f).2 (hgm0 σ)
  have hn1 : ‖f (gm σ)‖ ≤ 1 := norm_le_one_of_isIntegral ((integral_prod_sub c α σ).map f.toIntAlgHom)
  have hpos : 0 < ‖f (gm σ)‖ := norm_pos_iff.2 hfgm
  refine ⟨‖f (gm σ)‖⁻¹, (one_le_inv₀ hpos).2 hn1, ?_, ?_⟩
  · rw [inv_mul_le_iff₀ hpos, _root_.mul_one, ← Finset.mul_prod_erase _ _ (Finset.mem_univ σ), Nat.cast_mul, norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) (norm_natCast_le_one' _)).trans (he σ C f)
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

section Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem abs_lnStep_sub_le (Dw : Datum H) {l : Level H} (c : Coeff l) : ∃ N : ℕ, N ≠ 0 ∧
    ∀ {X : Scheme.{0}} (t : SAB H X) (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] (p : ℕ), p.Prime →
    ‖(p : C)‖ = (p : ℝ)⁻¹ → ∀ (f : c.F →+* C) (x : Sp C ⟶ X) (u : Vecs Dw t C), GlobalTheory.LocM.IsFrame t f x u →
    ∀ (j : Fin (letters Dw).length),
      |lnStep t x u p false (.inr (j : ℕ)) -
        lnStep t x u p false (.inl (((letters Dw).get j).1, (((letters Dw).get j).2 : ℕ)))| ≤
        if p ∈ N.primeFactors then Real.log N else 0 := by
  obtain ⟨N, hN, h⟩ := scale_unif Dw c
  refine ⟨N, hN, fun {X} t C _ _ p hp hpC f x u hu j => ?_⟩
  obtain ⟨a, h1, ha, hs⟩ := h t C f x u hu j
  refine le_trans ?_ (log_le_of_mul_norm_le hp hpC hN h1 ha)
  simp only [lnStep, dif_pos j.2, dif_pos ((letters Dw).get j).2.2, lat, Bool.false_eq_true, false_and, if_false,
    sub_zero]
  refine abs_log_sInf_sub_le h1 ?_ ?_ hs
  · rintro r ⟨cf, -, -, -, rfl⟩
    positivity
  · rintro r ⟨cf, h0, hz, ⟨w, hw, hc⟩, rfl⟩
    obtain ⟨cg, g1, g2, g3⟩ := (GlobalTheory.Proof.frame_combination_coeff_unique.concat_frame E H Dw l c X t C f x u hu).2 j cf w hz hc
    exact ⟨cg, g2 ▸ h0, g1, ⟨w, hw, g3⟩, by rw [g2]⟩

theorem expo_eq (Dw : Datum H) (j : Fin (letters Dw).length) :
    expo Dw (Finsupp.single (((fun _ => false), none, .inr (j : ℕ)) : Sym E) 1) =
      expo Dw (Finsupp.single (((fun _ => false), none,
        .inl (((letters Dw).get j).1, (((letters Dw).get j).2 : ℕ))) : Sym E) 1) := by
  funext x
  rw [GlobalTheory.LgDiff.expo_single', GlobalTheory.LgDiff.expo_single']
  have e1 : letterOf Dw (.inr (j : ℕ)) = some ((letters Dw).get j) := List.getElem?_eq_getElem j.2
  have e2 : letterOf Dw (.inl (((letters Dw).get j).1, (((letters Dw).get j).2 : ℕ))) = some ((letters Dw).get j) :=
    dif_pos ((letters Dw).get j).2.2
  rw [e1, e2]

omit [NumberField E] [IsCMField E] in

theorem parOf_single (a : Sym E) : parOf (Finsupp.single a 1) = a.2.1 := by
  unfold parOf
  have hn : (Finsupp.single a (1 : ℤ)).support.Nonempty := ⟨a, by simp⟩
  rw [dif_pos hn]
  have := Finsupp.support_single_subset hn.choose_spec
  rw [Finset.mem_singleton] at this
  rw [this]

omit [NumberField E] [IsCMField E] in

theorem sum_single (a : Sym E) (Φ : Sym E → ℝ) :
    ((Finsupp.single a (1 : ℤ)).sum fun b n => (n : ℝ) * Φ b) = Φ a := by
  rw [Finsupp.sum_single_index (by simp), Int.cast_one, one_mul]

theorem abs_lnStep_bc_le (Dw : Datum H) {l : Level H} (c : Coeff l) : ∃ N : ℕ, N ≠ 0 ∧
    ∀ {Xo : Moduli Dw l} {O : Type} [CommRing O] {β : O →+* c.F} (Z : Model Xo c β) (j : Fin (letters Dw).length)
      (p : ℕ) (_ : Fact p.Prime) (_ : IsUltrametricDist ℂ_[p]) (R : Type) [CommRing R] (φ : c.F →+* R) (x₀ : Sp R ⟶ Z.X) (f : EigFrame Z φ x₀)
      (ψ : R →+* ℂ_[p]),
        |lnStep Z.t (spMap ψ ≫ x₀) (fun τ i => spMap (dualMap ψ) ≫ f.v τ i) p false (.inr (j : ℕ)) -
          lnStep Z.t (spMap ψ ≫ x₀) (fun τ i => spMap (dualMap ψ) ≫ f.v τ i) p false
            (.inl (((letters Dw).get j).1, (((letters Dw).get j).2 : ℕ)))| ≤
          if p ∈ N.primeFactors then Real.log N else 0 := by
  obtain ⟨N, hN, h⟩ := abs_lnStep_sub_le Dw c
  refine ⟨N, hN, fun {Xo O} _ {β} Z j p hp _ R _ φ x₀ f ψ => ?_⟩
  have hn : ‖(p : ℂ_[p])‖ = (p : ℝ)⁻¹ := by
    rw [← map_natCast (algebraMap ℚ_[p] ℂ_[p]), norm_algebraMap', Padic.norm_p]
  exact h Z.t _ _ hp.out hn _ _ _ (GlobalTheory.LocM.isFrame_bc E H Dw l c _ Z.t _ _ φ ψ x₀ f.v
    ⟨fun τ i => ⟨f.tan τ i, f.eig τ i⟩, f.basis⟩) j

theorem abs_add_mul_sub_le {A k m s s' B : ℝ} (h : |s - s'| ≤ B) :
    |A + -k / m * s - (A + -k / m * s')| ≤ |k / m| * B := by
  rw [add_sub_add_left_eq_sub, ← mul_sub, abs_mul, neg_div, abs_neg]
  exact mul_le_mul_of_nonneg_left h (abs_nonneg _)

theorem abs_lgOf_single_sub_le {Dw : Datum H} {l : Level H} {c : Coeff l} {Xo : Moduli Dw l} {O : Type} [CommRing O]
    {β : O →+* c.F} {Z : Model Xo c β} {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} (Y : FlagCpt Z e)
    (a a' : Sym E) (he : expo Dw (Finsupp.single a 1) = expo Dw (Finsupp.single a' 1))
    (v : HeightOneSpectrum (𝓞 F)) (ε : Ext v) (y : AlgPt Y.Y) (hp : (resP v).Prime) (B : ℝ)
    (h : ∀ (_ : Fact (resP v).Prime) (_ : IsUltrametricDist ℂ_[resP v]) (R : Type) [CommRing R] (φ : c.F →+* R) (x₀ : Sp R ⟶ Z.X) (f : EigFrame Z φ x₀)
      (ψ : R →+* ℂ_[resP v]),
      |lnStep Z.t (spMap ψ ≫ x₀) (fun τ i => spMap (dualMap ψ) ≫ f.v τ i) (resP v) (a.1 (resP v)) a.2.2 -
        lnStep Z.t (spMap ψ ≫ x₀) (fun τ i => spMap (dualMap ψ) ≫ f.v τ i) (resP v) (a'.1 (resP v)) a'.2.2| ≤ B) :
    |lgOf Y (Finsupp.single a 1) v ε y - lgOf Y (Finsupp.single a' 1) v ε y| ≤
      |Real.log (ε.w (resP v)) / Real.log (resP v)| * B := by
  simp only [lgOf, dif_pos hp]
  rewrite [he, sum_single, sum_single]
  exact abs_add_mul_sub_le (h _ _ _ _ _ _ _)

theorem abs_lgOf_sub_le (Dw : Datum H) {l : Level H} (c : Coeff l) : ∃ N : ℕ, N ≠ 0 ∧
    ∀ {Xo : Moduli Dw l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
      {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} (Y : FlagCpt Z e) (j : Fin (letters Dw).length)
      (v : HeightOneSpectrum (𝓞 F)) (ε : Ext v) (y : AlgPt Y.Y),
      |lgOf Y (Finsupp.single (((fun _ => false), none, .inr (j : ℕ)) : Sym E) 1) v ε y -
        lgOf Y (Finsupp.single (((fun _ => false), none,
          .inl (((letters Dw).get j).1, (((letters Dw).get j).2 : ℕ))) : Sym E) 1) v ε y| ≤
        |Real.log (ε.w (resP v)) / Real.log (resP v)| * if resP v ∈ N.primeFactors then Real.log N else 0 := by
  obtain ⟨N, hN, h⟩ := abs_lnStep_bc_le Dw c
  refine ⟨N, hN, fun {Xo O} _ {β Z F} _ _ {e} Y j v ε y => ?_⟩
  by_cases hp : (resP v).Prime
  · exact abs_lgOf_single_sub_le Y _ _ (expo_eq Dw j) v ε y hp _ (h Z j (resP v))
  · simp only [lgOf, dif_neg hp, sub_self, abs_zero]
    refine mul_nonneg (abs_nonneg _) ?_
    split_ifs
    · exact Real.log_natCast_nonneg _
    · exact le_rfl

theorem abs_ht_sub_le (Dw : Datum H) {l : Level H} (c : Coeff l) : ∃ K : ℝ,
    ∀ {Xo : Moduli Dw l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
      {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} (Y : FlagCpt Z e) {C : CxSt F} (hm : Mets Y C)
      (x : Y.Y.X) (j : Fin (letters Dw).length),
      |(adlOf Y hm (Finsupp.single (((fun _ => false), none, .inr (j : ℕ)) : Sym E) 1)).ht x -
        (adlOf Y hm (Finsupp.single (((fun _ => false), none,
          .inl (((letters Dw).get j).1, (((letters Dw).get j).2 : ℕ))) : Sym E) 1)).ht x| ≤ K := by
  obtain ⟨N, hN, h⟩ := abs_lgOf_sub_le Dw c
  refine ⟨∑ _p ∈ N.primeFactors, Real.log N, fun {Xo O} _ {β Z F} _ _ {e} Y C hm x j => ?_⟩
  set w₁ : Sym E →₀ ℤ := Finsupp.single (((fun _ => false), none, .inr (j : ℕ)) : Sym E) 1 with hw₁
  set w₂ : Sym E →₀ ℤ := Finsupp.single (((fun _ => false), none,
          .inl (((letters Dw).get j).1, (((letters Dw).get j).2 : ℕ))) : Sym E) 1 with hw₂
  have e0 : adlOf Y hm w₂ = { adlOf Y hm w₁ with lg := lgOf Y w₂ } := by
    have e1 : expo Dw w₂ = expo Dw w₁ := (expo_eq Dw j).symm
    have e2 : parOf w₂ = parOf w₁ := by rw [hw₁, hw₂, parOf_single, parOf_single]
    unfold adlOf
    rw [e1, e2]
  rw [e0]
  have hl : 0 ≤ Real.log N := Real.log_natCast_nonneg _
  obtain ⟨hle, S, hS, hsum⟩ := GlobalTheory.PlaceSum.sum_localDeg_le (F := F) N.primeFactors
    (fun p hp => Nat.prime_of_mem_primeFactors hp) (fun _ => Real.log N) (fun _ => hl)
  have hw : ∀ (v : HeightOneSpectrum (𝓞 F)) (ε : Ext v),
      ε.w (resP v : AlgebraicClosure F) = NumberField.HeightOneSpectrum.adicAbv F v (resP v : F) := by
    intro v ε
    rw [← map_natCast (algebraMap F (AlgebraicClosure F)), ε.w_alg]
  refine GlobalTheory.TrueGeo.Adl.abs_ht_sub_ht_with_lg_le _ _ _ S
    (fun v => (-Real.log (NumberField.HeightOneSpectrum.adicAbv F v (resP v : F)) / Real.log (resP v)) *
      Real.log N) _ (Finset.sum_nonneg fun _ _ => hl) ?_ ?_ ?_
  · intro v hv e y
    have h' := h Y j v e y
    rw [if_neg (fun h'' => hv ((hS v).2 h'')), mul_zero] at h'
    exact sub_eq_zero.1 (abs_nonpos_iff.1 h')
  · intro v e y
    refine (h Y j v e y).trans ?_
    rw [hw, abs_div, abs_of_nonpos (Real.log_nonpos (AbsoluteValue.nonneg _ _) (hle v)),
      abs_of_nonneg (Real.log_natCast_nonneg _)]
    refine mul_le_mul_of_nonneg_left ?_
      (div_nonneg (neg_nonneg.2 (Real.log_nonpos (AbsoluteValue.nonneg _ _) (hle v))) (Real.log_natCast_nonneg _))
    split_ifs
    · exact le_rfl
    · exact hl
  · refine hsum.trans_eq ?_
    simp only [adlOf, PNat.one_coe, Nat.cast_one, one_mul]

end Gen

end GlobalTheory.ConcatStep

end

open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts
open GlobalTheory.ShFam GlobalTheory.ShFam.Pad ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem GlobalTheory.ConcatStep.step : ∀ (D : D7) (O : Setup D), ∃ C : ℝ, ∀ (c : O.s.Comp) (x : (O.var c).X)
    (j : Fin (letters O.S.Dw).length),
    |(adlOf (O.Φ.C c) (O.met.hm c) (Finsupp.single (((fun _ => false), none, .inr (j : ℕ)) : Sym D.host.E) 1)).ht x -
      (adlOf (O.Φ.C c) (O.met.hm c) (Finsupp.single (((fun _ => false), none,
        .inl (((letters O.S.Dw).get j).1, (((letters O.S.Dw).get j).2 : ℕ))) : Sym D.host.E) 1)).ht x| ≤ C := by
  intro D O
  exact (GlobalTheory.ConcatStep.abs_ht_sub_le O.S.Dw _).imp fun K h c x j => h (O.Φ.C c) (O.met.hm c) x j
