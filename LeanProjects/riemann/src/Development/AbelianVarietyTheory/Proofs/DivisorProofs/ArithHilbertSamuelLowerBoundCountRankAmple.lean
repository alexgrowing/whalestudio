import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundlePairSectionsMulMemNormMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermPairPowSectionMemAndNormPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveSectionValueUnitFrameStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousHermSectionValueMulConjAndNormBoundedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionQuotientsTranscendenceBasisBasepointFreeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFunctionFieldBasisOfSectionsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardBoundedHomogeneousIntFormFamiliesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneousFormCombinationEqZeroIndependentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjArithFunctionFieldCharZeroTrdegStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp.FLower

open MvPolynomial

abbrev Deg (D q : ℕ) : Type := {α : Fin (D + 1) →₀ ℕ // α.degree = q}

scoped instance (D q : ℕ) : Finite (Deg D q) :=
  Nat.finite_of_card_ne_zero <| by
    rw [(GlobalTheory.T.card_bounded_homogeneous_int_form_families D q 0 0 le_rfl).2.2.1]
    exact (Nat.choose_pos (Nat.le_add_left D q)).ne'

scoped instance (D q : ℕ) : Fintype (Deg D q) := Fintype.ofFinite _

theorem card_deg (D q : ℕ) : Fintype.card (Deg D q) = (q + D).choose D := by
  rw [← Nat.card_eq_fintype_card]; exact (GlobalTheory.T.card_bounded_homogeneous_int_form_families D q 0 0 le_rfl).2.2.1

def xm {K : Type} [CommRing K] {D : ℕ} (x : Fin (D + 1) → K) (α : Fin (D + 1) →₀ ℕ) : K := ∏ l, x l ^ α l

theorem aeval_eq_sum {K : Type} [CommRing K] {D q : ℕ} (x : Fin (D + 1) → K) (T : MvPolynomial (Fin (D + 1)) ℤ)
    (hT : T.IsHomogeneous q) : aeval x T = ∑ α : Deg D q, coeff α.1 T • xm x α.1 := by
  rw [aeval_def, eval₂_eq']
  have hsub : T.support ⊆ Finset.univ.map (Function.Embedding.subtype fun α : Fin (D + 1) →₀ ℕ => α.degree = q) := by
    intro d hd
    have h := hT (mem_support_iff.1 hd)
    refine Finset.mem_map.2 ⟨⟨d, ?_⟩, Finset.mem_univ _, rfl⟩
    rw [Finsupp.degree_eq_weight_one]; exact h
  rw [Finset.sum_subset hsub (fun d _ hd => by rw [notMem_support_iff.1 hd, map_zero, zero_mul]), Finset.sum_map]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [zsmul_eq_mul, xm, algebraMap_int_eq, eq_intCast]
  rfl

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

theorem H_congr (P : Pair p) {a a' b b' : ℤ} (ha : a = a') (hb : b = b') {f : X.functionField} (hf : f ∈ P.H a b) :
    f ∈ P.H a' b' := by subst ha hb; exact hf

theorem nu_nonneg (P : Pair p) (a b : ℤ) (σ : k →+* ℂ) (y : CxPts p σ) (f : X.functionField) : 0 ≤ P.nu a b σ y f :=
  mul_nonneg (norm_nonneg _) (Real.exp_pos _).le

theorem prod_pow_mem (P : Pair p) (e : ℤ) {D : ℕ} (x : Fin (D + 1) → X.functionField) (hx : ∀ l, x l ∈ P.H e 0)
    (α : Fin (D + 1) →₀ ℕ) (s : Finset (Fin (D + 1))) :
    (∏ l ∈ s, x l ^ α l) ∈ P.H ((∑ l ∈ s, (α l : ℤ)) * e) 0 ∧ ∀ σ y,
      P.nu ((∑ l ∈ s, (α l : ℤ)) * e) 0 σ y (∏ l ∈ s, x l ^ α l) = ∏ l ∈ s, P.nu e 0 σ y (x l) ^ α l := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    obtain ⟨h1, h2⟩ := GlobalTheory.VolBr.NuPow.pow_mem_H_and_nu_pow k X p P e 0 (x 0) (hx 0) 0
    simp only [Finset.prod_empty, Finset.sum_empty, pow_zero, Nat.cast_zero, zero_mul] at h1 h2 ⊢
    exact ⟨h1, fun σ y => h2 σ y⟩
  | insert l s hl ih =>
    obtain ⟨h1, h2⟩ := GlobalTheory.VolBr.NuPow.pow_mem_H_and_nu_pow k X p P e 0 (x l) (hx l) (α l)
    obtain ⟨h3, h4⟩ := GlobalTheory.VolBr.NuMul.mul_mem_H_and_nu_mul k X p P _ _ _ _ _ _ h1 ih.1
    have ea : ((α l : ℕ) : ℤ) * e + (∑ l ∈ s, (α l : ℤ)) * e = (∑ l ∈ insert l s, (α l : ℤ)) * e := by
      rw [Finset.sum_insert hl]; ring
    have eb : ((α l : ℕ) : ℤ) * 0 + 0 = 0 := by ring
    rw [Finset.prod_insert hl]
    refine ⟨H_congr P ea eb h3, fun σ y => ?_⟩
    have h5 := h4 σ y
    rw [eb, ea] at h5
    rw [Finset.prod_insert hl, h5, h2 σ y, ih.2 σ y]

theorem xm_mem (P : Pair p) (e : ℤ) {D q : ℕ} (x : Fin (D + 1) → X.functionField) (hx : ∀ l, x l ∈ P.H e 0)
    (α : Fin (D + 1) →₀ ℕ) (hα : α.degree = q) :
    xm x α ∈ P.H (e * q) 0 ∧ ∀ σ y, P.nu (e * q) 0 σ y (xm x α) = ∏ l, P.nu e 0 σ y (x l) ^ α l := by
  have hq : (∑ l, (α l : ℤ)) * e = e * q := by
    subst hα; rw [mul_comm, Finsupp.degree_eq_sum]; push_cast; rfl
  obtain ⟨h1, h2⟩ := prod_pow_mem P e x hx α Finset.univ
  exact ⟨H_congr P hq rfl h1, fun σ y => by rw [← hq, xm, h2]⟩

theorem sum_zsmul (P : Pair p) (a b : ℤ) {J : Type} [Fintype J] (f : J → X.functionField) (hf : ∀ j, f j ∈ P.H a b)
    (n : J → ℤ) : (∑ j, n j • f j) ∈ P.H a b ∧ ∀ σ y,
      P.nu a b σ y (∑ j, n j • f j) ≤ ∑ j, |(n j : ℝ)| * P.nu a b σ y (f j) := by
  refine ⟨AddSubgroup.sum_mem _ fun j _ => AddSubgroup.zsmul_mem _ (hf j) _, fun σ y => ?_⟩
  obtain ⟨ℓ, hℓ⟩ := GlobalTheory.T.exists_additive_sectionValueUnitFrame k X p P a b σ y
  let F : P.H a b := ∑ j, n j • (⟨f j, hf j⟩ : P.H a b)
  have hF : (F : X.functionField) = ∑ j, n j • f j := by simp [F]
  rw [← hF, ← norm_val, ← hℓ, map_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [map_zsmul, zsmul_eq_mul, norm_mul, Complex.norm_intCast, hℓ, norm_val]

theorem count_rank_lower : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → ∀ (e : ℕ) (x : Fin (D + 1) → X.functionField), Gens P D e x → ∀ a b : ℤ, ∃ (c : ℕ) (C : ℝ), 0 < C ∧ ∀ q : ℕ, (∃ v : Fin (Module.finrank (ratF x) X.functionField * (q + D).choose D) → X.functionField, (∀ i, v i ∈ P.H (e * (q + c : ℕ) + a) b) ∧ LinearIndependent ℤ v) ∧ ∀ R : ℝ, 0 ≤ R → (∀ l (σ : k →+* ℂ) (y : CxPts p σ), P.nu e 0 σ y (x l) ≤ 1) → (((2 * ⌊R⌋₊ + 1) ^ (Module.finrank (ratF x) X.functionField * (q + D).choose D) : ℕ) : ℕ∞) ≤ (P.Bl (e * (q + c : ℕ) + a) b (C * (q + D).choose D * R)).encard := by
  intro k _ X _ p D hX P hA e x hx a b
  haveI : CharZero X.functionField := (GlobalTheory.T.projArith_functionField_charZero_trdeg k X p D hX).1
  obtain ⟨hx0, halg, hfin⟩ := GlobalTheory.T.sectionQuotients_transcendenceBasis_basepointFree k X p D hX P hA e x hx
  set δ := Module.finrank (ratF x) X.functionField with hδ
  obtain ⟨c, g, hg, hgi⟩ : ∃ (c : ℕ) (g : Fin δ → X.functionField), (∀ i, g i ∈ P.H (e * c + a) b) ∧
      LinearIndependent (ratF x) g := GlobalTheory.T.exists_functionField_basis_of_sections k X p D hX P hA e x hx a b
  have hbd : ∀ i, ∃ M : ℝ, ∀ σ y, P.nu (e * c + a) b σ y (g i) ≤ M := fun i =>
    ((GlobalTheory.T.continuous_hermSectionValue_mul_conj_and_norm_bounded k X p D hX P _ b).2 (g i) (hg i)).2
  choose M hM using hbd
  set M' : ℝ := 1 + ∑ i, |M i| with hM'
  have hM'0 : 0 ≤ M' := by positivity
  have hgM : ∀ i σ y, P.nu (e * c + a) b σ y (g i) ≤ M' := fun i σ y => by
    have := Finset.single_le_sum (f := fun i => |M i|) (fun i _ => abs_nonneg (M i)) (Finset.mem_univ i)
    have := le_abs_self (M i)
    have := hM i σ y
    simp only [hM'] at *
    linarith
  refine ⟨c, ((δ : ℝ) + 1) * M', by positivity, fun q => ?_⟩
  let w : Fin δ × Deg D q → X.functionField := fun ia => xm x ia.2.1 * g ia.1
  have hidx : (e : ℤ) * q + (e * c + a) = e * ((q + c : ℕ) : ℤ) + a := by push_cast; ring
  have hw : ∀ ia, w ia ∈ P.H (e * ((q + c : ℕ) : ℤ) + a) b ∧ ∀ σ y,
      P.nu (e * ((q + c : ℕ) : ℤ) + a) b σ y (w ia) =
        (∏ l, P.nu e 0 σ y (x l) ^ ia.2.1 l) * P.nu (e * c + a) b σ y (g ia.1) := by
    intro ia
    obtain ⟨h1, h2⟩ := xm_mem P e x hx.mem ia.2.1 ia.2.2
    obtain ⟨h3, h4⟩ := GlobalTheory.VolBr.NuMul.mul_mem_H_and_nu_mul k X p P _ _ _ _ _ _ h1 (hg ia.1)
    have h0b : (0 : ℤ) + b = b := zero_add b
    refine ⟨H_congr P hidx h0b h3, fun σ y => ?_⟩
    have h5 := h4 σ y
    rw [hidx, h0b] at h5
    rw [h5, h2 σ y]
  constructor
  · have hcard : δ * (q + D).choose D = Nat.card (Fin δ × Deg D q) := by
      rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Deg D q), card_deg, Nat.card_eq_fintype_card, Fintype.card_fin]
    let E : Fin (δ * (q + D).choose D) ≃ Fin δ × Deg D q := (finCongr hcard).trans (Finite.equivFin _).symm
    refine ⟨w ∘ E, fun i => (hw (E i)).1, (linearIndependent_equiv E).2 ?_⟩
    rw [Fintype.linearIndependent_iff]
    intro n hn ia
    let T : Fin δ → MvPolynomial (Fin (D + 1)) ℤ := fun i => ∑ α : Deg D q, monomial α.1 (n (i, α))
    have hT : ∀ i, (T i).IsHomogeneous q := fun i =>
      IsHomogeneous.sum _ _ _ fun α _ => isHomogeneous_monomial _ α.2
    have hTe : ∀ i, aeval x (T i) = ∑ α : Deg D q, n (i, α) • xm x α.1 := fun i => by
      simp only [T, map_sum, aeval_monomial, Finsupp.prod_pow, algebraMap_int_eq, eq_intCast, zsmul_eq_mul, xm]
    have h0 := GlobalTheory.T.homogeneousFormCombination_eq_zero_independent X.functionField D x hx0 halg hfin (Fin δ) g hgi q T hT (by
      rw [← hn, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hTe, Finset.sum_mul]
      refine Finset.sum_congr rfl fun α _ => ?_
      simp only [w, smul_mul_assoc])
    have h1 := congrArg (coeff ia.2.1) (congrFun h0 ia.1)
    simp only [T, coeff_sum, coeff_monomial, Pi.zero_apply, coeff_zero] at h1
    have h2 : ∀ α : Deg D q, (if (α : Fin (D + 1) →₀ ℕ) = ia.2.1 then n (ia.1, α) else 0) =
        if α = ia.2 then n (ia.1, α) else 0 := fun α => by simp only [Subtype.coe_inj]
    rw [Finset.sum_congr rfl fun α _ => h2 α] at h1
    simpa using h1
  · intro R hR hxl
    obtain ⟨hfinS, hcnt, -, -, -⟩ := GlobalTheory.T.card_bounded_homogeneous_int_form_families D q δ R hR
    let Φ : (Fin δ → MvPolynomial (Fin (D + 1)) ℤ) → X.functionField := fun T => ∑ i, aeval x (T i) * g i
    have hΦ : ∀ T : Fin δ → MvPolynomial (Fin (D + 1)) ℤ, (∀ i, (T i).IsHomogeneous q) →
        Φ T = ∑ ia : Fin δ × Deg D q, coeff ia.2.1 (T ia.1) • w ia := by
      intro T hT
      simp only [Φ, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [aeval_eq_sum x (T i) (hT i), Finset.sum_mul]
      refine Finset.sum_congr rfl fun α _ => ?_
      simp only [w, smul_mul_assoc]
    have hinj : Set.InjOn Φ {T : Fin δ → MvPolynomial (Fin (D + 1)) ℤ | (∀ i, (T i).IsHomogeneous q) ∧
        ∀ i α, |((coeff α (T i) : ℤ) : ℝ)| ≤ R} := by
      intro T hT T' hT' h
      have := GlobalTheory.T.homogeneousFormCombination_eq_zero_independent X.functionField D x hx0 halg hfin (Fin δ) g hgi q (T - T')
        (fun i => (hT.1 i).sub (hT'.1 i)) (by
          simp only [Pi.sub_apply, map_sub, sub_mul, Finset.sum_sub_distrib]
          exact sub_eq_zero.2 h)
      exact sub_eq_zero.1 this
    have hmaps : Set.MapsTo Φ {T : Fin δ → MvPolynomial (Fin (D + 1)) ℤ | (∀ i, (T i).IsHomogeneous q) ∧
        ∀ i α, |((coeff α (T i) : ℤ) : ℝ)| ≤ R}
        (P.Bl (e * (q + c : ℕ) + a) b (((δ : ℝ) + 1) * M' * (q + D).choose D * R)) := by
      intro T hT
      rw [Set.mem_setOf_eq] at hT
      rw [hΦ T hT.1]
      obtain ⟨h1, h2⟩ := sum_zsmul P _ b w (fun ia => (hw ia).1) (fun ia => coeff ia.2.1 (T ia.1))
      refine ⟨h1, fun σ y => (h2 σ y).trans ?_⟩
      have hterm : ∀ ia : Fin δ × Deg D q,
          |((coeff ia.2.1 (T ia.1) : ℤ) : ℝ)| * P.nu (e * ((q + c : ℕ) : ℤ) + a) b σ y (w ia) ≤ R * M' := by
        intro ia
        rw [(hw ia).2 σ y]
        have hp : ∏ l, P.nu e 0 σ y (x l) ^ ia.2.1 l ≤ 1 :=
          Finset.prod_le_one (fun l _ => pow_nonneg (nu_nonneg _ _ _ _ _ _) _)
            (fun l _ => pow_le_one₀ (nu_nonneg _ _ _ _ _ _) (hxl l σ y))
        refine mul_le_mul (hT.2 _ _) ?_
          (mul_nonneg (Finset.prod_nonneg fun l _ => pow_nonneg (nu_nonneg _ _ _ _ _ _) _) (nu_nonneg _ _ _ _ _ _)) hR
        calc _ ≤ 1 * M' := mul_le_mul hp (hgM _ σ y) (nu_nonneg _ _ _ _ _ _) zero_le_one
          _ = M' := one_mul _
      refine (Finset.sum_le_sum fun ia _ => hterm ia).trans ?_
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, card_deg, nsmul_eq_mul,
        Nat.cast_mul]
      have h0 : 0 ≤ ((q + D).choose D : ℝ) * R * M' := by positivity
      have key : ((δ : ℝ) + 1) * M' * ((q + D).choose D : ℝ) * R =
          (δ : ℝ) * ((q + D).choose D : ℝ) * (R * M') + ((q + D).choose D : ℝ) * R * M' := by ring
      rw [key]
      linarith
    rw [← hcnt, hfinS.cast_ncard_eq, ← hinj.encard_image]
    exact Set.encard_le_encard hmaps.image_subset

end GlobalTheory.HSAmp.FLower
