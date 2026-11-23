import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BaseIdealIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.ProjectiveNotIsUnit
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveAlgebraisationFormalCompleteLoca
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeQuotientClosedImmersionIdealSheafStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

noncomputable section
namespace GlobalTheory.FormalAlg.PolyLoc

open MvPolynomial

theorem exists_homogeneous_coeff_mem {σ R : Type} [CommRing R] (J : Ideal R) (i : σ) (g : MvPolynomial σ R)
    (hg : ∀ m, coeff m g ∈ J) : ∃ e : ℕ, ∀ d, e ≤ d → ∃ G : MvPolynomial σ R, G.IsHomogeneous d ∧
      (∀ m, coeff m G ∈ J) ∧ (X i - 1 : MvPolynomial σ R) ∣ G - g := by
  let Q : MvPolynomial σ R → Prop := fun p => ∃ e : ℕ, ∀ d, e ≤ d → ∃ G : MvPolynomial σ R, G.IsHomogeneous d ∧
      (∀ m, coeff m G ∈ J) ∧ (X i - 1 : MvPolynomial σ R) ∣ G - p
  have h0 : Q 0 := ⟨0, fun d _ => ⟨0, isHomogeneous_zero _ _ _, fun m => by rw [coeff_zero]; exact J.zero_mem,
    by rw [sub_zero]; exact dvd_zero _⟩⟩
  have hadd : ∀ p q, Q p → Q q → Q (p + q) := by
    rintro p q ⟨e, he⟩ ⟨e', he'⟩
    refine ⟨max e e', fun d hd => ?_⟩
    obtain ⟨G, hG, hGJ, hGd⟩ := he d (le_of_max_le_left hd)
    obtain ⟨G', hG', hGJ', hGd'⟩ := he' d (le_of_max_le_right hd)
    refine ⟨G + G', hG.add hG', fun m => by rw [coeff_add]; exact J.add_mem (hGJ m) (hGJ' m), ?_⟩
    rw [add_sub_add_comm]
    exact hGd.add hGd'
  have hmon : ∀ v (c : R), c ∈ J → Q (monomial v c) := by
    intro v c hc
    refine ⟨v.degree, fun d hd => ⟨monomial v c * X i ^ (d - v.degree), ?_, fun m => ?_, ?_⟩⟩
    · have := (isHomogeneous_monomial (R := R) c (rfl : v.degree = v.degree)).mul (isHomogeneous_X_pow i (d - v.degree))
      rwa [Nat.add_sub_cancel' hd] at this
    · classical
      rw [X_pow_eq_monomial, monomial_mul, coeff_monomial, _root_.mul_one]
      split_ifs
      · exact hc
      · exact J.zero_mem
    · rw [← mul_sub_one]
      exact (sub_one_dvd_pow_sub_one _ _).mul_left _
  rw [g.as_sum]
  exact Finset.sum_induction _ Q hadd h0 fun v _ => hmon v _ (hg v)

theorem exists_X_pow_mul_mem_vanIdeal {X : Scheme.{0}} {R : Type} [CommRing R] (f : X ⟶ Spec (CommRingCat.of R))
    {H : LB X} {m : ℕ} {s : Fin (m + 1) → LB.Sec H} (hc : ⨆ j, nonzeroLocus (s j) = ⊤)
    (ha : ∀ j, IsAffineOpen (nonzeroLocus (s j))) (r : ∀ j, Fin (m + 1) → Γ(X, nonzeroLocus (s j)))
    (hr : ∀ j, IsRatioFamily s j (r j)) (i : Fin (m + 1)) {Q : MvPolynomial (Fin (m + 1)) R} {e : ℕ}
    (hQ : Q.IsHomogeneous e) (h0 : eval₂Hom (cst f _) (r i) Q = 0) :
    ∃ c : ℕ, MvPolynomial.X i ^ c * Q ∈ vanIdeal f s := by
  have hn : ∀ j, ∃ n, r j i ^ n * eval₂Hom (cst f _) (r j) Q = 0 := fun j => by
    refine exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isAffineOpen X (ha j) _ _ (fn_ext fun y hy => ?_)
    have hj : y ∈ nonzeroLocus (s j) := X.basicOpen_le _ hy
    obtain ⟨k, hk⟩ := exists_chart_of_mem_nonzeroLocus hj
    have uj := (mem_nonzeroLocus_iff_isUnit _ hk).1 hj
    have hi : y ∈ nonzeroLocus (s i) := by
      rw [mem_nonzeroLocus_iff_isUnit _ hk, (hr j).gs_eq hj hk i]
      exact ((LBGerm.isUnit_gs_iff (𝟙 X) y _ hj _).2 hy).mul uj
    have e₁ := ((hr j).gs_form f hj hk hQ).symm.trans ((hr i).gs_form f hi hk hQ)
    rw [h0, LBGerm.gs_zero _ y _ hi, mul_zero] at e₁
    rw [LBGerm.gs_zero _ y _ hy]
    exact (gs_res _ y (X.basicOpen_le _) hy _).trans ((uj.pow e).mul_right_eq_zero.1 e₁)
  choose n hn using hn
  refine ⟨Finset.univ.sup n, (mem_vanIdeal _ _ _).2 ?_⟩
  refine (mem_vanishingForms_of_ratios f hc r hr ((isHomogeneous_X_pow i _).mul hQ) fun j => ?_).2
  have hle : n j ≤ Finset.univ.sup n := Finset.le_sup (Finset.mem_univ j)
  obtain ⟨b, hb⟩ := Nat.exists_eq_add_of_le' hle
  rw [hb, map_mul, map_pow, eval₂Hom_X', pow_add, _root_.mul_assoc, hn j, mul_zero]

theorem app_eval_eq_zero {R : Type} [CommRing R] {X X' : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R))
    (β : X' ⟶ X) {H : LB X} {H' : LB X'} {w : LB.Iso H' (H.pull β)} {m : ℕ} {s : Fin (m + 1) → LB.Sec H}
    {s' : Fin (m + 1) → LB.Sec H'} (hH : H.IsLB) (hH' : H'.IsLB) (hrel : ∀ j, Rel β w (s j) (s' j))
    (i : Fin (m + 1)) (r : Fin (m + 1) → Γ(X, nonzeroLocus (s i))) (hr : IsRatioFamily s i r)
    {F : MvPolynomial (Fin (m + 1)) R} {t : ℕ} (hF : F.IsHomogeneous t) (h0 : F ∈ vanIdeal (β ≫ f) s') :
    (β.app (nonzeroLocus (s i))).hom (eval₂Hom (cst f _) r F) = 0 := by
  refine fn_ext fun z hz => ?_
  rw [gs_pull (𝟙 X') β z _ hz, Category.id_comp, LBGerm.gs_zero _ z _ hz]
  obtain ⟨k, hk⟩ := exists_chart hH (β z)
  obtain ⟨k', hk'⟩ := exists_chart hH' z
  have e₁ := Rel.form hrel f hF z k k' hk hk'
  rw [(mem_vanIdeal _ _ _).1 h0 k', LBGerm.gs_zero _ z _ hk', mul_zero] at e₁
  have e₂ := congrArg (β.stalkMap z).hom (hr.gs_form f hz hk hF)
  rw [map_mul, map_pow, gs_stalkMap_comp β (𝟙 X) z _ hk, gs_stalkMap_comp β (𝟙 X) z _ hk,
    gs_stalkMap_comp β (𝟙 X) z _ hz] at e₂
  simp only [Category.comp_id] at e₂
  rw [e₁] at e₂
  have u := (mem_nonzeroLocus_iff_pull (s i) β z hk).1 hz
  exact ((u.pow t).mul_right_eq_zero.1 e₂.symm)

end GlobalTheory.FormalAlg.PolyLoc

open GlobalTheory.FormalAlg.PolyLoc MvPolynomial in

theorem GlobalTheory.FormalAlg.exists_X_pow_mul_sub_mem_vanIdeal : ∀ (R : Type) [CommRing R] (J : Ideal R) (X X' : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (β : X' ⟶ X) (q : X' ⟶ Spec (CommRingCat.of (R ⧸ J))), IsPullback β q f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) → ∀ (H : LB X) (H' : LB X') (w : LB.Iso H' (H.pull β)) (n : ℕ) (s : Fin (n + 1) → LB.Sec H) (s' : Fin (n + 1) → LB.Sec H'), H.IsLB → H'.IsLB → w.IsGen → (∀ j, Rel β w (s j) (s' j)) → VeryAmpleBy f H s → ∀ (t : ℕ) (F : MvPolynomial (Fin (n + 1)) R), F.IsHomogeneous t → F ∈ vanIdeal (β ≫ f) s' → ∀ i, ∃ (N : ℕ) (G : MvPolynomial (Fin (n + 1)) R), G.IsHomogeneous (t + N) ∧ (∀ m, MvPolynomial.coeff m G ∈ J) ∧ MvPolynomial.X i ^ N * F - G ∈ vanIdeal f s := by
  intro R _ J X X' f β q hpb H H' w n s s' hH hH' _ hrel hva t F hF h0 i
  obtain ⟨hc, hva⟩ := hva
  choose ha r hr hsur using hva
  have hR : ∀ j, IsRatioFamily s j (r j) := hr
  set φ := eval₂Hom (AbLaw.cst f (nonzeroLocus (s i))) (r i) with hφ
  have hker := ((GlobalTheory.T.baseChange_quotient_closedImmersion_idealSheaf R J X X' f β q hpb).2.2 _ (ha i)).2
  have hβ : (β.app (nonzeroLocus (s i))).hom (φ F) = 0 := app_eval_eq_zero f β hH hH' hrel i (r i) (hR i) hF h0
  have hJ : φ F ∈ (Ideal.map (C : R →+* MvPolynomial (Fin (n + 1)) R) J).map φ := by
    have h2 : φ F ∈ J.map (AbLaw.cst f (nonzeroLocus (s i))) := hker ▸ (RingHom.mem_ker.2 hβ)
    have h3 : AbLaw.cst f (nonzeroLocus (s i)) = φ.comp C := by
      ext a
      simp [hφ]
    rwa [h3, ← Ideal.map_map] at h2
  obtain ⟨g, hg, hgF⟩ := (Ideal.mem_map_iff_of_surjective φ (hsur i)).1 hJ
  rw [MvPolynomial.mem_map_C_iff] at hg
  obtain ⟨e, he⟩ := exists_homogeneous_coeff_mem J i g hg
  obtain ⟨G₁, hG₁, hG₁J, hdvd⟩ := he (t + e) (Nat.le_add_left e t)
  have hQ : (MvPolynomial.X i ^ e * F - G₁).IsHomogeneous (t + e) := by
    have := (isHomogeneous_X_pow i e).mul hF
    rw [Nat.add_comm e t] at this
    exact this.sub hG₁
  have hφQ : φ (MvPolynomial.X i ^ e * F - G₁) = 0 := by
    obtain ⟨P, hP⟩ := hdvd
    have hx : φ (MvPolynomial.X i) = 1 := by rw [hφ, eval₂Hom_X']; exact (hR i).self_eq_one
    have hG : G₁ = g + (MvPolynomial.X i - 1) * P := by rw [← hP]; ring
    rw [hG, map_sub, map_mul, map_pow, hx, one_pow, _root_.one_mul, map_add, map_mul, map_sub, hx, map_one, sub_self,
      zero_mul, add_zero, hgF, sub_self]
  obtain ⟨c, hc'⟩ := exists_X_pow_mul_mem_vanIdeal f hc ha r hR i hQ hφQ
  refine ⟨c + e, MvPolynomial.X i ^ c * G₁, ?_, fun m => ?_, ?_⟩
  · have := (isHomogeneous_X_pow i c).mul hG₁
    convert this using 1
    ring
  · have h4 : MvPolynomial.X i ^ c * G₁ ∈ Ideal.map (C : R →+* MvPolynomial (Fin (n + 1)) R) J :=
      Ideal.mul_mem_left _ _ (mem_map_C_iff.2 hG₁J)
    exact mem_map_C_iff.1 h4 m
  · convert hc' using 1
    ring
