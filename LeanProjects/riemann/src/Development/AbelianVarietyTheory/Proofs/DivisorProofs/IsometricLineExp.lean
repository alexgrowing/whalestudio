import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfSwap2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OddHarmZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SwapSumSwap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwoEmbeddingsOfTranscendental
import Development.AbelianVarietyTheory.Definitions.Divisors.GenericPointAsIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GradedMetricPullbackIsometric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankTwoGradedDeterminantIsometric
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.BlockPoint
open GlobalTheory.Cartier GlobalTheory.CovTest.SwapLine
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BlockPoint.OddTerm

open HermLB

section General

variable {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k} {ι κ : Type} [Fintype ι] [Fintype κ]

theorem isGeoFun_subst {L : ι → HermLB p} {D : ℕ} {Ψ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ} (hΨ : IsGeoFun L D Ψ)
    (M : κ → HermLB p) (T : κ → ι → ℤ) (hT : ∀ j, (comb L (T j)).Isometric (M j)) :
    IsGeoFun M D (Ψ ∘ₗ (aeval fun j => lin fun i => (T j i : ℝ) : MvPolynomial κ ℝ →ₐ[ℝ] MvPolynomial ι ℝ).toLinearMap) := by
  refine ⟨fun m => ?_, fun P e he hP => ?_⟩
  · rw [LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_pow, aeval_lin]
    have h2 := hΨ.1 (fun z => ∑ j, m j * T j z)
    simp only [Int.cast_sum, Int.cast_mul] at h2
    rw [h2]
    exact ((isometric_comb_comb L T m).trans (isometric_comb_congr hT m)).gdeg_eq _
  · exact hΨ.2 _ e he (by simpa using hP.aeval _ fun j => isHomogeneous_lin _)

variable (p) in

def cst (t : ℝ) : HermLB p := (triv p).shift (fun _ => t) fun _ => rfl

theorem icls_shift (L : HermLB p) (t : ℝ) :
    (L.shift (fun _ => t) fun _ => rfl).icls = L.icls + (cst p t).icls := by
  rw [← icls_tens, icls_eq_iff]
  refine Isometric.symm (isometric_of_chart (fun c => c.1) (fun _ _ h => h.1)
    (fun x c c' h h' => (CechPic.gm_tens L.B (LB.triv X) (𝟙 X) x c c' h h').trans
      ((congrArg (_ * ·) (map_one _)).trans (mul_one _))) fun σ a y _ => ?_)
  show (L.φ σ).φ a.1 y + 2 * t = (L.φ σ).φ a.1 y + ((0 : ℝ) + 2 * t)
  ring

theorem icls_cst_add (s t : ℝ) : (cst p (s + t)).icls = (cst p s).icls + (cst p t).icls := by
  rw [← icls_shift, icls_eq_iff]
  exact isometric_of_eqOn fun σ a y _ => by
    show ((0 : ℝ) + 2 * s) + 2 * t = (0 : ℝ) + 2 * (s + t)
    ring

theorem icls_cst_int (n : ℤ) : (cst p (n : ℝ)).icls = n • (cst p 1).icls := by
  have := map_zsmul (AddMonoidHom.mk' (fun t : ℝ => (cst p t).icls) icls_cst_add) n 1
  simpa using this

theorem pull_shift (L : HermLB p) (t : ℝ) (π : Y ⟶ X) (hπ : π ≫ p = q) :
    ((L.shift (fun _ => t) fun _ => rfl).pull π hπ).Isometric ((L.pull π hπ).shift (fun _ => t) fun _ => rfl) :=
  isometric_of_eqOn fun σ a y _ => by
    exact (congrArg (· + 2 * t) (Weight.pull_φ (L.φ σ) π hπ a y)).trans
      (Weight.pull_φ ((L.φ σ).addFn fun _ => 2 * t) π hπ a y).symm

theorem comb_shift {L L' : ι → HermLB p} (a : ι) (ha : (L' a).Isometric ((L a).shift (fun _ => 1) fun _ => rfl))
    (hne : ∀ i, i ≠ a → L' i = L i) (n : ι → ℤ) :
    (comb L' n).Isometric ((comb L n).shift (fun _ => (n a : ℝ)) fun _ => rfl) := by
  refine icls_eq_iff.1 ?_
  rw [icls_shift, icls_comb, icls_comb, icls_cst_int, ← Finset.add_sum_erase _ _ (Finset.mem_univ a),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ a), icls_eq_iff.2 ha, icls_shift,
    Finset.sum_congr rfl fun i hi => by rw [hne i (Finset.ne_of_mem_erase hi)], smul_add]
  abel

theorem chernInt_shift (L : HermLB p) (t : ℝ) (σ : k →+* ℂ) (D : ℕ) :
    ((L.shift (fun _ => t) fun _ => rfl).φ σ).chernInt D = (L.φ σ).chernInt D := by
  funext S f
  simp only [HermLB.shift, Weight.chernInt, Weight.chernPart_addFn_const]

theorem arFun_shift (hC : ArCalc) [IsIntegral X] {D : ℕ} (hX : IsArithVar p D) {L L' : ι → HermLB p} (a : ι)
    (hs : ∀ n : ι → ℤ, (comb L' n).Isometric ((comb L n).shift (fun _ => (n a : ℝ)) fun _ => rfl))
    {Φ Φ' Ψ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ} (hΦ : IsArFun L D Φ) (hΦ' : IsArFun L' D Φ') (hΨ : IsGeoFun L D Ψ)
    (G : MvPolynomial ι ℝ) : Φ' G = Φ G + Ψ (pderiv a G) := by
  have hz := GlobalTheory.ArInt.Model.eq_zero_of_pow (D + 1) (Φ' - Φ - Ψ ∘ₗ (pderiv a).toLinearMap) (fun n => by
      have h3 := hC.arShift k X p D hX (comb L n) _ (n a) (hΦ.1 n)
      have h4 := (hΦ'.1 n).unique hX ((hs n).symm.isSelfInter hX h3)
      have h5 : pderiv a (lin (fun i => (n i : ℝ)) ^ (D + 1)) =
          (((D : ℝ) + 1) * n a) • lin (fun i => (n i : ℝ)) ^ D := by
        have : pderiv a (lin (fun i => (n i : ℝ))) = C (n a : ℝ) := by
          simp [lin, pderiv_X, Pi.single_apply]
        rw [pderiv_pow, this, smul_eq_C_mul]
        simp only [Nat.add_sub_cancel, map_mul, map_add, map_natCast, map_one]
        push_cast
        ring
      simp only [LinearMap.sub_apply, LinearMap.comp_apply, Derivation.coeFn_coe]
      rw [h5, map_smul, hΨ.1 n, h4, smul_eq_mul]
      ring)
    (fun P e he hP => by
      simp only [LinearMap.sub_apply, LinearMap.comp_apply, Derivation.coeFn_coe]
      rw [hΦ.2 P e he hP, hΦ'.2 P e he hP]
      rcases Nat.eq_zero_or_pos e with rfl | h0
      · rw [totalDegree_eq_zero_iff_eq_C.1 (Nat.le_zero.1 hP.totalDegree_le), pderiv_C, map_zero]
        ring
      · rw [hΨ.2 _ (e - 1) (by omega) hP.pderiv]
        ring)
  have := LinearMap.congr_fun hz G
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, Derivation.coeFn_coe, LinearMap.zero_apply] at this
  linarith

end General

section Bundle

variable {k : Type} [CommRing k] {B Y : Scheme.{0}} [IsIntegral B] [IsIntegral Y] {q : B ⟶ Sp k} {p : Y ⟶ Sp k} {d : ℕ}

theorem dim_image_lt (hq : IsArithVar q d) (π : Y ⟶ B) :
    topologicalKrullDim (closure ({π (genericPoint Y)} : Set B)) < ((d + 1 + 1 : ℕ) : WithBot ℕ∞) := by
  refine (topologicalKrullDim_subspace_le B _).trans_lt ?_
  rw [hq.dim_eq]
  exact_mod_cast Nat.lt_succ_self (d + 1)

theorem gdeg_pull_zero (hC : ArCalc) (hq : IsArithVar q d) (hp : IsArithVar p (d + 1)) (π : Y ⟶ B) (w : π ≫ q = p)
    (L : HermLB q) : gdeg (L.pull π w) (d + 1) = 0 := by
  have h0 := GlobalTheory.ProjDrop.isSelfInter_zero_of_dim_lt hC k B Y q p d (d + 1) hq hp π w (dim_image_lt hq π)
  have h1 := hC.arShift k Y p (d + 1) hp _ _ 1 (h0 L)
  have h2 := ((pull_shift L 1 π w).isSelfInter hp (h0 _)).unique hp h1
  have h3 : (((d + 1 : ℕ) : ℝ) + 1) ≠ 0 := by positivity
  rw [zero_add, mul_one] at h2
  exact (mul_eq_zero.1 h2.symm).resolve_left h3

variable {π : Y ⟶ B} {w : π ≫ q = p} {E : B.Modules} {h : VMetric q E 2} {H : h.IsCInf} {flB : Vert.Flag E 2}
  {fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2} {A : HermLB q}

def baseExp : Fin 3 → Fin 5 → ℤ := fun j => Pi.single ((![3, 4, 2] : Fin 3 → Fin 5) j) 1

theorem aeval_baseExp (f : MvPolynomial (Fin 3) ℝ) :
    aeval (fun j => lin fun i => (baseExp j i : ℝ)) f = rename (![3, 4, 2] : Fin 3 → Fin 5) f := by
  simp only [baseExp, lin_single]
  rw [rename_eq_aeval]
  rfl

theorem isometric_baseExp (j : Fin 3) : (comb (fam5 π w H flB fl A) (baseExp j)).Isometric
    (((![VMetric.grLB flB 0 H, VMetric.grLB flB 1 H, A] : Fin 3 → HermLB q) j).pull π w) := by
  refine (isometric_comb_single _ _).trans ?_
  fin_cases j <;> exact Isometric.refl _

theorem arFun_base (hC : ArCalc) (hq : IsArithVar q d) (hp : IsArithVar p (d + 1))
    {Φ : MvPolynomial (Fin 5) ℝ →ₗ[ℝ] ℝ} (hΦ : IsArFun (fam5 π w H flB fl A) (d + 1) Φ) (f : MvPolynomial (Fin 3) ℝ) :
    Φ (rename (![3, 4, 2] : Fin 3 → Fin 5) f) = 0 := by
  have h1 := ((hC.arIso k Y p (d + 1) hp).2 (Fin 5) _ Φ hΦ).2.2 (Fin 3) _ baseExp isometric_baseExp
  have h2 : IsArFun (fun j => ((![VMetric.grLB flB 0 H, VMetric.grLB flB 1 H, A] : Fin 3 → HermLB q) j).pull π w)
      (d + 1) 0 := by
    refine ⟨fun n => ?_, fun _ _ _ _ => rfl⟩
    rw [LinearMap.zero_apply]
    exact (isometric_comb_pull _ n π w).symm.isSelfInter hp
      (GlobalTheory.ProjDrop.isSelfInter_zero_of_dim_lt hC k B Y q p d (d + 1) hq hp π w (dim_image_lt hq π) _)
  have := LinearMap.congr_fun (GlobalTheory.ArInt.Model.isArFun_unique hp h1 h2) f
  rwa [LinearMap.comp_apply, AlgHom.toLinearMap_apply, aeval_baseExp] at this

theorem geoFun_base (hC : ArCalc) (hq : IsArithVar q d) (hp : IsArithVar p (d + 1))
    {Ψ : MvPolynomial (Fin 5) ℝ →ₗ[ℝ] ℝ} (hΨ : IsGeoFun (fam5 π w H flB fl A) (d + 1) Ψ) (f : MvPolynomial (Fin 3) ℝ) :
    Ψ (rename (![3, 4, 2] : Fin 3 → Fin 5) f) = 0 := by
  have h1 := isGeoFun_subst hΨ _ baseExp isometric_baseExp
  have h2 : IsGeoFun (fun j => ((![VMetric.grLB flB 0 H, VMetric.grLB flB 1 H, A] : Fin 3 → HermLB q) j).pull π w)
      (d + 1) 0 := by
    refine ⟨fun n => ?_, fun _ _ _ _ => rfl⟩
    rw [LinearMap.zero_apply, (isometric_comb_pull _ n π w).gdeg_eq, gdeg_pull_zero hC hq hp]
  have := LinearMap.congr_fun (GlobalTheory.ArInt.Model.isGeoFun_unique h1 h2) f
  rwa [LinearMap.comp_apply, AlgHom.toLinearMap_apply, aeval_baseExp] at this

def lineExp : Fin 3 → Fin 5 → ℤ := ![![1, 0, 0, 0, 0], ![-1, 0, 0, 1, 1], ![0, 0, 1, 0, 0]]

theorem lin_lineExp : (fun j => lin fun i => (lineExp j i : ℝ)) =
    (![X 0, X 3 + X 4 - X 0, X 2] : Fin 3 → MvPolynomial (Fin 5) ℝ) := by
  funext j
  fin_cases j <;> simp [lineExp, lin, Fin.sum_univ_five] <;> ring

theorem isometric_lineExp (j : Fin 3) : (comb (fam5 π w H flB fl A) (lineExp j)).Isometric
    ((![VMetric.grLB fl 0 (H.pull π w), VMetric.grLB fl 1 (H.pull π w), A.pull π w] : Fin 3 → HermLB p) j) := by
  set L5 := fam5 π w H flB fl A with hL5
  have iso : ((L5 0).tens (L5 1)).Isometric ((L5 3).tens (L5 4)) := by
    have e₁ := VMetric.isometric_grLB_tens_grLB_det k Y p _ _ (H.pull π w) fl
    have e₂ := VMetric.isometric_det_pull H π w
    have e₃ := ((VMetric.isometric_grLB_tens_grLB_det k B q E h H flB).symm.pull π w).trans
      (HermLB.isometric_pull_tens _ _ π w)
    exact e₁.trans (e₂.trans e₃)
  have icl : (L5 1).icls = (L5 3).icls + (L5 4).icls - (L5 0).icls := by
    have := HermLB.icls_eq_iff.2 iso
    rw [HermLB.icls_tens, HermLB.icls_tens] at this
    rw [← this]
    abel
  refine HermLB.icls_eq_iff.1 ?_
  rw [icls_comb]
  fin_cases j
  · change _ = (L5 0).icls
    simp [lineExp, Fin.sum_univ_five]
  · change _ = (L5 1).icls
    rw [icl]
    simp [lineExp, Fin.sum_univ_five]
    abel
  · change _ = (L5 2).icls
    simp [lineExp, Fin.sum_univ_five]

end Bundle

end GlobalTheory.BlockPoint.OddTerm

end
