import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RootToFlag
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagRelativeTangentTopChernNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSpanOfChernClassesOfRootsEqZeroStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomogeneousComponentChernClassesOfRootsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagRelativeTangentTopChernIsHomogeneousCmTypeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHomogeneousOfMulIsHomogeneousOfNeZeroRightStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GrassmannProductIntegralEqFlagDegreeWeightStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GrassmannProductIntegralEqZeroOfMemRelIdealStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GrassmannProductIntegralPointClassEqOneStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GrassmannProductTopDegreeEqSmulPointClassStatement

namespace GlobalTheory.GrassTop
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical

theorem add_mul_pred_div_two : ∀ (a b : ℕ), (a + b) * (a + b - 1) / 2 = a * (a - 1) / 2 + b * (b - 1) / 2 + a * b := by
  have g : ∀ n : ℕ, (n + 1) * (n + 1 - 1) / 2 = n * (n - 1) / 2 + n := by
    intro n
    rw [Nat.add_sub_cancel]
    cases n with
    | zero => simp
    | succ k =>
      rw [Nat.add_sub_cancel, show (k + 1 + 1) * (k + 1) = (k + 1) * k + 2 * (k + 1) by ring,
        Nat.add_mul_div_left _ _ (by norm_num)]
  intro a b
  induction b with
  | zero => simp
  | succ b ih =>
    rw [← add_assoc, g (a + b), g b, ih]; ring

theorem pointPoly_isWeightedHomogeneous : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), IsWeightedHomogeneous Prod.snd (pointPoly H Dw) (Fintype.card (GlobalTheory.AllWt.Psi H) * (Dw.p * Dw.q)) := by
  intro E _ _ _ H Dw
  unfold pointPoly
  have hs : Fintype.card (GlobalTheory.AllWt.Psi H) * (Dw.p * Dw.q) = ∑ τ : GlobalTheory.AllWt.Psi H, Dw.p * Dw.q := by simp
  rw [hs]
  apply IsWeightedHomogeneous.prod
  intro τ _
  have hm : Dw.mult τ.1 = Dw.p := by simp [Datum.mult, τ.2]
  rw [hm, show Dw.p + Dw.q - Dw.p = Dw.q by omega]
  have h1 : IsWeightedHomogeneous (Prod.snd : (E →+* ℂ) × ℕ → ℕ)
      (C ((-1 : ℝ) ^ Dw.p) * X (τ.1, Dw.p) : MvPolynomial ((E →+* ℂ) × ℕ) ℝ) Dw.p := by
    simpa using (isWeightedHomogeneous_C (Prod.snd : (E →+* ℂ) × ℕ → ℕ) ((-1 : ℝ) ^ Dw.p)).mul
      (isWeightedHomogeneous_X ℝ (Prod.snd : (E →+* ℂ) × ℕ → ℕ) (τ.1, Dw.p))
  simpa [mul_comm] using h1.pow Dw.q

theorem antisymm_isHomogeneous : ∀ {ι : Type} [Fintype ι] {m : ι → ℕ} (P : MvPolynomial (Root m) ℝ) (d : ℕ), P.IsHomogeneous d → (antisymm P).IsHomogeneous d := by
  intro ι _ m P d h
  unfold GlobalTheory.GoodMetric.antisymm
  apply IsHomogeneous.sum
  intro w _
  have h1 := h.rename_isHomogeneous (f := fun x : Root m => (⟨x.fst, (w x.fst) x.snd⟩ : Root m))
  have h2 := (mem_homogeneousSubmodule _ _).mpr h1
  exact (mem_homogeneousSubmodule _ _).mp (Submodule.smul_of_tower_mem _ _ h2)

theorem intGr_sub {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (A B : MvPolynomial ((E →+* ℂ) × ℕ) ℝ) : intGr H Dw (A - B) = intGr H Dw A - intGr H Dw B := by
  unfold intGr Formalism.DegreeFormula.degFl
  simp only [map_sub, sub_mul, coeff_sub, mul_sub, Finset.sum_sub_distrib, sub_div]

theorem intGr_C_mul {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (c : ℝ) (A : MvPolynomial ((E →+* ℂ) × ℕ) ℝ) : intGr H Dw (C c * A) = c * intGr H Dw A := by
  unfold intGr Formalism.DegreeFormula.degFl
  have hc : rho H Dw (C c) = C c := by
    simpa [MvPolynomial.algebraMap_eq] using (rho H Dw).commutes c
  have hc0 : chernRoots Dw.mult (C c) = C c := by
    simpa [MvPolynomial.algebraMap_eq] using (chernRoots Dw.mult).commutes c
  simp only [map_mul, hc0, hc, mul_assoc, coeff_C_mul]
  rw [mul_div_assoc']
  congr 1
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => by ring

theorem intGr_of_chernRoots_eq_zero {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E)
    (Dw : Datum H) (A : MvPolynomial ((E →+* ℂ) × ℕ) ℝ) (h : chernRoots Dw.mult A = 0) :
    intGr H Dw A = 0 := by
  unfold intGr Formalism.DegreeFormula.degFl
  simp [h]

theorem grass_top : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (la : GlobalTheory.AllWt.Weight Dw) (R : MvPolynomial ((E →+* ℂ) × ℕ) ℝ) (n D : ℕ) (L : MvPolynomial ((E →+* ℂ) × ℕ) ℝ →ₗ[ℝ] ℝ), D = Fintype.card (GlobalTheory.AllWt.Psi H) * ((Dw.p + Dw.q) * (Dw.p + Dw.q - 1) / 2) → antisymm ((∑ x : Root Dw.mult, MvPolynomial.C (-(GlobalTheory.AllWt.exOf Dw la 0 (some x) : ℝ)) * MvPolynomial.X x) ^ D) = chernRoots Dw.mult R * rootDiscr Dw.mult → (∀ (Q : MvPolynomial ((E →+* ℂ) × ℕ) ℝ) (d : ℕ), MvPolynomial.IsWeightedHomogeneous (Prod.snd : (E →+* ℂ) × ℕ → ℕ) Q d → d ≠ n → L Q = 0) → (∀ (τ : E →+* ℂ) (Q : MvPolynomial ((E →+* ℂ) × ℕ) ℝ), L ((MvPolynomial.X (τ, 0) - 1) * Q) = 0) → (∀ (τ : E →+* ℂ) (k : ℕ) (Q : MvPolynomial ((E →+* ℂ) × ℕ) ℝ), Dw.mult τ < k → L (MvPolynomial.X (τ, k) * Q) = 0) → (∀ (τ : GlobalTheory.AllWt.Psi H) (k : ℕ) (Q : MvPolynomial ((E →+* ℂ) × ℕ) ℝ), 1 ≤ k → L ((∑ a ∈ Finset.range (k + 1), MvPolynomial.C ((-1 : ℝ) ^ (k - a)) * MvPolynomial.X (τ.1, a) * MvPolynomial.X (conjEmb τ.1, k - a)) * Q) = 0) → L R = Formalism.DegreeFormula.flagDeg (GlobalTheory.AllWt.Psi H) (Dw.p + Dw.q) (fun τ i => (la τ i : ℝ)) * L (pointPoly H Dw) := by
  intro E _ _ _ H Dw la R n D L hD hR hdeg hJ0 hJk hrel

  have hL : ∀ Q ∈ relIdeal H Dw, L Q = 0 := by
    intro Q hQ
    have key : ∀ a, L (Q * a) = 0 := by
      refine Submodule.span_induction (p := fun x _ => ∀ a, L (x * a) = 0) ?_ ?_ ?_ ?_ hQ
      · rintro x ((⟨τ, rfl⟩ | ⟨τ, k, hk, rfl⟩) | ⟨τ, k, hk, rfl⟩) a
        · exact hJ0 τ a
        · exact hJk τ k a hk
        · exact hrel τ k a hk
      · intro a; simp
      · intro x y _ _ hx hy a; rw [add_mul, map_add, hx, hy, add_zero]
      · intro b x _ hx a; rw [smul_eq_mul, mul_comm b x, mul_assoc]; exact hx _
    simpa using key 1
  have hker : ∀ Q, chernRoots Dw.mult Q = 0 → L Q = 0 := by
    intro Q hQ
    apply hL
    refine Ideal.span_mono ?_ (GlobalTheory.T.mem_span_of_chernClassesOfRoots_eq_zero Dw.mult Q hQ)
    exact Set.subset_union_left
  set e := Fintype.card (GlobalTheory.AllWt.Psi H) * (Dw.p * Dw.q) with he
  set δ := Fintype.card (GlobalTheory.AllWt.Psi H) * (Dw.p * (Dw.p - 1) / 2 + Dw.q * (Dw.q - 1) / 2) with hδ

  have hRh : (chernRoots Dw.mult R).IsHomogeneous e := by
    refine GlobalTheory.T.isHomogeneous_of_mul_isHomogeneous_of_ne_zero_right _ _ e δ (by apply GlobalTheory.GoodMetric.rootDiscr_ne_zero) (GlobalTheory.T.flagRelativeTangentTopChern_isHomogeneous_cmType H Dw) ?_
    rw [← hR]
    have hed : e + δ = D := by
      rw [hD, he, hδ, add_mul_pred_div_two]; ring
    rw [hed]
    apply antisymm_isHomogeneous
    have hlin : (∑ x : Root Dw.mult, MvPolynomial.C (-(GlobalTheory.AllWt.exOf Dw la 0 (some x) : ℝ)) *
        MvPolynomial.X x).IsHomogeneous 1 :=
      IsHomogeneous.sum _ _ _ fun x _ => isHomogeneous_C_mul_X _ _
    simpa using hlin.pow D
  set Re := weightedHomogeneousComponent (Prod.snd : (E →+* ℂ) × ℕ → ℕ) e R with hRe
  have hReW : IsWeightedHomogeneous (Prod.snd : (E →+* ℂ) × ℕ → ℕ) Re e :=
    weightedHomogeneousComponent_isWeightedHomogeneous _ _
  have hrest : chernRoots Dw.mult (R - Re) = 0 := by
    have hc : ∀ d, homogeneousComponent d (chernRoots Dw.mult (R - Re)) = 0 := by
      intro d
      rw [GlobalTheory.T.homogeneousComponent_chernClassesOfRoots, map_sub]
      by_cases hd : d = e
      · rw [hd, hReW.weightedHomogeneousComponent_same]
        simp [hRe]
      · rw [map_sub, ← GlobalTheory.T.homogeneousComponent_chernClassesOfRoots, homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).mpr hRh), if_neg hd,
          weightedHomogeneousComponent_of_mem ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr hReW), if_neg hd,
          map_zero, sub_zero]
    rw [← sum_homogeneousComponent (chernRoots Dw.mult (R - Re))]
    exact Finset.sum_eq_zero fun d _ => hc d
  have hLR : L R = L Re := by
    have := hker _ hrest
    rw [map_sub, sub_eq_zero] at this
    exact this
  have hIR : intGr H Dw R = intGr H Dw Re := by
    have := intGr_of_chernRoots_eq_zero H Dw _ hrest
    rw [intGr_sub, sub_eq_zero] at this
    exact this
  by_cases hn : n = e
  · obtain ⟨c, hc⟩ := GlobalTheory.T.grassmannProduct_topDegree_eq_smul_pointClass H Dw Re hReW
    have h1 := hL _ hc
    rw [map_sub, sub_eq_zero, C_mul', map_smul, smul_eq_mul] at h1
    have h2 := GlobalTheory.T.grassmannProductIntegral_eq_zero_of_mem_relIdeal H Dw _ hc
    rw [intGr_sub, intGr_C_mul, GlobalTheory.T.grassmannProductIntegral_pointClass_eq_one, mul_one, sub_eq_zero] at h2
    rw [hLR, h1, ← h2, ← hIR, GlobalTheory.T.grassmannProductIntegral_eq_flagDegree_weight H Dw la R D hD hR]
  · have h1 : L Re = 0 := hdeg Re e hReW (Ne.symm hn)
    have h2 : L (pointPoly H Dw) = 0 := hdeg _ e (pointPoly_isWeightedHomogeneous H Dw) (Ne.symm hn)
    rw [hLR, h1, h2, mul_zero]

end GlobalTheory.GrassTop
