import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocFacOfNeg
import Development.AbelianVarietyTheory.Definitions.Divisors.MemMspan
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
import Development.AbelianVarietyTheory.Definitions.Divisors.UnrOutside
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LastRowSubSingleNotMemLatticeOfNegExponentStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LastRowDiagonalMulMemLatticeIffStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMirabolicWhittakerReductionCellStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdeleModuleDetDiagonalUniformiserMulStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SphericalLocalFactorNormSqStatement
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical

noncomputable section

namespace GlobalTheory.CellPw

variable {E : Type} [Field E] [NumberField E]

theorem rowInf_tl [IsTotallyComplex E] {n : ℕ} (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ)
    (l : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ)) (g : GA E n) (r : Fin n) :
    (fun i => pInf E ((GlobalTheory.CellDec.tl n ϖ l * g).val r i)) = fun i => pInf E (g.val r i) := by
  have h : GeneralLinearGroup.map (pInf E) (GlobalTheory.CellDec.tl n ϖ l * g) = GeneralLinearGroup.map (pInf E) g := by
    rw [map_mul, GlobalTheory.CellDec.tl, pInf_finGL, one_mul]
  funext i
  exact congrArg (fun M : GL (Fin n) (Cinf E) => M.val r i) h

theorem bInt_of_not_mem [IsTotallyComplex E] {a : ℕ} (ℓ : Fin a) (F : GA E a → ℂ) (Φ : (Fin a → Cinf E) → ℂ)
    (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E) (x : ℝ) (h : GA E a)
    (hm : (fun i => pFin E (h.val ℓ i)) - η ∉ GlobalTheory.ThetaPoisson.latt a J) :
    GlobalTheory.RSCell.bInt ℓ F Φ J η x h = 0 := by
  simp [GlobalTheory.RSCell.bInt, GlobalTheory.RSTheta.rsPsi, GlobalTheory.ThetaPoisson.thetaFn, Set.indicator_of_notMem hm]

theorem bInt_of_mem [IsTotallyComplex E] {a : ℕ} (ℓ : Fin a) (F : GA E a → ℂ) (Φ : (Fin a → Cinf E) → ℂ)
    (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E) (x : ℝ) (h : GA E a)
    (hm : (fun i => pFin E (h.val ℓ i)) - η ∈ GlobalTheory.ThetaPoisson.latt a J) :
    GlobalTheory.RSCell.bInt ℓ F Φ J η x h =
      ENNReal.ofReal (‖GlobalTheory.JSW.whit F (h * (infGL E a (GlobalTheory.RSTheta.rowGL ℓ (fun i => pInf E (h.val ℓ i))))⁻¹)‖ ^ 2 *
        ‖Φ (fun i => pInf E (h.val ℓ i))‖ * (ideleModule E (GeneralLinearGroup.det h) : ℝ) ^ x) := by
  rw [GlobalTheory.RSCell.bInt, GlobalTheory.RSTheta.rsPsi, GlobalTheory.ThetaPoisson.thetaFn, GlobalTheory.RSTheta.rsInf, Set.indicator_of_mem hm,
    ← ofReal_norm_eq_enorm, ← ENNReal.ofReal_mul (norm_nonneg _)]
  congr 1
  simp only [Pi.one_apply, mul_one, norm_mul, Complex.norm_conj]
  ring

theorem prod_supp_add {n : ℕ} (q : HeightOneSpectrum (𝓞 E) → ℝ) (hq : ∀ v, q v ≠ 0) (f : (Fin n → ℤ) →+ ℤ)
    (a b : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ)) :
    ∏ v ∈ (a + b).support, q v ^ f ((a + b) v) =
      (∏ v ∈ a.support, q v ^ f (a v)) * ∏ v ∈ b.support, q v ^ f (b v) := by
  have := Finsupp.prod_add_index' (f := a) (g := b) (h := fun v y => q v ^ f y) (fun v => by simp)
    (fun v y₁ y₂ => by simp [zpow_add₀ (hq v)])
  simpa [Finsupp.prod] using this

def wtSHom (n : ℕ) : (Fin n → ℤ) →+ ℤ where
  toFun := GlobalTheory.CellDec.wtS n
  map_zero' := by simp [GlobalTheory.CellDec.wtS]
  map_add' a b := by
    simp only [GlobalTheory.CellDec.wtS, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp <;> ring

def negSumHom (n : ℕ) : (Fin n → ℤ) →+ ℤ where
  toFun a := -∑ i, a i
  map_zero' := by simp
  map_add' a b := by simp [Finset.sum_add_distrib]; ring

omit [Field E] [NumberField E] in

theorem cell_identity : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ) (T : Finset (HeightOneSpectrum (𝓞 E)))
    (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
    ∀ (α : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} → Fin (m + 1) → ℂ) (F : GA E (m + 1) → ℂ) (l₀ : GlobalTheory.CellDec.abelian₂ E (m + 1) T)
      (U : Subgroup (GL (Fin (m + 1)) (Af E))) (Φ : (Fin (m + 1) → Cinf E) → ℂ) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ),
    (∀ w, l₀.1 w (Fin.last m) = 0) → (∀ u ∈ U, ∀ g, GlobalTheory.JSW.whit F (g * finGL E (m + 1) u) = GlobalTheory.JSW.whit F g) →
    (∀ k ∈ GlobalTheory.CellDec.US E (m + 1) T, GeneralLinearGroup.map (pInf E) k = 1 →
      (∀ w ∈ T, GlobalTheory.CellDec.compV E (m + 1) w k = 1) → ∀ g, GlobalTheory.JSW.whit F (g * k) = GlobalTheory.JSW.whit F g) →
    (∀ u ∈ GlobalTheory.CellDec.NA E (m + 1), ∀ g, ‖GlobalTheory.JSW.whit F (u * g)‖ = ‖GlobalTheory.JSW.whit F g‖) →
    (∀ p ∈ GlobalTheory.JSW.mirS E T m, ∀ l : GlobalTheory.CellDec.abelian₂ E (m + 1) T, (∀ w, 0 ≤ l.1 w (Fin.last m)) →
      GlobalTheory.JSW.whit F (p * GlobalTheory.CellDec.tl (m + 1) ϖ (l₀.1 + l.1)) = GlobalTheory.JSW.whit F (p * GlobalTheory.CellDec.tl (m + 1) ϖ l₀.1) *
        ∏ w ∈ l.1.support, (if h : w ∈ T then 1 else GlobalTheory.RSCell.sphZ (Ideal.absNorm w.asIdeal) (α ⟨w, h⟩) (l.1 w))) →
    tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E (Fin.last m) → (∀ w ∉ T, FractionalIdeal.count E w (J : FractionalIdeal (𝓞 E)⁰ E) = 0) →
    (∀ y : Fin (m + 1) → Af E, y - Pi.single (Fin.last m) 1 ∈ GlobalTheory.ThetaPoisson.latt (m + 1) J →
      ∃ κ ∈ U, (∀ w ∉ T, GeneralLinearGroup.map (pLoc E w) κ = 1) ∧
        ∀ w ∈ T, ∀ j, (GeneralLinearGroup.map (pLoc E w) κ : Matrix (Fin (m + 1)) (Fin (m + 1)) (w.adicCompletion E)) (Fin.last m) j =
          pLoc E w (y j)) →
    ∀ (x : ℝ), ∀ g ∈ GlobalTheory.CellDec.C0 E (m + 1) T, ∀ l : GlobalTheory.CellDec.abelian₂ E (m + 1) T,
      ENNReal.ofReal (GlobalTheory.CellDec.dinv (m + 1) l.1) * GlobalTheory.RSCell.bInt (Fin.last m) F Φ J (Pi.single (Fin.last m) 1) x (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g) =
        ENNReal.ofReal (GlobalTheory.CellDec.dinv (m + 1) l₀.1) * GlobalTheory.RSCell.bInt (Fin.last m) F Φ J (Pi.single (Fin.last m) 1) x (GlobalTheory.CellDec.tl (m + 1) ϖ l₀.1 * g) *
          GlobalTheory.RSCell.cellProd T α x (l.1 - l₀.1) := by
  intro E _ _ _ m T ϖ hϖ α F l₀ U Φ J hl₀ hU hK hN hprof hΦ hJ horb x g hg l
  have hνT : ∀ v ∈ T, (l.1 - l₀.1) v = 0 := fun v hv => by simp [l.2 v hv, l₀.2 v hv]
  let ν : GlobalTheory.CellDec.abelian₂ E (m + 1) T := ⟨l.1 - l₀.1, hνT⟩
  have hνl : l₀.1 + ν.1 = l.1 := by simp [ν]
  have hνw : ∀ w, ν.1 w (Fin.last m) = l.1 w (Fin.last m) := fun w => by simp [ν, hl₀ w]
  by_cases hneg : ∃ w, l.1 w (Fin.last m) < 0
  · obtain ⟨w, hw⟩ := hneg
    have hwT : w ∉ T := fun h => by simp [l.2 w h] at hw
    rw [bInt_of_not_mem _ _ _ _ _ _ _ (GlobalTheory.T.lastRow_sub_single_not_mem_lattice_of_neg_exponent E m T ϖ hϖ J hJ g hg l w hw)]
    have h2 : GlobalTheory.RSCell.cellProd T α x (l.1 - l₀.1) = 0 := by
      refine Finset.prod_eq_zero (i := w) ?_ ?_
      · rw [Finsupp.mem_support_iff]
        intro h
        have := congrFun h (Fin.last m)
        simp [hl₀ w] at this
        omega
      · rw [dif_neg hwT]
        exact GlobalTheory.RSCell.locFac_of_neg _ _ _ (i := Fin.last m) (by simp [hl₀ w]; exact hw)
    rw [h2]
    simp
  push_neg at hneg
  have hl₀n : ∀ w, 0 ≤ l₀.1 w (Fin.last m) := fun w => (hl₀ w).ge
  have hposl := GlobalTheory.T.lastRow_diagonal_mul_mem_lattice_iff E m T ϖ hϖ J hJ g hg l hneg
  have hposl₀ := GlobalTheory.T.lastRow_diagonal_mul_mem_lattice_iff E m T ϖ hϖ J hJ g hg l₀ hl₀n
  by_cases hI : (fun i => pFin E (g.val (Fin.last m) i)) - Pi.single (Fin.last m) 1 ∈ GlobalTheory.ThetaPoisson.latt (m + 1) J
  swap
  · rw [bInt_of_not_mem _ _ _ _ _ _ _ (fun h => hI (hposl.1 h)),
      bInt_of_not_mem _ _ _ _ _ _ _ (fun h => hI (hposl₀.1 h))]
    simp
  rw [bInt_of_mem _ _ _ _ _ _ _ (hposl.2 hI), bInt_of_mem _ _ _ _ _ _ _ (hposl₀.2 hI),
    rowInf_tl, rowInf_tl]
  set u : Fin (m + 1) → Cinf E := fun i => pInf E (g.val (Fin.last m) i) with hu
  by_cases hΦu : Φ u = 0
  · simp [hΦu]
  have hunit : IsUnit (pInf E (g.val (Fin.last m) (Fin.last m))) :=
    GlobalTheory.RSTheta.isUnit_of_mem_rowSet (hΦ (subset_tsupport _ hΦu))
  obtain ⟨p, hp, hpl⟩ := GlobalTheory.T.exists_mirabolic_whittaker_reduction_cell E m T ϖ F U J hU hK hN horb g hg hunit hI
  rw [hpl l, hpl l₀, GlobalTheory.T.ideleModule_det_diagonalUniformiser_mul E (m + 1) ϖ hϖ l.1 g, GlobalTheory.T.ideleModule_det_diagonalUniformiser_mul E (m + 1) ϖ hϖ l₀.1 g]
  have hpr := hprof p hp ν (fun w => by rw [hνw]; exact hneg w)
  rw [hνl] at hpr
  rw [hpr]

  have hq : ∀ v : HeightOneSpectrum (𝓞 E), (qV E v : ℝ) ≠ 0 := fun v => by
    rw [qV, Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  have hqpos : ∀ v : HeightOneSpectrum (𝓞 E), 0 < (qV E v : ℝ) := fun v =>
    lt_of_le_of_ne (Nat.cast_nonneg _) (hq v).symm
  have hcell : GlobalTheory.RSCell.cellProd T α x (l.1 - l₀.1) = ENNReal.ofReal (∏ w ∈ ν.1.support,
      ((qV E w : ℝ) ^ GlobalTheory.CellDec.wtS (m + 1) (ν.1 w) * (qV E w : ℝ) ^ (-((∑ i, (ν.1 w i : ℝ)) * x)) *
        ‖(if h : w ∈ T then 1 else GlobalTheory.RSCell.sphZ (Ideal.absNorm w.asIdeal) (α ⟨w, h⟩) (ν.1 w))‖ ^ 2)) := by
    rw [ENNReal.ofReal_prod_of_nonneg (fun w _ => by positivity)]
    refine Finset.prod_congr rfl fun w hw => ?_
    have hwT : w ∉ T := fun h => (Finsupp.mem_support_iff.1 hw) (hνT w h)
    rw [dif_neg hwT, dif_neg hwT, ← GlobalTheory.T.spherical_local_factor_norm_sq (Ideal.absNorm w.asIdeal) (Nat.pos_of_ne_zero (by
      rw [Ne, Ideal.absNorm_eq_zero_iff]; exact w.ne_bot)) m (α ⟨w, hwT⟩) x (ν.1 w) (by rw [hνw]; exact hneg w),
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (norm_nonneg _),
      ofReal_norm_eq_enorm]
    rfl
  have hd0 : ∀ k : HeightOneSpectrum (𝓞 E) →₀ (Fin (m + 1) → ℤ), 0 ≤ GlobalTheory.CellDec.dinv (m + 1) k := fun k =>
    Finset.prod_nonneg fun v _ => (zpow_pos (hqpos v) _).le
  rw [hcell, ← ENNReal.ofReal_mul (hd0 _), ← ENNReal.ofReal_mul (hd0 _), ← ENNReal.ofReal_mul (mul_nonneg (hd0 _) <| mul_nonneg (mul_nonneg (by positivity) (norm_nonneg _))
    (Real.rpow_nonneg (mul_nonneg (Finset.prod_nonneg fun v _ => (inv_pos.2 (zpow_pos (hqpos v) _)).le)
      ((ideleModule E (GeneralLinearGroup.det g)).2.le)) _))]
  congr 1
  have hd : GlobalTheory.CellDec.dinv (m + 1) l.1 = GlobalTheory.CellDec.dinv (m + 1) l₀.1 *
      ∏ w ∈ ν.1.support, (qV E w : ℝ) ^ GlobalTheory.CellDec.wtS (m + 1) (ν.1 w) := by
    rw [← hνl]
    exact prod_supp_add (fun v => (qV E v : ℝ)) hq (wtSHom (m + 1)) l₀.1 ν.1
  have hQ : ∀ k : HeightOneSpectrum (𝓞 E) →₀ (Fin (m + 1) → ℤ),
      ∏ v ∈ k.support, ((qV E v : ℝ) ^ ∑ i, k v i)⁻¹ = ∏ v ∈ k.support, (qV E v : ℝ) ^ negSumHom (m + 1) (k v) := by
    intro k
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [← _root_.zpow_neg]; rfl
  have hQl : ∏ v ∈ l.1.support, ((qV E v : ℝ) ^ ∑ i, l.1 v i)⁻¹ =
      (∏ v ∈ l₀.1.support, ((qV E v : ℝ) ^ ∑ i, l₀.1 v i)⁻¹) * ∏ v ∈ ν.1.support, ((qV E v : ℝ) ^ ∑ i, ν.1 v i)⁻¹ := by
    rw [hQ, hQ, hQ, ← hνl]
    exact prod_supp_add (fun v => (qV E v : ℝ)) hq (negSumHom (m + 1)) l₀.1 ν.1
  have hQν : (∏ v ∈ ν.1.support, ((qV E v : ℝ) ^ ∑ i, ν.1 v i)⁻¹) ^ x =
      ∏ v ∈ ν.1.support, (qV E v : ℝ) ^ (-((∑ i, (ν.1 v i : ℝ)) * x)) := by
    rw [← Real.finset_prod_rpow _ _ (fun v _ => (inv_pos.2 (zpow_pos (hqpos v) _)).le)]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [← Real.rpow_intCast, ← Real.rpow_neg (hqpos v).le, ← Real.rpow_mul (hqpos v).le]
    push_cast
    ring_nf
  have hD := ((ideleModule E (GeneralLinearGroup.det g)).2 : (0 : ℝ) < _)
  have hQ₀ : 0 ≤ ∏ v ∈ l₀.1.support, ((qV E v : ℝ) ^ ∑ i, l₀.1 v i)⁻¹ :=
    Finset.prod_nonneg fun v _ => (inv_pos.2 (zpow_pos (hqpos v) _)).le
  have hQν0 : 0 ≤ ∏ v ∈ ν.1.support, ((qV E v : ℝ) ^ ∑ i, ν.1 v i)⁻¹ :=
    Finset.prod_nonneg fun v _ => (inv_pos.2 (zpow_pos (hqpos v) _)).le
  rw [hd, hQl, Real.mul_rpow (mul_nonneg hQ₀ hQν0) hD.le, Real.mul_rpow hQ₀ hQν0, hQν, Real.mul_rpow hQ₀ hD.le,
    norm_mul, norm_prod, mul_pow, ← Finset.prod_pow, Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  ring

end GlobalTheory.CellPw
