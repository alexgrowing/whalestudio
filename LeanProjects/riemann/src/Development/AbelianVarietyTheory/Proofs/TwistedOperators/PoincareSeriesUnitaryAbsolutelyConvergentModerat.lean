import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsModGrowthExpLeNormInfPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeCharInfinityEqCoeffMulHalfNormPow
import Development.AbelianVarietyTheory.Proofs.HeightProofs.UnitaryAdelicHeightCosetLeNormInfPow
import Formalism.LocalToGlobal.Columns.TiedTilA
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SumProductWeightsLeOfSeparatedGeometricMeanStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCommonDenominatorSelfDualLevelStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFinitePartDenominatorLeHeightPowStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PoinCount

variable {D : D7}

theorem norm_entry_le_hsn {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) : ‖X i j‖ ≤ hsn X := by
  unfold hsn
  rw [← Real.sqrt_sq (norm_nonneg (X i j))]
  apply Real.sqrt_le_sqrt
  calc ‖X i j‖ ^ 2 ≤ ∑ j', ‖X i j'‖ ^ 2 :=
        Finset.single_le_sum (f := fun j' => ‖X i j'‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', ‖X i' j'‖ ^ 2 :=
        Finset.single_le_sum (f := fun i' => ∑ j', ‖X i' j'‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ i)

theorem hsn_le_sum {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) : hsn X ≤ ∑ i, ∑ j, ‖X i j‖ := by
  unfold hsn
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  calc ∑ i, ∑ j, ‖X i j‖ ^ 2 ≤ ∑ i, (∑ j, ‖X i j‖) ^ 2 :=
        Finset.sum_le_sum fun i _ => Finset.sum_sq_le_sq_sum_of_nonneg fun j _ => norm_nonneg _
    _ ≤ (∑ i, ∑ j, ‖X i j‖) ^ 2 :=
        Finset.sum_sq_le_sq_sum_of_nonneg fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _

theorem hsn_mul_le {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℂ) : hsn (X * Y) ≤ hsn X * hsn Y := by
  letI := Matrix.frobeniusSeminormedAddCommGroup (m := Fin n) (n := Fin n) (α := ℂ)
  have e : ∀ Z : Matrix (Fin n) (Fin n) ℂ, hsn Z = ‖Z‖ := fun Z => by
    rw [Matrix.frobenius_norm_def, hsn, Real.sqrt_eq_rpow]
    congr 1
    simp only [Real.rpow_two]
  rw [e, e, e]
  exact Matrix.frobenius_norm_mul X Y

theorem one_le_prod_tauE (D : D7) {y : D.host.E} (hy : y ≠ 0) (hi : IsIntegral ℤ y) : 1 ≤ ∏ τ, ‖tauE D τ y‖ := by
  have hnorm : ∏ τ, ‖tauE D τ y‖ ^ 2 = |((Algebra.norm ℚ y : ℚ) : ℝ)| := by
    rw [← Rat.cast_abs, ← NumberField.InfinitePlace.prod_eq_abs_norm]
    refine (Fintype.prod_bijective _ (GlobalTheory.LevelSeries.mk_tauE_bij D) _ _ (fun τ => ?_))
    rw [NumberField.InfinitePlace.mult, if_neg (GlobalTheory.LevelSeries.mk_tauE_complex D τ)]
    rfl
  have h1 : (1 : ℝ) ≤ |((Algebra.norm ℚ y : ℚ) : ℝ)| := by
    let z : 𝓞 D.host.E := ⟨y, hi⟩
    have hz : z ≠ 0 := fun h => hy (congrArg Subtype.val h)
    have e : ((Algebra.norm ℤ z : ℤ) : ℚ) = Algebra.norm ℚ y := Algebra.coe_norm_int z
    have hn : Algebra.norm ℤ z ≠ 0 := Algebra.norm_ne_zero_iff.2 hz
    rw [← e]
    have := Int.one_le_abs hn
    push_cast
    exact_mod_cast this
  rw [← hnorm, Finset.prod_pow] at h1
  have h0 : 0 ≤ ∏ τ, ‖tauE D τ y‖ := Finset.prod_nonneg fun _ _ => norm_nonneg _
  nlinarith

theorem exists_rat (V : HSp D) (γ : GQ V) :
    ∃ δ : GL (Fin V.rank) D.host.E, Formalism.UG.bc (inclR (AF D.host.F)) δ = matHom V (γ : GA D V) := by
  have h1 := γ.2
  simp only [GQ, HFinIn, HFin, Subgroup.mem_subgroupOf, Subgroup.mem_map] at h1
  obtain ⟨δ, -, hδ⟩ := h1
  exact ⟨δ, hδ⟩

theorem cmp_rat {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) (γ : GA D V) (δ : GL (Fin V.rank) D.host.E)
    (h : Formalism.UG.bc (inclR (AF D.host.F)) δ = matHom V γ) (τ : D.what₂.Tau) :
    cmp θ τ γ = (δ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (tauE D τ) := by
  ext i j
  have e : (HA.mat (AF D.host.F) D.sp.cm.sig V.gram γ).1 i j =
      inclR (AF D.host.F) ((δ : Matrix (Fin V.rank) (Fin V.rank) D.host.E) i j) := by
    rw [show HA.mat (AF D.host.F) D.sp.cm.sig V.gram γ = matHom V γ from rfl, ← h]
    rfl
  show infMat D.sp.cm.sig V.gram (θ τ) γ i j = _
  simp only [infMat, Matrix.map_apply, e]
  simp [inclR, (hθ τ).1]

end GlobalTheory.PoinCount

namespace GlobalTheory.PoinCount

theorem level_den (D : D7) (V : HSp D) (Λ : Lat V) (hΛ : IsSelfDualC V Λ) : ∃ b : ℕ, 0 < b ∧
    ∀ k ∈ congLev D.sp.cm V.gram Λ ⊤, ∀ i j,
      (b : Lev.EAf D) * k.1 i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
  GlobalTheory.T.exists_common_denominator_selfDual_level D V Λ hΛ

theorem point_den (D : D7) (V : HSp D) : ∃ (C : ℝ) (A : ℕ), ∀ g : GA D V, ∃ d : ℕ, 0 < d ∧ (d : ℝ) ≤ C * height V g ^ A ∧
    ∀ i j, (d : Lev.EAf D) * (Lev.finE V g).1 i j ∈
      Formalism.L2.Herm.intAf D.host.F D.host.E :=
  GlobalTheory.T.exists_finitePart_denominator_le_height_pow D V

variable {D : D7}

theorem finE_rat (V : HSp D) (γ : GA D V) (δ : GL (Fin V.rank) D.host.E)
    (h : Formalism.UG.bc (inclR (AF D.host.F)) δ = matHom V γ) (i j : Fin V.rank) :
    (Lev.finE V γ).1 i j =
      Formalism.L2.Col.iA D.host.F D.host.E ((δ : Matrix (Fin V.rank) (Fin V.rank) D.host.E) i j) := by
  simp only [Lev.finE, finHom, MonoidHom.comp_apply, ← h]
  rfl

end GlobalTheory.PoinCount

namespace GlobalTheory.PoinCount

variable {D : D7}

theorem mem_mul_of_mem {n : ℕ} {S : Subring (Lev.EAf D)} (X Y : Matrix (Fin n) (Fin n) (Lev.EAf D))
    (hX : ∀ i j, X i j ∈ S) (hY : ∀ i j, Y i j ∈ S) (i j : Fin n) : (X * Y) i j ∈ S := by
  rw [Matrix.mul_apply]
  exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hX i k) (hY k j)

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in
theorem exists_den (D : D7) (V : HSp D) (Λ : Lat V) (hΛ : IsSelfDualC V Λ) (c : GA D V) :
    ∃ (C : ℝ) (A : ℕ), ∀ g : GA D V, ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ C * height V g ^ A ∧
      ∀ γ : GA D V, Lev.finE V (c * γ * g) ∈ congLev D.sp.cm V.gram Λ ⊤ →
        ∀ δ : GL (Fin V.rank) D.host.E, Formalism.UG.bc (inclR (AF D.host.F)) δ = matHom V γ →
          ∀ i j, IsIntegral ℤ ((m : D.host.E) * (δ : Matrix (Fin V.rank) (Fin V.rank) D.host.E) i j) := by
  obtain ⟨b, hb0, hb⟩ := level_den D V Λ hΛ
  obtain ⟨C, A, hg⟩ := point_den D V
  obtain ⟨dc, hdc0, -, hdc⟩ := hg c⁻¹
  refine ⟨(dc : ℝ) * b * C, A, fun g => ?_⟩
  obtain ⟨dg, hdg0, hdgH, hdg⟩ := hg g⁻¹
  rw [GlobalTheory.Grow.height_inv] at hdgH
  refine ⟨dc * b * dg, by positivity, ?_, fun γ hk δ hδ i j => ?_⟩
  · push_cast
    calc (dc : ℝ) * b * dg ≤ dc * b * (C * height V g ^ A) :=
          mul_le_mul_of_nonneg_left hdgH (by positivity)
      _ = dc * b * C * height V g ^ A := by ring
  · have e : (Lev.finE V γ).1 = (Lev.finE V c⁻¹).1 * (Lev.finE V (c * γ * g)).1 * (Lev.finE V g⁻¹).1 := by
      rw [← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul]
      congr 2
      group
    have hP : ∀ i j, ((dc : Lev.EAf D) • (Lev.finE V c⁻¹).1) i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
      fun i j => by rw [Matrix.smul_apply, smul_eq_mul]; exact hdc i j
    have hK : ∀ i j, ((b : Lev.EAf D) • (Lev.finE V (c * γ * g)).1) i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
      fun i j => by rw [Matrix.smul_apply, smul_eq_mul]; exact hb _ hk i j
    have hQ : ∀ i j, ((dg : Lev.EAf D) • (Lev.finE V g⁻¹).1) i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
      fun i j => by rw [Matrix.smul_apply, smul_eq_mul]; exact hdg i j
    have hmem := mem_mul_of_mem _ _ (mem_mul_of_mem _ _ hP hK) hQ i j
    have e2 : ((dc : Lev.EAf D) • (Lev.finE V c⁻¹).1 * ((b : Lev.EAf D) • (Lev.finE V (c * γ * g)).1) *
        ((dg : Lev.EAf D) • (Lev.finE V g⁻¹).1)) i j = ((dc * b * dg : ℕ) : Lev.EAf D) * (Lev.finE V γ).1 i j := by
      rw [e]
      simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_apply, smul_eq_mul, Nat.cast_mul]
      ring
    rw [e2, finE_rat V γ δ hδ i j] at hmem
    have e3 : Formalism.L2.Col.iA D.host.F D.host.E (((dc * b * dg : ℕ) : D.host.E) *
        (δ : Matrix (Fin V.rank) (Fin V.rank) D.host.E) i j) =
        ((dc * b * dg : ℕ) : Lev.EAf D) * Formalism.L2.Col.iA D.host.F D.host.E ((δ : Matrix (Fin V.rank) (Fin V.rank) D.host.E) i j) := by
      rw [map_mul, map_natCast]
    rw [← e3] at hmem
    obtain ⟨r, hr⟩ := Formalism.L2.Col.til_tmv_int_of_iA hmem
    rw [← hr]
    exact RingOfIntegers.isIntegral_coe r

end GlobalTheory.PoinCount

namespace GlobalTheory.PoinCount

theorem sum_sep_le (ι : Type) [Fintype ι] [Nonempty ι] (n : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ la : ℝ, 0 < la → la ≤ 1 →
    ∀ S : Finset (ι → Matrix (Fin n) (Fin n) ℂ),
      (∀ s ∈ S, ∀ s' ∈ S, s ≠ s' → la ^ Fintype.card ι ≤ ∏ v, hsn (s v - s' v)) →
      ∑ s ∈ S, ∏ v, ((1 + hsn (s v)) ^ (2 * n ^ 2 + 1))⁻¹ ≤ C * la⁻¹ ^ (2 * n ^ 2 * Fintype.card ι) :=
  GlobalTheory.T.sum_productWeights_le_of_separated_geometricMean ι n

variable {D : D7}

theorem hsn_cmp_le {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g : GA D V) τ, hsn (cmp θ τ g) ≤ C * height V g := by
  obtain ⟨C, hC⟩ := GlobalTheory.Grow.normInf_le_height V hθ
  refine ⟨max C 0, le_max_right _ _, fun g τ => ?_⟩
  have h1 : hsn (cmp θ τ g) ≤ normInf θ V g := by
    refine (hsn_le_sum _).trans ?_
    unfold normInf
    refine le_trans ?_ (Finset.single_le_sum (f := fun τ => ∑ i, ∑ j,
      (‖infMat D.sp.cm.sig V.gram (θ τ) g i j‖ + ‖infMat D.sp.cm.sig V.gram (θ τ) g⁻¹ i j‖))
      (fun _ _ => by positivity) (Finset.mem_univ τ))
    exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => le_add_of_nonneg_right (norm_nonneg _)
  exact h1.trans ((hC g).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (GlobalTheory.Grow.height_pos V g).le))

theorem poincare_count : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (Λ : Lat V), IsSelfDualC V Λ → ∀ c : GA D V,
    ∃ (C : ℝ) (A : ℕ), ∀ (g : GA D V) (s : Finset (GQ V)),
      (∀ γ ∈ s, Lev.finE V (c * (γ : GA D V) * g) ∈ congLev D.sp.cm V.gram Λ ⊤) →
      ∑ γ ∈ s, ∏ τ, ((1 + hsn (GlobalTheory.SepPer.cmp θ τ (c * (γ : GA D V) * g))) ^ (2 * V.rank ^ 2 + 1))⁻¹ ≤
        C * height V g ^ A := by
  intro D θ hθ V Λ hΛ c
  haveI : Nonempty D.what₂.Tau := ⟨((GlobalTheory.LevelSeries.mk_tauE_bij D).2 (Classical.arbitrary _)).choose⟩
  obtain ⟨C3, A3, h3⟩ := exists_den D V Λ hΛ c
  obtain ⟨C4, hC4, h4⟩ := hsn_cmp_le hθ V
  obtain ⟨C5, hC5, h5⟩ := sum_sep_le D.what₂.Tau V.rank
  set N := 2 * V.rank ^ 2 + 1 with hN
  set f := Fintype.card D.what₂.Tau with hf
  set Kc : ℝ := ∑ τ, hsn (cmp θ τ c⁻¹) with hKc
  have hKc0 : 0 ≤ Kc := Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _
  set B : ℝ := 1 + Kc * C4 with hB
  have hB1 : 1 ≤ B := le_add_of_nonneg_right (mul_nonneg hKc0 hC4)
  refine ⟨B ^ (N * f) * C5 * (max C3 1) ^ (2 * V.rank ^ 2 * f), N * f + A3 * (2 * V.rank ^ 2 * f),
    fun g s hs => ?_⟩
  obtain ⟨m, hm0, hmH, hm⟩ := h3 g
  set H := height V g with hHdef
  have hH : 1 ≤ H := GlobalTheory.Grow.one_le_height V g
  choose δ hδ using fun γ : GQ V => exists_rat V γ
  let x : GQ V → D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ := fun γ τ => cmp θ τ (γ : GA D V)
  have hx : ∀ γ τ, x γ τ = (δ γ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (tauE D τ) :=
    fun γ τ => cmp_rat hθ V γ (δ γ) (hδ γ) τ
  have hinj : Set.InjOn x s := by
    intro γ _ γ' _ e
    have e1 : (δ γ : Matrix (Fin V.rank) (Fin V.rank) D.host.E) = δ γ' := by
      obtain ⟨τ⟩ := ‹Nonempty D.what₂.Tau›
      have := congrFun e τ
      rw [hx, hx] at this
      exact Matrix.ext fun i j => (tauE D τ).injective (congrFun (congrFun this i) j)
    have e2 : δ γ = δ γ' := Units.ext e1
    have e3 : matHom V (γ : GA D V) = matHom V (γ' : GA D V) := by rw [← hδ, ← hδ, e2]
    have e4 : (γ : GA D V) = γ' := by
      unfold Formalism.L2.Theta.matHom at e3
      exact Subgroup.subtype_injective _ e3
    exact Subtype.ext e4
  have hsep : ∀ y ∈ s.image x, ∀ y' ∈ s.image x, y ≠ y' →
      ((m : ℝ)⁻¹) ^ f ≤ ∏ τ, hsn (y τ - y' τ) := by
    intro y hy y' hy' hne
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.1 hy
    obtain ⟨γ', hγ', rfl⟩ := Finset.mem_image.1 hy'
    have hδne : (δ γ : Matrix (Fin V.rank) (Fin V.rank) D.host.E) ≠ δ γ' := by
      intro e; apply hne; funext τ; rw [hx, hx, e]
    obtain ⟨i, j, hij⟩ : ∃ i j, (δ γ : Matrix (Fin V.rank) (Fin V.rank) D.host.E) i j ≠
        (δ γ' : Matrix (Fin V.rank) (Fin V.rank) D.host.E) i j := by
      by_contra hc; push_neg at hc; exact hδne (Matrix.ext hc)
    set z := (δ γ : Matrix (Fin V.rank) (Fin V.rank) D.host.E) i j -
      (δ γ' : Matrix (Fin V.rank) (Fin V.rank) D.host.E) i j with hz
    have hz0 : z ≠ 0 := sub_ne_zero.2 hij
    have hint : IsIntegral ℤ ((m : D.host.E) * z) := by
      rw [hz, mul_sub]
      exact (hm _ (hs γ hγ) _ (hδ γ) i j).sub (hm _ (hs γ' hγ') _ (hδ γ') i j)
    have h1 := one_le_prod_tauE D (mul_ne_zero (Nat.cast_ne_zero.2 hm0.ne') hz0) hint
    have h2 : ∀ τ, ‖tauE D τ ((m : D.host.E) * z)‖ ≤ m * hsn (x γ τ - x γ' τ) := by
      intro τ
      have ez : (x γ τ - x γ' τ) i j = tauE D τ z := by
        rw [hx, hx, Matrix.sub_apply, Matrix.map_apply, Matrix.map_apply, hz, map_sub]
      rw [map_mul, norm_mul, map_natCast, Complex.norm_natCast, ← ez]
      exact mul_le_mul_of_nonneg_left (norm_entry_le_hsn _ i j) (Nat.cast_nonneg _)
    have h3 : (1 : ℝ) ≤ (m : ℝ) ^ f * ∏ τ, hsn (x γ τ - x γ' τ) := by
      calc (1 : ℝ) ≤ ∏ τ, ‖tauE D τ ((m : D.host.E) * z)‖ := h1
        _ ≤ ∏ τ, ((m : ℝ) * hsn (x γ τ - x γ' τ)) :=
          Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun τ _ => h2 τ
        _ = (m : ℝ) ^ f * ∏ τ, hsn (x γ τ - x γ' τ) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
    have hmpos : (0 : ℝ) < (m : ℝ) ^ f := by positivity
    rw [inv_pow, inv_le_iff_one_le_mul₀' hmpos]
    exact h3
  have hterm : ∀ γ ∈ s, ∏ τ, ((1 + hsn (cmp θ τ (c * (γ : GA D V) * g))) ^ N)⁻¹ ≤
      (B * H) ^ (N * f) * ∏ τ, ((1 + hsn (x γ τ)) ^ N)⁻¹ := by
    intro γ _
    rw [pow_mul, hf, ← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod (fun τ _ => inv_nonneg.2 (pow_nonneg (add_nonneg zero_le_one (Real.sqrt_nonneg _)) _)) fun τ _ => ?_
    set h := hsn (cmp θ τ (c * (γ : GA D V) * g)) with hh
    have hh0 : 0 ≤ h := Real.sqrt_nonneg _
    have e : (γ : GA D V) = c⁻¹ * (c * (γ : GA D V) * g) * g⁻¹ := by group
    have hx' : x γ τ = cmp θ τ c⁻¹ * cmp θ τ (c * (γ : GA D V) * g) * cmp θ τ g⁻¹ := by
      show infMat D.sp.cm.sig V.gram (θ τ) (γ : GA D V) = _
      conv_lhs => rw [e]
      rw [GlobalTheory.SmoothForms.HeightCoset.infMat_mul', GlobalTheory.SmoothForms.HeightCoset.infMat_mul']
    have hg : hsn (cmp θ τ g⁻¹) ≤ C4 * H := by
      have := h4 g⁻¹ τ; rwa [GlobalTheory.Grow.height_inv] at this
    have hc : hsn (cmp θ τ c⁻¹) ≤ Kc :=
      Finset.single_le_sum (f := fun τ => hsn (cmp θ τ c⁻¹)) (fun _ _ => Real.sqrt_nonneg _) (Finset.mem_univ τ)
    have hb : hsn (x γ τ) ≤ Kc * C4 * H * h := by
      rw [hx']
      calc _ ≤ hsn (cmp θ τ c⁻¹ * cmp θ τ (c * (γ : GA D V) * g)) * hsn (cmp θ τ g⁻¹) := hsn_mul_le _ _
        _ ≤ (hsn (cmp θ τ c⁻¹) * h) * (C4 * H) :=
          mul_le_mul (hsn_mul_le _ _) hg (Real.sqrt_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hh0)
        _ ≤ (Kc * h) * (C4 * H) := by gcongr
        _ = Kc * C4 * H * h := by ring
    have hK : 0 ≤ Kc * C4 := mul_nonneg hKc0 hC4
    have hH0 : 0 ≤ H := zero_le_one.trans hH
    have t1 : 0 ≤ H * h := mul_nonneg hH0 hh0
    have t2 : 0 ≤ Kc * C4 * H := mul_nonneg hK hH0
    have t3 : 0 ≤ Kc * C4 * H * h := mul_nonneg t2 hh0
    have eB : B * H * (1 + h) = H + H * h + Kc * C4 * H + Kc * C4 * H * h := by rw [hB]; ring
    have hle : 1 + hsn (x γ τ) ≤ B * H * (1 + h) := by rw [eB]; linarith
    have hp : 0 < (1 + hsn (x γ τ)) ^ N := pow_pos (add_pos_of_pos_of_nonneg zero_lt_one (Real.sqrt_nonneg _)) _
    have hq : 0 < (1 + h) ^ N := pow_pos (add_pos_of_pos_of_nonneg zero_lt_one hh0) _
    rw [← div_eq_mul_inv, le_div_iff₀ hp, ← div_eq_inv_mul, div_le_iff₀ hq, ← mul_pow]
    exact pow_le_pow_left₀ (add_nonneg zero_le_one (Real.sqrt_nonneg _)) hle N
  have hla : (0 : ℝ) < (m : ℝ)⁻¹ := by positivity
  have hla1 : (m : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hm0)
  have hsum := h5 _ hla hla1 (s.image x) hsep
  rw [inv_inv] at hsum
  have hmle : (m : ℝ) ≤ max C3 1 * H ^ A3 :=
    hmH.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  calc ∑ γ ∈ s, ∏ τ, ((1 + hsn (cmp θ τ (c * (γ : GA D V) * g))) ^ N)⁻¹
      ≤ ∑ γ ∈ s, (B * H) ^ (N * f) * ∏ τ, ((1 + hsn (x γ τ)) ^ N)⁻¹ := Finset.sum_le_sum hterm
    _ = (B * H) ^ (N * f) * ∑ y ∈ s.image x, ∏ τ, ((1 + hsn (y τ)) ^ N)⁻¹ := by
      rw [← Finset.mul_sum, Finset.sum_image hinj]
    _ ≤ (B * H) ^ (N * f) * (C5 * (m : ℝ) ^ (2 * V.rank ^ 2 * f)) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ (B * H) ^ (N * f) * (C5 * (max C3 1 * H ^ A3) ^ (2 * V.rank ^ 2 * f)) := by
      gcongr
    _ = B ^ (N * f) * C5 * (max C3 1) ^ (2 * V.rank ^ 2 * f) * H ^ (N * f + A3 * (2 * V.rank ^ 2 * f)) := by
      rw [mul_pow, mul_pow, ← pow_mul, pow_add]; ring

end GlobalTheory.PoinCount
