import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepRationalSupportCommonDenominator
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsScaleMovedHeisenbergLatticePolynomialHeigh
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzFixedBySmallHeisenbergLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundedDenominatorStandardCharTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawPairPlaneDescentTenth

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

noncomputable section

namespace GlobalTheory.EvPtDenom

open Formalism.UG in

theorem exists_scale : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n d : ℕ) (κ ι : Type)
    [Fintype κ] [Fintype ι]
    (e : Matrix (Fin n) (Fin d) (AF F ⊗[F] E) ≃ₗ[AF F] (κ → AF F) × (κ → AF F)) (Y : ι → Matrix (Fin n) (Fin d) (AF F ⊗[F] E))
    (N : ℕ), 1 ≤ N →
    ∃ (C : ℝ) (k : ℕ), ∀ (g : GL (Fin n) (AF F ⊗[F] E)) (h : GL (Fin d) (AF F ⊗[F] E)), ∃ m : ℕ, 1 ≤ m ∧
      (m : ℝ) ≤ C * ((heightGL F g : ℝ) * heightGL F h) ^ k ∧ ∀ (i : ι) (j : κ),
        GlobalTheory.FinSupp.FinDiv F N ((m : AF F) *
          (e (((g⁻¹ : GL (Fin n) (AF F ⊗[F] E)) : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) * Y i *
            (((h⁻¹ : GL (Fin d) (AF F ⊗[F] E)) : Matrix (Fin d) (Fin d) (AF F ⊗[F] E)))ᵀ)).1 j) ∧
        GlobalTheory.FinSupp.FinDiv F N ((m : AF F) *
          (e (((g⁻¹ : GL (Fin n) (AF F ⊗[F] E)) : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) * Y i *
            (((h⁻¹ : GL (Fin d) (AF F ⊗[F] E)) : Matrix (Fin d) (Fin d) (AF F ⊗[F] E)))ᵀ)).2 j) := by
  intro F E _ _ _ _ _ n d κ ι _ _ e Y N hN
  classical
  let f1 : κ → (Matrix (Fin n) (Fin d) (AF F ⊗[F] E) →ₗ[AF F] AF F) := fun j =>
    (LinearMap.proj j).comp ((LinearMap.fst (AF F) (κ → AF F) (κ → AF F)).comp e.toLinearMap)
  let f2 : κ → (Matrix (Fin n) (Fin d) (AF F ⊗[F] E) →ₗ[AF F] AF F) := fun j =>
    (LinearMap.proj j).comp ((LinearMap.snd (AF F) (κ → AF F) (κ → AF F)).comp e.toLinearMap)
  choose K1 hK1f hK1 hK1b using fun j => GlobalTheory.LinFormBound.main (f1 j)
  choose K2 hK2f hK2 hK2b using fun j => GlobalTheory.LinFormBound.main (f2 j)
  choose Kx hKxf hKx hKxb using fun i => GlobalTheory.FixedBound.exists_entry_absFin_bound (Y i)
  let Kc : HeightOneSpectrum (𝓞 F) → ℝ≥0 := fun v => (∏ j, K1 j v * K2 j v) * ∏ i, Kx i v
  have hKc1 : ∀ v, 1 ≤ Kc v := fun v =>
    one_le_mul_of_one_le_of_one_le (Finset.one_le_prod' fun j _ => one_le_mul_of_one_le_of_one_le (hK1 j v) (hK2 j v))
      (Finset.one_le_prod' fun i _ => hKx i v)
  have hKcf : (Function.mulSupport Kc).Finite := by
    refine ((Set.finite_iUnion fun j => (hK1f j).union (hK2f j)).union (Set.finite_iUnion hKxf)).subset ?_
    refine (Function.mulSupport_mul _ _).trans (Set.union_subset_union ?_ ?_)
    · refine (Finset.mulSupport_prod _ _).trans ?_
      intro v hv
      simp only [Set.mem_iUnion] at hv ⊢
      obtain ⟨j, -, hj⟩ := hv
      exact ⟨j, Function.mulSupport_mul _ _ hj⟩
    · refine (Finset.mulSupport_prod _ _).trans ?_
      intro v hv
      simp only [Set.mem_iUnion] at hv ⊢
      obtain ⟨i, -, hi⟩ := hv
      exact ⟨i, hi⟩
  have hP1 : ∀ v, ∏ j, K1 j v * K2 j v ≤ Kc v := fun v =>
    le_mul_of_one_le_right' (Finset.one_le_prod' fun i _ => hKx i v)
  have hP2 : ∀ v, ∏ i, Kx i v ≤ Kc v := fun v =>
    le_mul_of_one_le_left' (Finset.one_le_prod' fun j _ => one_le_mul_of_one_le_of_one_le (hK1 j v) (hK2 j v))
  have hK1c : ∀ v i j, K1 j v * Kx i v ≤ Kc v := fun v i j => by
    refine le_trans ?_ (mul_le_mul' (Finset.single_le_prod' (fun j _ => one_le_mul_of_one_le_of_one_le (hK1 j v) (hK2 j v))
      (Finset.mem_univ j)) (Finset.single_le_prod' (fun i _ => hKx i v) (Finset.mem_univ i)))
    exact mul_le_mul' (le_mul_of_one_le_right' (hK2 j v)) le_rfl
  have hK2c : ∀ v i j, K2 j v * Kx i v ≤ Kc v := fun v i j => by
    refine le_trans ?_ (mul_le_mul' (Finset.single_le_prod' (fun j _ => one_le_mul_of_one_le_of_one_le (hK1 j v) (hK2 j v))
      (Finset.mem_univ j)) (Finset.single_le_prod' (fun i _ => hKx i v) (Finset.mem_univ i)))
    exact mul_le_mul' (le_mul_of_one_le_left' (hK1 j v)) le_rfl
  let C0 : ℝ≥0 := ∏ᶠ v, Kc v
  refine ⟨N * C0, 1, fun g h => ?_⟩
  let Hg : HeightOneSpectrum (𝓞 F) → ℝ≥0 := fun v => htFin F v (bc (compFin F E v) g)
  let Hh : HeightOneSpectrum (𝓞 F) → ℝ≥0 := fun v => htFin F v (bc (compFin F E v) h)
  have hgf : (Function.mulSupport Hg).Finite := finite_mulSupport_htFin F g
  have hhf : (Function.mulSupport Hh).Finite := finite_mulSupport_htFin F h
  let Z : ι → Matrix (Fin n) (Fin d) (AF F ⊗[F] E) := fun i =>
    ((g⁻¹ : GL (Fin n) (AF F ⊗[F] E)) : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) * Y i *
      (((h⁻¹ : GL (Fin d) (AF F ⊗[F] E)) : Matrix (Fin d) (Fin d) (AF F ⊗[F] E)))ᵀ
  have hsup : ∀ i v, (Finset.univ.sup fun p : Fin n × Fin d => absFin F v (compFin F E v (Z i p.1 p.2))) ≤
      Kx i v * (Hg v * Hh v) := fun i v => by
    refine Finset.sup_le fun p _ => (GlobalTheory.absFin_mul_mul_transpose_le g⁻¹ (Y i) h⁻¹ v p.1 p.2).trans ?_
    rw [GlobalTheory.MovedLat.htFin_bc_inv, GlobalTheory.MovedLat.htFin_bc_inv]
    calc _ ≤ Hg v * Kx i v * Hh v := mul_le_mul' (mul_le_mul' le_rfl (hKxb i v)) le_rfl
      _ = Kx i v * (Hg v * Hh v) := by ring
  have hloc1 : ∀ i j v, ‖evFin F v ((e (Z i)).1 j)‖₊ ≤ Kc v * (Hg v * Hh v) := fun i j v => by
    have := hK1b j (Z i) v
    calc _ ≤ K1 j v * (Kx i v * (Hg v * Hh v)) := this.trans (mul_le_mul' le_rfl (hsup i v))
      _ = (K1 j v * Kx i v) * (Hg v * Hh v) := by ring
      _ ≤ Kc v * (Hg v * Hh v) := mul_le_mul' (hK1c v i j) le_rfl
  have hloc2 : ∀ i j v, ‖evFin F v ((e (Z i)).2 j)‖₊ ≤ Kc v * (Hg v * Hh v) := fun i j v => by
    have := hK2b j (Z i) v
    calc _ ≤ K2 j v * (Kx i v * (Hg v * Hh v)) := this.trans (mul_le_mul' le_rfl (hsup i v))
      _ = (K2 j v * Kx i v) * (Hg v * Hh v) := by ring
      _ ≤ Kc v * (Hg v * Hh v) := mul_le_mul' (hK2c v i j) le_rfl
  let H : HeightOneSpectrum (𝓞 F) → ℝ≥0 := fun v => Kc v * (Hg v * Hh v)
  have hH1 : ∀ v, 1 ≤ H v := fun v =>
    one_le_mul_of_one_le_of_one_le (hKc1 v) (one_le_mul_of_one_le_of_one_le (one_le_htOf _ _) (one_le_htOf _ _))
  have hHf : (Function.mulSupport H).Finite :=
    (hKcf.union (hgf.union hhf)).subset ((Function.mulSupport_mul _ _).trans
      (Set.union_subset_union le_rfl (Function.mulSupport_mul _ _)))
  obtain ⟨M, hM0, hMb, hMv⟩ := GlobalTheory.SmoothForms.denom_global H hH1 hHf
  have hfin : ∀ x : AF F, (∀ v, ‖evFin F v x‖₊ ≤ H v) → GlobalTheory.FinSupp.FinDiv F N (((N * M : ℕ) : AF F) * x) := by
    intro x hx v
    refine ⟨(M : Fv F v) * evFin F v x, Valued.toNormedField.norm_le_one_iff.1 (hMv v _ (hx v)), ?_⟩
    rw [map_mul, map_natCast]
    push_cast
    ring
  refine ⟨N * M, Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega)), ?_, fun i j => ⟨hfin _ (hloc1 i j), hfin _ (hloc2 i j)⟩⟩
  have hMH : (M : ℝ≥0) ≤ C0 * (heightGL F g * heightGL F h) := by
    refine hMb.trans (le_of_eq_of_le (finprod_mul_distrib hKcf ((hgf.union hhf).subset (Function.mulSupport_mul _ _))) ?_)
    refine mul_le_mul' le_rfl ?_
    rw [finprod_mul_distrib hgf hhf]
    exact mul_le_mul' (GlobalTheory.MovedLat.finprod_htFin_le g) (GlobalTheory.MovedLat.finprod_htFin_le h)
  have := NNReal.coe_le_coe.2 hMH
  push_cast at this ⊢
  rw [pow_one, mul_assoc]
  exact mul_le_mul_of_nonneg_left this (by positivity)

theorem hTens_eq_zero {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n n₁ d : ℕ} (JX : Matrix (Fin n) (Fin n) E) (JW : Matrix (Fin d) (Fin d) (AE F E)) (ι : Matrix (Fin n) (Fin n₁) E)
    (y : Fin n → E) (hy : ∀ u, form σ JX (ι *ᵥ u) y = 0) (z : Matrix (Fin n₁) (Fin d) (AE F E)) (w : Fin d → AE F E) :
    hTens (cA σ) (incM F JX) JW (incM F ι * z) (Matrix.vecMulVec (incV F y) w) = 0 := by
  have h0 : ∀ a, ∑ i, ∑ k, incM F ι i a * incM F JX i k * cA σ (incV F y k) = 0 := by
    intro a
    have h1 := congrArg (inclR (F := F) (AF F)) (hy (Pi.single a 1))
    rw [map_zero] at h1
    rw [← h1]
    simp only [form, dotProduct, Matrix.mulVec_single_one, Matrix.col_apply, incM, incV, Matrix.map_apply,
      GlobalTheory.ThKCptBoundX.cA_inclR]
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Finset.mul_sum, mul_assoc]
  have h2 : hTens (cA σ) (incM F JX) JW (incM F ι * z) (Matrix.vecMulVec (incV F y) w) =
      ∑ a, ∑ j, ∑ l, (z a j * JW j l * cA σ (w l)) * ∑ i, ∑ k, incM F ι i a * incM F JX i k * cA σ (incV F y k) := by
    simp only [hTens, Matrix.mul_apply, Matrix.vecMulVec_apply, map_mul, Finset.sum_mul, Finset.mul_sum]
    calc _ = ∑ i, ∑ j, ∑ k, ∑ l, ∑ a, (z a j * JW j l * cA σ (w l)) * (incM F ι i a * incM F JX i k * cA σ (incV F y k)) :=
          Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ =>
            Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun a _ => by ring
      _ = ∑ j, ∑ l, ∑ a, ∑ i, ∑ k, (z a j * JW j l * cA σ (w l)) * (incM F ι i a * incM F JX i k * cA σ (incV F y k)) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => ?_
          refine (Finset.sum_congr rfl fun i _ => Finset.sum_comm).trans ?_
          refine Finset.sum_comm.trans (Finset.sum_congr rfl fun l _ => ?_)
          refine (Finset.sum_congr rfl fun i _ => Finset.sum_comm).trans ?_
          exact Finset.sum_comm
      _ = _ := by
          symm
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun j _ => Finset.sum_comm
  rw [h2]
  simp only [h0, mul_zero, Finset.sum_const_zero]

theorem main : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' →
    ∀ (d₂ : ℕ) (H : Plane E n d₂), (d₂ + 2 = n ∧ form σ X.J H.x H.x = 0 ∧ form σ X.J H.y H.y = 0 ∧ form σ X.J H.x H.y = 1 ∧
        (∀ u, form σ X.J (H.ι *ᵥ u) H.x = 0 ∧ form σ X.J (H.ι *ᵥ u) H.y = 0) ∧ Function.Injective H.ι.mulVec) →
    ∀ (V₁ : Spc F E d₂) (M₁ : Model σ V₁ W) (e : Fn F n d →ₗ[ℂ] Fn F d₂ d),
      V₁.J = H.ιᵀ * X.J * H.ι.map σ → M₁.IsGood B.ψ → IsEv B M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e →
    ∀ Φ ∈ schA F (Fin n × Fin d), ∀ g : UA σ X.J, ∀ K : Set (UA σ X.J), IsCompact K → K ⊆ unip σ X H →
      ∃ (C : ℝ) (k : ℕ), ∀ u ∈ K, ∀ h : UA σ W.J, ∀ N : ℕ, 1 ≤ N → ∃ m : ℕ, 1 ≤ m ∧ (m : ℝ) ≤ C * ((N : ℝ) * ht h) ^ k ∧
        ∀ w : Fin d → E, (∀ i, ∃ o : 𝓞 E, (N : E) * w i = o) → ∀ ξ : Fin d₂ × Fin d → F,
          e (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) (om (u, 1) (om (g, h) Φ))) (fun i => algebraMap F (AF F) (ξ i)) ≠ 0 →
          ∀ i, IsIntegral ℤ ((m : F) * ξ i) := by
  intro _ F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP d₂ H hH V₁ M₁ e _ _ hev Φ hΦ g K hK _
  have S := hP.weil.isUSplitting
  have hstd : IsStd B.ψ := hP.base.std
  obtain ⟨N₀, hN1, hinv⟩ := GlobalTheory.FinSuppHeis.heis_fix_finDiv F (Fin n × Fin d) B.ψ hstd.1 Φ hΦ
  obtain ⟨C, k, hC⟩ := exists_scale F E n d (Fin n × Fin d) (Fin d₂ × Fin d) M.co.e
    (fun i => incM F H.ι * M₁.co.e.symm (0, Pi.single i 1)) N₀ hN1
  obtain ⟨D, hD1, hD⟩ := GlobalTheory.FinSupp.DenStd.exists_den F
  have hcont : Continuous (fun u : UA σ X.J => (ht (u * g) : ℝ)) :=
    NNReal.continuous_coe.comp ((GlobalTheory.Grow.continuous_heightGL F).comp
      (continuous_subtype_val.comp (continuous_id.mul continuous_const)))
  obtain ⟨R, hR⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨D * (max C 0 * (max R 0) ^ k), k, fun u hu h N hN => ?_⟩
  obtain ⟨m, hm1, hmC, hmT⟩ := hC (u * g).1 h.1
  refine ⟨D * m, Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)), ?_, ?_⟩
  · push_cast
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left (hmC.trans ?_) (by positivity)
    have h1 : (ht (u * g) : ℝ) ≤ max R 0 := ((le_abs_self _).trans (hR u hu)).trans (le_max_left _ _)
    have h2 : (ht h : ℝ) ≤ (N : ℝ) * ht h :=
      le_mul_of_one_le_left (NNReal.coe_nonneg _) (by exact_mod_cast hN)
    show C * ((ht (u * g) : ℝ) * ht h) ^ k ≤ _
    rw [mul_assoc, ← mul_pow]
    refine mul_le_mul (le_max_left _ _) ?_ (by positivity) (le_max_right _ _)
    exact pow_le_pow_left₀ (by positivity) (mul_le_mul h1 h2 (NNReal.coe_nonneg _) (le_max_right _ _)) k
  · intro w _ ξ hξ i
    set p : UA σ X.J × UA σ W.J := (u * g, h) with hp
    have hom : om (u, 1) (om (g, h) Φ) = om p Φ := by
      rw [← Module.End.mul_apply, ← map_mul, hp, Prod.mk_mul_mk, one_mul]
    rw [hom] at hξ
    have hpΦ : om p Φ ∈ schA F (Fin n × Fin d) := S.pres p Φ hΦ
    set a₀ := Matrix.vecMulVec (incV F H.y) (incV F w) with ha₀
    have hΨ : M.co.rho B.ψ a₀ (om p Φ) ∈ schA F _ := GlobalTheory.HeisSchA.rho_mem_schA M B.ψ hstd a₀ _ hpΦ
    have key : ∀ a : 𝓞 F, B.ψ (GlobalTheory.FinSupp.finPart F (algebraMap F (AF F) ((a : F) * ((m : F) * ξ i)))) = 1 := by
      intro a
      set c : AF F := GlobalTheory.FinSupp.finPart F (algebraMap F (AF F) ((m : F) * (a : F))) with hc
      set y : Fin d₂ × Fin d → AF F := c • Pi.single i 1 with hy
      set z := M₁.co.e.symm (0, y) with hz
      set w' := incM F H.ι * z with hw'
      set w₁ := actAB (cA σ) p⁻¹ w' with hw
      have hwe : M.co.e w₁ = c • M.co.e (((((u * g).1)⁻¹ : GL (Fin n) (AF F ⊗[F] E)) : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) *
          (incM F H.ι * M₁.co.e.symm (0, Pi.single i 1)) *
          (((h.1⁻¹ : GL (Fin d) (AF F ⊗[F] E)) : Matrix (Fin d) (Fin d) (AF F ⊗[F] E)))ᵀ) := by
        rw [hw, hw', hz, hy, hp]
        rw [show ((0 : Fin d₂ × Fin d → AF F), c • Pi.single i (1 : AF F)) =
          c • ((0 : Fin d₂ × Fin d → AF F), Pi.single i (1 : AF F)) by simp]
        rw [LinearEquiv.map_smul, ← LinearEquiv.map_smul M.co.e]
        congr 1
        simp only [actAB, Prod.inv_mk, Subgroup.coe_inv]
        rw [Matrix.mul_smul, Matrix.mul_smul, Matrix.smul_mul]
      have hrho : M.co.rho B.ψ w₁ Φ = Φ := by
        unfold Darboux.rho
        apply hinv
        intro l
        rw [hwe]
        obtain ⟨h1, h2⟩ := hmT i l
        refine ⟨?_, ?_, ?_, ?_⟩
        · show (c * _).1 = 0
          exact zero_mul _
        · rw [Prod.smul_fst, Pi.smul_apply, smul_eq_mul]
          exact GlobalTheory.FinSupp.finDiv_finPart_mul h1 a
        · show (c * _).1 = 0
          exact zero_mul _
        · rw [Prod.smul_snd, Pi.smul_apply, smul_eq_mul]
          exact GlobalTheory.FinSupp.finDiv_finPart_mul h2 a
      have himpl := S.impl p w₁ Φ hΦ
      rw [hrho] at himpl
      have hact : actAB (cA σ) p w₁ = w' := by
        rw [hw]
        simp only [actAB, Prod.fst_inv, Prod.snd_inv, Subgroup.coe_inv]
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul,
          Matrix.mul_assoc, ← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.transpose_one,
          Matrix.mul_one]
      rw [hact] at himpl
      have horth : (M.co.e w').1 ⬝ᵥ (M.co.e a₀).2 - (M.co.e a₀).1 ⬝ᵥ (M.co.e w').2 = 0 := by
        rw [← M.co.form, symp, hw', ha₀, hTens_eq_zero X.J _ H.ι H.y (fun u => (hH.2.2.2.2.1 u).2), mul_zero, map_zero]
      have hcomm : M.co.rho B.ψ w' (M.co.rho B.ψ a₀ (om p Φ)) = M.co.rho B.ψ a₀ (om p Φ) := by
        conv_rhs => rw [himpl]
        simp only [Darboux.rho]
        rw [GlobalTheory.ThetaQuasiRat.schr_schr, GlobalTheory.ThetaQuasiRat.schr_schr, horth, ← neg_sub, horth, neg_zero, add_comm]
      have hheis := hev.Heisenberg₂ z _ hΨ
      have h11 : incM F (1 : Matrix (Fin d) (Fin d) E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
      rw [h11, Matrix.transpose_one, Matrix.mul_one, ← hw', hcomm] at hheis
      have hx := congrFun hheis (fun j => algebraMap F (AF F) (ξ j))
      rw [Darboux.rho.eq_1 M₁.co, hz, LinearEquiv.apply_symm_apply] at hx
      simp only [schr, zero_dotProduct, mul_zero, add_zero] at hx
      have h1 : B.ψ ((fun j => algebraMap F (AF F) (ξ j)) ⬝ᵥ y) = 1 := (mul_eq_right₀ hξ).1 hx.symm
      rw [hy, dotProduct_smul, dotProduct_single, smul_eq_mul, mul_one, hc, GlobalTheory.FinSupp.finPart_mul, ← map_mul] at h1
      convert h1 using 3
      ring
    have := hD B.ψ hstd _ key
    convert this using 1
    push_cast
    ring

end GlobalTheory.EvPtDenom
