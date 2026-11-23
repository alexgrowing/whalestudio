import Mathlib
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsHeight
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.DecayUniform
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.TorusReduction

open NumberField IsDedekindDomain Topology Filter Set MeasureTheory
open scoped NumberField.AdeleRing Pointwise

namespace GroundTheory.Automorphic

noncomputable section

namespace CuspidalSpectrum

open AutomorphicForm

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

theorem conj_unipGL_eq_archExp {r : ℕ} (x : AdelicGLn.AdelicGL K n) (P : UPos n r → 𝔸[K])
    (hP : ∀ p, (P p).2 = 0) : x⁻¹ * unipGL P * x = archExp (conjArch K n x P) := by
  set g := x⁻¹ * unipGL P * x with hg
  have hfin : finPart g = 1 := prodEquiv_conj_snd x P hP
  rw [← infEmb_archPart_mul_finEmb_finPart g, hfin, map_one, mul_one, archExp]
  congr 1
  refine Subtype.ext (Units.ext ?_)
  rw [coe_expG_top, exp_eq_one_add_of_mul_self_eq_zero (conjArch_mul_conjArch x P P)]
  show archMat K n ((g : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) = _
  rw [hg, coe_conj_unipGL, map_add, map_one]
  rfl

theorem exists_norm_le_siegel_root {φ : AdelicGLn.AdelicGL K n → ℂ} (hφ : φ ∈ cuspForms K n)
    {ω : Set (AdelicGLn.AdelicGL K n)} (hω : IsCompact ω)
    (hωB : ω ⊆ ((Reduction.adelicBorel : Subgroup (AdelicGLn.AdelicGL K n)) :
      Set (AdelicGLn.AdelicGL K n)))
    {t : ℝ} (ht : 0 < t) {r : ℕ} (hr : 0 < r) (hrn : r < n) :
    ∃ N : ℕ, ∀ k : ℕ, ∃ C : ℝ, ∀ b ∈ ω, ∀ (ρ : Fin n → ℝ) (hρ : ∀ i, 0 < ρ i),
      (∀ i j : Fin n, (j : ℕ) = i + 1 → t * ρ j ≤ ρ i) →
      ∀ kk ∈ (Reduction.maxCompact : Subgroup (AdelicGLn.AdelicGL K n)),
      ∀ x : AdelicGLn.AdelicGL K n,
      x = b * Reduction.diagUnits n (fun i => Reduction.posIdele (K := K) (ρ i) (hρ i)) * kk →
      ‖φ x‖ ≤ C * (ρ ⟨r, hrn⟩ / ρ ⟨r - 1, by omega⟩) ^ k * height x ^ N := by
  obtain ⟨N, hN⟩ := exists_norm_diffSum_le hφ.1
  refine ⟨N, fun k => ?_⟩
  obtain ⟨U₀, -, hU₀⟩ := exists_openSubgroup_rightInvariant hφ.1.isSmooth hφ.1.isKFinite
  set U : Subgroup (AdelicGLn.integralFiniteGL K n) :=
    (U₀ : Subgroup (AdelicGLn.FiniteAdelicGL K n)).subgroupOf (AdelicGLn.integralFiniteGL K n)
  have hU : IsOpen (U : Set (AdelicGLn.integralFiniteGL K n)) :=
    U₀.isOpen.preimage continuous_subtype_val
  obtain ⟨M, hM, hMconj⟩ := exists_natCast_conj_unipGL_mem U hU hω r
  obtain ⟨C₁, hC₁⟩ := exists_norm_archMat_conj_le hω hωB ht hr hrn
    (isCompact_scaledInfSet (K := K) M)
  set C₁' := max C₁ 0
  have hC₁'0 : 0 ≤ C₁' := le_max_right _ _
  obtain ⟨C, hC⟩ := hN k (C₁' * t⁻¹)
  refine ⟨max C 0 * C₁' ^ k, ?_⟩
  intro b hb ρ hρ hsieg kk hkk x hx
  set gain := ρ ⟨r, hrn⟩ / ρ ⟨r - 1, by omega⟩
  have hgain0 : 0 ≤ gain := div_nonneg (hρ _).le (hρ _).le
  have hgain : gain ≤ t⁻¹ := by
    have h1 := hsieg ⟨r - 1, by omega⟩ ⟨r, hrn⟩ (by simp; omega)
    rw [div_le_iff₀ (hρ _), ← div_eq_inv_mul, le_div_iff₀ ht, mul_comm]
    exact h1
  set H : (UPos n r → 𝔸[K]) → ℂ := fun s => φ (unipGL s * x) with hH
  have hHc : Continuous H := hφ.1.continuous.comp (continuous_unipGL.mul continuous_const)
  have hper : ∀ ξ ∈ unipLattice K n r, ∀ s, H (ξ + s) = H s := fun ξ hξ s =>
    hφ.1.isLeftInvariant.unipGL_vadd x ⟨ξ, hξ⟩ s
  have hD := isAddFundamentalDomain_scaledUnipFD (K := K) (n := n) (r := r) hM
  obtain ⟨Cc, hCc, hDC⟩ := exists_isCompact_superset_scaledUnipFD (K := K) (n := n) r hM
  have hint : ∀ t', IntegrableOn (fun y => H (t' + y)) (scaledUnipFD K n r M) (unipMeasure K n r) :=
    fun t' => ((hHc.comp (continuous_const.add continuous_id)).continuousOn.integrableOn_compact
      hCc).mono_set hDC
  have hmean : ∫ y in scaledUnipFD K n r M, H y ∂unipMeasure K n r = 0 := by
    rw [hD.setIntegral_eq isAddFundamentalDomain_unipFundamentalDomain fun ξ s => hper ξ ξ.2 s]
    exact hφ.2 r hr hrn x
  have h0 := norm_le_of_forall_altSum_le hD (unipMeasure_scaledUnipFD hM) k H hper hint hmean
    (max C 0 * (C₁' * gain) ^ k * height x ^ N) ?_
  · have hH0 : H 0 = φ x := by simp [hH, unipGL_zero]
    rw [hH0] at h0
    refine h0.trans (le_of_eq ?_)
    rw [mul_pow]
    ring
  intro y hy
  set Y : Fin k → ArchMatrix K n := fun i => conjArch K n x (truncInf (y i)) with hYdef
  have hYY : ∀ i j, Y i * Y j = 0 := fun i j => conjArch_mul_conjArch _ _ _
  have hYn : ∀ i, ‖Y i‖ ≤ C₁' * gain := by
    intro i
    have h1 := hC₁ b hb ρ hρ hsieg kk hkk (truncInf (y i)) (fun p => rfl)
      (fun p => infinite_mem_scaledInfSet hM (hy i) p)
    have h2 : Y i = archMat K n ((((b * Reduction.diagUnits n (fun i =>
        Reduction.posIdele (K := K) (ρ i) (hρ i)) * kk)⁻¹ : AdelicGLn.AdelicGL K n) :
          Matrix (Fin n) (Fin n) 𝔸[K]) * blockEntry (truncInf (y i)) *
        ((b * Reduction.diagUnits n (fun i => Reduction.posIdele (K := K) (ρ i) (hρ i)) * kk :
          AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])) := by
      simp only [hYdef, conjArch, AddMonoidHom.coe_mk, ZeroHom.coe_mk, hx]
    rw [h2]
    exact h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hgain0)
  have hYT : ∀ i, ‖Y i‖ ≤ C₁' * t⁻¹ := fun i =>
    (hYn i).trans (mul_le_mul_of_nonneg_left hgain hC₁'0)
  have key : ∀ ε : Fin k → Bool, H (0 + altPoint y ε) = φ (x * archExp (altPoint Y ε)) := by
    intro ε
    rw [zero_add]
    set P := altPoint y ε
    obtain ⟨u, hu⟩ := hMconj b hb ρ hρ kk hkk (truncFin P) (fun p => rfl) fun p => by
      obtain ⟨a, ha, hPa⟩ := exists_finite_altPoint_eq_natCast_mul hM y hy ε p
      exact ⟨a, ha, hPa⟩
    rw [← hx] at hu
    have hsplit : unipGL P * x = unipGL (truncInf P) * x * (x⁻¹ * unipGL (truncFin P) * x) := by
      rw [show unipGL P = unipGL (truncInf P) * unipGL (truncFin P) by
        rw [← unipGL_add, truncInf_add_truncFin]]
      group
    have hinf : unipGL (truncInf P) * x = x * (x⁻¹ * unipGL (truncInf P) * x) := by group
    have hY : conjArch K n x (truncInf P) = altPoint Y ε := by
      rw [← truncInfHom_apply, map_altPoint (truncInfHom n r), map_altPoint (conjArch K n x)]
      rfl
    simp only [hH]
    rw [hsplit, hu, hU₀ _ ((u : AdelicGLn.integralFiniteGL K n) : AdelicGLn.FiniteAdelicGL K n)
      (Subgroup.mem_subgroupOf.1 u.2), hinf, conj_unipGL_eq_archExp x _ fun p => rfl, hY]
  have hsum : altSum k H y 0 = diffSum φ x Y := by
    rw [altSum_eq_sum, diffSum]
    refine Finset.sum_congr rfl fun ε _ => ?_
    rw [key ε, zsmul_eq_mul]
  rw [hsum]
  refine (hC x Y hYY hYT).trans ?_
  have hprod : ∏ i, ‖Y i‖ ≤ (C₁' * gain) ^ k := by
    rw [← Fin.prod_const]
    exact Finset.prod_le_prod (fun i _ => norm_nonneg _) fun i _ => hYn i
  have hh := pow_nonneg (height_pos x).le N
  calc C * (∏ i, ‖Y i‖) * height x ^ N ≤ max C 0 * (∏ i, ‖Y i‖) * height x ^ N :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _)
          (Finset.prod_nonneg fun i _ => norm_nonneg _)) hh
    _ ≤ max C 0 * (C₁' * gain) ^ k * height x ^ N :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hprod (le_max_right _ _)) hh

theorem exists_norm_le_height_pow_neg_siegel {φ : AdelicGLn.AdelicGL K n → ℂ}
    (hφ : φ ∈ cuspForms K n) {ω : Set (AdelicGLn.AdelicGL K n)} (hω : IsCompact ω)
    (hωB : ω ⊆ ((Reduction.adelicBorel : Subgroup (AdelicGLn.AdelicGL K n)) :
      Set (AdelicGLn.AdelicGL K n)))
    {t : ℝ} (ht : 0 < t) (N' : ℕ) :
    ∃ C : ℝ, ∀ b ∈ ω, ∀ (ρ : Fin n → ℝ) (hρ : ∀ i, 0 < ρ i),
      (∀ i j : Fin n, (j : ℕ) = i + 1 → t * ρ j ≤ ρ i) →
      ∀ kk ∈ (Reduction.maxCompact : Subgroup (AdelicGLn.AdelicGL K n)),
      ∀ x : AdelicGLn.AdelicGL K n, x ∈ Reduction.normOneGL K n →
      x = b * Reduction.diagUnits n (fun i => Reduction.posIdele (K := K) (ρ i) (hρ i)) * kk →
      ‖φ x‖ ≤ C * (height x ^ N')⁻¹ := by
  obtain ⟨C₀, N₀, hC₀⟩ := hφ.1.hasModerateGrowth
  obtain ⟨Ch, hCh0, hCh⟩ := exists_height_le_normOne (K := K) (n := n) hω
  set e := 2 * Fintype.card (InfinitePlace K)
  set τ := (max 1 t⁻¹) ^ n with hτ
  have hτ1 : 1 ≤ τ := one_le_pow₀ (le_max_left _ _)
  set D := max (Ch * τ ^ e) 1 with hD
  have hD1 : 1 ≤ D := le_max_right _ _
  have hD0 : 0 ≤ D := le_trans zero_le_one hD1
  have hroot := fun (r : ℕ) (hr : 0 < r) (hrn : r < n) => exists_norm_le_siegel_root hφ hω hωB ht hr hrn
  choose Nf hNf using hroot
  have hroot2 := fun (r : ℕ) (hr : 0 < r) (hrn : r < n) => hNf r hr hrn (n * e * (Nf r hr hrn + N'))
  choose Cf hCf using hroot2
  set S : ℝ := ∑ r : Fin n, if h : 0 < (r : ℕ) then
    max (Cf r h r.2) 0 * D ^ (Nf r h r.2 + N') else 0 with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun r _ => by
    split_ifs
    · exact mul_nonneg (le_max_right _ _) (pow_nonneg hD0 _)
    · exact le_rfl
  have hSle : ∀ (r : ℕ) (hr : 0 < r) (hrn : r < n),
      max (Cf r hr hrn) 0 * D ^ (Nf r hr hrn + N') ≤ S := by
    intro r hr hrn
    have h1 := Finset.single_le_sum (f := fun r : Fin n => if h : 0 < (r : ℕ) then
      max (Cf r h r.2) 0 * D ^ (Nf r h r.2 + N') else 0)
      (fun r _ => by
        split_ifs
        · exact mul_nonneg (le_max_right _ _) (pow_nonneg hD0 _)
        · exact le_rfl) (Finset.mem_univ ⟨r, hrn⟩)
    simpa only [hr, dif_pos] using h1
  set C₀' := |C₀| * D ^ (N₀ + N')
  have hC₀'0 : 0 ≤ C₀' := mul_nonneg (abs_nonneg _) (pow_nonneg hD0 _)
  refine ⟨C₀' + S, ?_⟩
  intro b hb ρ hρ hsieg kk hkk x hx1 hx
  have hh0 : 0 < height x := height_pos x
  have hhN' : 0 < height x ^ N' := pow_pos hh0 _

  have hsmall : height x ≤ D → ‖φ x‖ ≤ (C₀' + S) * (height x ^ N')⁻¹ := by
    intro hxD
    have h1 : ‖φ x‖ ≤ |C₀| * D ^ N₀ :=
      (hC₀ x).trans (mul_le_mul (le_abs_self _) (pow_le_pow_left₀ hh0.le hxD _)
        (pow_nonneg hh0.le _) (abs_nonneg _))
    have h2 : |C₀| * D ^ N₀ ≤ C₀' * (height x ^ N')⁻¹ := by
      rw [le_mul_inv_iff₀ hhN']
      simp only [C₀', pow_add, mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hh0.le hxD _) (pow_nonneg hD0 _)) (abs_nonneg _)
    refine h1.trans (h2.trans ?_)
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hS0) (inv_nonneg.2 hhN'.le)

  have hheight : ∀ R : ℝ, 1 ≤ R → (∀ i j : Fin n, i < j → ρ i / ρ j ≤ R) →
      height x ≤ D * R ^ e := by
    intro R hR1 hR
    have hall : ∀ i j : Fin n, ρ i / ρ j ≤ τ * R := fun i j =>
      siegel_div_le_mul ht hρ hsieg hR1 hR i j
    have h1 := hCh b hb ρ hρ kk hkk x hx1 hx (τ * R) (one_le_mul_of_one_le_of_one_le hτ1 hR1) hall
    calc height x ≤ Ch * (τ * R) ^ e := h1
      _ = Ch * τ ^ e * R ^ e := by rw [mul_pow]; ring
      _ ≤ D * R ^ e := mul_le_mul_of_nonneg_right (le_max_left _ _)
          (pow_nonneg (le_trans zero_le_one hR1) _)
  by_cases hn : 2 ≤ n
  · obtain ⟨r, hr, hrn, hratio⟩ := exists_le_max_pow hn ρ hρ
    set α := ρ ⟨r - 1, by omega⟩ / ρ ⟨r, hrn⟩ with hα
    have hα0 : 0 < α := div_pos (hρ _) (hρ _)
    rcases le_or_gt α 1 with hα1 | hα1
    · refine hsmall ?_
      have := hheight 1 le_rfl fun i j hij => (hratio i j hij).trans (by
        rw [max_eq_left hα1, one_pow])
      simpa using this
    · have hM : max 1 α = α := max_eq_right hα1.le
      set A := α ^ (n * e) with hA
      have hA1 : 1 ≤ A := one_le_pow₀ hα1.le
      have hxA : height x ≤ D * A := by
        have := hheight (α ^ n) (one_le_pow₀ hα1.le) fun i j hij =>
          (hratio i j hij).trans (by rw [hM])
        rwa [← pow_mul] at this
      set k := n * e * (Nf r hr hrn + N')
      have h1 := hCf r hr hrn b hb ρ hρ hsieg kk hkk x hx
      have hgain : ρ ⟨r, hrn⟩ / ρ ⟨r - 1, by omega⟩ = α⁻¹ := by rw [hα, inv_div]
      rw [hgain] at h1
      have hk : (α⁻¹) ^ k = (A ^ (Nf r hr hrn + N'))⁻¹ := by
        rw [inv_pow, hA, ← pow_mul]
      rw [hk] at h1
      have hApos : 0 < A := lt_of_lt_of_le one_pos hA1
      have hAN : 0 < A ^ N' := pow_pos hApos _
      have hhN : height x ^ Nf r hr hrn ≤ D ^ Nf r hr hrn * A ^ Nf r hr hrn := by
        rw [← mul_pow]; exact pow_le_pow_left₀ hh0.le hxA _
      have hhN'' : height x ^ N' ≤ D ^ N' * A ^ N' := by
        rw [← mul_pow]; exact pow_le_pow_left₀ hh0.le hxA _
      set Cr := max (Cf r hr hrn) 0
      have hCr0 : 0 ≤ Cr := le_max_right _ _
      calc ‖φ x‖ ≤ Cf r hr hrn * (A ^ (Nf r hr hrn + N'))⁻¹ * height x ^ Nf r hr hrn := h1
        _ ≤ Cr * (A ^ (Nf r hr hrn + N'))⁻¹ * (D ^ Nf r hr hrn * A ^ Nf r hr hrn) := by
            refine mul_le_mul (mul_le_mul_of_nonneg_right (le_max_left _ _)
              (inv_nonneg.2 (pow_nonneg hApos.le _))) hhN (pow_nonneg hh0.le _)
              (mul_nonneg hCr0 (inv_nonneg.2 (pow_nonneg hApos.le _)))
        _ = Cr * D ^ Nf r hr hrn * (A ^ N')⁻¹ := by
            rw [pow_add]; field_simp
        _ ≤ Cr * D ^ Nf r hr hrn * (D ^ N' * (height x ^ N')⁻¹) := by
            refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hCr0 (pow_nonneg hD0 _))
            rw [inv_le_iff_one_le_mul₀ hAN, mul_right_comm, ← div_eq_mul_inv, le_div_iff₀ hhN',
              one_mul]
            exact hhN''
        _ = Cr * D ^ (Nf r hr hrn + N') * (height x ^ N')⁻¹ := by rw [pow_add]; ring
        _ ≤ (C₀' + S) * (height x ^ N')⁻¹ := by
            refine mul_le_mul_of_nonneg_right ?_ (inv_nonneg.2 hhN'.le)
            exact (hSle r hr hrn).trans (le_add_of_nonneg_left hC₀'0)
  · refine hsmall ?_
    have := hheight 1 le_rfl fun i j hij => by
      exfalso
      have : (i : ℕ) < j := hij
      omega
    simpa using this

theorem exists_norm_le_of_mem_cuspForms {φ : AdelicGLn.AdelicGL K n → ℂ}
    (hφ : φ ∈ cuspForms K n) : ∃ C : ℝ, ∀ x ∈ Reduction.normOneGL K n, ‖φ x‖ ≤ C := by
  obtain ⟨ω, hω, hωB, t, ht, hsieg⟩ := Reduction.exists_siegelSet (K := K) n
  obtain ⟨C, hC⟩ := exists_norm_le_height_pow_neg_siegel hφ hω hωB ht 0
  refine ⟨C, fun x hx => ?_⟩
  obtain ⟨γ, hγ⟩ := hsieg x
  obtain ⟨b, hb, a, ⟨ρ, hρ, hs, rfl⟩, kk, hkk, hxe⟩ := hγ
  have hγx : AdelicGLn.diagonal K n γ * x ∈ Reduction.normOneGL K n :=
    mul_mem (Reduction.rationalGL_le_normOneGL ⟨γ, rfl⟩) hx
  have h := hC b hb ρ hρ hs kk hkk _ hγx hxe
  rwa [pow_zero, inv_one, mul_one, hφ.1.isLeftInvariant γ x] at h

end CuspidalSpectrum

end

end GroundTheory.Automorphic
