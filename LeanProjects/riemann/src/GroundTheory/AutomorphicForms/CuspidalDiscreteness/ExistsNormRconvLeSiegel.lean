import Mathlib
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.RconvDiff
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.SiegelConj
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.SiegelCount
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.SiegelFinite

open MeasureTheory Set Filter Topology Function
open NumberField IsDedekindDomain
open scoped ENNReal Pointwise NumberField.AdeleRing

namespace GroundTheory.Automorphic

noncomputable section

namespace CuspidalSpectrum

open Reduction AutomorphicForm RightCosetSpace

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

local notation "Γ₁" => rationalGLOne K n

theorem exists_archProj_eq {g : normOneGL K n} (hg : (AdelicGLn.prodEquiv K n g).2 = 1) :
    ∃ C : ArchUnits K n, archProj K n C = g ∧
      (C : ArchMatrix K n) = archMat K n ((g : AdelicGLn.AdelicGL K n) :
        Matrix (Fin n) (Fin n) 𝔸[K]) := by
  set h := (AdelicGLn.prodEquiv K n g).1
  set C : ArchUnits K n := ((archEquiv K n h : archGroup K n) : ArchUnits K n)
  have hincl : archIncl K n C = g := by
    have h1 := infEmb_mul_finEmb (K := K) (n := n) g
    rw [hg, map_one, mul_one] at h1
    exact h1
  refine ⟨C, ?_, ?_⟩
  · rw [archProj_of_mem (hincl ▸ g.2)]
    exact Subtype.ext hincl
  · rfl

theorem prodEquiv_conj_snd {r : ℕ} (x : AdelicGLn.AdelicGL K n) (P : UPos n r → 𝔸[K])
    (hP : ∀ p, (P p).2 = 0) : (AdelicGLn.prodEquiv K n (x⁻¹ * unipGL P * x)).2 = 1 := by
  rw [map_mul, map_mul, map_inv, Prod.snd_mul, Prod.snd_mul, Prod.snd_inv, prodEquiv_unipGL_snd]
  have : (fun p => (P p).2) = 0 := funext hP
  rw [this, unipGL_zero, mul_one, inv_mul_cancel]

theorem coe_conj_unipGL {r : ℕ} (x : AdelicGLn.AdelicGL K n) (P : UPos n r → 𝔸[K]) :
    ((x⁻¹ * unipGL P * x : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) =
      1 + ((x⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) * blockEntry P *
        (x : Matrix (Fin n) (Fin n) 𝔸[K]) := by
  rw [Units.val_mul, Units.val_mul, coe_unipGL, unipMatrix, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_one, Units.inv_mul]

variable (K n) in

def conjArch {r : ℕ} (x : AdelicGLn.AdelicGL K n) : (UPos n r → 𝔸[K]) →+ ArchMatrix K n where
  toFun P := archMat K n (((x⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) *
    blockEntry P * (x : Matrix (Fin n) (Fin n) 𝔸[K]))
  map_zero' := by simp [blockEntry_zero]
  map_add' P Q := by simp [blockEntry_add, Matrix.mul_add, Matrix.add_mul]

theorem conjArch_mul_conjArch {r : ℕ} (x : AdelicGLn.AdelicGL K n) (P Q : UPos n r → 𝔸[K]) :
    conjArch K n x P * conjArch K n x Q = 0 := by
  change archMat K n _ * archMat K n _ = 0
  rw [← map_mul]
  have : ((x⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) * blockEntry P *
      (x : Matrix (Fin n) (Fin n) 𝔸[K]) * (((x⁻¹ : AdelicGLn.AdelicGL K n) :
        Matrix (Fin n) (Fin n) 𝔸[K]) * blockEntry Q * (x : Matrix (Fin n) (Fin n) 𝔸[K])) = 0 := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (x : Matrix (Fin n) (Fin n) 𝔸[K]), Units.mul_inv, Matrix.one_mul,
      ← Matrix.mul_assoc (blockEntry P), blockEntry_mul_blockEntry, Matrix.zero_mul,
      Matrix.mul_zero]
  rw [this, map_zero]

theorem exists_archProj_eq_conj {r : ℕ} (x : normOneGL K n) (P : UPos n r → 𝔸[K])
    (hP : ∀ p, (P p).2 = 0) :
    ∃ C : ArchUnits K n, archProj K n C = x⁻¹ * unipOne K n r P * x ∧
      (C : ArchMatrix K n) = 1 + conjArch K n (x : AdelicGLn.AdelicGL K n) P := by
  obtain ⟨C, hC1, hC2⟩ := exists_archProj_eq (g := x⁻¹ * unipOne K n r P * x)
    (prodEquiv_conj_snd (x : AdelicGLn.AdelicGL K n) P hP)
  refine ⟨C, hC1, ?_⟩
  rw [hC2]
  have h1 : ((x⁻¹ * unipOne K n r P * x : normOneGL K n) : AdelicGLn.AdelicGL K n) =
      (x : AdelicGLn.AdelicGL K n)⁻¹ * unipGL P * (x : AdelicGLn.AdelicGL K n) := rfl
  rw [h1, coe_conj_unipGL, map_add, map_one]
  rfl

theorem map_altPoint {V W : Type*} [AddCommGroup V] [AddCommGroup W] (φ : V →+ W) {k : ℕ}
    (y : Fin k → V) (ε : Fin k → Bool) : φ (altPoint y ε) = altPoint (fun i => φ (y i)) ε := by
  unfold altPoint
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp

variable (n) in

def truncInfHom (r : ℕ) : (UPos n r → 𝔸[K]) →+ (UPos n r → 𝔸[K]) where
  toFun := truncInf
  map_zero' := rfl
  map_add' _ _ := funext fun _ => Prod.ext rfl (add_zero (0 : FiniteAdeleRing (𝓞 K) K)).symm

@[simp] theorem truncInfHom_apply {r : ℕ} (s : UPos n r → 𝔸[K]) : truncInfHom n r s = truncInf s :=
  rfl

theorem encard_le_of_subset_biUnion {α ι : Type*} [DecidableEq ι] (s : Finset ι) (A : ι → Set α)
    {m : ℕ} (hm : ∀ i ∈ s, (A i).encard ≤ m) {B : Set α} (hB : B ⊆ ⋃ i ∈ s, A i) :
    B.encard ≤ s.card * m := by
  induction s using Finset.induction_on generalizing B with
  | empty =>
    have : B = ∅ := Set.subset_empty_iff.1 (by simpa using hB)
    simp [this]
  | insert a s ha ih =>
    have hB' : B ⊆ A a ∪ ⋃ i ∈ s, A i := by
      intro z hz
      obtain ⟨i, hi, hz⟩ := Set.mem_iUnion₂.1 (hB hz)
      rcases Finset.mem_insert.1 hi with rfl | hi
      · exact Or.inl hz
      · exact Or.inr (Set.mem_iUnion₂.2 ⟨i, hi, hz⟩)
    calc B.encard ≤ (A a ∪ ⋃ i ∈ s, A i).encard := Set.encard_le_encard hB'
      _ ≤ (A a).encard + (⋃ i ∈ s, A i).encard := Set.encard_union_le _ _
      _ ≤ m + s.card * m := add_le_add (hm a (Finset.mem_insert_self _ _))
          (ih (fun i hi => hm i (Finset.mem_insert_of_mem hi)) subset_rfl)
      _ = (insert a s).card * m := by
          rw [Finset.card_insert_of_notMem ha]
          push_cast
          ring

theorem encard_le_of_subset_mul {x : normOneGL K n} {Q V : Set (normOneGL K n)}
    (s : Finset (normOneGL K n)) (hQ : Q ⊆ ⋃ g ∈ s, (fun y => y * g) '' V) {m : ℕ}
    (hm : ∀ z : normOneGL K n, {γ : Γ₁ | γ • z ∈ (fun y => x * y) '' V}.encard ≤ m)
    (z : normOneGL K n) :
    {γ : Γ₁ | γ • z ∈ (fun y => x * y) '' Q}.encard ≤ s.card * m := by
  classical
  refine encard_le_of_subset_biUnion s (fun g => {γ : Γ₁ | γ • (z * g⁻¹) ∈ (fun y => x * y) '' V})
    (fun g _ => hm _) fun γ hγ => ?_
  obtain ⟨q, hq, hqz⟩ := hγ
  obtain ⟨g, hg, hqg⟩ := Set.mem_iUnion₂.1 (hQ hq)
  obtain ⟨v, hv, rfl⟩ := hqg
  refine Set.mem_iUnion₂.2 ⟨g, hg, v, hv, ?_⟩
  change x * v = γ • (z * g⁻¹)
  rw [Subgroup.smul_def, smul_eq_mul] at hqz ⊢
  rw [← mul_assoc, ← hqz, mul_assoc, mul_assoc, mul_inv_cancel, mul_one]

variable (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure] (ν : Measure (ArchUnits K n))
  [ν.IsHaarMeasure]

theorem exists_norm_rconv_le_siegel {β : ArchMatrix K n → ℝ}
    (hβ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) β) (hβc : HasCompactSupport β)
    (hβu : tsupport β ⊆ range (Units.val : ArchUnits K n → ArchMatrix K n))
    (U : Subgroup (AdelicGLn.integralFiniteGL K n))
    (hU : IsOpen (U : Set (AdelicGLn.integralFiniteGL K n)))
    (g : CompactlySupportedContinuousMap (normOneGL K n) ℂ)
    {ω : Set (AdelicGLn.AdelicGL K n)} (hω : IsCompact ω)
    (hωB : ω ⊆ ((adelicBorel : Subgroup (AdelicGLn.AdelicGL K n)) : Set (AdelicGLn.AdelicGL K n)))
    {t : ℝ} (ht : 0 < t) {r : ℕ} (hr : 0 < r) (hrn : r < n) :
    ∃ N : ℕ, ∀ k : ℕ, ∃ C : ℝ, ∀ φ ∈ cuspidalL2 μ, ∀ b ∈ ω, ∀ (ρ : Fin n → ℝ) (hρ : ∀ i, 0 < ρ i),
      (∀ i j : Fin n, (j : ℕ) = i + 1 → t * ρ j ≤ ρ i) →
      ∀ kk ∈ (maxCompact : Subgroup (AdelicGLn.AdelicGL K n)), ∀ x : normOneGL K n,
      (x : AdelicGLn.AdelicGL K n) = b * diagUnits n (fun i => posIdele (K := K) (ρ i) (hρ i)) * kk →
      ∀ R : ℝ, 1 ≤ R → (∀ i j : Fin n, i < j → ρ i / ρ j ≤ R) →
      ‖rconv Γ₁ μ (archConv ν hβ.continuous hβc hβu (finAvg U hU g)) φ x‖ ≤
        C * (ρ ⟨r, hrn⟩ / ρ ⟨r - 1, by omega⟩) ^ k * √(R ^ N) * ‖φ‖ := by
  obtain ⟨V₀, hV₀c, hV₀⟩ := exists_compact_mem_nhds (1 : normOneGL K n)
  obtain ⟨Cc, N, hCc⟩ := exists_encard_le_siegel hω ht hV₀c
  refine ⟨N, fun k => ?_⟩
  set h := finAvg U hU g
  set f := archConv ν hβ.continuous hβc hβu h
  obtain ⟨M, hM, hMconj⟩ := exists_natCast_conj_unipGL_mem U hU hω r
  obtain ⟨C₁, hC₁⟩ := exists_norm_archMat_conj_le hω hωB ht hr hrn
    (isCompact_scaledInfSet (K := K) M)
  set C₁' := max C₁ 0
  set R₁ := C₁' * t⁻¹
  obtain ⟨c, hc⟩ := exists_norm_sum_altSign_archConvFun_le ν hβ hβc hβu h k R₁
  set c' := max c 0
  have h𝒞 := isCompact_unipBall (K := K) (n := n) (k * R₁)
  set Q := archProj K n '' unipBall (K := K) (n := n) (k * R₁) * tsupport (f : normOneGL K n → ℂ)
  have hQ : IsCompact Q := (h𝒞.image continuous_archProj).mul f.hasCompactSupport
  obtain ⟨s, -, hs⟩ := hQ.elim_nhds_subcover (fun g => (fun y => y * g) '' V₀) fun g _ => by
    have := (Homeomorph.mulRight g).isOpenMap.image_mem_nhds hV₀
    simpa using this
  refine ⟨c' * C₁' ^ k * √(μ.real Q * (s.card * max Cc 0)), ?_⟩
  intro φ hφ b hb ρ hρ hsieg kk hkk x hx R hR1 hR
  obtain ⟨m₀, hmC₀, hm₀⟩ := hCc b hb ρ hρ hsieg kk hkk x hx R hR1 hR
  obtain ⟨m, hmdef⟩ : ∃ m : ℕ, m = s.card * m₀ := ⟨_, rfl⟩
  have hm : ∀ z : normOneGL K n, {γ : Γ₁ | γ • z ∈ (fun y => x * y) '' Q}.encard ≤ m := by
    intro z
    have := encard_le_of_subset_mul s hs hm₀ z
    rw [hmdef]
    exact_mod_cast this
  have hmC : (m : ℝ) ≤ s.card * Cc * R ^ N := by
    rw [hmdef, Nat.cast_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left hmC₀ (Nat.cast_nonneg _)
  set gain := ρ ⟨r, hrn⟩ / ρ ⟨r - 1, by omega⟩
  have hgain0 : 0 ≤ gain := div_nonneg (hρ _).le (hρ _).le
  have hgain : gain ≤ t⁻¹ := by
    have h1 := hsieg ⟨r - 1, by omega⟩ ⟨r, hrn⟩ (by simp; omega)
    rw [div_le_iff₀ (hρ _), ← div_eq_inv_mul, le_div_iff₀ ht, mul_comm]
    exact h1
  have hc'0 : 0 ≤ c' := le_max_right _ _
  have hC₁'0 : 0 ≤ C₁' := le_max_right _ _
  set b₀ := c' * (C₁' * gain) ^ k
  have hb₀ : 0 ≤ b₀ := mul_nonneg hc'0 (pow_nonneg (mul_nonneg hC₁'0 hgain0) _)
  have hfinal : ‖rconv Γ₁ μ f φ x‖ ≤ b₀ * √(μ.real Q * m) * ‖φ‖ := by
    refine norm_rconv_le_of_altSum_inf μ f hφ hr hrn hM x ?_ k ?_
    · intro z hz1 hz2 w
      obtain ⟨u, hu⟩ := hMconj b hb ρ hρ kk hkk z hz1 hz2
      have hxu : x⁻¹ * unipOne K n r z * x = finOne K n (u : AdelicGLn.integralFiniteGL K n) := by
        refine Subtype.ext ?_
        change (x : AdelicGLn.AdelicGL K n)⁻¹ * unipGL z * (x : AdelicGLn.AdelicGL K n) =
          finEmb K n _
        rw [hx]
        exact hu
      rw [hxu, ← map_inv, ← Subgroup.coe_inv]
      exact archConvFun_finOne_mul ν h _ (fun y => finAvgFun_finOne_mul U hU g u⁻¹ y) w
    · intro y hy
      set Y : Fin k → ArchMatrix K n :=
        fun i => conjArch K n (x : AdelicGLn.AdelicGL K n) (truncInf (y i))
      have hYY : ∀ i j, Y i * Y j = 0 := fun i j => conjArch_mul_conjArch _ _ _
      have hYn : ∀ i, ‖Y i‖ ≤ C₁' * gain := by
        intro i
        have h1 := hC₁ b hb ρ hρ hsieg kk hkk (truncInf (y i)) (fun p => rfl)
          (fun p => infinite_mem_scaledInfSet hM (hy i) p)
        have h2 : Y i = archMat K n ((((b * diagUnits n (fun i => posIdele (K := K) (ρ i) (hρ i)) *
            kk)⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) *
            blockEntry (truncInf (y i)) * ((b * diagUnits n (fun i => posIdele (K := K) (ρ i)
              (hρ i)) * kk : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])) := by
          simp only [Y, conjArch, AddMonoidHom.coe_mk, ZeroHom.coe_mk, hx]
        rw [h2]
        exact h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hgain0)
      have hYR : ∀ i, ‖Y i‖ ≤ R₁ := fun i =>
        (hYn i).trans (mul_le_mul_of_nonneg_left hgain hC₁'0)
      have hex : ∀ ε : Fin k → Bool, ∃ C : ArchUnits K n,
          archProj K n C = x⁻¹ * unipOne K n r (truncInf (altPoint y ε)) * x ∧
            (C : ArchMatrix K n) = 1 + altPoint Y ε := by
        intro ε
        obtain ⟨C, hC1, hC2⟩ := exists_archProj_eq_conj x (truncInf (altPoint y ε)) fun p => rfl
        refine ⟨C, hC1, ?_⟩
        rw [hC2, ← truncInfHom_apply, map_altPoint (truncInfHom n r),
          map_altPoint (conjArch K n (x : AdelicGLn.AdelicGL K n))]
        rfl
      choose Cε hCε1 hCε2 using hex
      have hsum : altSum k (fun s => rconv Γ₁ μ f φ (unipOne K n r (truncInf s) * x)) y 0 =
          ∑ ε, (altSign ε : ℂ) * rconv Γ₁ μ f φ (x * archProj K n (Cε ε)) := by
        rw [altSum_eq_sum]
        refine Finset.sum_congr rfl fun ε _ => ?_
        rw [zero_add, hCε1 ε, zsmul_eq_mul]
        have : x * (x⁻¹ * unipOne K n r (truncInf (altPoint y ε)) * x) =
            unipOne K n r (truncInf (altPoint y ε)) * x := by group
        rw [this]
      rw [hsum]
      have hb' : ∀ w, ‖∑ ε, (altSign ε : ℂ) * f ((archProj K n (Cε ε))⁻¹ * w)‖ ≤ b₀ := by
        intro w
        refine (hc Y hYY hYR Cε hCε2 w).trans ?_
        have hprod : ∏ i, ‖Y i‖ ≤ (C₁' * gain) ^ k := by
          rw [← Fin.prod_const]
          exact Finset.prod_le_prod (fun i _ => norm_nonneg _) fun i _ => hYn i
        calc c * ∏ i, ‖Y i‖ ≤ c' * ∏ i, ‖Y i‖ :=
              mul_le_mul_of_nonneg_right (le_max_left _ _)
                (Finset.prod_nonneg fun i _ => norm_nonneg _)
          _ ≤ b₀ := mul_le_mul_of_nonneg_left hprod hc'0
      have hmem : ∀ ε, Cε ε ∈ unipBall (K := K) (n := n) (k * R₁) := fun ε =>
        mem_unipBall_of_val_eq hYY hYR (hCε2 ε)
      have hsq := enorm_sum_altSign_rconv_sq_le μ f φ x h𝒞 Cε hmem hb' hm
      have hA : ENNReal.ofReal b₀ ^ 2 * μ Q * (m : ℝ≥0∞) ≠ ⊤ :=
        ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) hQ.measure_lt_top.ne) (by simp)
      have hle := norm_le_of_enorm_sq_le hA (by rw [mul_assoc]; exact hsq)
      refine hle.trans (le_of_eq ?_)
      congr 1
      rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hb₀,
        ENNReal.toReal_natCast, Real.sqrt_mul (by positivity), Real.sqrt_mul' _ (by positivity),
        Real.sqrt_sq hb₀, measureReal_def, mul_assoc, Real.sqrt_mul ENNReal.toReal_nonneg]
  refine hfinal.trans ?_
  have hμQ : 0 ≤ μ.real Q := measureReal_nonneg
  have hm' : (m : ℝ) ≤ s.card * max Cc 0 * R ^ N :=
    hmC.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_max_left _ _)
      (Nat.cast_nonneg _)) (pow_nonneg (by linarith) _))
  have hsqrt : √(μ.real Q * m) ≤ √(μ.real Q * (s.card * max Cc 0)) * √(R ^ N) := by
    rw [← Real.sqrt_mul (mul_nonneg hμQ (mul_nonneg (Nat.cast_nonneg _) (le_max_right _ _)))]
    refine Real.sqrt_le_sqrt ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hm' hμQ
  calc b₀ * √(μ.real Q * m) * ‖φ‖
      ≤ b₀ * (√(μ.real Q * (s.card * max Cc 0)) * √(R ^ N)) * ‖φ‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsqrt hb₀) (norm_nonneg _)
    _ = c' * C₁' ^ k * √(μ.real Q * (s.card * max Cc 0)) * gain ^ k * √(R ^ N) * ‖φ‖ := by
        simp only [b₀, mul_pow]
        ring

end CuspidalSpectrum

end

end GroundTheory.Automorphic
