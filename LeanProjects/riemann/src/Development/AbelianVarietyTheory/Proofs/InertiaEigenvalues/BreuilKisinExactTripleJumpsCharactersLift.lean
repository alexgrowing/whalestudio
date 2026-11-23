import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrimePowSmulMemRangeOfFiniteLengthCokerStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralLeftInverseOfPhiModuleExactTripleStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinJumpsSubsetOfSplitMonoStatement

noncomputable section

open PowerSeries GlobalTheory.BK Matrix

namespace GlobalTheory.ExactTripleBK

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a]
  [TameDescentExponentData K l e a] {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem smul_eq_of_retr {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ} (F : GlobalTheory.BK.Hom P Q) {n : ℕ}
    {τ : ZMod a} {Λ : Matrix ι κ K⟦X⟧} (h : Λ * F.mat τ = (l : K) ^ n • (1 : Matrix ι ι K⟦X⟧))
    (v : Vec K a ι) : (l : K) ^ n • v τ = Λ *ᵥ F.app v τ := by
  rw [Hom.app_apply, Matrix.mulVec_mulVec, h, Matrix.smul_mulVec, Matrix.one_mulVec]

theorem onPol_injective {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ} (F : GlobalTheory.BK.Hom P Q) (n : ℕ)
    (hΛ : ∀ τ : ZMod a, ∃ Λ : Matrix ι κ K⟦X⟧, (∀ i k, Λ i k ∈ A O K) ∧
      Λ * F.mat τ = (l : K) ^ n • (1 : Matrix ι ι K⟦X⟧)) :
    Function.Injective F.onPol := by
  refine (injective_iff_map_eq_zero F.onPol).2 fun w hw => ?_
  obtain ⟨v, rfl⟩ := P.Man.mkQ_surjective w
  have hv : F.app v ∈ Q.Man := Q.cls_eq_zero_iff.1 hw
  change P.cls v = 0
  rw [PhiMod.cls_eq_zero_iff]
  have h1 : (l : K) ^ n • v ∈ P.Man := by
    refine P.mem_Man.2 (mem_tot.2 fun τ i => ?_)
    obtain ⟨Λ, hΛA, hΛF⟩ := hΛ τ
    have hFv := mem_tot.1 (Q.mem_Man.1 hv) τ
    have h2 : ((l : K) ^ n • v) τ = Λ *ᵥ F.app v τ := by
      rw [Pi.smul_apply]
      exact smul_eq_of_retr F hΛF v
    rw [h2]
    exact Subalgebra.sum_mem _ fun k _ => Subalgebra.mul_mem _ (A_le_Rpi l e (hΛA i k)) (hFv k)
  have h3 := P.Man.smul_mem ((l : K) ^ n)⁻¹ h1
  rwa [smul_smul, inv_mul_cancel₀ (pow_ne_zero _ (l_ne_zero l)), one_smul] at h3

omit [CompleteSpace K] in

theorem onD_actD {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ} {Δ₁ : Descent P} {Δ₂ : Descent Q}
    (F : Descent.Hom Δ₁ Δ₂) (g : TameGal K l e a) (d : P.D) :
    F.onD (Δ₁.actD g d) = Δ₂.actD g (F.onD d) := by
  have h1 : Δ₁.actD g d = red (Δ₁.act g (cst d)) := rfl
  rw [h1, ← Hom.red_app, F.app_act, Δ₂.red_act, Hom.red_app, red_cst]

theorem map_constantCoeff_smul_one (c : K) :
    (c • (1 : Matrix ι ι K⟦X⟧)).map constantCoeff = c • (1 : Matrix ι ι K) := by
  ext i j
  rw [Matrix.map_apply, Matrix.smul_apply, Matrix.smul_apply, ← coeff_zero_eq_constantCoeff_apply, coeff_smul]
  by_cases h : i = j <;> simp [h, Matrix.one_apply]

theorem chars_subset {η H : ℕ} {D₀ : BKDat O K l e a ι η H} {D₁ : BKDat O K l e a κ η H}
    (F : BKHom D₀ D₁) (n : ℕ)
    (hΛ : ∀ τ : ZMod a, ∃ Λ : Matrix ι κ K⟦X⟧, (∀ i k, Λ i k ∈ A O K) ∧
      Λ * F.mat τ = (l : K) ^ n • (1 : Matrix ι ι K⟦X⟧)) (τ : ZMod a) :
    D₀.desc.chars τ ⊆ D₁.desc.chars τ := by
  rintro c ⟨d, hd, hc⟩
  refine ⟨F.onD d, fun h0 => hd ?_, fun ζ => ?_⟩
  · obtain ⟨Λ, -, hΛF⟩ := hΛ τ
    have h1 : Λ.map constantCoeff *ᵥ F.onD d τ = (l : K) ^ n • d τ := by
      rw [show F.onD d τ = (F.mat τ).map constantCoeff *ᵥ d τ from rfl, Matrix.mulVec_mulVec,
        ← Matrix.map_mul, hΛF, map_constantCoeff_smul_one, Matrix.smul_mulVec,
        Matrix.one_mulVec]
    rw [h0, Matrix.mulVec_zero] at h1
    exact (smul_eq_zero.1 h1.symm).resolve_left (pow_ne_zero _ (l_ne_zero l))
  · rw [← onD_actD]
    change (F.mat τ).map constantCoeff *ᵥ _ = _ • ((F.mat τ).map constantCoeff *ᵥ d τ)
    rw [hc ζ, Matrix.mulVec_smul]

theorem exists_Z_of_onPol_eq_zero {μ : Type} [Fintype μ] [DecidableEq μ] {η H : ℕ}
    {D₀ : BKDat O K l e a ι η H} {D₁ : BKDat O K l e a κ η H} {D₂ : BKDat O K l e a μ η H}
    (F : BKHom D₀ D₁) (G : BKHom D₁ D₂) (hex : IsExactTriple F.toHom G.toHom)
    (hinj : Function.Injective F.onPol) (n : ℕ)
    (hn : ∀ y ∈ D₂.M, ∃ x ∈ D₁.M, G.app x = (l : K) ^ n • y) {w : D₁.Pol} (hw : w ∈ D₁.Z)
    (hG : G.onPol w = 0) : ∃ w₀ ∈ D₀.Z, F.onPol w₀ = (l : K) ^ n • w := by
  obtain ⟨⟨y, hy, rfl⟩, hinv⟩ := D₁.desc.mem_Z.1 hw
  have hGy : G.app y ∈ D₂.M :=
    D₂.mem_M_of_mem_Man (G.app_mem_EM hy) (D₂.cls_eq_zero_iff.1 hG)
  obtain ⟨x, hx, hxy⟩ := hn _ hGy
  have hGz : G.app ((l : K) ^ n • y - x) = 0 := by
    rw [map_sub, LinearMap.map_smul_of_tower, hxy, sub_self]
  have hlM : ∀ {m : Vec K a κ}, m ∈ D₁.M → (l : K) ^ n • m ∈ D₁.M := fun hm => by
    rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
    exact nsmul_mem hm _
  have hEz : E K l e ^ η • ((l : K) ^ n • y - x) ∈ D₁.M := by
    rw [smul_sub, smul_comm]
    refine sub_mem (hlM hy) ?_
    exact D₁.M.smul_mem (⟨E K l e ^ η, pow_mem (E_mem l e _) η⟩ : A O K) hx
  have hker : G.app (E K l e ^ η • ((l : K) ^ n • y - x)) = 0 := by rw [map_smul, hGz, smul_zero]
  obtain ⟨m₀, hm₀, hFm⟩ := Submodule.mem_map.1 ((hex.exact _ hEz).1 hker)
  have hFm' : F.app m₀ = E K l e ^ η • ((l : K) ^ n • y - x) := hFm
  have hFy : F.app (Ezpow K l e (-η) • m₀) = (l : K) ^ n • y - x := by
    rw [map_smul, hFm', smul_smul, mul_comm, E_pow_mul_Ezpow_neg, one_smul]
  have hy₀M : Ezpow K l e (-η) • m₀ ∈ D₀.EM η := by
    show E K l e ^ η • (Ezpow K l e (-η) • m₀) ∈ D₀.M
    rw [smul_smul, E_pow_mul_Ezpow_neg, one_smul]
    exact hm₀
  have hF : F.onPol (D₀.cls (Ezpow K l e (-η) • m₀)) = (l : K) ^ n • D₁.cls y := by
    rw [BK.Hom.onPol_cls, hFy, map_sub, map_smul, D₁.cls_eq_zero_iff.2 (D₁.M_le_Man hx), sub_zero]
  refine ⟨D₀.cls (Ezpow K l e (-η) • m₀), D₀.desc.mem_Z.2 ⟨⟨_, hy₀M, rfl⟩, fun g => hinj ?_⟩, hF⟩
  rw [F.onPol_act, hF, map_smul, hinv g]

end GlobalTheory.ExactTripleBK

open GlobalTheory.ExactTripleBK in

theorem GlobalTheory.exactTriple_jumps_chars_lift : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (κ μ : Type) [Fintype κ] [DecidableEq κ] [Fintype μ] [DecidableEq μ] (η H : ℕ) (D₀ : BKDat O K l e a ι η H) (D₁ : BKDat O K l e a κ η H) (D₂ : BKDat O K l e a μ η H) (F : BKHom D₀ D₁) (G : BKHom D₁ D₂), IsExactTriple F.toHom G.toHom → D₀.jumps ⊆ D₁.jumps ∧ (∀ τ, D₀.desc.chars τ ⊆ D₁.desc.chars τ) ∧ Function.Injective F.onPol ∧ (∀ n : ℕ, (∀ y ∈ D₂.M, ∃ x ∈ D₁.M, G.app x = (l : K) ^ n • y) → ∀ w ∈ D₁.Z, G.onPol w = 0 → ∃ w₀ ∈ D₀.Z, F.onPol w₀ = (l : K) ^ n • w) := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ κ μ _ _ _ _ η H D₀ D₁ D₂ F G hex
  obtain ⟨n, hn⟩ := GlobalTheory.T.exists_prime_pow_smul_mem_range_of_finiteLength_coker O K l e a κ μ D₁.toPhiMod D₂.toPhiMod G.toHom hex.finiteLength
  have hΛ := GlobalTheory.T.exists_integral_leftInverse_of_phiModule_exactTriple O K l e a ι κ μ D₀.toPhiMod D₁.toPhiMod D₂.toPhiMod F.toHom G.toHom hex n hn
  have hinj := onPol_injective F.toHom n hΛ
  exact ⟨GlobalTheory.T.breuilKisin_jumps_subset_of_split_mono O K l e a ι κ η H D₀ D₁ F.toHom n hΛ, fun τ => chars_subset F n hΛ τ, hinj,
    fun m hm w hw hG => exists_Z_of_onPol_eq_zero F G hex hinj m hm hw hG⟩
