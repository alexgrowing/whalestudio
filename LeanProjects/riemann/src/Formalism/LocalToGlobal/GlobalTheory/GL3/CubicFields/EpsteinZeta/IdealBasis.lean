import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.EpsteinZeta.DedekindFactorK

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5

open NumberField Classical
open scoped Pointwise

theorem ib_im_conj_mul (u v : ℂ) : ((starRingEnd ℂ) u * v).im = u.re * v.im - u.im * v.re := by
  simp [Complex.mul_im]; ring

theorem ib_mem_range {K : Type} [Field K] [NumberField K] (φ : K →+* ℂ) (a₀ b₀ : ℂ)
    (h₀ : latI φ ⊤ 1 = AddSubgroup.closure {a₀, b₀}) (w : ℂ)
    (hw : w ∈ AddSubgroup.closure ({a₀, b₀} : Set ℂ)) :
    ∃ c : 𝓞 K, (φ.comp (algebraMap (𝓞 K) K)) c = w := by
  rw [← h₀] at hw
  have hle : latI φ ⊤ 1 ≤ (φ.comp (algebraMap (𝓞 K) K)).toAddMonoidHom.range := by
    unfold latI
    rw [AddSubgroup.closure_le]
    rintro _ ⟨c, -, rfl⟩
    exact ⟨c, by simp⟩
  obtain ⟨c, hc⟩ := hle hw
  exact ⟨c, hc⟩

theorem ib_exists_basis {K : Type} [Field K] [NumberField K] (φ : K →+* ℂ) (a₀ b₀ : ℂ)
    (hab₀ : 0 < ((starRingEnd ℂ) a₀ * b₀).im)
    (h₀ : latI φ ⊤ 1 = AddSubgroup.closure {a₀, b₀}) :
    ∃ B : Module.Basis (Fin 2) ℤ (𝓞 K), (φ.comp (algebraMap (𝓞 K) K)) (B 0) = a₀ ∧
      (φ.comp (algebraMap (𝓞 K) K)) (B 1) = b₀ := by
  obtain ⟨e, he⟩ := ib_mem_range φ a₀ b₀ h₀ a₀ (AddSubgroup.subset_closure (by simp))
  obtain ⟨f, hf⟩ := ib_mem_range φ a₀ b₀ h₀ b₀ (AddSubgroup.subset_closure (by simp))
  set ψ : 𝓞 K →+* ℂ := φ.comp (algebraMap (𝓞 K) K) with hψ
  have hinj : Function.Injective ψ :=
    φ.injective.comp (FaithfulSMul.algebraMap_injective (𝓞 K) K)
  have hli : LinearIndependent ℤ ![e, f] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 : (s : ℂ) * a₀ + (t : ℂ) * b₀ = 0 := by
      have := congrArg ψ hst
      simpa [map_add, map_zsmul, he, hf, zsmul_eq_mul] using this
    rw [ib_im_conj_mul] at hab₀
    have hre := congrArg Complex.re h1
    have him := congrArg Complex.im h1
    simp at hre him
    constructor
    · have : (s : ℝ) * (a₀.re * b₀.im - a₀.im * b₀.re) = 0 := by
        linear_combination b₀.im * hre - b₀.re * him
      exact_mod_cast (mul_eq_zero.mp this).resolve_right hab₀.ne'
    · have : (t : ℝ) * (a₀.re * b₀.im - a₀.im * b₀.re) = 0 := by
        linear_combination a₀.re * him - a₀.im * hre
      exact_mod_cast (mul_eq_zero.mp this).resolve_right hab₀.ne'
  have hsp : ⊤ ≤ Submodule.span ℤ (Set.range ![e, f]) := by
    intro c _
    have hc : ψ c ∈ AddSubgroup.closure ({a₀, b₀} : Set ℂ) := by
      rw [← h₀]
      exact AddSubgroup.subset_closure ⟨c, Submodule.mem_top, by simp [hψ]⟩
    obtain ⟨m, n, hmn⟩ := AddSubgroup.mem_closure_pair.mp hc
    have : c = m • e + n • f := hinj (by rw [← hmn]; simp [map_add, he, hf, zsmul_eq_mul])
    rw [this]
    exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))
  refine ⟨Module.Basis.mk hli hsp, ?_, ?_⟩ <;> simp [he, hf]

theorem ib_im_det {K : Type} [Field K] [NumberField K] (ψ : 𝓞 K →+* ℂ) (a₀ b₀ : ℂ)
    (B : Module.Basis (Fin 2) ℤ (𝓞 K)) (hB0 : ψ (B 0) = a₀) (hB1 : ψ (B 1) = b₀)
    (v : Fin 2 → 𝓞 K) :
    ((starRingEnd ℂ) (ψ (v 0)) * ψ (v 1)).im = (B.det v : ℝ) * ((starRingEnd ℂ) a₀ * b₀).im := by
  have hv : ∀ j, ψ (v j) = (B.repr (v j) 0 : ℂ) * a₀ + (B.repr (v j) 1 : ℂ) * b₀ := by
    intro j
    conv_lhs => rw [← B.sum_repr (v j)]
    simp [Fin.sum_univ_two, map_add, hB0, hB1, zsmul_eq_mul]
  rw [Module.Basis.det_apply, Matrix.det_fin_two, hv 0, hv 1]
  simp only [Module.Basis.toMatrix_apply, ib_im_conj_mul]
  push_cast
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.intCast_re,
    Complex.intCast_im]
  ring

theorem latI_basis (K : Type) [Field K] [NumberField K] (hK : Module.finrank ℚ K = 2)
    (φ : K →+* ℂ) (a₀ b₀ : ℂ) (hab₀ : 0 < ((starRingEnd ℂ) a₀ * b₀).im)
    (h₀ : latI φ ⊤ 1 = AddSubgroup.closure {a₀, b₀}) (𝔞 : Ideal (𝓞 K)) (h𝔞 : 𝔞 ≠ ⊥) :
    ∃ a b : ℂ, 0 < ((starRingEnd ℂ) a * b).im ∧ latI φ 𝔞 1 = AddSubgroup.closure {a, b} ∧
      ((starRingEnd ℂ) a * b).im = (Ideal.absNorm 𝔞 : ℝ) * ((starRingEnd ℂ) a₀ * b₀).im := by
  set ψ : 𝓞 K →+* ℂ := φ.comp (algebraMap (𝓞 K) K) with hψ
  obtain ⟨B, hB0, hB1⟩ := ib_exists_basis φ a₀ b₀ hab₀ h₀
  set bI := Ideal.selfBasis B 𝔞 h𝔞
  have hdet := Ideal.natAbs_det_basis_change B 𝔞 bI
  set D := B.det ((↑) ∘ bI) with hD
  have hD0 : D ≠ 0 := by
    intro h
    rw [h, Int.natAbs_zero] at hdet
    exact h𝔞 (Ideal.absNorm_eq_zero_iff.mp hdet.symm)
  have hcross := ib_im_det ψ a₀ b₀ B hB0 hB1 ((↑) ∘ bI)
  rw [← hD] at hcross
  simp only [Function.comp_apply] at hcross
  have hN : (Ideal.absNorm 𝔞 : ℝ) = |(D : ℝ)| := by
    rw [← hdet, Nat.cast_natAbs, Int.cast_abs]
  have hlat : latI φ 𝔞 1 = AddSubgroup.closure {ψ (bI 0 : 𝓞 K), ψ (bI 1 : 𝓞 K)} := by
    apply le_antisymm
    · unfold latI
      rw [AddSubgroup.closure_le]
      rintro _ ⟨c, hc, rfl⟩
      rw [one_mul, SetLike.mem_coe, AddSubgroup.mem_closure_pair]
      have hs := bI.sum_repr ⟨c, hc⟩
      have hc' : c = (bI.repr ⟨c, hc⟩ 0) • (bI 0 : 𝓞 K) + (bI.repr ⟨c, hc⟩ 1) • (bI 1 : 𝓞 K) := by
        have h2 : ((∑ i, bI.repr ⟨c, hc⟩ i • bI i : 𝔞) : 𝓞 K) = c := by rw [hs]
        rw [Fin.sum_univ_two] at h2
        exact h2.symm
      refine ⟨bI.repr ⟨c, hc⟩ 0, bI.repr ⟨c, hc⟩ 1, ?_⟩
      show _ = ψ c
      conv_rhs => rw [hc']
      simp [map_add]
    · rw [AddSubgroup.closure_le, Set.insert_subset_iff, Set.singleton_subset_iff]
      exact ⟨AddSubgroup.subset_closure ⟨_, (bI 0).2, by simp [hψ]⟩,
        AddSubgroup.subset_closure ⟨_, (bI 1).2, by simp [hψ]⟩⟩
  rcases lt_or_gt_of_ne hD0 with hneg | hpos
  · have hneg' : (D : ℝ) < 0 := by exact_mod_cast hneg
    have hsw : ((starRingEnd ℂ) (ψ (bI 1 : 𝓞 K)) * ψ (bI 0 : 𝓞 K)).im =
        -((starRingEnd ℂ) (ψ (bI 0 : 𝓞 K)) * ψ (bI 1 : 𝓞 K)).im := by
      rw [ib_im_conj_mul, ib_im_conj_mul]; ring
    refine ⟨ψ (bI 1 : 𝓞 K), ψ (bI 0 : 𝓞 K), ?_, by rw [hlat, Set.pair_comm], ?_⟩
    · rw [hsw, hcross]; nlinarith
    · rw [hsw, hcross, hN, abs_of_neg hneg']; ring
  · have hpos' : (0 : ℝ) < D := by exact_mod_cast hpos
    refine ⟨ψ (bI 0 : 𝓞 K), ψ (bI 1 : 𝓞 K), ?_, hlat, ?_⟩
    · rw [hcross]; positivity
    · rw [hcross, hN, abs_of_pos hpos']

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
