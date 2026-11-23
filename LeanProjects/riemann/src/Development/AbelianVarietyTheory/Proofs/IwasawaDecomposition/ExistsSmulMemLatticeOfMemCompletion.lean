import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlESymmApply
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemStabGLAdeleIff
open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix GlobalTheory.LevelHecke
open scoped TensorProduct

namespace GlobalTheory.LatticeDescent

theorem exists_rational_solution {F K V : Type} [Field F] [Field K] [Algebra F K]
    [TopologicalSpace K] [IsTopologicalRing K] (hd : DenseRange (algebraMap F K))
    [AddCommGroup V] [Module F V] {k : ℕ} (s : Fin k → V) (z : V) (a : Fin k → K)
    (U : Set K) (hU : IsOpen U) (ha : ∀ j, a j ∈ U)
    (h : ∀ l : V →ₗ[F] F, algebraMap F K (l z) = ∑ j, algebraMap F K (l (s j)) * a j) :
    ∃ c : Fin k → F, (∀ j, algebraMap F K (c j) ∈ U) ∧ ∑ j, c j • s j = z := by
  classical
  let S : (Fin k → F) →ₗ[F] V := Fintype.linearCombination F s
  have hS : ∀ c, S c = ∑ j, c j • s j := fun c => Fintype.linearCombination_apply F s c
  have hs : ∀ j, s j ∈ LinearMap.range S := fun j => ⟨Pi.single j 1, by
    simp [S]⟩
  have hz : z ∈ LinearMap.range S := by
    by_contra hz
    obtain ⟨f, hf, hm⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hz inferInstance
    have h0 : ∀ j, f (s j) = 0 := fun j => by
      have : f (s j) ∈ Submodule.map f (LinearMap.range S) := Submodule.mem_map_of_mem (hs j)
      rwa [hm] at this
    have := h f
    simp only [h0, map_zero, zero_mul, Finset.sum_const_zero] at this
    exact hf ((algebraMap F K).injective (by rw [this, map_zero]))
  obtain ⟨T0, hT0⟩ := S.rangeRestrict.exists_rightInverse_of_surjective S.range_rangeRestrict
  obtain ⟨T, hT⟩ := LinearMap.exists_extend T0
  have hST : ∀ y ∈ LinearMap.range S, S (T y) = y := fun y hy => by
    have e1 : T y = T0 ⟨y, hy⟩ := LinearMap.congr_fun hT ⟨y, hy⟩
    have e2 := congrArg Subtype.val (LinearMap.congr_fun hT0 ⟨y, hy⟩)
    rw [e1]
    exact e2
  let φ : (Fin k → K) → (Fin k → K) := fun x i =>
    x i - ∑ j, algebraMap F K (T (s j) i) * x j + algebraMap F K (T z i)
  have hφ : Continuous φ := by
    refine continuous_pi fun i => ?_
    simp only [φ]
    fun_prop
  have hφa : φ a = a := by
    funext i
    have := h ((LinearMap.proj i).comp T)
    simp only [LinearMap.comp_apply, LinearMap.proj_apply] at this
    simp only [φ, this]
    ring
  have hopen : IsOpen (φ ⁻¹' Set.pi Set.univ fun _ => U) :=
    (isOpen_set_pi Set.finite_univ fun _ _ => hU).preimage hφ
  obtain ⟨b, hb⟩ := (DenseRange.piMap (fun _ : Fin k => hd)).exists_mem_open hopen
    ⟨a, by rw [Set.mem_preimage, hφa]; exact fun j _ => ha j⟩
  refine ⟨b - T (S b) + T z, fun i => ?_, ?_⟩
  · have := hb i trivial
    convert this using 1
    simp only [φ, Pi.map_apply, hS, map_sum, map_smul, Pi.add_apply, Pi.sub_apply,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_add, map_sub, map_mul, mul_comm]
  · rw [← hS, map_add, map_sub, hST _ ⟨b, rfl⟩, hST _ hz, sub_self, zero_add]

theorem functional_of_tmul {F E K : Type} [Field F] [Field E] [Field K] [Algebra F E] [Algebra F K]
    {n k : ℕ} (s : Fin k → Fin n → E) (z : Fin n → E) (a : Fin k → K)
    (h : ∀ i, z i ⊗ₜ[F] (1 : K) = ∑ j, s j i ⊗ₜ[F] a j) (l : (Fin n → E) →ₗ[F] F) :
    algebraMap F K (l z) = ∑ j, algebraMap F K (l (s j)) * a j := by
  classical
  have hl : ∀ y : Fin n → E, l y = ∑ i, l (Pi.single i (y i)) := fun y => by
    rw [← map_sum, Finset.univ_sum_single]
  have hi : ∀ i, l (Pi.single i (z i)) • (1 : K) = ∑ j, l (Pi.single i (s j i)) • a j := fun i => by
    have := congrArg (fun t => TensorProduct.lid F K
      (LinearMap.rTensor K (l.comp (LinearMap.single F (fun _ : Fin n => E) i)) t)) (h i)
    simpa only [map_sum, LinearMap.rTensor_tmul, TensorProduct.lid_tmul, LinearMap.comp_apply,
      LinearMap.single_apply] using this
  rw [hl z, Algebra.algebraMap_eq_smul_one, Finset.sum_smul]
  simp only [hi]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_smul, ← hl, Algebra.smul_def]

theorem exists_smul_mem_of_mem_latS : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) (M : Submodule (𝓞 E) (Fin n → E)), Submodule.IsLattice E M → ∀ z : Fin n → E, (fun a => inclE (F := F) (v.adicCompletion F) (z a)) ∈ latS (F := F) (v.adicCompletion F) (intV E v) M → ∃ r : 𝓞 F, r ∉ v.asIdeal ∧ algebraMap (𝓞 F) (𝓞 E) r • z ∈ M := by
  intro F E _ _ _ _ _ v n M hM z hz
  classical
  have : Module.Finite (𝓞 E) M := Module.Finite.iff_fg.2 hM.fg
  have : Module.Finite ℤ M := Module.Finite.trans (𝓞 E) M
  obtain ⟨k, s, hs⟩ := Module.Finite.exists_fin (R := ℤ) (M := M)
  obtain ⟨a, ha, ea⟩ := (GlobalTheory.LatticeStabLocal.mem_latS_iff_isComb hs _).1 hz
  obtain ⟨c, hc, ec⟩ := exists_rational_solution (HeightOneSpectrum.denseRange_algebraMap F v)
    (fun j => (s j : Fin n → E)) z a (v.adicCompletionIntegers F)
    (Valued.isOpen_valuationSubring _) ha
    (functional_of_tmul (fun j => (s j : Fin n → E)) z a ea)
  have hv : ∀ j, v.valuation F (c j) ≤ 1 := fun j => by
    rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (c j)]
    exact hc j
  choose m d hmd using fun j => v.exists_primeCompl_mul_eq_of_integer (c j) (hv j)
  refine ⟨∏ j, (d j : 𝓞 F), (prod_mem fun j _ => (d j).2 : _ ∈ v.asIdeal.primeCompl), ?_⟩
  rw [← ec, Finset.smul_sum]
  refine sum_mem fun j _ => ?_
  have e : algebraMap (𝓞 F) (𝓞 E) (∏ j, (d j : 𝓞 F)) • c j • (s j : Fin n → E) =
      algebraMap (𝓞 F) (𝓞 E) ((∏ i ∈ Finset.univ.erase j, (d i : 𝓞 F)) * m j) •
        (s j : Fin n → E) := by
    have key : ∀ (x : 𝓞 F) (y : Fin n → E),
        algebraMap (𝓞 F) (𝓞 E) x • y = algebraMap (𝓞 F) F x • y := fun x y => by
      funext i
      simp only [Pi.smul_apply, Algebra.smul_def]
      rfl
    rw [key, key, smul_smul, map_mul, ← hmd j, ← Finset.prod_erase_mul _ _ (Finset.mem_univ j),
      map_mul]
    congr 1
    ring
  rw [e]
  exact M.smul_mem _ (s j).2

end GlobalTheory.LatticeDescent
