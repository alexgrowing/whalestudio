import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CosetFd

noncomputable section

open scoped Classical Pointwise
open MeasureTheory NumberField NumberField.mixedEmbedding

namespace Formalism.L2.SG.NGCut.SplitEmbedding

section Inv

variable {K : Type} [Field K] [NumberField K] [IsEmpty {w : InfinitePlace K // w.IsReal}] {ι : Type} [Fintype ι]
  (σ : ι ≃ {w : InfinitePlace K // w.IsComplex}) (cj : ι → Prop) [DecidablePred cj]

def phiInv (v : ι → ℂ) : mixedSpace K :=
  (fun w => isEmptyElim w, fun w => if cj (σ.symm w) then (starRingEnd ℂ) (v (σ.symm w)) else v (σ.symm w))

theorem phiMap_phiInv (v : ι → ℂ) : phiMap σ cj (phiInv σ cj v) = v := by
  funext i
  by_cases h : cj i <;> simp [phiMap, phiInv, h]

theorem phiInv_phiMap (x : mixedSpace K) : phiInv σ cj (phiMap σ cj x) = x := by
  refine Prod.ext (funext fun w => isEmptyElim w) (funext fun w => ?_)
  by_cases h : cj (σ.symm w) <;> simp [phiMap, phiInv, h]

theorem phiInv_add (v w : ι → ℂ) : phiInv σ cj (v + w) = phiInv σ cj v + phiInv σ cj w := by
  refine Prod.ext (funext fun w' => isEmptyElim w') (funext fun w' => ?_)
  by_cases h : cj (σ.symm w') <;> simp [phiInv, h]

theorem measurable_phiInv : Measurable (phiInv σ cj (K := K)) := by
  unfold phiInv
  refine Measurable.prodMk (measurable_pi_lambda _ fun w => isEmptyElim w) (measurable_pi_lambda _ fun w => ?_)
  by_cases h : cj (σ.symm w)
  · simp only [h, ↓reduceIte]
    exact Complex.continuous_conj.measurable.comp (measurable_pi_apply _)
  · simp only [h, ↓reduceIte]
    exact measurable_pi_apply _

end Inv

private theorem mem_idealLattice_iff' (K : Type) [Field K] [NumberField K]
    (I : (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ) (x : mixedSpace K) :
    x ∈ idealLattice K I ↔ ∃ a : K, a ∈ (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ∧ mixedEmbedding K a = x := by
  first
  | (rw [mem_idealLattice]; rfl)
  | exact mem_idealLattice K I
  | simp [idealLattice]

theorem idealLattice_fd (K : Type) [Field K] [NumberField K] (I : (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ) :
    ∃ FL : Set (mixedSpace K), MeasurableSet FL ∧
      (∀ x, ∃! l : (idealLattice K I).toAddSubgroup, (l : mixedSpace K) + x ∈ FL) := by
  let b := fractionalIdealLatticeBasis K I
  have hmem : ∀ y : mixedSpace K, y ∈ (idealLattice K I).toAddSubgroup ↔ y ∈ Submodule.span ℤ (Set.range b) := by
    intro y
    rw [Submodule.mem_toAddSubgroup, mem_idealLattice_iff', mem_span_fractionalIdealLatticeBasis, Set.mem_image]
    rfl
  refine ⟨ZSpan.fundamentalDomain b, ZSpan.fundamentalDomain_measurableSet b, fun x => ?_⟩
  obtain ⟨l, hl, hu⟩ := ZSpan.exist_unique_vadd_mem_fundamentalDomain b x
  refine ⟨⟨l, (hmem l).2 l.2⟩, by simpa [Submodule.vadd_def, vadd_eq_add] using hl, ?_⟩
  rintro ⟨m, hm⟩ hm'
  have h2 := hu ⟨m, (hmem m).1 hm⟩ (by simpa [Submodule.vadd_def, vadd_eq_add] using hm')
  have h3 : m = (l : mixedSpace K) := congrArg Subtype.val h2
  exact Subtype.ext h3

private theorem existsUnique_add_mem_preimage_of_additive_equiv {V W : Type} [AddCommGroup V] [AddCommGroup W]
    (f : V → W) (g : W → V) (hgf : ∀ x, g (f x) = x) (hfg : ∀ y, f (g y) = y)
    (hg : ∀ y z, g (y + z) = g y + g z) (L : AddSubgroup V) (M : AddSubgroup W)
    (hLM : ∀ w, w ∈ M ↔ g w ∈ L) (F : Set V) (h : ∀ x, ∃! l : L, (l : V) + x ∈ F) :
    ∀ y, ∃! m : M, (m : W) + y ∈ g ⁻¹' F := by
  intro y
  obtain ⟨l, hl, hu⟩ := h (g y)
  have hfl : f l ∈ M := (hLM _).2 (by rw [hgf]; exact l.2)
  refine ⟨⟨f l, hfl⟩, ?_, ?_⟩
  · show g (f l + y) ∈ F
    rw [hg, hgf]
    exact hl
  · rintro ⟨m, hm⟩ hm'
    have hm'' : g m + g y ∈ F := by
      have h3 := hm'
      rw [Set.mem_preimage, hg] at h3
      exact h3
    have h2 : g m = l := congrArg Subtype.val (hu ⟨g m, (hLM m).1 hm⟩ hm'')
    apply Subtype.ext
    show m = f l
    rw [← h2, hfg]

private theorem phiMap_mixedEmbedding_eq {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
    (φ : ι → (K →+* ℂ)) (σ : ι ≃ {w : InfinitePlace K // w.IsComplex})
    (hφ : ∀ i, φ i = (σ i).1.embedding ∨ φ i = ComplexEmbedding.conjugate (σ i).1.embedding) (a : K) :
    phiMap σ (fun i => φ i ≠ (σ i).1.embedding) (mixedEmbedding K a) = fun i => φ i a := by
  funext i
  simp only [phiMap]
  split_ifs with h
  · rw [(hφ i).resolve_left h, ComplexEmbedding.conjugate_coe_eq]
    first
    | rfl
    | simp [mixedEmbedding]
  · have h' : φ i = (σ i).1.embedding := by simpa using h
    rw [h']
    first
    | rfl
    | simp [mixedEmbedding]

theorem exists_fd (K : Type) [Field K] [NumberField K] [IsEmpty {w : InfinitePlace K // w.IsReal}]
    (ι : Type) [Fintype ι] (φ : ι → (K →+* ℂ)) (σ : ι ≃ {w : InfinitePlace K // w.IsComplex})
    (hφ : ∀ i, φ i = (σ i).1.embedding ∨ φ i = ComplexEmbedding.conjugate (σ i).1.embedding)
    (I : (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ) (Λ : AddSubgroup K)
    (hΛ : ∀ a ∈ Λ, a ∈ (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K))
    (hk0 : Λ.relIndex (((I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K).toAddSubgroup) ≠ 0)
    (s : ℂ) (hs : s ≠ 0) :
    ∃ F : Set (ι → ℂ), MeasurableSet F ∧ ∀ v, ∃! a : Λ, (fun i => s * φ i a) + v ∈ F := by
  have hne : Nonempty ι := by
    obtain ⟨w⟩ : Nonempty (InfinitePlace K) := inferInstance
    have hw : w.IsComplex := (w.isReal_or_isComplex).resolve_left
      (fun h => isEmptyElim (⟨w, h⟩ : {w : InfinitePlace K // w.IsReal}))
    exact ⟨σ.symm ⟨w, hw⟩⟩
  let cj : ι → Prop := fun i => φ i ≠ (σ i).1.embedding
  let IA : AddSubgroup K := ((I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K).toAddSubgroup
  let E : K →+ (ι → ℂ) :=
    { toFun := fun a i => s * φ i a
      map_zero' := by
        funext i
        simp
      map_add' := fun a b => by
        funext i
        simp [mul_add] }
  have hE : Function.Injective E := by
    intro a b hab
    obtain ⟨i0⟩ := hne
    have h1 : s * φ i0 a = s * φ i0 b := congrFun hab i0
    exact (φ i0).injective (mul_left_cancel₀ hs h1)
  let f : mixedSpace K → (ι → ℂ) := fun x i => s * phiMap σ cj x i
  let g : (ι → ℂ) → mixedSpace K := fun v => phiInv σ cj (fun i => s⁻¹ * v i)
  have hgf : ∀ x, g (f x) = x := fun x => by
    show phiInv σ cj (fun i => s⁻¹ * (s * phiMap σ cj x i)) = x
    simp only [inv_mul_cancel_left₀ hs]
    exact phiInv_phiMap σ cj x
  have hfg : ∀ y, f (g y) = y := fun y => by
    show (fun i => s * phiMap σ cj (phiInv σ cj (fun j => s⁻¹ * y j)) i) = y
    simp only [phiMap_phiInv, mul_inv_cancel_left₀ hs]
  have hg : ∀ y z, g (y + z) = g y + g z := fun y z => by
    show phiInv σ cj (fun i => s⁻¹ * (y + z) i) =
      phiInv σ cj (fun i => s⁻¹ * y i) + phiInv σ cj (fun i => s⁻¹ * z i)
    rw [← phiInv_add]
    congr 1
    funext i
    simp [mul_add]
  have hfE : ∀ a, f (mixedEmbedding K a) = E a := fun a => by
    funext i
    exact congrArg (s * ·) (congrFun (phiMap_mixedEmbedding_eq φ σ hφ a) i)
  let L : AddSubgroup (ι → ℂ) := IA.map E
  have hLM : ∀ w, w ∈ L ↔ g w ∈ (idealLattice K I).toAddSubgroup := by
    intro w
    constructor
    · intro hw
      obtain ⟨a, ha, rfl⟩ := AddSubgroup.mem_map.1 hw
      have h1 : g (E a) = mixedEmbedding K a := by rw [← hfE a, hgf]
      rw [h1, Submodule.mem_toAddSubgroup, mem_idealLattice_iff']
      exact ⟨a, ha, rfl⟩
    · intro hw
      rw [Submodule.mem_toAddSubgroup, mem_idealLattice_iff'] at hw
      obtain ⟨a, ha, hae⟩ := hw
      refine AddSubgroup.mem_map.2 ⟨a, ha, ?_⟩
      rw [← hfE a, hae, hfg]
  obtain ⟨FL, hFLm, hFL⟩ := idealLattice_fd K I
  have hgm : Measurable g :=
    (measurable_phiInv σ cj).comp (measurable_pi_lambda _ fun i => measurable_const.mul (measurable_pi_apply i))
  have hdL : ∀ y, ∃! m : L, (m : ι → ℂ) + y ∈ g ⁻¹' FL :=
    existsUnique_add_mem_preimage_of_additive_equiv f g hgf hfg hg _ L hLM FL hFL
  let Λ' : AddSubgroup (ι → ℂ) := Λ.map E
  have hle : Λ' ≤ L := AddSubgroup.map_mono (fun a ha => hΛ a ha)
  have hri : Λ'.relIndex L ≠ 0 := by
    show Λ'.relIndex (IA.map E) ≠ 0
    rw [← AddSubgroup.relIndex_comap, AddSubgroup.comap_map_eq_self_of_injective hE]
    exact hk0
  have hfin : (Λ'.addSubgroupOf L).FiniteIndex := ⟨hri⟩
  obtain ⟨G, hGm, hG⟩ := coset_fd L Λ' hle hfin (g ⁻¹' FL) (hFLm.preimage hgm) hdL
  refine ⟨G, hGm, fun v => ?_⟩
  obtain ⟨⟨w, hw⟩, hwG, hu⟩ := hG v
  obtain ⟨a, ha, rfl⟩ := AddSubgroup.mem_map.1 hw
  refine ⟨⟨a, ha⟩, hwG, ?_⟩
  rintro ⟨b, hb⟩ hbG
  have h3 := hu ⟨E b, AddSubgroup.mem_map_of_mem E hb⟩ hbG
  exact Subtype.ext (hE (congrArg Subtype.val h3))

private theorem measurePreserving_mul_left_of_norm_eq_one (u : ℂ) (hu : ‖u‖ = 1) :
    MeasurePreserving (fun z : ℂ => u * z) volume volume := by
  have hu0 : u ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hu
    exact zero_ne_one hu
  let e : ℂ ≃ₗᵢ[ℝ] ℂ :=
    { toFun := fun z => u * z
      invFun := fun z => u⁻¹ * z
      map_add' := fun z w => mul_add u z w
      map_smul' := fun c z => by
        simp only [RingHom.id_apply, Complex.real_smul]
        ring
      left_inv := fun z => inv_mul_cancel_left₀ hu0 z
      right_inv := fun z => mul_inv_cancel_left₀ hu0 z
      norm_map' := fun z => by
        show ‖u * z‖ = ‖z‖
        rw [norm_mul, hu, one_mul] }
  exact e.measurePreserving

theorem idealCovolC (K : Type) [Field K] [NumberField K] [IsEmpty {w : InfinitePlace K // w.IsReal}]
    (ι : Type) [Fintype ι] (φ : ι → (K →+* ℂ)) (σ : ι ≃ {w : InfinitePlace K // w.IsComplex})
    (hφ : ∀ i, φ i = (σ i).1.embedding ∨ φ i = ComplexEmbedding.conjugate (σ i).1.embedding)
    (I : (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ) (Λ : AddSubgroup K)
    (hΛ : ∀ a ∈ Λ, a ∈ (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)) (k : ℕ)
    (hk : Λ.relIndex (((I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K).toAddSubgroup) = k)
    (hk0 : k ≠ 0) (s : ℂ) (hs : s ≠ 0) (F : Set (ι → ℂ)) (hF : MeasurableSet F)
    (hFd : ∀ v, ∃! a : Λ, (fun i => s * φ i a) + v ∈ F) :
    volume F = ENNReal.ofReal ((k : ℝ) * (FractionalIdeal.absNorm (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : ℝ) *
      2⁻¹ ^ Fintype.card ι * √|(discr K : ℝ)| * ‖s‖ ^ (2 * Fintype.card ι)) := by
  have hr0 : ‖s‖ ≠ 0 := norm_ne_zero_iff.2 hs
  have hrc : ((‖s‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr0
  let u : ℂ := s / ((‖s‖ : ℝ) : ℂ)
  have hur : u * ((‖s‖ : ℝ) : ℂ) = s := div_mul_cancel₀ s hrc
  have hu1 : ‖u‖ = 1 := by
    show ‖s / ((‖s‖ : ℝ) : ℂ)‖ = 1
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_norm, div_self hr0]
  have h1 : MeasurePreserving (fun z : ℂ => u * z) volume volume := by
    exact measurePreserving_mul_left_of_norm_eq_one u hu1
  have hm : MeasurePreserving (fun v : ι → ℂ => fun i => u * v i) volume volume := by
    exact volume_preserving_pi (fun _ => h1)
  have hF' : MeasurableSet ((fun v : ι → ℂ => fun i => u * v i) ⁻¹' F) := hm.measurable hF
  have hFd' : ∀ v, ∃! a : Λ, (fun i => ((‖s‖ : ℝ) : ℂ) * φ i a) + v ∈ (fun v : ι → ℂ => fun i => u * v i) ⁻¹' F := by
    intro v
    refine (existsUnique_congr fun a => ?_).2 (hFd (fun i => u * v i))
    have h2 : (fun i => u * ((fun i => ((‖s‖ : ℝ) : ℂ) * φ i a) + v) i) = (fun i => s * φ i a) + fun i => u * v i := by
      funext i
      simp only [Pi.add_apply]
      rw [mul_add, ← mul_assoc, hur]
    rw [Set.mem_preimage, h2]
  have h3 := idealCovol K ι φ σ hφ I Λ hΛ k hk hk0 ‖s‖ hr0 _ hF' hFd'
  rw [← hm.measure_preimage hF.nullMeasurableSet, h3, abs_norm]

end Formalism.L2.SG.NGCut.SplitEmbedding
