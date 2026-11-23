import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LinearIndependentEigProj
open AlgebraicGeometry CategoryTheory Limits NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.AdaptedEx

section Main

variable {E : Type} [Field E] [NumberField E] {K W : Type} [Field K] [AddCommGroup W] [Module K W]
  {ρ : 𝓞 E →+* Module.End K W} {ρH : 𝓞 E →+* Module.End K (W × Module.Dual K W)}

theorem fst_proj (hact : ∀ a y, (ρH a y).1 = ρ a y.1) (σ : E →+* K) (y : W × Module.Dual K W) :
    (HT.eigProj ρH σ y).1 = HT.eigProj ρ σ y.1 := by
  simp only [HT.eigProj, LinearMap.sum_apply, LinearMap.smul_apply, Prod.fst_sum, Prod.smul_fst, hact]

theorem comp_proj {bar : 𝓞 E ≃+* 𝓞 E} (hinr : ∀ a f, ρH a (0, f) = (0, f ∘ₗ ρ (bar a))) {σ σ' : E →+* K}
    (hσ : ∀ a : 𝓞 E, σ' (a : E) = σ (bar a : 𝓞 E)) (hb : ∀ a, bar (bar a) = a) {φ : Module.Dual K W}
    (h : ((0 : W), φ) ∈ HT.eigSp ρH σ) : φ ∘ₗ HT.eigProj ρ σ' = φ := by
  have h3 : ∀ k z, φ (ρ (RingOfIntegers.basis E k) z) = σ' ((RingOfIntegers.basis E k : 𝓞 E) : E) • φ z := by
    intro k z
    have h1 := HT.LatBasic.mem_eigSp.1 h (bar (RingOfIntegers.basis E k))
    rw [hinr, hb, ← hσ] at h1
    have h2 := congrArg Prod.snd h1
    exact LinearMap.congr_fun h2 z
  have h2 : ∑ k, σ' (HT.dualInt E k) * σ' ((RingOfIntegers.basis E k : 𝓞 E) : E) = 1 := by
    rw [← map_one σ', ← HT.LatBasic.sum_dualInt_mul, map_sum]
    simp
  ext z
  simp only [HT.eigProj, LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, h3,
    smul_smul]
  rw [← Finset.sum_smul, h2, one_smul]

theorem dual_frame [CharZero K] {q : ℕ} {b : Fin q → W} (hb : LinearIndependent K b) {τ : E →+* K}
    (hspan : Submodule.span K (Set.range b) = HT.eigSp ρ τ) :
    ∃ f : Fin q → Module.Dual K W, (∀ x, HT.eigProj ρ τ x = ∑ j, f j x • b j) ∧
      (∀ j j', f j (b j') = if j = j' then 1 else 0) ∧
      ∀ j (c : 𝓞 E), f j ∘ₗ ρ c = τ (c : E) • f j := by
  classical
  let B := Module.Basis.span hb
  let π : W →ₗ[K] Submodule.span K (Set.range b) := (HT.eigProj ρ τ).codRestrict _ fun x => by
    rw [hspan]
    exact HT.LatBasic.eigProj_mem ρ τ x
  have hπ : ∀ x, ((π x : Submodule.span K (Set.range b)) : W) = HT.eigProj ρ τ x := fun x => rfl
  have hfix : ∀ x ∈ HT.eigSp ρ τ, HT.eigProj ρ τ x = x := fun x hx => HT.LatBasic.eigProj_of_mem hx
  refine ⟨fun j => B.coord j ∘ₗ π, fun x => ?_, fun j j' => ?_, fun j c => ?_⟩
  · have h1 := congrArg Subtype.val (B.sum_repr (π x))
    rw [hπ] at h1
    rw [← h1, AddSubmonoidClass.coe_finsetSum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [B, Module.Basis.span_apply]
  · have h1 : π (b j') = B j' := Subtype.ext (by
      rw [hπ, Module.Basis.span_apply]
      exact hfix _ (hspan ▸ Submodule.subset_span ⟨j', rfl⟩))
    simp [h1, Finsupp.single_apply, eq_comm]
  · ext x
    have h1 : π (ρ c x) = τ (c : E) • π x := Subtype.ext (by
      have h2 : HT.eigProj ρ τ (ρ c x) = ρ c (HT.eigProj ρ τ x) := by
        have hcomm : ∀ k, ρ (RingOfIntegers.basis E k) (ρ c x) = ρ c (ρ (RingOfIntegers.basis E k) x) := fun k => by
          rw [← Module.End.mul_apply, ← map_mul, mul_comm, map_mul, Module.End.mul_apply]
        simp only [HT.eigProj, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, hcomm]
      rw [hπ, h2, HT.LatBasic.mem_eigSp.1 (HT.LatBasic.eigProj_mem ρ τ x) c]
      rfl)
    simp [h1]

end Main

theorem exists_adapted_basis : ∀ (E : Type) [Field E] [NumberField E] (K W : Type) [Field K] [CharZero K] [AddCommGroup W] [Module K W] [FiniteDimensional K W] (ρ : 𝓞 E →+* Module.End K W) (ρH : 𝓞 E →+* Module.End K (W × Module.Dual K W)) (bar : 𝓞 E ≃+* 𝓞 E) (σ σ' : E →+* K) (p q : ℕ) (v : Fin p → W) (w : Fin q → W), (∀ a y, (ρH a y).1 = ρ a y.1) → (∀ a φ, ρH a (0, φ) = (0, φ ∘ₗ ρ (bar a))) → (∀ a : 𝓞 E, σ' (a : E) = σ (bar a : 𝓞 E)) → (∀ a, bar (bar a) = a) → LinearIndependent K v → Submodule.span K (Set.range v) = HT.eigSp ρ σ → LinearIndependent K w → Submodule.span K (Set.range w) = HT.eigSp ρ σ' → ∃ u, IsAdapted ρH σ v w u ∧ LinearIndependent K u ∧ Submodule.span K (Set.range u) = HT.eigSp ρH σ := by
  intro E _ _ K W _ _ _ _ _ ρ ρH bar σ σ' p q v w hact hinr hσσ' hbar hv hvs hw hws
  classical
  obtain ⟨f, hf1, hf2, hf4⟩ := dual_frame hw hws
  let u : Fin (p + q) → W × Module.Dual K W :=
    Fin.addCases (fun i => HT.eigProj ρH σ (v i, 0)) (fun j => ((0 : W), f j))
  have hul : ∀ i, u (Fin.castAdd q i) = HT.eigProj ρH σ (v i, 0) := fun i => by simp [u]
  have hur : ∀ j, u (Fin.natAdd p j) = ((0 : W), f j) := fun j => by simp [u]
  have hvm : ∀ i, v i ∈ HT.eigSp ρ σ := fun i => hvs ▸ Submodule.subset_span ⟨i, rfl⟩
  have hu1 : ∀ i, (u (Fin.castAdd q i)).1 = v i := fun i => by
    rw [hul, fst_proj hact]
    exact HT.LatBasic.eigProj_of_mem (hvm i)
  have hueig : ∀ i, u i ∈ HT.eigSp ρH σ := by
    intro i
    induction i using Fin.addCases with
    | left i =>
      rw [hul]
      exact HT.LatBasic.eigProj_mem _ _ _
    | right j =>
      rw [hur, HT.LatBasic.mem_eigSp]
      intro a
      have h1 := hf4 j (bar a)
      rw [hσσ', hbar] at h1
      rw [hinr, h1]
      simp
  have had : IsAdapted ρH σ v w u := by
    unfold IsAdapted
    exact ⟨hueig, hu1, fun j => ⟨by rw [hur], fun j' => by rw [hur]; exact hf2 j j'⟩⟩
  refine ⟨u, had, ?_, le_antisymm ?_ ?_⟩
  · rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fin.sum_univ_add] at hg
    have h1 : ∑ i, g (Fin.castAdd q i) • v i = 0 := by
      have h := congrArg Prod.fst hg
      simpa [Prod.fst_sum, hu1, hur] using h
    have hc := Fintype.linearIndependent_iff.1 hv _ h1
    have h3 : ∑ j, g (Fin.natAdd p j) • f j = 0 := by
      have h := congrArg Prod.snd hg
      simpa [Prod.snd_sum, hur, hc] using h
    have hd : ∀ j', g (Fin.natAdd p j') = 0 := fun j' => by
      have h := LinearMap.congr_fun h3 (w j')
      simpa [LinearMap.sum_apply, hf2] using h
    intro i
    induction i using Fin.addCases with
    | left i => exact hc i
    | right j => exact hd j
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hueig i
  · intro y hye
    have hy1 : y.1 ∈ Submodule.span K (Set.range v) := by
      rw [hvs]
      refine HT.LatBasic.mem_eigSp.2 fun a => ?_
      rw [← hact, HT.LatBasic.mem_eigSp.1 hye a]
      rfl
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hy1
    obtain ⟨z, hz⟩ : ∃ z, z = y - ∑ i, c i • u (Fin.castAdd q i) := ⟨_, rfl⟩
    have hze : z ∈ HT.eigSp ρH σ := by
      rw [hz]
      exact Submodule.sub_mem _ hye (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hueig _))
    have hz1 : z.1 = 0 := by
      rw [hz, Prod.fst_sub, Prod.fst_sum, sub_eq_zero, ← hc]
      simp [hu1]
    have hzz : ((0 : W), z.2) = z := Prod.ext hz1.symm rfl
    have hcomp : z.2 ∘ₗ HT.eigProj ρ σ' = z.2 := comp_proj hinr hσσ' hbar (hzz.symm ▸ hze)
    have hd : z.2 = ∑ j, z.2 (w j) • f j := by
      ext x
      have h1 := LinearMap.congr_fun hcomp x
      rw [LinearMap.comp_apply, hf1, map_sum] at h1
      rw [← h1]
      simp [LinearMap.sum_apply, mul_comm]
    have e2 : ∑ j, z.2 (w j) • (((0 : W), f j) : W × Module.Dual K W) = z := by
      refine Prod.ext ?_ ?_
      · simp [Prod.fst_sum, hz1]
      · rw [Prod.snd_sum]
        simpa using hd.symm
    have e3 : y = ∑ i, (Fin.addCases c (fun j => z.2 (w j)) i : K) • u i := by
      rw [Fin.sum_univ_add]
      simp only [Fin.addCases_left, Fin.addCases_right, hur]
      rw [e2, hz]
      abel
    rw [e3]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

end GlobalTheory.CompanionTheory.Ar.Flat.AdaptedEx
