import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNilRad
open Matrix GlobalTheory.TorFin
open scoped ContDiff

namespace GlobalTheory.TorFin.Comb

theorem finiteDimensional_span_translates_prod : ∀ (G ι : Type) [Group G] (T : ι → Set G) (c : G → ℂ), (∀ i j, i ≠ j → ∀ a ∈ T i, ∀ b ∈ T j, a * b = b * a) → (∀ i, FiniteDimensional ℂ (Submodule.span ℂ {f : G → ℂ | ∃ a ∈ T i, f = fun g => c (a * g)})) → ∀ l : List ι, l.Nodup → FiniteDimensional ℂ (Submodule.span ℂ {f : G → ℂ | ∃ a : ι → G, (∀ i, a i ∈ T i) ∧ f = fun g => c ((l.map a).prod * g)}) := by
  intro G ι _ T c hcomm hfin l hl
  induction l with
  | nil =>
    apply FiniteDimensional.span_of_finite
    apply (Set.finite_singleton (fun g : G => c g)).subset
    rintro f ⟨a, -, rfl⟩
    simp
  | cons i l ih =>
    rw [List.nodup_cons] at hl
    obtain ⟨hil, hl⟩ := hl
    haveI := ih hl
    let L : G → (G → ℂ) →ₗ[ℂ] (G → ℂ) := fun b => LinearMap.funLeft ℂ ℂ (fun g => b * g)
    have hL : ∀ b (h : G → ℂ), L b h = fun g => h (b * g) := fun b h => rfl
    set Si : Set (G → ℂ) := {f | ∃ a ∈ T i, f = fun g => c (a * g)} with hSi
    set Sl : Set (G → ℂ) := {f | ∃ a : ι → G, (∀ i, a i ∈ T i) ∧ f = fun g => c ((l.map a).prod * g)} with hSl
    haveI := hfin i
    have hfg : (Submodule.span ℂ Si).FG := Module.Finite.iff_fg.mp inferInstance
    obtain ⟨s, hsSi, hsspan⟩ := (Submodule.fg_span_iff_fg_span_finset_subset Si).mp hfg
    have hb : ∀ x : (s : Set (G → ℂ)), ∃ b ∈ T i, (x : G → ℂ) = fun g => c (b * g) :=
      fun x => hsSi x.2
    choose b hbT hbx using hb
    let U : Submodule ℂ (G → ℂ) := ⨆ x : (s : Set (G → ℂ)), (Submodule.span ℂ Sl).map (L (b x))
    haveI : FiniteDimensional ℂ U := Submodule.finiteDimensional_iSup _
    refine Submodule.finiteDimensional_of_le (S₂ := U) ?_
    rw [Submodule.span_le]
    rintro f ⟨a, ha, rfl⟩
    set m := (l.map a).prod with hm
    have hcm : ∀ y ∈ T i, y * m = m * y := by
      intro y hy
      have : Commute y m := by
        apply Commute.list_prod_right
        intro x hx
        obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
        have hji : i ≠ j := fun h => hil (h ▸ hj)
        exact hcomm i j hji y hy (a j) (ha j)
      exact this.eq
    have hmem : (fun g => c (a i * g)) ∈ Submodule.span ℂ (s : Set (G → ℂ)) := by
      rw [← hsspan]; exact Submodule.subset_span ⟨a i, ha i, rfl⟩
    have hf : (fun g => c ((List.map a (i :: l)).prod * g)) = L m (fun g => c (a i * g)) := by
      funext g; simp [hL, List.map_cons, List.prod_cons, mul_assoc, hm]
    rw [SetLike.mem_coe, hf]
    have hmap : Submodule.map (L m) (Submodule.span ℂ (s : Set (G → ℂ))) ≤ U := by
      rw [Submodule.map_span_le]
      intro x hx
      have hx' : L m x = L (b ⟨x, hx⟩) (fun g => c (m * g)) := by
        have e := hbx ⟨x, hx⟩
        have hyT := hbT ⟨x, hx⟩
        generalize b ⟨x, hx⟩ = y at e hyT ⊢
        simp only at e
        subst e
        funext g; simp only [hL]
        rw [← mul_assoc, hcm _ hyT, mul_assoc]
      rw [hx']
      apply le_iSup (fun x : (s : Set (G → ℂ)) => (Submodule.span ℂ Sl).map (L (b x))) ⟨x, hx⟩
      exact Submodule.mem_map_of_mem (Submodule.subset_span ⟨a, ha, rfl⟩)
    exact hmap (Submodule.mem_map_of_mem hmem)

end GlobalTheory.TorFin.Comb
