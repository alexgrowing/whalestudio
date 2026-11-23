import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.UnitAtOfIsLineGenOn
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.WedgeLineLatticeVectorBundleStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.Flat.LineGenerator

theorem exists_ιMulti_eq_smul {Ω : Type} [Field Ω] {E : Type} [AddCommGroup E] [Module Ω E] {r : ℕ}
    {v b : Fin r → E} (h : ∀ i, v i ∈ Submodule.span Ω (Set.range b)) :
    ∃ α : Ω, exteriorPower.ιMulti Ω r v = α • exteriorPower.ιMulti Ω r b := by
  classical
  have hc : ∀ i, ∃ c : Fin r → Ω, ∑ j, c j • b j = v i := fun i =>
    (Submodule.mem_span_range_iff_exists_fun Ω).1 (h i)
  choose c hc using hc
  have hv : v = fun i => ∑ j, c i j • b j := funext fun i => (hc i).symm
  have hsum : exteriorPower.ιMulti Ω r v =
      ∑ f : Fin r → Fin r, (∏ i, c i (f i)) • exteriorPower.ιMulti Ω r (fun i => b (f i)) := by
    rw [hv]
    refine ((exteriorPower.ιMulti Ω r (M := E)).toMultilinearMap.map_sum
      (fun i j => c i j • b j)).trans (Finset.sum_congr rfl fun f _ => ?_)
    exact (exteriorPower.ιMulti Ω r (M := E)).toMultilinearMap.map_smul_univ
      (fun i => c i (f i)) (fun i => b (f i))
  have hmem : exteriorPower.ιMulti Ω r v ∈ Submodule.span Ω {exteriorPower.ιMulti Ω r b} := by
    rw [hsum]
    refine Submodule.sum_mem _ fun f _ => Submodule.smul_mem _ _ ?_
    by_cases hf : Function.Injective f
    · let σ : Equiv.Perm (Fin r) := Equiv.ofBijective f (Finite.injective_iff_bijective.1 hf)
      have h5 : (fun i => b (f i)) = b ∘ σ := rfl
      rw [h5, (exteriorPower.ιMulti Ω r (M := E)).map_perm b σ]
      have hm := Submodule.mem_span_singleton_self (R := Ω) (exteriorPower.ιMulti Ω r b)
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
      · rw [hs, one_smul]
        exact hm
      · rw [hs, Units.neg_smul, one_smul]
        exact neg_mem hm
    · have h6 : ¬ Function.Injective (fun i => b (f i)) := fun hh =>
        hf (Function.Injective.of_comp (f := b) hh)
      rw [(exteriorPower.ιMulti Ω r (M := E)).map_eq_zero_of_not_injective _ h6]
      exact zero_mem _
  obtain ⟨α, hα⟩ := Submodule.mem_span_singleton.1 hmem
  exact ⟨α, hα.symm⟩

theorem frame_mem_of_isVBOn {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    {E : Type} [AddCommGroup E] [Module Ω E] {L : Lat ξ E} {T : Set (Cpt ξ)} {r : ℕ}
    {V : Submodule Ω E} {v : Fin r → E} {x : Cpt ξ} (hx : x ∈ T) (hL : L.IsVBOn T r V)
    (hv : L.IsFrameAt v x) (i : Fin r) : v i ∈ V := by
  obtain ⟨U, hU, e, he, hfr⟩ := hL x hx
  have h1 : v i ∈ L x := hv.2 ▸ Submodule.subset_span ⟨i, rfl⟩
  rw [(hfr x hx hU).2] at h1
  have h2 : Submodule.span (regAt ξ x) (Set.range e) ≤
      (Submodule.span Ω (Set.range e)).restrictScalars (regAt ξ x) :=
    Submodule.span_le.2 fun _ hy => Submodule.subset_span hy
  exact he ▸ h2 h1

theorem exists_wedge_coeff {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    {E : Type} [AddCommGroup E] [Module Ω E] {L : Lat ξ E} {T : Set (Cpt ξ)} {r : ℕ}
    {V : Submodule Ω E} {v b : Fin r → E} {x : Cpt ξ} (hx : x ∈ T) (hL : L.IsVBOn T r V)
    (hb : Submodule.span Ω (Set.range b) = V) (hv : L.IsFrameAt v x) :
    ∃ α : Ω, α ≠ 0 ∧ exteriorPower.ιMulti Ω r v = α • exteriorPower.ιMulti Ω r b := by
  obtain ⟨α, hα⟩ := exists_ιMulti_eq_smul (v := v) (b := b)
    fun i => hb ▸ frame_mem_of_isVBOn hx hL hv i
  refine ⟨α, ?_, hα⟩
  rintro rfl
  exact GenModel.ιMulti_ne_zero hv.1 (by rw [hα, zero_smul])

theorem isGenAt_div : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (V : Type) [AddCommGroup V] [Module Ω V] (A B : Lat ξ V) (p q : ℕ) (Vp Vq : Submodule Ω V) (T : Set (Cpt ξ)) (b₁ v₁ : Fin p → V) (b₂ v₂ : Fin q → V) (x : Cpt ξ), x ∈ T → A.IsVBOn T p Vp → B.IsVBOn T q Vq → LinearIndependent Ω b₁ → Submodule.span Ω (Set.range b₁) = Vp → LinearIndependent Ω b₂ → Submodule.span Ω (Set.range b₂) = Vq → A.IsFrameAt v₁ x → B.IsFrameAt v₂ x → ∃ α κ : Ω, α ≠ 0 ∧ κ ≠ 0 ∧ exteriorPower.ιMulti Ω p v₁ = α • exteriorPower.ιMulti Ω p b₁ ∧ exteriorPower.ιMulti Ω q v₂ = κ • exteriorPower.ιMulti Ω q b₂ ∧ (lineLat A B p q (exteriorPower.ιMulti Ω p b₁) (exteriorPower.ιMulti Ω q b₂)).IsGenAt x (α / κ) := by
  intro X Ω _ ξ V _ _ A B p q Vp Vq T b₁ v₁ b₂ v₂ x hx hA hB hb₁ hs₁ hb₂ hs₂ hv₁ hv₂
  obtain ⟨α, hα, e₁⟩ := exists_wedge_coeff hx hA hs₁ hv₁
  obtain ⟨κ, hκ, e₂⟩ := exists_wedge_coeff hx hB hs₂ hv₂
  have hco : IsCoeffAt A B p q (exteriorPower.ιMulti Ω p b₁) (exteriorPower.ιMulti Ω q b₂) x (κ / α) :=
    ⟨α, κ, hα, hκ, by rw [GenModel.wedge_of_frame hv₁, e₁], by rw [GenModel.wedge_of_frame hv₂, e₂],
      div_mul_cancel₀ _ hα⟩
  have key := GlobalTheory.T.wedge_line_lattice_vector_bundle X Ω ξ V A B p q Vp Vq T _ _ hA hB (GenModel.ιMulti_ne_zero hb₁)
    (GenModel.ιMulti_ne_zero hb₂) ⟨x, hx, _, hco⟩
  exact ⟨α, κ, hα, hκ, e₁, e₂, key.2.2 x hx v₁ v₂ α κ hv₁ hv₂ e₁ e₂⟩

end GlobalTheory.CompanionTheory.Ar.Flat.LineGenerator
