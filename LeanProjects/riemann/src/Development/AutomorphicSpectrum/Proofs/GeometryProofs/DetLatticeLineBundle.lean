import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsPeriodAtRestrict
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatLineGenerator
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CardComapMulFinsumEqFinsumFibres
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SncPts
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase GlobalTheory.CompanionTheory.Ar.GeoModel
open GroundTheory.Heights₂.Heights.LowerBoundFree

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.DetLine

theorem matrix_eq_mul {Ω E : Type} [Field Ω] [AddCommGroup E] [Module Ω E] {r : ℕ} {b₀ c b : Fin r → E}
    {T T' A : Matrix (Fin r) (Fin r) Ω} (hb₀ : LinearIndependent Ω b₀)
    (hT : ∀ k, c k = ∑ k', T k' k • b₀ k') (hT' : ∀ k, b k = ∑ k', T' k' k • b₀ k')
    (hA : ∀ k, b k = ∑ i, A i k • c i) : T' = T * A := by
  ext i k
  have h : ∑ k', (T' k' k - (T * A) k' k) • b₀ k' = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib, Matrix.mul_apply, Finset.sum_smul, ← hT']
    rw [sub_eq_zero, hA k, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hT j, Finset.smul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [smul_smul, _root_.mul_comm]
  exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hb₀ _ h i)

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {E : Type} [AddCommGroup E] [Module Ω E]

theorem det_mem_span (L : Lat ξ E) {r : ℕ} {b₀ c b : Fin r → E} {q : Cpt ξ} {T T' : Matrix (Fin r) (Fin r) Ω}
    (hb₀ : LinearIndependent Ω b₀) (hc : L.IsFrameAt c q) (hb : L.IsFrameAt b q)
    (hT : ∀ k, c k = ∑ k', T k' k • b₀ k') (hT' : ∀ k, b k = ∑ k', T' k' k • b₀ k') :
    T'.det ∈ Submodule.span (regAt ξ q) {T.det} := by
  have hmem : ∀ k, b k ∈ Submodule.span (regAt ξ q) (Set.range c) := fun k => by
    rw [← hc.2, hb.2]
    exact Submodule.subset_span ⟨k, rfl⟩
  choose a ha using fun k => (Submodule.mem_span_range_iff_exists_fun (regAt ξ q)).1 (hmem k)
  let M : Matrix (Fin r) (Fin r) (regAt ξ q) := Matrix.of fun i k => a k i
  have hM : T' = T * (regAt ξ q).subtype.mapMatrix M :=
    matrix_eq_mul hb₀ hT hT' fun k => (ha k).symm
  refine Submodule.mem_span_singleton.2 ⟨M.det, ?_⟩
  rw [hM, Matrix.det_mul, ← RingHom.map_det, _root_.mul_comm]
  rfl

theorem isVB_detLat : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E]
    (L : Lat ξ E) (r : ℕ) (V : Submodule Ω E) (b₀ : Fin r → E), LinearIndependent Ω b₀ →
    Submodule.span Ω (Set.range b₀) = V → L.IsVB r V → (Cusp.detLat L b₀).IsVB 1 ⊤ := by
  intro X Ω _ ξ E _ _ L r V b₀ hb₀ hsp hL p _
  obtain ⟨U, hU, c, hc, hf⟩ := hL p trivial
  have hcV : ∀ k, c k ∈ Submodule.span Ω (Set.range b₀) := fun k => by
    rw [hsp, ← hc]
    exact Submodule.subset_span ⟨k, rfl⟩
  have hbV : ∀ k, b₀ k ∈ Submodule.span Ω (Set.range c) := fun k => by
    rw [hc, ← hsp]
    exact Submodule.subset_span ⟨k, rfl⟩
  choose a ha using fun k => (Submodule.mem_span_range_iff_exists_fun Ω).1 (hcV k)
  choose s hs using fun k => (Submodule.mem_span_range_iff_exists_fun Ω).1 (hbV k)
  let T : Matrix (Fin r) (Fin r) Ω := Matrix.of fun i k => a k i
  let S : Matrix (Fin r) (Fin r) Ω := Matrix.of fun i k => s k i
  have hT : ∀ k, c k = ∑ k', T k' k • b₀ k' := fun k => (ha k).symm
  have hTS : (1 : Matrix (Fin r) (Fin r) Ω) = T * S :=
    matrix_eq_mul hb₀ hT (fun k => by simp [Matrix.one_apply, ite_smul]) fun k => (hs k).symm
  have ht : T.det ≠ 0 := fun h => by
    have := congrArg Matrix.det hTS
    rw [Matrix.det_one, Matrix.det_mul, h, zero_mul] at this
    exact one_ne_zero this
  refine ⟨U, hU, fun _ => T.det, ?_, fun q _ hq => ⟨?_, ?_⟩⟩
  · refine eq_top_iff.2 fun x _ => ?_
    have hx : x = (x * T.det⁻¹) • T.det := by
      rw [smul_eq_mul, _root_.mul_assoc, inv_mul_cancel₀ ht, _root_.mul_one]
    rw [hx]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)
  · exact linearIndependent_unique_iff.2 ht
  · have hr : Set.range (fun _ : Fin 1 => T.det) = {T.det} := Set.range_const
    rw [hr]
    refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono ?_)
    · rintro _ ⟨b, T', hfr, hT', rfl⟩
      exact det_mem_span L hb₀ (hf q trivial hq) hfr hT hT'
    · rintro _ rfl
      exact ⟨c, T, hf q trivial hq, hT, rfl⟩

end GlobalTheory.CompanionTheory.Ar.Cusp.DetLine
