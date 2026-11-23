import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
import ReciprocityTheory.DualLattices.TowerZeroSurjective
import ReciprocityTheory.DualLattices.LinPairStatement
import ReciprocityTheory.DualLattices.LengthDegreeAbelianVariety
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import ReciprocityTheory.DualLattices.SubMemOfCompat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.GenericFiberCubeInclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSeparatedOfIsQProjOver
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
import ReciprocityTheory.DualLattices.HasLenLeOfSurj
import ReciprocityTheory.DualLattices.UpSmith
import ReciprocityTheory.DualLattices.HasLenCokerDet

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

private theorem hasLen_of_fp {C : Type} [Field C] {v : Valuation C NNReal} {O : Type} [CommRing O]
    [Algebra O C] (hv : v.Integers O) (M : Type) [AddCommGroup M] [Module O M]
    (h : Module.FinitePresentation O M) : ∃ x, HasLen v O M x := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' O M
  have hk : (LinearMap.ker f).FG := Module.FinitePresentation.fg_ker f hf
  obtain ⟨m, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hk
  exact ⟨_, hasLen_of_equiv ((Submodule.quotEquivOfEq _ _ hg).trans
    (f.quotKerEquivOfSurjective hf)).symm (Smith.hasLen_coker_gen hv g)⟩

private theorem hasLen_mono {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R]
    [Algebra R C] (hv : v.Integers R) {M M' : Type} [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module R M'] (f : M →ₗ[R] M') {z z' : NNReal} (hf : Function.Surjective f)
    (hz : HasLen v R M z) (hz' : HasLen v R M' z') : z ≤ z' := by
  have := isLocal_of_integers hv
  obtain ⟨m, c, ⟨e⟩, hzc⟩ := hz
  obtain ⟨r, q, ⟨e'⟩, hzq⟩ := hz'
  let π : M →ₗ[R] ((t : Fin r) → R ⧸ Ideal.span {q t}) := e'.toLinearMap ∘ₗ f
  have hπ : Function.Surjective π := e'.surjective.comp hf
  let y : Fin m → ((t : Fin r) → R ⧸ Ideal.span {q t}) :=
    fun i => π (e.symm (Pi.single i 1))
  have hspan : Submodule.span R (Set.range y) = ⊤ := by
    rw [eq_top_iff]
    intro w _
    obtain ⟨x, rfl⟩ := hπ w
    have hx := eq_sum_single c (e x)
    have : x = ∑ i, (Quotient.out (e x i) : R) • e.symm (Pi.single i 1) := by
      calc x = e.symm (e x) := (e.symm_apply_apply x).symm
        _ = e.symm (∑ i, (Quotient.out (e x i) : R) • (Pi.single i (1 : R ⧸ Ideal.span {c i}) :
            (i : Fin m) → R ⧸ Ideal.span {c i})) := congrArg e.symm hx
        _ = _ := by simp only [map_sum, map_smul]
    rw [this, map_sum]
    exact Submodule.sum_mem _ fun i _ => by
      rw [map_smul]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hT : ∀ k, ∑ i, (Matrix.diagonal c) k i • y i = 0 := by
    intro k
    rw [Finset.sum_eq_single k]
    · simp only [Matrix.diagonal_apply_eq, y]
      rw [← map_smul, ← map_smul, single_smul_self, map_zero, map_zero]
    · intro b _ hb; rw [Matrix.diagonal_apply_ne _ (Ne.symm hb), zero_smul]
    · intro h; exact absurd (Finset.mem_univ k) h
  have hdet := det_mem_span_prod r q m y hspan (Matrix.diagonal c) hT
  rw [Matrix.det_diagonal] at hdet
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 hdet
  have hle := hv.le_of_dvd (⟨w, by rw [← hw, mul_comm]⟩ : ∏ t : Fin r, q t ∣ ∏ i, c i)
  rw [map_prod, map_prod, map_prod, map_prod] at hle
  rw [← hzc, ← hzq]
  exact hle

private theorem fp_quot {C : Type} [Field C] {v : Valuation C NNReal} {O : Type} [CommRing O]
    [Algebra O C] (hv : v.Integers O) (n : ℕ) (M N : Submodule O (Fin n → O)) (hM : M.FG)
    (hN : N.FG) (hle : N ≤ M) : Module.FinitePresentation O (M ⧸ N.comap M.subtype) := by
  have : IsDomain O := hv.hom_inj.isDomain
  have : IsFractionRing O C := hv.isFractionRing
  have : ValuationRing O := ValuationRing.of_integers v hv
  have : Module.Finite O M := Module.Finite.iff_fg.2 hM
  have : Module.Flat O M := by
    rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, ← Submodule.isTorsionFree_iff_torsion_eq_bot]
    infer_instance
  have : Module.Free O M := Module.free_of_flat_of_isLocalRing
  have : Module.FinitePresentation O M := Module.finitePresentation_of_projective O M
  refine Module.finitePresentation_of_surjective (N.comap M.subtype).mkQ
    (Submodule.mkQ_surjective _) ?_
  rw [Submodule.ker_mkQ]
  refine Submodule.fg_of_fg_map_injective M.subtype M.injective_subtype ?_
  rwa [Submodule.map_comap_subtype, inf_eq_right.2 hle]

theorem hasLen_exists_mono_fp : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → (∀ (M : Type) [AddCommGroup M] [Module O M], Module.FinitePresentation O M → ∃ x, HasLen v O M x) ∧ (∀ (M M' : Type) [AddCommGroup M] [Module O M] [AddCommGroup M'] [Module O M'] (f : M →ₗ[O] M') (x x' : NNReal), Function.Surjective f → HasLen v O M x → HasLen v O M' x' → x ≤ x') ∧ ∀ (n : ℕ) (M N : Submodule O (Fin n → O)), M.FG → N.FG → N ≤ M → Module.FinitePresentation O (M ⧸ N.comap M.subtype) :=
  fun _ _ _ _ _ _ hv => ⟨fun M _ _ h => hasLen_of_fp hv M h,
    fun _ _ _ _ _ _ f _ _ hf hx hx' => hasLen_mono hv f hf hx hx',
    fun n M N hM hN hle => fp_quot hv n M N hM hN hle⟩

end GlobalTheory.ChF
