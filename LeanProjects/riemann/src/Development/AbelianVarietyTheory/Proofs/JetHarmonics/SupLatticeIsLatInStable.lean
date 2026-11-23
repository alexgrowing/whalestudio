import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ThetaLeMsupOfSetC
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.WeightedPrimeSumBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LatOfLamSt
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed

set_option autoImplicit false

open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.FormTies
open scoped TensorProduct

namespace GlobalTheory.FormTies

section General

variable {F : Type} [Field F] {K : Type} [Field K] [NumberField K] [Algebra F K]
  {C : Type} [AddCommGroup C] [Module F C] [Module (𝓞 F) C] [IsScalarTower (𝓞 F) F C] {n : ℕ}

omit [NumberField K] [Module (𝓞 F) C] [IsScalarTower (𝓞 F) F C] in

theorem coord_one_tmul_smul (z : (Fin n → K) ≃ₗ[K] K ⊗[F] C) (r : F) (f : C) :
    z.symm (1 ⊗ₜ[F] (r • f)) = algebraMap F K r • z.symm (1 ⊗ₜ[F] f) := by
  rw [← map_smul, TensorProduct.tmul_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul',
    Algebra.smul_def, smul_eq_mul]

theorem spanK_span (z : (Fin n → K) ≃ₗ[K] K ⊗[F] C) (s : Set C) :
    spanK z (Submodule.span (𝓞 F) s : Set C) = spanK z s := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨f, hf, rfl⟩
    induction hf using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero => simp
    | add x y _ _ hx hy =>
      simp only [TensorProduct.tmul_add, map_add]
      exact Submodule.add_mem _ hx hy
    | smul r x _ hx =>
      have hi : IsIntegral ℤ (algebraMap F K (r : F)) :=
        (RingOfIntegers.isIntegral_coe r).map (algebraMap F K).toIntAlgHom
      have e : z.symm (1 ⊗ₜ[F] (r • x)) = (⟨algebraMap F K (r : F), hi⟩ : 𝓞 K) • z.symm (1 ⊗ₜ[F] x) := by
        rw [← algebraMap_smul F r x, coord_one_tmul_smul]
        rfl
      simp only [e]
      exact Submodule.smul_mem _ _ hx
  · exact Submodule.span_mono (Set.image_mono Submodule.subset_span)

theorem spanK_isLatIn (z : (Fin n → K) ≃ₗ[K] K ⊗[F] C) (M : Submodule (𝓞 F) C) (hfg : M.FG)
    (htop : Submodule.span F (M : Set C) = ⊤) : Formalism.EigenvalueLevelCeiling.IsLatIn ⊤ (spanK z (M : Set C)) := by
  constructor
  · obtain ⟨s, rfl⟩ := hfg
    rw [spanK_span]
    exact Submodule.fg_span (s.finite_toSet.image _)
  · have h1 : ∀ f : C, z.symm (1 ⊗ₜ[F] f) ∈ Submodule.span K (spanK z (M : Set C) : Set (Fin n → K)) := by
      intro f
      have hf : f ∈ Submodule.span F (M : Set C) := htop ▸ Submodule.mem_top
      induction hf using Submodule.span_induction with
      | mem x hx => exact Submodule.subset_span (Submodule.subset_span ⟨x, hx, rfl⟩)
      | zero => simp
      | add x y _ _ hx hy =>
        simp only [TensorProduct.tmul_add, map_add]
        exact Submodule.add_mem _ hx hy
      | smul r x _ hx =>
        rw [coord_one_tmul_smul]
        exact Submodule.smul_mem _ _ hx
    rw [eq_top_iff]
    intro x _
    obtain ⟨t, rfl⟩ := z.symm.surjective x
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul k f =>
      have e : (k ⊗ₜ[F] f : K ⊗[F] C) = k • (1 ⊗ₜ[F] f) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [e, map_smul]
      exact Submodule.smul_mem _ _ (h1 f)
    | add x y hx hy =>
      rw [map_add]
      exact Submodule.add_mem _ (hx trivial) (hy trivial)

end General

theorem supLattice_isLatIn_stable : ∀ (D : D7) (B : WeightFamilies.Prov D) (P6 : ModuliIntegralCharts.Prov D) (j : ℕ) (X : WeightAlgebra.PJ D B P6 j) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (p : ℕ) (ka wL wF : WeightFamilies.Wt D j) (T : ℕ) (K : Type) [Field K] [NumberField K] [StarRing K] [Algebra B.KO K] (Bs : DefBase K) (Df : DefSide Bs) (S : IndefData Df) (P : Type) [Group P] [Finite P] (oc : OnConst) (O : OnObj S P oc) (v : HeightOneSpectrum (𝓞 K)) (i : Bs.J) (z : (Fin (O.nZ i) → K) ≃ₗ[K] K ⊗[B.KO] B.Cusp j ka) (act : P → B.Cusp j ka → B.Cusp j ka), FormTie X hinj EX p ka wL wF T O v i z act → Submodule.IsLattice B.KO (B.Mlat j ka) → (∀ g, ∀ F ∈ B.Mlat j ka, act g F ∈ B.Mlat j ka) → Formalism.EigenvalueLevelCeiling.IsLatIn ⊤ (O.Ms i) ∧ ∀ g : P, (O.Ms i).map ((O.ρ i g).restrictScalars (𝓞 K)) ≤ O.Ms i := by
  intro D B P6 j X hinj EX p ka wL wF T K _ _ _ _ Bs Df S P _ _ oc O v i z act h hL hact
  rw [h.Ms_eq]
  refine ⟨spanK_isLatIn z _ hL.fg hL.span_eq_top, fun g => ?_⟩
  rw [Submodule.map_le_iff_le_comap]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨f, hf, rfl⟩
  show O.ρ i g (z.symm (1 ⊗ₜ f)) ∈ spanK z _
  rw [h.rho_eq]
  exact Submodule.subset_span ⟨act g f, hact g f hf, rfl⟩

end GlobalTheory.FormTies
