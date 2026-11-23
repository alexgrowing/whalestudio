import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ThetaLeMsupOfSetC
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.WeightedPrimeSumBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LatOfLamSt
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LogNormNormaliserEqHalfDegreeLog
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RamifiedPrimePowersSizeBounds

open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.FormTies
open scoped TensorProduct

namespace GlobalTheory.FormTies

section General

variable {F : Type} [Field F] {K : Type} [Field K] [NumberField K] [Algebra F K] {C : Type} [AddCommGroup C]
  [Module F C] {n : ℕ} (z : (Fin n → K) ≃ₗ[K] K ⊗[F] C)

theorem spanK_fg_of_subset [Module (𝓞 F) C] [IsScalarTower (𝓞 F) F C] (N : Submodule (𝓞 F) C) (hN : N.FG)
    (s : Set C) (hs : s ⊆ N) : (spanK z s).FG := by
  classical
  obtain ⟨t, ht⟩ := hN
  have hle : spanK z s ≤ spanK z (t : Set C) := by
    unfold spanK
    rw [Submodule.span_le]
    rintro _ ⟨f, hf, rfl⟩
    have hf' : f ∈ Submodule.span (𝓞 F) (t : Set C) := ht ▸ hs hf
    clear hf
    induction hf' using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero => simp
    | add x y _ _ hx hy =>
      simp only [TensorProduct.tmul_add, map_add]
      exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      have e : z.symm (1 ⊗ₜ[F] (a • x)) =
          (RingOfIntegers.mapRingHom (algebraMap F K) a) • z.symm (1 ⊗ₜ[F] x) := by
        rw [← algebraMap_smul F a x, TensorProduct.tmul_smul, ← algebraMap_smul K, map_smul,
          ← algebraMap_smul K (RingOfIntegers.mapRingHom (algebraMap F K) a)]
        rfl
      beta_reduce
      rw [e]
      exact Submodule.smul_mem _ _ hx
  have hfg : (spanK z (t : Set C)).FG := Submodule.fg_span (t.finite_toSet.image _)
  exact hfg.of_le hle

theorem span_spanK_eq_top (s : Set C) (hs : Submodule.span F s = ⊤) :
    Submodule.span K (spanK z s : Set (Fin n → K)) = ⊤ := by
  have h1 : ∀ f : C, z.symm (1 ⊗ₜ[F] f) ∈ Submodule.span K (spanK z s : Set (Fin n → K)) := by
    intro f
    have hf : f ∈ Submodule.span F s := hs ▸ Submodule.mem_top
    induction hf using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span (Submodule.subset_span ⟨x, hx, rfl⟩)
    | zero => simp
    | add x y _ _ hx hy =>
      simp only [TensorProduct.tmul_add, map_add]
      exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      rw [TensorProduct.tmul_smul, ← algebraMap_smul K, map_smul]
      exact Submodule.smul_mem _ _ hx
  rw [eq_top_iff]
  intro x _
  obtain ⟨y, rfl⟩ := z.symm.surjective x
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a f =>
    have e : a ⊗ₜ[F] f = a • ((1 : K) ⊗ₜ[F] f) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [e, map_smul]
    exact Submodule.smul_mem _ _ (h1 f)
  | add x y hx hy =>
    rw [map_add]
    exact Submodule.add_mem _ (hx trivial) (hy trivial)

end General

theorem scalOfP_sK_ne_zero {D : D7} (B : WeightFamilies.Prov D) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D)
    {j : ℕ} (p : ℕ) (hp : 0 < p) (ka wL wF : WeightFamilies.Wt D j) (T : ℕ) :
    (scalOfP B hinj EX p ka wL wF T).sK ≠ 0 := by
  obtain ⟨σ⟩ : Nonempty (B.KO →+* ℂ) := inferInstance
  have h1 := fun w => (GlobalTheory.log_norm_normaliser D B hinj EX j w σ).1
  have h2 := fun a b c => ((GlobalTheory.RunIn.pPow_size D j ka).2.2.2.2.2 a b c).1
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ (pow_ne_zero _ (h1 _))) (h1 _)) ?_
  · exact Nat.cast_ne_zero.2 (pow_ne_zero _ hp.ne')
  · exact Nat.cast_ne_zero.2 (Nat.one_le_iff_ne_zero.1 (h2 _ _ _))

theorem theta_spans_isLatIn : ∀ (D : D7) (B : WeightFamilies.Prov D) (P6 : ModuliIntegralCharts.Prov D) (j : ℕ) (X : WeightAlgebra.PJ D B P6 j) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (p : ℕ) (ka wL wF : WeightFamilies.Wt D j) (T : ℕ) (K : Type) [Field K] [NumberField K] [StarRing K] [Algebra B.KO K] (Bs : DefBase K) (Df : DefSide Bs) (S : IndefData Df) (P : Type) [Group P] [Finite P] (oc : OnConst) (O : OnObj S P oc) (v : HeightOneSpectrum (𝓞 K)) (i : Bs.J) (z : (Fin (O.nZ i) → K) ≃ₗ[K] K ⊗[B.KO] B.Cusp j ka) (act : P → B.Cusp j ka → B.Cusp j ka), FormTie X hinj EX p ka wL wF T O v i z act → 0 < p → WeightAlgebra.IsF' ka wL wF T wF.n → ka.n = wF.n + T * wL.n → WeightFamilies.dimY D j ≤ T → Submodule.IsLattice B.KO (B.Mlat j ka) → ReciprocityTheory.ChartRestriction.G.PullbackSections.SpanAt X ka → WeightAlgebra.H2 X (scalOfP B hinj EX p ka wL wF T) ka wL wF → Formalism.EigenvalueLevelCeiling.IsLatIn ⊤ (O.Th v i) ∧ Formalism.EigenvalueLevelCeiling.IsLatIn ⊤ (O.ThK v i) := by
  intro D B P6 j X hinj EX p ka wL wF T K _ _ _ _ Bs Df S P _ _ oc O v i z act ht hp hF hn hD hM hSp h2
  have hle := Formalism.MainNotions.Gaps.T0.theta_le_msup X _ h2 hF rfl hn hD
  refine ⟨⟨?_, ?_⟩, ht.ThK_fg, ?_⟩
  · rw [ht.Th_eq]
    refine spanK_fg_of_subset z (B.Mlat j ka) hM.fg _ fun f hf => ?_
    obtain ⟨g, hg, e⟩ := Submodule.mem_map.1 (hle hf)
    exact X.inc_inj ka e ▸ hg
  · rw [ht.Th_eq]
    apply span_spanK_eq_top
    rw [eq_top_iff, ← hSp, Submodule.span_le]
    intro g hg
    set c : 𝓞 B.KO := (scalOfP B hinj EX p ka wL wF T).sK *
      ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 B.KO) ^ (D.R.f * D.R.r * ka.n) with hc
    have hc0 : c ≠ 0 := mul_ne_zero (scalOfP_sK_ne_zero B hinj EX p hp ka wL wF T)
      (pow_ne_zero _ (Nat.cast_ne_zero.2
        (Nat.mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero)))
    have hc1 : algebraMap (𝓞 B.KO) B.KO c ≠ 0 := fun h0 => hc0 (RingOfIntegers.coe_eq_zero_iff.1 h0)
    have hmem : c • g ∈ X.Thc (scalOfP B hinj EX p ka wL wF T).sK ka :=
      ⟨_, ⟨g, hg, rfl⟩, by rw [hc, mul_smul]; rfl⟩
    have e : g = (algebraMap (𝓞 B.KO) B.KO c)⁻¹ • (c • g) := by
      rw [← algebraMap_smul B.KO c g, smul_smul, inv_mul_cancel₀ hc1, one_smul]
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Submodule.mem_sup_right ⟨_, hmem, rfl⟩))
  · rw [eq_top_iff, ← span_spanK_eq_top z {F | X.inc ka F ∈ thetaPlain X ka wL wF T}]
    · exact Submodule.span_mono ht.ThK_ge
    · rw [eq_top_iff, ← hSp]
      exact Submodule.span_mono fun g hg => Submodule.mem_sup_right ⟨g, hg, rfl⟩

end GlobalTheory.FormTies
