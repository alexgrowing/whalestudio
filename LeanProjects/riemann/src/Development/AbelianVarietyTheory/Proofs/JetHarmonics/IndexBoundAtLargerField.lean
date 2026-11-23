import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ThetaLeMsupOfSetC
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.WeightedPrimeSumBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LatOfLamSt
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.WeightParameterMemUnitInterval

open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.FormTies
open scoped TensorProduct

namespace GlobalTheory.FormTies

theorem ringOfIntegersAlgebra_eq {F K : Type} [Field F] [Field K] [Algebra F K] (A : Algebra (𝓞 F) (𝓞 K))
    (h : ∀ x : 𝓞 F, ((@algebraMap (𝓞 F) (𝓞 K) _ _ A x : 𝓞 K) : K) = algebraMap F K (x : F)) :
    A = NumberField.inst_ringOfIntegersAlgebra F K := by
  refine Algebra.algebra_ext _ _ fun x => ?_
  apply NumberField.RingOfIntegers.ext
  rw [h x]
  rfl

noncomputable def coordMap {F : Type} [Field F] {K : Type} [Field K] [Algebra F K] {C : Type} [AddCommGroup C]
    [Module F C] {n : ℕ} (z : (Fin n → K) ≃ₗ[K] K ⊗[F] C) : C →ₗ[F] (Fin n → K) :=
  ((z.symm : K ⊗[F] C →ₗ[K] (Fin n → K)).restrictScalars F).comp (TensorProduct.mk F K C 1)

theorem coordMap_linearIndependent {F : Type} [Field F] {K : Type} [Field K] [Algebra F K] {C : Type} [AddCommGroup C]
    [Module F C] {n : ℕ} (z : (Fin n → K) ≃ₗ[K] K ⊗[F] C) (m : ℕ) (b : Fin m → C) (hb : LinearIndependent F b) :
    LinearIndependent K fun a => coordMap z (b a) :=
  (Module.Flat.linearIndependent_one_tmul (S := K) hb).map' (z.symm : K ⊗[F] C →ₗ[K] (Fin n → K)) z.symm.ker

theorem coordMap_span {F : Type} [Field F] {K : Type} [Field K] [Algebra F K] {C : Type} [AddCommGroup C]
    [Module F C] {n : ℕ} (z : (Fin n → K) ≃ₗ[K] K ⊗[F] C) : Submodule.span K (Set.range (coordMap z)) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  obtain ⟨y, rfl⟩ := z.symm.surjective x
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a f =>
    have e : a ⊗ₜ[F] f = a • ((1 : K) ⊗ₜ[F] f) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [e, map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨f, rfl⟩)
  | add x y hx hy =>
    rw [map_add]
    exact Submodule.add_mem _ (hx trivial) (hy trivial)

theorem index_bound_at_larger_field : ∀ (D : D7) (B : WeightFamilies.Prov D) (P6 : ModuliIntegralCharts.Prov D) (j : ℕ) (X : WeightAlgebra.PJ D B P6 j) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (p : ℕ) (ka wL wF : WeightFamilies.Wt D j) (T : ℕ) (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ) (β : ℝ), 0 < p → WeightAlgebra.IsF' ka wL wF T wF.n → ka.n = wF.n + T * wL.n → WeightFamilies.dimY D j ≤ T → Submodule.IsLattice B.KO (B.Mlat j ka) → ReciprocityTheory.ChartRestriction.G.PullbackSections.SpanAt X ka → WeightAlgebra.H2 X (scalOfP B hinj EX p ka wL wF T) ka wL wF → WeightAlgebra.Concl X (scalOfP B hinj EX p ka wL wF T) ka wL wF T nus β → ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [Algebra B.KO K] [Algebra (𝓞 B.KO) (𝓞 K)] [Algebra.IsIntegral (𝓞 B.KO) (𝓞 K)], (∀ x : 𝓞 B.KO, ((algebraMap (𝓞 B.KO) (𝓞 K) x : 𝓞 K) : K) = algebraMap B.KO K (x : B.KO)) → ∃ r : HeightOneSpectrum (𝓞 K) → ℝ, (∀ v, 0 ≤ r v) ∧ (∀ S' : Finset (HeightOneSpectrum (𝓞 K)), ∑ v ∈ S', Formalism.DivisionValues.lw v * r v ≤ β) ∧ ∀ (Bs : DefBase K) (Df : DefSide Bs) (S : IndefData Df) (P : Type) [Group P] [Finite P] (oc : OnConst) (O : OnObj S P oc) (v : HeightOneSpectrum (𝓞 K)) (i : Bs.J) (z : (Fin (O.nZ i) → K) ≃ₗ[K] K ⊗[B.KO] B.Cusp j ka) (act : P → B.Cusp j ka → B.Cusp j ka), FormTie X hinj EX p ka wL wF T O v i z act → ∀ e : ℕ, (T : ℝ) * nus (placeBelow (K := B.KO) v) ≤ e → ∀ W : Submodule K (Fin (O.nZ i) → K), (lix v (cut W (O.Ms i)) (cut W (O.Th v i)) : ℝ) ≤ ((ramOver (K := B.KO) v * e : ℕ) : ℝ) * (Module.finrank K W : ℝ) + r v := by
  intro D B P6 j X hinj EX p ka wL wF T nus β _ _ _ _ hM _ _ hC K _ _ _ _ A hint hA
  obtain rfl := ringOfIntegersAlgebra_eq A hA
  let Q : Formalism.MainNotions.Gaps.LocalGlobalPassage.Run D B P6 := ⟨j, X, scalOfP B hinj EX p ka wL wF T, ka, wL, wF, T, nus, β⟩
  obtain ⟨r, h0, h1, h2, h3⟩ := Formalism.MainNotions.Gaps.LocalGlobalPassage.l2 Q (fun la => Formalism.MainNotions.Gaps.LocalGlobalPassage.l1 la)
    (fun la => Formalism.MainNotions.Gaps.LocalGlobalPassage.l1b la) (fun la => Formalism.MainNotions.Gaps.LocalGlobalPassage.l1c la) hM hC
  refine ⟨fun v => (v.asIdeal.ramificationIdx (𝓞 B.KO) : ℝ) * r (v.under (𝓞 B.KO)),
    fun v => mul_nonneg (Nat.cast_nonneg _) (h0 _), fun S' => (Formalism.MainNotions.Gaps.LocalGlobalPassage.l4 r h0 h1 S').trans h2, ?_⟩
  intro Bs Df S P _ _ oc O v i z act ht e he W
  have hpl : placeBelow (K := B.KO) v = v.under (𝓞 B.KO) := rfl
  have hram : ramOver (K := B.KO) v = v.asIdeal.ramificationIdx (𝓞 B.KO) := Formalism.MainNotions.Gaps.LocalGlobalPassage.ram_eq v
  obtain ⟨h4, h5⟩ := h3 (v.under (𝓞 B.KO))
  have hMs : O.Ms i = Formalism.MainNotions.Gaps.LocalGlobalPassage.up (coordMap z) Q.M0 := ht.Ms_eq
  have hTh : Formalism.MainNotions.Gaps.LocalGlobalPassage.up (coordMap z) (Q.M0 ⊓ Q.Th0) ≤ O.Th v i := by
    rw [ht.Th_eq]
    exact Submodule.span_mono (Set.image_mono fun f hf => hf.2)
  rw [hMs]
  exact Formalism.MainNotions.Gaps.LocalGlobalPassage.l5 (coordMap z) (coordMap_linearIndependent z) (coordMap_span z) Q.M0 (Q.M0 ⊓ Q.Th0) hM.fg
    hM.span_eq_top h4 inf_le_left v e (r (v.under (𝓞 B.KO))) (ramOver (K := B.KO) v * e)
    (by rw [hram]; push_cast; rfl) (h5 e (by rw [Int.cast_natCast, ← hpl]; exact he)) (O.Th v i) hTh W

end GlobalTheory.FormTies
