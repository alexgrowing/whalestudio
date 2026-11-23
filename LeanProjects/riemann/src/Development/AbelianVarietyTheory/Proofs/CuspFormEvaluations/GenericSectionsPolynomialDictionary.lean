import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroOfReducedInputs
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.CombBound4Of
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.DescentStatementPf

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps GlobalTheory.Shares

namespace GlobalTheory.Shares.PolyDict

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j}

theorem ofWt_C {ι : Type} (u : WeightFamilies.Wt D j) (F : B.Cusp j u) :
    OfWt X u (MvPolynomial.C (X.inc u F) : MvPolynomial ι X.Forms) := by
  classical
  intro m
  rw [MvPolynomial.coeff_C]
  split_ifs
  · exact LinearMap.mem_range.mpr ⟨F, rfl⟩
  · exact Submodule.zero_mem _

theorem ofWt_sum {ι κ : Type} (u : WeightFamilies.Wt D j) (s : Finset κ) (p : κ → MvPolynomial ι X.Forms)
    (h : ∀ k ∈ s, OfWt X u (p k)) : OfWt X u (∑ k ∈ s, p k) := by
  intro m
  rw [MvPolynomial.coeff_sum]
  exact Submodule.sum_mem _ fun k hk => h k hk m

theorem ofWt_X_mul {ι : Type} (u : WeightFamilies.Wt D j) (i : ι) (p : MvPolynomial ι X.Forms) (h : OfWt X u p) :
    OfWt X u (MvPolynomial.X i * p) := by
  classical
  intro m
  rw [MvPolynomial.coeff_X_mul']
  split_ifs
  · exact h _
  · exact Submodule.zero_mem _

theorem ofWt_mul {ι : Type} (u u' : WeightFamilies.Wt D j) (p q : MvPolynomial ι X.Forms) (hp : OfWt X u p)
    (hq : OfWt X u' q) : OfWt X (wadd u u') (p * q) := by
  classical
  intro m
  rw [MvPolynomial.coeff_mul]
  refine Submodule.sum_mem _ fun x _ => ?_
  obtain ⟨F, hF⟩ := LinearMap.mem_range.mp (hp x.1)
  obtain ⟨G, hG⟩ := LinearMap.mem_range.mp (hq x.2)
  obtain ⟨H, hH⟩ := X.inc_mul u u' F G
  rw [← hF, ← hG, hH]
  exact LinearMap.mem_range_self _ _

theorem toRp_C (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ) (F : X.Forms) :
    toRp X la N (MvPolynomial.C F) = emb X la N F := MvPolynomial.eval₂Hom_C _ _ _

theorem toRp_X (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ) (p : Idx D j N) :
    toRp X la N (MvPolynomial.X p) = algebraMap (Op X la N) (Rp X la N) (Tv X la N p) := MvPolynomial.eval₂Hom_X' _ _ _

theorem toFn_C (R : Rdg X) {N : ℕ} (t : Idx D j N → ℂ) (F : X.Forms) :
    R.toFn t (MvPolynomial.C F) = R.ev F := MvPolynomial.eval₂Hom_C _ _ _

theorem toFn_X (R : Rdg X) {N : ℕ} (t : Idx D j N → ℂ) (p : Idx D j N) :
    R.toFn t (MvPolynomial.X p) = fun _ => t p := MvPolynomial.eval₂Hom_X' _ _ _

private lemma algebraMap_mul_mem_Vw (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ) (u : WeightFamilies.Wt D j)
    (x : Op X la N) {v : Rp X la N} (hv : v ∈ Vw X la N u) :
    algebraMap (Op X la N) (Rp X la N) x * v ∈ Vw X la N u := by
  rw [IsScalarTower.algebraMap_apply (Op X la N) (Kp X la N) (Rp X la N), ← Algebra.smul_def]
  exact Submodule.smul_mem _ _ hv

theorem toRp_mem (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ) (u : WeightFamilies.Wt D j)
    (p : MvPolynomial (Idx D j N) X.Forms) (hp : OfWt X u p) : toRp X la N p ∈ Vw X la N u := by
  rw [p.as_sum, map_sum]
  refine Submodule.sum_mem _ fun m _ => ?_
  obtain ⟨F, hF⟩ := LinearMap.mem_range.mp (hp m)
  have key : toRp X la N (MvPolynomial.monomial m (p.coeff m)) = emb X la N (p.coeff m) *
      m.prod fun n e => (algebraMap (Op X la N) (Rp X la N) (Tv X la N n)) ^ e := by
    rw [toRp, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_monomial]
  rw [key, ← hF, mul_comm]
  have hbase : emb X la N (X.inc u F) ∈ Vw X la N u := Submodule.subset_span ⟨F, rfl⟩
  suffices H : ∀ v ∈ Vw X la N u,
      (m.prod fun n e => (algebraMap (Op X la N) (Rp X la N) (Tv X la N n)) ^ e) * v ∈ Vw X la N u from
    H _ hbase
  unfold Finsupp.prod
  refine Finset.prod_induction _ (fun x => ∀ v ∈ Vw X la N u, x * v ∈ Vw X la N u) ?_ ?_ ?_
  · intro a b ha hb v hv
    rw [mul_assoc]
    exact ha _ (hb v hv)
  · intro v hv
    rwa [one_mul]
  · intro n _ v hv
    show algebraMap (Op X la N) (Rp X la N) (Tv X la N n) ^ (m n) * v ∈ _
    rw [← map_pow]
    exact algebraMap_mul_mem_Vw la N u _ hv

theorem toFn_mem (R : Rdg X) {N : ℕ} (t : Idx D j N → ℂ) (u : WeightFamilies.Wt D j)
    (p : MvPolynomial (Idx D j N) X.Forms) (hp : OfWt X u p) : R.toFn t p ∈ R.sp u Set.univ := by
  rw [p.as_sum, map_sum]
  refine Submodule.sum_mem _ fun m _ => ?_
  obtain ⟨F, hF⟩ := LinearMap.mem_range.mp (hp m)
  have key : R.toFn t (MvPolynomial.monomial m (p.coeff m)) = R.ev (p.coeff m) *
      m.prod fun n e => (fun _ : R.Y => t n) ^ e := by
    rw [Rdg.toFn, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_monomial]
  rw [key, ← hF, mul_comm]
  have hbase : R.ev (X.inc u F) ∈ R.sp u Set.univ := Submodule.subset_span ⟨F, Set.mem_univ _, rfl⟩
  suffices H : ∀ v ∈ R.sp u Set.univ,
      (m.prod fun n e => (fun _ : R.Y => t n) ^ e) * v ∈ R.sp u Set.univ from H _ hbase
  unfold Finsupp.prod
  refine Finset.prod_induction _ (fun x => ∀ v ∈ R.sp u Set.univ, x * v ∈ R.sp u Set.univ) ?_ ?_ ?_
  · intro a b ha hb v hv
    rw [mul_assoc]
    exact ha _ (hb v hv)
  · intro v hv
    rwa [one_mul]
  · intro n _ v hv
    show (fun _ : R.Y => t n) ^ (m n) * v ∈ _
    have hc : (fun _ : R.Y => t n) ^ (m n) * v = (t n ^ m n) • v := by
      funext y
      simp [Pi.pow_apply, Pi.mul_apply, Pi.smul_apply]
    rw [hc]
    exact Submodule.smul_mem _ _ hv

theorem sp_mul (R : Rdg X) (u u' : WeightFamilies.Wt D j) (f : R.Y → ℂ) (hf : f ∈ R.sp u Set.univ) (g : R.Y → ℂ)
    (hg : g ∈ R.sp u' Set.univ) : f * g ∈ R.sp (wadd u u') Set.univ := by
  have hfg := Submodule.mul_mem_mul hf hg
  simp only [Rdg.sp, Submodule.span_mul_span] at hfg ⊢
  refine Submodule.span_le.mpr ?_ hfg
  rintro _ ⟨_, ⟨F, -, rfl⟩, _, ⟨G, -, rfl⟩, rfl⟩
  obtain ⟨H, hH⟩ := X.inc_mul u u' F G
  show R.ev (X.inc u F) * R.ev (X.inc u' G) ∈ _
  rw [← map_mul R.ev, hH]
  exact Submodule.subset_span ⟨H, Set.mem_univ _, rfl⟩

theorem sp_span (R : Rdg X) (u : WeightFamilies.Wt D j) (s : Set (B.Cusp j u)) :
    R.sp u (Submodule.span B.KO s) = R.sp u s := by
  unfold Rdg.sp
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨F, hF, rfl⟩
    have hF' : F ∈ Submodule.span B.KO s := hF
    clear hF
    induction hF' using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero =>
      simp only [map_zero]
      exact Submodule.zero_mem _
    | add x y _ _ hx hy =>
      simp only [map_add]
      exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      simp only [map_smul, R.ev_smul]
      exact Submodule.smul_mem _ _ hx
  · exact Submodule.span_mono (Set.image_mono Submodule.subset_span)

theorem sp_finrank (R : Rdg X) (u : WeightFamilies.Wt D j) (M : Submodule B.KO (B.Cusp j u)) :
    FiniteDimensional ℂ (R.sp u M) ∧ Module.finrank ℂ (R.sp u M) = Module.finrank B.KO M := by
  let b := Module.finBasis B.KO M
  have hli : LinearIndependent B.KO (fun i => (b i : B.Cusp j u)) :=
    b.linearIndependent.map' M.subtype (Submodule.ker_subtype M)
  have hli' := R.indep u _ _ hli
  have hspan : Submodule.span B.KO (Set.range fun i => (b i : B.Cusp j u)) = M := by
    rw [show (Set.range fun i => (b i : B.Cusp j u)) = M.subtype '' Set.range b from Set.range_comp _ _,
      Submodule.span_image, b.span_eq, Submodule.map_subtype_top]
  have hs := sp_span R u (Set.range fun i => (b i : B.Cusp j u))
  rw [hspan] at hs
  have e : R.sp u (M : Set (B.Cusp j u)) =
      Submodule.span ℂ (Set.range fun i => R.ev (X.inc u (b i : B.Cusp j u))) := by
    rw [hs]
    unfold Rdg.sp
    rw [← Set.range_comp]
    rfl
  rw [e]
  exact ⟨FiniteDimensional.span_of_finite ℂ (Set.finite_range _),
    (finrank_span_eq_card hli').trans (Fintype.card_fin _)⟩

end GlobalTheory.Shares.PolyDict

namespace GlobalTheory.Shares

open PolyDict in

theorem polyDictionary : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (R : Rdg X) (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ) (wL : WeightFamilies.Wt D j) (w : Fin N → B.Cusp j wL) (t : Idx D j N → ℂ), (∀ i, toRp X la N (∑ k, MvPolynomial.X (i, k) * MvPolynomial.C (X.inc wL (w k))) = sec X la w i ∧ R.toFn t (∑ k, MvPolynomial.X (i, k) * MvPolynomial.C (X.inc wL (w k))) = R.s w t i ∧ OfWt X wL (∑ k, MvPolynomial.X (i, k) * MvPolynomial.C (X.inc wL (w k)) : MvPolynomial (Idx D j N) X.Forms)) ∧ (∀ F, toRp X la N (MvPolynomial.C F) = emb X la N F ∧ R.toFn t (MvPolynomial.C F) = R.ev F) ∧ (∀ u (F : B.Cusp j u), OfWt X u (MvPolynomial.C (X.inc u F) : MvPolynomial (Idx D j N) X.Forms)) ∧ (∀ u u' (p q : MvPolynomial (Idx D j N) X.Forms), OfWt X u p → OfWt X u' q → OfWt X (wadd u u') (p * q)) ∧ (∀ u (p : MvPolynomial (Idx D j N) X.Forms), OfWt X u p → toRp X la N p ∈ Vw X la N u ∧ R.toFn t p ∈ R.sp u Set.univ) ∧ (∀ u u', ∀ f ∈ R.sp u Set.univ, ∀ g ∈ R.sp u' Set.univ, f * g ∈ R.sp (wadd u u') Set.univ) ∧ (∀ u (s : Set (B.Cusp j u)), R.sp u (Submodule.span B.KO s) = R.sp u s) ∧ (∀ u (M : Submodule B.KO (B.Cusp j u)), FiniteDimensional ℂ (R.sp u M) ∧ Module.finrank ℂ (R.sp u M) = Module.finrank B.KO M) := by
  intro D B P j X R la N wL w t
  refine ⟨fun i => ⟨?_, ?_, ?_⟩, fun F => ⟨PolyDict.toRp_C la N F, PolyDict.toFn_C R t F⟩,
    fun u F => PolyDict.ofWt_C u F, fun u u' p q hp hq => PolyDict.ofWt_mul u u' p q hp hq,
    fun u p hp => ⟨PolyDict.toRp_mem la N u p hp, PolyDict.toFn_mem R t u p hp⟩,
    fun u u' f hf g hg => PolyDict.sp_mul R u u' f hf g hg,
    fun u s => PolyDict.sp_span R u s, fun u M => PolyDict.sp_finrank R u M⟩
  · rw [map_sum]
    unfold Formalism.MainNotions.Gaps.EtaleWeightGaps.sec
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, PolyDict.toRp_X, PolyDict.toRp_C, Algebra.smul_def,
      IsScalarTower.algebraMap_apply (Op X la N) (Kp X la N) (Rp X la N)]
  · rw [map_sum]
    unfold Rdg.s
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, PolyDict.toFn_X, PolyDict.toFn_C]
    funext y
    simp [Pi.mul_apply, Pi.smul_apply]
  · exact PolyDict.ofWt_sum wL _ _ fun k _ => PolyDict.ofWt_X_mul wL _ _ (PolyDict.ofWt_C wL (w k))

end GlobalTheory.Shares
