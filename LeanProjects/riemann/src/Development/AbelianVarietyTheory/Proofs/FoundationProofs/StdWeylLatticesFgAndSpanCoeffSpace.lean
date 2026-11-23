import Mathlib
import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
import Formalism.LocalToGlobal.Columns.PolyFnLemmas

open NumberField MvPolynomial Formalism.BasicNotions Formalism.L2.DIV

noncomputable section

namespace GlobalTheory.StdLatSpan

variable (K : Type) [Field K] [NumberField K]

theorem toK_apply {σ : Type} (f : MvPolynomial σ (𝓞 K)) : toK K σ f = map (algebraMap (𝓞 K) K) f := rfl

open NumberField MvPolynomial Pointwise in
variable (K : Type) [Field K] [NumberField K] in
private lemma nabStd_fg' (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι] (n : ℕ)
    (lam : ι → _root_.Formalism.BasicNotions.DomWeight n) : (_root_.Formalism.L2.DIV.nabStd K lam).FG := by
  classical
  unfold _root_.Formalism.L2.DIV.nabStd
  choose b hb _ using fun τ : ι => _root_.Formalism.GradedWeylDivisibility.sSBasis (𝓞 K) n n (lam τ).natW
  have hinj : LinearMap.ker (_root_.Formalism.L2.DIV.toK K (Fin n × Fin n)) = ⊥ :=
    LinearMap.ker_eq_bot.mpr (MvPolynomial.map_injective _ (IsFractionRing.injective (𝓞 K) K))
  have hwb : ∀ τ, LinearIndependent (𝓞 K) (b τ) ∧
      Submodule.span (𝓞 K) (Set.range (b τ)) = _root_.Formalism.GradedWeylDivisibility.dualWeyl (𝓞 K) n n (lam τ).natW := by
    intro τ
    have h := hb τ
    unfold _root_.Formalism.GradedWeylDivisibility.IsWeightBasis at h
    exact ⟨h.1, h.2.1⟩
  haveI : ∀ τ, Finite ↑(_root_.Formalism.GradedWeylDivisibility.ssIdx n n (lam τ).natW) := fun τ => (_root_.Formalism.GradedWeylDivisibility.sSIdxFinite n n _).to_subtype
  obtain ⟨-, hspan⟩ := _root_.Formalism.GradedWeylDivisibility.tensorBasis (𝓞 K) K ι n n (fun τ => ↑(_root_.Formalism.GradedWeylDivisibility.ssIdx n n (lam τ).natW))
    (fun τ => Submodule.map (_root_.Formalism.L2.DIV.toK K (Fin n × Fin n)) (_root_.Formalism.BasicNotions.nablaSq (𝓞 K) n (lam τ)))
    (fun τ i => _root_.Formalism.L2.DIV.toK K (Fin n × Fin n) (b τ i))
    (fun τ => (hwb τ).1.map' _ hinj)
    (fun τ => by
      rw [Set.range_comp' (g := _root_.Formalism.L2.DIV.toK K (Fin n × Fin n)) (f := b τ), ← Submodule.map_span, (hwb τ).2]
      rfl)
  rw [← hspan]
  exact Submodule.fg_def.mpr ⟨_, Set.finite_range _, rfl⟩

open NumberField MvPolynomial Pointwise in
variable (K : Type) [Field K] [NumberField K] in
private lemma prod_image_blockEmb_eq_setOf_prod {K : Type} [Field K] {S : Type} [Fintype S] {k n : ℕ}
    (X : S → Set (MvPolynomial (Fin k × Fin n) K)) :
    (∏ s ∈ Finset.univ, (_root_.Formalism.GradedWeylDivisibility.blockEmb K s : MvPolynomial (Fin k × Fin n) K → _) '' X s) =
      {P | ∃ F : S → MvPolynomial (Fin k × Fin n) K, (∀ s, F s ∈ X s) ∧
        P = ∏ s, _root_.Formalism.GradedWeylDivisibility.blockEmb K s (F s)} := by
  ext P
  rw [Set.mem_finset_prod]
  constructor
  · rintro ⟨g, hg, rfl⟩
    choose F hF hFe using fun s => hg (Finset.mem_univ s)
    exact ⟨F, hF, Finset.prod_congr rfl fun s _ => (hFe s).symm⟩
  · rintro ⟨F, hF, rfl⟩
    exact ⟨fun s => _root_.Formalism.GradedWeylDivisibility.blockEmb K s (F s), fun {s} _ => ⟨F s, hF s, rfl⟩, rfl⟩

open NumberField MvPolynomial Pointwise in
variable (K : Type) [Field K] [NumberField K] in
private lemma span_setOf_prod_blockEmb_eq_prod_map_span {K : Type} [Field K] {S : Type} [Fintype S] {k n : ℕ}
    (X : S → Set (MvPolynomial (Fin k × Fin n) K)) :
    Submodule.span K {P | ∃ F : S → MvPolynomial (Fin k × Fin n) K, (∀ s, F s ∈ X s) ∧
        P = ∏ s, _root_.Formalism.GradedWeylDivisibility.blockEmb K s (F s)} =
      ∏ s, Submodule.map (_root_.Formalism.GradedWeylDivisibility.blockEmb K s).toLinearMap (Submodule.span K (X s)) := by
  rw [← prod_image_blockEmb_eq_setOf_prod, ← Submodule.prod_span]
  simp only [Submodule.map_span, AlgHom.coe_toLinearMap]

open NumberField MvPolynomial Pointwise in
variable (K : Type) [Field K] [NumberField K] in
private lemma span_tensorLat_eq_prod_map_span {R K : Type} [CommRing R] [Field K] [Algebra R K] {S : Type} [Fintype S]
    {k n : ℕ} (L : S → Submodule R (MvPolynomial (Fin k × Fin n) K)) :
    Submodule.span K (_root_.Formalism.GradedWeylDivisibility.tensorLat R K L : Set (MvPolynomial (S × Fin k × Fin n) K)) =
      ∏ s, Submodule.map (_root_.Formalism.GradedWeylDivisibility.blockEmb K s).toLinearMap (Submodule.span K (L s : Set _)) := by
  unfold _root_.Formalism.GradedWeylDivisibility.tensorLat
  rw [Submodule.span_span_of_tower]
  exact span_setOf_prod_blockEmb_eq_prod_map_span (K := K) (k := k) (n := n)
    fun s => (L s : Set (MvPolynomial (Fin k × Fin n) K))

open NumberField MvPolynomial Pointwise in
variable (K : Type) [Field K] [NumberField K] in
private lemma span_map_toK_nablaSq_eq_nablaSq (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : _root_.Formalism.BasicNotions.DomWeight n) :
    Submodule.span K (Submodule.map (_root_.Formalism.L2.DIV.toK K (Fin n × Fin n)) (_root_.Formalism.BasicNotions.nablaSq (𝓞 K) n μ) : Set _) =
      _root_.Formalism.BasicNotions.nablaSq K n μ := by
  unfold _root_.Formalism.BasicNotions.nablaSq
  obtain ⟨b, hb, -⟩ := _root_.Formalism.GradedWeylDivisibility.sSBasis (𝓞 K) n n μ.natW
  rw [← _root_.Formalism.GradedWeylDivisibility.span_map_weightBasis_eq_dualWeyl (K := K) hb]
  have hspan : Submodule.span (𝓞 K) (Set.range b) = _root_.Formalism.GradedWeylDivisibility.dualWeyl (𝓞 K) n n μ.natW := by
    unfold _root_.Formalism.GradedWeylDivisibility.IsWeightBasis at hb
    exact hb.2.1
  rw [← hspan, Submodule.map_span, Submodule.span_span_of_tower, ← Set.range_comp]
  rfl

open NumberField MvPolynomial Pointwise in
variable (K : Type) [Field K] [NumberField K] in
private lemma span_map_toK_delSq_eq_nablaSq (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : _root_.Formalism.BasicNotions.DomWeight n) :
    Submodule.span K (Submodule.map (_root_.Formalism.L2.DIV.toK K (Fin n × Fin n)) (_root_.Formalism.BasicNotions.delSq (𝓞 K) n μ) : Set _) =
      _root_.Formalism.BasicNotions.nablaSq K n μ := by
  rw [_root_.Formalism.L2.Col.nablaSq_eq_delSq]
  unfold _root_.Formalism.BasicNotions.delSq _root_.Formalism.GradedWeylDivisibility.weyl
  rw [Submodule.map_span, Submodule.span_span_of_tower, ← Set.range_comp]
  congr 2
  funext w
  change MvPolynomial.map (algebraMap (𝓞 K) K) _ = _
  rw [← _root_.Formalism.GradedWeylDivisibility.lclosedeq_applyWord_map, _root_.Formalism.GradedWeylDivisibility.lclosedeq_hw_map]

open NumberField MvPolynomial Pointwise in
variable (K : Type) [Field K] [NumberField K] in

theorem _root_.GlobalTheory.StdLatSpan.std_fg_span : ∀ (K : Type) [Field K] [NumberField K] (ι : Type)
    [Fintype ι] (n : ℕ) (lam : ι → _root_.Formalism.BasicNotions.DomWeight n),
    (_root_.Formalism.L2.DIV.nabStd K lam).FG ∧ (_root_.Formalism.L2.DIV.delStd K lam).FG ∧
      Submodule.span K (_root_.Formalism.L2.DIV.nabStd K lam : Set (_root_.Formalism.L2.DIV.Pol K ι n)) = _root_.Formalism.L2.DIV.VV K lam ∧
      Submodule.span K (_root_.Formalism.L2.DIV.delStd K lam : Set (_root_.Formalism.L2.DIV.Pol K ι n)) = _root_.Formalism.L2.DIV.VV K lam := by
  intro K _ _ ι _ n lam
  have hnab := nabStd_fg' K ι n lam
  refine ⟨hnab, hnab.of_le (_root_.Formalism.L2.DIV.delStd_le_nabStd K lam), ?_, ?_⟩
  · unfold _root_.Formalism.L2.DIV.nabStd _root_.Formalism.L2.DIV.VV
    rw [span_tensorLat_eq_prod_map_span, ← Submodule.span_eq (_root_.Formalism.GradedWeylDivisibility.tensorLat K K _), span_tensorLat_eq_prod_map_span]
    simp only [span_map_toK_nablaSq_eq_nablaSq, Submodule.span_eq]
  · unfold _root_.Formalism.L2.DIV.delStd _root_.Formalism.L2.DIV.VV
    rw [span_tensorLat_eq_prod_map_span, ← Submodule.span_eq (_root_.Formalism.GradedWeylDivisibility.tensorLat K K _), span_tensorLat_eq_prod_map_span]
    simp only [span_map_toK_delSq_eq_nablaSq, Submodule.span_eq]

end GlobalTheory.StdLatSpan
