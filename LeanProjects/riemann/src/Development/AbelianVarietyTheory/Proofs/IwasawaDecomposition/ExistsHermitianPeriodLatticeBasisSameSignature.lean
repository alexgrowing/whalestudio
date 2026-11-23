import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EmbRtSq

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Matrix CategoryTheory.Obj Topology

namespace GlobalTheory.ShFam.Hor.PerBasis

theorem mult_conj_add_mult {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    (D : Datum H) (τ : E →+* ℂ) : D.mult (conjEmb τ) + D.mult τ = D.p + D.q := by
  first
  | exact @_root_.GlobalTheory.ConjugateMultiplicity.target
  | exact _root_.GlobalTheory.ConjugateMultiplicity.target
  | (apply _root_.GlobalTheory.ConjugateMultiplicity.target <;> assumption)
  | (intros; apply _root_.GlobalTheory.ConjugateMultiplicity.target <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ConjugateMultiplicity.target <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ConjugateMultiplicity.target ..)

theorem exists_indep {E : Type} [Field E] [NumberField E] (M : Type) [AddCommGroup M] [Module (𝓞 E) M]
    [Module.Finite (𝓞 E) M] (J : Type) [Fintype J] (hJ : Fintype.card J = Module.finrank (𝓞 E) M) :
    ∃ x : J → M, LinearIndependent (𝓞 E) x ∧
      ∀ v, ∃ n : ℕ, n ≠ 0 ∧ n • v ∈ Submodule.span (𝓞 E) (Set.range x) := by
  obtain ⟨f, hf⟩ := exists_linearIndependent_of_le_finrank (R := 𝓞 E) (M := M) (n := Fintype.card J) hJ.le
  let e := Fintype.equivFin J
  refine ⟨f ∘ e, hf.comp _ e.injective, fun v => ?_⟩
  rw [e.surjective.range_comp]
  have hc : ∃ c : 𝓞 E, c ≠ 0 ∧ c • v ∈ Submodule.span (𝓞 E) (Set.range f) := by
    by_contra hcon
    push Not at hcon
    have hli : LinearIndependent (𝓞 E) (Fin.cons v f : Fin (Fintype.card J + 1) → M) := by
      refine LinearIndependent.finCons' v f hf fun c y hy h => ?_
      by_contra hc
      refine hcon c hc ?_
      rw [eq_neg_of_add_eq_zero_left h]
      exact neg_mem hy
    have := hli.fintype_card_le_finrank
    simp at this
    omega
  obtain ⟨c, hc0, hc⟩ := hc
  refine ⟨Ideal.absNorm (Ideal.span {c}), ?_, ?_⟩
  · rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact hc0
  · obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {c}))
    rw [← Nat.cast_smul_eq_nsmul (𝓞 E), ← hd, mul_smul]
    exact Submodule.smul_mem _ _ hc

theorem exists_trace_rep {E : Type} [Field E] [NumberField E] (φ : 𝓞 E →ₗ[ℤ] ℤ) :
    ∃ h : E, ∀ a : 𝓞 E, ((φ a : ℤ) : ℚ) = Algebra.trace ℚ E ((a : E) * h) := by
  let ψ : E →ₗ[ℚ] ℚ := (integralBasis E).constr ℚ fun i => (φ (RingOfIntegers.basis E i) : ℚ)
  have hψ : ∀ a : 𝓞 E, ((φ a : ℤ) : ℚ) = ψ (a : E) := by
    intro a
    have : (Int.castAddHom ℚ).toIntLinearMap ∘ₗ φ =
        (ψ.restrictScalars ℤ) ∘ₗ ((algebraMap (𝓞 E) E).toAddMonoidHom.toIntLinearMap) := by
      refine (RingOfIntegers.basis E).ext fun i => ?_
      change ((φ (RingOfIntegers.basis E i) : ℤ) : ℚ) = ψ (algebraMap (𝓞 E) E (RingOfIntegers.basis E i))
      rw [← integralBasis_apply, Module.Basis.constr_basis]
    exact LinearMap.congr_fun this a
  refine ⟨((Algebra.traceForm ℚ E).toDual (traceForm_nondegenerate ℚ E)).symm ψ, fun a => ?_⟩
  rw [hψ, mul_comm, ← Algebra.traceForm_apply]
  exact (LinearMap.BilinForm.apply_toDual_symm_apply _ _).symm

theorem exists_isPerBasis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw Di : Datum H) (τ : E →+* ℂ), Di.p = Dw.p ∧ Di.q = Dw.q →
    ∃ (x : Idx Dw τ → Di.La) (hm : Matrix (Idx Dw τ) (Idx Dw τ) E), IsPerBasis Di x hm := by
  intro E _ _ _ H Dw Di τ ⟨hp, hq⟩
  have := Di.fin
  obtain ⟨x, hx, hsp⟩ := exists_indep (E := E) Di.La (Idx Dw τ) (by
    rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, mult_conj_add_mult, Di.rank, hp, hq])
  have hrep : ∀ k k', ∃ h : E, ∀ a : 𝓞 E,
      ((Di.EF (a • x k) (x k') : ℤ) : ℚ) = Algebra.trace ℚ E ((a : E) * h) := fun k k' =>
    exists_trace_rep (AddMonoidHom.toIntLinearMap
      { toFun := fun a : 𝓞 E => Di.EF (a • x k) (x k')
        map_zero' := by simp
        map_add' := fun a b => by simp [add_smul] })
  choose hm hhm using hrep
  refine ⟨x, Matrix.of hm, hx, hsp, fun a k k' => hhm k k' a, fun hdet => ?_⟩
  obtain ⟨c₀, hc₀, hker⟩ := Matrix.exists_vecMul_eq_zero_iff.2 hdet
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (𝓞 E)) c₀
  choose c hc using hd
  set v := ∑ k, c k • x k with hv
  have h1 : ∀ (a : 𝓞 E) k', Di.EF (a • v) (x k') = 0 := by
    intro a k'
    have hk := congrFun hker k'
    simp only [Matrix.vecMul, dotProduct, Matrix.of_apply, Pi.zero_apply] at hk
    have : ((Di.EF (a • v) (x k') : ℤ) : ℚ) = 0 := by
      rw [hv, Finset.smul_sum, map_sum, LinearMap.sum_apply]
      push_cast
      simp_rw [← mul_smul, hhm]
      rw [← map_sum]
      have : ∑ k, ((a * c k : 𝓞 E) : E) * hm k k' = (a : E) * ((d : 𝓞 E) : E) * ∑ k, c₀ k * hm k k' := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        have h2 : ((c k : 𝓞 E) : E) = ((d : 𝓞 E) : E) * c₀ k := by
          exact (hc k).trans (Algebra.smul_def _ _)
        have h3 : ((a * c k : 𝓞 E) : E) = (a : E) * ((c k : 𝓞 E) : E) := map_mul (algebraMap (𝓞 E) E) _ _
        rw [h3, h2]; ring
      rw [this, hk]; simp
    exact_mod_cast this
  have h2 : ∀ w ∈ Submodule.span (𝓞 E) (Set.range x), ∀ a : 𝓞 E, Di.EF v (a • w) = 0 := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨k, rfl⟩ := hw
      intro a
      have := h1 (H.bar.symm a) k
      rwa [Di.adj, RingEquiv.apply_symm_apply] at this
    | zero => simp
    | add y z _ _ hy hz => intro a; rw [smul_add, map_add, hy, hz, add_zero]
    | smul b y _ hy => intro a; rw [← mul_smul, hy]
  have h3 : v = 0 := by
    apply Di.unimod.1
    rw [map_zero]
    ext w
    obtain ⟨n, hn, hw⟩ := hsp w
    have := h2 _ hw 1
    rw [one_smul, map_nsmul] at this
    simpa [hn] using this
  apply hc₀
  funext k
  have h4 := Fintype.linearIndependent_iff.1 hx c h3 k
  have h5 := hc k
  rw [h4, map_zero, Algebra.smul_def] at h5
  refine (mul_eq_zero.1 h5.symm).resolve_left ?_
  exact (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).2 (nonZeroDivisors.coe_ne_zero d)

end GlobalTheory.ShFam.Hor.PerBasis
