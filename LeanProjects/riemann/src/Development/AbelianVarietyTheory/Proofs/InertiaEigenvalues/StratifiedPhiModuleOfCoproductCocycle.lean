import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section
namespace GlobalTheory.BSP

theorem strat_of_envCocycle : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (En : Env bk bk.prism (bk.toP bk.E) (bk.toP X)) (d a b : ℕ) (A A' : Matrix (Fin d) (Fin d) bk.S), A * A' = bk.E ^ b • (1 : Matrix (Fin d) (Fin d) bk.S) → ∀ ε : Matrix (Fin d) (Fin d) En.Q.A, BK.hf En.inr bk.E ^ a • (A.map (BK.hf En.inl) * ε.map En.Q.D.φ) = BK.hf En.inl bk.E ^ a • (ε * A.map (BK.hf En.inr)) → (∀ (B : Obj l ↥(OL K)), (∀ k : Hom En.Q B, k.comp En.inl = k.comp En.inr → ε.map k.f = 1) ∧ ∀ k₁ k₂ k₃ : Hom En.Q B, k₁.comp En.inr = k₂.comp En.inl → k₁.comp En.inl = k₃.comp En.inl → k₂.comp En.inr = k₃.comp En.inr → ε.map k₁.f * ε.map k₂.f = ε.map k₃.f) → ∃ S : Strat bk d, S.a = a ∧ S.A = A ∧ ∀ (B : Obj l ↥(OL K)) (k : Hom En.Q B), S.ε (k.comp En.inl) (k.comp En.inr) = ε.map k.f := by
  intro l _ K bk En d a b A A' hA ε hφ hε
  have comp_assoc : ∀ {P P' P'' P''' : Obj l ↥(OL K)} (h : Hom P'' P''') (g : Hom P' P'') (f : Hom P P'),
      (h.comp g).comp f = h.comp (g.comp f) := fun _ _ _ => Hom.ext' rfl
  let c : ∀ {B : Obj l ↥(OL K)}, Hom bk.prism B → Hom bk.prism B → Hom En.Q B :=
    fun {B} f g => (En.univ B f g).choose
  have hc : ∀ {B : Obj l ↥(OL K)} (f g : Hom bk.prism B), (c f g).comp En.inl = f ∧ (c f g).comp En.inr = g :=
    fun {B} f g => (En.univ B f g).choose_spec.1
  have hu : ∀ {B : Obj l ↥(OL K)} (k : Hom En.Q B), c (k.comp En.inl) (k.comp En.inr) = k :=
    fun {B} k => ((En.univ B _ _).choose_spec.2 k ⟨rfl, rfl⟩).symm
  clear_value c
  refine ⟨Strat.mk a b A A' hA (fun f g => ε.map (c f g).f) ?_ ?_ ?_ ?_, rfl, rfl, ?_⟩
  · intro B f
    exact (hε B).1 (c f f) ((hc f f).1.trans (hc f f).2.symm)
  · intro B f g h
    exact (hε B).2 (c f g) (c g h) (c f h) ((hc f g).2.trans (hc g h).1.symm)
      ((hc f g).1.trans (hc f h).1.symm) ((hc g h).2.trans (hc f h).2.symm)
  · intro B B' k f g
    have e : c (k.comp f) (k.comp g) = k.comp (c f g) :=
      (En.univ B' (k.comp f) (k.comp g)).unique (hc _ _)
        ⟨by rw [comp_assoc, (hc f g).1], by rw [comp_assoc, (hc f g).2]⟩
    refine Eq.trans ?_ (congrArg (fun k' : Hom En.Q B' => ε.map k'.f) e).symm
    ext i j
    rfl
  · intro B f g
    have e1 : ∀ x, (c f g).f (BK.hf En.inl x) = BK.hf f x := fun x =>
      congrArg (fun k : Hom bk.prism B => k.f x) (hc f g).1
    have e2 : ∀ x, (c f g).f (BK.hf En.inr x) = BK.hf g x := fun x =>
      congrArg (fun k : Hom bk.prism B => k.f x) (hc f g).2
    have e3 : ∀ x, (c f g).f (En.Q.D.φ x) = B.D.φ ((c f g).f x) := (c f g).f_φ
    ext i j
    have h := congrArg (fun M => (c f g).f (M i j)) hφ
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, map_mul, map_pow, map_sum, Matrix.map_apply,
      e1, e2, e3] at h
    simpa only [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Matrix.map_apply] using h
  · intro B k
    exact congrArg (fun k' : Hom En.Q B => ε.map k'.f) (hu k)

end GlobalTheory.BSP
