import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CoefExtendsHolomorphically

open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology

noncomputable section

namespace GlobalTheory.KFinSep

variable {n : ℕ} {ε : Fin n → Bool}

lemma kfin_of_span {ι : Type} [Finite ι] (b : ι → KG ε → ℂ) (hc : ∀ i, Continuous (b i))
    (ht : ∀ i (k₀ : KG ε), (fun k => b i (k₀ * k)) ∈ Submodule.span ℂ (Set.range b) ∧
      (fun k => b i (k * k₀)) ∈ Submodule.span ℂ (Set.range b)) (i : ι) : KFinFun ε (b i) := by
  refine ⟨Submodule.span ℂ (Set.range b), FiniteDimensional.span_of_finite ℂ (Set.finite_range b),
    Submodule.subset_span ⟨i, rfl⟩, ?_, ?_⟩
  · intro φ hφ
    induction hφ using Submodule.span_induction with
    | mem x hx => obtain ⟨j, rfl⟩ := hx; exact hc j
    | zero => exact continuous_const
    | add x y _ _ hx hy => exact hx.add hy
    | smul a x _ hx => exact hx.const_smul a
  · intro φ hφ k₀
    induction hφ using Submodule.span_induction with
    | mem x hx => obtain ⟨j, rfl⟩ := hx; exact ht j k₀
    | zero => exact ⟨Submodule.zero_mem _, Submodule.zero_mem _⟩
    | add x y _ _ hx hy => exact ⟨Submodule.add_mem _ hx.1 hy.1, Submodule.add_mem _ hx.2 hy.2⟩
    | smul a x _ hx => exact ⟨Submodule.smul_mem _ a hx.1, Submodule.smul_mem _ a hx.2⟩

lemma kfin_const (c : ℂ) : KFinFun ε (fun _ => c) :=
  kfin_of_span (ε := ε) (ι := Unit) (fun _ _ => c) (fun _ => continuous_const)
    (fun i _ => ⟨Submodule.subset_span ⟨i, rfl⟩, Submodule.subset_span ⟨i, rfl⟩⟩) ()

lemma kfin_add {p q : KG ε → ℂ} (hp : KFinFun ε p) (hq : KFinFun ε q) : KFinFun ε (p + q) := by
  obtain ⟨F, _, hpF, hFc, hF⟩ := hp
  obtain ⟨G, _, hqG, hGc, hG⟩ := hq
  refine ⟨F ⊔ G, inferInstance, Submodule.add_mem_sup hpF hqG, ?_, ?_⟩
  · intro φ hφ
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hφ
    exact (hFc x hx).add (hGc y hy)
  · intro φ hφ k₀
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hφ
    exact ⟨Submodule.add_mem_sup (hF x hx k₀).1 (hG y hy k₀).1, Submodule.add_mem_sup (hF x hx k₀).2 (hG y hy k₀).2⟩

lemma kfin_mul {p q : KG ε → ℂ} (hp : KFinFun ε p) (hq : KFinFun ε q) : KFinFun ε (p * q) := by
  obtain ⟨F, hFf, hpF, hFc, hF⟩ := hp
  obtain ⟨G, hGf, hqG, hGc, hG⟩ := hq
  refine ⟨F * G, ?_, Submodule.mul_mem_mul hpF hqG, ?_, ?_⟩
  · exact Module.Finite.iff_fg.2 ((Module.Finite.iff_fg.1 hFf).mul (Module.Finite.iff_fg.1 hGf))
  · intro φ hφ
    refine Submodule.mul_induction_on hφ (fun x hx y hy => (hFc x hx).mul (hGc y hy)) (fun x y hx hy => hx.add hy)
  · intro φ hφ k₀
    refine Submodule.mul_induction_on (C := fun φ => (fun k => φ (k₀ * k)) ∈ F * G ∧ (fun k => φ (k * k₀)) ∈ F * G)
      hφ (fun x hx y hy => ?_) (fun x y hx hy => ?_)
    · exact ⟨Submodule.mul_mem_mul (hF x hx k₀).1 (hG y hy k₀).1, Submodule.mul_mem_mul (hF x hx k₀).2 (hG y hy k₀).2⟩
    · exact ⟨Submodule.add_mem _ hx.1 hy.1, Submodule.add_mem _ hx.2 hy.2⟩

lemma mem_span_of_sum {ι κ : Type} [Fintype κ] (b : ι → KG ε → ℂ) (f : KG ε → ℂ) (c : κ → ℂ) (j : κ → ι)
    (h : ∀ k, f k = ∑ l, c l * b (j l) k) : f ∈ Submodule.span ℂ (Set.range b) := by
  have : f = ∑ l, c l • b (j l) := by
    funext k; simp [h, Finset.sum_apply]
  rw [this]
  exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j l, rfl⟩)

lemma kfin_entry (i j : Fin n) : KFinFun ε (fun k => toMK k i j) := by
  refine kfin_of_span (ε := ε) (ι := Fin n × Fin n) (fun a k => toMK k a.1 a.2)
    (fun a => (GlobalTheory.KHolExt.ent ε a.1 a.2).continuous) (fun a k₀ => ⟨?_, ?_⟩) (i, j)
  · refine mem_span_of_sum _ _ (fun l => toMK k₀ a.1 l) (fun l => (l, a.2)) fun k => ?_
    simp only [GlobalTheory.KHolExt.toMK_mul, Matrix.mul_apply]
  · refine mem_span_of_sum _ _ (fun l => toMK k₀ l a.2) (fun l => (a.1, l)) fun k => ?_
    simp only [GlobalTheory.KHolExt.toMK_mul, Matrix.mul_apply, mul_comm]

lemma kfin_conjEntry (i j : Fin n) : KFinFun ε (fun k => star (toMK k i j)) := by
  refine kfin_of_span (ε := ε) (ι := Fin n × Fin n) (fun a k => star (toMK k a.1 a.2))
    (fun a => (GlobalTheory.KHolExt.ent ε a.1 a.2).continuous.star) (fun a k₀ => ⟨?_, ?_⟩) (i, j)
  · refine mem_span_of_sum _ _ (fun l => star (toMK k₀ a.1 l)) (fun l => (l, a.2)) fun k => ?_
    simp only [GlobalTheory.KHolExt.toMK_mul, Matrix.mul_apply, star_sum, star_mul']
  · refine mem_span_of_sum _ _ (fun l => star (toMK k₀ l a.2)) (fun l => (a.1, l)) fun k => ?_
    simp only [GlobalTheory.KHolExt.toMK_mul, Matrix.mul_apply, star_sum, star_mul', mul_comm]

def finAlg (ε : Fin n → Bool) : StarSubalgebra ℂ C(KG ε, ℂ) where
  carrier := {p | KFinFun ε p ∧ KFinFun ε (star p : C(KG ε, ℂ))}
  mul_mem' := fun {p q} hp hq => ⟨kfin_mul hp.1 hq.1, by
    rw [star_mul']; exact kfin_mul hp.2 hq.2⟩
  add_mem' := fun {p q} hp hq => ⟨kfin_add hp.1 hq.1, by
    rw [star_add]; exact kfin_add hp.2 hq.2⟩
  algebraMap_mem' := fun c => ⟨by
    have : ((algebraMap ℂ C(KG ε, ℂ) c : C(KG ε, ℂ)) : KG ε → ℂ) = fun _ => c := by
      funext k; simp
    rw [this]; exact kfin_const c, by
    have : ((star (algebraMap ℂ C(KG ε, ℂ) c) : C(KG ε, ℂ)) : KG ε → ℂ) = fun _ => star c := by
      funext k; simp
    rw [this]; exact kfin_const _⟩
  star_mem' := fun {p} hp => ⟨hp.2, by rw [star_star]; exact hp.1⟩

lemma finAlg_dense (ε : Fin n → Bool) : (finAlg ε).topologicalClosure = ⊤ := by
  refine ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints _ ?_
  intro x y hxy
  have h : toMK x ≠ toMK y := fun h => hxy ((GlobalTheory.KHolExt.isEmb ε).injective h)
  obtain ⟨i, j, hij⟩ : ∃ i j, toMK x i j ≠ toMK y i j := by
    by_contra hc
    push Not at hc
    exact h (Matrix.ext hc)
  exact ⟨GlobalTheory.KHolExt.ent ε i j, ⟨GlobalTheory.KHolExt.ent ε i j, ⟨kfin_entry i j, kfin_conjEntry i j⟩, rfl⟩, hij⟩

end GlobalTheory.KFinSep
