import Mathlib
import Formalism.SatakeDualWeyl.Statement
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PFnRing
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.HodgeTraceFromLefschetzAndGroupSide

set_option autoImplicit false

noncomputable section

namespace UpperTheory.Gal.LocalSmoothExtension.FunctionDecomposition

variable {H : Type} [Group H] {K : Subgroup H} {f : H → ℂ}

private lemma val_of_mem (hb : ∀ k ∈ K, ∀ g, f (k * g) = f g ∧ f (g * k) = f g) {g x : H}
    (hg : g ∈ DoubleCoset.doubleCoset x (K : Set H) K) : f g = f x := by
  obtain ⟨a, ha, b, hb', rfl⟩ := DoubleCoset.mem_doubleCoset.1 hg
  rw [(hb b hb' _).2, (hb a ha _).1]

private lemma ind_mem {g x : H} (hg : g ∈ DoubleCoset.doubleCoset x (K : Set H) K) :
    UpperTheory.Gal.G3.ind ℂ K x g = 1 :=
  Set.indicator_of_mem hg _

private lemma ind_notMem {g x : H} (hg : g ∉ DoubleCoset.doubleCoset x (K : Set H) K) :
    UpperTheory.Gal.G3.ind ℂ K x g = 0 :=
  Set.indicator_of_notMem hg _

private lemma mem_of_ind {g x : H} (hg : UpperTheory.Gal.G3.ind ℂ K x g ≠ 0) :
    g ∈ DoubleCoset.doubleCoset x (K : Set H) K := by
  by_contra hn
  exact hg (ind_notMem hn)

private lemma mk_of_mem {g : H} {q : DoubleCoset.Quotient (K : Set H) K}
    (hg : g ∈ DoubleCoset.doubleCoset q.out (K : Set H) K) : DoubleCoset.mk K K g = q :=
  (DoubleCoset.mem_quotToDoubleCoset_iff q g).1 hg

private lemma mem_of_mk {g : H} {q : DoubleCoset.Quotient (K : Set H) K}
    (hg : DoubleCoset.mk K K g = q) : g ∈ DoubleCoset.doubleCoset q.out (K : Set H) K :=
  (DoubleCoset.mem_quotToDoubleCoset_iff q g).2 hg

private lemma coset_ne (hb : ∀ k ∈ K, ∀ g, f (k * g) = f g ∧ f (g * k) = f g) {g : H} (hg : f g ≠ 0) :
    (g : H ⧸ K) ∈ {y : H ⧸ K | f y.out ≠ 0} := by
  obtain ⟨c, hc⟩ := QuotientGroup.mk_out_eq_mul K g
  show f (g : H ⧸ K).out ≠ 0
  rw [hc, (hb c c.2 g).2]
  exact hg

private lemma mem_hecke (hb : ∀ k ∈ K, ∀ g, f (k * g) = f g ∧ f (g * k) = f g)
    (hfin : {y : H ⧸ K | f y.out ≠ 0}.Finite) : f ∈ Formalism.UG.Hecke ℂ K := by
  classical
  have h : Formalism.UG.IsBiInv K f ∧ Formalism.UG.FinDosetSupp K f := by
    refine ⟨fun a b g => ?_, hfin.toFinset.image Quotient.out, fun g hg => ?_⟩
    · rw [(hb b b.2 _).2, (hb a a.2 _).1]
    · obtain ⟨c, hc⟩ := QuotientGroup.mk_out_eq_mul K g
      refine ⟨(g : H ⧸ K).out, Finset.mem_image.2 ⟨_, hfin.mem_toFinset.2 (coset_ne hb hg), rfl⟩, 1, c⁻¹, ?_⟩
      rw [hc]
      simp
  exact h

private lemma decomp (hb : ∀ k ∈ K, ∀ g, f (k * g) = f g ∧ f (g * k) = f g)
    (hfin : {y : H ⧸ K | f y.out ≠ 0}.Finite) :
    ∃ (m : ℕ) (q : Fin m → H) (c : Fin m → ℂ), (∀ i, f (q i) ≠ 0) ∧
      f = ∑ i, c i • UpperTheory.Gal.G3.ind ℂ K (q i) ∧ ∀ i g, UpperTheory.Gal.G3.ind ℂ K (q i) g ≠ 0 → f g ≠ 0 := by
  classical
  let Q : Finset (DoubleCoset.Quotient (K : Set H) K) :=
    (hfin.toFinset.image fun y => DoubleCoset.mk K K y.out).filter fun q => f q.out ≠ 0
  have hQ : ∀ q : DoubleCoset.Quotient (K : Set H) K, f q.out ≠ 0 → q ∈ Q := by
    intro q hq
    refine Finset.mem_filter.2 ⟨Finset.mem_image.2 ⟨(q.out : H ⧸ K), hfin.mem_toFinset.2 (coset_ne hb hq), ?_⟩, hq⟩
    obtain ⟨c, hc⟩ := QuotientGroup.mk_out_eq_mul K q.out
    refine mk_of_mem (DoubleCoset.mem_doubleCoset.2 ⟨1, K.one_mem, c, c.2, ?_⟩)
    rw [hc]
    simp
  have hne : ∀ q ∈ Q, f q.out ≠ 0 := fun q hq => (Finset.mem_filter.1 hq).2
  let e := Q.equivFin
  refine ⟨Q.card, fun i => (e.symm i).1.out, fun i => f (e.symm i).1.out, fun i => hne _ (e.symm i).2, ?_, ?_⟩
  · funext g
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hg : f g = 0
    · rw [hg]
      refine (Finset.sum_eq_zero fun i _ => ?_).symm
      rw [ind_notMem fun hm => hne _ (e.symm i).2 (by rw [← val_of_mem hb hm]; exact hg), mul_zero]
    · have hp : f (DoubleCoset.mk K K g).out = f g :=
        val_of_mem hb (by
          obtain ⟨a, b, ha, hb', e'⟩ := DoubleCoset.mk_out_eq_mul K K g
          exact DoubleCoset.mem_doubleCoset.2 ⟨a, ha, b, hb', e'⟩)
      have hpQ := hQ (DoubleCoset.mk K K g) (by rw [hp]; exact hg)
      rw [Finset.sum_eq_single (e ⟨_, hpQ⟩)]
      · rw [e.symm_apply_apply]
        show f g = f (DoubleCoset.mk K K g).out * _
        rw [ind_mem (mem_of_mk rfl), hp, mul_one]
      · intro i _ hi
        rw [ind_notMem, mul_zero]
        intro hm
        apply hi
        have : (⟨_, hpQ⟩ : Q) = e.symm i := Subtype.ext (mk_of_mem hm)
        rw [this, e.apply_symm_apply]
      · intro h
        exact absurd (Finset.mem_univ _) h
  · intro i g hg
    rw [val_of_mem hb (mem_of_ind hg)]
    exact hne _ (e.symm i).2

end UpperTheory.Gal.LocalSmoothExtension.FunctionDecomposition

open UpperTheory.Gal.LocalSmoothExtension.FunctionDecomposition in
private theorem UpperTheory.Gal.LocalSmoothExtension.FunctionDecomposition.fwd {B : AlgebraicGeometry.Scheme.{0}} {Γ : Type} [Group Γ]
    (X : UpperTheory.Gal.G3.Tower B Γ) (j : X.ι) (f : Γ → ℂ) (hf : X.IsFn j f) :
    f ∈ Formalism.UG.Hecke ℂ (X.K j) ∧ ∃ (m : ℕ) (h : Fin m → Γ) (c : Fin m → ℂ), (∀ i, h i ∈ X.Δ) ∧
      f = ∑ i, c i • UpperTheory.Gal.G3.ind ℂ (X.K j) (h i)⁻¹ ∧
      ∀ i g, UpperTheory.Gal.G3.ind ℂ (X.K j) (h i)⁻¹ g ≠ 0 → f g ≠ 0 := by
  obtain ⟨hb, hΔ, hfin⟩ := hf
  obtain ⟨m, q, c, hq, e, hs⟩ := decomp hb hfin
  refine ⟨mem_hecke hb hfin, m, fun i => (q i)⁻¹, c, fun i => hΔ _ (hq i), ?_, ?_⟩
  · simpa only [inv_inv] using e
  · simpa only [inv_inv] using hs

private theorem UpperTheory.Gal.LocalSmoothExtension.FunctionDecomposition.bwd {B : AlgebraicGeometry.Scheme.{0}} {Γ : Type} [Group Γ]
    (X : UpperTheory.Gal.G3.Tower B Γ) (j : X.ι) (f : Γ → ℂ) (hf : f ∈ Formalism.UG.Hecke ℂ (X.K j))
    (hΔ : ∀ g, f g ≠ 0 → g⁻¹ ∈ X.Δ) : X.IsFn j f := by
  classical
  obtain ⟨hb, S, hS⟩ : Formalism.UG.IsBiInv (X.K j) f ∧ Formalism.UG.FinDosetSupp (X.K j) f := hf
  have hbi : ∀ k ∈ X.K j, ∀ g, f (k * g) = f g ∧ f (g * k) = f g := fun k hk g =>
    ⟨by simpa using hb ⟨k, hk⟩ 1 g, by simpa using hb 1 ⟨k, hk⟩ g⟩
  refine ⟨hbi, hΔ, ?_⟩
  have hone : ∀ s : Γ, s⁻¹ ∈ X.Δ →
      {y : Γ ⧸ X.K j | UpperTheory.Gal.G3.ind ℂ (X.K j) s y.out ≠ 0}.Finite := by
    intro s hs
    have := ((UpperTheory.Gal.G3.pFnRing X ℂ j).1 s⁻¹ hs).2.2
    simpa only [inv_inv] using this
  refine ((S.filter fun s => s⁻¹ ∈ X.Δ).finite_toSet.biUnion
    (t := fun s => {y : Γ ⧸ X.K j | UpperTheory.Gal.G3.ind ℂ (X.K j) s y.out ≠ 0}) ?_).subset ?_
  · intro s hs
    exact hone s (Finset.mem_filter.1 hs).2
  · intro y hy
    obtain ⟨s, hs, a, b, e⟩ := hS y.out hy
    have hfs : f s ≠ 0 := by
      have h1 : f y.out = f s := by rw [e]; exact hb a b s
      rw [← h1]
      exact hy
    refine Set.mem_biUnion (Finset.mem_coe.2 (Finset.mem_filter.2 ⟨hs, hΔ s hfs⟩)) ?_
    show UpperTheory.Gal.G3.ind ℂ (X.K j) s y.out ≠ 0
    rw [UpperTheory.Gal.LocalSmoothExtension.FunctionDecomposition.ind_mem (K := X.K j)
      (DoubleCoset.mem_doubleCoset.2 ⟨(a : Γ), a.2, (b : Γ), b.2, e⟩)]
    exact one_ne_zero

open UpperTheory.Gal.LocalSmoothExtension in
theorem UpperTheory.Gal.LocalSmoothExtension.fnDecomp_of :
    FnDecomp := by
  intro B Γ _ X j f
  exact ⟨UpperTheory.Gal.LocalSmoothExtension.FunctionDecomposition.fwd X j f, UpperTheory.Gal.LocalSmoothExtension.FunctionDecomposition.bwd X j f⟩
