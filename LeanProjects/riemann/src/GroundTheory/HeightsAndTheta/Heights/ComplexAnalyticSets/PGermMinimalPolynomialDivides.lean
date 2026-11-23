import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.AnalyticGerm
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StGermMinimalPolynomialDivides
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFiniteFibreGermIntegral
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StHolGermsIntegrallyClosed
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter Polynomial

noncomputable section

namespace GermMinimalPolynomialDivides

def germsAlong {σ : Type} [Fintype σ] (X : Set (σ → ℂ)) (x : σ → ℂ) : Subring (Germ (𝓝[X] x) ℂ) where
  carrier := {φ | ∃ f : (σ → ℂ) → ℂ, AnalyticAt ℂ f x ∧ (f : Germ (𝓝[X] x) ℂ) = φ}
  mul_mem' := by
    rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨f * g, hf.mul hg, rfl⟩
  one_mem' := ⟨fun _ => 1, analyticAt_const, rfl⟩
  add_mem' := by
    rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨f + g, hf.add hg, rfl⟩
  zero_mem' := ⟨fun _ => 0, analyticAt_const, rfl⟩
  neg_mem' := by
    rintro _ ⟨f, hf, rfl⟩
    exact ⟨-f, hf.neg, rfl⟩

def analyticAtRing {ι : Type} [Fintype ι] (w : ι → ℂ) : Subring ((ι → ℂ) → ℂ) where
  carrier := {f | AnalyticAt ℂ f w}
  mul_mem' := fun hf hg => hf.mul hg
  one_mem' := (analyticAt_const : AnalyticAt ℂ (fun _ : ι → ℂ => (1 : ℂ)) w)
  add_mem' := fun hf hg => hf.add hg
  zero_mem' := (analyticAt_const : AnalyticAt ℂ (fun _ : ι → ℂ => (0 : ℂ)) w)
  neg_mem' := fun hf => hf.neg

def germOf {ι : Type} [Fintype ι] (w : ι → ℂ) : analyticAtRing w →+* holGerms w :=
  ((Germ.coeRingHom (𝓝 w)).comp (analyticAtRing w).subtype).codRestrict (holGerms w)
    fun f => ⟨f.1, f.2, rfl⟩

theorem germOf_surjective {ι : Type} [Fintype ι] (w : ι → ℂ) : Function.Surjective (germOf w) := by
  intro φ
  obtain ⟨f, hf, hφ⟩ := φ.2
  exact ⟨⟨f, hf⟩, Subtype.ext hφ⟩

def germRep {ι : Type} [Fintype ι] (w : ι → ℂ) : holGerms w → analyticAtRing w :=
  Function.surjInv (germOf_surjective w)

theorem germOf_germRep {ι : Type} [Fintype ι] (w : ι → ℂ) (φ : holGerms w) : germOf w (germRep w φ) = φ :=
  Function.surjInv_eq (germOf_surjective w) φ

theorem germOf_eq_zero {ι : Type} [Fintype ι] (w : ι → ℂ) (f : analyticAtRing w) :
    germOf w f = 0 ↔ ∀ᶠ y in 𝓝 w, f.1 y = 0 := by
  rw [← Subtype.coe_inj]
  exact Germ.coe_eq

def alongOf {σ : Type} [Fintype σ] (X : Set (σ → ℂ)) (x : σ → ℂ) : analyticAtRing x →+* germsAlong X x :=
  ((Germ.coeRingHom (𝓝[X] x)).comp (analyticAtRing x).subtype).codRestrict (germsAlong X x)
    fun f => ⟨f.1, f.2, rfl⟩

def germCompHom {α β : Type} {l : Filter β} {l' : Filter α} (g : α → β) (hg : Tendsto g l' l) :
    Germ l ℂ →+* Germ l' ℂ where
  toFun φ := φ.compTendsto g hg
  map_one' := rfl
  map_mul' φ ψ := Germ.inductionOn₂ φ ψ fun _ _ => rfl
  map_zero' := rfl
  map_add' φ ψ := Germ.inductionOn₂ φ ψ fun _ _ => rfl

theorem tendsto_nhdsWithin_linear {σ : Type} [Fintype σ] {d : ℕ} (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ))
    (X : Set (σ → ℂ)) (x : σ → ℂ) : Tendsto A (𝓝[X] x) (𝓝 (A x)) :=
  (A.continuous.tendsto x).mono_left nhdsWithin_le_nhds

def alongPull {σ : Type} [Fintype σ] (X : Set (σ → ℂ)) (x : σ → ℂ) {d : ℕ} (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) :
    holGerms (A x) →+* germsAlong X x :=
  ((germCompHom A (tendsto_nhdsWithin_linear A X x)).comp (holGerms (A x)).subtype).codRestrict _ fun φ => by
    obtain ⟨f, hf, hφ⟩ := φ.2
    refine ⟨f ∘ A, hf.comp (A.analyticAt x), ?_⟩
    change _ = (φ.1 : Germ (𝓝 (A x)) ℂ).compTendsto A (tendsto_nhdsWithin_linear A X x)
    rw [← hφ]
    rfl

def preLinear {σ : Type} [Fintype σ] (x : σ → ℂ) {d : ℕ} (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) :
    analyticAtRing (A x) →+* ((σ → ℂ) → ℂ) :=
  (RingHom.pi fun z => Pi.evalRingHom (fun _ : Fin d → ℂ => ℂ) (A z)).comp (analyticAtRing (A x)).subtype

theorem eventually_of_germ_eq {σ : Type} [Fintype σ] {X : Set (σ → ℂ)} {x : σ → ℂ} {f g : (σ → ℂ) → ℂ}
    (h : (f : Germ (𝓝[X] x) ℂ) = g) : ∀ᶠ z in 𝓝 x, z ∈ X → f z = g z :=
  eventually_nhdsWithin_iff.1 (Germ.coe_eq.1 h)

theorem coe_eval₂_map {σ : Type} [Fintype σ] (X : Set (σ → ℂ)) (x : σ → ℂ) {d : ℕ}
    (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) (P : (analyticAtRing (A x))[X]) (v : analyticAtRing x) :
    ((eval₂ (alongPull X x A) (alongOf X x v) (P.map (germOf (A x))) : germsAlong X x) : Germ (𝓝[X] x) ℂ) =
      ((eval₂ (preLinear x A) v.1 P : (σ → ℂ) → ℂ) : Germ (𝓝[X] x) ℂ) := by
  change (germsAlong X x).subtype _ = Germ.coeRingHom _ _
  rw [eval₂_map, hom_eval₂, hom_eval₂]
  rfl

theorem eval₂_monic_apply {σ : Type} [Fintype σ] (x : σ → ℂ) {d : ℕ} (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ))
    (g : (σ → ℂ) → ℂ) {M : ℕ} (b : Fin M → analyticAtRing (A x)) (z : σ → ℂ) :
    eval₂ (preLinear x A) g (Polynomial.X ^ M + ∑ j, C (b j) * Polynomial.X ^ (j : ℕ)) z =
      g z ^ M + ∑ j, (b j).1 (A z) * g z ^ (j : ℕ) := by
  simp [eval₂_finsetSum, Finset.sum_apply, preLinear]

theorem proof (hF : FiniteFibreGermIntegral.Statement) (hH : HolGermsIntegrallyClosed.Statement) :
    GermMinimalPolynomialDivides.Statement := by
  intro σ _ X w d A hXan hirr hiso hinj g hg
  classical
  obtain ⟨hdom, hic⟩ := hH d (A w)

  have : (𝓝[X] w).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (subset_closure hirr.1)
  have germ_zero : ∀ f : (σ → ℂ) → ℂ, (∀ᶠ z in 𝓝 w, z ∈ X → f z = 0) →
      (f : Germ (𝓝[X] w) ℂ) = ((0 : (σ → ℂ) → ℂ) : Germ (𝓝[X] w) ℂ) :=
    fun f h => Germ.coe_eq.2 (eventually_nhdsWithin_iff.2 h)
  have : NoZeroDivisors (germsAlong X w) := by
    refine ⟨fun {a b} hab => ?_⟩
    obtain ⟨f, hf, hfa⟩ := a.2
    obtain ⟨g, hg, hgb⟩ := b.2
    have h0 : ((f * g : (σ → ℂ) → ℂ) : Germ (𝓝[X] w) ℂ) = ((0 : (σ → ℂ) → ℂ) : Germ (𝓝[X] w) ℂ) := by
      rw [Germ.coe_mul, hfa, hgb]
      exact congrArg Subtype.val hab
    rcases hirr.2 f g hf hg ((eventually_of_germ_eq h0).mono fun z hz hzX => by simpa using hz hzX) with h | h
    · exact Or.inl (Subtype.ext (hfa ▸ germ_zero f h))
    · exact Or.inr (Subtype.ext (hgb ▸ germ_zero g h))
  have : IsDomain (germsAlong X w) := NoZeroDivisors.to_isDomain _

  let _ : Algebra (holGerms (A w)) (germsAlong X w) := (alongPull X w A).toAlgebra
  have hα : Function.Injective (algebraMap (holGerms (A w)) (germsAlong X w)) := by
    rw [injective_iff_map_eq_zero]
    intro φ hφ
    obtain ⟨h, hh, hφh⟩ := φ.2
    have h1 : ((h ∘ A : (σ → ℂ) → ℂ) : Germ (𝓝[X] w) ℂ) = ((0 : (σ → ℂ) → ℂ) : Germ (𝓝[X] w) ℂ) := by
      have h2 := congrArg Subtype.val hφ
      change (φ.1 : Germ (𝓝 (A w)) ℂ).compTendsto A (tendsto_nhdsWithin_linear A X w) =
        (0 : Germ (𝓝[X] w) ℂ) at h2
      rw [← hφh] at h2
      exact h2
    have h3 := hinj h hh ((eventually_of_germ_eq h1).mono fun z hz hzX => hz hzX)
    apply Subtype.ext
    rw [← hφh]
    exact Germ.coe_eq.2 h3
  have : FaithfulSMul (holGerms (A w)) (germsAlong X w) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 hα

  set s : germsAlong X w := alongOf X w ⟨g, hg⟩ with hs
  have aeval_zero : ∀ P : (analyticAtRing (A w))[X],
      (∀ᶠ z in 𝓝 w, z ∈ X → eval₂ (preLinear w A) g P z = 0) → aeval s (P.map (germOf (A w))) = 0 := by
    intro P hP
    rw [aeval_def]
    apply Subtype.ext
    change ((eval₂ (alongPull X w A) (alongOf X w ⟨g, hg⟩) (P.map (germOf (A w))) : germsAlong X w) :
      Germ (𝓝[X] w) ℂ) = ((0 : (σ → ℂ) → ℂ) : Germ (𝓝[X] w) ℂ)
    rw [coe_eval₂_map]
    exact germ_zero _ hP

  have hint : IsIntegral (holGerms (A w)) s := by
    obtain ⟨M, b, hb, hev⟩ := hF σ X w d A hXan hiso g hg
    let bt : Fin M → analyticAtRing (A w) := fun j => ⟨b j, hb j⟩
    refine ⟨(Polynomial.X ^ M + ∑ j, C (bt j) * Polynomial.X ^ (j : ℕ)).map (germOf (A w)),
      (monic_X_pow_add (degree_sum_fin_lt _)).map _, ?_⟩
    rw [← aeval_def]
    exact aeval_zero _ (hev.mono fun z hz hzX => by rw [eval₂_monic_apply]; exact hz hzX)

  set m := minpoly (holGerms (A w)) s with hm
  have hmon : m.Monic := minpoly.monic hint
  let bt : Fin m.natDegree → analyticAtRing (A w) := fun j => germRep (A w) (m.coeff j)
  let P : (analyticAtRing (A w))[X] := Polynomial.X ^ m.natDegree + ∑ j, C (bt j) * Polynomial.X ^ (j : ℕ)
  have hPm : P.map (germOf (A w)) = m := by
    have h1 := hmon.as_sum
    rw [← Fin.sum_univ_eq_sum_range (fun i => C (m.coeff i) * Polynomial.X ^ i)] at h1
    conv_rhs => rw [h1]
    simp only [P, bt, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_sum,
      Polynomial.map_mul, Polynomial.map_C, germOf_germRep]
  have hPz : ∀ z, eval₂ (preLinear w A) g P z = g z ^ m.natDegree + ∑ j, (bt j).1 (A z) * g z ^ (j : ℕ) :=
    fun z => eval₂_monic_apply w A g bt z
  refine ⟨m.natDegree, fun j => (bt j).1, fun j => (bt j).2, ?_, ?_⟩
  ·
    have h0 : aeval s m = 0 := minpoly.aeval _ _
    rw [← hPm, aeval_def] at h0
    have h1 := congrArg Subtype.val h0
    change ((eval₂ (alongPull X w A) (alongOf X w ⟨g, hg⟩) (P.map (germOf (A w))) : germsAlong X w) :
      Germ (𝓝[X] w) ℂ) = ((0 : (σ → ℂ) → ℂ) : Germ (𝓝[X] w) ℂ) at h1
    rw [coe_eval₂_map] at h1
    exact (eventually_of_germ_eq h1).mono fun z hz hzX => (hPz z).symm.trans (hz hzX)
  ·
    intro E hE hEz
    have hcoeffs : (↑E.coeffs : Set ((Fin d → ℂ) → ℂ)) ⊆ analyticAtRing (A w) := by
      intro c hc
      obtain ⟨k, -, rfl⟩ := mem_coeffs_iff.1 hc
      exact hE k
    let Et := E.toSubring (analyticAtRing (A w)) hcoeffs
    have hEval : ∀ z, eval₂ (preLinear w A) g Et z = E.eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ => ℂ) (A z)) (g z) := by
      intro z
      have hmap : Et.map (analyticAtRing (A w)).subtype = E := map_toSubring _ _ _
      have h1 : eval₂ (preLinear w A) g Et =
          eval₂ (RingHom.pi fun z => Pi.evalRingHom (fun _ : Fin d → ℂ => ℂ) (A z)) g E := by
        rw [← hmap, eval₂_map]
        rfl
      rw [h1]
      exact hom_eval₂ E _ (Pi.evalRingHom (fun _ : σ → ℂ => ℂ) z) g
    have hEt0 : aeval s (Et.map (germOf (A w))) = 0 :=
      aeval_zero Et (hEz.mono fun z hz hzX => (hEval z).trans (hz hzX))
    obtain ⟨q, hq⟩ := minpoly.isIntegrallyClosed_dvd hint hEt0
    obtain ⟨Q, rfl⟩ := Polynomial.map_surjective _ (germOf_surjective (A w)) q
    have hDz : (Et - P * Q).map (germOf (A w)) = 0 := by
      rw [Polynomial.map_sub, Polynomial.map_mul, hPm, hq, sub_self]
    have hDev : ∀ᶠ y in 𝓝 (A w), ∀ k ∈ (Et - P * Q).support, ((Et - P * Q).coeff k).1 y = 0 := by
      rw [eventually_all_finset]
      intro k _
      have : germOf (A w) ((Et - P * Q).coeff k) = 0 := by rw [← coeff_map, hDz, coeff_zero]
      exact (germOf_eq_zero _ _).1 this
    filter_upwards [hDev] with y hy
    let ev : analyticAtRing (A w) →+* ℂ :=
      (Pi.evalRingHom (fun _ : Fin d → ℂ => ℂ) y).comp (analyticAtRing (A w)).subtype
    have hD0 : (Et - P * Q).map ev = 0 := by
      ext k
      rw [coeff_map, coeff_zero]
      by_cases hk : k ∈ (Et - P * Q).support
      · exact hy k hk
      · rw [notMem_support_iff.1 hk, map_zero]
    have hE' : Et.map ev = E.map (Pi.evalRingHom (fun _ : Fin d → ℂ => ℂ) y) := by
      rw [← map_toSubring E (analyticAtRing (A w)) hcoeffs, Polynomial.map_map]
    have hP' : P.map ev =
        Polynomial.X ^ m.natDegree + ∑ j, C ((bt j).1 y) * Polynomial.X ^ (j : ℕ) := by
      simp [P, ev, Polynomial.map_sum]
    refine ⟨Q.map ev, ?_⟩
    rw [← hE', ← hP', ← Polynomial.map_mul, ← sub_eq_zero, ← Polynomial.map_sub]
    exact hD0

end GermMinimalPolynomialDivides

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
