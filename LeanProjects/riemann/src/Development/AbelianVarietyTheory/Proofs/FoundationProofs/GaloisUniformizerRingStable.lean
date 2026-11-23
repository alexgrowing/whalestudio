import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.SelmerWindowSums
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankCyclotomicExtAndCyclotomicCharSurjective

noncomputable section

namespace GlobalTheory.RingAsStable

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N TensorProduct

section General

variable {R : Type} [CommRing R]

def adicHull (C : Subring R) (π : R) : Subring R :=
  ⨅ m : ℕ, (C.map (Ideal.Quotient.mk (Ideal.span {π ^ m}))).comap
    (Ideal.Quotient.mk (Ideal.span {π ^ m}))

theorem mem_adicHull {C : Subring R} {π a : R} :
    a ∈ adicHull C π ↔ ∀ m : ℕ, ∃ p ∈ C, π ^ m ∣ p - a := by
  simp only [adicHull, Subring.mem_iInf, Subring.mem_comap, Subring.mem_map, Ideal.Quotient.eq,
    Ideal.mem_span_singleton]

theorem le_adicHull (C : Subring R) (π : R) : C ≤ adicHull C π := fun a ha =>
  mem_adicHull.2 fun _ => ⟨a, ha, by simp⟩

theorem mem_adicHull_of_approx {C : Subring R} {π a : R}
    (h : ∀ m : ℕ, ∃ p ∈ adicHull C π, π ^ m ∣ p - a) : a ∈ adicHull C π := by
  refine mem_adicHull.2 fun m => ?_
  obtain ⟨p, hp, hpa⟩ := h m
  obtain ⟨q, hq, hqp⟩ := mem_adicHull.1 hp m
  exact ⟨q, hq, by simpa using dvd_add hqp hpa⟩

theorem stable_closure (S : Set R) (π : R) (A : Subring R)
    (hA : Subring.closure (insert π S) ≤ A) (σ : R →+* R) (hS : ∀ w ∈ S, σ w = w)
    (u : R) (hu : u ∈ A) (hσ : σ π = π * u) (p : R) (hp : p ∈ Subring.closure (insert π S)) :
    σ p ∈ A ∧ ∃ b ∈ A, σ p - p = π * b := by
  have hπ : π ∈ A := hA (Subring.subset_closure (Set.mem_insert _ _))
  have key : ∃ b ∈ A, σ p - p = π * b := by
    induction hp using Subring.closure_induction with
    | mem x hx =>
      rcases hx with rfl | hx
      · exact ⟨u - 1, A.sub_mem hu A.one_mem, by rw [hσ]; ring⟩
      · exact ⟨0, A.zero_mem, by rw [hS x hx]; ring⟩
    | zero => exact ⟨0, A.zero_mem, by simp⟩
    | one => exact ⟨0, A.zero_mem, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨b, hb, h⟩ := hx
      obtain ⟨c, hc, h'⟩ := hy
      exact ⟨b + c, A.add_mem hb hc, by rw [map_add]; linear_combination h + h'⟩
    | neg x _ hx =>
      obtain ⟨b, hb, h⟩ := hx
      exact ⟨-b, A.neg_mem hb, by rw [map_neg]; linear_combination -h⟩
    | mul x y hx' hy' hx hy =>
      obtain ⟨b, hb, h⟩ := hx
      obtain ⟨c, hc, h'⟩ := hy
      refine ⟨(x + π * b) * c + b * y, A.add_mem (A.mul_mem (A.add_mem (hA hx')
        (A.mul_mem hπ hb)) hc) (A.mul_mem hb (hA hy')), ?_⟩
      rw [map_mul]
      linear_combination (σ y) * h + (x + π * b) * h'
  refine ⟨?_, key⟩
  obtain ⟨b, hb, h⟩ := key
  have : σ p = p + π * b := by linear_combination h
  rw [this]
  exact A.add_mem (hA hp) (A.mul_mem hπ hb)

theorem stable_adicHull [IsDomain R] (S : Set R) (π : R) (hπ0 : π ≠ 0) (σ : R →+* R)
    (hS : ∀ w ∈ S, σ w = w) (u : R) (hu : u ∈ adicHull (Subring.closure (insert π S)) π)
    (hσ : σ π = π * u) (a : R) (ha : a ∈ adicHull (Subring.closure (insert π S)) π) :
    σ a ∈ adicHull (Subring.closure (insert π S)) π ∧
      ∃ b ∈ adicHull (Subring.closure (insert π S)) π, σ a - a = π * b := by
  have H := stable_closure S π _ (le_adicHull _ π) σ hS u hu hσ
  have approx : ∀ m : ℕ, ∃ b ∈ adicHull (Subring.closure (insert π S)) π,
      ∃ r, σ a - a = π * (b + π ^ m * r) := by
    intro m
    obtain ⟨p, hp, r, hr⟩ := mem_adicHull.1 ha (m + 1)
    obtain ⟨-, b, hb, h⟩ := H p hp
    have h2 := congrArg σ hr
    rw [map_sub, map_mul, map_pow, hσ, mul_pow] at h2
    exact ⟨b, hb, r - u ^ (m + 1) * σ r, by linear_combination h - h2 + hr⟩
  obtain ⟨b0, -, r0, h0⟩ := approx 0
  have hb : b0 + π ^ 0 * r0 ∈ adicHull (Subring.closure (insert π S)) π := by
    refine mem_adicHull_of_approx fun m => ?_
    obtain ⟨b, hb, r, h⟩ := approx m
    refine ⟨b, hb, -r, ?_⟩
    have := mul_left_cancel₀ hπ0 (h0.symm.trans h)
    linear_combination -this
  refine ⟨?_, _, hb, h0⟩
  have : σ a = a + π * (b0 + π ^ 0 * r0) := by linear_combination h0
  rw [this]
  exact Subring.add_mem _ ha (Subring.mul_mem _
    (le_adicHull _ π (Subring.subset_closure (Set.mem_insert _ _))) hb)

end General

theorem piS_ne_zero {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P) (s : ℕ) :
    GlobalTheory.IndefiniteRowSideFullHecke.SelmerFiniteUnramified.piS AI s ≠ 0 := by
  intro h
  have h1 : WittVector.teichmuller l (AI.εroot s) = 1 := sub_eq_zero.1 h
  have h2 : AI.εroot s = 1 := by
    have := congrArg (fun x : Ainf l => x.coeff 0) h1
    simpa using this
  apply AI.ε_ne_one
  have h3 : ((frobeniusEquiv (OCb l) l).symm)^[s] (1 : OCb l) = 1 :=
    Function.iterate_fixed (map_one _) s
  exact ((frobeniusEquiv (OCb l) l).symm.injective.iterate s) (h2.trans h3.symm)

theorem ringAs_stable : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (σ : Ainf l →+* Ainf l), (∀ w ∈ GlobalTheory.IndefiniteRowSideFullHecke.SelmerFiniteUnramified.wittFixedFrobeniusPow K, σ w = w) → (∃ u ∈ GlobalTheory.IndefiniteRowSideFullHecke.SelmerFiniteUnramified.ringAs AI K s, σ (GlobalTheory.IndefiniteRowSideFullHecke.SelmerFiniteUnramified.piS AI s) = GlobalTheory.IndefiniteRowSideFullHecke.SelmerFiniteUnramified.piS AI s * u) → ∀ a ∈ GlobalTheory.IndefiniteRowSideFullHecke.SelmerFiniteUnramified.ringAs AI K s, σ a ∈ GlobalTheory.IndefiniteRowSideFullHecke.SelmerFiniteUnramified.ringAs AI K s ∧ ∃ b ∈ GlobalTheory.IndefiniteRowSideFullHecke.SelmerFiniteUnramified.ringAs AI K s, σ a - a = GlobalTheory.IndefiniteRowSideFullHecke.SelmerFiniteUnramified.piS AI s * b := by
  intro l _ P AI K s σ hS ⟨u, hu, hσ⟩ a ha
  haveI : IsDomain (Ainf l) := inferInstance
  exact stable_adicHull _ _ (piS_ne_zero AI s) σ hS u hu hσ a ha

end GlobalTheory.RingAsStable
