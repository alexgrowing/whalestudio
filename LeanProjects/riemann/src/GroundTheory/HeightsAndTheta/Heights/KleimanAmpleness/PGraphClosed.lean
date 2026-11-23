import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PGraphClosedLocal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial
open scoped Pointwise

noncomputable section

universe u w

namespace GraphClosedAlt

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem mem_sub_of_mem_secs' {F : SubSystem S x Ω} {z : Ω} (hz : z ∈ F.secs) (I : Chart x) :
    z ∈ F.sub I := by
  rw [SubSystem.secs, Submodule.mem_iInf] at hz
  exact hz I

theorem exists_fin_generators (G : LineBundle S x) (hG : G.toSubSystem.Generated) :
    ∃ (r : ℕ) (g : Fin (r + 1) → Ω), (∀ a, g a ∈ G.toSubSystem.secs) ∧
      ∀ I, Submodule.span (chartRing S x I) (Set.range g) = G.sub I := by
  classical
  have hloc : ∀ I : Chart x, ∃ F : Finset Ω, (F : Set Ω) ⊆ G.toSubSystem.secs ∧
      G.sub I ≤ Submodule.span (chartRing S x I) (F : Set Ω) := by
    intro I
    obtain ⟨t, ht⟩ := G.fg I
    have hy : ∀ y : Ω, ∃ T : Finset Ω, (T : Set Ω) ⊆ G.toSubSystem.secs ∧
        (y ∈ G.sub I → y ∈ Submodule.span (chartRing S x I) (T : Set Ω)) := by
      intro y
      by_cases hyI : y ∈ G.sub I
      · have : y ∈ Submodule.span (chartRing S x I) (G.toSubSystem.secs : Set Ω) := by
          rw [hG I]; exact hyI
        obtain ⟨T, hT, hyT⟩ := Submodule.mem_span_finite_of_mem_span this
        exact ⟨T, hT, fun _ => hyT⟩
      · exact ⟨∅, by simp, fun h => absurd h hyI⟩
    choose T hT hTy using hy
    refine ⟨t.biUnion T, ?_, ?_⟩
    · intro z hz
      obtain ⟨y, -, hzy⟩ := Finset.mem_biUnion.mp hz
      exact hT y hzy
    · rw [← ht, Submodule.span_le]
      intro y hyt
      have hyI : y ∈ G.sub I := by rw [← ht]; exact Submodule.subset_span hyt
      exact Submodule.span_mono (by
        intro z hz
        exact Finset.mem_coe.mpr (Finset.mem_biUnion.mpr ⟨y, hyt, hz⟩)) (hTy y hyI)
  choose F hF hFI using hloc
  set A := Finset.univ.biUnion F
  let g : Fin (A.card + 1) → Ω := Fin.cons 0 fun i => (A.equivFin.symm i : Ω)
  have hrange : Set.range g = insert 0 (A : Set Ω) := by
    simp only [g, Fin.range_cons]
    congr 1
    ext y
    constructor
    · rintro ⟨i, rfl⟩; exact (A.equivFin.symm i).2
    · intro hy; exact ⟨A.equivFin ⟨y, hy⟩, by simp⟩
  have hA : (A : Set Ω) ⊆ G.toSubSystem.secs := by
    intro z hz
    obtain ⟨I, -, hzI⟩ := Finset.mem_biUnion.mp hz
    exact hF I hzI
  refine ⟨A.card, g, fun a => ?_, fun I => le_antisymm ?_ ?_⟩
  · have : g a ∈ insert 0 (A : Set Ω) := hrange ▸ Set.mem_range_self a
    rcases this with h0 | hA'
    · rw [h0]; exact Submodule.zero_mem _
    · exact hA hA'
  · rw [Submodule.span_le, hrange]
    rintro z (rfl | hz)
    · exact Submodule.zero_mem _
    · exact mem_sub_of_mem_secs' (hA hz) I
  · refine (hFI I).trans (Submodule.span_mono ?_)
    rw [hrange]
    intro z hz
    exact Set.mem_insert_of_mem _ (Finset.mem_coe.mpr
      (Finset.mem_biUnion.mpr ⟨I, Finset.mem_univ I, Finset.mem_coe.mp hz⟩))

theorem twist_pow_sub (G H : SubSystem S x Ω) (n : ℕ) (I : Chart x) :
    ((G.twist H).pow n).sub I = (H.sub I * G.sub I) ^ n := by
  rw [SubSystem.pow_sub, SubSystem.twist_sub_eq_mul_of_line]

theorem ampleChart_twist (G H : SubSystem S x Ω) {h g : Ω} (I : Chart x) (hg : g ∈ G.sub I) {u : Ω}
    (hu : u ∈ ampleChart H 1 h I) : u ∈ ampleChart (G.twist H) 1 (h * g) I := by
  obtain ⟨n, hn⟩ := hu
  refine ⟨n, ?_⟩
  rw [one_mul] at hn ⊢
  rw [SubSystem.pow_sub] at hn
  rw [twist_pow_sub, mul_pow]
  have : u * (h * g) ^ n = (u * h ^ n) * g ^ n := by ring
  rw [this]
  exact Submodule.mul_mem_mul hn (Submodule.pow_mem_pow _ hg n)

theorem ampleRing_twist (G H : SubSystem S x Ω) {h g : Ω} (hg : g ∈ G.secs) {u : Ω}
    (hu : u ∈ ampleRing H 1 h) : u ∈ ampleRing (G.twist H) 1 (h * g) :=
  Set.mem_iInter.mpr fun I =>
    ampleChart_twist G H I (mem_sub_of_mem_secs' hg I) (Set.mem_iInter.mp hu I)

theorem ampleRing_twist_subset (G H : SubSystem S x Ω) {r₁ r₂ : ℕ} (g : Fin (r₁ + 1) → Ω)
    (h : Fin (r₂ + 1) → Ω)
    (hgI : ∀ I, Submodule.span (chartRing S x I) (Set.range g) = G.sub I) (hh : IsVeryAmpleBy H h)
    {b₀ : Fin (r₁ + 1)} {l₀ : Fin (r₂ + 1)} (hne : h l₀ * g b₀ ≠ 0) (T : Subalgebra S Ω)
    (hT : ∀ b m, h m * g b / (h l₀ * g b₀) ∈ T) :
    ampleRing (G.twist H) 1 (h l₀ * g b₀) ⊆ T := by
  classical
  set p := h l₀ * g b₀ with hp
  have hl₀ : h l₀ ≠ 0 := left_ne_zero_of_mul hne
  have hb₀ : g b₀ ≠ 0 := right_ne_zero_of_mul hne
  have hB : ampleRing H 1 (h l₀) ⊆ T := by
    intro y hy
    have hy' := hh.closed l₀ hl₀ hy
    refine (Algebra.adjoin_le ?_ : ampleBase (S := S) h l₀ ≤ T) hy'
    rintro _ ⟨m, rfl⟩
    have : h m / h l₀ = h m * g b₀ / p := by rw [hp, mul_div_mul_right _ _ hb₀]
    show h m / h l₀ ∈ T
    rw [this]; exact hT b₀ m
  have hPn : ∀ n : ℕ, ∀ t ∈ (Set.range h * Set.range g) ^ n, t / p ^ n ∈ T := by
    intro n
    induction n with
    | zero =>
      intro t ht
      rw [pow_zero, Set.mem_one] at ht
      rw [ht, pow_zero, div_one]; exact one_mem T
    | succ n ih =>
      intro t ht
      rw [pow_succ, Set.mem_mul] at ht
      obtain ⟨t₁, ht₁, t₂, ht₂, rfl⟩ := ht
      obtain ⟨_, ⟨m, rfl⟩, _, ⟨b, rfl⟩, rfl⟩ := Set.mem_mul.mp ht₂
      have : t₁ * (h m * g b) / p ^ (n + 1) = (t₁ / p ^ n) * (h m * g b / p) := by
        rw [pow_succ, mul_div_mul_comm]
      rw [this]
      exact mul_mem (ih t₁ ht₁) (hT b m)
  obtain ⟨n, a, b, J, ha, hb, hsum, hJ⟩ := hh.affine l₀ hl₀
  intro y hy
  have hloc : ∀ k, ∃ e : ℕ, b k ^ e * y ∈ T := by
    intro k
    obtain ⟨n', hn'⟩ := Set.mem_iInter.mp hy (J k)
    rw [one_mul, twist_pow_sub, ← hgI (J k), ← hh.generates (J k), Submodule.span_mul_span,
      Submodule.span_pow] at hn'
    have hbT : b k ∈ T := hB (hb k)
    suffices hQ : ∀ z ∈ Submodule.span (chartRing S x (J k)) ((Set.range h * Set.range g) ^ n'),
        ∃ e : ℕ, b k ^ e * (z / p ^ n') ∈ T by
      obtain ⟨e, he⟩ := hQ _ hn'
      rw [mul_div_cancel_right₀ _ (pow_ne_zero _ hne)] at he
      exact ⟨e, he⟩
    intro z hz
    induction hz using Submodule.span_induction with
    | mem t ht => exact ⟨0, by rw [pow_zero, one_mul]; exact hPn n' t ht⟩
    | zero => exact ⟨0, by rw [zero_div, mul_zero]; exact zero_mem T⟩
    | add z₁ z₂ _ _ h₁ h₂ =>
      obtain ⟨e₁, he₁⟩ := h₁
      obtain ⟨e₂, he₂⟩ := h₂
      refine ⟨e₁ + e₂, ?_⟩
      have : b k ^ (e₁ + e₂) * ((z₁ + z₂) / p ^ n') =
          b k ^ e₂ * (b k ^ e₁ * (z₁ / p ^ n')) + b k ^ e₁ * (b k ^ e₂ * (z₂ / p ^ n')) := by
        rw [pow_add, add_div]; ring
      rw [this]
      exact add_mem (mul_mem (pow_mem hbT _) he₁) (mul_mem (pow_mem hbT _) he₂)
    | smul c z _ hz =>
      obtain ⟨e₂, he₂⟩ := hz
      obtain ⟨e₁, he₁⟩ := exists_pow_mul_mem_ampleRing H (h l₀) (b k) (J k) (hb k) (hJ k) c.2
      refine ⟨e₁ + e₂, ?_⟩
      have : b k ^ (e₁ + e₂) * (c • z / p ^ n') = (b k ^ e₁ * c) * (b k ^ e₂ * (z / p ^ n')) := by
        rw [chartRing_smul_def, pow_add]; ring
      rw [this]
      exact mul_mem (hB he₁) he₂
  choose e he using hloc
  let bT : Fin n → T := fun k => ⟨b k, hB (hb k)⟩
  have htop : Ideal.span (Set.range bT) = ⊤ := by
    rw [Ideal.eq_top_iff_one]
    have h1 : (1 : T) = ∑ k, (⟨a k, hB (ha k)⟩ : T) * bT k := by
      apply Subtype.ext
      simp only [bT]
      push_cast
      exact hsum.symm
    rw [h1]
    exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨k, rfl⟩)
  set E := ∑ k, e k
  have h1 : (1 : T) ∈ Ideal.span ((fun z : T => z ^ E) '' Set.range bT) := by
    rw [Ideal.span_pow_eq_top _ htop E]; trivial
  suffices hP : ∀ t ∈ Ideal.span ((fun z : T => z ^ E) '' Set.range bT), (t : Ω) * y ∈ T by
    simpa using hP 1 h1
  intro t ht
  induction ht using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨_, ⟨k, rfl⟩, rfl⟩ := hz
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le
      (Finset.single_le_sum (fun k _ => Nat.zero_le (e k)) (Finset.mem_univ k))
    have : ((bT k ^ E : T) : Ω) * y = b k ^ d * (b k ^ e k * y) := by
      simp only [SubmonoidClass.coe_pow, bT]
      rw [show E = e k + d from hd, pow_add]; ring
    rw [this]
    exact mul_mem (pow_mem (hB (hb k)) _) (he k)
  | zero => simp
  | add t₁ t₂ _ _ h₁ h₂ =>
    rw [Subalgebra.coe_add, add_mul]; exact add_mem h₁ h₂
  | smul c t _ ht =>
    rw [smul_eq_mul, Subalgebra.coe_mul, mul_assoc]; exact mul_mem c.2 ht

end GraphClosedAlt

open GraphClosedAlt in

theorem GraphClosed.proof : GraphClosed.Statement.{u, w} := by
  intro k _ Ω _ _ N x G H hG hH
  obtain ⟨r₁, g, hg, hgI⟩ := exists_fin_generators G hG
  obtain ⟨r₂, h, hh⟩ := hH
  have hr : (r₁ + 1) * (r₂ + 1) = (r₁ * r₂ + r₁ + r₂) + 1 := by ring
  let E : Fin (r₁ + 1) × Fin (r₂ + 1) ≃ Fin (r₁ * r₂ + r₁ + r₂ + 1) :=
    finProdFinEquiv.trans (finCongr hr)
  let pr : Fin (r₁ + 1) × Fin (r₂ + 1) → Ω := fun q => h q.2 * g q.1
  let s : Fin (r₁ * r₂ + r₁ + r₂ + 1) → Ω := fun j => pr (E.symm j)
  have hs : ∀ j, s j = h (E.symm j).2 * g (E.symm j).1 := fun j => rfl
  have hsE : ∀ b m, s (E (b, m)) = h m * g b := fun b m => by simp [s, pr]
  have hrange : Set.range s = Set.range h * Set.range g := by
    ext z
    constructor
    · rintro ⟨j, rfl⟩
      exact Set.mem_mul.mpr ⟨_, ⟨(E.symm j).2, rfl⟩, _, ⟨(E.symm j).1, rfl⟩, (hs j).symm⟩
    · intro hz
      obtain ⟨_, ⟨m, rfl⟩, _, ⟨b, rfl⟩, rfl⟩ := Set.mem_mul.mp hz
      exact ⟨E (b, m), hsE b m⟩
  refine ⟨r₁ * r₂ + r₁ + r₂, s, ?_, ?_, ?_, ?_⟩
  · intro j
    rw [hs, SubSystem.secs, Submodule.mem_iInf]
    intro I
    exact Submodule.subset_span ⟨h (E.symm j).2, mem_sub_of_mem_secs' (hh.mem_secs _) I,
      g (E.symm j).1, mem_sub_of_mem_secs' (hg _) I, (smul_eq_mul _ _).symm⟩
  · intro I
    rw [hrange, ← Submodule.span_mul_span, hh.generates I, hgI I,
      SubSystem.twist_sub_eq_mul_of_line]
  · intro j hj
    rw [hs] at hj ⊢
    refine ampleRing_twist_subset G.toSubSystem H.toSubSystem g h hgI hh hj _ fun b m => ?_
    have : h m * g b / (h (E.symm j).2 * g (E.symm j).1) = s (E (b, m)) / s j := by
      rw [hsE, hs]
    rw [this]
    exact Algebra.subset_adjoin ⟨E (b, m), rfl⟩
  · intro j hj
    rw [hs] at hj ⊢
    have hl : h (E.symm j).2 ≠ 0 := left_ne_zero_of_mul hj
    obtain ⟨n, a, b, J, ha, hb, hsum, hJ⟩ := hh.affine _ hl
    refine ⟨n, a, b, J, fun q => ampleRing_twist _ _ (hg _) (ha q),
      fun q => ampleRing_twist _ _ (hg _) (hb q), hsum, fun q I => ?_⟩
    obtain ⟨e, he⟩ := hJ q I
    exact ⟨e, ampleChart_twist _ _ I (mem_sub_of_mem_secs' (hg _) I) he⟩

end

end GroundTheory.Heights₂.Heights.Kleiman
