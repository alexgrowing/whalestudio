import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsHilbert
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.LengthLocalizedQuotientEqZero
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u v

namespace MultigradedFiltration

variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  [∀ k, Fintype (ι k)] {M : Type v} [AddCommGroup M] [Module (MRing ι F) M] [Module F M]
  [IsScalarTower F (MRing ι F) M] {piece : (K → ℤ) → Submodule F M}

def degZ (b : K → ℕ) : K → ℤ := fun k => (b k : ℤ)

theorem degZ_add (b b' : K → ℕ) : degZ (b + b') = degZ b + degZ b' := by
  funext k; simp [degZ]

theorem degZ_injective : Function.Injective (degZ : (K → ℕ) → K → ℤ) := by
  intro b b' h; funext k
  have h' := congr_fun h k
  simp only [degZ] at h'
  exact_mod_cast h'

theorem degZ_zero : degZ (0 : K → ℕ) = 0 := by
  funext k; simp [degZ]

theorem X_pow_smul_mem (hM : IsMultigrading ι M piece) (v : Σ k, ι k) (n : ℕ) :
    ∀ (m : K → ℤ) (x : M), x ∈ piece m →
      ((X v : MRing ι F) ^ n) • x ∈ piece (m + degZ (n • blockWeight ι v)) := by
  induction n with
  | zero => intro m x hx; simpa [degZ_zero] using hx
  | succ n ih =>
    intro m x hx
    rw [pow_succ, mul_smul]
    have h := ih _ _ (hM.smul_mem v m x hx)
    convert h using 2
    funext k
    simp only [degZ, unitDeg, blockWeight, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
    split_ifs <;> push_cast <;> ring

theorem monomial_smul_mem (hM : IsMultigrading ι M piece) (d : (Σ k, ι k) →₀ ℕ) :
    ∀ (m : K → ℤ) (x : M), x ∈ piece m →
      (monomial d (1 : F) : MRing ι F) • x ∈ piece (m + degZ (Finsupp.weight (blockWeight ι) d)) := by
  induction d using Finsupp.induction with
  | zero => intro m x hx; simpa [degZ_zero] using hx
  | single_add v n d _ _ ih =>
    intro m x hx
    have e : (monomial (Finsupp.single v n + d) (1 : F) : MRing ι F) =
        (X v : MRing ι F) ^ n * monomial d (1 : F) := by
      rw [X_pow_eq_monomial, monomial_mul, one_mul]
    rw [e, mul_smul]
    have h := X_pow_smul_mem hM v n _ _ (ih m x hx)
    convert h using 2
    rw [map_add, Finsupp.weight_single, degZ_add, add_assoc, add_comm (degZ _)]

theorem homog_smul_mem (hM : IsMultigrading ι M piece) {f : MRing ι F} {b : K → ℕ}
    (hf : IsWeightedHomogeneous (blockWeight ι) f b) {m : K → ℤ} {x : M} (hx : x ∈ piece m) :
    f • x ∈ piece (m + degZ b) := by
  have ef := f.as_sum
  rw [ef]
  rw [Finset.sum_smul]
  refine Submodule.sum_mem _ fun d hd => ?_
  have hw : Finsupp.weight (blockWeight ι) d = b := hf (mem_support_iff.mp hd)
  have e : (monomial d (coeff d f) : MRing ι F) = coeff d f • monomial d (1 : F) := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [e, smul_assoc]
  exact Submodule.smul_mem _ _ (hw ▸ monomial_smul_mem hM d m x hx)

section Graded

variable [DecidableEq (K → ℤ)] [DirectSum.Decomposition piece]

theorem decompose_smul (hM : IsMultigrading ι M piece) (f : MRing ι F) {c : K → ℤ} {x : M}
    (hx : x ∈ piece c) (m : K → ℤ) :
    (DirectSum.decompose piece (f • x) m : M) =
      (∑ d ∈ f.support with c + degZ (Finsupp.weight (blockWeight ι) d) = m,
        monomial d (coeff d f)) • x := by
  have ef := f.as_sum
  conv_lhs => rw [ef]
  rw [Finset.sum_smul, DirectSum.decompose_sum, DFinsupp.finsetSum_apply,
    AddSubmonoidClass.coe_finsetSum, Finset.sum_filter, Finset.sum_smul]
  refine Finset.sum_congr rfl fun d _ => ?_
  have hd : (monomial d (coeff d f) : MRing ι F) • x ∈
      piece (c + degZ (Finsupp.weight (blockWeight ι) d)) :=
    homog_smul_mem hM (isWeightedHomogeneous_monomial _ _ _ rfl) hx
  split_ifs with h
  · subst h; exact DirectSum.decompose_of_mem_same piece hd
  · rw [zero_smul]; exact DirectSum.decompose_of_mem_ne piece hd h

def IsGradedSub (piece : (K → ℤ) → Submodule F M) [DirectSum.Decomposition piece]
    (N : Submodule (MRing ι F) M) : Prop :=
  ∀ y ∈ N, ∀ m, (DirectSum.decompose piece y m : M) ∈ N

theorem isGradedSub_bot : IsGradedSub piece (⊥ : Submodule (MRing ι F) M) := by
  intro y hy m
  rw [Submodule.mem_bot] at hy
  subst hy
  simp

theorem isGradedSub_sup (hM : IsMultigrading ι M piece) {N : Submodule (MRing ι F) M}
    (hN : IsGradedSub piece N) {c : K → ℤ} {x : M} (hx : x ∈ piece c) :
    IsGradedSub piece (N ⊔ Submodule.span (MRing ι F) {x}) := by
  intro y hy m
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hy
  obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hb
  rw [DirectSum.decompose_add, DirectSum.add_apply, Submodule.coe_add]
  refine add_mem (Submodule.mem_sup_left (hN a ha m)) (Submodule.mem_sup_right ?_)
  rw [decompose_smul hM s hx m]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x)

theorem isMultiHomog_colon (hM : IsMultigrading ι M piece) {N : Submodule (MRing ι F) M}
    (hN : IsGradedSub piece N) {c : K → ℤ} {x : M} (hx : x ∈ piece c) :
    IsMultiHomogIdeal (N.colon {x}) := by
  intro f hf b
  rw [Submodule.mem_colon_singleton] at hf ⊢
  have h := hN _ hf (c + degZ b)
  rw [decompose_smul hM f hx] at h
  convert h using 2
  rw [weightedHomogeneousComponent_apply]
  refine Finset.sum_congr (Finset.filter_congr fun d _ => ?_) fun _ _ => rfl
  exact ⟨fun h => by rw [h], fun h => degZ_injective (add_left_cancel h)⟩

theorem exists_homog_not_mem {N : Submodule (MRing ι F) M} (hN : N ≠ ⊤) :
    ∃ (c : K → ℤ) (x : M), x ∈ piece c ∧ x ∉ N := by
  classical
  by_contra h
  push Not at h
  apply hN
  rw [eq_top_iff]
  intro y _
  rw [← DirectSum.sum_support_decompose piece y]
  exact Submodule.sum_mem _ fun i _ => h i _ (Submodule.coe_mem _)

end Graded

theorem isPrime_of_forms_ordered {σ L : Type*} [AddCommMonoid L] [LinearOrder L]
    [IsOrderedCancelAddMonoid L] (w : σ → L) (q : Ideal (MvPolynomial σ F))
    (hq : ∀ r ∈ q, ∀ i, weightedHomogeneousComponent w i r ∈ q) (hne : q ≠ ⊤)
    (h : ∀ a b : MvPolynomial σ F, (∃ i, IsWeightedHomogeneous w a i) →
      (∃ j, IsWeightedHomogeneous w b j) → a * b ∈ q → a ∈ q ∨ b ∈ q) :
    q.IsPrime := by
  letI := weightedGradedAlgebra F w
  have hH : q.IsHomogeneous (weightedHomogeneousSubmodule F w) := by
    intro i r hr
    have e : (DirectSum.decompose (weightedHomogeneousSubmodule F w) r i : MvPolynomial σ F) =
        weightedHomogeneousComponent w i r := weightedDecomposition.decompose'_apply F w r i
    rw [e]
    exact hq r hr i
  refine hH.isPrime_of_homogeneous_mem_or_mem hne ?_
  rintro a b ⟨i, hi⟩ ⟨j, hj⟩ hab
  exact h a b ⟨i, hi⟩ ⟨j, hj⟩ hab

theorem isPrime_of_forms (q : Ideal (MRing ι F)) (hq : IsMultiHomogIdeal q) (hne : q ≠ ⊤)
    (h : ∀ a b : MRing ι F, (∃ i, IsWeightedHomogeneous (blockWeight ι) a i) →
      (∃ j, IsWeightedHomogeneous (blockWeight ι) b j) → a * b ∈ q → a ∈ q ∨ b ∈ q) :
    q.IsPrime := by
  classical
  letI : LinearOrder K := LinearOrder.lift' (Fintype.equivFin K) (Fintype.equivFin K).injective
  haveI : WellFoundedLT K := Finite.to_wellFoundedLT
  have hw : ∀ d : (Σ k, ι k) →₀ ℕ, Finsupp.weight (fun v => toLex (blockWeight ι v)) d =
      toLex (Finsupp.weight (blockWeight ι) d) := by
    intro d
    induction d using Finsupp.induction with
    | zero => simp
    | single_add v n d _ _ ih =>
      rw [map_add, map_add, ih, Finsupp.weight_single, Finsupp.weight_single, toLex_add, toLex_smul]
      rfl
  have hc : ∀ (i : Lex (K → ℕ)) (r : MRing ι F),
      weightedHomogeneousComponent (fun v => toLex (blockWeight ι v)) i r =
        weightedHomogeneousComponent (blockWeight ι) (ofLex i) r := by
    intro i r
    ext d
    rw [coeff_weightedHomogeneousComponent, coeff_weightedHomogeneousComponent, hw]
    exact if_congr ⟨fun e => by rw [← e]; rfl, fun e => by rw [e]; rfl⟩ rfl rfl
  have hh : ∀ (a : MRing ι F) (i : Lex (K → ℕ)),
      IsWeightedHomogeneous (fun v => toLex (blockWeight ι v)) a i →
        IsWeightedHomogeneous (blockWeight ι) a (ofLex i) := by
    intro a i ha d hd
    have := ha hd
    rw [hw] at this
    rw [← this, ofLex_toLex]
  refine isPrime_of_forms_ordered (fun v => toLex (blockWeight ι v)) q (fun r hr i => ?_) hne ?_
  · rw [hc]; exact hq r hr _
  · rintro a b ⟨i, hi⟩ ⟨j, hj⟩ hab
    exact h a b ⟨_, hh a i hi⟩ ⟨_, hh b j hj⟩ hab

section Chain

variable [DecidableEq (K → ℤ)] [DirectSum.Decomposition piece]

theorem isPrime_colon (hM : IsMultigrading ι M piece) {N : Submodule (MRing ι F) M}
    (hN : IsGradedSub piece N) {c : K → ℤ} {x : M} (hx : x ∈ piece c) (hxN : x ∉ N)
    (hmax : ∀ (c' : K → ℤ) (y : M), y ∈ piece c' → y ∉ N → ¬ N.colon {x} < N.colon {y}) :
    (N.colon {x}).IsPrime := by
  refine isPrime_of_forms _ (isMultiHomog_colon hM hN hx) ?_ ?_
  · intro htop
    apply hxN
    have h1 : (1 : MRing ι F) ∈ N.colon {x} := htop ▸ Submodule.mem_top
    rwa [Submodule.mem_colon_singleton, one_smul] at h1
  · rintro a b - ⟨j, hj⟩ hab
    by_cases hb : b ∈ N.colon {x}
    · exact Or.inr hb
    left
    rw [Submodule.mem_colon_singleton] at hb hab
    have hbx : b • x ∈ piece (c + degZ j) := homog_smul_mem hM hj hx
    have hle : N.colon {x} ≤ N.colon {b • x} := by
      intro s hs
      rw [Submodule.mem_colon_singleton] at hs ⊢
      rw [smul_comm]
      exact N.smul_mem b hs
    have heq := eq_of_le_of_not_lt hle (hmax _ _ hbx hb)
    have ha : a ∈ N.colon {b • x} := by
      rw [Submodule.mem_colon_singleton, ← mul_smul]
      exact hab
    rwa [← heq] at ha

theorem exists_step (hM : IsMultigrading ι M piece) {N : Submodule (MRing ι F) M}
    (hN : IsGradedSub piece N) (hNt : N ≠ ⊤) :
    ∃ (c : K → ℤ) (x : M), x ∈ piece c ∧ x ∉ N ∧ (N.colon {x}).IsPrime ∧
      IsMultiHomogIdeal (N.colon {x}) := by
  obtain ⟨c₀, x₀, hx₀, hx₀N⟩ := exists_homog_not_mem (piece := piece) hNt
  obtain ⟨I, ⟨c, x, hx, hxN, rfl⟩, hI⟩ :=
    set_has_maximal_iff_noetherian.mpr (inferInstance : IsNoetherian (MRing ι F) (MRing ι F))
      {I | ∃ (c : K → ℤ) (x : M), x ∈ piece c ∧ x ∉ N ∧ N.colon {x} = I}
      ⟨_, c₀, x₀, hx₀, hx₀N, rfl⟩
  exact ⟨c, x, hx, hxN,
    isPrime_colon hM hN hx hxN fun c' y hy hyN => hI _ ⟨c', y, hy, hyN, rfl⟩,
    isMultiHomog_colon hM hN hx⟩

theorem exists_chain [Module.Finite (MRing ι F) M] (hM : IsMultigrading ι M piece) :
    ∀ N₀ : Submodule (MRing ι F) M, IsGradedSub piece N₀ →
      ∃ (n : ℕ) (N : Fin (n + 1) → Submodule (MRing ι F) M) (x : Fin n → M) (c : Fin n → K → ℤ)
        (q : Fin n → Ideal (MRing ι F)),
        N 0 = N₀ ∧ N (Fin.last n) = ⊤ ∧
        ∀ j : Fin n, x j ∈ piece (c j) ∧
          N j.succ = N j.castSucc ⊔ Submodule.span (MRing ι F) {x j} ∧
          (q j).IsPrime ∧ IsMultiHomogIdeal (q j) ∧
          ∀ s : MRing ι F, s • x j ∈ N j.castSucc ↔ s ∈ q j := by
  haveI : IsNoetherian (MRing ι F) M := inferInstance
  haveI : WellFoundedGT (Submodule (MRing ι F) M) := isNoetherian_iff'.mp inferInstance
  intro N₀
  induction N₀ using WellFoundedGT.induction with
  | _ N₀ ih =>
  intro hN₀
  by_cases ht : N₀ = ⊤
  · exact ⟨0, fun _ => N₀, Fin.elim0, Fin.elim0, Fin.elim0, rfl, ht, fun j => j.elim0⟩
  obtain ⟨c, x, hx, hxN, hq, hqh⟩ := exists_step hM hN₀ ht
  have hlt : N₀ < N₀ ⊔ Submodule.span (MRing ι F) {x} := by
    refine lt_of_le_of_ne le_sup_left fun h => hxN ?_
    rw [h]
    exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self x)
  obtain ⟨n, N, x', c', q', h0, hl, hj⟩ := ih _ hlt (isGradedSub_sup hM hN₀ hx)
  refine ⟨n + 1, Fin.cons N₀ N, Fin.cons x x', Fin.cons c c', Fin.cons (N₀.colon {x}) q', rfl,
    ?_, fun j => ?_⟩
  · rw [← Fin.succ_last, Fin.cons_succ]
    exact hl
  · refine Fin.cases ?_ (fun j => ?_) j
    · simp only [Fin.cons_zero, Fin.castSucc_zero, Fin.cons_succ]
      exact ⟨hx, h0, hq, hqh, fun s => Submodule.mem_colon_singleton.symm⟩
    · simp only [← Fin.succ_castSucc, Fin.cons_succ]
      exact hj j

end Chain

end MultigradedFiltration

theorem MultigradedFiltration.proof : MultigradedFiltration.Statement.{u, v} := by
  intro F _ K _ _ ι _ M _ _ _ _ _ piece hM
  classical
  letI := hM.internal.chooseDecomposition
  obtain ⟨n, N, x, c, q, h0, hl, hj⟩ :=
    MultigradedFiltration.exists_chain hM ⊥ MultigradedFiltration.isGradedSub_bot
  refine ⟨n, N, x, c, q, h0, hl, hj, fun W hW => ?_⟩
  haveI : W.IsPrime := hW.1.1
  convert GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel.card_eq_length_of_filtration N x q h0 hl
    (fun j => (hj j).2.1) (fun j => (hj j).2.2.1) (fun j => (hj j).2.2.2.2) W hW using 1
  rfl

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
