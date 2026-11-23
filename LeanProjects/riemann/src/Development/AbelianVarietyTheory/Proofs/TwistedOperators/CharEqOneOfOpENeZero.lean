import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwasawaBlockTriangular

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped Topology

noncomputable section
namespace GlobalTheory.RootEx.Supp

section Bounds
variable {k : Type} [Field k] [ValuativeRel k]

def Bd {ι κ : Type} (γ : ValueGroupWithZero k) (x : Matrix ι κ k) : Prop := ∀ r s, valuation k (x r s) ≤ γ

theorem Bd.mul {ι κ τ : Type} [Fintype κ] {γ δ : ValueGroupWithZero k} {x : Matrix ι κ k} {y : Matrix κ τ k}
    (hx : Bd γ x) (hy : Bd δ y) : Bd (γ * δ) (x * y) := by
  intro r s
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_le _ fun t _ => ?_
  rw [map_mul]
  exact mul_le_mul' (hx r t) (hy t s)

theorem Bd.mono {ι κ : Type} {γ δ : ValueGroupWithZero k} {x : Matrix ι κ k} (hx : Bd γ x) (h : γ ≤ δ) :
    Bd δ x := fun r s => (hx r s).trans h

theorem bd_one {ι : Type} [DecidableEq ι] : Bd 1 (1 : Matrix ι ι k) := by
  intro r s
  rw [Matrix.one_apply]
  split_ifs <;> simp

theorem bd_zero {ι κ : Type} (γ : ValueGroupWithZero k) : Bd γ (0 : Matrix ι κ k) := by
  intro r s; simp

theorem bd_fromBlocks {ι κ ι' κ' : Type} {γ : ValueGroupWithZero k} {a : Matrix ι κ k} {b : Matrix ι κ' k}
    {c : Matrix ι' κ k} {d : Matrix ι' κ' k} (ha : Bd γ a) (hb : Bd γ b) (hc : Bd γ c) (hd : Bd γ d) :
    Bd γ (fromBlocks a b c d) := by
  rintro (r | r) (s | s)
  exacts [ha r s, hb r s, hc r s, hd r s]

variable [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem bd_of_mem_KO {ι : Type} [Fintype ι] [DecidableEq ι] {w : GL ι k} (hw : w ∈ KO k ι) : Bd 1 w.val := by
  obtain ⟨g, rfl⟩ := hw
  intro r s
  exact (g.val r s).2

theorem exists_bd_of_isCompact {ι κ : Type} [Finite ι] [Finite κ] {S : Set (Matrix ι κ k)} (hS : IsCompact S) :
    ∃ γ : ValueGroupWithZero k, ∀ x ∈ S, Bd γ x := by
  have hT : IsCompact (⋃ r, ⋃ s, (fun x : Matrix ι κ k => x r s) '' S) :=
    isCompact_iUnion fun r => isCompact_iUnion fun s => hS.image (by fun_prop)
  obtain ⟨u, hu⟩ := hT.elim_directed_cover (fun s : kˣ => cball s) isOpen_cball
    (fun y _ => by
      by_cases hy : y = 0
      · exact Set.mem_iUnion.2 ⟨1, by simp [cball, hy]⟩
      · exact Set.mem_iUnion.2 ⟨Units.mk0 y hy, by simp [cball]⟩)
    (fun s t => by
      rcases le_total (valuation k (s : k)) (valuation k (t : k)) with h | h
      · exact ⟨t, fun y (hy : valuation k y ≤ _) => (hy.trans h : valuation k y ≤ _), subset_rfl⟩
      · exact ⟨s, subset_rfl, fun y (hy : valuation k y ≤ _) => (hy.trans h : valuation k y ≤ _)⟩)
  exact ⟨valuation k (u : k), fun x hx r s => hu (Set.mem_iUnion.2 ⟨r, Set.mem_iUnion.2 ⟨s, x, hx, rfl⟩⟩)⟩

theorem exists_bd_subset {ι κ : Type} [Fintype ι] [Fintype κ] (Λ : AddSubgroup (Matrix ι κ k))
    (hΛ : IsOpen (Λ : Set (Matrix ι κ k))) :
    ∃ u : kˣ, ∀ x, Bd (valuation k (u : k)) x → x ∈ Λ := by
  classical
  have h : ∀ᶠ t in 𝓝 (0 : k), ∀ r s, Matrix.single r s t ∈ Λ := by
    refine Filter.eventually_all.2 fun r => Filter.eventually_all.2 fun s => ?_
    have hc : Continuous fun t : k => Matrix.single r s t := by
      refine continuous_pi fun i => continuous_pi fun j => ?_
      simp only [Matrix.single, Matrix.of_apply]
      split_ifs
      exacts [continuous_id, continuous_const]
    refine hc.continuousAt.eventually_mem (hΛ.mem_nhds ?_)
    simp
  obtain ⟨u, hu⟩ := exists_cball_subset h
  refine ⟨u, fun x hx => ?_⟩
  rw [Matrix.matrix_eq_sum_single x]
  exact sum_mem fun r _ => sum_mem fun s _ => hu (hx r s) r s

theorem isCompact_bd {ι : Type} [Fintype ι] [DecidableEq ι] (γ : ValueGroupWithZero k) :
    IsCompact {g : GL ι k | Bd γ g.val ∧ Bd γ (g⁻¹).val} := by
  haveI := t2Space k
  have hB : IsCompact {x : Matrix ι ι k | Bd γ x} := by
    have := isCompact_univ_pi (fun _ : ι => isCompact_univ_pi
      (fun _ : ι => IsNonarchimedeanLocalField.isCompact_closedBall k γ))
    have e : {x : Matrix ι ι k | Bd γ x} =
        (Set.univ.pi fun _ : ι => Set.univ.pi fun _ : ι => {x : k | valuation k x ≤ γ} : Set (ι → ι → k)) := by
      ext x
      exact ⟨fun h r _ s _ => h r s, fun h r s => h r trivial s trivial⟩
    rw [e]
    exact this
  have := (Units.isClosedEmbedding_embedProduct (α := Matrix ι ι k)).isCompact_preimage
    (hB.prod (hB.image MulOpposite.continuous_op))
  convert this using 1
  ext g
  refine and_congr_right fun _ => ⟨fun h => ⟨_, h, rfl⟩, ?_⟩
  rintro ⟨x, hx, e⟩
  obtain rfl : x = (g⁻¹).val := MulOpposite.op_injective e
  exact hx

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem exists_bd_of_char (ψ : AddChar k Circle) (hψ : ψ ≠ 1) (u : kˣ) :
    ∃ γ : ValueGroupWithZero k, ∀ a : k,
      (∀ t, valuation k t ≤ valuation k (u : k) → ψ (a * t) = 1) → valuation k a ≤ γ := by
  obtain ⟨y, hy⟩ : ∃ y, ψ y ≠ 1 := by
    by_contra h
    push Not at h
    exact hψ (by ext y; simp [h y])
  refine ⟨valuation k (y / u), fun a ha => ?_⟩
  by_contra hlt
  push Not at hlt
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at hlt
  apply hy
  have := ha (y / a) (by
    rw [map_div₀] at hlt ⊢
    rw [div_lt_iff₀ (by simp [zero_lt_iff])] at hlt
    rw [div_le_iff₀ (by simp [zero_lt_iff, ha0]), mul_comm]
    exact hlt.le)
  rwa [mul_div_cancel₀ _ ha0] at this

end Bounds

section Levi
variable {k : Type} [Field k] {ι : Type} [Fintype ι] [DecidableEq ι]

def diagPart (lv : ι → ℕ) (b : Matrix ι ι k) : Matrix ι ι k :=
  Matrix.of fun r s => if lv r = lv s then b r s else 0

theorem mul_diagPart_apply {lv : ι → ℕ} {b b' : Matrix ι ι k} (hb : b.BlockTriangular lv)
    (hb' : b'.BlockTriangular lv) {r s : ι} (h : lv s ≤ lv r) :
    (b * diagPart lv b') r s = (b * b') r s := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp only [diagPart, Matrix.of_apply]
  split_ifs with h1
  · rfl
  · rcases lt_or_gt_of_ne h1 with h2 | h2
    · rw [hb (h2.trans_le h)]; simp
    · rw [hb' h2]

theorem diagPart_mul {lv : ι → ℕ} {b b' : Matrix ι ι k} (hb : b.BlockTriangular lv)
    (hb' : b'.BlockTriangular lv) (h1 : b * b' = 1) : diagPart lv b * diagPart lv b' = 1 := by
  ext r s
  by_cases h : lv r = lv s
  · rw [← h1, ← mul_diagPart_apply hb hb' h.ge, Matrix.mul_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [diagPart, Matrix.of_apply]
    by_cases h2 : lv t = lv s
    · simp [h, h2]
    · simp [h2]
  · rw [Matrix.one_apply_ne (fun e => h (by rw [e])), Matrix.mul_apply]
    refine Finset.sum_eq_zero fun t _ => ?_
    simp only [diagPart, Matrix.of_apply]
    by_cases h2 : lv t = lv s
    · simp [h, h2]
    · simp [h2]

theorem inv_blockTriangular {lv : ι → ℕ} {b : GL ι k} (hb : b.val.BlockTriangular lv) :
    (b⁻¹).val.BlockTriangular lv := by
  rw [Matrix.coe_units_inv]
  letI := b.invertible
  exact Matrix.blockTriangular_inv_of_blockTriangular hb

def levi (lv : ι → ℕ) (b : GL ι k) (hb : b.val.BlockTriangular lv) : GL ι k :=
  ⟨diagPart lv b.val, diagPart lv (b⁻¹).val, diagPart_mul hb (inv_blockTriangular hb) b.mul_inv,
    diagPart_mul (inv_blockTriangular hb) hb b.inv_mul⟩

end Levi

theorem exists_embX_mul {k : Type} [Field k] [ValuativeRel k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
    (m : GL (n ⊕ Fin c) k) (h0 : ∀ i s, m.val (Sum.inr i) (Sum.inl s) = 0) {γ : ValueGroupWithZero k}
    (hγ : 1 ≤ γ) (h1 : ∀ i j, valuation k (m.val (Sum.inr i) (Sum.inr j)) ≤ γ)
    (h2 : ∀ r j, valuation k ((m⁻¹).val r (Sum.inr j)) ≤ γ) :
    ∃ (x : GL n k) (w : GL (n ⊕ Fin c) k), m = embX c x * w ∧ Bd (γ * γ) w.val ∧ Bd (γ * γ) (w⁻¹).val := by
  obtain ⟨m, m', hm, hm'⟩ := m
  change ∀ r j, valuation k (m' r (Sum.inr j)) ≤ γ at h2
  dsimp only at h0 h1
  obtain ⟨a, B, C, t, rfl⟩ : ∃ a B C t, m = fromBlocks a B C t := ⟨_, _, _, _, (fromBlocks_toBlocks m).symm⟩
  obtain ⟨a', B', C', t', rfl⟩ : ∃ a B C t, m' = fromBlocks a B C t :=
    ⟨_, _, _, _, (fromBlocks_toBlocks m').symm⟩
  obtain rfl : C = 0 := by ext i s; exact h0 i s
  have hm2 := hm
  rw [fromBlocks_multiply, ← fromBlocks_one, fromBlocks_inj] at hm2
  obtain ⟨e1, e2, e3, e4⟩ := hm2
  simp only [Matrix.zero_mul, zero_add] at e3 e4
  have e5 : t' * t = 1 := mul_eq_one_comm.1 e4
  obtain rfl : C' = 0 := by rw [← Matrix.one_mul C', ← e5, Matrix.mul_assoc, e3, Matrix.mul_zero]
  simp only [Matrix.mul_zero, add_zero] at e1
  have hγ2 : γ ≤ γ * γ := le_mul_of_one_le_left' hγ
  have ht : Bd γ t := fun i j => h1 i j
  have ht' : Bd γ t' := fun i j => h2 (Sum.inr i) j
  have hB' : Bd γ B' := fun i j => h2 (Sum.inl i) j
  refine ⟨⟨a, a', e1, mul_eq_one_comm.1 e1⟩, ⟨fromBlocks 1 (-(B' * t)) 0 t, fromBlocks 1 B' 0 t', ?_, ?_⟩,
    ?_, ?_, ?_⟩
  · simp [fromBlocks_multiply, Matrix.mul_assoc, e4]
  · simp [fromBlocks_multiply, e5]
  · ext1
    change fromBlocks a B 0 t = fromBlocks a 0 0 1 * fromBlocks 1 (-(B' * t)) 0 t
    have : a * (B' * t) = -B := by
      rw [← Matrix.mul_assoc, eq_neg_of_add_eq_zero_left e2, Matrix.neg_mul, Matrix.mul_assoc, e5, Matrix.mul_one]
    simp [fromBlocks_multiply, this]
  · refine bd_fromBlocks (bd_one.mono (hγ.trans hγ2)) ?_ (bd_zero _) (ht.mono hγ2)
    intro r s
    rw [Matrix.neg_apply, Valuation.map_neg]
    exact hB'.mul ht r s
  · exact bd_fromBlocks (bd_one.mono (hγ.trans hγ2)) (hB'.mono hγ2) (bd_zero _) (ht'.mono hγ2)

theorem char_eq_one_of_opE_ne_zero {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {n n' : Type} [Fintype n] [DecidableEq n]
    [Fintype n'] [DecidableEq n'] {c p : ℕ} (ψ : AddChar k Circle) (ν : Measure k) [ν.IsAddHaarMeasure]
    (F : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (x₀ : Matrix n n' k) (hF : opE ψ ν p F x₀ ≠ 0)
    (d : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) (hd : ∀ r s, ¬ Free p (r, s) → d r s = 0)
    (hFd : ∀ x, F (x + d) = F x) : ψ (ch d) = 1 := by
  classical
  haveI := secondCountable k
  unfold opE at hF
  set e₀ : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k := fun rs => d rs.1.1 rs.1.2
  have hadd : ∀ e, affPt p x₀ (e₀ + e) = affPt p x₀ e + d := by
    intro e
    ext r s
    simp only [affPt, Matrix.add_apply, Matrix.of_apply]
    split_ifs with h
    · simp [e₀]; ring
    · simp [hd r s h]
  have hch : ∀ x : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k, ch (x + d) = ch x + ch d := by
    intro x; simp [ch, Finset.sum_add_distrib]
  have key := integral_add_left_eq_self (μ := Measure.pi fun _ => ν)
    (fun e => F (affPt p x₀ e) * (ψ (-ch (affPt p x₀ e)) : ℂ)) e₀
  simp only [hadd, hFd, hch, neg_add, AddChar.map_add_eq_mul, Circle.coe_mul, ← mul_assoc] at key
  rw [integral_mul_const] at key
  have h1 : (ψ (-ch d) : ℂ) = 1 := by
    apply mul_left_cancel₀ hF
    rw [mul_one]
    convert key
  have h2 : ψ (-ch d) = 1 := Circle.coe_eq_one.1 h1
  rwa [AddChar.map_neg_eq_inv, inv_eq_one] at h2

theorem inv_mul_affPt_apply {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n]
    [Fintype n'] [DecidableEq n'] {c p : ℕ} {b : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k}
    (hb : b.BlockTriangular (lev p)) (x₀ : Matrix n n' k)
    (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) (r : n ⊕ Fin c) (j : Fin c)
    (h : lev p r = lev p (Sum.inr j : n ⊕ Fin c)) :
    (b * affPt p x₀ e) r (Sum.inr j.castSucc) = b r (Sum.inr j) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (Sum.inr j)]
  · simp [affPt, basePt, Free]
  · intro s _ hs
    by_cases hl : lev p s < lev p r
    · rw [hb hl, zero_mul]
    · rw [h] at hl
      rcases s with s | l
      · have : ¬ p < j.val + 1 := by simpa [lev] using hl
        simp [affPt, basePt, Free, this]
      · have h1 : ¬ l.val < j.val := by simpa [lev] using hl
        have h2 : l.val ≠ j.val := fun e => hs (by rw [Fin.ext e])
        simp [affPt, basePt, Free, h1, h2]
  · simp

end GlobalTheory.RootEx.Supp

namespace GlobalTheory.RootEx
open Supp

theorem opE_support_compact_mod_R : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ) (_ : 1 ≤ p) (_ : p ≤ c) (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : ψ ≠ 1) (ν : Measure k) [ν.IsAddHaarMeasure] (S : Set (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) (_ : IsCompact S) (Λ : AddSubgroup (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) (_ : IsOpen (Λ : Set (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k))), ∃ Ω : Set (GL (n ⊕ Fin c) k), IsCompact Ω ∧ ∀ (μ : kˣ →* ℂˣ) (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ), Function.support Φ ⊆ S → (∀ x, ∀ y ∈ Λ, Φ (x + y) = Φ x) → ∀ (χ : Matrix (n ⊕ Fin c) n' k → ℂ), IsLocallyConstant χ → ∀ (h : GL (n ⊕ Fin c) k) (x₀ : Matrix n n' k), opE ψ ν p (fun x => χ x.toCols₁ * om μ 1 h Φ x) x₀ ≠ 0 → ∃ r ∈ R k n c p, ∃ w ∈ Ω, h = r * w := by
  intro k _ _ _ _ _ _ n n' _ _ _ _ c p _ _ ψ _ hψ ν _ S hS Λ hΛ
  obtain ⟨γ₁, hγ₁⟩ := exists_bd_of_isCompact hS
  obtain ⟨u, hu⟩ := exists_bd_subset Λ hΛ
  obtain ⟨γ₂, hγ₂⟩ := exists_bd_of_char ψ hψ u
  set γ : ValueGroupWithZero k := max 1 (max γ₁ γ₂) with hγ
  have g0 : 1 ≤ γ := le_max_left _ _
  have g1 : γ₁ ≤ γ := (le_max_left _ _).trans (le_max_right _ _)
  have g2 : γ₂ ≤ γ := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨_, isCompact_bd (γ * γ), fun μ Φ hΦ hinv χ _ h x₀ hne => ?_⟩
  obtain ⟨b, hb', κ, hκ, rfl⟩ := iwasawa_blockTriangular k (n ⊕ Fin c)
    (Sum.elim (fun _ => 2 * p) (fun i => 2 * (i.val + 1) + 1)) h
  have hb : b.val.BlockTriangular (lev p) := by
    intro r s hrs
    apply hb'
    rcases r with r | r <;> rcases s with s | s <;> simp [lev] at hrs ⊢ <;> omega
  have hκ1 : Bd 1 κ.val := bd_of_mem_KO hκ
  have hκ2 : Bd 1 (κ⁻¹).val := bd_of_mem_KO (inv_mem hκ)
  have hdiag : ∀ i : Fin c, valuation k (b.val (Sum.inr i) (Sum.inr i)) ≤ γ₂ := by
    intro i
    refine hγ₂ _ fun t ht => ?_
    set E : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k := Matrix.single (Sum.inr i) (Sum.inr i.succ) t with hE
    have hEb : Bd (valuation k (u : k)) E := by
      intro r s
      simp only [hE, Matrix.single, Matrix.of_apply]
      split_ifs
      · exact ht
      · simp
    have hd : ∀ r s, (b.val * E) r s = if s = Sum.inr i.succ then b.val r (Sum.inr i) * t else 0 := by
      intro r s
      split_ifs with hs
      · rw [hs, hE, Matrix.mul_single_apply_same]
      · rw [hE, Matrix.mul_single_apply_of_ne _ _ _ _ _ hs]
    have := char_eq_one_of_opE_ne_zero ψ ν _ x₀ hne (b.val * E) ?_ ?_
    · have hc : ch (b.val * E) = b.val (Sum.inr i) (Sum.inr i) * t := by
        simp [ch, hd]
      rwa [hc] at this
    · intro r s hf
      rw [hd]
      split_ifs with hs
      · subst hs
        rw [hb (i := r) (j := Sum.inr i), zero_mul]
        rcases r with r | r <;> simp [lev, Free] at hf ⊢ <;> omega
      · rfl
    · intro x
      have e1 : (x + b.val * E).toCols₁ = x.toCols₁ := by
        ext r s
        simp [hd]
      have e2 : ((b * κ)⁻¹).val * (x + b.val * E) * (1 : GL (n' ⊕ Fin (c + 1)) k).val =
          ((b * κ)⁻¹).val * x * (1 : GL (n' ⊕ Fin (c + 1)) k).val + (κ⁻¹).val * E := by
        rw [Units.val_one, Matrix.mul_one, Matrix.mul_one, Matrix.mul_add, ← Matrix.mul_assoc, ← Units.val_mul,
          _root_.mul_inv_rev, inv_mul_cancel_right]
      have e3 : (κ⁻¹).val * E ∈ Λ := hu _ (by simpa using hκ2.mul hEb)
      simp only [om, e1, e2, hinv _ _ e3]
  obtain ⟨e, he⟩ : ∃ e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k,
      Φ (((b * κ)⁻¹).val * (affPt p x₀ e : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hne
    simp only [opE, om, Units.val_one, Matrix.mul_one, hcon, mul_zero, zero_mul, integral_zero]
  have hbx : Bd γ₁ ((b⁻¹).val * affPt p x₀ e) := by
    have := hκ1.mul (hγ₁ _ (hΦ he))
    rwa [one_mul, ← Matrix.mul_assoc, ← Units.val_mul, _root_.mul_inv_rev, mul_inv_cancel_left] at this
  have m0 : ∀ i s, (levi (lev p) b hb).val (Sum.inr i) (Sum.inl s) = 0 := by
    intro i s
    change (if _ then _ else _) = _
    split_ifs with hl
    · apply hb'
      simp [lev] at hl ⊢
      omega
    · rfl
  have m1 : ∀ i j, valuation k ((levi (lev p) b hb).val (Sum.inr i) (Sum.inr j)) ≤ γ := by
    intro i j
    change valuation k (if _ then _ else _) ≤ _
    split_ifs with hl
    · obtain rfl : i = j := Fin.ext (by simpa [lev] using hl)
      exact (hdiag i).trans g2
    · simp
  have m2 : ∀ r j, valuation k (((levi (lev p) b hb)⁻¹).val r (Sum.inr j)) ≤ γ := by
    intro r j
    change valuation k (if _ then _ else _) ≤ _
    split_ifs with hl
    · rw [← inv_mul_affPt_apply (inv_blockTriangular hb) x₀ e r j hl]
      exact (hbx _ _).trans g1
    · simp
  obtain ⟨x, w, hxw, hw1, hw2⟩ := exists_embX_mul (levi (lev p) b hb) (γ := γ) m0 g0 m1 m2
  · refine ⟨b * (levi (lev p) b hb)⁻¹ * embX c x, mul_mem (Subgroup.mem_sup_right (Subgroup.subset_closure ?_))
      (Subgroup.mem_sup_left ⟨x, rfl⟩), w * κ, ⟨?_, ?_⟩, ?_⟩
    · intro r s hrs
      change (b.val * diagPart (lev p) (b⁻¹).val) r s = _
      rw [mul_diagPart_apply hb (inv_blockTriangular hb) hrs, b.mul_inv]
    · simpa using hw1.mul hκ1
    · rw [_root_.mul_inv_rev, Units.val_mul]
      simpa using hκ2.mul hw2
    · rw [mul_assoc, ← mul_assoc (embX c x), ← hxw]
      group

end GlobalTheory.RootEx
