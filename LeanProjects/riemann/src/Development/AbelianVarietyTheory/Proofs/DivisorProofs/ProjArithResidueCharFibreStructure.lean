import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory.IntFib

section Dim

variable {S : Type} [TopologicalSpace S]

theorem dim_le_of_ne_univ [IrreducibleSpace S] {C : Set S} (hC : IsClosed C) (hne : C ≠ Set.univ) {D : ℕ}
    (hS : topologicalKrullDim S ≤ ((D + 1 : ℕ) : WithBot ℕ∞)) : topologicalKrullDim C ≤ D := by
  unfold topologicalKrullDim at *
  refine iSup_le fun q => ?_
  let f := IrreducibleCloseds.map (Subtype.val : C → S) continuous_subtype_val
  have hf : StrictMono f := IrreducibleCloseds.map_strictMono_of_isInducing Topology.IsInducing.subtypeVal
  let q' := q.map f hf
  let top : IrreducibleCloseds S := ⟨Set.univ, IrreducibleSpace.isIrreducible_univ S, isClosed_univ⟩
  have hlt : q'.last < top := by
    have hsub : (q'.last : Set S) ⊆ C := by
      show closure (Subtype.val '' (q.last : Set C)) ⊆ C
      exact closure_minimal (by rintro _ ⟨t, -, rfl⟩; exact t.2) hC
    refine lt_of_le_of_ne (fun x _ => Set.mem_univ x) fun heq => hne ?_
    refine Set.eq_univ_of_univ_subset fun x _ => hsub ?_
    rw [heq]
    exact Set.mem_univ x
  have h1 := Order.LTSeries.length_le_krullDim (q'.snoc top hlt)
  have h2 : ((q.length + 1 : ℕ) : WithBot ℕ∞) ≤ ((D + 1 : ℕ) : WithBot ℕ∞) := by
    simpa [q'] using h1.trans hS
  have h3 : q.length + 1 ≤ D + 1 := by exact_mod_cast h2
  exact_mod_cast (by omega : q.length ≤ D)

theorem dim_le_of_closedPoint_notMem [T0Space S] [CompactSpace S] {T : Set S}
    (hT : ∀ s : S, IsClosed ({s} : Set S) → s ∉ T) {D : ℕ}
    (hS : topologicalKrullDim S ≤ ((D + 1 : ℕ) : WithBot ℕ∞)) : topologicalKrullDim T ≤ D := by
  unfold topologicalKrullDim at *
  refine iSup_le fun q => ?_
  let f := IrreducibleCloseds.map (Subtype.val : T → S) continuous_subtype_val
  have hf : StrictMono f := IrreducibleCloseds.map_strictMono_of_isInducing Topology.IsInducing.subtypeVal
  let q' := q.map f hf
  obtain ⟨t, ht⟩ := q.head.isIrreducible.nonempty
  have htm : (t : S) ∈ (q'.head : Set S) := subset_closure ⟨t, ht, rfl⟩
  obtain ⟨s, hs, hsc⟩ := q'.head.isClosed.exists_closed_singleton ⟨_, htm⟩
  let bot : IrreducibleCloseds S := ⟨{s}, isIrreducible_singleton, hsc⟩
  have hlt : bot < q'.head := by
    refine lt_of_le_of_ne (fun x hx => (Set.mem_singleton_iff.1 hx) ▸ hs) fun heq => ?_
    have : (t : S) ∈ (bot : Set S) := by rw [heq]; exact htm
    have hts : (t : S) = s := this
    exact hT s hsc (hts ▸ t.2)
  have h1 := Order.LTSeries.length_le_krullDim (q'.cons bot hlt)
  have h2 : ((q.length + 1 : ℕ) : WithBot ℕ∞) ≤ ((D + 1 : ℕ) : WithBot ℕ∞) := by
    simpa [q'] using h1.trans hS
  have h3 : q.length + 1 ≤ D + 1 := by exact_mod_cast h2
  exact_mod_cast (by omega : q.length ≤ D)

end Dim

variable {X : Scheme.{0}}

theorem ringChar_eq_zero_or_prime (x : X) :
    ringChar (X.residueField x) = 0 ∨ (ringChar (X.residueField x)).Prime :=
  (CharP.char_is_prime_or_zero (X.residueField x) _).symm

theorem natCast_eq_zero_iff (ℓ : ℕ) (x : X) :
    (ℓ : X.residueField x) = 0 ↔ x ∉ X.basicOpen ((ℓ : ℕ) : Γ(X, ⊤)) := by
  rw [← Scheme.evaluation_eq_zero_iff_notMem_basicOpen X x (show x ∈ (⊤ : X.Opens) from trivial)]
  simp

theorem notMem_basicOpen_of_mem_fib {ℓ : ℕ} {x : X} (hx : x ∈ fib X ℓ) :
    x ∉ X.basicOpen ((ℓ : ℕ) : Γ(X, ⊤)) := by
  rw [← natCast_eq_zero_iff, ringChar.spec]
  exact (show ringChar (X.residueField x) = ℓ from hx) ▸ dvd_refl _

theorem mem_fib_iff_of_prime {ℓ : ℕ} (hℓ : ℓ.Prime) (x : X) :
    x ∈ fib X ℓ ↔ x ∉ X.basicOpen ((ℓ : ℕ) : Γ(X, ⊤)) := by
  refine ⟨notMem_basicOpen_of_mem_fib, fun h => ?_⟩
  rw [← natCast_eq_zero_iff, ringChar.spec] at h
  rcases hℓ.eq_one_or_self_of_dvd _ h with h1 | h1
  · have h2 : ((1 : ℕ) : X.residueField x) = 0 := (ringChar.spec _ 1).2 (by rw [h1])
    simp at h2
  · exact h1

theorem isClosed_fib {ℓ : ℕ} (hℓ : ℓ ≠ 0) : IsClosed (fib X ℓ) := by
  by_cases hp : ℓ.Prime
  · have e : fib X ℓ = ((X.basicOpen ((ℓ : ℕ) : Γ(X, ⊤)) : Set X))ᶜ :=
      Set.ext fun x => mem_fib_iff_of_prime hp x
    rw [e]
    exact (X.basicOpen _).isOpen.isClosed_compl
  · have e : fib X ℓ = ∅ := Set.eq_empty_iff_forall_notMem.2 fun x hx => by
      have hx' : ringChar (X.residueField x) = ℓ := hx
      rcases ringChar_eq_zero_or_prime x with h | h
      · exact hℓ (hx'.symm.trans h)
      · exact hp (hx' ▸ h)
    rw [e]
    exact isClosed_empty

theorem mem_fib_zero_of_specializes {x y : X} (h : x ⤳ y) (hy : y ∈ fib X 0) : x ∈ fib X 0 := by
  rcases ringChar_eq_zero_or_prime x with h0 | hp
  · exact h0
  · have hx : x ∈ fib X (ringChar (X.residueField x)) := rfl
    have hy' : ringChar (X.residueField y) = ringChar (X.residueField x) :=
      h.mem_closed (isClosed_fib hp.ne_zero) hx
    exact absurd (hy'.symm.trans hy) hp.ne_zero

variable {k : Type} [CommRing k] {p : X ⟶ Sp k} {D : ℕ}

theorem fib_ne_univ [IsIntegral X] (hX : IsArithVar p D) {ℓ : ℕ} (hℓ : ℓ ≠ 0) : fib X ℓ ≠ Set.univ := by
  intro h
  have hb : X.basicOpen ((ℓ : ℕ) : Γ(X, ⊤)) = ⊥ :=
    eq_bot_iff.2 fun x hx => (notMem_basicOpen_of_mem_fib (h.symm ▸ Set.mem_univ x : x ∈ fib X ℓ) hx).elim
  have h0 := (AlgebraicGeometry.basicOpen_eq_bot_iff _).1 hb
  have := hX.charZero
  exact hℓ (Nat.cast_eq_zero.1 h0)

theorem closedPoint_notMem_fib_zero (hX : IsArithVar p D) (x : X) (hx : IsClosed ({x} : Set X)) :
    x ∉ fib X 0 := by
  intro h0
  have := hX.finite_residueField hx
  exact CharP.char_ne_zero_of_finite (X.residueField x) (ringChar (X.residueField x)) h0

theorem fib_structure : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → (∀ x : X, x ∈ fib X 0 ∨ ∃ ℓ : ℕ, ℓ.Prime ∧ x ∈ fib X ℓ) ∧
      (∀ ℓ : ℕ, ℓ ≠ 0 → IsClosed (fib X ℓ)) ∧ (∀ x y : X, x ⤳ y → y ∈ fib X 0 → x ∈ fib X 0) ∧
      (∀ ℓ : ℕ, topologicalKrullDim (fib X ℓ) ≤ D) ∧
      ∀ W : Set X, IsClosed W → ∃ S : Finset ℕ, (∀ ℓ ∈ S, ℓ.Prime) ∧
        W ⊆ closure (W ∩ fib X 0) ∪ ⋃ ℓ ∈ S, fib X ℓ := by
  intro k _ X _ p D hX
  have := hX.isNoetherian
  refine ⟨fun x => ?_, fun ℓ hℓ => isClosed_fib hℓ, fun x y h hy => mem_fib_zero_of_specializes h hy,
    fun ℓ => ?_, fun W hW => ?_⟩
  · rcases ringChar_eq_zero_or_prime x with h | h
    · exact .inl h
    · exact .inr ⟨_, h, rfl⟩
  · rcases eq_or_ne ℓ 0 with rfl | hℓ
    · exact dim_le_of_closedPoint_notMem (fun s hs => closedPoint_notMem_fib_zero hX s hs) hX.dim_eq.le
    · exact dim_le_of_ne_univ (isClosed_fib hℓ) (fib_ne_univ hX hℓ) hX.dim_eq.le
  · classical
    obtain ⟨T, hTf, hTc, hTi, rfl⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible hW
    let ch : Set X → ℕ := fun t =>
      if h : IsIrreducible t then ringChar (X.residueField (IsIrreducible.genericPoint h)) else 0
    refine ⟨(hTf.toFinset.image ch).filter Nat.Prime, fun ℓ hℓ => (Finset.mem_filter.1 hℓ).2, ?_⟩
    rintro x ⟨t, ht, hxt⟩
    have hct : ch t = ringChar (X.residueField (IsIrreducible.genericPoint (hTi t ht))) := dif_pos (hTi t ht)
    have hg := IsIrreducible.isGenericPoint_genericPoint (hTi t ht) (hTc t ht)
    have hsp := hg.specializes hxt
    rcases ringChar_eq_zero_or_prime (IsIrreducible.genericPoint (hTi t ht)) with h0 | hp
    · left
      exact hsp.mem_closed isClosed_closure (subset_closure ⟨⟨t, ht, hg.mem⟩, h0⟩)
    · right
      refine Set.mem_iUnion₂.2 ⟨ch t, Finset.mem_filter.2
        ⟨Finset.mem_image.2 ⟨t, hTf.mem_toFinset.2 ht, rfl⟩, hct ▸ hp⟩, ?_⟩
      exact hsp.mem_closed (isClosed_fib (hct ▸ hp.ne_zero)) hct.symm

end GlobalTheory.IntFib
