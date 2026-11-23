import Mathlib
import Formalism.SatakeDualWeyl.Statement
open scoped Matrix

namespace GlobalTheory.MaxEvenLat
open Formalism.UG

variable {A : Type} [CommRing A] {n : ℕ}

theorem hform_add_left (σ : A →+* A) (J : Matrix (Fin n) (Fin n) A) (x y z : Fin n → A) :
    hform σ J (x + y) z = hform σ J x z + hform σ J y z := by
  simp only [hform, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

theorem hform_add_right (σ : A →+* A) (J : Matrix (Fin n) (Fin n) A) (x y z : Fin n → A) :
    hform σ J x (y + z) = hform σ J x y + hform σ J x z := by
  simp only [hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem hform_smul_left (σ : A →+* A) (J : Matrix (Fin n) (Fin n) A) (c : A) (x y : Fin n → A) :
    hform σ J (c • x) y = σ c * hform σ J x y := by
  simp only [hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hform_smul_right (σ : A →+* A) (J : Matrix (Fin n) (Fin n) A) (c : A) (x y : Fin n → A) :
    hform σ J x (c • y) = c * hform σ J x y := by
  simp only [hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hform_swap (σ : A →+* A) (hσ : ∀ a, σ (σ a) = a) (J : Matrix (Fin n) (Fin n) A)
    (hJ : ∀ i j, σ (J j i) = J i j) (x y : Fin n → A) :
    hform σ J y x = σ (hform σ J x y) := by
  simp only [hform, map_sum, map_mul, hσ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hJ]
  ring

theorem hform_single (σ : A →+* A) (J : Matrix (Fin n) (Fin n) A) (i : Fin n) (v : Fin n → A) :
    hform σ J (Pi.single i 1) v = (J *ᵥ v) i := by
  simp [hform, Pi.single_apply, apply_ite σ, Matrix.mulVec, dotProduct]

theorem hform_expand (σ : A →+* A) (J : Matrix (Fin n) (Fin n) A) (l l' x : Fin n → A) (c c' : A) :
    hform σ J (l + c • x) (l' + c' • x) = hform σ J l l' + c' * hform σ J l x
      + σ c * hform σ J x l' + σ c * (c' * hform σ J x x) := by
  rw [hform_add_left, hform_add_right, hform_add_right, hform_smul_left, hform_smul_left,
    hform_smul_right, hform_smul_right]
  ring

end GlobalTheory.MaxEvenLat

namespace GlobalTheory.MaxEvenLat
open Formalism.UG

def IsEven {A : Type} [CommRing A] {n : ℕ} (σ : A →+* A) (J : Matrix (Fin n) (Fin n) A)
    (R : Subring A) (L : Submodule R (Fin n → A)) : Prop :=
  (∀ u ∈ L, ∀ v ∈ L, hform σ J u v ∈ R) ∧ (∀ u ∈ L, ∃ b ∈ R, hform σ J u u = b + σ b)

theorem exists_maximal_even_lattice : ∀ (A : Type) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [T2Space A] (σ : A →+* A), (∀ a, σ (σ a) = a) →
    ∀ R : Subring A, IsCompact (R : Set A) → IsOpen (R : Set A) → (∀ a ∈ R, σ a ∈ R) → (∀ a : A, ∃ N : ℕ, N ≠ 0 ∧ (N : A) * a ∈ R) →
    (∀ N : ℕ, N ≠ 0 → IsUnit (N : A)) →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) A), (∀ i j, σ (J j i) = J i j) → IsUnit J.det →
    ∃ L : Submodule R (Fin n → A), L.FG ∧ IsOpen (L : Set (Fin n → A)) ∧ IsCompact (L : Set (Fin n → A)) ∧
      (∀ u ∈ L, ∀ v ∈ L, Formalism.UG.hform σ J u v ∈ R) ∧ (∀ u ∈ L, ∃ b ∈ R, Formalism.UG.hform σ J u u = b + σ b) ∧
      ∀ x : Fin n → A, Formalism.UG.hform σ J x x = 0 → (∀ v ∈ L, Formalism.UG.hform σ J x v ∈ R) → x ∈ L := by
  intro A _ _ _ _ σ hσ R hRc hRo hσR hden hunit n J hJ hdet

  obtain ⟨N₀, hN₀, hNJ⟩ : ∃ N₀ : ℕ, N₀ ≠ 0 ∧ ∀ i j, (N₀ : A) * J i j ∈ R := by
    choose f hf0 hf using fun p : Fin n × Fin n => hden (J p.1 p.2)
    refine ⟨∏ p, f p, Finset.prod_ne_zero_iff.mpr fun p _ => hf0 p, fun i j => ?_⟩
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ (i, j)), Nat.cast_mul, mul_assoc]
    exact R.mul_mem (natCast_mem R _) (hf (i, j))
  have hN : 2 * N₀ ≠ 0 := by omega
  obtain ⟨u, hu⟩ := hunit _ hN
  have hσN : σ ((2 * N₀ : ℕ) : A) = ((2 * N₀ : ℕ) : A) := map_natCast σ _

  have hRform : ∀ a b : Fin n → A, (∀ i, a i ∈ R) → (∀ j, b j ∈ R) → (N₀ : A) * hform σ J a b ∈ R := by
    intro a b ha hb
    rw [hform, Finset.mul_sum]
    refine R.sum_mem fun i _ => ?_
    rw [Finset.mul_sum]
    refine R.sum_mem fun j _ => ?_
    have : (N₀ : A) * (σ (a i) * J i j * b j) = σ (a i) * ((N₀ : A) * J i j) * b j := by ring
    rw [this]
    exact R.mul_mem (R.mul_mem (hσR _ (ha i)) (hNJ i j)) (hb j)
  have hfix : ∀ a : Fin n → A, σ (hform σ J a a) = hform σ J a a := fun a =>
    (hform_swap σ hσ J hJ a a).symm

  set L₀ : Submodule R (Fin n → A) :=
    Submodule.span R (Set.range fun i : Fin n => Pi.single i ((2 * N₀ : ℕ) : A)) with hL₀
  have hsmulR : ∀ (r : R) (v : Fin n → A), r • v = (r : A) • v := fun r v => rfl
  have hL0sub : ∀ v ∈ L₀, ∀ i, (↑u⁻¹ : A) * v i ∈ R := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      intro i
      dsimp only
      rw [Pi.single_apply]
      split_ifs
      · rw [← hu, Units.inv_mul]; exact R.one_mem
      · rw [mul_zero]; exact R.zero_mem
    | zero => intro i; simp
    | add x y _ _ hx hy => intro i; rw [Pi.add_apply, mul_add]; exact R.add_mem (hx i) (hy i)
    | smul r x _ hx =>
      intro i
      rw [hsmulR, Pi.smul_apply, smul_eq_mul, mul_left_comm]
      exact R.mul_mem r.2 (hx i)
  have hL0sup : ∀ v : Fin n → A, (∀ i, (↑u⁻¹ : A) * v i ∈ R) → v ∈ L₀ := by
    intro v hv
    have : v = ∑ i, (⟨(↑u⁻¹ : A) * v i, hv i⟩ : R) • Pi.single i ((2 * N₀ : ℕ) : A) := by
      funext j
      simp only [hsmulR, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, mul_ite,
        mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [← hu, mul_comm _ (u : A), Units.mul_inv_cancel_left]
    rw [this]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hdecomp : ∀ v ∈ L₀, ∃ a : Fin n → A, (∀ i, a i ∈ R) ∧ v = ((2 * N₀ : ℕ) : A) • a := by
    intro v hv
    refine ⟨fun i => (↑u⁻¹ : A) * v i, hL0sub v hv, ?_⟩
    funext i
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← hu, Units.mul_inv_cancel_left]
  have hNN : ∀ c : A, ((2 * N₀ : ℕ) : A) * (((2 * N₀ : ℕ) : A) * c) = ((4 * N₀ : ℕ) : A) * ((N₀ : A) * c) := by
    intro c; push_cast; ring
  have hL0even : IsEven σ J R L₀ := by
    constructor
    · intro v hv w hw
      obtain ⟨a, ha, rfl⟩ := hdecomp v hv
      obtain ⟨b, hb, rfl⟩ := hdecomp w hw
      rw [hform_smul_left, hform_smul_right, hσN, hNN]
      exact R.mul_mem (natCast_mem R _) (hRform a b ha hb)
    · intro v hv
      obtain ⟨a, ha, rfl⟩ := hdecomp v hv
      refine ⟨((2 * N₀ : ℕ) : A) * ((N₀ : A) * hform σ J a a),
        R.mul_mem (natCast_mem R _) (hRform a a ha ha), ?_⟩
      rw [hform_smul_left, hform_smul_right, hσN, hNN, map_mul, map_mul, map_natCast, map_natCast,
        hfix]
      push_cast; ring

  have hL0open : IsOpen (L₀ : Set (Fin n → A)) := by
    have hU : IsOpen {v : Fin n → A | ∀ i, (↑u⁻¹ : A) * v i ∈ R} := by
      have : {v : Fin n → A | ∀ i, (↑u⁻¹ : A) * v i ∈ R} =
          (fun v : Fin n → A => fun i => (↑u⁻¹ : A) * v i) ⁻¹' Set.univ.pi fun _ => (R : Set A) := by
        ext v; simp
      rw [this]
      exact (isOpen_set_pi Set.finite_univ fun _ _ => hRo).preimage
        (continuous_pi fun i => continuous_const.mul (continuous_apply i))
    refine AddSubgroup.isOpen_of_mem_nhds L₀.toAddSubgroup (g := 0) ?_
    refine Filter.mem_of_superset (hU.mem_nhds (by simp)) fun v hv => hL0sup v hv

  obtain ⟨L, hL0L, hLmax⟩ := zorn_le_nonempty₀ {L : Submodule R (Fin n → A) | IsEven σ J R L}
    (fun c hcs hc y hy => by
      refine ⟨sSup c, ?_, fun z hz => le_sSup hz⟩
      have hdir : DirectedOn (· ≤ ·) c := hc.directedOn
      have hne : c.Nonempty := ⟨y, hy⟩
      have two : ∀ v w, v ∈ sSup c → w ∈ sSup c → ∃ M ∈ c, v ∈ M ∧ w ∈ M := by
        intro v w hv hw
        obtain ⟨M₁, hM₁, hv₁⟩ := (Submodule.mem_sSup_of_directed hne hdir).mp hv
        obtain ⟨M₂, hM₂, hw₂⟩ := (Submodule.mem_sSup_of_directed hne hdir).mp hw
        rcases hc.total hM₁ hM₂ with h | h
        · exact ⟨M₂, hM₂, h hv₁, hw₂⟩
        · exact ⟨M₁, hM₁, hv₁, h hw₂⟩
      constructor
      · intro v hv w hw
        obtain ⟨M, hM, hvM, hwM⟩ := two v w hv hw
        exact (hcs hM).1 v hvM w hwM
      · intro v hv
        obtain ⟨M, hM, hvM, -⟩ := two v v hv hv
        exact (hcs hM).2 v hvM) L₀ hL0even
  have hLeven : IsEven σ J R L := hLmax.1

  have hLopen : IsOpen (L : Set (Fin n → A)) :=
    AddSubgroup.isOpen_mono (H₁ := L₀.toAddSubgroup) (H₂ := L.toAddSubgroup) hL0L hL0open
  have hLclosed : IsClosed (L : Set (Fin n → A)) :=
    AddSubgroup.isClosed_of_isOpen L.toAddSubgroup hLopen

  have hK : IsCompact ((fun w : Fin n → A => J⁻¹ *ᵥ ((↑u⁻¹ : A) • w)) '' Set.univ.pi fun _ => (R : Set A)) :=
    (isCompact_univ_pi fun _ => hRc).image
      (Continuous.matrix_mulVec continuous_const (continuous_const_smul _))
  have hLK : (L : Set (Fin n → A)) ⊆
      (fun w : Fin n → A => J⁻¹ *ᵥ ((↑u⁻¹ : A) • w)) '' Set.univ.pi fun _ => (R : Set A) := by
    intro v hv
    refine ⟨((2 * N₀ : ℕ) : A) • (J *ᵥ v), fun i _ => ?_, ?_⟩
    · have hsing : Pi.single i ((2 * N₀ : ℕ) : A) ∈ L := hL0L (Submodule.subset_span ⟨i, rfl⟩)
      have := hLeven.1 _ hsing v hv
      have heq : (Pi.single i ((2 * N₀ : ℕ) : A) : Fin n → A) = ((2 * N₀ : ℕ) : A) • Pi.single i 1 := by
        ext k; by_cases h : k = i <;> simp [Pi.single_apply, h]
      rw [heq, hform_smul_left, hσN, hform_single] at this
      simpa using this
    · simp only
      rw [smul_smul, ← hu, Units.inv_mul, one_smul, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul J hdet,
        Matrix.one_mulVec]
  have hLcomp : IsCompact (L : Set (Fin n → A)) := hK.of_isClosed_subset hLclosed hLK

  have hLfg : L.FG := by
    obtain ⟨t, ht, hcov⟩ := hLcomp.elim_nhds_subcover (fun x => {y | y - x ∈ L₀}) (fun x _ =>
      (hL0open.preimage (continuous_id.sub continuous_const)).mem_nhds (by simp [L₀.zero_mem]))
    have heq : L = Submodule.span R (t : Set (Fin n → A)) ⊔ L₀ := by
      refine le_antisymm (fun y hy => ?_) (sup_le (Submodule.span_le.mpr fun x hx => ht x hx) hL0L)
      have := hcov hy
      simp only [Set.mem_iUnion, Set.mem_setOf_eq] at this
      obtain ⟨x, hx, hyx⟩ := this
      have : y = x + (y - x) := by abel
      rw [this]
      exact Submodule.add_mem_sup (Submodule.subset_span hx) hyx
    rw [heq]
    exact (Submodule.fg_span t.finite_toSet).sup (Submodule.fg_span (Set.finite_range _))
  refine ⟨L, hLfg, hLopen, hLcomp, hLeven.1, hLeven.2, ?_⟩

  intro x hxx hxL
  have hL' : IsEven σ J R (L ⊔ Submodule.span R {x}) := by
    have hdesc : ∀ y ∈ L ⊔ Submodule.span R {x}, ∃ l ∈ L, ∃ a : R, y = l + (a : A) • x := by
      intro y hy
      obtain ⟨l, hl, z, hz, rfl⟩ := Submodule.mem_sup.mp hy
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hz
      exact ⟨l, hl, a, by rw [hsmulR]⟩
    constructor
    · intro y hy y' hy'
      obtain ⟨l, hl, a, rfl⟩ := hdesc y hy
      obtain ⟨l', hl', a', rfl⟩ := hdesc y' hy'
      rw [hform_expand, hxx, mul_zero, mul_zero, add_zero, hform_swap σ hσ J hJ x l]
      exact R.add_mem (R.add_mem (hLeven.1 l hl l' hl')
        (R.mul_mem a'.2 (hσR _ (hxL l hl)))) (R.mul_mem (hσR _ a.2) (hxL l' hl'))
    · intro y hy
      obtain ⟨l, hl, a, rfl⟩ := hdesc y hy
      obtain ⟨b, hb, hbeq⟩ := hLeven.2 l hl
      refine ⟨b + σ a * hform σ J x l, R.add_mem hb (R.mul_mem (hσR _ a.2) (hxL l hl)), ?_⟩
      rw [hform_expand, hxx, mul_zero, mul_zero, add_zero, hform_swap σ hσ J hJ x l, hbeq, map_add,
        map_mul, hσ]
      ring
  exact hLmax.2 hL' le_sup_left (Submodule.mem_sup_right (Submodule.mem_span_singleton_self x))

end GlobalTheory.MaxEvenLat
