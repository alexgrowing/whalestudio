import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SplitDoublingNBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankMirabolicWhittakerEigenspaceStatement

noncomputable section

namespace GlobalTheory.FinGL.PosOne

open GlobalTheory.FinGL Formalism.L2.DIV Module Matrix

theorem mem_eig {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ G V) (S : Set G) (χ : G → ℂ)
    (v : V) : v ∈ eig τ S χ ↔ ∀ g ∈ S, τ g v = χ g • v := by
  simp [eig, Submodule.mem_iInf, sub_eq_zero]

theorem exists_descent {G P V : Type} [Group G] [Group P] [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ G V)
    (Q : Subgroup G) (ρ : Q →* P) (hρ : Function.Surjective ρ) (χ : Q →* ℂˣ) :
    ∃ (M : Submodule ℂ V) (π : Representation ℂ P M), ∀ (S : Set P) (c : P → ℂ) (T : Set G) (d : G → ℂ),
      (1 : P) ∈ S → c 1 = 1 → (∀ g, g ∈ T ↔ ∃ h : g ∈ Q, ρ ⟨g, h⟩ ∈ S) →
      (∀ g : Q, ρ g ∈ S → d g = χ g * c (ρ g)) → finrank ℂ (eig π S c) = finrank ℂ (eig τ T d) := by
  let σ : Representation ℂ Q V :=
    { toFun := fun g => (((χ g)⁻¹ : ℂˣ) : ℂ) • τ g
      map_one' := by simp
      map_mul' := fun x y => by
        simp only [map_mul, Subgroup.coe_mul, mul_inv, Units.val_mul, smul_mul_smul_comm] }
  have hσ : ∀ (g : Q) (v : V), σ g v = (((χ g)⁻¹ : ℂˣ) : ℂ) • τ g v := fun g v => rfl
  let M : Submodule ℂ V := eig σ (ρ.ker : Set Q) fun _ => 1
  have hM : ∀ v, v ∈ M ↔ ∀ g : Q, ρ g = 1 → σ g v = v := fun v => by
    simp [M, mem_eig]
  have hst : ∀ g : Q, ∀ v ∈ M, σ g v ∈ M := by
    intro g v hv
    rw [hM] at hv ⊢
    intro n hn
    have h1 := hv (g⁻¹ * n * g) (by simp [hn])
    have h2 : n * g = g * (g⁻¹ * n * g) := by group
    calc σ n (σ g v) = σ (n * g) v := by rw [map_mul]; rfl
      _ = σ g (σ (g⁻¹ * n * g) v) := by rw [h2, map_mul]; rfl
      _ = σ g v := by rw [h1]
  let σM : Q →* Module.End ℂ M :=
    { toFun := fun g => (σ g).restrict (hst g)
      map_one' := by ext v; simp
      map_mul' := fun x y => by ext v; simp }
  have hσM : ∀ (g : Q) (v : M), (σM g v : V) = σ g v := fun g v => rfl
  have hker : ∀ x y : Q, ρ x = ρ y → σM x = σM y := by
    intro x y h
    ext v
    have h1 := (hM v.1).1 v.2 (y⁻¹ * x) (by simp [h])
    have h2 : x = y * (y⁻¹ * x) := by group
    rw [hσM, hσM]
    conv_lhs => rw [h2, map_mul]
    show σ y (σ (y⁻¹ * x) v) = _
    rw [h1]
  obtain ⟨s, hs⟩ := hρ.hasRightInverse
  let π : Representation ℂ P M :=
    { toFun := fun p => σM (s p)
      map_one' := by rw [hker (s 1) 1 (by rw [hs 1, map_one]), map_one]
      map_mul' := fun x y => by
        rw [← map_mul]; exact hker _ _ (by rw [map_mul, hs x, hs y, hs (x * y)]) }
  have hπ : ∀ (g : Q) (v : M), (π (ρ g) v : V) = σ g v := fun g v => by
    show (σM (s (ρ g)) v : V) = _
    rw [hker (s (ρ g)) g (hs _), hσM]
  refine ⟨M, π, fun S c T d h1 hc hT hd => ?_⟩
  have key : ∀ (g : Q) (v : V), ρ g ∈ S → (σ g v = c (ρ g) • v ↔ τ g v = d g • v) := by
    intro g v hg
    rw [hσ, hd g hg, mul_smul]
    constructor
    · intro h; rw [← h, smul_smul]; simp
    · intro h; rw [h, smul_smul]; simp
  have e : (eig π S c).map M.subtype = eig τ T d := by
    ext v
    simp only [Submodule.mem_map, mem_eig]
    constructor
    · rintro ⟨w, hw, rfl⟩ g hg
      obtain ⟨h, hh⟩ := (hT g).1 hg
      refine (key ⟨g, h⟩ _ hh).1 ?_
      have := congrArg Subtype.val (hw _ hh)
      rw [hπ] at this
      exact this
    · intro hv
      have hv' : ∀ g : Q, ρ g ∈ S → σ g v = c (ρ g) • v := fun g hg =>
        (key g v hg).2 (hv g ((hT g).2 ⟨g.2, hg⟩))
      refine ⟨⟨v, (hM v).2 fun g hg => ?_⟩, fun p hp => ?_, rfl⟩
      · rw [hv' g (by rw [hg]; exact h1), hg, hc, one_smul]
      · obtain ⟨g, rfl⟩ := hρ p
        apply Subtype.ext
        rw [hπ]
        exact hv' g hp
  rw [← e]
  exact (Submodule.finrank_map_subtype_eq M _).symm

variable {F : Type} [Field F] {r : ℕ}

def tailOnesBlockSizes (k : ℕ) (a : Fin r) : ℕ := if a.val < k then 0 else a.val + 1

def tailUnip (F : Type) [Field F] (r k : ℕ) : Subgroup (GL (Fin r) F) where
  carrier := {g | g ∈ blockTri (κ := F) (tailOnesBlockSizes k) ∧ ∀ i : Fin r, k ≤ i.val → (g : Matrix (Fin r) (Fin r) F) i i = 1}
  one_mem' := ⟨Subgroup.one_mem _, fun i _ => by simp⟩
  mul_mem' := by
    rintro x y ⟨hx, hx1⟩ ⟨hy, hy1⟩
    refine ⟨Subgroup.mul_mem _ hx hy, fun i hi => ?_⟩
    rw [Units.val_mul, mul_apply, Finset.sum_eq_single i, hx1 i hi, hy1 i hi, one_mul]
    · intro l _ hl
      rcases lt_or_gt_of_ne hl with h | h
      · have h' : l.val < i.val := h
        rw [hx (show tailOnesBlockSizes k l < tailOnesBlockSizes k i by unfold tailOnesBlockSizes; split_ifs <;> omega), zero_mul]
      · have h' : i.val < l.val := h
        rw [hy (show tailOnesBlockSizes k i < tailOnesBlockSizes k l by unfold tailOnesBlockSizes; split_ifs <;> omega), mul_zero]
    · intro h; exact absurd (Finset.mem_univ i) h
  inv_mem' := by
    rintro x ⟨hx, hx1⟩
    have hi := Subgroup.inv_mem _ hx
    refine ⟨hi, fun i hk => ?_⟩
    have h1 : ((x * x⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i i = 1 := by simp
    rw [Units.val_mul, mul_apply, Finset.sum_eq_single i, hx1 i hk, one_mul] at h1
    · exact h1
    · intro l _ hl
      rcases lt_or_gt_of_ne hl with h | h
      · have h' : l.val < i.val := h
        rw [hx (show tailOnesBlockSizes k l < tailOnesBlockSizes k i by unfold tailOnesBlockSizes; split_ifs <;> omega), zero_mul]
      · have h' : i.val < l.val := h
        rw [hi (show tailOnesBlockSizes k i < tailOnesBlockSizes k l by unfold tailOnesBlockSizes; split_ifs <;> omega), mul_zero]
    · intro h; exact absurd (Finset.mem_univ i) h

theorem mem_tailUnip {k : ℕ} {g : GL (Fin r) F} : g ∈ tailUnip F r k ↔
    ∀ i j : Fin r, k ≤ i.val → j.val ≤ i.val →
      (g : Matrix (Fin r) (Fin r) F) i j = (1 : Matrix (Fin r) (Fin r) F) i j := by
  constructor
  · rintro ⟨h1, h2⟩ i j hi hj
    rcases hj.lt_or_eq with h | h
    · rw [h1 (show tailOnesBlockSizes k j < tailOnesBlockSizes k i by unfold tailOnesBlockSizes; split_ifs <;> omega),
        one_apply_ne (fun e => by rw [e] at h; omega)]
    · obtain rfl : j = i := Fin.ext h
      rw [h2 j hi, one_apply_eq]
  · intro h
    refine ⟨fun i j hij => ?_, fun i hi => by rw [h i i hi le_rfl, one_apply_eq]⟩
    have : k ≤ i.val ∧ j.val < i.val := by
      unfold tailOnesBlockSizes at hij; split_ifs at hij <;> omega
    rw [h i j this.1 this.2.le, one_apply_ne (fun e => by rw [e] at this; omega)]

theorem mem_unip {g : GL (Fin r) F} : g ∈ unip F r ↔
    ∀ i j : Fin r, j.val ≤ i.val → (g : Matrix (Fin r) (Fin r) F) i j = (1 : Matrix (Fin r) (Fin r) F) i j := by
  constructor
  · intro hg i j hj
    rcases hj.lt_or_eq with h | h
    · rw [unip_lower hg (show j < i from h), one_apply_ne (fun e => by rw [e] at h; omega)]
    · obtain rfl : j = i := Fin.ext h
      rw [unip_diag hg, one_apply_eq]
  · intro h
    refine ⟨fun i j hij => ?_, fun i => by rw [h i i le_rfl, one_apply_eq]⟩
    have hij' : j.val < i.val := hij
    rw [h i j hij'.le, one_apply_ne (fun e => by rw [e] at hij'; omega)]

theorem mem_tailUnip_last {k : ℕ} (g : GL (Fin (k + 1)) F) : g ∈ tailUnip F (k + 1) k ↔
    ∀ j, (g : Matrix (Fin (k + 1)) (Fin (k + 1)) F) (Fin.last k) j =
      (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) F) (Fin.last k) j := by
  rw [mem_tailUnip]
  constructor
  · intro h j
    exact h _ j (by simp) (by have := j.2; simp only [Fin.val_last]; omega)
  · intro h i j hi _
    obtain rfl : i = Fin.last k := Fin.ext (by have := i.2; simp only [Fin.val_last]; omega)
    exact h j

theorem tailUnip_le (k : ℕ) : tailUnip F r k ≤ blockTri (blk2 (k + 1)) := by
  intro g hg i j hij
  have : k + 1 ≤ i.val ∧ j.val < k + 1 := by
    unfold blk2 at hij; split_ifs at hij <;> omega
  rw [mem_tailUnip.1 hg i j (by omega) (by omega), one_apply_ne (fun e => by rw [e] at this; omega)]

theorem one_castLE {n : ℕ} (h : n ≤ r) (i j : Fin n) :
    (1 : Matrix (Fin r) (Fin r) F) (Fin.castLE h i) (Fin.castLE h j) = (1 : Matrix (Fin n) (Fin n) F) i j := by
  simp [one_apply]

def corner {k : ℕ} (h : k + 1 ≤ r) : tailUnip F r k →* tailUnip F (k + 1) k :=
  ((blkR h).comp (Subgroup.inclusion (tailUnip_le k))).codRestrict _ fun g =>
    mem_tailUnip.2 fun i j hi hj => by
      rw [← one_castLE h]
      exact mem_tailUnip.1 g.2 (Fin.castLE h i) (Fin.castLE h j) hi hj

theorem corner_apply {k : ℕ} (h : k + 1 ≤ r) (g : tailUnip F r k) (i j : Fin (k + 1)) :
    ((corner h g : GL (Fin (k + 1)) F) : Matrix (Fin (k + 1)) (Fin (k + 1)) F) i j =
      ((g : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) (Fin.castLE h i) (Fin.castLE h j) := rfl

theorem corner_surj {k : ℕ} (h : k + 1 ≤ r) : Function.Surjective (corner (F := F) h) := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le h
  intro p
  let e : Fin (k + 1) ⊕ Fin c ≃ Fin (k + 1 + c) := finSumFinEquiv
  let f : GL (Fin (k + 1)) F → Matrix (Fin (k + 1 + c)) (Fin (k + 1 + c)) F := fun x =>
    (fromBlocks (x : Matrix (Fin (k + 1)) (Fin (k + 1)) F) 0 0 (1 : Matrix (Fin c) (Fin c) F)).submatrix e.symm e.symm
  have hf : ∀ x y, x * y = 1 → f x * f y = 1 := fun x y hxy => by
    simp only [f, submatrix_mul_equiv, fromBlocks_multiply, ← Units.val_mul, hxy]
    simp
  let g : GL (Fin (k + 1 + c)) F := ⟨f p, f p⁻¹, hf _ _ (by simp), hf _ _ (by simp)⟩
  have hg : ∀ a b, (g : Matrix _ _ F) (e a) (e b) =
      fromBlocks ((p : GL (Fin (k + 1)) F) : Matrix (Fin (k + 1)) (Fin (k + 1)) F) 0 0 (1 : Matrix (Fin c) (Fin c) F) a b :=
    fun a b => by simp [g, f]
  have h1 : ∀ a b, (1 : Matrix _ _ F) (e a) (e b) =
      fromBlocks (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) F) 0 0 (1 : Matrix (Fin c) (Fin c) F) a b :=
    fun a b => by rw [fromBlocks_one]; simp [one_apply]
  refine ⟨⟨g, mem_tailUnip.2 fun i j hi hj => ?_⟩, ?_⟩
  · obtain ⟨a, rfl⟩ := e.surjective i
    obtain ⟨b, rfl⟩ := e.surjective j
    rw [hg, h1]
    rcases a with a | a <;> rcases b with b | b
    · exact mem_tailUnip.1 p.2 a b hi hj
    all_goals rfl
  · apply Subtype.ext
    apply Units.ext
    ext i j
    rw [corner_apply]
    exact hg (Sum.inl i) (Sum.inl j)

def tailEdge (k : ℕ) (a b : Fin r) : Prop := b.val = a.val + 1 ∧ k ≤ a.val

instance (k : ℕ) : DecidableRel (tailEdge (r := r) k) := fun a b =>
  inferInstanceAs (Decidable (b.val = a.val + 1 ∧ k ≤ a.val))

def tailHom (F : Type) [Field F] (r k : ℕ) : tailUnip F r k →* Multiplicative F :=
  edgeHom (tailEdge k) (tailUnip F r k) (fun i j h e => by unfold tailEdge at h; rw [e] at h; omega)
    (fun x hx y hy i j h => by
      obtain ⟨h1, h2⟩ := h
      have hij : i ≠ j := fun e => by rw [e] at h1; omega
      rw [Units.val_mul, mul_apply, Finset.sum_eq_add i j hij, hx.2 i h2, hy.2 j (by omega), one_mul, mul_one, add_comm]
      · rintro l _ ⟨hli, hlj⟩
        have a1 : l.val ≠ i.val := fun e => hli (Fin.ext e)
        have a2 : l.val ≠ j.val := fun e => hlj (Fin.ext e)
        rcases lt_or_gt_of_ne a1 with h | h
        · rw [mem_tailUnip.1 hx i l h2 h.le, one_apply_ne (Ne.symm hli), zero_mul]
        · rw [mem_tailUnip.1 hy l j (by omega) (by omega), one_apply_ne hlj, mul_zero]
      · intro h; exact absurd (Finset.mem_univ i) h
      · intro h; exact absurd (Finset.mem_univ j) h)

theorem edgeSum_split {k : ℕ} (h : k + 1 ≤ r) (g : tailUnip F r k) (E : Fin r → Fin r → Prop) [DecidableRel E]
    (E' : Fin (k + 1) → Fin (k + 1) → Prop) [DecidableRel E']
    (h1 : ∀ a b, E' a b ↔ E (Fin.castLE h a) (Fin.castLE h b))
    (h2 : ∀ a b, E a b → b.val = a.val + 1) (h3 : ∀ a b, tailEdge k a b → E a b) :
    edgeSum E (g : GL (Fin r) F) =
      edgeSum (tailEdge k) (g : GL (Fin r) F) + edgeSum E' (corner h g : GL (Fin (k + 1)) F) := by
  have e : edgeSum E' (corner h g : GL (Fin (k + 1)) F) =
      edgeSum (fun a b => E a b ∧ a.val < k) (g : GL (Fin r) F) := by
    unfold edgeSum
    refine Fintype.sum_of_injective (Fin.castLE h) (Fin.castLE_injective h) _ _ (fun a ha => ?_) (fun a => ?_)
    · refine Finset.sum_eq_zero fun b _ => if_neg fun hb => ha ⟨⟨a.val, by omega⟩, rfl⟩
    · refine Fintype.sum_of_injective (Fin.castLE h) (Fin.castLE_injective h) _ _ (fun b hb => ?_) (fun b => ?_)
      · refine if_neg fun hE => hb ⟨⟨b.val, by have := h2 _ _ hE.1; have := hE.2; omega⟩, rfl⟩
      · rw [corner_apply]
        refine if_congr ⟨fun hE => ⟨(h1 _ _).1 hE, ?_⟩, fun hE => (h1 _ _).2 hE.1⟩ rfl rfl
        have := h2 _ _ ((h1 _ _).1 hE)
        have hb := b.2
        simp only [Fin.val_castLE] at this ⊢
        omega
  rw [e]
  unfold edgeSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  by_cases hE : E a b
  · by_cases ha : a.val < k
    · rw [if_pos hE, if_neg (fun t : tailEdge k a b => absurd t.2 (by omega)), if_pos ⟨hE, ha⟩, zero_add]
    · rw [if_pos hE, if_pos (show tailEdge k a b from ⟨h2 _ _ hE, by omega⟩), if_neg (fun t => ha t.2), add_zero]
  · rw [if_neg hE, if_neg (fun t => hE (h3 _ _ t)), if_neg (fun t => hE t.1), add_zero]

theorem mem_unip_iff {k : ℕ} (h : k + 1 ≤ r) (g : GL (Fin r) F) : g ∈ unip F r ↔
    ∃ hg : g ∈ tailUnip F r k, (corner h ⟨g, hg⟩ : GL (Fin (k + 1)) F) ∈ unip F (k + 1) := by
  constructor
  · intro hg
    refine ⟨mem_tailUnip.2 fun i j _ hj => mem_unip.1 hg i j hj, mem_unip.2 fun i j hj => ?_⟩
    rw [corner_apply, ← one_castLE h]
    exact mem_unip.1 hg _ _ hj
  · rintro ⟨hg, hc⟩
    refine mem_unip.2 fun i j hj => ?_
    by_cases hi : k ≤ i.val
    · exact mem_tailUnip.1 hg i j hi hj
    · have := mem_unip.1 hc ⟨i.val, by omega⟩ ⟨j.val, by omega⟩ hj
      rw [corner_apply, ← one_castLE h] at this
      exact this

theorem mem_unipSym_iff {k : ℕ} (h : k + 1 ≤ r) (g : GL (Fin r) F) : g ∈ unipSym F r 0 k ↔
    ∃ hg : g ∈ tailUnip F r k, (corner h ⟨g, hg⟩ : GL (Fin (k + 1)) F) ∈ unipSym F (k + 1) 0 k := by
  constructor
  · rintro ⟨hg, h0⟩
    obtain ⟨hg', hc⟩ := (mem_unip_iff h g).1 hg
    exact ⟨hg', hc, fun i j a b c => h0 (Fin.castLE h i) (Fin.castLE h j) a b c⟩
  · rintro ⟨hg, hc, h0⟩
    exact ⟨(mem_unip_iff h g).2 ⟨hg, hc⟩, fun i j a b c =>
      h0 ⟨i.val, by omega⟩ ⟨j.val, by omega⟩ a b c⟩

theorem edgeSum_one {n : ℕ} (E : Fin n → Fin n → Prop) [DecidableRel E] (h : ∀ a b, E a b → b.val = a.val + 1) :
    edgeSum E (1 : GL (Fin n) F) = 0 := by
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  split_ifs with hE
  · have := h _ _ hE
    rw [Units.val_one, one_apply_ne (fun e => by rw [e] at this; omega)]
  · rfl

theorem nPos_zero_eq_sum : ∀ (F : Type) [Field F] [Fintype F] (ψ : AddChar F ℂ), ψ ≠ 1 → ∀ (r : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (τ : Representation ℂ (GL (Fin r) F) V) (k : ℕ), k + 1 ≤ r → nPos ψ τ 0 k = ∑ j ∈ Finset.range (k + 1), gam (Fintype.card F) (k - j) * whCut ψ τ j := by
  intro F _ _ ψ hψ r V _ _ _ τ k h
  obtain ⟨M, π, hπ⟩ := exists_descent τ (tailUnip F r k) (corner h) (corner_surj h) (addCharHom ψ (tailHom F r k))
  have hχ : ∀ g : tailUnip F r k, ((addCharHom ψ (tailHom F r k) g : ℂˣ) : ℂ) =
      ψ (edgeSum (tailEdge k) (g : GL (Fin r) F)) := fun g => rfl
  have main := GlobalTheory.T.finrank_mirabolic_whittaker_eigenspace F ψ hψ k (tailUnip F (k + 1) k) mem_tailUnip_last M π
  have hs : ∀ {n : ℕ} (a b : Fin n), symEdge 0 k a b → b.val = a.val + 1 := fun a b t => by
    unfold symEdge at t; omega
  rw [hπ _ _ (unipSym F r 0 k : Set (GL (Fin r) F)) (fun g => ψ (edgeSum (symEdge 0 k) g))
    (Subgroup.one_mem (unipSym F (k + 1) 0 k))
    (by simp only [OneMemClass.coe_one]; rw [edgeSum_one _ hs, AddChar.map_zero_eq_one])
    (mem_unipSym_iff h) (fun g _ => by
      rw [hχ, ← AddChar.map_add_eq_mul, ← edgeSum_split h g (symEdge 0 k) (symEdge 0 k) (fun _ _ => Iff.rfl) hs
        (fun a b t => by unfold tailEdge at t; unfold symEdge; omega)])] at main
  unfold nPos
  rw [main]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' := Finset.mem_range.1 hj
  rw [hπ _ _ (unip F r : Set (GL (Fin r) F)) (fun g => ψ (edgeSum (cutEdge j) g))
    (Subgroup.one_mem (unip F (k + 1)))
    (by simp only [OneMemClass.coe_one]; rw [edgeSum_one _ (fun _ _ t => t.1), AddChar.map_zero_eq_one])
    (mem_unip_iff h) (fun g _ => by
      rw [hχ, ← AddChar.map_add_eq_mul, ← edgeSum_split h g (cutEdge j) (cutEdge j) (fun _ _ => Iff.rfl) (fun _ _ t => t.1)
        (fun a b t => by unfold tailEdge at t; unfold cutEdge; omega)])]
  rfl

end GlobalTheory.FinGL.PosOne
