import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SplitDoublingNBlock

noncomputable section

namespace GlobalTheory.FinGL.RootExchange

open Formalism.L2.DIV Module

section Abstract

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

theorem mem_eig_iff (τ : Representation ℂ G V) (S : Set G) (χ : G → ℂ) (v : V) :
    v ∈ eig τ S χ ↔ ∀ g ∈ S, τ g v = χ g • v := by
  simp [eig, Submodule.mem_iInf, sub_eq_zero]

def proj (τ : Representation ℂ G V) (A : Subgroup G) [Fintype A] (χ : G → ℂ) : V →ₗ[ℂ] V :=
  ∑ a : A, χ (a : G)⁻¹ • τ a

theorem proj_apply (τ : Representation ℂ G V) (A : Subgroup G) [Fintype A] (χ : G → ℂ) (v : V) :
    proj τ A χ v = ∑ a : A, χ (a : G)⁻¹ • τ a v := by
  simp [proj, LinearMap.sum_apply]

theorem proj_mem (τ : Representation ℂ G V) (A : Subgroup G) [Fintype A] (χ : G → ℂ)
    (hχ : ∀ x ∈ A, ∀ y ∈ A, χ (x * y) = χ x * χ y) (v : V) : proj τ A χ v ∈ eig τ A χ := by
  rw [mem_eig_iff]
  intro g hg
  rw [proj_apply, map_sum, Finset.smul_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft (⟨g, hg⟩ : A)) _ _ fun a => ?_
  have h : χ (a : G)⁻¹ = χ g * χ (g * a)⁻¹ := by
    rw [mul_comm, ← hχ _ (A.inv_mem (A.mul_mem hg a.2)) _ hg]
    congr 1
    group
  simp only [Equiv.coe_mulLeft, Subgroup.coe_mul, map_smul, map_mul, Module.End.mul_apply, smul_smul, h]

theorem proj_act (τ : Representation ℂ G V) (A : Subgroup G) [Fintype A] (χ : G → ℂ)
    (hχ : ∀ x ∈ A, ∀ y ∈ A, χ (x * y) = χ x * χ y) {g : G} (hg : g ∈ A) (v : V) :
    proj τ A χ (τ g v) = χ g • proj τ A χ v := by
  rw [proj_apply, proj_apply, Finset.smul_sum]
  refine Fintype.sum_equiv (Equiv.mulRight (⟨g, hg⟩ : A)) _ _ fun a => ?_
  have h : χ (a : G)⁻¹ = χ g * χ (a * g)⁻¹ := by
    rw [← hχ _ hg _ (A.inv_mem (A.mul_mem a.2 hg))]
    congr 1
    group
  simp only [Equiv.coe_mulRight, Subgroup.coe_mul, map_mul, Module.End.mul_apply, smul_smul, h]

theorem proj_of_mem (τ : Representation ℂ G V) (A : Subgroup G) [Fintype A] (χ : G → ℂ)
    (hχ : ∀ x ∈ A, ∀ y ∈ A, χ (x * y) = χ x * χ y) (h1 : χ 1 = 1) {v : V} (hv : v ∈ eig τ A χ) :
    proj τ A χ v = (Fintype.card A : ℂ) • v := by
  rw [mem_eig_iff] at hv
  rw [proj_apply, Finset.sum_congr rfl (g := fun _ => v)]
  · rw [Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]
  · intro a _
    rw [hv a a.2, smul_smul, ← hχ _ (A.inv_mem a.2) _ a.2, inv_mul_cancel, h1, one_smul]

theorem finrank_eig_le [FiniteDimensional ℂ V] (τ : Representation ℂ G V) (A B : Subgroup G) [Finite A] [Finite B]
    (χ : G → ℂ) (hA : ∀ x ∈ A, ∀ y ∈ A, χ (x * y) = χ x * χ y) (hB : ∀ x ∈ B, ∀ y ∈ B, χ (x * y) = χ x * χ y)
    (h1 : χ 1 = 1) (hx : ∀ b ∈ B, b ∉ A → ∃ a ∈ A, b⁻¹ * a * b ∈ A ∧ χ (b⁻¹ * a * b) ≠ χ a) :
    finrank ℂ (eig τ A χ) ≤ finrank ℂ (eig τ B χ) := by
  classical
  haveI := Fintype.ofFinite A
  haveI := Fintype.ofFinite B
  let f : eig τ A χ →ₗ[ℂ] eig τ B χ :=
    ((proj τ B χ).comp (eig τ A χ).subtype).codRestrict _ fun v => proj_mem τ B χ hB v
  refine LinearMap.finrank_le_finrank_of_injective (f := f) ?_
  rw [injective_iff_map_eq_zero]
  rintro ⟨v, hv⟩ h0
  have h0' : proj τ B χ v = 0 := congrArg Subtype.val h0
  have hv' := (mem_eig_iff τ A χ v).1 hv
  have key : ∀ b : B, proj τ A χ (χ (b : G)⁻¹ • τ b v) =
      (if (b : G) ∈ A then (Fintype.card A : ℂ) else 0) • v := by
    intro b
    rw [map_smul]
    split_ifs with hb
    · rw [proj_act τ A χ hA hb, smul_smul, ← hA _ (A.inv_mem hb) _ hb, inv_mul_cancel, h1, one_smul,
        proj_of_mem τ A χ hA h1 hv]
    · obtain ⟨a, ha, ha', hne⟩ := hx b b.2 hb
      have e1 := proj_act τ A χ hA ha (τ b v)
      have e2 : τ a (τ b v) = χ ((b : G)⁻¹ * a * b) • τ b v := by
        rw [← map_smul, ← hv' _ ha', ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
        congr 2
        group
      rw [e2, map_smul, ← sub_eq_zero, ← sub_smul, smul_eq_zero, sub_eq_zero] at e1
      rw [e1.resolve_left hne, smul_zero, zero_smul]
  have h2 := congrArg (proj τ A χ) h0'
  rw [proj_apply τ B, map_sum, map_zero, Finset.sum_congr rfl fun b _ => key b, ← Finset.sum_smul,
    smul_eq_zero] at h2
  refine Subtype.ext (h2.resolve_left ?_)
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  refine mul_ne_zero ?_ (Nat.cast_ne_zero.2 Fintype.card_ne_zero)
  refine Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 ⟨1, ?_⟩)
  simp

theorem finrank_eig_conj (τ : Representation ℂ G V) (S T : Set G) (χ χ' : G → ℂ) (w : G)
    (hS : ∀ g, g ∈ T ↔ w⁻¹ * g * w ∈ S) (hχ : ∀ g, χ (w⁻¹ * g * w) = χ' g) :
    finrank ℂ (eig τ S χ) = finrank ℂ (eig τ T χ') := by
  let e : V ≃ₗ[ℂ] V := LinearEquiv.ofLinear (τ w) (τ w⁻¹)
    (by rw [← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one]; rfl)
    (by rw [← Module.End.mul_eq_comp, ← map_mul, inv_mul_cancel, map_one]; rfl)
  refine (e.ofSubmodules _ _ ?_).finrank_eq
  ext v
  rw [Submodule.mem_map_equiv, mem_eig_iff, mem_eig_iff]
  have he : e.symm v = τ w⁻¹ v := rfl
  rw [he]
  constructor
  · intro h g hg
    have h1 := congrArg (τ w) (h _ ((hS g).1 hg))
    rw [hχ, map_smul] at h1
    simp only [← Module.End.mul_apply, ← map_mul] at h1
    simpa [mul_assoc] using h1
  · intro h g hg
    have e1 : w⁻¹ * (w * g * w⁻¹) * w = g := by group
    have h1 := congrArg (τ w⁻¹) (h (w * g * w⁻¹) ((hS _).2 (by rwa [e1])))
    rw [← hχ, e1, map_smul] at h1
    rw [← h1]
    simp only [← Module.End.mul_apply, ← map_mul]
    congr 2
    group

end Abstract

section Matrices

variable {F : Type} [Field F] {r : ℕ}

def cyc (ρ k : ℕ) (h : ρ + k < r) : Equiv.Perm (Fin r) where
  toFun i := ⟨if i.val < ρ then i.val else if i.val < ρ + k then i.val + 1 else if i.val = ρ + k then ρ else i.val, by
    have := i.2
    split_ifs <;> omega⟩
  invFun i := ⟨if i.val < ρ then i.val else if i.val = ρ then ρ + k else if i.val ≤ ρ + k then i.val - 1 else i.val, by
    have := i.2
    split_ifs <;> omega⟩
  left_inv i := by
    ext
    dsimp only
    split_ifs <;> omega
  right_inv i := by
    ext
    dsimp only
    split_ifs <;> omega

theorem cyc_val (ρ k : ℕ) (h : ρ + k < r) (i : Fin r) : (cyc ρ k h i).val =
    if i.val < ρ then i.val else if i.val < ρ + k then i.val + 1 else if i.val = ρ + k then ρ else i.val := rfl

theorem exists_perm (σ : Equiv.Perm (Fin r)) : ∃ w : GL (Fin r) F, ∀ (g : GL (Fin r) F) (i j : Fin r),
    ((w⁻¹ * g * w : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i j = (g : Matrix (Fin r) (Fin r) F) (σ i) (σ j) := by
  refine ⟨⟨σ.symm.toPEquiv.toMatrix, σ.toPEquiv.toMatrix, ?_, ?_⟩, fun g i j => ?_⟩
  · rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans]; simp
  · rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans]; simp
  · show ((σ.toPEquiv.toMatrix * (g : Matrix (Fin r) (Fin r) F) * σ.symm.toPEquiv.toMatrix :
      Matrix (Fin r) (Fin r) F)) i j = _
    rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
    simp

def elem {p q : Fin r} (h : p ≠ q) (t : F) : GL (Fin r) F :=
  ⟨Matrix.transvection p q t, Matrix.transvection p q (-t),
    by rw [Matrix.transvection_mul_transvection_same _ _ h]; simp,
    by rw [Matrix.transvection_mul_transvection_same _ _ h]; simp⟩

theorem conj_elem {p q : Fin r} (h : p ≠ q) (t : F) (g : GL (Fin r) F) (i l : Fin r) :
    ((g⁻¹ * elem h t * g : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i l =
      (1 : Matrix (Fin r) (Fin r) F) i l +
        ((g⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i p * t * (g : Matrix (Fin r) (Fin r) F) q l := by
  have e : ((elem h t : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) = 1 + Matrix.single p q t := rfl
  rw [Units.val_mul, Units.val_mul, e, mul_add, add_mul, mul_one, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Matrix.add_apply]
  congr 1
  rw [Matrix.mul_apply, Finset.sum_eq_single q]
  · rw [Matrix.mul_single_apply_same]
  · intro b _ hb
    rw [Matrix.mul_single_apply_of_ne _ _ _ _ _ hb, zero_mul]
  · simp

end Matrices

section Main

variable {F : Type} [Field F] {r : ℕ}

theorem edgeSum_single (Ed : Fin r → Fin r → Prop) [DecidableRel Ed] (g : GL (Fin r) F) {p q : Fin r} (h : Ed p q)
    (h0 : ∀ i j, Ed i j → (i ≠ p ∨ j ≠ q) → (g : Matrix (Fin r) (Fin r) F) i j = 0) :
    edgeSum Ed g = (g : Matrix (Fin r) (Fin r) F) p q := by
  unfold edgeSum
  rw [Finset.sum_eq_single p, Finset.sum_eq_single q, if_pos h]
  · intro j _ hj
    split_ifs with e
    · exact h0 _ _ e (Or.inr hj)
    · rfl
  · simp
  · intro i _ hi
    refine Finset.sum_eq_zero fun j _ => ?_
    split_ifs with e
    · exact h0 _ _ e (Or.inl hi)
    · rfl
  · simp

theorem mem_unip_iff (g : GL (Fin r) F) : g ∈ unip F r ↔
    (∀ i, (g : Matrix (Fin r) (Fin r) F) i i = 1) ∧
      ∀ i j : Fin r, j.val < i.val → (g : Matrix (Fin r) (Fin r) F) i j = 0 :=
  ⟨fun h => ⟨h.2, fun _ _ e => h.1 e⟩, fun h => ⟨fun i j e => h.2 i j e, h.1⟩⟩

theorem mem_unipSym_iff (ρ k : ℕ) (g : GL (Fin r) F) : g ∈ unipSym F r ρ k ↔
    g ∈ unip F r ∧ ∀ i j : Fin r, ρ ≤ i.val → i.val < ρ + k → j.val = ρ + k →
      (g : Matrix (Fin r) (Fin r) F) i j = 0 := Iff.rfl

theorem mem_conj_iff {ρ k : ℕ} (h : ρ + k < r) {g g' : GL (Fin r) F}
    (e : ∀ i j, (g' : Matrix (Fin r) (Fin r) F) i j = (g : Matrix (Fin r) (Fin r) F) (cyc ρ k h i) (cyc ρ k h j)) :
    g' ∈ unipSym F r ρ k ↔ g ∈ unip F r ∧ ∀ i j : Fin r, i.val = ρ → ρ < j.val → j.val ≤ ρ + k →
      (g : Matrix (Fin r) (Fin r) F) i j = 0 := by
  rw [mem_unipSym_iff, mem_unip_iff, mem_unip_iff]
  simp only [e]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨⟨fun i => ?_, fun i j hij => ?_⟩, fun i j a1 a2 a3 => ?_⟩
    · obtain ⟨i, rfl⟩ := (cyc ρ k h).surjective i
      exact h1 i
    · obtain ⟨i, rfl⟩ := (cyc ρ k h).surjective i
      obtain ⟨j, rfl⟩ := (cyc ρ k h).surjective j
      rw [cyc_val, cyc_val] at hij
      by_cases c : j.val < i.val
      · exact h2 i j c
      · refine h3 i j ?_ ?_ ?_ <;> split_ifs at hij <;> omega
    · obtain ⟨i, rfl⟩ := (cyc ρ k h).surjective i
      obtain ⟨j, rfl⟩ := (cyc ρ k h).surjective j
      rw [cyc_val] at a1 a2 a3
      refine h2 i j ?_
      split_ifs at a1 a2 a3 <;> omega
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨⟨fun i => h1 _, fun i j hij => ?_⟩, fun i j a1 a2 a3 => ?_⟩
    · by_cases c : (cyc ρ k h j).val < (cyc ρ k h i).val
      · exact h2 _ _ c
      · rw [cyc_val, cyc_val] at c
        refine h3 _ _ ?_ ?_ ?_ <;> rw [cyc_val] <;> split_ifs at c ⊢ <;> omega
    · refine h2 _ _ ?_
      rw [cyc_val, cyc_val]
      split_ifs <;> omega

theorem edgeSum_conj {ρ k : ℕ} (h : ρ + k < r) {g g' : GL (Fin r) F}
    (e : ∀ i j, (g' : Matrix (Fin r) (Fin r) F) i j = (g : Matrix (Fin r) (Fin r) F) (cyc ρ k h i) (cyc ρ k h j)) :
    edgeSum (symEdge ρ k) g' = edgeSum (symEdge (ρ + 1) k) g := by
  unfold edgeSum
  refine Fintype.sum_equiv (cyc ρ k h) _ _ fun i => Fintype.sum_equiv (cyc ρ k h) _ _ fun j => ?_
  rw [e]
  refine if_congr ?_ rfl rfl
  unfold symEdge
  rw [cyc_val, cyc_val]
  split_ifs <;> omega

theorem chi_mul (ψ : AddChar F ℂ) (ρ k : ℕ) {x y : GL (Fin r) F} (hx : x ∈ unipSym F r ρ k)
    (hy : y ∈ unipSym F r ρ k) :
    ψ (edgeSum (symEdge ρ k) (x * y)) = ψ (edgeSum (symEdge ρ k) x) * ψ (edgeSum (symEdge ρ k) y) := by
  rw [← AddChar.map_add_eq_mul]
  congr 1
  exact congrArg Multiplicative.toAdd ((symHom F r ρ k).map_mul ⟨x, hx⟩ ⟨y, hy⟩)

theorem conj_elem_mem_unip {p q : Fin r} (h : p ≠ q) (hpq : p.val < q.val) (t : F) {g : GL (Fin r) F}
    (hg : g ∈ unip F r) : g⁻¹ * elem h t * g ∈ unip F r := by
  refine (unip F r).mul_mem ((unip F r).mul_mem ((unip F r).inv_mem hg) ?_) hg
  have e : ((elem h t : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) = 1 + Matrix.single p q t := rfl
  rw [mem_unip_iff, e]
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · rw [Matrix.add_apply, Matrix.single_apply_of_ne, Matrix.one_apply_eq, add_zero]
    rintro ⟨rfl, rfl⟩
    exact h rfl
  · rw [Matrix.add_apply, Matrix.single_apply_of_ne, Matrix.one_apply_ne, add_zero]
    · rintro rfl
      omega
    · rintro ⟨rfl, rfl⟩
      omega

theorem conj_elem_zero {p q : Fin r} (h : p ≠ q) (t : F) {g : GL (Fin r) F} (hg : g ∈ unip F r) {i l : Fin r}
    (hil : i.val ≠ l.val) (h0 : p.val < i.val ∨ l.val < q.val) :
    ((g⁻¹ * elem h t * g : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i l = 0 := by
  rw [conj_elem, Matrix.one_apply_ne (fun e => hil (congrArg _ e)), zero_add]
  rcases h0 with h0 | h0
  · rw [unip_lower ((unip F r).inv_mem hg) (show p < i from h0), zero_mul, zero_mul]
  · rw [unip_lower hg (show l < q from h0), mul_zero]

theorem edgeSum_conj_elem {ρ k : ℕ} {a c p q : Fin r} (ha : a.val = ρ) (hc : c.val = ρ + k + 1) (h : p ≠ q)
    (hs : (p.val = ρ ∧ ρ < q.val) ∨ (q.val = ρ + k + 1 ∧ p.val ≤ ρ + k)) (t : F) {g : GL (Fin r) F}
    (hg : g ∈ unip F r) :
    edgeSum (symEdge (ρ + 1) k) (g⁻¹ * elem h t * g) =
      ((g⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) a p * t * (g : Matrix (Fin r) (Fin r) F) q c := by
  rw [edgeSum_single (p := a) (q := c) _ _ (Or.inr ⟨by omega, by omega⟩), conj_elem,
    Matrix.one_apply_ne (fun e => by rw [e] at ha; omega), zero_add]
  intro i j hij hne
  rw [Ne, Ne, Fin.ext_iff, Fin.ext_iff] at hne
  unfold symEdge at hij
  exact conj_elem_zero h t hg (by omega) (by omega)

theorem nPos_succ (F : Type) [Field F] [Fintype F] (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) (r : ℕ) (V : Type)
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (τ : Representation ℂ (GL (Fin r) F) V) (ρ k : ℕ)
    (hr : ρ + k + 2 ≤ r) : nPos ψ τ ρ k = nPos ψ τ (ρ + 1) k := by
  classical
  have h : ρ + k < r := by omega
  obtain ⟨w, hw⟩ := exists_perm (F := F) (cyc ρ k h)
  obtain ⟨t, ht⟩ := AddChar.ne_one_iff.1 hψ
  let A : Subgroup (GL (Fin r) F) := (unipSym F r ρ k).comap (MulAut.conj w⁻¹).toMonoidHom
  have hA0 : ∀ g, g ∈ A ↔ w⁻¹ * g * w ∈ unipSym F r ρ k := fun g => by simp [A]
  have hA : ∀ g, g ∈ A ↔ g ∈ unip F r ∧ ∀ i j : Fin r, i.val = ρ → ρ < j.val → j.val ≤ ρ + k →
      (g : Matrix (Fin r) (Fin r) F) i j = 0 := fun g => (hA0 g).trans (mem_conj_iff h (hw g))
  have hE : ∀ g : GL (Fin r) F, edgeSum (symEdge ρ k) (w⁻¹ * g * w) = edgeSum (symEdge (ρ + 1) k) g :=
    fun g => edgeSum_conj h (hw g)
  let χ : GL (Fin r) F → ℂ := fun g => ψ (edgeSum (symEdge (ρ + 1) k) g)
  have hχA : ∀ x ∈ A, ∀ y ∈ A, χ (x * y) = χ x * χ y := by
    intro x hx y hy
    simp only [χ, ← hE]
    rw [← chi_mul ψ ρ k ((hA0 x).1 hx) ((hA0 y).1 hy)]
    congr 2
    group
  have hχB : ∀ x ∈ unipSym F r (ρ + 1) k, ∀ y ∈ unipSym F r (ρ + 1) k, χ (x * y) = χ x * χ y :=
    fun x hx y hy => chi_mul ψ (ρ + 1) k hx hy
  have hχ1 : χ 1 = 1 := by
    have : edgeSum (symEdge (ρ + 1) k) (1 : GL (Fin r) F) = 0 :=
      congrArg Multiplicative.toAdd (symHom F r (ρ + 1) k).map_one
    simp only [χ, this, AddChar.map_zero_eq_one]
  let a : Fin r := ⟨ρ, by omega⟩
  let c : Fin r := ⟨ρ + k + 1, by omega⟩
  have ha : a.val = ρ := rfl
  have hc : c.val = ρ + k + 1 := rfl
  have triv : ∀ x : GL (Fin r) F, x = 1⁻¹ * x * 1 := fun x => by simp
  unfold nPos
  rw [finrank_eig_conj τ _ (A : Set (GL (Fin r) F)) _ χ w hA0 (fun g => by simp only [χ, hE])]
  refine le_antisymm (finrank_eig_le τ _ _ χ hχA hχB hχ1 fun b hb hbA => ?_)
    (finrank_eig_le τ _ _ χ hχB hχA hχ1 fun b hb hbB => ?_)
  · have hu : b ∈ unip F r := hb.1
    have h1 : b⁻¹ ∉ A := fun e => hbA (by simpa using A.inv_mem e)
    rw [hA] at h1
    push Not at h1
    obtain ⟨i, j, hi, hj1, hj2, hne⟩ := h1 ((unip F r).inv_mem hu)
    obtain rfl : i = a := Fin.ext hi
    have hjc : j ≠ c := fun e => by rw [e] at hj2; omega
    have hmem : ∀ (s : F) (g : GL (Fin r) F), g ∈ unip F r → g⁻¹ * elem hjc s * g ∈ A := fun s g hg =>
      (hA _).2 ⟨conj_elem_mem_unip hjc (by omega) s hg, fun i l _ _ _ =>
        conj_elem_zero hjc s hg (by omega) (by omega)⟩
    refine ⟨elem hjc ((((b⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) a j)⁻¹ * t), ?_, hmem _ _ hu, ?_⟩
    · rw [triv (elem _ _)]
      exact hmem _ _ (unip F r).one_mem
    · conv_rhs => rw [triv (elem _ _)]
      simp only [χ]
      rw [edgeSum_conj_elem ha hc hjc (by omega) _ hu, edgeSum_conj_elem ha hc hjc (by omega) _ (unip F r).one_mem,
        unip_diag hu, mul_one, mul_inv_cancel_left₀ hne, inv_one, Units.val_one,
        Matrix.one_apply_ne (fun e : a = j => by rw [← e] at hj1; omega), zero_mul, zero_mul, AddChar.map_zero_eq_one]
      exact ht
  · have hu : b ∈ unip F r := ((hA b).1 hb).1
    rw [mem_unipSym_iff] at hbB
    push Not at hbB
    obtain ⟨j, l, hj1, hj2, hl, hne⟩ := hbB hu
    obtain rfl : l = c := Fin.ext (by omega)
    have haj : a ≠ j := fun e => by rw [← e] at hj1; omega
    have hmem : ∀ (s : F) (g : GL (Fin r) F), g ∈ unip F r → g⁻¹ * elem haj s * g ∈ unipSym F r (ρ + 1) k :=
      fun s g hg => ⟨conj_elem_mem_unip haj (by omega) s hg, fun i l _ _ _ =>
        conj_elem_zero haj s hg (by omega) (by omega)⟩
    refine ⟨elem haj (t * ((b : Matrix (Fin r) (Fin r) F) j c)⁻¹), ?_, hmem _ _ hu, ?_⟩
    · rw [triv (elem _ _)]
      exact hmem _ _ (unip F r).one_mem
    · conv_rhs => rw [triv (elem _ _)]
      simp only [χ]
      rw [edgeSum_conj_elem ha hc haj (by omega) _ hu, edgeSum_conj_elem ha hc haj (by omega) _ (unip F r).one_mem,
        unip_diag ((unip F r).inv_mem hu), one_mul, inv_mul_cancel_right₀ hne, Units.val_one,
        Matrix.one_apply_ne (fun e : j = c => by rw [e] at hj2; omega), mul_zero, AddChar.map_zero_eq_one]
      exact ht

end Main

end GlobalTheory.FinGL.RootExchange
