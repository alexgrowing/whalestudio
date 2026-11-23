import Mathlib

noncomputable section
open scoped BigOperators
open Module

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FS

theorem rat_four_sq (p : ℚ) (hp : 0 ≤ p) : ∃ a b c d : ℚ, p = a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 := by
  obtain ⟨x, y, z, w, hs⟩ := Nat.sum_four_squares (p.num.toNat * p.den)
  refine ⟨x / p.den, y / p.den, z / p.den, w / p.den, ?_⟩
  have hnum : (0 : ℤ) ≤ p.num := Rat.num_nonneg.mpr hp
  have hd : (p.den : ℚ) ≠ 0 := by positivity
  have hn : ((p.num.toNat : ℕ) : ℚ) = (p.num : ℚ) := by exact_mod_cast Int.toNat_of_nonneg hnum
  have key : (x : ℚ) ^ 2 + (y : ℚ) ^ 2 + (z : ℚ) ^ 2 + (w : ℚ) ^ 2 = (p.num : ℚ) * p.den := by
    have h1 : ((x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 : ℕ) : ℚ) = ((p.num.toNat * p.den : ℕ) : ℚ) := by rw [hs]
    push_cast at h1
    rw [h1, hn]
  calc p = (p.num : ℚ) / p.den := (Rat.num_div_den p).symm
    _ = ((p.num : ℚ) * p.den) / (p.den : ℚ) ^ 2 := by field_simp
    _ = _ := by rw [← key]; field_simp

variable {K : Type} [Field K]

def qM (p q r s : K) : Matrix (Fin 4) (Fin 4) K :=
  !![p, -q, -r, -s; q, p, -s, r; r, s, p, -q; s, -r, q, p]

theorem qM_form (p q r s : K) (u v : Fin 4 → K) :
    ∑ β, (∑ a, qM p q r s β a * u a) * (∑ a, qM p q r s β a * v a)
      = (p ^ 2 + q ^ 2 + r ^ 2 + s ^ 2) * ∑ a, u a * v a := by
  simp [qM, Fin.sum_univ_four]
  ring

theorem qM_fix (c : K →+* K) {p q r s : K} (hp : c p = p) (hq : c q = q) (hr : c r = r) (hs : c s = s) (β a : Fin 4) :
    c (qM p q r s β a) = qM p q r s β a := by
  fin_cases β <;> fin_cases a <;> simp [qM, hp, hq, hr, hs, map_neg]

variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable (c : K →+* K) (h : V → V → K)

structure Herm4 : Prop where
  add_left : ∀ x x' y, h (x + x') y = h x y + h x' y
  smul_left : ∀ (k : K) x y, h (k • x) y = k * h x y
  symm : ∀ x y, h y x = c (h x y)
  pos : ∀ x, x ≠ 0 → h x x ≠ 0 ∧ ∃ p q r s : K, c p = p ∧ c q = q ∧ c r = r ∧ c s = s ∧
    h x x = p ^ 2 + q ^ 2 + r ^ 2 + s ^ 2

variable {c h}

def Herm4.hl (H : Herm4 c h) (y : V) : V →ₗ[K] K where
  toFun x := h x y
  map_add' x x' := H.add_left x x' y
  map_smul' k x := H.smul_left k x y

theorem Herm4.ortho_symm (H : Herm4 c h) {x y : V} (e : h x y = 0) : h y x = 0 := by
  rw [H.symm x y, e, map_zero]

theorem Herm4.ortho_fam (H : Herm4 c h) (m : ℕ) (hm : m ≤ finrank K V) :
    ∃ v : Fin m → V, (∀ i, v i ≠ 0) ∧ ∀ i j, i ≠ j → h (v i) (v j) = 0 := by
  induction m with
  | zero => exact ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0⟩
  | succ m ih =>
    obtain ⟨v, hv0, hv⟩ := ih (by omega)
    let L : V →ₗ[K] (Fin m → K) := LinearMap.pi (fun i => H.hl (v i))
    have hrank := LinearMap.finrank_range_add_finrank_ker L
    have hr : finrank K (LinearMap.range L) ≤ m := by
      calc finrank K (LinearMap.range L) ≤ finrank K (Fin m → K) := Submodule.finrank_le _
        _ = m := by simp
    have hker : LinearMap.ker L ≠ ⊥ := by
      intro hb
      rw [hb, finrank_bot] at hrank
      omega
    obtain ⟨x, hxk, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
    have hx : ∀ i, h x (v i) = 0 := fun i => by
      have h1 := congrFun (LinearMap.mem_ker.mp hxk) i
      simpa [L, Herm4.hl] using h1
    refine ⟨Fin.snoc (α := fun _ => V) v x, fun i => ?_, fun i j hij => ?_⟩
    · induction i using Fin.lastCases with
      | last => simpa using hx0
      | cast i => simpa using hv0 i
    · induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last => exact absurd rfl hij
        | cast j => simpa using hx j
      | cast i =>
        induction j using Fin.lastCases with
        | last => simpa using H.ortho_symm (hx i)
        | cast j =>
          simp only [Fin.snoc_castSucc]
          exact hv i j (fun e => hij (by rw [e]))

theorem Herm4.linInd (H : Herm4 c h) {ι : Type} [Fintype ι] [DecidableEq ι] (v : ι → V) (hv0 : ∀ i, v i ≠ 0)
    (hv : ∀ i j, i ≠ j → h (v i) (v j) = 0) : LinearIndependent K v := by
  rw [linearIndependent_iff']
  intro s g hg i hi
  have h1 : H.hl (v i) (∑ j ∈ s, g j • v j) = 0 := by rw [hg, map_zero]
  rw [map_sum] at h1
  simp only [map_smul, smul_eq_mul] at h1
  rw [Finset.sum_eq_single i] at h1
  · exact (mul_eq_zero.mp h1).resolve_right (H.pos (v i) (hv0 i)).1
  · intro j _ hji
    show g j * h (v j) (v i) = 0
    rw [hv j i hji, mul_zero]
  · intro his
    exact absurd hi his

theorem Herm4.ortho_basis (H : Herm4 c h) {n : Type} [Fintype n] [DecidableEq n] (hn : Fintype.card n = finrank K V) :
    ∃ b : Basis n K V, ∀ i j, i ≠ j → h (b i) (b j) = 0 := by
  rcases isEmpty_or_nonempty n with hne | hne
  · have h0 : finrank K V = 0 := by rw [← hn, Fintype.card_eq_zero]
    exact ⟨basisOfFinrankZero h0, fun i => isEmptyElim i⟩
  · obtain ⟨v, hv0, hv⟩ := H.ortho_fam (finrank K V) le_rfl
    let e : n ≃ Fin (finrank K V) := Fintype.equivFinOfCardEq hn
    have hli : LinearIndependent K (v ∘ e) :=
      H.linInd (v ∘ e) (fun i => hv0 _) (fun i j hij => hv _ _ (fun h' => hij (e.injective h')))
    refine ⟨basisOfLinearIndependentOfCardEqFinrank hli hn, fun i j hij => ?_⟩
    simp only [coe_basisOfLinearIndependentOfCardEqFinrank, Function.comp_apply]
    exact hv _ _ (fun h' => hij (e.injective h'))

private theorem coord_lemma (H : Herm4 c h) {n : Type} [Fintype n] [DecidableEq n] (b : Basis n K V)
    (hb : ∀ i j, i ≠ j → h (b i) (b j) = 0) (v : V) (i : n) : h v (b i) = b.repr v i * h (b i) (b i) := by
  have e : h v (b i) = H.hl (b i) (∑ j, b.repr v j • b j) := by
    rw [b.sum_repr v]
    rfl
  rw [e, map_sum]
  simp only [map_smul, smul_eq_mul]
  rw [Finset.sum_eq_single i]
  · rfl
  · intro j _ hj
    show b.repr v j * h (b j) (b i) = 0
    rw [hb j i hj, mul_zero]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

theorem Herm4.form_repr (H : Herm4 c h) {n : Type} [Fintype n] [DecidableEq n] (b : Basis n K V)
    (hb : ∀ i j, i ≠ j → h (b i) (b j) = 0) (u v : V) :
    h u v = ∑ i, h (b i) (b i) * (b.repr u i * c (b.repr v i)) := by
  have e : h u v = H.hl v (∑ i, b.repr u i • b i) := by
    rw [b.sum_repr u]
    rfl
  rw [e, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, smul_eq_mul]
  show b.repr u i * h (b i) v = _
  have hbb : c (h (b i) (b i)) = h (b i) (b i) := (H.symm (b i) (b i)).symm
  rw [H.symm v (b i), coord_lemma H b hb v i, map_mul, hbb]
  ring

theorem Herm4.iso_of (H : Herm4 c h) {n : Type} [Fintype n] [DecidableEq n] (b : Basis n K V)
    (hb : ∀ i j, i ≠ j → h (b i) (b j) = 0) (p q r s : n → K) (hp : ∀ i, c (p i) = p i) (hq : ∀ i, c (q i) = q i)
    (hr : ∀ i, c (r i) = r i) (hs : ∀ i, c (s i) = s i)
    (hsq : ∀ i, h (b i) (b i) = p i ^ 2 + q i ^ 2 + r i ^ 2 + s i ^ 2) :
    ∃ g : (Fin 4 → V) ≃ₗ[K] (Fin 4 × n → K), (∀ x y, ∑ w, g x w * c (g y w) = ∑ a, h (x a) (y a)) ∧
      ∀ x w, g x w = ∑ a, qM (p w.2) (q w.2) (r w.2) (s w.2) w.1 a * b.repr (x a) w.2 := by
  let Φ : (Fin 4 → V) →ₗ[K] (Fin 4 × n → K) :=
    { toFun := fun x w => ∑ a, qM (p w.2) (q w.2) (r w.2) (s w.2) w.1 a * b.repr (x a) w.2
      map_add' := by
        intro x y
        funext w
        simp [Finset.sum_add_distrib, mul_add]
      map_smul' := by
        intro k x
        funext w
        simp only [Pi.smul_apply, map_smul, Finsupp.smul_apply, smul_eq_mul, Finset.mul_sum, RingHom.id_apply]
        exact Finset.sum_congr rfl fun _ _ => by ring }
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    funext a
    apply b.repr.injective
    ext i
    have hN : h (b i) (b i) ≠ 0 := (H.pos (b i) (b.ne_zero i)).1
    have hzero : ∀ β, ∑ a', qM (p i) (q i) (r i) (s i) β a' * b.repr (x a') i = 0 := fun β => by
      have h1 := congrFun hx (β, i)
      simpa [Φ] using h1
    have hf := qM_form (p i) (q i) (r i) (s i) (fun a' => b.repr (x a') i) (Pi.single a 1)
    simp only [hzero, zero_mul, Finset.sum_const_zero] at hf
    rw [← hsq i] at hf
    simp [Pi.single_apply] at hf
    simp only [map_zero, Finsupp.coe_zero, Pi.zero_apply]
    exact hf.resolve_left hN
  have hdim : finrank K (Fin 4 → V) = finrank K (Fin 4 × n → K) := by
    have e := ((LinearEquiv.piCongrRight fun _ : Fin 4 => b.equivFun).finrank_eq)
    rw [e]
    simp only [Module.finrank_eq_card_basis b, Module.finrank_fintype_fun_eq_card, Fintype.card_prod, Fintype.card_fin]
    first
      | (rw [Module.finrank_pi_fintype]; simp)
      | (rw [FiniteDimensional.finrank_pi_fintype]; simp)
      | simp [Module.finrank_pi_fintype]
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj
  refine ⟨LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩, fun x y => ?_, fun x w => rfl⟩
  show ∑ w, Φ x w * c (Φ y w) = _
  have hc : ∀ (i : n) β, c (∑ a, qM (p i) (q i) (r i) (s i) β a * b.repr (y a) i) =
      ∑ a, qM (p i) (q i) (r i) (s i) β a * c (b.repr (y a) i) := by
    intro i β
    rw [map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_mul, qM_fix c (hp i) (hq i) (hr i) (hs i)]
  simp only [Φ, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp only [hc]
  simp_rw [qM_form, ← hsq, Finset.mul_sum]
  rw [Finset.sum_congr rfl fun a _ => H.form_repr b hb (x a) (y a)]
  exact Finset.sum_comm

theorem Herm4.iso (H : Herm4 c h) {n : Type} [Fintype n] [DecidableEq n] (hn : Fintype.card n = finrank K V) :
    ∃ g : (Fin 4 → V) ≃ₗ[K] (Fin 4 × n → K), ∀ x y, ∑ w, g x w * c (g y w) = ∑ a, h (x a) (y a) := by
  obtain ⟨b, hb⟩ := H.ortho_basis hn
  have hpos : ∀ i, ∃ P : K × K × K × K, c P.1 = P.1 ∧ c P.2.1 = P.2.1 ∧ c P.2.2.1 = P.2.2.1 ∧
      c P.2.2.2 = P.2.2.2 ∧ h (b i) (b i) = P.1 ^ 2 + P.2.1 ^ 2 + P.2.2.1 ^ 2 + P.2.2.2 ^ 2 := fun i => by
    obtain ⟨-, p, q, r, s, h1, h2, h3, h4, h5⟩ := H.pos (b i) (b.ne_zero i)
    exact ⟨(p, q, r, s), h1, h2, h3, h4, h5⟩
  choose P hP using hpos
  obtain ⟨g, hg, -⟩ := H.iso_of b hb (fun i => (P i).1) (fun i => (P i).2.1) (fun i => (P i).2.2.1)
    (fun i => (P i).2.2.2) (fun i => (hP i).1) (fun i => (hP i).2.1) (fun i => (hP i).2.2.1)
    (fun i => (hP i).2.2.2.1) (fun i => (hP i).2.2.2.2)
  exact ⟨g, hg⟩

theorem Herm4.coord (H : Herm4 c h) {n : Type} [Fintype n] [DecidableEq n] (b : Basis n K V)
    (hb : ∀ i j, i ≠ j → h (b i) (b j) = 0) (v : V) (i : n) : h v (b i) = b.repr v i * h (b i) (b i) :=
  coord_lemma H b hb v i

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FS

end
