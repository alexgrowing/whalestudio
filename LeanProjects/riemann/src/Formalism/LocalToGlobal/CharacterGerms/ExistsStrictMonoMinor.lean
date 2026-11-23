import Mathlib

noncomputable section

open Matrix

namespace Formalism.L2.FormalSeriesBounds.S4

section Minors

variable {R : Type*} [CommRing R]

def lenCoker (v : AddValuation R (WithTop ℝ)) {m h : ℕ} (B : Matrix (Fin m) (Fin h) R) :
    WithTop ℝ :=
  Finset.univ.inf fun g : Fin m → Fin h => v (B.submatrix id g).det

def fitt0 {m h : ℕ} (B : Matrix (Fin m) (Fin h) R) : Ideal R :=
  Ideal.span (Set.range fun g : Fin m → Fin h => (B.submatrix id g).det)

theorem le_v_sum (v : AddValuation R (WithTop ℝ)) {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → R) (g : WithTop ℝ) (hg : ∀ i ∈ s, g ≤ v (f i)) : g ≤ v (∑ i ∈ s, f i) := by
  revert hg
  refine Finset.induction_on s (fun _ => by simp) ?_
  intro i s hi ih hg
  rw [Finset.sum_insert hi]
  exact le_trans (le_min (hg i (Finset.mem_insert_self i s))
    (ih fun j hj => hg j (Finset.mem_insert_of_mem hj))) (v.map_add _ _)

theorem lenCoker_le_of_mem (v : AddValuation R (WithTop ℝ)) (hv : ∀ x, 0 ≤ v x)
    {m h : ℕ} (B : Matrix (Fin m) (Fin h) R) {x : R} (hx : x ∈ fitt0 B) :
    lenCoker v B ≤ v x := by
  unfold fitt0 at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨g, rfl⟩ := hy
    exact Finset.inf_le (Finset.mem_univ g)
  | zero => simp
  | add a b _ _ ha hb => exact le_trans (le_min ha hb) (v.map_add a b)
  | smul c a _ ha =>
    rw [smul_eq_mul, v.map_mul]
    exact le_trans ha (le_add_of_nonneg_left (hv c))

theorem exists_topMinor_le (v : AddValuation R (WithTop ℝ)) (hv : ∀ x, 0 ≤ v x) (n : ℕ) :
    ∀ (k : ℕ) (Y : Matrix (Fin (n + k)) (Fin (n + k)) R),
      ∃ f : Fin n → Fin (n + k), StrictMono f ∧
        v (Y.submatrix (Fin.castAdd k) f).det ≤ v Y.det := by
  intro k
  induction k with
  | zero =>
    intro Y
    exact ⟨Fin.castAdd 0, Fin.strictMono_castAdd 0, le_of_eq rfl⟩
  | succ k ih =>
    intro Y
    have hexp := Matrix.det_succ_row Y (Fin.last (n + k))
    obtain ⟨j, -, hj⟩ := Finset.exists_min_image Finset.univ
      (fun j : Fin (n + k + 1) => v (Y.submatrix (Fin.last (n + k)).succAbove j.succAbove).det)
      Finset.univ_nonempty
    have hle : v (Y.submatrix (Fin.last (n + k)).succAbove j.succAbove).det ≤ v Y.det := by
      rw [hexp]
      apply le_v_sum
      intro i _
      rw [v.map_mul]
      exact le_trans (hj i (Finset.mem_univ _)) (le_add_of_nonneg_left (hv _))
    obtain ⟨f', hf', hle'⟩ := ih (Y.submatrix (Fin.last (n + k)).succAbove j.succAbove)
    refine ⟨j.succAbove ∘ f', (Fin.strictMono_succAbove j).comp hf', le_trans (le_of_eq ?_) (le_trans hle' hle)⟩
    congr 2
    ext a b
    simp only [Matrix.submatrix_apply, Function.comp_apply, Fin.succAbove_last]
    congr 1

theorem exists_strictMono_minor (v : AddValuation R (WithTop ℝ)) {n h : ℕ}
    (B : Matrix (Fin n) (Fin h) R) (g : Fin n → Fin h) (hg : (B.submatrix id g).det ≠ 0) :
    ∃ f : Fin n → Fin h, StrictMono f ∧ v (B.submatrix id f).det = v (B.submatrix id g).det := by
  have hinj : Function.Injective g := by
    by_contra hni
    apply hg
    simp only [Function.Injective, not_forall, exists_prop] at hni
    obtain ⟨i, j, hij, hne⟩ := hni
    exact Matrix.det_zero_of_column_eq hne (fun k => by simp [hij])
  have hcard : (Finset.univ.image g).card = n := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_fin]
  let f := (Finset.univ.image g).orderEmbOfFin hcard
  have hmem : ∀ i, f i ∈ Finset.univ.image g := fun i => Finset.orderEmbOfFin_mem _ hcard i
  choose σ hσ using fun i => Finset.mem_image.mp (hmem i)
  have hσinj : Function.Injective σ := fun a b hab =>
    f.injective (by rw [← (hσ a).2, ← (hσ b).2, hab])
  let τ : Equiv.Perm (Fin n) := Equiv.ofBijective σ (Finite.injective_iff_bijective.mp hσinj)
  refine ⟨f, f.strictMono, ?_⟩
  have hfe : B.submatrix id f = (B.submatrix id g).submatrix id τ := by
    ext a b
    simp [τ, (hσ b).2]
  rw [hfe, Matrix.det_permute']
  rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with h1 | h1 <;> simp [h1]

theorem lenCoker_mul_le (v : AddValuation R (WithTop ℝ)) (hv : ∀ x, 0 ≤ v x) {n p h : ℕ}
    (S : Matrix (Fin n) (Fin p) R) (W : Matrix (Fin p) (Fin n) R) (hSW : S * W = 1)
    (α : Matrix (Fin p) (Fin h) R) : lenCoker v (S * α) ≤ lenCoker v α := by
  unfold lenCoker
  refine Finset.le_inf fun g _ => ?_
  change (Finset.univ.inf fun g' : Fin n → Fin h => v ((S * α).submatrix id g').det) ≤ _
  obtain ⟨Q, hQ⟩ : ∃ Q : Matrix (Fin p) (Fin p) R, Q = 1 - W * S := ⟨_, rfl⟩
  have hSQ : S * Q = 0 := by
    rw [hQ, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hSW, Matrix.one_mul, sub_self]
  have hQW : Q * W = 0 := by
    rw [hQ, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hSW, Matrix.mul_one, sub_self]
  have hWS : W * S * (W * S) = W * S := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc S, hSW, Matrix.one_mul]
  have hQQ : Q * Q + W * S = 1 := by
    rw [hQ, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, hWS]
    abel
  let M := α.submatrix id g
  let Z' : Matrix (Fin n ⊕ Fin p) (Fin p ⊕ Fin n) R := Matrix.fromBlocks S 0 Q W
  let Zi : Matrix (Fin p ⊕ Fin n) (Fin n ⊕ Fin p) R := Matrix.fromBlocks W Q 0 S
  let Dm : Matrix (Fin p ⊕ Fin n) (Fin p ⊕ Fin n) R := Matrix.fromBlocks M 0 0 1
  let er : Fin n ⊕ Fin p ≃ Fin (n + p) := finSumFinEquiv
  let ec : Fin p ⊕ Fin n ≃ Fin (n + p) := (Equiv.sumComm (Fin p) (Fin n)).trans finSumFinEquiv
  have hZ : Z' * Zi = 1 := by
    simp only [Z', Zi, Matrix.fromBlocks_multiply, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]
    rw [hSW, hSQ, hQW, hQQ, Matrix.fromBlocks_one]
  have hZZ : Matrix.reindex er ec Z' * Matrix.reindex ec er Zi = 1 := by
    simp only [Matrix.reindex_apply]
    rw [Matrix.submatrix_mul_equiv, hZ, Matrix.submatrix_one_equiv]
  have hv0 : v (Matrix.reindex er ec Z').det = 0 := by
    have h2 := congrArg v (congrArg Matrix.det hZZ)
    rw [Matrix.det_mul, Matrix.det_one, v.map_mul, v.map_one] at h2
    refine le_antisymm ?_ (hv _)
    calc v (Matrix.reindex er ec Z').det
        ≤ v (Matrix.reindex er ec Z').det + v (Matrix.reindex ec er Zi).det := le_add_of_nonneg_right (hv _)
      _ = 0 := h2
  let Y := Matrix.reindex er ec (Z' * Dm)
  have hdetY : Y.det = (Matrix.reindex er ec Z').det * M.det := by
    simp only [Y, Matrix.reindex_apply]
    rw [← Matrix.submatrix_mul_equiv Z' Dm er.symm ec.symm ec.symm, Matrix.det_mul,
      Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]
  have hvY : v Y.det = v M.det := by
    rw [hdetY, v.map_mul, hv0, zero_add]
  obtain ⟨f, -, hf⟩ := exists_topMinor_le v hv n p Y
  refine le_trans ?_ (hvY ▸ hf)
  by_cases hz : ∃ b c, ec.symm (f b) = Sum.inr c
  · obtain ⟨b, c, hb⟩ := hz
    have h0 : (Y.submatrix (Fin.castAdd p) f).det = 0 := by
      refine Matrix.det_eq_zero_of_column_eq_zero b fun i => ?_
      simp [Y, Z', Dm, er, Matrix.reindex_apply, hb, Matrix.mul_apply, Fintype.sum_sum_type]
    rw [h0, AddValuation.map_zero]
    exact le_top
  · push_neg at hz
    have hx : ∀ b, ∃ x, ec.symm (f b) = Sum.inl x := by
      intro b
      rcases hfb : ec.symm (f b) with x | c
      · exact ⟨x, rfl⟩
      · exact absurd hfb (hz b c)
    choose x hx using hx
    have heq : Y.submatrix (Fin.castAdd p) f = (S * α).submatrix id (g ∘ x) := by
      ext i b
      simp [Y, Z', Dm, M, er, Matrix.reindex_apply, hx b, Matrix.mul_apply, Fintype.sum_sum_type]
    rw [heq]
    exact Finset.inf_le (Finset.mem_univ _)

end Minors

section Numbers

def gam (l : ℕ) : ℝ := (l : ℝ) / ((l : ℝ) ^ 2 - 1)

def rho (l : ℕ) : ℝ := 1 / ((l : ℝ) ^ 2 - 1)

def frobSum {d : ℕ} (l : ℕ) (p : ZMod d → ℕ) (τ : ZMod d) : ℝ :=
  ∑' k : ℕ, ((l : ℝ) ^ (k + 1))⁻¹ * (p (τ + ((k + 1 : ℕ) : ZMod d)) : ℝ)

def CorDET {d : ℕ} (l : ℕ) (p : ZMod d → ℕ) (l1 l2 : ZMod d → ℝ) (τ : ZMod d) : Prop :=
  l1 τ - l2 τ = (p τ : ℝ) / ((l : ℝ) - 1) - frobSum l p τ

def ThmAi {d : ℕ} (l r rh : ℕ) (p : ZMod d → ℕ) (l2 : ZMod d → ℝ) (τ : ZMod d) : Prop :=
  l2 τ ≤ ((r : ℝ) - rh - p τ) / ((l : ℝ) - 1)

def ThmAiii {R : Type*} [CommRing R] (v : AddValuation R (WithTop ℝ)) {m h : ℕ}
    (α : Matrix (Fin m) (Fin h) R) (l1 : ℝ) : Prop :=
  lenCoker v α = (l1 : WithTop ℝ)

def xInert (l r j' rh : ℕ) : ℝ := ((r : ℝ) - 2 * j') * gam l + ((j' : ℝ) - rh) / ((l : ℝ) - 1)

theorem one_div_eq_gam_add_rho {l : ℕ} (hl : 1 < l) :
    1 / ((l : ℝ) - 1) = gam l + rho l := by
  have h1 : (1 : ℝ) < l := by exact_mod_cast hl
  have h2 : (l : ℝ) - 1 ≠ 0 := by
    intro h
    linarith
  have h3 : (l : ℝ) ^ 2 - 1 ≠ 0 := by
    intro h
    nlinarith
  unfold gam rho
  field_simp
  ring

theorem parity_of_alt {d : ℕ} (big : ZMod d → Prop) (halt : ∀ b, big (b + 1) ↔ ¬ big b)
    (a : ZMod d) (ha : big a) : ∀ k : ℕ, big (a + (k : ZMod d)) ↔ Even k := by
  intro k
  induction k with
  | zero => simp [ha]
  | succ k ih => rw [Nat.cast_succ, ← add_assoc, halt, ih, Nat.even_add_one]

theorem frobSum_alt {d : ℕ} {l : ℕ} (hl : 1 < l) (n j j' : ℕ) (big : ZMod d → Prop)
    (halt : ∀ b, big (b + 1) ↔ ¬ big b) (p : ZMod d → ℕ)
    (hpb : ∀ b, big b → p b = n + j) (hps : ∀ b, ¬ big b → p b = j')
    (a : ZMod d) (ha : big a) :
    frobSum l p a = (j' : ℝ) * gam l + ((n : ℝ) + j) * rho l := by
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl
  have hlne : (l : ℝ) ≠ 0 := by positivity
  have h3 : (l : ℝ) ^ 2 - 1 ≠ 0 := by
    intro h
    nlinarith
  have hq0 : (0 : ℝ) ≤ ((l : ℝ)⁻¹) ^ 2 := by positivity
  have hq1 : ((l : ℝ)⁻¹) ^ 2 < 1 := pow_lt_one₀ (by positivity) (inv_lt_one_of_one_lt₀ hl1) two_ne_zero
  have hpar := parity_of_alt big halt a ha
  have hval : ∀ k : ℕ, (p (a + ((k + 1 : ℕ) : ZMod d)) : ℝ) = if Even k then (j' : ℝ) else (n : ℝ) + j := by
    intro k
    by_cases hk : Even k
    · have hb : ¬ big (a + ((k + 1 : ℕ) : ZMod d)) := by
        rw [hpar, Nat.even_add_one]
        exact not_not.mpr hk
      rw [hps _ hb, if_pos hk]
    · have hb : big (a + ((k + 1 : ℕ) : ZMod d)) := by
        rw [hpar, Nat.even_add_one]
        exact hk
      rw [hpb _ hb, if_neg hk]
      push_cast
      ring
  have hF : (fun k : ℕ => ((l : ℝ) ^ (k + 1))⁻¹ * (p (a + ((k + 1 : ℕ) : ZMod d)) : ℝ)) =
      fun k => ((l : ℝ) ^ (k + 1))⁻¹ * (if Even k then (j' : ℝ) else (n : ℝ) + j) :=
    funext fun k => by rw [hval]
  have hev : ∀ m : ℕ, ((l : ℝ) ^ (2 * m + 1))⁻¹ * (if Even (2 * m) then (j' : ℝ) else (n : ℝ) + j) =
      ((j' : ℝ) * (l : ℝ)⁻¹) * (((l : ℝ)⁻¹) ^ 2) ^ m := by
    intro m
    rw [if_pos (even_two_mul m), ← inv_pow, pow_succ, pow_mul]
    ring
  have hod : ∀ m : ℕ, ((l : ℝ) ^ (2 * m + 1 + 1))⁻¹ * (if Even (2 * m + 1) then (j' : ℝ) else (n : ℝ) + j) =
      (((n : ℝ) + j) * ((l : ℝ)⁻¹) ^ 2) * (((l : ℝ)⁻¹) ^ 2) ^ m := by
    intro m
    rw [if_neg (Nat.not_even_two_mul_add_one m), ← inv_pow, pow_succ, pow_succ, pow_mul]
    ring
  have hs := summable_geometric_of_lt_one hq0 hq1
  unfold frobSum
  rw [hF, ← tsum_even_add_odd (f := fun k : ℕ => ((l : ℝ) ^ (k + 1))⁻¹ * (if Even k then (j' : ℝ) else (n : ℝ) + j))
    (by simp only [hev]; exact hs.mul_left _) (by simp only [hod]; exact hs.mul_left _)]
  simp only [hev, hod, tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]
  unfold gam rho
  field_simp
  try ring

theorem frobSum_const {d : ℕ} {l : ℕ} (hl : 1 < l) (P : ℕ) (p : ZMod d → ℕ) (hp : ∀ τ, p τ = P)
    (a : ZMod d) : frobSum l p a = (P : ℝ) / ((l : ℝ) - 1) := by
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl
  have h0 : (0 : ℝ) ≤ (l : ℝ)⁻¹ := by positivity
  have h1 : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl1
  have h2 : (l : ℝ) - 1 ≠ 0 := by
    intro h
    linarith
  have hlne : (l : ℝ) ≠ 0 := by positivity
  unfold frobSum
  have hk : ∀ k : ℕ, ((l : ℝ) ^ (k + 1))⁻¹ * (p (a + ((k + 1 : ℕ) : ZMod d)) : ℝ) =
      ((P : ℝ) * (l : ℝ)⁻¹) * ((l : ℝ)⁻¹) ^ k := by
    intro k
    rw [hp, ← inv_pow, pow_succ]
    ring
  simp only [hk, tsum_mul_left, tsum_geometric_of_lt_one h0 h1]
  field_simp
  try ring

end Numbers

section Derivatives

variable {R : Type*} [CommRing R]

def detOp {F : Type*} [AddCommGroup F] [Module R F] {n : ℕ}
    (D : Fin n → Fin n → Module.End R F) : Module.End R F :=
  ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : R) • (List.ofFn fun ρ => D ρ (σ ρ)).prod

theorem ofFn_prod_apply {F : Type*} [AddCommGroup F] [Module R F] (g : F) :
    ∀ {m : ℕ} (E : Fin m → Module.End R F) (s : Fin m → R), (∀ i, E i g = s i • g) →
      (List.ofFn E).prod g = (∏ i, s i) • g := by
  intro m
  induction m with
  | zero =>
    intro E s _
    simp
  | succ m ih =>
    intro E s hE
    rw [List.ofFn_succ, List.prod_cons, Module.End.mul_apply,
      ih (fun i => E i.succ) (fun i => s i.succ) (fun i => hE i.succ), map_smul, hE 0, smul_smul,
      Fin.prod_univ_succ]
    congr 1
    ring

theorem detOp_apply_eigen {F : Type*} [AddCommGroup F] [Module R F] {n : ℕ}
    (D : Fin n → Fin n → Module.End R F) (a : Matrix (Fin n) (Fin n) R) (g : F)
    (hD : ∀ ρ c, D ρ c g = a ρ c • g) : detOp D g = a.det • g := by
  unfold detOp
  rw [LinearMap.sum_apply, ← Matrix.det_transpose, Matrix.det_apply, Finset.sum_smul]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [LinearMap.smul_apply, ofFn_prod_apply g (fun ρ => D ρ (σ ρ)) (fun ρ => a ρ (σ ρ)) (fun ρ => hD ρ (σ ρ)),
    smul_smul]
  simp [Matrix.transpose_apply, Units.smul_def]

theorem detOp_pow_apply_eigen {F : Type*} [AddCommGroup F] [Module R F] {n : ℕ}
    (D : Fin n → Fin n → Module.End R F) (a : Matrix (Fin n) (Fin n) R) (g : F)
    (hD : ∀ ρ c, D ρ c g = a ρ c • g) (y : ℕ) : ((detOp D) ^ y) g = a.det ^ y • g := by
  induction y with
  | zero => simp
  | succ y ih =>
    rw [pow_succ, Module.End.mul_apply, detOp_apply_eigen D a g hD, map_smul, ih, smul_smul, pow_succ]
    congr 1
    ring

theorem derivation_prod {F : Type*} [CommRing F] [Algebra R F] {n : ℕ} (D : Derivation R F F)
    (χ : Fin n → F) (b : Fin n → R) (hD : ∀ σ, D (χ σ) = b σ • χ σ) (s : Finset (Fin n)) :
    D (∏ σ ∈ s, χ σ) = (∑ σ ∈ s, b σ) • ∏ σ ∈ s, χ σ := by
  refine Finset.induction_on s (by simp) ?_
  intro i s hi ih
  rw [Finset.prod_insert hi, Finset.sum_insert hi, Derivation.leibniz, ih, hD]
  simp only [Algebra.smul_def, smul_eq_mul, map_add, Algebra.algebraMap_self, RingHom.id_apply]
  ring

end Derivatives

section Main

variable {R : Type*} [CommRing R]

theorem ch_minor (v : AddValuation R (WithTop ℝ)) (hv : ∀ x, 0 ≤ v x) {n p h : ℕ}
    (S : Matrix (Fin n) (Fin p) R) (W : Matrix (Fin p) (Fin n) R) (hSW : S * W = 1)
    (α : Matrix (Fin p) (Fin h) R) (x : ℝ) (hx : lenCoker v α ≤ (x : WithTop ℝ)) :
    ∃ f : Fin n → Fin h, StrictMono f ∧
      v (Matrix.of fun k c => (S * α) c (f k)).det ≤ lenCoker v α ∧
      ∀ (F : Type) [CommRing F] [Algebra R F] (D : Fin n → Fin n → Derivation R F F)
        (χ : Fin n → F) (ev : F →ₐ[R] R),
        (∀ ρ c σ, D ρ c (χ σ) = (if σ = ρ then (S * α) c (f ρ) else 0) • χ σ) →
        (∀ σ, ev (χ σ) = 1) →
        ∀ y : ℕ,
          ev (((detOp fun ρ c => (D ρ c : F →ₗ[R] F)) ^ y) (∏ σ, χ σ)) =
              (Matrix.of fun k c => (S * α) c (f k)).det ^ y ∧
            v ((Matrix.of fun k c => (S * α) c (f k)).det ^ y) ≤
              (((y : ℝ) * x : ℝ) : WithTop ℝ) := by
  have h1 := lenCoker_mul_le v hv S W hSW α
  have hxt : lenCoker v α ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top hx
  have hSt : lenCoker v (S * α) ≠ ⊤ := ne_top_of_le_ne_top hxt h1
  rcases isEmpty_or_nonempty (Fin n → Fin h) with hE | hE
  · exact absurd (by simp [lenCoker, Finset.univ_eq_empty]) hSt
  obtain ⟨g, -, hg⟩ := Finset.exists_mem_eq_inf Finset.univ Finset.univ_nonempty
    (fun g : Fin n → Fin h => v ((S * α).submatrix id g).det)
  have hgv : v ((S * α).submatrix id g).det = lenCoker v (S * α) := hg.symm
  have hdet : ((S * α).submatrix id g).det ≠ 0 := by
    intro h0
    apply hSt
    rw [← hgv, h0, AddValuation.map_zero]
  obtain ⟨f, hf, hfv⟩ := exists_strictMono_minor v (S * α) g hdet
  have htr : (Matrix.of fun k c => (S * α) c (f k)) = ((S * α).submatrix id f)ᵀ := by
    ext k c
    rfl
  have hmain : v (Matrix.of fun k c => (S * α) c (f k)).det ≤ lenCoker v α := by
    rw [htr, Matrix.det_transpose, hfv, hgv]
    exact h1
  refine ⟨f, hf, hmain, ?_⟩
  intro F _ _ D χ ev hD hev y
  set a : Matrix (Fin n) (Fin n) R := Matrix.of fun k c => (S * α) c (f k) with ha
  have hDa : ∀ ρ c, (D ρ c : F →ₗ[R] F) (∏ σ, χ σ) = a ρ c • ∏ σ, χ σ := by
    intro ρ c
    have := derivation_prod (D ρ c) χ (fun σ => if σ = ρ then (S * α) c (f ρ) else 0)
      (fun σ => hD ρ c σ) Finset.univ
    rw [Finset.sum_ite_eq'] at this
    simpa [ha] using this
  refine ⟨?_, ?_⟩
  · rw [detOp_pow_apply_eigen _ a _ hDa y, map_smul, map_prod]
    simp [hev]
  · have hvd : v a.det ≤ (x : WithTop ℝ) := le_trans hmain hx
    obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_le_ne_top WithTop.coe_ne_top hvd)
    have htx : t ≤ x := by
      rw [← ht] at hvd
      exact WithTop.coe_le_coe.mp hvd
    rw [AddValuation.map_pow, ← ht, ← WithTop.coe_nsmul, WithTop.coe_le_coe, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_left htx (Nat.cast_nonneg y)

theorem ch_inert (v : AddValuation R (WithTop ℝ)) (hv : ∀ x, 0 ≤ v x)
    {d : ℕ} (hd : Even d) (l : ℕ) (hl : l.Prime) (hlodd : Odd l)
    (r n j j' rh h : ℕ) (hr : r = n + j + j') (hh : h + rh = r) (hrh : rh ≤ j')
    (big : ZMod d → Prop) (halt : ∀ b, big (b + 1) ↔ ¬ big b) (p : ZMod d → ℕ)
    (hpb : ∀ b, big b → p b = n + j) (hps : ∀ b, ¬ big b → p b = j')
    (a : ZMod d) (ha : big a) (α : Matrix (Fin (p a)) (Fin h) R)
    (S : Matrix (Fin n) (Fin (p a)) R) (W : Matrix (Fin (p a)) (Fin n) R) (hSW : S * W = 1)
    (l1 l2 : ZMod d → ℝ) (hDET : CorDET l p l1 l2 a) (hAi : ThmAi l r rh p l2 a)
    (hAiii : ThmAiii v α (l1 a)) :
    (lenCoker v α ≤ (xInert l r j' rh : WithTop ℝ) ∧
      xInert l r j' rh = ((r : ℝ) - j' - rh) * gam l + ((j' : ℝ) - rh) * rho l ∧
      xInert l r j' rh ≤ (n : ℝ) * gam l + ((j : ℝ) + j') / ((l : ℝ) - 1)) ∧
    ∃ f : Fin n → Fin h, StrictMono f ∧
      v (Matrix.of fun k c => (S * α) c (f k)).det ≤ lenCoker v α ∧
      ∀ (F : Type) [CommRing F] [Algebra R F] (D : Fin n → Fin n → Derivation R F F)
        (χ : Fin n → F) (ev : F →ₐ[R] R),
        (∀ ρ c σ, D ρ c (χ σ) = (if σ = ρ then (S * α) c (f ρ) else 0) • χ σ) →
        (∀ σ, ev (χ σ) = 1) →
        ∀ y : ℕ,
          ev (((detOp fun ρ c => (D ρ c : F →ₗ[R] F)) ^ y) (∏ σ, χ σ)) =
              (Matrix.of fun k c => (S * α) c (f k)).det ^ y ∧
            v ((Matrix.of fun k c => (S * α) c (f k)).det ^ y) ≤
              (((y : ℝ) * xInert l r j' rh : ℝ) : WithTop ℝ) := by
  subst hr
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.one_lt
  have hu := one_div_eq_gam_add_rho hl.one_lt
  have hg0 : 0 ≤ gam l := by
    unfold gam
    exact div_nonneg (by positivity) (by nlinarith)
  have hr0 : 0 ≤ rho l := by
    unfold rho
    exact div_nonneg zero_le_one (by nlinarith)
  have hpa : p a = n + j := hpb a ha
  have hfs := frobSum_alt hl.one_lt n j j' big halt p hpb hps a ha
  have hrhR : (rh : ℝ) ≤ j' := by exact_mod_cast hrh
  have hD : l1 a - l2 a = (p a : ℝ) / ((l : ℝ) - 1) - frobSum l p a := hDET
  have hA : l2 a ≤ ((n + j + j' : ℕ) - (rh : ℝ) - p a) / ((l : ℝ) - 1) := hAi
  rw [hpa, hfs, div_eq_mul_one_div, hu] at hD
  rw [hpa, div_eq_mul_one_div, hu] at hA
  push_cast at hD hA
  have hxi : xInert l (n + j + j') j' rh = (((n + j + j' : ℕ) : ℝ) - j' - rh) * gam l + ((j' : ℝ) - rh) * rho l := by
    unfold xInert
    rw [div_eq_mul_one_div, hu]
    push_cast
    ring
  have hlen : lenCoker v α ≤ (xInert l (n + j + j') j' rh : WithTop ℝ) := by
    have h3 : lenCoker v α = (l1 a : WithTop ℝ) := hAiii
    rw [h3]
    refine WithTop.coe_le_coe.mpr ?_
    rw [hxi]
    push_cast
    nlinarith
  refine ⟨⟨hlen, hxi, ?_⟩, ch_minor v hv S W hSW α _ hlen⟩
  rw [hxi, div_eq_mul_one_div, hu]
  push_cast
  have e1 := mul_nonneg (Nat.cast_nonneg (α := ℝ) rh) hg0
  have e2 := mul_nonneg (Nat.cast_nonneg (α := ℝ) j') hg0
  have e3 := mul_nonneg (Nat.cast_nonneg (α := ℝ) j) hr0
  have e4 := mul_nonneg (Nat.cast_nonneg (α := ℝ) rh) hr0
  nlinarith

theorem ch_split (v : AddValuation R (WithTop ℝ)) (hv : ∀ x, 0 ≤ v x)
    {d : ℕ} (hd : d ≠ 0) (l : ℕ) (hl : l.Prime) (hlodd : Odd l)
    (r n j j' rh h P : ℕ) (hP : P + j' = r) (hh : h + rh = r) (hrh : rh ≤ j')
    (p : ZMod d → ℕ) (hp : ∀ τ, p τ = P)
    (a : ZMod d) (α : Matrix (Fin (p a)) (Fin h) R)
    (S : Matrix (Fin n) (Fin (p a)) R) (W : Matrix (Fin (p a)) (Fin n) R) (hSW : S * W = 1)
    (l1 l2 : ZMod d → ℝ) (hDET : CorDET l p l1 l2 a) (hAi : ThmAi l r rh p l2 a)
    (hAiii : ThmAiii v α (l1 a)) :
    (lenCoker v α ≤ ((((j' : ℝ) - rh) / ((l : ℝ) - 1) : ℝ) : WithTop ℝ) ∧
      ((j' : ℝ) - rh) / ((l : ℝ) - 1) ≤ ((j : ℝ) + j') / ((l : ℝ) - 1)) ∧
    ∃ f : Fin n → Fin h, StrictMono f ∧
      v (Matrix.of fun k c => (S * α) c (f k)).det ≤ lenCoker v α ∧
      ∀ (F : Type) [CommRing F] [Algebra R F] (D : Fin n → Fin n → Derivation R F F)
        (χ : Fin n → F) (ev : F →ₐ[R] R),
        (∀ ρ c σ, D ρ c (χ σ) = (if σ = ρ then (S * α) c (f ρ) else 0) • χ σ) →
        (∀ σ, ev (χ σ) = 1) →
        ∀ y : ℕ,
          ev (((detOp fun ρ c => (D ρ c : F →ₗ[R] F)) ^ y) (∏ σ, χ σ)) =
              (Matrix.of fun k c => (S * α) c (f k)).det ^ y ∧
            v ((Matrix.of fun k c => (S * α) c (f k)).det ^ y) ≤
              (((y : ℝ) * (((j' : ℝ) - rh) / ((l : ℝ) - 1)) : ℝ) : WithTop ℝ) := by
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.one_lt
  have hl0 : (0 : ℝ) < (l : ℝ) - 1 := by linarith
  have hfs := frobSum_const hl.one_lt P p hp a
  have hD : l1 a - l2 a = (p a : ℝ) / ((l : ℝ) - 1) - frobSum l p a := hDET
  have hA : l2 a ≤ ((r : ℝ) - rh - p a) / ((l : ℝ) - 1) := hAi
  rw [hp, hfs, sub_self] at hD
  rw [hp] at hA
  have hPR : (P : ℝ) + j' = r := by exact_mod_cast hP
  have hb : l1 a ≤ ((j' : ℝ) - rh) / ((l : ℝ) - 1) := by
    have : (r : ℝ) - rh - P = (j' : ℝ) - rh := by linarith
    rw [this] at hA
    linarith
  have hlen : lenCoker v α ≤ ((((j' : ℝ) - rh) / ((l : ℝ) - 1) : ℝ) : WithTop ℝ) := by
    have h3 : lenCoker v α = (l1 a : WithTop ℝ) := hAiii
    rw [h3]
    exact WithTop.coe_le_coe.mpr hb
  refine ⟨⟨hlen, ?_⟩, ch_minor v hv S W hSW α _ hlen⟩
  apply div_le_div_of_nonneg_right _ hl0.le
  have : (0 : ℝ) ≤ rh := Nat.cast_nonneg rh
  have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  linarith

end Main

end Formalism.L2.FormalSeriesBounds.S4
