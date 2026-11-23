import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHDef

noncomputable section

open Matrix Finset
open scoped ComplexConjugate

namespace PI.SchurPlaces.LeviLA

open Formalism.L2.SG.HidaSetting

variable {n : ℕ} (ε : Fin n → Bool)

theorem hJ_add_right (x y y' : Fin n → ℂ) : hJ ε x (y + y') = hJ ε x y + hJ ε x y' := by
  unfold hJ; rw [Matrix.mulVec_add, dotProduct_add]

theorem hJ_add_left (x x' y : Fin n → ℂ) : hJ ε (x + x') y = hJ ε x y + hJ ε x' y := by
  unfold hJ; rw [star_add, add_dotProduct]

theorem hJ_sub_right' (x y y' : Fin n → ℂ) : hJ ε x (y - y') = hJ ε x y - hJ ε x y' := by
  unfold hJ; rw [Matrix.mulVec_sub, dotProduct_sub]

theorem hJ_sub_left' (x x' y : Fin n → ℂ) : hJ ε (x - x') y = hJ ε x y - hJ ε x' y := by
  unfold hJ; rw [star_sub, sub_dotProduct]

theorem hJ_smul_right (c : ℂ) (x y : Fin n → ℂ) : hJ ε x (c • y) = c * hJ ε x y := by
  unfold hJ; rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem hJ_smul_left (c : ℂ) (x y : Fin n → ℂ) : hJ ε (c • x) y = conj c * hJ ε x y := by
  unfold hJ; rw [star_smul, smul_dotProduct, smul_eq_mul]; rfl

theorem hJ_sum_right {ι : Type*} (s : Finset ι) (x : Fin n → ℂ) (y : ι → Fin n → ℂ) :
    hJ ε x (∑ i ∈ s, y i) = ∑ i ∈ s, hJ ε x (y i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hJ]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hJ_add_right, ih]

theorem hJ_sum_left {ι : Type*} (s : Finset ι) (x : ι → Fin n → ℂ) (y : Fin n → ℂ) :
    hJ ε (∑ i ∈ s, x i) y = ∑ i ∈ s, hJ ε (x i) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hJ]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hJ_add_left, ih]

theorem hJ_zero_right (x : Fin n → ℂ) : hJ ε x 0 = 0 := by
  simp [hJ]

private theorem hJ_conj_lemma (x y : Fin n → ℂ) : star (hJ ε x y) = hJ ε y x := by
  unfold hJ Formalism.REAL.Jm
  simp only [Matrix.mulVec_diagonal, dotProduct, star_sum, star_mul', star_star, Pi.star_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp [mul_comm]

theorem hJ_swap {x y : Fin n → ℂ} (h : hJ ε x y = 0) : hJ ε y x = 0 := by
  rw [← hJ_conj_lemma, h, star_zero]

theorem hJ_mulVec (A : Matrix (Fin n) (Fin n) ℂ) (x y : Fin n → ℂ) :
    hJ ε (A *ᵥ x) (A *ᵥ y) = star x ⬝ᵥ ((Aᴴ * Formalism.REAL.Jm ε * A) *ᵥ y) := by
  unfold hJ
  rw [Matrix.star_mulVec, Matrix.mulVec_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    Matrix.mul_assoc]

theorem unitary_of_hJ (A : Matrix (Fin n) (Fin n) ℂ) (h : ∀ x y, hJ ε (A *ᵥ x) (A *ᵥ y) = hJ ε x y) :
    Aᴴ * Formalism.REAL.Jm ε * A = Formalism.REAL.Jm ε := by
  ext i j
  have := h (Pi.single i 1) (Pi.single j 1)
  rw [hJ_mulVec] at this
  unfold hJ at this
  simpa [Matrix.mulVec_single_one, Pi.star_single] using this

variable {r k : ℕ}

structure Frame (e f : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (w : Fin k → Fin n → ℂ) : Prop where
  ee : ∀ a b, hJ ε (e a) (e b) = 0
  ef : ∀ a b, hJ ε (e a) (f b) = if a = b then 1 else 0
  ff : ∀ a b, hJ ε (f a) (f b) = 0
  ez : ∀ a, hJ ε (e a) z = 0
  fz : ∀ a, hJ ε (f a) z = 0
  ew : ∀ a b, hJ ε (e a) (w b) = 0
  fw : ∀ a b, hJ ε (f a) (w b) = 0
  zw : ∀ b, hJ ε z (w b) = 0
  ww : ∀ a b, hJ ε (w a) (w b) = if a = b then 1 else 0
  zz : hJ ε z z ≠ 0
  card : r + r + 1 + k = n

variable {ε} {e f : Fin r → Fin n → ℂ} {z : Fin n → ℂ} {w : Fin k → Fin n → ℂ}

abbrev Xs (e : Fin r → Fin n → ℂ) : Submodule ℂ (Fin n → ℂ) := Submodule.span ℂ (Set.range e)

theorem spanLt_top (e : Fin r → Fin n → ℂ) : spanLt e r = Xs e := by
  unfold spanLt
  congr 1
  ext v
  simp

theorem spanLt_le (e : Fin r → Fin n → ℂ) (a : ℕ) : spanLt e a ≤ Xs e := Submodule.span_mono (Set.image_subset_range _ _)

theorem e_mem (e : Fin r → Fin n → ℂ) (a : Fin r) : e a ∈ Xs e := Submodule.subset_span (Set.mem_range_self a)

theorem hJ_X_left {x p : Fin n → ℂ} (hx : x ∈ Xs e) (hp : ∀ a, hJ ε (e a) p = 0) : hJ ε x p = 0 := by
  induction hx using Submodule.span_induction with
  | mem v hv => obtain ⟨a, rfl⟩ := hv; exact hp a
  | zero => simp [hJ]
  | add u v _ _ hu hv => rw [hJ_add_left, hu, hv, add_zero]
  | smul c u _ hu => rw [hJ_smul_left, hu, mul_zero]

theorem hJ_X_right {x p : Fin n → ℂ} (hx : x ∈ Xs e) (hp : ∀ a, hJ ε p (e a) = 0) : hJ ε p x = 0 := by
  induction hx using Submodule.span_induction with
  | mem v hv => obtain ⟨a, rfl⟩ := hv; exact hp a
  | zero => exact hJ_zero_right ε p
  | add u v _ _ hu hv => rw [hJ_add_right, hu, hv, add_zero]
  | smul c u _ hu => rw [hJ_smul_right, hu, mul_zero]

def cmb (e f : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (w : Fin k → Fin n → ℂ) (α β : Fin r → ℂ) (γ : ℂ)
    (δ : Fin k → ℂ) : Fin n → ℂ :=
  ∑ a, α a • e a + ∑ a, β a • f a + γ • z + ∑ b, δ b • w b

theorem hJ_cmb (p : Fin n → ℂ) (α β : Fin r → ℂ) (γ : ℂ) (δ : Fin k → ℂ) :
    hJ ε p (cmb e f z w α β γ δ) = ∑ a, α a * hJ ε p (e a) + ∑ a, β a * hJ ε p (f a) + γ * hJ ε p z +
      ∑ b, δ b * hJ ε p (w b) := by
  simp only [cmb, hJ_add_right, hJ_sum_right, hJ_smul_right]

theorem cmb_e (H : Frame ε e f z w) (α β : Fin r → ℂ) (γ : ℂ) (δ : Fin k → ℂ) (c : Fin r) :
    hJ ε (e c) (cmb e f z w α β γ δ) = β c := by
  rw [hJ_cmb]
  simp [H.ee, H.ef, H.ez, H.ew]

theorem cmb_f (H : Frame ε e f z w) (α β : Fin r → ℂ) (γ : ℂ) (δ : Fin k → ℂ) (c : Fin r) :
    hJ ε (f c) (cmb e f z w α β γ δ) = α c := by
  rw [hJ_cmb]
  have h1 : ∀ a, hJ ε (f c) (e a) = if a = c then 1 else 0 := fun a => by
    rw [← hJ_conj_lemma, H.ef]; split_ifs <;> simp
  have h2 : ∀ a, hJ ε (f c) (f a) = 0 := fun a => H.ff c a
  simp [h1, h2, H.fz, H.fw]

theorem hermitian_combination_z (H : Frame ε e f z w) (α β : Fin r → ℂ) (γ : ℂ) (δ : Fin k → ℂ) :
    hJ ε z (cmb e f z w α β γ δ) = γ * hJ ε z z := by
  rw [hJ_cmb]
  have h1 : ∀ a, hJ ε z (e a) = 0 := fun a => by rw [← hJ_conj_lemma, H.ez, star_zero]
  have h2 : ∀ a, hJ ε z (f a) = 0 := fun a => by rw [← hJ_conj_lemma, H.fz, star_zero]
  simp [h1, h2, H.zw]

theorem cmb_w (H : Frame ε e f z w) (α β : Fin r → ℂ) (γ : ℂ) (δ : Fin k → ℂ) (c : Fin k) :
    hJ ε (w c) (cmb e f z w α β γ δ) = δ c := by
  rw [hJ_cmb]
  have h1 : ∀ a, hJ ε (w c) (e a) = 0 := fun a => by rw [← hJ_conj_lemma, H.ew, star_zero]
  have h2 : ∀ a, hJ ε (w c) (f a) = 0 := fun a => by rw [← hJ_conj_lemma, H.fw, star_zero]
  have h3 : hJ ε (w c) z = 0 := by rw [← hJ_conj_lemma, H.zw, star_zero]
  simp [h1, h2, h3, H.ww]

theorem frame_span (H : Frame ε e f z w) (y : Fin n → ℂ) :
    ∃ α β γ δ, y = cmb e f z w α β γ δ := by
  classical
  let Φ : ((Fin r → ℂ) × (Fin r → ℂ) × ℂ × (Fin k → ℂ)) →ₗ[ℂ] (Fin n → ℂ) :=
    { toFun := fun p => cmb e f z w p.1 p.2.1 p.2.2.1 p.2.2.2
      map_add' := fun p q => by
        simp only [cmb, Prod.fst_add, Prod.snd_add, Pi.add_apply, add_smul, Finset.sum_add_distrib]
        abel
      map_smul' := fun a p => by
        simp only [cmb, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, mul_smul,
          ← Finset.smul_sum, RingHom.id_apply, smul_add] }
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨α, β, γ, δ⟩ hp
    have h0 : cmb e f z w α β γ δ = 0 := hp
    have hα : α = 0 := funext fun c => by
      have := cmb_f H α β γ δ c
      rw [h0, hJ_zero_right] at this; exact this.symm
    have hβ : β = 0 := funext fun c => by
      have := cmb_e H α β γ δ c
      rw [h0, hJ_zero_right] at this; exact this.symm
    have hγ : γ = 0 := by
      have := hermitian_combination_z H α β γ δ
      rw [h0, hJ_zero_right] at this
      exact (mul_eq_zero.1 this.symm).resolve_right H.zz
    have hδ : δ = 0 := funext fun c => by
      have := cmb_w H α β γ δ c
      rw [h0, hJ_zero_right] at this; exact this.symm
    subst hα hβ hγ hδ
    rfl
  have hdim : Module.finrank ℂ ((Fin r → ℂ) × (Fin r → ℂ) × ℂ × (Fin k → ℂ)) =
      Module.finrank ℂ (Fin n → ℂ) := by
    simp only [Module.finrank_prod, Module.finrank_fin_fun, Module.finrank_self]
    have := H.card
    omega
  obtain ⟨p, hp⟩ := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).1 hinj y
  exact ⟨p.1, p.2.1, p.2.2.1, p.2.2.2, hp.symm⟩

theorem perp_e (H : Frame ε e f z w) (y : Fin n → ℂ) (hy : ∀ a, hJ ε (e a) y = 0) :
    y - (hJ ε z y / hJ ε z z) • z - ∑ b, hJ ε (w b) y • w b ∈ Xs e := by
  obtain ⟨α, β, γ, δ, rfl⟩ := frame_span H y
  have hβ : β = 0 := funext fun c => by rw [← cmb_e H α β γ δ c]; exact hy c
  subst hβ
  have hz : γ * hJ ε z z / hJ ε z z = γ := mul_div_cancel_right₀ _ H.zz
  simp only [hermitian_combination_z H, cmb_w H, hz]
  have e1 : cmb e f z w α 0 γ δ - γ • z - ∑ b, δ b • w b = ∑ a, α a • e a := by
    simp only [cmb, Pi.zero_apply, zero_smul, Finset.sum_const_zero, add_zero]
    abel
  rw [e1]
  exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (e_mem e a)

theorem perp_efz (H : Frame ε e f z w) (y : Fin n → ℂ) (hy : ∀ a, hJ ε (e a) y = 0 ∧ hJ ε (f a) y = 0)
    (hz : hJ ε z y = 0) : y = ∑ b, hJ ε (w b) y • w b := by
  obtain ⟨α, β, γ, δ, rfl⟩ := frame_span H y
  have hβ : β = 0 := funext fun c => by rw [← cmb_e H α β γ δ c]; exact (hy c).1
  have hα : α = 0 := funext fun c => by rw [← cmb_f H α β γ δ c]; exact (hy c).2
  have hγ : γ = 0 := by
    have := hermitian_combination_z H α β γ δ
    rw [hz] at this
    exact (mul_eq_zero.1 this.symm).resolve_right H.zz
  subst hα hβ hγ
  simp only [cmb_w H]
  simp [cmb]

section U

variable (U : (Matrix (Fin n) (Fin n) ℂ)ˣ)

theorem hJ_U (hU : (U : Matrix (Fin n) (Fin n) ℂ)ᴴ * Formalism.REAL.Jm ε * U = Formalism.REAL.Jm ε) (x y : Fin n → ℂ) :
    hJ ε ((U : Matrix (Fin n) (Fin n) ℂ) *ᵥ x) ((U : Matrix (Fin n) (Fin n) ℂ) *ᵥ y) = hJ ε x y := by
  rw [hJ_mulVec, hU]; rfl

theorem U_X (hS : InS e z (U : Matrix (Fin n) (Fin n) ℂ)) {x : Fin n → ℂ} (hx : x ∈ Xs e) :
    (U : Matrix (Fin n) (Fin n) ℂ) *ᵥ x ∈ Xs e := by
  induction hx using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨a, rfl⟩ := hv
    have h1 := spanLt_le e a.1 (hS.1 a)
    have e1 : (U : Matrix (Fin n) (Fin n) ℂ) *ᵥ e a =
        ((U : Matrix (Fin n) (Fin n) ℂ) - 1) *ᵥ e a + e a := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_add_cancel]
    rw [e1]
    exact Submodule.add_mem _ h1 (e_mem e a)
  | zero => rw [Matrix.mulVec_zero]; exact Submodule.zero_mem _
  | add u v _ _ hu hv => rw [Matrix.mulVec_add]; exact Submodule.add_mem _ hu hv
  | smul c u _ hu => rw [Matrix.mulVec_smul]; exact Submodule.smul_mem _ _ hu

theorem U_X_surj (hS : InS e z (U : Matrix (Fin n) (Fin n) ℂ)) {x : Fin n → ℂ} (hx : x ∈ Xs e) :
    ∃ x' ∈ Xs e, (U : Matrix (Fin n) (Fin n) ℂ) *ᵥ x' = x := by
  set M := (Xs e).map (Matrix.mulVecLin (U : Matrix (Fin n) (Fin n) ℂ)) with hM
  have key : ∀ m : ℕ, spanLt e m ≤ M := by
    intro m
    induction m with
    | zero =>
      unfold spanLt
      rw [Submodule.span_le]
      rintro v ⟨b, hb, rfl⟩
      exact absurd hb (Nat.not_lt_zero _)
    | succ m ih =>
      unfold spanLt
      rw [Submodule.span_le]
      rintro v ⟨b, hb, rfl⟩
      by_cases hbm : b.1 < m
      · exact ih (Submodule.subset_span ⟨b, hbm, rfl⟩)
      · have hb' : b.1 = m := by
          have : b.1 < m + 1 := hb
          omega
        have h1 : ((U : Matrix (Fin n) (Fin n) ℂ) - 1) *ᵥ e b ∈ M := by
          have := hS.1 b
          rw [hb'] at this
          exact ih this
        have h2 : (U : Matrix (Fin n) (Fin n) ℂ) *ᵥ e b ∈ M := ⟨e b, e_mem e b, rfl⟩
        have e1 : e b = (U : Matrix (Fin n) (Fin n) ℂ) *ᵥ e b -
            ((U : Matrix (Fin n) (Fin n) ℂ) - 1) *ᵥ e b := by
          rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_sub_cancel]
        rw [e1]
        exact M.sub_mem h2 h1
  have hx' : x ∈ M := by
    rw [← spanLt_top] at hx
    exact key r hx
  obtain ⟨x', hx', hxe⟩ := hx'
  exact ⟨x', hx', hxe⟩

def Mm (w : Fin k → Fin n → ℂ) (a b : Fin k) : ℂ := hJ ε (w a) ((U : Matrix (Fin n) (Fin n) ℂ) *ᵥ w b)

def uu (w : Fin k → Fin n → ℂ) (b : Fin k) : Fin n → ℂ := ∑ a, Mm (ε := ε) U w a b • w a

def Vm (w : Fin k → Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  1 + ∑ b, vecMulVec (uu (ε := ε) U w b - w b) (star (w b) ᵥ* Formalism.REAL.Jm ε)

variable {U}

theorem Uw (H : Frame ε e f z w) (hU : (U : Matrix (Fin n) (Fin n) ℂ)ᴴ * Formalism.REAL.Jm ε * U = Formalism.REAL.Jm ε)
    (hS : InS e z (U : Matrix (Fin n) (Fin n) ℂ)) (b : Fin k) :
    (U : Matrix (Fin n) (Fin n) ℂ) *ᵥ w b - uu (ε := ε) U w b ∈ Xs e := by
  have hUe : ∀ a, hJ ε (e a) ((U : Matrix (Fin n) (Fin n) ℂ) *ᵥ w b) = 0 := by
    intro a
    obtain ⟨x', hx', hxe⟩ := U_X_surj U hS (e_mem e a)
    rw [← hxe, hJ_U U hU]
    exact hJ_X_left hx' (fun c => H.ew c b)
  have hUz : hJ ε z ((U : Matrix (Fin n) (Fin n) ℂ) *ᵥ w b) = 0 := by
    have h0 : ((U : Matrix (Fin n) (Fin n) ℂ) - 1) *ᵥ z ∈ Xs e := by
      rw [← spanLt_top]; exact hS.2
    obtain ⟨x1, hx1, hx1e⟩ := U_X_surj U hS h0
    have e1 : z = (U : Matrix (Fin n) (Fin n) ℂ) *ᵥ (z - x1) := by
      rw [Matrix.mulVec_sub, hx1e, Matrix.sub_mulVec, Matrix.one_mulVec, sub_sub_cancel]
    rw [e1, hJ_U U hU, hJ_sub_left', H.zw, hJ_X_left hx1 (fun c => H.ew c b), sub_zero]
  have := perp_e H _ hUe
  rw [hUz, zero_div, zero_smul, sub_zero] at this
  unfold uu Mm
  exact this

theorem uu_on (H : Frame ε e f z w) (hU : (U : Matrix (Fin n) (Fin n) ℂ)ᴴ * Formalism.REAL.Jm ε * U = Formalism.REAL.Jm ε)
    (hS : InS e z (U : Matrix (Fin n) (Fin n) ℂ)) (b c : Fin k) :
    hJ ε (uu (ε := ε) U w b) (uu (ε := ε) U w c) = if b = c then 1 else 0 := by
  have hX : ∀ b, (U : Matrix (Fin n) (Fin n) ℂ) *ᵥ w b - uu (ε := ε) U w b ∈ Xs e := Uw H hU hS
  have hwX : ∀ a {x}, x ∈ Xs e → hJ ε (w a) x = 0 := fun a x hx =>
    hJ_X_right hx (fun c => by rw [← hJ_conj_lemma, H.ew, star_zero])
  have hXw : ∀ a {x}, x ∈ Xs e → hJ ε x (w a) = 0 := fun a x hx => hJ_X_left hx (fun c => H.ew c a)
  have huX : ∀ b {x}, x ∈ Xs e → hJ ε (uu (ε := ε) U w b) x = 0 := fun b x hx => by
    simp only [uu, hJ_sum_left, hJ_smul_left, hwX _ hx, mul_zero, Finset.sum_const_zero]
  have hXu : ∀ b {x}, x ∈ Xs e → hJ ε x (uu (ε := ε) U w b) = 0 := fun b x hx => by
    simp only [uu, hJ_sum_right, hJ_smul_right, hXw _ hx, mul_zero, Finset.sum_const_zero]
  have hXX : ∀ {x y}, x ∈ Xs e → y ∈ Xs e → hJ ε x y = 0 := fun hx hy =>
    hJ_X_left hx (fun a => hJ_X_right hy (fun c => H.ee a c))
  have h1 := hJ_U U hU (w b) (w c)
  rw [H.ww] at h1
  have eb : (U : Matrix (Fin n) (Fin n) ℂ) *ᵥ w b = uu (ε := ε) U w b +
      ((U : Matrix (Fin n) (Fin n) ℂ) *ᵥ w b - uu (ε := ε) U w b) := by abel
  have ec : (U : Matrix (Fin n) (Fin n) ℂ) *ᵥ w c = uu (ε := ε) U w c +
      ((U : Matrix (Fin n) (Fin n) ℂ) *ᵥ w c - uu (ε := ε) U w c) := by abel
  rw [eb, ec, hJ_add_left, hJ_add_right, hJ_add_right, huX _ (hX c), hXu _ (hX b),
    hXX (hX b) (hX c)] at h1
  simpa using h1

variable (U) in
theorem Vm_mulVec (w : Fin k → Fin n → ℂ) (y : Fin n → ℂ) :
    Vm (ε := ε) U w *ᵥ y = y + ∑ b, hJ ε (w b) y • (uu (ε := ε) U w b - w b) := by
  have hs : ∀ (s : Finset (Fin k)) (A : Fin k → Matrix (Fin n) (Fin n) ℂ),
      (∑ b ∈ s, A b) *ᵥ y = ∑ b ∈ s, A b *ᵥ y := by
    intro s A
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Matrix.add_mulVec, ih]
  have hv : ∀ a b : Fin n → ℂ, vecMulVec a b *ᵥ y = (b ⬝ᵥ y) • a := by
    intro a b
    ext i
    simp [Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, Finset.sum_mul, mul_comm, mul_left_comm]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  unfold Vm
  rw [Matrix.add_mulVec, Matrix.one_mulVec, hs]
  congr 1
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [hv, ← Matrix.dotProduct_mulVec]
  rfl

theorem Vm_fix (p : Fin n → ℂ) (hp : ∀ b, hJ ε (w b) p = 0) : Vm (ε := ε) U w *ᵥ p = p := by
  rw [Vm_mulVec]
  simp [hp]

theorem Vm_w (H : Frame ε e f z w) (c : Fin k) : Vm (ε := ε) U w *ᵥ w c = uu (ε := ε) U w c := by
  rw [Vm_mulVec]
  simp [H.ww]

theorem hJ_orth (q : Fin k → Fin n → ℂ) (hq : ∀ a b, hJ ε (q a) (q b) = if a = b then 1 else 0)
    (p p' : Fin n → ℂ) (hp : ∀ b, hJ ε p (q b) = 0) (hp' : ∀ b, hJ ε (q b) p' = 0) (c d : Fin k → ℂ) :
    hJ ε (p + ∑ b, c b • q b) (p' + ∑ b, d b • q b) = hJ ε p p' + ∑ b, conj (c b) * d b := by
  simp [hJ_add_left, hJ_add_right, hJ_sum_left, hJ_sum_right, hJ_smul_left, hJ_smul_right, hp, hp',
    hq]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

theorem Vm_hJ (H : Frame ε e f z w) (hU : (U : Matrix (Fin n) (Fin n) ℂ)ᴴ * Formalism.REAL.Jm ε * U = Formalism.REAL.Jm ε)
    (hS : InS e z (U : Matrix (Fin n) (Fin n) ℂ)) (x y : Fin n → ℂ) :
    hJ ε (Vm (ε := ε) U w *ᵥ x) (Vm (ε := ε) U w *ᵥ y) = hJ ε x y := by
  have hww := H.ww
  have huu := uu_on H hU hS
  have hperp : ∀ v : Fin n → ℂ, ∀ c, hJ ε (w c) (v - ∑ b, hJ ε (w b) v • w b) = 0 := by
    intro v c
    rw [hJ_sub_right', hJ_sum_right]
    simp [hJ_smul_right, hww]
  have hperp' : ∀ v : Fin n → ℂ, ∀ c, hJ ε (v - ∑ b, hJ ε (w b) v • w b) (w c) = 0 := fun v c => by
    rw [← hJ_conj_lemma, hperp, star_zero]
  have hpu : ∀ v : Fin n → ℂ, ∀ c, hJ ε (v - ∑ b, hJ ε (w b) v • w b) (uu (ε := ε) U w c) = 0 :=
    fun v c => by
      simp only [uu, hJ_sum_right, hJ_smul_right, hperp', mul_zero, Finset.sum_const_zero]
  have hup : ∀ v : Fin n → ℂ, ∀ c, hJ ε (uu (ε := ε) U w c) (v - ∑ b, hJ ε (w b) v • w b) = 0 :=
    fun v c => by
      simp only [uu, hJ_sum_left, hJ_smul_left, hperp, mul_zero, Finset.sum_const_zero]
  have eV : ∀ v : Fin n → ℂ, Vm (ε := ε) U w *ᵥ v =
      (v - ∑ b, hJ ε (w b) v • w b) + ∑ b, hJ ε (w b) v • uu (ε := ε) U w b := fun v => by
    rw [Vm_mulVec]
    simp only [smul_sub, Finset.sum_sub_distrib]
    abel
  have ev : ∀ v : Fin n → ℂ, v = (v - ∑ b, hJ ε (w b) v • w b) + ∑ b, hJ ε (w b) v • w b :=
    fun v => by abel
  calc hJ ε (Vm (ε := ε) U w *ᵥ x) (Vm (ε := ε) U w *ᵥ y)
      = hJ ε (x - ∑ b, hJ ε (w b) x • w b) (y - ∑ b, hJ ε (w b) y • w b) +
          ∑ b, starRingEnd ℂ (hJ ε (w b) x) * hJ ε (w b) y := by
        rw [eV, eV]
        exact hJ_orth _ huu _ _ (hpu x) (hup y) _ _
    _ = hJ ε ((x - ∑ b, hJ ε (w b) x • w b) + ∑ b, hJ ε (w b) x • w b)
          ((y - ∑ b, hJ ε (w b) y • w b) + ∑ b, hJ ε (w b) y • w b) :=
        (hJ_orth _ hww _ _ (hperp' x) (hperp y) _ _).symm
    _ = hJ ε x y := by rw [← ev, ← ev]

end U

theorem levi_place (H : Frame ε e f z w) (U : (Matrix (Fin n) (Fin n) ℂ)ˣ)
    (hU : (U : Matrix (Fin n) (Fin n) ℂ)ᴴ * Formalism.REAL.Jm ε * U = Formalism.REAL.Jm ε)
    (hS : InS e z (U : Matrix (Fin n) (Fin n) ℂ)) :
    ∃ V : (Matrix (Fin n) (Fin n) ℂ)ˣ, (V : Matrix (Fin n) (Fin n) ℂ)ᴴ * Formalism.REAL.Jm ε * V = Formalism.REAL.Jm ε ∧
      (∀ a, (V : Matrix (Fin n) (Fin n) ℂ) *ᵥ e a = e a) ∧ (∀ a, (V : Matrix (Fin n) (Fin n) ℂ) *ᵥ f a = f a) ∧
      (V : Matrix (Fin n) (Fin n) ℂ) *ᵥ z = z ∧
      (∀ a b, hJ ε (w a) ((V : Matrix (Fin n) (Fin n) ℂ) *ᵥ w b) =
        hJ ε (w a) ((U : Matrix (Fin n) (Fin n) ℂ) *ᵥ w b)) ∧
      InN ε e z (((V⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) * U) := by
  have hVJ : (Vm (ε := ε) U w)ᴴ * Formalism.REAL.Jm ε * Vm (ε := ε) U w = Formalism.REAL.Jm ε :=
    unitary_of_hJ ε _ (Vm_hJ H hU hS)
  have hJJ : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
    unfold Formalism.REAL.Jm
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs <;> norm_num
  have hleft : (Formalism.REAL.Jm ε * (Vm (ε := ε) U w)ᴴ * Formalism.REAL.Jm ε) * Vm (ε := ε) U w = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (Vm (ε := ε) U w)ᴴ, hVJ, hJJ]
  have hright : Vm (ε := ε) U w * (Formalism.REAL.Jm ε * (Vm (ε := ε) U w)ᴴ * Formalism.REAL.Jm ε) = 1 :=
    by first
      | exact mul_eq_one_comm.1 hleft
      | exact (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _)).1 hleft
  have hfe : ∀ a, Vm (ε := ε) U w *ᵥ e a = e a := fun a =>
    Vm_fix _ (fun b => by rw [← hJ_conj_lemma, H.ew, star_zero])
  refine ⟨⟨Vm (ε := ε) U w, Formalism.REAL.Jm ε * (Vm (ε := ε) U w)ᴴ * Formalism.REAL.Jm ε, hright, hleft⟩,
    hVJ, hfe, fun a => Vm_fix _ (fun b => by rw [← hJ_conj_lemma, H.fw, star_zero]),
    Vm_fix _ (fun b => by rw [← hJ_conj_lemma, H.zw, star_zero]), ?_, ?_⟩
  · intro a b
    show hJ ε (w a) (Vm (ε := ε) U w *ᵥ w b) = _
    rw [Vm_w H]
    unfold uu Mm
    rw [hJ_sum_right]
    simp [hJ_smul_right, H.ww]
  · show InN ε e z ((Formalism.REAL.Jm ε * (Vm (ε := ε) U w)ᴴ * Formalism.REAL.Jm ε) *
      (U : Matrix (Fin n) (Fin n) ℂ))
    have hinv : ∀ v, Vm (ε := ε) U w *ᵥ v = v →
        (Formalism.REAL.Jm ε * (Vm (ε := ε) U w)ᴴ * Formalism.REAL.Jm ε) *ᵥ v = v := fun v hv => by
      conv_lhs => rw [← hv]
      rw [Matrix.mulVec_mulVec, hleft, Matrix.one_mulVec]
    have hXfix : ∀ x ∈ Xs e, (Formalism.REAL.Jm ε * (Vm (ε := ε) U w)ᴴ * Formalism.REAL.Jm ε) *ᵥ x = x := by
      intro x hx
      apply hinv
      induction hx using Submodule.span_induction with
      | mem v hv =>
        obtain ⟨a, rfl⟩ := hv
        exact hfe a
      | zero => exact Matrix.mulVec_zero _
      | add u v _ _ hu hv => rw [Matrix.mulVec_add, hu, hv]
      | smul c u _ hu => rw [Matrix.mulVec_smul, hu]
    have hz : (Formalism.REAL.Jm ε * (Vm (ε := ε) U w)ᴴ * Formalism.REAL.Jm ε) *ᵥ z = z :=
      hinv z (Vm_fix _ (fun b => by rw [← hJ_conj_lemma, H.zw, star_zero]))
    have huu : ∀ b, (Formalism.REAL.Jm ε * (Vm (ε := ε) U w)ᴴ * Formalism.REAL.Jm ε) *ᵥ uu (ε := ε) U w b = w b :=
      fun b => by rw [← Vm_w H b, Matrix.mulVec_mulVec, hleft, Matrix.one_mulVec]
    have hsub : ∀ v, ((Formalism.REAL.Jm ε * (Vm (ε := ε) U w)ᴴ * Formalism.REAL.Jm ε) *
        (U : Matrix (Fin n) (Fin n) ℂ) - 1) *ᵥ v =
        (Formalism.REAL.Jm ε * (Vm (ε := ε) U w)ᴴ * Formalism.REAL.Jm ε) *ᵥ ((U : Matrix (Fin n) (Fin n) ℂ) *ᵥ v) - v :=
      fun v => by rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_mulVec]
    have hUsub : ∀ v, ((U : Matrix (Fin n) (Fin n) ℂ) - 1) *ᵥ v = (U : Matrix (Fin n) (Fin n) ℂ) *ᵥ v - v :=
      fun v => by rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    have hzX : (U : Matrix (Fin n) (Fin n) ℂ) *ᵥ z - z ∈ Xs e := by
      rw [← hUsub, ← spanLt_top]; exact hS.2
    have hUz : (Formalism.REAL.Jm ε * (Vm (ε := ε) U w)ᴴ * Formalism.REAL.Jm ε) *ᵥ ((U : Matrix (Fin n) (Fin n) ℂ) *ᵥ z) =
        (U : Matrix (Fin n) (Fin n) ℂ) *ᵥ z := by
      have e1 : (U : Matrix (Fin n) (Fin n) ℂ) *ᵥ z = z + ((U : Matrix (Fin n) (Fin n) ℂ) *ᵥ z - z) := by abel
      rw [e1, Matrix.mulVec_add, hz, hXfix _ hzX]
    have hwb : ∀ b, (Formalism.REAL.Jm ε * (Vm (ε := ε) U w)ᴴ * Formalism.REAL.Jm ε) *ᵥ
        ((U : Matrix (Fin n) (Fin n) ℂ) *ᵥ w b) - w b =
        (U : Matrix (Fin n) (Fin n) ℂ) *ᵥ w b - uu (ε := ε) U w b := fun b => by
      have e1 : (U : Matrix (Fin n) (Fin n) ℂ) *ᵥ w b = uu (ε := ε) U w b +
          ((U : Matrix (Fin n) (Fin n) ℂ) *ᵥ w b - uu (ε := ε) U w b) := by abel
      conv_lhs => rw [e1]
      rw [Matrix.mulVec_add, huu, hXfix _ (Uw H hU hS b)]
      abel
    refine ⟨⟨fun a => ?_, ?_⟩, fun y hy => ?_⟩
    · rw [hsub]
      have hd := hS.1 a
      rw [hUsub] at hd
      rw [hXfix _ (U_X U hS (e_mem e a))]
      exact hd
    · rw [hsub, hUz, ← hUsub]
      exact hS.2
    · rw [hsub, spanLt_top]
      have hx := perp_e H y hy
      let D : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) :=
        Matrix.mulVecLin ((Formalism.REAL.Jm ε * (Vm (ε := ε) U w)ᴴ * Formalism.REAL.Jm ε) *
          (U : Matrix (Fin n) (Fin n) ℂ)) - LinearMap.id
      have hD : ∀ v, D v = (Formalism.REAL.Jm ε * (Vm (ε := ε) U w)ᴴ * Formalism.REAL.Jm ε) *ᵥ
          ((U : Matrix (Fin n) (Fin n) ℂ) *ᵥ v) - v := fun v => by
        simp only [D, LinearMap.sub_apply, Matrix.mulVecLin_apply, LinearMap.id_apply,
          Matrix.mulVec_mulVec]
      have hmem : ∀ v, D v ∈ Xs e → v ∈ (Xs e).comap D := fun v h => h
      have h1 : y - (hJ ε z y / hJ ε z z) • z - ∑ b, hJ ε (w b) y • w b ∈ (Xs e).comap D := by
        apply hmem
        rw [hD, hXfix _ (U_X U hS hx)]
        exact Submodule.sub_mem _ (U_X U hS hx) hx
      have h2 : z ∈ (Xs e).comap D := by
        apply hmem; rw [hD, hUz]; exact hzX
      have h3 : ∀ b, w b ∈ (Xs e).comap D := fun b => by
        apply hmem; rw [hD, hwb]; exact Uw H hU hS b
      have h4 : y ∈ (Xs e).comap D := by
        have h3' : ∑ b, hJ ε (w b) y • w b ∈ (Xs e).comap D :=
          Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ (hJ ε (w b) y) (h3 b)
        have := Submodule.add_mem _ (Submodule.add_mem _ h1
          (Submodule.smul_mem _ (hJ ε z y / hJ ε z z) h2)) h3'
        convert this using 1
        abel
      have h5 := h4
      rw [Submodule.mem_comap, hD] at h5
      exact h5

end PI.SchurPlaces.LeviLA
