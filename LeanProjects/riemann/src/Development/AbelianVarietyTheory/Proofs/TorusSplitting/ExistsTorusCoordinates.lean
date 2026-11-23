import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TorusAtDataPf

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.I2.TorusAtDataPf
open scoped ComplexConjugate

namespace GlobalTheory

namespace TorusCoord

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

open NumberField in
open scoped ComplexConjugate in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in

theorem _root_.GlobalTheory.TorusCoord.sum_emb_split {M : Type} [AddCommMonoid M] (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (F : (E →+* ℂ) → M) :
    ∑ σ, F σ = ∑ τ : X.Ψ, (F τ.1 + F (ComplexEmbedding.conjugate τ.1)) := by
  classical
  rw [Finset.sum_add_distrib, Finset.sum_coe_sort X.Ψ F,
    Finset.sum_coe_sort X.Ψ (fun τ => F (ComplexEmbedding.conjugate τ)),
    ← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ X.Ψ)]
  congr 1
  · congr 1
    ext σ
    simp
  · refine Finset.sum_nbij' ComplexEmbedding.conjugate ComplexEmbedding.conjugate ?_ ?_ ?_ ?_ ?_
    · intro σ hσ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
      exact (X.cmType _).mpr (by rwa [_root_.ReciprocityTheory.ChartRestriction.G.I2.TorusAtDataPf.conj_conj_X])
    · intro τ hτ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact (X.cmType τ).mp hτ
    · intro σ _
      exact _root_.ReciprocityTheory.ChartRestriction.G.I2.TorusAtDataPf.conj_conj_X σ
    · intro τ _
      exact _root_.ReciprocityTheory.ChartRestriction.G.I2.TorusAtDataPf.conj_conj_X τ
    · intro σ _
      rw [_root_.ReciprocityTheory.ChartRestriction.G.I2.TorusAtDataPf.conj_conj_X]

open Classical in

def dimOf (X : Data E r) (σ : E →+* ℂ) : ℕ := if σ ∈ X.Ψ then X.p0 else r - X.p0

theorem dimOf_mem (X : Data E r) {σ : E →+* ℂ} (h : σ ∈ X.Ψ) : dimOf X σ = X.p0 := by
  simp [dimOf, h]

theorem dimOf_not_mem (X : Data E r) {σ : E →+* ℂ} (h : σ ∉ X.Ψ) : dimOf X σ = r - X.p0 := by
  simp [dimOf, h]

open NumberField in
open scoped ComplexConjugate in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
theorem _root_.GlobalTheory.TorusCoord.conj_mem (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) {σ : E →+* ℂ} (h : σ ∉ X.Ψ) :
    ComplexEmbedding.conjugate σ ∈ X.Ψ :=
  (X.cmType _).mpr (by rwa [_root_.ReciprocityTheory.ChartRestriction.G.I2.TorusAtDataPf.conj_conj_X])

theorem dimOf_add (X : Data E r) (σ : E →+* ℂ) :
    dimOf X σ + dimOf X (ComplexEmbedding.conjugate σ) = r := by
  have := X.p0_le
  by_cases h : σ ∈ X.Ψ
  · rw [dimOf_mem X h, dimOf_not_mem X ((X.cmType σ).mp h)]; omega
  · rw [dimOf_not_mem X h, dimOf_mem X (conj_mem X h)]; omega

theorem card_idx (X : Data E r) : Fintype.card (Idx (dimOf X)) = X.Ψ.card * r := by
  rw [Fintype.card_sigma, sum_emb_split X]
  simp [dimOf_add]

open NumberField in
open scoped ComplexConjugate in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
theorem _root_.GlobalTheory.TorusCoord.c_pos (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (τ : X.Ψ) : 0 < X.c τ := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.c
  exact mul_pos two_pos (norm_pos_iff.mpr ((map_ne_zero _).mpr X.ξ0_ne))

def pr (X : Data E r) (e : X.Ψ → Fin r → (Fin r → ℂ)) (y : X.Ψ → Fin r → ℂ) (τ : X.Ψ) (b : Fin r) : ℂ :=
  (Real.sqrt (X.c τ) : ℂ) * hermC τ.1 X.Gm (y τ) (e τ b)

open NumberField in
open scoped ComplexConjugate in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
theorem _root_.GlobalTheory.TorusCoord.pr_add (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (e : X.Ψ → Fin r → (Fin r → ℂ)) (y y' : X.Ψ → Fin r → ℂ) (τ : X.Ψ)
    (b : Fin r) : _root_.GlobalTheory.TorusCoord.pr X e (y + y') τ b = _root_.GlobalTheory.TorusCoord.pr X e y τ b + _root_.GlobalTheory.TorusCoord.pr X e y' τ b := by
  simp only [_root_.GlobalTheory.TorusCoord.pr, Pi.add_apply, _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC_add_left]
  ring

theorem pr_smul (X : Data E r) (e : X.Ψ → Fin r → (Fin r → ℂ)) (t : X.Ψ → ℂ) (y : X.Ψ → Fin r → ℂ)
    (τ : X.Ψ) (b : Fin r) : pr X e (fun τ => t τ • y τ) τ b = t τ * pr X e y τ b := by
  simp only [pr, hermC_smul_left]; ring

open NumberField in
open scoped ComplexConjugate in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
theorem _root_.GlobalTheory.TorusCoord.pr_real_smul (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (e : X.Ψ → Fin r → (Fin r → ℂ)) (t : ℝ) (y : X.Ψ → Fin r → ℂ)
    (τ : X.Ψ) (b : Fin r) : _root_.GlobalTheory.TorusCoord.pr X e (t • y) τ b = (t : ℂ) * _root_.GlobalTheory.TorusCoord.pr X e y τ b := by
  simp only [_root_.GlobalTheory.TorusCoord.pr, Pi.smul_apply, ← Complex.coe_smul, _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC_smul_left]
  ring

open NumberField in
open scoped ComplexConjugate in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
theorem _root_.GlobalTheory.TorusCoord.lt_pos (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) {σ : E →+* ℂ} (h : σ ∈ X.Ψ) (a : Fin (_root_.GlobalTheory.TorusCoord.dimOf X σ)) : a.1 < r := by
  have ha : a.1 < X.p0 := lt_of_lt_of_eq a.2 (if_pos h)
  have := X.p0_le
  omega

open NumberField in
open scoped ComplexConjugate in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
theorem _root_.GlobalTheory.TorusCoord.lt_neg (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) {σ : E →+* ℂ} (h : σ ∉ X.Ψ) (a : Fin (_root_.GlobalTheory.TorusCoord.dimOf X σ)) :
    X.p0 + a.1 < r := by
  have ha : a.1 < r - X.p0 := lt_of_lt_of_eq a.2 (if_neg h)
  have := X.p0_le
  omega

open Classical in

def coord (X : Data E r) (e : X.Ψ → Fin r → (Fin r → ℂ)) (y : X.Ψ → Fin r → ℂ)
    (i : Idx (dimOf X)) : ℂ :=
  if h : i.1 ∈ X.Ψ then pr X e y ⟨i.1, h⟩ ⟨i.2.1, lt_pos X h i.2⟩
  else - conj (pr X e y ⟨ComplexEmbedding.conjugate i.1, conj_mem X h⟩ ⟨X.p0 + i.2.1, lt_neg X h i.2⟩)

def coordMap (X : Data E r) (e : X.Ψ → Fin r → (Fin r → ℂ)) :
    (X.Ψ → Fin r → ℂ) →ₗ[ℝ] Vsp (dimOf X) where
  toFun y := WithLp.toLp 2 (coord X e y)
  map_add' y y' := by
    ext i
    simp only [PiLp.add_apply, coord]
    split_ifs
    · rw [pr_add]
    · rw [pr_add, map_add]; ring
  map_smul' t y := by
    ext i
    simp only [PiLp.smul_apply, coord, RingHom.id_apply, Complex.real_smul]
    split_ifs
    · rw [pr_real_smul]
    · rw [pr_real_smul, map_mul, Complex.conj_ofReal]; ring

theorem coordMap_pos (X : Data E r) (e : X.Ψ → Fin r → (Fin r → ℂ)) (y : X.Ψ → Fin r → ℂ) (τ : X.Ψ)
    (a : Fin (dimOf X τ.1)) :
    coordMap X e y ⟨τ.1, a⟩ = pr X e y τ ⟨a.1, lt_pos X τ.2 a⟩ := by
  show coord X e y ⟨τ.1, a⟩ = _
  unfold coord
  rw [dif_pos τ.2]

theorem coordMap_neg (X : Data E r) (e : X.Ψ → Fin r → (Fin r → ℂ)) (y : X.Ψ → Fin r → ℂ) (τ : X.Ψ)
    (a : Fin (dimOf X (ComplexEmbedding.conjugate τ.1))) :
    coordMap X e y ⟨ComplexEmbedding.conjugate τ.1, a⟩ =
      - conj (pr X e y τ ⟨X.p0 + a.1, lt_neg X ((X.cmType _).mp τ.2) a⟩) := by
  show coord X e y ⟨ComplexEmbedding.conjugate τ.1, a⟩ = _
  unfold coord
  rw [dif_neg ((X.cmType _).mp τ.2)]
  have : (⟨ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ.1),
      conj_mem X ((X.cmType _).mp τ.2)⟩ : X.Ψ) = τ := Subtype.ext (conj_conj_X _)
  simp only [this]

theorem coordMap_injective (X : Data E r) (e : X.Ψ → Fin r → (Fin r → ℂ))
    (he : ∀ τ a b, hermC τ.1 X.Gm (e τ a) (e τ b) =
      if a = b then ((ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 a : ℝ) : ℂ) else 0) :
    Function.Injective (coordMap X e) := by
  rw [injective_iff_map_eq_zero]
  intro y hy
  funext τ
  have hb : ∀ b, pr X e y τ b = 0 := by
    intro b
    by_cases h : b.1 < X.p0
    · have := coordMap_pos X e y τ ⟨b.1, by rw [dimOf_mem X τ.2]; exact h⟩
      rw [hy] at this
      exact this.symm
    · have := coordMap_neg X e y τ ⟨b.1 - X.p0, by
        rw [dimOf_not_mem X ((X.cmType _).mp τ.2)]; have := b.2; omega⟩
      rw [hy] at this
      have h2 : (⟨X.p0 + (b.1 - X.p0), by have := b.2; omega⟩ : Fin r) = b := Fin.ext (by simp only; omega)
      simp only [h2] at this
      have h3 : - conj (pr X e y τ b) = 0 := this.symm
      simpa using h3
  have hs : (Real.sqrt (X.c τ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (c_pos X τ)).ne'
  have hb' : ∀ b, hermC τ.1 X.Gm (y τ) (e τ b) = 0 := fun b =>
    (mul_eq_zero.mp (hb b)).resolve_left hs
  rw [expand X τ (e τ) (he τ) (y τ)]
  simp [hb']

theorem finrank_eq (X : Data E r) :
    Module.finrank ℝ (X.Ψ → Fin r → ℂ) = Module.finrank ℝ (Vsp (dimOf X)) := by
  rw [(WithLp.linearEquiv 2 ℝ (Idx (dimOf X) → ℂ)).finrank_eq]
  simp only [Module.finrank_pi_fintype, Complex.finrank_real_complex, Finset.sum_const,
    Finset.card_univ, card_idx, smul_eq_mul, Fintype.card_coe, Fintype.card_fin]
  ring

theorem parseval (X : Data E r) (τ : X.Ψ) (e : Fin r → Fin r → ℂ)
    (he : ∀ a b, hermC τ.1 X.Gm (e a) (e b) =
      if a = b then ((ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 a : ℝ) : ℂ) else 0) (u v : Fin r → ℂ) :
    hermC τ.1 X.Gm u v = ∑ a : Fin r, ((ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 a : ℝ) : ℂ) *
      (hermC τ.1 X.Gm u (e a) * conj (hermC τ.1 X.Gm v (e a))) := by
  conv_lhs => arg 4; rw [expand X τ e he v]
  rw [hermC_sum_right]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [hermC_smul_right, map_mul, Complex.conj_ofReal]
  ring

theorem im_eq (X : Data E r) (e : X.Ψ → Fin r → (Fin r → ℂ))
    (he : ∀ τ a b, hermC τ.1 X.Gm (e τ a) (e τ b) =
      if a = b then ((ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 a : ℝ) : ℂ) else 0) (y y' : X.Ψ → Fin r → ℂ) :
    (Hf (coordMap X e y) (coordMap X e y')).im =
      ∑ τ : X.Ψ, X.c τ * (hermC τ.1 X.Gm (y τ) (y' τ)).im := by
  rw [Hf, Fintype.sum_sigma, sum_emb_split X, Complex.im_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  let g : Fin r → ℝ := fun b => X.c τ * (((ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 b : ℝ) : ℂ) *
      (hermC τ.1 X.Gm (y τ) (e τ b) * conj (hermC τ.1 X.Gm (y' τ) (e τ b)))).im
  have hsq : Real.sqrt (X.c τ) * Real.sqrt (X.c τ) = X.c τ := Real.mul_self_sqrt (c_pos X τ).le
  have hle : dimOf X τ.1 ≤ r := by rw [dimOf_mem X τ.2]; exact X.p0_le
  have hn := (X.cmType _).mp τ.2
  rw [parseval X τ (e τ) (he τ), Complex.im_sum, Finset.mul_sum, Complex.add_im, Complex.im_sum,
    Complex.im_sum]
  show _ = ∑ b, g b
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun b : Fin r => (b : ℕ) < X.p0)]
  congr 1
  · have h := sum_castLE_eq hle g
    rw [show (Finset.univ.filter (fun b : Fin r => (b : ℕ) < X.p0)) =
      Finset.univ.filter (fun b : Fin r => (b : ℕ) < dimOf X τ.1) by rw [dimOf_mem X τ.2], ← h]
    refine Finset.sum_congr rfl fun a _ => ?_
    have ha : a.1 < X.p0 := lt_of_lt_of_eq a.2 (dimOf_mem X τ.2)
    rw [coordMap_pos, coordMap_pos]
    have hc : (⟨a.1, lt_pos X τ.2 a⟩ : Fin r) = Fin.castLE hle a := rfl
    simp only [g, pr, hc, ReciprocityTheory.ChartRestriction.G.FD.sgn, Fin.val_castLE, if_pos ha]
    generalize hermC τ.1 X.Gm (y τ) (e τ (Fin.castLE hle a)) = A
    generalize hermC τ.1 X.Gm (y' τ) (e τ (Fin.castLE hle a)) = B
    simp
    linear_combination (A.im * B.re - A.re * B.im) * hsq
  · rw [← sum_shift_eq X.p0_le (dimOf_not_mem X hn) g (fun a => ⟨X.p0 + a.1, lt_neg X hn a⟩)
      (fun a => rfl)]
    refine Finset.sum_congr rfl fun a _ => ?_
    have ha : ¬ (X.p0 + a.1 < X.p0) := by omega
    rw [coordMap_neg, coordMap_neg]
    simp only [g, pr, ReciprocityTheory.ChartRestriction.G.FD.sgn, if_neg ha]
    generalize hermC τ.1 X.Gm (y τ) (e τ ⟨X.p0 + a.1, _⟩) = A
    generalize hermC τ.1 X.Gm (y' τ) (e τ ⟨X.p0 + a.1, _⟩) = B
    simp
    linear_combination (A.re * B.im - A.im * B.re) * hsq

theorem act_eq (X : Data E r) (e : X.Ψ → Fin r → (Fin r → ℂ)) (α : 𝓞 E) (y : X.Ψ → Fin r → ℂ) :
    coordMap X e (fun τ => τ.1 (α : E) • y τ) = act α (coordMap X e y) := by
  ext i
  show coord X e _ i = i.1 (α : E) * coord X e y i
  unfold coord
  split_ifs
  · rw [pr_smul X e (fun τ => τ.1 (α : E))]
  · rw [pr_smul X e (fun τ => τ.1 (α : E)), map_mul]
    simp

end

end TorusCoord

open NumberField in
open scoped ComplexConjugate in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
private theorem coord_eq_pr_of_mem_psi (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (e : X.Ψ → Fin r → (Fin r → ℂ))
    (y : X.Ψ → Fin r → ℂ) (τ : X.Ψ) (a : Fin (_root_.GlobalTheory.TorusCoord.dimOf X τ.1)) :
    _root_.GlobalTheory.TorusCoord.coord X e y ⟨τ.1, a⟩ =
      _root_.GlobalTheory.TorusCoord.pr X e y τ ⟨a.1, _root_.GlobalTheory.TorusCoord.lt_pos X τ.2 a⟩ := by
  unfold _root_.GlobalTheory.TorusCoord.coord
  rw [dif_pos τ.2]

open NumberField in
open scoped ComplexConjugate in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
private theorem coord_conjugate_eq_neg_conj_pr (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (e : X.Ψ → Fin r → (Fin r → ℂ))
    (y : X.Ψ → Fin r → ℂ) (τ : X.Ψ) (a : Fin (_root_.GlobalTheory.TorusCoord.dimOf X (ComplexEmbedding.conjugate τ.1))) :
    _root_.GlobalTheory.TorusCoord.coord X e y ⟨ComplexEmbedding.conjugate τ.1, a⟩ =
      -conj (_root_.GlobalTheory.TorusCoord.pr X e y τ
        ⟨X.p0 + a.1, _root_.GlobalTheory.TorusCoord.lt_neg X ((X.cmType τ.1).mp τ.2) a⟩) := by
  have h : ComplexEmbedding.conjugate τ.1 ∉ X.Ψ := (X.cmType τ.1).mp τ.2
  have hτ : (⟨ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ.1),
      _root_.GlobalTheory.TorusCoord.conj_mem X h⟩ : X.Ψ) = τ := Subtype.ext (_root_.ReciprocityTheory.ChartRestriction.G.I2.TorusAtDataPf.conj_conj_X _)
  unfold _root_.GlobalTheory.TorusCoord.coord
  rw [dif_neg h, hτ]

open NumberField in
open scoped ComplexConjugate in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
private theorem sum_idx_eq_sum_sigma {dim : (E →+* ℂ) → ℕ} (G : _root_.ReciprocityTheory.ChartRestriction.G.I2.Idx dim → ℝ) :
    ∑ i, G i = ∑ σ, ∑ a : Fin (dim σ), G ⟨σ, a⟩ := Fintype.sum_sigma G

open NumberField in
open scoped ComplexConjugate in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
private theorem torusCoordinates_pair_im_lemma_4 (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (e : X.Ψ → Fin r → (Fin r → ℂ))
    (he : ∀ τ a b, _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ.1 X.Gm (e τ a) (e τ b) = if a = b then ((_root_.ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 a : ℝ) : ℂ) else 0)
    (y y' : X.Ψ → Fin r → ℂ) (τ : X.Ψ) :
    ∑ a : Fin (_root_.GlobalTheory.TorusCoord.dimOf X τ.1),
        (_root_.GlobalTheory.TorusCoord.coord X e y ⟨τ.1, a⟩ *
          conj (_root_.GlobalTheory.TorusCoord.coord X e y' ⟨τ.1, a⟩)).im +
      ∑ a : Fin (_root_.GlobalTheory.TorusCoord.dimOf X (ComplexEmbedding.conjugate τ.1)),
        (_root_.GlobalTheory.TorusCoord.coord X e y ⟨ComplexEmbedding.conjugate τ.1, a⟩ *
          conj (_root_.GlobalTheory.TorusCoord.coord X e y' ⟨ComplexEmbedding.conjugate τ.1, a⟩)).im =
      X.c τ * (_root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ.1 X.Gm (y τ) (y' τ)).im := by
  set g : Fin r → ℝ := fun b => (_root_.GlobalTheory.TorusCoord.pr X e y τ b *
    conj (_root_.GlobalTheory.TorusCoord.pr X e y' τ b)).im with hg
  have hnot : ComplexEmbedding.conjugate τ.1 ∉ X.Ψ := (X.cmType τ.1).mp τ.2
  have hpos : _root_.GlobalTheory.TorusCoord.dimOf X τ.1 = X.p0 := if_pos τ.2
  have hneg : _root_.GlobalTheory.TorusCoord.dimOf X (ComplexEmbedding.conjugate τ.1) = r - X.p0 := if_neg hnot
  have hle : _root_.GlobalTheory.TorusCoord.dimOf X τ.1 ≤ r := hpos ▸ X.p0_le
  have e1 : ∑ a : Fin (_root_.GlobalTheory.TorusCoord.dimOf X τ.1),
      (_root_.GlobalTheory.TorusCoord.coord X e y ⟨τ.1, a⟩ *
        conj (_root_.GlobalTheory.TorusCoord.coord X e y' ⟨τ.1, a⟩)).im = ∑ b : Fin r with b.val < X.p0, g b := by
    simp only [coord_eq_pr_of_mem_psi]
    refine (_root_.ReciprocityTheory.ChartRestriction.G.I2.TorusAtDataPf.sum_castLE_eq hle g).trans ?_
    rw [hpos]
  have e2 : ∑ a : Fin (_root_.GlobalTheory.TorusCoord.dimOf X (ComplexEmbedding.conjugate τ.1)),
      (_root_.GlobalTheory.TorusCoord.coord X e y ⟨ComplexEmbedding.conjugate τ.1, a⟩ *
        conj (_root_.GlobalTheory.TorusCoord.coord X e y' ⟨ComplexEmbedding.conjugate τ.1, a⟩)).im =
      -∑ b : Fin r with ¬ b.val < X.p0, g b := by
    rw [← _root_.ReciprocityTheory.ChartRestriction.G.I2.TorusAtDataPf.sum_shift_eq X.p0_le hneg g
      (fun a => (⟨X.p0 + a.1, _root_.GlobalTheory.TorusCoord.lt_neg X hnot a⟩ : Fin r)) (fun _ => rfl),
      ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [coord_conjugate_eq_neg_conj_pr, coord_conjugate_eq_neg_conj_pr, hg]
    simp only [map_neg, Complex.conj_conj, neg_mul_neg, Complex.mul_im, Complex.conj_re, Complex.conj_im]
    ring
  have hs : (Real.sqrt (X.c τ) : ℂ) * (Real.sqrt (X.c τ) : ℂ) = (X.c τ : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (_root_.GlobalTheory.TorusCoord.c_pos X τ).le]
  have hterm : ∀ b : Fin r, X.c τ * ((starRingEnd ℂ) (((_root_.ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 b : ℝ) : ℂ) *
      _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ.1 X.Gm (y' τ) (e τ b)) * _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ.1 X.Gm (y τ) (e τ b)).im = _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 b * g b := by
    intro b
    have hgb : g b = X.c τ * (_root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ.1 X.Gm (y τ) (e τ b) *
        conj (_root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ.1 X.Gm (y' τ) (e τ b))).im := by
      rw [hg]
      simp only [_root_.GlobalTheory.TorusCoord.pr, map_mul, Complex.conj_ofReal]
      rw [show (Real.sqrt (X.c τ) : ℂ) * _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ.1 X.Gm (y τ) (e τ b) *
          ((Real.sqrt (X.c τ) : ℂ) * conj (_root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ.1 X.Gm (y' τ) (e τ b))) =
          ((Real.sqrt (X.c τ) : ℂ) * (Real.sqrt (X.c τ) : ℂ)) *
            (_root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ.1 X.Gm (y τ) (e τ b) * conj (_root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ.1 X.Gm (y' τ) (e τ b))) by ring,
        hs, Complex.im_ofReal_mul]
    rw [hgb, map_mul, Complex.conj_ofReal, mul_assoc, Complex.im_ofReal_mul,
      mul_comm (conj (_root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ.1 X.Gm (y' τ) (e τ b)))]
    ring
  rw [e1, e2, _root_.ReciprocityTheory.ChartRestriction.G.I2.TorusAtDataPf.expand X τ (e τ) (he τ) (y' τ), _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC_sum_right]
  simp only [_root_.ReciprocityTheory.ChartRestriction.G.FD.hermC_smul_right]
  rw [Complex.im_sum, Finset.mul_sum]
  refine Eq.trans ?_ (Finset.sum_congr rfl fun b _ => (hterm b).symm)
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun b : Fin r => (b : ℕ) < X.p0),
    ← Finset.sum_neg_distrib]
  congr 1
  · refine Finset.sum_congr rfl fun b hb => ?_
    rw [Finset.mem_filter] at hb
    simp [_root_.ReciprocityTheory.ChartRestriction.G.FD.sgn, hb.2]
  · refine Finset.sum_congr rfl fun b hb => ?_
    rw [Finset.mem_filter] at hb
    simp [_root_.ReciprocityTheory.ChartRestriction.G.FD.sgn, hb.2]

open NumberField in
open scoped ComplexConjugate in

theorem _root_.GlobalTheory.exists_torus_coordinates : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (e : X.Ψ → Fin r → (Fin r → ℂ)), (∀ τ a b, _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ.1 X.Gm (e τ a) (e τ b) = if a = b then ((_root_.ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 a : ℝ) : ℂ) else 0) → ∃ (dim : (E →+* ℂ) → ℕ) (hp : ∀ τ : X.Ψ, dim τ.1 = X.p0) (hn : ∀ τ : X.Ψ, dim (ComplexEmbedding.conjugate τ.1) = r - X.p0) (Φ : (X.Ψ → Fin r → ℂ) ≃ₗ[ℝ] _root_.ReciprocityTheory.ChartRestriction.G.I2.Vsp dim), Fintype.card (_root_.ReciprocityTheory.ChartRestriction.G.I2.Idx dim) = X.Ψ.card * r ∧ (∀ τ, dim τ + dim (ComplexEmbedding.conjugate τ) = r) ∧ (∀ y (τ : X.Ψ) (a : Fin (dim τ.1)), (Φ y) ⟨τ.1, a⟩ = (Real.sqrt (X.c τ) : ℂ) * _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ.1 X.Gm (y τ) (e τ (Fin.castLE (by rw [hp τ]; exact X.p0_le) a))) ∧ (∀ y (τ : X.Ψ) (a : Fin (dim (ComplexEmbedding.conjugate τ.1))), (Φ y) ⟨ComplexEmbedding.conjugate τ.1, a⟩ = (Real.sqrt (X.c τ) : ℂ) * (starRingEnd ℂ) (-_root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ.1 X.Gm (y τ) (e τ ⟨X.p0 + a.1, by have h1 : a.1 < r - X.p0 := lt_of_lt_of_eq a.2 (hn τ); have := X.p0_le; omega⟩))) ∧ (∀ (α : 𝓞 E) y, Φ (fun τ => τ.1 (α : E) • y τ) = _root_.ReciprocityTheory.ChartRestriction.G.I2.act α (Φ y)) ∧ ∀ y y', (_root_.ReciprocityTheory.ChartRestriction.G.I2.Hf (Φ y) (Φ y')).im = ∑ τ : X.Ψ, X.c τ * (_root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ.1 X.Gm (y τ) (y' τ)).im := by
  intro E _ _ _ r X e he
  have hp : ∀ τ : X.Ψ, _root_.GlobalTheory.TorusCoord.dimOf X τ.1 = X.p0 := fun τ => if_pos τ.2
  have hn : ∀ τ : X.Ψ, _root_.GlobalTheory.TorusCoord.dimOf X (ComplexEmbedding.conjugate τ.1) = r - X.p0 :=
    fun τ => if_neg ((X.cmType τ.1).mp τ.2)
  have hsum : ∀ σ, _root_.GlobalTheory.TorusCoord.dimOf X σ +
      _root_.GlobalTheory.TorusCoord.dimOf X (ComplexEmbedding.conjugate σ) = r := by
    intro σ
    have := X.p0_le
    by_cases hσ : σ ∈ X.Ψ
    · rw [_root_.GlobalTheory.TorusCoord.dimOf, _root_.GlobalTheory.TorusCoord.dimOf, if_pos hσ, if_neg ((X.cmType σ).mp hσ)]
      omega
    · rw [_root_.GlobalTheory.TorusCoord.dimOf, _root_.GlobalTheory.TorusCoord.dimOf, if_neg hσ,
        if_pos (_root_.GlobalTheory.TorusCoord.conj_mem X hσ)]
      omega
  have hcard : Fintype.card (_root_.ReciprocityTheory.ChartRestriction.G.I2.Idx (_root_.GlobalTheory.TorusCoord.dimOf X)) = X.Ψ.card * r := by
    rw [Fintype.card_sigma]
    simp only [Fintype.card_fin]
    rw [_root_.GlobalTheory.TorusCoord.sum_emb_split X]
    simp [hsum]
  have hdim : Module.finrank ℝ (X.Ψ → Fin r → ℂ) =
      Module.finrank ℝ (_root_.ReciprocityTheory.ChartRestriction.G.I2.Vsp (_root_.GlobalTheory.TorusCoord.dimOf X)) := by
    have h1 : Module.finrank ℝ (X.Ψ → Fin r → ℂ) = X.Ψ.card * r * 2 := by
      rw [Module.finrank_pi_fintype]
      simp [Module.finrank_pi_fintype, Complex.finrank_real_complex]
      ring
    have h2 : Module.finrank ℝ (_root_.ReciprocityTheory.ChartRestriction.G.I2.Vsp (_root_.GlobalTheory.TorusCoord.dimOf X)) =
        Fintype.card (_root_.ReciprocityTheory.ChartRestriction.G.I2.Idx (_root_.GlobalTheory.TorusCoord.dimOf X)) * 2 := by
      unfold _root_.ReciprocityTheory.ChartRestriction.G.I2.Vsp
      rw [(WithLp.linearEquiv 2 ℝ _).finrank_eq, Module.finrank_pi_fintype]
      simp [Complex.finrank_real_complex]
    rw [h1, h2, hcard]
  have hc : ∀ τ : X.Ψ, (Real.sqrt (X.c τ) : ℂ) ≠ 0 := fun τ => by
    exact_mod_cast (Real.sqrt_pos.mpr (_root_.GlobalTheory.TorusCoord.c_pos X τ)).ne'
  have hinj : Function.Injective (_root_.GlobalTheory.TorusCoord.coordMap X e) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    have hy' : ∀ i, _root_.GlobalTheory.TorusCoord.coord X e y i = 0 := fun i =>
      congrArg (fun v : _root_.ReciprocityTheory.ChartRestriction.G.I2.Vsp (_root_.GlobalTheory.TorusCoord.dimOf X) => v i) hy
    funext τ
    have hz : ∀ b : Fin r, _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ.1 X.Gm (y τ) (e τ b) = 0 := by
      intro b
      have key : _root_.GlobalTheory.TorusCoord.pr X e y τ b = 0 := by
        have hb' := b.2
        by_cases hb : (b : ℕ) < X.p0
        · have h1 := hy' ⟨τ.1, ⟨b.1, by rw [hp τ]; exact hb⟩⟩
          rw [coord_eq_pr_of_mem_psi] at h1
          exact h1
        · have h2 := hy' ⟨ComplexEmbedding.conjugate τ.1, ⟨b.1 - X.p0, by rw [hn τ]; omega⟩⟩
          rw [coord_conjugate_eq_neg_conj_pr, neg_eq_zero, map_eq_zero] at h2
          convert h2 using 3
          first
            | (simp only [Fin.val_mk]; omega)
            | (ext; simp only [Fin.val_mk]; omega)
      exact (mul_eq_zero.mp key).resolve_left (hc τ)
    show y τ = 0
    rw [_root_.ReciprocityTheory.ChartRestriction.G.I2.TorusAtDataPf.expand X τ (e τ) (he τ) (y τ)]
    simp [hz]
  refine ⟨_root_.GlobalTheory.TorusCoord.dimOf X, hp, hn,
    LinearMap.linearEquivOfInjective (_root_.GlobalTheory.TorusCoord.coordMap X e) hinj hdim, hcard, hsum,
    ?_, ?_, ?_, ?_⟩
  · intro y τ a
    exact coord_eq_pr_of_mem_psi X e y τ a
  · intro y τ a
    refine (coord_conjugate_eq_neg_conj_pr X e y τ a).trans ?_
    simp only [_root_.GlobalTheory.TorusCoord.pr, map_mul, map_neg, Complex.conj_ofReal]
    ring
  · intro α y
    refine PiLp.ext fun i => ?_
    change _root_.GlobalTheory.TorusCoord.coord X e (fun τ => τ.1 (α : E) • y τ) i =
      i.1 (α : E) * _root_.GlobalTheory.TorusCoord.coord X e y i
    unfold _root_.GlobalTheory.TorusCoord.coord
    split_ifs with hσ
    · simp only [_root_.GlobalTheory.TorusCoord.pr, _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC_smul_left]
      ring
    · simp only [_root_.GlobalTheory.TorusCoord.pr, _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC_smul_left, map_mul, map_neg,
        ComplexEmbedding.conjugate_coe_eq, Complex.conj_conj, Complex.conj_ofReal]
      ring
  · intro y y'
    change (∑ i : _root_.ReciprocityTheory.ChartRestriction.G.I2.Idx (_root_.GlobalTheory.TorusCoord.dimOf X), _root_.GlobalTheory.TorusCoord.coord X e y i *
      conj (_root_.GlobalTheory.TorusCoord.coord X e y' i)).im = _
    rw [Complex.im_sum, sum_idx_eq_sum_sigma, _root_.GlobalTheory.TorusCoord.sum_emb_split X]
    exact Finset.sum_congr rfl fun τ _ => torusCoordinates_pair_im_lemma_4 X e he y y' τ

end GlobalTheory
