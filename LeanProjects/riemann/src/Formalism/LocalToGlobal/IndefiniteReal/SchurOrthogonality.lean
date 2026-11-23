import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.HaarTransfer.SchurClosable
import Formalism.LocalToGlobal.IndefiniteReal.SmExpSmulContDiff
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSchur
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SchurClosable

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory Matrix
open Formalism.L2.Theta Formalism.IndefR.Mult
open Filter Topology
open scoped InnerProductSpace ContDiff TensorProduct

namespace Formalism.IndefR.SchurOrthogonalityAlt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Alg

theorem polar {X H' : Type*} [AddCommGroup X] [Module ℂ X] [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
    (A₁ A₂ : X →ₗ[ℂ] H') (ip : X → X → ℂ)
    (h : ∀ a b : ℂ, ∃ c : ℝ, ∀ x y, ⟪(a • A₁ + b • A₂) x, (a • A₁ + b • A₂) y⟫_ℂ = (c : ℂ) * ip x y) :
    ∃ c : ℂ, ∀ x y, ⟪A₁ x, A₂ y⟫_ℂ = c * ip x y := by
  obtain ⟨c10, h10⟩ := h 1 0
  obtain ⟨c01, h01⟩ := h 0 1
  obtain ⟨c11, h11⟩ := h 1 1
  obtain ⟨c1i, h1i⟩ := h 1 Complex.I
  refine ⟨(((c11 : ℂ) - c10 - c01) - Complex.I * ((c1i : ℂ) - c10 - c01)) / 2, fun x y => ?_⟩
  have e10 := h10 x y
  have e01 := h01 x y
  have e11 := h11 x y
  have e1i := h1i x y
  simp only [LinearMap.add_apply, LinearMap.smul_apply, inner_add_left, inner_add_right, inner_smul_left,
    inner_smul_right, one_smul, zero_smul, add_zero, zero_add, map_one, map_zero, one_mul, zero_mul,
    inner_zero_left, inner_zero_right, Complex.conj_I] at e10 e01 e11 e1i
  linear_combination (1 / 2 : ℂ) * (e11 - e10 - e01) - (Complex.I / 2) * (e1i - e10 - e01) +
    ((⟪A₁ x, A₂ y⟫_ℂ - ⟪A₂ x, A₁ y⟫_ℂ) / 2 - Complex.I * ⟪A₂ x, A₂ y⟫_ℂ / 2) * Complex.I_sq

theorem prod_of_place {ι : Type*} [Fintype ι] [DecidableEq ι] {X : ι → Type*} (B : (∀ i, X i) → (∀ i, X i) → ℂ)
    (ip : ∀ i, X i → X i → ℂ)
    (h : ∀ i (v v' : ∀ i, X i), ∃ c : ℂ, ∀ x y, B (Function.update v i x) (Function.update v' i y) = c * ip i x y)
    (e : ∀ i, X i) (v v' : ∀ i, X i) :
    (∏ i, ip i (e i) (e i)) * B v v' = (∏ i, ip i (v i) (v' i)) * B e e := by
  have key : ∀ s : Finset ι, (∏ i ∈ s, ip i (e i) (e i)) * B v v' =
      (∏ i ∈ s, ip i (v i) (v' i)) * B (s.piecewise e v) (s.piecewise e v') := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.piecewise_insert, Finset.piecewise_insert]
      obtain ⟨c, hc⟩ := h a (s.piecewise e v) (s.piecewise e v')
      have hu : Function.update (s.piecewise e v) a (v a) = s.piecewise e v :=
        Function.update_eq_self_iff.2 (Finset.piecewise_eq_of_notMem _ _ _ ha).symm
      have hu' : Function.update (s.piecewise e v') a (v' a) = s.piecewise e v' :=
        Function.update_eq_self_iff.2 (Finset.piecewise_eq_of_notMem _ _ _ ha).symm
      have h1 := hc (v a) (v' a)
      rw [hu, hu'] at h1
      rw [hc]
      linear_combination (ip a (e a) (e a)) * ih + (ip a (e a) (e a) * ∏ i ∈ s, ip i (v i) (v' i)) * h1
  have := key Finset.univ
  rwa [Finset.piecewise_univ, Finset.piecewise_univ] at this

end Alg

section L2

variable {α : Type*} [MeasurableSpace α] {ν : Measure α}

def toL2 {X : Type*} [AddCommGroup X] [Module ℂ X] (L : X →ₗ[ℂ] (α → ℂ)) (hL : ∀ w, MemLp (L w) 2 ν) :
    X →ₗ[ℂ] Lp ℂ 2 ν where
  toFun w := (hL w).toLp (L w)
  map_add' x y := by
    rw [← MemLp.toLp_add]
    exact MemLp.toLp_congr _ _ (Filter.EventuallyEq.of_eq (map_add L x y))
  map_smul' c x := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    exact MemLp.toLp_congr _ _ (Filter.EventuallyEq.of_eq (map_smul L c x))

theorem to_square_integrable_apply {X : Type*} [AddCommGroup X] [Module ℂ X] (L : X →ₗ[ℂ] (α → ℂ))
    (hL : ∀ w, MemLp (L w) 2 ν) (w : X) : toL2 L hL w = (hL w).toLp (L w) := rfl

theorem inner_toLp {f g : α → ℂ} (hf : MemLp f 2 ν) (hg : MemLp g 2 ν) :
    ⟪hf.toLp f, hg.toLp g⟫_ℂ = ∫ x, star (f x) * g x ∂ν := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x h1 h2
  rw [h1, h2]
  simp [RCLike.inner_apply, mul_comm]

theorem integrable_star_mul {f g : α → ℂ} (hf : MemLp f 2 ν) (hg : MemLp g 2 ν) :
    Integrable (fun x => star (f x) * g x) ν := by
  refine (L2.integrable_inner (𝕜 := ℂ) (hf.toLp f) (hg.toLp g)).congr ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x h1 h2
  rw [h1, h2]
  simp [RCLike.inner_apply, mul_comm]

end L2

section Sob

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {Lie : Set (Matrix (Fin n) (Fin n) ℂ)} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem sobCont_zero : Sobolev₂ Lie σ (0 : H →ₗ[ℂ] ℂ) :=
  ⟨[], 0, by simp, fun w _ => by simp⟩

theorem sum_map_norm_nonneg (S : List (List (Matrix (Fin n) (Fin n) ℂ))) (w : H) :
    0 ≤ (S.map fun l => ‖l.foldr (dRep σ) w‖).sum :=
  List.sum_nonneg (fun x hx => by
    obtain ⟨l, -, rfl⟩ := List.mem_map.1 hx
    exact norm_nonneg _)

theorem sobCont_add {ℓ₁ ℓ₂ : H →ₗ[ℂ] ℂ} (h₁ : Sobolev₂ Lie σ ℓ₁) (h₂ : Sobolev₂ Lie σ ℓ₂) :
    Sobolev₂ Lie σ (ℓ₁ + ℓ₂) := by
  obtain ⟨S₁, C₁, hS₁, hb₁⟩ := h₁
  obtain ⟨S₂, C₂, hS₂, hb₂⟩ := h₂
  refine ⟨S₁ ++ S₂, |C₁| + |C₂|, ?_, fun w hw => ?_⟩
  · intro l hl X hX
    rcases List.mem_append.1 hl with h | h
    exacts [hS₁ l h X hX, hS₂ l h X hX]
  · have e₁ := hb₁ w hw
    have e₂ := hb₂ w hw
    have a₀ := sum_map_norm_nonneg (σ := σ) S₁ w
    have b₀ := sum_map_norm_nonneg (σ := σ) S₂ w
    rw [List.map_append, List.sum_append, LinearMap.add_apply]
    calc ‖ℓ₁ w + ℓ₂ w‖ ≤ ‖ℓ₁ w‖ + ‖ℓ₂ w‖ := norm_add_le _ _
      _ ≤ _ := by
        nlinarith [mul_nonneg (sub_nonneg.2 (le_abs_self C₁)) a₀, mul_nonneg (abs_nonneg C₁) b₀,
          mul_nonneg (sub_nonneg.2 (le_abs_self C₂)) b₀, mul_nonneg (abs_nonneg C₂) a₀]

theorem sobCont_smul {ℓ : H →ₗ[ℂ] ℂ} (c : ℂ) (h : Sobolev₂ Lie σ ℓ) : Sobolev₂ Lie σ (c • ℓ) := by
  obtain ⟨S, C, hS, hb⟩ := h
  refine ⟨S, ‖c‖ * |C|, hS, fun w hw => ?_⟩
  have e := hb w hw
  have a₀ := sum_map_norm_nonneg (σ := σ) S w
  rw [LinearMap.smul_apply, norm_smul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (e.trans (mul_le_mul_of_nonneg_right (le_abs_self C) a₀)) (norm_nonneg c)

end Sob

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

def Gt (V : HSp D) (τ : D.what₂.Tau) : Subgroup (GL (Fin V.rank) ℂ) where
  carrier := {u | ((u : GL (Fin V.rank) ℂ) : Matrix (Fin V.rank) (Fin V.rank) ℂ) ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)}
  one_mem' := by
    show (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ)ᴴ * gramAt D V τ * 1 = gramAt D V τ
    simp
  mul_mem' {a b} ha hb := by
    have ha' : (a : Matrix (Fin V.rank) (Fin V.rank) ℂ)ᴴ * gramAt D V τ * a = gramAt D V τ := ha
    have hb' : (b : Matrix (Fin V.rank) (Fin V.rank) ℂ)ᴴ * gramAt D V τ * b = gramAt D V τ := hb
    show (((a * b : GL (Fin V.rank) ℂ)) : Matrix (Fin V.rank) (Fin V.rank) ℂ)ᴴ * gramAt D V τ *
      ((a * b : GL (Fin V.rank) ℂ) : Matrix (Fin V.rank) (Fin V.rank) ℂ) = gramAt D V τ
    rw [Units.val_mul]
    generalize (a : Matrix (Fin V.rank) (Fin V.rank) ℂ) = A at ha' ⊢
    generalize (b : Matrix (Fin V.rank) (Fin V.rank) ℂ) = B at hb' ⊢
    calc (A * B)ᴴ * gramAt D V τ * (A * B) = Bᴴ * (Aᴴ * gramAt D V τ * A) * B := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = gramAt D V τ := by rw [ha', hb']
  inv_mem' {a} ha := by
    have ha' : (a : Matrix (Fin V.rank) (Fin V.rank) ℂ)ᴴ * gramAt D V τ * a = gramAt D V τ := ha
    show (((a⁻¹ : GL (Fin V.rank) ℂ) : Matrix (Fin V.rank) (Fin V.rank) ℂ))ᴴ * gramAt D V τ *
      ((a⁻¹ : GL (Fin V.rank) ℂ) : Matrix (Fin V.rank) (Fin V.rank) ℂ) = gramAt D V τ
    have hi : (a : Matrix (Fin V.rank) (Fin V.rank) ℂ) *
        ((a⁻¹ : GL (Fin V.rank) ℂ) : Matrix (Fin V.rank) (Fin V.rank) ℂ) = 1 := a.mul_inv
    generalize ((a⁻¹ : GL (Fin V.rank) ℂ) : Matrix (Fin V.rank) (Fin V.rank) ℂ) = b at hi ⊢
    generalize (a : Matrix (Fin V.rank) (Fin V.rank) ℂ) = A at ha' hi
    calc bᴴ * gramAt D V τ * b = bᴴ * (Aᴴ * gramAt D V τ * A) * b := by rw [ha']
      _ = (A * b)ᴴ * gramAt D V τ * (A * b) := by simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = gramAt D V τ := by rw [hi]; simp

abbrev gm {τ : D.what₂.Tau} (g : Gt V τ) : Matrix (Fin V.rank) (Fin V.rank) ℂ :=
  ((g : GL (Fin V.rank) ℂ) : Matrix (Fin V.rank) (Fin V.rank) ℂ)

theorem gm_mem {τ : D.what₂.Tau} (g : Gt V τ) : gm g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) := g.2

theorem fr_mul_inv (M : DSModel V S) (τ : D.what₂.Tau) : M.fr τ * (M.fr τ)⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ))

theorem fr_inv_mul (M : DSModel V S) (τ : D.what₂.Tau) : (M.fr τ)⁻¹ * M.fr τ = 1 :=
  Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ))

theorem conj_mem (M : DSModel V S) (τ : D.what₂.Tau) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) : M.fr τ * g * (M.fr τ)⁻¹ ∈ UJset (M.ε τ) := by
  have hG := M.fr_gram τ
  have hQ : gᴴ * gramAt D V τ * g = gramAt D V τ := hg
  have hinv := fr_mul_inv M τ
  show (M.fr τ * g * (M.fr τ)⁻¹)ᴴ * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * g * (M.fr τ)⁻¹) = Formalism.REAL.Jm (M.ε τ)
  calc (M.fr τ * g * (M.fr τ)⁻¹)ᴴ * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * g * (M.fr τ)⁻¹)
      = ((M.fr τ)⁻¹)ᴴ * (gᴴ * ((M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ) * g) * (M.fr τ)⁻¹ := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = ((M.fr τ)⁻¹)ᴴ * ((M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ) * (M.fr τ)⁻¹ := by rw [hG, hQ]
    _ = (M.fr τ * (M.fr τ)⁻¹)ᴴ * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * (M.fr τ)⁻¹) := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = Formalism.REAL.Jm (M.ε τ) := by rw [hinv]; simp

def piR (M : DSModel V S) (τ : D.what₂.Tau) : Gt V τ →* (M.H τ →L[ℂ] M.H τ) where
  toFun g := M.rep τ (gm g)
  map_one' := by
    show M.σ τ (M.fr τ * 1 * (M.fr τ)⁻¹) = 1
    rw [Matrix.mul_one, fr_mul_inv]
    exact (M.ds τ).2.2.1.1.1
  map_mul' a b := by
    show M.σ τ (M.fr τ * (gm a * gm b) * (M.fr τ)⁻¹) = (M.σ τ (M.fr τ * gm a * (M.fr τ)⁻¹)) *
      (M.σ τ (M.fr τ * gm b * (M.fr τ)⁻¹))
    have e : M.fr τ * (gm a * gm b) * (M.fr τ)⁻¹ =
        (M.fr τ * gm a * (M.fr τ)⁻¹) * (M.fr τ * gm b * (M.fr τ)⁻¹) := by
      calc M.fr τ * (gm a * gm b) * (M.fr τ)⁻¹ = M.fr τ * gm a * 1 * gm b * (M.fr τ)⁻¹ := by
            simp only [Matrix.mul_one, Matrix.mul_assoc]
        _ = M.fr τ * gm a * ((M.fr τ)⁻¹ * M.fr τ) * gm b * (M.fr τ)⁻¹ := by rw [fr_inv_mul]
        _ = _ := by simp only [Matrix.mul_assoc]
    rw [e, ContinuousLinearMap.mul_def]
    exact (M.ds τ).2.2.1.1.2 _ (conj_mem M τ (gm_mem a)) _ (conj_mem M τ (gm_mem b))

theorem piR_apply (M : DSModel V S) (τ : D.what₂.Tau) (g : Gt V τ) : piR M τ g = M.rep τ (gm g) := rfl

theorem piR_norm (M : DSModel V S) (τ : D.what₂.Tau) (g : Gt V τ) (x : M.H τ) : ‖piR M τ g x‖ = ‖x‖ :=
  (M.ds τ).2.2.1.2.1 _ (conj_mem M τ (gm_mem g)) x

theorem isUnit_of_mem_UJ {n : ℕ} (ε : Fin n → Bool) {h : Matrix (Fin n) (Fin n) ℂ} (hh : h ∈ UJset ε) :
    IsUnit h := by
  have hh' : hᴴ * Formalism.REAL.Jm ε * h = Formalism.REAL.Jm ε := hh
  have hJ : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
    unfold Formalism.REAL.Jm
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs <;> norm_num
  have hl : (Formalism.REAL.Jm ε * hᴴ * Formalism.REAL.Jm ε) * h = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc hᴴ, hh', hJ]
  exact (Matrix.isUnit_iff_isUnit_det h).2 (Matrix.isUnit_det_of_left_inverse hl)

theorem exists_gt_of_UJ (M : DSModel V S) (τ : D.what₂.Tau) {h : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hh : h ∈ UJset (M.ε τ)) : ∃ g : Gt V τ, M.rep τ (gm g) = M.σ τ h := by
  have hh' : hᴴ * Formalism.REAL.Jm (M.ε τ) * h = Formalism.REAL.Jm (M.ε τ) := hh
  set g : Matrix (Fin V.rank) (Fin V.rank) ℂ := (M.fr τ)⁻¹ * h * M.fr τ with hgdef
  have hfu : IsUnit (M.fr τ)⁻¹ := (Matrix.isUnit_nonsing_inv_iff).2 (M.fr_unit τ)
  have hu : IsUnit g := (hfu.mul (isUnit_of_mem_UJ (M.ε τ) hh)).mul (M.fr_unit τ)
  have hmem : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) := by
    show gᴴ * gramAt D V τ * g = gramAt D V τ
    rw [← M.fr_gram τ, hgdef]
    calc ((M.fr τ)⁻¹ * h * M.fr τ)ᴴ * ((M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ) * ((M.fr τ)⁻¹ * h * M.fr τ)
        = (M.fr τ)ᴴ * hᴴ * ((M.fr τ * (M.fr τ)⁻¹)ᴴ * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * (M.fr τ)⁻¹)) * h *
            M.fr τ := by simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = (M.fr τ)ᴴ * (hᴴ * Formalism.REAL.Jm (M.ε τ) * h) * M.fr τ := by
          rw [fr_mul_inv]; simp only [conjTranspose_one, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc]
      _ = (M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ := by rw [hh']
  refine ⟨⟨hu.unit, hmem⟩, ?_⟩
  show M.σ τ (M.fr τ * g * (M.fr τ)⁻¹) = M.σ τ h
  congr 1
  rw [hgdef]
  calc M.fr τ * ((M.fr τ)⁻¹ * h * M.fr τ) * (M.fr τ)⁻¹
      = (M.fr τ * (M.fr τ)⁻¹) * h * (M.fr τ * (M.fr τ)⁻¹) := by simp only [Matrix.mul_assoc]
    _ = h := by rw [fr_mul_inv]; simp

theorem piR_inner (M : DSModel V S) (τ : D.what₂.Tau) (g : Gt V τ) (x y : M.H τ) :
    ⟪piR M τ g x, piR M τ g y⟫_ℂ = ⟪x, y⟫_ℂ := by
  let L : M.H τ →ₗᵢ[ℂ] M.H τ := { toLinearMap := (piR M τ g : M.H τ →ₗ[ℂ] M.H τ), norm_map' := piR_norm M τ g }
  exact L.inner_map_map x y

theorem commutant_scalar (M : DSModel V S) (τ : D.what₂.Tau) :
    ∀ B : M.H τ →L[ℂ] M.H τ, (∀ g, B.comp (piR M τ g) = (piR M τ g).comp B) →
      ∃ c : ℂ, B = c • ContinuousLinearMap.id ℂ (M.H τ) := by
  haveI : CompleteSpace (M.H τ) := (M.ds τ).1
  intro B hB
  have hstar : ∀ g, star (piR M τ g) = piR M τ g⁻¹ := by
    intro g
    rw [ContinuousLinearMap.star_eq_adjoint, eq_comm, ContinuousLinearMap.eq_adjoint_iff]
    intro x y
    rw [← piR_inner M τ g, ← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      ContinuousLinearMap.one_apply]
  obtain ⟨c, hc⟩ := Formalism.MainNotions.BridgeCSchur.schur_bounded (Set.range (piR M τ))
    (by rintro U ⟨g, rfl⟩; exact ⟨g⁻¹, (hstar g).symm⟩)
    (by
      intro W hW hinv
      apply (M.ds τ).2.2.2.1 W hW
      intro h hh v hv
      obtain ⟨g, hg⟩ := exists_gt_of_UJ M τ hh
      rw [← hg]
      exact hinv _ ⟨g, rfl⟩ v hv)
    B (by rintro U ⟨g, rfl⟩; exact hB g)
  exact ⟨c, by rw [hc]; rfl⟩

theorem sm_dense (M : DSModel V S) (τ : D.what₂.Tau) : Dense (M.sm τ : Set (M.H τ)) := by
  haveI : CompleteSpace (M.H τ) := (M.ds τ).1
  obtain ⟨-, -, hU, -⟩ := M.ds τ
  have hb := Formalism.IndefR.PeterssonHilbertSpace.sm_isURepOn_bridge (M.ε τ) (M.σ τ) hU
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
    Submodule.eq_bot_iff]
  intro x hx
  obtain ⟨Φ, hΦ, hΦc, -, hle⟩ := PI.KFinSmoothW.dense_weak_vectors _ (M.ε τ) (M.H τ) (M.σ τ) hb (ℂ ∙ x) inferInstance
  have hws := PI.KFinSmoothW.garding_vectors_smooth _ (M.ε τ) (M.H τ) (M.σ τ) hb Φ hΦ hΦc x
  have hsv : SmoothVec (lieAt V τ) (M.rep τ) (PI.KFinSmoothW.gv (M.ε τ) (M.σ τ) Φ x) :=
    Formalism.IndefR.PeterssonHilbertSpace.sm_transfer (M.ε τ) (M.σ τ) (M.fr τ) _ (M.fr_unit τ) (M.fr_gram τ) (lieAt V τ)
      (fun X hX => hX) _ hws
  have hw : PI.KFinSmoothW.gv (M.ε τ) (M.σ τ) Φ x ∈ M.sm τ := Submodule.subset_span hsv
  have h0 : ⟪PI.KFinSmoothW.gv (M.ε τ) (M.σ τ) Φ x, x⟫_ℂ = 0 := Submodule.inner_right_of_mem_orthogonal hw hx
  have h1 := hle x (Submodule.mem_span_singleton_self x)
  have h2 : ‖PI.KFinSmoothW.gv (M.ε τ) (M.σ τ) Φ x - x‖ ^ 2 =
      ‖PI.KFinSmoothW.gv (M.ε τ) (M.σ τ) Φ x‖ ^ 2 + ‖x‖ ^ 2 := by
    rw [@norm_sub_sq ℂ, h0]; simp
  have h3 : ‖x‖ ^ 2 ≤ 0 := by
    nlinarith [norm_nonneg (PI.KFinSmoothW.gv (M.ε τ) (M.σ τ) Φ x - x), norm_nonneg x,
      sq_nonneg ‖PI.KFinSmoothW.gv (M.ε τ) (M.σ τ) Φ x‖]
  exact norm_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 (le_antisymm h3 (sq_nonneg _)))

theorem rep_mul (M : DSModel V S) (τ : D.what₂.Tau) {a b : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (ha : a ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (hb : b ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) :
    M.rep τ (a * b) = (M.rep τ a).comp (M.rep τ b) := by
  show M.σ τ (M.fr τ * (a * b) * (M.fr τ)⁻¹) = (M.σ τ (M.fr τ * a * (M.fr τ)⁻¹)).comp
    (M.σ τ (M.fr τ * b * (M.fr τ)⁻¹))
  have e : M.fr τ * (a * b) * (M.fr τ)⁻¹ = (M.fr τ * a * (M.fr τ)⁻¹) * (M.fr τ * b * (M.fr τ)⁻¹) := by
    calc M.fr τ * (a * b) * (M.fr τ)⁻¹ = M.fr τ * a * 1 * b * (M.fr τ)⁻¹ := by
          simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = M.fr τ * a * ((M.fr τ)⁻¹ * M.fr τ) * b * (M.fr τ)⁻¹ := by rw [fr_inv_mul]
      _ = _ := by simp only [Matrix.mul_assoc]
  rw [e]
  exact (M.ds τ).2.2.1.1.2 _ (conj_mem M τ ha) _ (conj_mem M τ hb)

theorem conj_prod_exp {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) (hg : IsUnit g) :
    ∀ (k : ℕ) (Xs : Fin k → Matrix (Fin n) (Fin n) ℂ) (t : Fin k → ℝ),
      g⁻¹ * (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod * g =
        (List.ofFn fun i => NormedSpace.exp (t i • (g⁻¹ * Xs i * g))).prod
  | 0, Xs, t => by
    simp [Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hg)]
  | k + 1, Xs, t => by
    have ih := conj_prod_exp g hg k (fun i => Xs i.succ) (fun i => t i.succ)
    beta_reduce at ih
    have hgi : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hg)
    have he : NormedSpace.exp (t 0 • (g⁻¹ * Xs 0 * g)) = g⁻¹ * NormedSpace.exp (t 0 • Xs 0) * g := by
      rw [← Matrix.exp_conj' g _ hg, Matrix.mul_smul, Matrix.smul_mul]
    simp only [List.ofFn_succ, List.prod_cons]
    rw [he, ← ih]
    calc g⁻¹ * (NormedSpace.exp (t 0 • Xs 0) *
          (List.ofFn fun i : Fin k => NormedSpace.exp (t i.succ • Xs i.succ)).prod) * g
        = g⁻¹ * NormedSpace.exp (t 0 • Xs 0) * 1 *
          (List.ofFn fun i : Fin k => NormedSpace.exp (t i.succ • Xs i.succ)).prod * g := by
          simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = _ := by rw [← hgi]; simp only [Matrix.mul_assoc]

theorem smoothVec_rep (M : DSModel V S) (τ : D.what₂.Tau) (g : Gt V τ) {w : M.H τ}
    (hw : SmoothVec (lieAt V τ) (M.rep τ) w) : SmoothVec (lieAt V τ) (M.rep τ) (M.rep τ (gm g) w) := by
  intro k Xs hX
  have hgu : IsUnit (gm g) := Units.isUnit _
  have hgd := (Matrix.isUnit_iff_isUnit_det _).1 hgu
  have hG : (gm g)ᴴ * gramAt D V τ * gm g = gramAt D V τ := gm_mem g
  have hY : ∀ i, (gm g)⁻¹ * Xs i * gm g ∈ lieAt V τ := by
    intro i
    have hXi : (Xs i)ᴴ * gramAt D V τ + gramAt D V τ * Xs i = 0 := hX i
    have e1 : gramAt D V τ * (gm g)⁻¹ = (gm g)ᴴ * gramAt D V τ := by
      calc gramAt D V τ * (gm g)⁻¹ = (gm g)ᴴ * gramAt D V τ * (gm g * (gm g)⁻¹) := by
            rw [← Matrix.mul_assoc, hG]
        _ = _ := by rw [Matrix.mul_nonsing_inv _ hgd, Matrix.mul_one]
    have e2 : ((gm g)⁻¹)ᴴ * gramAt D V τ = gramAt D V τ * gm g := by
      calc ((gm g)⁻¹)ᴴ * gramAt D V τ = ((gm g)⁻¹)ᴴ * ((gm g)ᴴ * gramAt D V τ * gm g) := by rw [hG]
        _ = (gm g * (gm g)⁻¹)ᴴ * gramAt D V τ * gm g := by
            simp only [conjTranspose_mul, Matrix.mul_assoc]
        _ = _ := by rw [Matrix.mul_nonsing_inv _ hgd]; simp
    show ((gm g)⁻¹ * Xs i * gm g)ᴴ * gramAt D V τ + gramAt D V τ * ((gm g)⁻¹ * Xs i * gm g) = 0
    calc ((gm g)⁻¹ * Xs i * gm g)ᴴ * gramAt D V τ + gramAt D V τ * ((gm g)⁻¹ * Xs i * gm g)
        = (gm g)ᴴ * (Xs i)ᴴ * (((gm g)⁻¹)ᴴ * gramAt D V τ) + (gramAt D V τ * (gm g)⁻¹) * Xs i * gm g := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = (gm g)ᴴ * ((Xs i)ᴴ * gramAt D V τ + gramAt D V τ * Xs i) * gm g := by
          rw [e1, e2]; simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
      _ = 0 := by rw [hXi]; simp
  have hsm : ContDiff ℝ ∞ (fun t : Fin k → ℝ => M.rep τ (gm g)
      (M.rep τ (List.ofFn fun i => NormedSpace.exp (t i • ((gm g)⁻¹ * Xs i * gm g))).prod w)) :=
    ((M.rep τ (gm g)).restrictScalars ℝ).contDiff.comp (hw k (fun i => (gm g)⁻¹ * Xs i * gm g) hY)
  convert hsm using 1
  funext t
  have hP := Formalism.IndefR.PeterssonHilbertSpace.sm_prod_exp_mem (gramAt D V τ) k Xs (fun i => hX i) t
  have hQ := Formalism.IndefR.PeterssonHilbertSpace.sm_prod_exp_mem (gramAt D V τ) k (fun i => (gm g)⁻¹ * Xs i * gm g)
    (fun i => hY i) t
  have hc := conj_prod_exp (gm g) hgu k Xs t
  have e : (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod * gm g =
      gm g * (List.ofFn fun i => NormedSpace.exp (t i • ((gm g)⁻¹ * Xs i * gm g))).prod := by
    rw [← hc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hgd, Matrix.one_mul]
  show M.rep τ (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod (M.rep τ (gm g) w) =
    M.rep τ (gm g) (M.rep τ (List.ofFn fun i => NormedSpace.exp (t i • ((gm g)⁻¹ * Xs i * gm g))).prod w)
  rw [← ContinuousLinearMap.comp_apply, ← rep_mul M τ hP (gm_mem g), e, rep_mul M τ (gm_mem g) hQ,
    ContinuousLinearMap.comp_apply]

theorem sm_stable (M : DSModel V S) (τ : D.what₂.Tau) (g : Gt V τ) {w : M.H τ} (hw : w ∈ M.sm τ) :
    M.rep τ (gm g) w ∈ M.sm τ := by
  induction hw using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span (smoothVec_rep M τ g hx)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ a hx

variable (M : DSModel V S)

variable (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))

def MultiplicitySquareIntegrable (J : Set (GA D V)) (χ : GA D V → ℂ) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) : Prop :=
  IsInfFam θ → μ.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕 μ →
    ∀ T, IsMultMap θ M J χ T → ∀ v, MemLp (T v) 2 (μ.restrict 𝓕)

variable (V) in

def RightRegularUnitary (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) : Prop :=
  IsInfFam θ → μ.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕 μ → ∀ τ,
    ∃ π' : Gt V τ →* (Lp ℂ 2 (μ.restrict 𝓕) →L[ℂ] Lp ℂ 2 (μ.restrict 𝓕)), (∀ g f, ‖π' g f‖ = ‖f‖) ∧
      ∀ g (F : GA D V → ℂ), (∀ γ ∈ GQ V, ∀ x, F (γ * x) = F x) → ∀ hF : MemLp F 2 (μ.restrict 𝓕),
        ∃ hF' : MemLp (rTr V (atTau θ V τ (gm g)) F) 2 (μ.restrict 𝓕),
          π' g (hF.toLp F) = hF'.toLp (rTr V (atTau θ V τ (gm g)) F)

def ClosableInSquareIntegrable (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) : Prop :=
  IsInfFam θ → μ.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕 μ →
    ∀ τ (A : M.sm τ →ₗ[ℂ] (GA D V → ℂ)) (hA : ∀ w, MemLp (A w) 2 (μ.restrict 𝓕)),
      (∀ w, ∀ γ ∈ GQ V, ∀ x, A w (γ * x) = A w x) →
      (∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ w w' : M.sm τ, (w' : M.H τ) = M.rep τ g w →
        A w' = rTr V (atTau θ V τ g) (A w)) →
      (∀ x, ∃ ℓ : M.H τ →ₗ[ℂ] ℂ, Sobolev₂ (lieAt V τ) (M.rep τ) ℓ ∧ ∀ w : M.sm τ, ℓ w = A w x) →
      (∀ w, Continuous (A w)) →
      ∀ (u : ℕ → M.sm τ) (y : Lp ℂ 2 (μ.restrict 𝓕)), Tendsto (fun n => (u n : M.H τ)) atTop (𝓝 0) →
        Tendsto (fun n => (hA (u n)).toLp (A (u n))) atTop (𝓝 y) → y = 0

open Classical in

structure GoodMap (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (M : DSModel V S)
    (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (T : MMap M) : Prop where
  l2 : ∀ v, MemLp (T v) 2 (μ.restrict 𝓕)
  left : ∀ v, ∀ γ ∈ GQ V, ∀ x, T v (γ * x) = T v x
  equiv : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ (v : M.Vec) (w : M.sm τ),
    (w : M.H τ) = M.rep τ g (v τ) → T (Function.update v τ w) = rTr V (atTau θ V τ g) (T v)
  cont : ∀ τ (v : M.Vec) (x : GA D V), ∃ ℓ : M.H τ →ₗ[ℂ] ℂ, Sobolev₂ (lieAt V τ) (M.rep τ) ℓ ∧
    ∀ w : M.sm τ, ℓ w = T (Function.update v τ w) x
  cv : ∀ v, Continuous (T v)

variable {M θ} {J : Set (GA D V)} {χ : GA D V → ℂ} {μ : Measure (GA D V)} {𝓕 : Set (GA D V)}

open Classical in
theorem good_of_mem (hL2 : MultiplicitySquareIntegrable M θ J χ μ 𝓕) (hθ : IsInfFam θ) (hμ : μ.IsHaarMeasure)
    (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μ) {T : MMap M} (hT : T ∈ Mult θ M J χ) : GoodMap θ M μ 𝓕 T := by
  induction hT using Submodule.span_induction with
  | mem T hT => exact ⟨hL2 hθ hμ h𝓕 T hT, fun v => (hT.aut v).left, hT.equiv, hT.cont, fun v => (hT.aut v).cont⟩
  | zero =>
    refine ⟨fun v => ?_, fun v γ _ x => ?_, fun τ g _ v w _ => ?_, fun τ v x => ⟨0, sobCont_zero, fun w => ?_⟩,
      fun v => ?_⟩
    · rw [MultilinearMap.zero_apply]; exact MemLp.zero
    · simp
    · rw [MultilinearMap.zero_apply, MultilinearMap.zero_apply]; rfl
    · simp
    · rw [MultilinearMap.zero_apply]; exact continuous_zero
  | add T T' _ _ h h' =>
    refine ⟨fun v => ?_, fun v γ hγ x => ?_, fun τ g hg v w hw => ?_, fun τ v x => ?_, fun v => ?_⟩
    · rw [MultilinearMap.add_apply]; exact (h.l2 v).add (h'.l2 v)
    · rw [MultilinearMap.add_apply, Pi.add_apply, Pi.add_apply, h.left v γ hγ x, h'.left v γ hγ x]
    · rw [MultilinearMap.add_apply, MultilinearMap.add_apply, h.equiv τ g hg v w hw, h'.equiv τ g hg v w hw]; rfl
    · obtain ⟨ℓ, hℓ, e⟩ := h.cont τ v x
      obtain ⟨ℓ', hℓ', e'⟩ := h'.cont τ v x
      exact ⟨ℓ + ℓ', sobCont_add hℓ hℓ', fun w => by
        rw [LinearMap.add_apply, e, e', MultilinearMap.add_apply, Pi.add_apply]⟩
    · rw [MultilinearMap.add_apply]; exact (h.cv v).add (h'.cv v)
  | smul a T _ h =>
    refine ⟨fun v => ?_, fun v γ hγ x => ?_, fun τ g hg v w hw => ?_, fun τ v x => ?_, fun v => ?_⟩
    · rw [MultilinearMap.smul_apply]; exact (h.l2 v).const_smul a
    · rw [MultilinearMap.smul_apply, Pi.smul_apply, Pi.smul_apply, h.left v γ hγ x]
    · rw [MultilinearMap.smul_apply, MultilinearMap.smul_apply, h.equiv τ g hg v w hw]; rfl
    · obtain ⟨ℓ, hℓ, e⟩ := h.cont τ v x
      exact ⟨a • ℓ, sobCont_smul a hℓ, fun w => by
        rw [LinearMap.smul_apply, e, MultilinearMap.smul_apply, Pi.smul_apply]⟩
    · rw [MultilinearMap.smul_apply]; exact (h.cv v).const_smul a

set_option maxHeartbeats 1000000 in
open Classical in

theorem place (hSC : Formalism.IndefR.Leaf.SchurClosable) (hR : RightRegularUnitary V θ μ 𝓕)
    (hcl : ClosableInSquareIntegrable M θ μ 𝓕) (hθ : IsInfFam θ) (hμ : μ.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μ)
    {T T' : MMap M} (hT : GoodMap θ M μ 𝓕 T) (hT' : GoodMap θ M μ 𝓕 T') (τ : D.what₂.Tau) (v v' : M.Vec) :
    ∃ c : ℂ, ∀ x y : M.sm τ, ∫ g in 𝓕, star (T (Function.update v τ x) g) * T' (Function.update v' τ y) g ∂μ =
      c * ⟪(x : M.H τ), (y : M.H τ)⟫_ℂ := by
  haveI : CompleteSpace (M.H τ) := (M.ds τ).1
  obtain ⟨π', hπ'n, hπ'⟩ := hR hθ hμ h𝓕 τ
  have h₁ : ∀ w, MemLp (T.toLinearMap v τ w) 2 (μ.restrict 𝓕) := fun w => hT.l2 _
  have h₂ : ∀ w, MemLp (T'.toLinearMap v' τ w) 2 (μ.restrict 𝓕) := fun w => hT'.l2 _
  have hab : ∀ a b : ℂ, ∀ w, MemLp ((a • T.toLinearMap v τ + b • T'.toLinearMap v' τ) w) 2 (μ.restrict 𝓕) :=
    fun a b w => ((h₁ w).const_smul a).add ((h₂ w).const_smul b)
  have hcomb : ∀ a b : ℂ, toL2 (a • T.toLinearMap v τ + b • T'.toLinearMap v' τ) (hab a b) =
      a • toL2 (T.toLinearMap v τ) h₁ + b • toL2 (T'.toLinearMap v' τ) h₂ := by
    intro a b
    apply LinearMap.ext
    intro w
    show (hab a b w).toLp _ = a • (h₁ w).toLp _ + b • (h₂ w).toLp _
    rw [← MemLp.toLp_const_smul, ← MemLp.toLp_const_smul, ← MemLp.toLp_add]
    exact MemLp.toLp_congr _ _ (Filter.EventuallyEq.of_eq (by simp))
  obtain ⟨c, hc⟩ := polar (toL2 (T.toLinearMap v τ) h₁) (toL2 (T'.toLinearMap v' τ) h₂)
    (fun x y : M.sm τ => ⟪(x : M.H τ), (y : M.H τ)⟫_ℂ) (fun a b => by
      rw [← hcomb a b]
      generalize hab a b = hL
      generalize hLdef : a • T.toLinearMap v τ + b • T'.toLinearMap v' τ = L at hL ⊢
      have hLw : ∀ w : M.sm τ, L w = a • T (Function.update v τ w) + b • T' (Function.update v' τ w) := by
        intro w; rw [← hLdef]; rfl
      have hleft : ∀ (w : M.sm τ), ∀ γ ∈ GQ V, ∀ z, L w (γ * z) = L w z := by
        intro w γ hγ z
        rw [hLw, Pi.add_apply, Pi.add_apply, Pi.smul_apply, Pi.smul_apply, Pi.smul_apply, Pi.smul_apply,
          hT.left _ γ hγ z, hT'.left _ γ hγ z]
      have hequiv : ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ w w' : M.sm τ, (w' : M.H τ) = M.rep τ g w →
          L w' = rTr V (atTau θ V τ g) (L w) := by
        intro g hg w w' hw
        have e1 := hT.equiv τ g hg (Function.update v τ w) w' (by rw [Function.update_self]; exact hw)
        have e2 := hT'.equiv τ g hg (Function.update v' τ w) w' (by rw [Function.update_self]; exact hw)
        rw [Function.update_idem] at e1 e2
        rw [hLw, hLw, e1, e2]
        rfl
      have hcont : ∀ z, ∃ ℓ : M.H τ →ₗ[ℂ] ℂ, Sobolev₂ (lieAt V τ) (M.rep τ) ℓ ∧ ∀ w : M.sm τ, ℓ w = L w z := by
        intro z
        obtain ⟨ℓ₁, hℓ₁, e₁⟩ := hT.cont τ v z
        obtain ⟨ℓ₂, hℓ₂, e₂⟩ := hT'.cont τ v' z
        refine ⟨a • ℓ₁ + b • ℓ₂, sobCont_add (sobCont_smul a hℓ₁) (sobCont_smul b hℓ₂), fun w => ?_⟩
        rw [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply, e₁, e₂, hLw]
        rfl
      have hint : ∀ (g : Gt V τ) (x : M.sm τ) (hx : piR M τ g x ∈ M.sm τ),
          toL2 L hL ⟨piR M τ g x, hx⟩ = π' g (toL2 L hL x) := by
        intro g x hx
        obtain ⟨hF', he⟩ := hπ' g (L x) (hleft x) (hL x)
        rw [to_square_integrable_apply, to_square_integrable_apply, he]
        exact MemLp.toLp_congr _ _ (Filter.EventuallyEq.of_eq (hequiv (gm g) (gm_mem g) x ⟨piR M τ g x, hx⟩ rfl))
      have hcv : ∀ w : M.sm τ, Continuous (L w) := by
        intro w; rw [hLw]; exact ((hT.cv _).const_smul a).add ((hT'.cv _).const_smul b)
      have hclo := hcl hθ hμ h𝓕 τ L hL hleft hequiv hcont hcv
      have hclo' : ∀ (u : ℕ → M.sm τ) (y : Lp ℂ 2 (μ.restrict 𝓕)),
          Tendsto (fun n => (u n : M.H τ)) atTop (𝓝 0) → Tendsto (fun n => toL2 L hL (u n)) atTop (𝓝 y) →
            y = 0 := by
        intro u y h1 h2
        simp only [to_square_integrable_apply] at h2
        exact hclo u y h1 h2
      obtain ⟨c, -, hc⟩ := hSC (Gt V τ) (M.H τ) (Lp ℂ 2 (μ.restrict 𝓕)) (piR M τ) π' (piR_norm M τ) hπ'n
        (commutant_scalar M τ) (M.sm τ) (toL2 L hL) (sm_dense M τ) (fun g x hx => sm_stable M τ g hx)
        hint hclo'
      exact ⟨c, fun x y => hc x y⟩)
  refine ⟨c, fun x y => ?_⟩
  have e := hc x y
  rw [to_square_integrable_apply, to_square_integrable_apply, inner_toLp] at e
  exact e

open Classical in

theorem schurMult_of (hSC : Formalism.IndefR.Leaf.SchurClosable) (hL2 : MultiplicitySquareIntegrable M θ J χ μ 𝓕)
    (hR : RightRegularUnitary V θ μ 𝓕) (hcl : ClosableInSquareIntegrable M θ μ 𝓕) : SchurMult θ M J χ μ 𝓕 := by
  intro hθ hμ h𝓕 T hT T' hT'
  have gT := good_of_mem hL2 hθ hμ h𝓕 hT
  have gT' := good_of_mem hL2 hθ hμ h𝓕 hT'
  have hne : ∀ τ, ∃ e : M.sm τ, ⟪(e : M.H τ), (e : M.H τ)⟫_ℂ ≠ 0 := by
    intro τ
    obtain ⟨e, he⟩ := Formalism.IndefR.PeterssonHilbertSpace.smNonzero M τ
    refine ⟨e, ?_⟩
    rw [inner_self_ne_zero]
    exact fun h => he (Subtype.ext h)
  choose e he using hne
  have hP : (∏ τ, ⟪(e τ : M.H τ), (e τ : M.H τ)⟫_ℂ) ≠ 0 := Finset.prod_ne_zero_iff.2 fun τ _ => he τ
  have key := prod_of_place (fun v v' : M.Vec => ∫ g in 𝓕, star (T v g) * T' v' g ∂μ)
    (fun τ (x y : M.sm τ) => ⟪(x : M.H τ), (y : M.H τ)⟫_ℂ)
    (fun τ v v' => place hSC hR hcl hθ hμ h𝓕 gT gT' τ v v') e
  refine ⟨(∫ g in 𝓕, star (T e g) * T' e g ∂μ) / ∏ τ, ⟪(e τ : M.H τ), (e τ : M.H τ)⟫_ℂ,
    fun v v' => ⟨integrable_star_mul (gT.l2 v) (gT'.l2 v'), ?_⟩⟩
  have := key v v'
  beta_reduce at this
  rw [div_mul_eq_mul_div, eq_div_iff hP]
  linear_combination this

theorem schurMult (hL2 : MultiplicitySquareIntegrable M θ J χ μ 𝓕) (hR : RightRegularUnitary V θ μ 𝓕)
    (hcl : ClosableInSquareIntegrable M θ μ 𝓕) : SchurMult θ M J χ μ 𝓕 :=
  schurMult_of schur_closable hL2 hR hcl

end Formalism.IndefR.SchurOrthogonalityAlt
