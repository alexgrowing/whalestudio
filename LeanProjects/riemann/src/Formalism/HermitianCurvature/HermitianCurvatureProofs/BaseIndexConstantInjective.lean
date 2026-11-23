import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBGLet
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ActualAdjointnessFromHermitian
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FirstExpansionIdentity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SecondExpansionIdentity

open Matrix Finset
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBG

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.Qx5 Formalism.FourierDecayAlt.P.Qx2

section ring

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {D : Set (Q.Mx k r)}

def c0 (a : Fin (2 * r + k + 1)) : Fin (Q.mdim k r 0) := Fin.cast (by simp [Q.mdim]) a

theorem position_level_zero_coord (a : Fin (2 * r + k + 1)) : Q.posL k r 0 (c0 a) = a := by
  ext
  simp [Q.posL, c0]

theorem baseIndexConstant_injective {a b : Fin (2 * r + k + 1)} : c0 (k := k) a = c0 b ↔ a = b := by
  constructor
  · intro h
    exact Fin.ext (by simpa [c0] using congrArg Fin.val h)
  · intro h
    rw [h]

def E0 (hD : IsOpen D) (a b : Fin (2 * r + k + 1)) : Module.End ℂ (VS k r 0 D E) := Eh hD (c0 a) (c0 b)

theorem level_zero_derivation_relation (hD : IsOpen D) : GlRel (E0 (E := E) hD) := by
  intro a b c d
  have := Eh_gl (E := E) (i := 0) hD (c0 a) (c0 b) (c0 c) (c0 d)
  simp only [baseIndexConstant_injective] at this
  exact this

theorem good_foldr (hD : IsOpen D) :
    ∀ L : List ((Q.Mx k r → E) → Q.Mx k r → E), (∀ T ∈ L, Good k r 0 D T) →
      Good k r 0 D (fun f => L.foldr (fun T h => T h) f)
  | [], _ => good_id
  | T :: L, h => by
    simp only [List.foldr_cons]
    exact Good.comp (h T (by simp)) (good_foldr hD L (fun T' hT' => h T' (by simp [hT'])))

theorem good_top_level_zero (hD : IsOpen D) (u : ℂ) (a b : Fin (2 * r + k + 1)) :
    Good k r 0 D (QuantumDeterminants.Top (Q.EH (E := E) k r) u a b) := by
  have := good_top (E := E) (i := 0) hD u (c0 a) (c0 b)
  rwa [position_level_zero_coord, position_level_zero_coord] at this

theorem qminorOp_loc (hD : IsOpen D) {t : ℕ} (a b : Fin t → Fin (2 * r + k + 1)) (u : ℂ) (f f₂ : Q.Mx k r → E)
    (h : ∀ x ∈ Q.Glev k r 0 ∩ D, f x = f₂ x) (g : Q.Mx k r) (hg : g ∈ Q.Glev k r 0 ∩ D) :
    qminorOp (Q.EH k r) a b u f g = qminorOp (Q.EH k r) a b u f₂ g := by
  unfold qminorOp
  simp only [Finset.sum_apply, Pi.smul_apply]
  apply Finset.sum_congr rfl
  intro σ _
  congr 1
  exact (good_foldr hD _ (fun T hT => by
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hT
    exact good_top_level_zero hD _ _ _)).loc f f₂ h g hg

theorem AAop_loc (hD : IsOpen D) (m : ℕ) (hm : m ≤ r) (u : ℂ) (f f₂ : Q.Mx k r → E)
    (h : ∀ x ∈ Q.Glev k r 0 ∩ D, f x = f₂ x) (g : Q.Mx k r) (hg : g ∈ Q.Glev k r 0 ∩ D) :
    C3.AAop k r m hm u f g = C3.AAop k r m hm u f₂ g := by
  unfold C3.AAop
  apply Finset.sum_congr rfl
  intro c _
  split_ifs
  · rw [qminorOp_loc hD _ _ u f f₂ h g hg]
  · rfl

theorem AAvop_loc (hD : IsOpen D) (m : ℕ) (hm : m ≤ r) (ell : ℂ) (f f₂ : Q.Mx k r → E)
    (h : ∀ x ∈ Q.Glev k r 0 ∩ D, f x = f₂ x) (g : Q.Mx k r) (hg : g ∈ Q.Glev k r 0 ∩ D) :
    C3.AAvop k r m hm ell f g = C3.AAvop k r m hm ell f₂ g := by
  unfold C3.AAvop
  apply Finset.sum_congr rfl
  intro c _
  split_ifs
  · rw [qminorOp_loc hD _ _ _ f f₂ h g hg]
  · rfl

theorem quantum_minor_level_eq_hat (hD : IsOpen D) {t : ℕ} (a b : Fin t → Fin (2 * r + k + 1)) (u : ℂ) (v : VS k r 0 D E)
    (g : Q.Mx k r) (hg : g ∈ Q.Glev k r 0 ∩ D) :
    ((qminor (E0 (E := E) hD) a b u) v : Q.Mx k r → E) g = qminorOp (Q.EH k r) a b u (v : Q.Mx k r → E) g := by
  have := rep_qminor (E := E) (i := 0) hD (c0 ∘ a) (c0 ∘ b) u v g hg
  simp only [Function.comp_def, position_level_zero_coord] at this
  exact this

theorem raising_operator_level_zero (hD : IsOpen D) (m : ℕ) (hm : m ≤ r) (u : ℂ) (v : VS k r 0 D E) (g : Q.Mx k r)
    (hg : g ∈ Q.Glev k r 0 ∩ D) :
    C3.AAop k r m hm u (v : Q.Mx k r → E) g = ((C3.AAx k r (E0 (E := E) hD) (xi0 g) m hm u) v : Q.Mx k r → E) g := by
  unfold C3.AAop C3.AAx
  rw [LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro c _
  split_ifs
  · rw [LinearMap.smul_apply, Submodule.coe_smul, Pi.smul_apply, quantum_minor_level_eq_hat hD _ _ _ v g hg]
    rfl
  · simp

theorem lowering_operator_level_zero (hD : IsOpen D) (m : ℕ) (hm : m ≤ r) (ell : ℂ) (v : VS k r 0 D E) (g : Q.Mx k r)
    (hg : g ∈ Q.Glev k r 0 ∩ D) :
    C3.AAvop k r m hm ell (v : Q.Mx k r → E) g =
      ((C3.AAv k r (E0 (E := E) hD) (y0 g) m hm ell) v : Q.Mx k r → E) g := by
  unfold C3.AAvop C3.AAv
  rw [LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro c _
  split_ifs
  · rw [LinearMap.smul_apply, Submodule.coe_smul, Pi.smul_apply, quantum_minor_level_eq_hat hD _ _ _ v g hg]
    rfl
  · simp

def vK (hD : IsOpen D) (K : Q.Mx k r → E) (hK : Q.SmoothLev k r 0 D K) : VS k r 0 D E :=
  ⟨cut k r 0 D K, cut_mem hD hK⟩

def La (hD : IsOpen D) (K : Q.Mx k r → E) (hK : Q.SmoothLev k r 0 D K) (x₁ : Q.Mx k r) :
    Module.End ℂ (VS k r 0 D E) →ₗ[ℂ] E where
  toFun X := ((X (vK hD K hK)) : Q.Mx k r → E) x₁
  map_add' X Y := by simp [LinearMap.add_apply]
  map_smul' c X := by simp [LinearMap.smul_apply]

theorem level_zero_derivative_rule (hD : IsOpen D) (z' : Fin (2 * r + k + 1) → ℂ) (K : Q.Mx k r → E) (hK : Q.SmoothLev k r 0 D K)
    (hR : ∀ g ∈ Q.Glev k r 0 ∩ D, ∀ p q, C3.InNp k r p q → Q.EH k r p q K g = C3.dpsiP k r z' p q • K g)
    (p q : Fin (2 * r + k + 1)) (hpq : C3.InNp k r p q) :
    E0 hD p q (vK hD K hK) = C3.dpsiP k r z' p q • vK hD K hK := by
  refine Subtype.ext (funext fun g => ?_)
  by_cases hg : g ∈ Q.Glev k r 0 ∩ D
  · show ((Eh hD (c0 p) (c0 q) (vK hD K hK)) : Q.Mx k r → E) g = _
    rw [ev_E hD (c0 p) (c0 q) _ hg]
    have hl := (good_eh (E := E) hD (c0 p) (c0 q)).loc ((vK hD K hK) : Q.Mx k r → E) K
      (fun x hx => cut_of_mem K hx) g hg
    rw [hl]
    rw [position_level_zero_coord, position_level_zero_coord, hR g hg p q hpq]
    simp only [Submodule.coe_smul, Pi.smul_apply, vK]
    rw [cut_of_mem K hg]
  · rw [(E0 hD p q (vK hD K hK)).2.2 g hg]
    simp only [Submodule.coe_smul, Pi.smul_apply]
    rw [(vK hD K hK).2.2 g hg, smul_zero]

theorem La_rule (hD : IsOpen D) (z' : Fin (2 * r + k + 1) → ℂ) (K : Q.Mx k r → E) (hK : Q.SmoothLev k r 0 D K)
    (hR : ∀ g ∈ Q.Glev k r 0 ∩ D, ∀ p q, C3.InNp k r p q → Q.EH k r p q K g = C3.dpsiP k r z' p q • K g)
    (x₁ : Q.Mx k r) : C3.RightRuleFn k r z' (E0 hD) (La hD K hK x₁) := by
  intro X p q hpq
  show (((X * E0 hD p q : Module.End ℂ (VS k r 0 D E)) (vK hD K hK)) : Q.Mx k r → E) x₁ = C3.dpsiP k r z' p q • ((X (vK hD K hK)) : Q.Mx k r → E) x₁
  rw [Module.End.mul_apply, level_zero_derivative_rule hD z' K hK hR p q hpq, map_smul]
  rfl

theorem La_AAx (hD : IsOpen D) (K : Q.Mx k r → E) (hK : Q.SmoothLev k r 0 D K) (x₁ : Q.Mx k r)
    (hx₁ : x₁ ∈ Q.Glev k r 0 ∩ D) (m : ℕ) (hm : m ≤ r) (u : ℂ) :
    La hD K hK x₁ (C3.AAx k r (E0 hD) (xi0 x₁) m hm u) = C3.AAop k r m hm u K x₁ := by
  show (((C3.AAx k r (E0 hD) (xi0 x₁) m hm u) (vK hD K hK)) : Q.Mx k r → E) x₁ = _
  rw [← raising_operator_level_zero hD m hm u (vK hD K hK) x₁ hx₁]
  exact AAop_loc hD m hm u _ K (fun x hx => cut_of_mem K hx) x₁ hx₁

theorem La_AAv (hD : IsOpen D) (K : Q.Mx k r → E) (hK : Q.SmoothLev k r 0 D K) (x₁ : Q.Mx k r)
    (hx₁ : x₁ ∈ Q.Glev k r 0 ∩ D) (m : ℕ) (hm : m ≤ r) (ell : ℂ) :
    La hD K hK x₁ (C3.AAv k r (E0 hD) (y0 x₁) m hm ell) = C3.AAvop k r m hm ell K x₁ := by
  show (((C3.AAv k r (E0 hD) (y0 x₁) m hm ell) (vK hD K hK)) : Q.Mx k r → E) x₁ = _
  rw [← lowering_operator_level_zero hD m hm ell (vK hD K hK) x₁ hx₁]
  exact AAvop_loc hD m hm ell _ K (fun x hx => cut_of_mem K hx) x₁ hx₁

theorem AAop_congr' {m₁ m₂ : ℕ} (h : m₁ = m₂) (h₁ : m₁ ≤ r) (h₂ : m₂ ≤ r) (u : ℂ) (f : Q.Mx k r → E) (g : Q.Mx k r) :
    C3.AAop k r m₁ h₁ u f g = C3.AAop k r m₂ h₂ u f g := by
  subst h
  rfl

theorem AAvop_congr' {m₁ m₂ : ℕ} (h : m₁ = m₂) (h₁ : m₁ ≤ r) (h₂ : m₂ ≤ r) (u : ℂ) (f : Q.Mx k r → E) (g : Q.Mx k r) :
    C3.AAvop k r m₁ h₁ u f g = C3.AAvop k r m₂ h₂ u f g := by
  subst h
  rfl

theorem letter_plus_component_one (z z' : Fin (2 * r + k + 1) → ℂ) (j : ℕ) (hj : j ≤ r) (hj1 : 1 ≤ j) (Y : ℝ) (f : Q.Mx k r → E)
    (g : Q.Mx k r) :
    Formalism.FourierDecayAlt.D.vLet k r z z' j hj (true, Y) 1 f g =
      (Dmin k r z z' g ⟨j, by omega⟩)⁻¹ • C3.AAop k r (j - 1) (by omega) ((Y : ℂ) + ((2 * r + k : ℕ) : ℂ) / 2) f g := by
  show (if (1 : Fin 2) = 1 ∧ j = 0 then 0 else _) = _
  rw [if_neg (by omega)]
  show (if true = true then _ else _) = _
  rw [if_pos rfl, AAop_congr' (m₂ := j - 1) (by simp) _ (by omega)]

theorem letter_plus_component_zero (z z' : Fin (2 * r + k + 1) → ℂ) (j : ℕ) (hj : j ≤ r) (Y : ℝ) (f : Q.Mx k r → E) (g : Q.Mx k r) :
    Formalism.FourierDecayAlt.D.vLet k r z z' j hj (true, Y) 0 f g =
      (Dmin k r z z' g ⟨j, by omega⟩)⁻¹ • C3.AAop k r j hj ((Y : ℂ) + ((2 * r + k : ℕ) : ℂ) / 2) f g := by
  show (if (0 : Fin 2) = 1 ∧ j = 0 then 0 else _) = _
  rw [if_neg (by simp)]
  show (if true = true then _ else _) = _
  rw [if_pos rfl, AAop_congr' (m₂ := j) (by simp) _ hj]

theorem letter_minus_component_one (z z' : Fin (2 * r + k + 1) → ℂ) (j : ℕ) (hj : j ≤ r) (hj1 : 1 ≤ j) (Y : ℝ) (f : Q.Mx k r → E)
    (g : Q.Mx k r) :
    Formalism.FourierDecayAlt.D.vLet k r z z' j hj (false, Y) 1 f g =
      (conj (Dmin k r z z' g ⟨j, by omega⟩))⁻¹ •
        C3.AAvop k r (j - 1) (by omega) ((Y : ℂ) - ((2 * r + k : ℕ) : ℂ) / 2) f g := by
  show (if (1 : Fin 2) = 1 ∧ j = 0 then 0 else _) = _
  rw [if_neg (by omega)]
  show (if false = true then _ else _) = _
  rw [if_neg (by simp), AAvop_congr' (m₂ := j - 1) (by simp) _ (by omega)]

theorem letter_minus_component_zero (z z' : Fin (2 * r + k + 1) → ℂ) (j : ℕ) (hj : j ≤ r) (Y : ℝ) (f : Q.Mx k r → E) (g : Q.Mx k r) :
    Formalism.FourierDecayAlt.D.vLet k r z z' j hj (false, Y) 0 f g =
      (conj (Dmin k r z z' g ⟨j, by omega⟩))⁻¹ • C3.AAvop k r j hj ((Y : ℂ) - ((2 * r + k : ℕ) : ℂ) / 2) f g := by
  show (if (0 : Fin 2) = 1 ∧ j = 0 then 0 else _) = _
  rw [if_neg (by simp)]
  show (if false = true then _ else _) = _
  rw [if_neg (by simp), AAvop_congr' (m₂ := j) (by simp) _ hj]

theorem dmin_nf (z z' : Fin (2 * r + k + 1) → ℂ) (x₁ : Q.Mx k r) (i0 s : ℕ) (hh : Matrix (Fin i0) (Fin i0) ℂ) (τ : ℂ)
    (hj : i0 + s ≤ r)
    (hnf : ∀ (a : Fin r) (p : Fin (2 * r + k + 1)), a.val < i0 + s →
      xi0 x₁ a p = if p.val < i0 + s then C3.Zb i0 s hh τ a.val p.val else 0)
    (n : ℕ) (hn : n ≤ i0 + s) :
    Dmin k r z z' x₁ ⟨n, by omega⟩ = C3.Dlead i0 s hh τ n := by
  rw [← det_upper_minor_eq_minor z z' x₁ n (by omega)]
  unfold C3.Dlead
  congr 1
  ext a b
  simp only [Matrix.of_apply]
  rw [hnf _ _ (by simp; omega), if_pos (by simp [C3.xR, eI]; omega)]
  simp [C3.xR, eI]

theorem letter_plus_component_one_eq_smul_component_zero (hD : IsOpen D) (z z' : Fin (2 * r + k + 1) → ℂ) (i0 s : ℕ) (hs : 1 ≤ s) (hj : i0 + s ≤ r)
    (hh : Matrix (Fin i0) (Fin i0) ℂ) (τ : ℂ) (hdet : hh.det ≠ 0) (hτ : τ ≠ 0) (x₁ : Q.Mx k r)
    (hx₁ : x₁ ∈ Q.Glev k r 0 ∩ D)
    (hnf : ∀ (a : Fin r) (p : Fin (2 * r + k + 1)), a.val < i0 + s →
      xi0 x₁ a p = if p.val < i0 + s then C3.Zb i0 s hh τ a.val p.val else 0)
    (K : Q.Mx k r → E) (hK : Q.SmoothLev k r 0 D K)
    (hR : ∀ g ∈ Q.Glev k r 0 ∩ D, ∀ p q, C3.InNp k r p q → Q.EH k r p q K g = C3.dpsiP k r z' p q • K g) (Y : ℝ) :
    Formalism.FourierDecayAlt.D.vLet k r z z' (i0 + s) hj (true, Y) 1 K x₁ =
      ((-1 : ℂ) ^ (s - 1) * τ⁻¹) • Formalism.FourierDecayAlt.D.vLet k r z z' i0 (by omega) (true, Y) 0 K x₁ := by
  have hE := Formalism.FourierDecayAlt.P.SignAntidiagonal.first_expansion_identity (Module.End ℂ (VS k r 0 D E)) E k r z' (E0 hD) (La hD K hK x₁)
    (xi0 x₁) i0 s hh τ ((Y : ℂ) + ((2 * r + k : ℕ) : ℂ) / 2) hs hj (La_rule hD z' K hK hR x₁) hdet hτ hnf
  rw [La_AAx hD K hK x₁ hx₁, La_AAx hD K hK x₁ hx₁] at hE
  rw [← dmin_nf z z' x₁ i0 s hh τ hj hnf (i0 + s) le_rfl, ← dmin_nf z z' x₁ i0 s hh τ hj hnf i0 (by omega)] at hE
  rw [letter_plus_component_one z z' (i0 + s) hj (by omega), letter_plus_component_zero z z' i0 (by omega), smul_smul]
  rw [smul_smul] at hE
  exact hE

theorem letter_minus_component_one_eq_smul_component_zero (hD : IsOpen D) (z z' : Fin (2 * r + k + 1) → ℂ) (i0 s : ℕ) (hs : 1 ≤ s) (hj : i0 + s ≤ r)
    (hh : Matrix (Fin i0) (Fin i0) ℂ) (τ : ℂ) (hdet : hh.det ≠ 0) (hτ : τ ≠ 0) (x₁ : Q.Mx k r)
    (hx₁ : x₁ ∈ Q.Glev k r 0 ∩ D) (hxG : x₁ ∈ B.GV k r)
    (hnf : ∀ (a : Fin r) (p : Fin (2 * r + k + 1)), a.val < i0 + s →
      xi0 x₁ a p = if p.val < i0 + s then C3.Zb i0 s hh τ a.val p.val else 0)
    (hnfy : ∀ (a : Fin r) (p : Fin (2 * r + k + 1)), a.val < i0 + s →
      y0 x₁ a p = if r + k < p.val ∧ 2 * r + k - p.val < i0 + s then star (C3.Zb i0 s hh τ a.val (2 * r + k - p.val))
        else 0)
    (K : Q.Mx k r → E) (hK : Q.SmoothLev k r 0 D K)
    (hR : ∀ g ∈ Q.Glev k r 0 ∩ D, ∀ p q, C3.InNp k r p q → Q.EH k r p q K g = C3.dpsiP k r z' p q • K g) (Y : ℝ) :
    Formalism.FourierDecayAlt.D.vLet k r z z' (i0 + s) hj (false, Y) 1 K x₁ =
      ((-1 : ℂ) ^ (s - 1) * (conj τ)⁻¹) • Formalism.FourierDecayAlt.D.vLet k r z z' i0 (by omega) (false, Y) 0 K x₁ := by
  have hE := Formalism.FourierDecayAlt.P.SignAntidiagonal.second_expansion_identity (Module.End ℂ (VS k r 0 D E)) E k r z' (E0 hD) (La hD K hK x₁)
    (y0 x₁) i0 s hh τ ((Y : ℂ) - ((2 * r + k : ℕ) : ℂ) / 2) hs hj (level_zero_derivation_relation hD) (La_rule hD z' K hK hR x₁) hdet hτ hnfy
  rw [La_AAv hD K hK x₁ hx₁, La_AAv hD K hK x₁ hx₁] at hE
  rw [← dmin_nf z z' x₁ i0 s hh τ hj hnf (i0 + s) le_rfl, ← dmin_nf z z' x₁ i0 s hh τ hj hnf i0 (by omega)] at hE
  rw [letter_minus_component_one z z' (i0 + s) hj (by omega), letter_minus_component_zero z z' i0 (by omega), smul_smul]
  rw [smul_smul] at hE
  simp only [starRingEnd_apply]
  exact hE

end ring

end Formalism.FourierDecayAlt.P.PBG
