import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRCoreCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRDatumConst
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SumDualVectorEqZeta
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ActualAdjointnessFromHermitian
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NFRadRedA

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP

noncomputable section

namespace TW

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

abbrev Ix (k r : ℕ) := Fin (mdim k r (Fin.last r))

abbrev pL (k r : ℕ) (j : Ix k r) : Fin (2 * r + k + 1) := posL k r (Fin.last r) j

def un (k r : ℕ) (p : Ix k r × Ix k r) : Q.Mx k r := Matrix.single (pL k r p.1) (pL k r p.2) 1

abbrev FC (k r : ℕ) := List (ℂ × List (Ix k r × Ix k r))

section words

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {D : Set (Q.Mx k r)}

def ev (L : FC k r) (F : Q.Mx k r → E) (g : Q.Mx k r) : E :=
  L.foldr (fun p acc => acc + p.1 • wordR (p.2.map (un k r)) F g) 0

def pre (q : Ix k r × Ix k r) (L : FC k r) : FC k r := L.map fun p => (p.1, q :: p.2)

def sc (u : ℂ) (L : FC k r) : FC k r := L.map fun p => (u * p.1, p.2)

def topL (u : ℂ) (q : Ix k r × Ix k r) (L : FC k r) : FC k r :=
  (if pL k r q.1 = pL k r q.2 then sc u L else []) ++ pre q L

def foldL (Qs : List (ℂ × (Ix k r × Ix k r))) : FC k r := Qs.foldr (fun t L => topL t.1 t.2 L) [(1, [])]

theorem ev_append (L L' : FC k r) (F : Q.Mx k r → E) (g : Q.Mx k r) : ev (L ++ L') F g = ev L F g + ev L' F g := by
  induction L with
  | nil => simp [ev]
  | cons p L ih =>
    show ev (L ++ L') F g + p.1 • wordR (p.2.map (un k r)) F g = ev L F g + p.1 • wordR (p.2.map (un k r)) F g + ev L' F g
    rw [ih]
    abel

theorem ev_sc (u : ℂ) (L : FC k r) (F : Q.Mx k r → E) (g : Q.Mx k r) : ev (sc u L) F g = u • ev L F g := by
  induction L with
  | nil => simp [ev, sc]
  | cons p L ih =>
    show ev (sc u L) F g + (u * p.1) • wordR (p.2.map (un k r)) F g = u • (ev L F g + p.1 • wordR (p.2.map (un k r)) F g)
    rw [ih, smul_add, mul_smul]

theorem good_word (hD : IsOpen D) (w : List (Ix k r × Ix k r)) :
    Qx2.Good k r (Fin.last r) D (fun F : Q.Mx k r → E => wordR (w.map (un k r)) F) := by
  induction w with
  | nil => exact Qx2.good_id
  | cons p w ih => exact (Qx2.good_eh hD p.1 p.2).comp ih

theorem sm_ev (hD : IsOpen D) (L : FC k r) {F : Q.Mx k r → E} (hF : Q.SmoothLev k r (Fin.last r) D F) :
    Q.SmoothLev k r (Fin.last r) D (ev L F) := by
  induction L with
  | nil => exact Qx2.smooth_zero
  | cons p L ih => exact Qx2.smooth_add ih (Qx2.smooth_smul ((good_word hD p.2).sm F hF) p.1)

theorem good_at_zero {T : (Q.Mx k r → E) → Q.Mx k r → E} (hT : Qx2.Good k r (Fin.last r) D T) {x : Q.Mx k r}
    (hx : x ∈ Q.Glev k r (Fin.last r) ∩ D) : T (fun _ => (0 : E)) x = 0 := by
  have h := hT.lin (fun _ => 0) (fun _ => 0) 1 Qx2.smooth_zero Qx2.smooth_zero x hx
  simpa using h

theorem eh_ev (hD : IsOpen D) (q : Ix k r × Ix k r) (L : FC k r) {F : Q.Mx k r → E}
    (hF : Q.SmoothLev k r (Fin.last r) D F) {x : Q.Mx k r} (hx : x ∈ Q.Glev k r (Fin.last r) ∩ D) :
    Q.EH k r (pL k r q.1) (pL k r q.2) (ev L F) x = ev (pre q L) F x := by
  induction L with
  | nil => exact good_at_zero (Qx2.good_eh hD q.1 q.2) hx
  | cons p L ih =>
    have h := (Qx2.good_eh (E := E) hD q.1 q.2).lin (ev L F) (wordR (p.2.map (un k r)) F) p.1 (sm_ev hD L hF)
      ((good_word hD p.2).sm F hF) x hx
    refine h.trans ?_
    show Q.EH k r (pL k r q.1) (pL k r q.2) (ev L F) x +
      p.1 • Q.EH k r (pL k r q.1) (pL k r q.2) (wordR (p.2.map (un k r)) F) x = _
    rw [ih]
    rfl

theorem top_ev (hD : IsOpen D) (u : ℂ) (q : Ix k r × Ix k r) (L : FC k r) {F : Q.Mx k r → E}
    (hF : Q.SmoothLev k r (Fin.last r) D F) {h : Q.Mx k r → E} (hh : ∀ x ∈ Q.Glev k r (Fin.last r) ∩ D, h x = ev L F x)
    {x : Q.Mx k r} (hx : x ∈ Q.Glev k r (Fin.last r) ∩ D) :
    QuantumDeterminants.Top (Q.EH k r) u (pL k r q.1) (pL k r q.2) h x = ev (topL u q L) F x := by
  have h1 : Q.EH k r (pL k r q.1) (pL k r q.2) h x = Q.EH k r (pL k r q.1) (pL k r q.2) (ev L F) x :=
    (Qx2.good_eh (E := E) hD q.1 q.2).loc h (ev L F) hh x hx
  have h2 := eh_ev hD q L hF hx
  unfold topL
  rw [ev_append]
  show (if pL k r q.1 = pL k r q.2 then u • h x else 0) + Q.EH k r (pL k r q.1) (pL k r q.2) h x = _
  rw [h1, h2, hh x hx]
  split_ifs with hc
  · rw [ev_sc]
  · rfl

theorem fold_ev (hD : IsOpen D) {F : Q.Mx k r → E} (hF : Q.SmoothLev k r (Fin.last r) D F)
    (Qs : List (ℂ × (Ix k r × Ix k r))) : ∀ x ∈ Q.Glev k r (Fin.last r) ∩ D,
    (Qs.map fun t => QuantumDeterminants.Top (Q.EH (E := E) k r) t.1 (pL k r t.2.1) (pL k r t.2.2)).foldr (fun T h => T h) F x =
      ev (foldL Qs) F x := by
  induction Qs with
  | nil =>
    intro x _
    simp [foldL, ev, wordR]
  | cons t Qs ih =>
    intro x hx
    exact top_ev hD t.1 t.2 (foldL Qs) hF ih hx

def QL {t : ℕ} (a b : Fin t → Ix k r) (u : ℂ) (σ : Equiv.Perm (Fin t)) : List (ℂ × (Ix k r × Ix k r)) :=
  List.ofFn fun l : Fin t => (u - ((l : ℕ) : ℂ), (a (σ l), b l))

theorem qminor_ev (hD : IsOpen D) {t : ℕ} (a b : Fin t → Ix k r) (u : ℂ) {F : Q.Mx k r → E}
    (hF : Q.SmoothLev k r (Fin.last r) D F) {x : Q.Mx k r} (hx : x ∈ Q.Glev k r (Fin.last r) ∩ D) :
    qminorOp (Q.EH k r) (posL k r (Fin.last r) ∘ a) (posL k r (Fin.last r) ∘ b) u F x =
      ∑ σ : Equiv.Perm (Fin t), ((Equiv.Perm.sign σ : ℤ) : ℂ) • ev (foldL (QL a b u σ)) F x := by
  simp only [qminorOp, Finset.sum_apply, Pi.smul_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [← fold_ev hD hF _ x hx, QL, List.map_ofFn]
  rfl

theorem posL_wI (j : Ix k r) : ∃ a : Fin (k + 1), pL k r j = wI k r a := by
  have h := j.isLt
  simp only [mdim, Fin.val_last, Nat.sub_self, Nat.mul_zero, Nat.zero_add] at h
  exact ⟨⟨j.val, h⟩, Fin.ext (by simp [posL, wI, Nat.add_comm])⟩

theorem un_unit (p : Ix k r × Ix k r) : ∃ a b : Fin (k + 1), un k r p = Matrix.single (wI k r a) (wI k r b) 1 := by
  obtain ⟨a, ha⟩ := posL_wI p.1
  obtain ⟨b, hb⟩ := posL_wI p.2
  exact ⟨a, b, by rw [un, ha, hb]⟩

end words

def AnnulusPolynomial (TT : ℝ) (f : ℂ → ℂ) : Prop :=
  ∃ p : MvPolynomial (Fin 3) ℂ, ∀ ζ : ℂ, TT < Complex.normSq ζ → f ζ = MvPolynomial.eval ![ζ, conj ζ, sig TT ζ] p

theorem polynomial_of_annulus_polynomial {TT : ℝ} {f : ℂ → ℂ} (h : AnnulusPolynomial TT f) : PS TT f := by
  obtain ⟨p, hp⟩ := h
  exact ⟨0, p, fun ζ hζ => by rw [pow_zero, one_mul, hp ζ hζ]⟩

theorem annulus_polynomial_const (TT : ℝ) (c : ℂ) : AnnulusPolynomial TT (fun _ => c) := ⟨MvPolynomial.C c, fun ζ _ => by simp⟩

theorem annulus_polynomial_conj (TT : ℝ) : AnnulusPolynomial TT (fun ζ => conj ζ) := ⟨MvPolynomial.X 1, fun ζ _ => by simp⟩

theorem annulus_polynomial_sigma (TT : ℝ) : AnnulusPolynomial TT (fun ζ => sig TT ζ) := ⟨MvPolynomial.X 2, fun ζ _ => by simp⟩

theorem annulus_polynomial_add {TT : ℝ} {f g : ℂ → ℂ} (hf : AnnulusPolynomial TT f) (hg : AnnulusPolynomial TT g) : AnnulusPolynomial TT (fun ζ => f ζ + g ζ) := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  exact ⟨p + q, fun ζ hζ => by rw [map_add, ← hp ζ hζ, ← hq ζ hζ]⟩

theorem annulus_polynomial_mul {TT : ℝ} {f g : ℂ → ℂ} (hf : AnnulusPolynomial TT f) (hg : AnnulusPolynomial TT g) : AnnulusPolynomial TT (fun ζ => f ζ * g ζ) := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  exact ⟨p * q, fun ζ hζ => by rw [map_mul, ← hp ζ hζ, ← hq ζ hζ]⟩

theorem annulus_polynomial_congr {TT : ℝ} {f g : ℂ → ℂ} (hf : AnnulusPolynomial TT f) (h : ∀ ζ : ℂ, TT < Complex.normSq ζ → g ζ = f ζ) : AnnulusPolynomial TT g := by
  obtain ⟨p, hp⟩ := hf
  exact ⟨p, fun ζ hζ => by rw [h ζ hζ, hp ζ hζ]⟩

section sec

open Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.P.SettingConstruction Formalism.FourierDecayAlt.P.TwoByOneBlock Formalism.FourierDecayAlt.P.TheSec

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ}

theorem section_point_mem_level_domain (hk : 1 ≤ k) (hz : inWb k r z) (hz' : inWb k r z') (hT : 0 < Tz k r z) (hT' : 0 < Tz k r z') {ζ : ℂ}
    (hζ : Tz k r z * Tz k r z' < Complex.normSq ζ) : mu0 k r z z' ζ ∈ Q.Glev k r (Fin.last r) ∩ Dp k r z z' := by
  have hsec := TheSec.theSection_isSection k r z z' hk hz hz' hT hT'
  refine ⟨NFRadRedA.uwb_glev (NFRadRedA.muZ_uwb hsec hζ), ?_⟩
  show 0 < Q.GGl k r z z' (NF.muZ k r (TheSec.theSection k r z z') ζ)
  unfold Q.GGl
  rw [NFRadRedA.zeta_muZ hz hz' hsec hζ]
  linarith

theorem y_eq (hk : 1 ≤ k) (hz : inWb k r z) (hz' : inWb k r z') (hT : 0 < Tz k r z) (hT' : 0 < Tz k r z') {ζ : ℂ}
    (hζ : Tz k r z * Tz k r z' < Complex.normSq ζ) :
    (mu0 k r z z' ζ)⁻¹ *ᵥ z = (((-(Real.sqrt (Tz k r z) * DC.sR (Tz k r z) (Tz k r z') ζ) : ℝ) : ℂ)) • DC.EE' k r z' +
      (((Real.sqrt (Tz k r z) : ℝ) : ℂ) * star (wZ (Tz k r z) (Tz k r z') ζ) * (((Real.sqrt (Tz k r z') : ℝ) : ℂ))⁻¹) • z' := by
  have ha := SettingConstruction.herm_self k r z hz
  have hb := SettingConstruction.herm_self k r z' hz'
  unfold mu0
  rw [DC.muZ_eq, emb_inv (DC.secB_mem hk hT hT' ha hb hζ), DC.emb_mulVec_of _ hz, DC.secB_inv_a hk hT hT' ha hb hζ, DC.jV_add,
    DC.jV_smul, DC.jV_smul, jV_wbPart hz']
  rfl

theorem annulus_polynomial_inverse_coords (hk : 1 ≤ k) (hz : inWb k r z) (hz' : inWb k r z') (hT : 0 < Tz k r z) (hT' : 0 < Tz k r z')
    (p : Fin (2 * r + k + 1)) : AnnulusPolynomial (Tz k r z * Tz k r z') (fun ζ => ((mu0 k r z z' ζ)⁻¹ *ᵥ z) p) := by
  set T := Tz k r z with hTd
  set T' := Tz k r z' with hTd'
  have hP : 0 < T * T' := mul_pos hT hT'
  refine annulus_polynomial_congr (annulus_polynomial_add
    (annulus_polynomial_mul (annulus_polynomial_const _ (-(((Real.sqrt T : ℝ) : ℂ) / ((Real.sqrt (T * T') : ℝ) : ℂ)) * DC.EE' k r z' p)) (annulus_polynomial_sigma _))
    (annulus_polynomial_mul (annulus_polynomial_const _ (((Real.sqrt T : ℝ) : ℂ) * (-((Real.sqrt T * Real.sqrt T' : ℝ) : ℂ)⁻¹) *
      (((Real.sqrt T' : ℝ) : ℂ))⁻¹ * z' p)) (annulus_polynomial_conj _))) ?_
  intro ζ hζ
  rw [y_eq hk hz hz' hT hT' hζ]
  have h1 : ((DC.sR T T' ζ : ℝ) : ℂ) = sig (T * T') ζ / ((Real.sqrt (T * T') : ℝ) : ℂ) := by
    have e : Complex.normSq ζ / (T * T') - 1 = (Complex.normSq ζ - T * T') / (T * T') := by
      field_simp
    unfold DC.sR sig
    rw [e, Real.sqrt_div' _ hP.le]
    push_cast
    rfl
  have h2 : star (wZ T T' ζ) = (-((Real.sqrt T * Real.sqrt T' : ℝ) : ℂ)⁻¹) * conj ζ := by
    have e1 : star ((Real.sqrt T * Real.sqrt T' : ℝ) : ℂ) = ((Real.sqrt T * Real.sqrt T' : ℝ) : ℂ) := Complex.conj_ofReal _
    unfold wZ
    rw [star_mul', star_neg, star_inv₀, e1]
    rfl
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [h2, Complex.ofReal_neg, Complex.ofReal_mul, h1]
  ring

end sec

abbrev Fam (k r : ℕ) := ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E], (Q.Mx k r → E) → ℂ → E

def HasRep (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (Φ : Fam k r) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (κ : ι → ℂ → ℂ) (w : ι → List (Ix k r × Ix k r)),
    (∀ i, AnnulusPolynomial (Tz k r z * Tz k r z') (κ i)) ∧
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (F : Q.Mx k r → E),
      Q.SmoothLev k r (Fin.last r) (Dp k r z z') F → ∀ ζ : ℂ, Tz k r z * Tz k r z' < Complex.normSq ζ →
        Φ E F ζ = ∑ i, κ i ζ • wordR ((w i).map (un k r)) F (mu0 k r z z' ζ)

section rep

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ}

theorem hr_congr {Φ Ψ : Fam k r} (h : HasRep k r z z' Φ)
    (e : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (F : Q.Mx k r → E),
      Q.SmoothLev k r (Fin.last r) (Dp k r z z') F → ∀ ζ : ℂ, Tz k r z * Tz k r z' < Complex.normSq ζ →
        Ψ E F ζ = Φ E F ζ) : HasRep k r z z' Ψ := by
  obtain ⟨ι, inst, κ, w, hκ, h⟩ := h
  exact ⟨ι, inst, κ, w, hκ, fun E _ _ F hF ζ hζ => (e E F hF ζ hζ).trans (h E F hF ζ hζ)⟩

theorem hr_zero : HasRep k r z z' (fun E _ _ _ _ => (0 : E)) :=
  ⟨Empty, inferInstance, fun i => i.elim, fun i => i.elim, fun i => i.elim, fun _ _ _ _ _ _ _ => by simp⟩

theorem hr_word (c : ℂ) (w : List (Ix k r × Ix k r)) :
    HasRep k r z z' (fun _ _ _ F ζ => c • wordR (w.map (un k r)) F (mu0 k r z z' ζ)) :=
  ⟨Unit, inferInstance, fun _ _ => c, fun _ => w, fun _ => annulus_polynomial_const _ c, fun _ _ _ _ _ _ _ => by simp⟩

theorem hr_add {Φ Ψ : Fam k r} (h1 : HasRep k r z z' Φ) (h2 : HasRep k r z z' Ψ) :
    HasRep k r z z' (fun E _ _ F ζ => Φ E F ζ + Ψ E F ζ) := by
  obtain ⟨ι, inst, κ, w, hκ, h⟩ := h1
  obtain ⟨ι', inst', κ', w', hκ', h'⟩ := h2
  refine ⟨ι ⊕ ι', inferInstance, Sum.elim κ κ', Sum.elim w w', ?_, ?_⟩
  · rintro (i | i)
    · exact hκ i
    · exact hκ' i
  · intro E _ _ F hF ζ hζ
    show Φ E F ζ + Ψ E F ζ = _
    rw [Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr]
    rw [h E F hF ζ hζ, h' E F hF ζ hζ]

theorem hr_coef {a : ℂ → ℂ} (ha : AnnulusPolynomial (Tz k r z * Tz k r z') a) {Φ : Fam k r} (h : HasRep k r z z' Φ) :
    HasRep k r z z' (fun E _ _ F ζ => a ζ • Φ E F ζ) := by
  obtain ⟨ι, inst, κ, w, hκ, h⟩ := h
  refine ⟨ι, inst, fun i ζ => a ζ * κ i ζ, w, fun i => annulus_polynomial_mul ha (hκ i), ?_⟩
  intro E _ _ F hF ζ hζ
  show a ζ • Φ E F ζ = _
  rw [h E F hF ζ hζ, Finset.smul_sum]
  simp only [mul_smul]

theorem hr_sum {J : Type} (s : Finset J) (Φ : J → Fam k r) (h : ∀ j ∈ s, HasRep k r z z' (Φ j)) :
    HasRep k r z z' (fun E _ _ F ζ => ∑ j ∈ s, Φ j E F ζ) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact hr_congr hr_zero (fun _ _ _ _ _ _ _ => by simp)
  | insert j s hj ih =>
    refine hr_congr (hr_add (h j (by simp)) (ih fun l hl => h l (by simp [hl]))) ?_
    intro E _ _ F _ ζ _
    exact Finset.sum_insert hj

theorem hr_ev (L : FC k r) : HasRep k r z z' (fun _ _ _ F ζ => ev L F (mu0 k r z z' ζ)) := by
  induction L with
  | nil => exact hr_zero
  | cons p L ih => exact hr_add ih (hr_word p.1 p.2)

theorem hr_minor (hk : 1 ≤ k) (hz : inWb k r z) (hz' : inWb k r z') (hT : 0 < Tz k r z) (hT' : 0 < Tz k r z')
    {t : ℕ} (a b : Fin t → Ix k r) (u : ℂ) :
    HasRep k r z z' (fun _ _ _ F ζ =>
      qminorOp (Q.EH k r) (posL k r (Fin.last r) ∘ a) (posL k r (Fin.last r) ∘ b) u F (mu0 k r z z' ζ)) := by
  refine hr_congr (hr_sum Finset.univ
    (fun σ : Equiv.Perm (Fin t) => fun E _ _ F ζ =>
      ((Equiv.Perm.sign σ : ℤ) : ℂ) • ev (foldL (QL a b u σ)) F (mu0 k r z z' ζ))
    (fun σ _ => hr_coef (annulus_polynomial_const _ _) (hr_ev _))) ?_
  intro E _ _ F hF ζ hζ
  exact qminor_ev (Qx5.Dp_open k r z z') a b u hF (section_point_mem_level_domain hk hz hz' hT hT' hζ)

theorem lower_unipotent_has_representation (hk : 1 ≤ k) (hz : inWb k r z) (hz' : inWb k r z') (hT : 0 < Tz k r z) (hT' : 0 < Tz k r z') (Y : ℂ) :
    HasRep k r z z' (fun _ _ _ F ζ => Q.tL k r z z' (Fin.last r) Y 1 0 F (mu0 k r z z' ζ)) := by
  have hfv : fvec k r z (Fin.last r) = z := by
    unfold fvec
    rw [dif_neg (by simp)]
  refine hr_congr (hr_sum Finset.univ
    (fun i : Ix k r => fun E _ _ F ζ => ∑ j ∈ (Finset.univ : Finset (Ix k r)),
      (-((-1 : ℂ) ^ ((i : ℕ) + (j : ℕ)) * xbv k r z' (Fin.last r) i) * ((mu0 k r z z' ζ)⁻¹ *ᵥ z) (pL k r j)) •
        qminorOp (Q.EH k r) (posL k r (Fin.last r) ∘ skip1 i) (posL k r (Fin.last r) ∘ skip1 j)
          (uC k r (Fin.last r) Y) F (mu0 k r z z' ζ))
    (fun i _ => hr_sum Finset.univ _ (fun j _ =>
      hr_coef (annulus_polynomial_mul (annulus_polynomial_const _ _) (annulus_polynomial_inverse_coords hk hz hz' hT hT' _)) (hr_minor hk hz hz' hT hT' _ _ _)))) ?_
  intro E _ _ F _ ζ _
  show (-(chatL (Q.EH k r) (posL k r (Fin.last r)) (uC k r (Fin.last r) Y) (yv k r z (Fin.last r))
    (fun _ => xbv k r z' (Fin.last r)) F)) (mu0 k r z z' ζ) = _
  simp only [Pi.neg_apply, chatL, yv, hfv, ← Finset.sum_neg_distrib, ← neg_smul, neg_mul]

end rep

end TW

theorem lower_unipotent_matrix_words : LowerUnipotentMatrixWords := by
  intro k r z z' hk hz hz' hT hT' Y
  obtain ⟨ι, inst, κ, w, hκ, h⟩ := TW.lower_unipotent_has_representation hk hz hz' hT hT' Y
  refine ⟨Fintype.card ι, fun i => κ ((Fintype.equivFin ι).symm i),
    fun i => (w ((Fintype.equivFin ι).symm i)).map (TW.un k r), fun i => TW.polynomial_of_annulus_polynomial (hκ _), ?_, ?_⟩
  · intro i Z hZ
    rw [List.mem_map] at hZ
    obtain ⟨p, _, rfl⟩ := hZ
    exact TW.un_unit p
  · intro E _ _ F hF ζ hζ
    exact (h E F hF ζ hζ).trans (Equiv.sum_comp (Fintype.equivFin ι).symm
      (fun i => κ i ζ • wordR ((w i).map (TW.un k r)) F (mu0 k r z z' ζ))).symm

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP
