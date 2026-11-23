import Formalism.HermitianCurvature.StatementB
import Formalism.FormalDegreeBessel.FinalG
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CartanInvolutionConjTransposeMul
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ComplexifiedDerivativeCommutator

open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal

noncomputable section

namespace Formalism.FourierDecayAlt.P.BetaSesquilinearity

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
open scoped ContDiff

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

lemma Hsq (k r : ℕ) : Hpk k r * Hpk k r = 1 := (hpkFacts k r).2.1

lemma Hdet (k r : ℕ) : IsUnit (Hpk k r).det := by
  exact Matrix.isUnit_det_of_right_inverse (Hsq k r)

lemma gv_one : (1 : Mat k r) ∈ GV k r := by
  show (1 : Mat k r)ᴴ * Hpk k r * 1 = Hpk k r
  simp

lemma gv_mul {a b : Mat k r} (ha : a ∈ GV k r) (hb : b ∈ GV k r) : a * b ∈ GV k r := by
  have ha' : aᴴ * Hpk k r * a = Hpk k r := ha
  have hb' : bᴴ * Hpk k r * b = Hpk k r := hb
  show (a * b)ᴴ * Hpk k r * (a * b) = Hpk k r
  rw [Matrix.conjTranspose_mul]
  calc bᴴ * aᴴ * Hpk k r * (a * b) = bᴴ * (aᴴ * Hpk k r * a) * b := by simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [ha', hb']

lemma gv_inv {a : Mat k r} (ha : a ∈ GV k r) : a⁻¹ ∈ GV k r := by
  have hg : aᴴ * Hpk k r * a = Hpk k r := ha
  have hu : IsUnit a.det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    have h1 := congrArg Matrix.det hg
    rw [Matrix.det_mul, h0, mul_zero] at h1
    exact (Hdet k r).ne_zero h1.symm
  have h1 : a * a⁻¹ = 1 := Matrix.mul_nonsing_inv a hu
  have h2 : (a⁻¹)ᴴ * aᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
  show (a⁻¹)ᴴ * Hpk k r * a⁻¹ = Hpk k r
  calc (a⁻¹)ᴴ * Hpk k r * a⁻¹ = (a⁻¹)ᴴ * (aᴴ * Hpk k r * a) * a⁻¹ := by rw [hg]
    _ = ((a⁻¹)ᴴ * aᴴ) * Hpk k r * (a * a⁻¹) := by simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]

lemma gv_unit {a : Mat k r} (ha : a ∈ GV k r) : IsUnit a.det := by
  have hg : aᴴ * Hpk k r * a = Hpk k r := ha
  rw [isUnit_iff_ne_zero]
  intro h0
  have h1 := congrArg Matrix.det hg
  rw [Matrix.det_mul, h0, mul_zero] at h1
  exact (Hdet k r).ne_zero h1.symm

lemma gv_closed : IsClosed (GV k r) := by
  show IsClosed {g : Mat k r | gᴴ * Hpk k r * g = Hpk k r}
  exact isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul
    continuous_id) continuous_const

lemma exp_mem {X : Mat k r} (hX : inLie k r X) : NormedSpace.exp X ∈ GV k r := by
  have hX' : Xᴴ * Hpk k r + Hpk k r * X = 0 := hX
  have hH : Hpk k r * Hpk k r = 1 := Hsq k r
  have hHu : IsUnit (Hpk k r) := (Matrix.isUnit_iff_isUnit_det _).mpr (Hdet k r)
  have hinv : (Hpk k r)⁻¹ = Hpk k r := Matrix.inv_eq_left_inv hH
  have hXH : Xᴴ = Hpk k r * (-X) * (Hpk k r)⁻¹ := by
    rw [hinv]
    have h1 : Xᴴ * Hpk k r = -(Hpk k r * X) := eq_neg_of_add_eq_zero_left hX'
    calc Xᴴ = Xᴴ * Hpk k r * Hpk k r := by rw [Matrix.mul_assoc, hH, Matrix.mul_one]
      _ = Hpk k r * (-X) * Hpk k r := by rw [h1, Matrix.mul_neg, Matrix.neg_mul]
  show (NormedSpace.exp X)ᴴ * Hpk k r * NormedSpace.exp X = Hpk k r
  rw [← Matrix.exp_conjTranspose, hXH, Matrix.exp_conj _ _ hHu, hinv, Matrix.exp_neg]
  have hu : IsUnit (NormedSpace.exp X).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (Matrix.isUnit_exp X)
  calc Hpk k r * (NormedSpace.exp X)⁻¹ * Hpk k r * Hpk k r * NormedSpace.exp X
      = Hpk k r * ((NormedSpace.exp X)⁻¹ * NormedSpace.exp X) := by
        rw [Matrix.mul_assoc (Hpk k r * _) (Hpk k r) (Hpk k r), hH, Matrix.mul_one, Matrix.mul_assoc]
    _ = Hpk k r := by rw [Matrix.nonsing_inv_mul _ hu, Matrix.mul_one]

lemma lie_rsmul {X : Mat k r} (hX : inLie k r X) (t : ℝ) : inLie k r ((t : ℂ) • X) := by
  have hX' : Xᴴ * Hpk k r + Hpk k r * X = 0 := hX
  have h : star (t : ℂ) = (t : ℂ) := by simp
  show ((t : ℂ) • X)ᴴ * Hpk k r + Hpk k r * ((t : ℂ) • X) = 0
  rw [Matrix.conjTranspose_smul, h, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hX', smul_zero]

lemma lie_neg {X : Mat k r} (hX : inLie k r X) : inLie k r (-X) := by
  have hX' : Xᴴ * Hpk k r + Hpk k r * X = 0 := hX
  show (-X)ᴴ * Hpk k r + Hpk k r * (-X) = 0
  rw [Matrix.conjTranspose_neg, Matrix.neg_mul, Matrix.mul_neg, ← neg_add, hX', neg_zero]

def crv (x : Bool × Mat k r) (g : Mat k r) (t : ℝ) : Mat k r :=
  if x.1 then NormedSpace.exp (-((t : ℂ) • x.2)) * g else g * NormedSpace.exp ((t : ℂ) • x.2)

def dirv (x : Bool × Mat k r) (g : Mat k r) : Mat k r := if x.1 then -x.2 * g else g * x.2

def Dx (x : Bool × Mat k r) (f : Mat k r → E) : Mat k r → E := if x.1 then LdV x.2 f else RdV x.2 f

def Dw (w : List (Bool × Mat k r)) (f : Mat k r → E) : Mat k r → E := w.foldr Dx f

lemma Dx_eq (x : Bool × Mat k r) (f : Mat k r → E) (g : Mat k r) :
    Dx x f g = deriv (fun t : ℝ => f (crv x g t)) 0 := by
  rcases x with ⟨_ | _, X⟩ <;> rfl

lemma crv_zero (x : Bool × Mat k r) (g : Mat k r) : crv x g 0 = g := by
  rcases x with ⟨_ | _, X⟩ <;> simp [crv]

lemma crv_hasDerivAt (x : Bool × Mat k r) (g : Mat k r) : HasDerivAt (crv x g) (dirv x g) 0 := by
  rcases x with ⟨_ | _, X⟩
  · exact hasDerivAt_mul_exp_smul_zero g X
  · have h := (mulRightRealCLM g).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_matrix_exp_smul_at_zero (-X))
    have e : (fun t : ℝ => NormedSpace.exp (-((t : ℂ) • X)) * g) =
        (mulRightRealCLM g) ∘ fun t : ℝ => NormedSpace.exp ((t : ℂ) • -X) := by
      funext t
      simp only [Function.comp_apply, smul_neg]
      rfl
    show HasDerivAt (fun t : ℝ => NormedSpace.exp (-((t : ℂ) • X)) * g) (-X * g) 0
    rw [e]
    exact h

lemma crv_mem {x : Bool × Mat k r} (hx : inLie k r x.2) {g : Mat k r} (hg : g ∈ GV k r) (t : ℝ) :
    crv x g t ∈ GV k r := by
  rcases x with ⟨_ | _, X⟩
  · exact gv_mul hg (exp_mem (lie_rsmul hx t))
  · exact gv_mul (exp_mem (lie_neg (lie_rsmul hx t))) hg

lemma crv_ev {x : Bool × Mat k r} {g : Mat k r} {O : Set (Mat k r)} (hO : IsOpen O) (hg : g ∈ O) :
    ∀ᶠ t : ℝ in 𝓝 0, crv x g t ∈ O := by
  have hc := (crv_hasDerivAt x g).continuousAt
  have h : O ∈ 𝓝 (crv x g 0) := by rw [crv_zero]; exact hO.mem_nhds hg
  exact hc.preimage_mem_nhds h

lemma Dx_congr_loc {x : Bool × Mat k r} (hx : inLie k r x.2) {O : Set (Mat k r)} (hO : IsOpen O)
    {f f₂ : Mat k r → E} (h : ∀ g ∈ GV k r, g ∈ O → f g = f₂ g) :
    ∀ g ∈ GV k r, g ∈ O → Dx x f g = Dx x f₂ g := by
  intro g hg hgO
  rw [Dx_eq, Dx_eq]
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [crv_ev (x := x) hO hgO] with t ht
  exact h _ (crv_mem hx hg t) ht

lemma Dx_congr {x : Bool × Mat k r} (hx : inLie k r x.2)
    {f f₂ : Mat k r → E} (h : ∀ g ∈ GV k r, f g = f₂ g) :
    ∀ g ∈ GV k r, Dx x f g = Dx x f₂ g := by
  intro g hg
  exact Dx_congr_loc hx isOpen_univ (fun g hg _ => h g hg) g hg (Set.mem_univ g)

lemma Dw_congr_loc {w : List (Bool × Mat k r)} (hw : ∀ x ∈ w, inLie k r x.2) {O : Set (Mat k r)}
    (hO : IsOpen O) {f f₂ : Mat k r → E} (h : ∀ g ∈ GV k r, g ∈ O → f g = f₂ g) :
    ∀ g ∈ GV k r, g ∈ O → Dw w f g = Dw w f₂ g := by
  induction w with
  | nil => exact h
  | cons x w ih =>
    intro g hg hgO
    exact Dx_congr_loc (hw x (by simp)) hO (ih (fun y hy => hw y (by simp [hy]))) g hg hgO

lemma Dw_congr {w : List (Bool × Mat k r)} (hw : ∀ x ∈ w, inLie k r x.2)
    {f f₂ : Mat k r → E} (h : ∀ g ∈ GV k r, f g = f₂ g) :
    ∀ g ∈ GV k r, Dw w f g = Dw w f₂ g := by
  intro g hg
  exact Dw_congr_loc hw isOpen_univ (fun g hg _ => h g hg) g hg (Set.mem_univ g)

lemma Dx_zero (x : Bool × Mat k r) : Dx x (fun _ => (0 : E)) = fun _ => 0 := by
  funext g
  rw [Dx_eq]
  simp

lemma Dw_zero (w : List (Bool × Mat k r)) : Dw w (fun _ => (0 : E)) = fun _ => 0 := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    show Dx x (Dw w (fun _ => (0 : E))) = _
    rw [ih, Dx_zero]

lemma Dw_append (w w' : List (Bool × Mat k r)) (f : Mat k r → E) :
    Dw (w ++ w') f = Dw w (Dw w' f) := by
  show (w ++ w').foldr Dx f = w.foldr Dx (w'.foldr Dx f)
  rw [List.foldr_append]

lemma Dx_hasDerivAt {x : Bool × Mat k r} (hx : inLie k r x.2) {f f' : Mat k r → E} {U : Set (Mat k r)}
    {g : Mat k r} (hU : IsOpen U) (hgU : g ∈ U) (hg : g ∈ GV k r) (hd : DifferentiableAt ℝ f' g)
    (hff : ∀ h ∈ U, h ∈ GV k r → f h = f' h) :
    HasDerivAt (fun t : ℝ => f (crv x g t)) (fderiv ℝ f' g (dirv x g)) 0 := by
  have hcomp : HasDerivAt (fun t : ℝ => f' (crv x g t)) (fderiv ℝ f' g (dirv x g)) 0 :=
    hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) (crv_hasDerivAt x g) (crv_zero x g).symm
  refine hcomp.congr_of_eventuallyEq ?_
  filter_upwards [crv_ev (x := x) hU hgU] with t ht
  exact hff _ ht (crv_mem hx hg t)

def dirL (x : Bool × Mat k r) : Mat k r →L[ℝ] Mat k r :=
  if x.1 then LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ (-x.2)) else mulRightRealCLM x.2

lemma dirL_apply (x : Bool × Mat k r) (g : Mat k r) : dirL x g = dirv x g := by
  rcases x with ⟨_ | _, X⟩ <;> rfl

lemma sCkOn_mono {m m' : ℕ∞} (h : m ≤ m') {UU : Set (Mat k r)} {f : Mat k r → E} (hf : CkOn m' UU f) :
    CkOn m UU f := by
  intro g₀ hg₀
  obtain ⟨U, f', hU, hgU, hc, he⟩ := hf g₀ hg₀
  exact ⟨U, f', hU, hgU, hc.of_le (WithTop.coe_le_coe.mpr h), he⟩

lemma CkOn_Dx {m : ℕ∞} {x : Bool × Mat k r} (hx : inLie k r x.2) {UU : Set (Mat k r)}
    {f : Mat k r → E} (hf : CkOn (m + 1) UU f) : CkOn m UU (Dx x f) := by
  intro g₀ hg₀
  obtain ⟨U, f', hU, hgU, hc, hff⟩ := hf g₀ hg₀
  refine ⟨U, fun h => fderiv ℝ f' h (dirL x h), hU, hgU, ?_, ?_⟩
  · have h1 := hc.fderiv_of_isOpen (m := (m : WithTop ℕ∞)) hU (by push_cast; exact le_rfl)
    exact h1.clm_apply (dirL x).contDiff.contDiffOn
  · intro h hh hhG
    have hd : DifferentiableAt ℝ f' h :=
      (hc.differentiableOn (by push_cast; simp)).differentiableAt (hU.mem_nhds hh)
    show Dx x f h = fderiv ℝ f' h (dirL x h)
    rw [Dx_eq, dirL_apply]
    exact (Dx_hasDerivAt hx hU hh hhG hd hff).deriv

lemma CkOn_Dw {m : ℕ∞} {w : List (Bool × Mat k r)} (hw : ∀ x ∈ w, inLie k r x.2) {UU : Set (Mat k r)}
    {f : Mat k r → E} (hf : CkOn (m + w.length) UU f) : CkOn m UU (Dw w f) := by
  induction w generalizing m with
  | nil =>
    show CkOn m UU f
    simpa using hf
  | cons x w ih =>
    have h1 : CkOn (m + 1 + w.length) UU f := by
      have e : m + 1 + (w.length : ℕ∞) = m + ((x :: w).length : ℕ∞) := by
        simp only [List.length_cons, Nat.cast_add, Nat.cast_one]; ring
      rw [e]; exact hf
    exact CkOn_Dx (hw x (by simp)) (ih (fun y hy => hw y (by simp [hy])) h1)

lemma CkOn_diff {x : Bool × Mat k r} (hx : inLie k r x.2) {UU : Set (Mat k r)}
    {f : Mat k r → E} (hf : CkOn 1 UU f) {g : Mat k r} (hgU : g ∈ UU) (hg : g ∈ GV k r) :
    HasDerivAt (fun t : ℝ => f (crv x g t)) (Dx x f g) 0 := by
  obtain ⟨U, f', hU, hgU', hc, he⟩ := hf g hgU
  have hd : DifferentiableAt ℝ f' g :=
    (hc.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hgU')
  have h := Dx_hasDerivAt hx hU hgU' hg hd he
  rw [Dx_eq]
  rwa [h.deriv]

lemma CkOn_cont {UU : Set (Mat k r)} (hUU : UU ⊆ GV k r) {f : Mat k r → E} (hf : CkOn 0 UU f) :
    ContinuousOn f UU := by
  intro g hg
  obtain ⟨U, f', hU, hgU, hc, he⟩ := hf g hg
  have h1 : ContinuousAt f' g := hc.continuousOn.continuousAt (hU.mem_nhds hgU)
  apply (h1.continuousWithinAt (s := UU)).congr_of_eventuallyEq
  · filter_upwards [nhdsWithin_le_nhds (hU.mem_nhds hgU), self_mem_nhdsWithin] with y hyU hyUU
    exact he y hyU (hUU hyUU)
  · exact he g hgU (hUU hg)

end Formalism.FourierDecayAlt.P.BetaSesquilinearity

namespace Formalism.FourierDecayAlt.P.BetaSesquilinearity

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
open scoped ContDiff

section Frob

attribute [local instance] Matrix.frobeniusSeminormedAddCommGroup Matrix.frobeniusNormedAddCommGroup
  Matrix.frobeniusNormedSpace Matrix.frobeniusNormedRing

lemma gN_eq_frob {k r : ℕ} (g : Mat k r) : gN g = ‖g‖ := by
  unfold gN
  rw [Matrix.frobenius_norm_def, Real.sqrt_eq_rpow]
  simp only [Complex.normSq_eq_norm_sq, Real.rpow_two]

lemma gN_ge_one {k r : ℕ} {g : Mat k r} (hg : g ∈ GV k r) : 1 ≤ gN g := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  have hH0 : Hpk k r ≠ 0 := by
    intro h0
    have h1 := congrFun (congrFun h0 ⟨r, by omega⟩) ⟨r, by omega⟩
    clear h0 hg' hg
    simp [Hpk] at h1 <;> split_ifs at h1 <;> norm_num at h1
  have hn : 0 < ‖Hpk k r‖ := norm_pos_iff.mpr hH0
  have h2 : ‖Hpk k r‖ ≤ ‖g‖ * ‖Hpk k r‖ * ‖g‖ := by
    calc ‖Hpk k r‖ = ‖gᴴ * Hpk k r * g‖ := by rw [hg']
      _ ≤ ‖gᴴ * Hpk k r‖ * ‖g‖ := norm_mul_le _ _
      _ ≤ ‖gᴴ‖ * ‖Hpk k r‖ * ‖g‖ := by gcongr; exact norm_mul_le _ _
      _ = ‖g‖ * ‖Hpk k r‖ * ‖g‖ := by rw [Matrix.frobenius_norm_conjTranspose]
  rw [gN_eq_frob]
  by_contra hlt
  push_neg at hlt
  have h3 : ‖g‖ * ‖g‖ < 1 := by nlinarith [norm_nonneg g]
  nlinarith [mul_pos (sub_pos.mpr h3) hn]

end Frob

end Formalism.FourierDecayAlt.P.BetaSesquilinearity

namespace Formalism.FourierDecayAlt.P.BetaSesquilinearity

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
open scoped ContDiff

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E']

lemma Dx_smul (c : ℂ) (x : Bool × Mat k r) (f : Mat k r → E) :
    Dx x (fun g => c • f g) = fun g => c • Dx x f g := by
  funext g
  rw [Dx_eq, Dx_eq]
  show deriv (fun t : ℝ => c • f (crv x g t)) 0 = c • deriv (fun t : ℝ => f (crv x g t)) 0
  by_cases hc : c = 0
  · subst hc; simp
  by_cases hd : DifferentiableAt ℝ (fun t : ℝ => f (crv x g t)) 0
  · exact deriv_const_smul c hd
  · have hd' : ¬ DifferentiableAt ℝ (fun t : ℝ => c • f (crv x g t)) 0 := by
      intro h'
      apply hd
      have h2 : DifferentiableAt ℝ (fun t : ℝ => c⁻¹ • (c • f (crv x g t))) 0 := h'.const_smul c⁻¹
      simpa [smul_smul, inv_mul_cancel₀ hc] using h2
    rw [deriv_zero_of_not_differentiableAt hd, deriv_zero_of_not_differentiableAt hd', smul_zero]

lemma Dw_smul (c : ℂ) (w : List (Bool × Mat k r)) (f : Mat k r → E) :
    Dw w (fun g => c • f g) = fun g => c • Dw w f g := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    show Dx x (Dw w (fun g => c • f g)) = fun g => c • Dx x (Dw w f) g
    rw [ih, Dx_smul]

lemma CkOn_smul {m : ℕ∞} {UU : Set (Mat k r)} (c : ℂ) {f : Mat k r → E} (hf : CkOn m UU f) :
    CkOn m UU (fun g => c • f g) := by
  intro g₀ hg₀
  obtain ⟨U, f', hU, hgU, hc, he⟩ := hf g₀ hg₀
  exact ⟨U, fun g => c • f' g, hU, hgU, hc.const_smul c, fun g hg hgG => by
    show c • f g = c • f' g
    rw [he g hg hgG]⟩

lemma CkOn_add {m : ℕ∞} {UU : Set (Mat k r)} {f₁ f₂ : Mat k r → E} (h₁ : CkOn m UU f₁)
    (h₂ : CkOn m UU f₂) : CkOn m UU (fun g => f₁ g + f₂ g) := by
  intro g₀ hg₀
  obtain ⟨U₁, f₁', hU₁, hg₁, hc₁, he₁⟩ := h₁ g₀ hg₀
  obtain ⟨U₂, f₂', hU₂, hg₂, hc₂, he₂⟩ := h₂ g₀ hg₀
  refine ⟨U₁ ∩ U₂, fun g => f₁' g + f₂' g, hU₁.inter hU₂, ⟨hg₁, hg₂⟩,
    (hc₁.mono Set.inter_subset_left).add (hc₂.mono Set.inter_subset_right), ?_⟩
  intro g hg hgG
  show f₁ g + f₂ g = f₁' g + f₂' g
  rw [he₁ g hg.1 hgG, he₂ g hg.2 hgG]

lemma CkOn_zero {m : ℕ∞} {UU : Set (Mat k r)} : CkOn m UU (fun _ => (0 : E)) := fun _ _ =>
  ⟨Set.univ, fun _ => 0, isOpen_univ, Set.mem_univ _, contDiffOn_const, fun _ _ _ => rfl⟩

lemma Dx_add {x : Bool × Mat k r} (hx : inLie k r x.2) {f₁ f₂ : Mat k r → E}
    (h₁ : CkOn 1 (GV k r) f₁) (h₂ : CkOn 1 (GV k r) f₂) :
    ∀ g ∈ GV k r, Dx x (fun g => f₁ g + f₂ g) g = Dx x f₁ g + Dx x f₂ g := by
  intro g hg
  have h1 := CkOn_diff hx h₁ hg hg
  have h2 := CkOn_diff hx h₂ hg hg
  rw [Dx_eq]
  exact (h1.add h2).deriv

lemma Dw_add {w : List (Bool × Mat k r)} (hw : ∀ x ∈ w, inLie k r x.2) {f₁ f₂ : Mat k r → E}
    (h₁ : CkOn w.length (GV k r) f₁) (h₂ : CkOn w.length (GV k r) f₂) :
    ∀ g ∈ GV k r, Dw w (fun g => f₁ g + f₂ g) g = Dw w f₁ g + Dw w f₂ g := by
  induction w with
  | nil => intro g _; rfl
  | cons x w ih =>
    intro g hg
    have hw' : ∀ y ∈ w, inLie k r y.2 := fun y hy => hw y (by simp [hy])
    have hx : inLie k r x.2 := hw x (by simp)
    have e : (((x :: w).length : ℕ) : ℕ∞) = 1 + (w.length : ℕ∞) := by
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one]; ring
    have h₁' : CkOn (1 + w.length) (GV k r) f₁ := by rw [← e]; exact h₁
    have h₂' : CkOn (1 + w.length) (GV k r) f₂ := by rw [← e]; exact h₂
    have hle : ((w.length : ℕ) : ℕ∞) ≤ (((x :: w).length : ℕ) : ℕ∞) := by
      exact_mod_cast Nat.le_succ w.length
    have hm₁ : CkOn (w.length) (GV k r) f₁ := sCkOn_mono hle h₁
    have hm₂ : CkOn (w.length) (GV k r) f₂ := sCkOn_mono hle h₂
    show Dx x (Dw w (fun g => f₁ g + f₂ g)) g = Dx x (Dw w f₁) g + Dx x (Dw w f₂) g
    rw [Dx_congr hx (ih hw' hm₁ hm₂) g hg]
    exact Dx_add hx (CkOn_Dw hw' h₁') (CkOn_Dw hw' h₂') g hg

def ap (a : Mat k r → (E →L[ℂ] E')) (Φ : Mat k r → E) : Mat k r → E' := fun g => a g (Φ g)

structure Pr (O UU : Set (Mat k r)) (m : ℕ∞) (a : Mat k r → (E →L[ℂ] E')) (Φ : Mat k r → E) : Prop where
  ha : CkOn m UU a
  hΦ : CkOn m (GV k r) Φ
  hz : ∀ g ∈ GV k r, g ∈ O → Φ g = 0

variable {O UU : Set (Mat k r)} {a : Mat k r → (E →L[ℂ] E')} {Φ : Mat k r → E}

lemma Pr.mono {m m' : ℕ∞} (hm : m ≤ m') (h : Pr O UU m' a Φ) : Pr O UU m a Φ := ⟨sCkOn_mono hm h.ha, sCkOn_mono hm h.hΦ, h.hz⟩

lemma Pr.left {m : ℕ∞} {x : Bool × Mat k r} (hx : inLie k r x.2) (h : Pr O UU (m + 1) a Φ) :
    Pr O UU m (Dx x a) Φ := ⟨CkOn_Dx hx h.ha, sCkOn_mono le_self_add h.hΦ, h.hz⟩

lemma Dx_vanish (hO : IsOpen O) {x : Bool × Mat k r} (hx : inLie k r x.2) {f : Mat k r → E}
    (hz : ∀ g ∈ GV k r, g ∈ O → f g = 0) : ∀ g ∈ GV k r, g ∈ O → Dx x f g = 0 := by
  intro g hg hgO
  rw [Dx_congr_loc hx hO (f₂ := fun _ => (0 : E)) hz g hg hgO, Dx_zero]

lemma Dw_vanish (hO : IsOpen O) {w : List (Bool × Mat k r)} (hw : ∀ x ∈ w, inLie k r x.2)
    {f : Mat k r → E} (hz : ∀ g ∈ GV k r, g ∈ O → f g = 0) : ∀ g ∈ GV k r, g ∈ O → Dw w f g = 0 := by
  induction w with
  | nil => exact hz
  | cons x w ih => exact Dx_vanish hO (hw x (by simp)) (ih fun y hy => hw y (by simp [hy]))

lemma Pr.right (hO : IsOpen O) {m : ℕ∞} {x : Bool × Mat k r} (hx : inLie k r x.2)
    (h : Pr O UU (m + 1) a Φ) : Pr O UU m a (Dx x Φ) := ⟨sCkOn_mono le_self_add h.ha, CkOn_Dx hx h.hΦ, Dx_vanish hO hx h.hz⟩

lemma Pr.apz (h : Pr O UU 0 a Φ) : ∀ g ∈ GV k r, g ∈ O → ap a Φ g = 0 := by
  intro g hg hgO
  show a g (Φ g) = 0
  rw [h.hz g hg hgO, map_zero]

lemma Pr.ck (hO : IsOpen O) (hcov : ∀ g ∈ GV k r, g ∈ O ∨ g ∈ UU) {m : ℕ∞} (h : Pr O UU m a Φ) :
    CkOn m (GV k r) (ap a Φ) := by
  intro g₀ hg₀
  rcases hcov g₀ hg₀ with hO' | hU'
  · refine ⟨O, fun _ => 0, hO, hO', contDiffOn_const, fun g hg hgG => ?_⟩
    show a g (Φ g) = 0
    rw [h.hz g hgG hg, map_zero]
  · obtain ⟨U₁, a', hU₁, hg₁, hc₁, he₁⟩ := h.ha g₀ hU'
    obtain ⟨U₂, Φ', hU₂, hg₂, hc₂, he₂⟩ := h.hΦ g₀ hg₀
    have hc₁' : ContDiffOn ℝ (m : WithTop ℕ∞) (fun g => (a' g).restrictScalars ℝ) (U₁ ∩ U₂) :=
      (ContinuousLinearMap.restrictScalarsL ℂ E E' ℝ ℝ).contDiff.comp_contDiffOn
        (hc₁.mono Set.inter_subset_left)
    refine ⟨U₁ ∩ U₂, fun g => a' g (Φ' g), hU₁.inter hU₂, ⟨hg₁, hg₂⟩,
      hc₁'.clm_apply (hc₂.mono Set.inter_subset_right), ?_⟩
    intro g hg hgG
    show a g (Φ g) = a' g (Φ' g)
    rw [he₁ g hg.1 hgG, he₂ g hg.2 hgG]

lemma Pr.leib (hO : IsOpen O) (hcov : ∀ g ∈ GV k r, g ∈ O ∨ g ∈ UU) {x : Bool × Mat k r}
    (hx : inLie k r x.2) (h : Pr O UU 1 a Φ) :
    ∀ g ∈ GV k r, Dx x (ap a Φ) g = ap (Dx x a) Φ g + ap a (Dx x Φ) g := by
  intro g hg
  rcases hcov g hg with hgO | hgU
  · have h1 : Dx x (ap a Φ) g = 0 := Dx_vanish hO hx (Pr.apz (h.mono (by simp))) g hg hgO
    have h2 : Φ g = 0 := h.hz g hg hgO
    have h3 : Dx x Φ g = 0 := Dx_vanish hO hx h.hz g hg hgO
    rw [h1]
    show (0 : E') = Dx x a g (Φ g) + a g (Dx x Φ g)
    rw [h2, h3, map_zero, map_zero, add_zero]
  · have ha := CkOn_diff hx h.ha hgU hg
    have hΦ := CkOn_diff hx h.hΦ hg hg
    have ha' := (ContinuousLinearMap.restrictScalarsL ℂ E E' ℝ ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) ha
    have hp := ha'.clm_apply hΦ
    have e1 : ∀ A : E →L[ℂ] E', (ContinuousLinearMap.restrictScalarsL ℂ E E' ℝ ℝ) A =
        A.restrictScalars ℝ := fun A => rfl
    simp only [Function.comp_def, crv_zero, e1, ContinuousLinearMap.coe_restrictScalars'] at hp
    rw [Dx_eq]
    exact hp.deriv

lemma leib_bound (hO : IsOpen O) (hcov : ∀ g ∈ GV k r, g ∈ O ∨ g ∈ UU) (g : Mat k r) (hg : g ∈ GV k r)
    (M : ℝ) (w : List (Bool × Mat k r)) :
    ∀ (a : Mat k r → (E →L[ℂ] E')) (Φ : Mat k r → E), (∀ x ∈ w, inLie k r x.2) → Pr O UU w.length a Φ →
      (∀ w₁ w₂ : List (Bool × Mat k r), w₁.Sublist w → w₂.Sublist w → w₁.length + w₂.length = w.length →
        ‖Dw w₁ a g‖ * ‖Dw w₂ Φ g‖ ≤ M) →
      ‖Dw w (ap a Φ) g‖ ≤ 2 ^ w.length * M := by
  induction w using List.reverseRecOn with
  | nil =>
    intro a Φ _ _ hM
    have := hM [] [] (List.Sublist.refl _) (List.Sublist.refl _) rfl
    simp only [Dw, List.foldr_nil, List.length_nil, pow_zero, one_mul] at this ⊢
    exact ((a g).le_opNorm _).trans this
  | append_singleton w x ih =>
    intro a Φ hw hP hM
    have hw' : ∀ y ∈ w, inLie k r y.2 := fun y hy => hw y (by simp [hy])
    have hx : inLie k r x.2 := hw x (by simp)
    have hlen : (((w ++ [x]).length : ℕ) : ℕ∞) = (w.length : ℕ∞) + 1 := by simp
    rw [hlen] at hP
    have hPl := hP.left hx
    have hPr := hP.right hO hx
    have e1 : Dw (w ++ [x]) (ap a Φ) g = Dw w (ap (Dx x a) Φ) g + Dw w (ap a (Dx x Φ)) g := by
      rw [Dw_append]
      show Dw w (Dx x (ap a Φ)) g = _
      rw [Dw_congr hw' (Pr.leib hO hcov hx (hP.mono le_add_self)) g hg]
      exact Dw_add hw' (hPl.ck hO hcov) (hPr.ck hO hcov) g hg
    have b1 := ih (Dx x a) Φ hw' hPl (by
      intro w₁ w₂ h₁ h₂ hl
      have := hM (w₁ ++ [x]) w₂ (List.Sublist.append h₁ (List.Sublist.refl _))
        (h₂.trans (List.sublist_append_left _ _)) (by simp; omega)
      rwa [Dw_append] at this)
    have b2 := ih a (Dx x Φ) hw' hPr (by
      intro w₁ w₂ h₁ h₂ hl
      have := hM w₁ (w₂ ++ [x]) (h₁.trans (List.sublist_append_left _ _))
        (List.Sublist.append h₂ (List.Sublist.refl _)) (by simp; omega)
      rwa [Dw_append] at this)
    rw [e1]
    calc ‖Dw w (ap (Dx x a) Φ) g + Dw w (ap a (Dx x Φ)) g‖
        ≤ 2 ^ w.length * M + 2 ^ w.length * M := (norm_add_le _ _).trans (add_le_add b1 b2)
      _ = 2 ^ (w ++ [x]).length * M := by simp [pow_succ]; ring

def wL (u : List (Mat k r)) : List (Bool × Mat k r) := u.map (Prod.mk true)

def wR (v : List (Mat k r)) : List (Bool × Mat k r) := v.map (Prod.mk false)

lemma Dw_wR (v : List (Mat k r)) (f : Mat k r → E) : Dw (wR v) f = Rw v f := by
  induction v with
  | nil => rfl
  | cons X v ih =>
    show Dx (false, X) (Dw (wR v) f) = RdV X (Rw v f)
    rw [ih]
    rfl

lemma Dw_wL (u : List (Mat k r)) (f : Mat k r → E) : Dw (wL u) f = u.foldr LdV f := by
  induction u with
  | nil => rfl
  | cons X u ih =>
    show Dx (true, X) (Dw (wL u) f) = LdV X (u.foldr LdV f)
    rw [ih]
    rfl

lemma dLR_eq (u v : List (Mat k r)) (f : Mat k r → E) : dLR u v f = Dw (wL u ++ wR v) f := by
  show u.foldr LdV (Rw v f) = _
  rw [Dw_append, Dw_wR, Dw_wL]

lemma sub_LR {u v : List (Mat k r)} {w : List (Bool × Mat k r)} (h : w.Sublist (wL u ++ wR v)) :
    ∃ u₁ v₁, u₁.Sublist u ∧ v₁.Sublist v ∧ w = wL u₁ ++ wR v₁ := by
  obtain ⟨r₁, r₂, rfl, h₁, h₂⟩ := List.sublist_append_iff.mp h
  obtain ⟨u₁, hu₁, rfl⟩ := List.sublist_map_iff.mp h₁
  obtain ⟨v₁, hv₁, rfl⟩ := List.sublist_map_iff.mp h₂
  exact ⟨u₁, v₁, hu₁, hv₁, rfl⟩

lemma lie_LR {u v : List (Mat k r)} (hu : ∀ X ∈ u, inLie k r X) (hv : ∀ X ∈ v, inLie k r X) :
    ∀ x ∈ wL u ++ wR v, inLie k r x.2 := by
  intro x hx
  simp only [wL, wR, List.mem_append, List.mem_map] at hx
  rcases hx with ⟨X, hX, rfl⟩ | ⟨X, hX, rfl⟩
  · exact hu X hX
  · exact hv X hX

def nz (X : Mat k r) : ℝ := max 1 ‖X‖

def nrm (X : Mat k r) : Mat k r := (((nz X)⁻¹ : ℝ) : ℂ) • X

lemma nz_pos (X : Mat k r) : 0 < nz X := lt_of_lt_of_le one_pos (le_max_left _ _)

lemma nrm_unit {X : Mat k r} (hX : inLie k r X) : unitLie k r (nrm X) := by
  unfold unitLie
  refine ⟨lie_rsmul hX _, fun i j => ?_⟩
  have hp := nz_pos X
  have h1 : ‖X i j‖ ≤ ‖X‖ := Matrix.norm_entry_le_entrywise_sup_norm X
  have h2 : ‖X‖ ≤ nz X := le_max_right _ _
  have h3 : ‖(((nz X)⁻¹ : ℝ) : ℂ)‖ = (nz X)⁻¹ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hp)]
  calc ‖nrm X i j‖ = ‖(((nz X)⁻¹ : ℝ) : ℂ)‖ * ‖X i j‖ := by
        simp only [nrm, Matrix.smul_apply]; exact norm_smul _ _
    _ ≤ (nz X)⁻¹ * nz X := by rw [h3]; gcongr; linarith
    _ = 1 := inv_mul_cancel₀ hp.ne'

lemma nrm_back (X : Mat k r) : ((nz X : ℝ) : ℂ) • nrm X = X := by
  unfold nrm
  rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ (nz_pos X).ne', Complex.ofReal_one, one_smul]

lemma Dx_scale (s : ℝ) (b : Bool) (X : Mat k r) (f : Mat k r → E) :
    Dx (b, (s : ℂ) • X) f = fun g => (s : ℂ) • Dx (b, X) f g := by
  funext g
  rcases b with _ | _
  · show deriv (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • (s : ℂ) • X))) 0 =
      (s : ℂ) • deriv (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) 0
    have h := deriv_comp_mul_left s (fun u : ℝ => f (g * NormedSpace.exp ((u : ℂ) • X))) 0
    simp only [mul_zero] at h
    rw [← Complex.coe_smul] at h
    rw [← h]
    congr 1
    funext t
    simp only [smul_smul, Complex.ofReal_mul, mul_comm (t : ℂ)]
  · show deriv (fun t : ℝ => f (NormedSpace.exp (-((t : ℂ) • (s : ℂ) • X)) * g)) 0 =
      (s : ℂ) • deriv (fun t : ℝ => f (NormedSpace.exp (-((t : ℂ) • X)) * g)) 0
    have h := deriv_comp_mul_left s (fun u : ℝ => f (NormedSpace.exp (-((u : ℂ) • X)) * g)) 0
    simp only [mul_zero] at h
    rw [← Complex.coe_smul] at h
    rw [← h]
    congr 1
    funext t
    simp only [smul_smul, Complex.ofReal_mul, mul_comm (t : ℂ)]

lemma Rw_scale (v : List (Mat k r)) (f : Mat k r → E) :
    Rw v f = fun g => (((v.map nz).prod : ℝ) : ℂ) • Rw (v.map nrm) f g := by
  induction v with
  | nil => funext g; simp [Rw]
  | cons X v ih =>
    funext g
    have h1 : RdV X (Rw v f) = Dx (false, ((nz X : ℝ) : ℂ) • nrm X) (Rw v f) := by
      rw [nrm_back]; rfl
    show RdV X (Rw v f) g = _
    rw [h1, Dx_scale, ih, Dx_smul]
    show ((nz X : ℝ) : ℂ) • ((((v.map nz).prod : ℝ) : ℂ) • Dx (false, nrm X) (Rw (v.map nrm) f) g) = _
    rw [smul_smul, ← Complex.ofReal_mul]
    simp only [List.map_cons, List.prod_cons]
    rfl

end Formalism.FourierDecayAlt.P.BetaSesquilinearity

namespace Formalism.FourierDecayAlt.P.BetaSesquilinearity

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
open scoped ContDiff

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E']

lemma gN_pos {g : Mat k r} (hg : g ∈ GV k r) : 0 < gN g := lt_of_lt_of_le one_pos (gN_ge_one hg)

lemma len_LR (u v : List (Mat k r)) : (wL u ++ wR v).length = u.length + v.length := by
  simp [wL, wR]

lemma unit_lie {u : List (Mat k r)} (hu : ∀ X ∈ u, unitLie k r X) : ∀ X ∈ u, inLie k r X := fun X hX => (hu X hX).1

lemma CCle_mono_m {A : ℝ} {m m' : ℕ} (h : m ≤ m') {F : Mat k r → E} {c : ℝ} (hF : CCle A m' F c) :
    CCle A m F c := by
  obtain ⟨hc, hb⟩ := hF
  exact ⟨sCkOn_mono (by exact_mod_cast h) hc, fun u v hu hv hl g hg => hb u v hu hv (hl.trans h) g hg⟩

lemma CCle_mono_A {A A' : ℝ} (h : A ≤ A') {m : ℕ} {F : Mat k r → E} {c : ℝ} (hF : CCle A' m F c) :
    CCle A m F c := by
  obtain ⟨hc, hb⟩ := hF
  refine ⟨hc, fun u v hu hv hl g hg => le_trans ?_ (hb u v hu hv hl g hg)⟩
  exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le (gN_ge_one hg) h) (norm_nonneg _)

lemma CCle_zero {A : ℝ} {m : ℕ} : CCle A m (fun _ : Mat k r => (0 : E)) 0 := ⟨CkOn_zero, fun u v _ _ _ g _ => by rw [dLR_eq, Dw_zero]; simp⟩

lemma CCle_add {A : ℝ} {m : ℕ} {F F' : Mat k r → E} {c c' : ℝ} (hF : CCle A m F c) (hF' : CCle A m F' c') :
    CCle A m (fun g => F g + F' g) (c + c') := by
  obtain ⟨hc, hb⟩ := hF
  obtain ⟨hc', hb'⟩ := hF'
  refine ⟨CkOn_add hc hc', fun u v hu hv hl g hg => ?_⟩
  have hl' : (((wL u ++ wR v).length : ℕ) : ℕ∞) ≤ (m : ℕ∞) := by
    rw [len_LR]; exact_mod_cast hl
  have hw : ∀ x ∈ wL u ++ wR v, inLie k r x.2 := lie_LR (unit_lie hu) (unit_lie hv)
  have e : dLR u v (fun g => F g + F' g) g = dLR u v F g + dLR u v F' g := by
    rw [dLR_eq, dLR_eq, dLR_eq]
    exact Dw_add hw (sCkOn_mono hl' hc) (sCkOn_mono hl' hc') g hg
  rw [e]
  have h1 := hb u v hu hv hl g hg
  have h2 := hb' u v hu hv hl g hg
  have h3 := norm_add_le (dLR u v F g) (dLR u v F' g)
  have h4 : 0 ≤ gN g ^ A := Real.rpow_nonneg (le_trans zero_le_one (gN_ge_one hg)) _
  calc gN g ^ A * ‖dLR u v F g + dLR u v F' g‖ ≤ gN g ^ A * (‖dLR u v F g‖ + ‖dLR u v F' g‖) :=
        mul_le_mul_of_nonneg_left h3 h4
    _ ≤ c + c' := by rw [mul_add]; exact add_le_add h1 h2

lemma CCle_smul {A : ℝ} {m : ℕ} {F : Mat k r → E} {c : ℝ} (a : ℂ) (hF : CCle A m F c) :
    CCle A m (fun g => a • F g) (‖a‖ * c) := by
  obtain ⟨hc, hb⟩ := hF
  refine ⟨CkOn_smul a hc, fun u v hu hv hl g hg => ?_⟩
  have e : dLR u v (fun g => a • F g) g = a • dLR u v F g := by
    rw [dLR_eq, dLR_eq, Dw_smul]
  rw [e, norm_smul]
  calc gN g ^ A * (‖a‖ * ‖dLR u v F g‖) = ‖a‖ * (gN g ^ A * ‖dLR u v F g‖) := by ring
    _ ≤ ‖a‖ * c := mul_le_mul_of_nonneg_left (hb u v hu hv hl g hg) (norm_nonneg _)

lemma CCle_Rw {A : ℝ} {m : ℕ} {v' : List (Mat k r)} (hv' : ∀ X ∈ v', unitLie k r X) {F : Mat k r → E}
    {c : ℝ} (hF : CCle A (m + v'.length) F c) : CCle A m (Rw v' F) c := by
  obtain ⟨hc, hb⟩ := hF
  refine ⟨?_, fun u v hu hv hl g hg => ?_⟩
  · have hw : ∀ x ∈ wR v', inLie k r x.2 := by
      intro x hx
      simp only [wR, List.mem_map] at hx
      obtain ⟨X, hX, rfl⟩ := hx
      exact (hv' X hX).1
    have hc' : CkOn ((m : ℕ∞) + ((wR v').length : ℕ∞)) (GV k r) F := by
      have e : (((m + v'.length : ℕ)) : ℕ∞) = (m : ℕ∞) + ((wR v').length : ℕ∞) := by simp [wR]
      rw [← e]; exact hc
    rw [← Dw_wR]
    exact CkOn_Dw hw hc'
  · have e : dLR u v (Rw v' F) = dLR u (v ++ v') F := by
      show u.foldr LdV (v.foldr RdV (v'.foldr RdV F)) = u.foldr LdV ((v ++ v').foldr RdV F)
      rw [List.foldr_append]
    rw [e]
    refine hb u (v ++ v') hu (fun X hX => ?_) (by simp only [List.length_append]; omega) g hg
    rcases List.mem_append.mp hX with h | h
    · exact hv X h
    · exact hv' X h

lemma InCC_Rw {A : ℝ} {m : ℕ} {v : List (Mat k r)} (hv : ∀ X ∈ v, inLie k r X) {F : Mat k r → E}
    (hF : InCC A (m + v.length) F) : InCC A m (Rw v F) := by
  obtain ⟨c, hc⟩ := hF
  have hv' : ∀ X ∈ v.map nrm, unitLie k r X := by
    intro X hX
    obtain ⟨Y, hY, rfl⟩ := List.mem_map.mp hX
    exact nrm_unit (hv Y hY)
  have h1 : CCle A (m + (v.map nrm).length) F c := by rw [List.length_map]; exact hc
  rw [Rw_scale]
  exact ⟨_, CCle_smul _ (CCle_Rw hv' h1)⟩

lemma sInCC_mono {A A' : ℝ} (h : A ≤ A') {m m' : ℕ} (hm : m ≤ m') {F : Mat k r → E} (hF : InCC A' m' F) :
    InCC A m F := by
  obtain ⟨c, hc⟩ := hF
  exact ⟨c, CCle_mono_A h (CCle_mono_m hm hc)⟩

lemma Rw_vanish {O : Set (Mat k r)} (hO : IsOpen O) {v : List (Mat k r)} (hv : ∀ X ∈ v, inLie k r X)
    {f : Mat k r → E} (hz : ∀ g ∈ GV k r, g ∈ O → f g = 0) : ∀ g ∈ GV k r, g ∈ O → Rw v f g = 0 := by
  rw [← Dw_wR]
  refine Dw_vanish hO (fun x hx => ?_) hz
  simp only [wR, List.mem_map] at hx
  obtain ⟨X, hX, rfl⟩ := hx
  exact hv X hX

lemma prodBound {O UU : Set (Mat k r)} (hO : IsOpen O) (hcov : ∀ g ∈ GV k r, g ∈ O ∨ g ∈ UU)
    {A d : ℝ} {m : ℕ} {a : Mat k r → (E →L[ℂ] E')} {Φ : Mat k r → E} {C c : ℝ}
    (ha : CkOn m UU a)
    (hab : ∀ u v : List (Mat k r), (∀ X ∈ u, unitLie k r X) → (∀ X ∈ v, unitLie k r X) →
      u.length + v.length ≤ m → ∀ g ∈ GV k r, g ∉ O → ‖dLR u v a g‖ ≤ C * gN g ^ d)
    (hΦ : CCle (A + d) m Φ c) (hz : ∀ g ∈ GV k r, g ∈ O → Φ g = 0) :
    CCle A m (ap a Φ) (2 ^ m * (|C| * |c|)) := by
  have hP : Pr O UU m a Φ := ⟨ha, hΦ.1, hz⟩
  have hK : 0 ≤ |C| * |c| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
  refine ⟨hP.ck hO hcov, fun u v hu hv hl g hg => ?_⟩
  have hlie := lie_LR (unit_lie hu) (unit_lie hv)
  have hle : (((wL u ++ wR v).length : ℕ) : ℕ∞) ≤ (m : ℕ∞) := by rw [len_LR]; exact_mod_cast hl
  rw [dLR_eq]
  by_cases hgO : g ∈ O
  · rw [Dw_vanish hO hlie (hP.mono zero_le).apz g hg hgO]
    simp only [norm_zero, mul_zero]
    positivity
  · have hp := gN_pos hg
    have hpA : 0 < gN g ^ A := Real.rpow_pos_of_pos hp _
    have hpd : 0 < gN g ^ d := Real.rpow_pos_of_pos hp _
    have hpAd : gN g ^ (A + d) = gN g ^ A * gN g ^ d := Real.rpow_add hp _ _
    have hb := leib_bound hO hcov g hg (|C| * gN g ^ d * (|c| / gN g ^ (A + d))) (wL u ++ wR v) a Φ hlie
      (hP.mono hle) (by
        intro w₁ w₂ h₁ h₂ hlen
        obtain ⟨u₁, v₁, hu₁, hv₁, rfl⟩ := sub_LR h₁
        obtain ⟨u₂, v₂, hu₂, hv₂, rfl⟩ := sub_LR h₂
        rw [len_LR, len_LR, len_LR] at hlen
        rw [← dLR_eq, ← dLR_eq]
        have b1 : ‖dLR u₁ v₁ a g‖ ≤ |C| * gN g ^ d :=
          (hab u₁ v₁ (fun X hX => hu X (hu₁.subset hX)) (fun X hX => hv X (hv₁.subset hX)) (by omega) g hg
            hgO).trans (mul_le_mul_of_nonneg_right (le_abs_self _) hpd.le)
        have b2 : ‖dLR u₂ v₂ Φ g‖ ≤ |c| / gN g ^ (A + d) := by
          rw [le_div_iff₀' (by rw [hpAd]; positivity)]
          exact (hΦ.2 u₂ v₂ (fun X hX => hu X (hu₂.subset hX)) (fun X hX => hv X (hv₂.subset hX)) (by omega)
            g hg).trans (le_abs_self _)
        exact mul_le_mul b1 b2 (norm_nonneg _) (by positivity))
    have hpow : (2 : ℝ) ^ (wL u ++ wR v).length ≤ 2 ^ m := by
      rw [len_LR]; exact pow_le_pow_right₀ (by norm_num) hl
    calc gN g ^ A * ‖Dw (wL u ++ wR v) (ap a Φ) g‖
        ≤ gN g ^ A * (2 ^ (wL u ++ wR v).length * (|C| * gN g ^ d * (|c| / gN g ^ (A + d)))) :=
          mul_le_mul_of_nonneg_left hb hpA.le
      _ = 2 ^ (wL u ++ wR v).length * (|C| * |c|) := by
          rw [hpAd]; field_simp
      _ ≤ 2 ^ m * (|C| * |c|) := mul_le_mul_of_nonneg_right hpow hK

def trn (L : E →L[ℂ] E') (a b : Mat k r) (f : Mat k r → E) : Mat k r → E' := fun g => L (f (a * g * b))

def abL (a b : Mat k r) : Mat k r →L[ℝ] Mat k r :=
  (mulRightRealCLM b).comp (LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ a))

lemma abL_apply (a b g : Mat k r) : abL a b g = a * g * b := by
  rfl

lemma CkOn_trn {m : ℕ∞} (L : E →L[ℂ] E') {a b : Mat k r} (ha : a ∈ GV k r) (hb : b ∈ GV k r)
    {f : Mat k r → E} (hf : CkOn m (GV k r) f) : CkOn m (GV k r) (trn L a b f) := by
  intro g₀ hg₀
  obtain ⟨U, f', hU, hgU, hc, he⟩ := hf (a * g₀ * b) (gv_mul (gv_mul ha hg₀) hb)
  refine ⟨(abL a b) ⁻¹' U, fun g => L (f' (a * g * b)), hU.preimage (abL a b).continuous, ?_, ?_, ?_⟩
  · show abL a b g₀ ∈ U
    rw [abL_apply]; exact hgU
  · have h1 : ContDiffOn ℝ (m : WithTop ℕ∞) (fun g => f' (abL a b g)) ((abL a b) ⁻¹' U) :=
      hc.comp (abL a b).contDiff.contDiffOn (fun g hg => hg)
    have h2 := (L.restrictScalars ℝ).contDiff.comp_contDiffOn h1
    refine h2.congr (fun g _ => ?_)
    simp [abL_apply]
  · intro g hg hgG
    show L (f (a * g * b)) = L (f' (a * g * b))
    have hg' : a * g * b ∈ U := by rw [← abL_apply]; exact hg
    rw [he _ hg' (gv_mul (gv_mul ha hgG) hb)]

lemma lie_conj {X b : Mat k r} (hX : inLie k r X) (hb : b ∈ GV k r) : inLie k r (b⁻¹ * X * b) := by
  have hX' : Xᴴ * Hpk k r + Hpk k r * X = 0 := hX
  have hb' : bᴴ * Hpk k r * b = Hpk k r := hb
  have hu := gv_unit hb
  have h1 : b * b⁻¹ = 1 := Matrix.mul_nonsing_inv b hu
  have h2 : (b⁻¹)ᴴ * bᴴ = 1 := by rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
  have e1 : Hpk k r * b⁻¹ = bᴴ * Hpk k r := by
    calc Hpk k r * b⁻¹ = bᴴ * Hpk k r * b * b⁻¹ := by rw [hb']
      _ = bᴴ * Hpk k r := by rw [Matrix.mul_assoc, h1, Matrix.mul_one]
  have e2 : (b⁻¹)ᴴ * Hpk k r = Hpk k r * b := by
    calc (b⁻¹)ᴴ * Hpk k r = (b⁻¹)ᴴ * (bᴴ * Hpk k r * b) := by rw [hb']
      _ = ((b⁻¹)ᴴ * bᴴ) * Hpk k r * b := by simp only [Matrix.mul_assoc]
      _ = Hpk k r * b := by rw [h2, Matrix.one_mul]
  show (b⁻¹ * X * b)ᴴ * Hpk k r + Hpk k r * (b⁻¹ * X * b) = 0
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
  calc bᴴ * (Xᴴ * (b⁻¹)ᴴ) * Hpk k r + Hpk k r * (b⁻¹ * X * b)
      = bᴴ * Xᴴ * ((b⁻¹)ᴴ * Hpk k r) + (Hpk k r * b⁻¹) * X * b := by simp only [Matrix.mul_assoc]
    _ = bᴴ * (Xᴴ * Hpk k r + Hpk k r * X) * b := by
        rw [e1, e2]; simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    _ = 0 := by rw [hX', Matrix.mul_zero, Matrix.zero_mul]

lemma Dx_trn (L : E →L[ℂ] E') {a b : Mat k r} (ha : a ∈ GV k r) (hb : b ∈ GV k r) {X : Mat k r}
    (hX : inLie k r X) {f : Mat k r → E} (hf : CkOn 1 (GV k r) f) :
    ∀ g ∈ GV k r, Dx (false, X) (trn L a b f) g = trn L a b (Dx (false, b⁻¹ * X * b) f) g := by
  intro g hg
  have hb' := gv_unit hb
  have hagb : a * g * b ∈ GV k r := gv_mul (gv_mul ha hg) hb
  have hY : inLie k r (b⁻¹ * X * b) := lie_conj hX hb
  have hφ := CkOn_diff (x := (false, b⁻¹ * X * b)) hY hf hagb hagb
  have hc : ∀ t : ℝ, crv (false, b⁻¹ * X * b) (a * g * b) t =
      a * g * b * NormedSpace.exp ((t : ℂ) • (b⁻¹ * X * b)) := fun t => rfl
  simp only [hc] at hφ
  have hL := (L.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hφ
  simp only [Function.comp_def, ContinuousLinearMap.coe_restrictScalars'] at hL
  have e : ∀ t : ℝ, a * (g * NormedSpace.exp ((t : ℂ) • X)) * b =
      a * g * b * NormedSpace.exp ((t : ℂ) • (b⁻¹ * X * b)) := by
    intro t
    have h1 : (t : ℂ) • (b⁻¹ * X * b) = b⁻¹ * ((t : ℂ) • X) * b := by
      rw [Matrix.mul_smul, Matrix.smul_mul]
    rw [h1, Matrix.exp_conj' _ _ ((Matrix.isUnit_iff_isUnit_det _).mpr hb')]
    have h2 : b * b⁻¹ = 1 := Matrix.mul_nonsing_inv b hb'
    calc a * (g * NormedSpace.exp ((t : ℂ) • X)) * b
        = a * g * (b * b⁻¹) * NormedSpace.exp ((t : ℂ) • X) * b := by
          rw [h2, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = a * g * b * (b⁻¹ * NormedSpace.exp ((t : ℂ) • X) * b) := by simp only [Matrix.mul_assoc]
  show deriv (fun t : ℝ => L (f (a * (g * NormedSpace.exp ((t : ℂ) • X)) * b))) 0 =
    L (Dx (false, b⁻¹ * X * b) f (a * g * b))
  simp only [e]
  exact hL.deriv

lemma Rw_trn (L : E →L[ℂ] E') {a b : Mat k r} (ha : a ∈ GV k r) (hb : b ∈ GV k r) (v : List (Mat k r))
    (hv : ∀ X ∈ v, inLie k r X) {f : Mat k r → E} (hf : CkOn v.length (GV k r) f) :
    ∀ g ∈ GV k r, Rw v (trn L a b f) g = trn L a b (Rw (v.map fun X => b⁻¹ * X * b) f) g := by
  induction v with
  | nil => intro g _; rfl
  | cons X v ih =>
    intro g hg
    have hX : inLie k r X := hv X (by simp)
    have hv' : ∀ Y ∈ v, inLie k r Y := fun Y hY => hv Y (by simp [hY])
    have hle : ((v.length : ℕ) : ℕ∞) ≤ (((X :: v).length : ℕ) : ℕ∞) := by
      exact_mod_cast Nat.le_succ v.length
    have hfv : CkOn v.length (GV k r) f := sCkOn_mono hle hf
    have hw : ∀ x ∈ wR (v.map fun Z => b⁻¹ * Z * b), inLie k r x.2 := by
      intro x hx
      simp only [wR, List.mem_map] at hx
      obtain ⟨Y, ⟨Z, hZ, rfl⟩, rfl⟩ := hx
      exact lie_conj (hv' Z hZ) hb
    have e1 : (((X :: v).length : ℕ) : ℕ∞) =
        1 + ((wR (v.map fun Z => b⁻¹ * Z * b)).length : ℕ∞) := by
      simp only [wR, List.length_map, List.length_cons, Nat.cast_add, Nat.cast_one]; ring
    have hc1 : CkOn 1 (GV k r) (Rw (v.map fun Z => b⁻¹ * Z * b) f) := by
      rw [← Dw_wR]; exact CkOn_Dw hw (by rw [← e1]; exact hf)
    show Dx (false, X) (Rw v (trn L a b f)) g =
      trn L a b (Dx (false, b⁻¹ * X * b) (Rw (v.map fun Z => b⁻¹ * Z * b) f)) g
    rw [Dx_congr (x := (false, X)) hX (f := Rw v (trn L a b f)) (f₂ := trn L a b (Rw (v.map fun Z => b⁻¹ * Z * b) f))
      (ih hv' hfv) g hg]
    exact Dx_trn L ha hb hX hc1 g hg

end Formalism.FourierDecayAlt.P.BetaSesquilinearity

namespace Formalism.FourierDecayAlt.P.BetaSesquilinearity

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

lemma Sset_sub {z : Fin (2 * r + k + 1) → ℂ} {s : Mat k r} (hs : s ∈ Sset k r z) : s ∈ GV k r := by
  obtain ⟨h, hh, m, hm, rfl⟩ := hs
  exact gv_mul hh.1 hm.1

lemma Dmin_cont (z z' : Fin (2 * r + k + 1) → ℂ) (l : Fin (r + 2)) : Continuous fun g : Mat k r => Dmin k r z z' g l := by
  unfold Dmin
  refine Continuous.matrix_det (Continuous.matrix_submatrix ?_ _ _)
  refine continuous_matrix fun a b => ?_
  unfold Zhat herm
  simp only [dotProduct, Matrix.mulVec]
  fun_prop

lemma Gf_cont (z z' : Fin (2 * r + k + 1) → ℂ) : Continuous (Gf k r z z') := by
  unfold Gf
  exact (Complex.continuous_normSq.comp (Dmin_cont z z' _)).sub
    (continuous_const.mul (Complex.continuous_normSq.comp (Dmin_cont z z' _)))

lemma gPos_stable (D : RealPlaceData k r Wp Wq) : IsStableOpen D (GPos D) := by
  refine ⟨⟨{g | 0 < Gf k r D.z D.z' g}, isOpen_lt continuous_const (Gf_cont _ _), ?_⟩, ?_⟩
  · ext g; simp only [GPos, Set.mem_ofPred_eq, Set.mem_inter_iff]; tauto
  · intro s hs s' hs' g hg
    refine ⟨gv_mul (gv_mul (Sset_sub hs) hg.1) (Sset_sub hs'), ?_⟩
    rw [gInv k r D.z D.z' D.z_mem D.z'_mem s hs s' hs' g]
    exact hg.2

lemma suppIn_of (D : RealPlaceData k r Wp Wq) {ε : ℝ} (hε : 0 < ε) {F : Mat k r → (Wq →L[ℂ] Wp)}
    (h : ∀ g ∈ GV k r, F g ≠ 0 → ε ≤ Gf k r D.z D.z' g) : SuppIn (GPos D) F := by
  intro g hg
  have hcl : IsClosed {g : Mat k r | g ∈ GV k r ∧ ε ≤ Gf k r D.z D.z' g} :=
    gv_closed.inter (isClosed_le continuous_const (Gf_cont D.z D.z'))
  have hsub : {g | g ∈ GV k r ∧ F g ≠ 0} ⊆ {g : Mat k r | g ∈ GV k r ∧ ε ≤ Gf k r D.z D.z' g} :=
    fun g hg => ⟨hg.1, h g hg.1 hg.2⟩
  have h2 := closure_minimal hsub hcl hg
  exact ⟨h2.1, lt_of_lt_of_le hε h2.2⟩

section weaken

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

lemma aesm_of_continuousOn (D : RealPlaceData k r Wp Wq) {f : Mat k r → E} (hf : ContinuousOn f (GV k r)) :
    AEStronglyMeasurable (fun g : Mt k r => f (Matrix.of g)) D.μG := by
  have hcl : IsClosed (GV k r : Set (Mt k r)) := gv_closed
  have h1 : AEStronglyMeasurable (fun g : Mt k r => f (Matrix.of g)) (D.μG.restrict (GV k r : Set (Mt k r))) :=
    ContinuousOn.aestronglyMeasurable (α := Mt k r) (f := fun g : Mt k r => f (Matrix.of g))
      (s := (GV k r : Set (Mt k r))) hf (IsClosed.measurableSet (α := Mt k r) hcl)
  have h2 : D.μG.restrict (GV k r : Set (Mt k r)) = D.μG :=
    Measure.restrict_eq_self_of_ae_mem (by
      have := D.haarG.conc
      rw [ae_iff]
      exact this)
  rwa [h2] at h1

end weaken

end Formalism.FourierDecayAlt.P.BetaSesquilinearity

namespace Formalism.FourierDecayAlt.P.BetaSesquilinearity

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
open scoped ContDiff

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section gen

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

lemma InCC_opsum {ι : Type*} {A : ℝ} {m : ℕ} (Θ : List ι) (φ : ι → Mat k r → E)
    (h : ∀ T ∈ Θ, InCC A m (φ T)) : InCC A m (fun g => (Θ.map fun T => φ T g).sum) := by
  induction Θ with
  | nil => exact ⟨0, by simpa using (CCle_zero : CCle A m (fun _ : Mat k r => (0 : E)) 0)⟩
  | cons T Θ ih =>
    obtain ⟨c, hc⟩ := h T (by simp)
    obtain ⟨c', hc'⟩ := ih (fun T' hT' => h T' (by simp [hT']))
    exact ⟨c + c', by simpa using CCle_add hc hc'⟩

lemma CC_bdd {A : ℝ} (hA : 0 ≤ A) {f : Mat k r → E} {c : ℝ} (hf : CCle A 0 f c) :
    ∀ g ∈ GV k r, ‖f g‖ ≤ c := by
  intro g hg
  have h1 := hf.2 [] [] (by simp) (by simp) (by simp) g hg
  have h2 : 1 ≤ gN g ^ A := Real.one_le_rpow (gN_ge_one hg) hA
  have h3 : dLR [] [] f g = f g := rfl
  rw [h3] at h1
  nlinarith [mul_nonneg (sub_nonneg.mpr h2) (norm_nonneg (f g))]

end gen

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

lemma word_le_order (Θ : DiffOp k r Wp Wq) {T : DTerm k r Wp Wq} (hT : T ∈ Θ) :
    T.word.length ≤ opOrder Θ := by
  induction Θ with
  | nil => simp at hT
  | cons T' Θ ih =>
    show T.word.length ≤ max T'.word.length ((Θ.map fun T => T.word.length).foldr max 0)
    rcases List.mem_cons.mp hT with rfl | h
    · exact le_max_left _ _
    · exact le_trans (ih h) (le_max_right _ _)

def Lp (D : RealPlaceData k r Wp Wq) (p : SS k r) : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp) :=
  (ContinuousLinearMap.compL ℂ Wq Wp Wp (D.π (Matrix.of p.1.1))).comp
    ((ContinuousLinearMap.compL ℂ Wq Wq Wp).flip (D.π' (Matrix.of p.2.1)⁻¹))

lemma rho_eq_trn (D : RealPlaceData k r Wp Wq) (p : SS k r) (F : Mat k r → (Wq →L[ℂ] Wp)) :
    rho D p F = trn (Lp D p) ((Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹) (Matrix.of p.2.2 * Matrix.of p.2.1) F := by
  funext g
  have e : sgs p g = (Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * g * (Matrix.of p.2.2 * Matrix.of p.2.1) := by
    simp only [sgs, Matrix.mul_assoc]
  ext v
  simp [rho, trn, Lp, e]

end Formalism.FourierDecayAlt.P.BetaSesquilinearity

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
open scoped ContDiff

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem clause_of_regularized_limit : Formalism.FourierDecayAlt.B.StepClause := by
  intro k r Wp Wq _ _ _ _ _ _ D A hA hCC
  refine ⟨gPos_stable D, ?_⟩
  intro Θ ε d hε hd hS hP F F' hF hF' hsF hsF'
  set O : Set (Mat k r) := {g | Gf k r D.z D.z' g < ε} with hOdef
  have hO : IsOpen O := isOpen_lt (Gf_cont _ _) continuous_const
  have hcov : ∀ g ∈ GV k r, g ∈ O ∨ g ∈ GPos D := by
    intro g hg
    rcases lt_or_ge (Gf k r D.z D.z' g) ε with h | h
    · exact Or.inl h
    · exact Or.inr ⟨hg, lt_of_lt_of_le hε h⟩
  have hz : ∀ g ∈ GV k r, g ∈ O → F g = 0 := by
    intro g hg hgO
    by_contra hne
    exact absurd (hsF g hg hne) (not_le.mpr hgO)
  have hz' : ∀ g ∈ GV k r, g ∈ O → F' g = 0 := by
    intro g hg hgO
    by_contra hne
    exact absurd (hsF' g hg hne) (not_le.mpr hgO)
  have hAd : A ≤ A + d := by linarith
  have hAd0 : 0 ≤ A + d := by linarith

  have hadj : ∀ T ∈ Θ, InCC A (opOrder Θ + 5) (ap T.coefAdj F') := by
    intro T hT
    obtain ⟨C, hC⟩ := hP T hT
    obtain ⟨c', hc'⟩ := hF'
    exact ⟨_, prodBound hO hcov (sCkOn_mono le_top (hS T hT).2)
      (fun u v hu hv hl g hg hgO => (hC u v hu hv hl g hg (not_lt.mp hgO)).2) hc' hz'⟩
  refine ⟨suppIn_of D hε hsF, suppIn_of D hε hsF', sInCC_mono hAd (by omega) hF, sInCC_mono hAd (by omega) hF',
    ?_, ?_, ?_⟩
  ·
    refine InCC_opsum Θ (fun T => ap T.coef (Rw T.word F)) ?_
    intro T hT
    have hlen := word_le_order Θ hT
    obtain ⟨C, hC⟩ := hP T hT
    obtain ⟨c, hc⟩ : InCC (A + d) 5 (Rw T.word F) :=
      InCC_Rw T.word_lie (sInCC_mono le_rfl (by omega) hF)
    exact ⟨_, prodBound hO hcov (sCkOn_mono le_top (hS T hT).1)
      (fun u v hu hv hl g hg hgO => (hC u v hu hv (by omega) g hg (not_lt.mp hgO)).1) hc
      (Rw_vanish hO T.word_lie hz)⟩
  ·
    refine InCC_opsum Θ
      (fun T => fun g => ((-1 : ℂ) ^ T.word.length) • Rw T.word.reverse (ap T.coefAdj F') g) ?_
    intro T hT
    have hlen := word_le_order Θ hT
    obtain ⟨c, hc⟩ : InCC A 5 (Rw T.word.reverse (ap T.coefAdj F')) :=
      InCC_Rw (fun X hX => T.word_lie X (List.mem_reverse.mp hX))
        (sInCC_mono le_rfl (by simp; omega) (hadj T hT))
    exact ⟨_, CCle_smul _ hc⟩
  ·
    intro p hp T hT i j hij hj
    have hlen := word_le_order Θ hT
    set a : Mat k r := (Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ with hadef
    set b : Mat k r := Matrix.of p.2.2 * Matrix.of p.2.1 with hbdef
    have ha : a ∈ GV k r := gv_mul (gv_inv hp.1.1) (gv_inv hp.2.1.1)
    have hb : b ∈ GV k r := gv_mul hp.2.2.2.1 hp.2.2.1.1
    have hlie1 : ∀ X ∈ (T.word.take i).reverse, inLie k r X := fun X hX =>
      T.word_lie X (List.mem_of_mem_take (List.mem_reverse.mp hX))
    have hlie2 : ∀ X ∈ T.word.drop j, inLie k r X := fun X hX => T.word_lie X (List.mem_of_mem_drop hX)
    have hl1 : (T.word.take i).reverse.length ≤ opOrder Θ := by
      simp only [List.length_reverse, List.length_take]; omega
    have hl2 : (T.word.drop j).length ≤ opOrder Θ := by
      simp only [List.length_drop]; omega
    obtain ⟨K₁, hK₁⟩ : InCC A 0 (Rw (T.word.take i).reverse (ap T.coefAdj F')) :=
      InCC_Rw hlie1 (sInCC_mono le_rfl (by omega) (hadj T hT))
    obtain ⟨K₂, hK₂⟩ : InCC (A + d) 0 (Rw ((T.word.drop j).map fun X => b⁻¹ * X * b) F) :=
      InCC_Rw (fun X hX => by
        obtain ⟨Y, hY, rfl⟩ := List.mem_map.mp hX
        exact lie_conj (hlie2 Y hY) hb) (sInCC_mono le_rfl (by simp only [List.length_map]; omega) hF)
    obtain ⟨cF, hcF⟩ := hF
    have hFk : CkOn ((opOrder Θ + 5 : ℕ) : ℕ∞) (GV k r) F := hcF.1
    set f₁ : Mat k r → (Wq →L[ℂ] Wp) := Rw (T.word.take i).reverse (ap T.coefAdj F') with hf₁
    set f₂ : Mat k r → (Wq →L[ℂ] Wp) := Rw (T.word.drop j) (rho D p F) with hf₂
    have hc₁ : ContinuousOn f₁ (GV k r) := CkOn_cont subset_rfl hK₁.1
    have hc₂ : ContinuousOn f₂ (GV k r) := by
      apply CkOn_cont subset_rfl
      rw [hf₂, ← Dw_wR, rho_eq_trn]
      apply CkOn_Dw (fun x hx => lie_LR (u := []) (by simp) hlie2 x (by simpa [wL] using hx))
      apply CkOn_trn _ ha hb
      refine sCkOn_mono ?_ hFk
      simp only [wR, List.length_map, zero_add]
      exact_mod_cast (by omega : (T.word.drop j).length ≤ opOrder Θ + 5)
    have hb₂ : ∀ g ∈ GV k r, ‖f₂ g‖ ≤ ‖Lp D p‖ * K₂ := by
      intro g hg
      rw [hf₂, rho_eq_trn, Rw_trn _ ha hb _ hlie2
        (sCkOn_mono (by exact_mod_cast (by omega : (T.word.drop j).length ≤ opOrder Θ + 5)) hFk) g hg]
      exact ((Lp D p).le_opNorm _).trans (mul_le_mul_of_nonneg_left
        (CC_bdd hAd0 hK₂ _ (gv_mul (gv_mul ha hg) hb)) (norm_nonneg _))
    set G : Mat k r → (Wq →L[ℂ] Wp) := fun g => ((‖f₂ g‖ : ℝ) : ℂ) • f₁ g with hG
    have hGn : ∀ g, ‖G g‖ = ‖f₁ g‖ * ‖f₂ g‖ := by
      intro g
      simp only [hG, norm_smul, Complex.norm_real, norm_norm]
      ring
    have hGc : ContinuousOn G (GV k r) := (Complex.continuous_ofReal.comp_continuousOn hc₂.norm).smul hc₁
    have hGm := aesm_of_continuousOn D hGc
    have hfin := hCC G (‖Lp D p‖ * K₂ * K₁) hGm (by
      intro g hg
      have h1 : gN g ^ A * ‖f₁ g‖ ≤ K₁ := hK₁.2 [] [] (by simp) (by simp) (by simp) g hg
      have h0 : 0 ≤ gN g ^ A * ‖f₁ g‖ := mul_nonneg (Real.rpow_nonneg (gN_pos hg).le _) (norm_nonneg _)
      calc gN g ^ A * ‖G g‖ = ‖f₂ g‖ * (gN g ^ A * ‖f₁ g‖) := by rw [hGn]; ring
        _ ≤ ‖Lp D p‖ * K₂ * K₁ := mul_le_mul (hb₂ g hg) h1 h0 ((norm_nonneg _).trans (hb₂ g hg)))
    have hint : Integrable (fun g : Mt k r => G (Matrix.of g)) D.μG := ⟨hGm, hfin⟩
    refine hint.norm.congr (Filter.Eventually.of_forall fun g => ?_)
    exact hGn _

end Formalism.FourierDecayAlt.P

namespace Formalism.FourierDecayAlt.P.BetaSesquilinearity

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

def wt (D : RealPlaceData k r Wp Wq) (q : (Fin r → ℂ) × ℂ) : ℝ := bcWeight k r (Tz k r D.z) (Tz k r D.z') q

lemma wt_nonneg (D : RealPlaceData k r Wp Wq) (q) : 0 ≤ wt D q := by
  unfold wt bcWeight
  split_ifs with h
  · exact mul_nonneg (Finset.prod_nonneg fun a _ => pow_nonneg (norm_nonneg _) _)
      (pow_nonneg (sub_nonneg.mpr h) _)
  · exact le_refl 0

lemma wt_measurable (D : RealPlaceData k r Wp Wq) : Measurable (wt D) := by
  unfold wt bcWeight
  refine Measurable.ite ?_ ?_ measurable_const
  · exact measurableSet_le measurable_const (Complex.continuous_normSq.measurable.comp measurable_snd)
  · exact Continuous.measurable ((continuous_finset_prod _ fun a _ =>
      ((continuous_apply a).comp continuous_fst).norm.pow _).mul
      (((Complex.continuous_normSq.comp continuous_snd).sub continuous_const).pow _))

lemma Qset_measurable (D : RealPlaceData k r Wp Wq) : MeasurableSet (Qset D) :=
  measurableSet_lt measurable_const (wt_measurable D)

lemma wt_eq_zero (D : RealPlaceData k r Wp Wq) {q} (h : q ∉ Qset D) : wt D q = 0 := by
  have h1 : ¬ (0 < wt D q) := h
  exact le_antisymm (not_lt.mp h1) (wt_nonneg D q)

def μQ (D : RealPlaceData k r Wp Wq) : Measure ((Fin r → ℂ) × ℂ) :=
  (volume.restrict (Qset D)).withDensity fun q => ENNReal.ofReal (wt D q)

lemma μQ_ac (D : RealPlaceData k r Wp Wq) : μQ D ≪ volume.restrict (Qset D) := withDensity_absolutelyContinuous _ _

def Jv (D : RealPlaceData k r Wp Wq) (τ : ℝ × ℝ) (F : Mat k r → (Wq →L[ℂ] Wp)) (q : (Fin r → ℂ) × ℂ) :
    PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp) := hsVec (Jtau D τ F (gq D q))

lemma lint_μQ (D : RealPlaceData k r Wp Wq) (f : (Fin r → ℂ) × ℂ → ℝ≥0∞) :
    ∫⁻ q, f q ∂μQ D = ∫⁻ q, ENNReal.ofReal (wt D q) * f q := by
  unfold μQ
  rw [lintegral_withDensity_eq_lintegral_mul_non_measurable _ (wt_measurable D).ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  rw [← lintegral_indicator (Qset_measurable D)]
  congr 1
  funext q
  by_cases hq : q ∈ Qset D
  · simp [Set.indicator_apply, hq]
  · simp [Set.indicator_apply, hq, wt_eq_zero D hq]

lemma normSqTau_eq (D : RealPlaceData k r Wp Wq) (τ : ℝ × ℝ) (F : Mat k r → (Wq →L[ℂ] Wp)) :
    normSqTau D τ F = ∫⁻ q, ‖Jv D τ F q‖ₑ ^ 2 ∂μQ D := by
  rw [lint_μQ]
  unfold normSqTau jNormSq
  refine lintegral_congr fun q => ?_
  rw [ENNReal.ofReal_mul (show 0 ≤ bcWeight k r (Tz k r D.z) (Tz k r D.z') q from wt_nonneg D q),
    ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
  rfl

lemma int_μQ (D : RealPlaceData k r Wp Wq) (f : (Fin r → ℂ) × ℂ → ℂ) :
    ∫ q, f q ∂μQ D = ∫ q, (wt D q : ℂ) * f q := by
  unfold μQ
  rw [integral_withDensity_eq_integral_toReal_smul (wt_measurable D).ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun q hq => by rw [wt_eq_zero D hq]; simp)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
  simp only [ENNReal.toReal_ofReal (wt_nonneg D q), Complex.real_smul]

lemma betaTau_eq (D : RealPlaceData k r Wp Wq) (τ : ℝ × ℝ) (F F' : Mat k r → (Wq →L[ℂ] Wp)) :
    betaTau D τ F F' = ∫ q, inner ℂ (Jv D τ F' q) (Jv D τ F q) ∂μQ D := by
  rw [int_μQ]
  rfl

lemma hsVec_add (A B : Wq →L[ℂ] Wp) : hsVec (A + B) = hsVec A + hsVec B := by
  ext i
  simp [hsVec]

lemma hsVec_smul (a : ℂ) (A : Wq →L[ℂ] Wp) : hsVec (a • A) = a • hsVec A := by
  ext i
  simp [hsVec]

lemma hsVec_cont : Continuous (hsVec : (Wq →L[ℂ] Wp) → _) := by
  let φ : (Wq →L[ℂ] Wp) →ₗ[ℂ] PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp) :=
    { toFun := hsVec, map_add' := hsVec_add, map_smul' := fun a A => hsVec_smul a A }
  exact φ.continuous_of_finiteDimensional

lemma isOpen_Quad : IsOpen Quad := isOpen_Ioi.prod isOpen_Ioi

section steps

variable {D : RealPlaceData k r Wp Wq} {A : ℝ}

lemma ae_eq (hAe : AeFromTests) (hRB : RegBound D A) (hRA : RegAverage D A) (hU : Unfold D A)
    {F : Mat k r → (Wq →L[ℂ] Wp)} (hF : InCC A 4 F) :
    ∀ᵐ τ ∂(volume.restrict Quad), normSqTau D τ F ≠ ∞ ∧
      (((normSqTau D τ F).toReal : ℝ) : ℂ) = betaInfTau D τ F F := by
  obtain ⟨hm, hu⟩ := hU F hF
  refine hAe _ _ hm (hRB.2.1 F F hF hF) ?_
  intro w₁ w₂ h1 h2 p1 p2
  obtain ⟨a, b⟩ := hu w₁ w₂ h1 h2 p1 p2
  exact ⟨a, b.trans (hRA F F hF hF w₁ w₂ h1 h2).2.symm⟩

lemma inf_abs (hAe : AeFromTests) (hRB : RegBound D A) (hRA : RegAverage D A) (hU : Unfold D A)
    {F : Mat k r → (Wq →L[ℂ] Wp)} (hF : InCC A 4 F) :
    ∀ τ ∈ Quad, betaInfTau D τ F F = ((|(betaInfTau D τ F F).re| : ℝ) : ℂ) := by
  have hc := hRB.2.1 F F hF hF
  have hc' : ContinuousOn (fun τ => ((|(betaInfTau D τ F F).re| : ℝ) : ℂ)) Quad :=
    Complex.continuous_ofReal.comp_continuousOn
      (continuous_abs.comp_continuousOn (Complex.continuous_re.comp_continuousOn hc))
  refine Measure.eqOn_open_of_ae_eq (μ := volume) ?_ isOpen_Quad hc hc'
  filter_upwards [ae_eq hAe hRB hRA hU hF] with τ h
  rw [← h.2]
  simp [abs_of_nonneg ENNReal.toReal_nonneg]

lemma Jv_aesm (hJ : JCont D A) {F : Mat k r → (Wq →L[ℂ] Wp)} (hF : InCC A 4 F) {τ : ℝ × ℝ} (hτ : τ ∈ Quad) :
    AEStronglyMeasurable (Jv D τ F) (μQ D) :=
  (hsVec_cont.comp_aestronglyMeasurable ((hJ F hF).2.2 τ hτ)).mono_ac (μQ_ac D)

lemma diagDom (hAe : AeFromTests) (hFa : FatouParam) (hRB : RegBound D A) (hRA : RegAverage D A)
    (hU : Unfold D A) (hJ : JCont D A) : DiagDom D A := by
  intro F hF τ hτ
  have habs := inf_abs hAe hRB hRA hU hF
  refine ⟨by rw [habs τ hτ]; simp, ?_⟩
  rw [normSqTau_eq]
  refine hFa _ (μQ D) _ Quad (fun τ => Jv D τ F) (fun τ => (betaInfTau D τ F F).re) isOpen_Quad
    (fun τ hτ => Jv_aesm hJ hF hτ) ?_ ?_ ?_ τ hτ
  · have := (μQ_ac D).ae_le (hJ F hF).2.1
    filter_upwards [this] with q hq
    exact hsVec_cont.comp_continuousOn hq
  · exact Complex.continuous_re.comp_continuousOn (hRB.2.1 F F hF hF)
  · filter_upwards [ae_eq hAe hRB hRA hU hF] with τ h
    rw [← normSqTau_eq, ← h.2]
    simp [ENNReal.ofReal_toReal h.1]

lemma Jv_memLp (hJ : JCont D A) (hDD : DiagDom D A) {F : Mat k r → (Wq →L[ℂ] Wp)} (hF : InCC A 4 F)
    {τ : ℝ × ℝ} (hτ : τ ∈ Quad) : MemLp (Jv D τ F) 2 (μQ D) := by
  rw [memLp_two_iff_integrable_sq_norm (Jv_aesm hJ hF hτ)]
  refine ⟨(Jv_aesm hJ hF hτ).norm.pow 2, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have h := (hDD F hF τ hτ).2
  rw [normSqTau_eq] at h
  refine lt_of_le_of_lt (le_of_eq ?_) (lt_of_le_of_lt h ENNReal.ofReal_lt_top)
  congr 1
  funext q
  rw [enorm_pow, enorm_norm]

lemma int_inner (hJ : JCont D A) (hDD : DiagDom D A) {F G : Mat k r → (Wq →L[ℂ] Wp)} (hF : InCC A 4 F)
    (hG : InCC A 4 G) {τ : ℝ × ℝ} (hτ : τ ∈ Quad) :
    Integrable (fun q => inner ℂ (Jv D τ G q) (Jv D τ F q)) (μQ D) := by
  have h : Integrable (fun q => ‖Jv D τ G q‖ * ‖Jv D τ F q‖) (μQ D) :=
    MemLp.integrable_mul (Jv_memLp hJ hDD hG hτ).norm (Jv_memLp hJ hDD hF hτ).norm
  exact h.mono' ((Jv_aesm hJ hG hτ).inner (Jv_aesm hJ hF hτ)) (Eventually.of_forall fun q => norm_inner_le_norm _ _)

lemma betaTau_self (hJ : JCont D A) {F : Mat k r → (Wq →L[ℂ] Wp)} (hF : InCC A 4 F)
    {τ : ℝ × ℝ} (hτ : τ ∈ Quad) : betaTau D τ F F = (((normSqTau D τ F).toReal : ℝ) : ℂ) := by
  rw [betaTau_eq, normSqTau_eq]
  have : (fun q => inner ℂ (Jv D τ F q) (Jv D τ F q)) = fun q => ((‖Jv D τ F q‖ ^ 2 : ℝ) : ℂ) := by
    funext q
    rw [inner_self_eq_norm_sq_to_K]
    simp
  have hm : AEStronglyMeasurable (fun q => ‖Jv D τ F q‖ ^ 2) (μQ D) := (Jv_aesm hJ hF hτ).norm.pow 2
  rw [this, integral_complex_ofReal, integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun q => by positivity) hm]
  congr 3
  funext q
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

end steps

lemma rho_add (D : RealPlaceData k r Wp Wq) (p : SS k r) (F F' : Mat k r → (Wq →L[ℂ] Wp)) (g : Mat k r) :
    rho D p (F + F') g = rho D p F g + rho D p F' g := by
  simp only [rho, Pi.add_apply, ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add]

lemma rho_smul (D : RealPlaceData k r Wp Wq) (p : SS k r) (a : ℂ) (F : Mat k r → (Wq →L[ℂ] Wp)) (g : Mat k r) :
    rho D p (a • F) g = a • rho D p F g := by
  simp only [rho, Pi.smul_apply, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]

lemma ell_cont (z : Fin (2 * r + k + 1) → ℂ) : Continuous fun n : Mt k r => ell k r z (Matrix.of n) := by
  unfold ell
  refine continuous_finsetSum _ fun a _ => ?_
  by_cases h : a.val + 1 < r
  · simp only [h, dite_true]
    exact (continuous_apply _).comp (continuous_apply _)
  · simp only [h, dite_false]
    unfold Matrix.mulVec dotProduct
    refine continuous_finsetSum _ fun j _ => ?_
    have : Continuous fun n : Mt k r => n (eI k r a) j := (continuous_apply j).comp (continuous_apply (eI k r a))
    exact this.mul continuous_const

lemma xiTau_cont (D : RealPlaceData k r Wp Wq) (τ : ℝ × ℝ) : Continuous (xiTau D τ) := by
  unfold xiTau lam
  have h1 := (ell_cont (k := k) (r := r) D.z).comp (continuous_snd.comp (continuous_fst : Continuous fun p : SS k r => p.1))
  have h2 := (ell_cont (k := k) (r := r) D.z').comp (continuous_snd.comp (continuous_snd : Continuous fun p : SS k r => p.2))
  refine Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp ?_))
  exact (continuous_const.mul (Complex.continuous_re.comp (continuous_const.mul h1))).sub
    (continuous_const.mul (Complex.continuous_re.comp (continuous_const.mul h2)))

lemma xiTau_norm (D : RealPlaceData k r Wp Wq) (τ : ℝ × ℝ) (p : SS k r) : ‖xiTau D τ p‖ = 1 := by
  unfold xiTau
  rw [mul_comm]
  exact Complex.norm_exp_ofReal_mul_I _

lemma xi_int (D : RealPlaceData k r Wp Wq) (τ : ℝ × ℝ) {F : Mat k r → (Wq →L[ℂ] Wp)} {g : Mat k r}
    (h : Integrable (fun p => rho D p F g) D.μSS) : Integrable (fun p => xiTau D τ p • rho D p F g) D.μSS := by
  refine h.mono ((xiTau_cont D τ).aestronglyMeasurable.smul h.aestronglyMeasurable) ?_
  filter_upwards with p
  rw [norm_smul, xiTau_norm, one_mul]

lemma Jtau_add (D : RealPlaceData k r Wp Wq) (τ : ℝ × ℝ) {F F' : Mat k r → (Wq →L[ℂ] Wp)} {g : Mat k r}
    (h : Integrable (fun p => rho D p F g) D.μSS) (h' : Integrable (fun p => rho D p F' g) D.μSS) :
    Jtau D τ (F + F') g = Jtau D τ F g + Jtau D τ F' g := by
  simp only [Jtau]
  rw [← integral_add (xi_int D τ h) (xi_int D τ h')]
  congr 1
  funext p
  rw [rho_add, smul_add]

lemma Jtau_smul (D : RealPlaceData k r Wp Wq) (τ : ℝ × ℝ) (a : ℂ) (F : Mat k r → (Wq →L[ℂ] Wp)) (g : Mat k r) :
    Jtau D τ (a • F) g = a • Jtau D τ F g := by
  simp only [Jtau]
  rw [← integral_smul]
  congr 1
  funext p
  rw [rho_smul, smul_comm]

lemma Jv_smul (D : RealPlaceData k r Wp Wq) (τ : ℝ × ℝ) (a : ℂ) (F : Mat k r → (Wq →L[ℂ] Wp)) (q) :
    Jv D τ (a • F) q = a • Jv D τ F q := by
  simp only [Jv]
  rw [Jtau_smul, hsVec_smul]

section sesq

variable {D : RealPlaceData k r Wp Wq} {A : ℝ}

lemma Jv_add (hJ : JCont D A) {F F' : Mat k r → (Wq →L[ℂ] Wp)} (hF : InCC A 4 F) (hF' : InCC A 4 F')
    (τ : ℝ × ℝ) : ∀ᵐ q ∂μQ D, Jv D τ (F + F') q = Jv D τ F q + Jv D τ F' q := by
  filter_upwards [(μQ_ac D).ae_le (hJ F hF).1, (μQ_ac D).ae_le (hJ F' hF').1] with q h h'
  unfold Jv
  rw [Jtau_add D τ h h', hsVec_add]

lemma betaTau_sesq (hJ : JCont D A) (hDD : DiagDom D A) {τ : ℝ × ℝ} (hτ : τ ∈ Quad) :
    SesqOn (InCC A 4) (betaTau D τ) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x x' y hx hx' hy
    rw [betaTau_eq, betaTau_eq, betaTau_eq, ← integral_add (int_inner hJ hDD hx hy hτ) (int_inner hJ hDD hx' hy hτ)]
    refine integral_congr_ae ?_
    filter_upwards [Jv_add hJ hx hx' τ] with q h
    rw [h, inner_add_right]
  · intro x y y' hx hy hy'
    rw [betaTau_eq, betaTau_eq, betaTau_eq, ← integral_add (int_inner hJ hDD hx hy hτ) (int_inner hJ hDD hx hy' hτ)]
    refine integral_congr_ae ?_
    filter_upwards [Jv_add hJ hy hy' τ] with q h
    rw [h, inner_add_left]
  · intro a x y _ _
    rw [betaTau_eq, betaTau_eq, ← integral_const_mul]
    congr 1
    funext q
    rw [Jv_smul, inner_smul_right]
  · intro a x y _ _
    rw [betaTau_eq, betaTau_eq, ← integral_const_mul]
    congr 1
    funext q
    rw [Jv_smul, inner_smul_left]

end sesq

section zero

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

lemma dLR_zero (u v : List (Mat k r)) : dLR u v (0 : Mat k r → E) = 0 := by
  rw [dLR_eq]
  exact Dw_zero _

lemma inCC_zero (A : ℝ) (m : ℕ) : InCC A m (0 : Mat k r → E) := ⟨0, CCle_zero⟩

lemma CkOn_mono {m m' : ℕ∞} (h : m' ≤ m) {UU : Set (Mat k r)} {f : Mat k r → E} (hf : CkOn m UU f) :
    CkOn m' UU f := sCkOn_mono h hf

lemma InCC_mono {A : ℝ} {m m' : ℕ} (h : m' ≤ m) {F : Mat k r → E} (hF : InCC A m F) : InCC A m' F := sInCC_mono le_rfl h hF

end zero

def CCs (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (hL : CCLin) (A : ℝ) (m : ℕ) :
    Submodule ℂ (Mat k r → (Wq →L[ℂ] Wp)) where
  carrier := {F | InCC A m F}
  add_mem' := by
    rintro a b ⟨c, hc⟩ ⟨c', hc'⟩
    exact ⟨_, (hL k r _ A m a b c c' 0 hc hc').1⟩
  zero_mem' := inCC_zero A m
  smul_mem' := by
    rintro a x ⟨c, hc⟩
    exact ⟨_, (hL k r _ A m x x c c a hc hc).2⟩

lemma aDil_one : aDil k r 1 = 1 := by
  unfold aDil
  rw [← Matrix.diagonal_one]
  congr 1
  funext i
  simp

lemma dilF_one (F : Mat k r → (Wq →L[ℂ] Wp)) : dilF (1, 1) F = F := by
  funext g
  simp [dilF, aDil_one]

lemma scale_qmp {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    Measure.QuasiMeasurePreserving (fun t : ℝ × ℝ => (a * t.1, b * t.2)) volume volume := by
  let e : (ℝ × ℝ) ≃ₗ[ℝ] (ℝ × ℝ) :=
    LinearEquiv.prodCongr (LinearEquiv.smulOfNeZero ℝ ℝ a ha) (LinearEquiv.smulOfNeZero ℝ ℝ b hb)
  have := Measure.LinearMap.quasiMeasurePreserving (volume : Measure (ℝ × ℝ)) (e : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ))
    (LinearEquiv.isUnit_det' e).ne_zero
  exact this

section core

variable {D : RealPlaceData k r Wp Wq} {A : ℝ}

lemma core (hC : FormCoreC) (hAe : AeFromTests) (hFa : FatouParam) (hL : CCLin) (hDC : DilCC) (hA : 0 ≤ A)
    (hRB : RegBound D A) (hRA : RegAverage D A) (hU : Unfold D A) (hJ : JCont D A) (hDB : DilBeta D A)
    {τ₀ : ℝ × ℝ} (hτ₀ : τ₀ ∈ Quad) (F F' : Mat k r → (Wq →L[ℂ] Wp)) (hF : InCC A 5 F) (hF' : InCC A 5 F') :
    betaTau D τ₀ F F' = betaInfTau D τ₀ F F' := by
  classical
  have hDD : DiagDom D A := diagDom hAe hFa hRB hRA hU hJ
  let V := CCs k r Wp Wq hL A 4
  let W : Submodule ℂ V := Submodule.comap V.subtype (CCs k r Wp Wq hL A 5)
  have hs1 := betaTau_sesq hJ hDD hτ₀
  have hs2 := hRB.2.2 τ₀ hτ₀
  have key := hC V W (fun x y => betaTau D τ₀ x.1 y.1) (fun x y => betaInfTau D τ₀ x.1 y.1)
    ⟨fun x x' y => hs1.1 _ _ _ x.2 x'.2 y.2, fun x y y' => hs1.2.1 _ _ _ x.2 y.2 y'.2,
      fun a x y => hs1.2.2.1 a _ _ x.2 y.2, fun a x y => hs1.2.2.2 a _ _ x.2 y.2⟩
    ⟨fun x x' y => hs2.1 _ _ _ x.2 x'.2 y.2, fun x y y' => hs2.2.1 _ _ _ x.2 y.2 y'.2,
      fun a x y => hs2.2.2.1 a _ _ x.2 y.2, fun a x y => hs2.2.2.2 a _ _ x.2 y.2⟩
    ?_ ?_ ?_
  · exact key ⟨F, InCC_mono (by norm_num) hF⟩ hF ⟨F', InCC_mono (by norm_num) hF'⟩ hF'
  · intro x
    show (betaTau D τ₀ x.1 x.1).im = 0 ∧ 0 ≤ (betaTau D τ₀ x.1 x.1).re
    rw [betaTau_self hJ x.2 hτ₀]
    simp
  · intro x
    show (betaTau D τ₀ x.1 x.1).re ≤ (betaInfTau D τ₀ x.1 x.1).re
    rw [betaTau_self hJ x.2 hτ₀, Complex.ofReal_re]
    have h0 : 0 ≤ (betaInfTau D τ₀ x.1 x.1).re := by
      rw [inf_abs hAe hRB hRA hU x.2 τ₀ hτ₀, Complex.ofReal_re]; exact abs_nonneg _
    exact ENNReal.toReal_le_of_le_ofReal h0 (hDD x.1 x.2 τ₀ hτ₀).2
  · intro x hx
    obtain ⟨c5, hc5⟩ : InCC A 5 x.1 := hx
    obtain ⟨C, hCd⟩ := hDC k r Wp Wq A hA
    obtain ⟨C0, U0, hU0, hC0⟩ := hRB.1 τ₀ hτ₀
    have hC0' := hC0 τ₀ (mem_of_mem_nhds hU0)
    let box : Set (ℝ × ℝ) := Set.Icc (1 / 2 : ℝ) 2 ×ˢ Set.Icc (1 / 2 : ℝ) 2
    have hbox : box ∈ 𝓝 ((1, 1) : ℝ × ℝ) :=
      prod_mem_nhds (Icc_mem_nhds (by norm_num) (by norm_num)) (Icc_mem_nhds (by norm_num) (by norm_num))
    have hmem : ∀ t, t ∈ box → InCC A 4 (dilF t x.1) := fun t h =>
      InCC_mono (by norm_num) ⟨_, (hCd t h x.1 c5 hc5).1⟩
    let Φ : ℝ × ℝ → V := fun t => if h : t ∈ box then ⟨dilF t x.1, hmem t h⟩ else x
    have hΦ : ∀ t, t ∈ box → (Φ t).1 = dilF t x.1 := fun t h => by simp only [Φ, dif_pos h]
    refine ⟨Φ, fun t => (((t.1 * t.2) ^ kap k r : ℝ) : ℂ) * betaInfTau D (τ₀.1 * t.1, τ₀.2 * t.2) x.1 x.1,
      (1, 1), ?_, ?_, ?_, ?_, ?_⟩
    · apply Subtype.ext
      rw [hΦ _ (mem_of_mem_nhds hbox), dilF_one]
    · simp
    · have h1 : ContinuousAt (fun τ => betaInfTau D τ x.1 x.1) τ₀ :=
        (hRB.2.1 x.1 x.1 x.2 x.2).continuousAt (isOpen_Quad.mem_nhds hτ₀)
      have h2 : ContinuousAt (fun t : ℝ × ℝ => (τ₀.1 * t.1, τ₀.2 * t.2)) (1, 1) := by fun_prop
      have h3 : ContinuousAt (fun t : ℝ × ℝ => betaInfTau D (τ₀.1 * t.1, τ₀.2 * t.2) x.1 x.1) (1, 1) :=
        ContinuousAt.comp_of_eq (g := fun τ => betaInfTau D τ x.1 x.1)
          (f := fun t : ℝ × ℝ => (τ₀.1 * t.1, τ₀.2 * t.2)) (y := τ₀) h1 h2 (by simp)
      have h4 : ContinuousAt (fun t : ℝ × ℝ => (((t.1 * t.2) ^ kap k r : ℝ) : ℂ)) (1, 1) := by fun_prop
      exact h4.mul h3
    · have hb : ∀ᶠ t in 𝓝 ((1, 1) : ℝ × ℝ), ‖(betaInfTau D τ₀ (Φ t - x).1 (Φ t - x).1).re‖ ≤
          C0 * (C * (|t.1 - 1| + |t.2 - 1|) * c5) * (C * (|t.1 - 1| + |t.2 - 1|) * c5) := by
        filter_upwards [hbox] with t ht
        have e : (Φ t - x).1 = dilF t x.1 - x.1 := by
          show (Φ t).1 - x.1 = _
          rw [hΦ t ht]
        rw [e]
        have h := (hCd t ht x.1 c5 hc5).2
        exact (Complex.abs_re_le_norm _).trans (hC0' _ _ _ _ h h)
      refine squeeze_zero_norm' hb ?_
      have hc : Continuous fun t : ℝ × ℝ =>
          C0 * (C * (|t.1 - 1| + |t.2 - 1|) * c5) * (C * (|t.1 - 1| + |t.2 - 1|) * c5) := by fun_prop
      have := hc.tendsto (1, 1)
      simpa using this
    · refine ⟨Set.Ioo (1 / 2 : ℝ) 2 ×ˢ Set.Ioo (1 / 2 : ℝ) 2,
        prod_mem_nhds (Ioo_mem_nhds (by norm_num) (by norm_num)) (Ioo_mem_nhds (by norm_num) (by norm_num)), ?_⟩
      have h1 := ae_eq hAe hRB hRA hU x.2
      rw [ae_restrict_iff' isOpen_Quad.measurableSet] at h1
      have h2 := (scale_qmp (ne_of_gt hτ₀.1) (ne_of_gt hτ₀.2)).ae h1
      rw [ae_restrict_iff' (measurableSet_Ioo.prod measurableSet_Ioo)]
      filter_upwards [h2] with t ht htU
      have t1 : 0 < t.1 := lt_trans (by norm_num) htU.1.1
      have t2 : 0 < t.2 := lt_trans (by norm_num) htU.2.1
      have htq : t ∈ Quad := ⟨t1, t2⟩
      have htb : t ∈ box := ⟨Set.Ioo_subset_Icc_self htU.1, Set.Ioo_subset_Icc_self htU.2⟩
      have hq : (τ₀.1 * t.1, τ₀.2 * t.2) ∈ Quad := ⟨mul_pos hτ₀.1 t1, mul_pos hτ₀.2 t2⟩
      obtain ⟨-, h3⟩ := ht hq
      show betaTau D τ₀ (Φ t).1 (Φ t).1 = _
      rw [hΦ t htb, betaTau_self hJ (hmem t htb) hτ₀, hDB x.1 x.2 τ₀ hτ₀ t htq, ← h3, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (by positivity)]
      push_cast
      ring

end core

end Formalism.FourierDecayAlt.P.BetaSesquilinearity

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity

theorem assemble_diagonal_identity : Formalism.FourierDecayAlt.B.AssembleDiag := by
  intro hC hAe hFa hL hDC k r Wp Wq _ _ _ _ _ _ D A hA hRB hRA hU hJ hDB
  have hDD : DiagDom D A := diagDom hAe hFa hRB hRA hU hJ
  refine ⟨hDD, ?_⟩
  intro F hF τ hτ
  have hF4 : InCC A 4 F := InCC_mono (by norm_num) hF
  refine ⟨ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hDD F hF4 τ hτ).2, ?_⟩
  rw [← betaTau_self hJ hF4 hτ]
  exact core hC hAe hFa hL hDC hA hRB hRA hU hJ hDB hτ F F hF hF

theorem assemble_equality_identity : Formalism.FourierDecayAlt.B.AssembleEq := by
  intro hC hAe hFa hL hDC hJ1 k r Wp Wq _ _ _ _ _ _ D A hA hRB hRA hU hJ hDB
  have hDD : DiagDom D A := diagDom hAe hFa hRB hRA hU hJ
  have h11 : ((1, 1) : ℝ × ℝ) ∈ Quad := by simp [Quad]
  have eJ : ∀ F : Mat k r → (Wq →L[ℂ] Wp), Jtau D (1, 1) F = JF D F := fun F => funext fun g => hJ1 k r Wp Wq D F g
  have eN : ∀ F : Mat k r → (Wq →L[ℂ] Wp), normSq D F = normSqTau D (1, 1) F := fun F => by
    unfold normSq normSqTau; rw [eJ]
  have eB : ∀ F F' : Mat k r → (Wq →L[ℂ] Wp), beta D F F' = betaTau D (1, 1) F F' := fun F F' => by
    unfold beta betaTau; rw [eJ, eJ]
  have h2 : PairingEqLimitPairing D A := fun F F' hF hF' => by
    rw [eB]
    exact core hC hAe hFa hL hDC hA hRB hRA hU hJ hDB h11 F F' hF hF'
  refine ⟨?_, h2⟩
  obtain ⟨C0, U0, hU0, hC0⟩ := hRB.1 (1, 1) h11
  refine ⟨C0, fun F F' c c' hF hF' hc hc' => ⟨?_, ?_, ?_⟩⟩
  · rw [eN]
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hDD F (InCC_mono (by norm_num) hF) _ h11).2
  · rw [eN]
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hDD F' (InCC_mono (by norm_num) hF') _ h11).2
  · rw [h2 F F' hF hF']
    exact hC0 _ (mem_of_mem_nhds hU0) F F' c c' hc hc'

end Formalism.FourierDecayAlt.P
