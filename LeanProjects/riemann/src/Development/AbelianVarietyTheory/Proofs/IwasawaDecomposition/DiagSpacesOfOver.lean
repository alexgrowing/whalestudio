import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExplicitRanksBasicBoundsLargeScale

noncomputable section

namespace GlobalTheory.Mem.HostFrames

open Formalism.BasicNotions Formalism.IndefR.Links GlobalTheory.EX GlobalTheory.Mem GlobalTheory.Mem.Top NumberField

section Coord

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def SignFrame (S : HSpace E) : Prop :=
  (∃ neg : Fin S.rank → Bool, ∀ a b, S.hT (S.frame a) (S.frame b) = if a = b then (Examples₂.sgn (neg a) : E) else 0) ∧
    S.L0 = Submodule.span (𝓞 E) (Set.range S.frame)

def UnitFrame (S : HSpace E) : Prop :=
  (∀ a b, S.hT (S.frame a) (S.frame b) = if a = b then 1 else 0) ∧ S.L0 = Submodule.span (𝓞 E) (Set.range S.frame)

theorem UnitFrame.signFrame {S : HSpace E} (h : UnitFrame S) : SignFrame S :=
  ⟨⟨fun _ => false, fun a b => by rw [h.1]; simp [Examples₂.sgn]⟩, h.2⟩

variable (hstar : ∀ x : E, IsIntegral ℤ x → IsIntegral ℤ (star x))

theorem signFrame_stdSpace (N : ℕ) (neg : Fin N → Bool) (p q : ℕ) : SignFrame (Examples₂.stdSpace hstar N neg p q) :=
  ⟨⟨neg, Examples₂.stdSpace_gram_apply hstar N neg p q⟩, rfl⟩

theorem unitFrame_stdSpace (N p q : ℕ) : UnitFrame (Examples₂.stdSpace hstar N (fun _ => false) p q) :=
  ⟨fun a b => (Examples₂.stdSpace_gram_apply hstar N (fun _ => false) p q a b).trans (by simp [Examples₂.sgn]; rfl), rfl⟩

theorem SignFrame.gram_eq {S : HSpace E} (h : SignFrame S) (F : Type) [Field F] [Algebra F E] :
    ∃ d : Fin S.rank → F, (∀ a, d a = 1 ∨ d a = -1) ∧ S.gram = Matrix.diagonal fun a => algebraMap F E (d a) := by
  obtain ⟨neg, hn⟩ := h.1
  refine ⟨fun a => Examples₂.sgn (neg a), fun a => by cases hh : neg a <;> simp [Examples₂.sgn, hh], ?_⟩
  ext a b
  rw [HSpace.gram, hn, Matrix.diagonal_apply, Examples₂.map_sgn]

end Coord

section Diag

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  {S : Spaces R F E}

theorem signFrame_Y (h : DiagSpaces S) (j : ℕ) : SignFrame (S.Y j) := by
  obtain ⟨hs, -, -, hY, -, -⟩ := h
  rw [hY]; exact signFrame_stdSpace hs _ _ _ _

theorem signFrame_V (h : DiagSpaces S) (j : ℕ) : SignFrame (S.V j) := by
  obtain ⟨hs, -, -, -, -, hV⟩ := h
  rw [hV]; exact signFrame_stdSpace hs _ _ _ _

theorem signFrame_W_of_one_le_of_le (h : DiagSpaces S) {j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ R.m) : SignFrame (S.W j) := by
  obtain ⟨hs, -, -, -, hW, -⟩ := h
  rw [hW j h1 h2]; exact signFrame_stdSpace hs _ _ _ _

theorem unitFrame_X' (h : DiagSpaces S) : UnitFrame S.X' := by
  obtain ⟨hs, -, hX, -, -, -⟩ := h
  rw [hX]; exact unitFrame_stdSpace hs _ _ _

theorem unitFrame_X (h : DiagSpaces S) (j : ℕ) : UnitFrame (S.X j) := by
  obtain ⟨hs, hX, -, -, -, -⟩ := h
  rw [hX]; exact unitFrame_stdSpace hs _ _ _

theorem unitFrame_V (h : DiagSpaces S) {j : ℕ} (hn : S.Vneg j = false) : UnitFrame (S.V j) ∧ (S.V j).IsPosDef := by
  obtain ⟨hs, -, -, -, -, hV⟩ := h
  rw [hV, hn]; exact ⟨unitFrame_stdSpace hs _ _ _, fun _ => rfl⟩

def setW0 (S : Spaces R F E) (Z : HSpace E) (hZ : Z.SigOK) : Spaces R F E :=
  { S with
    W := fun j => match j with
      | 0 => Z
      | j + 1 => S.W (j + 1)
    W_sig := fun j => match j with
      | 0 => hZ
      | j + 1 => S.W_sig (j + 1)
    W_rank := fun j h1 h2 => match j, h1, h2 with
      | j + 1, h1, h2 => S.W_rank (j + 1) h1 h2
    W_sigval := fun j h1 h2 => match j, h1, h2 with
      | j + 1, h1, h2 => S.W_sigval (j + 1) h1 h2
    baseSpace_isometric_graded := fun j h1 h2 => match j, h1, h2 with
      | j + 1, h1, h2 => S.baseSpace_isometric_graded (j + 1) h1 h2 }

theorem diagSpaces_setW0 (h : DiagSpaces S) (Z : HSpace E) (hZ : Z.SigOK) :
    DiagSpaces (setW0 S Z hZ) ∧ (setW0 S Z hZ).W 0 = Z := by
  obtain ⟨hs, h1, h2, h3, h4, h5⟩ := h
  refine ⟨⟨hs, h1, h2, h3, fun j a b => ?_, h5⟩, rfl⟩
  match j, a, b with
  | j + 1, a, b => exact h4 (j + 1) a b

end Diag

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem diagSpaces_of_over {K : Ctx} {B : Pre} (h : K.Over B) : DiagSpaces B.sp := by
  obtain ⟨sp, hT, hY, hA, hV, hz, rfl, hd⟩ := h
  exact hd

theorem val_of_over {K : Ctx} {B : Pre} (h : K.Over B) :
    RankVal K.s B.R ∧ ∃ bT, ∀ u, HCVal K.s K.cD K.ch B.host (fun τ : Tau B.R => (τ : B.R.GG)) (B.hcW u) bT := by
  obtain ⟨sp, hT, hY, hA, hV, hz, rfl, hd⟩ := h
  exact ⟨K.ok.rank, _, K.ok.hc⟩

theorem frames_of_over (K : Ctx) (X : Stages) (h : K.Over X.B.toPre) :
    X.toD7.host.F = maximalRealSubfield X.toD7.host.E ∧
    (∀ i, SignFrame (Wc X.toD7 i) ∧ SignFrame (Vc X.toD7 i)) ∧ (∀ i, (Vc X.toD7 i).IsPosDef) ∧
    (∀ j, SignFrame (X.toD7.sp.Y j) ∧ SignFrame (X.toD7.sp.V j) ∧ (1 ≤ j → j ≤ X.toD7.R.m → SignFrame (X.toD7.sp.W j))) ∧
    SignFrame X.toD7.sp.X' ∧
    (∀ i, (∀ a b, (Vc X.toD7 i).hT ((Vc X.toD7 i).frame a) ((Vc X.toD7 i).frame b) = if a = b then 1 else 0) ∧
      (Vc X.toD7 i).L0 = Submodule.span (𝓞 X.toD7.host.E) (Set.range (Vc X.toD7 i).frame)) ∧
    ((∀ a b, X.toD7.sp.X'.hT (X.toD7.sp.X'.frame a) (X.toD7.sp.X'.frame b) = if a = b then 1 else 0) ∧
      X.toD7.sp.X'.L0 = Submodule.span (𝓞 X.toD7.host.E) (Set.range X.toD7.sp.X'.frame)) := by
  have hd : DiagSpaces X.toD7.sp := diagSpaces_of_over h
  have hV : ∀ i : Fin X.toD7.R.m, X.toD7.sp.Vneg ((i : ℕ) + 1) = false := fun i => X.B.V_pos _ (by omega) i.2
  exact ⟨rfl, fun i => ⟨signFrame_W_of_one_le_of_le hd (by omega) i.2, signFrame_V hd _⟩, fun i => (unitFrame_V hd (hV i)).2,
    fun j => ⟨signFrame_Y hd j, signFrame_V hd j, signFrame_W_of_one_le_of_le hd⟩, (unitFrame_X' hd).signFrame,
    fun i => (unitFrame_V hd (hV i)).1, unitFrame_X' hd⟩

theorem size_le (eps c : ℝ) (A : ℕ) (he : 0 < eps) (he' : eps < 1 / 52) : ∃ x0 : ℝ, ∀ (s : Scale) (R : Ranks) (y : ℝ),
    s.eps = eps → x0 ≤ s.x → RankVal s R → 402 * (A : ℝ) + 2 ≤ y → c * s.L * (R.N R.m : ℝ) ^ A ≤ (⌈s.x ^ y⌉₊ : ℝ) := by
  obtain ⟨x1, h1⟩ := rank_basic_bounds eps he he'
  refine ⟨max x1 c, fun s R y hs hx hR hy => ?_⟩
  obtain ⟨-, -, -, -, -, hL, hL1, -, -, -, -, -, -, -, hN, -, -⟩ := h1 s R hs ((le_max_left _ _).trans hx) hR
  have hc : c ≤ s.x := (le_max_right _ _).trans hx
  have hx1 : 1 ≤ s.x := s.one_lt_alt.le
  have hx0 : 0 < s.x := by linarith
  have a1 : (R.N R.m : ℝ) ^ A ≤ s.x ^ (402 * (A : ℝ)) := by
    rw [Real.rpow_mul hx0.le, Real.rpow_natCast]
    exact pow_le_pow_left₀ (by positivity) hN A
  have a2 : c * s.L ≤ s.x * s.x := mul_le_mul hc hL (by linarith) hx0.le
  calc c * s.L * (R.N R.m : ℝ) ^ A ≤ s.x * s.x * s.x ^ (402 * (A : ℝ)) :=
        mul_le_mul a2 a1 (by positivity) (by positivity)
    _ = s.x ^ (402 * (A : ℝ) + 2) := by rw [Real.rpow_add hx0, Real.rpow_two]; ring
    _ ≤ s.x ^ y := Real.rpow_le_rpow_of_exponent_le hx1 hy
    _ ≤ _ := Nat.le_ceil _

theorem gaps_ev (c : ℝ) (A : ℕ) : Ev fun K => ∀ X : Stages, K.Over X.B.toPre → ∃ h Δ : ℕ,
    c * K.s.L * (X.toD7.R.N X.toD7.R.m : ℝ) ^ A ≤ h ∧ c * K.s.L * (X.toD7.R.N X.toD7.R.m : ℝ) ^ A ≤ Δ ∧ 1 ≤ K.s.L ∧
    ∀ u τ, (∀ j, (X.toD7.hcW u τ).e j - (X.toD7.hcW u τ).b j = h) ∧
      (∀ (j : Fin X.toD7.R.m) (hj : j.1 + 1 < X.toD7.R.m), (X.toD7.hcW u τ).b ⟨j.1 + 1, hj⟩ - (X.toD7.hcW u τ).e j = h) ∧
      ∀ i : Fin (X.toD7.R.k - 1), (X.toD7.hcW u τ).v i = ((X.toD7.R.k - 2 - i.1 : ℕ) : ℚ) * (4 * Δ) := by
  refine ⟨1, one_pos, fun eps C8 he _ he' _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun C _ _ _ =>
    ⟨402 * A + 2, fun cD hcD => ⟨402 * A + 2, fun ch hch => ?_⟩⟩⟩⟩
  obtain ⟨x0, h0⟩ := size_le eps c A he he'
  refine ⟨x0, fun K _ k1 k2 k3 k4 X hX => ?_⟩
  obtain ⟨hR, bT, hH⟩ := val_of_over hX
  refine ⟨⌈K.s.x ^ K.ch⌉₊, Delv K.s K.cD, h0 _ _ _ k3 k4 hR (k2 ▸ hch), h0 _ _ _ k3 k4 hR (k1 ▸ hcD),
    Real.one_le_rpow K.s.one_lt_alt.le K.s.eps_pos.le, fun u τ => ?_⟩
  obtain ⟨hv, -, ⟨b1, hb, -⟩, -⟩ := hH u
  refine ⟨fun j => ?_, fun j hj => ?_, hv τ⟩
  · have := (hb τ j).2
    show (X.B.hcW u τ).e j - (X.B.hcW u τ).b j = _
    rw [this]
    simp only [h0v]; push_cast; ring
  · have e1 := (hb τ j).2
    have e2 := (hb τ j).1
    have e3 := (hb τ ⟨j.1 + 1, hj⟩).1
    refine (congrArg₂ (· - ·) e3 (e1.trans (congrArg (· + _) e2))).trans ?_
    simp only [h0v]; push_cast; ring

end GlobalTheory.Mem.HostFrames

end
