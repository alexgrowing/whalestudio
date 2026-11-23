import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.FNonneg
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.IntegralityGoodReduction

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open GroundTheory.Automorphic GroundTheory.Automorphic.CuspidalSpectrum
open scoped ContDiff TensorProduct

namespace UpperTheory.V.Lit.Geo

section Abs

variable {V' V F : Type} [NormedAddCommGroup V'] [NormedSpace ℝ V'] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def pb (H : V' → V) {q : ℕ} (w : V → V [⋀^Fin q]→L[ℝ] F) (p : V') : V' [⋀^Fin q]→L[ℝ] F :=
  (w (H p)).compContinuousLinearMap (fderiv ℝ H p)

theorem pb_apply (H : V' → V) {q : ℕ} (w : V → V [⋀^Fin q]→L[ℝ] F) (p : V') (v : Fin q → V') :
    pb H w p v = w (H p) fun i => fderiv ℝ H p (v i) := rfl

def flow (W : V → V) (t : ℝ) (p : V) : V := p + t • W p

def hk (W : V → V) (t : ℝ) {q : ℕ} (w : V → V [⋀^Fin (q + 1)]→L[ℝ] F) (p : V) : V [⋀^Fin q]→L[ℝ] F :=
  ((w (flow W t p)).curryLeft (W p)).compContinuousLinearMap (fderiv ℝ (flow W t) p)

theorem hk_apply (W : V → V) (t : ℝ) {q : ℕ} (w : V → V [⋀^Fin (q + 1)]→L[ℝ] F) (p : V) (v : Fin q → V) :
    hk W t w p v = w (flow W t p) (Matrix.vecCons (W p) fun i => fderiv ℝ (flow W t) p (v i)) := rfl

def hom (W : V → V) {q : ℕ} (w : V → V [⋀^Fin (q + 1)]→L[ℝ] F) (p : V) : V [⋀^Fin q]→L[ℝ] F :=
  ∫ t in (0 : ℝ)..1, hk W t w p

def IsField (Y : Set V) (W : V → V) : Prop :=
  ContDiffOn ℝ ∞ W Y ∧ ∀ p ∈ Y, ∀ t ∈ Set.Icc (0 : ℝ) 1, flow W t p ∈ Y

end Abs

section Om

variable {Γ V S : Type} [Group Γ] [NormedAddCommGroup V] [NormedSpace ℝ V] {d : ℕ} (G : Dr.Geo Γ V S d)

structure IsFlow (W : S → V → V) : Prop where
  field : ∀ s, IsField G.Y (W s)
  equiv : ∀ γ s, ∀ p ∈ G.Y, W (G.σ γ s) (G.ρ γ p) = G.ρ γ (W s p)
  homog : ∀ s (t : ℝ), 0 < t → ∀ p ∈ G.Y, W s (t • p) = t • W s p

theorem isFlow_zero : IsFlow G 0 :=
  ⟨fun _ => ⟨contDiffOn_const, fun p hp t _ => by simpa [flow] using hp⟩, fun _ _ _ _ => by simp, fun _ _ _ _ _ => by simp⟩

open Classical in

def toOm {q : ℕ} (z : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) : G.Om q :=
  if h : ∀ s, ContDiffOn ℝ ∞ (z s) G.Y then
    ⟨fun s => G.Y.indicator (z s), fun s =>
      ⟨(h s).congr fun _ hp => Set.indicator_of_mem hp _, fun _ hp => Set.indicator_of_notMem hp _⟩⟩
  else 0

theorem toOm_apply {q : ℕ} {z : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)} (h : ∀ s, ContDiffOn ℝ ∞ (z s) G.Y) (s : S) {p : V}
    (hp : p ∈ G.Y) : (toOm G z).1 s p = z s p := by
  rw [toOm, dif_pos h]
  exact Set.indicator_of_mem hp _

def pbOm (W : S → V → V) {q : ℕ} (w : G.Om q) : G.Om q := toOm G fun s => pb (flow (W s) 1) (w.1 s)

def homOm (W : S → V → V) {q : ℕ} (w : G.Om (q + 1)) : G.Om q := toOm G fun s => hom (W s) (w.1 s)

structure Good {q : ℕ} (w : G.Om q) : Prop where
  inv : ∀ γ, G.act q γ w = w
  basic : ∀ s, RadBasic G.Y (w.1 s)
  dbasic : ∀ s, RadBasic G.Y ((G.dOm q w).1 s)

end Om

section Ad

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

structure IsFld (U : Subgroup (GL (Fin a) (Af E))) (Y : GA E a → Herm E a) (C : ℝ) : Prop where
  sm : ∀ i j w, ∃ φ : Sm E a, (∀ g, φ.1 g = (Y g).1 i j w) ∧ BddDer φ
  left : ∀ γ t g, Y (ratGL E a γ * splitCentre E a t * g) = Y g
  cpt : ∀ (k : Kinf E a) g, adHerm k (Y (g * infGL E a (Unitary.toUnits k))) = Y g
  lev : ∀ u ∈ U, ∀ g, Y (g * finGL E a u) = Y g
  root : ∀ g (t : ℝ), |t| ≤ 1 → ∃ h : GL (Fin a) (Cinf E), h.val * star h.val = 1 + t • (Y g).1 ∧
    ‖toL h.val‖ ≤ C ∧ ‖toL (h⁻¹).val‖ ≤ C

theorem IsStep.fld {U : Subgroup (GL (Fin a) (Af E))} {f : GA E a → ℝ} {Y : GA E a → Herm E a} {C c f₀ : ℝ}
    (h : IsStep U f Y C c f₀) : IsFld U Y C := ⟨h.Y_sm, h.Y_left, h.Y_cpt, h.Y_lev, h.root⟩

theorem IsFld.neg {U : Subgroup (GL (Fin a) (Af E))} {Y : GA E a → Herm E a} {C : ℝ} (h : IsFld U Y C) :
    IsFld U (-Y) C where
  sm i j w := by
    obtain ⟨φ, h1, h2⟩ := h.sm i j w
    refine ⟨-φ, fun g => congrArg Neg.neg (h1 g), fun X l => ?_⟩
    obtain ⟨B, hB⟩ := h2 X l
    exact ⟨B, fun g => by rw [map_neg]; exact (norm_neg _).trans_le (hB g)⟩
  left γ t g := congrArg Neg.neg (h.left γ t g)
  cpt k g := by
    have e := congrArg Subtype.val (h.cpt k g)
    refine Subtype.ext ?_
    change k.1 * (-(Y (g * infGL E a (Unitary.toUnits k))).1) * star k.1 = -(Y g).1
    rw [mul_neg, neg_mul, ← e]
    rfl
  lev u hu g := congrArg Neg.neg (h.lev u hu g)
  root g t ht := by
    obtain ⟨x, h1, h2⟩ := h.root g (-t) (by rwa [abs_neg])
    exact ⟨x, by rw [h1, neg_smul]; exact congrArg (1 + ·) (smul_neg t (Y g).1).symm, h2⟩

def FCorr (U : Subgroup (GL (Fin a) (Af E))) (Y : GA E a → Herm E a) (W : (GL (Fin a) (Af E) ⧸ U) → HV E a → HV E a) : Prop :=
  ∀ (g : GL (Fin a) (Cinf E)) (x : GL (Fin a) (Af E)),
    W (x : GL (Fin a) (Af E) ⧸ U) (sand g (hOne E a)) = sand g (hv (Y (infGL E a g * finGL E a x)))

theorem FCorr.neg {U : Subgroup (GL (Fin a) (Af E))} {Y : GA E a → Herm E a}
    {W : (GL (Fin a) (Af E) ⧸ U) → HV E a → HV E a} (h : FCorr U Y W) : FCorr U (-Y) (-W) := fun g x => by
  simp only [Pi.neg_apply, map_neg, h g x]

def Bd {Ξ : AlgRep E a} {q : ℕ} (α : Co Ξ q) (g : GA E a) (M : ℝ) : Prop :=
  ∀ X : Fin q → Herm E a, ‖ev (α X) (retractOne g : KernelIndexFullLattice.G1 E a).1‖ ≤ M * ∏ i, ‖hv (X i)‖

theorem Bd.mono {Ξ : AlgRep E a} {q : ℕ} {α : Co Ξ q} {g : GA E a} {M M' : ℝ} (h : Bd α g M) (hM : M ≤ M') : Bd α g M' :=
  fun X => (h X).trans (mul_le_mul_of_nonneg_right hM (Finset.prod_nonneg fun _ _ => norm_nonneg _))

theorem Bd.sub {Ξ : AlgRep E a} {q : ℕ} {α β : Co Ξ q} {g : GA E a} {M M' : ℝ} (h : Bd α g M) (h' : Bd β g M') :
    Bd (α - β) g (M + M') := fun X => by
  rw [AlternatingMap.sub_apply, map_sub, Pi.sub_apply, add_mul]
  exact (norm_sub_le _ _).trans (add_le_add (h X) (h' X))

end Ad

end UpperTheory.V.Lit.Geo
