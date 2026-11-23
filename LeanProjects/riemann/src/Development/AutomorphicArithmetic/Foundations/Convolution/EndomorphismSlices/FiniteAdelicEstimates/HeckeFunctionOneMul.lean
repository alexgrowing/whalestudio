import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.SphComm2
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.ConvMul
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.HeckeFunctionIsHecke
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.FinSplit
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.IdmAct
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.PositionTest
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.LocAlg
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.HintTranslate

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf TypeB TypeH)
open UpperTheory.V.Z.Tf.GlobalTraceComparison
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

namespace UpperTheory.Zero.ConvolutionTheory.EB

attribute [local instance] borelG borelF borelA borelH

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

private theorem heckeFunction_mul (w : Pl E) (x y : Ex (Fin (a + 1) × Fin (b + 1))) :
    fn2 a b w (x.mul y) = PositivityTheory.Rg.BcN.F2.mconv (fn2 a b w x) (fn2 a b w y) := by
  funext m
  simp only [fn2, Ex.fn, PositivityTheory.Rg.BcN.F2.mconv]

private theorem heckeFunction_one (w : Pl E) :
    fn2 a b w (.one : Ex (Fin (a + 1) × Fin (b + 1))) = (K2 a b w : Set _).indicator 1 := rfl

private theorem heckeFunction_mul_one {Z : Finset (Pl E)} (L : Lv a b Z) (w : Pl E) (x : Ex (Fin (a + 1) × Fin (b + 1))) :
    fn2 a b w (x.mul .one) = fn2 a b w x := by
  rw [heckeFunction_mul, heckeFunction_one]
  exact ((locAlg E a b Z L w).2.2.2.2 _ (Asm.exHecke2 E a b w x)).1

private theorem heckeFunction_one_mul {Z : Finset (Pl E)} (L : Lv a b Z) (w : Pl E) (x : Ex (Fin (a + 1) × Fin (b + 1))) :
    fn2 a b w (Ex.one.mul x) = fn2 a b w x := by
  rw [heckeFunction_mul, heckeFunction_one]
  exact ((locAlg E a b Z L w).2.2.2.2 _ (Asm.exHecke2 E a b w x)).2.1

private theorem position_congr {Z : Finset (Pl E)} (φ : ∀ w : Pl E, LF a b w) {w : Pl E}
    {e e' : Pl E → Ex (Fin (a + 1) × Fin (b + 1))} (h : fn2 a b w (e w) = fn2 a b w (e' w)) :
    intersection_update_fsHerm_neg_one Z {w} φ e = intersection_update_fsHerm_neg_one Z {w} φ e' := by
  funext x
  unfold intersection_update_fsHerm_neg_one
  by_cases hx : x = w
  · subst hx
    simp [h]
  · simp [hx]

end

theorem hkVal : HkVal := by
  intro E _ _ _ a b l₁ l₂ D A S Z L hS hZ f t₁ t₂ T e₁ e₂ hT hd hc hlv hev
  obtain ⟨-, -, -, hone, hemp, hfx, hfin, hins⟩ := hkMul E a b l₁ l₂ D A S Z L hS hZ
  have hCM : ∀ ψ ψ' : Matrix Unit Unit (Hf E a b → ℂ), IsFinM ψ → IsFinM ψ' →
      convF A.ν (mulF A.ν ψ ψ') f = convF A.ν ψ (convF A.ν ψ' f) ∧
      convF A.ν (ψ + ψ') f = convF A.ν ψ f + convF A.ν ψ' f ∧
      ∀ c : ℂ, convF A.ν (c • ψ) f = c • convF A.ν ψ f ∧ convF A.ν ψ (c • f) = c • convF A.ν ψ f :=
    (convMul E A.blk f hc).2
  have hfix : convF A.ν (A.idm S L) f = f := (idmAct E a b l₁ l₂ D A S Z L hS hZ).2.2 f hlv
  have hln : L.Fix L.ln := (positionTest E a b S Z L hZ).1
  have hmul : ∀ (T : Finset (Pl E)) (x₁ x₂ y₁ y₂ : Pl E → Ex (Fin (a + 1) × Fin (b + 1))),
      mulF A.ν (A.hk S L T x₁ x₂) (A.hk S L T y₁ y₂) =
        A.hk S L T (fun w => (x₁ w).mul (y₁ w)) (fun w => (x₂ w).mul (y₂ w)) :=
    fun T x₁ x₂ y₁ y₂ => (hfx T L.ln x₁ x₂ hln).2.2 y₁ y₂
  have hact : ∀ (ψ ψ' : Matrix Unit Unit (Hf E a b → ℂ)) (c c' : ℂ), IsFinM ψ → IsFinM ψ' →
      convF A.ν ψ f = c • f → convF A.ν ψ' f = c' • f → convF A.ν (mulF A.ν ψ ψ') f = (c * c') • f := by
    intro ψ ψ' c c' h h' hc₁ hc₂
    rw [(hCM ψ ψ' h h').1, hc₂, ((hCM ψ ψ' h h').2.2 c').2, hc₁, smul_smul, mul_comm]
  have hcg : ∀ (w : Pl E) (x₁ x₂ y₁ y₂ : Pl E → Ex (Fin (a + 1) × Fin (b + 1))),
      fn2 a b w (x₁ w) = fn2 a b w (y₁ w) → fn2 a b w (x₂ w) = fn2 a b w (y₂ w) →
      A.hk S L {w} x₁ x₂ = A.hk S L {w} y₁ y₂ := by
    intro w x₁ x₂ y₁ y₂ h₁ h₂
    show A.ff S (intersection_update_fsHerm_neg_one Z {w} L.ln x₁) (intersection_update_fsHerm_neg_one Z {w} L.ln x₂) = A.ff S (intersection_update_fsHerm_neg_one Z {w} L.ln y₁) (intersection_update_fsHerm_neg_one Z {w} L.ln y₂)
    rw [position_congr L.ln h₁, position_congr L.ln h₂]
  have hone' : ∀ w : Pl E, convF A.ν (A.hk S L {w} (fun _ => .one) (fun _ => .one)) f = f := by
    intro w
    rw [hone, hfix]
  have left : ∀ w ∈ T, ∀ x : Ex (Fin (a + 1) × Fin (b + 1)),
      convF A.ν (A.hk S L {w} (fun _ => x) (fun _ => .one)) f = x.ev (t₁ w) • f := by
    intro w hw x
    have hwS : w ∈ S := hT.1 w hw
    have hwZ : w ∉ Z := Finset.disjoint_left.1 hd hw
    have hl := fun x y z c => hkLin E a b l₁ l₂ D A S Z L hS hZ w hwS hwZ x y z c
    induction x with
    | one => rw [hone' w]; simp [Ex.ev]
    | gen p => simpa [Ar.hk1, Ex.ev] using (hev w hw p).1
    | smul c x ih =>
      rw [(hl x x .one c).2.1, ((hCM _ _ (hfin {w} (fun _ => x) (fun _ => .one)).1
        (hfin {w} (fun _ => x) (fun _ => .one)).1).2.2 c).1, ih, smul_smul]
      rfl
    | add x y ihx ihy =>
      rw [(hl x y .one 0).1, (hCM _ _ (hfin {w} (fun _ => x) (fun _ => .one)).1
        (hfin {w} (fun _ => y) (fun _ => .one)).1).2.1, ihx, ihy, ← add_smul]
      rfl
    | mul x y ihx ihy =>
      have h := hact _ _ _ _ (hfin _ _ _).1 (hfin _ _ _).1 ihx ihy
      rw [hmul, hcg w (fun w => (fun _ => x) w |>.mul ((fun _ => y) w))
        (fun w => (Ex.one).mul .one) (fun _ => x.mul y) (fun _ => .one) rfl (heckeFunction_mul_one L w .one)] at h
      exact h
  have right : ∀ w ∈ T, IsSplitAt w → ∀ y : Ex (Fin (a + 1) × Fin (b + 1)),
      convF A.ν (A.hk S L {w} (fun _ => .one) (fun _ => y)) f = y.ev (t₂ w) • f := by
    intro w hw hsp y
    have hwS : w ∈ S := hT.1 w hw
    have hwZ : w ∉ Z := Finset.disjoint_left.1 hd hw
    have hl := fun x y z c => (hkLin E a b l₁ l₂ D A S Z L hS hZ w hwS hwZ x y z c).2.2.1 hsp
    induction y with
    | one => rw [hone' w]; simp [Ex.ev]
    | gen p => simpa [Ar.hk1, Ex.ev] using (hev w hw p).2 hsp
    | smul c x ih =>
      rw [(hl x x .one c).2, ((hCM _ _ (hfin {w} (fun _ => .one) (fun _ => x)).1
        (hfin {w} (fun _ => .one) (fun _ => x)).1).2.2 c).1, ih, smul_smul]
      rfl
    | add x y ihx ihy =>
      rw [(hl x y .one 0).1, (hCM _ _ (hfin {w} (fun _ => .one) (fun _ => x)).1
        (hfin {w} (fun _ => .one) (fun _ => y)).1).2.1, ihx, ihy, ← add_smul]
      rfl
    | mul x y ihx ihy =>
      have h := hact _ _ _ _ (hfin _ _ _).1 (hfin _ _ _).1 ihx ihy
      rw [hmul, hcg w (fun w => (Ex.one).mul .one) (fun w => (fun _ => x) w |>.mul ((fun _ => y) w))
        (fun _ => .one) (fun _ => x.mul y) (heckeFunction_mul_one L w .one) rfl] at h
      exact h
  have place : ∀ w ∈ T, convF A.ν (A.hk S L {w} e₁ e₂) f = ((e₁ w).ev (t₁ w) * (e₂ w).ev (t₂ w)) • f := by
    intro w hw
    by_cases hsp : IsSplitAt w
    · have h := hact _ _ _ _ (hfin {w} (fun _ => e₁ w) (fun _ => .one)).1
        (hfin {w} (fun _ => .one) (fun _ => e₂ w)).1 (left w hw (e₁ w)) (right w hw hsp (e₂ w))
      rw [hmul, hcg w _ _ e₁ e₂ (heckeFunction_mul_one L w (e₁ w)) (heckeFunction_one_mul L w (e₂ w))] at h
      exact h
    · have hwS : w ∈ S := hT.1 w hw
      have hwZ : w ∉ Z := Finset.disjoint_left.1 hd hw
      have h₁ : A.hk S L {w} e₁ e₂ = A.hk S L {w} (fun _ => e₁ w) (fun _ => .one) :=
        (hcg w e₁ e₂ (fun _ => e₁ w) (fun _ => e₂ w) rfl rfl).trans
          ((hkLin E a b l₁ l₂ D A S Z L hS hZ w hwS hwZ (e₂ w) .one (e₁ w) 0).2.2.2 hsp)
      rw [h₁, left w hw (e₁ w), hT.2 w hw hsp, mul_one]
  have all : ∀ T' : Finset (Pl E), T' ⊆ T →
      convF A.ν (A.hk S L T' e₁ e₂) f = (∏ w ∈ T', (e₁ w).ev (t₁ w) * (e₂ w).ev (t₂ w)) • f := by
    intro T'
    refine Finset.induction_on T' ?_ ?_
    · intro _
      rw [hemp, hfix]
      simp
    · intro w T'' hw ih hsub
      have hwT : w ∈ T := hsub (Finset.mem_insert_self w T'')
      rw [hins T'' w e₁ e₂ hw, Finset.prod_insert hw]
      exact hact _ _ _ _ (hfin _ _ _).1 (hfin _ _ _).1 (place w hwT)
        (ih fun x hx => hsub (Finset.mem_insert_of_mem hx))
  exact all T subset_rfl

end UpperTheory.Zero.ConvolutionTheory.EB
