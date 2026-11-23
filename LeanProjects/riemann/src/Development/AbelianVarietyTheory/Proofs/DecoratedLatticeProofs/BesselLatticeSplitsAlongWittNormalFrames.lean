import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsNormalFr
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSplitLatMonoId
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GoodPositionSplitLinesReadCompletionsAtPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RatMulVecSec
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitIdealCompletionAtPlaceEqIntegralAdelesAtPlac
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittProjAnisotropicMulVecLeviEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsTameFinitePlaceHermitianAll
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RatioOKOfRootOfUnity
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.MonoBes

open GlobalTheory.FinPl GlobalTheory.SeeSaw.SplitLat

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mul_mem_iff {c : k} (hc : valuation k c = 1) (y : k) : c * y ∈ 𝒪[k] ↔ y ∈ 𝒪[k] := by
  rw [Valuation.mem_integer_iff, Valuation.mem_integer_iff, map_mul, hc, one_mul]

theorem ne_zero_of_val {x : k} (h : valuation k x = 1) : x ≠ 0 := by
  rintro rfl
  rw [map_zero] at h
  exact zero_ne_one h

theorem sec_mem_intAt_iff (q : SplitPt D k) (c : k) : q.sec c ∈ intAt D (· = q.v) ↔ c ∈ 𝒪[k] :=
  ⟨fun h => (q.int_iff c).2 h.2, FrameLat.sec_mem_intAt q c⟩

theorem sec_pr_eq (q : SplitPt D k) (x : D.host.E) : q.sec ((ofSplit q).pr x) = incA D x * q.e := by
  rw [show (ofSplit q).pr x = q.pr (incA D x) from rfl, q.sec_pr, mul_comm]

theorem val_xi (q : SplitPt D k) (hU : q.UnitAA) : valuation k (ofSplit q).xi = 1 := by
  have h1 := (hU.1 q.e (FrameLat.e_mem_intAt q)).1
  have h2 := (hU.1 q.e (FrameLat.e_mem_intAt q)).2
  rw [← sec_pr_eq, sec_mem_intAt_iff] at h1 h2
  have e : (ofSplit q).pr D.host.xi0⁻¹ = ((ofSplit q).xi)⁻¹ := by
    rw [← GlobalTheory.SliceModel.prH_apply, map_inv₀]; rfl
  rw [e, Valuation.mem_integer_iff, map_inv₀] at h2
  rw [Valuation.mem_integer_iff] at h1
  have hne : valuation k (ofSplit q).xi ≠ 0 := by
    rw [Ne, Valuation.zero_iff]; exact GlobalTheory.LocMod.Witness.xi_ne (ofSplit q)
  exact le_antisymm h1 (by
    by_contra hlt
    push_neg at hlt
    have := (one_lt_inv₀ (zero_lt_iff.2 hne)).2 hlt
    exact absurd h2 (not_le.2 this))

end GlobalTheory.MonoBes

namespace GlobalTheory.MonoBes

open GlobalTheory.FinPl GlobalTheory.SeeSaw.SplitLat

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem eq_sec_add_csec (q : SplitPt D k) {n : ℕ} {y : Fin n → AE D} (hy : ∀ i, y i ∈ idAt D (· = q.v)) :
    y = (fun i => q.sec (q.pr (y i))) + (fun i => cA D (q.sec (q.pr (cA D (y i))))) := by
  funext i
  have h := (FrameLat.idem_iff q (y i)).1 (hy i)
  simp only [Pi.add_apply, q.sec_pr, map_mul, cA_cA]
  rw [← add_mul, h]

theorem mem_of_sec_iff (q : SplitPt D k) {S : HSp D} {L L' : Lat S} (hL : IsSelfDualC S L) (hL' : IsSelfDualC S L')
    (h : ∀ u : Fin S.rank → k, (fun i => q.sec (u i)) ∈ latV S L (· = q.v) ↔ (fun i => q.sec (u i)) ∈ latV S L' (· = q.v))
    {y : Fin S.rank → AE D} (hy : y ∈ latV S L (· = q.v)) : y ∈ latV S L' (· = q.v) := by
  have hs : ∀ i, y i ∈ idAt D (· = q.v) := fun i => FrameLat.latV_supp hy i
  rw [eq_sec_add_csec q hs] at hy ⊢
  have hy' := (FrameLat.decomp hL (fun i => q.pr (y i)) (fun i => q.pr (cA D (y i)))).1 hy
  refine (FrameLat.decomp hL' (fun i => q.pr (y i)) (fun i => q.pr (cA D (y i)))).2 ⟨(h _).1 hy'.1, ?_⟩
  have hd := (FrameLat.csec_mem_iff hL (fun i => q.pr (cA D (y i)))).1 hy'.2
  exact (FrameLat.csec_mem_iff hL' (fun i => q.pr (cA D (y i)))).2 fun x hx => hd x ((h x).2 hx)

theorem latV_eq_of_frame (q : SplitPt D k) {S : HSp D} {L L' : Lat S} (hL : IsSelfDualC S L) (hL' : IsSelfDualC S L')
    {Y : Type} [Fintype Y] [DecidableEq Y] (F : GlobalTheory.LocMod.Frame k S.rank Y) (h1 : IntIn q S F L) (h2 : IntIn q S F L') :
    latV S L (· = q.v) = latV S L' (· = q.v) := by
  have h : ∀ u : Fin S.rank → k,
      (fun i => q.sec (u i)) ∈ latV S L (· = q.v) ↔ (fun i => q.sec (u i)) ∈ latV S L' (· = q.v) := by
    intro u
    have e : F.β *ᵥ (F.γ *ᵥ u) = u := by rw [Matrix.mulVec_mulVec, F.βγ, Matrix.one_mulVec]
    have := (h1 (F.γ *ᵥ u)).symm.trans (h2 (F.γ *ᵥ u))
    rwa [e] at this
  exact AddSubgroup.ext fun _ => ⟨mem_of_sec_iff q hL hL' h, mem_of_sec_iff q hL' hL fun u => (h u).symm⟩

def besselNormalFrameAuxiliaryColumnIndex (ρ : ℕ) : Fin ρ ⊕ (Unit ⊕ Fin ρ) → Fin (2 * ρ + 1) :=
  Sum.elim (fun i => ⟨i.val, by omega⟩) (Sum.elim (fun _ => ⟨ρ, by omega⟩) fun i => ⟨2 * ρ - i.val, by omega⟩)

theorem besselNormalFrameAuxiliaryColumnIndex_bijective (ρ : ℕ) : Function.Bijective (besselNormalFrameAuxiliaryColumnIndex ρ) := by
  refine (Fintype.bijective_iff_injective_and_card _).2 ⟨?_, by simp; ring⟩
  rintro (a | a | a) (b | b | b) h <;> simp [besselNormalFrameAuxiliaryColumnIndex, Fin.ext_iff] at h ⊢ <;> first | exact h | omega

theorem sum_divisible_eq_sum_mul {M : Type} [AddCommMonoid M] (ρ : ℕ) (f : Fin (2 * ρ + 1) → M) :
    ∑ j, f j = ∑ i : Fin ρ, f ⟨i.val, by omega⟩ + f ⟨ρ, by omega⟩ + ∑ i : Fin ρ, f ⟨2 * ρ - i.val, by omega⟩ := by
  rw [← (Equiv.ofBijective _ (besselNormalFrameAuxiliaryColumnIndex_bijective ρ)).sum_comp, Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp [besselNormalFrameAuxiliaryColumnIndex, add_assoc]

theorem forall_fin_odd_iff_lower_middle_upperReversed (ρ : ℕ) (p : Fin (2 * ρ + 1) → Prop) :
    (∀ j, p j) ↔ (∀ i : Fin ρ, p ⟨i.val, by omega⟩) ∧ p ⟨ρ, by omega⟩ ∧ ∀ i : Fin ρ, p ⟨2 * ρ - i.val, by omega⟩ := by
  refine ⟨fun h => ⟨fun i => h _, h _, fun i => h _⟩, fun ⟨h1, h2, h3⟩ j => ?_⟩
  obtain ⟨x, rfl⟩ := (besselNormalFrameAuxiliaryColumnIndex_bijective ρ).2 j
  rcases x with (a | a | a)
  · exact h1 a
  · exact h2
  · exact h3 a

end GlobalTheory.MonoBes

namespace GlobalTheory.MonoBes

open GlobalTheory.FinPl GlobalTheory.SeeSaw.SplitLat

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem proj_sec (q : SplitPt D k) {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (w : Fin S₀.rank → k) (a b : Fin ρ → k) :
    (d.pX *ᵥ fun i => q.sec ((d.i₀.map (GlobalTheory.SliceModel.prH (ofSplit q)) *ᵥ w +
        d.e.map (GlobalTheory.SliceModel.prH (ofSplit q)) *ᵥ a + d.e'.map (GlobalTheory.SliceModel.prH (ofSplit q)) *ᵥ b) i)) =
        (fun i => q.sec (a i)) ∧
    (d.pY *ᵥ fun i => q.sec ((d.i₀.map (GlobalTheory.SliceModel.prH (ofSplit q)) *ᵥ w +
        d.e.map (GlobalTheory.SliceModel.prH (ofSplit q)) *ᵥ a + d.e'.map (GlobalTheory.SliceModel.prH (ofSplit q)) *ᵥ b) i)) =
        (fun i => q.sec (b i)) ∧
    (d.p0 *ᵥ fun i => q.sec ((d.i₀.map (GlobalTheory.SliceModel.prH (ofSplit q)) *ᵥ w +
        d.e.map (GlobalTheory.SliceModel.prH (ofSplit q)) *ᵥ a + d.e'.map (GlobalTheory.SliceModel.prH (ofSplit q)) *ᵥ b) i)) =
        (fun i => q.sec (w i)) := by
  set P := GlobalTheory.SliceModel.prH (ofSplit q) with hP
  have m : ∀ {a b c : ℕ} (X : Matrix (Fin a) (Fin b) D.host.E) (Y : Matrix (Fin b) (Fin c) D.host.E),
      X.map P * Y.map P = (X * Y).map P := fun X Y => Matrix.map_mul.symm
  have z : ∀ {a b : ℕ}, (0 : Matrix (Fin a) (Fin b) D.host.E).map P = 0 := Matrix.map_zero _ (map_zero P)
  have o : ∀ {a : ℕ}, (1 : Matrix (Fin a) (Fin a) D.host.E).map P = 1 := Matrix.map_one _ (map_zero P) (map_one P)
  refine ⟨?_, ?_, ?_⟩
  · change rat d.qX *ᵥ _ = _
    rw [GlobalTheory.CoreFrameLat.rat_mulVec_sec, ← hP, Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, m, m, m, GlobalTheory.SeeSaw.SplitLat.qX_i₀, GlobalTheory.SeeSaw.SplitLat.qX_e, GlobalTheory.SeeSaw.SplitLat.qX_e']
    simp only [z, o, Matrix.zero_mulVec, Matrix.one_mulVec, zero_add, add_zero]
  · change rat d.qY *ᵥ _ = _
    rw [GlobalTheory.CoreFrameLat.rat_mulVec_sec, ← hP, Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, m, m, m, GlobalTheory.SeeSaw.SplitLat.qY_i₀, GlobalTheory.SeeSaw.SplitLat.qY_e, GlobalTheory.SeeSaw.SplitLat.qY_e']
    simp only [z, o, Matrix.zero_mulVec, Matrix.one_mulVec, zero_add, add_zero]
  · change rat d.q0 *ᵥ _ = _
    rw [GlobalTheory.CoreFrameLat.rat_mulVec_sec, ← hP, Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, m, m, m, GlobalTheory.SeeSaw.SplitLat.wittDecomposition_coreProj_mul_core_eq_one, GlobalTheory.SeeSaw.SplitLat.wittDecomposition_coreProj_mul_e_eq_zero, GlobalTheory.SeeSaw.SplitLat.wittZeroProjection_mul_dualBasis_eq_zero]
    simp only [z, o, Matrix.zero_mulVec, Matrix.one_mulVec, zero_add, add_zero]

end GlobalTheory.MonoBes

namespace GlobalTheory.MonoBes

open GlobalTheory.FinPl GlobalTheory.SeeSaw.SplitLat

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem lineX_sec (q : SplitPt D k) {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (M : Lat S₀) (i : Fin ρ) (c : k) :
    colMul d.jX i (q.sec c) ∈ latV S (splitL d M fun _ => 1) (· = q.v) ↔ c ∈ 𝒪[k] := by
  rw [line_splitL, GlobalTheory.SeeSaw.idV_one_eq_intAt, sec_mem_intAt_iff]

theorem lineY_sec (q : SplitPt D k) {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (M : Lat S₀) (i : Fin ρ) (c : k) :
    colMul d.jY i (q.sec c) ∈ latV S (splitL d M fun _ => 1) (· = q.v) ↔ c ∈ 𝒪[k] := by
  rw [GlobalTheory.FinPl.MonoIdele.line_splitL_jY, GlobalTheory.SeeSaw.idV_one_eq_intAt, sec_mem_intAt_iff]

end GlobalTheory.MonoBes

namespace GlobalTheory.MonoBes

open GlobalTheory.FinPl GlobalTheory.SeeSaw.SplitLat

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

set_option maxHeartbeats 1000000 in

theorem intIn_splitL (q : SplitPt D k) {ρ : ℕ} (B : BesLev D ρ) {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} (s : k)
    (FA : GlobalTheory.LocMod.Frame k B.A.rank n) (F₀ : GlobalTheory.LocMod.Frame k B.V₀.rank (n ⊕ Unit))
    (FV : GlobalTheory.LocMod.Frame k B.V.rank (n ⊕ Fin c)) (M : Lat B.V₀)
    (hs : valuation k s = 1) (hxi : valuation k (ofSplit q).xi = 1) (hz : valuation k ((ofSplit q).hz B) = 1)
    (hC : (ofSplit q).IsCoreFrame B s FA F₀) (hB : (ofSplit q).IsBesFrame B s FA FV) (hM : IntIn q B.V₀ F₀ M) :
    IntIn q B.V FV (splitL B.d M fun _ => 1) := by
  obtain ⟨rfl, h1, h2, h3, h4⟩ := hB
  intro y
  have hPa : ∀ x, GlobalTheory.SliceModel.prH (ofSplit q) x = (ofSplit q).pr x := fun x => GlobalTheory.SliceModel.prH_apply _ x
  set P := GlobalTheory.SliceModel.prH (ofSplit q) with hP
  let ca : Fin ρ → k := fun i => s * (ofSplit q).xi ^ (ρ - i.val)
  let cb : Fin ρ → k := fun i => s * (-(ofSplit q).hz B / (ofSplit q).xi) * (-1 / (ofSplit q).xi) ^ (ρ - 1 - i.val)
  let a : Fin ρ → k := fun i => ca i * y (Sum.inr ⟨i.val, by omega⟩)
  let b : Fin ρ → k := fun i => cb i * y (Sum.inr ⟨2 * ρ - i.val, by omega⟩)
  let y₀ : n ⊕ Unit → k := Sum.elim (fun x => y (Sum.inl x)) fun _ => y (Sum.inr ⟨ρ, by omega⟩)
  have hca : ∀ i, valuation k (ca i) = 1 := fun i => by simp [ca, hs, hxi]
  have hcb : ∀ i, valuation k (cb i) = 1 := fun i => by simp [cb, hs, hxi, hz, map_div₀]
  have c1 : ∀ r x, FV.β r (Sum.inl x) = (B.d.i₀.map P * F₀.β) r (Sum.inl x) := by
    intro r x
    rw [h1]
    change ((B.d.i₀ * B.o.iA).map P * FA.β) r x = _
    rw [Matrix.map_mul, Matrix.mul_assoc, Matrix.mul_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [hC.1]
    rfl
  have c2 : ∀ r, FV.β r (Sum.inr ⟨ρ, by omega⟩) = (B.d.i₀.map P * F₀.β) r (Sum.inr ()) := by
    intro r
    rw [h3 _ rfl, Matrix.mul_apply, ← hPa, Matrix.mulVec, dotProduct, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [hC.2, map_mul, Matrix.map_apply]
    simp only [hPa]
    ring
  have c3 : ∀ r (i : Fin ρ), FV.β r (Sum.inr ⟨i.val, by omega⟩) = ca i * (B.d.e.map P) r i := by
    intro r i; rw [h2 i _ rfl]; simp [ca, hPa]
  have c4 : ∀ r (i : Fin ρ), FV.β r (Sum.inr ⟨2 * ρ - i.val, by omega⟩) = cb i * (B.d.e'.map P) r i := by
    intro r i; rw [h4 i _ (by simp; omega)]; simp [cb, hPa]
  have hdec : FV.β *ᵥ y = B.d.i₀.map P *ᵥ (F₀.β *ᵥ y₀) + B.d.e.map P *ᵥ a + B.d.e'.map P *ᵥ b := by
    rw [Matrix.mulVec_mulVec]
    funext r
    simp only [Pi.add_apply, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fintype.sum_unique]
    rw [sum_divisible_eq_sum_mul ρ]
    have ea : ∑ i : Fin ρ, B.d.e.map P r i * a i =
        ∑ i : Fin ρ, FV.β r (Sum.inr ⟨i.val, by omega⟩) * y (Sum.inr ⟨i.val, by omega⟩) :=
      Finset.sum_congr rfl fun i _ => by rw [c3]; simp only [a]; ring
    have eb : ∑ i : Fin ρ, B.d.e'.map P r i * b i =
        ∑ i : Fin ρ, FV.β r (Sum.inr ⟨2 * ρ - i.val, by omega⟩) * y (Sum.inr ⟨2 * ρ - i.val, by omega⟩) :=
      Finset.sum_congr rfl fun i _ => by rw [c4]; simp only [b]; ring
    rw [ea, eb]
    simp only [c1, c2, y₀, Sum.elim_inl, Sum.elim_inr]
    ring
  have hpr := proj_sec q B.d (F₀.β *ᵥ y₀) a b
  have hpX : B.d.pX *ᵥ (fun i => q.sec ((FV.β *ᵥ y) i)) = fun i => q.sec (a i) := by rw [hdec]; exact hpr.1
  have hpY : B.d.pY *ᵥ (fun i => q.sec ((FV.β *ᵥ y) i)) = fun i => q.sec (b i) := by rw [hdec]; exact hpr.2.1
  have hp0 : B.d.p0 *ᵥ (fun i => q.sec ((FV.β *ᵥ y) i)) = fun i => q.sec ((F₀.β *ᵥ y₀) i) := by rw [hdec]; exact hpr.2.2
  have lX : ∀ i, colMul B.d.jX i (q.sec (a i)) ∈ latV B.V (splitL B.d M fun _ => 1) (· = q.v) ↔
      y (Sum.inr ⟨i.val, by omega⟩) ∈ 𝒪[k] := fun i =>
    (lineX_sec q B.d M i (a i)).trans (mul_mem_iff (hca i) _)
  have lY : ∀ i, colMul B.d.jY i (q.sec (b i)) ∈ latV B.V (splitL B.d M fun _ => 1) (· = q.v) ↔
      y (Sum.inr ⟨2 * ρ - i.val, by omega⟩) ∈ 𝒪[k] := fun i =>
    (lineY_sec q B.d M i (b i)).trans (mul_mem_iff (hcb i) _)
  have hf := forall_fin_odd_iff_lower_middle_upperReversed ρ (fun j => y (Sum.inr j) ∈ 𝒪[k])
  rw [monoAt_splitL B.d M _ q.v, hpX, hpY, hp0, ← hM y₀]
  have e1 : (∀ i, colMul B.d.jX i ((fun i => q.sec (a i)) i) ∈ latV B.V (splitL B.d M fun _ => 1) (· = q.v)) ↔
      ∀ i : Fin ρ, y (Sum.inr ⟨i.val, by omega⟩) ∈ 𝒪[k] := forall_congr' lX
  have e2 : (∀ i, colMul B.d.jY i ((fun i => q.sec (b i)) i) ∈ latV B.V (splitL B.d M fun _ => 1) (· = q.v)) ↔
      ∀ i : Fin ρ, y (Sum.inr ⟨2 * ρ - i.val, by omega⟩) ∈ 𝒪[k] := forall_congr' lY
  have e3 : (∀ i, y₀ i ∈ 𝒪[k]) ↔ (∀ x, y (Sum.inl x) ∈ 𝒪[k]) ∧ y (Sum.inr ⟨ρ, by omega⟩) ∈ 𝒪[k] :=
    ⟨fun h => ⟨fun x => h (Sum.inl x), h (Sum.inr ())⟩, fun h m => by
      rcases m with x | u
      · exact h.1 x
      · exact h.2⟩
  rw [e1, e2, e3, Sum.forall, hf]
  constructor
  · rintro ⟨hl, ha, hr, hb⟩; exact ⟨ha, hb, hl, hr⟩
  · rintro ⟨ha, hb, hl, hr⟩; exact ⟨hl, ha, hr, hb⟩

end GlobalTheory.MonoBes

theorem GlobalTheory.MonoBes.besLat_monoAt : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ {a : XGeo D} (y : YRat a) {βT : GL (Fin D.sp.X'.rank) (Lev.EAf D)} {PP : Pl D.host.E} (l : LocX a βT PP) (FY : FYFam l) (sc : ℕ → l.k), IsNormalFr l y FY sc → (∀ j, j ≤ D.R.m → (a.x j).Is) → ∀ (N : ∀ j, GlobalTheory.FinPl.Lat (Yc D j)) (M : ∀ j ρ (h : j + 2 * ρ + 2 = D.R.m), GlobalTheory.FinPl.Lat (y.bes j ρ h).V₀), (∀ j, j < D.R.m → IsSelfDualC (Yc D j) (N j)) → (∀ j c (hc : j + c = l.s + 1), IntIn l.q (Yc D j) (FY j c hc) (N j)) → (∀ j ρ h, IsSelfDualC (y.bes j ρ h).V₀ (M j ρ h)) → (∀ j ρ h (hj : j ≤ l.s + 1) (F₀ : Frame l.k ((y.bes j ρ h).lev (a.x j).vol).V₀.rank (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Unit)), (ofSplit l.q).IsCoreFrame ((y.bes j ρ h).lev (a.x j).vol) (sc j) (l.FX j hj) F₀ → IntIn l.q _ F₀ (M j ρ h)) → ∀ j ρ (h : j + 2 * ρ + 2 = D.R.m), GlobalTheory.FinPl.MonoAt ((y.bes j ρ h).lev (a.x j).vol).d (N j) (M j ρ h) (PP.under (𝓞 D.host.F)) := by
  intro D ψ hψ a y βT PP l FY sc hN hx N M hsdN hIntN hsdM hIntM j ρ h
  have hs := l.hs
  have hj : j ≤ l.s + 1 := by omega
  have hc : j + (2 * ρ + 1) = l.s + 1 := by omega
  have hjm : j < D.R.m := by omega
  have hsc := hN.1 j
  have hxi := GlobalTheory.MonoBes.val_xi l.q l.unit
  have hhz := hN.2.2.1 j ρ h
  have hB := hN.2.2.2.1 j ρ h (2 * ρ + 1) hc
  obtain ⟨F₀, hF₀⟩ := GlobalTheory.LocMod.Witness.exists_core (ofSplit l.q) ((y.bes j ρ h).lev (a.x j).vol)
    (GlobalTheory.MonoBes.ne_zero_of_val hsc) (l.FX j hj)
  have hM₀ := hIntM j ρ h hj F₀ hF₀
  have hL' := GlobalTheory.SeeSaw.SplitLat.isSelfDualC_splitL ((y.bes j ρ h).lev (a.x j).vol).d (fun _ => one_ne_zero) (hsdM j ρ h)
  have hint := GlobalTheory.MonoBes.intIn_splitL l.q ((y.bes j ρ h).lev (a.x j).vol) (sc j) (l.FX j hj) F₀ (FY j (2 * ρ + 1) hc)
    (M j ρ h) hsc hxi hhz hF₀ hB hM₀
  have heq := GlobalTheory.MonoBes.latV_eq_of_frame l.q (hsdN j hjm) hL' (FY j _ hc) (hIntN j _ hc) hint
  rw [← l.under]
  exact GlobalTheory.LocCongr.monoAt_congr heq.symm rfl
    (GlobalTheory.SeeSaw.SplitLat.monoAt_splitL ((y.bes j ρ h).lev (a.x j).vol).d (M j ρ h) _ l.q.v)
