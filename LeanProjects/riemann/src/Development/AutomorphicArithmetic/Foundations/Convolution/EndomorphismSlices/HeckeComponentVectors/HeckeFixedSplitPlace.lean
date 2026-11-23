import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.SphComm2
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.KgFacts
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.PositionTest
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.LocAlg
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.HintTranslate
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.FmTools
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.LocalActionPowers.FactorActionAlgebra
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.LocalActionPowers.FaSlot

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf TypeB TypeH)
open UpperTheory.V.Z.Tf.GlobalTraceComparison
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

open UpperTheory.Zero.ConvolutionTheory.EB PositivityTheory.Rg.BcB.F.RS

attribute [local instance] borelG borelF borelA borelH

namespace UpperTheory.Zero.ConvolutionTheory.EB.HeckeActionLevel

open PositivityTheory.Rg.BcB.F.FA PositivityTheory.Rg.BcB.F.Tail

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n a b : ℕ}

private theorem mem_Kg {S : Set (Pl E)} {L : ∀ w : Pl E, Subgroup (GLw n w)} {u : GL (Fin n) (Af E)} :
    u ∈ Kg S L ↔ ∀ w ∈ S, GeneralLinearGroup.map (pLoc E w) u ∈ L w ∧
      (IsSplitAt w → GeneralLinearGroup.map (pLoc E w) (thF E n u) ∈ L w) := by
  simp only [Kg, Subgroup.mem_iInf, Subgroup.mem_inf, Subgroup.mem_comap]
  refine forall₂_congr fun w _ => and_congr_right fun _ => ?_
  split_ifs with hs
  · simp [hs, Subgroup.mem_comap]
  · simp [hs]

private theorem eH_mem {S : Set (Pl E)} {Z : Finset (Pl E)} (hS : IsSection S) (L : Lv a b Z) (i : Slot S)
    (m : GLw a i.pl × GLw b i.pl) (hm : m ∈ (L.L₁ i.pl).prod (L.L₂ i.pl)) :
    (Sl.eH a b i m).1 ∈ Kg S L.L₁ ∧ (Sl.eH a b i m).2 ∈ Kg S L.L₂ := by
  have key : ∀ j : Slot S, Sl.cpH a b j (Sl.eH a b i m) ∈ (L.L₁ j.pl).prod (L.L₂ j.pl) := by
    intro j
    by_cases hj : j = i
    · subst hj
      rw [Sl.cpH_eH_self hS]
      exact hm
    · rw [Sl.cpH_eH_ne hS i j m hj]
      exact one_mem _
  refine ⟨mem_Kg.2 fun w hw => ⟨?_, fun hs => ?_⟩, mem_Kg.2 fun w hw => ⟨?_, fun hs => ?_⟩⟩
  · exact (Subgroup.mem_prod.1 (key (.inl ⟨w, hw⟩))).1
  · exact (Subgroup.mem_prod.1 (key (.inr ⟨w, hw, hs⟩))).1
  · exact (Subgroup.mem_prod.1 (key (.inl ⟨w, hw⟩))).2
  · exact (Subgroup.mem_prod.1 (key (.inr ⟨w, hw, hs⟩))).2

private theorem fix_P {S : Set (Pl E)} {Z : Finset (Pl E)} (hS : IsSection S) (L : Lv a b Z) {G : H E a b → ℂ}
    (hG : ∀ u₁ ∈ Kg S L.L₁, ∀ u₂ ∈ Kg S L.L₂, ∀ x, G (x * (finGL E a u₁, finGL E b u₂)) = G x) {v : Pl E} (hv : v ∈ S) :
    G ∈ fixed (pairRt a b v) ((L.L₁ v).prod (L.L₂ v)) := by
  rw [GlobalTheory.TwTrLin.mem_fixed_iff]
  intro k hk
  funext z
  have h := eH_mem hS L (.inl ⟨v, hv⟩) k hk
  exact hG _ h.1 _ h.2 z

private theorem heckeFixed_split_place {S : Set (Pl E)} {Z : Finset (Pl E)} (hS : IsSection S) (L : Lv a b Z) {G : H E a b → ℂ}
    (hG : ∀ u₁ ∈ Kg S L.L₁, ∀ u₂ ∈ Kg S L.L₂, ∀ x, G (x * (finGL E a u₁, finGL E b u₂)) = G x) {v : Pl E} (hv : v ∈ S)
    (hs : IsSplitAt v) : G ∈ fixed (pairRtT a b v) ((L.L₁ v).prod (L.L₂ v)) := by
  rw [GlobalTheory.TwTrLin.mem_fixed_iff]
  intro k hk
  funext z
  have h := eH_mem hS L (.inr ⟨v, hv, hs⟩) k hk
  have e := hG _ h.1 _ h.2 z
  change G (z * ((embT a v).prodMap (embT b v) k)) = G z
  rw [← e]
  congr 2
  exact Prod.ext (GlobalTheory.ThetaPull.thetaA_finGL _) (GlobalTheory.ThetaPull.thetaA_finGL _)

private theorem position_one {Z : Finset (Pl E)} (T : Finset (Pl E)) (L : Lv a b Z) :
    intersection_update_fsHerm_neg_one Z T L.ln (fun _ => .one) = L.ln := by
  funext v
  have hI : v ∉ Z → L.ln v = (K2 a b v : Set _).indicator 1 := (locAlg E a b Z L v).2.2.1
  unfold intersection_update_fsHerm_neg_one
  by_cases h1 : v ∈ Z
  · rw [if_pos h1]
  · rw [if_neg h1, hI h1]
    split_ifs <;> rfl

private theorem position_ne {Z : Finset (Pl E)} (L : Lv a b Z) (e : Pl E → Ex (Fin (a + 1) × Fin (b + 1))) {v w : Pl E}
    (h : v ≠ w) : intersection_update_fsHerm_neg_one Z {w} L.ln e v = L.ln v := by
  have hI : v ∉ Z → L.ln v = (K2 a b v : Set _).indicator 1 := (locAlg E a b Z L v).2.2.1
  unfold intersection_update_fsHerm_neg_one
  by_cases h1 : v ∈ Z
  · rw [if_pos h1]
  · rw [if_neg h1, if_neg (by simpa using h), hI h1]

private theorem position_self {Z : Finset (Pl E)} (L : Lv a b Z) (e : Pl E → Ex (Fin (a + 1) × Fin (b + 1))) {w : Pl E}
    (h : w ∉ Z) : intersection_update_fsHerm_neg_one Z {w} L.ln e w = fn2 a b w (e w) := by
  unfold intersection_update_fsHerm_neg_one
  rw [if_neg h, if_pos (by simp)]

private theorem ln_open {Z : Finset (Pl E)} (L : Lv a b Z) (v : Pl E) :
    IsOpen (((L.L₁ v).prod (L.L₂ v) : Subgroup _) : Set (GLw a v × GLw b v)) := by
  rw [Subgroup.coe_prod]
  exact (L.open₁ v).prod (L.open₂ v)

private theorem ln_le {Z : Finset (Pl E)} (L : Lv a b Z) (v : Pl E) : (L.L₁ v).prod (L.L₂ v) ≤ K2 a b v :=
  Subgroup.prod_mono (L.le₁ v) (L.le₂ v)

private theorem actP_ln {S : Set (Pl E)} {Z : Finset (Pl E)} (hS : IsSection S) (L : Lv a b Z) {G : H E a b → ℂ}
    (hL : HasLev G)
    (hG : ∀ u₁ ∈ Kg S L.L₁, ∀ u₂ ∈ Kg S L.L₂, ∀ x, G (x * (finGL E a u₁, finGL E b u₂)) = G x) {v : Pl E} (hv : v ∈ S) :
    actP v (L.ln v) G = G :=
  (actIdem_holds E a b v ((L.L₁ v).prod (L.L₂ v)) G (ln_open L v) (ln_le L v) hL).1.2 (fix_P hS L hG hv)

private theorem actT_ln {S : Set (Pl E)} {Z : Finset (Pl E)} (hS : IsSection S) (L : Lv a b Z) {G : H E a b → ℂ}
    (hL : HasLev G)
    (hG : ∀ u₁ ∈ Kg S L.L₁, ∀ u₂ ∈ Kg S L.L₂, ∀ x, G (x * (finGL E a u₁, finGL E b u₂)) = G x) {v : Pl E} (hv : v ∈ S)
    (hs : IsSplitAt v) : actT v (L.ln v) G = G :=
  (actIdem_holds E a b v ((L.L₁ v).prod (L.L₂ v)) G (ln_open L v) (ln_le L v) hL).2.2 (heckeFixed_split_place hS L hG hv hs)

private theorem finAct' : FinAct :=
  finAct_of PositivityTheory.Rg.BcB.F.intHint PositivityTheory.Rg.BcB.F.slots PositivityTheory.Rg.BcB.F.BlockFiniteConvolution.finConv'

private theorem conv_one {a b : ℕ} {l₁ : InfinitePlace E → DomWeight a} {l₂ : InfinitePlace E → DomWeight b} {D : Dom E a b}
    (A : Ar l₁ l₂ D) {S : Set (Pl E)} (hS : IsSection S) {φ₁ φ₂ : ∀ w : Pl E, LF a b w} (h₁ : IsTestP φ₁) (h₂ : IsTestP φ₂)
    (f : A.blk.I → H E a b → ℂ) (i : A.blk.I) (hL : HasLev (f i)) (i₀ : Slot S)
    (hq : ∀ j, j ≠ i₀ → actS φ₁ φ₂ j (f i) = f i) :
    convF A.ν (A.ff S φ₁ φ₂) f i = actS φ₁ φ₂ i₀ (f i) := by
  have hvol : A.blk.vol ≠ 0 := (PositivityTheory.Rg.BcB.F.BlockFiniteConvolution.finConv' E A.blk S hS).1
  funext x
  have h := finAct' E A.blk S hS φ₁ φ₂ h₁ h₂ (f i) hL [i₀] (List.nodup_singleton _)
    (fun j hj => hq j (by simpa using hj)) x
  show ∑ z : Unit, ∫ h, A.ff S φ₁ φ₂ i.2 z h * f (i.1, z) (x * PositivityTheory.Rg.BcB.SpectralAccumulation.finH h) ∂A.ν = _
  rw [Fintype.sum_unique]
  show ∫ h, A.blk.vol⁻¹ * finFn S φ₁ φ₂ h * f i (x * PositivityTheory.Rg.BcB.SpectralAccumulation.finH h) ∂A.ν = _
  simp only [mul_assoc]
  rw [MeasureTheory.integral_const_mul]
  have h' : ∫ h, finFn S φ₁ φ₂ h * f i (x * PositivityTheory.Rg.BcB.SpectralAccumulation.finH h) ∂A.ν = A.blk.vol * actS φ₁ φ₂ i₀ (f i) x := by
    simpa using h
  rw [h', ← mul_assoc, inv_mul_cancel₀ hvol, one_mul]

end UpperTheory.Zero.ConvolutionTheory.EB.HeckeActionLevel

theorem UpperTheory.Zero.ConvolutionTheory.EB.hkAct :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (l₁ : InfinitePlace E → DomWeight a) (l₂ : InfinitePlace E → DomWeight b)
    (D : Dom E a b) (A : Ar l₁ l₂ D) (S : Set (Pl E)) (Z : Finset (Pl E)) (L : Lv a b Z), IsSection S → SplitIn S Z →
    ∀ (f : A.blk.I → H E a b → ℂ), LevelF (Kg S L.L₁) (Kg S L.L₂) f → ∀ w ∈ S, w ∉ Z → ∀ (p : Fin (a + 1) × Fin (b + 1)) (i : A.blk.I),
    (f i ∈ fixed (pairRt a b w) (K2 a b w) ∧ convF A.ν (A.hk1 S L w p false) f i = heckeVec (pairRt a b w) (K2 a b w) (fun y : GLw a w × GLw b w => Tj ℂ a (Ov E w) (UpperTheory.V.Z.Tf.GlobalTraceComparison.unif w) p.1 y.1 * Tj ℂ b (Ov E w) (UpperTheory.V.Z.Tf.GlobalTraceComparison.unif w) p.2 y.2) (f i)) ∧
    (IsSplitAt w → f i ∈ fixed (pairRtT a b w) (K2 a b w) ∧ convF A.ν (A.hk1 S L w p true) f i = heckeVec (pairRtT a b w) (K2 a b w) (fun y : GLw a w × GLw b w => Tj ℂ a (Ov E w) (UpperTheory.V.Z.Tf.GlobalTraceComparison.unif w) p.1 y.1 * Tj ℂ b (Ov E w) (UpperTheory.V.Z.Tf.GlobalTraceComparison.unif w) p.2 y.2) (f i)) := by
  intro E _ _ _ a b l₁ l₂ D A S Z L hS hZ f hf w hw hwZ p i
  have hG := hf i
  have hLev : PositivityTheory.Rg.BcB.F.Tail.HasLev (f i) := by
    refine ⟨(Kg S L.L₁).prod (Kg S L.L₂), ?_, fun u hu x => hf i u.1 (Subgroup.mem_prod.1 hu).1 u.2 (Subgroup.mem_prod.1 hu).2 x⟩
    rw [Subgroup.coe_prod]
    exact (UpperTheory.Zero.ConvolutionTheory.EB.kgFacts E a S Z L.L₁ hS hZ (fun w => ⟨L.open₁ w, L.le₁ w⟩) fun w hw => (L.off w hw).1).1.prod
      (UpperTheory.Zero.ConvolutionTheory.EB.kgFacts E b S Z L.L₂ hS hZ (fun w => ⟨L.open₂ w, L.le₂ w⟩) fun w hw => (L.off w hw).2).1
  have hK : (L.L₁ w).prod (L.L₂ w) = K2 a b w := by
    rw [(L.off w hwZ).1, (L.off w hwZ).2]
  have hst := UpperTheory.Zero.ConvolutionTheory.EB.positionTest E a b S Z L hZ
  have hT : ∀ e, IsTestP (intersection_update_fsHerm_neg_one Z {w} L.ln e) := fun e => ((hst.2.2 L.ln hst.1).2 {w} e)
  have hH := UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.exHecke2 E a b w (.gen p)
  have hc := hH.1
  have hr : ∀ k ∈ K2 a b w, ∀ g, fn2 a b w (.gen p) (g * k) = fn2 a b w (.gen p) g := fun k hk g => (hH.2 k hk g).2
  have hA := PositivityTheory.Rg.BcB.F.Tail.actHecke_holds E a b w _ (f i) hc hr
  refine ⟨⟨?_, ?_⟩, fun hs => ⟨?_, ?_⟩⟩
  · rw [← hK]
    exact UpperTheory.Zero.ConvolutionTheory.EB.HeckeActionLevel.fix_P hS L hG hw
  · have p1 : f i ∈ fixed (pairRt a b w) (K2 a b w) := by
      rw [← hK]
      exact UpperTheory.Zero.ConvolutionTheory.EB.HeckeActionLevel.fix_P hS L hG hw
    have e0 : A.hk1 S L w p false = A.ff S (intersection_update_fsHerm_neg_one Z {w} L.ln fun _ => .gen p) (intersection_update_fsHerm_neg_one Z {w} L.ln fun _ => .one) := by
      simp [Ar.hk1, Ar.hk, Ar.fx]
    rw [e0, UpperTheory.Zero.ConvolutionTheory.EB.HeckeActionLevel.conv_one A hS (hT _) (hT _) f i hLev (.inl ⟨w, hw⟩) ?_]
    · show PositivityTheory.Rg.BcB.F.Tail.actP w (intersection_update_fsHerm_neg_one Z {w} L.ln (fun _ => .gen p) w) (f i) = _
      rw [UpperTheory.Zero.ConvolutionTheory.EB.HeckeActionLevel.position_self L _ hwZ]
      exact hA.1 p1
    · intro j hj
      rcases j with ⟨v, hv⟩ | ⟨v, hv, hs⟩
      · have hvw : v ≠ w := fun e => hj (by subst e; rfl)
        show PositivityTheory.Rg.BcB.F.Tail.actP v (intersection_update_fsHerm_neg_one Z {w} L.ln (fun _ => .gen p) v) (f i) = f i
        rw [UpperTheory.Zero.ConvolutionTheory.EB.HeckeActionLevel.position_ne L _ hvw]
        exact UpperTheory.Zero.ConvolutionTheory.EB.HeckeActionLevel.actP_ln hS L hLev hG hv
      · show PositivityTheory.Rg.BcB.F.Tail.actT v (intersection_update_fsHerm_neg_one Z {w} L.ln (fun _ => .one) v) (f i) = f i
        rw [UpperTheory.Zero.ConvolutionTheory.EB.HeckeActionLevel.position_one]
        exact UpperTheory.Zero.ConvolutionTheory.EB.HeckeActionLevel.actT_ln hS L hLev hG hv hs
  · rw [← hK]
    exact UpperTheory.Zero.ConvolutionTheory.EB.HeckeActionLevel.heckeFixed_split_place hS L hG hw hs
  · have p1 : f i ∈ fixed (pairRtT a b w) (K2 a b w) := by
      rw [← hK]
      exact UpperTheory.Zero.ConvolutionTheory.EB.HeckeActionLevel.heckeFixed_split_place hS L hG hw hs
    have e0 : A.hk1 S L w p true = A.ff S (intersection_update_fsHerm_neg_one Z {w} L.ln fun _ => .one) (intersection_update_fsHerm_neg_one Z {w} L.ln fun _ => .gen p) := by
      simp [Ar.hk1, Ar.hk, Ar.fx]
    rw [e0, UpperTheory.Zero.ConvolutionTheory.EB.HeckeActionLevel.conv_one A hS (hT _) (hT _) f i hLev (.inr ⟨w, hw, hs⟩) ?_]
    · show PositivityTheory.Rg.BcB.F.Tail.actT w (intersection_update_fsHerm_neg_one Z {w} L.ln (fun _ => .gen p) w) (f i) = _
      rw [UpperTheory.Zero.ConvolutionTheory.EB.HeckeActionLevel.position_self L _ hwZ]
      exact hA.2 p1
    · intro j hj
      rcases j with ⟨v, hv⟩ | ⟨v, hv, hs'⟩
      · show PositivityTheory.Rg.BcB.F.Tail.actP v (intersection_update_fsHerm_neg_one Z {w} L.ln (fun _ => .one) v) (f i) = f i
        rw [UpperTheory.Zero.ConvolutionTheory.EB.HeckeActionLevel.position_one]
        exact UpperTheory.Zero.ConvolutionTheory.EB.HeckeActionLevel.actP_ln hS L hLev hG hv
      · have hvw : v ≠ w := fun e => hj (by subst e; rfl)
        show PositivityTheory.Rg.BcB.F.Tail.actT v (intersection_update_fsHerm_neg_one Z {w} L.ln (fun _ => .gen p) v) (f i) = f i
        rw [UpperTheory.Zero.ConvolutionTheory.EB.HeckeActionLevel.position_ne L _ hvw]
        exact UpperTheory.Zero.ConvolutionTheory.EB.HeckeActionLevel.actT_ln hS L hLev hG hv hs'
