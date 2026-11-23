import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.SphComm2
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.PositionTest
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.HeckeFunctionIsHecke
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.KgFacts
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.LocAlg
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.EntEmpty
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.HintTranslate
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousPairProjection

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf TypeB TypeH finH)
open UpperTheory.V.Z.Tf.GlobalTraceComparison
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

namespace UpperTheory.Zero.ConvolutionTheory.EB

attribute [local instance] borelG borelF borelA borelH

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n a b : ℕ}

private theorem mem_Kg {S : Set (Pl E)} {L : ∀ w : Pl E, Subgroup (GLw n w)} {u : GL (Fin n) (Af E)} :
    u ∈ Kg S L ↔ ∀ w ∈ S, GeneralLinearGroup.map (pLoc E w) u ∈ L w ∧
      (IsSplitAt w → GeneralLinearGroup.map (pLoc E w) (thF E n u) ∈ L w) := by
  simp only [Kg, Subgroup.mem_iInf, Subgroup.mem_inf, Subgroup.mem_comap]
  refine forall₂_congr fun w _ => and_congr_right fun _ => ?_
  split_ifs with hs
  · simp [hs, Subgroup.mem_comap]
  · simp [hs]

private theorem finFn_left {S : Set (Pl E)} {Z : Finset (Pl E)} (L : Lv a b Z) {φ₁ φ₂ : ∀ w : Pl E, LF a b w}
    (h₁ : ∀ w, ∀ k ∈ (L.L₁ w).prod (L.L₂ w), ∀ y, φ₁ w (k * y) = φ₁ w y)
    (h₂ : ∀ w, ∀ k ∈ (L.L₁ w).prod (L.L₂ w), ∀ y, φ₂ w (k * y) = φ₂ w y)
    {u₁ : GL (Fin a) (Af E)} {u₂ : GL (Fin b) (Af E)} (hu₁ : u₁ ∈ Kg S L.L₁) (hu₂ : u₂ ∈ Kg S L.L₂) (h : Hf E a b) :
    finFn S φ₁ φ₂ ((u₁, u₂) * h) = finFn S φ₁ φ₂ h := by
  unfold finFn
  refine finprod_mem_congr rfl fun w hw => ?_
  obtain ⟨p₁, q₁⟩ := mem_Kg.1 hu₁ w hw
  obtain ⟨p₂, q₂⟩ := mem_Kg.1 hu₂ w hw
  have e₁ : atW w ((u₁, u₂) * h) =
      (GeneralLinearGroup.map (pLoc E w) u₁, GeneralLinearGroup.map (pLoc E w) u₂) * atW w h :=
    Prod.ext (map_mul _ _ _) (map_mul _ _ _)
  rw [e₁, h₁ w _ (Subgroup.mem_prod.2 ⟨p₁, p₂⟩)]
  split_ifs with hs
  · have e₂ : atW w (thP E a b ((u₁, u₂) * h)) =
        (GeneralLinearGroup.map (pLoc E w) (thF E a u₁), GeneralLinearGroup.map (pLoc E w) (thF E b u₂)) *
          atW w (thP E a b h) := by
      rw [map_mul]
      exact Prod.ext (map_mul _ _ _) (map_mul _ _ _)
    rw [e₂, h₂ w _ (Subgroup.mem_prod.2 ⟨q₁ hs, q₂ hs⟩)]
  · rfl

private theorem position_left {Z : Finset (Pl E)} (T : Finset (Pl E)) (L : Lv a b Z) {φ : ∀ w : Pl E, LF a b w}
    (hφ : L.Fix φ) (e : Pl E → Ex (Fin (a + 1) × Fin (b + 1))) (w : Pl E) :
    ∀ k ∈ (L.L₁ w).prod (L.L₂ w), ∀ y, intersection_update_fsHerm_neg_one Z T φ e w (k * y) = intersection_update_fsHerm_neg_one Z T φ e w y := by
  intro k hk y
  unfold intersection_update_fsHerm_neg_one
  by_cases h1 : w ∈ Z
  · simp only [if_pos h1]
    exact ((hφ w h1).2 k hk y).1
  · simp only [if_neg h1]
    have hk' : k ∈ K2 a b w := by
      have ho := L.off w h1
      rw [ho.1, ho.2] at hk
      exact hk
    by_cases h2 : w ∈ T
    · simp only [if_pos h2]
      exact ((UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.exHecke2 E a b w (e w)).2 k hk' y).1
    · simp only [if_neg h2]
      have hc : k * y ∈ (K2 a b w : Set (GLw a w × GLw b w)) ↔ y ∈ (K2 a b w : Set (GLw a w × GLw b w)) :=
        (K2 a b w).mul_mem_cancel_left hk'
      by_cases hy : y ∈ (K2 a b w : Set (GLw a w × GLw b w))
      · rw [Set.indicator_of_mem hy, Set.indicator_of_mem (hc.2 hy)]
        rfl
      · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem (fun h => hy (hc.1 h))]

private theorem relIndex_ne {Z : Finset (Pl E)} (L : Lv a b Z) (w : Pl E) :
    ((L.L₁ w).prod (L.L₂ w)).relIndex (K2 a b w) ≠ 0 := by
  have hc : IsCompact (K2 a b w : Set (GLw a w × GLw b w)) := by
    rw [Subgroup.coe_prod]
    exact (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a).2.prod (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w b).2
  have ho : IsOpen (((L.L₁ w).prod (L.L₂ w) : Subgroup _) : Set (GLw a w × GLw b w)) := by
    rw [Subgroup.coe_prod]
    exact (L.open₁ w).prod (L.open₂ w)
  haveI : CompactSpace (K2 a b w) := isCompact_iff_compactSpace.1 hc
  have ho' : IsOpen ((((L.L₁ w).prod (L.L₂ w)).subgroupOf (K2 a b w) : Subgroup (K2 a b w)) : Set (K2 a b w)) :=
    ho.preimage continuous_subtype_val
  haveI := Subgroup.quotient_finite_of_isOpen _ ho'
  exact Subgroup.index_ne_zero_of_finite

private theorem ln_one_ne {Z : Finset (Pl E)} (L : Lv a b Z) (w : Pl E) : L.ln w 1 ≠ 0 := by
  unfold Lv.ln
  rw [Set.indicator_of_mem (Subgroup.one_mem _)]
  exact Nat.cast_ne_zero.2 (relIndex_ne L w)

private theorem finFn_one_ne (S : Set (Pl E)) {Z : Finset (Pl E)} (L : Lv a b Z) : finFn S L.ln L.ln 1 ≠ 0 := by
  unfold finFn
  refine finprod_mem_induction (fun x : ℂ => x ≠ 0) one_ne_zero (fun _ _ => mul_ne_zero) fun w _ => ?_
  have e₁ : atW w (1 : Hf E a b) = 1 := Prod.ext (map_one _) (map_one _)
  rw [map_one, e₁]
  refine mul_ne_zero (ln_one_ne L w) ?_
  split_ifs
  · exact ln_one_ne L w
  · exact one_ne_zero

end

theorem idmAct : IdmAct := by
  intro E _ _ _ a b l₁ l₂ D A S Z L hS hZ
  have hfixln : L.Fix L.ln := fun w _ => (locAlg E a b Z L w).1
  have hlnl : ∀ w, ∀ k ∈ (L.L₁ w).prod (L.L₂ w), ∀ y, L.ln w (k * y) = L.ln w y :=
    fun w k hk y => (((locAlg E a b Z L w).1).2 k hk y).1
  have c1 : ∀ x y, ∀ u₁ ∈ Kg S L.L₁, ∀ u₂ ∈ Kg S L.L₂, ∀ h, A.idm S L x y ((u₁, u₂) * h) = A.idm S L x y h := by
    intro x y u₁ hu₁ u₂ hu₂ h
    show A.blk.vol⁻¹ * finFn S L.ln L.ln _ = A.blk.vol⁻¹ * finFn S L.ln L.ln _
    rw [finFn_left L hlnl hlnl hu₁ hu₂]
  refine ⟨c1, ?_, ?_⟩
  · intro T φ e₁ e₂ hφ x y u₁ hu₁ u₂ hu₂ h
    show A.blk.vol⁻¹ * finFn S _ _ _ = A.blk.vol⁻¹ * finFn S _ _ _
    rw [finFn_left L (fun w => position_left T L hφ e₁ w) (fun w => position_left T L hfixln e₂ w) hu₁ hu₂]
  · intro f hf
    haveI : BorelSpace (Hf E a b) := ⟨rfl⟩
    set K : Subgroup (Hf E a b) := (Kg S L.L₁).prod (Kg S L.L₂) with hKdef
    have hKo : IsOpen (K : Set (Hf E a b)) := by
      rw [hKdef, Subgroup.coe_prod]
      exact (kgFacts E a S Z L.L₁ hS hZ (fun w => ⟨L.open₁ w, L.le₁ w⟩) fun w hw => (L.off w hw).1).1.prod
        (kgFacts E b S Z L.L₂ hS hZ (fun w => ⟨L.open₂ w, L.le₂ w⟩) fun w hw => (L.off w hw).2).1
    have hKm : MeasurableSet (K : Set (Hf E a b)) := hKo.measurableSet
    set c : ℂ := A.idm S L () () 1 with hc
    have hvol : A.blk.vol ≠ 0 := (ffAlg E a b l₁ l₂ D A S hS).1
    have hc0 : c ≠ 0 := mul_ne_zero (inv_ne_zero hvol) (finFn_one_ne S L)
    have hmem : ∀ h ∈ K, A.idm S L () () h = c := by
      intro h hh
      have := c1 () () h.1 (Subgroup.mem_prod.1 hh).1 h.2 (Subgroup.mem_prod.1 hh).2 1
      rwa [mul_one] at this
    have hnot : ∀ h, h ∉ K → A.idm S L () () h = 0 := by
      intro h hh
      have hz : finFn S L.ln L.ln h = 0 := by
        by_contra hne
        have ht : IsTestP L.ln := (positionTest E a b S Z L hZ).2.1
        have key := fun w hw => GlobalTheory.CompanionTheory.FinTestTw.factors_ne_zero ht ht hne w hw
        have m : ∀ w ∈ S, atW w h ∈ (L.L₁ w).prod (L.L₂ w) ∧
            (IsSplitAt w → atW w (thP E a b h) ∈ (L.L₁ w).prod (L.L₂ w)) := fun w hw =>
          ⟨Set.mem_of_indicator_ne_zero (key w hw).1, fun hs => Set.mem_of_indicator_ne_zero ((key w hw).2 hs)⟩
        refine hh (Subgroup.mem_prod.2 ⟨mem_Kg.2 fun w hw => ⟨(Subgroup.mem_prod.1 (m w hw).1).1, fun hs => ?_⟩,
          mem_Kg.2 fun w hw => ⟨(Subgroup.mem_prod.1 (m w hw).1).2, fun hs => ?_⟩⟩)
        · exact (Subgroup.mem_prod.1 ((m w hw).2 hs)).1
        · exact (Subgroup.mem_prod.1 ((m w hw).2 hs)).2
      show A.blk.vol⁻¹ * finFn S L.ln L.ln h = 0
      rw [hz, mul_zero]
    have hone : (A.ν.real (K : Set (Hf E a b)) : ℂ) * c = 1 := by
      have h0 := congrFun (congrFun (congrFun (hkMul E a b l₁ l₂ D A S Z L hS hZ).2.1 ()) ()) 1
      have hi : (fun h => A.idm S L () () h * A.idm S L () () (h⁻¹ * 1)) =
          (K : Set (Hf E a b)).indicator fun _ => c * c := by
        funext h
        by_cases hh : h ∈ K
        · rw [Set.indicator_of_mem (show h ∈ (K : Set (Hf E a b)) from hh), hmem h hh,
            hmem _ (by simpa using K.inv_mem hh)]
        · rw [Set.indicator_of_notMem (show h ∉ (K : Set (Hf E a b)) from hh), hnot h hh, zero_mul]
      have h1 : ∫ h, A.idm S L () () h * A.idm S L () () (h⁻¹ * 1) ∂A.ν = c := by
        simpa [mulF] using h0
      rw [hi, integral_indicator_const _ hKm] at h1
      have h2 : c * ((A.ν.real (K : Set (Hf E a b)) : ℂ) * c) = c * 1 := by
        rw [mul_one]
        simpa [Complex.real_smul, mul_assoc, mul_comm, mul_left_comm] using h1
      exact mul_left_cancel₀ hc0 h2
    funext i x
    have hi : (fun h => A.idm S L i.2 () h * f (i.1, ()) (x * finH h)) =
        (K : Set (Hf E a b)).indicator fun _ => c * f i x := by
      funext h
      by_cases hh : h ∈ K
      · rw [Set.indicator_of_mem (show h ∈ (K : Set (Hf E a b)) from hh)]
        have := hf (i.1, ()) h.1 (Subgroup.mem_prod.1 hh).1 h.2 (Subgroup.mem_prod.1 hh).2 x
        show A.idm S L () () h * f (i.1, ()) (x * (finGL E a h.1, finGL E b h.2)) = _
        rw [this, hmem h hh]
      · rw [Set.indicator_of_notMem (show h ∉ (K : Set (Hf E a b)) from hh)]
        show A.idm S L () () h * _ = 0
        rw [hnot h hh, zero_mul]
    show ∑ z : Unit, ∫ h, A.idm S L i.2 z h * f (i.1, z) (x * finH h) ∂A.ν = f i x
    rw [Fintype.sum_unique]
    show ∫ h, A.idm S L i.2 () h * f (i.1, ()) (x * finH h) ∂A.ν = f i x
    rw [hi, integral_indicator_const _ hKm, Complex.real_smul, ← mul_assoc, hone, one_mul]

end UpperTheory.Zero.ConvolutionTheory.EB

end
