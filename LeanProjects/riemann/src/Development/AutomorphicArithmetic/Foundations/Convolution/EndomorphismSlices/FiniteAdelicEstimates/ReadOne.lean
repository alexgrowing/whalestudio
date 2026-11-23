import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.SphComm2
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.PackStep
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.Imports
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.SatRead
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.HeckeFunctionOneMul
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.Places

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf TypeB TypeH)
open UpperTheory.V.Z.Tf.GlobalTraceComparison
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

attribute [local instance] borelG borelF borelA borelH

theorem UpperTheory.Zero.ConvolutionTheory.EB.readOne :
    UpperTheory.Zero.ConvolutionTheory.EB.ReadOne := by
  intro E _ _ _ a b l₁ l₂
  obtain ⟨W₁, W₂, hW₁, hW₂, hP⟩ := UpperTheory.Zero.ConvolutionTheory.EB.packStep E a b l₁ l₂
  refine ⟨W₁, W₂, hW₁, hW₂, ?_⟩
  intro D A S Z L hS hZ T e₁ e₂ s f hT hTZ hs hE
  obtain ⟨χa, χb, hχa, hχb, hL, hSm, hs₁, hs₂, hv⟩ := hP D A S Z L hS hZ T e₁ e₂ s f hs hE
  obtain ⟨-, hPl, -, hSec⟩ := UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.places E

  obtain ⟨i, x, hx⟩ : ∃ i x, f i x ≠ 0 := by
    by_contra h
    push_neg at h
    exact hE.ne (funext fun i => funext fun x => h i x)
  obtain ⟨φ₁, hφ₁⟩ := hSm.1 i x.2
  obtain ⟨φ₂, hφ₂⟩ := hSm.2 i x.1
  have hm₁ : φ₁ ∈ slices₁ f := ⟨i, x.2, hφ₁⟩
  have hm₂ : φ₂ ∈ slices₂ f := ⟨i, x.1, hφ₂⟩
  have hn₁ : φ₁ ≠ 0 := by
    rintro rfl
    exact hx (by simpa using (congrFun hφ₁ x.1).symm)
  have hn₂ : φ₂ ≠ 0 := by
    rintro rfl
    exact hx (by simpa using (congrFun hφ₂ x.2).symm)

  let t₁ : Pl E → Fin (a + 1) × Fin (b + 1) → ℂ := fun w p =>
    if h : w ∈ S ∧ w ∉ Z then s (.inr (.inr (.inl (⟨w, h⟩, p, false)))) / s (.inl ()) else 0
  let t₂ : Pl E → Fin (a + 1) × Fin (b + 1) → ℂ := fun w p =>
    if h : w ∈ S ∧ w ∉ Z then s (.inr (.inr (.inl (⟨w, h⟩, p, true)))) / s (.inl ()) else 0
  have ht₁ : ∀ w, w ∈ S → w ∉ Z → ∀ p, convF A.ν (A.hk1 S L w p false) f = t₁ w p • f := by
    intro w hw hwZ p
    have h : t₁ w p = s (.inr (.inr (.inl (⟨w, hw, hwZ⟩, p, false)))) / s (.inl ()) := dif_pos ⟨hw, hwZ⟩
    rw [h]
    exact hv (.inl (⟨w, hw, hwZ⟩, p, false))
  have ht₂ : ∀ w, w ∈ S → w ∉ Z → ∀ p, convF A.ν (A.hk1 S L w p true) f = t₂ w p • f := by
    intro w hw hwZ p
    have h : t₂ w p = s (.inr (.inr (.inl (⟨w, hw, hwZ⟩, p, true)))) / s (.inl ()) := dif_pos ⟨hw, hwZ⟩
    rw [h]
    exact hv (.inl (⟨w, hw, hwZ⟩, p, true))

  have key : ∀ w : Pl E, ∃ B₁ B₂ : Multiset ℂˣ, Off Z w → B₁.card = a ∧ B₂.card = b ∧
      IsSatVecGL w (UpperTheory.V.Cj.S.fL a w) φ₁ B₁ ∧ IsSatVecGL w (UpperTheory.V.Cj.S.fL b w) φ₂ B₂ ∧
      (w ∈ S → ∀ p, t₁ w p = satEig (qV E w) a B₁ p.1 * satEig (qV E w) b B₂ p.2) ∧
      (w ∉ S → ∀ p, t₂ (cPl w) p = satEig (qV E (cPl w)) a (inv B₁) p.1 * satEig (qV E (cPl w)) b (inv B₂) p.2) := by
    intro w
    by_cases hO : Off Z w
    · by_cases hw : w ∈ S
      · obtain ⟨B₁, B₂, c₁, c₂, he, h₁, h₂⟩ := UpperTheory.Zero.ConvolutionTheory.EB.satRead₁ E a b l₁ l₂ D A S Z L hS hZ f hE.ne hE.cont hL hSm
          w hw hO.1 (t₁ w) (ht₁ w hw hO.1)
        exact ⟨B₁, B₂, fun _ => ⟨c₁, c₂, h₁ φ₁ hm₁ hn₁, h₂ φ₂ hm₂ hn₂, fun _ => he, fun h => absurd hw h⟩⟩
      · have hu : cPl w ∈ S := ((hSec S hS w).1).resolve_left hw
        have hsp : IsSplitAt (cPl w) := by
          rw [(hPl (cPl w)).2, (hPl w).1]
          intro h
          exact hw (h ▸ hu)
        obtain ⟨u, rfl⟩ : ∃ u, w = cPl u := ⟨cPl w, ((hPl w).1).symm⟩
        rw [(hPl u).1] at hu hsp
        obtain ⟨B₁, B₂, c₁, c₂, he, h₁, h₂⟩ := UpperTheory.Zero.ConvolutionTheory.EB.satRead₂ E a b l₁ l₂ D A S Z L hS hZ f hE.ne hE.cont hL hSm
          u hu (by simpa [(hPl u).1] using hO.2) hsp (t₂ u) (ht₂ u hu (by simpa [(hPl u).1] using hO.2))
        refine ⟨B₁, B₂, fun _ => ⟨?_, ?_, h₁ φ₁ hm₁ hn₁, h₂ φ₂ hm₂ hn₂, fun h => absurd h hw, fun _ => ?_⟩⟩
        · exact c₁
        · exact c₂
        · simpa only [(hPl u).1] using he
    · exact ⟨0, 0, fun h => absurd h hO⟩
  choose B₁ B₂ hB using key
  refine ⟨χa, χb, φ₁, φ₂, B₁, B₂, hχa, hχb, hm₁, hn₁, (hs₁ φ₁ hm₁).1, (hs₁ φ₁ hm₁).2.1, (hs₁ φ₁ hm₁).2.2, hn₂,
    (hs₂ φ₂ hm₂).1, (hs₂ φ₂ hm₂).2.1, (hs₂ φ₂ hm₂).2.2, ?_, ?_⟩
  · intro w hO
    obtain ⟨h1, h2, h3, h4, -, -⟩ := hB w hO
    exact ⟨h1, h2, h3, h4⟩
  ·
    have hTS : ∀ w ∈ T, w ∈ S ∧ w ∉ Z := fun w hw => ⟨hT.1 w hw, Finset.disjoint_left.mp hTZ hw⟩
    have hTEv : TEv S T e₂ := ⟨hT.1, fun w hw hn x => by rw [hT.2 w hw hn]; rfl⟩
    have h1 := UpperTheory.Zero.ConvolutionTheory.EB.hkVal E a b l₁ l₂ D A S Z L hS hZ f t₁ t₂ T e₁ e₂ hTEv hTZ hE.cont hL
      (fun w hw p => ⟨ht₁ w (hTS w hw).1 (hTS w hw).2 p, fun _ => ht₂ w (hTS w hw).1 (hTS w hw).2 p⟩)
    have h2 : convF A.ν (A.hk S L T e₁ e₂) f = (s (.inr (.inr (.inr ()))) / s (.inl ())) • f := hv (.inr ())
    have h3 : s (.inr (.inr (.inr ()))) / s (.inl ()) = ∏ w ∈ T, (e₁ w).ev (t₁ w) * (e₂ w).ev (t₂ w) := by
      have h4 := congrFun (congrFun (h2.symm.trans h1) i) x
      simp only [Pi.smul_apply, smul_eq_mul] at h4
      exact mul_right_cancel₀ hx h4
    rw [h3]
    refine Finset.prod_congr rfl fun w hw => ?_
    obtain ⟨hwS, hwZ⟩ := hTS w hw
    have hOff : Off Z w := by
      refine ⟨hwZ, fun hc => hwZ ?_⟩
      have hcs := hZ _ hc
      have : cPl w = w := (hSec S hS w).2 hwS hcs.1
      exact this ▸ hc
    have hA : (e₁ w).ev (t₁ w) = ev2 a b w (e₁ w) (B₁ w) (B₂ w) := by
      have := (hB w hOff).2.2.2.2.1 hwS
      unfold ev2
      congr 1
      exact funext this
    have hC : (e₂ w).ev (t₂ w) = ev2 a b w (e₂ w) (inv (B₁ (cPl w))) (inv (B₂ (cPl w))) := by
      by_cases hsp : IsSplitAt w
      · have hne : cPl w ≠ w := ((hPl w).2).1 hsp
        have hnS : cPl w ∉ S := fun h => hne ((hSec S hS w).2 hwS h)
        have hOc : Off Z (cPl w) := by
          refine ⟨fun hc => hnS (hZ _ hc).1, ?_⟩
          rw [(hPl w).1]
          exact hwZ
        have := (hB (cPl w) hOc).2.2.2.2.2 hnS
        simp only [(hPl w).1] at this
        unfold ev2
        congr 1
        exact funext this
      · rw [hT.2 w hw hsp]
        rfl
    rw [hA, hC]
