import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.CandOut
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.LocalActionPowers.FactorActionAlgebra
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.BlkGrowth
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.Imports

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Tr pairSpace)
open PositivityTheory.Rg.BcB.One PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.RS
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

namespace PositivityTheory.Rg.BcB.F

attribute [local instance] borelG borelF borelA GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PCandSa

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem locM_comp {a b : ℕ} {k k' : Type} [Fintype k] [Fintype k'] (w : Pl E) (φ : k ≃ k')
    (N : k' → k' → LF a b w) (Y : k' → H E a b → ℂ) (m : ℕ) :
    (locM w (fun x y => N (φ x) (φ y)))^[m] (Y ∘ φ) = ((locM w N)^[m] Y) ∘ φ := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    funext x
    simp only [locM, Function.comp]
    exact Equiv.sum_comp φ (fun y' => actP w (N (φ x) y') (((locM w N)^[m] Y) y'))

theorem isLev_lev {n a : ℕ} (d : LocData E n) (hd : d.Ok) (ha : a ≤ n) : Tail.IsLev (d.lev a) := by
  refine ⟨fun w => ?_, ?_⟩
  · obtain ⟨K₁, K₂, h₁, h₂, e⟩ := LocOk.lev_lv d hd ha w
    rw [e]
    exact LocOk.prod_open_le h₁ h₂
  · refine Filter.eventually_cofinite.2 ((d.T ∪ d.S₀ ∪ d.Bad).finite_toSet.subset fun w hw => ?_)
    by_contra h
    exact hw (LocOk.lev_out d (LocOk.out3 d h).1 (LocOk.out3 d h).2)

theorem isLev_lev₂ {n a : ℕ} (d : LocData E n) (hd : d.Ok) (ha : a ≤ n) : Tail.IsLev (d.lev₂ a) := by
  refine ⟨fun w => ?_, ?_⟩
  · obtain ⟨K₁, K₂, h₁, h₂, e⟩ := LocOk.lev₂_lv d hd ha w
    rw [e]
    exact LocOk.prod_open_le h₁ h₂
  · refine Filter.eventually_cofinite.2 ((d.T ∪ d.S₀ ∪ d.Bad).finite_toSet.subset fun w hw => ?_)
    by_contra h
    exact hw (LocOk.lev₂_out d (LocOk.out3 d h).2)

theorem betaL_hecke {n a : ℕ} (d : LocData E n) (hd : d.Ok) (ha : a ≤ n) :
    ∀ w ∈ d.P, ∀ x y, IsHecke (d.lev a w) ((d.betaL a ha).m w x y) := by
  intro w hw x y
  show IsHecke _ (if w ∈ d.T then d.diag (fun x => d.qT a w x.1.1) x y else d.mac a ha w (d.e w) x.1.2 y.1.2)
  split_ifs with hT
  · rw [LocOk.level_eq_iwahori_pair_at_bad_places d hT]
    exact LocOk.diagH d _ (fun z => LocOk.qT_H d w z.1.1) x y
  · have hS : w ∈ d.S₀ := by
      simp only [LocData.P, Finset.mem_union] at hw
      tauto
    rw [LocOk.lev_S d hT (Finset.mem_union_left _ hS)]
    exact LocOk.mac_H d PositivityTheory.Rg.BcN.F2.LocOpPf.locOp3 hd ha hS (LocOk.kap_X d hT hS x) (LocOk.kap_X d hT hS y)

def kapX {n : ℕ} (d : LocData E n) {w : Pl E} (hT : w ∉ d.T) (hS : w ∈ d.S₀) : d.kap w ≃ (d.X w) :=
  Equiv.ofBijective (fun x => ⟨x.1.2, LocOk.kap_X d hT hS x⟩) (by
    have e : d.idx w = {∅} ×ˢ d.X w := by unfold LocData.idx; rw [if_neg hT, if_pos hS]
    constructor
    · rintro ⟨⟨s, x⟩, hx⟩ ⟨⟨s', x'⟩, hx'⟩ h
      have h1 := (Finset.mem_product.1 (e ▸ hx)).1
      have h2 := (Finset.mem_product.1 (e ▸ hx')).1
      simp only [Finset.mem_singleton] at h1 h2
      simp only [Subtype.mk.injEq] at h
      subst h1 h2 h
      rfl
    · rintro ⟨x, hx⟩
      exact ⟨⟨(∅, x), by rw [e]; simp [hx]⟩, rfl⟩)

end PCandSa

open PCandSa in
theorem candS_of (h : Tail.ReadS) : CandS := by
  intro hR E _ _ _ hE n hn π hπ S T F₀ F hF i s₁ s₂ Pa Pb D A G hc hG hl hne w hwS hsplit
  have ha : F₀.C.a i ≤ n := F₀.C.le i
  obtain ⟨hS0, hBad, hμ, hϖ, hK', hX, hL, hfix, hKB⟩ := F.same
  have hw0 : w ∈ F₀.d₀.S₀ := F₀.S_le w hwS hsplit
  have hwd : w ∈ F.d.S₀ := hS0 ▸ hw0
  have hwT : w ∉ F.d.T := fun h => Finset.disjoint_left.1 F.ok.disj.1 h hwd
  have hwP : w ∈ F.d.P := Finset.mem_union_right _ hwd
  have hwSec : w ∈ F₀.Sec := (F₀.S₀ w hw0).1
  have hPS : (↑F.d.P : Set (Pl E)) ⊆ F₀.Sec := by
    intro u hu
    rcases Finset.mem_union.1 hu with h1 | h1
    · exact (F.T_in u h1).1
    · exact (F₀.S₀ u (hS0 ▸ h1)).1
  have hpow := FA.fmPow_of intHint slots BlockFiniteConvolution.finConv' BlockFiniteConvolution.fmAlg' E F.d.kap F₀.Sec F.d.P (F.B i) (Equiv.refl _)
    F₀.hSec hPS (F.d.lev _) (F.d.lev₂ _) (F.d.betaL _ ha) A G F.m (isLev_lev F.d F.ok ha) (isLev_lev₂ F.d F.ok ha)
    ((BlockFiniteConvolution.locOk₀ E n F.d F.ok _ ha).2.1) (fun _ => rfl) (fun _ => rfl)
    (fun u hu x y k hk g => ((betaL_hecke F.d F.ok ha u hu x y).2 k hk g)) hl hne ⟨w, hwP⟩
  obtain ⟨α, x₀, hx₀⟩ := hpow
  have hGy : ∀ j, G j ∈ pairSpace s₁.space s₂.space ∧ G j ∈ fixed (pairRt _ _ w) (F.d.lev (F₀.C.a i) w) :=
    fun j => ⟨hG j, ((hl j).2 w hwSec).1⟩
  set G' : F.d.kap w → H E (F₀.C.a i) (n - F₀.C.a i) → ℂ :=
    fun y => G (α, (Equiv.refl _).symm (Function.update x₀ ⟨w, hwP⟩ y)) with hG'def
  have hG'p : ∀ y, G' y ∈ pairSpace s₁.space s₂.space ∧ G' y ∈ fixed (pairRt _ _ w) (F.d.lev (F₀.C.a i) w) :=
    fun y => hGy _
  change (locM w ((F.d.betaL _ ha).m w))^[F.m] G' ≠ 0 at hx₀
  clear_value G'
  set φ := kapX F.d hwT hwd with hφ
  let N : (F.d.X w) → (F.d.X w) → LF (F₀.C.a i) (n - F₀.C.a i) w :=
    fun x y => phiMu (Nat.add_sub_of_le ha) w (F₀.μ.loc w) (F.d.e w) x y
  have hm : (F.d.betaL _ ha).m w = fun x y => (F.d.sgn (F₀.C.a i) w * ((F.d.X w).card : ℂ))⁻¹ • N (φ x) (φ y) := by
    funext x y g
    simp only [LocData.betaL, if_neg hwT, LocData.mac, Pi.smul_apply, smul_eq_mul, N, hμ, F₀.μloc]
    rfl
  rw [hm] at hx₀
  have hopen : IsOpen (F.d.lev (F₀.C.a i) w : Set (GLw (F₀.C.a i) w × GLw (n - F₀.C.a i) w)) :=
    ((isLev_lev F.d F.ok ha).1 w).1
  have h1 := (Tail.locPow_holds E _ _ w (F.d.kap w) (F.d.lev _ w) G' F.m hopen (fun y => (hG'p y).2)).1 _
    (fun x y => N (φ x) (φ y)) hx₀
  have h2 : (matS (Nat.add_sub_of_le ha) w (F₀.μ.loc w) (F.d.e w) (F.d.X w))^[F.m] (G' ∘ φ.symm) ≠ 0 := by
    intro h0
    apply h1
    have e1 := locM_comp w φ N (G' ∘ φ.symm) F.m
    rw [show (G' ∘ φ.symm) ∘ φ = G' from by funext y; simp] at e1
    rw [e1]
    change ((matS (Nat.add_sub_of_le ha) w (F₀.μ.loc w) (F.d.e w) (F.d.X w))^[F.m] (G' ∘ φ.symm)) ∘ φ = 0
    rw [h0]
    rfl
  obtain ⟨P, hPc, hkill⟩ := F.choiceS w hw0
  have hOk := F.ok.K' w hwd
  rw [hK'] at hOk
  obtain ⟨hO, hle, hN, hXK, hU, hHk⟩ := hOk
  exact ⟨P, h E n (F₀.C.a i) (n - F₀.C.a i) (Nat.add_sub_of_le ha) F₀.μ s₁ s₂ Pa Pb D hc.ctx w (F₀.d₀.K' w) (F.d.X w)
    (F.d.lev _ w) (F.d.e w) P F.m (G' ∘ φ.symm) hO hle hN hXK hU hopen hHk (hkill i s₁ s₂ Pa Pb D hc)
    ((F.choiceM i s₁ s₂ Pa Pb D hc).1 w hw0) (fun x => hG'p _) h2, hPc⟩

end PositivityTheory.Rg.BcB.F

end
