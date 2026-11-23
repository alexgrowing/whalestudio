import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameA
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameL
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.Imports

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

namespace PositivityTheory.Rg.BcB.F

attribute [local instance] borelG borelF borelA GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace FrameOk

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem pt_ok {a b : ℕ} {l₁ : InfinitePlace E → DomWeight a} {l₂ : InfinitePlace E → DomWeight b}
    {μ₁ : Measure (GA E a)} {μ₂ : Measure (GA E b)} {μa : Measure (G a)} {μb : Measure (G b)}
    (A : Arch E a b l₁ l₂ μ₁ μ₂ μa μb) {κ : Type} [Fintype κ] (wa wb : InfinitePlace E → List (Bool × ℕ))
    (ψ : Matrix κ κ (Hf E a b → ℂ)) (hψ : IsFinM ψ) : (A.pt wa wb ψ (PositivityTheory.Rg.BcB.F.sizeOf ψ)).Ok := by
  have hex : ∃ r, 0 ≤ r ∧ ∀ x y g, ψ x y g ≠ 0 → logSize (finGL E a g.1) ≤ r ∧ logSize (finGL E b g.2) ≤ r :=
    (BlockFiniteConvolution.rtAlg' E (A.blk κ) 1 1).2.2 ψ hψ
  have hs : PositivityTheory.Rg.BcB.F.sizeOf ψ = hex.choose := by
    unfold PositivityTheory.Rg.BcB.F.sizeOf
    rw [dif_pos hex]
  refine ⟨A.T_nonneg, ?_, fun v => ?_, fun v => ?_, hψ, ?_⟩
  · show 0 ≤ PositivityTheory.Rg.BcB.F.sizeOf ψ
    rw [hs]; exact hex.choose_spec.1
  · exact ⟨1, fun _ => 1, fun _ => wa v, fun _ => A.bump, fun _ => A.ka (wa v) v, fun _ => ⟨A.isBump, A.kera _ _⟩,
      fun y _ => by simp [Arch.pt], fun χ => by simp [Arch.pt, Arch.valW]⟩
  · exact ⟨1, fun _ => 1, fun _ => wb v, fun _ => A.bump, fun _ => A.kb (wb v) v, fun _ => ⟨A.isBump, A.kerb _ _⟩,
      fun y _ => by simp [Arch.pt], fun χ => by simp [Arch.pt, Arch.valW]⟩
  · intro x y g hg
    show logSize (finGL E a g.1) ≤ PositivityTheory.Rg.BcB.F.sizeOf ψ ∧ logSize (finGL E b g.2) ≤ PositivityTheory.Rg.BcB.F.sizeOf ψ
    rw [hs]; exact hex.choose_spec.2 x y g hg

theorem blk_complete {a b : ℕ} {l₁ : InfinitePlace E → DomWeight a} {l₂ : InfinitePlace E → DomWeight b}
    {μ₁ : Measure (GA E a)} {μ₂ : Measure (GA E b)} {μa : Measure (G a)} {μb : Measure (G b)}
    (A : Arch E a b l₁ l₂ μ₁ μ₂ μa μb) (κ : Type) [Fintype κ] : CompleteSpace (A.blk κ).Hb :=
  hsComplete _

attribute [local instance] blk_complete

theorem fm_eqv {κ : Pl E → Type} [∀ w, Fintype (κ w)] (S : Set (Pl E)) (P : Finset (Pl E)) (B : Block E)
    (e : B.κ ≃ ∀ w : P, κ w) {L L' : LM κ B.a B.b} (h : LM.Eqv P L L') : fm S P B e L = fm S P B e L' := by
  have hent : ∀ x y, L.ent P x y = L'.ent P x y := by
    intro x y
    funext w
    unfold LM.ent
    split_ifs with hw
    · rw [h.1 w hw]
    · rw [h.2.1 w hw]
  funext x y g
  simp only [fm, hent, h.2.2]

section Data

variable {n a : ℕ} {l₁ : InfinitePlace E → DomWeight a} {l₂ : InfinitePlace E → DomWeight (n - a)}
  {μ₁ : Measure (GA E a)} {μ₂ : Measure (GA E (n - a))} {μa : Measure (G a)} {μb : Measure (G (n - a))}
  (A : Arch E a (n - a) l₁ l₂ μ₁ μ₂ μa μb) (d : LocData E n) (Sec : Set (Pl E))

abbrev ψL (L : LM d.kap a (n - a)) : Matrix (∀ w : d.P, d.kap w) (∀ w : d.P, d.kap w) (Hf E a (n - a) → ℂ) :=
  fm Sec d.P (A.blk (∀ w : d.P, d.kap w)) (Equiv.refl _) L

abbrev ptW (wa wb : InfinitePlace E → List (Bool × ℕ)) (L : LM d.kap a (n - a)) : PT (A.blk (∀ w : d.P, d.kap w)) :=
  A.pt wa wb (ψL A d Sec L) (PositivityTheory.Rg.BcB.F.sizeOf (ψL A d Sec L))

variable {A d Sec}

theorem ψL_fin (hS : IsSection Sec) (hP : (↑d.P : Set (Pl E)) ⊆ Sec) {L : LM d.kap a (n - a)} (hL : L.Ok d.P) :
    IsFinM (ψL A d Sec L) :=
  (BlockFiniteConvolution.fmAlg' E d.kap Sec d.P (A.blk (∀ w : d.P, d.kap w)) (Equiv.refl _) hS hP L L hL hL).1

theorem ψL_mul (hS : IsSection Sec) (hP : (↑d.P : Set (Pl E)) ⊆ Sec) {L L' : LM d.kap a (n - a)} (hL : L.Ok d.P)
    (hL' : L'.Ok d.P) : mulF (A.blk (∀ w : d.P, d.kap w)).ν (ψL A d Sec L) (ψL A d Sec L') = ψL A d Sec (L.mul L') :=
  (BlockFiniteConvolution.fmAlg' E d.kap Sec d.P (A.blk (∀ w : d.P, d.kap w)) (Equiv.refl _) hS hP L L' hL hL').2.2.1

theorem ψL_adj (hS : IsSection Sec) (hP : (↑d.P : Set (Pl E)) ⊆ Sec) {L : LM d.kap a (n - a)} (hL : L.Ok d.P) :
    L.adj.Ok d.P ∧ adjF (ψL A d Sec L) = ψL A d Sec L.adj :=
  (BlockFiniteConvolution.fmAlg' E d.kap Sec d.P (A.blk (∀ w : d.P, d.kap w)) (Equiv.refl _) hS hP L L hL hL).2.2.2

theorem ψL_eqv {L L' : LM d.kap a (n - a)} (h : L.Eqv d.P L') : ψL A d Sec L = ψL A d Sec L' :=
  fm_eqv Sec d.P (A.blk (∀ w : d.P, d.kap w)) (Equiv.refl _) h

theorem ptW_ok (hS : IsSection Sec) (hP : (↑d.P : Set (Pl E)) ⊆ Sec) (wa wb : InfinitePlace E → List (Bool × ℕ))
    {L : LM d.kap a (n - a)} (hL : L.Ok d.P) : (ptW A d Sec wa wb L).Ok :=
  pt_ok A wa wb _ (ψL_fin hS hP hL)

theorem ptRt_ok (hS : IsSection Sec) (hP : (↑d.P : Set (Pl E)) ⊆ Sec) (wa wb : InfinitePlace E → List (Bool × ℕ))
    {L : LM d.kap a (n - a)} (hL : L.Ok d.P) (u₁ : GL (Fin a) E) (u₂ : GL (Fin (n - a)) E) :
    (A.pt wa wb (rt u₁ u₂ (ψL A d Sec L)) (PositivityTheory.Rg.BcB.F.sizeOf (rt u₁ u₂ (ψL A d Sec L)))).Ok := by
  obtain ⟨r, hr⟩ := (BlockFiniteConvolution.rtAlg' E (A.blk (∀ w : d.P, d.kap w)) u₁ u₂).2.1 _ (ptW_ok hS hP wa wb hL)
  exact pt_ok A wa wb _ hr.ψ

theorem comm_pt (hS : IsSection Sec) (hP : (↑d.P : Set (Pl E)) ⊆ Sec) {t t' : PT (A.blk (∀ w : d.P, d.kap w))}
    (ht : t.Ok) (ht' : t'.Ok) {L L' : LM d.kap a (n - a)} (hL : L.Ok d.P) (hL' : L'.Ok d.P)
    (e : t.ψ = ψL A d Sec L) (e' : t'.ψ = ψL A d Sec L') (hq : (L.mul L').Eqv d.P (L'.mul L)) : Commute t.op t'.op :=
  BlockFiniteConvolution.blkComm₀ E _ t t' ht ht' (by rw [e, e', ψL_mul hS hP hL hL', ψL_mul hS hP hL' hL, ψL_eqv hq])

theorem commStar_pt (hS : IsSection Sec) (hP : (↑d.P : Set (Pl E)) ⊆ Sec) {t t' : PT (A.blk (∀ w : d.P, d.kap w))}
    (ht : t.Ok) (ht' : t'.Ok) {L L' : LM d.kap a (n - a)} (hL : L.Ok d.P) (hL' : L'.Ok d.P)
    (e : t.ψ = ψL A d Sec L) (e' : t'.ψ = ψL A d Sec L') (hq : (L.mul L'.adj).Eqv d.P (L'.adj.mul L)) :
    Commute t.op (ContinuousLinearMap.adjoint t'.op) := by
  have hb := BlockFiniteConvolution.blkOp₀ E _ t' t' ht' ht'
  have hA := ψL_adj (A := A) hS hP hL'
  rw [← hb.2.2.2.2.2.1]
  have e'' : t'.adj.ψ = ψL A d Sec L'.adj := by
    show adjF t'.ψ = _
    rw [e']
    exact hA.2
  exact BlockFiniteConvolution.blkComm₀ E _ t t'.adj ht hb.2.2.2.2.1
    (by rw [e, e'', ψL_mul hS hP hL hA.1, ψL_mul hS hP hA.1 hL, ψL_eqv hq])

theorem gen_ok (hd : d.Ok) (ha : a ≤ n) {L : LM d.kap a (n - a)}
    (hL : d.IsGen a ha L) : L.Ok d.P :=
  (BlockFiniteConvolution.locOk₀ E n d hd a ha).2.2.2 L hL

theorem oks (hd : d.Ok) (hS : IsSection Sec) (hP : (↑d.P : Set (Pl E)) ⊆ Sec) (ha : a ≤ n)
    (wa wb : InfinitePlace E → List (Bool × ℕ)) :
    (∀ L, d.IsGen a ha L → (ptW A d Sec wa wb L).Ok) ∧ (ptW A d Sec wa wb (d.betaL a ha)).Ok ∧
      (ptW A d Sec wa wb (d.fixL a)).Ok ∧ ∀ (u₁ : GL (Fin a) E) (u₂ : GL (Fin (n - a)) E),
        (A.pt wa wb (rt u₁ u₂ (ψL A d Sec (d.eL a))) (PositivityTheory.Rg.BcB.F.sizeOf (rt u₁ u₂ (ψL A d Sec (d.eL a))))).Ok :=
  ⟨fun L hL => ptW_ok hS hP wa wb (gen_ok hd ha hL), ptW_ok hS hP wa wb (BlockFiniteConvolution.locOk₀ E n d hd a ha).2.1,
    ptW_ok hS hP wa wb (BlockFiniteConvolution.locOk₀ E n d hd a ha).2.2.1,
    fun u₁ u₂ => ptRt_ok hS hP wa wb (gen_ok hd ha (L := d.eL a) (Or.inl rfl)) u₁ u₂⟩

theorem comm_gen (hd : d.Ok) (hS : IsSection Sec) (hP : (↑d.P : Set (Pl E)) ⊆ Sec) (ha : a ≤ n)
    {L L' : LM d.kap a (n - a)} (hL : d.IsGen a ha L) (hL' : d.IsGen a ha L') (wa wb wa' wb' : InfinitePlace E → List (Bool × ℕ)) :
    Commute (ptW A d Sec wa wb L).op (ptW A d Sec wa' wb' L').op ∧
      Commute (ptW A d Sec wa wb L).op (ContinuousLinearMap.adjoint (ptW A d Sec wa' wb' L').op) := by
  have h₁ := gen_ok hd ha hL
  have h₂ := gen_ok hd ha hL'
  have hq := BlockFiniteConvolution.locComm₀ E n d hd a ha L L' hL hL'
  exact ⟨comm_pt hS hP (ptW_ok hS hP wa wb h₁) (ptW_ok hS hP wa' wb' h₂) h₁ h₂ rfl rfl hq.1,
    commStar_pt hS hP (ptW_ok hS hP wa wb h₁) (ptW_ok hS hP wa' wb' h₂) h₁ h₂ rfl rfl hq.2.1⟩

theorem comm_beta (hd : d.Ok) (hS : IsSection Sec) (hP : (↑d.P : Set (Pl E)) ⊆ Sec) (ha : a ≤ n)
    {L : LM d.kap a (n - a)} (hL : d.IsGen a ha L) (wa wb wa' wb' : InfinitePlace E → List (Bool × ℕ)) :
    Commute (ptW A d Sec wa wb (d.betaL a ha)).op (ptW A d Sec wa' wb' L).op ∧
      Commute (ptW A d Sec wa wb (d.betaL a ha)).op (ContinuousLinearMap.adjoint (ptW A d Sec wa' wb' L).op) := by
  have h₁ := (BlockFiniteConvolution.locOk₀ E n d hd a ha).2.1
  have h₂ := gen_ok hd ha hL
  have hq := BlockFiniteConvolution.locComm₀ E n d hd a ha L L hL hL
  exact ⟨comm_pt hS hP (ptW_ok hS hP wa wb h₁) (ptW_ok hS hP wa' wb' h₂) h₁ h₂ rfl rfl hq.2.2.1,
    commStar_pt hS hP (ptW_ok hS hP wa wb h₁) (ptW_ok hS hP wa' wb' h₂) h₁ h₂ rfl rfl hq.2.2.2⟩

end Data

end FrameOk

end PositivityTheory.Rg.BcB.F

end
