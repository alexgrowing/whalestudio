import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RationalRootsDef
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjugateEmbApply
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDiagSpacesOfCh
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpreadLamOfLe
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLayerParametersOkStatement

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top NumberField IsDedekindDomain

namespace GlobalTheory.Mem.Top.V4.TwoPass

theorem large_of_sup {C : FC} {K K' : TransportedAlt} {CH : ℝ} (h : C.Large (K.sup K') CH) : C.Large K CH ∧ C.Large K' CH :=
  ⟨⟨fun c hc => (le_max_left _ _).trans (h.1 c hc), trivial, fun c hc => (le_max_left _ _).trans (h.2.2.1 c hc),
      fun c hc => (le_max_left _ _).trans (h.2.2.2 c hc)⟩,
    ⟨fun c hc => (le_max_right _ _).trans (h.1 c hc), trivial, fun c hc => (le_max_right _ _).trans (h.2.2.1 c hc),
      fun c hc => (le_max_right _ _).trans (h.2.2.2 c hc)⟩⟩

theorem ev_and {p q : Ctx → Prop} (hp : Ev p) (hq : Ev q) : Ev fun K => p K ∧ q K := by
  obtain ⟨a, ha, hp⟩ := hp
  obtain ⟨b, hb, hq⟩ := hq
  refine ⟨min a b, lt_min ha hb, fun e C8 he hle h52 h8 => ?_⟩
  obtain ⟨K, hK⟩ := hp e C8 he (hle.trans (min_le_left _ _)) h52 h8
  obtain ⟨K', hK'⟩ := hq e C8 he (hle.trans (min_le_right _ _)) h52 h8
  refine ⟨K.sup K', fun C hC hC8 hL => ?_⟩
  obtain ⟨a1, ha1⟩ := hK C hC hC8 (large_of_sup hL).1
  obtain ⟨b1, hb1⟩ := hK' C hC hC8 (large_of_sup hL).2
  refine ⟨max a1 b1, fun cD hcD => ?_⟩
  obtain ⟨a2, ha2⟩ := ha1 cD (le_trans (le_max_left _ _) hcD)
  obtain ⟨b2, hb2⟩ := hb1 cD (le_trans (le_max_right _ _) hcD)
  refine ⟨max a2 b2, fun ch hch => ?_⟩
  obtain ⟨a3, ha3⟩ := ha2 ch (le_trans (le_max_left _ _) hch)
  obtain ⟨b3, hb3⟩ := hb2 ch (le_trans (le_max_right _ _) hch)
  exact ⟨max a3 b3, fun X h1 h2 h3 h4 hx =>
    ⟨ha3 X h1 h2 h3 h4 (le_trans (le_max_left _ _) hx), hb3 X h1 h2 h3 h4 (le_trans (le_max_right _ _) hx)⟩⟩

theorem ev_mono {p q : Ctx → Prop} (h : ∀ K, p K → q K) (hp : Ev p) : Ev q := by
  obtain ⟨a, ha, hp⟩ := hp
  refine ⟨a, ha, fun e C8 he hle h52 h8 => ?_⟩
  obtain ⟨K, hK⟩ := hp e C8 he hle h52 h8
  refine ⟨K, fun C hC hC8 hL => ?_⟩
  obtain ⟨a1, ha1⟩ := hK C hC hC8 hL
  refine ⟨a1, fun cD hcD => ?_⟩
  obtain ⟨a2, ha2⟩ := ha1 cD hcD
  refine ⟨a2, fun ch hch => ?_⟩
  obtain ⟨a3, ha3⟩ := ha2 ch hch
  exact ⟨a3, fun X h1 h2 h3 h4 hx => h X (ha3 X h1 h2 h3 h4 hx)⟩

theorem congr_frame {α : Type*} (g : ∀ P : Pre, Fr P → α) {P P' : Pre} {f : Fr P} {f' : Fr P'} (h : P = P') (hf : HEq f f') :
    g P f = g P' f' := by
  subst h
  rw [eq_of_heq hf]

theorem untw_set (B : Base) (pl : Finset ℕ) (f : Fr B.toPre) :
    (TwDat.untw B pl).set f = {1, f.del, f.del'} := by
  refine Set.union_eq_left.2 ?_
  rintro _ ⟨w, rfl⟩
  change (if _ then f.del' else f.del) * 1 ∈ _
  rw [mul_one]
  split_ifs
  · exact .inr (.inr rfl)
  · exact .inr (.inl rfl)

theorem exists_base_over (K : Ctx) : ∃ B : Base, K.Over B.toPre := by
  obtain ⟨sp, hT, hY, hA, hV, hz, ⟨hd, -⟩, -⟩ := GlobalTheory.Mem.exists_diagSpaces_ofCh K.P K.Lv
  obtain ⟨B, hB, -⟩ := GlobalTheory.Mem.BaseExt.exists_base (Pre.ofCh K.P K.Lv sp hT hY hA hV hz) ∅ ∅ ∅ (by simp) (by simp) (by simp)
  exact ⟨B, sp, hT, hY, hA, hV, hz, hB, hd⟩

end GlobalTheory.Mem.Top.V4.TwoPass

namespace GlobalTheory.Mem.Top.V4

open TwoPass

theorem recAt_of_two_passes : StandardLattice.SiegelMassRatioCM → (∀ D : D7, Formalism.L2.Theta.VolTieG D → StandardLattice.VolumeEqMass₂ D) →
    ∀ (KP : ∀ B : Base, Fr B.toPre → Prop) (Q Q' : V4.Slot), V4.KsCond KP → V4.ExTrue KP Q → V4.Export Q → V4.Retwist Q Q' →
      RecAt (fun D Y => V4.FromCore Q' D Y ∧ DQ.TupUsedAt D ∧ DQ.TwAllAt D Y.nch Y.xd ∧ DQ.MtStableAt D) := by
  intro h2b h2v KP Q Q' hK hE hX hR
  refine ev_mono ?_ (ev_and (ev_and (ev_and (ev_preX_frame h2b) hK.ex) (ev_and hE hX)) (ev_and hR GlobalTheory.T.exists_layer_sizeData))
  rintro K ⟨⟨⟨hfr, hks⟩, ⟨S₁, P₁, A, S₂, a₁, a₂, hlg⟩, hex⟩, hre, hlay⟩
  obtain ⟨B₀, hB₀⟩ := exists_base_over K
  obtain ⟨f₀⟩ := (hfr _ hB₀).2
  obtain ⟨B, f, hB, hf, hKP, hH₁, hH₂⟩ := hks B₀ f₀ (S₁ B₀.toPre f₀)
    (fun F F₀ => S₂ B₀.toPre f₀ F F₀ {1, f₀.del, f₀.del'}) hB₀ (a₁ _ _) (fun F F₀ => a₂ _ _ F F₀ _)
  have hO : K.Over B.toPre := hB ▸ hB₀
  rw [← congr_frame S₁ hB hf] at hH₁
  have e₂ := congr_frame (fun P g => S₂ P g B.KsC B.fixedCoefficientFieldInComplex {1, g.del, g.del'}) hB hf
  rw [← e₂] at hH₂
  obtain ⟨C, W, V, S, N, G, c, hQ⟩ := hlg B f (TwDat.untw B (P₁ B.toPre f B.KsC B.fixedCoefficientFieldInComplex)) hO
    ⟨hH₁, by rw [untw_set]; exact hH₂⟩ (Finset.Subset.refl _) (fun w v hv => absurd hv (Finset.notMem_empty _)) hKP
  obtain ⟨B', f', T', hEnl, hf', hpl, hAv, hS, hfin⟩ := hre ⟨B, C, W, V, S, N, G⟩ f _ c hQ (hex ⟨B, C, W, V, S, N, G⟩ f _ c hQ)
    (A B.toPre f B.KsC B.fixedCoefficientFieldInComplex) (fun P g Ξ => S₂ P g B.KsC B.fixedCoefficientFieldInComplex Ξ) (fun P g Ξ => a₂ P g _ _ Ξ)
  have hP : B'.toPre = B.toPre := hEnl.1
  have hk : B'.KsC = B.KsC := hEnl.KsC_eq
  have hl : B'.fixedCoefficientFieldInComplex = B.fixedCoefficientFieldInComplex := hEnl.fixedCoefficientField_eq
  have hO' : K.Over B'.toPre := hP ▸ hO
  obtain ⟨C', W', V', S', N', G', c', hQ'⟩ := hlg B' f' T' hO'
    ⟨by rw [hk, hl, congr_frame S₁ hP hf']; exact hH₁, by rw [hk, hl]; exact hS⟩
    (by rw [hk, hl, congr_frame P₁ hP hf', hpl]; exact Finset.Subset.refl _)
    (by rw [hk, hl, congr_frame A hP hf']; exact hAv) (hK.enl B B' f f' hEnl hf' hKP)
  obtain ⟨hTw, hQ''⟩ := hfin C' W' V' S' N' G' c' hQ'
  obtain ⟨Y, hY, h1, h2, h3, h4⟩ := hlay ⟨B', C', W', V', S', N', G'⟩ f' T' c' (h2v _ c'.real.vol)
  have hTw' : DQ.TwAllAt (Stages.toD7 ⟨B', C', W', V', S', N', G'⟩) Y.nch Y.xd := by
    have e1 : Y.nch = c'.O.nch := by rw [← hY]; rfl
    have e2 : Y.xd = c'.O.xd := by rw [← hY]; rfl
    rw [e1, e2]
    exact hTw
  exact ⟨_, Y, h1, h2, h3, hTw'.twAt, ⟨K, _, f', T', c', hQ'', by rw [hY]⟩, h4, hTw', c'.mtStable⟩

end GlobalTheory.Mem.Top.V4
