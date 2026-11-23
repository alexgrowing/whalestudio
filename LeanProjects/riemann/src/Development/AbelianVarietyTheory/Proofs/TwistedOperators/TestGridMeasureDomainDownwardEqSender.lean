import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AuxiliaryPrimeLtFirstTypePrimeOfSizes
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SizesOfSizeRows
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PathConvergenceDownChain
import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.GridMeasDown

open GlobalTheory.GridJoin GlobalTheory.Grid

variable {D : D7}

theorem exch {V₁ V₂ : HSp D} (hV : SameSp V₂ V₁) (e : GA D V₁ = GA D V₂)
    {μ₁ : Measure (GA D V₁)} {F₁ : Set (GA D V₁)} {μ₂ : Measure (GA D V₂)} {F₂ : Set (GA D V₂)}
    (hμ : HEq μ₁ μ₂) (hH₂ : μ₂.IsHaarMeasure) (h1 : IsFundamentalDomain (GQ V₁) F₁ μ₁)
    (h2 : IsFundamentalDomain (GQ V₂) F₂ μ₂) (H : GA D V₂ → ℂ) (hH : ∀ γ ∈ GQ V₂, ∀ g, H (γ * g) = H g) :
    (IntegrableOn (fun g => H (cast e g)) F₁ μ₁ ↔ IntegrableOn H F₂ μ₂) ∧
      ∫ g in F₁, H (cast e g) ∂μ₁ = ∫ g in F₂, H g ∂μ₂ := by
  obtain ⟨L, hl1, hl2, rfl⟩ := hV
  obtain rfl : μ₁ = μ₂ := eq_of_heq hμ
  exact GlobalTheory.FlipStart.Col.fund_exch (V := V₂) (μ := μ₁) h1 h2 H hH

theorem measFD_heq {V V₀ : HSp D} (hV : SameSp V₀ V) {K : Subgroup (GL (Fin V.rank) (Lev.EAf D))}
    {K₀ : Subgroup (GL (Fin V₀.rank) (Lev.EAf D))} (hK : HEq K K₀) {μ : Measure (GA D V)} {μ₀ : Measure (GA D V₀)}
    {F : Set (GA D V)} {F₀ : Set (GA D V₀)} (h : Lev.IsMeasFD V K μ F) (h₀ : Lev.IsMeasFD V₀ K₀ μ₀ F₀) : HEq μ μ₀ := by
  obtain ⟨L, hl1, hl2, rfl⟩ := hV
  obtain rfl := eq_of_heq hK
  exact heq_of_eq (GlobalTheory.FunObjModel.isMeasLevW_unique (V := V₀) (fun _ _ e => e.1) h.1 h₀.1)

theorem measDef_heq {V V₀ : HSp D} (hV : SameSp V₀ V) {K : Subgroup (GL (Fin V.rank) (Lev.EAf D))}
    {K₀ : Subgroup (GL (Fin V₀.rank) (Lev.EAf D))} (hK : HEq K K₀) {μ : Measure (GA D V)} {μ₀ : Measure (GA D V₀)}
    {F : Set (GA D V)} {F₀ : Set (GA D V₀)} (h : IsMeasDef V K μ F) (h₀ : IsMeasDef V₀ K₀ μ₀ F₀) : HEq μ μ₀ := by
  obtain ⟨L, hl1, hl2, rfl⟩ := hV
  obtain rfl := eq_of_heq hK
  have h1 : Lev.IsMeasLevDef V₀ K μ := h.1
  exact heq_of_eq (GlobalTheory.FunObjModel.isMeasLevW_unique (V := V₀) (fun _ _ e => e.1) h1 h₀.1)

theorem lev_heq {V V' : HSp D} (hsp : SameSp V V') {β : GL (Fin V'.rank) (Lev.EAf D)}
    {Λ' : Submodule (𝓞 D.host.E) (Fin V'.rank → D.host.E)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hl : HEq Λ' Λ) (hf : Formalism.L2.DIV.IsFrame β Λ') :
    HEq (UA D.sp.cm V'.gram ⊓ St β) (GlobalTheory.ChiGrid.congLev D.sp.cm V.gram Λ ⊤) := by
  obtain ⟨L, hl1, hl2, rfl⟩ := hsp
  obtain rfl := eq_of_heq hl
  have hs := Formalism.L2.DIV.stabilizer_eq_stabilizer_lattice _ _ _ _ _ hf
  have h2 := GlobalTheory.ChiGrid.congLev_top (hc := D.sp.cm) (J := V.gram) (Λ := Λ')
  apply heq_of_eq
  rw [h2, hs]
  rfl

theorem cast_heq {S S' : GlobalTheory.Grid.Node D} (h : S = S') (m : S.MeasDat) :
    HEq (Node.MeasDat.cast h m).ν m.ν ∧ HEq (Node.MeasDat.cast h m).fd m.fd := by
  subst h; exact ⟨HEq.rfl, HEq.rfl⟩

theorem cast_fd {S S' : GlobalTheory.Grid.Node D} (h : S = S') (m : S.MeasDat) (hf : IsFundamentalDomain (GQ S.V) m.fd m.ν) :
    IsFundamentalDomain (GQ S'.V) (Node.MeasDat.cast h m).fd (Node.MeasDat.cast h m).ν := by
  subst h; exact hf

theorem meas_down : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : Consts} {large₂ : SizeData₂ D}
    {F : Face D A}, GlobalTheory.RowClaim.HidaSetting large₂ R F → sc.cGap = 1 →
    ∀ {G' : GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ G : GlobalTheory.Grid.GridPre R, G.Is → GlobalTheory.GridJoin.Match G W →
    ∀ (M : Vol G') (t : T), M.Is t → ∀ (i j : ℕ), i ≤ D.R.m → j < D.R.m →
    ∀ (e : GA D (G.V i (j + 1)).V = GA D (G'.V (.grid i (j + 1)))) (H : GA D (G'.V (.grid i (j + 1))) → ℂ),
    (∀ γ ∈ GQ (G'.V (.grid i (j + 1))), ∀ g, H (γ * g) = H g) →
    (IntegrableOn (fun g => H (cast e g)) (G.meas t i (j + 1)).fd (G.meas t i (j + 1)).ν ↔
      IntegrableOn H (M.fd (.grid i (j + 1))) (M.ν (.grid i (j + 1)))) ∧
    ∫ g in (G.meas t i (j + 1)).fd, H (cast e g) ∂(G.meas t i (j + 1)).ν =
      ∫ g in M.fd (.grid i (j + 1)), H g ∂(M.ν (.grid i (j + 1))) := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc large₂ F hS hc G' W hW G hG hJ M t hM i j hi hj e H hH
  have hAt := hM.vtx (.grid i (j + 1)) ⟨hi, by omega⟩
  obtain ⟨hHaar, hfd⟩ := hAt.haar_fund
  have hsp : SameSp (G'.V (.grid i (j + 1))) (G.V i (j + 1)).V := (hJ.1.vert i (j + 1) hi (by omega)).sp
  suffices key : HEq (G.meas t i (j + 1)).ν (M.ν (.grid i (j + 1))) ∧
      IsFundamentalDomain (GQ (G.V i (j + 1)).V) (G.meas t i (j + 1)).fd (G.meas t i (j + 1)).ν from
    exch hsp e key.1 hHaar key.2 hfd H hH
  unfold Vol.IsAt at hAt
  rcases i with _ | i
  · have hmod := hS.core.models
    by_cases h : j + 1 < D.R.m
    · have hT : G'.V (.grid 0 (j + 1)) = Yc D (j + 1) := congrArg LSp.sp (colY_lt R.toLevCh h)
      have hK : HEq (levJ G' t (.grid 0 (j + 1)))
          (lev D.sp.cm (Yc D (j + 1)).gram (R.βY (j + 1)) (R.datYt t (j + 1) R.triv)) := levCol_lt R.toLevCh t h
      have e0 : G.meas t 0 (j + 1) = Node.MeasDat.cast (nodeY_eq_chainVertexAtRowZero_of_lt R h) ⟨R.νY t (j + 1), R.fdY t (j + 1)⟩ := by
        show meas0 R t j = _
        rw [meas0, dif_pos h]
      rw [e0]
      rcases Nat.lt_or_ge (j + 1 + 1) D.R.m with h' | h'
      · have hc := hmod.νY t (j + 1) h'
        rw [if_neg (show ¬ (GlobalTheory.ChiGrid.Node.grid 0 (j + 1)).neg D.R.m = 0 by simp only [GlobalTheory.ChiGrid.Node.neg]; omega)] at hAt
        exact ⟨(cast_heq _ _).1.trans (GlobalTheory.FlipStart.Col.measFD_heq hT hK hAt hc).symm, cast_fd _ _ hc.2⟩
      · have e1 : j + 1 = D.R.m - 1 := by omega
        have hc := hmod.νY' t
        rw [← e1] at hc
        rw [if_pos (show (GlobalTheory.ChiGrid.Node.grid 0 (j + 1)).neg D.R.m = 0 by simp only [GlobalTheory.ChiGrid.Node.neg]; omega)] at hAt
        exact ⟨(cast_heq _ _).1.trans (GlobalTheory.FlipStart.Col.measDef_heq hT hK hAt hc).symm, cast_fd _ _ hc.2⟩
    · have hj' : j + 1 = D.R.m := by omega
      have hT : G'.V (.grid 0 (j + 1)) = D.sp.X' := by
        show (columnBlock R.toLevCh (j + 1)).sp = _
        rw [hj', colY_m]
      have hK : HEq (levJ G' t (.grid 0 (j + 1))) (lev D.sp.cm D.sp.X'.gram R.βX (R.datXt t)) := levCol_top R.toLevCh t h
      have e0 : G.meas t 0 (j + 1) = Node.MeasDat.cast (nodeX_eq_chainVertexAtRowZero_of_ge R h) ⟨R.νX t, R.fdX t⟩ := by
        show meas0 R t j = _
        rw [meas0, dif_neg h]
      rw [e0]
      have hc := hmod.νX t
      rw [if_pos (show (GlobalTheory.ChiGrid.Node.grid 0 (j + 1)).neg D.R.m = 0 by simp only [GlobalTheory.ChiGrid.Node.neg]; omega)] at hAt
      exact ⟨(cast_heq _ _).1.trans (GlobalTheory.FlipStart.Col.measDef_heq hT hK hAt hc).symm, cast_fd _ _ hc.2⟩
  · have hN := hJ.1.vert (i + 1) (j + 1) hi (by omega)
    have hm := hG.meas.vert i j hi (by omega)
    obtain ⟨c, hfr⟩ := (hG.spaces.vert i (j + 1) hi (by omega)).frame
    have hK : HEq ((G.nV i (j + 1)).princ ⊤) (levJ G' t (.grid (i + 1) (j + 1))) := by
      rw [GlobalTheory.Grid.Node.princ_top]
      exact lev_heq hN.sp hN.lat hfr.1
    show HEq (G.mV i (j + 1)).ν _ ∧ IsFundamentalDomain (GQ (G.nV i (j + 1)).V) (G.mV i (j + 1)).fd (G.mV i (j + 1)).ν
    by_cases hd : D.R.m - 1 ≤ j + 1
    · have h1 := hm.1 hd
      rw [if_pos (show (GlobalTheory.ChiGrid.Node.grid (i + 1) (j + 1)).neg D.R.m = 0 by simp only [GlobalTheory.ChiGrid.Node.neg]; omega)] at hAt
      exact ⟨measDef_heq hN.sp hK h1 hAt, h1.2⟩
    · have h1 := hm.2 hd
      rw [if_neg (show ¬ (GlobalTheory.ChiGrid.Node.grid (i + 1) (j + 1)).neg D.R.m = 0 by simp only [GlobalTheory.ChiGrid.Node.neg]; omega)] at hAt
      exact ⟨measFD_heq hN.sp hK h1 hAt, h1.2⟩

end GlobalTheory.GridMeasDown
