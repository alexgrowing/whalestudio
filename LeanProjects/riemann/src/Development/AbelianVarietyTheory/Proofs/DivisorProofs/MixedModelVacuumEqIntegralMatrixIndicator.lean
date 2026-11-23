import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMixModelB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAwayUnitOfPowEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaussianDatumFlippedFiniteTensorBigRoute
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemCompletedHomLatticeIffIntegralOnUnitHalf
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HostIdealUnitAtPlacesPrimeToLevel
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory Matrix
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm GlobalTheory.BigNZ GlobalTheory.FlipMatch GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB incM)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW psiLoc chrW)
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopFlip

noncomputable section

namespace GlobalTheory.MixVacBig

open GlobalTheory.BigDat

variable {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {μ₀ : T}

theorem isIdemSum_atPl (hL : L.Is μ₀) (t : T) {w : Pl D.host.E} (hw : w ∈ locPl G t) : IsIdemSum (atPl w 1) {w} := by
  obtain ⟨_, ⟨es, hes, -⟩, -⟩ := GlobalTheory.FunObj.LocTensor.exists_idemSum_locPl hL G t
  have h := hes w hw
  rw [← GlobalTheory.IdemAtPl.eq_atPl_of_isIdemAt h]
  exact ⟨⟨fun _ => es w, fun P hP => by rw [Finset.mem_singleton.1 hP]; exact h, by simp⟩, h.1.2.1⟩

theorem aa_unit_of_standing {t : T} (hst : SquareStanding G t) {w : Pl D.host.E} (hw : w ∈ locPl G t) :
    (∀ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) ≤ 1) ∧
      ∃ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) = 1 := by
  have h := hst.2 w hw
  rw [Nat.cast_mul] at h
  exact GlobalTheory.AAUnit.aa_unit D w (fun h' => h (w.asIdeal.mul_mem_right _ h')) fun h' => h (w.asIdeal.mul_mem_left _ h')

theorem coord_int_iff (B : Frames G) (t : T) (w : Pl D.host.E) {X Y : ℕ × ℕ}
    (hX : X.1 ≤ D.R.m ∧ X.2 ≤ D.R.m) (hY : Y.1 ≤ D.R.m ∧ Y.2 ≤ D.R.m)
    (z : Matrix (Fin (G.V (.grid X.1 X.2)).rank) (Fin (G.V (.grid Y.1 Y.2)).rank) (AE D)) :
    GlobalTheory.StepData.IntM (B.coord t w hX hY (z.map (atW w))) ↔
      GlobalTheory.StepData.IntM ((Comparison₂.fr (B.β X.1 X.2) (B.β Y.1 Y.2) (z.map (toEAf D))).map (cpt (D := D) w)) := by
  have e : z.map (atW w) = (z.map (toEAf D)).map (cpt (D := D) w) := rfl
  rw [e, Comparison₂.coord_map]
  refine ⟨fun H a b => ?_, fun H a b => H _ _⟩
  have := H (b.cast (rank_vertex G t w hY).symm) (a.cast (rank_vertex G t w hX).symm)
  simpa only [Matrix.transpose_apply, Matrix.submatrix_apply, Fin.cast_cast, Fin.cast_eq_self] using this

theorem mem_lat_iff (hL : L.Is μ₀) (B : Frames G) (t : T) (hst : SquareStanding G t) {i j : Fin D.R.m} (e : Num G i j)
    {w : Pl D.host.E} (hw : w ∈ locPl G t) {x : Pt G i j} (hx : x ∈ mixHalf e (atPl w 1)) :
    (mapV e x ∈ latV G i j ∧ mapW e x ∈ latW G i j) ↔
      ∀ r s, mixCo B t e w x r s ∈ (ValuativeRel.valuation (Kw w)).integer := by
  have hI := isIdemSum_atPl hL t hw
  have hA : ∀ w' ∈ ({w} : Finset (Pl D.host.E)), ((∀ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w') a) ≤ 1) ∧
      ∃ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w') a) = 1) := fun w' hw' => by
    rw [Finset.mem_singleton.1 hw']
    exact aa_unit_of_standing hst hw
  have hT₁ : IsSelfDualC (spW G i j) (G.Λ (.grid ((i : ℕ) + 1) ((j : ℕ) + 1))) :=
    (node_isV G hL (X := .grid ((i : ℕ) + 1) ((j : ℕ) + 1)) ⟨i.2, j.2⟩).sd
  have hS : IsSelfDualC (negSp (spW G i j)) (G.Λ (.grid ((i : ℕ) + 1) ((j : ℕ) + 1))) := isSelfDualC_neg hT₁
  have hT : IsSelfDualC (spV G i j) (G.Λ (.grid (i : ℕ) ((j : ℕ) + 1))) :=
    (node_isV G hL (X := .grid (i : ℕ) ((j : ℕ) + 1)) ⟨i.2.le, j.2⟩).sd
  have hS₁ : IsSelfDualC (spV₁ G i j) (G.Λ (.grid ((i : ℕ) + 1) (j : ℕ))) :=
    (node_isV G hL (X := .grid ((i : ℕ) + 1) (j : ℕ)) ⟨i.2, j.2.le⟩).sd
  have fW := B.isFrame_β hL (i := (i : ℕ) + 1) (j := (j : ℕ) + 1) i.2 j.2
  have fV := B.isFrame_β hL (i := (i : ℕ)) (j := (j : ℕ) + 1) i.2.le j.2
  have fV₁ := B.isFrame_β hL (i := (i : ℕ) + 1) (j := (j : ℕ)) i.2 j.2.le
  have k₁ := GlobalTheory.ColLatDict.mem_latO_iff_intM hS hT fW fV hI hA (mapV e x) hx.1
  have k₂ := GlobalTheory.ColLatDict.mem_latO_iff_intM hS₁ hT₁ fV₁ fW hI hA (mapW e x) hx.2
  simp only [Finset.mem_singleton, forall_eq] at k₁ k₂
  have c₁ := coord_int_iff B t w (X := (i, j + 1)) (Y := (i + 1, j + 1)) ⟨i.2.le, j.2⟩ ⟨i.2, j.2⟩ (mapV e x)
  have c₂ := coord_int_iff B t w (X := (i + 1, j + 1)) (Y := (i + 1, j)) ⟨i.2, j.2⟩ ⟨i.2, j.2.le⟩ (mapW e x)
  refine (and_congr (k₁.trans c₁.symm) (k₂.trans c₂.symm)).trans ?_
  rw [mixCo_eq]
  refine ⟨fun H r s => ?_, fun H => ⟨fun r s => H r (.inl s), fun r s => H s (.inr r)⟩⟩
  rcases s with s | s
  · exact H.1 r s
  · exact H.2 s r

set_option maxHeartbeats 800000 in

theorem mix_vac : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (W : G.Weil) (B : Frames G) (t : T) (i j : Fin D.R.m) (M : Vol G), SquareStanding G t →
    ∀ (e : Num G i j) (Bs : Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : Chars D.host.F D.host.E)
      (om : Rep D.sp.cm.sig Γ.V Γ.W) (om' : Rep D.sp.cm.sig Γ.V' Γ.W), IsTripleOf W M t i j e Bs Γ X →
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om' → IsTied t i j e Bs Γ X → ∀ w ∈ locPl G t, ∀ ι : ToA G t i j w, IsMixModelA W B t e Γ w ι →
      ι (Γ.M.vac _) = ι (Γ.M.vac _) 0 • Set.indicator {Z | ∀ r s, Z r s ∈ (ValuativeRel.valuation (Kw w)).integer} 1 := by
  intro D T L sc G μ₀ hL W B t i j M hst e Bs Γ X om om' h hT hti w hw ι hι
  classical
  have hG : Γ.M.IsGood W.ψ := h.ψ ▸ hT.geo.hM
  obtain ⟨hid, -⟩ := GlobalTheory.IdemAtPl.main hL (G := G) t
  have hh := GlobalTheory.BigDat.halves_split hL W i j e Γ h.JW h.JWW _ _ (hid w hw).1 (hid w hw).2
  have hco := GlobalTheory.BigDat.mixCo_spec B t i j e
  have hv := GlobalTheory.BigDat.lagr_vac hι (hG.vac _).1 (hG.vac _).2.1 (latPt e (w.under (𝓞 D.host.F)) : Set _)
    (fun γ hγ hγ' => GlobalTheory.BigDat.VacFix.vac_fixed W M t i j e Bs Γ X om om' h hT _
      (GlobalTheory.BigDat.latPt_le_latAtV t i j e Bs Γ X hti _) γ (.inr ⟨hγ, hγ'.elim
      (fun h => ⟨_, (hid w hw).1, h⟩) fun h => ⟨_, splitIdem_conj (hid w hw).1, h⟩⟩)) (hco w).2.1 hh.2.2.2.1
  funext z
  obtain ⟨x, hx, rfl⟩ := (hco w).2.1 z
  have key := mem_lat_iff hL B t hst e hw hx
  rw [hv.2 x hx, Pi.smul_apply, smul_eq_mul]
  by_cases hl : mapV e x ∈ latV G i j ∧ mapW e x ∈ latW G i j
  · rw [Set.indicator_of_mem (show x ∈ (latPt e (w.under (𝓞 D.host.F)) : Set _) from ⟨hh.1 x hx, hl⟩),
      Set.indicator_of_mem (show mixCo B t e w x ∈ {Z : MatA G t i j w | ∀ r s, Z r s ∈ (ValuativeRel.valuation (Kw w)).integer}
        from key.1 hl), Pi.one_apply, mul_one]
  · rw [Set.indicator_of_notMem (show x ∉ (latPt e (w.under (𝓞 D.host.F)) : Set _) from fun h' => hl h'.2),
      Set.indicator_of_notMem (show mixCo B t e w x ∉ {Z : MatA G t i j w | ∀ r s, Z r s ∈ (ValuativeRel.valuation (Kw w)).integer}
        from fun h' => hl (key.2 h')), mul_zero]

end GlobalTheory.MixVacBig

end
