import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ProdDat
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsDblClosed
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SingleMemIdAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsHeisenbergCombinationSplitPlaceDatum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsInjectiveModel
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeIndicatorOnSplitHalfEqHalfIndicator
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsGLEmbeddingUnitaryAdelicSplitPlaceBasisStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsClopenIsCompactMapsPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GlobalFormOfSiegelWeil
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousSingleAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InfinitelyManySplitPlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNatEqMul
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EventuallyIncAMulMemIntAt

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SplitWeil GlobalTheory.LocMod ValuativeRel Filter
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.SeeSaw.LocPlModel
variable {D : D7}

section Rel
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] {S T : HSp D}

theorem up_zero (q : GlobalTheory.FinPl.SplitPt D k) (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) : (ofSplit q).up FS FT 0 = 0 := by
  unfold Place.up
  rw [Matrix.mul_zero, Matrix.zero_mul, Matrix.map_zero _ (map_zero _)]

theorem exists_latInd (q : GlobalTheory.FinPl.SplitPt D k) (hU : q.UnitAA) (FS : Frame k S.rank Y') (FT : Frame k T.rank Y)
    {M : GlobalTheory.FinPl.Lat S} {M' : GlobalTheory.FinPl.Lat T} (hM : IsSelfDualC S M) (hM' : IsSelfDualC T M') :
    ∃ Φ₀ : SB (Matrix Y Y' k),
      Φ₀.1 = Set.indicator {x | (ofSplit q).up FS FT x ∈ latO S T (M : Set _) (M' : Set _) (· = q.v)} (fun _ => 1) := by
  obtain ⟨gS, hS1, hS2⟩ := GlobalTheory.T.exists_GL_embedding_unitaryAdelic_splitPlace_basis D k q S Y' FS.β FS.γ FS.βγ FS.γβ
  obtain ⟨gT, hT1, hT2⟩ := GlobalTheory.T.exists_GL_embedding_unitaryAdelic_splitPlace_basis D k q T Y FT.β FT.γ FT.βγ FT.γβ
  let α : GlobalTheory.FinPl.Frame q S Y' := ⟨FS.β, FS.γ, FS.βγ, FS.γβ, gS, hS1, hS2⟩
  let β : GlobalTheory.FinPl.Frame q T Y := ⟨FT.β, FT.γ, FT.βγ, FT.γβ, gT, hT1, hT2⟩
  obtain ⟨ΛS, i1, hα, -⟩ := GlobalTheory.FinPl.FrameLat.exists_lat D k q S Y' α M hM
  obtain ⟨ΛT, i2, hβ, -⟩ := GlobalTheory.FinPl.FrameLat.exists_lat D k q T Y β M' hM'
  refine ⟨⟨GlobalTheory.LatPair.latInd ΛS ΛT, GlobalTheory.LatPair.latInd_mem_SB ΛS ΛT⟩, funext fun x => ?_⟩
  have hh := GlobalTheory.FinPl.HalfInd.isHalf_wr α β x
  have key := GlobalTheory.FinPl.LatIndHalf.mem_latO_iff_rd α β hM hM' hU hα hβ hh
  have hr : GlobalTheory.FinPl.rd α β (GlobalTheory.FinPl.HalfInd.wr α β x) = x := by
    rw [GlobalTheory.FinPl.HalfInd.rd_eq]
    have : Matrix.map (GlobalTheory.FinPl.HalfInd.wr α β x) q.pr = FT.β * x * FS.γ := by
      ext i j; rw [Matrix.map_apply, GlobalTheory.FinPl.HalfInd.wr_apply, q.pr_sec]
    rw [this]
    change FT.γ * (FT.β * x * FS.γ) * FS.β = x
    rw [Matrix.mul_assoc FT.β, ← Matrix.mul_assoc FT.γ, FT.γβ, Matrix.one_mul, Matrix.mul_assoc, FS.γβ, Matrix.mul_one]
  rw [hr] at key
  change GlobalTheory.LatPair.latInd ΛS ΛT x = _
  unfold GlobalTheory.LatPair.latInd
  by_cases h : ∀ y ∈ ΛS, x *ᵥ y ∈ ΛT
  · rw [if_pos h, Set.indicator_of_mem (by exact key.2 h)]
  · rw [if_neg h, Set.indicator_of_notMem (by exact fun h' => h (key.1 h'))]

theorem exists_locPl {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (q : GlobalTheory.FinPl.SplitPt D k) (hU : q.UnitAA)
    (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (Φ : SB (Matrix Y Y' k))
    {M : GlobalTheory.FinPl.Lat S} {M' : GlobalTheory.FinPl.Lat T} (hM : IsSelfDualC S M) (hM' : IsSelfDualC T M') :
    ∃ e o h1 h2 h3, (⟨k, q, hU, Y, Y', FS, FT, Φ, e, h1, o, h2, h3⟩ : LocPl ψ S T M M').q.v = q.v := by
  obtain ⟨O, hO, hO0⟩ := GlobalTheory.LocMod.PinModel.exists_isOne (k := k) (Y := Y) (Y' := Y')
  obtain ⟨Φ₀, h₀⟩ := exists_latInd q hU FS FT hM hM'
  have n1 : O ≠ 0 := by rintro rfl; simp at hO0
  have n0 : Φ₀ ≠ 0 := by
    rintro rfl
    have := congrFun h₀ 0
    rw [Set.indicator_of_mem (by simp [up_zero])] at this
    simp at this
  obtain ⟨e, he1, he2⟩ := GlobalTheory.LocComb.exists_comb D k (ofSplit q) Y Y' S T FS FT ψ hψ O Φ n1
  obtain ⟨o, ho1, ho2⟩ := GlobalTheory.LocComb.exists_comb D k (ofSplit q) Y Y' S T FS FT ψ hψ Φ₀ O n0
  refine ⟨e, o, ⟨he1, fun Tm hT O' Φ' h1 h2 => ?_⟩, ho1, fun Tm hT Φ₀' O' h1 h2 => ?_, rfl⟩
  · obtain rfl : O' = O := Subtype.ext (h1.trans hO.symm)
    obtain rfl : Φ' = Φ := Subtype.ext h2
    exact he2 Tm hT
  · obtain rfl : O' = O := Subtype.ext (h1.trans hO.symm)
    obtain rfl : Φ₀' = Φ₀ := Subtype.ext (h2.trans h₀.symm)
    exact ho2 Tm hT

end Rel

variable {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {M : GlobalTheory.FinPl.Lat S} {M' : GlobalTheory.FinPl.Lat T}

theorem comb_comb (L : LocPl ψ S T M M') {Tm} (hT : (ofSplit L.q).IsModel ψ L.FS L.FT Tm) (Φ₀ : SB (Matrix L.Y L.Y' L.k))
    (h₀ : Φ₀.1 = Set.indicator {x | (ofSplit L.q).up L.FS L.FT x ∈ latO S T (M : Set _) (M' : Set _) (· = L.q.v)} (fun _ => 1)) :
    Tm L.Φ = comb ψ S T L.e (comb ψ S T L.o (Tm Φ₀)) := by
  obtain ⟨O, hO, -⟩ := GlobalTheory.LocMod.PinModel.exists_isOne (k := L.k) (Y := L.Y) (Y' := L.Y')
  rw [L.e_is.2 Tm hT O L.Φ hO rfl, L.o_is Tm hT Φ₀ O hO h₀]

theorem o_ne_zero (hψ : IsStdChar D ψ (-1)) (hM : IsSelfDualC S M) (hM' : IsSelfDualC T M') (L : LocPl ψ S T M M') : L.o ≠ 0 := by
  intro h
  obtain ⟨O, hO, hO0⟩ := GlobalTheory.LocMod.PinModel.exists_isOne (k := L.k) (Y := L.Y) (Y' := L.Y')
  obtain ⟨Φ₀, h₀⟩ := exists_latInd L.q L.unit L.FS L.FT hM hM'
  obtain ⟨Tm, hT, hi⟩ := GlobalTheory.LocMod.Exist.exists_injective_model D L.k (ofSplit L.q) ψ hψ S T L.Y L.Y' L.FS L.FT
  have := L.o_is Tm hT Φ₀ O hO h₀
  rw [h] at this
  have h0 : O = 0 := hi (by rw [this, map_zero]; simp [comb])
  rw [h0] at hO0; simp at hO0

theorem e_ne_zero (hψ : IsStdChar D ψ (-1)) (L : LocPl ψ S T M M') (hΦ : L.Φ ≠ 0) : L.e ≠ 0 := by
  intro h
  obtain ⟨O, hO, -⟩ := GlobalTheory.LocMod.PinModel.exists_isOne (k := L.k) (Y := L.Y) (Y' := L.Y')
  obtain ⟨Tm, hT, hi⟩ := GlobalTheory.LocMod.Exist.exists_injective_model D L.k (ofSplit L.q) ψ hψ S T L.Y L.Y' L.FS L.FT
  have := L.e_is.2 Tm hT O L.Φ hO rfl
  rw [h] at this
  exact hΦ (hi (by rw [this, map_zero]; simp [comb]))

theorem prodDat_one (L : LocPl ψ S T M M') (x : Matrix L.Y L.Y' L.k) :
    prodDat (fun _ : Fin 1 => L) ((ofSplit L.q).up L.FS L.FT x) = L.Φ.1 x := by
  have h1 : IsHalf L.q.e ((ofSplit L.q).up L.FS L.FT x) := fun i j => by
    change L.q.e * L.q.sec _ = L.q.sec _
    exact GlobalTheory.FinPl.LatIndHalf.e_mul_sec _ _
  have h2 : (ofSplit L.q).down L.FS L.FT ((ofSplit L.q).up L.FS L.FT x) = x := by
    unfold Place.down
    have : Matrix.map ((ofSplit L.q).up L.FS L.FT x) (ofSplit L.q).π = L.FT.β * x * L.FS.γ := by
      ext i j; exact L.q.pr_sec _
    rw [this, Matrix.mul_assoc L.FT.β, ← Matrix.mul_assoc L.FT.γ, L.FT.γβ, Matrix.one_mul, Matrix.mul_assoc, L.FS.γβ, Matrix.mul_one]
  simp [prodDat, h1, h2]

theorem prodDat_zero (L : Fin 0 → LocPl ψ S T M M') (Λ : AddSubgroup (WO S T)) : prodDat L = halfInd 0 Λ := by
  funext x
  have : IsHalf 0 x ↔ x = 0 := ⟨fun h => by ext i j; simpa using (h i j).symm, fun h i j => by simp [h]⟩
  by_cases hx : x = 0
  · subst hx; simp [prodDat, halfInd, this]
  · simp [prodDat, halfInd, this, hx]

theorem e_mul_e (L L' : LocPl ψ S T M M') (h : L.q.v ≠ L'.q.v) : L.q.e * L'.q.e = 0 := by
  have h1 : L.q.e * L'.q.e ∈ GlobalTheory.FinPl.idAt D (· = L.q.v) := Ideal.mul_mem_right _ _ (GlobalTheory.FinPl.LatIndHalf.e_mem_idAt L.q)
  have h2 : L.q.e * L'.q.e ∈ GlobalTheory.FinPl.idAt D (· = L'.q.v) := Ideal.mul_mem_left _ _ (GlobalTheory.FinPl.LatIndHalf.e_mem_idAt L'.q)
  have h3 : GlobalTheory.FinPl.compAt D L.q.v (L.q.e * L'.q.e) = 0 := (Submodule.mem_iInf _).1 (Submodule.mem_inf.1 h2).2 ⟨_, h⟩
  rw [GlobalTheory.FinPl.Model.eq_single h1, h3, map_zero]

theorem prodDat_sum {n : ℕ} (L : Fin n → LocPl ψ S T M M') (inj : Function.Injective fun i => (L i).q.v)
    (x : ∀ i, Matrix (L i).Y (L i).Y' (L i).k) :
    prodDat L (∑ i, (ofSplit (L i).q).up (L i).FS (L i).FT (x i)) = ∏ i, (L i).Φ.1 (x i) := by
  have hz : ∀ i j, i ≠ j → ∀ a, (L i).q.e * (L j).q.sec a = 0 := fun i j h a => by
    rw [← GlobalTheory.FinPl.LatIndHalf.e_mul_sec (L j).q a, ← mul_assoc, e_mul_e _ _ (fun h' => h (inj h')), zero_mul]
  have hp : ∀ i j, i ≠ j → ∀ a, (L i).q.pr ((L j).q.sec a) = 0 := fun i j h a => by
    rw [← (L i).q.pr_sec ((L i).q.pr _), (L i).q.sec_pr, hz i j h, map_zero]
  have h1 : IsHalf (∑ i, (L i).q.e) (∑ i, (ofSplit (L i).q).up (L i).FS (L i).FT (x i)) := fun r s => by
    rw [Matrix.sum_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    change _ * (L j).q.sec _ = (L j).q.sec _
    rw [Finset.sum_mul, Finset.sum_eq_single j (fun i _ h => hz i j h _) (fun h => (h (Finset.mem_univ _)).elim), GlobalTheory.FinPl.LatIndHalf.e_mul_sec]
  have h2 : ∀ i, (ofSplit (L i).q).down (L i).FS (L i).FT (∑ i, (ofSplit (L i).q).up (L i).FS (L i).FT (x i)) = x i := fun i => by
    unfold Place.down
    have : Matrix.map (∑ i, (ofSplit (L i).q).up (L i).FS (L i).FT (x i)) (ofSplit (L i).q).π = (L i).FT.β * x i * (L i).FS.γ := by
      ext r s
      rw [Matrix.map_apply, Matrix.sum_apply, map_sum]
      exact (Finset.sum_eq_single i (fun j _ h => hp i j (Ne.symm h) _) (fun h => (h (Finset.mem_univ _)).elim)).trans
        ((L i).q.pr_sec _)
    rw [this, Matrix.mul_assoc (L i).FT.β, ← Matrix.mul_assoc (L i).FT.γ, (L i).FT.γβ, Matrix.one_mul, Matrix.mul_assoc,
      (L i).FS.γβ, Matrix.mul_one]
  unfold prodDat
  rw [if_pos h1]
  exact Finset.prod_congr rfl fun i _ => by rw [h2]

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem infinite_unit (D : D7) : {v : GlobalTheory.FinPl.Pl D | ∃ p : GlobalTheory.FinPl.SplitPt D (Fv D.host.F v), p.v = v ∧ p.UnitAA}.Infinite := by
  have h := ((GlobalTheory.FinPl.AlmostAll.latA_eq_latV D).and ((GlobalTheory.FinPl.AeUnit.eventually_incA_mul_mem_intAt D D.host.xi0).and
    (GlobalTheory.FinPl.AeUnit.eventually_incA_mul_mem_intAt D D.host.xi0⁻¹)))
  refine Set.infinite_iff_frequently_cofinite.2
    (((Set.infinite_iff_frequently_cofinite.1 (GlobalTheory.FinPl.infinite_splitIdem_places D)).and_eventually h).mono ?_)
  rintro v ⟨⟨e, ε, he, hε, hs⟩, h1, h2, h3⟩
  obtain ⟨p, -, hp⟩ := GlobalTheory.FinPl.SplitPoint.exists_splitPt D v e ε he hε hs
  refine ⟨p, hp, ?_⟩
  unfold GlobalTheory.FinPl.SplitPt.UnitAA
  rw [hp]
  exact ⟨fun a ha => ⟨h2 a ha, h3 a ha⟩, h1⟩

theorem exists_family (hψ : IsStdChar D ψ (-1)) (hM : IsSelfDualC S M) (hM' : IsSelfDualC T M') (n : ℕ) :
    ∃ L : Fin n → LocPl ψ S T M M', (Function.Injective fun i => (L i).q.v) ∧ prodDat L 0 = 1 ∧
      ∀ i, (L i).e ≠ 0 ∧ (L i).o ≠ 0 := by
  let g := (infinite_unit D).natEmbedding
  have : ∀ i : Fin n, ∃ L : LocPl ψ S T M M', L.q.v = (g i).1 ∧ L.Φ.1 0 = 1 := fun i => by
    obtain ⟨p, hp, hU⟩ := (g i).2
    obtain ⟨O, -, hO0⟩ := GlobalTheory.LocMod.PinModel.exists_isOne (k := Fv D.host.F (g i).1) (Y := Fin T.rank) (Y' := Fin S.rank)
    obtain ⟨e, o, h1, h2, h3, -⟩ := exists_locPl hψ p hU (Frame.ofGL 1) (Frame.ofGL 1) O hM hM'
    exact ⟨⟨_, p, hU, _, _, _, _, O, e, h1, o, h2, h3⟩, hp, hO0⟩
  choose L h1 h2 using this
  refine ⟨L, fun i j h => ?_, ?_, fun i => ⟨e_ne_zero hψ _ fun h => ?_, o_ne_zero hψ hM hM' _⟩⟩
  · simp only [h1] at h
    exact Fin.ext (g.injective (Subtype.ext h))
  · have h0 : IsHalf (∑ i, (L i).q.e) (0 : WO S T) := fun i j => by simp
    have hd : ∀ i, (ofSplit (L i).q).down (L i).FS (L i).FT (0 : WO S T) = 0 := fun i => by
      unfold Place.down
      rw [Matrix.map_zero _ (map_zero _), Matrix.mul_zero, Matrix.zero_mul]
    simp [prodDat, h0, hd, h2]
  · have := h2 i
    rw [h] at this; simp at this

theorem exists_closed (D : D7) (S T : HSp D) (n : ℕ) : ∃ (ψ : AddChar (AF D.host.F) ℂ) (M : GlobalTheory.FinPl.Lat S) (M' : GlobalTheory.FinPl.Lat T),
    IsStdChar D ψ (-1) ∧ IsSelfDualC S M ∧ IsSelfDualC T M' ∧ ∃ L : Fin n → LocPl ψ S T M M',
      (Function.Injective fun i => (L i).q.v) ∧ prodDat L 0 = 1 ∧ ∀ i, (L i).e ≠ 0 ∧ (L i).o ≠ 0 := by
  obtain ⟨ψ, hψ⟩ := (GlobalTheory.Ker.exists_infFam_and_stdChar D).2
  exact ⟨ψ, _, _, hψ, GlobalTheory.Core.Rk.IP.frameLat_isSelfDualC S, GlobalTheory.Core.Rk.IP.frameLat_isSelfDualC T,
    exists_family hψ (GlobalTheory.Core.Rk.IP.frameLat_isSelfDualC S) (GlobalTheory.Core.Rk.IP.frameLat_isSelfDualC T) n⟩

end GlobalTheory.SeeSaw.LocPlModel
end
