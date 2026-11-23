import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeOrbitVectorsMovedPair
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumVectorMovedPair
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ApplyAddInfRat

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped TensorProduct

namespace GlobalTheory.RowVac

set_option synthInstance.maxHeartbeats 400000

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GlobalTheory.ChiGrid.GridData L sc} {U : Set T}

private lemma eToEAf_mem_hatL_of_mem {n : ℕ} (C : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (s : Fin n → D.host.E) (hs : s ∈ C) :
    (fun j => Formalism.IndefR.Datum.eToEAf D (s j)) ∈ Formalism.L2.Herm.hatL (F := D.host.F) C := by
  unfold Formalism.L2.Herm.hatL Formalism.UG.latS
  exact Submodule.subset_span ⟨s, hs, rfl⟩

theorem fwd_gen (V : HSp D) (k : Formalism.L2.Theta.GA D V) (C Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (hb : ∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) C ↔
      (Formalism.IndefR.Lev.finE V k).1 *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ)
    (s : Fin V.rank → D.host.E) (hs : s ∈ C) :
    (fun i => Formalism.IndefR.Datum.toEAf D ((Formalism.L2.Theta.mt V k *ᵥ fun j => incA D (s j)) i)) ∈
      Formalism.L2.Herm.hatL (F := D.host.F) Λ := by
  rw [GlobalTheory.MovedHomLat.bridge]
  exact (hb _).1 (eToEAf_mem_hatL_of_mem C s hs)

set_option maxHeartbeats 1000000 in

theorem bwd_gen (V : HSp D) (k : Formalism.L2.Theta.GA D V) (C Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (hb : ∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) C ↔
      (Formalism.IndefR.Lev.finE V k).1 *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ)
    (s : Fin V.rank → D.host.E) (hs : s ∈ Λ) :
    (fun i => Formalism.IndefR.Datum.toEAf D ((Formalism.L2.Theta.mt V k⁻¹ *ᵥ fun j => incA D (s j)) i)) ∈
      Formalism.L2.Herm.hatL (F := D.host.F) C := by
  apply GlobalTheory.MovedHomLat.bwd V k C s
  rw [GlobalTheory.MovedHomLat.mem_globLat_iff]
  apply (hb _).2
  rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  exact eToEAf_mem_hatL_of_mem Λ s hs

theorem isVacO_om (W : G.Weil) (p : Pair T) (hp : p.InRange D.R.m) (g : Formalism.L2.Theta.GA D (G.pS p)) (h : Formalism.L2.Theta.GA D (G.pT p))
    (hg : g ∈ GfC (G.pS p)) (hh : h ∈ GfC (G.pT p)) (AS BS : Set (Fin (G.pS p).rank → D.host.E))
    (AT BT : Set (Fin (G.pT p).rank → D.host.E))
    (hact : ∀ w' ∈ latO _ _ BS BT (fun _ => True), ∃ w ∈ latO _ _ AS AT (fun _ => True), actO _ _ g h w = w')
    (f : WO (G.pS p) (G.pT p) → ℂ) (hf : IsVacO W.ψ W.θ _ _ (G.cartS W.cart p) (G.onT W.cart p) AS AT f) :
    IsVacO W.ψ W.θ _ _ (G.cartS W.cart p) (G.onT W.cart p) BS BT (W.om p (g, h) f) := by
  have hW := W.om_is p hp
  unfold IsVacO at hf ⊢
  obtain ⟨hstd, hvac⟩ := hf
  obtain ⟨hθ, hth, hlat, hfock, hnrm⟩ := hvac
  obtain ⟨-, -, -, -, -, hpres, hint, -, -, hunit, -⟩ := hW
  have hth' := hpres (g, h) f hth
  have ⟨_, _, hc, _⟩ := hth
  have ⟨_, _, hc', _⟩ := hth'
  refine ⟨hstd, hθ, hth', ⟨?_, ?_⟩, ?_, ?_⟩
  · intro u hu
    obtain ⟨w, hw, rfl⟩ := hact u hu
    rw [← GlobalTheory.WeilVacMove.actO_two_nsmul, ← hint g h _ f hth, hlat.1 w hw]
  · intro e he u hu hhalf
    obtain ⟨w, hw, rfl⟩ := hact u hu
    have hw' : IsHalf e w := by
      have := GlobalTheory.WeilVacMove.isHalf_actO e g⁻¹ h⁻¹ hhalf
      rwa [GlobalTheory.WeilVacMove.actO_inv_actO] at this
    rw [← hint g h _ f hth, hlat.2 e he w hw hw']
  · intro τ
    have hg1 := GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC W.θ _ hg τ
    have hh1 := GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC W.θ _ hh τ
    have hgi : compAt W.θ τ (Formalism.L2.Theta.mt _ g⁻¹) = 1 := by
      have := GlobalTheory.WeilVacMove.compAt_mt_mul_inv W.θ τ _ g
      rwa [hg1, one_mul] at this
    have key : ∀ z', W.om p (g, h) (Formalism.IndefR.Datum.dRho (heisO W.ψ _ _) W.θ τ z' f) =
        Formalism.IndefR.Datum.dRho (heisO W.ψ _ _) W.θ τ z' (W.om p (g, h) f) := by
      intro z'
      have := GlobalTheory.WeilVacMove.om_dRho (W.om_is p hp) hθ g h τ z' hth
      rwa [hh1, hgi, Matrix.one_mul, Matrix.mul_one] at this
    have h0 := hfock τ
    unfold IsFockVacAt at h0 ⊢
    intro z
    have h1 := h0 z
    unfold annih at h1 ⊢
    rw [← key, ← key, ← map_smul, ← map_add, h1, map_zero]
  · refine ⟨hnrm.1, fun a ha => ?_⟩
    have h1 : nrm2 a.1 a.2 f = 1 := hnrm.2 a ha
    show nrm2 a.1 a.2 _ = 1
    unfold IsCovolOne at ha
    obtain ⟨hμ, hF, -⟩ := ha
    rw [GlobalTheory.WeilVacMove.sqNormIntegralFundamentalDomain_eq_l2Norm_sq _ _ hc] at h1
    rw [GlobalTheory.WeilVacMove.sqNormIntegralFundamentalDomain_eq_l2Norm_sq _ _ hc', hunit a.1 a.2 hμ hF (g, h) f hth]
    exact h1

theorem neg_mem_GfC (V : HSp D) {g : Formalism.L2.Theta.GA D V} (hg : g ∈ GfC V) : negGA V g ∈ GfC (negSp V) := by
  unfold GfC at hg ⊢
  rw [MonoidHom.mem_ker] at hg ⊢
  exact hg

set_option maxHeartbeats 1000000 in

theorem moved_isVac (W : G.Weil) (N : Std G U) (Z : Normal W N) (i : ℕ) (hi : i < D.R.m) :
    W.IsVac (.chi i D.R.m) (W.om (.chi i D.R.m) (G.toPair (.chi i D.R.m) (N.u (Pair.chi i D.R.m : Pair T).small).1
      (N.u (Pair.chi i D.R.m : Pair T).big).1) (Z.vac (.chi i D.R.m))) := by
  have hdp : DefPair D.R.m (Pair.chi i D.R.m : Pair T) := ⟨hi, rfl⟩
  have hbig : DefNode D.R.m (Node.grid (i + 1) D.R.m) := ⟨hi, rfl⟩
  have hsmall : DefNode D.R.m (Node.grid i D.R.m) := ⟨hi.le, rfl⟩
  have hp : (Pair.chi i D.R.m : Pair T).InRange D.R.m := ⟨hi, le_rfl⟩
  have hU := N.u_lat _ hbig
  have hV := N.u_lat _ hsmall
  have hg : negGA (G.V (.grid (i + 1) D.R.m)) (N.u (.grid (i + 1) D.R.m)).1 ∈ GfC (negSp (G.V (.grid (i + 1) D.R.m))) :=
    neg_mem_GfC (G.V (.grid (i + 1) D.R.m)) (N.u (.grid (i + 1) D.R.m)).2
  have hh : (N.u (.grid i D.R.m)).1 ∈ GfC (G.V (.grid i D.R.m)) := (N.u (.grid i D.R.m)).2
  have hv := Z.vac_is _ hdp
  have hact : ∀ w' ∈ latO (G.pS (.chi i D.R.m)) (G.pT (.chi i D.R.m)) (G.latS (.chi i D.R.m) : Set _)
      (G.latT (.chi i D.R.m) : Set _) (fun _ => True), ∃ w ∈ latO (G.pS (.chi i D.R.m)) (G.pT (.chi i D.R.m))
      (N.latS (.chi i D.R.m) : Set _) (N.latT (.chi i D.R.m) : Set _) (fun _ => True),
      actO (G.pS (.chi i D.R.m)) (G.pT (.chi i D.R.m)) (negGA (G.V (.grid (i + 1) D.R.m)) (N.u (.grid (i + 1) D.R.m)).1)
        (N.u (.grid i D.R.m)).1 w = w' := by
    refine (GlobalTheory.MovedHomLat.actO_latO_onto _ _ _ _ (N.latS (.chi i D.R.m)) (G.latS (.chi i D.R.m))
      (N.latT (.chi i D.R.m)) (G.latT (.chi i D.R.m)) ?_ ?_ ?_ ?_).2
    · intro s hs
      rw [mt_negGA]
      exact fwd_gen _ _ _ _ hU s hs
    · intro t ht
      exact fwd_gen _ _ _ _ hV t ht
    · intro s hs
      rw [← map_inv, mt_negGA]
      exact bwd_gen _ _ _ _ hU s hs
    · intro t ht
      exact bwd_gen _ _ _ _ hV t ht
  exact isVacO_om W (.chi i D.R.m) hp _ _ hg hh _ _ _ _ hact _ hv

private lemma sigOK_and_isSelfDualC_grid {μ₀ : T} (hL : L.Is μ₀) (a b : ℕ) (ha : a ≤ D.R.m) (hb : b ≤ D.R.m) :
    (G.V (.grid a b)).SigOK ∧ IsSelfDualC (G.V (.grid a b)) (G.Λ (.grid a b)) := by
  rcases Nat.eq_zero_or_pos a with rfl | ha1
  · show (columnBlock L b).sp.SigOK ∧ IsSelfDualC (columnBlock L b).sp (columnBlock L b).lat
    rcases lt_or_eq_of_le hb with hb' | rfl
    · rw [colY_lt L hb']
      exact ⟨D.sp.Y_sig _, GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame _ _ _ _ _ (hL.βY b hb')⟩
    · rw [colY_m L]
      exact ⟨D.sp.X'_sig, GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame _ _ _ _ _ hL.βX⟩
  · have hv := G.isV (X := .grid a b) ⟨ha, hb⟩ (by intro j h; injection h with h1 h2; omega)
    exact ⟨hv.sigOK, hv.sd⟩

theorem isVac_unique (W : G.Weil) {μ₀ : T} (hL : L.Is μ₀) (i j : ℕ) (hp : (Pair.chi i j : Pair T).InRange D.R.m) {f f'}
    (hf : W.IsVac (.chi i j) f) (hf' : W.IsVac (.chi i j) f') : ∃ κ : ℂˣ, f' = (κ : ℂ) • f := by
  unfold GridData.Weil.IsVac at hf hf'
  obtain ⟨hp1, hp2⟩ := hp
  obtain ⟨hs1, hd1⟩ := sigOK_and_isSelfDualC_grid hL (i + 1) j hp1 hp2
  obtain ⟨hs2, hd2⟩ := sigOK_and_isSelfDualC_grid hL i j (by omega) hp2
  have key := VacUnique.vacUniqueO D W.ψ W.θ W.ψ_std W.θ_is _ _ _ _ (GlobalTheory.GridWeil.sigOK_neg hs1) hs2
    (fun τ => GlobalTheory.ChiGrid.isCartanInv_neg (W.cart_is (.grid (i + 1) j) ⟨hp1, hp2⟩ τ))
    (W.cart_is (.grid i j) ⟨by omega, hp2⟩) _ _
    (isSelfDualC_neg hd1) hd2 f f' hf hf'
  obtain ⟨c, hc, hcf⟩ := key
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hc
    exact zero_ne_one hc
  exact ⟨Units.mk0 c hc0, hcf⟩

theorem moved_vac_eq : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (large₂ : SizeData₂ D) (F : Face D A), HidaSetting large₂ R F → ∀ (ch : Choice R), ch.Is → ∀ i : ℕ, i < D.R.m → ∃ κ : ℂˣ, ch.W.om (.chi i D.R.m) (ch.G.toPair (.chi i D.R.m) (ch.S.N.u (Pair.chi i D.R.m : Pair T).small).1 (ch.S.N.u (Pair.chi i D.R.m : Pair T).big).1) (ch.S.Z.vac (.chi i D.R.m)) = (κ : ℂ) • ch.rm.vX i D.R.m := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R large₂ F hS ch hch i hi
  have hL : R.toLevCh.Is A.μ0 := by
    obtain ⟨-, -, -, -, hcore, -⟩ := hS
    exact hcore.lev
  exact isVac_unique ch.W hL i D.R.m ⟨hi, le_rfl⟩ (ch.rm.vX_is i D.R.m hi le_rfl)
    (moved_isVac ch.W ch.S.N ch.S.Z i hi)

end GlobalTheory.RowVac
