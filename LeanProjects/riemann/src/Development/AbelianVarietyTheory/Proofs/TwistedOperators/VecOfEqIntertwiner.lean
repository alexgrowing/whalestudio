import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairPtsClasses
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairPtsEqSum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MovFn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionSchrodingerModelFiniteIdempotent
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsThetaAtOfVac
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHomLatticeIffFrameStabilizerActMem
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSelfDualAdelicFrameLevelOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugatedLevelElementKeepsStandardLatticeStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChiArrowPairMovesStandardVacuumByScalarStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.RowVertexInv
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.RowVertexInv.FactorTheta

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem om_theta_eq {ψ : AddChar (AF D.host.F) ℂ} {S' T' : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S' × GA D T' →* Module.End ℂ (WO S' T' → ℂ)} (hW : IsWeilDatumO ψ S' T' χS χT om) {e : AE D}
    (he : e * e = e) (hinf : infPart D e = 0) {ΛS : Submodule (𝓞 D.host.E) (Fin S'.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T'.rank → D.host.E)} (hS : IsSelfDualC S' ΛS) (hT : IsSelfDualC T' ΛT)
    {f₀ : WO S' T' → ℂ} (hf₀ : IsThetaFunO ψ S' T' f₀) (g : GA D S' × GA D T')
    (hΛ : ∀ u, u ∈ latO S' T' (ΛS : Set _) (ΛT : Set _) (fun _ => True) ↔
      actO S' T' g.1 g.2 u ∈ latO S' T' (ΛS : Set _) (ΛT : Set _) (fun _ => True))
    {c : ℂ} (hc : c ≠ 0) (h0 : om g f₀ = c • f₀) {Tm : (WO S' T' → ℂ) →ₗ[ℂ] (WO S' T' → ℂ)}
    (hTm : IsPlaceModel ψ (symplO S' T') (heisO ψ S' T') e (latO S' T' (ΛS : Set _) (ΛT : Set _) (fun _ => True)) 1 f₀ Tm)
    {Φ f : WO S' T' → ℂ}
    (hf : IsThetaAt ψ (symplO S' T') (heisO ψ S' T') e (latO S' T' (ΛS : Set _) (ΛT : Set _) (fun _ => True)) 1 f₀ Φ f) :
    om g f = Tm (c • fun x => Φ (actO S' T' g⁻¹.1 g⁻¹.2 x)) := by
  have hΛ' : ∀ u, u ∈ latO S' T' (ΛS : Set _) (ΛT : Set _) (fun _ => True) ↔
      actO S' T' g⁻¹.1 g⁻¹.2 u ∈ latO S' T' (ΛS : Set _) (ΛT : Set _) (fun _ => True) := by
    intro u
    have e1 : actO S' T' g.1 g.2 (actO S' T' g⁻¹.1 g⁻¹.2 u) = u := by
      rw [Prod.fst_inv, Prod.snd_inv]; exact GlobalTheory.AdelicLatMove.actO_actO_inv _ _ _ _ u
    rw [hΛ (actO S' T' g⁻¹.1 g⁻¹.2 u), e1]
  have hinv : om g⁻¹ f₀ = c⁻¹ • f₀ := by
    have e2 : om g⁻¹ (om g f₀) = f₀ := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    rw [h0, LinearMap.map_smul] at e2
    calc om g⁻¹ f₀ = c⁻¹ • (c • om g⁻¹ f₀) := by rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
      _ = c⁻¹ • f₀ := by rw [e2]
  have hth := GlobalTheory.SchrTheta.isTheta_placeModel D ψ hW.std S' T' ΛS ΛT hS hT e he hinf f₀ hf₀ Tm hTm
  have hmod := GlobalTheory.SchrMove.isPlaceModel_move hW hΛ' hTm hth (inv_ne_zero hc) hinv
  have hfe : f = ((c⁻¹)⁻¹ • (om g⁻¹ ∘ₗ Tm ∘ₗ LinearMap.funLeft ℂ ℂ (actO S' T' g⁻¹.1 g⁻¹.2))) Φ := hf.2 _ hmod
  rw [hfe, inv_inv, LinearMap.smul_apply, LinearMap.map_smul, LinearMap.comp_apply, LinearMap.comp_apply,
    ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply, LinearMap.map_smul]
  rfl

end GlobalTheory.RowVertexInv.FactorTheta

namespace GlobalTheory.RowVertexInv.FactorTheta

open Matrix

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem keepStd (S : GridChoice W U) {t : T} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m))
    (hk : finG (G.V (.grid (j + 1) D.R.m)) k ∈ S.levRow t (j + 1) hj.le) (v : Fin (G.V (.grid (j + 1) D.R.m)).rank → Formalism.IndefR.Lev.EAf D) :
    v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat (S.N.fr (.grid (j + 1) D.R.m))) ↔
      (Formalism.IndefR.Lev.finE (G.V (.grid (j + 1) D.R.m)) (moved S j k)).1 *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat (S.N.fr (.grid (j + 1) D.R.m))) :=
  GlobalTheory.T.conjugatedLevelElement_keeps_standardLattice S j hj k hk v

theorem mulVec_mulVec_inv {n : ℕ} {R : Type} [CommRing R] (X : GL (Fin n) R) (v : Fin n → R) :
    X.1 *ᵥ ((X⁻¹).1 *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]

theorem keepPair (S : GridChoice W U) {i : ℕ} (hi : i + 1 ≤ D.R.m) (x : GA D (G.V (.grid i D.R.m))) (y : GA D (G.V (.grid (i + 1) D.R.m)))
    (hxf : x ∈ GfC (G.V (.grid i D.R.m))) (hyf : y ∈ GfC (G.V (.grid (i + 1) D.R.m)))
    (hx : ∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat (S.N.fr (.grid i D.R.m))) ↔
      (Formalism.IndefR.Lev.finE (G.V (.grid i D.R.m)) x).1 *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat (S.N.fr (.grid i D.R.m))))
    (hy : ∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat (S.N.fr (.grid (i + 1) D.R.m))) ↔
      (Formalism.IndefR.Lev.finE (G.V (.grid (i + 1) D.R.m)) y).1 *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat (S.N.fr (.grid (i + 1) D.R.m))))
    (u : WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))) :
    u ∈ latO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) (S.N.latS (.chi i D.R.m) : Set _) (S.N.latT (.chi i D.R.m) : Set _) (fun _ => True) ↔
      actO _ _ (G.toPair (.chi i D.R.m) x y).1 (G.toPair (.chi i D.R.m) x y).2 u ∈
        latO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) (S.N.latS (.chi i D.R.m) : Set _) (S.N.latT (.chi i D.R.m) : Set _) (fun _ => True) := by
  have sdT := S.N.selfDual (X := .grid i D.R.m) ⟨by omega, rfl⟩
  have sdS := S.N.selfDual (X := .grid (i + 1) D.R.m) ⟨hi, rfl⟩
  obtain ⟨βT, hβT⟩ := GlobalTheory.AdelicFrame.exists_isFrame D.host.F _ sdT.1.fg sdT.1.span_eq_top
  obtain ⟨βS, hβS⟩ := GlobalTheory.AdelicFrame.exists_isFrame D.host.F _ sdS.1.fg sdS.1.span_eq_top
  have keep : ∀ {V : HSp D} (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)),
      Formalism.L2.DIV.IsFrame β Λ → ∀ X : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D),
      (∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ ↔ X.1 *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ) → X ∈ Formalism.L2.DIV.St β := by
    intro V Λ β hβ X hX
    refine (GlobalTheory.LevSplit.mem_St_iff β Λ hβ X).2 ⟨fun v hv => (hX v).1 hv, fun v hv => ?_⟩
    refine (hX _).2 ?_
    rw [mulVec_mulVec_inv]
    exact hv
  have stx := keep _ βT hβT _ hx
  have sty := keep _ βS hβS _ hy
  have sty' : Formalism.IndefR.Lev.finE (G.pS (.chi i D.R.m : Pair T)) (negGA _ y) ∈ Formalism.L2.DIV.St βS := sty
  exact GlobalTheory.StabLatInv.mem_latO_iff_actO_mem D (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))
    (S.N.latS (.chi i D.R.m)) (S.N.latT (.chi i D.R.m)) βS βT (isSelfDualC_neg sdS) sdT hβS hβT
    (negGA _ y) x sty' stx u

theorem keepLow (S : GridChoice W U) {t : T} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m))
    (hk : finG (G.V (.grid (j + 1) D.R.m)) k ∈ S.levRow t (j + 1) hj.le) (u : WO (G.pS (.chi j D.R.m : Pair T)) (G.pT (.chi j D.R.m : Pair T))) :
    u ∈ latO (G.pS (.chi j D.R.m : Pair T)) (G.pT (.chi j D.R.m : Pair T)) (S.N.latS (.chi j D.R.m) : Set _) (S.N.latT (.chi j D.R.m) : Set _) (fun _ => True) ↔
      actO _ _ (G.toPair (.chi j D.R.m) 1 (moved S j k)).1 (G.toPair (.chi j D.R.m) 1 (moved S j k)).2 u ∈
        latO (G.pS (.chi j D.R.m : Pair T)) (G.pT (.chi j D.R.m : Pair T)) (S.N.latS (.chi j D.R.m) : Set _) (S.N.latT (.chi j D.R.m) : Set _) (fun _ => True) := by
  have h1 : ∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat (S.N.fr (.grid j D.R.m))) ↔
      (Formalism.IndefR.Lev.finE (G.V (.grid j D.R.m)) 1).1 *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat (S.N.fr (.grid j D.R.m))) := by
    intro v
    have e0 : Formalism.IndefR.Lev.finE (G.V (.grid j D.R.m)) 1 = 1 := MonoidHom.map_one _
    have e1 : (Formalism.IndefR.Lev.finE (G.V (.grid j D.R.m)) 1).1 *ᵥ v = v := by rw [e0]; exact Matrix.one_mulVec v
    rw [e1]
  have h2 : moved S j k ∈ GfC (G.V (.grid (j + 1) D.R.m)) := ((S.N.u (.grid (j + 1) D.R.m))⁻¹ * k * S.N.u _).2
  have h3 := keepStd S j hj k hk
  exact keepPair S (i := j) (by omega) 1 (moved S j k) (one_mem _) h2 h1 h3 u

theorem keepHigh (S : GridChoice W U) {t : T} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m))
    (hk : finG (G.V (.grid (j + 1) D.R.m)) k ∈ S.levRow t (j + 1) hj.le) (u : WO (G.pS (.chi (j + 1) D.R.m : Pair T)) (G.pT (.chi (j + 1) D.R.m : Pair T))) :
    u ∈ latO (G.pS (.chi (j + 1) D.R.m : Pair T)) (G.pT (.chi (j + 1) D.R.m : Pair T)) (S.N.latS (.chi (j + 1) D.R.m) : Set _) (S.N.latT (.chi (j + 1) D.R.m) : Set _) (fun _ => True) ↔
      actO _ _ (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1).1 (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1).2 u ∈
        latO (G.pS (.chi (j + 1) D.R.m : Pair T)) (G.pT (.chi (j + 1) D.R.m : Pair T)) (S.N.latS (.chi (j + 1) D.R.m) : Set _) (S.N.latT (.chi (j + 1) D.R.m) : Set _) (fun _ => True) := by
  have h1 : ∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat (S.N.fr (.grid (j + 1 + 1) D.R.m))) ↔
      (Formalism.IndefR.Lev.finE (G.V (.grid (j + 1 + 1) D.R.m)) 1).1 *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat (S.N.fr (.grid (j + 1 + 1) D.R.m))) := by
    intro v
    have e0 : Formalism.IndefR.Lev.finE (G.V (.grid (j + 1 + 1) D.R.m)) 1 = 1 := MonoidHom.map_one _
    have e1 : (Formalism.IndefR.Lev.finE (G.V (.grid (j + 1 + 1) D.R.m)) 1).1 *ᵥ v = v := by rw [e0]; exact Matrix.one_mulVec v
    rw [e1]
  have h2 : moved S j k ∈ GfC (G.V (.grid (j + 1) D.R.m)) := ((S.N.u (.grid (j + 1) D.R.m))⁻¹ * k * S.N.u _).2
  have h3 := keepStd S j hj k hk
  exact keepPair S (i := j + 1) (by omega) (moved S j k) 1 h2 (one_mem _) h3 h1 u

theorem selfDual (S : GridChoice W U) {i : ℕ} (hi : i + 1 ≤ D.R.m) :
    IsSelfDualC (G.pS (.chi i D.R.m : Pair T)) (S.N.latS (.chi i D.R.m)) ∧ IsSelfDualC (G.pT (.chi i D.R.m : Pair T)) (S.N.latT (.chi i D.R.m)) :=
  ⟨isSelfDualC_neg (S.N.selfDual (X := .grid (i + 1) D.R.m) ⟨hi, rfl⟩), S.N.selfDual (X := .grid i D.R.m) ⟨by omega, rfl⟩⟩

theorem vacScalar (S : GridChoice W U) {i : ℕ} (hi : i + 1 ≤ D.R.m) (x : FinPt G (.grid i D.R.m)) (y : FinPt G (.grid (i + 1) D.R.m))
    (hΛ : ∀ u, u ∈ latO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) (S.N.latS (.chi i D.R.m) : Set _) (S.N.latT (.chi i D.R.m) : Set _) (fun _ => True) ↔
      actO _ _ (G.toPair (.chi i D.R.m) x y).1 (G.toPair (.chi i D.R.m) x y).2 u ∈
        latO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) (S.N.latS (.chi i D.R.m) : Set _) (S.N.latT (.chi i D.R.m) : Set _) (fun _ => True)) :
    ∃ c : ℂ, W.om (.chi i D.R.m) (G.toPair (.chi i D.R.m) x y) (S.Z.vac (.chi i D.R.m)) = c • S.Z.vac (.chi i D.R.m) :=
  GlobalTheory.T.chiArrowPair_moves_standardVacuum_by_scalar S hi x y hΛ

end GlobalTheory.RowVertexInv.FactorTheta

namespace GlobalTheory.RowVertexInv.FactorTheta

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem position_theta (S : GridChoice W U) {t : T} {e : AE D} (d : PureDat G t)
    (hd : (∀ j, (d.1 j).e = e ∧ (d.1 j).z = 1) ∧ ∀ i, (d.2 i).e = e ∧ (d.2 i).z = 1)
    (hv : (∀ j, S.Z.HasVec (d.1 j)) ∧ ∀ i, S.Z.HasVec (d.2 i)) (a : Fin D.R.m ⊕ Fin D.R.m) :
    IsThetaAt W.ψ (symplO _ _) (heisO W.ψ _ _) e
      (latO (G.pS (positionPair t D.R.m a)) (G.pT (positionPair t D.R.m a)) (S.N.latS (positionPair t D.R.m a) : Set _)
        (S.N.latT (positionPair t D.R.m a) : Set _) fun _ => True) 1 (S.Z.vac (positionPair t D.R.m a)) (fnOf d a) (vecOf S d a) := by
  have key : ∀ {p : Pair T} (x : FinDatum G t p), x.e = e → x.z = 1 → S.Z.HasVec x →
      IsThetaAt W.ψ (symplO _ _) (heisO W.ψ _ _) e
        (latO (G.pS p) (G.pT p) (S.N.latS p : Set _) (S.N.latT p : Set _) fun _ => True) 1 (S.Z.vac p) x.fn (S.Z.vec x) := by
    intro p x hxe hxz hx
    obtain ⟨f, hf⟩ := hx
    have h1 : S.Z.vec x = f := by
      rw [Normal.vec, FinDatum.vec_eq W hf, hxz]
      have h2 : W.om p (1, 1) = 1 := map_one _
      rw [h2]; rfl
    rw [h1, ← hxe]; exact hf
  rcases a with j | i
  · exact key (d.1 j) (hd.1 j).1 (hd.1 j).2 (hv.1 j)
  · exact key (d.2 i) (hd.2 i).1 (hd.2 i).2 (hv.2 i)

theorem scalar_ne_zero {p : Pair T} (g : GA D (G.pS p) × GA D (G.pT p)) {c : ℂ} {f : WO (G.pS p) (G.pT p) → ℂ}
    (hf : f ≠ 0) (h : W.om p g f = c • f) : c ≠ 0 := by
  intro hc
  apply hf
  have e1 : W.om p g⁻¹ (W.om p g f) = f := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  rw [h, hc, zero_smul, map_zero] at e1
  exact e1.symm

theorem vac_ne_zero (S : GridChoice W U) {i : ℕ} (hi : i + 1 ≤ D.R.m) : S.Z.vac (.chi i D.R.m) ≠ 0 := by
  intro h0
  obtain ⟨⟨p, hp⟩, hn⟩ := (S.Z.vac_is (.chi i D.R.m) ⟨hi, rfl⟩).2.norm
  have := hn p hp
  simp [nrm2, h0] at this

theorem vecOf_eq_intertwiner : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} {Φ : G.Datum} {β : CosFam G t} {τ : PureDat G t →₀ ℂ}, S.IsExpansion t Φ β τ → (∀ d ∈ τ.support, (∀ j, S.Z.HasVec (d.1 j)) ∧ ∀ i, S.Z.HasVec (d.2 i)) → ∀ (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m)), finG (G.V (.grid (j + 1) D.R.m)) k ∈ S.levRow t (j + 1) hj.le → ∃ (c₁ c₂ : ℂ) (Tm : ∀ a, FactorFn G t a →ₗ[ℂ] FactorFn G t a), W.om (.chi j D.R.m) (G.toPair (.chi j D.R.m) 1 (moved S j k)) (S.Z.vac (.chi j D.R.m)) = c₁ • S.Z.vac (.chi j D.R.m) ∧ W.om (.chi (j + 1) D.R.m) (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1) (S.Z.vac (.chi (j + 1) D.R.m)) = c₂ • S.Z.vac (.chi (j + 1) D.R.m) ∧ ∀ d ∈ τ.support, ∀ a, vecOf S d a = Tm a (fnOf d a) ∧ moveV S j hj k (vecOf S d) a = Tm a (scaleAt j hj c₁ c₂ a • movFn S j hj k (fnOf d) a) := by
  intro D T L sc G W U S t Φ β τ hexp hvec j hj k hk
  classical
  obtain ⟨e, he, hsupp, -⟩ := hexp
  have hee : e * e = e := GlobalTheory.PlaceDatum.idemSum_mul_self he
  have hinf : infPart D e = 0 := GlobalTheory.PlaceDatum.infPart_idemSum he
  let Tm : ∀ a, FactorFn G t a →ₗ[ℂ] FactorFn G t a := fun a =>
    Classical.epsilon (IsPlaceModel W.ψ (symplO _ _) (heisO W.ψ _ _) e
      (latO (G.pS (positionPair t D.R.m a)) (G.pT (positionPair t D.R.m a)) (S.N.latS (positionPair t D.R.m a) : Set _)
        (S.N.latT (positionPair t D.R.m a) : Set _) fun _ => True) 1 (S.Z.vac (positionPair t D.R.m a)))
  have hth : ∀ d ∈ τ.support, ∀ a, IsThetaAt W.ψ (symplO _ _) (heisO W.ψ _ _) e
      (latO (G.pS (positionPair t D.R.m a)) (G.pT (positionPair t D.R.m a)) (S.N.latS (positionPair t D.R.m a) : Set _)
        (S.N.latT (positionPair t D.R.m a) : Set _) fun _ => True) 1 (S.Z.vac (positionPair t D.R.m a)) (fnOf d a) (vecOf S d a) :=
    fun d hd a => position_theta S d ⟨fun j' => ⟨((hsupp d hd).1 j').2.1, ((hsupp d hd).1 j').2.2⟩,
      fun i => ⟨((hsupp d hd).2 i).2.1, ((hsupp d hd).2 i).2.2⟩⟩ (hvec d hd) a
  have hTm : ∀ d ∈ τ.support, ∀ a, IsPlaceModel W.ψ (symplO _ _) (heisO W.ψ _ _) e
      (latO (G.pS (positionPair t D.R.m a)) (G.pT (positionPair t D.R.m a)) (S.N.latS (positionPair t D.R.m a) : Set _)
        (S.N.latT (positionPair t D.R.m a) : Set _) fun _ => True) 1 (S.Z.vac (positionPair t D.R.m a)) (Tm a) ∧
      vecOf S d a = Tm a (fnOf d a) := by
    intro d hd a
    have h := hth d hd a
    have hs := Classical.epsilon_spec h.1
    exact ⟨hs, h.2 _ hs⟩
  have hj1 : j + 1 ≤ D.R.m := by omega
  have hj2 : j + 1 + 1 ≤ D.R.m := by omega
  obtain ⟨c₁, hc₁⟩ := vacScalar S hj1 1 ((S.N.u _)⁻¹ * k * S.N.u _) (keepLow S j hj k hk)
  obtain ⟨c₂, hc₂⟩ := vacScalar S hj2 ((S.N.u _)⁻¹ * k * S.N.u _) 1 (keepHigh S j hj k hk)
  refine ⟨c₁, c₂, Tm, hc₁, hc₂, fun d hd a => ⟨(hTm d hd a).2, ?_⟩⟩
  by_cases h2 : a = .inr ⟨j + 1, hj⟩
  · subst h2
    have e1 : moveV S j hj k (vecOf S d) (.inr ⟨j + 1, hj⟩) = W.om (.chi (j + 1) D.R.m)
        (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1) (vecOf S d (.inr ⟨j + 1, hj⟩)) := by
      unfold moveV; exact Function.update_self _ _ _
    have e2 : scaleAt j hj c₁ c₂ (.inr ⟨j + 1, hj⟩) = c₂ := by unfold scaleAt; exact Function.update_self _ _ _
    have e3 : movFn S j hj k (fnOf d) (.inr ⟨j + 1, hj⟩) = fun x => fnOf d (.inr ⟨j + 1, hj⟩)
        (actO _ _ (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1)⁻¹.1 (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1)⁻¹.2 x) := by
      unfold movFn; exact Function.update_self _ _ _
    rw [e1, e2, e3]
    exact om_theta_eq (W.om_is _ (by simp only [Pair.InRange, Pair.big, Node.InRange]; omega)) hee hinf
      (selfDual S hj2).1 (selfDual S hj2).2 (S.Z.vac_is (.chi (j + 1) D.R.m) ⟨hj2, rfl⟩).2.theta _ (keepHigh S j hj k hk)
      (scalar_ne_zero _ (vac_ne_zero S hj2) hc₂) hc₂ (hTm d hd (.inr ⟨j + 1, hj⟩)).1 (hth d hd (.inr ⟨j + 1, hj⟩))
  by_cases h1 : a = .inr ⟨j, by omega⟩
  · subst h1
    have hne : (Sum.inr ⟨j, by omega⟩ : Fin D.R.m ⊕ Fin D.R.m) ≠ .inr ⟨j + 1, hj⟩ := by simp
    have e1 : moveV S j hj k (vecOf S d) (.inr ⟨j, by omega⟩) = W.om (.chi j D.R.m)
        (G.toPair (.chi j D.R.m) 1 (moved S j k)) (vecOf S d (.inr ⟨j, by omega⟩)) := by
      unfold moveV; exact (Function.update_of_ne hne _ _).trans (Function.update_self _ _ _)
    have e2 : scaleAt j hj c₁ c₂ (.inr ⟨j, by omega⟩) = c₁ := by
      unfold scaleAt; exact (Function.update_of_ne hne _ _).trans (Function.update_self _ _ _)
    have e3 : movFn S j hj k (fnOf d) (.inr ⟨j, by omega⟩) = fun x => fnOf d (.inr ⟨j, by omega⟩)
        (actO _ _ (G.toPair (.chi j D.R.m) 1 (moved S j k))⁻¹.1 (G.toPair (.chi j D.R.m) 1 (moved S j k))⁻¹.2 x) := by
      unfold movFn; exact (Function.update_of_ne hne _ _).trans (Function.update_self _ _ _)
    rw [e1, e2, e3]
    exact om_theta_eq (W.om_is _ (by simp only [Pair.InRange, Pair.big, Node.InRange]; omega)) hee hinf
      (selfDual S hj1).1 (selfDual S hj1).2 (S.Z.vac_is (.chi j D.R.m) ⟨hj1, rfl⟩).2.theta _ (keepLow S j hj k hk)
      (scalar_ne_zero _ (vac_ne_zero S hj1) hc₁) hc₁ (hTm d hd (.inr ⟨j, by omega⟩)).1 (hth d hd (.inr ⟨j, by omega⟩))
  · have e1 : moveV S j hj k (vecOf S d) a = vecOf S d a := by
      unfold moveV; exact (Function.update_of_ne h2 _ _).trans (Function.update_of_ne h1 _ _)
    have e2 : scaleAt j hj c₁ c₂ a = 1 := by
      unfold scaleAt; exact (Function.update_of_ne h2 _ _).trans (Function.update_of_ne h1 _ _)
    have e3 : movFn S j hj k (fnOf d) a = fnOf d a := by
      unfold movFn; exact (Function.update_of_ne h2 _ _).trans (Function.update_of_ne h1 _ _)
    rw [e1, e2, e3, one_smul]
    exact (hTm d hd a).2

end GlobalTheory.RowVertexInv.FactorTheta
