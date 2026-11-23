import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankWeightComponentEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricLevelLiftsExistStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelCharactersRamificationLevelPlaces
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PostOnGaLMemGoodPart
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitIdempotentPrimeProjectionCorrespondence
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceAdjointMatrixIsCoordinateEquivariant
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualCoordLatticeOfSelfDualFrameStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftBlockDiagReductionToFlagGroupStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MirabolicHyperplaneAverageSupportResidueGLStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl idem SplitProj IsIdemOf IsProjAt adjCo grpCo frCo)
open GlobalTheory.DownLift.GenSplit

noncomputable section

namespace GlobalTheory.DownLift.HypAvg

theorem residueEquiv : ∀ (D : D7) (v : FinPl D) (PP : Pl D.host.E) (red : OI v →+* kP PP), Function.Surjective red → (∀ a : OI v, red a = 0 ↔ Valued.v (a : Fv D.host.F v) < 1) → ∃ ρk : IsLocalRing.ResidueField (OI v) ≃+* kP PP, ∀ a : OI v, ρk (IsLocalRing.residue (OI v) a) = red a := by
  intro D v PP red hs hk
  have hker : RingHom.ker red = IsLocalRing.maximalIdeal (OI v) := by
    ext a
    rw [RingHom.mem_ker, hk]
    exact (Valuation.mem_maximalIdeal_iff (v := (Valued.v : Valuation (Fv D.host.F v) _))).symm
  exact ⟨(Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hs), fun a => rfl⟩

theorem exists_blockGL : ∀ (O : Type) [CommRing O] [IsLocalRing O] (r t n : ℕ) (hn : r + t = n) (M : Matrix (Fin r) (Fin r) O) (g₀ : GL (Fin r) (IsLocalRing.ResidueField O)), M.map (IsLocalRing.residue O) = (g₀ : Matrix (Fin r) (Fin r) (IsLocalRing.ResidueField O)) → ∃ h : GL (Fin n) O, (h : Matrix (Fin n) (Fin n) O) = (Matrix.fromBlocks M 0 0 (1 : Matrix (Fin t) (Fin t) O)).submatrix (rowIx hn).symm (rowIx hn).symm := by
  intro O _ _ r t n hn M g₀ hM
  have hd : IsLocalRing.residue O M.det = (g₀ : Matrix (Fin r) (Fin r) (IsLocalRing.ResidueField O)).det := by
    rw [← hM, RingHom.map_det]; rfl
  have hdet : IsUnit ((Matrix.fromBlocks M 0 0 (1 : Matrix (Fin t) (Fin t) O)).submatrix (rowIx hn).symm
      (rowIx hn).symm).det := by
    rw [Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one,
      ← IsLocalRing.residue_ne_zero_iff_isUnit, hd, ← Matrix.GeneralLinearGroup.val_det_apply]
    exact Units.ne_zero _
  exact ⟨Matrix.nonsingInvUnit _ hdet, rfl⟩

theorem ell_heisO_omegaInv : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.thP_ωP → ∀ (i : Fin D.R.m) (t : T) (ℓ : (WO (Vc D i) (Wc D i) → ℂ) →ₗ[ℂ] ℂ) (κ : GA D (Vc D i)) (c : ℂ), c ≠ 0 → (∀ φ', IsThetaFunO R.ψ (Vc D i) (Wc D i) φ' → ℓ (R.ωP i t (κ, 1) φ') = c * ℓ φ') → ∀ (u : WO (Vc D i) (Wc D i)) (f : WO (Vc D i) (Wc D i) → ℂ), IsThetaFunO R.ψ (Vc D i) (Wc D i) f → ℓ (heisO R.ψ (Vc D i) (Wc D i) u (R.ωP i t (κ⁻¹, 1) f)) = c⁻¹ * ℓ (heisO R.ψ (Vc D i) (Wc D i) (actO (Vc D i) (Wc D i) κ 1 u) f) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R hω i t ℓ κ c hc hsc u f hf
  have hW := hω i t
  have e1 : actO (Vc D i) (Wc D i) κ⁻¹ 1 (actO (Vc D i) (Wc D i) κ 1 u) = u := by
    simpa using GlobalTheory.SplitHecke.actO_inv_actO (S := Vc D i) (T := Wc D i) κ 1 u
  have e2 := hW.om_heis κ⁻¹ 1 (actO (Vc D i) (Wc D i) κ 1 u) f hf
  rw [e1] at e2
  rw [← e2]
  have hth := hW.om_pres (κ⁻¹, 1) _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hW.std hf (actO (Vc D i) (Wc D i) κ 1 u))
  have e3 := hsc _ hth
  have e4 : R.ωP i t (κ, 1) (R.ωP i t (κ⁻¹, 1) (heisO R.ψ (Vc D i) (Wc D i) (actO (Vc D i) (Wc D i) κ 1 u) f)) =
      heisO R.ψ (Vc D i) (Wc D i) (actO (Vc D i) (Wc D i) κ 1 u) f := by
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_inv_cancel, mul_one]
    show R.ωP i t 1 _ = _
    rw [map_one]; rfl
  rw [e4] at e3
  rw [e3, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]

theorem actO_sigma : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → ∀ (i : Fin D.R.m) (v : FinPl D) (φ : SplitProj D v) (e : Formalism.L2.Theta.AE D), IsIdemOf φ e → ∀ (σ : Matrix (Fin D.R.r ⊕ Fin D.R.t) (Fin D.R.r) (Fv D.host.F v) → WO (Vc D i) (Wc D i)), (∀ X, IsHalf (cA D e) (σ X) ∧ coR R i φ (σ X) = X) → ∀ (κ : GA D (Vc D i)) (M : Matrix (Fin D.R.r ⊕ Fin D.R.t) (Fin D.R.r ⊕ Fin D.R.t) (Fv D.host.F v)), ((grpCo φ (Vc D i) (frCo φ (R.βV i)) κ : GL (Fin (Vc D i).rank) (Fv D.host.F v)) : Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) (Fv D.host.F v)) = M.submatrix (rowIx (rank_V i)).symm (rowIx (rank_V i)).symm → ∀ X, actO (Vc D i) (Wc D i) κ 1 (σ X) = σ (M * X) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R hL i v φ e he σ hσ κ M hM X
  have sdV := GlobalTheory.T.isSelfDualCoordLattice_of_selfDualFrame D _ _ _ _ (hL.βV i)
  have sdW := GlobalTheory.T.isSelfDualCoordLattice_of_selfDualFrame D _ _ _ _ (hL.βW i)
  obtain ⟨hco, hact⟩ := GlobalTheory.PlaceTensor.adjCo_isCoord D (Vc D i) (Wc D i) _ _ sdV sdW v φ e he (frCo φ (R.βV i))
    (frCo φ (R.βW i))
  have hhalf : IsHalf (cA D e) (actO (Vc D i) (Wc D i) κ 1 (σ X)) := GlobalTheory.SplitHecke.isHalf_actO κ 1 (hσ X).1
  apply hco.2.1.injOn hhalf (hσ (M * X)).1
  have h1 := hact κ⁻¹ 1 (σ X)
  simp only [inv_inv, inv_one] at h1
  have hg1 : grpCo φ (Wc D i) (frCo φ (R.βW i)) 1 = 1 := by
    unfold grpCo; simp
  have key : ∀ y, adjCo φ (Vc D i) (Wc D i) (frCo φ (R.βV i)) (frCo φ (R.βW i)) y =
      (coR R i φ y).submatrix (rowIx (rank_V i)).symm (finCongr (rank_weight_component_eq i)).symm := by
    intro y
    unfold coR co
    rw [Matrix.submatrix_submatrix]
    ext j k
    simp
  rw [h1, GlobalTheory.PlaceTensor.AdjCoord.grpCo_inv, inv_inv, hg1, Units.val_one, Matrix.mul_one, key (σ (M * X)),
    (hσ _).2, key (σ X), (hσ X).2, hM, Matrix.submatrix_mul_equiv]

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem liftsV (R : RealDat D A Ks) (h : R.toLevCh.Is A.μ0) (i : Fin D.R.m) (t : T) :
    LiftsExist (Vc D i) (R.βV i) (R.datVt i t) := by
  obtain ⟨c, hc⟩ := h.βV i
  refine GlobalTheory.T.parahoricLevel_liftsExist _ _ _ _ _ hc (fun PP hP PP' hP' => ?_)
    (GlobalTheory.LevelRamif.ramif_at_levels D T R.toLevCh A.μ0 h t i).1
  obtain ⟨k, hk⟩ := (h.Pg PP).1 hP
  rcases hP' with hP' | hP'
  · obtain ⟨k', hk'⟩ := (h.Pg PP').1 hP'
    exact GlobalTheory.ProjectedLift.not_isConjPl R.C.P hk hk'
  · intro hc
    obtain ⟨q, hq, hm, hne⟩ := GlobalTheory.LevelRamif.exists_prime_mem (h.Q_pl t) hP'
    exact GlobalTheory.LevelRamif.not_two_primes PP' hq (D.host.g_prime k) (hne k) hm
      (GlobalTheory.LevelRamif.natCast_mem_conj hc (GlobalTheory.LevelRamif.typePrime_mem hk))

theorem termAt (R : RealDat D A Ks) (hL : R.toLevCh.Is A.μ0) (hω : R.thP_ωP) (i : Fin D.R.m) (t : T)
    (PP : Pl D.host.E) (hPP : PP ∈ R.Pg) {v : FinPl D} (φ : SplitProj D v) (e : Formalism.L2.Theta.AE D) (he : IsIdemOf φ e)
    (red : OI v →+* kP PP) (ρk : IsLocalRing.ResidueField (OI v) ≃+* kP PP)
    (hρ : ∀ a : OI v, ρk (IsLocalRing.residue (OI v) a) = red a) (hAct : ActAt R i t PP φ e red)
    {Sb : Finset (FinPl D)} (hv : v ∈ Sb)
    (σ : Matrix (Fin D.R.r ⊕ Fin D.R.t) (Fin D.R.r) (Fv D.host.F v) → WO (Vc D i) (Wc D i))
    (hσ : ∀ X, IsHalf (cA D e) (σ X) ∧ coR R i φ (σ X) = X)
    (ℓ : (WO (Vc D i) (Wc D i) → ℂ) →ₗ[ℂ] ℂ) (hℓ : InvForm R.ψ (Vc D i) (Wc D i) e ℓ)
    (f : WO (Vc D i) (Wc D i) → ℂ) (hf : IsThetaFunO R.ψ (Vc D i) (Wc D i) f) (a' : Fin D.R.r → kP PP)
    (lift : GL (Fin D.R.r) (IsLocalRing.ResidueField (OI v)) → Matrix (Fin D.R.r) (Fin D.R.r) (OI v))
    (hlift : ∀ g, (lift g).map (IsLocalRing.residue (OI v)) =
      (g : Matrix (Fin D.R.r) (Fin D.R.r) (IsLocalRing.ResidueField (OI v))))
    (g : G) (hg : mirC R i ⟨PP, hPP⟩ a' false 1 g ≠ 0) :
    ∃ κ : GA D (Vc D i), IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) (R.eG g) κ ∧ SuppIn Sb (Vc D i) κ ∧
      ∀ X, mirC R i ⟨PP, hPP⟩ a' false 1 g * (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) κ)⁻¹ *
          ℓ (heisO R.ψ (Vc D i) (Wc D i) (σ X) (R.ωP i t (κ⁻¹, 1) f)) =
        ℓ (heisO R.ψ (Vc D i) (Wc D i) (σ ((Matrix.fromBlocks
          (lift (Matrix.GeneralLinearGroup.map ρk.symm.toRingHom (R.eG g ⟨PP, hPP⟩))) 0 0
          (1 : Matrix (Fin D.R.t) (Fin D.R.t) (OI v))).map (algebraMap (OI v) (Fv D.host.F v)) * X)) f) := by
  classical
  have hc : (∀ PP' : R.Pg, PP' ≠ ⟨PP, hPP⟩ → R.eG g PP' = 1) ∧
      ∀ x, a' ⬝ᵥ x = 0 → ((R.eG g ⟨PP, hPP⟩ : GL (Fin D.R.r) (kP PP)) : Matrix (Fin D.R.r) (Fin D.R.r) (kP PP)).mulVec x = x := by
    by_contra hc
    exact hg (by unfold mirC; rw [if_neg (by simpa using hc)])
  have hm : mirC R i ⟨PP, hPP⟩ a' false 1 g =
      ((R.chi ((i : ℕ) + 1) PP (Matrix.GeneralLinearGroup.det (R.eG g ⟨PP, hPP⟩)) : ℂˣ) : ℂ) := by
    unfold mirC; rw [if_pos (by simpa using hc), zpow_one]
  set g₀ := Matrix.GeneralLinearGroup.map ρk.symm.toRingHom (R.eG g ⟨PP, hPP⟩) with hg₀
  obtain ⟨hh, hhv⟩ := exists_blockGL (OI v) D.R.r D.R.t _ (rank_V i) (lift g₀) g₀ (hlift g₀)
  obtain ⟨κ, hSupp, hGf, hSt, hgrp, hred, hoth, hsc⟩ := hAct hh
  have hlr : (lift g₀).map red = ((R.eG g ⟨PP, hPP⟩ : GL (Fin D.R.r) (kP PP)) : Matrix (Fin D.R.r) (Fin D.R.r) (kP PP)) := by
    ext j k
    have e1 := congrFun (congrFun (hlift g₀) j) k
    simp only [Matrix.map_apply] at e1 ⊢
    rw [← hρ, e1, hg₀]
    simp [Matrix.GeneralLinearGroup.map]
  have hredM : ((redFn (R.βV i) PP (finE (Vc D i) κ) : GL (Fin (Vc D i).rank) (kP PP)) :
      Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) (kP PP)) =
      (Matrix.fromBlocks ((R.eG g ⟨PP, hPP⟩ : GL (Fin D.R.r) (kP PP)) : Matrix (Fin D.R.r) (Fin D.R.r) (kP PP)) 0 0
        (1 : Matrix (Fin D.R.t) (Fin D.R.t) (kP PP))).submatrix (rowIx (rank_V i)).symm (rowIx (rank_V i)).symm := by
    rw [hred]
    show (hh : Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) (OI v)).map red = _
    rw [hhv, ← Matrix.submatrix_map, Matrix.fromBlocks_map, hlr, Matrix.map_zero _ (map_zero red),
      Matrix.map_zero _ (map_zero red), Matrix.map_one _ (map_zero red) (map_one red)]
  obtain ⟨hLift, hchi⟩ := GlobalTheory.T.lift_blockDiag_reduction_to_flagGroup D G Pl0 T A Ks R i t PP hPP g hc.1 κ hGf hSt hredM hoth
  refine ⟨κ, hLift, suppIn_of_suppAt he hv hSupp, fun X => ?_⟩
  have hdet : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map red hh) =
      Matrix.GeneralLinearGroup.det (R.eG g ⟨PP, hPP⟩) := by
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply, ← hred, hredM,
      Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]
  set c : ℂ := ((R.chi ((i : ℕ) + 1) PP (Matrix.GeneralLinearGroup.det (R.eG g ⟨PP, hPP⟩)) : ℂˣ) : ℂ) with hcdef
  have hc0 : c ≠ 0 := Units.ne_zero _
  have key := ell_heisO_omegaInv D G Pl0 T A Ks R hω i t ℓ κ c hc0
    (fun φ' hφ' => by rw [hsc ℓ hℓ φ' hφ', hdet]) (σ X) f hf
  have hco := actO_sigma D G Pl0 T A Ks R hL i v φ e he σ hσ κ
    ((Matrix.fromBlocks (lift g₀) 0 0 (1 : Matrix (Fin D.R.t) (Fin D.R.t) (OI v))).map
      (algebraMap (OI v) (Fv D.host.F v))) (by
        rw [hgrp]
        show (hh : Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) (OI v)).map (algebraMap (OI v) (Fv D.host.F v)) = _
        rw [hhv, Matrix.submatrix_map]) X
  rw [key, hco, hchi, hm, inv_one, mul_one, ← mul_assoc, mul_inv_cancel₀ hc0, one_mul]

theorem avg_schrodinger_hyperplane : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.thP_ωP → ∀ (i : Fin D.R.m) (t : T) (PP : Pl D.host.E), PP ∈ R.Pg → ∀ (v : FinPl D) (φ : SplitProj D v) (e : Formalism.L2.Theta.AE D), IsProjAt φ PP → IsIdemOf φ e → ∀ (red : OI v →+* kP PP), Function.Surjective red → (∀ a : OI v, red a = 0 ↔ Valued.v (a : Fv D.host.F v) < 1) → ActAt R i t PP φ e red → ∀ (Sb : Finset (FinPl D)), v ∈ Sb → ∀ (σ : Matrix (Fin D.R.r ⊕ Fin D.R.t) (Fin D.R.r) (Fv D.host.F v) → WO (Vc D i) (Wc D i)), (∀ X, IsHalf (cA D e) (σ X) ∧ coR R i φ (σ X) = X) → ∀ (ℓ : (WO (Vc D i) (Wc D i) → ℂ) →ₗ[ℂ] ℂ), InvForm R.ψ (Vc D i) (Wc D i) e ℓ → ∀ (f : WO (Vc D i) (Wc D i) → ℂ), IsThetaFunO R.ψ (Vc D i) (Wc D i) f → CleanIn R i t Sb f → ∀ a : Fin D.R.r → IsLocalRing.ResidueField (OI v), a ≠ 0 → ∀ (lift : GL (Fin D.R.r) (IsLocalRing.ResidueField (OI v)) → Matrix (Fin D.R.r) (Fin D.R.r) (OI v)), (∀ g, (lift g).map (IsLocalRing.residue (OI v)) = (g : Matrix (Fin D.R.r) (Fin D.R.r) (IsLocalRing.ResidueField (OI v)))) → ∀ X : Matrix (Fin D.R.r ⊕ Fin D.R.t) (Fin D.R.r) (Fv D.host.F v), ∑ᶠ g ∈ {g : GL (Fin D.R.r) (IsLocalRing.ResidueField (OI v)) | ∀ w, a ⬝ᵥ w = 0 → (g : Matrix (Fin D.R.r) (Fin D.R.r) (IsLocalRing.ResidueField (OI v))).mulVec w = w}, ℓ (heisO R.ψ (Vc D i) (Wc D i) (σ ((Matrix.fromBlocks (lift g) 0 0 (1 : Matrix (Fin D.R.t) (Fin D.R.t) (OI v))).map (algebraMap (OI v) (Fv D.host.F v)) * X)) f) = 0 := by
  intro D G _ _ Pl0 T A Ks _ _ _ R hL hω i t PP hPP v φ e hproj he red hsurj hker hAct Sb hv σ hσ ℓ hℓ f hf hclean a ha
    lift hlift X
  classical
  obtain ⟨ρk, hρ⟩ := residueEquiv D v PP red hsurj hker
  have ha' : (fun j => ρk (a j)) ≠ 0 := fun h => ha (funext fun j => ρk.injective (by simpa using congrFun h j))
  have hOver : Over PP v := ((GlobalTheory.SplitIdemDict.idem_dictionary D).2 v φ PP hproj).1
  choose κ₀ hκ₀ using fun g : G => liftsV R hL i t (R.eG g)
  have hG := fun (g : G) (hg : mirC R i ⟨PP, hPP⟩ (fun j => ρk (a j)) false 1 g ≠ 0) =>
    termAt R hL hω i t PP hPP φ e he red ρk hρ hAct hv σ hσ ℓ hℓ f hf (fun j => ρk (a j)) lift hlift g hg
  let κ : G → GA D (Vc D i) := fun g =>
    if hg : mirC R i ⟨PP, hPP⟩ (fun j => ρk (a j)) false 1 g ≠ 0 then (hG g hg).choose else κ₀ g
  have hκ : ∀ g (hg : mirC R i ⟨PP, hPP⟩ (fun j => ρk (a j)) false 1 g ≠ 0), κ g = (hG g hg).choose :=
    fun g hg => dif_pos hg
  have hLifts : IsLifts R i t κ := fun g => by
    by_cases hg : mirC R i ⟨PP, hPP⟩ (fun j => ρk (a j)) false 1 g ≠ 0
    · rw [hκ g hg]; exact (hG g hg).choose_spec.1
    · have : κ g = κ₀ g := dif_neg hg
      rw [this]; exact hκ₀ g
  have hSupp : ∀ g, mirC R i ⟨PP, hPP⟩ (fun j => ρk (a j)) false 1 g ≠ 0 → SuppIn Sb (Vc D i) (κ g) :=
    fun g hg => by rw [hκ g hg]; exact (hG g hg).choose_spec.2.1
  have h0 := hclean ⟨PP, hPP⟩ (fun j => ρk (a j)) ha' false 1 (Or.inl rfl) ⟨v, hv, hOver⟩ κ hLifts hSupp
  have h1 := congrArg (fun φ' => ℓ (heisO R.ψ (Vc D i) (Wc D i) (σ X) φ')) h0
  simp only [avgW, GlobalTheory.SplitScalar.heisO_sum, GlobalTheory.SplitScalar.heisO_smul, map_sum, map_smul, smul_eq_mul] at h1
  set Fn : GL (Fin D.R.r) (IsLocalRing.ResidueField (OI v)) → ℂ := fun g =>
    ℓ (heisO R.ψ (Vc D i) (Wc D i) (σ ((Matrix.fromBlocks (lift g) 0 0 (1 : Matrix (Fin D.R.t) (Fin D.R.t) (OI v))).map
      (algebraMap (OI v) (Fv D.host.F v)) * X)) f) with hFn
  rw [← GlobalTheory.T.mirabolicHyperplaneAverage_support_residueGL D G Pl0 T A Ks R i PP hPP v ρk a Fn, finsum_mem_def, finsum_eq_sum_of_fintype]
  have hz : heisO R.ψ (Vc D i) (Wc D i) (σ X) (0 : WO (Vc D i) (Wc D i) → ℂ) = 0 := by
    funext w; simp [heisO]
  rw [hz, map_zero] at h1
  refine (Finset.sum_congr rfl fun g _ => ?_).trans h1
  by_cases hg : mirC R i ⟨PP, hPP⟩ (fun j => ρk (a j)) false 1 g ≠ 0
  · rw [Set.indicator_of_mem (show g ∈ {g : G | mirC R i ⟨PP, hPP⟩ (fun j => ρk (a j)) false 1 g ≠ 0} from hg), hκ g hg]
    exact ((hG g hg).choose_spec.2.2 X).symm
  · rw [Set.indicator_of_notMem (show g ∉ {g : G | mirC R i ⟨PP, hPP⟩ (fun j => ρk (a j)) false 1 g ≠ 0} from hg)]
    rw [not_not.1 hg, zero_mul, zero_mul]

end GlobalTheory.DownLift.HypAvg

end
