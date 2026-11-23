import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankWeightComponentEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaEqZeroOfReal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceAdjointMatrixIsCoordinateEquivariant
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualCoordLatticeOfSelfDualFrameStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetTwoDiagBlocksPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSumOfNoConj
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl idem SplitProj IsIdemOf IsProjAt adjCo grpCo frCo)
open GlobalTheory.DownLift.GenSplit

namespace GlobalTheory.DownLift.GenSplit

theorem actO_sigma_of_grpCo : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → ∀ (i : Fin D.R.m) (v : FinPl D) (φ : SplitProj D v) (e : Formalism.L2.Theta.AE D), IsIdemOf φ e → ∀ (σ : Matrix (Fin D.R.r ⊕ Fin D.R.t) (Fin D.R.r) (Fv D.host.F v) → WO (Vc D i) (Wc D i)), (∀ X, IsHalf (cA D e) (σ X) ∧ coR R i φ (σ X) = X) → ∀ (κ : GA D (Vc D i)) (h : GL (Fin D.R.r ⊕ Fin D.R.t) (OI v)) (h' : GL (Fin (Vc D i).rank) (OI v)), (∀ a b, (h' : Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) (OI v)) (rowIx (rank_V i) a) (rowIx (rank_V i) b) = (h : Matrix (Fin D.R.r ⊕ Fin D.R.t) (Fin D.R.r ⊕ Fin D.R.t) (OI v)) a b) → grpCo φ (Vc D i) (frCo φ (R.βV i)) κ = Matrix.GeneralLinearGroup.map (algebraMap (OI v) (Fv D.host.F v)) h' → ∀ X : Matrix (Fin D.R.r ⊕ Fin D.R.t) (Fin D.R.r) (Fv D.host.F v), actO (Vc D i) (Wc D i) κ 1 (σ X) = σ ((h : Matrix (Fin D.R.r ⊕ Fin D.R.t) (Fin D.R.r ⊕ Fin D.R.t) (OI v)).map (algebraMap (OI v) (Fv D.host.F v)) * X) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R hL i v φ e he σ hσ κ h h' hh' hgrp X
  have sdV := GlobalTheory.T.isSelfDualCoordLattice_of_selfDualFrame D _ _ _ _ (hL.βV i)
  have sdW := GlobalTheory.T.isSelfDualCoordLattice_of_selfDualFrame D _ _ _ _ (hL.βW i)
  have hco := (GlobalTheory.PlaceTensor.adjCo_isCoord D (Vc D i) (Wc D i) _ _ sdV sdW v φ e he
    (frCo φ (R.βV i)) (frCo φ (R.βW i))).1
  have hinj := hco.2.1.injOn
  have h1 : IsHalf (cA D e) (actO (Vc D i) (Wc D i) κ 1 (σ X)) := GlobalTheory.SplitHecke.isHalf_actO κ 1 (hσ X).1
  have h2 : IsHalf (cA D e) (σ ((h : Matrix (Fin D.R.r ⊕ Fin D.R.t) (Fin D.R.r ⊕ Fin D.R.t) (OI v)).map (algebraMap (OI v) (Fv D.host.F v)) * X)) := (hσ _).1
  refine hinj h1 h2 ?_
  have ha : adjCo φ (Vc D i) (Wc D i) (frCo φ (R.βV i)) (frCo φ (R.βW i)) (actO (Vc D i) (Wc D i) κ 1 (σ X)) =
      (grpCo φ (Vc D i) (frCo φ (R.βV i)) κ).val * adjCo φ (Vc D i) (Wc D i) (frCo φ (R.βV i)) (frCo φ (R.βW i)) (σ X) := by
    have := GlobalTheory.PlaceTensor.AdjCoord.adjCo_actO φ (Vc D i) (Wc D i) (frCo φ (R.βV i)) (frCo φ (R.βW i)) κ⁻¹ 1 (σ X)
    rw [inv_inv, inv_one, GlobalTheory.PlaceTensor.AdjCoord.grpCo_inv, inv_inv] at this
    rw [this]
    have g1 : grpCo φ (Wc D i) (frCo φ (R.βW i)) 1 = 1 := by
      unfold grpCo; rw [map_one, map_one, mul_one, inv_mul_cancel]
    rw [g1, Units.val_one, Matrix.mul_one]
  have hc : ∀ x, coR R i φ x = (adjCo φ (Vc D i) (Wc D i) (frCo φ (R.βV i)) (frCo φ (R.βW i)) x).submatrix (rowIx (rank_V i)) (finCongr (rank_weight_component_eq i)) := fun x => rfl
  have hX : coR R i φ (actO (Vc D i) (Wc D i) κ 1 (σ X)) = coR R i φ (σ ((h : Matrix (Fin D.R.r ⊕ Fin D.R.t) (Fin D.R.r ⊕ Fin D.R.t) (OI v)).map (algebraMap (OI v) (Fv D.host.F v)) * X)) := by
    rw [(hσ _).2, hc, ha, hgrp, ← Matrix.submatrix_mul_equiv _ _ _ (rowIx (rank_V i)), ← hc, (hσ X).2]
    congr 1
    ext a b
    simp [Matrix.GeneralLinearGroup.map, hh']
  refine Matrix.ext fun a b => ?_
  have e1 := congrFun (congrFun hX ((rowIx (rank_V i)).symm a)) ((finCongr (rank_weight_component_eq i)).symm b)
  simpa [hc] using e1

theorem levG_levChi_of_red : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → ∀ (i : Fin D.R.m) (t : T) (PP : Pl D.host.E), PP ∈ R.Pg → ∀ (κ : GA D (Vc D i)), κ ∈ GfC (Vc D i) → finE (Vc D i) κ ∈ St (R.βV i) → ∀ (g : GL (Fin (Vc D i).rank) (kP PP)), redFn (R.βV i) PP (finE (Vc D i) κ) = g → (∀ PP', PP' ∈ R.Pg ∨ PP' ∈ R.Q t → PP' ≠ PP → redFn (R.βV i) PP' (finE (Vc D i) κ) = 1) → (∀ a b : Fin D.R.r, (g : Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) (kP PP)) (rowIx (rank_V i) (Sum.inl a)) (rowIx (rank_V i) (Sum.inl b)) = (1 : Matrix (Fin D.R.r) (Fin D.R.r) (kP PP)) a b) → (∀ (a : Fin D.R.t) (b : Fin D.R.r), (g : Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) (kP PP)) (rowIx (rank_V i) (Sum.inr a)) (rowIx (rank_V i) (Sum.inl b)) = 0) → κ ∈ levG (Vc D i) (R.βV i) (R.datVt i t) ∧ levChi (Vc D i) (R.βV i) (R.datVt i t) κ = ((R.chi ((i : ℕ) + 1) PP (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹ := by
  intro D G _ _ Pl0 T A Ks _ _ _ R hL i t PP hPP κ hGf hSt g hg hoth hg1 hg2
  have rV : (Vc D i).rank = D.R.r + D.R.t := (rank_V i).symm
  have hdisj : PP ∉ R.Q t := Finset.disjoint_left.1 (Formalism.IndefR.Fin.disjoint_Pg_Q R.toLevCh hL t) hPP
  have hlo : ∀ a : Fin (Vc D i).rank, (ha : a.val < D.R.r) → a = rowIx (rank_V i) (Sum.inl ⟨a.val, ha⟩) := by
    intro a ha; ext; simp [rowIx]
  have hhi : ∀ a : Fin (Vc D i).rank, (ha : D.R.r ≤ a.val) →
      a = rowIx (rank_V i) (Sum.inr ⟨a.val - D.R.r, by have := a.2; omega⟩) := by
    intro a ha; ext; simp [rowIx]; omega
  have htri : g ∈ blockTri (blkOf D.R.r D.R.t) := by
    intro a b hab
    have ha : D.R.r ≤ a.val := by
      by_contra h; push_neg at h
      simp [blkOf, h] at hab
    have hb : b.val < D.R.r := by
      by_contra h; push_neg at h
      have h1 := a.2; have h2 := b.2
      have e1 : (a.val - D.R.r) / D.R.t = 0 := Nat.div_eq_of_lt (by omega)
      have e2 : (b.val - D.R.r) / D.R.t = 0 := Nat.div_eq_of_lt (by omega)
      simp [blkOf, not_lt.2 ha, not_lt.2 h, e1, e2] at hab
    rw [hhi a ha, hlo b hb]
    exact hg2 _ _
  have hr1 : upperLeftBlock (r_le_V i) g = 1 := by
    apply Units.ext
    rw [upper_block_val_submatrix _ (blockTri_blkOf_le _ _ htri), Units.val_one]
    refine Matrix.ext fun a b => ?_
    simp only [Matrix.submatrix_apply]
    have ea : Fin.castLE (r_le_V i) a = rowIx (rank_V i) (Sum.inl a) := by ext; simp [rowIx]
    have eb : Fin.castLE (r_le_V i) b = rowIx (rank_V i) (Sum.inl b) := by ext; simp [rowIx]
    rw [ea, eb, hg1]
  have hred : ∀ PP', PP' ∈ R.Pg ∨ PP' ∈ R.Q t → redFn (R.βV i) PP' (finE (Vc D i) κ) = 1 ∨ PP' = PP := by
    intro PP' h
    by_cases e : PP' = PP
    · exact Or.inr e
    · exact Or.inl (hoth PP' h e)
  have hrT : rTup (R.βV i) (R.datVt i t) (finE (Vc D i) κ) = 1 := by
    funext PP'
    show upperLeftBlock (r_le_V i) (redFn (R.βV i) PP'.1 (finE (Vc D i) κ)) = 1
    rcases hred PP'.1 (Or.inl PP'.2) with h | h
    · rw [h]; exact blockDiagonalExtendByOnePrimeField_one _ _
    · rw [h, hg, hr1]
  have hpar : finE (Vc D i) κ ∈ parLev D.sp.cm (Vc D i).gram (R.βV i) (R.datVt i t) := by
    refine mem_parLev.2 ⟨GlobalTheory.LevSplit.finE_mem_UA _ _, hSt, fun PP' hP' => ?_, fun PP' hP' => ?_⟩
    · rcases hred PP' (Or.inl hP') with h | h
      · rw [h]; exact Subgroup.one_mem _
      · rw [h, hg]; exact htri
    · rcases hred PP' (Or.inr hP') with h | h
      · rw [h]; exact Subgroup.one_mem _
      · exact absurd (h ▸ hP') hdisj
  refine ⟨⟨hGf, hpar, ?_⟩, ?_⟩
  · show rTup (R.βV i) (R.datVt i t) (finE (Vc D i) κ) ∈ (R.datVt i t).P.H
    rw [hrT]; exact Subgroup.one_mem _
  · have hQ : ∏ PP' ∈ (R.datVt i t).Q, (R.datVt i t).xq PP' (dBlk (blk2 (R.datVt i t).r) 1 (redFn (R.βV i) PP' (finE (Vc D i) κ))) = 1 := by
      refine Finset.prod_eq_one fun PP' hP' => ?_
      rcases hred PP' (Or.inr hP') with h | h
      · rw [h, dBlk, blockDiagonalExtendByOnePrimeField_one, map_one]
      · exact absurd (h ▸ hP') hdisj
    have hdet : Matrix.GeneralLinearGroup.det g = dBlk (blkOf D.R.r D.R.t) 1 g := by
      rw [(GlobalTheory.T.det_twoDiagBlocks_properties _ _ _ D.R.t (r_le_V i) g).1 (blockTri_blkOf_le _ _ htri), hr1, map_one, one_mul,
        (GlobalTheory.T.det_twoDiagBlocks_properties _ _ _ D.R.t (r_le_V i) g).2.1 rV htri]
    have hG : ∏ PP' ∈ (R.datVt i t).Pg, ∏ c ∈ Finset.range (R.datVt i t).s, (R.datVt i t).cg (c + 1) PP'
        (dBlk (blkOf (R.datVt i t).r (R.datVt i t).t) (c + 1) (redFn (R.βV i) PP' (finE (Vc D i) κ))) =
        (R.chi ((i : ℕ) + 1) PP (Matrix.GeneralLinearGroup.det g))⁻¹ := by
      rw [Finset.prod_eq_single PP]
      · show ∏ c ∈ Finset.range 1, _ = _
        rw [Finset.prod_range_one, hg, hdet]
        rfl
      · intro PP' hP' hne
        rcases hred PP' (Or.inl hP') with h | h
        · refine Finset.prod_eq_one fun c _ => ?_
          rw [h, dBlk, blockDiagonalExtendByOnePrimeField_one, map_one]
        · exact absurd h hne
      · intro h; exact absurd hPP h
    unfold levChi levFn
    rw [hrT, blockDiagonalExtendByOnePrimeField_one, hQ, hG, one_mul, mul_one, Units.val_inv_eq_inv_val]

theorem heisO_smul_fun {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} (w : WO S T) (c : ℂ) (f : WO S T → ℂ) :
    heisO ψ S T w (c • f) = c • heisO ψ S T w f := by
  funext x; simp only [heisO, Pi.smul_apply, smul_eq_mul]; ring

theorem schrodinger_type_inv : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.thP_ωP → ∀ (i : Fin D.R.m) (t : T) (PP : Pl D.host.E), PP ∈ R.Pg → ∀ (v : FinPl D) (φ : SplitProj D v) (e : Formalism.L2.Theta.AE D), IsProjAt φ PP → IsIdemOf φ e → ∀ (red : OI v →+* kP PP), Function.Surjective red → (∀ a : OI v, red a = 0 ↔ Valued.v (a : Fv D.host.F v) < 1) → ActAt R i t PP φ e red → ∀ (Sb : Finset (FinPl D)), v ∈ Sb → ∀ (σ : Matrix (Fin D.R.r ⊕ Fin D.R.t) (Fin D.R.r) (Fv D.host.F v) → WO (Vc D i) (Wc D i)), (∀ X, IsHalf (cA D e) (σ X) ∧ coR R i φ (σ X) = X) → ∀ (ℓ : (WO (Vc D i) (Wc D i) → ℂ) →ₗ[ℂ] ℂ), InvForm R.ψ (Vc D i) (Wc D i) e ℓ → ∀ (f : WO (Vc D i) (Wc D i) → ℂ), TypeIn R i t Sb f → ∀ (ϖ : OI v), Irreducible ϖ → ∀ h : GL (Fin D.R.r ⊕ Fin D.R.t) (OI v), (∀ a b, (h : Matrix (Fin D.R.r ⊕ Fin D.R.t) (Fin D.R.r ⊕ Fin D.R.t) (OI v)) (Sum.inl a) (Sum.inl b) - (1 : Matrix (Fin D.R.r) (Fin D.R.r) (OI v)) a b ∈ Ideal.span {ϖ}) → (∀ a b, (h : Matrix (Fin D.R.r ⊕ Fin D.R.t) (Fin D.R.r ⊕ Fin D.R.t) (OI v)) (Sum.inr a) (Sum.inl b) ∈ Ideal.span {ϖ}) → ∀ X : Matrix (Fin D.R.r ⊕ Fin D.R.t) (Fin D.R.r) (Fv D.host.F v), ℓ (heisO R.ψ (Vc D i) (Wc D i) (σ ((h : Matrix (Fin D.R.r ⊕ Fin D.R.t) (Fin D.R.r ⊕ Fin D.R.t) (OI v)).map (algebraMap (OI v) (Fv D.host.F v)) * X)) f) = ℓ (heisO R.ψ (Vc D i) (Wc D i) (σ X) f) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R hL hω i t PP hPP v φ e hφ he red hsur hker hAct Sb hv σ hσ ℓ hℓ f hf ϖ hϖ h hh1 hh2 X
  let e' := rowIx (rank_V i)
  let h' : GL (Fin (Vc D i).rank) (OI v) := Units.map (Matrix.reindexAlgEquiv (OI v) (OI v) e').toMonoidHom h
  have hh' : ∀ a b, (h' : Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) (OI v)) (e' a) (e' b) =
      (h : Matrix (Fin D.R.r ⊕ Fin D.R.t) (Fin D.R.r ⊕ Fin D.R.t) (OI v)) a b := by
    intro a b
    simp [h', Matrix.reindexAlgEquiv_apply]
  obtain ⟨κ, hsupp, hGf, hSt, hgrp, hred', hoth, hact⟩ := hAct h'
  have hϖ0 : red ϖ = 0 := by
    haveI : PP.asIdeal.IsMaximal := PP.isMaximal
    letI : Field (kP PP) := Ideal.Quotient.field _
    have hmax : RingHom.ker red = IsLocalRing.maximalIdeal (OI v) :=
      IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective red hsur)
    have : ϖ ∈ RingHom.ker red := by
      rw [hmax]; exact (IsLocalRing.mem_maximalIdeal _).2 hϖ.not_isUnit
    exact this
  have hspan : ∀ x ∈ Ideal.span {ϖ}, red x = 0 := by
    intro x hx
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hx
    rw [map_mul, hϖ0, mul_zero]
  have hg1 : ∀ a b : Fin D.R.r, ((Matrix.GeneralLinearGroup.map red h' : GL (Fin (Vc D i).rank) (kP PP)) :
      Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) (kP PP)) (e' (Sum.inl a)) (e' (Sum.inl b)) =
      (1 : Matrix (Fin D.R.r) (Fin D.R.r) (kP PP)) a b := by
    intro a b
    have h0 := hspan _ (hh1 a b)
    rw [map_sub, sub_eq_zero] at h0
    rw [Matrix.GeneralLinearGroup.map_apply, hh', h0]
    by_cases hab : a = b
    · subst hab; simp
    · simp [Matrix.one_apply_ne hab]
  have hg2 : ∀ (a : Fin D.R.t) (b : Fin D.R.r), ((Matrix.GeneralLinearGroup.map red h' : GL (Fin (Vc D i).rank) (kP PP)) :
      Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) (kP PP)) (e' (Sum.inr a)) (e' (Sum.inl b)) = 0 := by
    intro a b
    rw [Matrix.GeneralLinearGroup.map_apply, hh']
    exact hspan _ (hh2 a b)
  obtain ⟨hmem, hchi⟩ := levG_levChi_of_red D G Pl0 T A Ks R hL i t PP hPP κ hGf hSt _ hred' hoth hg1 hg2
  have hSIn : SuppIn Sb (Vc D i) κ := suppIn_of_suppAt he hv hsupp
  have hW := hω i t
  have hTy := hf.2 κ hmem hSIn
  rw [hchi, inv_inv] at hTy
  have hx := actO_sigma_of_grpCo D G Pl0 T A Ks R hL i v φ e he σ hσ κ h h' hh' hgrp X
  have e1 := hW.om_heis κ 1 (σ X) f hf.1
  rw [hx, hTy, heisO_smul_fun] at e1
  have e2 := hact ℓ hℓ (heisO R.ψ (Vc D i) (Wc D i) (σ X) f)
    (GlobalTheory.TwistFactorCompare.isTheta_heisO hW.std hf.1 _)
  rw [e1, map_smul, smul_eq_mul] at e2
  exact mul_left_cancel₀ (Units.ne_zero _) e2

end GlobalTheory.DownLift.GenSplit
