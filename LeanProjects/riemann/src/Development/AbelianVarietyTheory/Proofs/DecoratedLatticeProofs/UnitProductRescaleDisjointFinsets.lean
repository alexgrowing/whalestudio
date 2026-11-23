import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotBadPrimeBase
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.StepVectorLiftPairFlagLevelRealizedChain
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilRepThetaDatumHalfEqSmul
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TypePlacesLocalDatumBlockTriangularLaw
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotentsStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StepVecSum

section Mat

variable {κ : Type} [CommRing κ] {a b : ℕ}

theorem topL_mul_right (y : Matrix (Fin b) (Fin a) κ) (s : Matrix (Fin a) (Fin a) κ) :
    topL a (y * s) = topL a y * s := by
  ext p q
  rw [Matrix.mul_apply]
  unfold topL
  by_cases hp : p.val < b
  · rw [dif_pos ⟨hp, q.2⟩, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun l _ => by rw [dif_pos ⟨hp, l.2⟩]
  · rw [dif_neg fun h => hp h.1]
    exact (Finset.sum_eq_zero fun l _ => by rw [dif_neg fun h => hp h.1, zero_mul]).symm

theorem lowZero_mul_right {y : Matrix (Fin b) (Fin a) κ} (hy : LowZero a y) (s : Matrix (Fin a) (Fin a) κ) :
    LowZero a (y * s) := by
  intro p q hp _
  rw [Matrix.mul_apply]
  exact Finset.sum_eq_zero fun l _ => by rw [hy p l hp l.2, zero_mul]

theorem lowerRightBlock_mul_blockTriangular {r t : ℕ} (ha : r ≤ a) {x y : GL (Fin a) κ} (hx : x ∈ blockTri (blkOf r t)) (hy : y ∈ blockTri (blkOf r t)) :
    upperLeftBlock ha (x * y) = upperLeftBlock ha x * upperLeftBlock ha y :=
  extendMatrixByIdentityAlongIndices_mul _ (blockTri_blkOf_le r t hx) (blockTri_blkOf_le r t hy)

theorem lowerRightBlock_inv_blockTriangular {r t : ℕ} (ha : r ≤ a) {x : GL (Fin a) κ} (hx : x ∈ blockTri (blkOf r t)) :
    upperLeftBlock ha x⁻¹ = (upperLeftBlock ha x)⁻¹ :=
  extendOne_inv _ (blockTri_blkOf_le r t hx)

end Mat

section Dat

open GlobalTheory.StepLaw.TypeDatum

variable {D : D7} {a b r t j : ℕ} (ha : r ≤ a) (Pg Q : Finset (Pl D.host.E)) (P : LevelP Pg r ℂ)
  (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (ξ χj : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
  (y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP))

theorem omegaG_of_top (g : ∀ PP : ↥Pg, GL (Fin a) (kP PP.1)) (h1 : ∀ PP ∈ Pg, LowZero a (y PP))
    (h2 : ∀ PP : ↥Pg, (g PP).val = topL a (y PP.1)) (h3 : ∀ PP : ↥Pg, g PP ∈ blockTri (blkOf r t))
    (h4 : (fun PP => upperLeftBlock ha (g PP)) ∈ P.H) :
    omegaG (datY a r t j ha Pg Q P χ ξ Frm.B) χj y =
      ((P.chi ⟨_, h4⟩ * ∏ PP : ↥Pg, ((∏ c ∈ Finset.range j, χ (c + 1) PP.1 (dBlk (blkOf r t) (c + 1) (g PP))) *
        (χj PP.1 (Matrix.GeneralLinearGroup.det (g PP)))⁻¹) : ℂˣ) : ℂ) := by
  unfold omegaG
  split_ifs with h
  · have e : h.2.choose = g := funext fun PP => Units.ext ((h.2.choose_spec.1 PP).trans (h2 PP).symm)
    have e2 : (datY a r t j ha Pg Q P χ ξ Frm.B).P.chi ⟨fun PP => upperLeftBlock (datY a r t j ha Pg Q P χ ξ Frm.B).hr (h.2.choose PP),
        h.2.choose_spec.2.2⟩ = P.chi ⟨_, h4⟩ := congrArg P.chi (Subtype.ext (funext fun PP => congrArg (upperLeftBlock ha) (congrFun e PP)))
    rw [e2]
    simp only [e, Finset.prod_mul_distrib, Units.val_mul, Units.coe_prod, Units.val_inv_eq_inv_val, mul_assoc]
    rfl
  · exact absurd ⟨h1, g, h2, h3, h4⟩ h

theorem omegaG_sum [Fintype P.H] (G : P.H → ∀ PP : Pl D.host.E, GL (Fin a) (kP PP))
    (hG : ∀ p, ∀ PP ∈ Pg, G p PP ∈ blockTri (blkOf r t)) (hr : ∀ p, ∀ PP : ↥Pg, upperLeftBlock ha (G p PP.1) = p.1 PP) :
    omegaG (datY a r t j ha Pg Q P χ ξ Frm.B) χj y =
      ∑ p : P.H, (((P.chi p * ∏ PP ∈ Pg, ∏ c ∈ Finset.range j, χ (c + 1) PP (dBlk (blkOf r t) (c + 1) (G p PP)))⁻¹ *
        ∏ PP ∈ Pg, χj PP (Matrix.GeneralLinearGroup.det (G p PP)) : ℂˣ) : ℂ) *
        omegaG (datY a r t j ha Pg Q (LevelP.triv Pg r ℂ) χ ξ Frm.B) χj (fun PP => y PP * (G p PP).val) := by
  have back : ∀ (p : P.H) (g : ∀ PP : ↥Pg, GL (Fin a) (kP PP.1)), (∀ PP : ↥Pg, IsTop t ha (y PP.1 * (G p PP.1).val) (g PP)) →
      (∀ PP ∈ Pg, LowZero a (y PP)) ∧ (∀ PP : ↥Pg, (g PP * (G p PP.1)⁻¹).val = topL a (y PP.1)) ∧
      (∀ PP : ↥Pg, g PP * (G p PP.1)⁻¹ ∈ blockTri (blkOf r t)) ∧ (fun PP => upperLeftBlock ha (g PP * (G p PP.1)⁻¹)) = (p.1)⁻¹ := by
    intro p g hg
    have e : ∀ PP, y PP = y PP * (G p PP).val * ((G p PP)⁻¹).val := fun PP => by
      rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
    refine ⟨fun PP hP => ?_, fun PP => ?_, fun PP => Subgroup.mul_mem _ (hg PP).2.2.1 (Subgroup.inv_mem _ (hG p _ PP.2)),
      funext fun PP => ?_⟩
    · rw [e PP]; exact lowZero_mul_right (hg ⟨PP, hP⟩).1 _
    · rw [e PP.1, topL_mul_right, ← (hg PP).2.1, Units.val_mul]
    · rw [lowerRightBlock_mul_blockTriangular ha (hg PP).2.2.1 (Subgroup.inv_mem _ (hG p _ PP.2)), (hg PP).2.2.2, one_mul, lowerRightBlock_inv_blockTriangular ha (hG p _ PP.2), hr]
      rfl
  by_cases h : (∀ PP ∈ Pg, LowZero a (y PP)) ∧ ∃ g : ∀ PP : ↥Pg, GL (Fin a) (kP PP.1),
      (∀ PP : ↥Pg, (g PP).val = topL a (y PP.1)) ∧ (∀ PP : ↥Pg, g PP ∈ blockTri (blkOf r t)) ∧ (fun PP => upperLeftBlock ha (g PP)) ∈ P.H
  · obtain ⟨h1, g, h2, h3, h4⟩ := h
    rw [omegaG_of_top ha Pg Q P χ ξ χj y g h1 h2 h3 h4, Finset.sum_eq_single (⟨_, h4⟩ : P.H)⁻¹]
    · set p : P.H := (⟨_, h4⟩ : P.H)⁻¹ with hp
      have ht : ∀ PP : ↥Pg, IsTop t ha (y PP.1 * (G p PP.1).val) (g PP * G p PP.1) := fun PP =>
        ⟨lowZero_mul_right (h1 _ PP.2) _, by rw [topL_mul_right, ← h2, Units.val_mul], Subgroup.mul_mem _ (h3 PP) (hG p _ PP.2), by
          rw [lowerRightBlock_mul_blockTriangular ha (h3 PP) (hG p _ PP.2), hr]; exact mul_inv_cancel _⟩
      rw [omegaG_of_isTop ha Pg Q χ ξ χj _ _ ht, ← Units.val_mul]
      congr 1
      rw [hp, map_inv, ← hp, ← Finset.prod_coe_sort Pg, ← Finset.prod_coe_sort Pg]
      have e1 : ∀ PP : ↥Pg, ∏ c ∈ Finset.range j, χ (c + 1) PP.1 (dBlk (blkOf r t) (c + 1) (g PP * G p PP.1)) =
          (∏ c ∈ Finset.range j, χ (c + 1) PP.1 (dBlk (blkOf r t) (c + 1) (g PP))) *
          ∏ c ∈ Finset.range j, χ (c + 1) PP.1 (dBlk (blkOf r t) (c + 1) (G p PP.1)) := fun PP => by
        rw [← Finset.prod_mul_distrib]
        exact Finset.prod_congr rfl fun c _ => by rw [diag_block_det_mul (h3 PP) (hG p _ PP.2), map_mul]
      simp only [e1, map_mul, mul_inv, inv_inv, Finset.prod_mul_distrib, Finset.prod_inv_distrib]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel
    · intro p _ hp
      rw [omegaG_of_not ha Pg Q χ ξ χj _ ?_, mul_zero]
      rintro ⟨g', hg'⟩
      obtain ⟨-, b2, -, b4⟩ := back p g' hg'
      have b5 : (p.1)⁻¹ = fun PP => upperLeftBlock ha (g PP) :=
        b4.symm.trans (funext fun PP => congrArg (upperLeftBlock ha) (Units.ext ((b2 PP).trans (h2 PP).symm)))
      exact hp (Subtype.ext (inv_eq_iff_eq_inv.1 b5))
    · exact fun h => absurd (Finset.mem_univ _) h
  · have h0 : omegaG (datY a r t j ha Pg Q P χ ξ Frm.B) χj y = 0 := dif_neg h
    rw [h0]
    refine (Finset.sum_eq_zero fun p _ => ?_).symm
    rw [omegaG_of_not ha Pg Q χ ξ χj _ ?_, mul_zero]
    rintro ⟨g', hg'⟩
    obtain ⟨b1, b2, b3, b4⟩ := back p g' hg'
    exact h ⟨b1, _, b2, b3, b4 ▸ P.H.inv_mem p.2⟩

end Dat

section Move

open GlobalTheory.ThetaMove GlobalTheory.SplitHecke

variable {D : D7} {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {χS χT : (AE D)ˣ →* Circle}
  {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}

theorem placeModel_move (hom : IsWeilDatumO ψ S T χS χT om) {e : AE D} {Λ : AddSubgroup (WO S T)} {f₀ : WO S T → ℂ}
    {Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)} (hTm : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ 1 f₀ Tm)
    (hth : ∀ Ψ, IsSBHalf e Λ Ψ → IsThetaFunO ψ S T (Tm Ψ))
    {g : GA D S} {h : GA D T} (hΛ : ∀ u, u ∈ Λ ↔ actO S T g h u ∈ Λ) {c : ℂ} (hf₀ : c • om (g, h) f₀ = f₀) :
    IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ 1 f₀
      (c • (om (g, h) ∘ₗ Tm ∘ₗ LinearMap.funLeft ℂ ℂ (actO S T g h))) := by
  have hT' : ∀ Ψ, (c • (om (g, h) ∘ₗ Tm ∘ₗ LinearMap.funLeft ℂ ℂ (actO S T g h))) Ψ =
      c • om (g, h) (Tm fun t => Ψ (actO S T g h t)) := fun Ψ => rfl
  refine ⟨fun Ψ hΨ x hx => ?_, fun Ψ hΨ y hy => ?_, ?_⟩
  · have hΨ' := isSBHalf_comp g h hΛ hΨ
    have h1 := hTm.trans _ hΨ' _ (isHalf_actO g⁻¹ h⁻¹ hx)
    simp only [act_add, act_act_inv] at h1
    rw [hT', hT', h1, hom.om_heis _ _ _ _ (hth _ hΨ'), act_act_inv, heisO_smul']
  · have hΨ' := isSBHalf_comp g h hΛ hΨ
    have h1 := hTm.modul _ hΨ' _ (isHalf_actO g⁻¹ h⁻¹ hy)
    have h2 : ∀ t, symplO S T t (actO S T g⁻¹ h⁻¹ y) = symplO S T (actO S T g h t) y := fun t => by
      rw [← symplO_actO S T g h, act_act_inv]
    simp only [h2] at h1
    rw [hT', hT', h1, hom.om_heis _ _ _ _ (hth _ hΨ'), act_act_inv, heisO_smul']
  · have h1 := hTm.vac
    rw [one_smul] at h1 ⊢
    have h2 : (fun t => halfInd e Λ (actO S T g h t)) = halfInd e Λ := funext (halfInd_act g h hΛ)
    rw [hT', h2, h1, hf₀]

theorem om_theta (hom : IsWeilDatumO ψ S T χS χT om) {e : AE D} {Λ : AddSubgroup (WO S T)} {f₀ Φ f : WO S T → ℂ}
    {Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)} (hTm : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ 1 f₀ Tm)
    (hth : ∀ Ψ, IsSBHalf e Λ Ψ → IsThetaFunO ψ S T (Tm Ψ))
    (hΘ : IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ 1 f₀ Φ f)
    {g : GA D S} {h : GA D T} (hΛ : ∀ u, u ∈ Λ ↔ actO S T g h u ∈ Λ) {c : ℂ} (hf₀ : om (g, h) f₀ = c • f₀) :
    om (g, h) f = c • Tm fun t => Φ (actO S T g⁻¹ h⁻¹ t) := by
  have i1 : ∀ v, om (g⁻¹, h⁻¹) (om (g, h) v) = v := fun v => by
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, inv_mul_cancel, inv_mul_cancel, Prod.mk_one_one, map_one,
      Module.End.one_apply]
  have i2 : ∀ v, om (g, h) (om (g⁻¹, h⁻¹) v) = v := fun v => by
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_inv_cancel, mul_inv_cancel, Prod.mk_one_one, map_one,
      Module.End.one_apply]
  have hP := placeModel_move hom hTm hth (g := g⁻¹) (h := h⁻¹) (c := c)
    (fun u => by rw [hΛ (actO S T g⁻¹ h⁻¹ u), act_act_inv]) (by rw [← map_smul, ← hf₀, i1])
  have e2 : f = c • om (g⁻¹, h⁻¹) (Tm fun t => Φ (actO S T g⁻¹ h⁻¹ t)) := hΘ.2 _ hP
  rw [e2, map_smul, i2]

theorem idemSum_eq (V : HSp D) {e e' : AE D} {P : Finset (Pl D.host.E)} (h : IsIdemSum e P) (h' : IsIdemSum e' P) : e' = e := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := h
  obtain ⟨⟨es', hes', rfl⟩, -⟩ := h'
  exact Finset.sum_congr rfl fun PP hP =>
    (((GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).2.2.1 PP _ _ (Or.inl ⟨hes PP hP, rfl⟩)).2.2.2.1 _ _ (Or.inl ⟨hes' PP hP, rfl⟩)).1

end Move

theorem unit_product_rescale_disjoint_finsets {ι : Type} [DecidableEq ι] {Pg Q : Finset ι} (hd : Disjoint Pg Q) (l : ℂˣ) (c a x y z w : ι → ℂˣ)
    (hg : ∀ i ∈ Pg, c i = x i) (hq : ∀ i ∈ Q, c i = (y i)⁻¹) (hw : ∀ i ∈ Q, w i = y i * (z i)⁻¹) :
    (l * (∏ i ∈ Pg, a i) * ∏ i ∈ Q, (z i)⁻¹)⁻¹ * (∏ i ∈ Pg ∪ Q, c i) * ∏ i ∈ Q, w i =
      (l * ∏ i ∈ Pg, a i)⁻¹ * ∏ i ∈ Pg, x i := by
  rw [Finset.prod_union hd, Finset.prod_congr rfl hg, Finset.prod_congr rfl hq, Finset.prod_congr rfl hw]
  simp only [Finset.prod_mul_distrib, Finset.prod_inv_distrib]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

set_option maxHeartbeats 1000000 in

theorem stepVec_eq_sum : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (f₀ f f' : WO S T → ℂ), IsWeilDatumO ψ S T χS χT om → S.SigOK → T.SigOK → (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → IsSelfDualC S ΛS → IsSelfDualC T ΛT → IsFrame βS ΛS → IsFrame βT ΛT → ∀ (r t k : ℕ) (ha : r ≤ S.rank), S.rank = r + k * t → T.rank = r + (k + 1) * t → ∀ (Pg Q : Finset (Pl D.host.E)), Disjoint Pg Q → ∀ (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (P : LevelP Pg r ℂ) [Fintype P.H], IsStepVecOf ψ θ S T sS sT ΛS ΛT βS βT (datY S.rank r t k ha Pg Q (LevelP.triv Pg r ℂ) χ ξ Frm.B) (χ (k + 1)) Q ξ f₀ f → IsStepVecOf ψ θ S T sS sT ΛS ΛT βS βT (datY S.rank r t k ha Pg Q P χ ξ Frm.B) (χ (k + 1)) Q ξ f₀ f' → (∀ PP ∈ Pg, GlobalTheory.StepLaw.ResAt χS PP (χ (k + 1) PP)⁻¹ ∧ GlobalTheory.StepLaw.ResAt χT PP (χ (k + 1) PP)⁻¹) → (∀ PP ∈ Q, GlobalTheory.StepLaw.ResAt χS PP (ξ PP) ∧ GlobalTheory.StepLaw.ResAt χT PP (ξ PP)) → GlobalTheory.StepLaw.UnrOff χS (Pg ∪ Q) → GlobalTheory.StepLaw.UnrOff χT (Pg ∪ Q) → ∀ κ : P.H → GA D S, (∀ p : P.H, IsLevelLift S βS (datY S.rank r t k ha Pg Q (LevelP.triv Pg r ℂ) χ ξ Frm.B) p.1 (κ p)) → f' = ∑ p : P.H, (levChi S βS (datY S.rank r t k ha Pg Q P χ ξ Frm.B) (κ p))⁻¹ • om (κ p, 1) f := by
  intro D ψ θ S T χS χT om sS sT ΛS ΛT βS βT f₀ f f' hW kS kT cS cT dS dT fS fT r t k ha eS eT Pg Q hd χ ξ P _ hv hv' hG hQ uS uT
    κ hκ
  have hb : r ≤ T.rank := eT ▸ Nat.le_add_right _ _
  obtain ⟨hf, e, he, hΘ⟩ := hv
  obtain ⟨-, e', he2, hΘ'⟩ := hv'
  have he' : IsIdemSum e (Pg ∪ Q) := he
  obtain rfl : e' = e := idemSum_eq S he' he2
  obtain ⟨Tm, hTm⟩ := hΘ.1
  have hth := GlobalTheory.T.schrodingerIntertwiner_schwartzBruhat_isTheta D ψ hW.std S T ΛS ΛT dS dT e' (GlobalTheory.PlaceDatum.idemSum_mul_self he) (GlobalTheory.PlaceDatum.infPart_idemSum he) f₀
      hf.2.theta Tm hTm
  have one1 : finE T (1 : GA D T) = 1 := map_one (finE T)
  have sh : finE T (1 : GA D T) ∈ St βT := one1 ▸ one_mem _
  have r1 : ∀ PP, redFn βT PP (finE T (1 : GA D T)) = 1 := fun PP => by rw [one1, redFn_one]
  let a : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ := fun PP => if PP ∈ Pg then (χ (k + 1) PP)⁻¹ else ξ PP
  have a1 : ∀ PP ∈ Pg, a PP = (χ (k + 1) PP)⁻¹ := fun PP hP => if_pos hP
  have a2 : ∀ PP ∈ Q, a PP = ξ PP := fun PP hP => if_neg (Finset.disjoint_right.1 hd hP)
  have hres : ∀ PP ∈ Pg ∪ Q, GlobalTheory.StepLaw.ResAt χS PP (a PP) ∧ GlobalTheory.StepLaw.ResAt χT PP (a PP) := fun PP hP => by
    rcases Finset.mem_union.1 hP with hP | hP
    · rw [a1 PP hP]; exact hG PP hP
    · rw [a2 PP hP]; exact hQ PP hP
  have sg := fun p => parLev_St (hκ p).2.1
  have h2 := fun p => om_theta hW hTm hth hΘ (GlobalTheory.T.mem_homLattice_iff_frameStabilizer_act_mem D S T ΛS ΛT βS βT dS dT fS fT (κ p) 1 (sg p) sh)
    (GlobalTheory.StepVecLaw.om_vac hW kS kT cS cT dS dT fS fT hf he' (fun PP hP => (hres PP hP).1) (fun PP hP => (hres PP hP).2) uS uT
      (hκ p).1 (one_mem _) (sg p) sh)
  rw [hΘ'.2 Tm hTm, Finset.sum_congr rfl fun p _ => by rw [h2 p, smul_smul, ← map_smul], ← map_sum]
  congr 1
  funext x
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul]
  have i0 : ∀ p, IsHalf e' (actO S T (κ p)⁻¹ 1⁻¹ x) ↔ IsHalf e' x := fun p =>
    ⟨fun H => GlobalTheory.AdelicLatMove.actO_actO_inv S T (κ p) 1 x ▸ GlobalTheory.SplitHecke.isHalf_actO (κ p) 1 H,
      fun H => GlobalTheory.SplitHecke.isHalf_actO _ _ H⟩
  have i12 := fun p => GlobalTheory.T.frameMatrix_movedHom_integral_reductions D S T βS βT (κ p) 1 (sg p) sh x
  by_cases hx : IsHalf e' x ∧ IsIntM (frMapO S T βS βT x)
  · rw [if_pos hx, omegaG_sum (t := t) (j := k) ha Pg Q P χ ξ (χ (k + 1)) _ (fun p PP => redFn βS PP (finE S (κ p)))
      (fun p PP hP => parLev_g (hκ p).2.1 hP) (fun p PP => congrFun (hκ p).2.2 PP), Finset.sum_mul]
    refine Finset.sum_congr rfl fun p _ => ?_
    have hoQ := GlobalTheory.T.twistPlaceDatum_parabolic_move D _ _ r ha hb Q ξ 1 (fun PP => redFn βS PP (finE S (κ p))) (fun PP => redFn βT PP (finE T 1))
      (fun PP hP => ⟨parLev_q (hκ p).2.1 hP, by rw [r1]; exact one_mem _⟩) (fun PP => redM PP (frMapO S T βS βT x))
    rw [if_pos ⟨(i0 p).2 hx.1, (i12 p).1.2 hx.2⟩, funext ((i12 p).2 hx.2)]
    erw [hoQ]
    have hl : levChi S βS (datY S.rank r t k ha Pg Q P χ ξ Frm.B) (κ p) = ((P.chi p *
        (∏ PP ∈ Pg, ∏ c ∈ Finset.range k, χ (c + 1) PP (dBlk (blkOf r t) (c + 1) (redFn βS PP (finE S (κ p))))) *
        ∏ PP ∈ Q, (ξ PP (dBlk (blk2 r) 1 (redFn βS PP (finE S (κ p)))))⁻¹ : ℂˣ) : ℂ) := by
      have h : ext1 (datY S.rank r t k ha Pg Q P χ ξ Frm.B).P.H (datY S.rank r t k ha Pg Q P χ ξ Frm.B).P.chi
          (rTup βS (datY S.rank r t k ha Pg Q P χ ξ Frm.B) (finE S (κ p))) = P.chi p := by
        have h' : rTup βS (datY S.rank r t k ha Pg Q P χ ξ Frm.B) (finE S (κ p)) = p.1 := (hκ p).2.2
        rw [h']
        exact extendOne_of_mem _ p.2
      unfold levChi levFn
      rw [h]
      rfl
    have hy : (fun PP => ((redFn βT PP (finE T 1))⁻¹).val * redM PP (frMapO S T βS βT x) * (redFn βS PP (finE S (κ p))).val) =
        fun PP => redM PP (frMapO S T βS βT x) * (redFn βS PP (finE S (κ p))).val := funext fun PP => by
      rw [r1, inv_one, Units.val_one, Matrix.one_mul]
    rw [hl, hy, ← Units.val_inv_eq_inv_val, ← unit_product_rescale_disjoint_finsets hd (P.chi p)
      (fun PP => (a PP (Matrix.GeneralLinearGroup.det (redFn βS PP (finE S (κ p)))))⁻¹ *
        a PP (Matrix.GeneralLinearGroup.det (redFn βT PP (finE T 1)))) _ _
      (fun PP => ξ PP (Matrix.GeneralLinearGroup.det (redFn βS PP (finE S (κ p)))))
      (fun PP => ξ PP (dBlk (blk2 r) 1 (redFn βS PP (finE S (κ p)))))
      (fun PP => (ξ PP (Matrix.GeneralLinearGroup.det (redFn βS PP (finE S (κ p)))) *
        (ξ PP (dBlk (blk2 r) 1 (redFn βS PP (finE S (κ p)))))⁻¹ *
        ((ξ PP (Matrix.GeneralLinearGroup.det (redFn βT PP (finE T 1))))⁻¹ * ξ PP (dBlk (blk2 r) 1 (redFn βT PP (finE T 1))))) ^ (1 : ℤ))
      (fun PP hP => ?_) (fun PP hP => ?_) (fun PP hP => ?_)]
    · rw [Units.val_mul _ (∏ i ∈ Q, _), Units.val_mul _ (∏ i ∈ Pg ∪ Q, _)]
      exact (mul_assoc _ _ _).trans ((mul_assoc _ _ _).trans (congrArg _ (mul_left_comm _ _ _)))
    · rw [r1, map_one, map_one, mul_one, a1 PP hP]; exact inv_inv _
    · rw [r1, map_one, map_one, mul_one, a2 PP hP]
    · rw [r1, map_one, dBlk, dBlk, blockDiagonalExtendByOnePrimeField_one, map_one, inv_one, mul_one, mul_one, zpow_one]
  · rw [if_neg hx]
    refine (Finset.sum_eq_zero fun p _ => ?_).symm
    rw [if_neg fun H => hx ⟨(i0 p).1 H.1, (i12 p).1.1 H.2⟩, mul_zero]

end GlobalTheory.StepVecSum

end
