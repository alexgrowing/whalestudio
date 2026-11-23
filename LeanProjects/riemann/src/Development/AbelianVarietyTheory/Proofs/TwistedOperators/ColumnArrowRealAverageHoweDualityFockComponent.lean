import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SumProdPartialEqZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentMulAddOneSubInverse
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ApplyAddInfRat
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentTwistedGroupEndomorphism
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatOIffOfSt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.VacMoveLow

variable {D : D7}

theorem halfInd_isSBHalf {S T : HSp D} (e : AE D) (Λ : AddSubgroup (WO S T)) : IsSBHalf e Λ (halfInd e Λ) := by
  refine ⟨fun x hx => ?_, 1, one_pos, fun u hu hu' x => ?_, fun x hx => ?_⟩
  · by_contra h; exact hx (if_neg fun h' => h h'.2)
  · rw [one_smul]
    have h1 : IsHalf e (x + u) ↔ IsHalf e x := forall₂_congr fun i j => by
      rw [Matrix.add_apply, mul_add, hu' i j, add_left_inj]
    exact halfInd_congr (and_congr (AddSubgroup.add_mem_cancel_right _ hu) h1)
  · rw [one_smul]; by_contra h; exact hx (if_neg fun h' => h h'.1)

theorem om_base_law {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hW : IsWeilDatumO ψ S T χS χT om)
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) {P : Finset (Pl D.host.E)} {e : AE D} (he : IsIdemSum e P)
    {f₀ : WO S T → ℂ} (hf : IsThetaFunO ψ S T f₀) (hv : IsLatVac (heisO ψ S T) (latO S T ΛS ΛT fun _ => True) f₀)
    {Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)}
    (hTm : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e (latO S T ΛS ΛT fun _ => True) 1 f₀ Tm) {h : GA D T}
    (hh : SuppAt e T h) :
    ∃ c : ℂ, om (1, h) f₀ = c • Tm fun x => halfInd e (latO S T ΛS ΛT fun _ => True) (actO S T 1⁻¹ h⁻¹ x) := by
  have he' : e * e = e := (GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he).idem
  have key := GlobalTheory.SplitLinear.splitLinearModel D ψ S T χS χT om hW ΛS ΛT hS hT P e he f₀ hf hv 1 one_ne_zero Tm hTm 1 h
    (GlobalTheory.SplitLinear.suppAt_one e S) hh _ _ (GlobalTheory.VecInv.isDetAt_detAt e he' S 1) (GlobalTheory.VecInv.isDetAt_detAt e he' T h)
    _ (halfInd_isSBHalf e _)
  have h0 : Tm (halfInd e (latO S T ΛS ΛT fun _ => True)) = f₀ := by simpa using hTm.vac
  rw [h0] at key
  refine ⟨(splitFacO χS χT (GlobalTheory.VecInv.detAt e he' S 1) (GlobalTheory.VecInv.detAt e he' T h) : ℂ) *
    (GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.modFac S T (GlobalTheory.VecInv.detAt e he' S 1) (GlobalTheory.VecInv.detAt e he' T h) : ℂ), key.trans ?_⟩
  rw [← map_smul]
  rfl

end GlobalTheory.VacMoveLow

namespace GlobalTheory.VacMoveLow

variable {D : D7}

theorem compAt_fin {θ : InfFam D} {V : HSp D} {h : GA D V} (hh : h ∈ GfC V) (τ : D.what₂.Tau) :
    compAt θ τ (Formalism.L2.Theta.mt V h) = 1 := by
  have h1 : Formalism.UG.bc (infPart D) (matHom V h) = 1 := (GlobalTheory.UnitaryIdemCut.mem_GfC_iff V h).1 hh
  have h2 := congrArg Units.val h1
  ext i j
  have h3 := congrFun (congrFun h2 i) j
  simp only [compAt, Matrix.map_apply]
  have h4 : infPart D (Formalism.L2.Theta.mt V h i j) = (1 : Matrix (Fin V.rank) (Fin V.rank) _) i j := h3
  rw [h4, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem actO_one_one {S T : HSp D} (u : WO S T) : actO S T 1 1 u = u := by
  simp [actO, GlobalTheory.AdelicLatMove.mt_one]

theorem om_keep_vac {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hW : IsWeilDatumO ψ S T χS χT om) (hθ : IsInfFam θ)
    (kS : S.SigOK) (kT : T.SigOK) {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ}
    {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ} (cS : ∀ τ, IsCartanInv (gramAt D S τ) (sS τ))
    (cT : ∀ τ, IsCartanInv (gramAt D T τ) (sT τ))
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) {f : WO S T → ℂ}
    (hf : IsVacO ψ θ S T sS sT (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) f)
    {h : GA D T} (hh : h ∈ GfC T)
    (hk : ∀ u, u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) ↔
      actO S T 1 h u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True)) :
    ∃ c : ℂ, om (1, h) f = c • f := by
  have hf' := GlobalTheory.WeilVacMove.isVacO_om D ψ θ S T χS χT om hW hθ sS sS sT sT _ _ _ _ 1 h
    (fun τ => by rw [compAt_fin (one_mem _) τ, Matrix.mul_one, Matrix.one_mul])
    (fun τ => by rw [compAt_fin hh τ, Matrix.mul_one, Matrix.one_mul])
    (fun u => ⟨fun hu => ⟨actO S T 1 h⁻¹ u, (hk _).2 (by rw [← GlobalTheory.SplitLinear.actO_mul, mul_one, mul_inv_cancel, actO_one_one]; exact hu),
        by rw [← GlobalTheory.SplitLinear.actO_mul, mul_one, mul_inv_cancel, actO_one_one]⟩,
      fun ⟨u₀, hu₀, e⟩ => e ▸ (hk u₀).1 hu₀⟩) f hf
  obtain ⟨c, -, hc⟩ := GlobalTheory.VacUnique.vacUniqueO D ψ θ hf.1 hθ S T sS sT kS kT cS cT ΛS ΛT hS hT f _ hf hf'
  exact ⟨c, hc⟩

end GlobalTheory.VacMoveLow

namespace GlobalTheory.VacMoveLow

variable {D : D7}

theorem exists_cut_hom (V : HSp D) (r : AF D.host.F)
    (hb : algebraMap (AF D.host.F) (AE D) r * algebraMap (AF D.host.F) (AE D) r = algebraMap (AF D.host.F) (AE D) r) :
    ∃ κ : GA D V →* GA D V, ∀ g, Formalism.L2.Theta.mt V (κ g) = algebraMap (AF D.host.F) (AE D) r • Formalism.L2.Theta.mt V g +
      (1 - algebraMap (AF D.host.F) (AE D) r) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) := by
  obtain ⟨κ, hκ⟩ := GlobalTheory.UnitaryIdemCut.exists_cutHA (AF D.host.F) D.sp.cm.sig V.gram r hb
  refine ⟨κ, fun g => ?_⟩
  have := congrArg Units.val (hκ g)
  rw [GlobalTheory.UnitaryIdemCut.cutGL_val] at this
  exact this

theorem actO_cut_half {S T : HSp D} {b e : AE D} (hbe : b * e = 0) {g : GA D T}
    {M : Matrix (Fin T.rank) (Fin T.rank) (AE D)}
    (hg : Formalism.L2.Theta.mt T g = b • M + (1 - b) • (1 : Matrix (Fin T.rank) (Fin T.rank) (AE D))) {y : WO S T}
    (hy : IsHalf e y) : actO S T 1 g y = y := by
  have hby : ∀ i j, b * y i j = 0 := fun i j => by rw [← hy i j, ← mul_assoc, hbe, zero_mul]
  have h1 : actO S T 1 g y = (HMul.hMul (Formalism.L2.Theta.mt T g) (y : Matrix (Fin T.rank) (Fin S.rank) (AE D)) :
      Matrix (Fin T.rank) (Fin S.rank) (AE D)) := by
    simp [actO, GlobalTheory.AdelicLatMove.mt_one]
  rw [h1, hg, Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul]
  ext i j
  rw [Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, Matrix.mul_apply,
    Finset.mul_sum, Finset.sum_eq_zero fun k _ => by rw [mul_left_comm, hby, mul_zero], zero_add, sub_mul, one_mul,
    hby, sub_zero]

end GlobalTheory.VacMoveLow

namespace GlobalTheory.VacMoveLow

variable {D : D7}

theorem cut_mul_cut {n : Type} [Fintype n] [DecidableEq n] {a : AE D} (ha : a * a = a) (M : Matrix n n (AE D)) :
    (a • M + (1 - a) • (1 : Matrix n n (AE D))) * ((1 - a) • M + (1 - (1 - a)) • (1 : Matrix n n (AE D))) = M := by
  have h0 : a * (1 - a) = 0 := by rw [mul_sub, mul_one, ha, sub_self]
  have h0' : (1 - a) * a = 0 := by rw [mul_comm, h0]
  have h1 : (1 - a) * (1 - a) = 1 - a := by rw [sub_mul, one_mul, h0, sub_zero]
  rw [sub_sub_cancel]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.one_mul, Matrix.mul_one]
  simp only [smul_add, smul_smul, h0, h0', ha, h1, zero_smul, zero_add, add_zero]
  rw [← add_smul, sub_add_cancel, one_smul]

end GlobalTheory.VacMoveLow

namespace GlobalTheory.VacMoveLow

variable {D : D7}

set_option maxHeartbeats 1000000 in

theorem exists_cut_pair (V : HSp D) {e : AE D} (he : e * e = e) (hc : e * cA D e = 0) :
    ∃ κe κo : GA D V →* GA D V, (∀ g, g = κe g * κo g) ∧ (∀ g, SuppAt e V (κe g)) ∧ (∀ g ∈ GfC V, κo g ∈ GfC V) ∧
      (∀ g, Formalism.L2.Theta.mt V (κo g) = (1 - (e + cA D e)) • Formalism.L2.Theta.mt V g +
        (e + cA D e) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D))) ∧
      ∀ (S : HSp D) g (y : WO S V), IsHalf e y → actO S V 1 (κo g) y = y := by
  have hce : cA D e * cA D e = cA D e := by rw [← map_mul, he]
  have hec : cA D e * e = 0 := by rw [mul_comm]; exact hc
  obtain ⟨r, hr⟩ := GlobalTheory.PlaceModelSum.exists_add_conj e
  have hr1 : algebraMap (AF D.host.F) (AE D) (1 - r) = 1 - algebraMap (AF D.host.F) (AE D) r := by
    simp only [map_sub, map_one]
  have hrr : algebraMap (AF D.host.F) (AE D) r * algebraMap (AF D.host.F) (AE D) r =
      algebraMap (AF D.host.F) (AE D) r := by
    rw [hr, add_mul, mul_add, mul_add, he, hce, hc, hec, add_zero, zero_add]
  have hrr' : algebraMap (AF D.host.F) (AE D) (1 - r) * algebraMap (AF D.host.F) (AE D) (1 - r) =
      algebraMap (AF D.host.F) (AE D) (1 - r) := by
    rw [hr1, sub_mul, mul_sub, mul_sub, hrr, mul_one, one_mul, mul_one, sub_self, sub_zero]
  have hbe0 : algebraMap (AF D.host.F) (AE D) (1 - r) * e = 0 := by
    rw [map_sub, map_one, hr, sub_mul, add_mul, he, hec, one_mul, add_zero, sub_self]
  have hbe : (1 - algebraMap (AF D.host.F) (AE D) r) * e = 0 := by rw [← hr1]; exact hbe0
  obtain ⟨κe, hκe⟩ := exists_cut_hom V r hrr
  obtain ⟨κo, hκo⟩ := exists_cut_hom V (1 - r) hrr'
  rw [hr1] at hκo
  have hκo' : ∀ g, Formalism.L2.Theta.mt V (κo g) = (1 - (e + cA D e)) • Formalism.L2.Theta.mt V g +
      (e + cA D e) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) := fun g => by
    rw [hκo, ← hr, sub_sub_cancel]
  refine ⟨κe, κo, fun g => ?_, fun g i j => ?_, fun g hg => ?_, hκo', fun S g y hy => ?_⟩
  · refine Subtype.ext (Units.ext ?_)
    change Formalism.L2.Theta.mt V g = Formalism.L2.Theta.mt V (κe g * κo g)
    rw [GlobalTheory.AdelicLatMove.mt_mul, hκe, hκo, cut_mul_cut hrr]
  · have e1 : Formalism.L2.Theta.mt V (κe g) - 1 = algebraMap (AF D.host.F) (AE D) r • (Formalism.L2.Theta.mt V g - 1) := by
      rw [hκe, smul_sub, sub_smul, one_smul]; abel
    rw [e1, Matrix.smul_apply, smul_eq_mul, ← mul_assoc, ← hr, hrr]
  · have e1 : matHom V (κo g) = GlobalTheory.UnitaryIdemCut.cutGL _ hrr' (matHom V g) :=
      Units.ext (by rw [GlobalTheory.UnitaryIdemCut.cutGL_val, hr1]; exact hκo g)
    rw [GlobalTheory.UnitaryIdemCut.mem_GfC_iff, e1]
    exact GlobalTheory.UnitaryIdemCut.bc_cutGL_eq_one _ _ _ ((GlobalTheory.UnitaryIdemCut.mem_GfC_iff _ _).1 hg)
  · exact actO_cut_half hbe (hκo g) hy

theorem halfInd_move {S T : HSp D} {e : AE D} (Λ : AddSubgroup (WO S T)) {h he ho : GA D T} (hs : h = he * ho)
    (hfix : ∀ w, IsHalf e w → actO S T 1 ho w = w) (hfix' : ∀ w, IsHalf e w → actO S T 1 ho⁻¹ w = w) (x : WO S T) :
    halfInd e Λ (actO S T 1⁻¹ he⁻¹ x) = halfInd e Λ (actO S T 1⁻¹ h⁻¹ x) := by
  apply halfInd_congr
  have e0 : actO S T 1⁻¹ (ho⁻¹ * he⁻¹) x = actO S T 1 ho⁻¹ (actO S T 1⁻¹ he⁻¹ x) := by
    rw [← GlobalTheory.SplitLinear.actO_mul, one_mul]
  rw [hs, mul_inv_rev, e0]
  constructor
  · rintro ⟨h1, h2⟩
    rw [hfix' _ h2]
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    have e2 := hfix _ h2
    rw [← GlobalTheory.SplitLinear.actO_mul, mul_one, mul_inv_cancel, actO_one_one] at e2
    rw [← e2] at h1 h2
    exact ⟨h1, h2⟩

end GlobalTheory.VacMoveLow

namespace GlobalTheory.ExpansionInvariance

theorem vac_move_low : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T},
    t ∈ U → ∀ {Φ : G.Datum} {β : CosFam G t} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.top (j + 1))),
    finG (G.V (.top (j + 1))) k ∈ S.levTop t Φ β (j + 1) hj → ∀ e : AE D, IsIdemSum e (locPl G t) →
    ∀ Tm : (WO (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)) → ℂ) →ₗ[ℂ] (WO (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)) → ℂ),
      IsPlaceModel W.ψ (symplO _ _) (heisO W.ψ _ _) e (stdLatO S (.top t j)) 1 (S.Z.vac (.top t j)) Tm →
      ∃ c : ℂ, W.om (.top t j) (1, ((((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1))))) (S.Z.vac (.top t j)) =
        c • Tm fun x => halfInd e (stdLatO S (.top t j)) (actO _ _ 1⁻¹ ((((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1))))⁻¹ x) := by
  intro D T L sc G W U S t htU Φ β j hj k hk e he Tm hTm
  have hIn : (Pair.top t j : Pair T).InRange D.R.m := by
    show j + 1 ≤ D.R.m
    omega
  have hDef : GlobalTheory.FunObj.DefPair D.R.m (Pair.top t j : Pair T) := by
    show j + 1 ≤ D.R.m
    omega
  have hW := W.om_is _ hIn
  have hvac := S.Z.vac_is _ hDef
  have hSd : IsSelfDualC (G.pS (.top t j : Pair T)) (S.N.latS (.top t j)) :=
    S.N.selfDual (X := .top j) (show j ≤ D.R.m by omega)
  have hTd : IsSelfDualC (G.pT (.top t j : Pair T)) (S.N.latT (.top t j)) :=
    S.N.selfDual (X := .top (j + 1)) (show j + 1 ≤ D.R.m by omega)
  have kS : (G.pS (.top t j : Pair T)).SigOK := (G.isV (X := .top j) (show j ≤ D.R.m by omega) (by simp)).sigOK
  have kT : (G.pT (.top t j : Pair T)).SigOK :=
    (G.isV (X := .top (j + 1)) (show j + 1 ≤ D.R.m by omega) (by simp)).sigOK
  have he' : e * e = e := (GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he).idem
  obtain ⟨κe, κo, hsplit, hSupp, hFin, hmt, hfix⟩ := GlobalTheory.VacMoveLow.exists_cut_pair (G.V (.top (j + 1))) he' he.2
  set h : GA D (G.V (.top (j + 1))) := (((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) :
    GA D (G.V (.top (j + 1)))) with hh_def
  have hoLat := GlobalTheory.CutStdLat.keep_stdLatO S htU j hj k hk e he (κo h) (hmt h)
  obtain ⟨c₁, hc₁⟩ := GlobalTheory.VacMoveLow.om_keep_vac hW W.θ_is kS kT
    (fun τ => W.cart_is (.top j) (show j ≤ D.R.m by omega) τ)
    (fun τ => W.cart_is (.top (j + 1)) (show j + 1 ≤ D.R.m by omega) τ) hSd hTd hvac
    (hFin h ((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1))).2) hoLat
  obtain ⟨c₂, hc₂⟩ := GlobalTheory.VacMoveLow.om_base_law hW hSd hTd he hvac.2.theta hvac.2.lat hTm (hSupp h)
  refine ⟨c₁ * c₂, ?_⟩
  rw [show ((1 : GA D (G.pS (.top t j : Pair T))), h) = ((1 : GA D (G.pS (.top t j : Pair T))), κe h) * (1, κo h) by
    rw [Prod.mk_mul_mk, mul_one, ← hsplit], map_mul, Module.End.mul_apply, hc₁, map_smul, hc₂, smul_smul]
  congr 2
  funext x
  refine GlobalTheory.VacMoveLow.halfInd_move _ (hsplit h) (fun w hw => hfix _ h w hw) (fun w hw => ?_) x
  rw [← map_inv]
  exact hfix _ h⁻¹ w hw

end GlobalTheory.ExpansionInvariance
