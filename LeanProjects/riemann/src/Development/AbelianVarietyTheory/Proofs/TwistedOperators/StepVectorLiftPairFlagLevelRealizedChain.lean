import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnrOffOne
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.OmVacuumEqSplitFacSmulSum
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsInvariantForm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchrodingerIntertwinerSchwartzBruhatIsThetaStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilRepThetaDatumHalfEqSmulStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EigenOfLocalComponentsFiniteAdelicPairStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHomLatticeIffFrameStabilizerActMemStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentComponentMemFrameStabilizerStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntegralUnitDeterminantAtIdempotentResidueStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilOperatorFixesLatticeVacuumNonsplitUnramifiedStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PlaceIdempotentUnderEqOfLiesOverStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TypePlaceDatumBlockTriangularMoveStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TwistPlaceDatumParabolicMoveStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrameMatrixMovedHomIntegralReductionsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdeleCharRestrictLocalUnitsResidueCharStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsUnramifiedAtPlaceIdempotentOfHeckeCharUnramifiStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelCharactersUnramifiedOffLevelPlacesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCharFamIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualCoordLatticeOfSelfDualFrame

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StepVecLaw

open GlobalTheory.StepLaw

variable {D : D7}

theorem placeIdem_mul_self {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (h : IsPlaceIdem D v ε) : ε * ε = ε := by
  obtain ⟨α, rfl, h1, h0⟩ := h
  have : IsPlaceIdem D v (pairA D.host.F 0 (α * α)) :=
    ⟨α * α, rfl, by rw [map_mul, h1, one_mul], fun w hw => by rw [map_mul, h0 w hw, zero_mul]⟩
  have h2 : pairA D.host.F 0 α * pairA D.host.F 0 α = pairA D.host.F 0 (α * α) := Prod.ext (mul_zero _) rfl
  exact h2.trans (GlobalTheory.PlaceDatum.placeIdem_eq this ⟨α, rfl, h1, h0⟩)

theorem prod_fiber {ι κ : Type} [DecidableEq κ] (P : Finset ι) (u : ι → κ) (φ : ι → ℂˣ) :
    ∏ v ∈ P.image u, ∏ i ∈ P with u i = v, (φ i : ℂ) = ((∏ i ∈ P, φ i : ℂˣ) : ℂ) := by
  rw [Finset.prod_fiberwise_of_maps_to (fun PP hP => Finset.mem_image_of_mem _ hP), Units.coe_prod]

theorem idem_mul_det {R : Type} [CommRing R] {n : ℕ} {e f : R} (he : e * e = e) (hef : e * f = e)
    {M M' : Matrix (Fin n) (Fin n) R} (h : M' = f • M + (1 - f) • (1 : Matrix (Fin n) (Fin n) R)) :
    e * M'.det = e * M.det := by
  have h1 : e • M' = e • M := by
    rw [h, smul_add, smul_smul, smul_smul, hef, mul_sub, hef, mul_one, sub_self, zero_smul, add_zero]
  have h2 := congrArg (fun X => e * Matrix.det X) h1
  simp only [Matrix.det_smul, ← mul_assoc, ← pow_succ'] at h2
  rwa [IsIdempotentElem.pow_succ_eq _ he] at h2

theorem supp_of_comp {R : Type} [CommRing R] {n : ℕ} {f : R} (hf : f * f = f)
    {M M' : Matrix (Fin n) (Fin n) R} (h : M' = f • M + (1 - f) • (1 : Matrix (Fin n) (Fin n) R)) (i j : Fin n) :
    f * (M' - 1) i j = (M' - 1) i j := by
  rw [h]
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  linear_combination (M i j - (1 : Matrix (Fin n) (Fin n) R) i j) * hf

section Vac

variable {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
  {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
  {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
  {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
  {βS : GL (Fin S.rank) (Lev.EAf D)} {βT : GL (Fin T.rank) (Lev.EAf D)} {f₀ : WO S T → ℂ}

theorem om_vac_split (hW : IsWeilDatumO ψ S T χS χT om) (kS : S.SigOK) (kT : T.SigOK)
    (cS : ∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) (cT : ∀ τ, IsCartanInv (gramAt D T τ) (sT τ))
    (dS : IsSelfDualC S ΛS) (dT : IsSelfDualC T ΛT) (hf : IsVacO ψ θ S T sS sT ΛS ΛT f₀)
    {e : AE D} (he : IsSplitIdem D e) {g : GA D S} {h : GA D T} (hg : SuppAt e S g) (hh : SuppAt e T h)
    {x y : (AE D)ˣ} (hx : IsDetAt e S g x) (hy : IsDetAt e T h y)
    (hl : ∀ u, u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) ↔ actO S T g h u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True)) :
    om (g, h) f₀ = (((χT x : Circle) : ℂ)⁻¹ * ((χS y : Circle) : ℂ)) • f₀ := by
  have hu : ∀ a : AE D, ∀ u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True), IsHalf a u →
      ∃! v, v ∈ ({0} : Finset (WO S T)) ∧ u - v ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) := fun a u hu _ =>
    ⟨0, ⟨Finset.mem_singleton_self _, by rwa [sub_zero]⟩, fun v hv => Finset.mem_singleton.1 hv.1⟩
  have h0 : ∀ a : AE D, ∀ u ∈ ({0} : Finset (WO S T)), u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) ∧ IsHalf a u := fun a u hu => by
    rw [Finset.mem_singleton.1 hu]
    exact ⟨zero_mem _, fun i j => mul_zero a⟩
  have := GlobalTheory.SplitScalar.om_vacuum_eq_splitFac_smul_sum D ψ θ S T χS χT om hW hf.2.inf kS kT sS sT cS cT ΛS ΛS ΛT ΛT
    dS dS dT dT e he g h hg hh x y hx hy
    (fun u => ⟨fun hu => ⟨actO S T g⁻¹ h⁻¹ u, (hl _).2 (by rwa [GlobalTheory.AdelicLatMove.actO_actO_inv]),
      (GlobalTheory.AdelicLatMove.actO_actO_inv S T g h u).symm⟩, fun ⟨u₀, hu₀, e⟩ => e ▸ (hl u₀).1 hu₀⟩)
    {0} {0} (h0 _) (hu _) (h0 _) (hu _) f₀ hf
  rw [this]
  simp [splitFacO, GlobalTheory.SplitScalar.heisO_zero]

set_option maxHeartbeats 1000000 in
open Classical in

theorem om_vac (hW : IsWeilDatumO ψ S T χS χT om) (kS : S.SigOK) (kT : T.SigOK)
    (cS : ∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) (cT : ∀ τ, IsCartanInv (gramAt D T τ) (sT τ))
    (dS : IsSelfDualC S ΛS) (dT : IsSelfDualC T ΛT) (fS : IsFrame βS ΛS) (fT : IsFrame βT ΛT)
    (hf : IsVacO ψ θ S T sS sT ΛS ΛT f₀) {P : Finset (Pl D.host.E)} {e : AE D} (he : IsIdemSum e P)
    {aS aT : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ} (hS : ∀ PP ∈ P, ResAt χS PP (aS PP)) (hT : ∀ PP ∈ P, ResAt χT PP (aT PP))
    (uS : UnrOff χS P) (uT : UnrOff χT P) {g : GA D S} {h : GA D T} (hg : g ∈ GfC S) (hh : h ∈ GfC T)
    (sg : finE S g ∈ St βS) (sh : finE T h ∈ St βT) :
    om (g, h) f₀ = ((∏ PP ∈ P, (aT PP (Matrix.GeneralLinearGroup.det (redFn βS PP (finE S g))))⁻¹ *
      aS PP (Matrix.GeneralLinearGroup.det (redFn βT PP (finE T h))) : ℂˣ) : ℂ) • f₀ := by
  obtain ⟨⟨es, hes, rfl⟩, hec⟩ := he
  set φ : Pl D.host.E → ℂˣ := fun PP => (aT PP (Matrix.GeneralLinearGroup.det (redFn βS PP (finE S g))))⁻¹ *
      aS PP (Matrix.GeneralLinearGroup.det (redFn βT PP (finE T h))) with hφ
  have cross := GlobalTheory.PlaceDatum.cross_eq_zero (R := AE D) GlobalTheory.PlaceDatum.isUnit_natCast (cA D) es P (fun i hi => (hes i hi).1.1) hec
  have hsum : ∀ PP ∈ P, ∀ ε, IsPlaceIdem D (PP.under (𝓞 D.host.F)) ε →
      es PP + cA D (es PP) = algebraMap (AF D.host.F) (AE D) ε := fun PP hP ε hε => by
    obtain ⟨v', ε', h1, h2⟩ := (hes PP hP).1.2.2
    have := GlobalTheory.T.placeIdempotent_under_eq_of_lies_over D _ PP v' ε' (hes PP hP) h1 h2
    subst this
    rw [h2, GlobalTheory.PlaceDatum.placeIdem_eq h1 hε]
  have key := GlobalTheory.T.eigen_of_local_components_finiteAdelic_pair D S T om f₀ (hW.om_cont f₀ hf.2.theta) g hg h hh (P.image fun PP => PP.under (𝓞 D.host.F))
    (fun v => ∏ PP ∈ P with PP.under (𝓞 D.host.F) = v, (φ PP : ℂ)) (fun v hv => ?_) (fun v ε hε g' h' hg' hh' => ?_)
  · exact key.trans (congrArg (· • f₀) (prod_fiber P (fun PP => PP.under (𝓞 D.host.F)) φ))
  · refine Finset.prod_eq_one fun PP hP => absurd ?_ hv
    rw [Finset.mem_filter] at hP
    exact Finset.mem_image.2 ⟨PP, hP.1, hP.2⟩
  have hεε : algebraMap (AF D.host.F) (AE D) ε * algebraMap (AF D.host.F) (AE D) ε = algebraMap (AF D.host.F) (AE D) ε := by
    rw [← RingHom.map_mul, placeIdem_mul_self hε]
  have hl := GlobalTheory.T.mem_homLattice_iff_frameStabilizer_act_mem D S T ΛS ΛT βS βT dS dT fS fT g' h' (GlobalTheory.T.idempotentComponent_mem_frameStabilizer D S βS g g' _ hεε sg hg')
    (GlobalTheory.T.idempotentComponent_mem_frameStabilizer D T βT h h' _ hεε sh hh')
  have pg : SuppPl ε S g' := supp_of_comp hεε hg'
  have ph : SuppPl ε T h' := supp_of_comp hεε hh'
  have split : ∀ a : AE D, IsSplitIdem D a → a + cA D a = algebraMap (AF D.host.F) (AE D) ε → ∀ x y : (AE D)ˣ,
      IsDetAt a S g x → IsDetAt a T h y → om (g', h') f₀ = (((χT x : Circle) : ℂ)⁻¹ * ((χS y : Circle) : ℂ)) • f₀ := by
    intro a ha hae x y hx hy
    have h1 : a * algebraMap (AF D.host.F) (AE D) ε = a := by rw [← hae, mul_add, ha.1, ha.2.1, add_zero]
    refine om_vac_split hW kS kT cS cT dS dT hf ha (fun i j => ?_) (fun i j => ?_) ?_ ?_ hl
    · rw [hae]; exact pg i j
    · rw [hae]; exact ph i j
    · exact hx.trans (by rw [idem_mul_det ha.1 h1 hg'])
    · exact hy.trans (by rw [idem_mul_det ha.1 h1 hh'])
  have sup : ∀ {V : HSp D} {k : GA D V} {a : AE D} {x : (AE D)ˣ}, a * a = a → IsDetAt a V k x →
      a * ((x : AE D) - 1) = (x : AE D) - 1 := fun {V k a x} ha hx => by
    rw [show (x : AE D) = _ from hx]
    linear_combination ((Formalism.L2.Theta.mt V k).det - 1) * ha
  by_cases hv : ∃ PP ∈ P, PP.under (𝓞 D.host.F) = v
  · obtain ⟨PP, hP, rfl⟩ := hv
    have ha := (hes PP hP).1
    have hfil : (P.filter fun Q => Q.under (𝓞 D.host.F) = PP.under (𝓞 D.host.F)) = {PP} := by
      refine Finset.eq_singleton_iff_unique_mem.2 ⟨Finset.mem_filter.2 ⟨hP, rfl⟩, fun Q hQ => ?_⟩
      rw [Finset.mem_filter] at hQ
      by_contra hne
      have h1 := GlobalTheory.PlaceDatum.idemAt_mul (hes PP hP) (hes Q hQ.1) (cross PP hP Q hQ.1) (cross Q hQ.1 PP hP) hne
      have h2 : es PP = 0 := by
        have h3 := hsum Q hQ.1 ε (hQ.2 ▸ hε)
        rw [← hsum PP hP ε hε] at h3
        have h4 := congrArg (es PP * ·) h3
        simp only [mul_add, h1, cross PP hP Q hQ.1, ha.1, ha.2.1, add_zero] at h4
        exact h4.symm
      obtain ⟨z, hz, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot PP.ne_bot
      refine ((hes PP hP).2 z hz0).1 hz ?_
      rw [h2, zero_mul, RingHom.map_zero]
      exact zero_mem _
    obtain ⟨x, hx, -, -, hxi, hxr⟩ := GlobalTheory.T.exists_integralUnit_determinantAtIdempotent_residue D S βS g sg (es PP) ha.1
    obtain ⟨y, hy, -, -, hyi, hyr⟩ := GlobalTheory.T.exists_integralUnit_determinantAtIdempotent_residue D T βT h sh (es PP) ha.1
    rw [split _ ha (hsum PP hP ε hε) x y hx hy, hfil, Finset.prod_singleton,
      hT PP hP _ (hes PP hP) x (sup ha.1 hx) hxi _ (hxr PP (hes PP hP)),
      hS PP hP _ (hes PP hP) y (sup ha.1 hy) hyi _ (hyr PP (hes PP hP)), hφ]
    simp only [Units.val_mul, Units.val_inv_eq_inv_val]
  · have hv' : ∀ PP ∈ P, PP.under (𝓞 D.host.F) ≠ v := fun PP hP h => hv ⟨PP, hP, h⟩
    rw [Finset.filter_eq_empty_iff.2 hv', Finset.prod_empty, one_smul]
    by_cases hs : ∃ a : AE D, IsSplitIdem D a ∧ a + cA D a = algebraMap (AF D.host.F) (AE D) ε
    · obtain ⟨a, ha, hae⟩ := hs
      have h1 : algebraMap (AF D.host.F) (AE D) ε * a = a := by rw [← hae, mul_comm, mul_add, ha.1, ha.2.1, add_zero]
      obtain ⟨x, hx, x1, x2, -⟩ := GlobalTheory.T.exists_integralUnit_determinantAtIdempotent_residue D S βS g sg a ha.1
      obtain ⟨y, hy, y1, y2, -⟩ := GlobalTheory.T.exists_integralUnit_determinantAtIdempotent_residue D T βT h sh a ha.1
      rw [split _ ha hae x y hx hy, uT v ε hε hv' x (by rw [← sup ha.1 hx, ← mul_assoc, h1]) x1 x2,
        uS v ε hε hv' y (by rw [← sup ha.1 hy, ← mul_assoc, h1]) y1 y2]
      simp
    · exact GlobalTheory.T.weilOperator_fixes_latticeVacuum_nonsplit_unramified D ψ S T χS χT om hW ΛS ΛT dS dT v ε ⟨hε, hs⟩ (uS v ε hε hv') (uT v ε hε hv') g' h' pg ph hl
        f₀ hf.2.theta hf.2.lat

end Vac

theorem unit_product_rescale_disjoint_finsets {ι : Type} [DecidableEq ι] {Pg Q : Finset ι} (hd : Disjoint Pg Q) (c : ι → ℂˣ) (a a' x x' y y' z z' : ι → ℂˣ)
    (hg : ∀ i ∈ Pg, c i = (x i)⁻¹⁻¹ * (x' i)⁻¹) (hq : ∀ i ∈ Q, c i = (y i)⁻¹ * y' i) :
    (1 * (∏ i ∈ Pg, a i) * ∏ i ∈ Q, (z i)⁻¹)⁻¹ * ((∏ i ∈ Pg ∪ Q, c i) * ((∏ i ∈ Pg, a i * (a' i)⁻¹ * (x' i * (x i)⁻¹)) *
      ∏ i ∈ Q, (y i * (z i)⁻¹ * ((y' i)⁻¹ * z' i)) ^ (1 : ℤ))) = (1 * (∏ i ∈ Pg, a' i) * ∏ i ∈ Q, (z' i)⁻¹)⁻¹ := by
  rw [Finset.prod_union hd, Finset.prod_congr rfl hg, Finset.prod_congr rfl hq]
  simp only [zpow_one, Finset.prod_mul_distrib, Finset.prod_inv_distrib]
  generalize (∏ i ∈ Pg, a i) = A, (∏ i ∈ Pg, a' i) = A', (∏ i ∈ Pg, x i) = X, (∏ i ∈ Pg, x' i) = X', (∏ i ∈ Q, y i) = Y,
    (∏ i ∈ Q, y' i) = Y', (∏ i ∈ Q, z i) = Z, (∏ i ∈ Q, z' i) = Z'
  apply Units.ext
  push_cast
  field_simp

theorem levFn_flag_datY {n r t k : ℕ} (hr : r ≤ n) (Pg Q : Finset (Pl D.host.E)) (P : LevelP Pg r ℂ)
    (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (β x : GL (Fin n) (Lev.EAf D)) :
    levFn β (flagL (datY n r t k hr Pg Q P χ ξ Frm.B)) x =
      1 * (∏ PP ∈ Pg, ∏ c ∈ Finset.range k, χ (c + 1) PP (dBlk (blkOf r t) (c + 1) (redFn β PP x))) *
        ∏ PP ∈ Q, (ξ PP (dBlk (blk2 r) 1 (redFn β PP x)))⁻¹ := by
  have h : ext1 (flagL (datY n r t k hr Pg Q P χ ξ Frm.B)).P.H (flagL (datY n r t k hr Pg Q P χ ξ Frm.B)).P.chi
      (rTup β (flagL (datY n r t k hr Pg Q P χ ξ Frm.B)) x) = 1 := subgroupCharExtension_one_apply _ _
  unfold levFn
  rw [h]
  rfl

section Step

variable {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
  {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
  {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
  {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
  {βS : GL (Fin S.rank) (Lev.EAf D)} {βT : GL (Fin T.rank) (Lev.EAf D)} {f₀ f : WO S T → ℂ}

set_option maxHeartbeats 1000000 in
open Classical in

theorem step_law (hW : IsWeilDatumO ψ S T χS χT om) (kS : S.SigOK) (kT : T.SigOK)
    (cS : ∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) (cT : ∀ τ, IsCartanInv (gramAt D T τ) (sT τ))
    (dS : IsSelfDualC S ΛS) (dT : IsSelfDualC T ΛT) (fS : IsFrame βS ΛS) (fT : IsFrame βT ΛT)
    {r t k : ℕ} (ha : r ≤ S.rank) (hb : r ≤ T.rank) (eS : S.rank = r + k * t) (eT : T.rank = r + (k + 1) * t)
    {Pg Q : Finset (Pl D.host.E)} (hd : Disjoint Pg Q) {χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ}
    {ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ}
    (hv : IsStepVecOf ψ θ S T sS sT ΛS ΛT βS βT (datY S.rank r t k ha Pg Q (LevelP.triv Pg r ℂ) χ ξ Frm.B) (χ (k + 1)) Q ξ f₀ f)
    (hG : ∀ PP ∈ Pg, ResAt χS PP (χ (k + 1) PP)⁻¹ ∧ ResAt χT PP (χ (k + 1) PP)⁻¹)
    (hQ : ∀ PP ∈ Q, ResAt χS PP (ξ PP) ∧ ResAt χT PP (ξ PP)) (uS : UnrOff χS (Pg ∪ Q)) (uT : UnrOff χT (Pg ∪ Q))
    {g0 : G0 Pg r} {g : GA D S} {h : GA D T}
    (hg : IsLevelLift S βS (datY S.rank r t k ha Pg Q (LevelP.triv Pg r ℂ) χ ξ Frm.B) g0 g)
    (hh : IsLevelLift T βT (datY T.rank r t (k + 1) hb Pg Q (LevelP.triv Pg r ℂ) χ ξ Frm.B) g0 h) :
    (levChi S βS (flagL (datY S.rank r t k ha Pg Q (LevelP.triv Pg r ℂ) χ ξ Frm.B)) g)⁻¹ • om (g, h) f =
      (levChi T βT (flagL (datY T.rank r t (k + 1) hb Pg Q (LevelP.triv Pg r ℂ) χ ξ Frm.B)) h)⁻¹ • f := by
  obtain ⟨hf, e, he, hΘ⟩ := hv
  have he' : IsIdemSum e (Pg ∪ Q) := he
  have sg := parLev_St hg.2.1
  have sh := parLev_St hh.2.1
  let a : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ := fun PP => if PP ∈ Pg then (χ (k + 1) PP)⁻¹ else ξ PP
  have a1 : ∀ PP ∈ Pg, a PP = (χ (k + 1) PP)⁻¹ := fun PP hP => if_pos hP
  have a2 : ∀ PP ∈ Q, a PP = ξ PP := fun PP hP => if_neg (Finset.disjoint_right.1 hd hP)
  have hres : ∀ PP ∈ Pg ∪ Q, ResAt χS PP (a PP) ∧ ResAt χT PP (a PP) := fun PP hP => by
    rcases Finset.mem_union.1 hP with hP | hP
    · rw [a1 PP hP]; exact hG PP hP
    · rw [a2 PP hP]; exact hQ PP hP
  have h1 := om_vac hW kS kT cS cT dS dT fS fT hf he' (fun PP hP => (hres PP hP).1) (fun PP hP => (hres PP hP).2) uS uT
    hg.1 hh.1 sg sh
  have hoG := GlobalTheory.T.typePlaceDatum_blockTriangular_move D _ _ r t k ha hb eS eT Pg Q χ ξ (fun PP => redFn βS PP (finE S g)) (fun PP => redFn βT PP (finE T h))
    fun PP hP => ⟨parLev_g hg.2.1 hP, parLev_g hh.2.1 hP, (congrFun hg.2.2 ⟨PP, hP⟩).trans (congrFun hh.2.2 ⟨PP, hP⟩).symm⟩
  have hoQ := GlobalTheory.T.twistPlaceDatum_parabolic_move D _ _ r ha hb Q ξ 1 (fun PP => redFn βS PP (finE S g)) (fun PP => redFn βT PP (finE T h))
    fun PP hP => ⟨parLev_q hg.2.1 hP, parLev_q hh.2.1 hP⟩
  have h2 := GlobalTheory.T.weilRep_theta_datum_half_eq_smul D ψ S T χS χT om hW e _ f₀ _ f
    (GlobalTheory.T.schrodingerIntertwiner_schwartzBruhat_isTheta D ψ hW.std S T ΛS ΛT dS dT e (GlobalTheory.PlaceDatum.idemSum_mul_self he) (GlobalTheory.PlaceDatum.infPart_idemSum he) f₀
      hf.2.theta) hΘ g h (GlobalTheory.T.mem_homLattice_iff_frameStabilizer_act_mem D S T ΛS ΛT βS βT dS dT fS fT g h sg sh) _ (_ * _) (Units.ne_zero _) h1 (fun x => by
      obtain ⟨i1, i2⟩ := GlobalTheory.T.frameMatrix_movedHom_integral_reductions D S T βS βT g h sg sh x
      have i0 : IsHalf e (actO S T g⁻¹ h⁻¹ x) ↔ IsHalf e x :=
        ⟨fun H => GlobalTheory.AdelicLatMove.actO_actO_inv S T g h x ▸ GlobalTheory.SplitHecke.isHalf_actO g h H,
          fun H => GlobalTheory.SplitHecke.isHalf_actO _ _ H⟩
      by_cases hx : IsHalf e x ∧ IsIntM (frMapO S T βS βT x)
      · beta_reduce
        rw [if_pos hx, if_pos ⟨i0.2 hx.1, i1.2 hx.2⟩, funext (i2 hx.2)]
        exact (congrArg₂ (· * ·) (hoG _) (hoQ _)).trans (mul_mul_mul_comm _ _ _ _)
      · beta_reduce
        rw [if_neg hx, if_neg fun H => hx ⟨i0.1 H.1, i1.1 H.2⟩, mul_zero])
  rw [h2, smul_smul]
  congr 1
  unfold levChi
  rw [levFn_flag_datY, levFn_flag_datY, ← Units.val_mul, ← Units.val_mul, ← Units.val_inv_eq_inv_val, ← Units.val_inv_eq_inv_val,
    ← Units.val_mul]
  refine congrArg Units.val (unit_product_rescale_disjoint_finsets hd _ _ _ _ _ _ _ _ _ (fun PP hP => ?_) fun PP hP => ?_)
  · rw [a1 PP hP]; rfl
  · rw [a2 PP hP]

end Step

section Chars

open Classical

variable {T0 : Type} {L : LevCh D T0} {μ0 : T0}

def LevRes (L : LevCh D T0) (t : T0) (j : ℕ) (c : (AE D)ˣ →* Circle) : Prop :=
  (∀ PP ∈ L.Pg, ResAt c PP (L.chi j PP)⁻¹) ∧ (∀ PP ∈ L.Q t, ResAt c PP (L.xiR t PP)) ∧ UnrOff c (L.Pg ∪ L.Q t)

theorem levRes_mu (hL : L.Is μ0) (t : T0) (j : Fin D.R.m) : LevRes L t ((j : ℕ) + 1) (L.mu t ((j : ℕ) + 1)) := by
  obtain ⟨-, p1, p2, p3⟩ := GlobalTheory.T.levelCharacters_unramified_off_levelPlaces D T0 L μ0 hL t
  refine ⟨fun PP hP => ?_, fun PP hP => ?_, UnrOff.mul (fun v ε hε hv => ?_) fun v ε hε hv => ?_⟩
  · have := ((GlobalTheory.T.ideleChar_restrict_localUnits_residueChar D _ _ (hL.mu0 j) PP).1 _ ((L.C.isMu0 j).tame PP) (hL.chi j PP hP)).mul
      ((GlobalTheory.T.ideleChar_restrict_localUnits_residueChar D _ _ (hL.xi t) PP).2 (p1 PP hP))
    rwa [mul_one] at this
  · have := ((GlobalTheory.T.ideleChar_restrict_localUnits_residueChar D _ _ (hL.mu0 j) PP).2 (p2 PP hP j)).mul
      ((GlobalTheory.T.ideleChar_restrict_localUnits_residueChar D _ _ (hL.xi t) PP).1 _ (hL.xi_tame t PP) (hL.xiR t PP hP))
    rwa [one_mul] at this
  · exact GlobalTheory.T.isUnramifiedAtPlaceIdempotent_of_heckeChar_unramified_above D _ _ (hL.mu0 j) v ε hε fun P hP =>
      (p3 P fun PP h => hP ▸ hv PP (Finset.mem_union.2 h)).2 j
  · exact GlobalTheory.T.isUnramifiedAtPlaceIdempotent_of_heckeChar_unramified_above D _ _ (hL.xi t) v ε hε fun P hP =>
      (p3 P fun PP h => hP ▸ hv PP (Finset.mem_union.2 h)).1

theorem LevRes.mul_eta_inv (hL : L.Is μ0) {t : T0} {j : ℕ} {c : (AE D)ˣ →* Circle} (h : LevRes L t j c) :
    LevRes L t j (c * L.eta⁻¹) := by
  have h1 : ∀ PP, ResAt L.eta⁻¹ PP 1 := fun PP => by
    have := ((GlobalTheory.T.ideleChar_restrict_localUnits_residueChar D _ _ hL.eta PP).2 (L.C.isEta.unr PP)).inv
    rwa [inv_one] at this
  refine ⟨fun PP hP => ?_, fun PP hP => ?_, h.2.2.mul (UnrOff.inv fun v ε hε _ => ?_)⟩
  · have := (h.1 PP hP).mul (h1 PP)
    rwa [mul_one] at this
  · have := (h.2.1 PP hP).mul (h1 PP)
    rwa [mul_one] at this
  · exact GlobalTheory.T.isUnramifiedAtPlaceIdempotent_of_heckeChar_unramified_above D _ _ hL.eta v ε hε fun P _ => L.C.isEta.unr P

theorem levRes_chrStep (hL : L.Is μ0) (t : T0) (j : Fin D.R.m) :
    LevRes L t ((j : ℕ) + 1) (Lift.chrStep (L.mu t) L.eta ((j : ℕ) + 1)).1 ∧
      LevRes L t ((j : ℕ) + 1) (Lift.chrStep (L.mu t) L.eta ((j : ℕ) + 1)).2 := by
  have h := levRes_mu hL t j
  unfold Lift.chrStep
  split_ifs
  · exact ⟨h.mul_eta_inv hL, h⟩
  · exact ⟨h, h.mul_eta_inv hL⟩

end Chars

open Formalism.IndefR.Mult in

theorem stepVec_lifts : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.models_inf → R.chain_ωY → R.chain_vY → ∀ t k, k + 1 < D.R.m → ∀ (g0 : G0 R.Pg D.R.r) κ κ', IsLevelLift (Yc D k) (R.βY k) (R.datYt t k R.triv) g0 κ → IsLevelLift (Yc D (k + 1)) (R.βY (k + 1)) (R.datYt t (k + 1) R.triv) g0 κ' → (levChi _ (R.βY k) (flagL (R.datYt t k R.triv)) κ)⁻¹ • R.ωY t k (κ, κ') (R.vY t k) = (levChi _ (R.βY (k + 1)) (flagL (R.datYt t (k + 1) R.triv)) κ')⁻¹ • R.vY t k := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R hL _ hω hv t k hk g0 κ κ' hκ hκ'
  have hk' : k < D.R.m := Nat.lt_of_succ_lt hk
  obtain ⟨⟨a1, a2, a3⟩, b1, b2, b3⟩ := levRes_chrStep hL t ⟨k, hk'⟩
  obtain ⟨c, hc⟩ := hL.βY k hk'
  obtain ⟨c', hc'⟩ := hL.βY (k + 1) hk
  refine step_law (hω t k hk) (D.sp.Y_sig _) (D.sp.Y_sig _) (GlobalTheory.Chain.VacVec.cart_isCartanInv (R.MY k))
    (GlobalTheory.Chain.VacVec.cart_isCartanInv (R.MY (k + 1)))
    (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hL.βY k hk'))
    (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hL.βY (k + 1) hk)) hc.1 hc'.1 (r_le_Y k) (r_le_Y (k + 1)) ?_ ?_
    (GlobalTheory.T.levelCharacters_unramified_off_levelPlaces D T0 _ _ hL t).1 (hv t k hk) (fun PP hP => ⟨a1 PP hP, b1 PP hP⟩) (fun PP hP => ⟨a2 PP hP, b2 PP hP⟩) a3 b3 hκ hκ'
  · rw [D.sp.Y_rank _ (min_le_right _ _), min_eq_left hk'.le]; rfl
  · rw [D.sp.Y_rank _ (min_le_right _ _), min_eq_left hk.le]; rfl

end GlobalTheory.StepVecLaw

end
