import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EigenCompatibleOfBadSet
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EventuallyUnr
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsHasSatakeOfUnr
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRecTLocRecT

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.TwInputs.Eig
section Satake
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult ReciprocityTheory.Aut Formalism.AUTREP
  NumberField IsDedekindDomain GlobalTheory.HeightCounting GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.EigRows
open GlobalTheory.StdFrame (StdPsi tensCastR)
open GlobalTheory.Hk3 (hyp SphOp)
open GlobalTheory.HeckeScalarSph (locK)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
variable {D : D7} {V : HSp D} {n : ℕ} {hF : D.host.F = maximalRealSubfield D.host.E} {Q : principalLevelFrame.RowPsi V n}
end Satake
section Rows
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem
  GlobalTheory.HeightCounting GlobalTheory.EigRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 400000
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3} {X0 : BaseLevelRowSide D}
  {Sb Sb' : Finset (PlE D.host)}
set_option maxHeartbeats 1000000 in
theorem eigTrue_of_read (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0) (hlev : R.toLevCh.Is A3.A.μ0)
    (W : GlobalTheory.RowTie.WDTie D.nd D.naut) (Rw : RowSide D) {sat : D.what₂.FT → PlE D.host → Multiset ℂ}
    (hrow : _root_.GlobalTheory.HeightCounting.RepresentationParametersHold hL D (typeR Y) (fun σ w => W.e w (Rw.locR σ w)) sat)
    {eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0} (he : EigAd Y Sb eig) (hsub : Sb ⊆ Sb') (hlow : Low D Sb') :
    EigTrue D R.C Rw Sb' eig := by
  intro j σ hne hgood P hs hP
  obtain ⟨s, rfl⟩ := GlobalTheory.TypeBlockPf.splitAt D P hs
  have hQ := stdPsi_PW Y j
  obtain ⟨_, B₀, -, hB₀⟩ := exists_hkDat (Sb := Sb) F hlev hsub hlow j hs hP (Nat.zero_le _)
  obtain ⟨x, hx, hx0⟩ := exists_sphVec hQ (partR_ne_bot Y hne) hB₀.full
  have hK : ∀ κ ∈ GlobalTheory.HeckeScalarSph.locK D.R.r s.v, NG.rt D.host.E D.R.r κ x = x := fun κ hκ =>
    hx.2 κ ((hyp_iff hQ s κ).2 hκ)
  obtain ⟨τ, hτ⟩ := exists_isLocS (typeR Y σ) s hx.1 hx0 hK
  have hrec := _root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 s.w)
  have hu := (_root_.GlobalTheory.CuspRep.ParLaws.reciprocity_unramified_iff_spherical hrec τ).2 (isSpherical_of_isLocS (typeR Y σ) s τ hτ hx.1 hx0 hK)
  obtain ⟨α, hα⟩ := _root_.UpperTheory.One.M.exists_hasSatake_of_unr_alt hrec hu
  have hpar : W.e s.w (Rw.locR σ s.w) = _ := hrow.1 σ s τ hτ
  have hunr : D.naut.unr (Rw.locR σ s.w) := (W.unr _ _).2 (hpar ▸ hu)
  refine ⟨hunr, fun k _ hk => ?_⟩
  obtain ⟨a, B, hd, -⟩ := exists_hkDat (Sb := Sb) F hlev hsub hlow j hs hP hk
  obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have h1 : hkNorm R j k s.w • heckeOn _ B (readW Y j y) = _ • readW Y j y := he j σ k s.w a B hd hgood y hy
  rw [heckeOn_partR Y hlev j (hlow.offPg hlev hP) hk hd.elt hd.reps σ ((mem_isot_iff Y j σ y).1 hy), smul_smul] at h1
  have h2 := smul_left_injective ℂ (fun h => hy0 (readW_injective Y j (h.trans (map_zero _).symm))) h1
  have h3 := sphEig_eq_satEig hQ (typeR Y σ) s ((GlobalTheory.PlaceDict.isSplit_iff_conjPl_ne D _ s.w rfl).2
    (GlobalTheory.HeckeDatumExists.conj_ne_of_split hs)) τ hτ hα hk
  have hq : Formalism.UG.qV D.host.E s.w = normV s.w := Ideal.absNorm_apply _
  have h4 : D.naut.frobEig (Rw.locR σ s.w) = Finset.univ.val.map fun i => (((α i)⁻¹ : ℂˣ) : ℂ) := by
    rw [W.frobEig _ _ hunr, hpar, _root_.GlobalTheory.CuspRep.ParLaws.reciprocity_eq_diagonal_inv_of_has_satake hrec hα, GlobalTheory.WeilDeligne.WD.frobEig_diag]
  rw [← h2, rowEig, h3, satEig_eq _ _ _ hk, hq, h4, Multiset.map_map, Multiset.map_map]
  set c : ℂ := (((R.C.mu0 j).val s.w : ℂˣ) : ℂ)⁻¹ * (((normV s.w : ℕ) : ℂ) ^ (D.R.nV / 2))⁻¹ with hc
  have h5 : (Finset.univ.val.map ((fun a : ℂ => a⁻¹ * (((R.C.mu0 j).val s.w : ℂˣ) : ℂ)⁻¹ *
      (((normV s.w : ℕ) : ℂ) ^ (D.R.nV / 2))⁻¹) ∘ fun i => (((α i)⁻¹ : ℂˣ) : ℂ))) =
      (Finset.univ.val.map ((fun b : ℂˣ => (b : ℂ)) ∘ α)).map (c • ·) := by
    rw [Multiset.map_map]
    refine Multiset.map_congr rfl fun i _ => ?_
    simp only [Function.comp_apply, Units.val_inv_eq_inv_val, inv_inv, smul_eq_mul, hc]
    ring
  have h6 : hkNorm R j k s.w = c ^ k := by
    rw [hc, mul_pow, inv_pow (_ ^ _), ← pow_mul, mul_comm (D.R.nV / 2)]
    rfl
  rw [h5, ← Multiset.pow_smul_esymm, h6, smul_eq_mul]
  ring
variable {cG : G0 R.Pg D.R.r ≃* G0g D.nd} {θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ}
theorem eig_of_rational_adjoint (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0) (hlev : R.toLevCh.Is A3.A.μ0)
    (hU : R.toRealDat.LUnif) (hW : R.toRealDat.models_HW)
    (hidem : ∀ g, D.what₂.embLL ((idemOf A3.A.X).coeff g) = D.ntypes.e0.coeff ((R.eG.trans cG) g))
    {kKs : Ks →+* ↥D.LL0} {hk : ∀ x : Ks, ((kKs x : ↥D.LL0) : D.what₂.LL) = algebraMap Ks D.what₂.LL x}
    {In : RatIn D (ratDatR R cG kKs hk)} (h : RatAd Y cG kKs hk In) (W : GlobalTheory.RowTie.WDTie D.nd D.naut) (Rw : RowSide D)
    {sat : D.what₂.FT → PlE D.host → Multiset ℂ} (hrow : _root_.GlobalTheory.HeightCounting.RepresentationParametersHold hL D (typeR Y) (fun σ w => W.e w (Rw.locR σ w)) sat)
    (hsub : In.Sb ⊆ Sb') (hlow : Low D Sb') :
    EigTrue D R.C Rw Sb' In.eig ∧ EigOcc D (ratDatR R cG kKs hk) In.θ In.hL Sb' In.eig :=
  ⟨_root_.GlobalTheory.TwInputs.Eig.eigTrue_of_read hL Y hlev W Rw hrow h.eig hsub hlow, eigOcc Y hlev hU hW hidem ⟨h.lvl, h.psi⟩ h.eig hsub hlow
    fun j k P α Rr h1 h2 hd => h.hecke j k P α Rr h1 h2 ⟨hd.split, fun e => hd.offS (hsub e), hd.odd, hd.le, hd.elt, hd.reps⟩⟩
end Rows
section AtRows
end AtRows
end GlobalTheory.TwInputs.Eig
end
end
