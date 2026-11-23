import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemCuspFormsAllEmbeddingsOfInclusionReading
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SupLatticeLocalisationOfUnitBall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KapTopLastPosRun
import Formalism.LocalToGlobal.IndefiniteReal.FWCentral
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.TwistSeries
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyAlgHomOfIsIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarmonicPolynomialEqZeroOfFunctionStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.DictionaryCast
open Formalism.IndefR.FWT Formalism.L2.Pj
variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T0 : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  {Rl : RealDat3 D A3 Ks} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw}

theorem evW_smul (YS : NX.NExpRealS Rl cG S) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec)
    (j : Fin D.R.m) (a : D.what₂.LL) (x : S.WL ((j : ℕ) + 1)) :
    evW YS v₀ j (a • x) = sg0 D A3.A a • evW YS v₀ j x := by
  simp only [evW, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [LinearEquiv.map_smul, LinearMap.map_smulₛₗ, map_smul]
  rfl

theorem castDict_sum_smul' {V W : HSp D} (e : V = W) {m : ℕ} (a : Fin m → ℂ) (ψ : Fin m → GA D V → ℂ) (g : GA D W) :
    castDict e (∑ i, a i • ψ i) g = ∑ i, a i * castDict e (ψ i) g := by
  subst e
  simp [castDict, Finset.sum_apply]

theorem castDict_phiJ' {T : CoreJ D} {j : ℕ} {W : HSp D} {σ : T.Q.c.F →+* ℂ} (hσ : σ = T.σ₀) (h1 : T.V j σ = W)
    (h2 : T.V j T.σ₀ = W) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f : T.R j) (g : GA D W) :
    (h1 ▸ T.phiJ j σ a f : GA D W → ℂ) g = castDict h2 (T.phiJ j T.σ₀ a f) g := by
  subst hσ
  subst h1
  rfl

end GlobalTheory.DictionaryCast

theorem GlobalTheory.XiIntCore.supLattice_comb_of_baseInt : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SeriesRat → GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.SerInt → ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E), FieldOk X → (∀ (j : Fin D.R.m) hV, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin X.core X.R.toRealDat j X.core.σ₀ hV) → ∀ i, D.ntw.NonzeroIndexPlace i → ∀ (j : Fin D.R.m) (b : Bool) (hV : X.core.V ((j : ℕ) + 1) X.core.σ₀ = Wc D j) (la : HeightOneSpectrum (𝓞 X.core.Q.c.F)), (∀ x : X.core.Q.c.F, FinitePlace.mk la x ≤ 1 ↔ ∃ o : D.ntw.O i, Y.Z.ρ.eO i b o = X.core.σ₀ x) → ∀ (n : ℕ) (o : Fin n → D.ntw.O i) (ψ : Fin n → (GA D (X.core.V ((j : ℕ) + 1) X.core.σ₀) → ℂ)), (∀ k, ψ k ∈ GlobalTheory.CoverRead.baseInt X.core ((j : ℕ) + 1) X.core.σ₀ (Formalism.L2.Pj.wtA (X.geo.κ j)) (X.geo.κ j).n {la}) → ∃ (n' : ℕ) (o' : Fin n' → D.ntw.O i) (m : Fin n' → NX.FmK Y.S ((j : ℕ) + 1)), (∀ k, Subtype.val (m k) ∈ (Y.S.A ((j : ℕ) + 1)).MK) ∧ FWT.castDict hV (∑ k, Y.Z.ρ.eO i b (o k) • ψ k) = ∑ k, Y.Z.ρ.eO i b (o' k) • evW Y.YS X.geo.v₀ j (Subtype.val (m k)) := by
  intro hA hR hI D X E Y hF hP i hi j b hV la hla n o ψ hψ
  have hev : X.geo.fw.Evaluates := X.geo.fw.evaluates_of_lUnif X.unif
  have hσ : FWT.res X.core (sg0 D X.A3.A) = X.core.σ₀ := by
    rw [show sg0 D X.A3.A = D.what₂.embLL from sgAt_mk _ X.R.hv0]
    exact FWT.res_embLL X.core X.geo.fw.alg_eq X.geo.fw.laws.pins.2.2.1
  have hV' : X.core.V ((j : ℕ) + 1) (FWT.res X.core (sg0 D X.A3.A)) = Wc D j := by rw [hσ]; exact hV
  have hlast : (X.geo.κ j).LastPos := fun τ k hk => by
    rw [(X.geo.fw.kap j τ).1 k]; exact GlobalTheory.LiftWeight.kapTop_lastPos D j τ k hk
  have hinR : Formalism.L2.Pj.InR D ((j : ℕ) + 1) := ⟨Nat.le_add_left _ _, j.2⟩
  have key : ∀ k, ∃ (o'' : D.ntw.O i) (m : NX.FmK Y.S ((j : ℕ) + 1)), Subtype.val m ∈ (Y.S.A ((j : ℕ) + 1)).MK ∧
      FWT.castDict hV (ψ k) = Y.Z.ρ.eO i b o'' • evW Y.YS X.geo.v₀ j (Subtype.val m) := by
    intro k
    obtain ⟨f, ⟨hsec, hhol, hint⟩, hfk⟩ := hψ k
    have hcu := GlobalTheory.CuspAllEmb.mem_cuspA_of_rdU_mem_holSub0 D X.core X.geo.fw.laws _ hinR (X.geo.κ j) hlast f hsec hhol
    let fc : FWT.Cu X.core X.geo.κ j := ⟨f, hcu⟩
    have hball : ∀ y : (X.R.FW j).Pt la, (X.R.FW j).nrm la y (X.geo.fw.e j fc) ≤ 1 := fun y => by
      rw [X.geo.fw.nrm_eq]
      exact (X.core.nrmM_le_one_iff _ la _ _).2 (hint la rfl _ (X.geo.fw.pt j la y).2)
    obtain ⟨s, hs, hsM⟩ := GlobalTheory.supLattice_localisation_of_unitBall _ _ _ _ _ (X.R.FW j) (X.integral j).2.1.2 la _ hball
    set w := X.geo.fw.e j fc with hw
    have hx₀ : evW Y.YS X.geo.v₀ j ((Y.YS.fi j).e.symm (w : Fin (X.R.nW j) → D.what₂.LL)) =
        FWT.phiC X.core hV' (Formalism.L2.Pj.wtA (X.geo.κ j)) f := by
      refine Eq.trans ?_ (hev j (sg0 D X.A3.A) (by rw [hσ]; exact X.core.toCore.good_σ₀) hV' fc)
      simp only [evW, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
      rw [LinearEquiv.apply_symm_apply]
      rfl
    have hsm : s • (w : Fin (X.R.nW j) → D.what₂.LL) =
        algebraMap X.core.Q.c.F D.what₂.LL (s : X.core.Q.c.F) • (w : Fin (X.R.nW j) → D.what₂.LL) := by
      rw [algebraMap_smul]
      exact (algebraMap_smul X.core.Q.c.F s _).symm
    let m : NX.FmK Y.S ((j : ℕ) + 1) := ⟨(Y.YS.fi j).e.symm (s • (w : Fin (X.R.nW j) → D.what₂.LL)),
      ((Y.YS.fi j).wk _).2 (by rw [LinearEquiv.apply_symm_apply]; exact hsM.fst)⟩
    have hmK : Subtype.val m ∈ (Y.S.A ((j : ℕ) + 1)).MK :=
      ((Y.YS.fi j).mkK _).2 (by rw [LinearEquiv.apply_symm_apply]; exact hsM)
    have hsσ : sg0 D X.A3.A (algebraMap X.core.Q.c.F D.what₂.LL (s : X.core.Q.c.F)) = X.core.σ₀ (s : X.core.Q.c.F) :=
      congrArg (fun τ : X.core.Q.c.F →+* ℂ => τ (s : X.core.Q.c.F)) hσ
    have hevm : evW Y.YS X.geo.v₀ j (Subtype.val m) =
        X.core.σ₀ (s : X.core.Q.c.F) • evW Y.YS X.geo.v₀ j ((Y.YS.fi j).e.symm (w : Fin (X.R.nW j) → D.what₂.LL)) := by
      change evW Y.YS X.geo.v₀ j ((Y.YS.fi j).e.symm (s • (w : Fin (X.R.nW j) → D.what₂.LL))) = _
      rw [hsm, LinearEquiv.map_smul, GlobalTheory.DictionaryCast.evW_smul, hsσ]
    have hs0 : (s : X.core.Q.c.F) ≠ 0 := fun h => hs (by
      rw [show s = 0 from RingOfIntegers.coe_eq_zero_iff.1 h]; exact la.asIdeal.zero_mem)
    have hinv : FinitePlace.mk la ((s : X.core.Q.c.F)⁻¹) ≤ 1 := by
      rw [map_inv₀, FinitePlace.mk_apply, (FinitePlace.norm_eq_one_iff_notMem X.core.Q.c.F la s).mpr hs, inv_one]
    obtain ⟨o'', ho''⟩ := (hla _).1 hinv
    refine ⟨o'', m, hmK, ?_⟩
    have hc : FWT.castDict hV (ψ k) = FWT.phiC X.core hV' (Formalism.L2.Pj.wtA (X.geo.κ j)) f := by
      rw [← hfk]
      funext g
      exact (GlobalTheory.DictionaryCast.castDict_phiJ' hσ hV' hV _ _ g).symm
    rw [hc, ← hx₀, hevm, ho'', smul_smul, map_inv₀, inv_mul_cancel₀ ((map_ne_zero _).2 hs0), one_smul]
  choose o'' m hm he using key
  refine ⟨n, fun k => o k * o'' k, m, hm, ?_⟩
  funext g
  rw [GlobalTheory.DictionaryCast.castDict_sum_smul', Finset.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [he k]
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, mul_assoc]
