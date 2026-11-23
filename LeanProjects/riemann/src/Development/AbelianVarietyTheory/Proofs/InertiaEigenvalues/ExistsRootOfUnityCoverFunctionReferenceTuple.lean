import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConjTupRefl
import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsThClsDGalRul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjFourierCoefficientsConjugateTuplesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisConjClassScalarsAndVolumeStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.MarkedIsometryHalf
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SecEqZeroOfComplex
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GalRulGalRul
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CoefficientFieldAlgClosedInFunctionFieldsOfPerio
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCoversOfHalves
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLatticeEmbeddingLiftDatumHermitianSpace
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAlgebraMapOfSigRFixed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstRelIffTwistFactorAt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramedPointBaseChangeAlgebraMap
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ConjugateSectionValuesSemilinear
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsDeltaDatumHigherLevel

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GalRef

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH
  Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct

set_option maxHeartbeats 1000000 in

theorem val_of_cXiAt {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {n r : ℕ} (V : HSp D) (hr : V.rank = r) (d : DeltaDat Xo c n)
    (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) (hι : GlobalTheory.Member.IotaOK Dw V ι) (hpq : 1 ≤ Dw.p + Dw.q)
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ)
    (hx₀ : ∀ τ : D.host.E →+* ℂ, τ (H.rt : D.host.E) = H.rt0 →
      ReciprocityTheory.ChartRestriction.G.FD.gram τ (-(Matrix.reindex (finCongr hr) (finCongr hr) V.gram).transpose) (x₀ τ) =
        Matrix.diagonal fun a : Fin r => ((ReciprocityTheory.ChartRestriction.G.FD.sgn Dw.q (a : ℕ) : ℝ) : ℂ))
    (hA : d.l₂.A = 1) (hs : d.cδ ∈ sec d.Xo₂ d.c₂ 0 0) (xi : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ)
    (hxi : ∀ h : GA D V, xi (Matrix.GeneralLinearGroup.det (finHom V h)) = 1)
    (U₂ : Unf d.Xo₂ d.c₂ (c.F.val.toRingHom.comp (d.eF.symm : d.c₂.F →+* c.F)) r)
    (dict₂ : GA D V → Σ k, Frame (U₂.X k).Ψ r) (c0 : ℂ) (hc0 : c0 ≠ 0)
    (hv : GlobalTheory.OneMapAll.CXiAt V hr c.F.val.toRingHom d U₂ dict₂ ι x₀ xi c0) :
    (∀ y : FrPt d.Xo₂ d.c₂ (CAt (c.F.val.toRingHom.comp (d.eF.symm : d.c₂.F →+* c.F))),
      toC (evR d.Xo₂ d.c₂ d.cδ y) = c0) ∧
      Nonempty (FrPt d.Xo₂ d.c₂ (CAt (c.F.val.toRingHom.comp (d.eF.symm : d.c₂.F →+* c.F)))) := by
  classical
  subst hr
  obtain ⟨hU, hW, g₀, e₀, F, ik, φ, th, hth, hD, hval⟩ := hv
  have hσ : GoodEmb d.c₂ (c.F.val.toRingHom.comp (d.eF.symm : d.c₂.F →+* c.F)) := by
    have e : c.F.val.toRingHom.comp (d.eF.symm : d.c₂.F →+* c.F) = d.c₂.F.val.toRingHom := RingHom.ext fun _ => rfl
    rw [e]; rfl
  have val₀ : ∀ h : GA D V, ∃ hx : (dict₂ h).2 ∈ (U₂.X (dict₂ h).1).dom,
      toC (evR d.Xo₂ d.c₂ d.cδ (U₂.un _ ⟨_, hx⟩)) = c0 := by
    intro h
    obtain ⟨γ, hγ, hΛ, hm, -⟩ := hD.2 h
    have hv := hval h γ ⟨hγ, hΛ, hm⟩
    rw [hxi (γ * h), Units.val_one, mul_one] at hv
    by_cases hx : (dict₂ h).2 ∈ (U₂.X (dict₂ h).1).dom
    · refine ⟨hx, ?_⟩
      rw [← hv]
      show _ = (if h' : (dict₂ h).2 ∈ (U₂.X (dict₂ h).1).dom then toC (evR d.Xo₂ d.c₂ d.cδ (U₂.un _ ⟨_, h'⟩)) else 0)
      rw [dif_pos hx]
    · exfalso
      apply hc0
      rw [← hv]
      show (if h' : (dict₂ h).2 ∈ (U₂.X (dict₂ h).1).dom then toC (evR d.Xo₂ d.c₂ d.cδ (U₂.un _ ⟨_, h'⟩)) else 0) = 0
      rw [dif_neg hx]
  choose hdom val₀ using val₀
  refine ⟨fun y => ?_, ⟨U₂.un _ ⟨_, hdom 1⟩⟩⟩
  obtain ⟨h, hh⟩ := GlobalTheory.TwistTie.exists_dict_over V U₂ dict₂ ι e₀ F ik φ th x₀ hσ hA hpq hU hW hD hι hth
    (fun k τ hτ => by
      rw [(hW k).1, (hU.2.1 k).1]
      exact hx₀ τ (((hU.2.1 k).2 τ).1 hτ)) hdom y
  rw [GlobalTheory.WeightZeroValue.evR_eq_of_same_point hs hh]
  exact val₀ h

end GlobalTheory.GalRef

namespace GlobalTheory.GalRef

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory

set_option maxHeartbeats 1000000 in

theorem mem_of_val {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ} (d : DeltaDat Xo c n) (hs : d.cδ ∈ sec d.Xo₂ d.c₂ 0 0) (c0 : ℂ) (m : ℕ)
    (hm : 0 < m) (hc0 : c0 ^ m = 1)
    (hval : ∀ y : FrPt d.Xo₂ d.c₂ (CAt (c.F.val.toRingHom.comp (d.eF.symm : d.c₂.F →+* c.F))),
      toC (evR d.Xo₂ d.c₂ d.cδ y) = c0)
    (y₀ : FrPt d.Xo₂ d.c₂ (CAt (c.F.val.toRingHom.comp (d.eF.symm : d.c₂.F →+* c.F)))) : c0 ∈ c.F := by
  have hS : Out.SecBaseChangeSt := GlobalTheory.firstFiveLaws.1.secBaseChange
  let σ₂ : d.c₂.F →+* ℂ := c.F.val.toRingHom.comp (d.eF.symm : d.c₂.F →+* c.F)
  have hσ₂ : ∀ a : d.c₂.F, σ₂ a ∈ c.F := fun a => (d.eF.symm a).2
  have hfix : ∀ τ : ℂ ≃+* ℂ, (∀ x ∈ c.F, τ x = x) → τ c0 = c0 := by
    intro τ hτ
    let φ : CAt σ₂ →ₐ[d.c₂.F] CAt σ₂ :=
      { toRingHom := (τ : ℂ →+* ℂ)
        commutes' := fun a => hτ _ (hσ₂ a) }
    obtain ⟨z, hz⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap hS E H Dw d.l₂ d.Xo₂ d.c₂ _ _ φ y₀
    have hx : z.x = spMap (τ : ℂ →+* ℂ) ≫ y₀.x := hz.1
    have e := GlobalTheory.GalTw.CharSec.conj_value σ₂ σ₂ τ (RingHom.ext fun a => (hτ _ (hσ₂ a)).symm) hs y₀ z hx
    rw [hval, hval] at e
    exact e.symm
  let K := c.F
  let L := IntermediateField.adjoin K {c0}
  have hint : IsIntegral K c0 := by
    refine IsIntegral.of_pow hm ?_
    rw [hc0]; exact isIntegral_one
  haveI : FiniteDimensional K L := IntermediateField.adjoin.finiteDimensional hint
  haveI : FiniteDimensional ℚ K := c.fin
  haveI : FiniteDimensional ℚ L := Module.Finite.trans K L
  haveI : Countable L := (Module.finBasis ℚ L).equivFun.toEquiv.countable_iff.2 inferInstance
  have hr : IsIntegral K (⟨c0, IntermediateField.mem_adjoin_simple_self K c0⟩ : L) := by
    refine IsIntegral.of_pow hm ?_
    have : (⟨c0, IntermediateField.mem_adjoin_simple_self K c0⟩ : L) ^ m = 1 := Subtype.ext (by simpa using hc0)
    rw [this]; exact isIntegral_one
  obtain ⟨a, ha⟩ := GlobalTheory.CompRat.FixedConst.mem_range_of_fixed (K := K) (L := L) L.val hr fun τ hτ => hfix τ fun x hx => hτ ⟨x, hx⟩
  have : ((algebraMap K L a : L) : ℂ) = c0 := congrArg Subtype.val ha
  rw [← this]
  exact a.2

end GlobalTheory.GalRef

namespace GlobalTheory.GalRef

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

set_option maxHeartbeats 1000000 in

theorem eq_const_of_val {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ} (d : DeltaDat Xo c n) (hs : d.cδ ∈ sec d.Xo₂ d.c₂ 0 0) (a : d.c₂.F)
    (hval : ∀ y : FrPt d.Xo₂ d.c₂ (CAt (c.F.val.toRingHom.comp (d.eF.symm : d.c₂.F →+* c.F))),
      toC (evR d.Xo₂ d.c₂ d.cδ y) = ((d.eF.symm a : c.F) : ℂ)) :
    d.cδ = a • (1 : Rul d.Xo₂ d.c₂) := by
  have h1 : (1 : Rul d.Xo₂ d.c₂) ∈ sec d.Xo₂ d.c₂ 0 0 := GlobalTheory.LevelCover.one_mem_sec_zero _ _
  have hz : d.cδ + (-a) • (1 : Rul d.Xo₂ d.c₂) = 0 := by
    refine GlobalTheory.GalTw.CharSec.sec_eq_zero_of_complex (c.F.val.toRingHom.comp (d.eF.symm : d.c₂.F →+* c.F))
      (add_mem hs (Submodule.smul_mem _ _ h1)) fun y => ?_
    have e1 : evR d.Xo₂ d.c₂ (1 : Rul d.Xo₂ d.c₂) y = 1 :=
      evalAt_one _ _ y (GlobalTheory.Frames.allTest_of_secBaseChange GlobalTheory.firstFiveLaws.1.secBaseChange E H Dw d.l₂ d.Xo₂ d.c₂ _ y)
    have e2 : evR d.Xo₂ d.c₂ d.cδ y = algebraMap d.c₂.F _ a := hval y
    unfold evR at e1 e2 ⊢
    rw [evalAt_add, evalAt_smul, e1, e2, mul_one, map_neg, add_neg_cancel]
  rw [neg_smul, ← sub_eq_add_neg, sub_eq_zero] at hz
  exact hz

end GlobalTheory.GalRef

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

set_option synthInstance.maxHeartbeats 200000

namespace GlobalTheory.GalRef

set_option maxHeartbeats 4000000 in

theorem exists_root_galRul_isSum : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : Fin D.R.m → ℂ), 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → GlobalTheory.Hk3.Core R F → Finite T0 → Nonempty (FWTie T R κ v₀) → IoExt R → QGuard R → ∀ i : Fin D.R.m, OMPins T R κ v₀ O i → PhaseTie T R κ v₀ O ph i → ∀ M : OMDat T.toCore R i T0 id, M.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) → M.lev = (O i).lev → (∀ c, ExtC R i (inC (O i).c') (O i).c0' c ↔ ExtC R i (inC M.c') M.c0' c) → Normal ℚ M.c'.F → GlobalTheory.CompRat.CurveOver T.Q.H M.c'.F 1 → (∀ t x, ((R.xi t x : Circle) : ℂ) ∈ M.c'.F) → (∀ t t' : T0, R.Q t' = R.Q t → ∃ e, SameCover M t t' e) → ∃ c₀ : M.c'.F, IsRoot1 ((c₀ : M.c'.F) : ℂ) ∧ ∀ (τ : ℂ ≃+* ℂ) (ta : M.c'.F ≃+* M.c'.F), (∀ a : M.c'.F, ((ta a : M.c'.F) : ℂ) = τ (a : ℂ)) → FixBase T R i τ → ∀ (hf : Fixes M.c' ta) (x x' : M.Cl' A.μ0 → VsV D i M.c'.F), (∀ k, M.io (x' k) = MvPolynomial.map (ta : M.c'.F →+* M.c'.F) (M.io (x k))) → ∀ f ∈ sec (T.Q.Xo ((i : ℕ) + 1)) M.c' (wtA (κ i)) (Vc D i).rank, GlobalTheory.OneMapAll.IsSum M A.μ0 x f → (ta c₀ * c₀⁻¹)⁻¹ • galRul hf f ∈ sec (T.Q.Xo ((i : ℕ) + 1)) M.c' (wtA (κ i)) (Vc D i).rank ∧ GlobalTheory.OneMapAll.IsSum M A.μ0 x' ((ta c₀ * c₀⁻¹)⁻¹ • galRul hf f) := by
  intro hC D G _ _ Pl0 T0 A T _ R F κ v₀ O ph hnV hcore hfin hfw hioE hQG i hpins htie M hM hlev hext hnorm hcurve hxiF
    hsame
  obtain ⟨fw⟩ := hfw
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩
  have hσ : GoodEmb T.Q.c M.s0 := rfl
  obtain ⟨hι, hx₀⟩ := GlobalTheory.TupleCover.iotaOK_and_frame T fw.laws _ hj _ hσ (Wc D i) M.hV (rank_Wc i)
  have hpq : 1 ≤ (T.Q.Dw ((i : ℕ) + 1)).p + (T.Q.Dw ((i : ℕ) + 1)).q := by
    obtain ⟨h1, -, h3⟩ := (GlobalTheory.Member.exists_iotaOK D T.Q fw.laws.pins _ hj).2
    omega
  have hRxi : R.xi A.μ0 = 1 :=
    MonoidHom.ext (GlobalTheory.TwistFactorCompare.eq_one_of_chrEq_one (hcore.lev.xi_base ▸ hcore.lev.xi A.μ0))
  have hxi1 : ∀ h : GA D (Wc D i), M.xi A.μ0 (Matrix.GeneralLinearGroup.det (finHom (Wc D i) h)) = 1 := fun h => by
    obtain ⟨x, hx⟩ := (GlobalTheory.Member.isDetRoot_laws D (Wc D i)).1 h
    have e : _ = ((R.xi A.μ0 x : Circle) : ℂ) := (hM.tuple A.μ0).xi h x hx
    rw [hRxi, MonoidHom.one_apply, Circle.coe_one] at e
    exact Units.ext e
  obtain ⟨c0, ⟨m, hm, hc0⟩, hv⟩ := hM.cxi
  obtain ⟨hd, hA, hN⟩ := hM.cov A.μ0
  have hs := hd.2.2.2.2.2.2.2.1
  have hc0ne : c0 ≠ 0 := by
    rintro rfl
    rw [zero_pow hm.ne'] at hc0
    exact zero_ne_one hc0
  obtain ⟨hval, ⟨y₀⟩⟩ := GlobalTheory.GalRef.val_of_cXiAt (Wc D i) (rank_Wc i) (M.dδ A.μ0) (iotaW T i) hι hpq _ hx₀ hA hs
    (M.xi A.μ0) hxi1 (M.U₂ A.μ0) (M.dict₂ A.μ0) c0 hc0ne (hv A.μ0)
  have hmem := GlobalTheory.GalRef.mem_of_val (M.dδ A.μ0) hs c0 m hm hc0 hval y₀
  let c₀ : M.c'.F := ⟨c0, hmem⟩
  have hc₀ne : c₀ ≠ 0 := fun h => hc0ne (congrArg Subtype.val h)
  have hcδ : (M.dδ A.μ0).cδ = (M.dδ A.μ0).eF c₀ • (1 : Rul (M.dδ A.μ0).Xo₂ (M.dδ A.μ0).c₂) :=
    GlobalTheory.GalRef.eq_const_of_val _ hs _ fun y => by
      rw [hval y, AlgEquiv.symm_apply_apply]
  refine ⟨c₀, ⟨m, hm, hc0⟩, ?_⟩
  intro τ ta hta hfb hf x x' hx f hfs hsum
  have h₂ : Fixes (M.dδ A.μ0).c₂ (covAut (M.dδ A.μ0) ta) := GlobalTheory.GalTw.fixes_covAut (M.dδ A.μ0) hA hf
  have hka : ta c₀ * c₀⁻¹ ≠ 0 := mul_ne_zero ((map_ne_zero ta).2 hc₀ne) (inv_ne_zero hc₀ne)
  have hgal : galRul h₂ (M.dδ A.μ0).cδ = (M.dδ A.μ0).eF (ta c₀ * c₀⁻¹) • (M.dδ A.μ0).cδ := by
    rw [hcδ, GlobalTheory.GalTw.Test.galRul_const, covAut_apply_eF, smul_smul, ← map_mul, mul_assoc, inv_mul_cancel₀ hc₀ne,
      mul_one]
  have hcx : ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra (M.dδ A.μ0).c₂.F k] (y₂ : FrPt (M.dδ A.μ0).Xo₂ (M.dδ A.μ0).c₂ k),
      evR (M.dδ A.μ0).Xo₂ (M.dδ A.μ0).c₂ (galRul h₂ (M.dδ A.μ0).cδ) y₂ =
        algebraMap (M.dδ A.μ0).c₂.F k ((M.dδ A.μ0).eF (ta c₀ * c₀⁻¹)) * evR (M.dδ A.μ0).Xo₂ (M.dδ A.μ0).c₂ (M.dδ A.μ0).cδ y₂ := by
    intro k _ _ _ y₂
    rw [hgal]
    exact evalAt_smul _ _ _ _ y₂
  have hsame0 : SameCover M A.μ0 A.μ0 (Equiv.refl _) :=
    ⟨⟨_, rfl⟩, HEq.rfl, HEq.rfl, rfl, rfl, fun _ => ⟨rfl, rfl, rfl, rfl⟩⟩
  have hconj : ConjTup R τ (id A.μ0) (id A.μ0) := ⟨rfl, fun x => by simp [hRxi]⟩
  obtain ⟨u, s, w', hu, hw'e, hw⟩ := GlobalTheory.T.conj_fourierCoefficients_conjugate_tuples D G Pl0 T0 A T R F κ v₀ hcore ⟨fw⟩ i T0 id M hM τ ta hta hfb A.μ0 A.μ0
    (Equiv.refl _) hsame0 hconj
  obtain ⟨hvol, hep⟩ := GlobalTheory.T.galoisConj_classScalars_and_volume D G Pl0 T0 A T R F κ v₀ hcore ⟨fw⟩ i T0 id M hM τ ta hta hfb A.μ0 A.μ0
    (Equiv.refl _) hsame0 hconj
  have hu1 : u = 1 := by
    apply Subtype.ext
    rw [hu]
    simp [hRxi]
  have hw'1 : w' = M.w A.μ0 := funext fun k => eq_of_heq (hw'e k)
  subst hu1 hw'1
  have hio : ∀ v, M.io v ∈ HHa (T.Q.Dw ((i : ℕ) + 1)).mult (Vc D i).rank M.c'.F ComplexEmbedding.conjugate
      (InPsi T.Q.H) (fun τ k => wtA (κ i) (τ, k)) := fun v => by
    obtain ⟨-, cga, -, -, hr, -⟩ := hM.io
    have hv := hr.le (LinearMap.mem_range_self M.io v)
    exact (Submodule.span_le (p := GlobalTheory.FrameRead.CoefMap.harmSub _ _ _ _ _ _)).2 (fun _ hP => hP) hv
  have key := GlobalTheory.GalTw.isThClsD_galRul hC _ _ _ _ _ M.c' ta hf _ (M.dδ A.μ0) h₂ hN hs (M.dδ A.μ0).cδ
    (ta c₀ * c₀⁻¹) 1 hka one_ne_zero hcx (M.Cl' A.μ0) (M.w A.μ0) (M.w A.μ0) (M.La A.μ0) (M.Nc A.μ0) (M.gam A.μ0)
    (M.vol A.μ0) (M.ep A.μ0) _ M.io (wtA (κ i)) hio hw x x' hx _ f hfs hsum
  rw [mul_one] at key
  refine ⟨key.1, ?_⟩
  have e1 : ta (M.vol A.μ0) = M.vol A.μ0 := hvol
  have e2 : (fun k => ta (M.ep A.μ0 k)) = M.ep A.μ0 := funext hep
  have k2 := key.2
  rw [e1, e2] at k2
  exact k2

end GlobalTheory.GalRef
