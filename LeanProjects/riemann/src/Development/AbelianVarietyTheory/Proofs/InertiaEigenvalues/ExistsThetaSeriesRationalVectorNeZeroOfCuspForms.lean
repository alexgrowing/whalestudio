import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRatScalarMulIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsScaleOfChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjFunBaseRoot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGoodCoverGalois
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsConjugateFormsThetaLiftEqThetaSeriesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HolomorphicSectionsSpanRestrictionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassSumsSpanCuspFormsBaseTupleSecondFieldStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemOfForallRingEquivFixed
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftEqClassSumThetaKernelsLowestKType
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkMapInitMinor
import Formalism.LocalToGlobal.Columns.MtIsoVal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormsBaseChangeSecondFieldNeBotStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCentralTranslateUniformisationCuspFormNeZeStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.IndefR.Links IsDedekindDomain NumberField GlobalTheory.ExportSeries Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels GlobalTheory.ConjTwist
open Formalism.L2.Host (embLL0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SeriesTie.RatNe

theorem thetaKO_sum' {D : D7} {S T : HSp D} (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (x : GA D S) (g : GA D T)
    {ι : Type} (s : Finset ι) (c : ι → ℂ) (φ : ι → WO S T → ℂ) :
    thetaKO om x g (∑ k ∈ s, c k • φ k) = ∑ k ∈ s, c k * thetaKO om x g (φ k) := by
  unfold thetaKO
  rw [map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, Pi.smul_apply, smul_eq_mul]

theorem ser_sum {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T0 : Type} {A : FamIn D.what₂.LL Γ Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) (t : T0)
    (f : WO (Vc D i) (Wc D i) → ℂ) (u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (h : GA D (Vc D i)) (g : GA D (Wc D i))
    {ι : Type} (s : Finset ι) (a : ι → ℂ) (w : ι → (R.cV i).W) :
    ser R i t f u h (∑ k ∈ s, a k • w k) g = ∑ k ∈ s, a k * ser R i t f u h (w k) g := by
  unfold ser
  rw [map_sum, map_sum]
  simp only [map_smul]
  exact thetaKO_sum' _ _ _ _ _ _

theorem exists_rat_of_ser_ne {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T0 : Type} {A : FamIn D.what₂.LL Γ Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) (t : T0)
    (f : WO (Vc D i) (Wc D i) → ℂ) (u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (h : GA D (Vc D i)) (g : GA D (Wc D i))
    {K' : Type} [Field K'] (σ' : K' →+* ℂ) (ψ : K' →+* D.what₂.LL) (c0' : VsV D i K' →ₛₗ[σ'] (R.cV i).W)
    (c : VsV D i ℂ →ₗ[ℂ] (R.cV i).W) (hc : ExtC R i σ' c0' c) (w : VsV D i K')
    (hne : ser R i t f u h (c0' w) g ≠ 0) :
    ∃ (v : VsV D i D.what₂.LL) (x : VsV D i ℂ),
      (∀ m, ∃ q : ℚ, MvPolynomial.coeff m (v : Pol D.what₂.LL D.what₂.Tau (Vc D i).rank) = (q : D.what₂.LL)) ∧
      (x : Pol ℂ D.what₂.Tau (Vc D i).rank) = MvPolynomial.map D.what₂.embLL (v : Pol D.what₂.LL D.what₂.Tau (Vc D i).rank) ∧
      ser R i t f u h (c x) g ≠ 0 := by
  classical
  have hw' : c0' w = ∑ b, σ' ((bVV K' (lamV D i)).repr w b) • c0' (bVV K' (lamV D i) b) := by
    conv_lhs => rw [← (bVV K' (lamV D i)).sum_repr w]
    rw [map_sum]
    simp only [map_smulₛₗ]
  rw [hw', ser_sum] at hne
  obtain ⟨b, -, hb⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  have hb' := right_ne_zero_of_mul hb
  obtain ⟨P, hP⟩ := bVVfun_int K' (lamV D i) b
  have hvmem : MvPolynomial.map (Int.castRingHom D.what₂.LL) P ∈ VV D.what₂.LL (lamV D i) := by
    have := Formalism.L2.Col.mti_map_mem_VV ψ (lamV D i) (bVV K' (lamV D i) b).2
    rwa [bVV_coe, hP, MvPolynomial.map_map, show ψ.comp (Int.castRingHom K') = Int.castRingHom _ from
      RingHom.ext_int _ _] at this
  have hxmem : MvPolynomial.map (Int.castRingHom ℂ) P ∈ VV ℂ (lamV D i) := by
    have := Formalism.L2.Col.mti_map_mem_VV σ' (lamV D i) (bVV K' (lamV D i) b).2
    rwa [bVV_coe, hP, MvPolynomial.map_map, show σ'.comp (Int.castRingHom K') = Int.castRingHom _ from
      RingHom.ext_int _ _] at this
  refine ⟨⟨_, hvmem⟩, ⟨_, hxmem⟩, fun m => ⟨((MvPolynomial.coeff m P : ℤ) : ℚ), ?_⟩, ?_, ?_⟩
  · show MvPolynomial.coeff m (MvPolynomial.map (Int.castRingHom D.what₂.LL) P) = _
    rw [MvPolynomial.coeff_map]
    simp
  · show MvPolynomial.map (Int.castRingHom ℂ) P = MvPolynomial.map D.what₂.embLL (MvPolynomial.map (Int.castRingHom D.what₂.LL) P)
    rw [MvPolynomial.map_map, RingHom.ext_int (D.what₂.embLL.comp (Int.castRingHom D.what₂.LL)) (Int.castRingHom ℂ)]
  · rwa [hc (bVV K' (lamV D i) b) ⟨_, hxmem⟩ (by
      show MvPolynomial.map (Int.castRingHom ℂ) P = MvPolynomial.map σ' ((bVV K' (lamV D i) b : VV K' (lamV D i)) : Pol K' D.what₂.Tau (Vc D i).rank)
      rw [bVV_coe, hP, MvPolynomial.map_map, RingHom.ext_int (σ'.comp (Int.castRingHom K')) (Int.castRingHom ℂ)])]

end GlobalTheory.SeriesTie.RatNe

namespace GlobalTheory.SeriesTie.RatNe

set_option maxHeartbeats 2000000 in
open GlobalTheory.OneMapAll in
theorem exists_ser_rat_ne : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T0 : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (Rl : RealDat3 D A3 T.Q.c.F) (F : Face D A3.A) (κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) (O : ∀ j, OMDat T.toCore Rl.toRealDat j Unit (fun _ => A3.A.μ0)), 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → GlobalTheory.Hk3.Core Rl.toRealDat F → Nonempty (FWTie T Rl.toRealDat κ v₀) → IoExt Rl.toRealDat → ∀ (j : Fin D.R.m), OMPins T Rl.toRealDat κ v₀ O j → OneMapRow0 T Rl.toRealDat κ v₀ O j → T.toCore.cuspA ((j : ℕ) + 1) (wtA (κ j)) (κ j).n ≠ ⊥ → ∀ (c : VsV D j ℂ →ₗ[ℂ] (Rl.cV j).W), ExtC Rl.toRealDat j (inC (O j).c') (O j).c0' c → ∀ (u : ∀ ρ, lowT (Rl.MW j (sg0 D A3.A)) ρ), (∀ ρ, (u ρ : (Rl.MW j (sg0 D A3.A)).sm ρ) = v₀ j _ ρ) → ∃ (v : VsV D j D.what₂.LL) (x : VsV D j ℂ) (h : GA D (Vc D j)) (g : GA D (Wc D j)), (∀ m, ∃ q : ℚ, MvPolynomial.coeff m (v : Pol D.what₂.LL D.what₂.Tau (Vc D j).rank) = (q : D.what₂.LL)) ∧ (x : Pol ℂ D.what₂.Tau (Vc D j).rank) = MvPolynomial.map D.what₂.embLL (v : Pol D.what₂.LL D.what₂.Tau (Vc D j).rank) ∧ h ∈ GfC (Vc D j) ∧ ser Rl.toRealDat j A3.A.μ0 (Rl.vP j A3.A.μ0) u h (c x) g ≠ 0 := by
  intro D Γ _ _ Pl0 I0 T0 A3 T _ Rl F κ v₀ O hnV hC hFW hIo j hP hrow hne c hc u hu
  have hspan := GlobalTheory.ClassSumSpanCore.classSumsSpan_core D Γ Pl0 T0 A3.A T Rl.toRealDat F κ v₀ O hnV hC hFW hIo j hP hrow
  have hA1 : cuspOver (O j) (κ j) ≠ ⊥ := GlobalTheory.T.cuspForms_baseChange_secondField_ne_bot D Γ Pl0 T0 A3.A T Rl.toRealDat F κ v₀ O hnV hC hFW hIo j hP hrow hne
  obtain ⟨g0, ⟨hg0, x, hx, hsum⟩, hg0ne⟩ : ∃ g0 ∈ {g | g ∈ cuspOver (O j) (κ j) ∧ ∃ x, (O j).Plc () x ∧ IsSum (O j) () x g},
      g0 ≠ 0 := by
    by_contra hcon
    push Not at hcon
    refine hA1 (eq_bot_iff.2 (hspan.trans ((Submodule.span_le).2 fun g hg => ?_)))
    rw [SetLike.mem_coe, hcon g hg]
    exact Submodule.zero_mem _
  have hrow' := hrow
  obtain ⟨cc, ph, hO⟩ := hrow'
  obtain ⟨-, ⟨-, -, -, hcc, hph, z, hz, hR⟩, -⟩ := hO
  obtain ⟨ze, -, ⟨m, hm, hze⟩, hR⟩ := hR ()
  have hid := (hR x hx).2 g0 ((mem_cusp _ _ _ _ _ _).1 hg0).1 hsum
  obtain ⟨q, hq⟩ : ∃ q, jFn (Wc D j) (inC (O j).c') (rdU (unfBC (O j).hle (T.toCore.U ((j : ℕ) + 1)) (inC (O j).c')))
      (O j).dict (O j).mu (actLev (O j).c' (O j).lev2 z g0) q ≠ 0 :=
    GlobalTheory.T.exists_centralTranslate_uniformisation_cuspForm_ne_zero D Γ Pl0 T0 A3.A T Rl.toRealDat F κ v₀ O hnV hC hFW hIo j hP hrow g0 hg0 hg0ne z hz
  have hth : (O j).thAd () x q ≠ 0 := by
    intro h0
    have e := hid q
    rw [h0, mul_zero] at e
    have hze0 : ze ≠ 0 := fun h => by simp [h, hm.ne'] at hze
    have hcc0 : cc ((O j).dict q.out).1 ≠ 0 := fun h => by simpa [h] using hcc ((O j).dict q.out).1
    have hl : ((lieFac (T.toCore.Q.Dw ((j : ℕ) + 1)) (xiR D) (wtA (κ j)) : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.2 (lieFac_pos _ _ _).ne'
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero hze0 hcc0) hl) hq) e.symm
  obtain ⟨hLL, hPins⟩ := hP
  obtain ⟨hs, J', hRep, -, hTh, hPlc⟩ := (hPins.tuple ()).reps
  obtain ⟨x₀, hpl⟩ := (hPlc x).1 hx
  have e1 := hTh _ x hpl
  rw [e1] at hth
  have hv : (fun ρ => (u ρ : (Rl.toRealDat.MW j (sg0 D A3.A)).sm ρ)) = v₀ j (sg0 D A3.A) := funext hu
  have hcls := GlobalTheory.LiftUnfoldCore.thF_eq_classSum_core D Γ Pl0 T0 A3.A T.Q.c.F Rl.toRealDat F hC j A3.A.μ0 (O j).c'.F
    (inC (O j).c') (O j).c0' ((O j).Cl' ()) hs ((O j).bad ()) J' ((O j).Lh ()) ((O j).gam ()) ((O j).vol ()) hPins.lift.std hRep
    _ x hpl u q.out
  rw [hv] at hcls
  change Rl.toRealDat.thF j A3.A.μ0 (jVx Rl.toRealDat j A3.A.μ0 x₀) (v₀ j (sg0 D A3.A)) q.out ≠ 0 at hth
  rw [hcls] at hth
  obtain ⟨k, -, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero hth
  have hk' : ser Rl.toRealDat j A3.A.μ0 (Rl.vP j A3.A.μ0) u (hs k) ((O j).c0' (x k)) q.out ≠ 0 := right_ne_zero_of_mul hk
  have hsurj : Function.Surjective (O j).jL := by
    intro a
    have ha : (a : ℂ) ∈ D.what₂.embLL.toRatAlgHom.fieldRange := hLL ▸ a.2
    obtain ⟨y, hy⟩ := AlgHom.mem_fieldRange.1 ha
    refine ⟨y, Subtype.ext ?_⟩
    have := RingHom.congr_fun hPins.lift.field y
    exact this.trans hy
  let ψ : (O j).c'.F →+* D.what₂.LL := (RingEquiv.ofBijective (O j).jL ⟨(O j).jL.injective, hsurj⟩).symm.toRingHom
  obtain ⟨v, x', hv1, hv2, hv3⟩ := exists_rat_of_ser_ne Rl.toRealDat j A3.A.μ0 _ u (hs k) q.out (inC (O j).c') ψ (O j).c0' c hc
    (x k) hk'
  exact ⟨v, x', hs k, q.out, hv1, hv2, (hRep.2.2.2.2.2.2 k).1.1, hv3⟩

end GlobalTheory.SeriesTie.RatNe
