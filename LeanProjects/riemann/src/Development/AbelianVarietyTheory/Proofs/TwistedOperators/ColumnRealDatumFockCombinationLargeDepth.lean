import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestDefinitePeriodChangeOfMeasures
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpAttChrMu
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselColumnScalarFunctionContinuousLeftInvariant
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.KerFockMovedReal
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleLiftReductionToFockVectorsUniform
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawWeilBiActionCommutes
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CentralEigenThetaIsFockVectorBoundedDegree
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OmZeroRat
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealCentreActsByCharacterOnIsotypicSlices
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationCommFockPolynomialVectors
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SetIntegralFundamentalDomainRightTranslateInvari
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContAutRapidDecBoundedIntegrable
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealComponentCentralDefiniteUnitaryEqUnitScalar
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefficientSpaceEndomorphismScalarSchur
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AdelicUnitaryTopCong
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ColFockPf

section Generic

variable {D : D7}

theorem vol_scale {V : HSp D} (v v' : GlobalTheory.Unf.Vol V) : ∃ s : ℂ, s ≠ 0 ∧ ∀ f : GA D V → ℂ, (∀ γ ∈ GQ V, ∀ x, f (γ * x) = f x) →
    ∫ x in v.𝓕, f x ∂v.μ = s * ∫ x in v'.𝓕, f x ∂v'.μ := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.Ker.CongTop.adelicUnitary_top_cong D V
  haveI := v.haar
  haveI := v'.haar
  refine ⟨((Measure.haarScalarFactor v.μ v'.μ : ℝ) : ℂ), ?_, fun f hf => GlobalTheory.RowVal.fd_int_scale v.haar v'.haar
    (Measure.isMulLeftInvariant_eq_smul v.μ v'.μ) v.fund v'.fund f hf⟩
  exact_mod_cast (Measure.haarScalarFactor_pos_of_isHaarMeasure v.μ v'.μ).ne'

variable {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}

theorem fix_left {S T : HSp D} {χS χT} {om : Om S T} (hw : IsWeilDatumO ψ S T χS χT om) {Y : WO S T → ℂ}
    (hY : IsThetaFunO ψ S T Y) (g : GA D S) (h : GA D T) {γ : GA D S} (hγ : γ ∈ GQ S) : om (γ * g, h) Y 0 = om (g, h) Y 0 := by
  have e : ((γ * g, h) : GA D S × GA D T) = (γ, 1) * (g, h) := by simp
  rw [e, map_mul, Module.End.mul_apply]
  exact hw.om_aut γ hγ 1 (one_mem _) _ (hw.om_pres _ Y hY)

theorem fix_right {S T : HSp D} {χS χT} {om : Om S T} (hw : IsWeilDatumO ψ S T χS χT om) {Y : WO S T → ℂ}
    (hY : IsThetaFunO ψ S T Y) (g : GA D S) (h : GA D T) {γ : GA D T} (hγ : γ ∈ GQ T) : om (g, γ * h) Y 0 = om (g, h) Y 0 := by
  have e : ((g, γ * h) : GA D S × GA D T) = (1, γ) * (g, h) := by simp
  rw [e, map_mul, Module.End.mul_apply]
  exact hw.om_aut 1 (one_mem _) γ hγ _ (hw.om_pres _ Y hY)

theorem lift_cen (hθ : IsInfFam θ) {S T : HSp D} {x : DefSp S} {y : DefSp T} (hx : x.Is) (hy : y.Is) {k₀ : KerDat S T}
    (hk₀ : k₀.Is ψ θ x y) (χ : GA D S → ℂ) : ∃ χ' : GA D T → ℂ, ∀ (v : GlobalTheory.Unf.Vol S) (k : KerDat S T), k.Is ψ θ x y →
      k.vac = k₀.vac → (∀ a ∈ GinfC S, ∀ b ∈ GinfC T, ∀ f, IsThetaFunO ψ S T f → k.om (a, b) f = k₀.om (a, b) f) →
      ∀ P φ, GlobalTheory.Unf.IsContAut S φ → HasCen S χ φ → HasCen T χ' (GlobalTheory.MixPer.liftT k.om v.μ v.𝓕 φ (k.pt ψ θ x y P)) := by
  have key : ∀ b : GA D T, ∃ s : ℂ, b ∈ GinfC T → b ∈ Subgroup.center (GA D T) → ∀ (v : GlobalTheory.Unf.Vol S) (k : KerDat S T),
      k.Is ψ θ x y → k.vac = k₀.vac →
      (∀ a ∈ GinfC S, ∀ b ∈ GinfC T, ∀ f, IsThetaFunO ψ S T f → k.om (a, b) f = k₀.om (a, b) f) →
      ∀ P φ, GlobalTheory.Unf.IsContAut S φ → HasCen S χ φ → ∀ h, GlobalTheory.MixPer.liftT k.om v.μ v.𝓕 φ (k.pt ψ θ x y P) (h * b) =
        s * GlobalTheory.MixPer.liftT k.om v.μ v.𝓕 φ (k.pt ψ θ x y P) h := by
    intro b
    by_cases hb : b ∈ GinfC T ∧ b ∈ Subgroup.center (GA D T)
    swap
    · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ hb⟩
    rcases isEmpty_or_nonempty (Fin T.rank) with h0 | ⟨⟨i₀⟩⟩
    · have e : b = 1 := Subtype.ext (Units.ext (Subsingleton.elim _ _))
      exact ⟨1, fun _ _ _ _ _ _ _ _ _ _ _ h => by rw [e, mul_one, one_mul]⟩
    obtain ⟨a, ha, hac, c, c', hcc, e1, e2⟩ := GlobalTheory.CentreTarget.exists_central_realPoint_same_scalar_other_group S hy hb.1 hb.2 i₀
    obtain ⟨l, hl⟩ := GlobalTheory.CentreTarget.weilOperator_equal_scalars_acts_by_scalar_fock hθ hx hy hk₀ hcc e1 e2
    refine ⟨l * χ a, fun _ _ v k hk hv hag P φ hφ hc h => ?_⟩
    obtain ⟨χS, χT, hW⟩ := hk.weil
    have hvt : IsThetaFunO ψ S T k.vac := hk.vac.2.theta
    have h3 : ∀ w, actO S T a b w = w := fun w => by
      unfold actO
      rw [e1, e2, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul, mul_comm, hcc, one_smul]
    have hF := GlobalTheory.GalLift.Vec.theta_pureTensorO hW.std hθ x.s x.B y.s y.B hvt P
    have hcomb : ∀ g, comb ψ S T k.c g = ∑ i : Fin k.c.support.card,
        k.c (k.c.support.equivFin.symm i) • heisO ψ S T (k.c.support.equivFin.symm i) g := by
      intro g
      unfold comb
      rw [← Finset.sum_coe_sort]
      exact (Equiv.sum_comp k.c.support.equivFin.symm (fun u => k.c u • heisO ψ S T u g)).symm
    have key1 : k.pt ψ θ x y P = comb ψ S T k.c (pureTensorO ψ θ S T x.s y.s x.B y.B k.vac P) := by
      unfold KerDat.pt
      rw [hcomb, hcomb]
      exact (GlobalTheory.FockFiniteHeis.heis_comb_pureTensorO D ψ θ S T hW.std hθ x.s y.s x.B y.B _ hvt k.c.support.card _ _
        (fun i => hk.fin _ (Finset.coe_mem _)) P).1.symm
    have key2 : k.om (a, b) (k.pt ψ θ x y P) = l • k.pt ψ θ x y P := by
      rw [key1]
      unfold comb
      rw [map_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [map_smul, hW.om_heis a b u _ hF, h3, hag a ha b hb.1 _ hF, hv, hl, smul_comm]
      congr 1
      funext w
      simp only [heisO, Pi.smul_apply, smul_eq_mul]
      ring
    have hpt := (GlobalTheory.SeeSaw.LiftSumProof.liftSum D ψ θ hθ S T x y hx hy k hk P).1
    rw [liftT_apply, liftT_apply, ← GlobalTheory.ChainOnto.setIntegral_fd_mul_right D S v.μ v.𝓕 v.haar v.fund
      (fun g => k.om (g, h * b) (k.pt ψ θ x y P) 0 * φ g) (fun γ hγ g => by rw [fix_left hW hpt g _ hγ, hφ.1 γ hγ g]) a,
      ← integral_const_mul]
    congr 1
    funext g
    have e : ((g * a, h * b) : GA D S × GA D T) = (g, h) * (a, b) := rfl
    rw [e, map_mul, Module.End.mul_apply, key2, map_smul, hc a ha hac, Pi.smul_apply, smul_eq_mul]
    ring
  choose χ' h using key
  exact ⟨χ', fun v k hk hv hag P φ hφ hc b h1 h2 g => h b h1 h2 v k hk hv hag P φ hφ hc g⟩

abbrev wv {V : HSp D} (x : DefSp V) (v : GlobalTheory.Unf.Vol V) : DefSp V := ⟨x.s, x.B, x.L, v⟩

theorem wv_is {V : HSp D} {x : DefSp V} (hx : x.Is) (v : GlobalTheory.Unf.Vol V) : (wv x v).Is :=
  ⟨hx.sig, hx.cpt, hx.cart, hx.pm, hx.onb, hx.sd⟩

theorem ker_wv {S T : HSp D} {x : DefSp S} {y : DefSp T} {k : KerDat S T} (hk : k.Is ψ θ x y) (v : GlobalTheory.Unf.Vol S)
    (v' : GlobalTheory.Unf.Vol T) : k.Is ψ θ (wv x v) (wv y v') := ⟨hk.weil, hk.vac, hk.fin⟩

theorem step (hθ : IsInfFam θ) {A S A' : HSp D} {x : DefSp A} {y : DefSp S} {z : DefSp A'} (hx : x.Is) (hy : y.Is) (hz : z.Is)
    {k₀ : KerDat A S} {k₀' : KerDat S A'} (hk₀ : k₀.Is ψ θ x y) (hk₀' : k₀'.Is ψ θ y z) (χ : GA D A → ℂ)
    {C : WO A S → WO S A' → ℂ} (hC : IsBiVac ψ A S A' x.L y.L z.L C) (hs : IsBiSmooth C) :
    ∃ (n : ℕ) (P : Fin n → PolF D S.rank A.rank) (P' : Fin n → PolF D A'.rank S.rank) (χ' : GA D A' → ℂ),
      ∀ (vA : GlobalTheory.Unf.Vol A) (vS : GlobalTheory.Unf.Vol S) (k : KerDat A S) (k' : KerDat S A'), k.Is ψ θ x y → k'.Is ψ θ y z →
        k.vac = k₀.vac → k'.vac = k₀'.vac →
        (∀ a ∈ GinfC A, ∀ b ∈ GinfC S, ∀ f, IsThetaFunO ψ A S f → k.om (a, b) f = k₀.om (a, b) f) →
        (∀ a ∈ GinfC S, ∀ b ∈ GinfC A', ∀ f, IsThetaFunO ψ S A' f → k'.om (a, b) f = k₀'.om (a, b) f) →
        ∀ φ, GlobalTheory.Unf.IsContAut A φ → HasCen A χ φ →
          biLift k.om k'.om vA vS φ (biComb ψ A S A' k.c k'.c C) =
            ∑ i, k'.lift ψ θ (wv y vS) z (P' i) (k.lift ψ θ (wv x vA) (wv y vS) (P i) φ) ∧
          HasCen A' χ' (biLift k.om k'.om vA vS φ (biComb ψ A S A' k.c k'.c C)) := by
  have hL := GlobalTheory.SeeSaw.LiftSumProof.liftSum D
  obtain ⟨n, P, P', hF⟩ := fockRed_uniform D (biAct_all D) (GlobalTheory.SeeSaw.CenFockPf.cenFock D) hL ψ θ hθ A S A' x y z hx hy hz
    k₀ k₀' hk₀ hk₀' χ C hC hs
  obtain ⟨χ₁, h₁⟩ := lift_cen hθ hx hy hk₀ χ
  obtain ⟨χ₂, h₂⟩ := lift_cen hθ hy hz hk₀' χ₁
  refine ⟨n, P, P', χ₂, fun vA vS k k' hk hk' hv hv' ha ha' φ hφ hc => ?_⟩
  have hc1 : ∀ v i, GlobalTheory.Unf.IsContAut S (k.lift ψ θ (wv x v) y (P i) φ) := fun v i =>
    (hL ψ θ hθ A S _ y (wv_is hx v) hy k (ker_wv hk v y.vol) (P i)).2.1 φ hφ
  have e : biLift k.om k'.om vA vS φ (biComb ψ A S A' k.c k'.c C) =
      ∑ i, k'.lift ψ θ (wv y vS) z (P' i) (k.lift ψ θ (wv x vA) (wv y vS) (P i) φ) := by
    obtain ⟨χa, χb, hW⟩ := hk.weil
    obtain ⟨χc, χd, hW'⟩ := hk'.weil
    obtain ⟨s, -, hsA⟩ := vol_scale vA x.vol
    obtain ⟨s', -, hsS⟩ := vol_scale vS y.vol
    have hG : IsBiTheta ψ A S A' (biComb ψ A S A' k.c k'.c C) :=
      GlobalTheory.FrComb.biTheta_combL hW.std (GlobalTheory.FrComb.biTheta_combR hW.std
        (GlobalTheory.FrComb.biTheta_of_vac hx.sd hy.sd hz.sd hC hs) hk'.fin) hk.fin
    have e0 := hF k k' hk hk' hv hv' ha ha' φ hφ hc
    have l1 : ∀ i, k.lift ψ θ (wv x vA) (wv y vS) (P i) φ = s • k.lift ψ θ x y (P i) φ := fun i => funext fun h =>
      hsA _ fun γ hγ g => by
        show k.om (γ * g, h) (k.pt ψ θ x y (P i)) 0 * φ (γ * g) = k.om (g, h) (k.pt ψ θ x y (P i)) 0 * φ g
        rw [fix_left hW (hL ψ θ hθ A S x y hx hy k hk (P i)).1 g _ hγ, hφ.1 γ hγ g]
    have l2 : ∀ i, k'.lift ψ θ (wv y vS) z (P' i) (s • k.lift ψ θ x y (P i) φ) =
        (s' * s) • k'.lift ψ θ y z (P' i) (k.lift ψ θ x y (P i) φ) := fun i => funext fun h => by
      have hh : ∀ φ' : GA D S → ℂ, (∀ γ ∈ GQ S, ∀ g, φ' (γ * g) = φ' g) →
          k'.lift ψ θ (wv y vS) z (P' i) φ' h = s' * k'.lift ψ θ y z (P' i) φ' h := fun φ' hφ' =>
        hsS _ fun γ hγ g => by
          show k'.om (γ * g, h) (k'.pt ψ θ y z (P' i)) 0 * φ' (γ * g) = k'.om (g, h) (k'.pt ψ θ y z (P' i)) 0 * φ' g
          rw [fix_left hW' (hL ψ θ hθ S A' y z hy hz k' hk' (P' i)).1 g _ hγ, hφ' γ hγ g]
      rw [hh _ fun γ hγ g => by simp only [Pi.smul_apply, (hc1 x.vol i).1 γ hγ g]]
      simp only [KerDat.lift, liftT_apply, Pi.smul_apply, smul_eq_mul, mul_left_comm _ s, integral_const_mul, mul_assoc]
    simp only [l1, l2]
    rw [← Finset.smul_sum, ← e0]
    generalize biComb ψ A S A' k.c k'.c C = G at hG
    have mid : ∀ p, IsThetaFunO ψ S A' fun v => k.om p (fun u => G u v) 0 := fun p =>
      biTheta_slice2 ((biAct_all D ψ _ _ _ _ _ _ _ k.om k'.om hW hW' G hG).1 p) 0
    funext h₂
    have inner : ∀ h₁, ∫ h₀ in vA.𝓕, φ h₀ * k'.om (h₁, h₂) (fun v => k.om (h₀, h₁) (fun u => G u v) 0) 0 ∂vA.μ =
        s * ∫ h₀ in x.vol.𝓕, φ h₀ * k'.om (h₁, h₂) (fun v => k.om (h₀, h₁) (fun u => G u v) 0) 0 ∂x.vol.μ := fun h₁ =>
      hsA _ fun γ hγ h₀ => by simp only [fun v => fix_left hW (biTheta_slice1 hG v) h₀ h₁ hγ, hφ.1 γ hγ h₀]
    simp only [biLift, inner, Pi.smul_apply, smul_eq_mul]
    rw [integral_const_mul, hsS]
    · ring
    · intro γ hγ h₁
      congr 1; funext h₀; congr 1
      simp only [fun v => fix_right hW (biTheta_slice1 hG v) h₀ h₁ hγ]
      exact fix_left hW' (mid _) h₁ h₂ hγ
  refine ⟨e, fun b hb hbc h => ?_⟩
  rw [e, Finset.sum_apply, Finset.sum_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ =>
    h₂ vS k' hk' hv' ha' (P' i) _ (hc1 vA i) (h₁ vA k hk hv ha (P i) φ hφ hc) b hb hbc h

end Generic

section Grid

open scoped ComplexOrder

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil)

def sp (j : ℕ) : DefSp (G.V (.top j)) :=
  ⟨W.cart (.top j), W.onb (.top j), G.Λ (.top j), (GlobalTheory.Unf.Inhab.nonempty_vol _).some⟩

theorem sp_is {j : ℕ} (hj : j ≤ D.R.m) : (sp W j).Is := by
  have hV := G.isV (X := .top j) hj (fun _ e => by cases e)
  have hp : ∀ τ, (gramAt D (G.V (.top j)) τ).PosDef := fun τ => posDef_top G hj (tauE D τ)
  have hc : ∀ τ, W.cart (.top j) τ = 1 := fun τ => GlobalTheory.FockReal.cartan_eq_one (hp τ) (W.cart_is (.top j) hj τ)
  refine ⟨hV.sigOK, GlobalTheory.Unf.Inhab.coCpt_of_posDef hp, W.cart_is (.top j) hj, fun τ => Or.inl (hc τ), fun τ => ?_, hV.sd⟩
  obtain ⟨ε, h1, h2⟩ := W.onb_is (.top j) hj τ
  rw [hc, Matrix.one_mul] at h2
  have hJ : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
    unfold Formalism.REAL.Jm
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs <;> norm_num
  have h3 : (W.onb (.top j) τ)ᴴ * gramAt D (G.V (.top j)) τ * W.onb (.top j) τ = 1 :=
    calc _ = (W.onb (.top j) τ)ᴴ * gramAt D (G.V (.top j)) τ * (W.onb (.top j) τ * Formalism.REAL.Jm ε) := by rw [← h2]
      _ = Formalism.REAL.Jm ε * Formalism.REAL.Jm ε := by rw [← Matrix.mul_assoc, h1]
      _ = 1 := hJ
  refine ⟨(G.V (.top j)).rank, fun _ => 1, fun a => Or.inl ⟨rfl, a.2⟩, ?_, ?_⟩
  · show (W.onb (.top j) τ)ᴴ * gramAt D (G.V (.top j)) τ * W.onb (.top j) τ = _
    rw [h3]; simp
  · show W.cart (.top j) τ * W.onb (.top j) τ = W.onb (.top j) τ * _
    rw [hc]; simp

theorem coCpt_last : GlobalTheory.Unf.CoCpt (G.V (.grid D.R.m D.R.m)) := by
  have h2 := D.R.two_le_m
  have hV := G.isV (X := .grid D.R.m D.R.m) ⟨le_rfl, le_rfl⟩ (fun _ e => by injection e; omega)
  refine GlobalTheory.Unf.Inhab.coCpt_of_posDef fun τ => ?_
  have := hV.sigOK (tauE D τ)
  rw [hV.sig] at this
  simp only [Node.neg, Nat.sub_self, Nat.zero_div, Nat.sub_zero] at this
  exact GlobalTheory.DefiniteQuotient.posDef_of_signature this

variable (G) in

abbrev Pols : Type := ∀ j : ℕ, PolF D (G.V (.top (j + 1))).rank (G.V (.top j)).rank

variable (v : ∀ j : ℕ, WO (G.V (.top j)) (G.V (.top (j + 1))) → ℂ)

abbrev kd (t : T) (c : Combs G) (j : ℕ) : KerDat (G.V (.top j)) (G.V (.top (j + 1))) := ⟨W.om (.top t j), v j, c.1 j⟩

def Lp (M : Vol G) (t : T) (c : Combs G) (j : ℕ) (Q : Pols G) (φ : Fn G (.top 0)) : Fn G (.top j) :=
  liftP W M (colPath t j) (colFam t j fun i : Fin j => W.fock (.top t i) (comb W.ψ _ _ (c.1 i) (v i)) (Q i)) φ

def volT {M : Vol G} (hM : IsHaarDef M) {j : ℕ} (hj : j < D.R.m) : GlobalTheory.Unf.Vol (G.V (.top j)) :=
  ⟨M.ν (.top j), M.fd (.top j), (hM (.top j) hj.le fun e => by injection e; omega).1,
    (hM (.top j) hj.le fun e => by injection e; omega).2⟩

theorem Lp_succ {M : Vol G} (hM : IsHaarDef M) (t : T) (c : Combs G) {j : ℕ} (hj : j < D.R.m) (Q : Pols G) (φ : Fn G (.top 0))
    (v' : GlobalTheory.Unf.Vol (G.V (.top (j + 1)))) :
    Lp W v M t c (j + 1) Q φ = (kd W v t c j).lift W.ψ W.θ (wv (sp W j) (volT hM hj)) (wv (sp W (j + 1)) v') (Q j)
      (Lp W v M t c j Q φ) := rfl

theorem Lp_congr (M : Vol G) (t : T) (c : Combs G) (j : ℕ) {Q Q' : Pols G} (h : ∀ i, i < j → Q i = Q' i) (φ : Fn G (.top 0)) :
    Lp W v M t c j Q φ = Lp W v M t c j Q' φ := by
  unfold Lp
  congr 2
  funext i
  rw [h i i.2]

variable {v} (hv : ∀ t j, j < D.R.m → W.IsVac (.top t j) (v j))
include hv

theorem kd_is (t : T) {c : Combs G} {j : ℕ} (hj : j < D.R.m) (hc : IsFinComb (c.1 j)) :
    (kd W v t c j).Is W.ψ W.θ (sp W j) (sp W (j + 1)) :=
  ⟨⟨_, _, W.om_is (.top t j) (show j + 1 ≤ D.R.m from hj)⟩, hv t j hj, hc⟩

theorem Lp_cont {M : Vol G} (hM : IsHaarDef M) (t : T) {c : Combs G} (hc : ∀ j, j < D.R.m → IsFinComb (c.1 j)) (Q : Pols G)
    {φ : Fn G (.top 0)} (hφ : GlobalTheory.Unf.IsContAut _ φ) : ∀ j, j ≤ D.R.m → GlobalTheory.Unf.IsContAut _ (Lp W v M t c j Q φ)
  | 0, _ => hφ
  | j + 1, hj => by
    rw [Lp_succ W v hM t c hj Q φ (sp W (j + 1)).vol]
    exact (GlobalTheory.SeeSaw.LiftSumProof.liftSum D W.ψ W.θ W.θ_is _ _ _ _ (wv_is (sp_is W (by omega)) _) (wv_is (sp_is W hj) _) _
      (ker_wv (kd_is W hv t hj (hc j hj)) _ _) (Q j)).2.1 _ (Lp_cont hM t hc Q hφ j (by omega))

theorem lift_sum {M : Vol G} (hM : IsHaarDef M) (t : T) {c : Combs G} (hc : ∀ j, j < D.R.m → IsFinComb (c.1 j)) {j : ℕ}
    (hj : j < D.R.m) (v' : GlobalTheory.Unf.Vol (G.V (.top (j + 1)))) (P) {I : Type} [Fintype I] (φ : I → Fn G (.top j))
    (hφ : ∀ i, GlobalTheory.Unf.IsContAut _ (φ i)) :
    (kd W v t c j).lift W.ψ W.θ (wv (sp W j) (volT hM hj)) (wv (sp W (j + 1)) v') P (∑ i, φ i) =
      ∑ i, (kd W v t c j).lift W.ψ W.θ (wv (sp W j) (volT hM hj)) (wv (sp W (j + 1)) v') P (φ i) := by
  have h := (GlobalTheory.SeeSaw.LiftSumProof.liftSum D W.ψ W.θ W.θ_is _ _ _ _ (wv_is (sp_is W hj.le) (volT hM hj))
    (wv_is (sp_is W hj) v') _ (ker_wv (kd_is W hv t hj (hc j hj)) _ _) P).2.2 I Finset.univ (fun _ => 1) φ fun i _ => hφ i
  simpa only [one_smul] using h

variable (hre : ∀ t t' j, j < D.R.m → ∀ a ∈ GinfC _, ∀ b ∈ GinfC _, ∀ f, IsThetaFunO W.ψ _ _ f →
  W.om (.top t j) (a, b) f = W.om (.top t' j) (a, b) f) {C : BiFam G} (hC : IsRealFam W C) (t₀ : T)
include hre hC t₀

theorem col_step {j : ℕ} (hj : j + 2 ≤ D.R.m) (he : Even j) (I : Type) [Fintype I] (Q : I → Pols G) (χ : GA D (G.V (.top j)) → ℂ) :
    ∃ (I' : Type) (_ : Fintype I') (Q' : I' → Pols G) (χ' : GA D (G.V (.top (j + 1 + 1))) → ℂ),
      ∀ t (M : Vol G), IsHaarDef M → ∀ c : Combs G, (∀ j, j < D.R.m → IsFinComb (c.1 j)) → ∀ φ, GlobalTheory.Unf.IsContAut _ φ →
        HasCen _ χ (∑ i, Lp W v M t c j (Q i) φ) →
        biL W M t j (∑ i, Lp W v M t c j (Q i) φ) (combC W c C j) = ∑ i, Lp W v M t c (j + 1 + 1) (Q' i) φ ∧
          HasCen _ χ' (∑ i, Lp W v M t c (j + 1 + 1) (Q' i) φ) := by
  have h0 : j < D.R.m := by omega
  have h1 : j + 1 < D.R.m := by omega
  have hz : ∀ j, IsFinComb ((0 : Combs G).1 j) := fun j u hu => absurd hu (Finset.notMem_empty u)
  obtain ⟨n, P, P', χ', hS⟩ := step W.θ_is (sp_is W h0.le) (sp_is W h1.le) (sp_is W (j := j + 1 + 1) h1)
    (kd_is W hv t₀ h0 (hz _)) (kd_is W hv t₀ h1 (hz _)) χ (hC j he h0).1 (hC j he h0).2
  refine ⟨Fin n × I, inferInstance, fun p => Function.update (Function.update (Q p.2) j (P p.1)) (j + 1) (P' p.1), χ',
    fun t M hM c hc φ hφ hχ => ?_⟩
  have hcont := fun i => Lp_cont W hv hM t hc (Q i) hφ j h0.le
  have hsum : GlobalTheory.Unf.IsContAut _ (∑ i, Lp W v M t c j (Q i) φ) :=
    ⟨fun γ hγ g => by simp only [Finset.sum_apply, (hcont _).1 γ hγ g],
      by simpa only [Finset.sum_fn] using continuous_finset_sum _ fun i _ => (hcont i).2⟩
  obtain ⟨e1, e2⟩ := hS (volT hM h0) (volT hM h1) _ _ (kd_is W hv t h0 (hc _ h0)) (kd_is W hv t h1 (hc _ h1)) rfl rfl
    (hre t t₀ j h0) (hre t t₀ (j + 1) h1) _ hsum hχ
  have e : biL W M t j (∑ i, Lp W v M t c j (Q i) φ) (combC W c C j) = ∑ p : Fin n × I, Lp W v M t c (j + 1 + 1)
      (Function.update (Function.update (Q p.2) j (P p.1)) (j + 1) (P' p.1)) φ := by
    refine Eq.trans e1 ?_
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [lift_sum W hv hM t hc h0 _ _ _ hcont]
    refine (lift_sum W hv hM t hc h1 (sp W (j + 1 + 1)).vol _ _ fun i' =>
      (GlobalTheory.SeeSaw.LiftSumProof.liftSum D W.ψ W.θ W.θ_is _ _ _ _ (wv_is (sp_is W h0.le) _) (wv_is (sp_is W h1.le) _) _
      (ker_wv (kd_is W hv t h0 (hc j h0)) _ _) (P i)).2.1 _ (hcont i')).trans (Finset.sum_congr rfl fun i' _ => ?_)
    rw [Lp_succ W v hM t c h1 _ φ (sp W (j + 1 + 1)).vol, Lp_succ W v hM t c h0 _ φ (volT hM h1), Function.update_self,
      Function.update_of_ne (by omega), Function.update_self,
      Lp_congr W v M t c j (Q := Function.update (Function.update (Q i') j (P i)) (j + 1) (P' i)) (Q' := Q i') fun k hk => by
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]]
  exact ⟨e, e ▸ e2⟩

omit hv hre hC t₀ in
theorem Lp_topEmb (M : Vol G) (t : T) (c : Combs G) (Q : Pols G) (φ : Fn G (.top 0)) {n : ℕ} (h : D.R.m = n)
    (x : GA D (G.V (.grid D.R.m D.R.m))) :
    Lp W v M t c n Q φ (GlobalTheory.RowChain.topEmb G h x) = Lp W v M t c D.R.m Q φ (stabilizerEmbedding G.sp.topDec x) := by
  subst h
  rfl

theorem col_ind : ∀ σ j (hj : j + 2 * σ + 2 = D.R.m), Even j → ∀ (I : Type) [Fintype I] (Q : I → Pols G)
    (χ : GA D (G.V (.top j)) → ℂ), ∃ (I' : Type) (_ : Fintype I') (Q' : I' → Pols G),
      ∀ t (M : Vol G), IsHaarDef M → ∀ c : Combs G, (∀ j, j < D.R.m → IsFinComb (c.1 j)) → ∀ φ, GlobalTheory.Unf.IsContAut _ φ →
        HasCen _ χ (∑ i, Lp W v M t c j (Q i) φ) → ∀ F, GlobalTheory.Unf.IsContAut _ F →
        jPer W M t (combC W c C) F σ j hj (∑ i, Lp W v M t c j (Q i) φ) =
          ∑ i, ∫ h in M.fd (.grid D.R.m D.R.m), Lp W v M t c D.R.m (Q' i) φ (stabilizerEmbedding G.sp.topDec h) * F h
            ∂M.ν (.grid D.R.m D.R.m) := by
  intro σ
  induction σ with
  | zero =>
    intro j hj he I _ Q χ
    obtain ⟨I', _, Q', χ', hS⟩ := col_step W hv hre hC t₀ (by omega) he I Q χ
    refine ⟨I', inferInstance, Q', fun t M hM c hc φ hφ hχ F hF => ?_⟩
    show ∫ h' in M.fd (.grid D.R.m D.R.m), F h' * biL W M t j (∑ i, Lp W v M t c j (Q i) φ) (combC W c C j)
      (GlobalTheory.RowChain.topEmb G _ h') ∂M.ν (.grid D.R.m D.R.m) = _
    rw [(hS t M hM c hc φ hφ hχ).1]
    simp only [Finset.sum_apply, Lp_topEmb, mul_comm (F _), Finset.sum_mul]
    apply integral_finset_sum
    intro i _
    have h1 := Lp_cont W hv hM t hc (Q' i) hφ D.R.m le_rfl
    have h2 := hM (.grid D.R.m D.R.m) ⟨le_rfl, rfl⟩ (fun e => by cases e)
    refine (GlobalTheory.Unf.contAut_rapidDec_bounded_integrable D _ coCpt_last _ ⟨fun γ hγ g => ?_, ?_⟩).2.2 ⟨_, _, h2.1, h2.2⟩
    · rw [GlobalTheory.UnitaryEmbeddingProperties.unitaryEmbedding_mul, h1.1 _ (GlobalTheory.UnitaryEmbeddingProperties.unitaryEmbedding_rational _ γ hγ), hF.1 γ hγ g]
    · exact (h1.2.comp (GlobalTheory.UnitaryEmbeddingProperties.continuous_unitaryEmbedding _)).mul hF.2
  | succ σ ih =>
    intro j hj he I _ Q χ
    obtain ⟨I', _, Q', χ', hS⟩ := col_step W hv hre hC t₀ (by omega) he I Q χ
    obtain ⟨I'', _, Q'', hS'⟩ := ih (j + 1 + 1) (by omega) (by rw [add_assoc]; exact he.add even_two) I' Q' χ'
    refine ⟨I'', inferInstance, Q'', fun t M hM c hc φ hφ hχ F hF => ?_⟩
    show jPer W M t (combC W c C) F σ (j + 1 + 1) _ (biL W M t j (∑ i, Lp W v M t c j (Q i) φ) (combC W c C j)) = _
    rw [(hS t M hM c hc φ hφ hχ).1]
    exact hS' t M hM c hc φ hφ (hS t M hM c hc φ hφ hχ).2 F hF

end Grid

theorem rho_central {D : D7} {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} {x : DefSp V} (hx : x.Is)
    (lam : D.what₂.Tau → DomWeight V.rank) {z : GA D V} (h1 : z ∈ GinfC V) (h2 : z ∈ Subgroup.center (GA D V)) :
    ∃ s : ℂ, ∀ w, rhoK lam (invTrK (GlobalTheory.CoefModel.realGL θ V z)) w = s • w := by
  have hsc := GlobalTheory.CenterScalar.center_scalar D θ hθ V x hx z h1 h2
  have hc : ∀ g, GlobalTheory.CoefModel.realGL θ V z * g = g * GlobalTheory.CoefModel.realGL θ V z := fun g => funext fun τ => by
    obtain ⟨ζ, -, e⟩ := hsc τ
    have e' : (GlobalTheory.CoefModel.realGL θ V z τ).val = ζ • (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ) := e
    refine Units.ext ?_
    rw [Pi.mul_apply, Pi.mul_apply, Units.val_mul, Units.val_mul, e', Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one]
  generalize GlobalTheory.CoefModel.realGL θ V z = u at hc
  have hi : ∀ g : D.what₂.Tau → GL (Fin V.rank) ℂ, invTrK (invTrK g) = g := fun g => funext fun τ => Units.ext rfl
  refine GlobalTheory.CoefSchur.endo_scalar ℂ lam _ fun h w => ?_
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, ← hi h, ← map_mul invTrK, ← map_mul invTrK, hc]

theorem pairVec_cen' {D : D7} {V : HSp D} (c : CoefA V) (χ : GA D V → ℂ)
    (hχ : ∀ z ∈ GinfC V, z ∈ Subgroup.center (GA D V) → ∀ w, c.ρ z⁻¹ w = χ z • w) (ξ : Module.Dual ℂ c.W)
    (Ψ : Bridge.Gf V → c.W) : HasCen V χ (pairVec c ξ Ψ) := by
  intro z h1 h2 h
  have hz : finHom V z = 1 := MonoidHom.mem_ker.1 h1
  have hz' : (finHom V).rangeRestrict z = 1 := Subtype.ext hz
  have e : (finHom V).rangeRestrict (h * z) = (finHom V).rangeRestrict h :=
    (map_mul _ _ _).trans ((congrArg ((finHom V).rangeRestrict h * ·) hz').trans (mul_one _))
  have e2 : c.ρ (h * z)⁻¹ = c.ρ z⁻¹ * c.ρ h⁻¹ := by rw [_root_.mul_inv_rev, map_mul]
  have e3 : ∀ w, c.ρ (h * z)⁻¹ w = χ z • c.ρ h⁻¹ w := fun w => (LinearMap.congr_fun e2 w).trans (hχ z h1 h2 _)
  refine (pairVec_apply c ξ Ψ (h * z)).trans ?_
  refine (congrArg ξ (e3 _)).trans ?_
  refine (ξ.map_smul _ _).trans ?_
  exact congrArg (fun q => χ z * ξ (c.ρ h⁻¹ (Ψ q))) e

open scoped ComplexOrder in
theorem rhoH_central {D : D7} {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} {x : DefSp V} (hx : x.Is)
    (lam : D.what₂.Tau → DomWeight V.rank) {J : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} (hJ : ∀ τ, (J τ).PosDef)
    (z : GA D V) : ∃ s : ℂ, z ∈ GinfC V → z ∈ Subgroup.center (GA D V) →
      ∀ w, GlobalTheory.CoefModel.rhoH lam hJ (invTrK (GlobalTheory.CoefModel.realGL θ V z⁻¹)) w = s • w := by
  by_cases hz : z ∈ GinfC V ∧ z ∈ Subgroup.center (GA D V)
  swap
  · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ hz⟩
  obtain ⟨s, hs⟩ := rho_central hθ hx lam (inv_mem hz.1) (inv_mem hz.2)
  refine ⟨s, fun _ _ w => ?_⟩
  obtain ⟨w, rfl⟩ := (GlobalTheory.CoefModel.toHilb lam hJ).surjective w
  rw [GlobalTheory.CoefModel.rhoH_toHilb, hs]
  exact (GlobalTheory.CoefModel.toHilb lam hJ).map_smul _ _

open scoped ComplexOrder in

theorem pairVec_cen {D : D7} {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} {x : DefSp V} (hx : x.Is)
    (lam : D.what₂.Tau → DomWeight V.rank) {J : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} (hJ : ∀ τ, (J τ).PosDef) :
    ∃ χ, ∀ ξ Ψ, HasCen V χ (pairVec (GlobalTheory.CoefModel.coefOf lam hJ (invTrK.comp (GlobalTheory.CoefModel.realGL θ V))) ξ Ψ) := by
  choose χ hχ using rhoH_central hθ hx lam hJ
  exact ⟨χ, pairVec_cen' _ χ hχ⟩

section Col

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R)

theorem colFn_cen : ∃ χ, ∀ a, HasCen _ χ (colFn ch a) := by
  obtain ⟨χ, hχ⟩ := pairVec_cen ch.W.θ_is (sp_is ch.W (Nat.zero_le _)) (LaP ch.G) (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.posDef_dual ch.G)
  exact ⟨χ, fun a => hχ ch.ξ (ch.col a)⟩

theorem colFock_of (hc : ∀ a, GlobalTheory.Unf.IsContAut _ (colFn ch a)) (hre : RealEqAt ch) : ColFock ch := by
  intro v hv C hC
  rcases isEmpty_or_nonempty T with hT | ⟨⟨t₀⟩⟩
  · exact ⟨0, fun t => hT.elim t⟩
  obtain ⟨χ, hχ⟩ := colFn_cen ch
  obtain ⟨I, _, Q, h⟩ := col_ind ch.W hv (fun t t' j hj => (hre t t' j hj).1) hC t₀ _ 0 top_idx ⟨0, rfl⟩ Unit (fun _ => 0) χ
  refine ⟨∑ i, Finsupp.single (fun j : Fin D.R.m => Q i j) 1, fun t M hM a c hfc F hF => ?_⟩
  have e : ∑ _i : Unit, Lp ch.W v M t c 0 0 (colFn ch a) = colFn ch a := Fintype.sum_unique _
  have h1 := h t M hM c hfc (colFn ch a) (hc a) (e.symm ▸ hχ a) F hF
  rw [e] at h1
  rw [h1, ← Finsupp.sum_finsetSum_index (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finsupp.sum_single_index (zero_mul _), one_mul]
  rfl

end Col

theorem colFock_big : Big fun ch => ColFock ch :=
  big_mono (fun ch h => colFock_of ch (fun a => ⟨(h.1 a).2, (h.1 a).1⟩) h.2)
    (Big.and GlobalTheory.RowClaim.colFn_cont_left GlobalTheory.RowRealEq.realEqAt)

end GlobalTheory.ColFockPf

end
