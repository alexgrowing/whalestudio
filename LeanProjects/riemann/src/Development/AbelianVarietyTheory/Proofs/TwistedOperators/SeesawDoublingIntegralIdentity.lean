import Mathlib
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedThetaIntegralValue
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
import Development.AbelianVarietyTheory.Definitions.Foundations.EqPlaceIdemOfIsPrimeIdem
import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousSingleAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConstOfPolConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodSplitPlaceTranslationActsThroughWeil
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodPlaceTranslateCombinationLatticeIndica
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorPureTensorComponentAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitBasisWittModelEquivariantStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

open GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames ValuativeRel
open GlobalTheory.WeilM GlobalTheory.AdelicU
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RegSo

theorem mem_range_emb_of_conjU_mem_UAt {D : D7} (V : HSp D) (Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E V.rank) (c : D.host.E)
    (hc : Y.J = c • V.gram) (v : HeightOneSpectrum (𝓞 D.host.F)) (g : GA D V)
    (hg : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU V c hc g ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt D.sp.cm.sig Y (evFin D.host.F v)) :
    g ∈ Set.range (emb D.sp.cm.sig V.gram v) := by
  obtain ⟨α, hε, h1, h2⟩ := GlobalTheory.AdelicU.Supp.isPlaceIdem_placeIdem D v
  set ε := GlobalTheory.AdelicU.Supp.placeIdem (F := D.host.F) v with hεdef
  have e1 : evFin D.host.F v ε = 1 := by rw [hε]; exact h1
  have e2 : ∀ u, u ≠ v → evFin D.host.F u ε = 0 := fun u hu => by rw [hε]; exact h2 u hu
  have e0 : ∀ w, evInf D.host.F w ε = 0 := fun w => by rw [hε]; rfl
  have hu : evFin D.host.F v (1 - ε) = 0 := by rw [map_sub, map_one, e1, sub_self]
  have hz := hg (1 - ε) hu
  have key := (GlobalTheory.AdelicU.Supp.mul_idem_iff_mem_range_emb D.sp.cm.sig V.gram v ε e0 e1 e2 g).1 (fun i j => ?_)
  · exact key
  set M : Matrix (Fin V.rank) (Fin V.rank) (AE D) := (GlobalTheory.AdelicU.matHom (AF D.host.F) D.sp.cm.sig V.gram g).val with hM
  have hm : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU V c hc g) = M.map (Formalism.L2.Theta.cA D) := rfl
  have hij := congrFun (congrFun hz i) j
  rw [hm, Matrix.smul_apply, Matrix.sub_apply, Matrix.map_apply, Matrix.zero_apply] at hij
  have h1' : (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j = Formalism.L2.Theta.cA D ((1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j) := by
    rw [Matrix.one_apply]; split_ifs <;> simp
  have hsm : ∀ (a : AF D.host.F) (x : AE D), Formalism.L2.Theta.cA D (a • x) = a • Formalism.L2.Theta.cA D x :=
    fun a x => map_smul (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) a x
  rw [h1', ← map_sub, ← hsm] at hij
  have hinj : (M - 1) i j - ε • (M - 1) i j = 0 := by
    have := congrArg (Formalism.L2.Theta.cA D) hij
    rw [Formalism.L2.Theta.cA_cA, map_zero, sub_smul, one_smul] at this
    exact this
  rw [sub_eq_zero] at hinj
  rw [← Algebra.smul_def]
  exact hinj.symm

theorem mem_GfC_of_mem_range {D : D7} (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (g : GA D V)
    (hg : g ∈ Set.range (emb D.sp.cm.sig V.gram v)) : g ∈ GfC V := by
  obtain ⟨x, rfl⟩ := hg
  exact GlobalTheory.AdelicU.mem_finPts.2 (GlobalTheory.AdelicU.projInf_emb _ _ v x)

open GlobalTheory.SplitGLLift in

theorem homAt : ∀ {D : D7} (W₁ : HSp D) {a : ℕ} (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a W₁.rank)
    (hJ : Γ.V'.J = (-1 : D.host.E) • W₁.gram), IsCMExt D.host.F D.host.E D.sp.cm.sig →
    (∀ i j, D.sp.cm.sig (Γ.V'.J j i) = Γ.V'.J i j) →
    ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (t : D.host.E →ₐ[D.host.F] Fv D.host.F v),
    ∃ K : GL (Fin W₁.rank) (Fv D.host.F v) →* GA D W₁, ∀ g,
      K g ∈ GfC W₁ ∧ K g ∈ Set.range (GlobalTheory.AdelicU.emb D.sp.cm.sig W₁.gram v) ∧
      GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) hJ (K g) ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt D.sp.cm.sig Γ.V' (evFin D.host.F v) ∧
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) hJ (K g))).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW t) = g.val ∧
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) hJ (K g))).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (t.comp D.sp.cm.sig)) =
        (Γ.V'.J.map t)⁻¹ * ((g⁻¹ : GL _ _).val)ᵀ * Γ.V'.J.map t := by
  intro D W₁ a Γ hJW hcm herm v t
  have hJ : IsUnit (Γ.V'.J.map t).det := by
    rw [isUnit_iff_ne_zero]
    have e1 : (Γ.V'.J.map t).det = t Γ.V'.J.det := by
      rw [AlgHom.map_det]; rfl
    rw [e1, hJW, Matrix.det_smul]
    rw [map_ne_zero]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (Formalism.L2.Theta.gram_det_ne _)
  let N₀ : GL (Fin W₁.rank) (Fv D.host.F v) →* Matrix (Fin W₁.rank)
      (Fin W₁.rank) (AF D.host.F ⊗[D.host.F] D.host.E) :=
    (oneAdd (liftMat hcm t)).comp (pairHom (Γ.V'.J.map t) hJ)
  let N : GL (Fin W₁.rank) (Fv D.host.F v) →* GL (Fin W₁.rank)
      (AF D.host.F ⊗[D.host.F] D.host.E) :=
    (Matrix.GeneralLinearGroup.map (Formalism.L2.Theta.cA D)).comp N₀.toHomUnits
  have hU := fun g => unitary hcm t Γ.V'.J herm hJ g

  have hcc : ∀ g, ((N₀ g).map (Formalism.L2.Theta.cA D)).map (Formalism.L2.Theta.cA D) = N₀ g := fun g =>
    Matrix.ext fun a b => Formalism.L2.Theta.cA_cA _
  have mem : ∀ g, N g ∈ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (AF D.host.F) D.sp.cm.sig W₁.gram := by
    intro g
    have hU' : (N₀ g)ᵀ * Γ.V'.J.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := D.host.F) (AF D.host.F)) *
        (N₀ g).map (Formalism.L2.Theta.cA D) = Γ.V'.J.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := D.host.F) (AF D.host.F)) := hU g
    have hJi : Γ.V'.J.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := D.host.F) (AF D.host.F)) =
        -GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM W₁.gram := by
      show GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM Γ.V'.J = _
      rw [hJW, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM_smul, map_neg, map_one, neg_one_smul]
    rw [hJi, Matrix.mul_neg, Matrix.neg_mul, neg_inj] at hU'
    show (((N₀ g).map (Formalism.L2.Theta.cA D)).map (Formalism.L2.Theta.cA D))ᵀ *
        GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM W₁.gram * (N₀ g).map (Formalism.L2.Theta.cA D) =
      GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM W₁.gram
    rw [hcc]
    exact hU'
  refine ⟨N.codRestrict _ mem, fun g => ?_⟩
  have hmat : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU _ (-1) hJW (N.codRestrict _ mem g)) = N₀ g := hcc g
  have hN₀ : N₀ g = 1 + liftMat hcm t (pairHom (Γ.V'.J.map t) hJ g - 1) := rfl
  have hAt : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) hJW (N.codRestrict _ mem g) ∈
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt D.sp.cm.sig Γ.V' (evFin D.host.F v) := by
    show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin D.host.F v) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat _ - 1)
    erw [hmat]
    rw [hN₀, add_sub_cancel_left]
    exact at_liftMat hcm t _
  have hR := mem_range_emb_of_conjU_mem_UAt W₁ Γ.V' (-1) hJW v _ hAt
  refine ⟨?_, hR, hAt, ?_, ?_⟩
  · exact mem_GfC_of_mem_range W₁ v _ hR
  · erw [hmat]
    rw [hN₀, map_one_add_piW]
    exact add_sub_cancel _ _
  · erw [hmat]
    rw [hN₀, map_one_add_piW_comp]
    exact add_sub_cancel _ _

theorem actAt : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V' Γ.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om' →
    ∀ (K : GL (Fin a') (Fv F Bs.v₁) →* GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ Γ.V'.J),
    (∀ g, K g ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ Γ.V' (evFin F Bs.v₁) ∧
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (K g)).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW Bs.τ₁) = g.val ∧
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (K g)).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (Bs.τ₁.comp σ)) =
        (Γ.V'.J.map Bs.τ₁)⁻¹ * ((g⁻¹ : GL _ _).val)ᵀ * Γ.V'.J.map Bs.τ₁) →
    ∃ ν α : (Fv F Bs.v₁)ˣ →* ℂˣ, (∀ x, ‖(ν x : ℂ)‖ = 1) ∧
      ∀ ι : ((Fin a' × Fin (a + a') → Fv F Bs.v₁) → ℂ) →ₗ[ℂ] (Matrix (Fin a') (Fin (a + a')) (Fv F Bs.v₁) → ℂ),
      Γ.M'.IsLinBar Bs.ψ Bs.τ₁ 1 1 ι → ∀ g : GL (Fin a') (Fv F Bs.v₁),
        ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ r, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (evFin F Bs.v₁) φ r → ∃ φ₁ ∈ GlobalTheory.WeilM.SB _,
          om' (K g, 1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F Bs.v₁) φ r) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F Bs.v₁) φ₁ r ∧
            ι φ₁ = omB ν α g 1 (ι φ) := by
  intro F E _ _ _ _ _ σ a a' Bs Γ X om om' hTr K hK
  have hB := fun g => GlobalTheory.T.weilRepresentationLocality_unitaryGroupV' Bs Γ X om om' hTr Bs.v₁ (K g) (hK g).1
  choose S hS using hB
  have hSplit := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hTr.weil'
  have pres : ∀ p Φ, Φ ∈ GlobalTheory.WeilM.schA F _ → om' p Φ ∈ GlobalTheory.WeilM.schA F _ :=
    fun p Φ hΦ => hSplit.pres p Φ hΦ
  have restS : ∀ g φ r, φ ∈ GlobalTheory.WeilM.SB _ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (evFin F Bs.v₁) φ r →
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (evFin F Bs.v₁) (S g φ) r := fun g φ r hφ hr =>
    ⟨hr.1, by rw [← (hS g φ hφ).2 r hr]; exact pres _ _ hr.2⟩
  have h1 : ∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, S g φ ∈ GlobalTheory.WeilM.SB _ := fun g φ hφ => (hS g φ hφ).1
  have h2 : ∀ g g', ∀ φ ∈ GlobalTheory.WeilM.SB _, S (g * g') φ = S g (S g' φ) := by
    intro g g' φ hφ
    refine GlobalTheory.TensUniq.eq_of_tens_eq Bs.v₁ φ _ _ hφ fun r hr => ?_
    have e1 : ((K (g * g'), (1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ Γ.W.J))) =
        (K g, 1) * (K g', 1) := by rw [map_mul, Prod.mk_mul_mk, one_mul]
    rw [← (hS (g * g') φ hφ).2 r hr, e1, map_mul, Module.End.mul_apply, (hS g' φ hφ).2 r hr,
      (hS g (S g' φ) (h1 g' φ hφ)).2 r (restS g' φ r hφ hr)]
  have h3 : ∀ φ ∈ GlobalTheory.WeilM.SB _, S 1 φ = φ := by
    intro φ hφ
    refine GlobalTheory.TensUniq.eq_of_tens_eq Bs.v₁ φ _ _ hφ fun r hr => ?_
    have e1 : ((K 1, (1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ Γ.W.J))) = 1 := by rw [map_one]; rfl
    rw [← (hS 1 φ hφ).2 r hr, e1, map_one, Module.End.one_apply]
  have hψ : Continuous Bs.ψ := hTr.base.std.1
  have atAct : ∀ g (γ : Matrix _ _ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E)),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F Bs.v₁) γ →
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F Bs.v₁)
        (GlobalTheory.WeilM.actAB (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (K g, (1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ Γ.W.J)) γ) := by
    intro g γ hγ u hu
    simp only [GlobalTheory.WeilM.actAB]
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, hγ u hu, Matrix.mul_zero, Matrix.zero_mul]
  have h4 : ∀ g (γ : Matrix _ _ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E)),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F Bs.v₁) γ → ∀ φ ∈ GlobalTheory.WeilM.SB _,
        S g (GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ γ) φ) =
          GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁)
            (GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ (GlobalTheory.WeilM.actAB (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ)
              (K g, (1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ Γ.W.J)) γ)) (S g φ) := by
    intro g γ hγ φ hφ
    have hw := GlobalTheory.SchrSB.schr_mem_SB Bs.ψ hψ Bs.v₁ (GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ γ) φ hφ
    refine GlobalTheory.TensUniq.eq_of_tens_eq Bs.v₁ φ _ _ hφ fun r hr => ?_
    have hb1 := GlobalTheory.VacBridge.rho_acts_locCo Γ.M'.co Bs.ψ Bs.v₁ γ hγ φ r hr
    have hRw : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (evFin F Bs.v₁)
        (GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ γ) φ) r :=
      ⟨hr.1, by rw [← hb1]; exact GlobalTheory.HeisSchA.rho_mem_schA Γ.M' Bs.ψ hTr.base.std γ _ hr.2⟩
    rw [← (hS g _ hw).2 r hRw, ← hb1, hSplit.impl _ _ _ hr.2, (hS g φ hφ).2 r hr,
      GlobalTheory.VacBridge.rho_acts_locCo Γ.M'.co Bs.ψ Bs.v₁ _ (atAct g γ hγ) (S g φ) r (restS g φ r hφ hr)]
  have h5 : ∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ μ : @Measure (Fin a' × Fin (a + a') → Fv F Bs.v₁) (borel _),
      @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∫⁻ y, ‖S g φ y‖ₑ ^ 2 ∂μ = ∫⁻ y, ‖φ y‖ₑ ^ 2 ∂μ :=
    fun g φ hφ μ hμ => GlobalTheory.T.localWeilOperator_isometry_schwartzBruhat Bs Γ X om om' hTr Bs.v₁ (K g) (hK g).1 φ (S g φ) hφ (h1 g φ hφ) (hS g φ hφ).2 μ hμ
  obtain ⟨ν, α, hν, hC⟩ := GlobalTheory.T.heisenbergIntertwiner_eq_twisted_weilOperator Bs Γ X om om' hTr K (fun g => hK g) S h1
    (fun g => GlobalTheory.LocWeilAct.linear_of_acts Bs.v₁ (om' (K g, 1)) (S g) (hS g)) h2 h3 h4 h5
  exact ⟨ν, α, hν, fun ι hι g φ hφ r hr =>
    ⟨S g φ, h1 g φ hφ, (hS g φ hφ).2 r hr, hC ι hι g φ hφ⟩⟩

theorem combAt : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {a a' : ℕ} (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a')
    (hM' : Γ.M'.IsGood B.ψ) (hlt : a' < a)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V' Γ.W) {H : Type} (κ : H → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ Γ.V'.J)
    (kf : GL (Fin a') (Fv F B.v₁) → H)
    (ν α : (Fv F B.v₁)ˣ →* ℂˣ) (hν : ∀ x, ‖(ν x : ℂ)‖ = 1)
    (ι : ((Fin a' × Fin (a + a') → Fv F B.v₁) → ℂ) →ₗ[ℂ] (Matrix (Fin a') (Fin (a + a')) (Fv F B.v₁) → ℂ))
    (hι : Γ.M'.IsLinBar B.ψ B.τ₁ 1 1 ι)
    (hact : ∀ g : GL (Fin a') (Fv F B.v₁), ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ r, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (evFin F B.v₁) φ r →
      ∃ φ₁ ∈ GlobalTheory.WeilM.SB _, om' (κ (kf g), 1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F B.v₁) φ r) =
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F B.v₁) φ₁ r ∧ ι φ₁ = omB ν α g 1 (ι φ))
    (φ₀ : (Fin a' × Fin (a + a') → Fv F B.v₁) → ℂ)
    (P : GL (Fin a') (Fv F B.v₁)) (Λ : Submodule 𝒪[Fv F B.v₁] (Fin (a + a') → Fv F B.v₁)) (c : ℂ)
    (hφ₀ : ∀ Y, ι φ₀ Y = c * (GlobalTheory.SplitFlip.matLat (Fin a') Λ : Set _).indicator 1 (P.val * Y)),
    ∃ z : H →₀ ℂ, (∀ k ∈ z.support, k ∈ Set.range kf) ∧ zdeg z ≠ 0 ∧
      ∀ {m : ℕ} (f : Fin m → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a' × Fin (a + a')))
        (φ : Fin m → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (Fin a' × Fin (a + a') → Fv F v) → ℂ),
        (∀ k v, φ k v ∈ GlobalTheory.WeilM.SB _) → (∀ k, ∀ᶠ v in Filter.cofinite, φ k v = Γ.M'.vac v) → (∀ k, φ k B.v₁ = φ₀) →
        (z.sum fun k c => c • om' (κ k, 1) (∑ k, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f k) (φ k))) ∈ Γ.M'.So B.ψ B.τ₁ := by
  intro F E _ _ _ _ _ σ a a' B Γ hM' hlt om' H κ kf ν α hν ι hι hact φ₀ P Λ c hφ₀
  classical
  have hd : ((a' : ℕ) : ℝ) - 1 < (Fintype.card (Fin (a + a')) : ℝ) / 2 := by
    rw [Fintype.card_fin]; push_cast
    have : (a' : ℝ) + 1 ≤ a := by exact_mod_cast hlt
    linarith
  obtain ⟨z₁, hz₁, hz₁Y⟩ := GlobalTheory.CombAtGood.exists_translates_primFrame_conj ν α hν hd Λ P c
  refine ⟨z₁.mapDomain kf, fun k hk => ?_, ?_, fun {m} f φ hSB hvac h₀ => ?_⟩
  · obtain ⟨g, -, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hk)
    exact ⟨g, rfl⟩
  · rw [zdeg, Finsupp.sum_mapDomain_index (by simp) (by simp)]
    exact hz₁
  rw [Finsupp.sum_mapDomain_index (f := kf) (s := z₁)
    (h := fun k (c' : ℂ) => c' • om' (κ k, 1) (∑ k, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f k) (φ k)))
    (fun _ => zero_smul ℂ _) (fun _ _ _ => add_smul _ _ _)]
  simp only [Finsupp.sum, map_sum, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Submodule.sum_mem _ fun i _ => ?_
  have hstd : ∀ᶠ v in Filter.cofinite, φ i v = Set.indicator {x | ∀ j, x j ∈ v.adicCompletionIntegers F} 1 :=
    ((hvac i).and hM'.std).mono fun v h => h.1.trans h.2
  obtain ⟨r, hr, hrt⟩ := GlobalTheory.PureFactor.exists_rest_factor (B.v₁) (f i) (φ i) hstd
  have hφ₀SB : φ₀ ∈ GlobalTheory.WeilM.SB _ := h₀ i ▸ hSB i B.v₁
  have hpure : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F B.v₁) φ₀ r := by
    rw [hrt, ← h₀ i, Function.update_eq_self]
  have hRest : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (evFin F B.v₁) φ₀ r := ⟨hr, hpure ▸ GlobalTheory.TensUniq.pure_mem_schA (f i) (φ i) (hSB i) hstd⟩
  have hinj := (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model.IsLin.bij hι).injOn
  let φ₁ : GL (Fin a') (Fv F B.v₁) → _ := fun g =>
    Function.invFunOn ι (GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F B.v₁) : Set _) (omB ν α g 1 (ι φ₀))
  have hφ₁ : ∀ g, φ₁ g ∈ GlobalTheory.WeilM.SB _ ∧ ι (φ₁ g) = omB ν α g 1 (ι φ₀) ∧
      om' (κ (kf g), 1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F B.v₁) φ₀ r) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F B.v₁) (φ₁ g) r := by
    intro g
    obtain ⟨ψ₁, hψ₁, he, hι₁⟩ := hact g φ₀ hφ₀SB r hRest
    have hex : ∃ x ∈ (GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F B.v₁) : Set _), ι x = omB ν α g 1 (ι φ₀) :=
      ⟨ψ₁, hψ₁, hι₁⟩
    have hm := Function.invFunOn_mem hex
    have heq := Function.invFunOn_eq hex
    have h' : ψ₁ = φ₁ g := hinj hψ₁ hm (hι₁.trans heq.symm)
    exact ⟨hm, heq, h' ▸ he⟩
  set Φ₁ := ∑ g ∈ z₁.support, z₁ g • φ₁ g with hΦ₁
  have hΦ₁SB : Φ₁ ∈ GlobalTheory.WeilM.SB _ := Submodule.sum_mem _ fun g _ => Submodule.smul_mem _ _ (hφ₁ g).1
  have htens : ∀ (s : Finset (GL (Fin a') (Fv F B.v₁))) (w : GL (Fin a') (Fv F B.v₁) → ℂ),
      ∑ g ∈ s, w g • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F B.v₁) (φ₁ g) r =
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F B.v₁) (∑ g ∈ s, w g • φ₁ g) r := by
    intro s w
    funext x
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, mul_assoc]
  have hsum : ∑ g ∈ z₁.support, z₁ g • om' (κ (kf g), 1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i)) =
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (Function.update (φ i) B.v₁ Φ₁) := by
    rw [← hrt, hpure, ← htens]
    exact Finset.sum_congr rfl fun g _ => by rw [(hφ₁ g).2.2]
  rw [hsum]
  refine Submodule.subset_span ⟨f i, Function.update (φ i) B.v₁ Φ₁, fun v => ?_, ?_, ?_, rfl⟩
  · by_cases hv : v = B.v₁
    · subst hv; rw [Function.update_self]; exact hΦ₁SB
    · rw [Function.update_of_ne hv]; exact hSB i v
  · filter_upwards [hvac i, Filter.eventually_cofinite_ne B.v₁] with v h1 h2
    rw [Function.update_of_ne h2, h1]
  · rw [Function.update_self]
    refine ⟨hΦ₁SB, ι, hι, fun Y hY => ?_⟩
    have hιΦ : ι Φ₁ = ∑ g ∈ z₁.support, z₁ g • omB ν α g 1 (ι φ₀) := by
      rw [hΦ₁, map_sum]
      exact Finset.sum_congr rfl fun g _ => by rw [map_smul, (hφ₁ g).2.1]
    have hιφ₀ : ι φ₀ = fun Y => c * (GlobalTheory.SplitFlip.matLat (Fin a') Λ : Set (Matrix (Fin a') (Fin (a + a')) (Fv F B.v₁))).indicator 1 (P.val * Y) :=
      funext hφ₀
    have h3 := hz₁Y Y
    rw [hιφ₀] at hιΦ
    rw [hιΦ, ← hιφ₀]
    rw [← hιφ₀] at h3
    simp only [Finsupp.sum] at h3
    rw [h3, Set.indicator_of_notMem, mul_zero]
    intro hp
    apply hY
    have h4 := hp.1
    rwa [Matrix.rank_mul_eq_right_of_isUnit_det _ _ (P.isUnit.map Matrix.detMonoidHom), Fintype.card_fin] at h4

def mulHomeo {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k] {n d : ℕ} (A : GL (Fin n) k) (C : GL (Fin d) k) :
    Matrix (Fin n) (Fin d) k ≃ₜ Matrix (Fin n) (Fin d) k where
  toFun Y := A.val * Y * C.val
  invFun Y := (A⁻¹).val * Y * (C⁻¹).val
  left_inv Y := by
    simp only [← Matrix.mul_assoc]
    rw [Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  right_inv Y := by
    simp only [← Matrix.mul_assoc]
    rw [Units.mul_inv, Matrix.one_mul, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
  continuous_toFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  continuous_invFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

theorem mulHomeo_apply {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k] {n d : ℕ} (A : GL (Fin n) k)
    (C : GL (Fin d) k) (Y : Matrix (Fin n) (Fin d) k) : mulHomeo A C Y = A.val * Y * C.val := rfl

theorem comp_mem_SB {Z : Type} [TopologicalSpace Z] (T : Z ≃ₜ Z) {f : Z → ℂ} (hf : f ∈ GlobalTheory.WeilM.SB Z) :
    f ∘ T ∈ GlobalTheory.WeilM.SB Z := ⟨hf.1.comp_continuous T.continuous, hf.2.comp_homeomorph T⟩

theorem isLinBar_one {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd)
    (ψ : AddChar (AF F) ℂ) {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F} (t : E →ₐ[F] Fv F v) (b bt : GL (Fin n) (Fv F v)) (hbt : bt.val = b.valᵀ)
    (c : GL (Fin d) (Fv F v)) (ι : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) (Fv F v) → ℂ))
    (h : M.IsLinBar ψ t b c ι) : M.IsLinBar ψ t 1 1 ((LinearMap.funLeft ℂ ℂ (mulHomeo bt c)).comp ι) := by
  have hco : ∀ u : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E),
      mulHomeo bt c (-((1 : GL (Fin n) (Fv F v)).1ᵀ * Y.J.map t * u.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (t.comp σ)) * (Wd.J.map t)ᵀ *
        (1 : GL (Fin d) (Fv F v)).1)) =
      -(b.1ᵀ * Y.J.map t * u.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (t.comp σ)) * (Wd.J.map t)ᵀ * c.1) := fun u => by
    rw [mulHomeo_apply, hbt]
    simp only [Units.val_one, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one, Matrix.mul_neg, Matrix.neg_mul,
      Matrix.mul_assoc]
  have hadd : ∀ Z Z' : Matrix (Fin n) (Fin d) (Fv F v), mulHomeo bt c (Z + Z') = mulHomeo bt c Z + mulHomeo bt c Z' :=
    fun Z Z' => by
      simp only [mulHomeo_apply, Matrix.mul_add, Matrix.add_mul]
  have hb : Set.BijOn (LinearMap.funLeft ℂ ℂ (mulHomeo bt c)) (GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin d) (Fv F v)) : Set _)
      (GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin d) (Fv F v)) : Set _) := by
    refine ⟨fun f hf => comp_mem_SB _ hf, fun f _ f' _ e => ?_, fun f hf => ⟨f ∘ (mulHomeo bt c).symm, comp_mem_SB _ hf, ?_⟩⟩
    · funext Z
      have := congrFun e ((mulHomeo bt c).symm Z)
      simpa [LinearMap.funLeft_apply] using this
    · funext Z
      simp [LinearMap.funLeft_apply]
  refine ⟨hb.comp h.bij, fun u hu h0 φ hφ φ₁ hφ₁ ha Z => ?_, fun u hu h0 φ hφ φ₁ hφ₁ ha x hx hx0 => ?_⟩
  · simp only [LinearMap.comp_apply, LinearMap.funLeft_apply]
    rw [hadd, hco]
    exact h.trans u hu h0 φ hφ φ₁ hφ₁ ha _
  · simp only [LinearMap.comp_apply, LinearMap.funLeft_apply]
    rw [hco]
    exact h.mult u hu h0 φ hφ φ₁ hφ₁ ha x hx hx0

theorem vacAt : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' →
    ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (t : E →ₐ[F] Fv F v),
    ∃ (ι : ((Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a') (Fin (a + a')) (Fv F v) → ℂ))
      (P : GL (Fin a') (Fv F v)) (Λ : Submodule 𝒪[Fv F v] (Fin (a + a') → Fv F v)) (c : ℂ),
      G.M'.IsLinBar B.ψ t 1 1 ι ∧
      ∀ Y, ι (G.M'.vac v) Y = c * (GlobalTheory.SplitFlip.matLat (Fin a') Λ : Set _).indicator 1 (P.val * Y) := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hT v t
  haveI := hT.geo.hV'.lat
  haveI := hT.geo.hW.lat
  obtain ⟨b', hb'⟩ := exists_isSplitBasis t G.V'.L hT.base.cm
  obtain ⟨c, hc⟩ := exists_isSplitBasis t G.W.L hT.base.cm
  obtain ⟨b₁, -, ι', hι', hvac'⟩ :=
    GlobalTheory.T.split_basis_witt_model_equivariant hP F E σ B _ _ _ _ _ _ _ om' _ _ _ _ (GlobalTheory.ThKConst.isPair_small hT) v t b' c hb' hc
  let Q : GL (Fin a') (Fv F v) := Matrix.GeneralLinearGroup.mkOfDetNeZero b₁.valᵀ (by
    rw [Matrix.det_transpose]; exact b₁.isUnit.map Matrix.detMonoidHom |>.ne_zero)
  let Λ : Submodule 𝒪[Fv F v] (Fin (a + a') → Fv F v) :=
    { carrier := {x | ∀ j, (x ᵥ* c.val) j ∈ 𝒪[Fv F v]}
      add_mem' := fun {x y} hx hy j => by rw [Matrix.add_vecMul]; exact add_mem (hx j) (hy j)
      zero_mem' := fun j => by rw [Matrix.zero_vecMul]; exact zero_mem _
      smul_mem' := fun s x hx j => by
        rw [show s • x = (s : Fv F v) • x from rfl, Matrix.smul_vecMul]
        exact mul_mem s.2 (hx j) }
  refine ⟨_, Q, Λ, 1, isLinBar_one G.M' B.ψ t b₁ Q rfl c ι' hι', fun Y => ?_⟩
  simp only [LinearMap.comp_apply, LinearMap.funLeft_apply]
  rw [hvac', one_mul]
  have key : mulHomeo Q c Y ∈ {Y : Matrix (Fin a') (Fin (a + a')) (Fv F v) | ∀ i j, Y i j ∈ v.adicCompletionIntegers F} ↔
      Q.val * Y ∈ (GlobalTheory.SplitFlip.matLat (Fin a') Λ : Set (Matrix (Fin a') (Fin (a + a')) (Fv F v))) := by
    rw [mulHomeo_apply]
    show (∀ i j, (Q.val * Y * c.val) i j ∈ v.adicCompletionIntegers F) ↔ ∀ i j, ((Q.val * Y).row i ᵥ* c.val) j ∈ 𝒪[Fv F v]
    simp only [GlobalTheory.FinPl.SplitPoint.mem_integer_iff]
    rfl
  by_cases h : Q.val * Y ∈ (GlobalTheory.SplitFlip.matLat (Fin a') Λ : Set (Matrix (Fin a') (Fin (a + a')) (Fv F v)))
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem (key.2 h)]
    rfl
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h (key.1 h'))]

theorem decAlg : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd)
    (ψ : AddChar (AF F) ℂ) (emb : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w) (Φ : (Fin n × Fin d → AF F) → ℂ),
    Φ ∈ GlobalTheory.SquareAgree.algD M ψ emb →
    ∃ (m : ℕ) (f : Fin m → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d))
      (φ : Fin m → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (Fin n × Fin d → Fv F v) → ℂ),
      Φ = ∑ k, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f k) (φ k) ∧ (∀ k v, φ k v ∈ GlobalTheory.WeilM.SB _) ∧
        ∀ k, ∀ᶠ v in Filter.cofinite, φ k v = M.vac v := by
  intro F E _ _ _ _ _ σ n d Y Wd M ψ emb Φ hΦ
  obtain ⟨m, c, g, rfl⟩ := Submodule.mem_span_set'.1 hΦ
  choose f φ _ hSB hvac hg using fun k => (g k).2
  refine ⟨m, fun k => c k • f k, φ, Finset.sum_congr rfl fun k _ => ?_, hSB, hvac⟩
  rw [hg k]
  funext x
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, Pi.smul_apply, smul_eq_mul, SchwartzMap.smul_apply, mul_assoc]

theorem datumComb : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X)
    (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁)) (𝓕₁ : Set (GA D W₁))
    (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X)
    (hO : IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ (Φ : (Fin W₁.rank × Fin (W.rank + W₁.rank) → AF D.host.F) → ℂ) (f : WO W₁ X → ℂ), IsDatum Γ.M' ψ cB Φ f →
    ∀ z : GA D W₁ →₀ ℂ, IsDatum Γ.M' ψ cB (z.sum fun k c => c • om' (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) hO.JW₁ k, 1) Φ)
      ((z.sum fun k c => c • ωB (k, 1)) f) := by
  intro D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hO hT Φ f hD z
  have hψ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ := hO.psi ▸ hT.base.std
  have hk : kapX X e hO.JX 1 = 1 := by
    apply Subtype.ext
    simp [kapX]
  have h1 : ∀ k, IsDatum Γ.M' ψ cB (om' (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) hO.JW₁ k, 1) Φ) (ωB (k, 1) f) := fun k => by
    have := hO.weilB Φ f hD k 1
    rwa [hk] at this
  refine ⟨Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (h1 k).1, fun u => ?_⟩
  have e1 : Γ.M'.co.rho ψ u (z.sum fun k c => c • om' (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) hO.JW₁ k, 1) Φ) =
      ∑ k ∈ z.support, z k • Γ.M'.co.rho ψ u (om' (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) hO.JW₁ k, 1) Φ) := by
    funext x
    simp only [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [e1, GlobalTheory.ThKConst.thetaSum_sum _ _ fun k _ =>
    Submodule.smul_mem _ _ (GlobalTheory.HeisSchA.rho_mem_schA Γ.M' ψ hψ u _ (h1 k).1)]
  simp only [Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun k _ => by rw [thetaSum_smul, (h1 k).2 u]

theorem isTriple_goodPlace {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E} {a a' : ℕ} {G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a'}
    {X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E} {om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W} {om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W}
    (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om') (v : HeightOneSpectrum (𝓞 F)) (t : E →ₐ[F] Fv F v) (hv : X.Good v) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple { B with v₁ := v, τ₁ := t } G X om om' :=
  { h with
    base := { h.base with }
    geo := { h.geo with hV := { h.geo.hV with }, hV' := { h.geo.hV' with }, hW := { h.geo.hW with } }
    chars := { h.chars with good := hv } }

theorem exists_comb_mem_So : GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
    ∀ (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (α β : (AE D)ˣ →* Circle), IsTriple W W₁ X α β →
    ∀ (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁)) (𝓕₁ : Set (GA D W₁))
      (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
      (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
      (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
      (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
      (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ (n : ℕ) (Ψ : Fin n → WO W₁ X → ℂ), (∀ i, Ψ i ∈ algF ψ θ false A₁ B) →
    ∃ P : Finset (HeightOneSpectrum (𝓞 D.host.F)), ∀ v ∉ P, Xc.Good v → ∀ t : D.host.E →ₐ[D.host.F] Fv D.host.F v,
      ∃ z : GA D W₁ →₀ ℂ, (∀ k ∈ z.support, k ∈ GfC W₁ ∧ k ∈ Set.range (GlobalTheory.AdelicU.emb D.sp.cm.sig W₁.gram v)) ∧
        GlobalTheory.FunObj.zdeg z ≠ 0 ∧ ∀ i, ∃ Φ₀D, IsDatum Γ.M' ψ cB Φ₀D ((z.sum fun k c => c • ωB (k, 1)) (Ψ i)) ∧
          Φ₀D ∈ Γ.M'.So Bs.ψ t := by
  intro hP D ψ θ hθ W W₁ X A A₁ B α β hT ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hO hTD n Ψ hΨ
  classical
  choose ΦD hΦD hD using fun i => hO.algB (Ψ i) (hΨ i)
  choose m f φ hsum hSB hvac using fun i => decAlg Γ.M' Bs.ψ Bs.emb (ΦD i) (hΦD i)
  have hfin : Set.Finite (⋃ i, ⋃ k, {v | ¬ φ i k v = Γ.M'.vac v}) :=
    Set.finite_iUnion fun i => Set.finite_iUnion fun k => Filter.eventually_cofinite.1 (hvac i k)
  refine ⟨hfin.toFinset, fun v hv hg t => ?_⟩
  have h0 : ∀ i k, φ i k v = Γ.M'.vac v := fun i k => by
    by_contra h
    exact hv (hfin.mem_toFinset.2 (Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨k, h⟩⟩))
  have hTD' := isTriple_goodPlace hTD v t hg
  obtain ⟨K, hK⟩ := homAt W₁ Γ hO.JW₁ hTD.base.cm hTD.geo.hV'.herm v t
  let K' : GL (Fin W₁.rank) (Fv D.host.F v) →* GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig Γ.V'.J :=
    { toFun := fun g => GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) hO.JW₁ (K g)
      map_one' := by simp only [map_one]; exact GlobalTheory.LocWeilAct.conjU_one' _ _ _
      map_mul' := fun g g' => by simp only [map_mul]; exact GlobalTheory.LocWeilAct.conjU_mul' _ _ _ _ _ }
  obtain ⟨ν', α', hν', hact⟩ := actAt { Bs with v₁ := v, τ₁ := t } Γ Xc om om' hTD' K' (fun g => (hK g).2.2)
  obtain ⟨ι, Pm, Λ, c, hι, hvι⟩ := vacAt hP _ _ D.sp.cm.sig { Bs with v₁ := v, τ₁ := t } _ _ Γ Xc om om' hTD' v t
  obtain ⟨z, hzs, hzd, hz⟩ := combAt { Bs with v₁ := v, τ₁ := t } Γ hTD.geo.hM' hTD.geo.lt om'
    (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) hO.JW₁) K ν' α' hν' ι hι (hact ι hι) (Γ.M'.vac v) Pm Λ c hvι
  refine ⟨z, fun k hk => ?_, hzd, fun i => ⟨(z.sum fun k c => c • om' (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) hO.JW₁ k, 1) (ΦD i)),
    datumComb D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hO hTD (ΦD i) (Ψ i) (hD i) z, ?_⟩⟩
  · obtain ⟨g, rfl⟩ := hzs k hk
    exact ⟨(hK g).1, (hK g).2.1⟩
  · rw [hsum i]
    exact hz (f i) (φ i) (hSB i) (hvac i) (h0 i)

end GlobalTheory.RegSo

end
