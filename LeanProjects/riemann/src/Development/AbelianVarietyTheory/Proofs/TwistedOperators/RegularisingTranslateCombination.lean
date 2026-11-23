import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareThetaTripleHypothesesOfStandingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TestPlacesPrimeToLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallThetaKernelTranslateIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodSplitPlaceTranslationActsThroughWeil
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRouteDatumTranslationCombinationGoodPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslatedKernelLeThetaFunctionRouteBigVertex
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallRouteKernelEqUnitNormMulThetaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitCompletelyAuxiliaryPlaceOutsideFinsetStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.RegAt

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

open GlobalTheory.LocWeilAct in
open scoped GlobalTheory.VacAny in

theorem act_omB_at : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (t : T) (i j : Fin D.R.m) (M : Vol G)
    (e : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Num G i j) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j)
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W)
    (h : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.IsTripleOf W M t i j e Bs Γ X) (hTr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om'),
    ∃ ν α : (Fv D.host.F Bs.v₁)ˣ →* ℂˣ, (∀ x, ‖(ν x : ℂ)‖ = 1) ∧
      ∀ ι : ((Fin (G.V (.grid i j)).rank × Fin ((G.V (.grid (i + 1) (j + 1))).rank + (G.V (.grid i j)).rank) → Fv D.host.F Bs.v₁) → ℂ) →ₗ[ℂ]
              (Matrix (Fin (G.V (.grid i j)).rank) (Fin ((G.V (.grid (i + 1) (j + 1))).rank + (G.V (.grid i j)).rank)) (Fv D.host.F Bs.v₁) → ℂ),
      Γ.M'.IsLinBar Bs.ψ Bs.τ₁ 1 1 ι →
      ∀ g : GL (Fin (G.V (.grid i j)).rank) (Fv D.host.F Bs.v₁), ∃ k : GA D (G.V (.grid i j)),
        k ∈ Set.range (emb D.sp.cm.sig (G.V (.grid i j)).gram Bs.v₁) ∧
        ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ r, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (evFin D.host.F Bs.v₁) φ r → ∃ φ₁ ∈ GlobalTheory.WeilM.SB _,
          om' (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU _ (-1) h.JW₁ k, 1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin D.host.F Bs.v₁) φ r) =
            GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin D.host.F Bs.v₁) φ₁ r ∧ ι φ₁ = omB ν α g 1 (ι φ) := by
  intro D T L sc G W t i j M e Bs Γ X om om' h hTr
  obtain ⟨K, hK⟩ := GlobalTheory.SplitGLLift.exists_hom_supp_split W t i j M e Bs Γ X om om' h hTr
  let K' : GL (Fin (G.V (.grid i j)).rank) (Fv D.host.F Bs.v₁) →* GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig Γ.V'.J :=
    { toFun := fun g => GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU _ (-1) h.JW₁ (K g)
      map_one' := by simp only [map_one]; exact conjU_one' _ _ _
      map_mul' := fun g g' => by simp only [map_mul]; exact conjU_mul' _ _ _ _ _ }
  have hK' : ∀ g, K' g = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU _ (-1) h.JW₁ (K g) := fun _ => rfl
  have hB := fun g => GlobalTheory.T.weilRepresentationLocality_unitaryGroupV' Bs Γ X om om' hTr Bs.v₁ (K' g) (hK g).1
  choose S hS using hB
  have hSplit := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hTr.weil'
  have pres : ∀ p Φ, Φ ∈ GlobalTheory.WeilM.schA D.host.F _ → om' p Φ ∈ GlobalTheory.WeilM.schA D.host.F _ :=
    fun p Φ hΦ => hSplit.pres p Φ hΦ
  have restS : ∀ g φ r, φ ∈ GlobalTheory.WeilM.SB _ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (evFin D.host.F Bs.v₁) φ r →
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (evFin D.host.F Bs.v₁) (S g φ) r := fun g φ r hφ hr =>
    ⟨hr.1, by rw [← (hS g φ hφ).2 r hr]; exact pres _ _ hr.2⟩
  have h1 : ∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, S g φ ∈ GlobalTheory.WeilM.SB _ := fun g φ hφ => (hS g φ hφ).1
  have h2 : ∀ g g', ∀ φ ∈ GlobalTheory.WeilM.SB _, S (g * g') φ = S g (S g' φ) := by
    intro g g' φ hφ
    refine GlobalTheory.TensUniq.eq_of_tens_eq Bs.v₁ φ _ _ hφ fun r hr => ?_
    have e1 : ((K' (g * g'), (1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig Γ.W.J))) =
        (K' g, 1) * (K' g', 1) := by rw [map_mul, Prod.mk_mul_mk, one_mul]
    rw [← (hS (g * g') φ hφ).2 r hr, e1, map_mul, Module.End.mul_apply, (hS g' φ hφ).2 r hr,
      (hS g (S g' φ) (h1 g' φ hφ)).2 r (restS g' φ r hφ hr)]
  have h3 : ∀ φ ∈ GlobalTheory.WeilM.SB _, S 1 φ = φ := by
    intro φ hφ
    refine GlobalTheory.TensUniq.eq_of_tens_eq Bs.v₁ φ _ _ hφ fun r hr => ?_
    have e1 : ((K' 1, (1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig Γ.W.J))) = 1 := by rw [map_one]; rfl
    rw [← (hS 1 φ hφ).2 r hr, e1, map_one, Module.End.one_apply]
  have hψ : Continuous Bs.ψ := hTr.base.std.1
  have atAct : ∀ g (γ : Matrix _ _ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE D.host.F D.host.E)),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin D.host.F Bs.v₁) γ →
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin D.host.F Bs.v₁)
        (GlobalTheory.WeilM.actAB (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (K' g, (1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig Γ.W.J)) γ) := by
    intro g γ hγ u hu
    simp only [GlobalTheory.WeilM.actAB]
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, hγ u hu, Matrix.mul_zero, Matrix.zero_mul]
  have h4 : ∀ g (γ : Matrix _ _ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE D.host.F D.host.E)),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin D.host.F Bs.v₁) γ → ∀ φ ∈ GlobalTheory.WeilM.SB _,
        S g (GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ γ) φ) =
          GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁)
            (GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ (GlobalTheory.WeilM.actAB (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig)
              (K' g, (1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig Γ.W.J)) γ)) (S g φ) := by
    intro g γ hγ φ hφ
    have hw := GlobalTheory.SchrSB.schr_mem_SB Bs.ψ hψ Bs.v₁ (GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ γ) φ hφ
    refine GlobalTheory.TensUniq.eq_of_tens_eq Bs.v₁ φ _ _ hφ fun r hr => ?_
    have hb1 := GlobalTheory.VacBridge.rho_acts_locCo Γ.M'.co Bs.ψ Bs.v₁ γ hγ φ r hr
    have hRw : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (evFin D.host.F Bs.v₁)
        (GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ γ) φ) r :=
      ⟨hr.1, by rw [← hb1]; exact GlobalTheory.HeisSchA.rho_mem_schA Γ.M' Bs.ψ hTr.base.std γ _ hr.2⟩
    rw [← (hS g _ hw).2 r hRw, ← hb1, hSplit.impl _ _ _ hr.2, (hS g φ hφ).2 r hr,
      GlobalTheory.VacBridge.rho_acts_locCo Γ.M'.co Bs.ψ Bs.v₁ _ (atAct g γ hγ) (S g φ) r (restS g φ r hφ hr)]
  have h5 : ∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ μ : @Measure (Fin (G.V (.grid i j)).rank × Fin ((G.V (.grid (i + 1) (j + 1))).rank + (G.V (.grid i j)).rank) → Fv D.host.F Bs.v₁) (borel _),
      @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∫⁻ y, ‖S g φ y‖ₑ ^ 2 ∂μ = ∫⁻ y, ‖φ y‖ₑ ^ 2 ∂μ :=
    fun g φ hφ μ hμ => GlobalTheory.T.localWeilOperator_isometry_schwartzBruhat Bs Γ X om om' hTr Bs.v₁ (K' g) (hK g).1 φ (S g φ) hφ (h1 g φ hφ) (hS g φ hφ).2 μ hμ
  obtain ⟨ν, α, hν, hC⟩ := GlobalTheory.T.heisenbergIntertwiner_eq_twisted_weilOperator Bs Γ X om om' hTr K' (fun g => hK g) S h1
    (fun g => linear_of_acts Bs.v₁ (om' (K' g, 1)) (S g) (hS g)) h2 h3 h4 h5
  exact ⟨ν, α, hν, fun ι hι g => ⟨K g, mem_range_emb_of_conjU_mem_UAt _ Γ.V' (-1) h.JW₁ Bs.v₁ (K g) (hK g).1, fun φ hφ r hr =>
    ⟨S g φ, h1 g φ hφ, (hS g φ hφ).2 r hr, hC ι hι g φ hφ⟩⟩⟩

theorem exists_datum_comb_mem_So_at : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (B : Frames G)
    (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (M : Vol G) (hM : M.Is t) (Θ : TotT G (routeBig t i j))
    (Θ' : TotT G (routeSmall t i j)) (hΘ : IsMatched B t ρ i j Θ Θ') (g₁ : GA D (G.V (.grid (i + 1) j)))
    (e : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Num G i j) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j)
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W)
    (h : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.IsTripleOf W M t i j e Bs Γ X) (hTr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om')
    (hv : ∀ w ∈ locPl G t, w.under (𝓞 D.host.F) ≠ Bs.v₁),
    ∃ ΦB, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.IsDatumB W e Γ Θ' ΦB ∧ ∃ z : GA D (G.V (.grid i j)) →₀ ℂ, zdeg z ≠ 0 ∧
      (z.sum fun k c => c • om' (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU _ (-1) h.JW₁ k, 1) ΦB) ∈ Γ.M'.So Bs.ψ Bs.τ₁ ∧
      ∀ b ∈ z.support, b ∈ Set.range (emb D.sp.cm.sig (G.V (.grid i j)).gram Bs.v₁) := by
  intro D T L sc G μ₀ hL W B ρ t i j M hM Θ Θ' hΘ g₁ e Bs Γ X om om' h hTr hv
  obtain ⟨ΦB, hD, m, f, φ, φ₀, rfl, hSB, hvac, h₀, ι, P, Λ, c, hι, hφ₀⟩ :=
    GlobalTheory.T.exists_routeDatum_finite_pureTensors_vacuum hL W B ρ t i j M hM Θ Θ' hΘ g₁ e Bs Γ X om om' h hTr hv
  classical
  obtain ⟨ν, α, hν, hact⟩ := act_omB_at W t i j M e Bs Γ X om om' h hTr
  obtain ⟨zS, hz, hS⟩ := GlobalTheory.T.exists_goodPlace_translateCombination_latticeIndicator Bs Γ hTr.geo.hM' hTr.geo.lt om'
    (H := {k : GA D (G.V (.grid i j)) // k ∈ Set.range (emb D.sp.cm.sig (G.V (.grid i j)).gram Bs.v₁)})
    (fun k => GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU _ (-1) h.JW₁ k.1) ν α hν ι hι
    (fun g => by obtain ⟨k, hk1, hk2⟩ := hact ι hι g; exact ⟨⟨k, hk1⟩, hk2⟩) f φ φ₀ hSB hvac h₀ P Λ c hφ₀
  refine ⟨_, hD, zS.mapDomain Subtype.val, ?_, ?_, ?_⟩
  · rw [zdeg, Finsupp.sum_mapDomain_index (by simp) (by simp)]
    exact hz
  · rw [Finsupp.sum_mapDomain_index (by simp) (fun _ _ _ => add_smul _ _ _)]
    exact hS
  · intro b hb
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hb)
    exact k.2

open GlobalTheory.ZConvIdent in

theorem translates_kerSmall_le_theta_at : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (B : Frames G)
    (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (M : Vol G) (hM : M.Is t) (Θ : TotT G (routeBig t i j))
    (Θ' : TotT G (routeSmall t i j)) (hΘ : IsMatched B t ρ i j Θ Θ') (g₁ : GA D (G.V (.grid (i + 1) j)))
    (e : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Num G i j) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j)
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W)
    (h : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.IsTripleOf W M t i j e Bs Γ X) (hTr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om')
    (hv : ∀ w ∈ locPl G t, w.under (𝓞 D.host.F) ≠ Bs.v₁),
    ∃ (z : GA D (G.V (.grid i j)) →₀ ℂ) (Φ : (Fin (G.V (.grid i j)).rank × Fin ((G.V (.grid (i + 1) (j + 1))).rank +
        (G.V (.grid i j)).rank) → AF D.host.F) → ℂ) (a : GA D (G.V (.grid i j)) → GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.UB Γ.V'.J) (C₀ : ℝ),
      zdeg z ≠ 0 ∧ Φ ∈ Γ.M'.So Bs.ψ Bs.τ₁ ∧
      (∀ g u, ‖translates z (kerSmall W Θ' g g₁) u‖ ≤
        C₀ * ‖GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.theta om' Φ (a u) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blkU _ _ e h.JWW (g, g₁))‖) ∧
      ∀ b ∈ z.support, b ∈ Set.range (emb D.sp.cm.sig (G.V (.grid i j)).gram Bs.v₁) := by
  intro D T L sc G μ₀ hL W B ρ t i j M hM Θ Θ' hΘ g₁ e Bs Γ X om om' h hTr hv
  obtain ⟨ΦB, hB, z, hz, hS, hsupp⟩ := exists_datum_comb_mem_So_at hL W B ρ t i j M hM Θ Θ' hΘ g₁ e Bs Γ X om om' h hTr hv
  obtain ⟨ξ, hξ, hk⟩ := GlobalTheory.T.small_route_kernel_eq_unit_norm_mul_theta hL W B ρ t i j M hM Θ Θ' hΘ g₁ e Bs Γ X om om' h hTr hv ΦB hB
  refine ⟨z, _, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU _ (-1) h.JW₁, 1, hz, hS, fun g u => le_of_eq ?_, hsupp⟩
  have hW := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hTr.weil'
  have hpres : ∀ p φ, φ ∈ schA D.host.F _ → om' p φ ∈ schA D.host.F _ := fun p φ hφ => hW.pres p φ hφ
  have hB0 := hB.1
  set a := GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU _ (-1) h.JW₁
  set hh := GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blkU _ _ e h.JWW (g, g₁)
  have ha : ∀ x y, a (x * y) = a x * a y := conjU_mul _ _ _
  have e1 : translates z (kerSmall W Θ' g g₁) u =
      ξ (g, g₁) * z.sum fun k c => c * thetaSum D.host.F (om' (a u, hh) (om' (a k, 1) ΦB)) := by
    rw [translates, Finsupp.mul_sum]
    refine Finsupp.sum_congr fun k _ => ?_
    rw [hk, ha, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.theta, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
    ring
  have e2 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.theta om' (z.sum fun k c => c • om' (a k, 1) ΦB) (a u) hh =
      z.sum fun k c => c * thetaSum D.host.F (om' (a u, hh) (om' (a k, 1) ΦB)) := by
    rw [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.theta, map_finsuppSum, Finsupp.sum, thetaSum_finset_sum]
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_smul, thetaSum_smul]
    · intro k _
      rw [map_smul]
      exact Submodule.smul_mem _ _ (hpres _ _ (hpres _ _ hB0))
  rw [e1, e2, norm_mul, hξ, one_mul]

theorem squareTriple_avoid {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}
    (hL : L.Is μ₀) (W : G.Weil) (t : T) (i j : Fin D.R.m) (hst : SquareStanding G t)
    (P : Finset (HeightOneSpectrum (𝓞 D.host.F))) (M : Vol G) (hM : M.Is t) :
    ∃ (e : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Num G i j) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E)
      (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : _) (om' : _),
      GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.IsTripleOf W M t i j e Bs Γ X ∧ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om' ∧
      (∀ w ∈ locPl G t, w.under (𝓞 D.host.F) ≠ Bs.v₁) ∧ Bs.v₁ ∉ P := by
  classical
  obtain ⟨e, Bs, Γ, X, om, om', h, hTr, -⟩ := GlobalTheory.T.squareThetaTripleHypotheses_of_standing hL W t i j hst M hM
  obtain ⟨v, hvP, hvs, hvl, ⟨τ⟩⟩ := GlobalTheory.T.exists_splitCompletely_auxiliary_place_outside_finset (G := G) hL t (X.T ∪ P)
  let Bs' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E := { Bs with v₁ := v, τ₁ := τ }
  refine ⟨e, Bs', Γ, X, om, om', ?_, ?_, hvl, fun h' => hvP (Finset.mem_union_right _ h')⟩
  · exact ⟨h.ψ, h.JW, h.JW₁, h.JWW, h.cart, h.α, h.β, h.μW, h.μW₁⟩
  · obtain ⟨hb, hg, hc, hw, hw'⟩ := hTr
    exact ⟨{ hb with }, { hg with hV := { hg.hV with }, hV' := { hg.hV' with }, hW := { hg.hW with } }, { hc with good := ⟨fun h' => hvP (Finset.mem_union_left _ h'), hvs⟩ }, hw, hw'⟩

theorem standing_all : BigR fun R sc => ∀ (G : GridData R.toLevCh sc) t, SquareStanding G t := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hS => ?_⟩⟩
  have h11 : 11 ≤ D.host.splitBound := hS.size.2.1.eleven_le
  intro G t
  refine ⟨h11, fun w hw => ?_⟩
  classical
  unfold locPl at hw
  rcases Finset.mem_union.1 hw with hw | hw
  · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hw
    have hunder := G.pl.under_w hv
    have lift : ∀ n : ℕ, ((n : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal → ((n : ℕ) : 𝓞 D.host.E) ∈ (G.pl.w v).asIdeal := by
      intro n hn
      rw [← hunder] at hn
      have := Ideal.mem_comap.1 hn
      simpa using this
    obtain ⟨p, hp, hcop⟩ : ∃ p : ℕ, ((p : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal ∧
        Nat.Coprime p (D.host.QS * D.host.q * D.host.d * Ideal.absNorm D.host.ccK) := by
      rcases G.pl.mem_S0_of_sum_eq.1 hv with rfl | h1
      · exact ⟨q0 D, G.pl.basePlace_over_qZero, GlobalTheory.PlacesPrime.leastSplitAuxiliaryPrime_coprime_host_invariants D⟩
      · rcases (S1_mem_OmF D).1 h1 with h | h | h | h
        · exact ⟨_, h, GlobalTheory.PlacesPrime.coprime_level hS.size (D.host.g_prime 0) (D.host.g_level 0)⟩
        · exact ⟨_, h, GlobalTheory.PlacesPrime.coprime_level hS.size (D.host.g_prime 1) (D.host.g_level 1)⟩
        · exact ⟨_, h, GlobalTheory.PlacesPrime.coprime_level hS.size D.host.pde_prime D.host.pde_level.1⟩
        · exact ⟨_, h, GlobalTheory.PlacesPrime.coprime_level hS.size D.host.pde'_prime D.host.pde_level.2⟩
    exact GlobalTheory.PlacesPrime.not_both_mem (G.pl.w v).isPrime hcop (lift p hp)
  · intro hmem
    have h1 := (hS.core.lev.Q_off t w hw).1
    have h2 := hS.guard.2 t w hw
    push_cast at hmem h1 h2
    rcases w.isPrime.mem_or_mem hmem with h | h
    · exact h1 (Ideal.mul_mem_right _ _ h)
    · exact h2 (Ideal.mul_mem_left _ _ h)

theorem exists_regulariser_at : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.SquareSt.WeilConvergence → GlobalTheory.SquareSt.LocalMatching → GlobalTheory.SquareSt.ThetaIntegralsAgree → BigR fun {D} _ _ _ _ T _ _ _ _ _ R sc => ∀ (G : GridData R.toLevCh sc) (W : G.Weil), W.Over R → ∀ (B : Frames G)
  (ρ : RealMatch W), ρ.Over R → ∀ (t : T) (i j : Fin D.R.m) (M : Vol G), M.Is t → ∀ Θ Θ', IsMatched B t ρ i j Θ Θ' → ∀ g g₁
  (P : Finset (HeightOneSpectrum (𝓞 D.host.F))), ∃ v ∉ P, ∃ w : GA D (G.V (.grid i j)) →₀ ℂ, zdeg w ≠ 0 ∧
    IntegrableOn (translates w (kerSmall W Θ' g g₁)) (M.fd _) (M.ν _) ∧
    ∀ b ∈ w.support, b ∈ Set.range (GlobalTheory.AdelicU.emb D.sp.cm.sig (G.V (.grid i j)).gram v) := by
  intro _ hK _ _ _
  obtain ⟨CF0, hH⟩ := standing_all
  refine ⟨CF0, fun ε CF hCF => ?_⟩
  obtain ⟨x₀, hx⟩ := hH ε CF hCF
  refine ⟨x₀, fun D large₂ he hx0 Γ _ _ Pl0 T A Ks _ _ _ R F hS => ?_⟩
  have hst := hx D large₂ he hx0 Γ Pl0 T A Ks R F hS
  intro G W _ B ρ _ t i j M hM Θ Θ' hΘ g g₁ P
  have hL : R.toLevCh.Is A.μ0 := hS.core.lev
  obtain ⟨e, Bs, Γ', X, om, om', h, hTr, hv, hvP⟩ := squareTriple_avoid hL W t i j (hst G t) P M hM
  obtain ⟨z, Φ, a, C₀, hz, hΦ, hid, hsupp⟩ :=
    translates_kerSmall_le_theta_at hL W B ρ t i j M hM Θ Θ' hΘ g₁ e Bs Γ' X om om' h hTr hv
  have dec := (hK.1 D.host.F D.host.E D.sp.cm.sig Bs _ _ Γ' X om om' hTr).1
  obtain ⟨C, k, hC⟩ := (dec.2 Φ hΦ).1 0
  have hbd : ∀ u, ‖translates z (kerSmall W Θ' g g₁) u‖ ≤
      |C₀| * |C| * (2 * GlobalTheory.Grow.quotHeight _ g * GlobalTheory.Grow.height _ g₁) ^ k := by
    intro u
    obtain ⟨γ, hγ, hle⟩ := GlobalTheory.Grow.exists_height_le_two_mul_quotHeight _ g
    have e1 : translates z (kerSmall W Θ' g g₁) u = translates z (kerSmall W Θ' (γ * g) g₁) u := by
      simp only [translates, GlobalTheory.ZConvLeft.kerSmall_rat_left hL W B ρ t i j Θ Θ' hΘ g₁ γ hγ]
    rw [e1]
    have h1 := hC (a u) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blkU _ _ e h.JWW (γ * g, g₁))
    rw [pow_zero, mul_one] at h1
    have h2 := GlobalTheory.BlockHeight.ht_blkU_le _ _ e h.JWW (γ * g) g₁
    have h3 : (0 : ℝ) ≤ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ht (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blkU _ _ e h.JWW (γ * g, g₁)) : ℝ) := NNReal.coe_nonneg _
    have h4 : (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ht (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blkU _ _ e h.JWW (γ * g, g₁)) : ℝ) ≤
        2 * GlobalTheory.Grow.quotHeight _ g * GlobalTheory.Grow.height _ g₁ :=
      h2.trans (mul_le_mul_of_nonneg_right hle (GlobalTheory.Grow.height_pos _ _).le)
    calc _ ≤ C₀ * ‖GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.theta om' Φ (a u) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blkU _ _ e h.JWW (γ * g, g₁))‖ := hid _ _
      _ ≤ |C₀| * ‖GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.theta om' Φ (a u) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blkU _ _ e h.JWW (γ * g, g₁))‖ :=
          mul_le_mul_of_nonneg_right (le_abs_self C₀) (norm_nonneg _)
      _ ≤ |C₀| * (|C| * (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ht (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blkU _ _ e h.JWW (γ * g, g₁)) : ℝ) ^ k) :=
          mul_le_mul_of_nonneg_left (h1.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg h3 k)))
            (abs_nonneg C₀)
      _ ≤ _ := by
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h3 h4 k) (mul_nonneg (abs_nonneg C₀) (abs_nonneg C))
  have hWl := (hM.vtx (.grid i j) ⟨i.2.le, j.2.le⟩).haar_fund
  haveI : IsFiniteMeasure ((M.ν (.grid i j)).restrict (M.fd (.grid i j))) :=
    isFiniteMeasure_restrict.2 (GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol _ _ _ hWl.1 hWl.2).ne
  have hcont := GlobalTheory.SmallRoute.continuous_translates_kerSmall hL W B ρ t i j Θ Θ' hΘ g₁ z
  exact ⟨Bs.v₁, hvP, z, hz, Integrable.of_bound ((hcont.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable) _
    (.of_forall hbd), hsupp⟩

end GlobalTheory.RegAt
