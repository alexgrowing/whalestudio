import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftPRouteSmall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPureSumZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GenPtSSubset
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmallModelThetaTransformInjectiveProductsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmulOfMapsInlMemS
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatPtSLeClosureAndSelfDual
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HTensMixHalfS
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaussianDatumFlippedFiniteTensorBigRoute
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerFixedFunctionsProportionalOfSelfDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridLocalTensorPlacesSplitIdempotentSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLatticeVacuumFinitePlacesRationalDarboux
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAddCharSymplecticLocalLatticeEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzFinitePureTensors
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorPureTensorComponentAtPlace
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeisenbergOperatorFixThetaDatumAwaySplitPlaces
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeisenbergOrientedFiniteFixesFockPolynomialVecto
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FockVectorsChainIsVacuumOffThetaLevels
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLowestKTypeFockMapThetaVectors
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtYAndItYOfPair
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNegConjMemberHermitianLatticeSpaceData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHermitianLatticeLocalBases
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLatticeLatticeBlockDirectSumScaled
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScaledLatticeConjDirectSumTraceSelfDualStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumB skewGram)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At latAtV)
open GlobalTheory.SchrodTheta GlobalTheory.SmallDat

noncomputable section

namespace GlobalTheory.SmallDatumPure

theorem isPureSum_of_slices {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (vac : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (κ → Fv F v) → ℂ)
    (hvac : ∀ᶠ v in Filter.cofinite, vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1)
    (v₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) {φ₀ : (κ → Fv F v₁) → ℂ} (h₀ : φ₀ ∈ GlobalTheory.WeilM.SB (κ → Fv F v₁)) (hne : φ₀ ≠ 0)
    {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ)
    (hsl : ∀ y : κ → AF F, (∀ k, evFin F v₁ (y k) = 0) →
      ∃ a : ℂ, ∀ ξ : κ → Fv F v₁, Φ (y + fun k => GlobalTheory.LatVac.liftV v₁ (ξ k)) = a * φ₀ ξ) :
    IsPureSum vac v₁ φ₀ Φ := by
  classical
  obtain ⟨T, m, f, φ, h1, h2, hsum⟩ := GlobalTheory.SchADecomp.exists_sum_pure F κ Φ hΦ
  obtain ⟨ζ, hζ⟩ := Function.ne_iff.1 hne
  have hζ' : φ₀ ζ ≠ 0 := hζ
  have hstd : ∀ k, ∀ᶠ v in Filter.cofinite, φ k v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 :=
    fun k => T.eventually_cofinite_notMem.mono (h2 k)
  choose r hr hr' using fun k => GlobalTheory.PureFactor.exists_rest_factor v₁ (f k) (φ k) (hstd k)
  refine ⟨m, fun k => (φ k v₁ ζ / φ₀ ζ) • f k, fun k => Function.update (φ k) v₁ φ₀, ?_, fun k v => ?_, fun k => ?_,
    fun k => Function.update_self _ _ _⟩
  · funext x
    have hat : ∀ ξ : κ → Fv F v₁, At (evFin F v₁) (fun k => GlobalTheory.LatVac.liftV v₁ (ξ k)) := fun ξ u hu =>
      funext fun k => GlobalTheory.LatVac.at_liftV v₁ (ξ k) u hu
    let y : κ → AF F := x - fun k => GlobalTheory.LatVac.liftV v₁ (evFin F v₁ (x k))
    have hy : ∀ k, evFin F v₁ (y k) = 0 := fun k => by
      simp only [y, Pi.sub_apply, map_sub, GlobalTheory.LatVac.evFin_liftV, sub_self]
    obtain ⟨a, ha⟩ := hsl y hy
    have hx : x = y + fun k => GlobalTheory.LatVac.liftV v₁ (evFin F v₁ (x k)) := (sub_add_cancel _ _).symm
    have e1 : Φ x = a * φ₀ fun k => evFin F v₁ (x k) := by rw [← ha, ← hx]
    have hrx : ∀ k, r k x = r k y := fun k => by
      conv_lhs => rw [hx]
      exact hr k _ _ (hat _)
    have e2 : a * φ₀ ζ = ∑ k, φ k v₁ ζ * r k x := by
      rw [← ha, hsum, Finset.sum_apply]
      refine Finset.sum_congr rfl fun k _ => ?_
      have := congrFun (hr' k (φ k v₁)) (y + fun k => GlobalTheory.LatVac.liftV v₁ (ζ k))
      rw [Function.update_eq_self] at this
      rw [← this, hrx]
      unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens
      rw [hr k _ _ (hat _)]
      congr 2
      funext i
      rw [Pi.add_apply, map_add, hy, zero_add, GlobalTheory.LatVac.evFin_liftV]
    have e3 : ∀ k, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure ((φ k v₁ ζ / φ₀ ζ) • f k) (Function.update (φ k) v₁ φ₀) x =
        (φ k v₁ ζ * r k x) * ((φ₀ fun k => evFin F v₁ (x k)) / φ₀ ζ) := fun k => by
      have := congrFun (hr' k φ₀) x
      unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure at this
      unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure
      rw [SchwartzMap.smul_apply, smul_eq_mul, mul_assoc, ← this]
      ring
    rw [Finset.sum_apply, Finset.sum_congr rfl fun k _ => e3 k, ← Finset.sum_mul, ← e2, e1]
    field_simp
  · beta_reduce
    by_cases e : v = v₁
    · subst e; rwa [Function.update_self]
    · rw [Function.update_of_ne e]; exact h1 k v
  · filter_upwards [hstd k, hvac, Filter.eventually_cofinite_ne v₁] with v a b c
    beta_reduce
    rw [Function.update_of_ne c, a, b]

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}

theorem idem_mul_eq_zero (hL : L.Is μ₀) {t : T} {ε : AE D} (hε : IsIdemSum ε (locPl G t)) {v : Pl D.host.F}
    (hv : ∀ w ∈ locPl G t, w.under (𝓞 D.host.F) ≠ v) {x : AE D} (hx : At (evFin D.host.F v) x) :
    ε * x = 0 ∧ cA D ε * x = 0 := by
  obtain ⟨hid, hsum⟩ := GlobalTheory.IdemAtPl.main hL (G := G) t
  have key : ∀ w ∈ locPl G t, atPl w 1 * x = 0 ∧ cA D (atPl w 1) * x = 0 := fun w hw => by
    obtain ⟨⟨h1, h2, -⟩, h3⟩ := hid w hw
    have h4 : (atPl w 1 + cA D (atPl w 1)) * x = 0 := by
      rw [h3, ← Algebra.smul_def]
      exact hx _ (evalV_singleFin_ne (hv w hw).symm 1)
    have h5 : cA D (atPl w 1) * cA D (atPl w 1) = cA D (atPl w 1) := by rw [← RingHom.map_mul, h1]
    constructor
    · linear_combination atPl w 1 * h4 - x * h1 - x * h2
    · linear_combination cA D (atPl w 1) * h4 - x * h5 - x * h2
  rw [(hsum ε hε).1, map_sum, Finset.sum_mul, Finset.sum_mul]
  exact ⟨Finset.sum_eq_zero fun w hw => (key w hw).1, Finset.sum_eq_zero fun w hw => (key w hw).2⟩

theorem fock_locVec (W : G.Weil) {p : Pair T} {ε : AE D} {f₀ φ f : WO (G.pS p) (G.pT p) → ℂ} (h₀ : W.IsVac p f₀)
    (h : IsLocVec W p ε f₀ φ f) (P : PolF D (G.pT p).rank (G.pS p).rank) :
    IsThetaFunO W.ψ _ _ (W.fock p f P) ∧
      ∀ u ∈ latO (G.pS p) (G.pT p) (G.latS p : Set _) (G.latT p : Set _) fun _ => True,
        (∀ a b, ε * u a b = 0 ∧ cA D ε * u a b = 0) → heisO W.ψ _ _ u f₀ = f₀ →
        heisO W.ψ _ _ u (W.fock p f P) = W.fock p f P := by
  have hf := GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt W.ψ_std W.θ_is h.2 h₀.2.theta
  have hth := fun Q => GlobalTheory.Chain.InnerSteps.theta_pureTensorO W.ψ_std W.θ_is (G.cartS W.cart p) (G.onS W.onb p)
    (G.onT W.cart p) (G.onT W.onb p) hf Q
  exact ⟨hth P, fun u hu h1 h2 => GlobalTheory.Hk3.FiniteHeis.heisO_pureTensorO_of_finite W.ψ W.θ _ _ W.θ_is _ _ _ _ f hth u
    (GlobalTheory.VacGood.infPart_latO hu) (GlobalTheory.Hk3.heisO_fix_thetaAt_off W.ψ _ _ ε _ 1 f₀ φ f h.2 u h1 h2) P⟩

abbrev latSmall (G : GridData L sc) (i j : ℕ) : Submodule (𝓞 D.host.E) (Fin (spW₁ G i j).rank → D.host.E) :=
  GlobalTheory.TripleSpaceW.conjSub (G.Λ (.grid i j))

abbrev latSkew {i j : ℕ} (e : Num G i j) :
    Submodule (𝓞 D.host.E) (Fin ((spW G i j).rank + (spW₁ G i j).rank) → D.host.E) :=
  GlobalTheory.SkewLat.pairLat (GlobalTheory.SkewLat.scLat D.host.AA (G.Λ (.grid i (j + 1))))
    (GlobalTheory.TripleSpaceW.conjSub (GlobalTheory.SkewLat.scLat D.host.AA (GlobalTheory.TripleSpaceW.conjSub (G.Λ (.grid (i + 1) j))))) e

theorem latPtS_le {i j : ℕ} (t : T) (e : Num G i j) (X : Spc D.host.F D.host.E (spW₁ G i j).rank)
    (Y : Spc D.host.F D.host.E ((spW G i j).rank + (spW₁ G i j).rank)) (hX : X.L = latSmall G i j) (hY : Y.L = latSkew e)
    (v : Pl D.host.F) : ∀ u ∈ latPtS t e v, u ∈ latAtV X Y v := by
  have k1 : ∀ x ∈ latA G t i j, GlobalTheory.LatVac.liftV v 1 • ofMaps t e (x, 0) ∈ latAtV X Y v := fun x hx => by
    refine GlobalTheory.BigDat.map_mem_of_closure ((DistribMulAction.toAddMonoidHom (PtS G i j) (GlobalTheory.LatVac.liftV v 1)).comp
      ((maps t e).symm.toLinearMap.toAddMonoidHom.comp (AddMonoidHom.inl _ _))) ?_ hx
    rintro _ ⟨α, hα, -, a, ha, s, hs, r, hr, rfl⟩
    exact (congrArg (fun z => GlobalTheory.LatVac.liftV v 1 • z ∈ latAtV X Y v) (ofMaps_genA t e (pairA _ 0 α) a s r)).mpr
      (GlobalTheory.BigDat.one_smul_gen_mem _ _ v hα (hX.ge (GlobalTheory.BigDat.star_mem_conjSub hs))
        (hY.ge (GlobalTheory.BigDat.pair_mem e (GlobalTheory.BigDat.smul_mem_scLat_of_mem ha hr) (zero_mem _))))
  have k2 : ∀ x ∈ latB G i j, GlobalTheory.LatVac.liftV v 1 • ofMaps t e (0, x) ∈ latAtV X Y v := fun x hx => by
    refine GlobalTheory.BigDat.map_mem_of_closure ((DistribMulAction.toAddMonoidHom (PtS G i j) (GlobalTheory.LatVac.liftV v 1)).comp
      ((maps t e).symm.toLinearMap.toAddMonoidHom.comp (AddMonoidHom.inr _ _))) ?_ hx
    rintro _ ⟨α, hα, -, a, ha, s, hs, r, hr, rfl⟩
    exact (congrArg (fun z => GlobalTheory.LatVac.liftV v 1 • z ∈ latAtV X Y v) (ofMaps_genB t e (pairA _ 0 α) a s r)).mpr
      (GlobalTheory.BigDat.one_smul_gen_mem _ _ v hα (hX.ge (GlobalTheory.BigDat.star_mem_conjSub hr))
        (hY.ge (GlobalTheory.BigDat.pair_mem e (zero_mem _)
          (GlobalTheory.BigDat.star_mem_conjSub (GlobalTheory.BigDat.smul_mem_scLat_of_mem ha (GlobalTheory.BigDat.star_mem_conjSub hs))))))
  rintro u ⟨hat, h1, h2⟩
  have e1 : GlobalTheory.LatVac.liftV v 1 • u = u := by
    have := hat (1 - GlobalTheory.LatVac.liftV v 1) (by rw [map_sub, map_one, GlobalTheory.LatVac.evFin_liftV, sub_self])
    rw [sub_smul, one_smul, sub_eq_zero] at this
    exact this.symm
  have e2 : u = ofMaps t e (mapA t e u, 0) + ofMaps t e (0, mapB e u) :=
    ((ofMaps_maps t e u).symm.trans (congrArg (ofMaps t e) (Prod.ext (add_zero _).symm (zero_add _).symm))).trans
      (map_add (maps t e).symm (mapA t e u, 0) (0, mapB e u))
  have e3 := add_mem (k1 _ h1) (k2 _ h2)
  rwa [← smul_add, ← e2, e1] at e3

section Square

variable {W : G.Weil} {t : T} {i j : Fin D.R.m} {M : Vol G} {e : Num G i j} {Bs : Base D.host.F D.host.E}
  {Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j} {X : Chars D.host.F D.host.E} {om : Rep D.sp.cm.sig Γ.V Γ.W} {om' : Rep D.sp.cm.sig Γ.V' Γ.W}

theorem exists_bases (hL : L.Is μ₀) (h : IsTripleOf W M t i j e Bs Γ X) (hT : IsTriple Bs Γ X om om') :
    ∃ b₁ b₂, Spc.IsHerm D.sp.cm.sig Bs ⟨Γ.V'.J, latSmall G i j, Γ.V'.θ, b₁⟩ Γ.q ((spW₁ G i j).rank - Γ.q) ∧
      Spc.IsSkew D.sp.cm.sig Bs ⟨Γ.W.J, latSkew e, Γ.W.θ, b₂⟩
        ((spW G i j).rank + (spW₁ G i j).rank - (Γ.p + Γ.q)) (Γ.p + Γ.q) := by
  classical
  have hsd := (node_isV G hL (X := .grid i j) ⟨i.2.le, j.2.le⟩).sd
  have hV := (node_isV G hL (X := .grid i (j + 1)) ⟨i.2.le, j.2⟩).sd
  have hV₁ := (node_isV G hL (X := .grid (i + 1) j) ⟨i.2, j.2.le⟩).sd
  haveI hl₁ : (latSmall G i j).IsLattice D.host.E := GlobalTheory.TripleSpaceW.conjSub_isLattice hsd.1
  have hAA : D.host.AA ≠ 0 := fun h => by
    have := Formalism.IndefR.Fin.factPrincipalDatum D.R D.host
    rw [h, mul_zero, zero_mul, zero_mul] at this
    exact zero_ne_one this
  haveI hl₂ : (latSkew e).IsLattice D.host.E :=
    GlobalTheory.SkewLat.PairLatLattice.pairLat_isLattice (GlobalTheory.SkewLat.PairLatLattice.scLat_isLattice hAA hV.1)
      (GlobalTheory.TripleSpaceW.conjSub_isLattice (GlobalTheory.SkewLat.PairLatLattice.scLat_isLattice hAA
        (GlobalTheory.TripleSpaceW.conjSub_isLattice hV₁.1))) e
  choose b₁ hb₁ using fun v : Bs.P => exists_isSplitBasis (Bs.τ v) (latSmall G i j) (isCMExt_host D)
  choose b₂ hb₂ using fun v : Bs.P => exists_isSplitBasis (Bs.τ v) (latSkew e) (isCMExt_host D)
  refine ⟨fun v => if h : v ∈ Bs.P then b₁ ⟨v, h⟩ else 1, fun v => if h : v ∈ Bs.P then b₂ ⟨v, h⟩ else 1,
    ⟨hT.geo.hV'.herm, hT.geo.hV'.sig, hl₁, fun y => ?_, hT.geo.hV'.cartan, fun v => ?_⟩,
    ⟨hT.geo.hW.skew, hT.geo.hW.sig, hl₂, fun y => ?_, hT.geo.hW.cartan, fun v => ?_⟩⟩
  · have := GlobalTheory.TripleSpace.mem_starLat_iff_form (spW₁ G i j) hsd y
    rw [← h.JW₁] at this
    simp only [Formalism.L2.Col.mem_starLat] at this
    exact this
  · show IsSplitBasis _ _ (if h : v.1 ∈ Bs.P then b₁ ⟨v.1, h⟩ else 1)
    rw [dif_pos v.2]
    exact hb₁ v
  · have := GlobalTheory.T.scaledLattice_conj_directSum_trace_selfDual _ _ hV hV₁ e y
    rw [← h.JWW] at this
    exact this
  · show IsSplitBasis _ _ (if h : v.1 ∈ Bs.P then b₂ ⟨v.1, h⟩ else 1)
    rw [dif_pos v.2]
    exact hb₂ v

set_option maxHeartbeats 800000 in

theorem exists_vac (hL : L.Is μ₀) (h : IsTripleOf W M t i j e Bs Γ X) (hT : IsTriple Bs Γ X om om') (v : Pl D.host.F) :
    (latSmall G i j).IsLattice D.host.E ∧ (latSkew e).IsLattice D.host.E ∧
    (∀ z : PtS G i j, At (evFin D.host.F v) z →
      (z ∈ latAtV {Γ.V' with L := latSmall G i j} {Γ.W with L := latSkew e} v ↔
        ∀ γ ∈ latAtV {Γ.V' with L := latSmall G i j} {Γ.W with L := latSkew e} v, Bs.ψ (sympS Γ z γ) = 1)) ∧
    ∃ φ₀ ∈ GlobalTheory.WeilM.SB (IxS G i j → Fv D.host.F v), φ₀ ≠ 0 ∧
      (∃ θ : 𝓞 D.host.E, (θ : D.host.E) + D.sp.cm.sig θ = 1 ∧
        ∀ γ ∈ latAtV {Γ.V' with L := latSmall G i j} {Γ.W with L := latSkew e} v,
          Acts (evFin D.host.F v) (Γ.M'.co.rho Bs.ψ γ) φ₀
            (Bs.ψ (⅟(2 : AF D.host.F) * symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (inclR (F := D.host.F) (AF D.host.F) (θ : D.host.E))
              (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.V'.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J) γ γ) • φ₀)) ∧
      ∀ Φ : (IxS G i j → AF D.host.F) → ℂ, (∀ γ ∈ genPtS t e v, Γ.M'.co.rho W.ψ γ Φ = Φ) →
        ∀ y : IxS G i j → AF D.host.F, (∀ k, evFin D.host.F v (y k) = 0) →
          ∃ a : ℂ, ∀ ξ, Φ (y + fun k => GlobalTheory.LatVac.liftV v (ξ k)) = a * φ₀ ξ := by
  obtain ⟨b₁, b₂, h₁, h₂⟩ := exists_bases hL h hT
  let X₁ : Spc D.host.F D.host.E (spW₁ G i j).rank := ⟨Γ.V'.J, latSmall G i j, Γ.V'.θ, b₁⟩
  let Y₁ : Spc D.host.F D.host.E ((spW G i j).rank + (spW₁ G i j).rank) := ⟨Γ.W.J, latSkew e, Γ.W.θ, b₂⟩
  have eΛ : latAtV {Γ.V' with L := latSmall G i j} {Γ.W with L := latSkew e} v = latAtV X₁ Y₁ v := rfl
  have hstd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd W.ψ := h.ψ ▸ hT.base.std
  have hle := latPtS_le t e X₁ Y₁ rfl rfl v
  obtain ⟨hgen, hsd⟩ := GlobalTheory.SmallDatLat.latPtS_le_closure_and_selfDual hL W t i j e Γ h.JW₁ h.JWW v
  have hiso : ∀ γ ∈ latAtV X₁ Y₁ v, ∀ γ' ∈ latAtV X₁ Y₁ v, W.ψ (sympS Γ γ γ') = 1 := fun γ hγ γ' hγ' => by
    have := GlobalTheory.LatVacArith.psi_symp_latAtV _ Bs X₁ Y₁ _ _ _ _ hT.base h₁ h₂ v (-1) 1 (by rw [map_one]; exact one_mem _)
      γ hγ γ' hγ'
    rw [one_mul, h.ψ] at this
    convert this using 3
    simp
  have hge : ∀ γ ∈ latAtV X₁ Y₁ v, γ ∈ latPtS t e v := fun γ hγ =>
    (hsd γ ((GlobalTheory.LatVac.latAtV_at_stable X₁ Y₁ v).1 γ hγ)).2 fun γ' hγ' => hiso γ hγ γ' (hle γ' hγ')
  obtain ⟨φ₀, k1, k2, θ, k3, k4⟩ := GlobalTheory.LatVac.exists_isVac _ Bs X₁ Y₁ _ _ _ _ hT.base h₁ h₂
    ⟨Γ.M'.co, Γ.M'.vac, Γ.M'.μ, Γ.M'.dom⟩ hT.geo.hM'.rat v
  rw [eΛ]
  refine ⟨h₁.lat, h₂.lat, fun z hz => ⟨fun hz' γ hγ => h.ψ ▸ hiso z hz' γ hγ, fun hz' =>
    hle z ((hsd z hz).2 fun γ hγ => h.ψ ▸ hz' γ (hle γ hγ))⟩, φ₀, k1, k2, ⟨θ, k3, k4⟩, fun Φ hΦ y hy => ?_⟩
  have hfix : ∀ γ ∈ genPtS t e v, Acts (evFin D.host.F v) (Γ.M'.co.rho W.ψ γ) φ₀ φ₀ := fun γ hγ => by
    have a1 : Acts (evFin D.host.F v) (Γ.M'.co.rho Bs.ψ γ) φ₀ _ := k4 γ (hle γ (genPtS_subset t e v hγ))
    have a2 : Bs.ψ (⅟(2 : AF D.host.F) * symp (R := AF D.host.F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig)
        (inclR (F := D.host.F) (AF D.host.F) (θ : D.host.E)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F X₁.J)
        (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Y₁.J) γ γ) = 1 := by
      rcases hγ with ⟨γ', hγ', rfl⟩ | ⟨-, ε, hε, hγ⟩
      · exact GlobalTheory.BigDat.VacFix.psi_double _ Bs X₁ Y₁ _ _ _ _ hT.base h₁ h₂ v θ γ' (hle γ' hγ')
      · unfold symp
        rw [show hTens _ _ _ γ γ = 0 from GlobalTheory.SmallDat.VacFix.hTens_mixHalfS e Γ h.JWW ε hε.2.1 γ hγ, mul_zero, map_zero,
          mul_zero, AddChar.map_zero_eq_one]
    rw [a2, one_smul, h.ψ] at a1
    exact a1
  obtain ⟨c, hc0, hc⟩ := GlobalTheory.LatBound.locCo_latAtV_bounded X₁ Y₁ v Γ.M'.co h₁.lat h₂.lat
  obtain ⟨a, ha⟩ := GlobalTheory.SchrFixUniq.proportional_of_fixed v (GlobalTheory.LatVac.psiAt W.ψ v) (GlobalTheory.VacAny.continuous_psiV hstd.1 v)
    (GlobalTheory.PsiNontriv.psiAt_ne_one W.ψ hstd v) (GlobalTheory.LatVac.locCo Γ.M'.co v '' genPtS t e v)
    ((latPtS t e v).map (GlobalTheory.LatVac.locCo Γ.M'.co v)) c
    (by rw [← AddMonoidHom.map_closure]; exact AddSubgroup.map_mono hgen) hc0
    (GlobalTheory.LatVac.DualLoc.map_selfDual v Γ.M'.co W.ψ _ (fun γ hγ => hγ.1) hsd)
    (by rintro _ ⟨γ, hγ, rfl⟩; exact hc γ (hle γ hγ)) φ₀
    (fun ξ => Φ (y + fun k => GlobalTheory.LatVac.liftV v (ξ k)))
    (by
      rintro _ ⟨γ, hγ, rfl⟩
      exact GlobalTheory.BigDat.schr_eq_of_acts _ _ (genPtS_subset t e v hγ).1 k1 (hfix γ hγ))
    (by
      rintro _ ⟨γ, hγ, rfl⟩
      exact GlobalTheory.BigDat.schr_slice _ _ (genPtS_subset t e v hγ).1 (hΦ γ hγ) hy) k2
  exact ⟨a, congrFun ha⟩

theorem exists_datum (hL : L.Is μ₀) (h : IsTripleOf W M t i j e Bs Γ X) (hT : IsTriple Bs Γ X om om') {ε : AE D}
    (hε : IsIdemSum ε (locPl G t)) {v : Pl D.host.F} (hv : ∀ w ∈ locPl G t, w.under (𝓞 D.host.F) ≠ v)
    {g₁ φ₁ f₁ : HomA G t i j → ℂ} {g₂ φ₂ f₂ : HomB G i j → ℂ} (v₁ : W.IsVac (.mu t i j) g₁) (v₂ : W.IsVac (.chi i j) g₂)
    (h₁ : IsLocVec W (.mu t i j) ε g₁ φ₁ f₁) (h₂ : IsLocVec W (.chi i j) ε g₂ φ₂ f₂) (P₁) (P₂) :
    ∃ Φ ∈ schA D.host.F (IxS G i j),
      HasTheta Γ.M'.co W.ψ Φ (boxS t e (W.fock (.mu t i j) f₁ P₁) (W.fock (.chi i j) f₂ P₂)) ∧
      ∀ γ ∈ genPtS t e v, Γ.M'.co.rho W.ψ γ Φ = Φ := by
  obtain ⟨-, hinj, hon⟩ := GlobalTheory.T.smallModel_thetaTransform_injective_products W M t i j e Bs Γ X om om' h hT
  obtain ⟨a₁, b₁⟩ := fock_locVec W v₁ h₁ P₁
  obtain ⟨a₂, b₂⟩ := fock_locVec W v₂ h₂ P₂
  have hstd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd W.ψ := h.ψ ▸ hT.base.std
  obtain ⟨Φ, hΦ, hb⟩ := hon _ _ a₁ a₂
  refine ⟨Φ, hΦ, fun u => ?_, fun γ hγ => hinj _ (GlobalTheory.HeisSchA.rho_mem_schA Γ.M' W.ψ hstd γ Φ hΦ) _ hΦ ?_⟩
  · rw [← hb]
    exact GlobalTheory.WeilM.hasSum_thetaSum _ (GlobalTheory.HeisSchA.rho_mem_schA Γ.M' W.ψ hstd u Φ hΦ)
  have hl := genPtS_subset t e v hγ
  have c₁ : ∀ a b, At (evFin D.host.F v) (mapA t e γ a b) := fun a b u hu => by
    have : u • mapA t e γ = 0 := by
      rw [← mapA_smul, hl.1 u hu]; exact congrArg Prod.fst (map_zero (maps t e))
    exact congrFun (congrFun this a) b
  have c₂ : ∀ a b, At (evFin D.host.F v) (mapB e γ a b) := fun a b u hu => by
    have : u • mapB e γ = 0 := by
      rw [← mapB_smul, hl.1 u hu]; exact congrArg Prod.snd (map_zero (maps t e))
    exact congrFun (congrFun this a) b
  have d : heisO W.ψ _ _ (mapA t e γ) g₁ = g₁ ∧ heisO W.ψ _ _ (mapB e γ) g₂ = g₂ := by
    rcases hγ with ⟨γ', k, rfl⟩ | ⟨k, δ, hδ, hh⟩
    · rw [two_nsmul, mapA_add, mapB_add, ← two_nsmul, ← two_nsmul]
      exact ⟨v₁.2.lat.1 _ k.2.1, v₂.2.lat.1 _ k.2.2⟩
    · exact ⟨v₁.2.lat.2 δ hδ _ k.2.1 hh.1, v₂.2.lat.2 δ hδ _ k.2.2 hh.2⟩
  rw [thetaS_rho, hb, heisS_box t e Γ h.JW₁ h.JWW, b₁ _ hl.2.1 (fun a b => idem_mul_eq_zero hL hε hv (c₁ a b)) d.1,
    b₂ _ hl.2.2 (fun a b => idem_mul_eq_zero hL hε hv (c₂ a b)) d.2]

end Square

theorem exists_datum_pure_selfdual : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (B : Frames G)
    (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (M : Vol G) (hM : M.Is t) (Θ : TotT G (routeBig t i j))
    (Θ' : TotT G (routeSmall t i j)) (hΘ : IsMatched B t ρ i j Θ Θ')
    (e : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Num G i j) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j)
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W)
    (h : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.IsTripleOf W M t i j e Bs Γ X) (hTr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om')
    (hv : ∀ w ∈ locPl G t, w.under (𝓞 D.host.F) ≠ Bs.v₁),
    ∃ ΦB, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.IsDatumB W e Γ Θ' ΦB ∧
      ∃ (m : ℕ) (f : Fin m → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin (G.V (.grid i j)).rank × Fin ((G.V (.grid (i + 1) (j + 1))).rank + (G.V (.grid i j)).rank)))
        (φ : Fin m → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl D.host.F, (Fin (G.V (.grid i j)).rank × Fin ((G.V (.grid (i + 1) (j + 1))).rank + (G.V (.grid i j)).rank) → Fv D.host.F v) → ℂ)
        (φ₀ : (Fin (G.V (.grid i j)).rank × Fin ((G.V (.grid (i + 1) (j + 1))).rank + (G.V (.grid i j)).rank) → Fv D.host.F Bs.v₁) → ℂ),
        ΦB = ∑ k, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f k) (φ k) ∧ (∀ k v, φ k v ∈ GlobalTheory.WeilM.SB _) ∧ (∀ k, ∀ᶠ v in Filter.cofinite, φ k v = Γ.M'.vac v) ∧
        (∀ k, φ k Bs.v₁ = φ₀) ∧ φ₀ ∈ GlobalTheory.WeilM.SB _ ∧ φ₀ ≠ 0 ∧
        ∃ (L₁ : Submodule (𝓞 D.host.E) (Fin (G.V (.grid i j)).rank → D.host.E)) (L₂ : Submodule (𝓞 D.host.E) (Fin ((G.V (.grid (i + 1) (j + 1))).rank + (G.V (.grid i j)).rank) → D.host.E))
          (θ : 𝓞 D.host.E), L₁.IsLattice D.host.E ∧ L₂.IsLattice D.host.E ∧
          (∀ z : Matrix (Fin (G.V (.grid i j)).rank) (Fin ((G.V (.grid (i + 1) (j + 1))).rank + (G.V (.grid i j)).rank)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE D.host.F D.host.E),
            GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin D.host.F Bs.v₁) z →
            (z ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV {Γ.V' with L := L₁} {Γ.W with L := L₂} Bs.v₁ ↔
              ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV {Γ.V' with L := L₁} {Γ.W with L := L₂} Bs.v₁,
                Bs.ψ (symp (R := AF D.host.F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (-1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.V'.J)
                  (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J) z γ) = 1)) ∧
          (θ : D.host.E) + D.sp.cm.sig θ = 1 ∧ (∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV {Γ.V' with L := L₁} {Γ.W with L := L₂} Bs.v₁,
            GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin D.host.F Bs.v₁) (Γ.M'.co.rho Bs.ψ γ) φ₀
              (Bs.ψ (⅟(2 : AF D.host.F) * symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (inclR (F := D.host.F) (AF D.host.F) (θ : D.host.E))
                (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.V'.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J) γ γ) • φ₀)) := by
  intro D T L sc G μ₀ hL W B ρ t i j M hM Θ Θ' hΘ e Bs Γ X om om' h hTr hv
  obtain ⟨a, b, τ, τ', n, Φ, -, -, ⟨ε, hε, ⟨φ₁, φ₂, hloc, -⟩, -⟩, -, rfl⟩ := hΘ
  obtain ⟨l₁, l₂, hsd, φ₀, hSB, hne, ⟨θ, hθ, hact⟩, hsl⟩ := exists_vac hL h hTr Bs.v₁
  have hC : ∀ d ∈ τ'.support, ∀ P : PolT G (routeSmall t i j), ∃ Ψ,
      IsPureSum Γ.M'.vac Bs.v₁ φ₀ Ψ ∧ Ψ ∈ GlobalTheory.WeilM.schA D.host.F _ ∧
      HasTheta Γ.M'.co W.ψ Ψ (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.boxB e
        (Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) d P)) := by
    intro d hd P
    obtain ⟨h1, h2⟩ := hloc d hd
    obtain ⟨⟨⟨⟩, f₁⟩, f₂⟩ := d
    obtain ⟨⟨⟨⟩, P₁⟩, P₂⟩ := P
    obtain ⟨Ψ, k1, k2, k3⟩ := exists_datum hL h hTr hε hv (ρ.vT_is t i j i.2.le j.2) (ρ.vX_is i j i.2 j.2.le) h1 h2 P₁ P₂
    exact ⟨Ψ, isPureSum_of_slices _ hTr.geo.hM'.std _ hSB hne k1 (hsl Ψ k3), k1, k2⟩
  choose! Ψ hΨ1 hΨ2 hΨ3 using hC
  have hpure : IsPureSum Γ.M'.vac Bs.v₁ φ₀
      (∑ P ∈ b.support, ∑ d ∈ τ'.support, (b P * τ' d) • Ψ d P) :=
    IsPureSum.sum _ _ fun P _ => IsPureSum.sum _ _ fun d hd => (hΨ1 d hd P).smul _
  have hth' : HasTheta Γ.M'.co W.ψ (∑ P ∈ b.support, ∑ d ∈ τ'.support, (b P * τ' d) • Ψ d P)
      (∑ P ∈ b.support, ∑ d ∈ τ'.support, (b P * τ' d) • GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.boxB e
        (Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) d P)) :=
    HasTheta.sum _ fun P _ => HasTheta.sum _ fun d hd => (hΨ3 d hd P).smul _
  refine ⟨∑ P ∈ b.support, ∑ d ∈ τ'.support, (b P * τ' d) • Ψ d P, ⟨Submodule.sum_mem _ fun P _ =>
    Submodule.sum_mem _ fun d hd => Submodule.smul_mem _ _ (hΨ2 d hd P), fun u => ?_⟩, ?_⟩
  · rw [hth'.thetaSum_eq u]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    unfold GlobalTheory.FunObj.tensT
    rw [Finsupp.sum]
    erw [← Finsupp.sum_finset_sum_index (h := fun d c => c * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.boxB e d u) (fun _ => zero_mul _)
      (fun _ _ _ => add_mul _ _ _)]
    refine Finset.sum_congr rfl fun P _ => ?_
    rw [Finsupp.sum]
    erw [← Finsupp.sum_finset_sum_index (h := fun d c => c * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.boxB e d u) (fun _ => zero_mul _)
      (fun _ _ _ => add_mul _ _ _)]
    refine Finset.sum_congr rfl fun d _ => ?_
    erw [Finsupp.sum_single_index (h := fun d c => c * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.boxB e d u) (zero_mul _)]
    rfl
  · obtain ⟨m, f, φ, hΦ, h1, h2, h3⟩ := hpure
    exact ⟨m, f, φ, φ₀, hΦ, h1, h2, h3, hSB, hne, _, _, θ, l₁, l₂, hsd, hθ, hact⟩

end GlobalTheory.SmallDatumPure

end
