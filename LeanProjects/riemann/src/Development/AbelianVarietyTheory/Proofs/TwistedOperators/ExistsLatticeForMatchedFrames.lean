import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.VacuumFixedByLevelPairAtSelfDualPlaces
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeisenbergOperatorFixThetaDatumAwaySplitPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaPureTensorO
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmPureTensorOOfFinite
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelVectorFiniteDatumIsThetaVacuumOff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PlaceIdempotentUnderEqOfLiesOver
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EventuallyExtUnramTwoNotMem
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AeCharUnramAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryFiniteAdelicGroupSplitFinitePlaceSet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallRouteCombinationMulLiftByDegree
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.SmallKerInv

open GlobalTheory.FinPl

variable {D : D7}

theorem placeIdem_smul_offP {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    {P : HeightOneSpectrum (𝓞 D.host.F) → Prop} {w : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F}
    (hε : IsPlaceIdem D w ε) (hw : ¬ P w) {u : WO S T}
    (hu : u ∈ latO S T LS LT P) : algebraMap (AF D.host.F) (AE D) ε • u = 0 := by
  obtain ⟨β, rfl, -, h0⟩ := hε
  induction hu using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩ := hx
    have hβα : β * α = 0 := by
      refine RestrictedProduct.ext _ _ fun y => ?_
      change evalV D.host.F y (β * α) = evalV D.host.F y 0
      rw [map_mul, map_zero]
      by_cases hy : y = w
      · subst hy; rw [hP y hw, mul_zero]
      · rw [h0 y hy, zero_mul]
    have hp : pairA D.host.F 0 β * pairA D.host.F 0 α = 0 := Prod.ext (mul_zero _) hβα
    ext i j
    change (pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 : D.host.E)) * (_ ⊗ₜ _) = (0 : AE D)
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, hp, TensorProduct.zero_tmul]
  | zero => rw [smul_zero]
  | add x x' _ _ h h' => rw [smul_add, h, h', add_zero]
  | neg x _ h => rw [smul_neg, h, neg_zero]

theorem idemSum_mul_offP {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    {P : HeightOneSpectrum (𝓞 D.host.F) → Prop} {e : AE D} {Pset : Finset (Formalism.L2.DIV.Pl D.host.E)}
    (he : IsIdemSum e Pset) (hv : ∀ PP ∈ Pset, ¬ P (PP.under (𝓞 D.host.F))) {u : WO S T}
    (hu : u ∈ latO S T LS LT P) (a b) : e * u a b = 0 ∧ cA D e * u a b = 0 := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  have key : ∀ PP ∈ Pset, es PP * u a b = 0 ∧ cA D (es PP) * u a b = 0 := by
    intro PP hPP
    obtain ⟨⟨a1, a2, w, ε, hε, a3⟩, -⟩ := hes PP hPP
    have hw : ¬ P w := fun h => hv PP hPP (by
      rw [GlobalTheory.IdemUnder.under_eq_of_isIdemAt D _ PP w ε (hes PP hPP) hε a3]; exact h)
    have h0 := congrFun (congrFun (placeIdem_smul_offP hε hw hu) a) b
    rw [Matrix.smul_apply, smul_eq_mul, ← a3, Matrix.zero_apply] at h0
    have c1 : cA D (es PP) * cA D (es PP) = cA D (es PP) := by rw [← map_mul, a1]
    have c2 : cA D (es PP) * es PP = 0 := by rw [mul_comm, a2]
    refine ⟨?_, ?_⟩
    · linear_combination es PP * h0 - u a b * a1 - u a b * a2
    · linear_combination cA D (es PP) * h0 - u a b * c1 - u a b * c2
  refine ⟨?_, ?_⟩
  · rw [Finset.sum_mul]; exact Finset.sum_eq_zero fun PP hPP => (key PP hPP).1
  · rw [map_sum, Finset.sum_mul]; exact Finset.sum_eq_zero fun PP hPP => (key PP hPP).2

theorem latO_le_true {S T : HSp D} (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) : latO S T LS LT P ≤ latO S T LS LT fun _ => True := by
  apply AddSubgroup.closure_mono
  rintro w ⟨α, hα, -, rest⟩
  exact ⟨α, hα, fun v h => absurd trivial h, rest⟩

end GlobalTheory.SmallKerInv

namespace GlobalTheory.SmallKerInv

open GlobalTheory.FinPl

variable {D : D7}

theorem om_fock_fix (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (hW : IsWeilDatumO ψ S T χS χT om) (hθ : IsInfFam θ)
    (LS : Lat S) (LT : Lat T) (P : Pl D → Prop)
    (hP : ∀ v, P v → IsSelfDualC S LS ∧ IsSelfDualC T LT ∧ Tame D v ∧ GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D χS v ∧
      GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D χT v)
    (e : AE D) (Pset : Finset (Formalism.L2.DIV.Pl D.host.E)) (he : IsIdemSum e Pset)
    (hoff : ∀ PP ∈ Pset, ¬ P (PP.under (𝓞 D.host.F)))
    (f₀ φ f : WO S T → ℂ) (h₀ : IsThetaFunO ψ S T f₀)
    (hlat : IsLatVac (heisO ψ S T) (latO S T (LS : Set _) (LT : Set _) fun _ => True) f₀)
    (hth : IsThetaAt ψ (symplO S T) (heisO ψ S T) e (latO S T (LS : Set _) (LT : Set _) fun _ => True) 1 f₀ φ f)
    (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (Q : PolF D T.rank S.rank) (κ : GA D S) (κ' : GA D T) (hκ : InK S LS P κ) (hκ' : InK T LT P κ') :
    om (κ, κ') (pureTensorO ψ θ S T sS sT BS BT f Q) = pureTensorO ψ θ S T sS sT BS BT f Q := by
  have hf : IsThetaFunO ψ S T f := GlobalTheory.GalLift.Vec.theta_of_thetaAt hW.std hθ hth h₀
  have hz : ∀ u ∈ latO S T (LS : Set _) (LT : Set _) P, ∀ a b, e * u a b = 0 ∧ cA D e * u a b = 0 :=
    fun u hu a b => idemSum_mul_offP he hoff hu a b
  have hle := latO_le_true (S := S) (T := T) (LS : Set _) (LT : Set _) P
  have hvac : Vac ψ S T LS LT P f := by
    refine ⟨hf, fun u hu => ?_, fun e' he' u hu hh => ?_⟩
    · exact GlobalTheory.Hk3.heisO_fix_thetaAt_off ψ S T e _ 1 f₀ φ f hth (2 • u)
        (hz _ (AddSubgroup.nsmul_mem _ hu 2)) (hlat.1 u (hle hu))
    · exact GlobalTheory.Hk3.heisO_fix_thetaAt_off ψ S T e _ 1 f₀ φ f hth u (hz u hu) (hlat.2 e' he' u (hle hu) hh)
  have hfix : om (κ, κ') f = f := GlobalTheory.VacFixP.vac_fix_on D ψ S T χS χT om hW LS LT P hP f hvac κ κ' hκ hκ'
  have := GlobalTheory.FiniteFock.om_pureTensorO_of_finite ψ θ S T χS χT om hθ hW sS sT BS BT f
    (fun R => GlobalTheory.GalLift.Vec.theta_pureTensorO hW.std hθ sS BS sT BT hf R)
    κ (GlobalTheory.FinPl.SetCut.grpAt_le_GfC S P hκ.1) κ' (GlobalTheory.FinPl.SetCut.grpAt_le_GfC T P hκ'.1) 1
    (by rw [hfix, one_smul]) Q
  rw [this, one_smul]

theorem inK_one (S : HSp D) (L : Lat S) (P : Pl D → Prop) : InK S L P 1 := by
  refine ⟨one_mem _, fun y _ => ?_⟩
  have h : mt S 1 = 1 := rfl
  rw [h, Matrix.one_mulVec]

end GlobalTheory.SmallKerInv

namespace GlobalTheory.SmallKerInv

open GlobalTheory.FinPl

theorem kerSmall_inv : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.SquareSt.WeilConvergence → GlobalTheory.SquareSt.LocalMatching → GlobalTheory.SquareSt.ThetaIntegralsAgree → BigR fun {D} _ _ _ _ T _ _ _ _ _ R sc => ∀ (G : GridData R.toLevCh sc) (W : G.Weil), W.Over R → ∀ (B : Frames G)
  (ρ : RealMatch W), ρ.Over R → ∀ (t : T) (i j : Fin D.R.m) Θ Θ', IsMatched B t ρ i j Θ Θ' → ∀ g g₁,
  ∃ (L : GlobalTheory.FinPl.Lat (G.V (.grid i j))) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))),
    L.FG ∧ Submodule.span D.host.E (L : Set (Fin (G.V (.grid i j)).rank → D.host.E)) = ⊤ ∧
    ∀ κ, GlobalTheory.FinPl.InK (G.V (.grid i j)) L (fun v => v ∉ S) κ → ∀ u, kerSmall W Θ' g g₁ (u * κ) = kerSmall W Θ' g g₁ u := by
  intro _ _ _ _ _
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ he hx Γ _ _ Pl0 T A Ks _ _ _ R F hS => ?_⟩⟩
  intro G W hW B ρ hρ t i j Θ Θ' hΘ g g₁
  have hL : R.toLevCh.Is A.μ0 := hS.core.lev
  obtain ⟨a, b, τ, τ', n, Φ, -, -, ⟨e, he, ⟨φ₁, φ₂, h1, -⟩, -⟩, -, rfl⟩ := hΘ
  have hm := W.om_is (.mu t i j) ⟨i.2.le, j.2⟩
  have hc := W.om_is (.chi (i : ℕ) j) ⟨i.2, j.2.le⟩
  have s0 := (node_isV G hL (X := .grid (i : ℕ) (j : ℕ)) ⟨i.2.le, j.2.le⟩).sd
  have s1 := (node_isV G hL (X := .grid (i : ℕ) ((j : ℕ) + 1)) ⟨i.2.le, j.2⟩).sd
  have s2 := (node_isV G hL (X := .grid ((i : ℕ) + 1) (j : ℕ)) ⟨i.2, j.2.le⟩).sd
  set good : Pl D → Prop := fun v => Tame D v ∧
    GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D (G.chrS (.mu t i j)) v ∧ GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D (G.chrT (.mu t i j)) v ∧
    GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D (G.chrS (.chi (i : ℕ) j)) v ∧ GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D (G.chrT (.chi (i : ℕ) j)) v
    with hgood
  have hev : ∀ᶠ v : Pl D in Filter.cofinite, good v := by
    filter_upwards [GlobalTheory.FinPl.eventually_extUnram_two_notMem D,
      GlobalTheory.FinPl.ShapeSecond.ae_charUnramAt _ hm.hecS.1, GlobalTheory.FinPl.ShapeSecond.ae_charUnramAt _ hm.hecT.1,
      GlobalTheory.FinPl.ShapeSecond.ae_charUnramAt _ hc.hecS.1, GlobalTheory.FinPl.ShapeSecond.ae_charUnramAt _ hc.hecT.1]
      with v h0 h1 h2 h3 h4
    exact ⟨⟨h0.1, Or.inl h0.2⟩, h1, h2, h3, h4⟩
  have hfin : {v | ¬ good v}.Finite := Filter.eventually_cofinite.1 hev
  classical
  refine ⟨G.Λ (.grid i j), hfin.toFinset ∪ (locPl G t).image (fun PP => PP.under (𝓞 D.host.F)),
    s0.1.fg, s0.1.span_eq_top, ?_⟩
  intro κ hκ u
  have hgd : ∀ v, v ∉ hfin.toFinset ∪ (locPl G t).image (fun PP => PP.under (𝓞 D.host.F)) → good v := by
    intro v hv
    by_contra h
    exact hv (Finset.mem_union_left _ (hfin.mem_toFinset.2 h))
  have hoff : ∀ PP ∈ locPl G t,
      ¬ (PP.under (𝓞 D.host.F) ∉ hfin.toFinset ∪ (locPl G t).image (fun PP => PP.under (𝓞 D.host.F))) :=
    fun PP hPP h => h (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hPP))
  unfold kerSmall
  refine Finsupp.sum_congr fun d hd => ?_
  obtain ⟨P, -, hP⟩ := Finset.mem_biUnion.1 (Finsupp.support_sum hd)
  obtain ⟨d', hd', hd''⟩ := Finset.mem_biUnion.1 (Finsupp.support_sum hP)
  have hdd := Finsupp.support_single_subset hd''
  rw [Finset.mem_singleton] at hdd
  subst hdd
  obtain ⟨⟨hsb1, hth1⟩, ⟨hsb2, hth2⟩⟩ := h1 d' hd'
  have hv1 := ρ.vT_is t i j i.2.le j.2
  have hv2 := ρ.vX_is i j i.2 j.2.le
  congr 1
  congr 1
  · show thetaKO (W.om (.mu t i j)) (u * κ) g _ = thetaKO (W.om (.mu t i j)) u g _
    unfold thetaKO
    have e1 : ((u * κ, g) : GA D (G.pS (.mu t i j)) × GA D (G.pT (.mu t i j))) = (u, g) * (κ, 1) := by simp
    rw [e1, map_mul, Module.End.mul_apply]
    refine congrArg (fun x => W.om (.mu t i j) (u, g) x 0) ?_
    exact om_fock_fix _ _ _ _ _ _ _ hm W.θ_is _ _ _
      (fun v hv => ⟨s0, s1, (hgd v hv).1, (hgd v hv).2.1, (hgd v hv).2.2.1⟩) e _ he hoff _ _ _
      hv1.2.theta hv1.2.lat hth1 _ _ _ _ _ κ 1 hκ (inK_one _ _ _)
  · show thetaKO (W.om (.chi (i : ℕ) j)) (negGA _ g₁) (u * κ) _ = thetaKO (W.om (.chi (i : ℕ) j)) (negGA _ g₁) u _
    unfold thetaKO
    have e2 : ((negGA _ g₁, u * κ) : GA D (G.pS (.chi (i : ℕ) j)) × GA D (G.pT (.chi (i : ℕ) j))) =
        (negGA _ g₁, u) * (1, κ) := by simp
    rw [e2, map_mul, Module.End.mul_apply]
    refine congrArg (fun x => W.om (.chi (i : ℕ) j) (negGA _ g₁, u) x 0) ?_
    exact om_fock_fix _ _ _ _ _ _ _ hc W.θ_is _ _ _
      (fun v hv => ⟨isSelfDualC_neg s2, s0, (hgd v hv).1, (hgd v hv).2.2.2.1, (hgd v hv).2.2.2.2⟩) e _ he hoff _ _ _
      hv2.2.theta hv2.2.lat hth2 _ _ _ _ _ 1 κ (inK_one _ _ _) hκ

end GlobalTheory.SmallKerInv
