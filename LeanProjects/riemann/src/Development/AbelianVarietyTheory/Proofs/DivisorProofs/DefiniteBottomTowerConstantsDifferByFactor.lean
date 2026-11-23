import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaPureTensorO
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumUniqueOnThetaFunctions
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ApplyAddInfRat
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorNegSpaceFrameChangeConjSubst
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SignedUnitaryGroupCompat
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockPolynomialVectorBasisChangeEqSubstitution
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GenusMassSignature
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LawsRescaleWithS

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SqTower.Normal

open MeasureTheory Matrix
open GlobalTheory.Grid (neg sgn ofSgn)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Rig stdFst stdSnd)
open scoped ComplexOrder

theorem cartan_eq_one {k : ℕ} {s : Matrix (Fin k) (Fin k) ℂ} (h : IsCartanInv 1 s) : s = 1 := by
  obtain ⟨h1, -, h3⟩ := h
  rw [Matrix.one_mul] at h3
  have hu : IsUnit (s + 1) := (h3.add Matrix.PosDef.one).isUnit
  have e : (s + 1) * (s - 1) = 0 := by
    rw [Matrix.mul_sub, Matrix.add_mul, h1, Matrix.one_mul, Matrix.mul_one, add_comm, sub_self]
  exact sub_eq_zero.1 (hu.mul_right_eq_zero.1 e)

variable {D : D7}

theorem rigging_cartan_eq_one_of_gram_one {V : HSp D} (hV : V.gram = 1) {r : Rig V} (h : r.Is) : r.s = fun _ => 1 := funext fun τ => by
  have e : gramAt D V τ = 1 := by rw [gramAt, hV]; simp
  exact cartan_eq_one (e ▸ (h.2.2 τ).1)

theorem exists_haar_factor (V : HSp D) {μ ν : Measure (GA D V)} {𝓕 𝓖 : Set (GA D V)}
    (hμ : μ.IsHaarMeasure ∧ IsFundamentalDomain (GQ V) 𝓕 μ) (hν : ν.IsHaarMeasure ∧ IsFundamentalDomain (GQ V) 𝓖 ν) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ F : GA D V → ℂ, (∀ γ ∈ GQ V, ∀ g, F (γ * g) = F g) →
      (IntegrableOn F 𝓖 ν → IntegrableOn F 𝓕 μ) ∧ ∫ g in 𝓕, F g ∂μ = c * ∫ g in 𝓖, F g ∂ν := by
  obtain ⟨h1, h2, -, h4, h5, -, h7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  obtain ⟨a1, a2⟩ := hμ
  obtain ⟨b1, b2⟩ := hν
  have e := Measure.isMulLeftInvariant_eq_smul μ ν
  have hc := Measure.haarScalarFactor_pos_of_isHaarMeasure μ ν
  generalize μ.haarScalarFactor ν = c at e hc
  have b3 : IsFundamentalDomain (GQ V) 𝓖 μ := b2.mono (e ▸ Measure.smul_absolutelyContinuous)
  refine ⟨(c : ℝ), by exact_mod_cast hc.ne', fun F hF => ⟨fun hi => ?_, ?_⟩⟩
  · rw [a2.integrableOn_iff b3 fun γ y => hF γ.1 γ.2 y, e, IntegrableOn, Measure.restrict_smul]
    exact hi.smul_measure_nnreal
  · rw [a2.setIntegral_eq b3 fun γ y => hF γ.1 γ.2 y, e, Measure.restrict_smul, integral_smul_nnreal_measure]
    rfl

theorem vac_unique (ε : Bool) {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} (hS : S.gram = 1) (hT : T.gram = 1)
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    (cS : ∀ τ, IsCartanInv (gramAt D (sgn ε S) τ) (sS τ)) (cT : ∀ τ, IsCartanInv (gramAt D T τ) (sT τ))
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (dS : IsSelfDualC (sgn ε S) ΛS) (dT : IsSelfDualC T ΛT) {f f' : WO S T → ℂ}
    (h : IsVacO ψ θ (sgn ε S) T sS sT ΛS ΛT f) (h' : IsVacO ψ θ (sgn ε S) T sS sT ΛS ΛT f') :
    ∃ c : ℂ, ‖c‖ = 1 ∧ f' = c • f := by
  have k : ∀ V : HSp D, V.gram = 1 → HSpace.SigOK ({ V with sig := fun _ => (V.rank, 0) } : HSp D) := fun V hV φ => by
    refine GlobalTheory.Proof.GenusMassSignature.hasSignature_of_posDef (J := V.gram.map φ) ?_
    rw [hV, Matrix.map_one φ (map_zero φ) (map_one φ)]
    exact Matrix.PosDef.one
  let S₁ : HSp D := { S with sig := fun _ => (S.rank, 0) }
  let T₁ : HSp D := { T with sig := fun _ => (T.rank, 0) }
  have conv : ∀ g, IsVacO ψ θ (sgn ε S) T sS sT ΛS ΛT g → IsVacO ψ θ (sgn ε S₁) T₁ sS sT ΛS ΛT g := fun g hg =>
    ⟨hg.1, ⟨hg.2.inf, ⟨hg.2.theta.quasi, hg.2.theta.level, hg.2.theta.cont, hg.2.theta.smooth⟩, hg.2.lat, hg.2.fock,
      hg.2.norm⟩⟩
  exact GlobalTheory.VacUnique.vacUniqueO D ψ θ h.1 h.2.inf (sgn ε S₁) T₁ sS sT (GlobalTheory.Grid.sigOK_sgn ε (k S hS)) (k T hT) cS cT ΛS ΛT
    dS dT f f' (conv f h) (conv f' h')

theorem thetaAt_smul {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {e : AE D} {Λ : AddSubgroup (WO S T)} {c a : ℂ}
    {f₀ Φ f f' : WO S T → ℂ} (h : IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ c f₀ Φ f)
    (h' : IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ c (a • f₀) Φ f') : f' = a • f := by
  obtain ⟨⟨Tm, hT⟩, hall⟩ := h
  rw [hall Tm hT]
  exact h'.2 (a • Tm)
    { trans := fun Φ hΦ x hx => by
        rw [LinearMap.smul_apply, LinearMap.smul_apply, hT.trans Φ hΦ x hx, GlobalTheory.SeeSaw.Resc.heisO_smul]
      modul := fun Φ hΦ y hy => by
        rw [LinearMap.smul_apply, LinearMap.smul_apply, hT.modul Φ hΦ y hy, GlobalTheory.SeeSaw.Resc.heisO_smul]
      vac := by rw [LinearMap.smul_apply, hT.vac] }

theorem idemSum_unique (V : HSp D) {e e' : AE D} {P : Finset (Formalism.L2.DIV.Pl D.host.E)} (h : IsIdemSum e P)
    (h' : IsIdemSum e' P) : e' = e := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := h
  obtain ⟨⟨es', hes', rfl⟩, -⟩ := h'
  exact Finset.sum_congr rfl fun PP hPP =>
    (((GlobalTheory.IdemSupport.supported_group_and_prime_idempotents V).2.2.1 PP _ _ (Or.inl ⟨hes PP hPP, rfl⟩)).2.2.2.1 _ _
      (Or.inl ⟨hes' PP hPP, rfl⟩)).1

theorem thetaKO_left {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hom : IsWeilDatumO ψ S T χS χT om) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) {γ : GA D S} (hγ : γ ∈ GQ S) (g : GA D S) (h : GA D T) :
    thetaKO om (γ * g) h f = thetaKO om g h f := by
  have e : ((γ * g, h) : GA D S × GA D T) = (γ, 1) * (g, h) := by simp
  unfold thetaKO
  rw [e, map_mul, Module.End.mul_apply]
  exact hom.om_aut γ hγ 1 (one_mem _) _ (hom.om_pres _ _ hf)

variable {T : Type} {A A' WW : HSp D} {X Y : Tri T A A' WW} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}
  {α β : T → ((AE D)ˣ →* Circle)} {νH : T → HChar D.host.E} {S : T → Finset (Formalism.L2.DIV.Pl D.host.E)}

theorem e_ideal_eq (hX : X.Is ψ θ α β νH S) (hY : Y.Is ψ θ α β νH S) (t : T) :
    Y.e t = X.e t ∧ Y.ideal S t = X.ideal S t := by
  refine ⟨idemSum_unique A (hX.idem t) (hY.idem t), Finset.prod_congr rfl fun w hw => ?_⟩
  have a := hX.expo t w hw
  have b := hY.expo t w hw
  rw [le_antisymm ((b _).1 ((a _).2 le_rfl)) ((a _).1 ((b _).2 le_rfl))]

theorem ker_left (hX : X.Is ψ θ α β νH S) (t : T) (P h) : ∀ γ ∈ GQ A, ∀ g, X.ker ψ θ t P h (γ * g) = X.ker ψ θ t P h g :=
  fun γ hγ g => thetaKO_left (hX.weil t) (GlobalTheory.GalLift.Vec.theta_pureTensorO (S := neg A) hX.isVac.1 hX.isVac.2.inf _ _ _ _
    (GlobalTheory.GalLift.Vec.theta_of_thetaAt hX.isVac.1 hX.isVac.2.inf (hX.fst t) hX.isVac.2.theta) P)
    (γ := (ofSgn true A).symm γ) ((GlobalTheory.SgnIdent.mem_GQ_sgn true A _).2 hγ) ((ofSgn true A).symm g) h

theorem ker'_left (hX : X.Is ψ θ α β νH S) (t : T) (P h) : ∀ γ ∈ GQ A', ∀ g, X.ker' ψ θ t P h (γ * g) = X.ker' ψ θ t P h g :=
  fun γ hγ g => thetaKO_left (hX.weil' t) (GlobalTheory.GalLift.Vec.theta_pureTensorO hX.isVac.1 hX.isVac.2.inf _ _ _ _
    (GlobalTheory.GalLift.Vec.theta_of_thetaAt hX.isVac.1 hX.isVac.2.inf (hX.snd t) hX.isVac'.2.theta) P) hγ g h

set_option maxHeartbeats 1000000 in

theorem ker_eq (hX : X.Is ψ θ α β νH S) (hY : Y.Is ψ θ α β νH S) (sA : X.rA.IsStd) (sW : X.rW.IsStd)
    (l1 : Y.rA.Λ = X.rA.Λ) (l3 : Y.rW.Λ = X.rW.Λ) (b1 : Y.rA.β = X.rA.β) (b3 : Y.rW.β = X.rW.β) :
    ∃ a : ℂ, a ≠ 0 ∧ ∀ P, ∃ Q, ∀ t h g, Y.ker ψ θ t P h g = a * X.ker ψ θ t Q h g := by
  have hψ := hX.isVac.1
  have hθ := hX.isVac.2.inf
  have x1 := rigging_cartan_eq_one_of_gram_one sA.1 hX.rigA
  have x3 := rigging_cartan_eq_one_of_gram_one sW.1 hX.rigW
  have y1 := rigging_cartan_eq_one_of_gram_one sA.1 hY.rigA
  have y3 := rigging_cartan_eq_one_of_gram_one sW.1 hY.rigW
  have hv := hY.isVac
  rw [l1, l3, y1, y3, ← x1, ← x3] at hv
  obtain ⟨a, ha, e⟩ := vac_unique true sA.1 sW.1 (sS := fun τ => -X.rA.s τ)
    (fun τ => GlobalTheory.Grid.isCartanInv_sgn true A τ (hX.rigA.2.2 τ).1) (fun τ => (hX.rigW.2.2 τ).1)
    (GlobalTheory.ChiGrid.isSelfDualC_neg hX.rigA.1) hX.rigW.1 hX.isVac hv
  refine ⟨a, fun h0 => by simp [h0] at ha, fun P => ⟨GlobalTheory.CompactHowe.substF (fun τ => (Y.rW.B τ).map (starRingEnd ℂ))
    (fun τ => (((Y.rA.B τ)⁻¹)ᵀ).map (starRingEnd ℂ)) P, fun t h g => ?_⟩⟩
  have hf := hY.fst t
  rw [(e_ideal_eq hX hY t).1, (e_ideal_eq hX hY t).2, l1, l3, b1, b3, e] at hf
  have ef : Y.f t = a • X.f t := thetaAt_smul (S := neg A) (hX.fst t) hf
  have tX := GlobalTheory.GalLift.Vec.theta_of_thetaAt hψ hθ (hX.fst t) hX.isVac.2.theta
  have key := GlobalTheory.FockNegSubst.pureTensorO_negSp_subst D ψ θ A WW hψ hθ (fun _ => 1) Y.rA.B (fun _ => 1) Y.rW.B _ tX P
  simp only [Matrix.one_mul] at key
  have key' : pureTensorO ψ θ (neg A) WW (fun τ => -Y.rA.s τ) Y.rW.s Y.rA.B Y.rW.B (X.f t) P =
      pureTensorO ψ θ (neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t)
        (GlobalTheory.CompactHowe.substF (fun τ => (Y.rW.B τ).map (starRingEnd ℂ))
          (fun τ => (((Y.rA.B τ)⁻¹)ᵀ).map (starRingEnd ℂ)) P) := by
    rw [x1, x3, y1, y3, show X.rA.B = fun _ => 1 from funext fun τ => (sA.2.2 τ).2,
      show X.rW.B = fun _ => 1 from funext fun τ => (sW.2.2 τ).2]
    exact key
  unfold Tri.ker thetaKO
  rw [ef, GlobalTheory.SeeSaw.Resc.pureTensorO_smul ψ θ (neg A) WW, LinearMap.smul_apply, key', map_smul, Pi.smul_apply, smul_eq_mul]
  congr 1
  exact congrFun (GlobalTheory.WeilUniq.weilDatum_unique D ψ hψ (neg A) WW _ _ _ _ (hY.weil t) (hX.weil t)
    ((ofSgn true A).symm g, h) _ (GlobalTheory.GalLift.Vec.theta_pureTensorO (S := neg A) hψ hθ _ _ _ _ tX _)) 0

set_option maxHeartbeats 1000000 in

theorem ker'_eq (hX : X.Is ψ θ α β νH S) (hY : Y.Is ψ θ α β νH S) (sA : X.rA'.IsStd) (sW : X.rW.IsStd)
    (l1 : Y.rA'.Λ = X.rA'.Λ) (l3 : Y.rW.Λ = X.rW.Λ) (b1 : Y.rA'.β = X.rA'.β) (b3 : Y.rW.β = X.rW.β) :
    ∃ a : ℂ, a ≠ 0 ∧ ∀ P, ∃ Q, ∀ t h g, Y.ker' ψ θ t P h g = a * X.ker' ψ θ t Q h g := by
  have hψ := hX.isVac.1
  have hθ := hX.isVac.2.inf
  have x1 := rigging_cartan_eq_one_of_gram_one sA.1 hX.rigA'
  have x3 := rigging_cartan_eq_one_of_gram_one sW.1 hX.rigW
  have y1 := rigging_cartan_eq_one_of_gram_one sA.1 hY.rigA'
  have y3 := rigging_cartan_eq_one_of_gram_one sW.1 hY.rigW
  have hv := hY.isVac'
  rw [l1, l3, y1, y3, ← x1, ← x3] at hv
  obtain ⟨a, ha, e⟩ := vac_unique false sA.1 sW.1 (fun τ => (hX.rigA'.2.2 τ).1) (fun τ => (hX.rigW.2.2 τ).1)
    hX.rigA'.1 hX.rigW.1 hX.isVac' hv
  refine ⟨a, fun h0 => by simp [h0] at ha, fun P => ⟨GlobalTheory.CompactHowe.substF Y.rW.B
    (fun τ => ((Y.rA'.B τ)⁻¹)ᵀ) P, fun t h g => ?_⟩⟩
  have hf := hY.snd t
  rw [(e_ideal_eq hX hY t).1, (e_ideal_eq hX hY t).2, l1, l3, b1, b3, e] at hf
  have ef : Y.f' t = a • X.f' t := thetaAt_smul (hX.snd t) hf
  have tX := GlobalTheory.GalLift.Vec.theta_of_thetaAt hψ hθ (hX.snd t) hX.isVac'.2.theta
  have key := GlobalTheory.FockBaseChange.pureTensorO_subst D ψ θ A' WW hψ hθ (fun _ => 1) Y.rA'.B (fun _ => 1) Y.rW.B _ tX P
  simp only [Matrix.one_mul] at key
  have key' : pureTensorO ψ θ A' WW Y.rA'.s Y.rW.s Y.rA'.B Y.rW.B (X.f' t) P =
      pureTensorO ψ θ A' WW X.rA'.s X.rW.s X.rA'.B X.rW.B (X.f' t)
        (GlobalTheory.CompactHowe.substF Y.rW.B (fun τ => ((Y.rA'.B τ)⁻¹)ᵀ) P) := by
    rw [x1, x3, y1, y3, show X.rA'.B = fun _ => 1 from funext fun τ => (sA.2.2 τ).2,
      show X.rW.B = fun _ => 1 from funext fun τ => (sW.2.2 τ).2]
    exact key
  unfold Tri.ker' thetaKO
  rw [ef, GlobalTheory.SeeSaw.Resc.pureTensorO_smul ψ θ A' WW, LinearMap.smul_apply, key', map_smul, Pi.smul_apply, smul_eq_mul]
  congr 1
  exact congrFun (GlobalTheory.WeilUniq.weilDatum_unique D ψ hψ A' WW _ _ _ _ (hY.weil' t) (hX.weil' t)
    (g, h) _ (GlobalTheory.GalLift.Vec.theta_pureTensorO hψ hθ _ _ _ _ tX _)) 0

end GlobalTheory.SqTower.Normal

namespace GlobalTheory.SqTower

open MeasureTheory GlobalTheory.SqTower.Normal

theorem bottom_const_normal : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData Lc sc} (W : G.Weil) (i j : Fin D.R.m) {A A' WW : HSp D} (X Y : Tri T A A' WW),
  IsBottomTri W i j X → GlobalTheory.SqTower.IsStageC W i j 0 0 Y →
  Y.rA.Λ = X.rA.Λ → Y.rA'.Λ = X.rA'.Λ → Y.rW.Λ = X.rW.Λ → Y.rA.β = X.rA.β → Y.rA'.β = X.rA'.β → Y.rW.β = X.rW.β →
  ∀ c : T → ℂ, Y.IsConst W.ψ W.θ c → ∃ κ : ℂ, κ ≠ 0 ∧ X.IsConst W.ψ W.θ (fun t => κ * c t) := by
  intro D T Lc sc G W i j A A' WW X Y hB hS l1 l2 l3 b1 b2 b3 c hc
  have hX := hB.is
  have hY := hS.2.2.2.2.2.2.2
  obtain ⟨a, ha, k1⟩ := ker_eq hX hY hB.std hB.stdW l1 l3 b1 b3
  obtain ⟨a', ha', k2⟩ := ker'_eq hX hY hB.std' hB.stdW l2 l3 b2 b3
  obtain ⟨m, hm, m1⟩ := exists_haar_factor A hX.meas hY.meas
  obtain ⟨m', hm', m2⟩ := exists_haar_factor A' hX.meas' hY.meas'
  obtain ⟨⟨t₀, ht₀⟩, P, P', H⟩ := hc
  obtain ⟨Q, hQ⟩ := k1 P
  obtain ⟨Q', hQ'⟩ := k2 P'
  have e1 : ∀ t h, X.ker W.ψ W.θ t Q h = fun g => a⁻¹ * Y.ker W.ψ W.θ t P h g := fun t h => funext fun g => by
    rw [hQ, inv_mul_cancel_left₀ ha]
  have e2 : ∀ t h, X.ker' W.ψ W.θ t Q' h = fun g => a'⁻¹ * Y.ker' W.ψ W.θ t P' h g := fun t h => funext fun g => by
    rw [hQ', inv_mul_cancel_left₀ ha']
  have i1 : ∀ t h, X.I W.ψ W.θ t Q h = m * a⁻¹ * Y.I W.ψ W.θ t P h := fun t h => by
    rw [Tri.I, (m1 _ (ker_left hX t Q h)).2, e1, integral_const_mul, mul_assoc]; rfl
  have i2 : ∀ t h, X.I' W.ψ W.θ t Q' h = m' * a'⁻¹ * Y.I' W.ψ W.θ t P' h := fun t h => by
    rw [Tri.I', (m2 _ (ker'_left hX t Q' h)).2, e2, integral_const_mul, mul_assoc]; rfl
  have n1 : m * a⁻¹ ≠ 0 := mul_ne_zero hm (inv_ne_zero ha)
  have n2 : m' * a'⁻¹ ≠ 0 := mul_ne_zero hm' (inv_ne_zero ha')
  refine ⟨m * a⁻¹ / (m' * a'⁻¹), div_ne_zero n1 n2, ⟨t₀, mul_ne_zero (div_ne_zero n1 n2) ht₀⟩, Q, Q', fun t =>
    ⟨fun h => ⟨(m1 _ (ker_left hX t Q h)).1 ?_, (m2 _ (ker'_left hX t Q' h)).1 ?_⟩, ?_, fun h => ?_⟩⟩
  · rw [e1]; exact ((H t).1 h).1.const_mul _
  · rw [e2]; exact ((H t).1 h).2.const_mul _
  · obtain ⟨h, hh⟩ := (H t).2.1
    exact ⟨h, by rw [i2]; exact mul_ne_zero n2 hh⟩
  · rw [i1, i2, (H t).2.2 h]
    generalize m * a⁻¹ = u
    generalize m' * a'⁻¹ = v at n2
    field_simp

end GlobalTheory.SqTower

end
