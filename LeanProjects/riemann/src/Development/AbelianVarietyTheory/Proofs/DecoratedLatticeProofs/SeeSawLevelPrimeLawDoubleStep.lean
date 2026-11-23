import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DataAsCombinationsAtSplitPlacesProofStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.VacuumChangeAtSplitPlacesProofStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticePrescribedFinitelyManySplitPlacesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtensionByZeroAtSplitPlacesProofStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContractionOfVacuumCombinationsProofStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BiVacuumOperatorZeroOrLeftInvertibleStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleStepSmallPairsValueAllGluedSplitPlacesProoStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapPreservesVacuumProofStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleStepEqTwoThetaColumnLiftsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselThetaContractionExtendByZeroVacuumSmoothStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BilinearVacuumCentralCharacter
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RamifiedOperatorsBijectiveAtPlacesStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel IsLocalRing GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevPrimeMid

variable {D : D7}

theorem mxAt_mul_right (P : Pl D → Prop) {m n r : ℕ} {x : Mx D m n} (hx : MxAt P x) (M : Matrix (Fin n) (Fin r) (AE D)) :
    MxAt P (x * M) := fun i j => by
  rw [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_right _ _ (hx i l)

theorem mxAt_mul_left (P : Pl D → Prop) {m n r : ℕ} {x : Mx D n r} (hx : MxAt P x) (M : Matrix (Fin m) (Fin n) (AE D)) :
    MxAt P (M * x) := fun i j => by
  rw [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (hx l j)

theorem combAt_extS (P : Pl D → Prop) {S A L : HSp D} (o : OrthDec S A L) (T : HSp D) {c : WO A T →₀ ℂ}
    (hc : CombAt P c) : CombAt P (extS o T c) := by
  intro u hu
  classical
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hu)
  intro i j
  change (w ⬝ o.pA + (0 : WO L T) ⬝ o.pB) i j ∈ idAt D P
  rw [Matrix.zero_mul, add_zero]
  exact mxAt_mul_right P (hc w hw) _ i j

theorem combAt_extT (P : Pl D → Prop) {T A L : HSp D} (o : OrthDec T A L) (S : HSp D) {c : WO S A →₀ ℂ}
    (hc : CombAt P c) : CombAt P (extT o S c) := by
  intro u hu
  classical
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hu)
  intro i j
  change (o.jA ⬝ w + o.jB ⬝ (0 : WO S L)) i j ∈ idAt D P
  rw [Matrix.mul_zero, add_zero]
  exact mxAt_mul_left P (hc w hw) _ i j

theorem isFinComb_of_combAt (P : Pl D → Prop) {S T : HSp D} {c : WO S T →₀ ℂ} (hc : CombAt P c) : IsFinComb c := by
  intro u hu
  ext i j
  exact (RingHom.mem_ker).1 (Ideal.mem_inf.1 (hc u hu i j)).1

theorem places_of_preT {c : Comm D} {v : VCom c} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {ι : Type} {o : TDat c k ι} (H : PreT v o) : Places o.p o.I (· ∈ v.tP) :=
  ⟨H.nodup, H.all, H.inj, fun x => H.tP x, fun i => (H.char i).2⟩

theorem heisO_zero (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (u : WO S T) : heisO ψ S T u (fun _ => 0) = fun _ => 0 := by
  funext w
  simp [heisO]

theorem vac_zero (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (LS : Lat S) (LT : Lat T) (P : Pl D → Prop) :
    Vac ψ S T LS LT P (fun _ => 0) :=
  ⟨GlobalTheory.OrientedHeis.theta_zero, fun u _ => heisO_zero ψ S T _, fun _ _ u _ _ => heisO_zero ψ S T u⟩

theorem biVacAt_zero (ψ : AddChar (AF D.host.F) ℂ) {A S A' : HSp D} (LA : Lat A) (LS : Lat S) (LA' : Lat A')
    (P : Pl D → Prop) : BiVacAt ψ LA LS LA' P (fun _ _ => 0) :=
  ⟨fun _ => vac_zero ψ A S LA LS P, fun _ => vac_zero ψ S A' LS LA' P⟩

theorem comb_zero (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (c : WO S T →₀ ℂ) : comb ψ S T c (fun _ => 0) = fun _ => 0 := by
  funext w
  simp [comb, heisO_zero]

theorem biComb_zero (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D) (c : WO A S →₀ ℂ) (c' : WO S A' →₀ ℂ) :
    biComb ψ A S A' c c' (fun _ _ => 0) = fun _ _ => 0 := by
  funext u v
  simp only [biComb, comb_zero]

theorem biLift_zero {A S A' : HSp D} (oma : Om A S) (omb : Om S A') (vA : Vol A) (vS : Vol S) (φ : GA D A → ℂ) :
    biLift oma omb vA vS φ (fun _ _ => 0) = 0 := by
  funext h₂
  simp only [biLift]
  have e1 : ∀ h₀ h₁, (fun v : WO S A' => oma (h₀, h₁) (fun _ => 0) 0) = 0 := fun h₀ h₁ => by
    funext v; exact congrFun (map_zero (oma (h₀, h₁))) 0
  simp only [e1, map_zero, Pi.zero_apply, mul_zero, MeasureTheory.integral_zero]

end GlobalTheory.LevPrimeMid

namespace GlobalTheory.LevPrimeMid

variable {D : D7}

theorem bl_contr (hCL : ContrLaw D) {c : Comm D} (v : VCom c) (t : Tup c) (hW : WeilOK (t := t) v) {j σ : ℕ}
    (h : j + 2 * (σ + 1) + 2 = D.R.m) {φ : GA D (c.X j) → ℂ} (hφ : IsContAut (c.X j) φ)
    {Ξ₁ : WO (c.B j (σ + 1) h).V₀ (c.X (j + 1)) → ℂ} {Ξ₂ : WO (c.X (j + 1)) (c.B (j + 1 + 1) σ (idx_step h)).V₀ → ℂ}
    (h₁ : IsThetaFunO c.ψ _ _ Ξ₁) (h₂ : IsThetaFunO c.ψ _ _ Ξ₂) :
    c.bl j (t.kom j) (t.kom (j + 1)) φ (GlobalTheory.Unf.contr (c.lnk j σ h) (c.X (j + 1)) (c.vL j σ h) Ξ₁ Ξ₂) =
      hand0 (t.sBF j (σ + 1) h) (t.sFB j σ h) (c.lnk j σ h) (c.vL j σ h) φ Ξ₁ Ξ₂ := by
  obtain ⟨χA, χA', χz, omz, omz', e1, e2, w1, w2, w3, w4⟩ := hW.mid j σ h
  funext g
  have := (hCL c.ψ σ _ _ _ (t.sBF j (σ + 1) h) (t.sFB j σ h) (c.lnk j σ h) (c.vL j σ h) χA χA' χz (t.kom j) omz
    (t.kom (j + 1)) omz' e1 e2 w1 w2 w3 w4 φ Ξ₁ Ξ₂ hφ h₁ h₂).2.2 g
  rw [hand0, this]
  rfl

end GlobalTheory.LevPrimeMid

namespace GlobalTheory.LevPrimeMid

variable {D : D7}

theorem lastKer_isLattice {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : Type}
    (q : Unif k) (L : Submodule 𝒪[k] (n → k)) [L.IsLattice k] : (lastKer L).IsLattice k := by
  rw [GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.lastKer_eq q]
  exact gluedLat_isLattice q 1 2 L 0

end GlobalTheory.LevPrimeMid

namespace GlobalTheory.LevPrimeMid

theorem lawLevelPrime_double : ∀ (D : D7) (c : Comm D) (v : VCom c) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (o : TDat c k ι), c.Is → v.Is → ShapeOff v o → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m), ∃ (ε : ι → 𝓀[k]ˣ) (op : BiOp (c.X j) (c.X (j + 1)) (c.X (j + 1 + 1))) (r : ι → ℝ) (e : ι → ℤ), (∀ i, 0 < r i) ∧ OpAt (· ∈ v.tP) op ∧ ∀ t : Tup c, t.Is → WeilOK (t := t) v → t.UnrOn (· ∈ v.tP) → ∀ Ψ₁ Ψ₂, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ v.tP) Ψ₁ → Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (· ∈ v.tP) Ψ₂ → BiVacAt c.ψ (c.x j).L (c.x (j + 1)).L (c.x (j + 1 + 1)).L (· ∈ v.tP) (op.app c.ψ (c.ctr j σ h (t.sBF j (σ + 1) h) (t.sFB j σ h) Ψ₁ Ψ₂)) ∧ ∀ d d', CombAt (· ∉ v.tP) d → CombAt (· ∉ v.tP) d' → ∀ φ ∈ o.Ram j, c.bl j (t.kom j) (t.kom (j + 1)) φ (biComb c.ψ _ _ _ d d' (c.ctr j σ h (t.sBF j (σ + 1) h) (t.sFB j σ h) Ψ₁ Ψ₂)) = o.mono r e (t.sBF j (σ + 1) h).χW • c.bl j (t.kom j) (t.kom (j + 1)) (o.S (fun _ => ε) j φ) (biComb c.ψ _ _ _ d d' (biComb c.ψ _ _ _ (v.dT j) (v.dT (j + 1)) (op.app c.ψ (c.ctr j σ h (t.sBF j (σ + 1) h) (t.sFB j σ h) Ψ₁ Ψ₂)))) := by
  intro D c v k _ _ _ _ ι o hc hv hS j σ h
  have hPl := places_of_preT hS.pre
  obtain ⟨x₀⟩ := Formalism.L2.Col.nonempty_places D.host.F
  have hstd := hc.std
  have sd0 : IsSelfDualC _ (c.x j).L := (hc.x j (by omega)).sd
  have sd1 : IsSelfDualC _ (c.x (j + 1)).L := (hc.x (j + 1) (by omega)).sd
  have sd2 : IsSelfDualC _ (c.x (j + 1 + 1)).L := (hc.x (j + 1 + 1) (by omega)).sd
  have sdG : IsSelfDualC _ (o.M j (σ + 1) h) := ((hS.good x₀).bf j (σ + 1) h).sdV₀
  have sdG' : IsSelfDualC _ (o.M (j + 1 + 1) σ (idx_step h)) := ((hS.good x₀).fb j σ h).sdW₀
  obtain ⟨M0, sdM0, latM0, -⟩ := GlobalTheory.T.selfDualLattice_prescribed_finitelyManySplitPlaces D k ι o.p o.I _ hPl _ _ (o.β₀ j (σ + 1) h) (o.M j (σ + 1) h) sdG
    (fun i => lastKer (o.Q j i).lat) (fun i => lastKer_isLattice o.q _)
  obtain ⟨M0', sdM0', latM0', -⟩ := GlobalTheory.T.selfDualLattice_prescribed_finitelyManySplitPlaces D k ι o.p o.I _ hPl _ _ (o.β₀ (j + 1 + 1) σ (idx_step h))
    (o.M (j + 1 + 1) σ (idx_step h)) sdG' (fun i => lastKer (o.Q (j + 1 + 1) i).lat) (fun i => lastKer_isLattice o.q _)
  obtain ⟨e1, e1', he1, he1', hR1⟩ := GlobalTheory.T.vacuumChangeAtSplitPlaces_proof D k ι o.p o.I _ hPl (Fin (c.X (j + 1)).rank) (Fin (c.X j).rank ⊕ Fin 1)
    c.ψ hstd _ _ (o.β₀ j (σ + 1) h) (o.β (j + 1)) (o.M j (σ + 1) h) M0 (c.x (j + 1)).L (c.x (j + 1)).L sdG sd1 sdM0 sd1
  obtain ⟨e2, e2', he2, he2', hR2⟩ := GlobalTheory.T.vacuumChangeAtSplitPlaces_proof D k ι o.p o.I _ hPl (Fin (c.X (j + 1 + 1)).rank ⊕ Fin 1)
    (Fin (c.X (j + 1)).rank) c.ψ hstd _ _ (o.β (j + 1)) (o.β₀ (j + 1 + 1) σ (idx_step h)) (c.x (j + 1)).L (c.x (j + 1)).L
    (o.M (j + 1 + 1) σ (idx_step h)) M0' sd1 sdG' sd1 sdM0'

  have hext1 := GlobalTheory.T.extensionByZeroAtSplitPlaces_proof D k ι o.p o.I _ hPl (Fin (c.X (j + 1)).rank) (Fin (c.X j).rank) c.ψ hstd
    (c.bes j (σ + 1) h).V₀ (c.X j) (c.bes j (σ + 1) h).L (c.X (j + 1)) (c.bes j (σ + 1) h).o (c.bes j (σ + 1) h).ζ
    (c.bes j (σ + 1) h).line (o.β j) (o.β₀ j (σ + 1) h) (o.β (j + 1)) (fun i => (hS.glued j (σ + 1) h i).sum)
    (c.x j).L M0 (c.x (j + 1)).L (fun i => (o.Q j i).lat) (fun i => (o.Q (j + 1) i).lat) sd0 sdM0 sd1
    (fun i => ⟨hS.pre.latT j (by omega) i, latM0 i, hS.pre.latT (j + 1) (by omega) i⟩)
  have hext2 := GlobalTheory.T.extensionByZeroAtSplitPlaces_proof D k ι o.p o.I _ hPl (Fin (c.X (j + 1)).rank) (Fin (c.X (j + 1 + 1)).rank) c.ψ hstd
    (c.bes (j + 1 + 1) σ (idx_step h)).V₀ (c.X (j + 1 + 1)) (c.bes (j + 1 + 1) σ (idx_step h)).L (c.X (j + 1))
    (c.bes (j + 1 + 1) σ (idx_step h)).o (c.bes (j + 1 + 1) σ (idx_step h)).ζ (c.bes (j + 1 + 1) σ (idx_step h)).line
    (o.β (j + 1 + 1)) (o.β₀ (j + 1 + 1) σ (idx_step h)) (o.β (j + 1)) (fun i => (hS.glued (j + 1 + 1) σ (idx_step h) i).sum)
    (c.x (j + 1 + 1)).L M0' (c.x (j + 1)).L (fun i => (o.Q (j + 1 + 1) i).lat) (fun i => (o.Q (j + 1) i).lat) sd2 sdM0' sd1
    (fun i => ⟨hS.pre.latT (j + 1 + 1) (by omega) i, latM0' i, hS.pre.latT (j + 1) (by omega) i⟩)
  have hrep1 : Reps c.ψ (o.β j) (o.β (j + 1)) (c.x j).L (c.x (j + 1)).L (fun i => phiOne (o.Q j i) (o.Q (j + 1) i)) o.I
      (· ∈ v.tP) (v.dT j) := ⟨(hv.atT j).1, hS.rep j (by omega)⟩
  have hrep2 : Reps c.ψ (o.β (j + 1)) (o.β (j + 1 + 1)) (c.x (j + 1)).L (c.x (j + 1 + 1)).L
      (fun i => phiOne (o.Q (j + 1) i) (o.Q (j + 1 + 1) i)) o.I (· ∈ v.tP) (v.dT (j + 1)) :=
    ⟨(hv.atT (j + 1)).1, hS.rep (j + 1) (by omega)⟩
  have hX1 := hext1.2.1 _ _ hrep1
  have hX2 := hext2.2.2 _ _ hrep2
  obtain ⟨op0, hop0, hC⟩ := GlobalTheory.T.contractionOfVacuumCombinations_proof D k ι o.p o.I _ hPl (Fin (c.X j).rank) (Fin (c.X (j + 1 + 1)).rank) c.ψ hstd
    (σ + 1) σ (c.B j (σ + 1) h) (c.B (j + 1 + 1) σ (idx_step h)) (c.lnk j σ h) (c.X (j + 1)) (c.vL j σ h) (o.β j)
    (o.β₀ j (σ + 1) h) (o.β (j + 1 + 1)) (o.β₀ (j + 1 + 1) σ (idx_step h)) M0 (c.x (j + 1)).L M0'
    (fun i => (o.Q j i).lat) (fun i => (o.Q (j + 1 + 1) i).lat) sdM0 sd1 sdM0'
    (fun i => ⟨(hS.glued j (σ + 1) h i).sum, (hS.glued (j + 1 + 1) σ (idx_step h) i).sum, latM0 i, latM0' i⟩) e1' e2' he1' he2'
  have hInv := (GlobalTheory.T.biVacuumOperator_zero_or_left_invertible D k ι o.p o.I _ hPl c.ψ hstd _ _ _ op0 hop0).1 (c.x j).L (c.x (j + 1)).L (c.x (j + 1 + 1)).L
    sd0 sd1 sd2
  obtain ⟨ε, -, hV⟩ := GlobalTheory.T.doubleStepSmallPairsValueAllGluedSplitPlaces_proof D k ι o.p o.I _ hPl o.q c.ψ o.χ o.hχ (fun i => (hS.pre.char i).1)
  obtain ⟨r, e, hr, hVE⟩ := hV (Fin (c.X (j + 1)).rank) (Fin (c.X j).rank) (Fin (c.X (j + 1 + 1)).rank)

  let a : PairDat o.p (c.B j (σ + 1) h).A (c.B j (σ + 1) h).V₀ (Fin (c.X j).rank) := ⟨o.β j, o.β₀ j (σ + 1) h, o.Q j⟩
  let b : MidDat o.p (c.J j (σ + 1) h).W₀ (Fin (c.X (j + 1)).rank) := ⟨o.β (j + 1), o.Q (j + 1)⟩
  let a' : PairDat o.p (c.B (j + 1 + 1) σ (idx_step h)).A (c.B (j + 1 + 1) σ (idx_step h)).V₀ (Fin (c.X (j + 1 + 1)).rank) :=
    ⟨o.β (j + 1 + 1), o.β₀ (j + 1 + 1) σ (idx_step h), o.Q (j + 1 + 1)⟩
  have hcore : ∀ i, GluedCore (c.B j (σ + 1) h) (o.M j (σ + 1) h) o.q (a.α i) (a.α₀ i) (a.P i) ∧
      GluedCore (c.B (j + 1 + 1) σ (idx_step h)) (o.M (j + 1 + 1) σ (idx_step h)) o.q (a'.α i) (a'.α₀ i) (a'.P i) ∧
      (b.β i).IsLat (c.x (j + 1)).L (b.Q i).lat := fun i =>
    ⟨hS.glued j (σ + 1) h i, hS.glued (j + 1 + 1) σ (idx_step h) i, hS.pre.latT (j + 1) (by omega) i⟩
  have hOrth : ∀ x, x ∈ v.tP → (∃ LL, OrthAt (c.B j (σ + 1) h).o M0 (c.x j).L LL x) ∧
      ∃ LL, OrthAt (c.B (j + 1 + 1) σ (idx_step h)).o M0' (c.x (j + 1 + 1)).L LL x := fun x hx => ⟨hext1.1 x hx, hext2.1 x hx⟩

  have key : ∀ t : Tup c, ∀ Ψ₁ Ψ₂, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ v.tP) Ψ₁ →
      Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (· ∈ v.tP) Ψ₂ →
      ∃ f₁ f₂, Vac c.ψ _ _ (o.M j (σ + 1) h) (c.x (j + 1)).L (· ∈ v.tP) (flatBF (t.sBF j (σ + 1) h) Ψ₁) ∧
        Vac c.ψ _ _ (c.x (j + 1)).L (o.M (j + 1 + 1) σ (idx_step h)) (· ∈ v.tP) (flatFB (t.sFB j σ h) Ψ₂) ∧
        Vac c.ψ _ _ M0 (c.x (j + 1)).L (· ∈ v.tP) f₁ ∧ Vac c.ψ _ _ (c.x (j + 1)).L M0' (· ∈ v.tP) f₂ ∧
        c.ctr j σ h (t.sBF j (σ + 1) h) (t.sFB j σ h) Ψ₁ Ψ₂ = op0.app c.ψ (GlobalTheory.Unf.contr (B := c.B j (σ + 1) h) (B' := c.B (j + 1 + 1) σ (idx_step h)) (c.lnk j σ h) (c.X (j + 1)) (c.vL j σ h) f₁ f₂) ∧
        BiVacAt c.ψ (c.x j).L (c.x (j + 1)).L (c.x (j + 1 + 1)).L (· ∈ v.tP)
          (GlobalTheory.Unf.contr (B := c.B j (σ + 1) h) (B' := c.B (j + 1 + 1) σ (idx_step h)) (c.lnk j σ h) (c.X (j + 1)) (c.vL j σ h) f₁ f₂) ∧
        OverAll c.ψ a.α₀ b.β (o.M j (σ + 1) h) (c.x (j + 1)).L
          (fun i => tensCol (phiOne (a.P i) (b.Q i)) (vecInd (b.Q i).lat)) o.I
          (flatBF (t.sBF j (σ + 1) h) Ψ₁) (comb c.ψ _ _ (extS (c.bes j (σ + 1) h).o (c.X (j + 1)) (v.dT j)) f₁) ∧
        OverAll c.ψ b.β a'.α₀ (c.x (j + 1)).L (o.M (j + 1 + 1) σ (idx_step h))
          (fun i => tensRow (phiOne (b.Q i) (a'.P i)) (dualInd (b.Q i).lat)) o.I
          (flatFB (t.sFB j σ h) Ψ₂) (comb c.ψ _ _ (extT (c.bes (j + 1 + 1) σ (idx_step h)).o (c.X (j + 1)) (v.dT (j + 1))) f₂) := by
    intro t Ψ₁ Ψ₂ hΨ₁ hΨ₂
    have hF := GlobalTheory.T.flatMapPreservesVacuum_proof D c.ψ (· ∈ v.tP)
    have hXi1 := hF.1 (σ + 1) (c.B j (σ + 1) h) (c.J j (σ + 1) h) (t.sBF j (σ + 1) h) (v.N j) (o.M j (σ + 1) h) (v.N (j + 1))
      (c.x (j + 1)).L (fun x _ => (hS.good x).bf j (σ + 1) h) Ψ₁ hΨ₁
    have hXi2 := hF.2.1 σ (c.J j (σ + 1) h) (c.B (j + 1 + 1) σ (idx_step h)) (t.sFB j σ h) (v.N (j + 1)) (c.x (j + 1)).L
      (v.N (j + 1 + 1)) (o.M (j + 1 + 1) σ (idx_step h)) (fun x _ => (hS.good x).fb j σ h) Ψ₂ hΨ₂
    obtain ⟨hf1, hinv1, hov1⟩ := hR1 _ hXi1
    obtain ⟨hf2, hinv2, hov2⟩ := hR2 _ hXi2
    refine ⟨_, _, hXi1, hXi2, hf1, hf2, ?_, ?_, ?_, ?_⟩
    · have := hC _ _ hf1 hf2
      rw [hinv1, hinv2] at this
      exact this
    · exact (GlobalTheory.T.besselThetaContraction_extendByZero_vacuum_smooth D c.ψ hstd (σ + 1) σ (c.B j (σ + 1) h) (c.B (j + 1 + 1) σ (idx_step h)) (c.lnk j σ h) (c.X (j + 1))
        (c.vL j σ h) _ _ hf1.1 hf2.1).2.2 (· ∈ v.tP) (c.x j).L (c.x (j + 1)).L (c.x (j + 1 + 1)).L M0 M0' sd0 sd1 sd2 sdM0 sdM0'
        hOrth hf1 hf2
    · exact (hov1 _ _).2 (hX1.2 _ hf1)
    · exact (hov2 _ _).2 (hX2.2 _ hf2)

  have hCL : ContrLaw D := GlobalTheory.T.doubleStep_eq_two_thetaColumnLifts D
  have hCC := GlobalTheory.T.besselThetaContraction_extendByZero_vacuum_smooth D c.ψ hstd (σ + 1) σ (c.B j (σ + 1) h) (c.B (j + 1 + 1) σ (idx_step h)) (c.lnk j σ h) (c.X (j + 1))
    (c.vL j σ h)
  rcases hInv with hz | ⟨op', hop', hinv⟩
  ·
    have happ : ∀ C, BiOp.app c.ψ (⟨0, Fin.elim0, Fin.elim0⟩ : BiOp (c.X j) (c.X (j + 1)) (c.X (j + 1 + 1))) C = fun _ _ => 0 :=
      fun C => by funext u w; simp [BiOp.app]
    refine ⟨ε, ⟨0, Fin.elim0, Fin.elim0⟩, r, e, hr, fun i => i.elim0, ?_⟩
    intro t _ _ _ Ψ₁ Ψ₂ hΨ₁ hΨ₂
    obtain ⟨f₁, f₂, -, -, -, -, hctr, hC0, -, -⟩ := key t Ψ₁ Ψ₂ hΨ₁ hΨ₂
    have h0 : c.ctr j σ h (t.sBF j (σ + 1) h) (t.sFB j σ h) Ψ₁ Ψ₂ = fun _ _ => 0 := by rw [hctr, hz _ hC0]; rfl
    refine ⟨by rw [happ]; exact biVacAt_zero _ _ _ _ _, fun d d' _ _ φ _ => ?_⟩
    rw [h0, happ, biComb_zero, biComb_zero, biComb_zero]
    simp only [Comm.bl, biLift_zero, smul_zero]
  · refine ⟨ε, op', r, e, hr, hop', ?_⟩
    intro t _ hW hU Ψ₁ Ψ₂ hΨ₁ hΨ₂
    obtain ⟨f₁, f₂, hXi1, hXi2, hf₁, hf₂, hctr, hC0, hov1, hov2⟩ := key t Ψ₁ Ψ₂ hΨ₁ hΨ₂
    have hback : op'.app c.ψ (c.ctr j σ h (t.sBF j (σ + 1) h) (t.sFB j σ h) Ψ₁ Ψ₂) = (GlobalTheory.Unf.contr (B := c.B j (σ + 1) h) (B' := c.B (j + 1 + 1) σ (idx_step h)) (c.lnk j σ h) (c.X (j + 1)) (c.vL j σ h) f₁ f₂) := by
      rw [hctr]; exact hinv _ hC0
    refine ⟨by rw [hback]; exact hC0, fun d d' hd hd' φ hφ => ?_⟩
    rw [hback]
    have hD1 := combAt_extS (fun x => x ∉ v.tP) (c.bes j (σ + 1) h).o (c.X (j + 1)) hd
    have hD2 := combAt_extT (fun x => x ∉ v.tP) (c.bes (j + 1 + 1) σ (idx_step h)).o (c.X (j + 1)) hd'
    have hT1 := combAt_extS (· ∈ v.tP) (c.bes j (σ + 1) h).o (c.X (j + 1)) (hv.atT j).1
    have hT2 := combAt_extT (· ∈ v.tP) (c.bes (j + 1 + 1) σ (idx_step h)).o (c.X (j + 1)) (hv.atT (j + 1)).1
    have hAC1 := (GlobalTheory.T.dataAsCombinationsAtSplitPlaces_proof D k ι o.p o.I _ hPl (Fin (c.X (j + 1)).rank) (Fin (c.X j).rank ⊕ Fin 1) c.ψ hstd _ _
      (o.β₀ j (σ + 1) h) (o.β (j + 1)) (o.M j (σ + 1) h) (c.x (j + 1)).L sdG sd1
      (fun i => tensCol (phiOne (a.P i) (b.Q i)) (vecInd (b.Q i).lat))).2.2 _ hD1 _ hXi1
    have hAC2 := (GlobalTheory.T.dataAsCombinationsAtSplitPlaces_proof D k ι o.p o.I _ hPl (Fin (c.X (j + 1 + 1)).rank ⊕ Fin 1) (Fin (c.X (j + 1)).rank) c.ψ hstd _ _
      (o.β (j + 1)) (o.β₀ (j + 1 + 1) σ (idx_step h)) (c.x (j + 1)).L (o.M (j + 1 + 1) σ (idx_step h)) sd1 sdG'
      (fun i => tensRow (phiOne (b.Q i) (a'.P i)) (dualInd (b.Q i).lat))).2.2 _ hD2 _ hXi2
    have th1' := GlobalTheory.AvgMid.theta_comb hstd (isFinComb_of_combAt _ hT1) hf₁.1
    have th2' := GlobalTheory.AvgMid.theta_comb hstd (isFinComb_of_combAt _ hT2) hf₂.1
    have thD1' := GlobalTheory.AvgMid.theta_comb hstd (isFinComb_of_combAt _ hD1) th1'
    have thD2' := GlobalTheory.AvgMid.theta_comb hstd (isFinComb_of_combAt _ hD2) th2'
    have hVx := hVE σ (c.B j (σ + 1) h) (c.J j (σ + 1) h) (c.B (j + 1 + 1) σ (idx_step h)) (t.sBF j (σ + 1) h) (t.sFB j σ h)
      (c.lnk j σ h) (c.vL j σ h) (fun x hx => ⟨hU.bf j (σ + 1) h x hx, hU.fb j σ h x hx⟩) a b a' (o.M j (σ + 1) h)
      (c.x (j + 1)).L (o.M (j + 1 + 1) σ (idx_step h)) sdG sd1 sdG' hcore _ _ hAC1.1 hAC2.1 _ _ (hAC1.2 _ hov1)
      (hAC2.2 _ hov2) φ hφ
    have hSφ : IsContAut (c.X j) (a.sAll o.q (fun i => resChar (o.χ i) (o.hχ i) o.q) ε o.I φ) :=
      ((GlobalTheory.T.epsilonFourierProduct_bijective_gluedPlaces D k ι o.p o.q o.χ o.hχ ε (Fin (c.X j).rank) _ _ a hS.pre.inj o.I).1.mapsTo hφ).1
    have e1 := (hCC _ _ hXi1.1 hXi2.1).2.1 d d'
    have e2 := bl_contr hCL v t hW h hφ.1 hAC1.1.1 hAC2.1.1
    have e4 := bl_contr hCL v t hW h hSφ thD1' thD2'
    have e5 := (hCC _ _ th1' th2').2.1 d d'
    have e6 := (hCC _ _ hf₁.1 hf₂.1).2.1 (v.dT j) (v.dT (j + 1))
    show c.bl j (t.kom j) (t.kom (j + 1)) φ (biComb c.ψ _ _ _ d d' (GlobalTheory.Unf.contr (B := c.B j (σ + 1) h) (B' := c.B (j + 1 + 1) σ (idx_step h)) (c.lnk j σ h) (c.X (j + 1)) (c.vL j σ h) (flatBF (t.sBF j (σ + 1) h) Ψ₁) (flatFB (t.sFB j σ h) Ψ₂))) = _
    rw [← e1, e2, hVx, ← e4, e5, e6]
    rfl

end GlobalTheory.LevPrimeMid
