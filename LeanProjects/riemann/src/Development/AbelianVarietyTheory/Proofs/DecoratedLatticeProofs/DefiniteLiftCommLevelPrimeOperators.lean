import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PairForm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OverAllExists
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RamifiedOperatorsBijectiveAtPlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RamifiedThetaLiftCommutesSplitPlaceOperatorsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationCommFockPolynomialVectors
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OmZeroRat
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DataAsCombinationsAtSplitPlacesProofStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeisenbergOrientedFiniteFixesFockPolynomialVecto
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtYAndItYOfPair
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedTensorBasePointNormSq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FockVectorsChainIsVacuumOffThetaLevels
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.FinPl GlobalTheory.SeeSaw ValuativeRel IsLocalRing
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw.LiftsAtLevel

variable {D : D7}

theorem combAt_mono {P P' : Pl D → Prop} (h : ∀ v, P v → P' v) {S T : HSp D} {c : WO S T →₀ ℂ} (hc : CombAt P c) :
    CombAt P' c :=
  fun u hu a b => AllBij.idAt_mono h (hc u hu a b)

theorem comb_pureTensorO {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} (hstd : IsStdChar D ψ (-1))
    (hθ : IsInfFam θ) (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    {c : WO S T →₀ ℂ} (hc : IsFinComb c) (φ : MvPolynomial (FVar D T.rank S.rank) ℂ) :
    pureTensorO ψ θ S T sS sT BS BT (comb ψ S T c f) φ = comb ψ S T c (pureTensorO ψ θ S T sS sT BS BT f φ) := by
  classical
  have e : ∀ g : WO S T → ℂ, comb ψ S T c g =
      ∑ i, c (c.support.equivFin.symm i) • heisO ψ S T (c.support.equivFin.symm i) g := by
    intro g
    unfold comb
    rw [← Finset.sum_coe_sort c.support]
    exact Fintype.sum_equiv c.support.equivFin _ _ (fun x => by simp)
  have key := (GlobalTheory.FockFiniteHeis.heis_comb_pureTensorO D ψ θ S T hstd hθ sS sT BS BT f hf c.support.card
    (fun i => c (c.support.equivFin.symm i)) (fun i => (c.support.equivFin.symm i : WO S T))
    (fun i => hc _ (c.support.equivFin.symm i).2) φ).1
  rw [e, e, key]

theorem vac_pureTensorO {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {x : DefSp S} {y : DefSp T}
    {f₀ : WO S T → ℂ} (hvac : IsVacO ψ θ S T x.s y.s x.L y.L f₀) (P : Pl D → Prop)
    (φ : MvPolynomial (FVar D T.rank S.rank) ℂ) :
    Vac ψ S T x.L y.L P (pureTensorO ψ θ S T x.s y.s x.B y.B f₀ φ) := by
  have hth : ∀ φ, IsThetaFunO ψ S T (pureTensorO ψ θ S T x.s y.s x.B y.B f₀ φ) := fun φ =>
    GlobalTheory.Chain.InnerSteps.theta_pureTensorO hvac.1 hvac.2.inf x.s x.B y.s y.B hvac.2.theta φ
  have hle : latO S T (x.L : Set _) (y.L : Set _) P ≤ latO S T (x.L : Set _) (y.L : Set _) fun _ => True :=
    GlobalTheory.PlaceTensor.latO_mono fun _ _ => trivial
  refine ⟨hth φ, fun u hu => ?_, fun e he u hu hh => ?_⟩
  · have hu' := hle hu
    exact GlobalTheory.Hk3.FiniteHeis.heisO_pureTensorO_of_finite ψ θ S T hvac.2.inf x.s y.s x.B y.B f₀ hth (2 • u)
      (GlobalTheory.VacGood.infPart_latO (AddSubgroup.nsmul_mem _ hu' 2)) (hvac.2.lat.1 u hu') φ
  · have hu' := hle hu
    exact GlobalTheory.Hk3.FiniteHeis.heisO_pureTensorO_of_finite ψ θ S T hvac.2.inf x.s y.s x.B y.B f₀ hth u
      (GlobalTheory.VacGood.infPart_latO hu') (hvac.2.lat.2 e he u hu' hh) φ

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem sOp_ram {ι : Type} {p : ι → SplitPt D k} (hinj : Function.Injective fun i => (p i).v) {S : HSp D} {n : Type}
    [Fintype n] [DecidableEq n] (β : ∀ i, Frame (p i) S n) (Q : ι → Pair k n) (q : Unif k) (χ₀ : ι → AddChar k Circle)
    (hχ : ∀ i, HasConductor (χ₀ i) 1) (ε : 𝓀[k]ˣ) (i : ι) {φ : GA D S → ℂ}
    (hφ : IsContAut S φ ∧ ∀ i', RamAt (β i') (Q i') φ) :
    IsContAut S (sOp (β i) (Q i) q (resChar (χ₀ i) (hχ i) q) ε φ) ∧
      ∀ i', RamAt (β i') (Q i') (sOp (β i) (Q i) q (resChar (χ₀ i) (hχ i) q) ε φ) := by
  obtain ⟨hbij, -, c, c', hc, -⟩ := GlobalTheory.T.ramifiedOperator_bijective_finite_translation_combination D k (p i) n q (χ₀ i) (hχ i) _ rfl ε S (β i) (Q i)
  have hT : ∀ φ, sOp (β i) (Q i) q (resChar (χ₀ i) (hχ i) q) ε φ = AllBij.act (Finsupp.mapDomain (β i).gl c) φ :=
    fun φ => (hc φ).trans (AllBij.sum_rep_eq _ _ _)
  have hC := AllBij.mapDomain_mem _ (AllBij.gl_mem (β i)) c
  refine ⟨by rw [hT]; exact AllBij.isContAut_act _ hφ.1, fun i' => ?_⟩
  rcases eq_or_ne i' i with rfl | hne
  · exact hbij.mapsTo (hφ.2 i')
  · rw [hT]
    exact AllBij.ramAt_act _ _ _ (fun x hx g => AllBij.grpAt_comm S (fun e => hne (hinj e)) (hC x hx)
      (AllBij.gl_mem _ g)) (hφ.2 i')

theorem foldr_ram {ι : Type} {p : ι → SplitPt D k} (hinj : Function.Injective fun i => (p i).v) {S : HSp D} {n : Type}
    [Fintype n] [DecidableEq n] (β : ∀ i, Frame (p i) S n) (Q : ι → Pair k n) (q : Unif k) (χ₀ : ι → AddChar k Circle)
    (hχ : ∀ i, HasConductor (χ₀ i) 1) (ε : ι → 𝓀[k]ˣ) (l : List ι) {φ : GA D S → ℂ}
    (hφ : IsContAut S φ ∧ ∀ i', RamAt (β i') (Q i') φ) :
    IsContAut S (l.foldr (fun i φ' => sOp (β i) (Q i) q (resChar (χ₀ i) (hχ i) q) (ε i) φ') φ) ∧
      ∀ i', RamAt (β i') (Q i') (l.foldr (fun i φ' => sOp (β i) (Q i) q (resChar (χ₀ i) (hχ i) q) (ε i) φ') φ) := by
  induction l with
  | nil => exact hφ
  | cons i l ih => exact sOp_ram hinj β Q q χ₀ hχ (ε i) i ih

theorem isIdele_idele (p : SplitPt D k) (x : kˣ) : p.IsIdele x (p.idele x) := by
  unfold SplitPt.IsIdele
  rw [SplitPt.idele_val]
  ring

end Local

theorem chrPow_mul_neg (μ : (AE D)ˣ →* Circle) (a : (AE D)ˣ) (e : ℤ) : chrPow μ a e * chrPow μ a (-e) = 1 := by
  simp only [chrPow, ← Circle.coe_mul, _root_.zpow_neg, mul_inv_cancel, Circle.coe_one]

end GlobalTheory.SeeSaw.LiftsAtLevel

namespace GlobalTheory.SeeSaw.LiftsAtLevel

open GlobalTheory.FinPl.ValDbl in

theorem pt_over {D : D7} {c : Comm D} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {ι : Type} {v : VCom c} {o : TDat c k ι} {t : Tup c} {w : VTup t} (hc : c.Is) (ht : t.Is) (hv : v.Is) (hVF : VForm v w)
    (hSh : ShapeOff v o) (j : ℕ) (hj : j < D.R.m) (α : t.Ch j) (γ : t.Ch (j + 1))
    (P : PolF D (c.X (j + 1)).rank (c.X j).rank) (i : ι) :
    ∃ f₀, Over c.ψ (o.β j i) (o.β (j + 1) i) (c.x j).L (c.x (j + 1)).L f₀ (phiOne (o.Q j i) (o.Q (j + 1) i))
      ((t.ker j α γ).pt c.ψ c.θ (c.x j) (c.x (j + 1)) P) := by
  have hk := ht.ker j hj α γ
  have hvac : IsVacO c.ψ c.θ (c.X j) (c.X (j + 1)) (c.x j).s (c.x (j + 1)).s (c.x j).L (c.x (j + 1)).L (c.vac j) := hk.vac
  have hstd := hc.std
  have hxS := hc.x j hj.le
  have hxT := hc.x (j + 1) hj
  set f := pureTensorO c.ψ c.θ (c.X j) (c.X (j + 1)) (c.x j).s (c.x (j + 1)).s (c.x j).B (c.x (j + 1)).B (c.vac j) P
    with hfdef
  have hfV : ∀ Pp, Vac c.ψ _ _ (c.x j).L (c.x (j + 1)).L Pp f := fun Pp => vac_pureTensorO hvac Pp P
  have hpt : (t.ker j α γ).pt c.ψ c.θ (c.x j) (c.x (j + 1)) P =
      comb c.ψ _ _ (w.dQ j α γ) (comb c.ψ _ _ (v.dG j) (comb c.ψ _ _ (v.dT j) f)) := by
    show pureTensorO c.ψ c.θ (c.X j) (c.X (j + 1)) (c.x j).s (c.x (j + 1)).s (c.x j).B (c.x (j + 1)).B
      (comb c.ψ _ _ (t.dd j α γ) (c.vac j)) P = _
    rw [comb_pureTensorO hstd hc.inf _ _ _ _ hvac.2.theta (c := t.dd j α γ) hk.fin P]
    exact hVF.dd j hj α γ f (hfV fun _ => True).1
  have hrep := hSh.rep j hj f (hfV _)
  have hpl : Places o.p o.I (· ∈ v.tP) :=
    ⟨hSh.pre.nodup, hSh.pre.all, hSh.pre.inj, hSh.pre.tP, fun i => (hSh.pre.char i).2⟩
  have hAC := (GlobalTheory.T.dataAsCombinationsAtSplitPlaces_proof D k ι o.p o.I (· ∈ v.tP) hpl (Fin (c.X (j + 1)).rank) (Fin (c.X j).rank) c.ψ hstd
    (c.X j) (c.X (j + 1)) (o.β j) (o.β (j + 1)) (c.x j).L (c.x (j + 1)).L hxS.sd hxT.sd
    (fun i => phiOne (o.Q j i) (o.Q (j + 1) i))).2.2
  have hdG : CombAt (fun x => ¬ x ∈ v.tP) (v.dG j) :=
    combAt_mono (fun x hx ht' => Finset.disjoint_left.1 hv.disj hx ht') (hv.atG j).2.1
  have hdQ : CombAt (fun x => ¬ x ∈ v.tP) (w.dQ j α γ) :=
    combAt_mono (fun x hx ht' => Finset.disjoint_left.1 hVF.disjT hx ht') ((hVF.atQ j).2.2 α γ)
  obtain ⟨hV1, hO1⟩ := hAC (v.dG j) hdG f (hfV _)
  obtain ⟨hV2, hO2⟩ := hAC (w.dQ j α γ) hdQ _ hV1
  have hO := hO2 _ (hO1 _ hrep)
  obtain ⟨g, hg, -⟩ := overAll_last hstd (fun i => (hSh.pre.char i).2) hSh.pre.inj o.I hSh.pre.nodup _ _
    (fun j' => vac_at ((hSh.pre.tP _).2 ⟨j', rfl⟩) hV2) hO i (hSh.pre.all i)
  exact ⟨g, hpt ▸ hg⟩

end GlobalTheory.SeeSaw.LiftsAtLevel

open GlobalTheory.SeeSaw.LiftsAtLevel in

theorem GlobalTheory.SeeSaw.liftS_of_exact : ∀ (D : D7) (c : Comm D) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (v : VCom c) (o : TDat c k ι) (t : Tup c) (w : VTup t), LiftExact D → c.Is → t.Is → v.Is → VForm v w → ShapeOff v o → (∀ j, j < D.R.m → ∃ μ, IsWeilDatumO c.ψ _ _ μ μ (t.kom j) ∧ ∀ i, GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D μ (o.p i).v) → LiftS o t := by
  intro D c k _ _ _ _ ι v o t w hLE hc ht hv hVF hSh hμ j hj α γ P φ hφ
  obtain ⟨μ, hW, hU⟩ := hμ j hj
  have hxS := hc.x j hj.le
  have hxT := hc.x (j + 1) hj
  have hk := ht.ker j hj α γ
  have hφ' : IsContAut (c.X j) φ ∧ ∀ i, RamAt (o.β j i) (o.Q j i) φ := hφ
  set F := (t.ker j α γ).pt c.ψ c.θ (c.x j) (c.x (j + 1)) P with hF
  have hOv := pt_over hc ht hv hVF hSh j hj α γ P
  have hlift : ∀ φ', (t.ker j α γ).lift c.ψ c.θ (c.x j) (c.x (j + 1)) P φ' =
      liftT (t.kom j) (c.x j).vol.μ (c.x j).vol.𝓕 φ' F := fun φ' => rfl

  have hram : ∀ φ', (IsContAut (c.X j) φ' ∧ ∀ i, RamAt (o.β j i) (o.Q j i) φ') →
      liftT (t.kom j) (c.x j).vol.μ (c.x j).vol.𝓕 φ' F ∈ o.Ram (j + 1) := by
    intro φ' h'
    refine ⟨?_, fun i => ?_⟩
    · rw [← hlift]
      exact (GlobalTheory.SeeSaw.LiftSumProof.liftSum D c.ψ c.θ hc.inf _ _ (c.x j) (c.x (j + 1)) hxS hxT _ hk P).2.1 φ' h'.1
    · obtain ⟨f₀, hf₀⟩ := hOv i
      obtain ⟨c₀, -, H⟩ := GlobalTheory.T.ramifiedThetaLift_commutes_splitPlace_operators D k (o.p i) (Fin (c.X (j + 1)).rank) (Fin (c.X j).rank) o.q (o.χ i) (o.hχ i) c.ψ
        (c.X j) (c.X (j + 1)) hxS.cpt (c.x j).vol μ μ (t.kom j) hW (hU i) (hU i) (o.β j i) (o.β (j + 1) i) (o.Q j i)
        (o.Q (j + 1) i)
      exact (H _ _ f₀ F hf₀ φ' (h'.2 i)).1
  refine ⟨by rw [hlift]; exact hram φ hφ', fun η => ?_⟩

  have key : ∀ l : List ι, l.foldr (fun i φ' => sOp (o.β (j + 1) i) (o.Q (j + 1) i) o.q (resChar (o.χ i) (o.hχ i) o.q) (η i) φ')
        (liftT (t.kom j) (c.x j).vol.μ (c.x j).vol.𝓕 φ F) =
      ((((resCard k : ℝ) ^ ((((c.X (j + 1)).rank : ℝ) - (c.X j).rank) / 2) : ℝ) : ℂ) ^ l.length) •
        liftT (t.kom j) (c.x j).vol.μ (c.x j).vol.𝓕
          (l.foldr (fun i φ' => sOp (o.β j i) (o.Q j i) o.q (resChar (o.χ i) (o.hχ i) o.q) (η i) φ') φ) F := by
    intro l
    induction l with
    | nil => simp
    | cons i l ih =>
      simp only [List.foldr_cons, List.length_cons]
      rw [ih, GlobalTheory.FinPl.ValDbl.sOp_smul]
      obtain ⟨e, -, hE⟩ := hLE k (o.p i) o.q (o.χ i) (o.hχ i)
      obtain ⟨f₀, hf₀⟩ := hOv i
      have hr := (foldr_ram hSh.pre.inj (o.β j) (o.Q j) o.q o.χ o.hχ η l hφ').2 i
      rw [hE (Fin (c.X (j + 1)).rank) (Fin (c.X j).rank) c.ψ (c.X j) (c.X (j + 1)) hxS.cpt (c.x j).vol μ μ (t.kom j) hW
        (hU i) (hU i) (o.β j i) (o.β (j + 1) i) (o.Q j i) (o.Q (j + 1) i) _ (isIdele_idele (o.p i) o.q.unit) _ _ f₀ F hf₀ _ hr
        (η i), mul_assoc, chrPow_mul_neg, mul_one, smul_smul, pow_succ]
      simp only [Fintype.card_fin]
  simp only [TDat.S, TDat.cL, hlift]
  exact key o.I
