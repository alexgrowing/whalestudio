import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrysActApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBCTrivSqZeroExt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoords
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualNumberGraphFiltrationExistsIsComplStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemHodgeFiltrationIffDualNumberGraphReductionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualNumberGraphFiltrationPushforwardMemStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualNumberGraphFiltrationIsotropicOfSkewStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieConditionHodgeSubspaceLeHodgeFiltrationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualNumberGraphFiltrationLieOfMapIntoHodgeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorExistsLiftOrderActionHodgeSummand
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorExistsPolarisationBundleLiftStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLiftLieOfHodgeSummandLieStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLieMultiplicitySquareZeroLift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorPrimeToPLevelLiftSquareZeroStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

noncomputable section

namespace GlobalTheory.HTRealise

set_option maxHeartbeats 4000000 in

theorem realise_core (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R]
    (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (hN : N.Coprime p) (k : Type) [Field k] (β : R →+* k)
    (s : Sp k ⟶ Sp R) (hs : s = spMap β) (o₀ : GlobalTheory.UPel.HT.Obj b N s)
    (φ : LinearMap.BilinForm k (HdR o₀.A)) (hφ : GlobalTheory.AbDual.IsCorrForm (dp0 k) (𝟙 _) o₀.A o₀.A o₀.P φ)
    (f : HdR o₀.A →ₗ[k] HdR o₀.A)
    (hf : IsKS (GlobalTheory.HTCount.crysAct o₀) φ (Fil o₀.A) (GlobalTheory.HTCount.lieZ o₀ β) f)
    (tR : R →+* DualNumber k) (htR : tR = (algebraMap k (DualNumber k)).comp β)
    (hs' : s = spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ spMap tR) :
    ∃ (o' : GlobalTheory.UPel.HT.Obj b N (spMap tR))
      (m' : GlobalTheory.UPel.HT.ObjMap o₀ o' (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)),
      ∀ x ∈ Fil o₀.A, IsFilLift m'.cart x (f x) := by
  have hZ := GlobalTheory.T.lieConditionHodgeSubspace_le_hodgeFiltration p D R b N k β s hs o₀
  subst hs'
  haveI : Module.Finite k (DualNumber k) := inferInstanceAs (Module.Finite k (k × k))
  haveI : IsArtinianRing (DualNumber k) := IsArtinianRing.of_finite k (DualNumber k)
  have hπ : Function.Surjective (TrivSqZeroExt.fstHom k k k).toRingHom :=
    fun r => ⟨TrivSqZeroExt.inl r, rfl⟩
  have hsq : RingHom.ker (TrivSqZeroExt.fstHom k k k).toRingHom ^ 2 = 0 := (SqExt.dual k).sq
  have hA₀ := o₀.ab
  obtain ⟨M, hM⟩ := GlobalTheory.T.dualNumberGraphFiltration_exists_isCompl k o₀.A hA₀ f
  obtain ⟨A, _, i, h, act, hA, hE, hact⟩ := GlobalTheory.HTDeform.exists_lift_oAct p D R b N (DualNumber k) k
    (TrivSqZeroExt.fstHom k k k).toRingHom hπ hsq tR o₀ (graphFil o₀.A f) ⟨M, hM⟩
    (fun y => GlobalTheory.T.mem_hodgeFiltration_iff_dualNumberGraph_reduction k o₀.A hA₀ f y)
    (fun c d hd => by
      haveI := o₀.act.hom c
      exact GlobalTheory.T.dualNumberGraphFiltration_pushforward_mem k o₀.A (o₀.act.act c) f (fun x hx => hf.1 c x hx) d hd)
  haveI : IsCommMonObj A := hA.comm
  obtain ⟨P, φ₂, hP, r1, r2, hsym, hamp, hker, hros, hsq2, hpol⟩ :=
    GlobalTheory.T.harrisTaylor_exists_polarisation_bundle_lift p D R b N (DualNumber k) k (TrivSqZeroExt.fstHom k k k).toRingHom hπ hsq tR o₀ A i h hA act hact
      (fun φ' hφ' x hx y hy => by
        rw [hE] at hx hy
        exact GlobalTheory.T.dualNumberGraphFiltration_isotropic_of_skew k o₀.A hA₀ o₀.P o₀.isLB φ hφ f hf.2.2 φ' hφ' x hx y hy)
  obtain ⟨eta, e1, e2, e3, e4, e5⟩ := GlobalTheory.T.harrisTaylor_primeToP_level_lift_squareZero p D R b N (DualNumber k) k
    (TrivSqZeroExt.fstHom k k k).toRingHom hπ hsq tR o₀ A i h hA act hact hN P φ₂ hP hsq2 hpol
  have hEl : ∀ d : Crys (divided₂ hsq) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) o₀.A,
      (haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O D.ω);
        push (divided₂ hsq) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) (o₀.act.act (algebraMap (𝓞 D.F) D.O D.ω)) d)
        - tR b.ρ • d ∈ liftFil (divided₂ hsq) h →
      ∃ w : Fin D.a → Crys (divided₂ hsq) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) o₀.A,
        (∀ i (c : 𝓞 D.F), (haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O c);
          push (divided₂ hsq) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) (o₀.act.act (algebraMap (𝓞 D.F) D.O c)) (w i))
            - tR (b.t i c) • w i ∈ liftFil (divided₂ hsq) h) ∧ d - ∑ i, w i ∈ liftFil (divided₂ hsq) h := by
    intro d hd
    rw [hE] at hd ⊢
    subst htR
    exact GlobalTheory.T.dualNumberGraphFiltration_lie_of_map_into_hodge p D R b N k β _ o₀ f hZ hf.2.1 d hd
  refine ⟨{ A := A
            ab := hA
            act := act
            P := P
            isLB := hP
            rig₁ := r1
            rig₂ := r2
            symm := hsym
            ample := hamp
            kerP := hker
            rosati := hros
            lie := fun R' _ β' x hx v hv => GlobalTheory.T.harrisTaylor_lift_lie_of_hodge_summand_lie p D R b N (DualNumber k) k
              (TrivSqZeroExt.fstHom k k k).toRingHom hπ hsq tR o₀ A i h hA act hact hEl R' β' x hx v hv
            lieRank := fun k' _ _ x β' hx j => GlobalTheory.HTLiftLie.lieMult_of_sqZeroLift p D R b N (DualNumber k) k
              (TrivSqZeroExt.fstHom k k k).toRingHom hπ hsq tR o₀ A i h act hact k' x β' hx j
            eta := eta
            eta_add := e1
            eta_lin := e2
            eta_ker := e3
            geom := e4 },
    { φ := i
      φ₂ := φ₂
      cart := h
      sq := hsq2
      act := hact
      pol := hpol
      eta := e5 }, fun x hx => ?_⟩
  obtain ⟨d, hd⟩ := exists_crys hA₀ x (f x)
  refine ⟨d, ?_, hd⟩
  change d ∈ liftFil (divided₂ hsq) h
  rw [hE]
  exact ⟨x, hx, 0, zero_mem _, fun c => by rw [hd c, LinearMap.zero_apply, add_zero]⟩

end GlobalTheory.HTRealise

theorem GlobalTheory.UPel.HT.realise_isKS : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k), t = spMap β → ∀ φ : LinearMap.BilinForm k (HdR o₀.A), GlobalTheory.AbDual.IsCorrForm (dp0 k) (𝟙 _) o₀.A o₀.A o₀.P φ → ∀ f : HdR o₀.A →ₗ[k] HdR o₀.A, IsKS (GlobalTheory.HTCount.crysAct o₀) φ (Fil o₀.A) (GlobalTheory.HTCount.lieZ o₀ β) f → ∃ (o' : GlobalTheory.UPel.HT.Obj b N (spMap (algebraMap k (DualNumber k)) ≫ t)) (m' : GlobalTheory.UPel.HT.ObjMap o₀ o' (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)), ∀ x ∈ Fil o₀.A, IsFilLift m'.cart x (f x) := by
  intro p _ D R _ b N _ hN k _ _ t o₀ β ht φ hφ f hf
  have e1 : spMap (algebraMap k (DualNumber k)) ≫ t = spMap ((algebraMap k (DualNumber k)).comp β) := by
    rw [ht, ← GlobalTheory.Cris.spMap_comp]
  have e2 : t = spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ spMap ((algebraMap k (DualNumber k)).comp β) := by
    rw [ht, ← GlobalTheory.Cris.spMap_comp]
    exact congrArg spMap (RingHom.ext fun r => rfl)
  rw [e1]
  exact GlobalTheory.HTRealise.realise_core p D R b N hN k β t ht o₀ φ hφ f hf _ rfl e2
