import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsArtinianRingTsze
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupObjectLiftDividedPowers
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.InfUniv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumProjSingle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorExistsLiftOrderActionHodgeSummandStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorExistsPolarisationBundleLiftStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLiftLieOfHodgeSummandLieStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLieMultiplicitySquareZeroLiftStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorPrimeToPLevelLiftSquareZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLiftHodgeSummandAdmissibleStableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLiftHodgeSummandIsotropicStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLiftHodgeSummandCrystallineLieStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsComplCrystalGluedHodgeGraphFiltrationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemHodgeFiltrationIffReductionGluedFiltrationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystalGluedHodgeGraphOrderStableOfDirectionsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystalGluedHodgeGraphIsotropicOfDirectionsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystalGluedHodgeGraphLieConditionOfDirectionsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSqZeroLiftRealisingKs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorExistsDeRhamPairing
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

theorem GlobalTheory.HTGlue.isFilLift_coords {k : Type} [Field k] {A : Over (Sp k)} [GrpObj A] {A' : Over (Sp (DualNumber k))}
    [GrpObj A'] {i : A.left ⟶ A'.left} (h : IsGrpPullback A A' (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) i)
    {x y : HdR A} (hx : IsFilLift h x y) :
    ∃ e ∈ liftFil (divided₂ (GlobalTheory.FODef.sqZero k k)) h,
      ∀ c, e ((GlobalTheory.FODef.constMorV k k A).pull c) = TrivSqZeroExt.inl (x c) + TrivSqZeroExt.inr (y c) := hx

theorem GlobalTheory.HTGlue.exists_obj_of_summand (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R]
    (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (hNp : N.Coprime p) (C C₀ : Type) [CommRing C] [IsLocalRing C]
    [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀) (hπ : Function.Surjective π) (hsq : RingHom.ker π ^ 2 = 0)
    (tR : R →+* C) (o₀ : GlobalTheory.UPel.HT.Obj b N (spMap π ≫ spMap tR)) (E : Submodule C (Crys (divided₂ hsq) (spMap π) o₀.A))
    (hEc : ∃ M : Submodule C (Crys (divided₂ hsq) (spMap π) o₀.A), IsCompl E M)
    (hEf : ∀ y : HdR o₀.A, y ∈ Fil o₀.A ↔ ∃ d ∈ E, (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ hsq) rfl o₀.A).Corr d y)
    (hEs : ∀ (c : D.O), ∀ d ∈ E, (haveI := o₀.act.hom (c); push (divided₂ hsq) (spMap π) (o₀.act.act (c)) (d)) ∈ E)
    (hEi : ∀ φ : Crys (divided₂ hsq) (spMap π) o₀.A →ₗ[C] Crys (divided₂ hsq) (spMap π) o₀.A →ₗ[C] C,
      GlobalTheory.AbDual.IsCorrForm (divided₂ hsq) (spMap π) o₀.A o₀.A o₀.P φ → ∀ x ∈ E, ∀ y ∈ E, φ x y = 0)
    (hEl : ∀ d : Crys (divided₂ hsq) (spMap π) o₀.A, (haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O D.ω);
      push (divided₂ hsq) (spMap π) (o₀.act.act (algebraMap (𝓞 D.F) D.O D.ω)) (d)) - tR b.ρ • d ∈ E →
      ∃ w : Fin D.a → Crys (divided₂ hsq) (spMap π) o₀.A, (∀ i (c : 𝓞 D.F), (haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O c);
        push (divided₂ hsq) (spMap π) (o₀.act.act (algebraMap (𝓞 D.F) D.O c)) (w i)) - tR (b.t i c) • w i ∈ E) ∧
        d - ∑ i, w i ∈ E)
    (s : Sp C ⟶ Sp R) (hs : s = spMap tR) :
    ∃ (o : GlobalTheory.UPel.HT.Obj b N s) (m : GlobalTheory.UPel.HT.ObjMap o₀ o (spMap π)), liftFil (divided₂ hsq) m.cart = E := by
  subst hs
  obtain ⟨A, _, i, h, act, hA, hE, hact⟩ := GlobalTheory.T.harrisTaylor_exists_lift_orderAction_hodge_summand p D R b N C C₀ π hπ hsq tR o₀ E hEc hEf hEs
  haveI : IsCommMonObj A := hA.comm
  subst hE
  obtain ⟨P, φ₂, hP, r1, r2, hsym, hamp, hker, hros, hsq2, hpol⟩ :=
    GlobalTheory.T.harrisTaylor_exists_polarisation_bundle_lift p D R b N C C₀ π hπ hsq tR o₀ A i h hA act hact hEi
  obtain ⟨eta, e1, e2, e3, e4, e5⟩ :=
    GlobalTheory.T.harrisTaylor_primeToP_level_lift_squareZero p D R b N C C₀ π hπ hsq tR o₀ A i h hA act hact hNp P φ₂ hP hsq2 hpol
  exact ⟨{ A := A
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
           lie := fun R' _ β x hx v hv => GlobalTheory.T.harrisTaylor_lift_lie_of_hodge_summand_lie p D R b N C C₀ π hπ hsq tR o₀ A i h hA act hact hEl R' β x hx v hv
           lieRank := fun k _ _ x β hx j => GlobalTheory.T.harrisTaylor_lieMultiplicity_squareZeroLift p D R b N C C₀ π hπ hsq tR o₀ A i h act hact k x β hx j
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
      eta := e5 }, rfl⟩

theorem GlobalTheory.HTGlue.isFilLiftV_of_eq {k : Type} [Field k] {d : ℕ} {A₀ : Over (Sp k)} [GrpObj A₀] (hA : IsAbelianScheme A₀)
    {A : Over (Sp (TrivSqZeroExt k (Fin d → k)))} [GrpObj A] {i : A₀.left ⟶ A.left}
    (h : IsGrpPullback A₀ A (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) i)
    (f : Fin d → (HdR A₀ →ₗ[k] HdR A₀))
    (hh : liftFil (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) h = GlobalTheory.HTGlue.glueFil A₀ f) {x : HdR A₀}
    (hx : x ∈ Fil A₀) : GlobalTheory.FODef.IsFilLiftV h x (LinearMap.pi fun j => f j x) := by
  obtain ⟨e, he, hc⟩ := GlobalTheory.HTGlue.exists_mem_glueFil A₀ hA f hx
  exact ⟨e, hh ▸ he, hc⟩

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.HTGlue.exists_glue : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t), ∀ (d : ℕ) (f : Fin d → (HdR o₀.A →ₗ[k] HdR o₀.A)), (∀ j, ∃ (o' : GlobalTheory.UPel.HT.Obj b N (spMap (algebraMap k (DualNumber k)) ≫ t)) (m' : GlobalTheory.UPel.HT.ObjMap o₀ o' (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)), ∀ x ∈ Fil o₀.A, IsFilLift m'.cart x (f j x)) → ∃ (o : GlobalTheory.UPel.HT.Obj b N (spMap (algebraMap k (TrivSqZeroExt k (Fin d → k))) ≫ t)) (m : GlobalTheory.UPel.HT.ObjMap o₀ o (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom)), ∀ x ∈ Fil o₀.A, GlobalTheory.FODef.IsFilLiftV m.cart x (LinearMap.pi fun j => f j x) := by
  intro p _ D R _ b N hN hNp k _ _ t o₀ d f hdef
  rcases Nat.eq_zero_or_pos d with rfl | hd
  ·

    obtain ⟨tk, ht⟩ : ∃ tk : R →+* k, t = spMap tk := ⟨(Spec.preimage t).hom, by simp [spMap]⟩
    obtain ⟨φ, hφ⟩ := GlobalTheory.UPel.HT.CorrForm.exists_isCorrForm_obj p D R b N hN hNp k t o₀
    exact GlobalTheory.UPel.HT.exists_sqZero_lift_realising_ks p D R b N hN hNp k t o₀ tk ht φ hφ 0 f (fun j => j.elim0)
  haveI : IsArtinianRing (TrivSqZeroExt k (Fin d → k)) := GlobalTheory.HTGlue.isArtinianRing_tsze k d
  haveI : Module.Finite k (DualNumber k) :=
    Module.Finite.of_surjective ((Algebra.linearMap k (DualNumber k)).coprod (TrivSqZeroExt.inrHom k k))
      (fun x => ⟨(x.fst, x.snd), by ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]⟩)
  haveI : IsArtinianRing (DualNumber k) := IsArtinianRing.of_finite k _
  obtain ⟨tk, ht⟩ : ∃ tk : R →+* k, t = spMap tk := ⟨(Spec.preimage t).hom, by simp [spMap]⟩
  set tR : R →+* TrivSqZeroExt k (Fin d → k) := (algebraMap k (TrivSqZeroExt k (Fin d → k))).comp tk with htR
  have hs : t = spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom ≫ spMap tR := by
    rw [ht, ← GlobalTheory.Cris.spMap_comp]
    all_goals (congr 1 <;> ext x <;> simp [tR])
  subst hs
  choose o' m' hm' using hdef
  have hsε : spMap (algebraMap k (DualNumber k)) ≫
      (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom ≫ spMap tR) =
      spMap ((algebraMap k (TrivSqZeroExt k k)).comp tk) := by
    rw [ht, ← GlobalTheory.Cris.spMap_comp]
  have hs₀ : spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom ≫ spMap tR =
      spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ spMap ((algebraMap k (TrivSqZeroExt k k)).comp tk) := by
    rw [ht, ← GlobalTheory.Cris.spMap_comp]
    all_goals (congr 1 <;> ext x <;> simp)
  have hsurε : Function.Surjective (TrivSqZeroExt.fstHom k k k).toRingHom :=
    fun a => ⟨TrivSqZeroExt.inl a, by simp⟩
  have n1 := fun j => GlobalTheory.T.harrisTaylor_lift_hodge_summand_admissible_stable p D R b N (DualNumber k) k (TrivSqZeroExt.fstHom k k k).toRingHom hsurε (GlobalTheory.FODef.sqZero k k) ((algebraMap k (TrivSqZeroExt k k)).comp tk) (spMap (algebraMap k (DualNumber k)) ≫ (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom ≫ spMap tR)) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom ≫ spMap tR) o₀ (o' j) (m' j) hsε hs₀
  have n2 := fun j => GlobalTheory.T.harrisTaylor_lift_hodge_summand_isotropic p D R b N (DualNumber k) k (TrivSqZeroExt.fstHom k k k).toRingHom hsurε (GlobalTheory.FODef.sqZero k k) ((algebraMap k (TrivSqZeroExt k k)).comp tk) (spMap (algebraMap k (DualNumber k)) ≫ (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom ≫ spMap tR)) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom ≫ spMap tR) o₀ (o' j) (m' j) hsε hs₀
  have n3 := fun j => GlobalTheory.T.harrisTaylor_lift_hodge_summand_crystalline_lie p D R b N (DualNumber k) k (TrivSqZeroExt.fstHom k k k).toRingHom hsurε (GlobalTheory.FODef.sqZero k k) ((algebraMap k (TrivSqZeroExt k k)).comp tk) (spMap (algebraMap k (DualNumber k)) ≫ (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom ≫ spMap tR)) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom ≫ spMap tR) o₀ (o' j) (m' j) hsε hs₀
  have hmem : ∀ j, ∀ x ∈ Fil o₀.A, ∃ e ∈ liftFil (divided₂ (GlobalTheory.FODef.sqZero k k)) (m' j).cart,
      ∀ c, e ((GlobalTheory.FODef.constMorV k k o₀.A).pull c) = TrivSqZeroExt.inl (x c) + TrivSqZeroExt.inr (f j x c) :=
    fun j x hx => GlobalTheory.HTGlue.isFilLift_coords (m' j).cart (hm' j x hx)
  have hab := o₀.ab
  have htk : spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom ≫ spMap tR = spMap tk := ht
  have g1 := GlobalTheory.T.exists_isCompl_crystalGluedHodgeGraphFiltration p D R b N k tk _ o₀ htk d f
  have g2 := GlobalTheory.T.mem_hodgeFiltration_iff_reduction_gluedFiltration p D R b N k tk _ o₀ htk d f
  have g3 := GlobalTheory.T.crystalGluedHodgeGraph_order_stable_of_directions p D R b N k tk _ o₀ htk d f _ (fun j => (n1 j).1) (fun j => (n1 j).2.1) hmem (fun j => (n1 j).2.2)
  have g4 := GlobalTheory.T.crystalGluedHodgeGraph_isotropic_of_directions p D R b N k tk _ o₀ htk d f _ (fun j => (n1 j).1) (fun j => (n1 j).2.1) hmem (fun j => (n1 j).2.2) n2
  have g5 := GlobalTheory.T.crystalGluedHodgeGraph_lie_condition_of_directions p D R b N k tk _ o₀ htk d hd f _ (fun j => (n1 j).1) (fun j => (n1 j).2.1) hmem (fun j => (n1 j).2.2) n3
  have hsurC : Function.Surjective (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom :=
    fun a => ⟨TrivSqZeroExt.inl a, by simp⟩
  have hst : spMap (algebraMap k (TrivSqZeroExt k (Fin d → k))) ≫
      (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom ≫ spMap tR) = spMap tR := by
    rw [ht, ← GlobalTheory.Cris.spMap_comp]
  obtain ⟨o, m, hm⟩ := GlobalTheory.HTGlue.exists_obj_of_summand p D R b N hNp _ k _ hsurC (GlobalTheory.FODef.sqZero k (Fin d → k))
    tR o₀ (GlobalTheory.HTGlue.glueFil o₀.A f) g1 g2 g3 g4 g5 _ hst
  exact ⟨o, m, fun x hx => GlobalTheory.HTGlue.isFilLiftV_of_eq hab m.cart f hm hx⟩
