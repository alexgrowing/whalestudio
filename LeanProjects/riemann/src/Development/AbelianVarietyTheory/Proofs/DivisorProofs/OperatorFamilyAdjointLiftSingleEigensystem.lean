import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapRangeAdjointLeBlockSum
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesProperties
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FamilySplitOperatorsEqLabelOperatorsModels
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharacterisationPlacesPartsOfWeak
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RealizationFamilyNormalOperatorsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertHeckeOperatorsRowsRationalSelfAdjointLabelsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitPrimeHeckeTransferCompositeLiftStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MatchedSphericalPairsCommuteCompositeLiftStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory.UpSystem

theorem flatMap_cast (l : List ℕ) : List.flatMap (fun a : ℕ => [(a : ℤ)]) l = List.map (fun a : ℕ => (a : ℤ)) l := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem labIn_eq (n : ℕ) (s : List ℕ) : Formalism.IndefR.Links.labIn n s =
    List.map (fun a : ℕ => (a : ℤ)) s ++ List.replicate (n - 2 * s.length) 0 ++ List.map (fun a : ℕ => -(a : ℤ)) s.reverse := by
  unfold Formalism.IndefR.Links.labIn
  simp only [List.bind_eq_flatMap, List.pure_def, flatMap_cast, List.map_map]
  rfl

theorem labIn_pairwise {n : ℕ} {s : List ℕ} (h : Formalism.L2.Col.InertTypeOk n s) :
    (Formalism.IndefR.Links.labIn n s).Pairwise (fun a b : ℤ => b ≤ a) := by
  obtain ⟨h1, -, -⟩ := h
  rw [labIn_eq]
  refine List.pairwise_append.2 ⟨List.pairwise_append.2 ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · exact List.pairwise_map.2 (h1.imp fun h => by exact_mod_cast h)
  · exact List.pairwise_replicate.2 (Or.inr le_rfl)
  · intro a ha b hb
    obtain ⟨x, -, rfl⟩ := List.mem_map.1 ha
    rw [List.eq_of_mem_replicate hb]
    exact Int.natCast_nonneg x
  · rw [List.pairwise_map, List.pairwise_reverse]
    exact h1.imp fun h => by omega
  · intro a ha b hb
    obtain ⟨x, -, rfl⟩ := List.mem_map.1 hb
    rcases List.mem_append.1 ha with ha | ha
    · obtain ⟨y, -, rfl⟩ := List.mem_map.1 ha
      omega
    · rw [List.eq_of_mem_replicate ha]
      omega

end GlobalTheory.UpSystem

namespace GlobalTheory.UpSystem

set_option maxHeartbeats 1000000 in

theorem up_sys : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, GlobalTheory.Chain.LiftInteg D → A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → (∀ P, Good R.toRealDat A3.A.μ0 P → conjPl P = P → TwoSided R.toRealDat A3.A.μ0 P) → ((∀ t (k : A3.okI t × List ℕ), A3.heckeRI t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.R t).n y ∧ A3.heckeRI t k = A3.heckeRI t (k.1, y)) ∧ ∀ j t (k : A3.okI t × List ℕ), A3.heckeLI j t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.L j t).n y ∧ A3.heckeLI j t k = A3.heckeLI j t (k.1, y)) → ∃ Tc : (A3.rowI A3.A.μ0).OpIx → Module.End ℂ (R.HX A3.A.μ0).H, (∀ i f, R.jX A3.A.μ0 ((A3.rowI A3.A.μ0).opAll i f) = Tc i (R.jX A3.A.μ0 f)) ∧ ∀ c, ∃ x : (A3.rowI A3.A.μ0).OpIx → ℂ, ∀ w ∈ R.EEc c, ∀ i, Tc i (LinearMap.adjoint (R.Th A3.A.μ0) w) = x i • LinearMap.adjoint (R.Th A3.A.μ0) w := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hI hOk hW hEx hS hTS hInert
  have h1 := GlobalTheory.CoreThree.heckeCharacterisation_places_parts_of_weak R F hW
  have hC := h1.1 hEx
  have hSF := h1.2.1
  have hIn := h1.2.2.1
  have hEE := h1.2.2.2.2.1
  choose hX hXo _ using (GlobalTheory.T.realization_family_normal_operators R.toRealDat F.lv2 hC.lev hC.fam hC.models).1 A3.A.μ0
  have hf := GlobalTheory.AdjBlock.model_form (W := R.cX.W) (ι := Bridge.ratF D.sp.X') (ρ := R.cX.coef.ρ)
    (J := (levEnv _ R.βX (R.datXt A3.A.μ0)).J) (χ := (levEnv _ R.βX (R.datXt A3.A.μ0)).χ) (R.B.R A3.A.μ0).pres
    (R.HX A3.A.μ0) (hC.models.HX A3.A.μ0) (hC.models.jX A3.A.μ0)
  choose Tc hTc using fun i => GlobalTheory.AdjBlock.exists_cx hf.1 hf.2.1 ((A3.rowI A3.A.μ0).opAll i)
  refine ⟨Tc, fun i f => (hTc i f).symm, fun c => ?_⟩
  have hext : ∀ i (U : Module.End ℂ (R.HX A3.A.μ0).H),
      (∀ f, R.jX A3.A.μ0 ((A3.rowI A3.A.μ0).opAll i f) = U (R.jX A3.A.μ0 f)) → Tc i = U :=
    fun i U hU => GlobalTheory.AdjBlock.ext_of_span hf.2.1 fun f => (hTc i f).trans (hU f)
  have hzero : ∀ i, (A3.rowI A3.A.μ0).opAll i = 0 → Tc i = 0 := by
    intro i h0
    refine hext i 0 (fun f => ?_)
    have e1 : (A3.rowI A3.A.μ0).opAll i f = 0 := by rw [h0]; rfl
    exact (congrArg (R.jX A3.A.μ0) e1).trans ((map_zero _).trans (LinearMap.zero_apply _).symm)
  have hsys : ∀ P, Good R.toRealDat A3.A.μ0 P → ∀ cX c0, GlobalTheory.Hk3.MatchE R.toRealDat A3.A.μ0 P cX c0 → ∀ i,
      Tc i = hX P cX → ∃ a : ℂ, ∀ w ∈ R.EEc c,
        Tc i (LinearMap.adjoint (R.Th A3.A.μ0) w) = a • LinearMap.adjoint (R.Th A3.A.μ0) w := by
    intro P hP cX c0 hm i hi
    have h10 := (GlobalTheory.T.matched_spherical_pairs_commute_composite_lift R.toRealDat F.lv2 hC hS R.SF hSF A3.A.μ0 P hP cX c0 hm hX hXo).2 c
    refine ⟨_, fun w hw => (congrArg (fun U : Module.End ℂ (R.HX A3.A.μ0).H => U (LinearMap.adjoint (R.Th A3.A.μ0) w)) hi).trans
      (h10 w ((hEE c).symm ▸ hw))⟩
  have hev0 : ∀ i, Tc i = 0 → ∃ a : ℂ, ∀ w ∈ R.EEc c,
      Tc i (LinearMap.adjoint (R.Th A3.A.μ0) w) = a • LinearMap.adjoint (R.Th A3.A.μ0) w := fun i h0 =>
    ⟨0, fun w _ => (congrArg (fun U : Module.End ℂ (R.HX A3.A.μ0).H => U (LinearMap.adjoint (R.Th A3.A.μ0) w)) h0).trans
      ((LinearMap.zero_apply _).trans (zero_smul ℂ _).symm)⟩
  have key : ∀ i, ∃ a : ℂ, ∀ w ∈ R.EEc c,
      Tc i (LinearMap.adjoint (R.Th A3.A.μ0) w) = a • LinearMap.adjoint (R.Th A3.A.μ0) w := by
    rintro (⟨P, k⟩ | ⟨Q, y⟩)
    · by_cases hk : k ≤ D.sp.X'.rank
      · have hgood := ((GlobalTheory.GoodPrimes.good_primes R.toRealDat F.lv2 hC.lev).2.2.2 hC.fam A3.A.μ0 P.1 P.2).1
        have h99 := GlobalTheory.T.exists_splitPrime_heckeTransfer_compositeLift R.toRealDat F.lv2 hI hC hS A3.A.μ0 (P : A3.A.ok A3.A.μ0)
        have hso := (GlobalTheory.SplitHeckeLabel.split_ops R.toRealDat F.lv2 hC.lev hC.fam hC.models).1 A3.A.μ0 hX hXo
          (P : A3.A.ok A3.A.μ0) k hk
        exact hsys _ hgood _ _ (h99.choose_spec.1 k hk) _ (hext _ _ hso)
      · exact hev0 _ (hzero _ ((hC.fam.degR A3.A.μ0 P).2 k (not_le.1 hk)))
    · refine Or.elim (hInert.1 A3.A.μ0 ((Q : A3.okI A3.A.μ0), y)) (fun h0 => ?_) (fun hy => ?_)
      · exact hev0 (Sum.inr (Q, y)) (hzero (Sum.inr (Q, y)) h0)
      · have hgc := hIn A3.A.μ0 Q.1 Q.2
        have tie := (hW.inert.hR A3.A.μ0).some
        have hy'' : Formalism.L2.Col.InertTypeOk D.sp.X'.rank hy.choose := R.B.rankR ▸ hy.choose_spec.1
        have h78 := GlobalTheory.T.inertHeckeOperators_rows_rational_selfAdjoint_labels R.toRealDat F.lv2 hC.lev hC.fam hC.models A3.A.μ0 (A3.okI A3.A.μ0 × List ℕ)
          (fun i => R.plI i.1) (fun i => Formalism.IndefR.Links.labIn D.sp.X'.rank i.2) (A3.heckeRI A3.A.μ0)
          (fun i => Formalism.L2.Col.InertTypeOk D.sp.X'.rank i.2)
          (fun i hi => ⟨(hIn A3.A.μ0 i.1.1 i.1.2).1, (hIn A3.A.μ0 i.1.1 i.1.2).2, labIn_pairwise hi⟩) tie (Q, hy.choose) hy''
        have hm := (hTS _ hgc.1 hgc.2).1.1 (Finsupp.single (Formalism.IndefR.Links.labIn D.sp.X'.rank hy.choose) 1)
        refine hsys _ hgc.1 _ _ hm.choose_spec (Sum.inr (Q, y)) (hext _ _ fun f => ?_)
        exact (congrArg (R.jX A3.A.μ0) (LinearMap.congr_fun hy.choose_spec.2 f)).trans (h78.2.2.2 hX hXo f)
  exact ⟨fun i => (key i).choose, fun w hw i => (key i).choose_spec w hw⟩

end GlobalTheory.UpSystem
