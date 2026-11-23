import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Formalism.SharpRestriction.ParamsHeightRankConstant
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.SemisimplificationConstituents
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ResidualConstituentShape
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharpolyEqOfSemisimplificationStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsSemisimplificationOfStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimplificationUniqueUpToConjStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimplificationOfLinearEquivStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfSimpleSSupStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlockSumSemisimpleStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IrreducibleSpanAfterMapStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanRestrictEqTopOfSimpleStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIrredOfAbsIrrStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AbsIrrDistinctMapSurjectiveStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlockDecompositionFractionFieldStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EmbeddingIntegralContinuousStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImageFiniteExtensionStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DenseFrobeniusSplitPlacesStatement

noncomputable section

namespace GlobalTheory.ConstituentsCompare

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

open Polynomial Formalism.ConjugateSelfDual

def BrauerNesbitt : Prop :=
  ∀ (Γ k : Type) [Group Γ] [Field k] (a : ℕ) (ρ ρ' : Γ →* GL (Fin a) k), IsSSRep ρ → IsSSRep ρ' → (∀ g, ((ρ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k).charpoly = ((ρ' g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k).charpoly) → ∃ h : GL (Fin a) k, ∀ g, ρ' g = h * ρ g * h⁻¹

section Rep

variable {k Γ : Type} [Field k] [Group Γ]

theorem isSemisimplificationOf_iff (hBN : BrauerNesbitt) {W V : Type} [AddCommGroup W] [Module k W]
    [FiniteDimensional k W] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (s : Representation k Γ W) (ρ : Representation k Γ V) :
    IndefiniteRowSideFullHecke.SemisimplificationConstituents.IsSemisimplificationOf s ρ ↔
      IsSS s ∧ ∀ g, LinearMap.charpoly (s g) = LinearMap.charpoly (ρ g) := by
  refine ⟨fun h => ⟨h.1, GlobalTheory.T.charpoly_eq_of_semisimplification s ρ h⟩, fun ⟨h1, h2⟩ => ?_⟩
  obtain ⟨s', hs'⟩ := GlobalTheory.T.exists_semisimplification' ρ
  obtain ⟨e, he⟩ := GlobalTheory.T.semisimplification_unique_up_to_conj hBN s s' h1 hs'.1 (fun g => (h2 g).trans (GlobalTheory.T.charpoly_eq_of_semisimplification s' ρ hs' g).symm)
  exact GlobalTheory.T.semisimplification_of_linear_equiv s s' ρ e he hs'

theorem charpoly_matRep {a : ℕ} (M : Γ →* Matrix (Fin a) (Fin a) k) (g : Γ) :
    LinearMap.charpoly (matRep M g) = (M g).charpoly :=
  Matrix.charpoly_toLin' (M g)

theorem charpoly_blockSum {r t : ℕ} (ρ : Γ →* Matrix (Fin r) (Fin r) k) (χ : Fin t → (Γ →* kˣ)) (g : Γ) :
    LinearMap.charpoly (IndefiniteRowSideFullHecke.SemisimplificationConstituents.blockSum ρ χ g) =
      (ρ g).charpoly * ∏ c, (X - C ((χ c g : kˣ) : k)) := by
  have h : IndefiniteRowSideFullHecke.SemisimplificationConstituents.blockSum ρ χ g =
      LinearMap.prodMap (matRep ρ g) (Matrix.toLin' (Matrix.diagonal fun c => ((χ c g : kˣ) : k))) := by
    refine LinearMap.ext fun u => ?_
    rw [IndefiniteRowSideFullHecke.SemisimplificationConstituents.blockSum_apply]
    refine Prod.ext rfl (funext fun c => ?_)
    simp [Matrix.mulVec_diagonal]
  rw [h, LinearMap.charpoly_prodMap, charpoly_matRep, Matrix.charpoly_toLin', Matrix.charpoly_diagonal]

theorem absIrrSub_of_absIrrDistinct {a : ℕ} (ρ : Γ →* GL (Fin a) k)
    (h : AbsIrrDistinct (matRep ((Units.coeHom _).comp ρ))) (W : Submodule k (Fin a → k))
    (hW : IsIrrSub ρ W) : AbsIrrSub ρ W :=
  GlobalTheory.T.irreducible_span_after_map _ ρ W hW.2.1 hW.1 (GlobalTheory.T.span_restrict_eq_top_of_simple _ h W hW.2.1 hW.1 hW.2.2)

theorem isSSRep_map_of_absIrrDistinct {L : Type} [Field L] (f : k →+* L) {a : ℕ} (ρ : Γ →* GL (Fin a) k)
    (h : AbsIrrDistinct (matRep ((Units.coeHom _).comp ρ))) : IsSSRep (mapRep f ρ) := by
  classical
  obtain ⟨ι, _, _, Vs, hs, hint, hne, hsp, -⟩ := h
  have key := GlobalTheory.T.semisimple_of_simple_sSup (matRep ((Units.coeHom _).comp (mapRep f ρ)))
    (Set.range fun j => Submodule.span L ((fun v => f ∘ v) '' (Vs j : Set (Fin a → k)))) ?_ ?_
  · exact key
  · rintro _ ⟨j, rfl⟩
    exact (GlobalTheory.T.irreducible_span_after_map f ρ (Vs j) (hs j) (hne j) (hsp j)).2
  · set U := sSup (Set.range fun j => Submodule.span L ((fun v => f ∘ v) '' (Vs j : Set (Fin a → k))))
    have hall : ∀ v : Fin a → k, (f ∘ v) ∈ U := by
      intro v
      have hv : v ∈ ⨆ j, Vs j := by rw [hint.submodule_iSup_eq_top]; trivial
      induction hv using Submodule.iSup_induction' with
      | mem j v hv => exact (le_sSup (Set.mem_range_self j) : _ ≤ U) (Submodule.subset_span ⟨v, hv, rfl⟩)
      | zero =>
        have : (f ∘ (0 : Fin a → k)) = 0 := by funext j; simp
        rw [this]; exact U.zero_mem
      | add x y _ _ hx hy =>
        have : (f ∘ (x + y)) = f ∘ x + f ∘ y := by funext j; simp
        rw [this]; exact U.add_mem hx hy
    rw [eq_top_iff, ← (Pi.basisFun L (Fin a)).span_eq, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    have : (Pi.basisFun L (Fin a)) j = f ∘ (Pi.single j 1) := by
      funext j'; simp [Pi.single_apply]
    rw [this]; exact hall _

theorem charpoly_eq_of_dense {Y L : Type} [TopologicalSpace Y] [Field L] [Infinite L] [TopologicalSpace L]
    [IsTopologicalRing L] [T2Space L] {a : ℕ} (M M' : Y → Matrix (Fin a) (Fin a) L) (hM : Continuous M)
    (hM' : Continuous M') {S : Set Y} (hS : Dense S) (h : ∀ y ∈ S, (M y).charpoly = (M' y).charpoly) (y : Y) :
    (M y).charpoly = (M' y).charpoly := by
  refine Polynomial.funext fun c => ?_
  have := Continuous.ext_on hS (f := fun y => (Matrix.scalar (Fin a) c - M y).det)
    (g := fun y => (Matrix.scalar (Fin a) c - M' y).det)
    (continuous_const.sub hM).matrix_det (continuous_const.sub hM').matrix_det
    (fun y hy => by
      simp only [← Matrix.eval_charpoly]; rw [h y hy])
  rw [Matrix.eval_charpoly, Matrix.eval_charpoly]
  exact congrFun this y

end Rep

section Loc

variable (D : D7) (i : D.nd.Loc)

def FrobDense : Prop :=
  Dense {σ : GE D.nd | ∃ w, SplitOut D.nd i w ∧ ∃ B : ValuationSubring D.nd.Om,
    IsPlaceOver (F := D.host.E) B w ∧ IsFrob (F := D.host.E) B (normV w) σ}

theorem iota_facts : (∀ a, ‖iotaOQ D.nd D.naut i a‖ ≤ 1) ∧
    (∀ a ∈ IsLocalRing.maximalIdeal (D.nd.O i), ‖iotaOQ D.nd D.naut i a‖ < 1) ∧
    Continuous (iotaOQ D.nd D.naut i) :=
  GlobalTheory.T.embedding_integral_continuous (D.nd.l i) (D.nd.O_adic i) _ (D.naut.iotaQ_alg i)

theorem iota_inj : Function.Injective (iotaOQ D.nd D.naut i) :=
  (D.naut.iotaQ i).injective.comp (IsFractionRing.injective (D.nd.O i) (FractionRing (D.nd.O i)))

theorem cpol_mapRep {Γ A B : Type} [Group Γ] [CommRing A] [CommRing B] {a : ℕ} (f : A →+* B)
    (ρ : Γ →* GL (Fin a) A) (g : Γ) :
    IndefiniteRowSideFullHecke.ResidualConstituentShape.cpol (mapRep f ρ) g = (IndefiniteRowSideFullHecke.ResidualConstituentShape.cpol ρ g).map f :=
  Matrix.charpoly_map ((ρ g : GL (Fin a) A) : Matrix (Fin a) (Fin a) A) f

theorem mapRep_mapRep {Γ A B C : Type} [Group Γ] [CommRing A] [CommRing B] [CommRing C] {a : ℕ} (f : A →+* B)
    (f' : B →+* C) (ρ : Γ →* GL (Fin a) A) : mapRep f' (mapRep f ρ) = mapRep (f'.comp f) ρ :=
  MonoidHom.ext fun _ => Units.ext rfl

theorem coe_mapRep {Γ A B : Type} [Group Γ] [CommRing A] [CommRing B] {a : ℕ} (f : A →+* B)
    (ρ : Γ →* GL (Fin a) A) : (Units.coeHom _).comp (mapRep f ρ) = mapM f ((Units.coeHom _).comp ρ) := rfl

variable {D i}

theorem cont_map {x : D.nd.X i} {r : GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)} (hr : IsHeckeGalois D.nd i x r) :
    Continuous fun g => ((mapRep (iotaOQ D.nd D.naut i) r g : GL _ _) :
      Matrix (Fin D.R.nV) (Fin D.R.nV) (Qbar (D.nd.l i))) :=
  hr.1.matrix_map (iota_facts D i).2.2

theorem cpol_bar (hd : FrobDense D i) {x : D.nd.X i} {r : GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)}
    (hr : IsHeckeGalois D.nd i x r) {ρ : GE D.nd →* GL (Fin D.R.nV) (Qbar (D.nd.l i))}
    (hρ : IndefiniteRowSideFullHecke.ResidualConstituentShape.IsPointRepBar D.nd D.naut i x ρ) (g : GE D.nd) :
    IndefiniteRowSideFullHecke.ResidualConstituentShape.cpol ρ g = IndefiniteRowSideFullHecke.ResidualConstituentShape.cpol (mapRep (iotaOQ D.nd D.naut i) r) g := by
  refine charpoly_eq_of_dense _ _ hρ.1 (cont_map hr) hd ?_ g
  rintro σ ⟨w, hw, B, hB, hσ⟩
  refine (hρ.2.2 w hw B σ hB hσ).trans ?_
  rw [← hr.2.2 w hw B σ hB hσ]
  exact (cpol_mapRep _ r σ).symm

theorem cpol_point (hd : FrobDense D i) {x : D.nd.X i} {r r' : GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)}
    (hr : IsHeckeGalois D.nd i x r) (hr' : IsHeckeGalois D.nd i x r') (g : GE D.nd) :
    IndefiniteRowSideFullHecke.ResidualConstituentShape.cpol r g = IndefiniteRowSideFullHecke.ResidualConstituentShape.cpol r' g := by
  apply Polynomial.map_injective _ (iota_inj D i)
  rw [← cpol_mapRep, ← cpol_mapRep]
  refine charpoly_eq_of_dense _ _ (cont_map hr) (cont_map hr') hd ?_ g
  rintro σ ⟨w, hw, B, hB, hσ⟩
  refine (cpol_mapRep _ r σ).trans (Eq.trans ?_ (cpol_mapRep _ r' σ).symm)
  exact congrArg _ ((hr.2.2 w hw B σ hB hσ).trans (hr'.2.2 w hw B σ hB hσ).symm)

theorem charpoly_redK {a : ℕ} (ρ : GE D.nd →* GL (Fin a) (D.nd.O i)) (g : GE D.nd) :
    LinearMap.charpoly (IndefiniteRowSideFullHecke.SemisimplificationConstituents.redK D i ρ g) = IndefiniteRowSideFullHecke.ResidualConstituentShape.cpol (redRep D.nd i ρ) g :=
  charpoly_matRep _ g

theorem residualSame_of_common (h : IndefiniteRowSideFullHecke.SemisimplificationConstituents.ResidualCommon D i) (r : IndefiniteRowSideFullHecke.SemisimplificationConstituents.RepFam D i)
    (hr : GoodR D.nd i r) : IndefiniteRowSideFullHecke.ResidualConstituentShape.ResidualSame D.nd i r := by
  obtain ⟨s, hs⟩ := h
  intro x y g
  rw [← charpoly_redK, ← charpoly_redK, ← GlobalTheory.T.charpoly_eq_of_semisimplification _ _ (hs r hr x) g, ← GlobalTheory.T.charpoly_eq_of_semisimplification _ _ (hs r hr y) g]

theorem residualCommon_iff (hBN : BrauerNesbitt) (hd : FrobDense D i) :
    IndefiniteRowSideFullHecke.SemisimplificationConstituents.ResidualCommon D i ↔
      ∀ r, GoodR D.nd i r → IndefiniteRowSideFullHecke.ResidualConstituentShape.ResidualSame D.nd i r := by
  refine ⟨residualSame_of_common, fun h => ?_⟩
  by_cases h0 : ∃ r₀, GoodR D.nd i r₀
  · obtain ⟨r₀, hr₀⟩ := h0
    obtain ⟨x₀⟩ : Nonempty (D.nd.X i) := inferInstance
    obtain ⟨s, hs⟩ := GlobalTheory.T.exists_semisimplification' (IndefiniteRowSideFullHecke.SemisimplificationConstituents.redK D i (r₀ x₀))
    refine ⟨s, fun r hr x => (isSemisimplificationOf_iff hBN _ _).2 ⟨hs.1, fun g => ?_⟩⟩
    rw [GlobalTheory.T.charpoly_eq_of_semisimplification _ _ hs g, charpoly_redK, charpoly_redK, h r₀ hr₀ x₀ x g]
    unfold redRep
    rw [cpol_mapRep, cpol_mapRep, cpol_point hd (hr₀ x) (hr x)]
  · exact ⟨1, fun r hr => absurd ⟨r, hr⟩ h0⟩

theorem coeffLarge_of (h1 : IndefiniteRowSideFullHecke.SemisimplificationConstituents.Realised D i) (h2 : IndefiniteRowSideFullHecke.SemisimplificationConstituents.ConstituentsAbsIrrDistinct D i) :
    IndefiniteRowSideFullHecke.ResidualConstituentShape.CoeffLarge D.nd i := by
  obtain ⟨r, hr⟩ := h1
  exact ⟨r, hr, fun x W hW => absIrrSub_of_absIrrDistinct (mapRep (toK D.nd i) (r x)) (h2 r hr x) W hW⟩

theorem enlargement_of (hBN : BrauerNesbitt) (hd : FrobDense D i) (r : IndefiniteRowSideFullHecke.SemisimplificationConstituents.RepFam D i)
    (hr : GoodR D.nd i r) (h : IndefiniteRowSideFullHecke.ResidualConstituentShape.ConstituentsOver D.nd i r) :
    IndefiniteRowSideFullHecke.ResidualConstituentShape.EnlargementAt D.nd D.naut i := by
  intro ρ hρ
  have hc : ∀ x g, IndefiniteRowSideFullHecke.ResidualConstituentShape.cpol (ρ x) g = (IndefiniteRowSideFullHecke.ResidualConstituentShape.cpol (r x) g).map (iotaOQ D.nd D.naut i) :=
    fun x g => (cpol_bar hd (hr x) (hρ x) g).trans (cpol_mapRep _ _ g)
  refine ⟨?_, fun x y g n => ?_⟩
  · obtain ⟨L, hL, hmem⟩ := GlobalTheory.T.image_finite_extension (D.nd.l i) (D.naut.iotaQ i) (D.naut.iotaQ_alg i)
    refine ⟨⟨L, hL⟩, fun a => (hmem _).2 ⟨a, rfl⟩, fun x => ?_⟩
    obtain ⟨f, hf, hfc⟩ : ∃ f : KK D.nd i →+* L, Function.Surjective f ∧
        (algebraMap L (Qbar (D.nd.l i))).comp f = D.naut.iotaQ i := by
      refine ⟨(D.naut.iotaQ i).codRestrict L.toSubfield.toSubring (fun a => (hmem _).2 ⟨a, rfl⟩), ?_,
        RingHom.ext fun _ => rfl⟩
      rintro ⟨y, hy⟩
      obtain ⟨a, rfl⟩ := (hmem y).1 hy
      exact ⟨a, rfl⟩
    have hA := GlobalTheory.T.absIrrDistinct_map_surjective f hf _ (h.1 x).2
    refine ⟨mapRep f (mapRep (toK D.nd i) (r x)), ?_, ?_⟩
    swap
    · rw [coe_mapRep, coe_mapRep]
      exact hA
    have hss : IsSSRep (mapRep (D.naut.iotaQ i) (mapRep (toK D.nd i) (r x))) :=
      isSSRep_map_of_absIrrDistinct _ _ (h.1 x).2
    rw [mapRep_mapRep] at hss
    replace hss : IsSSRep (mapRep (iotaOQ D.nd D.naut i) (r x)) := hss
    have hcp := fun g => cpol_bar hd (hr x) (hρ x) g
    unfold IndefiniteRowSideFullHecke.ResidualConstituentShape.cpol at hcp
    obtain ⟨P, hP⟩ := hBN (GE D.nd) (Qbar (D.nd.l i)) D.R.nV (ρ x) (mapRep (iotaOQ D.nd D.naut i) (r x))
      (hρ x).2.1 hss hcp
    refine ⟨P, fun g => ?_⟩
    rw [← hP g, mapRep_mapRep f, hfc, mapRep_mapRep]
    rfl
  · rw [hc, hc, Polynomial.coeff_map, Polynomial.coeff_map, ← map_sub]
    refine ⟨(iota_facts D i).1 _, (iota_facts D i).2.1 _ ?_⟩
    have := congrArg (fun p => Polynomial.coeff p n) (h.2 x y g)
    unfold redRep at this
    simp only [cpol_mapRep, Polynomial.coeff_map] at this
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, this, sub_self]

theorem constituentsAt_iff (hBN : BrauerNesbitt) (hd : FrobDense D i) :
    IndefiniteRowSideFullHecke.SemisimplificationConstituents.ConstituentsAt D i ↔
      IndefiniteRowSideFullHecke.ResidualConstituentShape.CoeffLarge D.nd i ∧ (IndefiniteRowSideFullHecke.ResidualConstituentShape.EnlargementAt D.nd D.naut i ∧
        (IndefiniteRowSideFullHecke.ResidualConstituentShape.CoeffLarge D.nd i → ∀ r, GoodR D.nd i r → IndefiniteRowSideFullHecke.ResidualConstituentShape.ConstituentsOver D.nd i r)) := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    have hover : ∀ r, GoodR D.nd i r → IndefiniteRowSideFullHecke.ResidualConstituentShape.ConstituentsOver D.nd i r := fun r hr =>
      ⟨fun x => ⟨(hr x).2.1, h2 r hr x⟩, residualSame_of_common h3 r hr⟩
    refine ⟨coeffLarge_of h1 h2, ?_, fun _ => hover⟩
    obtain ⟨r, hr⟩ := h1
    exact enlargement_of hBN hd r hr (hover r hr)
  · rintro ⟨hO, -, h⟩
    have h := h hO
    obtain ⟨r, hr, -⟩ := hO
    exact ⟨⟨r, hr⟩, fun r hr x => ((h r hr).1 x).2,
      (residualCommon_iff hBN hd).2 fun r hr => (h r hr).2⟩

theorem offBlock_iff {r₀ : GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)}
    (h₀ : Continuous fun g => ((r₀ g : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i)))
    (ρ : GE D.nd →* GL (Fin D.R.r) (D.nd.O i)) :
    IndefiniteRowSideFullHecke.SemisimplificationConstituents.OffBlock D i r₀ ρ ↔ IndefiniteRowSideFullHecke.ResidualConstituentShape.IsBlockComplement D.nd i r₀ ρ := by
  constructor
  · rintro ⟨-, e, he⟩
    exact ⟨e, fun g v => (he g v).trans (IndefiniteRowSideFullHecke.SemisimplificationConstituents.blockSum_apply _ _ _ _)⟩
  · rintro ⟨e, he⟩
    refine ⟨GlobalTheory.T.block_decomposition_fraction_field (D.nd.O_adic i) _ _ e h₀ (fun g v => congrArg Prod.fst (he g v)), e, fun g v => ?_⟩
    rw [IndefiniteRowSideFullHecke.SemisimplificationConstituents.blockSum_apply]
    exact he g v

theorem charpoly_residualBlockSum (ρ : GE D.nd →* GL (Fin D.R.r) (D.nd.O i)) (g : GE D.nd) :
    LinearMap.charpoly (IndefiniteRowSideFullHecke.SemisimplificationConstituents.residualBlockSum D i ρ g) = IndefiniteRowSideFullHecke.ResidualConstituentShape.cpol (redRep D.nd i ρ) g *
      ∏ c ∈ Finset.Icc 1 D.R.t,
        (X - C (IsLocalRing.residue (D.nd.O i) ((D.nd.chi i c g : (D.nd.O i)ˣ) : D.nd.O i))) := by
  refine (charpoly_blockSum _ _ g).trans ?_
  congr 1
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.prod_Ico_eq_prod_range, Nat.add_sub_cancel,
    ← Fin.prod_univ_eq_prod_range (fun c => X - C (IsLocalRing.residue (D.nd.O i)
      ((D.nd.chi i (1 + c) g : (D.nd.O i)ˣ) : D.nd.O i)))]
  refine Finset.prod_congr rfl fun c _ => ?_
  rw [add_comm 1]
  rfl

theorem residualShape_iff (hBN : BrauerNesbitt) (r : IndefiniteRowSideFullHecke.SemisimplificationConstituents.RepFam D i)
    (ρ : GE D.nd →* GL (Fin D.R.r) (D.nd.O i)) :
    IndefiniteRowSideFullHecke.ResidualConstituentShape.ResidualShape D.nd i r ρ ↔
      IndefiniteRowSideFullHecke.SemisimplificationConstituents.ResidualShape D i r ρ ∧ AbsIrrSub (redRep D.nd i ρ) ⊤ := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    have hirr : IndefiniteRowSideFullHecke.SemisimplificationConstituents.IsIrred (IndefiniteRowSideFullHecke.SemisimplificationConstituents.redK D i ρ) := GlobalTheory.T.isIrred_of_absIrr (redRep D.nd i ρ) h2
    refine ⟨⟨fun x => (isSemisimplificationOf_iff hBN _ _).2 ⟨GlobalTheory.T.block_sum_semisimple _ _ hirr, fun g => ?_⟩, hirr, h1⟩, h2⟩
    rw [charpoly_residualBlockSum, charpoly_redK, h3 x g]
  · rintro ⟨⟨h1, -, h3⟩, h4⟩
    refine ⟨h3, h4, fun x g => ?_⟩
    rw [← charpoly_residualBlockSum, ← charpoly_redK, GlobalTheory.T.charpoly_eq_of_semisimplification _ _ (h1 x) g]

end Loc

theorem typeStanding_iff (D : D7) : IndefiniteRowSideFullHecke.SemisimplificationConstituents.TypeHypothesis D ↔ IndefiniteRowSideFullHecke.ResidualConstituentShape.TypePrimeSizes D :=
  ⟨fun h => ⟨h.1, h.2, D.ntypes.BB_disj⟩, fun h => ⟨h.1, h.2.1⟩⟩

def CoeffTie (D : D7) : Prop := ∀ i, IndefiniteRowSideFullHecke.ResidualConstituentShape.CoeffLarge D.nd i

def LiftPointGood (D : D7) : Prop := ∀ i x, IndefiniteRowSideFullHecke.SemisimplificationConstituents.GoodRowPoint D i x → x ∈ D.nd.Zgood i

def GoodPointLift (D : D7) : Prop := ∀ i, ∀ x ∈ D.nd.Zgood i, IndefiniteRowSideFullHecke.SemisimplificationConstituents.GoodRowPoint D i x

def ResidualAbsIrr (D : D7) : Prop :=
  IndefiniteRowSideFullHecke.SemisimplificationConstituents.TypeHypothesis D → ∀ i r, GoodR D.nd i r → ∀ x₀ ∈ D.nd.Zgood i, ∀ ρ,
    IndefiniteRowSideFullHecke.SemisimplificationConstituents.OffBlock D i (r x₀) ρ → AbsIrrSub (redRep D.nd i ρ) ⊤

theorem constituents_iff (hBN : BrauerNesbitt) (D : D7) (hd : ∀ i, FrobDense D i) :
    IndefiniteRowSideFullHecke.SemisimplificationConstituents.Constituents_at D ↔ CoeffTie D ∧ IndefiniteRowSideFullHecke.ResidualConstituentShape.Constituents_at D := by
  unfold IndefiniteRowSideFullHecke.SemisimplificationConstituents.Constituents_at CoeffTie IndefiniteRowSideFullHecke.ResidualConstituentShape.Constituents_at
  rw [← forall_and]
  exact forall_congr' fun i => constituentsAt_iff hBN (hd i)

theorem shape_second_of_first (hBN : BrauerNesbitt) (D : D7) (hO : CoeffTie D) (hg : LiftPointGood D)
    (h : IndefiniteRowSideFullHecke.ResidualConstituentShape.ResidualShape_at D) : IndefiniteRowSideFullHecke.SemisimplificationConstituents.ResidualShape_at D := by
  intro hT i r hr x₀ hx₀
  obtain ⟨⟨ρ, hρ⟩, h2⟩ := h ((typeStanding_iff D).1 hT) i (hO i) r hr x₀ (hg i x₀ hx₀)
  exact ⟨⟨ρ, (offBlock_iff (hr x₀).1 ρ).2 hρ⟩, fun ρ hρ =>
    ((residualShape_iff hBN r ρ).1 (h2 ρ ((offBlock_iff (hr x₀).1 ρ).1 hρ))).1⟩

theorem residualAbsIrr_of_first (D : D7) (hO : CoeffTie D) (h : IndefiniteRowSideFullHecke.ResidualConstituentShape.ResidualShape_at D) :
    ResidualAbsIrr D := fun hT i r hr x₀ hx₀ ρ hρ =>
  ((h ((typeStanding_iff D).1 hT) i (hO i) r hr x₀ hx₀).2 ρ ((offBlock_iff (hr x₀).1 ρ).1 hρ)).2.1

theorem shape_first_of_second (hBN : BrauerNesbitt) (D : D7) (hg : GoodPointLift D)
    (h : IndefiniteRowSideFullHecke.SemisimplificationConstituents.ResidualShape_at D) (ha : ResidualAbsIrr D) : IndefiniteRowSideFullHecke.ResidualConstituentShape.ResidualShape_at D := by
  intro hT i _ r hr x₀ hx₀
  have hT' := (typeStanding_iff D).2 hT
  obtain ⟨⟨ρ, hρ⟩, h2⟩ := h hT' i r hr x₀ (hg i x₀ hx₀)
  refine ⟨⟨ρ, (offBlock_iff (hr x₀).1 ρ).1 hρ⟩, fun ρ hρ => ?_⟩
  have hρ' := (offBlock_iff (hr x₀).1 ρ).2 hρ
  exact (residualShape_iff hBN r ρ).2 ⟨h2 ρ hρ', ha hT' i r hr x₀ hx₀ ρ hρ'⟩

theorem compare (hBN : BrauerNesbitt) (hC : GlobalTheory.TwSys.Cheb) (D : D7) :
    (IndefiniteRowSideFullHecke.SemisimplificationConstituents.TypeHypothesis D ↔ IndefiniteRowSideFullHecke.ResidualConstituentShape.TypePrimeSizes D) ∧
    (IndefiniteRowSideFullHecke.SemisimplificationConstituents.Constituents_at D ↔ CoeffTie D ∧ IndefiniteRowSideFullHecke.ResidualConstituentShape.Constituents_at D) ∧
    (∀ i (r : IndefiniteRowSideFullHecke.SemisimplificationConstituents.RepFam D i), GoodR D.nd i r → ∀ x ρ,
      (IndefiniteRowSideFullHecke.SemisimplificationConstituents.OffBlock D i (r x) ρ ↔ IndefiniteRowSideFullHecke.ResidualConstituentShape.IsBlockComplement D.nd i (r x) ρ)) ∧
    (∀ i r ρ, IndefiniteRowSideFullHecke.ResidualConstituentShape.ResidualShape D.nd i r ρ ↔
      IndefiniteRowSideFullHecke.SemisimplificationConstituents.ResidualShape D i r ρ ∧ AbsIrrSub (redRep D.nd i ρ) ⊤) ∧
    (LiftPointGood D → CoeffTie D ∧ IndefiniteRowSideFullHecke.ResidualConstituentShape.ConstituentsAndShape_at D →
      IndefiniteRowSideFullHecke.SemisimplificationConstituents.ConstituentsAndShape_at D ∧ ResidualAbsIrr D) ∧
    (GoodPointLift D → IndefiniteRowSideFullHecke.SemisimplificationConstituents.ConstituentsAndShape_at D ∧ ResidualAbsIrr D →
      CoeffTie D ∧ IndefiniteRowSideFullHecke.ResidualConstituentShape.ConstituentsAndShape_at D) := by
  have hc := constituents_iff hBN D (fun i => GlobalTheory.T.dense_frobenius_split_places hC D.nd i)
  refine ⟨typeStanding_iff D, hc, fun i r hr x ρ => offBlock_iff (hr x).1 ρ,
    fun i r ρ => residualShape_iff hBN r ρ, ?_, ?_⟩
  · rintro hg ⟨hO, h1, h2⟩
    exact ⟨⟨hc.2 ⟨hO, h1⟩, shape_second_of_first hBN D hO hg h2⟩, residualAbsIrr_of_first D hO h2⟩
  · rintro hg ⟨⟨h1, h2⟩, ha⟩
    exact ⟨(hc.1 h1).1, (hc.1 h1).2, shape_first_of_second hBN D hg h2 ha⟩

theorem compare_family (hBN : BrauerNesbitt) (hC : GlobalTheory.TwSys.Cheb) {eps : ℝ} (Fm : FamP eps)
    (h : ∀ x (j : Fm.Ix x), CoeffTie (Fm.D x j) ∧ LiftPointGood (Fm.D x j) ∧ GoodPointLift (Fm.D x j) ∧
      ResidualAbsIrr (Fm.D x j)) :
    IndefiniteRowSideFullHecke.ResidualConstituentShape.ConstituentsAndShapeF Fm ↔ IndefiniteRowSideFullHecke.SemisimplificationConstituents.ConstituentsAndShapeF Fm := by
  refine exists_congr fun x0 => forall_congr' fun x => forall_congr' fun _ => forall_congr' fun j => ?_
  obtain ⟨h1, h2, h3, h4⟩ := h x j
  obtain ⟨-, -, -, -, c1, c2⟩ := compare hBN hC (Fm.D x j)
  exact ⟨fun a => (c1 h2 ⟨h1, a⟩).1, fun b => (c2 h3 ⟨b, h4⟩).2⟩

end GlobalTheory.ConstituentsCompare

end
