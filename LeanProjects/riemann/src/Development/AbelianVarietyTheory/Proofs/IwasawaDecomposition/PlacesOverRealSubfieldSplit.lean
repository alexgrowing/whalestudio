import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDimensionalForms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDoubleCosetsDefiniteUnitaryMaximalLevelStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitPlOfNotIsConjPl
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameValuesGaloisCharFormResidueUnitCharacterStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSplitPlaceOfIsSplitPlaceCmFieldStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComapRealSubfieldEqIffEqOrIsConjPlaceStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsResidueHomZmodAtTypePlaceStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChosenHalfSplitPlacesMeetsConjugatePairOnceStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlacesAvoidAuxiliaryStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FifteenNotMemAndDeltaInertiaOrderDividesFifteenPStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AuxiliaryPrimePlacesNonemptyStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLevelGroupWithCharacterAtTypePlacesStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.LevForms

theorem typeSpF_finiteDimensional : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (K : Type) [Field K] {W : Type} [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] (ρ : Representation K (GQ L n) W) (J : Subgroup (GAf L n)) (χ : J →* Kˣ),
    (∃ N : ℕ, 0 < N ∧ ∀ κ, NG.Cong L n N κ → ∃ h : κ ∈ J, χ ⟨κ, h⟩ = 1) →
    FiniteDimensional K ↥(NX.TypeSpF L n K ρ J χ) := by
  intro L _ _ _ n K _ W _ _ _ ρ J χ hJ
  classical
  obtain ⟨N, hN, hNJ⟩ := hJ
  obtain ⟨T, hT⟩ := GlobalTheory.T.finite_doubleCosets_definiteUnitary_maximalLevel L n
  obtain ⟨Jc, hJc⟩ := GlobalTheory.AlgFormsFin.exists_cover L n hN
  let Φ : ↥(NX.TypeSpF L n K ρ J χ) →ₗ[K] (↥(T ×ˢ Jc) → W) :=
    { toFun := fun f p => (f : GAf L n → W) (p.1.1 * p.1.2)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine Module.Finite.of_injective Φ ((injective_iff_map_eq_zero Φ).2 fun f hf => ?_)
  refine Subtype.ext (funext fun g => ?_)
  obtain ⟨γ, t, u, ht, hu, rfl⟩ := hT g
  obtain ⟨j, hj, κ, hκ, rfl⟩ := hJc u hu
  have h0 : (f : GAf L n → W) (t * j) = 0 :=
    congrFun hf ⟨(t, j), Finset.mem_product.2 ⟨ht, hj⟩⟩
  obtain ⟨hκJ, hκ1⟩ := hNJ κ hκ
  have e : (γ : GAf L n) * t * (j * κ) = ((γ : GAf L n) * (t * j)) * κ := by simp only [mul_assoc]
  show (f : GAf L n → W) _ = 0
  rw [e, f.2.2 ⟨κ, hκJ⟩, hκ1, f.2.1 γ, h0, map_zero, Units.val_one, one_smul]

theorem levDatum_forms : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb)
    (A : SideA D cf jE) (S : RatDat D.ntw) (In : RatIn D S)
    (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (b0 b1 : Big D)
    (Sx : Finset (PlE D.host)) (T : TwR D.LL0 D.nd) (Sp : RingSpec D cf b0 b1 Sx T),
    (∀ v, NG.OverPl (Pq v) v) →
    (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) →
    ∀ (wt : WtData D T), (∀ i j b, 1 ≤ j → j ≤ D.R.m → (wt.rhoW i j b).IsIrreducible ∧
      NX.IsAlgWeightF D.host.E D.R.nV (FractionRing (T.O i)) (wt.rhoW i j b)) →
    ∀ (hE : IsEmpty D.nd.Loc) (F : TwF T) (i : T.Tw) (j : ℕ) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host))
      (ψ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* (T.Ok i k)ˣ), 1 ≤ j → j ≤ D.R.m →
      Formalism.MainNotions.NAdm.TWSet (T.ntw hE F (TwL.empty T)) i Q →
      (∀ P ∈ Q, P ∉ T.pD i ∧ ∀ k' : Fin 2, P ∉ placesOver D.host.E (D.host.g k')) →
      IsOpen (ψ.ker : Set (Formalism.ConjugateSelfDual.G D.host.E D.nd.Om)) → AntiHom T.cc ψ → (∀ σ, ∃ N : ℕ, ψ σ ^ (T.l i ^ N) = 1) →
      (∀ P, P ∉ Q → ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A P → ∀ σ ∈ Ine (F := D.host.E) A, ψ σ = 1) →
      ∃ L : LevT D T i k, LevLawsT D T Pq In.θ i j b k Q ψ L ∧
        FiniteDimensional (FractionRing (T.Ok i k))
          ↥(NX.TypeSpF D.host.E D.R.nV (FractionRing (T.Ok i k)) (rhoKT D T wt i j b k) L.J L.χ) := by
  intro hA D cf jE A S In Pq b0 b1 Sx T Sp hPq hsplit wt hwt hE F i j b k Q ψ hj1 hj2 hQ hQ2 hopen hanti hl hunr
  classical
  have hQs : ∀ P ∈ Q, IsSplitPl D.host P := fun P hP => (hQ P hP).1
  have hQl : ∀ P ∈ Q, P ∉ placesOver D.host.E (T.l i) := fun P hP => (hQ P hP).2
  have hDs : ∀ P ∈ T.pD i, IsSplitPl D.host P := by
    intro P hP
    have h := T.pD_eq i
    have hP' : P ∈ placesOver D.host.E (if T.l i = D.host.pde then D.host.pde' else D.host.pde) := by
      rw [← h]; exact hP
    split_ifs at hP' with hh
    · exact hsplit P (Or.inr hP')
    · exact hsplit P (Or.inl hP')
  obtain ⟨P₀, hP₀⟩ := GlobalTheory.T.auxiliaryPrimePlaces_nonempty D T i
  haveI : Nonempty (SplitPlace D.host.E) := ⟨(GlobalTheory.T.exists_splitPlace_of_isSplitPlace_cmField D P₀ (hDs P₀ hP₀)).choose⟩
  let sp : PlE D.host → SplitPlace D.host.E := fun P =>
    if h : IsSplitPl D.host P then (GlobalTheory.T.exists_splitPlace_of_isSplitPlace_cmField D P h).choose else Classical.arbitrary _
  have hsp : ∀ P, IsSplitPl D.host P → (sp P).w = P := fun P h => by
    simp only [sp, dif_pos h]; exact (GlobalTheory.T.exists_splitPlace_of_isSplitPlace_cmField D P h).choose_spec
  have hspw : ∀ P, (P ∈ qpOf D Pq Q ∨ P ∈ qpOf D Pq (T.pD i) ∨ ∃ kv, P = NX.pG D kv) → (sp P).w = P := by
    rintro P (h | h | ⟨kv, rfl⟩)
    · exact hsp P (hQs P (qpOf_sub D Pq Q h))
    · exact hsp P (hDs P (qpOf_sub D Pq _ h))
    · exact hsp _ (GlobalTheory.FixedPlaceSplit.isSplitPl_plGw D kv.1 kv.2)
  obtain ⟨hv, hdisj1, hdisj2, hpG⟩ := GlobalTheory.T.split_places_avoid_auxiliary D T i Q Pq sp hPq hQs hQ2 hDs hspw
  let redG : ∀ kv : (Σ kk : Fin 2, D.nd.PlG kk),
      (sp (NX.pG D kv)).v.adicCompletionIntegers (maximalRealSubfield D.host.E) →+* ZMod (D.host.g kv.1) := fun kv =>
    (GlobalTheory.T.exists_residueHom_zmod_at_typePlace D kv (sp (NX.pG D kv)) (hspw _ (Or.inr (Or.inr ⟨kv, rfl⟩)))).some
  have hψt := fun P (hP : P ∈ qpOf D Pq Q) =>
    GlobalTheory.T.tameValues_galoisChar_form_residue_unit_character ψ P 1 (T.l i) hopen (by simpa [placesOver] using hQl P (qpOf_sub D Pq Q hP)) (fun A _ σ _ => hl σ)
  have hδt := fun P (hP : P ∈ qpOf D Pq (T.pD i)) =>
    GlobalTheory.T.tameValues_galoisChar_form_residue_unit_character (T.delta i) P (if b then 1 else -1) 15 (T.delta_open i) (GlobalTheory.T.fifteen_not_mem_and_delta_inertia_order_divides_fifteen_pow D T i P (qpOf_sub D Pq _ hP)).1
      (GlobalTheory.T.fifteen_not_mem_and_delta_inertia_order_divides_fifteen_pow D T i P (qpOf_sub D Pq _ hP)).2
  obtain ⟨J, χ, hJo, hhyp, hJm, hchi⟩ := GlobalTheory.T.exists_levelGroup_with_character_at_type_places D T In.θ i j b k Q ψ (qpOf D Pq Q) (qpOf D Pq (T.pD i)) sp redG
    hspw hv hdisj1 hdisj2 hpG (qpOf_sub D Pq Q) (qpOf_sub D Pq _) hψt hδt
  obtain ⟨hQc, hQn⟩ := GlobalTheory.T.chosenHalf_splitPlaces_meets_conjugatePair_once D Pq hPq Q hQs
  obtain ⟨hDc, hDn⟩ := GlobalTheory.T.chosenHalf_splitPlaces_meets_conjugatePair_once D Pq hPq (T.pD i) hDs
  refine ⟨⟨J, χ, qpOf D Pq Q, qpOf D Pq (T.pD i), sp, redG⟩,
    ⟨hJo, hhyp, rfl, rfl, qpOf_sub D Pq Q, hQc, hQn, qpOf_sub D Pq _, hDc, hDn, hspw, hJm, hchi⟩, ?_⟩
  exact typeSpF_finiteDimensional D.host.E D.R.nV _ (rhoKT D T wt i j b k) J χ hJo

end GlobalTheory.LevForms
