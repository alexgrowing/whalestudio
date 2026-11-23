import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteSupport
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowestKTypesJointShapeBlockUnitary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GluingLawHolds
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFockPolynomialIsoUnitaryPair
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesPureInnerProductsTensorProduct
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubstitutionTotalDegreeLe
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultTEqZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmPureTensorOOfFinite
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NoIntertwinerSmallerFockToDiscreteSeries
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EquivariantMapCarriesGelfandInvariantToFunction
import Development.AbelianVarietyTheory.Statements.HaarFundamentalDomain.ExistsHaarFundDom
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ScalarOfComm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemRangeMapSubtypeOfContr
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.KerLeFinset
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InclTprodUpdate
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsKActOfStable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AbsIrrOfEquiv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryImage
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteSupportOfAdmissible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqZeroOfContr
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoverKerOfDown
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocKerOfCoverKer
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEmbeddingSkew
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCuspGrowOfMemSpan
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableOfContinuous
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SignBlockDeterminantNeZeroOfMemMaxCompact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.KMeanMemKFinOfCoefFam
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableOnMulRight
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ItEqSumKMean

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open Matrix MeasureTheory GlobalTheory.Chain GlobalTheory.Chain.RealIt
open GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension (kFin KVec KMap maxCpt rep_mem_kFin)
open scoped TensorProduct InnerProductSpace Classical

namespace GlobalTheory.Chain.IoLift

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Algebra

variable {ι : Type} {P Y K : ι → Type} [∀ i, AddCommGroup (P i)] [∀ i, Module ℂ (P i)] [∀ i, AddCommGroup (Y i)]
  [∀ i, Module ℂ (Y i)] [∀ i, AddCommGroup (K i)] [∀ i, Module ℂ (K i)] {Z : Type} [AddCommGroup Z] [Module ℂ Z]

def slice (B : MultilinearMap ℂ P (MultilinearMap ℂ Y Z)) (i : ι) (p : ∀ j, P j) (y : ∀ j, Y j) :
    P i →ₗ[ℂ] Y i →ₗ[ℂ] Z :=
  LinearMap.mk₂ ℂ (fun x z => B (Function.update p i x) (Function.update y i z)) (fun _ _ _ => by simp)
    (fun _ _ _ => by simp) (fun _ _ _ => by simp) fun _ _ _ => by simp

theorem slice_apply (B : MultilinearMap ℂ P (MultilinearMap ℂ Y Z)) (i : ι) (p : ∀ j, P j) (y : ∀ j, Y j) (x : P i)
    (z : Y i) : slice B i p y x z = B (Function.update p i x) (Function.update y i z) := rfl

def IsContr (i : ι) (L : (⨂[ℂ] j, K j) →ₗ[ℂ] K i) : Prop := ∀ f : Module.End ℂ (K i), L ∘ₗ intersection_update_fsHerm_neg_one i f = f ∘ₗ L

variable [Fintype ι]

theorem eq_zero_of_isContr (i : ι) {x : ⨂[ℂ] j, K j} (h : ∀ L, IsContr i L → L x = 0) : x = 0 := by
  obtain ⟨z, rfl⟩ := GlobalTheory.Chain.IoLift.mem_range_map_subtype_of_contr ι K (fun j => if j = i then ⊥ else ⊤) x fun j L hL => by
    by_cases e : j = i
    · subst e; rw [if_pos rfl, h L hL]; exact zero_mem _
    · rw [if_neg e]; trivial
  refine LinearMap.congr_fun (g := 0) (PiTensorProduct.ext (MultilinearMap.ext fun v => ?_)) z
  have := (v i).2
  simp only [if_true, Submodule.mem_bot] at this
  simp only [LinearMap.compMultilinearMap_apply, PiTensorProduct.map_tprod, LinearMap.zero_apply]
  exact MultilinearMap.map_coord_zero _ i this

theorem exists_factor {G : ι → Type} (c : ∀ i, G i → Module.End ℂ (P i)) (a : ∀ i, G i → Module.End ℂ (K i))
    (ha : ∀ i, AbsIrr (a i)) (I : MultilinearMap ℂ P (MultilinearMap ℂ Y (⨂[ℂ] j, K j)))
    (B : MultilinearMap ℂ P (MultilinearMap ℂ Y Z)) (h0 : ∃ p y, I p y ≠ 0)
    (he : ∀ i g p y, I (Function.update p i (c i g (p i))) y = intersection_update_fsHerm_neg_one i (a i g) (I p y))
    (hk : ∀ i L, IsContr i L → ∀ p y, (slice I i p y).compr₂ L ≠ 0 →
      (∀ L', IsContr i L' → ∀ p' y', KerLe (fun x z => (slice I i p y).compr₂ L x z)
        fun x z => (slice I i p' y').compr₂ L' x z) ∧
      ∀ p' y', KerLe (fun x z => (slice I i p y).compr₂ L x z) fun x z => slice B i p' y' x z) :
    (∃ T : (⨂[ℂ] j, K j) →ₗ[ℂ] Z, ∀ p y, T (I p y) = B p y) ∧ Submodule.span ℂ {x | ∃ p y, I p y = x} = ⊤ := by
  obtain ⟨p₀, y₀, h0⟩ := h0
  have h1 : ∀ i, ∃ L, IsContr i L ∧ L (I p₀ y₀) ≠ 0 := fun i => by
    by_contra hn
    exact h0 (eq_zero_of_isContr i fun L hL => by_contra fun h => hn ⟨L, hL, h⟩)
  choose L hL hL0 using h1
  let A : ∀ i, P i →ₗ[ℂ] Y i →ₗ[ℂ] K i := fun i => (slice I i p₀ y₀).compr₂ (L i)
  have hA0 : ∀ i, A i (p₀ i) (y₀ i) ≠ 0 := fun i => by
    simpa only [A, LinearMap.compr₂_apply, slice_apply, Function.update_eq_self] using hL0 i
  have hA : ∀ i, A i ≠ 0 := fun i e => hA0 i (by rw [e]; rfl)
  have hAe : ∀ i g x z, A i (c i g x) z = a i g (A i x z) := fun i g x z => by
    have := he i g (Function.update p₀ i x) (Function.update y₀ i z)
    rw [Function.update_idem, Function.update_self] at this
    simp only [A, LinearMap.compr₂_apply, slice_apply, this]
    exact LinearMap.congr_fun (hL i (a i g)) _
  have hAs : ∀ i, Submodule.span ℂ {x | ∃ p y, A i p y = x} = ⊤ := fun i => by
    refine ((ha i).1 _ fun g x hx => ?_).resolve_left fun e => hA0 i (Submodule.span_eq_bot.1 e _ ⟨_, _, rfl⟩)
    refine Submodule.mem_comap.1 ((Submodule.span_le (p := Submodule.comap (a i g) _)).2 ?_ hx)
    rintro _ ⟨p, y, rfl⟩
    exact Submodule.subset_span ⟨_, _, hAe i g p y⟩
  obtain ⟨hs, hf⟩ := GlobalTheory.Chain.IoLift.Factor.factor ι K P Y A hAs
  obtain ⟨T, hT⟩ := hf Z B fun i => (hk i (L i) (hL i) p₀ y₀ (hA i)).2
  obtain ⟨Φ, hΦ⟩ := hf _ I fun i p y n x z h => eq_zero_of_isContr i fun L' hL' => by
    rw [map_sum]
    exact (hk i (L i) (hL i) p₀ y₀ (hA i)).1 L' hL' p y n x z h
  obtain ⟨r, hr⟩ := GlobalTheory.Chain.IoLift.Scal.scalar_of_comm ι K G a ha Φ fun i g => by
    refine LinearMap.ext_on hs ?_
    rintro _ ⟨p, y, rfl⟩
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hΦ, ← he, ← hΦ, position_tprod]
    congr 2
    funext j
    by_cases e : j = i
    · subst e; simp [hAe]
    · simp [e]
  have hI : ∀ p y, I p y = r • PiTensorProduct.tprod ℂ fun i => A i (p i) (y i) := fun p y => by
    rw [← hΦ, hr]; rfl
  have hr0 : r ≠ 0 := fun e => h0 (by rw [hI, e, zero_smul])
  refine ⟨⟨r⁻¹ • T, fun p y => ?_⟩, eq_top_iff.2 (hs ▸ Submodule.span_le.2 ?_)⟩
  · rw [hI, map_smul, LinearMap.smul_apply, smul_smul, mul_inv_cancel₀ hr0, one_smul, hT]
  · rintro _ ⟨p, y, rfl⟩
    rw [SetLike.mem_coe, ← Submodule.smul_mem_iff _ hr0, ← hI]
    exact Submodule.subset_span ⟨p, y, rfl⟩

end Algebra

open GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix GlobalTheory.PointAtPlaceHom

variable {D : D7} {V W : HSp D} {S S' : D.what₂.Tau → SPar}

theorem exists_local {X : ProvA} (hX : ChosenSeries X) (h3 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisUpDownLine X) (h5 : GlobalTheory.Published.HarishChandraModules)
    (hB : ModelsAreCoverSeries D) (M : DSModel V S) (M' : DSModel W S') (τ : D.what₂.Tau) {t : ℕ}
    {al be ga de : List ℚ} (hd : Formalism.MainNotions.SchurIrreducible.DataAR t al be ga de) {aS aT : ℚ}
    (hS : S τ = dualPar (signed (al ++ be) (ga ++ de) aT))
    (hS' : S' τ = dualPar (signed (al ++ block t ++ de) (ga ++ be) aS)) :
    (kFin M τ ≤ M.sm τ ∧ kFin M' τ ≤ M'.sm τ) ∧ ∃ a a', IsKAct M τ a ∧ IsKAct M' τ a' ∧
      AbsIrr (fun X : lieAt V τ => a X) ∧ LocKer M M' τ aS aT a' := by
  obtain ⟨-, p1, p2, -⟩ := GlobalTheory.LowestTypes.lowest_types t al be ga de hd.1
  have ht := hd.1.1
  have hn := hd.1.2.1
  obtain ⟨⟨e, he⟩, m, hm, hU⟩ := hB.1 X V S M τ (al.length + be.length) (ga.length + de.length) _ _ aT
    ⟨by omega, by simp, by simp, p1, hX _ _ _ p1, hS⟩
  obtain ⟨⟨e', he'⟩, m', hm', hU'⟩ := hB.2 X W S' M' τ (al.length + de.length + t) (ga.length + be.length) _ _ aS
    ⟨by omega, by simp [block]; omega, by simp, p2, hX _ _ _ p2, hS'⟩
  obtain ⟨U, hU⟩ := hU e he
  obtain ⟨U', hU'⟩ := hU' e' he'
  obtain ⟨κ, hκ⟩ := PolyIso.exists_isPolyIso _ _ _ _ _ _ _ _ e e' he he'
  obtain ⟨s, a, ha⟩ := GlobalTheory.Chain.IoLift.kFin_smooth_isKAct D V S M τ _ _ _ _ _ _ _ hU
  obtain ⟨s', a', ha'⟩ := GlobalTheory.Chain.IoLift.kFin_smooth_isKAct D W S' M' τ _ _ _ _ _ _ _ hU'
  have i1 := GlobalTheory.SmallerSource.discrete_series_gk_admissible_irreducible X (h5.admQ5_of_harishChandraModules X) (by omega) (lamA al be ga de)
  have i2 := GlobalTheory.SmallerSource.discrete_series_gk_admissible_irreducible X (h5.admQ5_of_harishChandraModules X) (by omega) (lamA' t al be ga de)
  refine ⟨⟨s, s'⟩, a, a', ha, ha', GlobalTheory.KFinIrr.absIrr_kFin D V S M τ _ _ _ _ _ m U.toLinearEquiv a hU i1.2 i1.1 ha, ?_⟩
  exact GlobalTheory.Chain.IoLift.KerTransfer.locKer_of_coverKer D V W S S' M M' τ _ _ _ _ _ _ _ _ e e' m m' aS aT U U' κ a' hm' hU hU' hκ ha'
    (GlobalTheory.Chain.IoLift.CoverKernel.coverKer_of_down X _ _ _ _ _ _ (h3.1 t al be ga de hd).2.1 i1.2 (GlobalTheory.Chain.IoLift.UImg.unitaryImage _ _ _ _)
      (GlobalTheory.Chain.IoLift.finiteSupport_of_admissible _ _ _ _ _ _ i2.1) GlobalTheory.Chain.IoLift.TensorFormProof.tensorForm)

variable {M : DSModel V S} {M' : DSModel W S'}

theorem frame_mem (M : DSModel V S) (τ : D.what₂.Tau) {k : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hk : k ∈ Formalism.REAL.Kset (M.ε τ)) : (M.fr τ)⁻¹ * k * M.fr τ ∈ maxCpt M τ := by
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  change M.fr τ * ((M.fr τ)⁻¹ * k * M.fr τ) * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ)
  rwa [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_right _ _ hd, Matrix.mul_nonsing_inv_cancel_left _ _ hd]

theorem mem_range_inclK (h : KSm M) (x : SmT M)
    (hx : ∀ τ, ∃ E : Submodule ℂ (⨂[ℂ] τ, M.H τ), FiniteDimensional ℂ E ∧
      ∀ k ∈ maxCpt M τ, actT M τ k (inclT M x) ∈ E) : x ∈ LinearMap.range (inclK h) := by
  obtain ⟨z, hz⟩ := GlobalTheory.Chain.IoLift.mem_range_map_subtype_of_contr _ M.H (kFin M) (inclT M x) fun τ L hL => by
    obtain ⟨E, hE, hk⟩ := hx τ
    have hle : Submodule.span ℂ ((fun k => M.σ τ k (L (inclT M x))) '' Formalism.REAL.Kset (M.ε τ)) ≤ E.map L := by
      rw [Submodule.span_le]
      rintro _ ⟨k, hk', rfl⟩
      refine ⟨_, hk _ (frame_mem M τ hk'), (LinearMap.congr_fun (hL (M.rep τ _ : M.H τ →ₗ[ℂ] M.H τ)) _).trans ?_⟩
      exact congrArg (fun A : M.H τ →L[ℂ] M.H τ => A _) (GlobalTheory.SmVec.trRep_conj (σ := M.σ τ) (M.fr_unit τ) k)
    have hσ := (M.ds τ).2.2.1
    have hJ := (Formalism.REAL.maximal_compact_facts _ (M.ε τ)).1
    refine ⟨_, Submodule.finiteDimensional_of_le hle, Submodule.subset_span ⟨1, ⟨one_mem _, by simp⟩, ?_⟩,
      fun g hg v hv => ?_⟩
    · simp only [hσ.1.1]; rfl
    · refine Submodule.mem_comap.1 ((Submodule.span_le (p := Submodule.comap (M.σ τ g : M.H τ →ₗ[ℂ] M.H τ) _)).2 ?_ hv)
      rintro _ ⟨k, hk', rfl⟩
      refine Submodule.subset_span ⟨g * k, Formalism.REAL.Kset_mul _ hg hk', ?_⟩
      simp only [hσ.1.2 g (hJ g hg) k (hJ k hk')]; rfl
  refine ⟨z, (tensorLaw D V S M).inj (Eq.trans ?_ hz)⟩
  rw [inclT, inclK, ← LinearMap.comp_apply, ← PiTensorProduct.map_comp]
  rfl

theorem derT_unique {τ : D.what₂.Tau} {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} {x y y' : SmT M} (h : DerT M τ X x y)
    (h' : DerT M τ X x y') : y = y' := by
  refine (tensorLaw D V S M).inj (sub_eq_zero.1 ((tensorLaw D V S M).sep _ fun w => ?_))
  rw [map_sub, (h w).unique (h' w), sub_self]

theorem mem_span_of_average {P Z : Type} [AddCommGroup P] [Module ℂ P] [AddCommGroup Z] [Module ℂ Z]
    (G : P →ₗ[ℂ] SmT M →ₗ[ℂ] Z) (h : KSm M)
    (hs : ∀ τ φ (v : M.Vec), ∃ (n : ℕ) (φs : Fin n → P) (u : Fin n → M.sm τ), (∀ i, (u i : M.H τ) ∈ kFin M τ) ∧
      G φ (PiTensorProduct.tprod ℂ v) = ∑ i, G (φs i) (PiTensorProduct.tprod ℂ (Function.update v τ (u i))))
    (φ : P) (x : SmT M) : G φ x ∈ Submodule.span ℂ {z | ∃ φ y, G φ (inclK h y) = z} := by
  have key : ∀ (s : Finset D.what₂.Tau) φ (v : M.Vec), (∀ τ ∉ s, (v τ : M.H τ) ∈ kFin M τ) →
      G φ (PiTensorProduct.tprod ℂ v) ∈ Submodule.span ℂ {z | ∃ φ y, G φ (inclK h y) = z} := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      refine fun φ v hv => Submodule.subset_span ⟨φ, PiTensorProduct.tprod ℂ fun τ => ⟨v τ, hv τ (by simp)⟩, ?_⟩
      rw [inclK, PiTensorProduct.map_tprod]
      rfl
    | insert τ s _ ih =>
      intro φ v hv
      obtain ⟨n, φs, u, hu, e⟩ := hs τ φ v
      rw [e]
      refine sum_mem fun i _ => ih _ _ fun ρ hρ => ?_
      by_cases e : ρ = τ
      · subst e; rw [Function.update_self]; exact hu i
      · rw [Function.update_of_ne e]; exact hv ρ (by simp [e, hρ])
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r v => rw [map_smul]; exact Submodule.smul_mem _ _ (key Finset.univ φ v (by simp))
  | add a b ha hb => rw [map_add]; exact add_mem ha hb

def glueM (D : D7) (a b : ℕ) : MultilinearMap ℂ (fun _ : D.what₂.Tau => LPol b a) (PolF D b a) :=
  (MultilinearMap.mkPiAlgebra ℂ D.what₂.Tau (PolF D b a)).compLinearMap fun τ =>
    (MvPolynomial.rename (fun s => (τ, s)) : LPol b a →ₐ[ℂ] PolF D b a).toLinearMap

theorem glueM_apply {a b : ℕ} (p : D.what₂.Tau → LPol b a) : glueM D a b p = glue p := rfl

theorem srcOp_glue (τ : D.what₂.Tau) (aT : ℚ) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (p : D.what₂.Tau → LPol W.rank V.rank) :
    srcOp M M' τ aT X (glue p) = glue (Function.update p τ (sOp M M' τ aT X (p τ))) := by
  simp only [srcOp, sOp, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply,
    ((GlueProof.glueLaw D _ _).2 τ _ _ p).1]
  simp only [← glueM_apply, MultilinearMap.map_update_add,
    MultilinearMap.map_update_smul, Function.update_eq_self]

theorem tgtOp_glue (τ : D.what₂.Tau) (aS : ℚ) (Y : Matrix (Fin W.rank) (Fin W.rank) ℂ)
    (p : D.what₂.Tau → LPol W.rank V.rank) :
    tgtOp M M' τ aS Y (glue p) = glue (Function.update p τ (tOp M M' τ aS Y (p τ))) := by
  simp only [tgtOp, tOp, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply,
    ((GlueProof.glueLaw D _ _).2 τ _ _ p).2]
  simp only [← glueM_apply, MultilinearMap.map_update_add,
    MultilinearMap.map_update_smul, Function.update_eq_self]

def multi {Z : Type} [AddCommGroup Z] [Module ℂ Z] (A : PolF D W.rank V.rank →ₗ[ℂ] KT M' →ₗ[ℂ] Z) :
    MultilinearMap ℂ (fun _ : D.what₂.Tau => LPol W.rank V.rank) (MultilinearMap ℂ (fun τ => kFin M' τ) Z) :=
  (PiTensorProduct.lift.symm.toLinearMap ∘ₗ A).compMultilinearMap (glueM D _ _)

theorem multi_apply {Z : Type} [AddCommGroup Z] [Module ℂ Z] (A : PolF D W.rank V.rank →ₗ[ℂ] KT M' →ₗ[ℂ] Z)
    (p : D.what₂.Tau → LPol W.rank V.rank) (y : KVec M') : multi A p y = A (glue p) (PiTensorProduct.tprod ℂ y) := rfl

theorem span_multi {Z : Type} [AddCommGroup Z] [Module ℂ Z] (A : PolF D W.rank V.rank →ₗ[ℂ] KT M' →ₗ[ℂ] Z)
    (h : ∀ p y, A (glue p) (PiTensorProduct.tprod ℂ y) = 0) : A = 0 :=
  LinearMap.ext_on (GlueProof.glueLaw D _ _).1 (by
    rintro _ ⟨p, rfl⟩
    exact PiTensorProduct.ext (MultilinearMap.ext (h p)))

theorem inclK_injective (h : KSm M) : Function.Injective (inclK h) := by
  choose g hg using fun τ => LinearMap.exists_leftInverse_of_injective _ (Submodule.ker_inclusion _ _ (h τ))
  refine Function.LeftInverse.injective (g := PiTensorProduct.map g) fun x => ?_
  rw [inclK, ← LinearMap.comp_apply, ← PiTensorProduct.map_comp, funext hg, PiTensorProduct.map_id]
  rfl

theorem inclK_tprod (h : KSm M) (u : KVec M) :
    inclK h (PiTensorProduct.tprod ℂ u) = PiTensorProduct.tprod ℂ fun τ => (⟨u τ, h τ (u τ).2⟩ : M.sm τ) := by
  rw [inclK, PiTensorProduct.map_tprod]
  rfl

theorem inclK_update (h : KSm M) (u : KVec M) (τ : D.what₂.Tau) (w : kFin M τ) :
    inclK h (PiTensorProduct.tprod ℂ (Function.update u τ w)) = PiTensorProduct.tprod ℂ
      (Function.update (fun τ => (⟨u τ, h τ (u τ).2⟩ : M.sm τ)) τ ⟨w, h τ w.2⟩) := by
  rw [inclK_tprod]
  congr 1
  funext ρ
  by_cases e : ρ = τ
  · subst e; simp
  · simp [e]

theorem exists_factor_kFin (hdec : GlobalTheory.Published.CuspDecaySobolev) {θ : InfFam D} (hθ : IsInfFam θ)
    {aS aT : D.what₂.Tau → ℚ} {a : ∀ τ, Matrix (Fin V.rank) (Fin V.rank) ℂ → Module.End ℂ (kFin M τ)}
    {a' : ∀ τ, Matrix (Fin W.rank) (Fin W.rank) ℂ → Module.End ℂ (kFin M' τ)} (ha : ∀ τ, IsKAct M τ (a τ))
    (hirr : ∀ τ, AbsIrr fun X : lieAt V τ => a τ X) (hker : ∀ τ, LocKer M M' τ (aS τ) (aT τ) (a' τ))
    (I : PolF D W.rank V.rank →ₗ[ℂ] KT M' →ₗ[ℂ] KT M) (B : PolF D W.rank V.rank →ₗ[ℂ] KT M' →ₗ[ℂ] (GA D V → ℂ))
    (h0 : I ≠ 0) (hIs : ∀ τ, ∀ X ∈ lieAt V τ, ∀ φ y, I (srcOp M M' τ (aT τ) X φ) y = intersection_update_fsHerm_neg_one τ (a τ X) (I φ y))
    (hIt : ∀ τ, ∀ Y ∈ lieAt W τ, ∀ φ y, I (tgtOp M M' τ (aS τ) Y φ) y + I φ (intersection_update_fsHerm_neg_one τ (a' τ Y) y) = 0)
    (hBg : ∀ φ y, IsCuspGrow θ V (B φ y))
    (hBs : ∀ τ, ∀ X ∈ lieAt V τ, ∀ φ y, B (srcOp M M' τ (aT τ) X φ) y = Rder θ V τ X (B φ y))
    (hBt : ∀ τ, ∀ Y ∈ lieAt W τ, ∀ φ (y : KVec M'), B (tgtOp M M' τ (aS τ) Y φ) (PiTensorProduct.tprod ℂ y) +
      B φ (intersection_update_fsHerm_neg_one τ (a' τ Y) (PiTensorProduct.tprod ℂ y)) = 0) :
    (∃ T : KT M →ₗ[ℂ] (GA D V → ℂ), ∀ φ y, T (I φ y) = B φ y) ∧ Submodule.span ℂ {x | ∃ φ y, I φ y = x} = ⊤ := by
  obtain ⟨μ, 𝓕, hμ, h𝓕⟩ := GlobalTheory.Ker.HypModel.exists_haar_fundDom D V
  obtain ⟨E, hE0, hE⟩ := GlobalTheory.Chain.CuspL2.exists_embedding_skew hdec D θ V μ 𝓕 hθ hμ h𝓕
  have s1 : ∀ τ X (p : D.what₂.Tau → LPol W.rank V.rank) x, glue (Function.update p τ (sOp M M' τ (aT τ) X x)) =
      srcOp M M' τ (aT τ) X (glue (Function.update p τ x)) := fun τ X p x => by
    rw [srcOp_glue, Function.update_idem, Function.update_self]
  have s2 : ∀ τ Y (p : D.what₂.Tau → LPol W.rank V.rank) x, glue (Function.update p τ (tOp M M' τ (aS τ) Y x)) =
      tgtOp M M' τ (aS τ) Y (glue (Function.update p τ x)) := fun τ X p x => by
    rw [tgtOp_glue, Function.update_idem, Function.update_self]
  have s3 : ∀ τ (A : Module.End ℂ (kFin M' τ)) (y : KVec M') z, PiTensorProduct.tprod ℂ (Function.update y τ (A z)) =
      intersection_update_fsHerm_neg_one τ A (PiTensorProduct.tprod ℂ (Function.update y τ z)) := fun τ A y z => by
    rw [position_tprod, Function.update_idem, Function.update_self]
  have pI : ∀ τ L, IsContr τ L → ∀ p y,
      IsLocPair M M' τ (aS τ) (aT τ) (a' τ) ((slice (multi I) τ p y).compr₂ L) := fun τ L hL p y => by
    refine ⟨fun X hX P P' z z' => ?_, fun Y hY P z => ?_⟩
    · have hL' := fun x => LinearMap.congr_fun (hL (a τ X)) x
      simp only [LinearMap.comp_apply] at hL'
      simp only [LinearMap.compr₂_apply, slice_apply, multi_apply, s1, hIs τ X hX, hL']
      exact (ha τ).skew X hX _ _
    · simp only [LinearMap.compr₂_apply, slice_apply, multi_apply, s2, s3]
      rw [← map_add, hIt τ Y hY, map_zero]
  have pB : ∀ τ p y, IsLocPair M M' τ (aS τ) (aT τ) (a' τ) ((slice (multi B) τ p y).compr₂ E) := fun τ p y => by
    refine ⟨fun X hX P P' z z' => ?_, fun Y hY P z => ?_⟩
    · simp only [LinearMap.compr₂_apply, slice_apply, multi_apply, s1, hBs τ X hX]
      exact hE τ X hX _ _ (hBg _ _) (hBg _ _) (hBs τ X hX _ _ ▸ hBg _ _) (hBs τ X hX _ _ ▸ hBg _ _)
    · simp only [LinearMap.compr₂_apply, slice_apply, multi_apply, s2, s3]
      rw [← map_add, hBt τ Y hY, map_zero]
  obtain ⟨⟨T, hT⟩, hs⟩ := exists_factor (fun τ (X : lieAt V τ) => sOp M M' τ (aT τ) X) _ hirr (multi I) (multi B)
    (by by_contra hn; exact h0 (span_multi I fun p y => by_contra fun h => hn ⟨p, y, h⟩))
    (fun τ X p y => by rw [multi_apply, multi_apply, ← srcOp_glue, hIs τ X X.2])
    fun τ L hL p y hne => ⟨fun L' hL' p' y' => hker τ _ _ _ _ (pI τ L hL p y) (pI τ L' hL' p' y') hne,
      fun p' y' n x z h => by
        refine (hE0 _ (GlobalTheory.Chain.CuspGrowSpace.isCuspGrow_of_mem_span D θ V _ (sum_mem fun i _ => Submodule.subset_span (hBg _ _)))).2 ?_
        rw [map_sum]
        exact hker τ _ _ _ _ (pI τ L hL p y) (pB τ p' y') hne n x z h⟩
  refine ⟨⟨T, fun φ y => ?_⟩, eq_top_iff.2 (hs ▸ Submodule.span_mono ?_)⟩
  · have := span_multi (I.compr₂ T - B) fun p y => sub_eq_zero.2 (hT p y)
    exact sub_eq_zero.1 (LinearMap.congr_fun₂ this φ y)
  · rintro _ ⟨p, y, rfl⟩
    exact ⟨_, _, rfl⟩

theorem exists_mult (hG : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.ExtExists D) (hdec : GlobalTheory.Published.CuspDecaySobolev) {θ : InfFam D}
    (hθ : IsInfFam θ) (h : KSm M) (h' : KSm M')
    {aS aT : D.what₂.Tau → ℚ} {a : ∀ τ, Matrix (Fin V.rank) (Fin V.rank) ℂ → Module.End ℂ (kFin M τ)}
    {a' : ∀ τ, Matrix (Fin W.rank) (Fin W.rank) ℂ → Module.End ℂ (kFin M' τ)} (ha : ∀ τ, IsKAct M τ (a τ))
    (ha' : ∀ τ, IsKAct M' τ (a' τ))
    (hirr : ∀ τ, AbsIrr fun X : lieAt V τ => a τ X) (hker : ∀ τ, LocKer M M' τ (aS τ) (aT τ) (a' τ))
    (It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M) (B : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] (GA D V → ℂ))
    {J : Set (GA D V)} {χ : GA D V → ℂ} (h0 : ∃ φ y, It φ (inclK h' y) ≠ 0)
    (hK : ∀ τ (φ : PolF D W.rank V.rank), ∀ k ∈ maxCpt M τ, ∃ φ' : PolF D W.rank V.rank,
      φ'.totalDegree ≤ φ.totalDegree ∧ ∀ v, inclT M (It φ' v) = actT M τ k (inclT M (It φ v)) ∧
        B φ' v = rTr V (atTau θ V τ k) (B φ v))
    (hIs : ∀ τ, ∀ X ∈ lieAt V τ, ∀ φ v, DerT M τ X (It φ v) (It (srcOp M M' τ (aT τ) X φ) v))
    (hIt : ∀ τ, ∀ Y ∈ lieAt W τ, ∀ φ v v', DerT M' τ Y v v' → It (tgtOp M M' τ (aS τ) Y φ) v + It φ v' = 0)
    (hBg : ∀ φ v, IsCuspGrow θ V (B φ v))
    (hBs : ∀ τ, ∀ X ∈ lieAt V τ, ∀ φ v, B (srcOp M M' τ (aT τ) X φ) v = Rder θ V τ X (B φ v))
    (hBt : ∀ τ, ∀ Y ∈ lieAt W τ, ∀ φ (v : M'.Vec) (w : M'.sm τ), (w : M'.H τ) = dRep (M'.rep τ) Y (v τ) →
      B (tgtOp M M' τ (aS τ) Y φ) (PiTensorProduct.tprod ℂ v) +
        B φ (PiTensorProduct.tprod ℂ (Function.update v τ w)) = 0)
    (hlev : ∀ φ v, ∀ k ∈ J, ∀ g, B φ v (g * k) = χ k * B φ v g) :
    ∃ u ∈ MultT θ M J χ, ∀ φ y, u (It φ (inclK h' y)) = B φ (inclK h' y) := by
  have inj := inclK_injective h
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective _ (LinearMap.ker_eq_bot.2 inj)
  let I := (It.compl₂ (inclK h')).compr₂ g
  have hI : ∀ φ y, inclK h (I φ y) = It φ (inclK h' y) := fun φ y => by
    obtain ⟨z, hz⟩ := mem_range_inclK h (It φ (inclK h' y)) fun τ =>
      ⟨(MvPolynomial.restrictTotalDegree _ ℂ φ.totalDegree).map (inclT M ∘ₗ It.flip (inclK h' y)), inferInstance,
        fun k hk => by
          obtain ⟨φ', h1, h2⟩ := hK τ φ k hk
          exact ⟨φ', (MvPolynomial.mem_restrictTotalDegree _ _ _).2 h1, (h2 _).1⟩⟩
    change inclK h (g (It φ (inclK h' y))) = _
    rw [← hz, ← LinearMap.comp_apply g, hg, LinearMap.id_apply]
  have hIs' : ∀ τ, ∀ X ∈ lieAt V τ, ∀ φ y, I (srcOp M M' τ (aT τ) X φ) y = intersection_update_fsHerm_neg_one τ (a τ X) (I φ y) :=
    fun τ X hX φ y => inj (by
      rw [hI]
      exact derT_unique (hIs τ X hX φ _) (hI φ y ▸ (GlobalTheory.Chain.IoLift.FinTensor.kFinTensor D V S M τ h).2.1 _ (ha τ) X hX _))
  obtain ⟨⟨T, hT⟩, hs⟩ := exists_factor_kFin hdec hθ ha hirr hker I (B.compl₂ (inclK h'))
    (fun e => by
      obtain ⟨φ, y, h0⟩ := h0
      exact h0 (by rw [← hI, e]; simp)) hIs'
    (fun τ Y hY φ y => inj (by
      rw [map_add, hI, hI, map_zero]
      exact hIt τ Y hY φ _ _ ((GlobalTheory.Chain.IoLift.FinTensor.kFinTensor D W S' M' τ h').2.1 _ (ha' τ) Y hY _)))
    (fun φ y => hBg _ _) (fun τ X hX φ y => hBs τ X hX _ _) fun τ Y hY φ y => by
      rw [LinearMap.compl₂_apply, LinearMap.compl₂_apply, position_tprod, inclK_update, inclK_tprod]
      exact hBt τ Y hY φ _ _ ((ha' τ).der Y hY _).deriv.symm
  simp only [LinearMap.compl₂_apply] at hT
  have hind : ∀ p : KT M → Prop, (∀ φ y, p (I φ y)) → (∀ x y, p x → p y → p (x + y)) → ∀ y, p y := by
    intro p h1 h3 y
    have hy : y ∈ Submodule.span ℂ {x | ∃ φ y, I φ y = x} := hs ▸ Submodule.mem_top
    suffices ∀ c : ℂ, p (c • y) by simpa using this 1
    induction hy using Submodule.span_induction with
    | mem _ h => obtain ⟨P, x, rfl⟩ := h; intro c; rw [← map_smul]; exact h1 _ _
    | zero => intro c; simpa using h1 0 0
    | add _ _ _ _ a b => intro c; rw [smul_add]; exact h3 _ _ (a c) (b c)
    | smul a _ _ h => intro c; rw [smul_smul]; exact h _
  have hg : ∀ x, IsCuspGrow θ V (T x) := fun x => GlobalTheory.Chain.CuspGrowSpace.isCuspGrow_of_mem_span D θ V _ (hind (fun x => T x ∈ _)
    (fun φ y => Submodule.subset_span (hT φ y ▸ hBg _ _)) (fun x y a b => by rw [map_add]; exact add_mem a b) x)
  obtain ⟨μ, 𝓕, hμ, h𝓕⟩ := GlobalTheory.Ker.HypModel.exists_haar_fundDom D V
  obtain ⟨E, hE0, -⟩ := GlobalTheory.Chain.CuspL2.exists_embedding_skew hdec D θ V μ 𝓕 hθ hμ h𝓕
  obtain ⟨U, ⟨hU, hUe⟩, -⟩ := hG θ hθ V S M J χ μ 𝓕 hμ h𝓕 (T.compMultilinearMap (PiTensorProduct.tprod ℂ))
    ⟨fun u => (hg _).1, fun u => (hg _).2.1, fun u => (hg _).2.2.1, fun u => (hE0 _ (hg _)).1, fun u => (hg _).2.2.2,
      fun u => hind (fun x => ∀ k ∈ J, ∀ g, T x (g * k) = χ k * T x g) (fun φ y => hT φ y ▸ hlev _ _)
        (fun x y a b k hk g => by simp only [map_add, Pi.add_apply, a k hk g, b k hk g, mul_add]) _,
      fun τ k hk u w hw => by
        obtain rfl : w = kOp M τ hk (u τ) := Subtype.ext hw
        rw [LinearMap.compMultilinearMap_apply, ← position_tprod]
        refine hind (fun x => T (intersection_update_fsHerm_neg_one τ (kOp M τ hk) x) = rTr V (atTau θ V τ k) (T x)) (fun φ y => ?_)
          (fun x y a b => by rw [map_add, map_add, map_add, a, b]; rfl) _
        obtain ⟨φ', -, h2⟩ := hK τ φ k hk
        rw [hT, ← (h2 _).2, ← hT]
        refine congrArg T (inj ((tensorLaw D V S M).inj ?_))
        rw [(GlobalTheory.Chain.IoLift.FinTensor.kFinTensor D V S M τ h).2.2, hI, hI, (h2 _).1],
      fun τ X hX u w hw => by
        obtain rfl : w = a τ X (u τ) := Subtype.ext (hw.trans ((ha τ).der X hX _).deriv)
        rw [LinearMap.compMultilinearMap_apply, ← position_tprod]
        refine hind (fun x => T (intersection_update_fsHerm_neg_one τ (a τ X) x) = Rder θ V τ X (T x)) (fun φ y => ?_)
          (fun x y a b => by
            rw [map_add, map_add, map_add, a, b, (GlobalTheory.Mem.AutSpace.linOnSm_Rder hX).add _ (hg _).2.1 _ (hg _).2.1]) _
        rw [← hIs' τ X hX, hT, hT, hBs τ X hX]⟩
  refine ⟨PiTensorProduct.lift U, ⟨U, Submodule.subset_span hU, rfl⟩, fun φ y => ?_⟩
  have e : PiTensorProduct.lift U ∘ₗ inclK h = T := PiTensorProduct.ext (MultilinearMap.ext fun u => by
    rw [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, inclK_tprod, PiTensorProduct.lift.tprod]
    exact hUe _ u fun _ => rfl)
  rw [← hI, ← hT, ← e, LinearMap.comp_apply]

theorem exists_integralForm {X : Type} [MeasurableSpace X] (μ : Measure X) :
    ∃ I : (X → ℂ) →ₗ[ℂ] ℂ, ∀ φ, Integrable φ μ → I φ = ∫ x, φ x ∂μ := by
  let U : Submodule ℂ (X → ℂ) :=
    { carrier := {φ | Integrable φ μ}
      add_mem' := fun ha hb => Integrable.add ha hb
      zero_mem' := integrable_zero _ _ _
      smul_mem' := fun c _ h => Integrable.smul c h }
  let l : U →ₗ[ℂ] ℂ :=
    { toFun := fun φ => ∫ x, φ.1 x ∂μ
      map_add' := fun a b => integral_add a.2 b.2
      map_smul' := fun c a => integral_smul c a.1 }
  obtain ⟨I, hI⟩ := LinearMap.exists_extend l
  exact ⟨I, fun φ h => LinearMap.congr_fun hI ⟨φ, h⟩⟩

theorem exists_trilinear {G H S P Ds : Type} [MeasurableSpace H] [AddCommGroup S] [Module ℂ S] [AddCommGroup P] [Module ℂ P]
    [AddCommGroup Ds] [Module ℂ Ds] (ν : Measure H) (𝓕 : Set H) (th : G → H → S →ₗ[ℂ] ℂ) (pt : P →ₗ[ℂ] S)
    (C : Submodule ℂ (Ds →ₗ[ℂ] (H → ℂ)))
    (hint : ∀ F : C, ∀ φ v g, IntegrableOn (fun h => th g h (pt φ) * (F : Ds →ₗ[ℂ] (H → ℂ)) v h) 𝓕 ν) :
    ∃ B : P →ₗ[ℂ] Ds →ₗ[ℂ] C →ₗ[ℂ] (G → ℂ), ∀ φ v F,
      B φ v F = Lift.liftInt ν 𝓕 (fun g h s => th g h s) (pt φ) ((F : Ds →ₗ[ℂ] (H → ℂ)) v) := by
  obtain ⟨I, hI⟩ := exists_integralForm (ν.restrict 𝓕)
  let b : P → Ds → C →ₗ[ℂ] (G → ℂ) := fun φ v =>
    { toFun := fun F g => I fun h => th g h (pt φ) * (F : Ds →ₗ[ℂ] (H → ℂ)) v h
      map_add' := fun F F' => funext fun g => by
        rw [Pi.add_apply, ← map_add]; congr 1; funext h; simp [mul_add]
      map_smul' := fun c F => funext fun g => by
        rw [Pi.smul_apply, ← map_smul]; congr 1; funext h; simp [mul_left_comm] }
  refine ⟨LinearMap.mk₂ ℂ b ?_ ?_ ?_ ?_, fun φ v F => funext fun g => hI _ (hint F φ v g)⟩
  · refine fun φ φ' v => LinearMap.ext fun F => funext fun g => ?_
    show I _ = I _ + I _
    rw [← map_add]; congr 1; funext h; simp [add_mul]
  · refine fun c φ v => LinearMap.ext fun F => funext fun g => ?_
    show I _ = c • I _
    rw [← map_smul]; congr 1; funext h; simp [mul_assoc]
  · refine fun φ v v' => LinearMap.ext fun F => funext fun g => ?_
    show I _ = I _ + I _
    rw [← map_add]; congr 1; funext h; simp [mul_add]
  · refine fun c φ v => LinearMap.ext fun F => funext fun g => ?_
    show I _ = c • I _
    rw [← map_smul]; congr 1; funext h; simp [mul_left_comm]

theorem ioExists_of_forall {G H S P Ds Dt : Type} [MeasurableSpace H] [AddCommGroup P] [Module ℂ P]
    [AddCommGroup Ds] [Module ℂ Ds] [AddCommGroup Dt] [Module ℂ Dt] {ν : Measure H} {𝓕 : Set H} {th : G → H → S → ℂ}
    {pt : P → S} {T : P →ₗ[ℂ] Ds →ₗ[ℂ] Dt} {C : Submodule ℂ (Ds →ₗ[ℂ] (H → ℂ))} {C' : Submodule ℂ (Dt →ₗ[ℂ] (G → ℂ))}
    (hint : ∀ F : C, ∀ φ v g, IntegrableOn (fun h => th g h (pt φ) * (F : Ds →ₗ[ℂ] (H → ℂ)) v h) 𝓕 ν)
    (B : P →ₗ[ℂ] Ds →ₗ[ℂ] C →ₗ[ℂ] (G → ℂ))
    (hB : ∀ φ v F, B φ v F = Lift.liftInt ν 𝓕 th (pt φ) ((F : Ds →ₗ[ℂ] (H → ℂ)) v))
    (hex : ∀ F : C, ∃ u ∈ C', ∀ φ v, u (T φ v) = B φ v F) (hun : ∀ u ∈ C', (∀ φ v, u (T φ v) = 0) → u = 0) :
    Lift.IoExists ν 𝓕 th pt T C C' := by
  choose u hu he using hex
  refine ⟨LinearMap.codRestrict C' ⟨⟨u, fun F F' => ?_⟩, fun c F => ?_⟩ hu, hint, fun F φ v g => ?_⟩
  · refine sub_eq_zero.1 (hun _ (sub_mem (hu _) (add_mem (hu _) (hu _))) fun φ v => ?_)
    simp only [LinearMap.sub_apply, LinearMap.add_apply, he, map_add, sub_self]
  · refine sub_eq_zero.1 (hun _ (sub_mem (hu _) (C'.smul_mem _ (hu _))) fun φ v => ?_)
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, he, map_smul, RingHom.id_apply, sub_self]
  · exact congrFun ((hB φ v F).symm.trans (he F φ v).symm) g

theorem elt_one {θ : InfFam D} (hθ : IsInfFam θ) (M : DSModel V S) (τ : D.what₂.Tau) : elt θ M τ 1 = 1 := by
  rw [elt, Matrix.mul_one, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)), atTau_one hθ]

theorem apply_kMean {θ : InfFam D} {J : Set (GA D V)} {χ : GA D V → ℂ} {T : MMap M} (hT : IsMultMap θ M J χ T)
    (τ : D.what₂.Tau) {e : Formalism.REAL.KG (M.ε τ) → ℂ} (he : Continuous e) (v : M.Vec) (u : M.sm τ)
    (hu : (u : M.H τ) = kMean M τ e (v τ)) (x : GA D V) : T (Function.update v τ u) x =
      ∫ k, e k * T v (x * elt θ M τ (Formalism.REAL.toMK k)) ∂(Formalism.REAL.muK (M.ε τ)) := by
  obtain ⟨ℓ, hℓ, hl⟩ := hT.cont τ v x
  rw [← hl, hu, ((GlobalTheory.SmoothAverage.kMean_smooth D V S M τ e he _ (v τ).2).2 ℓ hℓ).2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  have hk := (Formalism.REAL.maximal_compact_facts _ (M.ε τ)).1 _ k.2
  have hw : M.σ τ (Formalism.REAL.toMK k) (v τ) ∈ M.sm τ := (GlobalTheory.MultGelf.mem_sm M τ).2
    (GlobalTheory.SmVec.sigma_mem (M.fr_unit τ) (M.fr_gram τ) (M.ds τ).2.2.1 ((GlobalTheory.MultGelf.mem_sm M τ).1 (v τ).2) hk)
  beta_reduce
  rw [hl ⟨_, hw⟩, hT.equiv τ _ (GlobalTheory.SmVec.conj_mem_UH (M.fr_unit τ) (M.fr_gram τ) hk) v ⟨_, hw⟩
    (congrArg (fun L : M.H τ →L[ℂ] M.H τ => L (v τ)) (GlobalTheory.SmVec.trRep_conj (σ := M.σ τ) (M.fr_unit τ) _)).symm]
  rfl

end GlobalTheory.Chain.IoLift

end
