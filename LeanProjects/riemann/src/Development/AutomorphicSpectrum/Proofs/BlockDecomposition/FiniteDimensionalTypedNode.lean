import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFiniteDeterminingSetStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TypedFirstBlockRestrictionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TypedSecondBlockRestrictionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemProdSpanInfStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDimensionalProdSpanStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinStable
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermAuxiliaryStatementA
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.LimV.FdNode

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {N r s : ℕ}

theorem memInd2_of_mem_indSpan {U₁ : Submodule ℂ (Sm E r)} {U₂ : Submodule ℂ (Sm E s)} {φ : Sm E (r + s)}
    (h : φ ∈ indSpan U₁ U₂) : MemInd2 U₁ U₂ φ := by
  unfold indSpan at h
  induction h using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => exact ⟨fun _ _ => rfl, fun _ _ => (tens2 U₁ U₂).zero_mem⟩
  | add x y _ _ hx hy =>
    refine ⟨fun u g => ?_, fun k g => (tens2 U₁ U₂).add_mem (hx.2 k g) (hy.2 k g)⟩
    change x.1 _ + y.1 _ = x.1 _ + y.1 _
    rw [hx.1, hy.1]
  | smul c x _ hx =>
    refine ⟨fun u g => ?_, fun k g => (tens2 U₁ U₂).smul_mem c (hx.2 k g)⟩
    change c • x.1 _ = c • x.1 _
    rw [hx.1]

def sliceMap (k : Kinf E (r + s)) (t : GL (Fin (r + s)) (Af E)) :
    Sm E (r + s) →ₗ[ℂ] (GA E r × GA E s → ℂ) where
  toFun φ m := φ.1 (lev (Ad E) r s m * cf (r + s) k t)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem tensor_le_prodSpan (U₁ : Submodule ℂ (Sm E r)) (U₂ : Submodule ℂ (Sm E s)) :
    tens2 U₁ U₂ ≤ prodSpan (U₁.map (Sm E r).subtype) (U₂.map (Sm E s).subtype) := by
  refine Submodule.span_le.2 ?_
  rintro F ⟨φ₁, h₁, φ₂, h₂, rfl⟩
  exact Submodule.subset_span ⟨φ₁.1, ⟨φ₁, h₁, rfl⟩, φ₂.1, ⟨φ₂, h₂, rfl⟩, rfl⟩

theorem fd_inf (U : Submodule ℂ (Sm E N)) (K : Subgroup (GL (Fin N) (Af E))) (W : Submodule ℂ (Kinf E N → ℂ))
    (h : FiniteDimensional ℂ (typed U K W)) :
    FiniteDimensional ℂ ↥(U.map (Sm E N).subtype ⊓ typeF K W) := by
  have hle : U.map (Sm E N).subtype ⊓ typeF K W ≤ (typed U K W).map (Sm E N).subtype := by
    rintro f ⟨⟨φ, hφ, rfl⟩, hf⟩
    exact ⟨φ, ⟨hφ, hf⟩, rfl⟩
  exact Submodule.finiteDimensional_of_le hle

end SlopeTestRemainingChoices

theorem finiteDimensional_typed_indSpan : ∀ {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {r s : ℕ} (U₁ : Submodule ℂ (Sm E r)) (U₂ : Submodule ℂ (Sm E s)), (∀ (K : Subgroup (GL (Fin r) (Af E))) (W : Submodule ℂ (Kinf E r → ℂ)), IsOpen (K : Set (GL (Fin r) (Af E))) → FiniteDimensional ℂ W → FiniteDimensional ℂ (typed U₁ K W)) → (∀ (K : Subgroup (GL (Fin s) (Af E))) (W : Submodule ℂ (Kinf E s → ℂ)), IsOpen (K : Set (GL (Fin s) (Af E))) → FiniteDimensional ℂ W → FiniteDimensional ℂ (typed U₂ K W)) → ∀ (K : Subgroup (GL (Fin (r + s)) (Af E))) (W : Submodule ℂ (Kinf E (r + s) → ℂ)), IsOpen (K : Set (GL (Fin (r + s)) (Af E))) → FiniteDimensional ℂ W → FiniteDimensional ℂ (typed (indSpan U₁ U₂) K W) := by
  intro E _ _ _ r s U₁ U₂ h₁ h₂ K W hK hW
  obtain ⟨T, hT⟩ := GlobalTheory.CompanionTheory.CTFin.IwaAd.iwasawa_finite_cosets E r s K hK
  obtain ⟨S, hS⟩ := GlobalTheory.T.exists_finite_determining_set W hW
  choose K₁ W₁ oK₁ fW₁ sl₁ using
    fun i : Kinf E (r + s) × GL (Fin (r + s)) (Af E) => GlobalTheory.T.typed_first_block_restriction i.1 i.2 K W hK hW
  choose K₂ W₂ oK₂ fW₂ sl₂ using
    fun i : Kinf E (r + s) × GL (Fin (r + s)) (Af E) => GlobalTheory.T.typed_second_block_restriction i.1 i.2 K W hK hW
  let P : ↥S × ↥T → Submodule ℂ (GA E r × GA E s → ℂ) := fun i =>
    prodSpan (U₁.map (Sm E r).subtype ⊓ typeF (K₁ (i.1.1, i.2.1)) (W₁ (i.1.1, i.2.1)))
      (U₂.map (Sm E s).subtype ⊓ typeF (K₂ (i.1.1, i.2.1)) (W₂ (i.1.1, i.2.1)))
  haveI : ∀ i, FiniteDimensional ℂ (P i) := fun i =>
    GlobalTheory.T.finiteDimensional_prodSpan _ _ (fd_inf _ _ _ (h₁ _ _ (oK₁ _) (fW₁ _))) (fd_inf _ _ _ (h₂ _ _ (oK₂ _) (fW₂ _)))
  have hmem : ∀ (i : ↥S × ↥T) (φ : typed (indSpan U₁ U₂) K W), sliceMap i.1.1 i.2.1 φ.1 ∈ P i := by
    intro i φ
    have hmi := memInd2_of_mem_indSpan φ.2.1
    exact GlobalTheory.T.mem_prodSpan_inf _ _ _ _ _ (tensor_le_prodSpan U₁ U₂ (hmi.2 i.1.1 i.2.1))
      (fun y => sl₁ (i.1.1, i.2.1) _ φ.2.2 y) (fun x => sl₂ (i.1.1, i.2.1) _ φ.2.2 x)
  let Φ : typed (indSpan U₁ U₂) K W →ₗ[ℂ] ∀ i, P i := LinearMap.pi fun i =>
    ((sliceMap i.1.1 i.2.1).comp (Submodule.subtype _)).codRestrict (P i) (hmem i)
  refine FiniteDimensional.of_injective Φ ((injective_iff_map_eq_zero Φ).2 fun φ hφ => ?_)
  have hz : ∀ a ∈ S, ∀ t ∈ T, ∀ m, φ.1.1 (lev (Ad E) r s m * cf (r + s) a t) = 0 := by
    intro a ha t ht m
    have e := congrArg Subtype.val (congrFun hφ (⟨a, ha⟩, ⟨t, ht⟩))
    exact congrFun e m
  have hmi := memInd2_of_mem_indSpan φ.2.1
  have hty : φ.1.1 ∈ typeF K W := φ.2.2
  refine Subtype.ext (Subtype.ext (funext fun g => ?_))
  obtain ⟨x, m, t, k, l, ht, hl, rfl⟩ := hT g
  have e : unip x * lev (Ad E) r s m * finGL E (r + s) t * infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) l =
      unip x * (lev (Ad E) r s m * finGL E (r + s) t * infGL E (r + s) (Unitary.toUnits k)) * finGL E (r + s) l := by
    simp only [mul_assoc]
  rw [e, hty.1 l hl, hmi.1]
  have hw := hS _ (hty.2 (lev (Ad E) r s m * finGL E (r + s) t)) (fun a ha => by
    have h0 := hz a ha t ht m
    rw [cf, infGL_comm, ← mul_assoc] at h0
    exact h0)
  exact congrFun hw k

end GlobalTheory.CompanionTheory.LimV.FdNode

end
