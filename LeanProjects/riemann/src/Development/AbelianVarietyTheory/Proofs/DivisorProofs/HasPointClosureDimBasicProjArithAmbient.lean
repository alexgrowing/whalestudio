import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.MixHt.DimBasic

theorem dim_image {W T : Type*} [TopologicalSpace W] [TopologicalSpace T] {e : W → T}
    (he : Topology.IsEmbedding e) (S : Set W) :
    topologicalKrullDim (e '' S) = topologicalKrullDim S := by
  have h := topologicalKrullDim_eq_of_isEmbedding (he.comp Topology.IsEmbedding.subtypeVal)
    (Z := e '' S) (by rw [Set.range_comp, Subtype.range_coe])
  exact h

theorem dim_closure_eq_zero_iff {T : Type*} [TopologicalSpace T] [T0Space T] (x : T) :
    topologicalKrullDim (closure ({x} : Set T)) = 0 ↔ IsClosed ({x} : Set T) := by
  constructor
  · intro h
    have hmax := Order.krullDim_nonpos_iff_forall_isMax.1
      (show Order.krullDim (IrreducibleCloseds (closure ({x} : Set T))) ≤ 0 from h.le)
    refine closure_subset_iff_isClosed.1 fun w hw => ?_
    let s : closure ({x} : Set T) := ⟨x, subset_closure rfl⟩
    let t : closure ({x} : Set T) := ⟨w, hw⟩
    have hst : s ⤳ t := Topology.IsInducing.subtypeVal.specializes_iff.1
      (specializes_iff_mem_closure.2 hw)
    let A : IrreducibleCloseds (closure ({x} : Set T)) :=
      ⟨closure {t}, isIrreducible_singleton.closure, isClosed_closure⟩
    let B : IrreducibleCloseds (closure ({x} : Set T)) :=
      ⟨closure {s}, isIrreducible_singleton.closure, isClosed_closure⟩
    have hAB : A ≤ B := specializes_iff_closure_subset.1 hst
    have hBA : B ≤ A := hmax A hAB
    have hts : t ⤳ s := specializes_iff_closure_subset.2 hBA
    have e := (hst.antisymm hts).eq
    exact Set.mem_singleton_iff.2 (congrArg Subtype.val e).symm
  · intro h
    rw [h.closure_eq]
    have : Subsingleton ({x} : Set T) := Set.subsingleton_singleton.coe_sort
    let pt : ({x} : Set T) := ⟨x, rfl⟩
    have : Nonempty (IrreducibleCloseds ({x} : Set T)) :=
      ⟨⟨closure {pt}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
    refine le_antisymm (Order.krullDim_nonpos_iff_forall_isMax.2 fun a b _ => ?_) Order.krullDim_nonneg
    intro y _
    have ha : (a : Set ({x} : Set T)) = Set.univ := a.isIrreducible.nonempty.eq_univ
    show y ∈ (a : Set ({x} : Set T))
    rw [ha]; trivial

theorem ringKrullDim_le_one (k : Type) [CommRing k] [Module.Finite ℤ k] : ringKrullDim k ≤ 1 := by
  have : Algebra.IsIntegral ℤ k := inferInstance
  calc ringKrullDim k ≤ ringKrullDim ℤ :=
        Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap ℤ k))
          fun I J h => Ideal.IsIntegral.comap_lt_comap (I := I.asIdeal) (J := J.asIdeal) h
    _ = 1 := IsPrincipalIdealRing.ringKrullDim_eq_one ℤ Int.not_isField

theorem dim_pspace_le (k : Type) [CommRing k] [Module.Finite ℤ k] (N : ℕ) :
    topologicalKrullDim (PSpace k N) ≤ (N + 1 : ℕ) := by
  have := IsNoetherianRing.of_finite ℤ k
  have hk := ringKrullDim_le_one k
  refine topologicalKrullDim_le_of_forall_exists_isOpen fun x => ?_
  obtain ⟨i, hi⟩ := ProjSpace.exists_mem_chart k N x
  refine ⟨_, (ProjSpace.chart k N i).isOpen, hi, ?_⟩
  rw [topologicalKrullDim_eq_of_isEmbedding (ProjSpace.chartι k N i).isOpenEmbedding.isEmbedding
    (congrArg SetLike.coe (ProjSpace.opensRange_chartι k N i))]
  refine (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim
    (R := MvPolynomial {j // j ≠ i} k)).trans_le ?_
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing]
  simp
  exact (add_le_add_left hk _).trans_eq (add_comm _ _)

theorem finite_residueField (k : Type) [CommRing k] [Module.Finite ℤ k] {X : Scheme.{0}}
    (p : X ⟶ Sp k) (hp : IsProjOver p) {x : X} (hx : IsClosed ({x} : Set X)) :
    Finite (X.residueField x) := by
  have := isClosed_singleton_iff_isClosedImmersion.1 hx
  obtain ⟨N, j, _, hj⟩ := hp
  have := isProper_str k N
  have : IsProper p := hj ▸ inferInstance
  have : IsFinite (spMap (Int.castRingHom k)) :=
    (IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.2 inferInstance)
  have hf : IsFinite (X.fromSpecResidueField x ≫ p ≫ spMap (Int.castRingHom k)) :=
    IsFinite.iff_isProper_and_isAffineHom.2 ⟨inferInstance, inferInstance⟩
  rw [← Spec.map_preimage (X.fromSpecResidueField x ≫ _), IsFinite.SpecMap_iff,
    RingHom.ext_int (Spec.preimage (X.fromSpecResidueField x ≫ p ≫ spMap (Int.castRingHom k))).hom
      (algebraMap ℤ (X.residueField x)), RingHom.finite_algebraMap] at hf
  obtain ⟨ℓ, _⟩ := CharP.exists (X.residueField x)
  rcases CharP.char_is_prime_or_zero (X.residueField x) ℓ with hℓ | rfl
  · have := Fact.mk hℓ
    let := ZMod.algebra (X.residueField x) ℓ
    have := Module.Finite.of_restrictScalars_finite ℤ (ZMod ℓ) (X.residueField x)
    exact Module.finite_of_finite (ZMod ℓ)
  · have := CharP.charP_to_charZero (X.residueField x)
    exact absurd (isField_of_isIntegral_of_isField (R := ℤ) (S := X.residueField x)
      (RingHom.injective_int _) (Field.toIsField _)) Int.not_isField

theorem hasDim_map_iff {X Y : Scheme.{0}} (i : Y ⟶ X) [IsClosedImmersion i] (y : Y) (d : ℕ) :
    HasDim (i y) d ↔ HasDim y d := by
  unfold HasDim
  rw [← Set.image_singleton, i.isClosedEmbedding.closure_image_eq,
    dim_image i.isClosedEmbedding.isEmbedding]

theorem hasDim_genericPoint_iff (Y : Scheme.{0}) [IsIntegral Y] (d : ℕ) :
    HasDim (genericPoint Y) d ↔ topologicalKrullDim Y = d := by
  unfold HasDim
  rw [(genericPoint_spec Y).def]
  rw [IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ Y).isHomeomorph]

end GlobalTheory.MixHt.DimBasic

namespace GlobalTheory.MixHt

open DimBasic in

theorem hasDim_basic : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k), IsAmb p →
    (∃ m : ℕ, ∀ x : X, ∃ d ≤ m, HasDim x d) ∧
    (∀ (x : X) (d d' : ℕ), HasDim x d → HasDim x d' → d = d') ∧
    (∀ x : X, HasDim x 0 ↔ IsClosed ({x} : Set X)) ∧
    (∀ x : X, IsClosed ({x} : Set X) → Finite (X.residueField x)) ∧
    (∀ (Y : Scheme.{0}) (i : Y ⟶ X) [IsClosedImmersion i] (y : Y) (d : ℕ), HasDim (i y) d ↔ HasDim y d) ∧
    ∀ (Y : Scheme.{0}) [IsIntegral Y] (d : ℕ), HasDim (genericPoint Y) d ↔ topologicalKrullDim Y = d := by
  intro k _ X p h
  have := h.finite
  refine ⟨?_, fun x d d' hd hd' => ?_, fun x => ?_, fun x hx => finite_residueField k p h.isProjOver hx,
    fun Y i _ y d => hasDim_map_iff i y d, fun Y _ d => hasDim_genericPoint_iff Y d⟩
  · obtain ⟨N, j, _, -⟩ := h.isProjOver
    refine ⟨N + 1, fun x => ?_⟩
    have h₁ : topologicalKrullDim (closure ({x} : Set X)) ≤ (N + 1 : ℕ) :=
      (topologicalKrullDim_subspace_le X _).trans
        (j.isClosedEmbedding.isInducing.topologicalKrullDim_le.trans (dim_pspace_le k N))
    let pt : closure ({x} : Set X) := ⟨x, subset_closure rfl⟩
    have : Nonempty (IrreducibleCloseds (closure ({x} : Set X))) :=
      ⟨⟨closure {pt}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
    have h₂ : (0 : WithBot ℕ∞) ≤ topologicalKrullDim (closure ({x} : Set X)) := Order.krullDim_nonneg
    unfold HasDim
    generalize topologicalKrullDim (closure ({x} : Set X)) = a at *
    induction a with
    | bot => exact absurd h₂ (by simp)
    | coe a =>
      induction a with
      | top => exact absurd h₁ (by rw [not_le]; exact WithBot.coe_lt_coe.2 (ENat.coe_lt_top _))
      | coe a => exact ⟨a, by exact_mod_cast h₁, rfl⟩
  · unfold HasDim at hd hd'
    exact_mod_cast hd.symm.trans hd'
  · unfold HasDim
    exact_mod_cast dim_closure_eq_zero_iff x

end GlobalTheory.MixHt
