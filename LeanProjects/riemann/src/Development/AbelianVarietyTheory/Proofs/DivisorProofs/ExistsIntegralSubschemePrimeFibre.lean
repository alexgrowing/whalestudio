import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemConeOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsOfInduces
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpanFinrankMaximalIdealLeNcardOfLeSupSq
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopologicalKrullDimEqSucc
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KrullDimQuotientMinimalPrimeOverLStatement

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.CoverNorm
open GlobalTheory.Cartier

namespace GlobalTheory.VertDivisor

theorem exists_vertical_prime_divisor : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X]
    [IsLocallyNoetherian X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (l : ℕ) [Fact l.Prime] (z : X),
    0 < Scheme.ord ((l : X.functionField)) z → ∃ (Z : Scheme.{0}) (i : Z ⟶ X) (_ : IsClosedImmersion i)
    (_ : IsIntegral Z) (_ : Algebra (ZMod l) Γ(Z, ⊤)), i (genericPoint Z) = z ∧ topologicalKrullDim Z = D := by
  intro k _ X _ _ p D hX l _ z hz
  have hl0 : (l : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hcoh : Order.coheight z = 1 := by
    by_contra h
    rw [Scheme.ord_eq_zero_of_coheight_neq_one h] at hz
    exact lt_irrefl _ hz
  let t : X ⟶ Sp ℤ := p ≫ spMap (Int.castRingHom k)
  have hlz : (l : ℤ) ∈ (t z).asIdeal := by
    by_contra h
    have e : t ⁻¹ᵁ PrimeSpectrum.basicOpen (l : ℤ) = X.basicOpen ((l : ℤ) : Γ(X, ⊤)) := by
      rw [← basicOpen_eq_of_affine (R := .of ℤ) (l : ℤ), Scheme.preimage_basicOpen_top,
        eq_intCast (Scheme.ΓSpecIso (.of ℤ)).inv.hom, map_intCast]
    have hu : z ∈ X.basicOpen ((l : ℤ) : Γ(X, ⊤)) := e ▸ (show z ∈ t ⁻¹ᵁ PrimeSpectrum.basicOpen (l : ℤ) from h)
    have hU := (unitAt_fnOf_iff (TopologicalSpace.Opens.mem_top z) (TopologicalSpace.Opens.mem_top _) _).2 hu
    rw [map_intCast, Int.cast_natCast] at hU
    rw [hU.ord_eq_zero] at hz
    exact lt_irrefl _ hz
  obtain ⟨Z, i, _, _, hiz⟩ := exists_isClosedImmersion_genericPoint z
  have hZl : ((l : ℤ) : Γ(Z, ⊤)) = 0 := by
    rw [← ArithBase.mem_asIdeal_iff (i ≫ t), Scheme.Hom.comp_apply, hiz]
    exact hlz
  have : CharP Γ(Z, ⊤) l := (CharP.charP_iff_prime_eq_zero (Fact.out : l.Prime)).2 (by simpa using hZl)
  refine ⟨Z, i, inferInstance, inferInstance, ZMod.algebra _ l, hiz, ?_⟩

  have hrange : Set.range i = closure {z} := by
    have h₁ := (genericPoint_spec Z).image i.continuous
    rw [Set.image_univ, i.isClosedEmbedding.isClosed_range.closure_eq, hiz] at h₁
    exact h₁.def.symm
  rw [← topologicalKrullDim_eq_of_isEmbedding i.isClosedEmbedding.isEmbedding hrange]

  have hgen : genericPoint X ∉ closure ({z} : Set X) := by
    intro h
    have e : z = genericPoint X :=
      ((genericPoint_specializes z).antisymm (specializes_iff_mem_closure.2 h)).eq.symm
    rw [e, Order.coheight_eq_zero.2 (fun y _ => genericPoint_specializes y)] at hcoh
    exact zero_ne_one hcoh

  have hX1 : topologicalKrullDim (Set.univ : Set X) = (D + 1 : ℕ) :=
    (topologicalKrullDim_eq_of_isEmbedding Topology.IsEmbedding.id Set.range_id).trans hX.dim_eq
  have hup : topologicalKrullDim (closure ({z} : Set X)) + 1 ≤ (D + 1 : ℕ) :=
    hX1 ▸ topologicalKrullDim_add_one_le isClosed_closure isClosed_univ
      fun x hx => ⟨genericPoint X, trivial, hgen, genericPoint_specializes x⟩

  obtain ⟨N, jN, _, hjN⟩ := hX.isProjOver
  have := isProper_str k N
  have : IsProper p := hjN ▸ inferInstance
  have : IsFinite (spMap (Int.castRingHom k)) :=
    (IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.2 hX.finite)
  have : LocallyOfFiniteType t := inferInstance
  have : Flat t := hX.flat

  obtain ⟨A, _, _, instA, _, _, j, _, ⟨a, ha⟩, hjt, hA⟩ := exists_affine_chart_trdeg_eq t z
  obtain rfl : instA = Ring.toIntAlgebra A := Subsingleton.elim _ _
  have : CharZero A := ⟨fun m n h => Nat.cast_injective (R := ℤ) (FaithfulSMul.algebraMap_injective ℤ A (by simpa using h))⟩
  obtain ⟨d, hd⟩ := exists_trdeg_eq_natCast ℤ (A := A)

  have hdimX : topologicalKrullDim X ≤ (d + 1 : ℕ) := by
    refine topologicalKrullDim_le_of_forall_exists_isOpen fun x => ?_
    obtain ⟨B, _, _, _, _, _, j', _, ⟨b, rfl⟩, -, hB⟩ := exists_affine_chart_trdeg_eq t x
    refine ⟨Set.range j', j'.isOpenEmbedding.isOpen_range, ⟨b, rfl⟩, ?_⟩
    rw [topologicalKrullDim_eq_of_isEmbedding j'.isOpenEmbedding.isEmbedding rfl]
    refine (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim B).le.trans ?_
    have hdB : Algebra.trdeg ℤ B = d := hB.trans (hA.symm.trans hd)
    have hZ1 : ringKrullDim ℤ ≤ 1 := by
      exact_mod_cast Ring.krullDimLE_iff.mp (inferInstance : Ring.KrullDimLE 1 ℤ)
    refine (IntModel.ringKrullDim_le_add (O := ℤ) ℚ).trans ?_
    rw [ringKrullDim_genericFibre_eq ℤ ℚ hdB]
    refine (add_le_add hZ1 (le_refl ((d : ℕ) : WithBot ℕ∞))).trans_eq ?_
    push_cast
    exact add_comm _ _
  have hDd : D ≤ d := by
    have := hX.dim_eq.symm.trans_le hdimX
    have : ((D + 1 : ℕ) : WithBot ℕ∞) ≤ ((d + 1 : ℕ) : WithBot ℕ∞) := this
    exact Nat.le_of_succ_le_succ (by exact_mod_cast this)

  set q := a.asIdeal with hqdef
  have hlq : (l : A) ∈ q := by
    rw [← ha, ← Scheme.Hom.comp_apply, hjt] at hlz
    have h' : algebraMap ℤ A (l : ℤ) ∈ a.asIdeal := hlz
    simpa using h'
  have hmin : q ∈ (Ideal.span {(l : A)}).minimalPrimes := by
    refine ⟨⟨a.isPrime, (Ideal.span_singleton_le_iff_mem _).2 hlq⟩, fun q' hq' hle => ?_⟩
    obtain ⟨hq'p, hlq'⟩ := hq'
    by_contra hne
    have hbot : (⊥ : Ideal A) ≠ q' := by
      intro h0
      have h1 : (l : A) ∈ q' := (Ideal.span_singleton_le_iff_mem _).1 hlq'
      rw [← h0, Ideal.mem_bot] at h1
      exact hl0 (FaithfulSMul.algebraMap_injective ℤ A (by simpa using h1))
    let b' : PrimeSpectrum A := ⟨q', hq'p⟩
    let g : PrimeSpectrum A := ⟨⊥, Ideal.isPrime_bot⟩
    have hsp (u v : PrimeSpectrum A) : j u ⤳ j v ↔ u.asIdeal ≤ v.asIdeal :=
      j.isOpenEmbedding.isInducing.specializes_iff.trans (PrimeSpectrum.le_iff_specializes u v).symm
    have h₁ : z < j b' := by
      rw [← ha]
      exact ⟨(hsp b' a).2 hle, fun h => hne ((hsp a b').1 h)⟩
    have h₂ : j b' < j g := ⟨(hsp g b').2 bot_le, fun h => hbot (le_bot_iff.1 ((hsp b' g).1 h)).symm⟩
    have h₃ := Order.coheight_add_one_le h₁
    have h₄ := Order.coheight_add_one_le h₂
    rw [hcoh] at h₃
    have h₅ : (1 : ℕ∞) + 1 ≤ 1 := (add_le_add_left (le_add_self.trans h₄) 1).trans h₃
    exact absurd h₅ (by decide)
  have : q.IsPrime := a.isPrime
  have hq := GlobalTheory.T.krull_dim_quotient_minimal_prime_over_l A l q hmin d hd
  have hlow : topologicalKrullDim (Set.range j ∩ closure {j a} : Set X) ≤
      topologicalKrullDim (closure ({z} : Set X)) := by
    rw [ha]
    exact (Topology.IsEmbedding.inclusion Set.inter_subset_right).isInducing.topologicalKrullDim_le
  rw [topologicalKrullDim_range_inter_closure_eq j a, hq] at hlow
  obtain ⟨e, he⟩ : ∃ e : ℕ, topologicalKrullDim (closure ({z} : Set X)) = e :=
    have ⟨e, he⟩ := hX.exists_dim_eq i
    ⟨e, (topologicalKrullDim_eq_of_isEmbedding i.isClosedEmbedding.isEmbedding hrange).trans he⟩
  rw [he] at hlow hup ⊢
  have h1 : d ≤ e := by exact_mod_cast hlow
  have h2 : e + 1 ≤ D + 1 := by exact_mod_cast hup
  have : e = D := by omega
  rw [this]

end GlobalTheory.VertDivisor
