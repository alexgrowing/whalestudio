import Mathlib
import Development.WeilBound.CoreStatements.MinimalPrimeDimensions.GenIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemConeOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsOfInduces
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpanFinrankMaximalIdealLeNcardOfLeSupSq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RingKrullDimQuotientAddOneOfMemMinimalPrimesSup
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopologicalKrullDimEqSucc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KrullDimQuotientMinimalPrimeOverL
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PIntDomainDim

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad

namespace ChowFormHeightComparison₂.CF

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
theorem le_dim_quotient_horizontal (A : Type) [CommRing A] [IsDomain A] [CharZero A] [Algebra.FiniteType ℤ A]
    (q : Ideal A) [q.IsPrime] (hq : q.height ≤ 1) (hinj : Function.Injective (algebraMap ℤ (A ⧸ q))) {d : ℕ}
    (hd : Algebra.trdeg ℤ A = d) : (d : WithBot ℕ∞) ≤ ringKrullDim (A ⧸ q) := by
  have : FaithfulSMul ℤ (A ⧸ q) := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  have : Algebra.FiniteType ℤ (A ⧸ q) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℤ q) (Ideal.Quotient.mkₐ_surjective ℤ q)
  obtain ⟨e, he⟩ := exists_trdeg_eq_natCast ℤ (A := A ⧸ q)
  have h1 := GroundTheory.Heights₂.Heights.IntDomainDim.proof (A ⧸ q) hinj
  rw [he, Cardinal.toENat_nat] at h1
  have hB := ringKrullDim_genericFibre_eq ℤ ℚ hd
  have hB' := ringKrullDim_genericFibre_eq ℤ ℚ he
  have := IsLocalization.tensorRight (S := A) ℚ (nonZeroDivisors ℤ)
  have := IsLocalization.tensorRight (S := A ⧸ q) ℚ (nonZeroDivisors ℤ)
  have hle : Algebra.algebraMapSubmonoid A (nonZeroDivisors ℤ) ≤ nonZeroDivisors A :=
    Submonoid.map_le_iff_le_comap.mpr fun x hx ↦ mem_nonZeroDivisors_of_ne_zero
      (by simpa using nonZeroDivisors.ne_zero hx)
  have hle' : Algebra.algebraMapSubmonoid (A ⧸ q) (nonZeroDivisors ℤ) ≤ nonZeroDivisors (A ⧸ q) :=
    Submonoid.map_le_iff_le_comap.mpr fun x hx ↦ mem_nonZeroDivisors_of_ne_zero
      ((map_ne_zero_iff _ hinj).2 (nonZeroDivisors.ne_zero hx))
  have : IsDomain (ℚ ⊗[ℤ] A) := IsLocalization.isDomain_of_le_nonZeroDivisors _ hle
  have : IsDomain (ℚ ⊗[ℤ] (A ⧸ q)) := IsLocalization.isDomain_of_le_nonZeroDivisors _ hle'
  let φ : ℚ ⊗[ℤ] A →ₐ[ℚ] ℚ ⊗[ℤ] (A ⧸ q) := Algebra.TensorProduct.map (AlgHom.id ℚ ℚ) (Ideal.Quotient.mkₐ ℤ q)
  have hφ : Function.Surjective φ := fun x => by
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨0, map_zero _⟩
    | tmul a b =>
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
      exact ⟨a ⊗ₜ b, rfl⟩
    | add x y hx hy =>
      obtain ⟨x, rfl⟩ := hx
      obtain ⟨y, rfl⟩ := hy
      exact ⟨x + y, map_add _ _ _⟩
  have : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime _
  have hc : (RingHom.ker φ).comap (algebraMap A (ℚ ⊗[ℤ] A)) = q := by
    ext a
    rw [Ideal.mem_comap, RingHom.mem_ker, ← Ideal.Quotient.eq_zero_iff_mem,
      ← map_eq_zero_iff _ (IsLocalization.injective (ℚ ⊗[ℤ] (A ⧸ q)) hle')]
    exact Iff.rfl
  have h2 := IsLocalization.height_comap (Algebra.algebraMapSubmonoid A (nonZeroDivisors ℤ)) (RingHom.ker φ)
  replace h2 : q.height = (RingHom.ker φ).height := (congrArg Ideal.height hc).symm.trans h2
  have h3 := height_add_ringKrullDim_quotient_of_finiteType ℚ (RingHom.ker φ)
  have h4 : ringKrullDim ((ℚ ⊗[ℤ] A) ⧸ RingHom.ker φ) = ringKrullDim (ℚ ⊗[ℤ] (A ⧸ q)) :=
    ringKrullDim_eq_of_ringEquiv (RingHom.quotientKerEquivOfSurjective (f := φ.toRingHom) hφ)
  rw [h4, hB, hB', ← h2] at h3
  rw [h1, ← h3, add_comm, WithBot.coe_add]
  refine add_le_add (le_of_eq (by norm_cast)) ?_
  exact_mod_cast hq

theorem le_dim_quotient (A : Type) [CommRing A] [IsDomain A] [CharZero A] [Algebra.FiniteType ℤ A]
    (q : Ideal A) [q.IsPrime] (hmin : ∀ f ∈ q, f ≠ 0 → q ∈ (Ideal.span {f}).minimalPrimes) {d : ℕ}
    (hd : Algebra.trdeg ℤ A = d) : (d : WithBot ℕ∞) ≤ ringKrullDim (A ⧸ q) := by
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing ℤ A
  obtain ⟨l, hl⟩ := CharP.exists (A ⧸ q)
  rcases CharP.char_is_prime_or_zero (A ⧸ q) l with h | rfl
  · have : Fact l.Prime := ⟨h⟩
    have hlq : (l : A) ∈ q := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
      exact CharP.cast_eq_zero _ l
    exact (GlobalTheory.ringKrullDim_quotient_eq_trdeg_of_mem_minimalPrimes_natPrime A l q
      (hmin _ hlq (Nat.cast_ne_zero.2 h.ne_zero)) d hd).ge
  · have : CharZero (A ⧸ q) := CharP.charP_to_charZero _
    refine le_dim_quotient_horizontal A q ?_ (algebraMap ℤ (A ⧸ q)).injective_int hd
    by_cases h0 : q = ⊥
    · subst h0
      rw [Ideal.height_bot]
      exact zero_le_one
    · obtain ⟨f, hf, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
      exact Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ (hmin f hf hf0)

theorem stDim : StDim := by
  intro k _ X p D hX Z i _ _ hcoh
  have := hX.isIntegral
  generalize hiz : i (genericPoint Z) = z at hcoh
  let t : X ⟶ Sp ℤ := p ≫ spMap (Int.castRingHom k)
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
  have : a.asIdeal.IsPrime := a.isPrime
  have hmin : ∀ f ∈ a.asIdeal, f ≠ 0 → a.asIdeal ∈ (Ideal.span {f}).minimalPrimes := fun f hf hf0 => by
    refine ⟨⟨a.isPrime, (Ideal.span_singleton_le_iff_mem _).2 hf⟩, fun q' hq' hle => ?_⟩
    obtain ⟨hq'p, hlq'⟩ := hq'
    by_contra hne
    have hbot : (⊥ : Ideal A) ≠ q' := by
      intro h0
      have h1 : f ∈ q' := (Ideal.span_singleton_le_iff_mem _).1 hlq'
      rw [← h0, Ideal.mem_bot] at h1
      exact hf0 h1
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
  have hq := le_dim_quotient A a.asIdeal hmin hd
  have hlow : topologicalKrullDim (Set.range j ∩ closure {j a} : Set X) ≤
      topologicalKrullDim (closure ({z} : Set X)) := by
    rw [ha]
    exact (Topology.IsEmbedding.inclusion Set.inter_subset_right).isInducing.topologicalKrullDim_le
  rw [topologicalKrullDim_range_inter_closure_eq j a] at hlow
  replace hlow := hq.trans hlow
  obtain ⟨e, he⟩ : ∃ e : ℕ, topologicalKrullDim (closure ({z} : Set X)) = e :=
    have ⟨e, he⟩ := hX.exists_dim_eq i
    ⟨e, (topologicalKrullDim_eq_of_isEmbedding i.isClosedEmbedding.isEmbedding hrange).trans he⟩
  rw [he] at hlow hup ⊢
  have h1 : d ≤ e := by exact_mod_cast hlow
  have h2 : e + 1 ≤ D + 1 := by exact_mod_cast hup
  have : e = D := by omega
  rw [this]

end ChowFormHeightComparison₂.CF
