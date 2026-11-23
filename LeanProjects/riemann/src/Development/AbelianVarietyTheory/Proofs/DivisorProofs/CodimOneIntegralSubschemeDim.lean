import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqMultiDiff
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpanFinrankMaximalIdealLeNcardOfLeSupSq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RingKrullDimQuotientAddOneOfMemMinimalPrimesSup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KrullDimQuotientMinimalPrimeOverL
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FiniteResidueFieldOfIsClosedOfLocallyOfFiniteTyp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopologicalKrullDimEqSucc

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.FibreProj

open scoped TensorProduct

namespace GlobalTheory.PrimeDivDim

theorem height_le_one_of_forall_le {A : Type} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    (q : Ideal A) [q.IsPrime] (hq0 : q ≠ ⊥)
    (hmin : ∀ q' : Ideal A, q'.IsPrime → q' ≤ q → q' = ⊥ ∨ q' = q) : q.height ≤ 1 := by
  obtain ⟨f, hfq, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hq0
  refine Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {f}) q
    ⟨⟨inferInstance, (Ideal.span_singleton_le_iff_mem _).2 hfq⟩, fun q' hq' hle => ?_⟩
  rcases hmin q' hq'.1 hle with h | h
  · exact absurd (h ▸ (Ideal.span_singleton_le_iff_mem _).1 hq'.2) (by simpa using hf0)
  · exact h.ge

attribute [local instance] Algebra.TensorProduct.rightAlgebra in

theorem trdeg_le_succ_trdeg_quotient (A : Type) [CommRing A] [IsDomain A]
    [Algebra.FiniteType ℤ A] (q : Ideal A) [q.IsPrime] (hq1 : q.height ≤ 1)
    (hint : ∀ n : ℤ, (n : A) ∈ q → n = 0) {d e : ℕ} (hd : Algebra.trdeg ℤ A = d)
    (he : Algebra.trdeg ℤ (A ⧸ q) = e) : d ≤ e + 1 := by
  have hint' : ∀ n : ℤ, algebraMap ℤ A n ∈ q → n = 0 := fun n h => hint n (by simpa using h)
  have : FaithfulSMul ℤ A := (faithfulSMul_iff_algebraMap_injective _ _).2
    ((injective_iff_map_eq_zero _).2 fun n hn => hint' n (hn ▸ q.zero_mem))
  have : FaithfulSMul ℤ (A ⧸ q) := (faithfulSMul_iff_algebraMap_injective _ _).2
    ((injective_iff_map_eq_zero _).2 fun n hn => hint' n (by
      rw [IsScalarTower.algebraMap_apply ℤ A (A ⧸ q), Ideal.Quotient.algebraMap_eq,
        Ideal.Quotient.eq_zero_iff_mem] at hn
      exact hn))
  have : Algebra.FiniteType ℤ (A ⧸ q) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℤ q) Ideal.Quotient.mk_surjective
  have := IsLocalization.tensorRight (S := A) ℚ (nonZeroDivisors ℤ)
  have hle : Algebra.algebraMapSubmonoid A (nonZeroDivisors ℤ) ≤ nonZeroDivisors A :=
    Submonoid.map_le_iff_le_comap.mpr fun x hx ↦ mem_nonZeroDivisors_of_ne_zero
      ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective ℤ A)).2 (nonZeroDivisors.ne_zero hx))
  have : IsDomain (ℚ ⊗[ℤ] A) := IsLocalization.isDomain_of_le_nonZeroDivisors _ hle
  have hdisj : Disjoint (Algebra.algebraMapSubmonoid A (nonZeroDivisors ℤ) : Set A) q := by
    rw [Set.disjoint_left]
    rintro _ ⟨v, hv, rfl⟩ h
    exact nonZeroDivisors.ne_zero hv (hint' v h)
  have hP : (q.map (algebraMap A (ℚ ⊗[ℤ] A))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint _ _ q inferInstance hdisj
  have hh := IsLocalization.height_map_of_disjoint
    (Algebra.algebraMapSubmonoid A (nonZeroDivisors ℤ)) (S := ℚ ⊗[ℤ] A) q hdisj
  have hS : ringKrullDim (ℚ ⊗[ℤ] A) = d := ringKrullDim_genericFibre_eq ℤ ℚ hd
  have hF := height_add_ringKrullDim_quotient_of_finiteType ℚ (q.map (algebraMap A (ℚ ⊗[ℤ] A)))
  have hk := Algebra.TensorProduct.lTensor_ker (A := ℚ) (Ideal.Quotient.mkₐ ℤ q)
    Ideal.Quotient.mk_surjective
  rw [show RingHom.ker (Ideal.Quotient.mkₐ ℤ q) = q from Ideal.mk_ker] at hk
  have hs : Function.Surjective
      (Algebra.TensorProduct.map (AlgHom.id ℤ ℚ) (Ideal.Quotient.mkₐ ℤ q)) :=
    LinearMap.lTensor_surjective ℚ (g := (Ideal.Quotient.mkₐ ℤ q).toLinearMap)
      Ideal.Quotient.mk_surjective
  have hQ : ringKrullDim ((ℚ ⊗[ℤ] A) ⧸ q.map (algebraMap A (ℚ ⊗[ℤ] A))) = e := by
    have e1 : q.map (algebraMap A (ℚ ⊗[ℤ] A)) =
        q.map (Algebra.TensorProduct.includeRight : A →ₐ[ℤ] ℚ ⊗[ℤ] A) := rfl
    rw [e1, ← hk, ringKrullDim_eq_of_ringEquiv (Ideal.quotientKerAlgEquivOfSurjective hs).toRingEquiv]
    exact ringKrullDim_genericFibre_eq ℤ ℚ he
  rw [hh, hQ, hS] at hF
  obtain ⟨n, hn⟩ : ∃ n : ℕ, q.height = n :=
    ENat.ne_top_iff_exists.1 (ne_top_of_le_ne_top (by decide) hq1) |>.imp fun _ h => h.symm
  rw [hn] at hF hq1
  have h1 : n ≤ 1 := by exact_mod_cast hq1
  have h2 : n + e = d := by exact_mod_cast hF
  omega

theorem succ_trdeg_le_ringKrullDim (B : Type) [CommRing B] [IsDomain B] [CharZero B]
    [inst : Algebra ℤ B] [Algebra.FiniteType ℤ B] {e : ℕ} (he : Algebra.trdeg ℤ B = e) :
    ((e + 1 : ℕ) : WithBot ℕ∞) ≤ ringKrullDim B := by
  obtain rfl : inst = Ring.toIntAlgebra B := Subsingleton.elim _ _
  obtain ⟨m, hm⟩ := Ideal.exists_maximal B
  have hft : Algebra.FiniteType ℤ (B ⧸ m) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℤ m) Ideal.Quotient.mk_surjective
  letI := Ideal.Quotient.field m
  have : @Algebra.FiniteType ℤ (B ⧸ m) _ _ (Ring.toIntAlgebra (B ⧸ m)) := by
    convert hft using 2 <;> first | rfl | exact Subsingleton.elim _ _
  have := finite_field_of_finiteType_int (B ⧸ m)
  obtain ⟨l, hl⟩ := CharP.exists (B ⧸ m)
  have hl0 : l ≠ 0 := CharP.char_ne_zero_of_finite (B ⧸ m) l
  have : Fact l.Prime := ⟨(CharP.char_is_prime_or_zero (B ⧸ m) l).resolve_right hl0⟩
  have hlm : (l : B) ∈ m := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact CharP.cast_eq_zero _ l
  obtain ⟨q', hq', -⟩ := Ideal.exists_minimalPrimes_le ((Ideal.span_singleton_le_iff_mem _).2 hlm)
  have := hq'.1.1
  have h1 := ringKrullDim_quotient_eq_trdeg_of_mem_minimalPrimes_natPrime B l q' hq' e he
  have hne : (l : B) ≠ 0 := Nat.cast_ne_zero.2 hl0
  have h2 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor (mem_nonZeroDivisors_of_ne_zero hne)
  have h3 : ringKrullDim (B ⧸ q') ≤ ringKrullDim (B ⧸ Ideal.span {(l : B)}) :=
    ringKrullDim_le_of_surjective (Ideal.Quotient.factor hq'.1.2)
      (Ideal.Quotient.factor_surjective hq'.1.2)
  rw [h1] at h3
  calc ((e + 1 : ℕ) : WithBot ℕ∞) = (e : WithBot ℕ∞) + 1 := by push_cast; rfl
    _ ≤ ringKrullDim (B ⧸ Ideal.span {(l : B)}) + 1 := by gcongr
    _ ≤ _ := h2

theorem le_ringKrullDim_quotient (A : Type) [CommRing A] [IsDomain A]
    [Algebra.FiniteType ℤ A] (q : Ideal A) [q.IsPrime] (hq1 : q.height ≤ 1)
    (hint : ∀ n : ℤ, (n : A) ∈ q → n = 0) {d : ℕ} (hd : Algebra.trdeg ℤ A = d) :
    (d : WithBot ℕ∞) ≤ ringKrullDim (A ⧸ q) := by
  have hinj : Function.Injective (algebraMap ℤ (A ⧸ q)) :=
    (injective_iff_map_eq_zero _).2 fun n hn => hint n (by
      rw [IsScalarTower.algebraMap_apply ℤ A (A ⧸ q), Ideal.Quotient.algebraMap_eq,
        Ideal.Quotient.eq_zero_iff_mem] at hn
      simpa using hn)
  have : CharZero (A ⧸ q) := charZero_of_injective_algebraMap hinj
  have : Algebra.FiniteType ℤ (A ⧸ q) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℤ q) Ideal.Quotient.mk_surjective
  obtain ⟨e, he⟩ := exists_trdeg_eq_natCast ℤ (A := A ⧸ q)
  have h1 := trdeg_le_succ_trdeg_quotient A q hq1 hint hd he
  exact (show (d : WithBot ℕ∞) ≤ ((e + 1 : ℕ) : WithBot ℕ∞) by exact_mod_cast h1).trans
    (succ_trdeg_le_ringKrullDim _ he)

end GlobalTheory.PrimeDivDim

namespace GlobalTheory.PrimeDivDim

theorem dim_eq_of_coheight_eq_one : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k)
    (D : ℕ), IsArithVar p D → ∀ (Z : Scheme.{0}) (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z],
    Order.coheight (i (genericPoint Z)) = 1 → topologicalKrullDim Z = D := by
  intro k _ X p D hX Z i _ _ hcoh
  have := hX.isIntegral
  set z := i (genericPoint Z) with hiz
  let t : X ⟶ Sp ℤ := p ≫ spMap (Int.castRingHom k)

  have hrange : Set.range i = closure {z} := by
    have h₁ := (genericPoint_spec Z).image i.continuous
    rw [Set.image_univ, i.isClosedEmbedding.isClosed_range.closure_eq] at h₁
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
  have : CharZero A := ⟨fun m n h => Nat.cast_injective (R := ℤ)
    (FaithfulSMul.algebraMap_injective ℤ A (by simpa using h))⟩
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing ℤ A
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
  have : q.IsPrime := a.isPrime
  have hsp (u v : PrimeSpectrum A) : j u ⤳ j v ↔ u.asIdeal ≤ v.asIdeal :=
    j.isOpenEmbedding.isInducing.specializes_iff.trans (PrimeSpectrum.le_iff_specializes u v).symm
  have hmin : ∀ q' : Ideal A, q'.IsPrime → q' ≤ q → q' = ⊥ ∨ q' = q := by
    intro q' hq'p hle
    by_contra hne
    push_neg at hne
    let b' : PrimeSpectrum A := ⟨q', hq'p⟩
    let g : PrimeSpectrum A := ⟨⊥, Ideal.isPrime_bot⟩
    have h₁ : z < j b' := by
      rw [← ha]
      exact ⟨(hsp b' a).2 hle, fun h => hne.2 (le_antisymm hle ((hsp a b').1 h))⟩
    have h₂ : j b' < j g := ⟨(hsp g b').2 bot_le, fun h => hne.1 (le_bot_iff.1 ((hsp b' g).1 h))⟩
    have h₃ := Order.coheight_add_one_le h₁
    have h₄ := Order.coheight_add_one_le h₂
    rw [hcoh] at h₃
    have h₅ : (1 : ℕ∞) + 1 ≤ 1 := (add_le_add_left (le_add_self.trans h₄) 1).trans h₃
    exact absurd h₅ (by decide)
  have hq0 : q ≠ ⊥ := by
    intro h0
    obtain ⟨b, hb⟩ : genericPoint X ∈ Set.range j :=
      ((genericPoint_spec X).mem_open_set_iff j.isOpenEmbedding.isOpen_range).2
        ⟨z, trivial, a, ha⟩
    apply hgen
    rw [← hb, ← ha]
    exact specializes_iff_mem_closure.1 ((hsp a b).2 (by rw [show a.asIdeal = ⊥ from h0]; exact bot_le))

  have hlowq : (d : WithBot ℕ∞) ≤ ringKrullDim (A ⧸ q) := by
    by_cases hv : ∀ n : ℤ, (n : A) ∈ q → n = 0
    · exact le_ringKrullDim_quotient A q (height_le_one_of_forall_le q hq0 hmin) hv hd
    · push_neg at hv
      obtain ⟨n, hnq, hn0⟩ := hv
      have hP : (q.comap (algebraMap ℤ A)).IsPrime := Ideal.comap_isPrime _ _
      have hPne : q.comap (algebraMap ℤ A) ≠ ⊥ := fun h => hn0 (by
        have : n ∈ q.comap (algebraMap ℤ A) := by simpa using hnq
        rw [h] at this
        exact (Ideal.mem_bot.1 this))
      obtain ⟨x, hxP, hx⟩ := Ideal.IsPrime.exists_mem_prime_of_ne_bot hP hPne
      have hl : Nat.Prime x.natAbs := Int.prime_iff_natAbs_prime.1 hx
      have : Fact x.natAbs.Prime := ⟨hl⟩
      have hlP : ((x.natAbs : ℕ) : ℤ) ∈ q.comap (algebraMap ℤ A) :=
        Ideal.mem_of_dvd _ (Int.dvd_natAbs.2 dvd_rfl) hxP
      have hlq : ((x.natAbs : ℕ) : A) ∈ q := by
        have := Ideal.mem_comap.1 hlP
        rwa [eq_intCast, Int.cast_natCast] at this
      have hminl : q ∈ (Ideal.span {((x.natAbs : ℕ) : A)}).minimalPrimes := by
        refine ⟨⟨inferInstance, (Ideal.span_singleton_le_iff_mem _).2 hlq⟩, fun q' hq' hle => ?_⟩
        rcases hmin q' hq'.1 hle with h | h
        · have h1 := (Ideal.span_singleton_le_iff_mem _).1 hq'.2
          rw [h, Ideal.mem_bot, Nat.cast_eq_zero] at h1
          exact absurd h1 hl.ne_zero
        · exact h.ge
      exact (ringKrullDim_quotient_eq_trdeg_of_mem_minimalPrimes_natPrime A x.natAbs q hminl d hd).ge
  have hlow : topologicalKrullDim (Set.range j ∩ closure {j a} : Set X) ≤
      topologicalKrullDim (closure ({z} : Set X)) := by
    rw [ha]
    exact (Topology.IsEmbedding.inclusion Set.inter_subset_right).isInducing.topologicalKrullDim_le
  rw [topologicalKrullDim_range_inter_closure_eq j a] at hlow
  have hlow' := hlowq.trans hlow
  obtain ⟨e, he⟩ : ∃ e : ℕ, topologicalKrullDim (closure ({z} : Set X)) = e :=
    have ⟨e, he⟩ := hX.exists_dim_eq i
    ⟨e, (topologicalKrullDim_eq_of_isEmbedding i.isClosedEmbedding.isEmbedding hrange).trans he⟩
  rw [he] at hlow' hup ⊢
  have h1 : d ≤ e := by exact_mod_cast hlow'
  have h2 : e + 1 ≤ D + 1 := by exact_mod_cast hup
  have : e = D := by omega
  rw [this]

end GlobalTheory.PrimeDivDim
