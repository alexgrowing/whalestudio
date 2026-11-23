import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Statements
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.SectionInjectivityHypothesesProjectiveLine
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close

open MvPolynomial NumberField
open ReciprocityTheory.ChartRestriction.G.Geo (mConeMap mCoordIdeal mcPts)

noncomputable section

section Homogenize

variable (K : Type) [Field K] (r : ℕ)

def homExp : (Fin (r + 1) →₀ ℕ) →+ (Unit ⊕ Fin r →₀ ℕ) where
  toFun a := Finsupp.equivFunOnFinite.symm (Sum.elim (fun _ ↦ ∑ i, a i) fun k ↦ a k.succ)
  map_zero' := by ext o; cases o <;> simp
  map_add' a b := by ext o; cases o <;> simp [Finset.sum_add_distrib]

theorem homExp_injective : Function.Injective (homExp r) := by
  intro a b h
  have hs : ∀ k : Fin r, a k.succ = b k.succ := fun k ↦ by
    simpa [homExp] using DFunLike.congr_fun h (Sum.inr k)
  have ht : ∑ i, a i = ∑ i, b i := by simpa [homExp] using DFunLike.congr_fun h (Sum.inl ())
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Finset.sum_congr rfl (fun k _ ↦ hs k)] at ht
  ext i
  refine Fin.cases ?_ (fun k ↦ hs k) i
  omega

theorem homExp_single_zero : homExp r (Finsupp.single 0 1) = Finsupp.single (Sum.inl ()) 1 := by
  ext o
  cases o with
  | inl u => cases u; simp [homExp]
  | inr k => simp [homExp, Finsupp.single_apply]

theorem homExp_single_succ (k : Fin r) :
    homExp r (Finsupp.single k.succ 1) =
      Finsupp.single (Sum.inl ()) 1 + Finsupp.single (Sum.inr k) 1 := by
  ext o
  cases o with
  | inl u => cases u; simp [homExp]
  | inr k' => simp [homExp, Finsupp.single_apply, Fin.succ_inj, eq_comm]

def homMap : MvPolynomial (Fin (r + 1)) K →+* MvPolynomial (Unit ⊕ Fin r) K :=
  AddMonoidAlgebra.mapDomainRingHom K (homExp r)

theorem homMap_injective : Function.Injective (homMap K r) :=
  AddMonoidAlgebra.mapDomain_injective (homExp_injective r)

theorem homMap_monomial (s : Fin (r + 1) →₀ ℕ) (c : K) :
    homMap K r (monomial s c) = monomial (homExp r s) c := by
  rw [← single_eq_monomial, ← single_eq_monomial]
  exact AddMonoidAlgebra.mapDomain_single

def fieldMap :
    MvPolynomial (Unit ⊕ Fin r) K →+* MvPolynomial Unit (FractionRing (MvPolynomial (Fin r) K)) :=
  (MvPolynomial.map (algebraMap (MvPolynomial (Fin r) K) _)).comp
    (sumAlgEquiv K Unit (Fin r)).toRingEquiv.toRingHom

theorem fieldMap_injective : Function.Injective (fieldMap K r) :=
  (MvPolynomial.map_injective _ (IsFractionRing.injective _ _)).comp
    (sumAlgEquiv K Unit (Fin r)).injective

def coneAff : MvPolynomial (Fin (r + 1)) K →+* MvPolynomial Unit (FractionRing (MvPolynomial (Fin r) K)) :=
  (fieldMap K r).comp (homMap K r)

theorem coneAff_injective : Function.Injective (coneAff K r) :=
  (fieldMap_injective K r).comp (homMap_injective K r)

theorem coneAff_C (c : K) : coneAff K r (C c) = C (algebraMap K _ c) := by
  have h : homMap K r (C c) = C c := by
    rw [← monomial_zero', homMap_monomial, map_zero, monomial_zero']
  simp only [coneAff, RingHom.comp_apply, h, fieldMap, RingEquiv.toRingHom_eq_coe,
    AlgEquiv.toRingEquiv_toRingHom, RingHom.coe_coe, sumAlgEquiv_C_inl, map_C]
  rw [IsScalarTower.algebraMap_apply K (MvPolynomial (Fin r) K), MvPolynomial.algebraMap_eq]

theorem coneAff_X (j : Fin (r + 1)) : coneAff K r (X j) = C (affGen K r j) * X () := by
  have hX : ∀ s : Unit ⊕ Fin r, (X s : MvPolynomial (Unit ⊕ Fin r) K) = monomial (Finsupp.single s 1) 1 :=
    fun _ ↦ rfl
  refine Fin.cases ?_ (fun k ↦ ?_) j
  · have h : homMap K r (X 0) = X (Sum.inl ()) := by
      rw [show (X 0 : MvPolynomial (Fin (r + 1)) K) = monomial (Finsupp.single 0 1) 1 from rfl,
        homMap_monomial, homExp_single_zero, hX]
    simp only [coneAff, RingHom.comp_apply, h, fieldMap, RingEquiv.toRingHom_eq_coe,
      AlgEquiv.toRingEquiv_toRingHom, RingHom.coe_coe, sumAlgEquiv_X_inl, map_X, affGen,
      Fin.cons_zero, map_one, one_mul]
  · have h : homMap K r (X k.succ) = X (Sum.inl ()) * X (Sum.inr k) := by
      rw [show (X k.succ : MvPolynomial (Fin (r + 1)) K) = monomial (Finsupp.single k.succ 1) 1 from rfl,
        homMap_monomial, homExp_single_succ, hX, hX, monomial_mul, one_mul]
    simp only [coneAff, RingHom.comp_apply, h, fieldMap, RingEquiv.toRingHom_eq_coe,
      AlgEquiv.toRingEquiv_toRingHom, RingHom.coe_coe, map_mul, sumAlgEquiv_X_inl,
      sumAlgEquiv_X_inr, map_X, map_C, affGen, Fin.cons_succ]
    ring

end Homogenize

section Kernels

variable {K : Type} [Field K] [NumberField K] {e r : ℕ}

variable (e r) in

def oneBlockReindex : Coord (oneBlockSizes e r) → (Σ _ : Unit, Fin (e + 1) × Fin (r + 1)) :=
  fun v ↦ ⟨(), oneBlockIndex e r v.2⟩

variable (e r) in

def oneBlockReindexInv : (Σ _ : Unit, Fin (e + 1) × Fin (r + 1)) → Coord (oneBlockSizes e r) :=
  fun p ↦ ⟨(), (oneBlockIndex e r).symm p.2⟩

theorem rename_reindex_reindexInv (g : MvPolynomial (Σ _ : Unit, Fin (e + 1) × Fin (r + 1)) ℤ) :
    rename (oneBlockReindex e r) (rename (oneBlockReindexInv e r) g) = g := by
  rw [rename_rename]
  convert rename_id_apply g
  funext p
  rcases p with ⟨⟨⟩, q⟩
  simp [oneBlockReindex, oneBlockReindexInv]

theorem rename_reindexInv_reindex (f : MvPolynomial (Coord (oneBlockSizes e r)) ℤ) :
    rename (oneBlockReindexInv e r) (rename (oneBlockReindex e r) f) = f := by
  rw [rename_rename]
  convert rename_id_apply f
  funext v
  rcases v with ⟨⟨⟩, q⟩
  simp [oneBlockReindex, oneBlockReindexInv]

theorem coneAff_oneBlockMap (om : Module.Basis (Fin (e + 1)) ℤ (𝓞 K))
    (f : MvPolynomial (Coord (oneBlockSizes e r)) ℤ) :
    coneAff K r (oneBlockMap (r := r) om f) =
      mConeMap (oneBlockPt om r) (rename (oneBlockReindex e r) f) := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    rw [show (C a : MvPolynomial (Coord (oneBlockSizes e r)) ℤ) = (a : MvPolynomial _ ℤ) from
      eq_intCast C a]
    simp only [map_intCast]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    simp only [map_mul]
    rw [hp]
    congr 1
    simp only [oneBlockMap, coe_eval₂Hom, eval₂_X, map_mul, coneAff_C, coneAff_X, rename_X,
      mConeMap, aeval_X, oneBlockReindex, oneBlockPt]
    ring

theorem mem_oneBlockIdeal_iff (om : Module.Basis (Fin (e + 1)) ℤ (𝓞 K))
    (f : MvPolynomial (Coord (oneBlockSizes e r)) ℤ) :
    f ∈ Heights.oneBlockIdeal (r := r) om ↔
      rename (oneBlockReindex e r) f ∈ mCoordIdeal (oneBlockPt om r) := by
  unfold Heights.oneBlockIdeal mCoordIdeal
  rw [RingHom.mem_ker, RingHom.mem_ker, ← (coneAff_injective K r).eq_iff, map_zero]
  rw [coneAff_oneBlockMap]

theorem oneBlockIdeal_eq_comap (om : Module.Basis (Fin (e + 1)) ℤ (𝓞 K)) :
    Heights.oneBlockIdeal (r := r) om =
      (mCoordIdeal (oneBlockPt om r)).comap (rename (oneBlockReindex e r)) := by
  ext f
  rw [Ideal.mem_comap]
  exact mem_oneBlockIdeal_iff om f

theorem mCoordIdeal_eq_comap (om : Module.Basis (Fin (e + 1)) ℤ (𝓞 K)) :
    mCoordIdeal (oneBlockPt om r) =
      (Heights.oneBlockIdeal (r := r) om).comap (rename (oneBlockReindexInv e r)) := by
  ext g
  rw [Ideal.mem_comap, mem_oneBlockIdeal_iff, rename_reindex_reindexInv]

end Kernels

section Points

variable {K : Type} [Field K] [NumberField K] {e r : ℕ}

def coneToPairs {F : Type*} (z : Cone (oneBlockSizes e r) F) :
    (Σ _ : Unit, Fin (e + 1) × Fin (r + 1)) → F :=
  fun p ↦ z () ((oneBlockIndex e r).symm p.2)

theorem evalCone_eq_eval (z : Cone (oneBlockSizes e r) ℂ) (f : MvPolynomial (Coord (oneBlockSizes e r)) ℤ) :
    evalCone z f = eval (coneToPairs z) (map (Int.castRingHom ℂ) (rename (oneBlockReindex e r) f)) := by
  rw [eval_map, eval₂_rename, evalCone]
  congr 1
  funext v
  rcases v with ⟨⟨⟩, i⟩
  simp [coneToPairs, oneBlockReindex]

theorem mem_conePoints_iff (om : Module.Basis (Fin (e + 1)) ℤ (𝓞 K)) (z : Cone (oneBlockSizes e r) ℂ) :
    z ∈ Heights.conePoints (Heights.oneBlockIdeal om) ℂ ↔
      coneToPairs z ∈ mcPts (mCoordIdeal (oneBlockPt om r)) := by
  constructor
  · rintro ⟨hz, hf⟩
    refine ⟨fun _ ↦ ?_, fun g hg ↦ ?_⟩
    · obtain ⟨i, hi⟩ := Function.ne_iff.mp (hz ())
      exact ⟨oneBlockIndex e r i, by simpa [coneToPairs] using hi⟩
    · have hmem : rename (oneBlockReindexInv e r) g ∈ Heights.oneBlockIdeal om := by
        rw [mem_oneBlockIdeal_iff, rename_reindex_reindexInv]
        exact hg
      have h := hf _ hmem
      rwa [evalCone_eq_eval, rename_reindex_reindexInv] at h
  · rintro ⟨hz, hf⟩
    refine ⟨fun _ h ↦ ?_, fun f hf' ↦ ?_⟩
    · obtain ⟨q, hq⟩ := hz ()
      exact hq (by simp [coneToPairs, h])
    · rw [evalCone_eq_eval]
      exact hf _ ((mem_oneBlockIdeal_iff om f).1 hf')

omit [NumberField K] in

theorem coneToPairs_oneBlockPoint {F : Type*} [CommRing F] (om : Module.Basis (Fin (e + 1)) ℤ (𝓞 K))
    (σ : K →+* F) (w : Fin (r + 1) → F) :
    coneToPairs (oneBlockPoint om σ w) = fun p ↦ σ (om p.2.1 : K) * w p.2.2 := by
  funext p
  simp [coneToPairs, oneBlockPoint]

end Points

section Metric

open Matrix
open scoped ComplexOrder

variable {K : Type} [Field K] [NumberField K] {e r : ℕ}

theorem oneBlockMetricAgrees_iff (om : Module.Basis (Fin (e + 1)) ℤ (𝓞 K)) (F : HermLattice K (r + 1))
    (A : HermLine (oneBlockSizes e r)) :
    OneBlockMetricAgrees om F A ↔
      ∀ (σ : K →+* ℂ) (w : Fin (r + 1) → ℂ), w ≠ 0 →
        A.metric (fun _ t ↦ σ (om ((oneBlockIndex e r).symm.symm t).1 : K) *
          w ((oneBlockIndex e r).symm.symm t).2) = hermNorm (F.metric σ) w :=
  Iff.rfl

theorem pointHeightDegree_hypotheses (om : Module.Basis (Fin (e + 1)) ℤ (𝓞 K))
    (F : HermLattice K (r + 1)) (A : HermLine (oneBlockSizes e r)) (hA : A.deg = 1)
    (hM : OneBlockMetricAgrees om F A) :
    (∀ σ, (F.metric σ).PosDef) ∧
      (∀ σ, F.metric (ComplexEmbedding.conjugate σ) = (F.metric σ).map (starRingEnd ℂ)) ∧
      (∀ u, A.deg u = 1) ∧
      ∀ (σ : K →+* ℂ) (w : Fin (r + 1) → ℂ), w ≠ 0 →
        A.metric (fun _ t ↦ σ (om ((oneBlockIndex e r).symm.symm t).1 : K) *
          w ((oneBlockIndex e r).symm.symm t).2) = hermNorm (F.metric σ) w :=
  ⟨F.posDef, F.conj, fun u ↦ by rw [hA]; rfl, hM⟩

end Metric

section Line

variable {K : Type} [Field K] [NumberField K] {K' : Type} [Field K'] [NumberField K'] [Algebra K K']
  {n : ℕ}

variable (K' n) in

def intoField : (Fin n → 𝓞 K') →ₗ[𝓞 K'] (Fin n → K') :=
  LinearMap.compLeft (Algebra.linearMap (𝓞 K') K') (Fin n)

variable (K K' n) in

abbrev stdLatticeExt : Submodule (𝓞 K') (Fin n → K') :=
  Submodule.span (𝓞 K')
    ((fun w : Fin n → K ↦ fun j ↦ algebraMap K K' (w j)) '' (HermLattice.standard K n).lattice)

theorem mem_stdLatticeExt_iff (x : Fin n → K') :
    x ∈ stdLatticeExt K K' n ↔ ∀ j, IsIntegral ℤ (x j) := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨w, hw, rfl⟩ := hy
      have hw' : ∀ j, IsIntegral ℤ (w j) := by
        induction hw using Submodule.span_induction with
        | mem u hu =>
          obtain ⟨i, rfl⟩ := hu
          intro j
          by_cases h : j = i
          · subst h
            simpa using (isIntegral_one : IsIntegral ℤ (1 : K))
          · simpa [Pi.single_apply, h] using (isIntegral_zero : IsIntegral ℤ (0 : K))
        | zero => intro j; simpa using (isIntegral_zero : IsIntegral ℤ (0 : K))
        | add a b _ _ ha hb => intro j; exact (ha j).add (hb j)
        | smul c a _ ha =>
          intro j
          rw [Pi.smul_apply, Algebra.smul_def]
          exact (RingOfIntegers.isIntegral_coe c).mul (ha j)
      intro j
      exact (hw' j).algebraMap
    | zero => intro j; simpa using (isIntegral_zero : IsIntegral ℤ (0 : K'))
    | add a b _ _ ha hb => intro j; exact (ha j).add (hb j)
    | smul c a _ ha =>
      intro j
      rw [Pi.smul_apply, Algebra.smul_def]
      exact (RingOfIntegers.isIntegral_coe c).mul (ha j)
  · intro hx
    have hsum : x = ∑ j, (⟨x j, hx j⟩ : 𝓞 K') •
        (fun k ↦ algebraMap K K' ((Pi.single j 1 : Fin n → K) k)) := by
      funext k
      rw [Finset.sum_apply, Finset.sum_eq_single k
        (fun j _ hj ↦ by simp [Pi.single_apply, Ne.symm hj]) (by simp)]
      simp only [Pi.smul_apply, Pi.single_eq_same, map_one, Algebra.smul_def, mul_one]
      rfl
    rw [hsum]
    exact Submodule.sum_mem _ fun j _ ↦ Submodule.smul_mem _ _
      (Submodule.subset_span ⟨Pi.single j 1, Submodule.subset_span ⟨j, rfl⟩, rfl⟩)

theorem satLine_map_eq (v : Fin n → 𝓞 K') :
    (satLine v).map (intoField K' n) =
      stdLatticeExt K K' n ⊓
        (Submodule.span K' (Set.range fun _ : Fin 1 ↦ fun j ↦ (v j : K'))).restrictScalars (𝓞 K') := by
  ext x
  rw [Submodule.mem_inf, Submodule.restrictScalars_mem, Set.range_const,
    Submodule.mem_span_singleton, mem_stdLatticeExt_iff, Submodule.mem_map]
  constructor
  · rintro ⟨y, ⟨c, hc⟩, rfl⟩
    refine ⟨fun j ↦ RingOfIntegers.isIntegral_coe (y j), c, ?_⟩
    funext j
    simp [intoField, hc j]
  · rintro ⟨hx, c, rfl⟩
    refine ⟨fun j ↦ ⟨c * v j, hx j⟩, ⟨c, fun j ↦ rfl⟩, ?_⟩
    funext j
    rfl

end Line

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
