import Formalism.FilteredPoleLength.ReducedBasisBounds.BetaSesquilinearity
import Formalism.LogFactorialIndices.LogProductFormula
import Formalism.LogFactorialIndices.SignedSubspaceIndex.SubspaceLatticeIndexSigned

noncomputable section

namespace Formalism.LatticeBaseChangeAlt

open Module

namespace LatticeIndexBis

theorem idx_map_inj {O Y X : Type} [CommRing O] [AddCommGroup Y] [Module O Y]
    [AddCommGroup X] [Module O X] (ι : Y →ₗ[O] X) (hι : Function.Injective ι)
    (P Q : Submodule O Y) :
    Formalism.LatticeIndexTer.idx O X (P.map ι) (Q.map ι) = Formalism.LatticeIndexTer.idx O Y P Q := by
  have key : ∀ P₁ Q₁ : Submodule O Y,
      Module.length O (↥(P₁.map ι) ⧸ Submodule.comap (P₁.map ι).subtype (Q₁.map ι)) =
        Module.length O (↥P₁ ⧸ Submodule.comap P₁.subtype Q₁) := by
    intro P₁ Q₁
    let e : P₁ ≃ₗ[O] P₁.map ι := Submodule.equivMapOfInjective ι hι P₁
    have hm : (Submodule.comap P₁.subtype Q₁).map (e : P₁ →ₗ[O] P₁.map ι) =
        Submodule.comap (P₁.map ι).subtype (Q₁.map ι) := by
      ext z
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨(y : Y), hy, rfl⟩
      · intro hz
        obtain ⟨q, hq, hqz⟩ := hz
        obtain ⟨p, hp, hpz⟩ := z.2
        refine ⟨⟨p, hp⟩, ?_, Subtype.ext hpz⟩
        have hpq : q = p := hι (hqz.trans hpz.symm)
        show p ∈ Q₁
        rw [← hpq]
        exact hq
    exact (Submodule.Quotient.equiv _ _ e hm).length_eq.symm
  unfold Formalism.LatticeIndexTer.idx Formalism.LatticeIndexTer.qlen
  rw [key P Q, key Q P]

theorem span_image_span {R S M N : Type} [Ring R] [Ring S] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module S N] (g : M →+ N) (φ : R → S) (h : ∀ r x, g (r • x) = φ r • g x)
    (s : Set M) :
    Submodule.span S (g '' (Submodule.span R s : Set M)) = Submodule.span S (g '' s) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    induction hx using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
    | smul r y _ hy => rw [h]; exact Submodule.smul_mem _ _ hy
  · exact Submodule.span_mono (Set.image_mono Submodule.subset_span)

section Core

variable {O K V ι : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
  [Algebra O K] [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V]
  [IsScalarTower O K V]

theorem core [Fintype ι] [DecidableEq ι] (a b : ι → V) (ha : LinearIndependent K a)
    (hb : LinearIndependent K b)
    (hab : Submodule.span K (Set.range a) = Submodule.span K (Set.range b))
    (P : Matrix ι ι K) (hP : ∀ i, a i = ∑ k, P k i • b k) :
    P.det ≠ 0 ∧ ∀ x y : O, x ≠ 0 → y ≠ 0 → algebraMap O K x = P.det * algebraMap O K y →
      Formalism.LatticeIndexTer.idx O V (Submodule.span O (Set.range b)) (Submodule.span O (Set.range a)) =
        ((IsDiscreteValuationRing.addVal O x).toNat : ℤ) -
          ((IsDiscreteValuationRing.addVal O y).toNat : ℤ) := by
  let bX := Basis.span ha
  let bY := Basis.span hb
  let f : Submodule.span K (Set.range a) ≃ₗ[K] Submodule.span K (Set.range b) :=
    LinearEquiv.ofEq _ _ hab
  have hbX : ∀ i, ((bX i : Submodule.span K (Set.range a)) : V) = a i := fun i => by
    simp [bX, Basis.span_apply]
  have hbY : ∀ i, ((bY i : Submodule.span K (Set.range b)) : V) = b i := fun i => by
    simp [bY, Basis.span_apply]
  have hM : LinearMap.toMatrix bX bY (f : _ →ₗ[K] _) = P := by
    ext k i
    rw [LinearMap.toMatrix_apply]
    have : (f : _ →ₗ[K] _) (bX i) = ∑ k, P k i • bY k := by
      apply Subtype.ext
      simp [f, hbX, hbY, hP i]
    rw [this, Basis.repr_sum_self]
  refine ⟨?_, ?_⟩
  · rw [← hM]
    exact (LinearEquiv.isUnit_det f bX bY).ne_zero
  · intro x y hx hy hxy
    have h := Formalism.LatticeIndexTer.idxDet O K _ _ ι bX bY f x y hx hy (by rw [hM]; exact hxy)
    let s : Submodule.span K (Set.range b) →ₗ[O] V :=
      (Submodule.span K (Set.range b)).subtype.restrictScalars O
    have hs : Function.Injective s := Subtype.val_injective
    rw [← idx_map_inj s hs] at h
    rw [← h]
    congr 1
    · rw [Submodule.map_span, ← Set.range_comp]
      congr 2
      ext i
      exact (hbY i).symm
    · rw [Submodule.map_span, Submodule.map_span, ← Set.range_comp, ← Set.range_comp]
      congr 2
      ext i
      exact (hbX i).symm

theorem exists_indep [FiniteDimensional K V] (A : Submodule O V) (hA : A.FG) (U : Submodule K V)
    (hU : Submodule.span K (A : Set V) = U) :
    ∃ a : Fin (finrank K U) → V, LinearIndependent K a ∧ A = Submodule.span O (Set.range a) ∧
      Submodule.span K (Set.range a) = U := by
  classical
  haveI : NoZeroSMulDivisors O V := ⟨fun {o v} h => by
    rw [← algebraMap_smul K o v, smul_eq_zero] at h
    rcases h with h | h
    · left
      exact (IsFractionRing.injective O K) (by rw [h, map_zero])
    · right
      exact h⟩
  haveI : Module.Finite O A := Module.Finite.iff_fg.mpr hA
  haveI : Module.Free O A := Module.free_of_finite_type_torsion_free'
  let bA := Module.Free.chooseBasis O A
  let e : Module.Free.ChooseBasisIndex O A → V := fun i => (bA i : V)
  have hliO : LinearIndependent O e := bA.linearIndependent.map' A.subtype (Submodule.ker_subtype A)
  have hli : LinearIndependent K e := by
    first
    | exact (LinearIndependent.iff_fractionRing O K).1 hliO
    | exact LinearIndependent.iff_fractionRing.1 hliO
  have hAe : A = Submodule.span O (Set.range e) := by
    conv_lhs => rw [← Submodule.map_subtype_top A]
    rw [← bA.span_eq, Submodule.map_span, ← Set.range_comp] <;> rfl
  have hspan : Submodule.span K (Set.range e) = U := by
    calc Submodule.span K (Set.range e)
        = Submodule.span K (Submodule.span O (Set.range e) : Set V) :=
          (Submodule.span_span_of_tower O K _).symm
      _ = Submodule.span K (A : Set V) :=
          congrArg (fun s : Submodule O V => Submodule.span K (s : Set V)) hAe.symm
      _ = U := hU
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex O A) = Module.finrank K U := by
    rw [← hspan, finrank_span_eq_card hli]
  let σ := Fintype.equivFinOfCardEq hcard
  have hr : Set.range (e ∘ σ.symm) = Set.range e := by
    first
    | exact EquivLike.range_comp e σ.symm
    | exact Equiv.range_comp e σ.symm
    | rw [Set.range_comp, σ.symm.range_eq_univ, Set.image_univ]
  refine ⟨e ∘ σ.symm, hli.comp _ σ.symm.injective, ?_, ?_⟩
  · rw [hr]
    exact hAe
  · rw [hr]
    exact hspan

end Core

theorem addVal_map {O O' : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O'] (ϖ : O)
    (hϖ : Irreducible ϖ) (hϖ' : Irreducible (algebraMap O O' ϖ)) (x : O) (hx : x ≠ 0) :
    IsDiscreteValuationRing.addVal O' (algebraMap O O' x) = IsDiscreteValuationRing.addVal O x := by
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hϖ
  rw [IsDiscreteValuationRing.addVal_def x u hϖ n hu,
    IsDiscreteValuationRing.addVal_def (algebraMap O O' x) (Units.map (algebraMap O O' : O →* O') u) hϖ' n
      (by rw [hu]; simp)]

theorem indep_baseChange {K K' V V₁ ι : Type} [Field K] [Field K'] [Algebra K K'] [AddCommGroup V]
    [Module K V] [AddCommGroup V₁] [Module K' V₁] [Module K V₁] [IsScalarTower K K' V₁]
    (j : V →ₗ[K] V₁) (hj : IsBaseChange K' j) (a : ι → V) (ha : LinearIndependent K a) :
    LinearIndependent K' (fun i => j (a i)) := by
  classical
  have hs : LinearIndepOn K id (Set.range a) := by
    first
    | exact (linearIndepOn_id_range_iff ha.injective).2 ha
    | exact ha.to_subtype_range
    | exact (linearIndependent_subtype_range ha.injective).2 ha
  let B := Module.Basis.extend hs
  let B' := hj.basis B
  have hB' : LinearIndependent K' (fun i : hs.extend (Set.subset_univ _) => j (i : V)) := by
    have h1 := B'.linearIndependent
    convert h1 using 1
    funext i
    rw [IsBaseChange.basis_apply, Module.Basis.coe_extend]
    rfl
  have hsub : ∀ i, a i ∈ hs.extend (Set.subset_univ _) :=
    fun i => hs.subset_extend _ ⟨i, rfl⟩
  exact hB'.comp (fun i => ⟨a i, hsub i⟩) (fun i i' h => ha.injective (congrArg Subtype.val h))

end LatticeIndexBis

theorem index_baseChange_lattice : RelIndexSpanImage := by
  intro O O' K K' V V₁
  intros
  rename_i j hj ϖ hϖ hϖ' A B hA hB hAB
  classical
  obtain ⟨a, ha, hAa, haU⟩ := LatticeIndexBis.exists_indep A hA (Submodule.span K (A : Set V)) rfl
  obtain ⟨b, hb, hBb, hbU⟩ := LatticeIndexBis.exists_indep B hB (Submodule.span K (A : Set V)) hAB.symm
  have hmem : ∀ i, b i ∈ Submodule.span K (Set.range a) := by
    intro i
    rw [haU, ← hbU]
    exact Submodule.subset_span ⟨i, rfl⟩
  have hc0 : ∀ i, ∃ c : Fin (Module.finrank K (Submodule.span K (A : Set V))) → K,
      ∑ k, c k • a k = b i := by
    intro i
    first
    | exact (Submodule.mem_span_range_iff_exists_fun K).1 (hmem i)
    | exact Submodule.mem_span_range_iff_exists_fun.1 (hmem i)
  choose c hc using hc0
  let P : Matrix (Fin (Module.finrank K (Submodule.span K (A : Set V))))
      (Fin (Module.finrank K (Submodule.span K (A : Set V)))) K := fun k i => c i k
  obtain ⟨hdet, hcore⟩ := LatticeIndexBis.core (O := O) b a hb ha (hbU.trans haU.symm) P (fun i => (hc i).symm)
  obtain ⟨⟨x, y⟩, hxy⟩ := IsLocalization.surj (nonZeroDivisors O) P.det
  dsimp only at hxy
  have hy0 : (y : O) ≠ 0 := nonZeroDivisors.ne_zero y.2
  have hyK : algebraMap O K (y : O) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors y.2
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [map_zero] at hxy
    exact (mul_ne_zero hdet hyK) hxy
  have hjK : ∀ (r : K) (z : V), j (r • z) = algebraMap K K' r • j z := by
    intro r z
    rw [map_smul, algebraMap_smul]
  have hjO : ∀ (o : O) (z : V), j (o • z) = algebraMap O O' o • j z := by
    intro o z
    rw [← algebraMap_smul K o z, map_smul, ← algebraMap_smul K' (algebraMap O K o) (j z),
      ← IsScalarTower.algebraMap_apply O K K', IsScalarTower.algebraMap_apply O O' K', algebraMap_smul]
  have hspanK : ∀ f : Fin (Module.finrank K (Submodule.span K (A : Set V))) → V,
      Submodule.span K (Set.range f) = Submodule.span K (A : Set V) →
      Submodule.span K' (Set.range fun i => j (f i)) =
        Submodule.span K' (j '' (Submodule.span K (A : Set V) : Set V)) := by
    intro f hf
    have h1 := LatticeIndexBis.span_image_span (R := K) (S := K') j.toAddMonoidHom (algebraMap K K')
      (fun r z => hjK r z) (Set.range f)
    simp only [LinearMap.toAddMonoidHom_coe] at h1
    calc Submodule.span K' (Set.range fun i => j (f i)) = Submodule.span K' (j '' Set.range f) := by
          rw [← Set.range_comp] <;> rfl
      _ = Submodule.span K' (j '' (Submodule.span K (Set.range f) : Set V)) := h1.symm
      _ = _ := congrArg (fun s : Submodule K V => Submodule.span K' (j '' (s : Set V))) hf
  have hspanO : ∀ f : Fin (Module.finrank K (Submodule.span K (A : Set V))) → V,
      Submodule.span O' (j '' (Submodule.span O (Set.range f) : Set V)) =
        Submodule.span O' (Set.range fun i => j (f i)) := by
    intro f
    have h1 := LatticeIndexBis.span_image_span (R := O) (S := O') j.toAddMonoidHom (algebraMap O O')
      (fun o z => hjO o z) (Set.range f)
    simp only [LinearMap.toAddMonoidHom_coe] at h1
    rw [h1, ← Set.range_comp]
    all_goals rfl
  have hP' : ∀ i, j (b i) = ∑ k, (P.map (algebraMap K K')) k i • j (a k) := by
    intro i
    rw [← hc i, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, Matrix.map_apply, algebraMap_smul]
    all_goals rfl
  have hdetmap : (P.map (algebraMap K K')).det = algebraMap K K' P.det := by
    rw [RingHom.map_det]
    rfl
  have hne : ∀ z : O, z ≠ 0 → algebraMap O O' z ≠ 0 := by
    intro z hz h0
    have hzK : algebraMap O K z ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hz)
    apply (map_ne_zero (algebraMap K K')).2 hzK
    rw [← IsScalarTower.algebraMap_apply O K K', IsScalarTower.algebraMap_apply O O' K', h0, map_zero]
  have hx'y' : algebraMap O' K' (algebraMap O O' x) =
      (P.map (algebraMap K K')).det * algebraMap O' K' (algebraMap O O' (y : O)) := by
    rw [← IsScalarTower.algebraMap_apply O O' K', ← IsScalarTower.algebraMap_apply O O' K',
      IsScalarTower.algebraMap_apply O K K' x, IsScalarTower.algebraMap_apply O K K' (y : O), hdetmap,
      ← map_mul, hxy]
  have hab' : Submodule.span K' (Set.range fun i => j (b i)) =
      Submodule.span K' (Set.range fun i => j (a i)) :=
    (hspanK b hbU).trans (hspanK a haU).symm
  obtain ⟨-, hcore'⟩ := LatticeIndexBis.core (O := O') (K := K') (V := V₁) (fun i => j (b i)) (fun i => j (a i))
    (LatticeIndexBis.indep_baseChange j hj b hb) (LatticeIndexBis.indep_baseChange j hj a ha) hab'
    (P.map (algebraMap K K')) hP'
  rw [hAa, hBb, hspanO a, hspanO b,
    hcore' (algebraMap O O' x) (algebraMap O O' (y : O)) (hne x hx0) (hne _ hy0) hx'y',
    hcore x (y : O) hx0 hy0 hxy.symm, LatticeIndexBis.addVal_map ϖ hϖ hϖ' x hx0,
    LatticeIndexBis.addVal_map ϖ hϖ hϖ' (y : O) hy0]

end Formalism.LatticeBaseChangeAlt
