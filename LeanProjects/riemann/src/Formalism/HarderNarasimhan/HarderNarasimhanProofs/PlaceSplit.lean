import Formalism.HarderNarasimhan.DefsPl

open Module NumberField Matrix

noncomputable section

namespace Formalism.HN

namespace PlaceDecomposition
section

theorem dense_comb (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]
    (t : InfinitePlace K → ℂ) :
    ∃ r : Free.ChooseBasisIndex ℤ (𝓞 K) → ℝ, ∀ u : InfinitePlace K,
      ∑ k, (r k : ℂ) * u.embedding ((RingOfIntegers.basis K k : 𝓞 K) : K) = t u := by
  obtain ⟨y, hy0⟩ : ∃ y : mixedEmbedding.mixedSpace K,
      ∀ w : {w : InfinitePlace K // w.IsComplex}, y.2 w = t w.1 :=
    ⟨(0, fun w => t w.1), fun _ => rfl⟩
  refine ⟨fun k => (mixedEmbedding.latticeBasis K).repr y k, fun u => ?_⟩
  have hu : u.IsComplex := by
    first
      | exact IsTotallyComplex.isComplex u
      | exact NumberField.IsTotallyComplex.isComplex u
  have hy := congrArg (fun z : mixedEmbedding.mixedSpace K => z.2 ⟨u, hu⟩)
    ((mixedEmbedding.latticeBasis K).sum_repr y)
  simp only [Prod.snd_sum, Finset.sum_apply, Prod.smul_snd, Pi.smul_apply,
    mixedEmbedding.latticeBasis_apply, hy0] at hy
  rw [← hy]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Complex.real_smul]
  congr 1
  rw [NumberField.integralBasis_apply]
  rfl

variable {K V ι : Type*} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Fintype ι] [DecidableEq ι]

theorem realize_apply (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (x : V)
    (p : InfinitePlace K × ι × Fin 2) :
    Formalism.HermitianLatticesTheory.realize b X x p =
      if p.2.2 = 0 then (Formalism.HermitianLatticesTheory.fcoord b X p.1 x p.2.1).re else (Formalism.HermitianLatticesTheory.fcoord b X p.1 x p.2.1).im := by
  first
    | rfl
    | simp [Formalism.HermitianLatticesTheory.realize]
    | (unfold Formalism.HermitianLatticesTheory.realize; done)

theorem fcoord_smul (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K)
    (a : K) (x : V) : Formalism.HermitianLatticesTheory.fcoord b X v (a • x) = v.embedding a • Formalism.HermitianLatticesTheory.fcoord b X v x := by
  unfold Formalism.HermitianLatticesTheory.fcoord
  have hv : Formalism.HermitianLatticesTheory.vecAt b v (a • x) = v.embedding a • Formalism.HermitianLatticesTheory.vecAt b v x := by
    first
      | (funext i; simp [Formalism.HermitianLatticesTheory.vecAt, map_mul])
      | (funext i; simp [Formalism.HermitianLatticesTheory.vecAt, Finsupp.smul_apply, map_mul])
      | (unfold Formalism.HermitianLatticesTheory.vecAt; done)
  rw [hv, Matrix.mulVec_smul]

end

section

theorem li_map {K L : Type*} [Field K] [Field L] (σ : K →+* L) {n m : Type*} [Fintype n]
    [Fintype m] [DecidableEq n] [DecidableEq m] (u : n → m → K) (hu : LinearIndependent K u) :
    LinearIndependent L (fun k i => σ (u k i)) := by
  classical
  let f : (n → K) →ₗ[K] (m → K) :=
    { toFun := fun c => ∑ k, c k • u k
      map_add' := by
        intro a c
        simp [add_smul, Finset.sum_add_distrib]
      map_smul' := by
        intro a c
        simp [Finset.smul_sum, smul_smul] }
  have hfinj : Function.Injective f := by
    intro a c hac
    have h0 := (Fintype.linearIndependent_iff.1 hu) (a - c) (by
      simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]
      exact sub_eq_zero.2 hac)
    funext k
    exact sub_eq_zero.1 (h0 k)
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective f (LinearMap.ker_eq_bot.2 hfinj)
  have hgu : ∀ k, g (u k) = Pi.single k 1 := by
    intro k
    have h1 : f (Pi.single k 1) = u k := by
      show ∑ j, (Pi.single k (1 : K) : n → K) j • u j = u k
      simp [Pi.single_apply]
    rw [← h1]
    exact LinearMap.congr_fun hg _
  have hexp : ∀ k, g (u k) = ∑ i, u k i • g (Pi.single i 1) := by
    intro k
    have hx : u k = ∑ i, u k i • (Pi.single i (1 : K) : m → K) := by
      funext j
      simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [hx]
    simp only [map_sum, map_smul]
  have hid : ∀ k k', ∑ i, σ (u k i) * σ (g (Pi.single i 1) k') = if k' = k then 1 else 0 := by
    intro k k'
    have h0 := congrFun ((hexp k).symm.trans (hgu k)) k'
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h0
    have h1 := congrArg σ h0
    rw [map_sum] at h1
    simp only [map_mul] at h1
    rw [h1, Pi.single_apply]
    split_ifs <;> simp
  rw [Fintype.linearIndependent_iff]
  intro c hc k'
  have hc' : ∀ i, ∑ k, c k * σ (u k i) = 0 := by
    intro i
    have h0 := congrFun hc i
    simpa [Finset.sum_apply] using h0
  calc c k' = ∑ k, c k * (if k' = k then 1 else 0) := by simp
    _ = ∑ k, c k * ∑ i, σ (u k i) * σ (g (Pi.single i 1) k') := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hid k k']
    _ = ∑ i, (∑ k, c k * σ (u k i)) * σ (g (Pi.single i 1) k') := by
        simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
        exact Finset.sum_comm
    _ = 0 := by simp [hc']

variable {P ι : Type*} [Fintype P] [DecidableEq P] [Fintype ι]

def prj (v : P) : EuclideanSpace ℝ (P × ι × Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (P × ι × Fin 2) where
  toFun w := (WithLp.equiv 2 _).symm (fun p => if p.1 = v then w p else 0)
  map_add' x y := by ext p; by_cases h : p.1 = v <;> simp [h]
  map_smul' c x := by ext p; by_cases h : p.1 = v <;> simp [h]

def psi (v : P) : (ι → ℂ) →ₗ[ℝ] EuclideanSpace ℝ (P × ι × Fin 2) where
  toFun z := (WithLp.equiv 2 _).symm
    (fun p => if p.1 = v then (if p.2.2 = 0 then (z p.2.1).re else (z p.2.1).im) else 0)
  map_add' x y := by ext p; by_cases h : p.1 = v <;> by_cases h' : p.2.2 = 0 <;> simp [h, h']
  map_smul' c x := by ext p; by_cases h : p.1 = v <;> by_cases h' : p.2.2 = 0 <;> simp [h, h']

theorem prj_apply (v : P) (w : EuclideanSpace ℝ (P × ι × Fin 2)) (p : P × ι × Fin 2) :
    prj v w p = if p.1 = v then w p else 0 := rfl

theorem psi_apply (v : P) (z : ι → ℂ) (p : P × ι × Fin 2) :
    psi v z p = if p.1 = v then (if p.2.2 = 0 then (z p.2.1).re else (z p.2.1).im) else 0 := rfl

theorem psi_injective (v : P) : Function.Injective (psi (ι := ι) v) := by
  intro z z' h
  funext k
  have h0 := congrArg (fun w => w (v, k, 0)) h
  have h1 := congrArg (fun w => w (v, k, 1)) h
  exact Complex.ext (by simpa [psi_apply] using h0) (by simpa [psi_apply] using h1)

theorem mem_placePart (v : P) (w : EuclideanSpace ℝ (P × ι × Fin 2)) :
    w ∈ placePart v ↔ ∀ p : P × ι × Fin 2, p.1 ≠ v → w p = 0 := by
  first
    | exact Iff.rfl
    | simp [placePart]
    | (unfold placePart; simp)

theorem prj_mem (v : P) (w : EuclideanSpace ℝ (P × ι × Fin 2)) : prj v w ∈ placePart v := by
  rw [mem_placePart]
  intro p hp
  rw [prj_apply, if_neg hp]

theorem prj_of_mem (v : P) (w : EuclideanSpace ℝ (P × ι × Fin 2)) (hw : w ∈ placePart v) :
    prj v w = w := by
  ext p
  rw [prj_apply]
  split_ifs with h
  · rfl
  · exact ((mem_placePart v w).1 hw p h).symm

theorem sum_prj (w : EuclideanSpace ℝ (P × ι × Fin 2)) : ∑ v, prj v w = w := by
  ext p
  first
    | rw [Finset.sum_apply]
    | erw [Finset.sum_apply]
    | simp only [WithLp.ofLp_sum, Finset.sum_apply]
  simp [prj_apply]

end

section

variable {K V ι : Type*} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [Fintype ι] [DecidableEq ι]

theorem fcoord_osmul (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K)
    (a : 𝓞 K) (x : V) :
    Formalism.HermitianLatticesTheory.fcoord b X v (a • x) = v.embedding (a : K) • Formalism.HermitianLatticesTheory.fcoord b X v x := by
  rw [← algebraMap_smul K a x]
  exact fcoord_smul b X v _ x

theorem fcoord_lincomb (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K)
    {n : Type*} [Fintype n] (c : n → K) (y : n → V) :
    Formalism.HermitianLatticesTheory.fcoord b X v (∑ k, c k • y k) = ∑ k, v.embedding (c k) • Formalism.HermitianLatticesTheory.fcoord b X v (y k) := by
  have hadd : ∀ x y : V, Formalism.HermitianLatticesTheory.fcoord b X v (x + y) =
      Formalism.HermitianLatticesTheory.fcoord b X v x + Formalism.HermitianLatticesTheory.fcoord b X v y := by
    intro x y
    unfold Formalism.HermitianLatticesTheory.fcoord
    rw [← Matrix.mulVec_add]
    congr 1
    funext i
    simp [Formalism.HermitianLatticesTheory.vecAt]
  have hzero : Formalism.HermitianLatticesTheory.fcoord b X v 0 = 0 := by
    simpa using fcoord_smul b X v 0 0
  let F : V →+ (ι → ℂ) :=
    { toFun := Formalism.HermitianLatticesTheory.fcoord b X v, map_zero' := hzero, map_add' := hadd }
  change F (∑ k, c k • y k) = _
  rw [map_sum]
  exact Finset.sum_congr rfl fun k _ => fcoord_smul b X v (c k) (y k)

theorem realize_mem (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (N : Submodule (𝓞 K) V)
    {x : V} (hx : x ∈ N) :
    Formalism.HermitianLatticesTheory.realize b X x ∈ Submodule.span ℝ
      (zl (Formalism.HermitianLatticesTheory.realize b X) N : Set (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))) := by
  first
    | exact Submodule.subset_span ⟨x, hx, rfl⟩
    | exact Submodule.subset_span (AddSubgroup.mem_map.2 ⟨x, hx, rfl⟩)
    | exact Submodule.subset_span (Set.mem_image_of_mem _ hx)

theorem re_comb {κ : Type*} [Fintype κ] (r : κ → ℝ) (c : κ → ℂ) (f : ℂ) :
    ∑ k, r k * (c k * f).re = ((∑ k, (r k : ℂ) * c k) * f).re := by
  rw [Finset.sum_mul, Complex.re_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_assoc, Complex.re_ofReal_mul]

theorem im_comb {κ : Type*} [Fintype κ] (r : κ → ℝ) (c : κ → ℂ) (f : ℂ) :
    ∑ k, r k * (c k * f).im = ((∑ k, (r k : ℂ) * c k) * f).im := by
  rw [Finset.sum_mul, Complex.im_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_assoc, Complex.im_ofReal_mul]

variable [DecidableEq (InfinitePlace K)]

theorem prj_realize (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K)
    (x : V) : prj v (Formalism.HermitianLatticesTheory.realize b X x) = psi v (Formalism.HermitianLatticesTheory.fcoord b X v x) := by
  ext p
  rw [prj_apply, psi_apply, realize_apply]
  split_ifs with h1 h2 <;> (try subst h1) <;> rfl

theorem prj_realize_comb (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (v : InfinitePlace K) (r : Free.ChooseBasisIndex ℤ (𝓞 K) → ℝ)
    (hr : ∀ u : InfinitePlace K,
      ∑ k, (r k : ℂ) * u.embedding ((RingOfIntegers.basis K k : 𝓞 K) : K) = if u = v then 1 else 0)
    (x : V) :
    prj v (Formalism.HermitianLatticesTheory.realize b X x) =
      ∑ k, r k • Formalism.HermitianLatticesTheory.realize b X ((RingOfIntegers.basis K k : 𝓞 K) • x) := by
  ext p
  rw [prj_apply]
  simp only [WithLp.ofLp_sum, Finset.sum_apply, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul,
    realize_apply, fcoord_osmul]
  by_cases h2 : p.2.2 = 0
  · simp only [h2, ↓reduceIte]
    rw [re_comb, hr p.1]
    by_cases h1 : p.1 = v <;> simp [h1]
  · simp only [h2, ↓reduceIte]
    rw [im_comb, hr p.1]
    by_cases h1 : p.1 = v <;> simp [h1]

theorem prj_mem_span (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (N : Submodule (𝓞 K) V) (v : InfinitePlace K)
    (w : EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))
    (hw : w ∈ Submodule.span ℝ
      (zl (Formalism.HermitianLatticesTheory.realize b X) N : Set (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2)))) :
    prj v w ∈ Submodule.span ℝ
      (zl (Formalism.HermitianLatticesTheory.realize b X) N : Set (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))) := by
  have key : Submodule.span ℝ (zl (Formalism.HermitianLatticesTheory.realize b X) N :
        Set (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))) ≤
      (Submodule.span ℝ (zl (Formalism.HermitianLatticesTheory.realize b X) N :
        Set (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2)))).comap (prj v) := by
    rw [Submodule.span_le]
    intro s hs
    have hs' : s ∈ (N.toAddSubgroup.map (Formalism.HermitianLatticesTheory.realize b X)) := hs
    obtain ⟨x, hx, rfl⟩ := AddSubgroup.mem_map.1 hs'
    show prj v (Formalism.HermitianLatticesTheory.realize b X x) ∈ Submodule.span ℝ (zl (Formalism.HermitianLatticesTheory.realize b X) N :
        Set (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2)))
    obtain ⟨r, hr⟩ := dense_comb K (fun u => if u = v then (1 : ℂ) else 0)
    rw [prj_realize_comb b X v r hr x]
    refine Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    exact AddSubgroup.mem_map.2 ⟨_, N.smul_mem _ hx, rfl⟩
  exact key hw

theorem split_eq (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (N : Submodule (𝓞 K) V) :
    Submodule.span ℝ (zl (Formalism.HermitianLatticesTheory.realize b X) N :
        Set (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))) =
      ⨆ v, Submodule.span ℝ (zl (Formalism.HermitianLatticesTheory.realize b X) N :
        Set (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))) ⊓ placePart v := by
  apply le_antisymm
  · intro w hw
    rw [← sum_prj w]
    exact Submodule.sum_mem _ fun v _ =>
      Submodule.mem_iSup_of_mem v (Submodule.mem_inf.2 ⟨prj_mem_span b X N v w hw, prj_mem v w⟩)
  · exact iSup_le fun v => inf_le_left

end

section

variable {K V ι : Type*} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [Fintype ι] [DecidableEq ι]

theorem span_real_eq_complex (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (N : Submodule (𝓞 K) V) (v : InfinitePlace K) :
    (Submodule.span ℂ (Formalism.HermitianLatticesTheory.fcoord b X v '' (N : Set V))).restrictScalars ℝ =
      Submodule.span ℝ (Formalism.HermitianLatticesTheory.fcoord b X v '' (N : Set V)) := by
  have hmul : ∀ (c : 𝓞 K) (w : ι → ℂ), w ∈ Submodule.span ℝ (Formalism.HermitianLatticesTheory.fcoord b X v '' (N : Set V)) →
      v.embedding (c : K) • w ∈ Submodule.span ℝ (Formalism.HermitianLatticesTheory.fcoord b X v '' (N : Set V)) := by
    intro c w hw
    have key : Submodule.span ℝ (Formalism.HermitianLatticesTheory.fcoord b X v '' (N : Set V)) ≤
        (Submodule.span ℝ (Formalism.HermitianLatticesTheory.fcoord b X v '' (N : Set V))).comap
          (DistribMulAction.toLinearMap ℝ (ι → ℂ) (v.embedding (c : K))) := by
      rw [Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      show v.embedding (c : K) • Formalism.HermitianLatticesTheory.fcoord b X v x ∈
        Submodule.span ℝ (Formalism.HermitianLatticesTheory.fcoord b X v '' (N : Set V))
      rw [← fcoord_osmul]
      exact Submodule.subset_span ⟨c • x, N.smul_mem c hx, rfl⟩
    exact key hw
  have hC : ∀ (z : ℂ) (w : ι → ℂ), w ∈ Submodule.span ℝ (Formalism.HermitianLatticesTheory.fcoord b X v '' (N : Set V)) →
      z • w ∈ Submodule.span ℝ (Formalism.HermitianLatticesTheory.fcoord b X v '' (N : Set V)) := by
    intro z w hw
    obtain ⟨r, hr⟩ := dense_comb K (fun _ => z)
    have hz : ∑ k, (r k : ℂ) * v.embedding ((RingOfIntegers.basis K k : 𝓞 K) : K) = z := hr v
    rw [← hz, Finset.sum_smul]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [mul_smul, Complex.coe_smul]
    exact Submodule.smul_mem _ _ (hmul _ w hw)
  let W : Submodule ℂ (ι → ℂ) :=
    { carrier := (Submodule.span ℝ (Formalism.HermitianLatticesTheory.fcoord b X v '' (N : Set V)) : Set (ι → ℂ))
      add_mem' := fun ha hb => Submodule.add_mem _ ha hb
      zero_mem' := Submodule.zero_mem _
      smul_mem' := fun z w hw => hC z w hw }
  apply le_antisymm
  · intro w hw
    have hle : Submodule.span ℂ (Formalism.HermitianLatticesTheory.fcoord b X v '' (N : Set V)) ≤ W :=
      Submodule.span_le.2 (fun x hx => Submodule.subset_span hx)
    exact hle hw
  · exact Submodule.span_le_restrictScalars ℝ ℂ _

theorem finrank_span_complex (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (N : Submodule (𝓞 K) V) (v : InfinitePlace K) :
    finrank ℂ (Submodule.span ℂ (Formalism.HermitianLatticesTheory.fcoord b X v '' (N : Set V))) = rkK N := by
  classical
  have hA : Function.Injective (Matrix.mulVecLin (X v)⁻¹) := by
    intro a c h
    have h' := congrArg (Matrix.mulVec (X v)) h
    simpa [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (hX v)] using h'
  have himg : Formalism.HermitianLatticesTheory.fcoord b X v '' (N : Set V) =
      (Matrix.mulVecLin (X v)⁻¹) '' (Formalism.HermitianLatticesTheory.vecAt b v '' (N : Set V)) := by
    rw [Set.image_image]
    rfl
  rw [himg, ← Submodule.map_span, ← (Submodule.equivMapOfInjective _ hA _).finrank_eq]
  haveI : Module.Finite K V := Module.Finite.of_basis b
  obtain ⟨t, htN, hspan, hli⟩ := exists_linearIndependent K (N : Set V)
  haveI : Fintype t := by
    first
      | exact hli.setFinite.fintype
      | exact @Fintype.ofFinite _ hli.finite
  have hadd : ∀ x y : V, Formalism.HermitianLatticesTheory.vecAt b v (x + y) =
      Formalism.HermitianLatticesTheory.vecAt b v x + Formalism.HermitianLatticesTheory.vecAt b v y := by
    intro x y
    funext i
    simp [Formalism.HermitianLatticesTheory.vecAt]
  have hsmul : ∀ (a : K) (x : V), Formalism.HermitianLatticesTheory.vecAt b v (a • x) =
      v.embedding a • Formalism.HermitianLatticesTheory.vecAt b v x := by
    intro a x
    funext i
    simp [Formalism.HermitianLatticesTheory.vecAt, map_mul]
  have hzero : Formalism.HermitianLatticesTheory.vecAt b v 0 = 0 := by
    funext i
    simp [Formalism.HermitianLatticesTheory.vecAt]
  let y : t → ι → ℂ := fun j => Formalism.HermitianLatticesTheory.vecAt b v (j : V)
  have hliC : LinearIndependent ℂ y := by
    have h1 : LinearIndependent K (fun j : t => b.equivFun (j : V)) :=
      hli.map' b.equivFun.toLinearMap b.equivFun.ker
    have h2 := li_map v.embedding (fun (j : t) (i : ι) => b.equivFun (j : V) i) h1
    have h3 : y = fun (j : t) (i : ι) => v.embedding (b.equivFun (j : V) i) := by
      funext j i
      simp [y, Formalism.HermitianLatticesTheory.vecAt, Basis.equivFun_apply]
    rw [h3]
    exact h2
  have hsp : Submodule.span ℂ (Formalism.HermitianLatticesTheory.vecAt b v '' (N : Set V)) =
      Submodule.span ℂ (Set.range y) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      let Q : Submodule K V :=
        { carrier := {x | Formalism.HermitianLatticesTheory.vecAt b v x ∈ Submodule.span ℂ (Set.range y)}
          add_mem' := fun {a c} ha hc => by
            show Formalism.HermitianLatticesTheory.vecAt b v (a + c) ∈ Submodule.span ℂ (Set.range y)
            rw [hadd]
            exact Submodule.add_mem _ ha hc
          zero_mem' := by
            show Formalism.HermitianLatticesTheory.vecAt b v 0 ∈ Submodule.span ℂ (Set.range y)
            rw [hzero]
            exact Submodule.zero_mem _
          smul_mem' := fun a c hc => by
            show Formalism.HermitianLatticesTheory.vecAt b v (a • c) ∈ Submodule.span ℂ (Set.range y)
            rw [hsmul]
            exact Submodule.smul_mem _ _ hc }
      have hle : Submodule.span K t ≤ Q := by
        rw [Submodule.span_le]
        intro j hj
        exact Submodule.subset_span ⟨⟨j, hj⟩, rfl⟩
      have hx' : x ∈ Submodule.span K t := by
        rw [hspan]
        exact Submodule.subset_span hx
      exact hle hx'
    · rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      exact Submodule.subset_span ⟨(j : V), htN j.2, rfl⟩
  rw [hsp, finrank_span_eq_card hliC]
  unfold rkK
  rw [← hspan]
  have h3 := finrank_span_eq_card hli
  first
    | rw [Subtype.range_coe] at h3
    | rw [Subtype.range_val] at h3
    | simp only [Subtype.range_coe_subtype, Set.setOf_mem_eq] at h3
  exact h3.symm

theorem finrank_real_span (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (N : Submodule (𝓞 K) V) (v : InfinitePlace K) :
    finrank ℝ (Submodule.span ℝ (Formalism.HermitianLatticesTheory.fcoord b X v '' (N : Set V))) = 2 * rkK N := by
  rw [← span_real_eq_complex b X N v, ← finrank_span_complex b X hX N v]
  exact finrank_real_of_complex _

end

section

variable {K V ι : Type*} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [Fintype ι] [DecidableEq ι] [DecidableEq (InfinitePlace K)]

theorem piece_eq_map (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (N : Submodule (𝓞 K) V) (v : InfinitePlace K) :
    Submodule.span ℝ (zl (Formalism.HermitianLatticesTheory.realize b X) N :
        Set (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))) ⊓ placePart v =
      (Submodule.span ℝ (Formalism.HermitianLatticesTheory.fcoord b X v '' (N : Set V))).map (psi v) := by
  apply le_antisymm
  · intro w hw
    obtain ⟨hwS, hwP⟩ := Submodule.mem_inf.1 hw
    rw [← prj_of_mem v w hwP]
    have key : Submodule.span ℝ (zl (Formalism.HermitianLatticesTheory.realize b X) N :
          Set (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))) ≤
        ((Submodule.span ℝ (Formalism.HermitianLatticesTheory.fcoord b X v '' (N : Set V))).map (psi v)).comap (prj v) := by
      rw [Submodule.span_le]
      intro s hs
      have hs' : s ∈ (N.toAddSubgroup.map (Formalism.HermitianLatticesTheory.realize b X)) := hs
      obtain ⟨x, hx, rfl⟩ := AddSubgroup.mem_map.1 hs'
      show prj v (Formalism.HermitianLatticesTheory.realize b X x) ∈
        (Submodule.span ℝ (Formalism.HermitianLatticesTheory.fcoord b X v '' (N : Set V))).map (psi v)
      rw [prj_realize]
      exact Submodule.mem_map_of_mem (Submodule.subset_span ⟨x, hx, rfl⟩)
    exact key hwS
  · rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    rw [← prj_realize]
    exact Submodule.mem_inf.2 ⟨prj_mem_span b X N v _ (realize_mem b X N hx), prj_mem v _⟩

theorem finrank_piece (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (N : Submodule (𝓞 K) V) (v : InfinitePlace K) :
    Module.finrank ℝ (Submodule.span ℝ (zl (Formalism.HermitianLatticesTheory.realize b X) N :
        Set (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))) ⊓ placePart v : Submodule ℝ _) =
      2 * rkK N := by
  rw [piece_eq_map, ← (Submodule.equivMapOfInjective (psi v) (psi_injective (ι := ι) v) _).finrank_eq]
  exact finrank_real_span b X hX N v

end
end PlaceDecomposition

theorem place_decomposition : PlaceSplit := by
  intro K V ι _ _ _ _ _ _ _ _ _ _ b X hX N _
  classical
  exact ⟨PlaceDecomposition.split_eq b X N, fun v => PlaceDecomposition.finrank_piece b X hX N v⟩

end Formalism.HN
