import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NuInRange

noncomputable section

namespace GlobalTheory.Mem.DivModel

open Formalism.BasicNotions NumberField IsDedekindDomain TensorProduct

section Gen

variable {K : Type} [Field K] {V M ι : Type} [AddCommGroup V] [Module K V] [AddCommGroup M] [Module ℂ M]

def ext (σ : K →+* ℂ) (e : V →ₛₗ[σ] M) (b : Module.Basis ι K V) :
    letI := σ.toAlgebra; ℂ ⊗[K] V →ₗ[ℂ] M :=
  letI := σ.toAlgebra
  (Algebra.TensorProduct.basis ℂ b).constr ℂ (fun a => e (b a))

theorem ext_one_tmul [Fintype ι] (σ : K →+* ℂ) (e : V →ₛₗ[σ] M) (b : Module.Basis ι K V) (x : V) :
    letI := σ.toAlgebra; ext σ e b ((1 : ℂ) ⊗ₜ[K] x) = e x := by
  letI := σ.toAlgebra
  conv_lhs => rw [← b.sum_repr x]
  conv_rhs => rw [← b.sum_repr x]
  rw [TensorProduct.tmul_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [LinearMap.map_smulₛₗ, TensorProduct.tmul_smul, ← algebraMap_smul ℂ, map_smul]
  congr 1
  rw [← Algebra.TensorProduct.basis_apply, ext, Module.Basis.constr_basis]

theorem ext_inj (σ : K →+* ℂ) (e : V →ₛₗ[σ] M) (b : Module.Basis ι K V)
    (h : LinearIndependent ℂ (fun a => e (b a))) : Function.Injective (ext σ e b) := by
  letI := σ.toAlgebra
  exact Module.Basis.injective_constr_of_linearIndependent _ h

theorem li_comp [Fintype ι] {V' ι' : Type} [AddCommGroup V'] [Module K V'] (σ : K →+* ℂ) (e : V →ₛₗ[σ] M)
    (b : Module.Basis ι K V) (h : LinearIndependent ℂ (fun a => e (b a))) (ψ : V' →ₗ[K] V)
    (hψ : Function.Injective ψ) (b' : Module.Basis ι' K V') :
    LinearIndependent ℂ (fun a => e (ψ (b' a))) := by
  letI := σ.toAlgebra
  have h1 : Function.Injective (ψ.baseChange ℂ) := Module.Flat.lTensor_preserves_injective_linearMap ψ hψ
  have h2 := (Algebra.TensorProduct.basis ℂ b').linearIndependent.map' (ext σ e b ∘ₗ ψ.baseChange ℂ)
    (LinearMap.ker_eq_bot.2 ((ext_inj σ e b h).comp h1))
  refine (congrArg (fun f => LinearIndependent ℂ f) (funext fun a => ?_)).mpr h2
  simp only [Function.comp, LinearMap.comp_apply, Algebra.TensorProduct.basis_apply, LinearMap.baseChange_tmul]
  rw [ext_one_tmul]

theorem ker_rational [Fintype ι] {J : Type} [Fintype J] (σ : K →+* ℂ) (e : V →ₛₗ[σ] M)
    (b : Module.Basis ι K V) (h : LinearIndependent ℂ (fun a => e (b a))) (N : J → M →ₗ[ℂ] M)
    (n : J → V →ₗ[K] V) (hn : ∀ j x, e (n j x) = N j (e x)) (φ : M)
    (hφ : φ ∈ Submodule.span ℂ (Set.range (fun a => e (b a)))) (h0 : ∀ j, N j φ = 0) :
    φ ∈ Submodule.span ℂ (e '' {x | ∀ j, n j x = 0}) := by
  classical
  letI := σ.toAlgebra
  obtain ⟨t, rfl⟩ : φ ∈ LinearMap.range (ext σ e b) := by
    rw [ext, Module.Basis.constr_range]; exact hφ
  have hc : ∀ j t, ext σ e b ((n j).baseChange ℂ t) = N j (ext σ e b t) := by
    intro j t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul c x =>
      have : ∀ y : V, c ⊗ₜ[K] y = c • ((1 : ℂ) ⊗ₜ[K] y) := fun y => by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [LinearMap.baseChange_tmul, this, this, map_smul, map_smul, map_smul, ext_one_tmul, ext_one_tmul, hn]
  have ht : ∀ j, (n j).baseChange ℂ t = 0 := fun j =>
    ext_inj σ e b h (by rw [hc, h0, map_zero])
  set P : V →ₗ[K] (J → V) := LinearMap.pi n with hP
  obtain ⟨g, hg⟩ : ∃ g : (J → V) →ₗ[K] V, P ∘ₗ g ∘ₗ P = P := by
    obtain ⟨s, hs⟩ := P.rangeRestrict.exists_rightInverse_of_surjective P.range_rangeRestrict
    obtain ⟨g, hg⟩ := LinearMap.exists_extend s
    refine ⟨g, LinearMap.ext fun x => ?_⟩
    have h1 : g (P x) = s (P.rangeRestrict x) := by rw [← hg]; rfl
    have h2 := LinearMap.congr_fun hs (P.rangeRestrict x)
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at h2 ⊢
    rw [h1]
    exact congrArg Subtype.val h2
  have hsum : g ∘ₗ P = ∑ j, (g ∘ₗ LinearMap.single K (fun _ => V) j) ∘ₗ n j := by
    ext x
    simp only [LinearMap.comp_apply, LinearMap.sum_apply, ← map_sum]
    congr 1
    ext j
    simp [hP, Finset.sum_apply, Pi.single_apply]
  have hz : (g ∘ₗ P).baseChange ℂ t = 0 := by
    rw [hsum, ← LinearMap.baseChangeHom_apply, map_sum, LinearMap.sum_apply]
    refine Finset.sum_eq_zero (fun j _ => ?_)
    rw [LinearMap.baseChangeHom_apply, LinearMap.baseChange_comp, LinearMap.comp_apply, ht, map_zero]
  have ht' : t = (LinearMap.id - g ∘ₗ P).baseChange ℂ t := by
    rw [LinearMap.baseChange_sub, LinearMap.sub_apply, hz]; simp
  rw [ht']
  generalize t = s
  induction s using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add]; exact Submodule.add_mem _ hx hy
  | tmul c x =>
    have : ∀ y : V, c ⊗ₜ[K] y = c • ((1 : ℂ) ⊗ₜ[K] y) := fun y => by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [LinearMap.baseChange_tmul, this, map_smul, ext_one_tmul]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, fun j => ?_, rfl⟩)
    have h3 := congrFun (LinearMap.congr_fun hg x) j
    simp only [LinearMap.comp_apply, hP, LinearMap.pi_apply] at h3
    simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, map_sub, hP, h3, sub_self]

theorem span_image_le [Fintype ι] (σ : K →+* ℂ) (e : V →ₛₗ[σ] M) (b : Module.Basis ι K V) (x : V) :
    e x ∈ Submodule.span ℂ (Set.range (fun a => e (b a))) := by
  rw [← b.sum_repr x, map_sum]
  refine Submodule.sum_mem _ (fun i _ => ?_)
  rw [LinearMap.map_smulₛₗ]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

end Gen

section Frames

variable {K : Type} [Field K] [NumberField K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V]

theorem exists_frame {n : ℕ} (v : InfinitePlace K) (b : Module.Basis (Fin n) K V) {E : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] (e : V →ₛₗ[v.embedding] E)
    (h : LinearIndependent ℂ (fun a => e (b a))) :
    ∃ X : Matrix (Fin n) (Fin n) ℂ, IsUnit X.det ∧
      ∀ x, Formalism.HermitianLatticesTheory.cnorm (Matrix.mulVec X⁻¹ (Formalism.HermitianLatticesTheory.vecAt b v x)) = ‖e x‖ := by
  let L : (Fin n → ℂ) →ₗ[ℂ] E := Fintype.linearCombination ℂ (fun a => e (b a))
  have hL : Function.Injective L := h.fintypeLinearCombination_injective
  have hr : Module.finrank ℂ (LinearMap.range L) = n := by
    rw [LinearMap.finrank_range_of_inj hL]; simp
  let c : OrthonormalBasis (Fin n) ℂ (LinearMap.range L) :=
    (stdOrthonormalBasis ℂ (LinearMap.range L)).reindex (finCongr hr)
  let T : (Fin n → ℂ) ≃ₗ[ℂ] (Fin n → ℂ) :=
    ((LinearEquiv.ofInjective L hL).trans c.repr.toLinearEquiv).trans (WithLp.linearEquiv 2 ℂ (Fin n → ℂ))
  have hT : IsUnit (LinearMap.toMatrix' T.toLinearMap).det := by
    rw [LinearMap.det_toMatrix']; exact T.isUnit_det'
  refine ⟨(LinearMap.toMatrix' T.toLinearMap)⁻¹, Matrix.isUnit_nonsing_inv_det _ hT, fun x => ?_⟩
  rw [Matrix.nonsing_inv_nonsing_inv _ hT, LinearMap.toMatrix'_mulVec]
  have h1 : e x = L (Formalism.HermitianLatticesTheory.vecAt b v x) := by
    conv_lhs => rw [← b.sum_repr x, map_sum]
    simp only [L, Fintype.linearCombination_apply, LinearMap.map_smulₛₗ, Formalism.HermitianLatticesTheory.vecAt]
  have h2 : ‖L (Formalism.HermitianLatticesTheory.vecAt b v x)‖ = ‖c.repr (LinearEquiv.ofInjective L hL (Formalism.HermitianLatticesTheory.vecAt b v x))‖ := by
    rw [LinearIsometryEquiv.norm_map]; rfl
  rw [h1, h2, EuclideanSpace.norm_eq]
  rfl

def fco {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (v : InfinitePlace K) : V →ₛₗ[v.embedding] EuclideanSpace ℂ ι where
  toFun x := WithLp.toLp 2 (Formalism.HermitianLatticesTheory.fcoord b X v x)
  map_add' x y := by rw [Formalism.HermitianLatticesTheory.fcoord_add]; rfl
  map_smul' a x := by
    have : Formalism.HermitianLatticesTheory.vecAt b v (a • x) = v.embedding a • Formalism.HermitianLatticesTheory.vecAt b v x := by
      funext i; simp [Formalism.HermitianLatticesTheory.vecAt]
    simp only [Formalism.HermitianLatticesTheory.fcoord, this, Matrix.mulVec_smul]; rfl

theorem fco_li {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (v : InfinitePlace K) (hX : IsUnit (X v).det) : LinearIndependent ℂ (fun a => fco b X v (b a)) := by
  have h1 : Function.Injective (Matrix.mulVecLin (X v)⁻¹) :=
    Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_nonsing_inv_det _ hX))
  have h2 := (Pi.basisFun ℂ ι).linearIndependent.map'
    ((WithLp.linearEquiv 2 ℂ (ι → ℂ)).symm.toLinearMap ∘ₗ Matrix.mulVecLin (X v)⁻¹)
    (LinearMap.ker_eq_bot.2 ((WithLp.linearEquiv 2 ℂ (ι → ℂ)).symm.injective.comp h1))
  refine (congrArg (fun f => LinearIndependent ℂ f) (funext fun a => ?_)).mpr h2
  have : Formalism.HermitianLatticesTheory.vecAt b v (b a) = Pi.basisFun ℂ ι a := by
    funext i
    simp only [Formalism.HermitianLatticesTheory.vecAt, Module.Basis.repr_self, Pi.basisFun_apply, Finsupp.single_apply, Pi.single_apply]
    by_cases h : a = i
    · simp [h]
    · simp [h, Ne.symm h]
  show WithLp.toLp 2 (Matrix.mulVec (X v)⁻¹ (Formalism.HermitianLatticesTheory.vecAt b v (b a))) = _
  rw [this]; rfl

theorem exists_frames {n : ℕ} (A : HLat K) (hA : ∀ v, IsUnit (A.X v).det) (b : Module.Basis (Fin n) K V)
    (ψ : V →ₗ[K] A.V) (hψ : Function.Injective ψ) :
    ∃ X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ, (∀ v, IsUnit (X v).det) ∧
      ∀ v x, Formalism.HermitianLatticesTheory.normAt b X v x = Formalism.HermitianLatticesTheory.normAt A.b A.X v (ψ x) := by
  have := fun v => exists_frame v b ((fco A.b A.X v).comp ψ)
    (li_comp v.embedding (fco A.b A.X v) A.b (fco_li A.b A.X v (hA v)) ψ hψ b)
  choose X hX hn using this
  refine ⟨X, hX, fun v x => (hn v x).trans ?_⟩
  rw [EuclideanSpace.norm_eq]; rfl

end Frames

section Std

variable {K : Type} [Field K] [NumberField K] [StarRing K]

def coord (e : K →+* ℂ) {W : Type} [AddCommGroup W] [Module ℂ W] {n : ℕ} (c : Fin n → W) :
    (Fin n → K) →ₛₗ[e] W where
  toFun x := ∑ i, e (x i) • c i
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a x := by simp [Finset.smul_sum, mul_smul]

set_option linter.unusedSectionVars false in
theorem coord_basisFun (e : K →+* ℂ) {W : Type} [AddCommGroup W] [Module ℂ W] {n : ℕ} (c : Fin n → W)
    (i : Fin n) : coord e c (Pi.basisFun K (Fin n) i) = c i := by
  simp [coord, Pi.single_apply, apply_ite e, ite_smul]

theorem normAt_id (e : K →+* ℂ) {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] {n : ℕ}
    (c : OrthonormalBasis (Fin n) ℂ W) (x : Fin n → K) :
    Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin n)) (fun _ => 1) (InfinitePlace.mk e) x = ‖coord e c x‖ := by
  have h1 : coord e c x = c.repr.symm (WithLp.toLp 2 (fun i => e (x i))) := by
    rw [← c.sum_repr_symm]; rfl
  rw [h1, LinearIsometryEquiv.norm_map, EuclideanSpace.norm_eq]
  unfold Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.cnorm Formalism.HermitianLatticesTheory.fcoord Formalism.HermitianLatticesTheory.vecAt
  simp [InfinitePlace.norm_embedding_eq, InfinitePlace.apply]

variable (K) in

def stdLat (n : ℕ) : HLat K where
  V := Fin n → K
  ι := Fin n
  b := Pi.basisFun K (Fin n)
  X := fun _ => 1
  L := Submodule.span (𝓞 K) (Set.range (Pi.basisFun K (Fin n)))

theorem stdLat_good (n : ℕ) : (stdLat K n).Good := by
  refine ⟨fun v => ?_, Submodule.fg_span (Set.finite_range _), ?_⟩
  · show IsUnit (1 : Matrix (Fin n) (Fin n) ℂ).det
    simp
  · exact top_le_iff.1 ((Pi.basisFun K (Fin n)).span_eq.symm.le.trans (Submodule.span_mono Submodule.subset_span))

def subLat (A : HLat K) (S : Submodule K A.V)
    (X : InfinitePlace K → Matrix (Fin (Module.finrank K S)) (Fin (Module.finrank K S)) ℂ) : HLat K :=
  haveI : Module.Finite K A.V := Module.Finite.of_basis A.b
  { V := S
    ι := Fin (Module.finrank K S)
    b := Module.finBasis K S
    X := X
    L := A.L.comap (S.subtype.restrictScalars (𝓞 K)) }

theorem exists_smul_mem {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (L : Submodule (𝓞 K) V)
    (hL : Submodule.span K (L : Set V) = ⊤) (x : V) : ∃ c : 𝓞 K, c ≠ 0 ∧ c • x ∈ L := by
  have hx : x ∈ Submodule.span K (L : Set V) := hL ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha, hya⟩ := hy
    obtain ⟨b, hb, hzb⟩ := hz
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine L.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact L.smul_mem b hya
    · rw [mul_smul]; exact L.smul_mem a hzb
  | smul k y _ hy =>
    obtain ⟨c, hc, hyc⟩ := hy
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) k
    have hb0 : algebraMap (𝓞 K) K b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
    refine ⟨b * c, mul_ne_zero (nonZeroDivisors.ne_zero hb) hc, ?_⟩
    have e1 : (b * c) • ((algebraMap (𝓞 K) K a / algebraMap (𝓞 K) K b) • y)
        = (algebraMap (𝓞 K) K (b * c) * (algebraMap (𝓞 K) K a / algebraMap (𝓞 K) K b)) • y := by
      simp only [map_mul, mul_smul, algebraMap_smul]
    have e2 : a • (c • y) = (algebraMap (𝓞 K) K a * algebraMap (𝓞 K) K c) • y := by
      simp only [mul_smul, algebraMap_smul]
    have e3 : algebraMap (𝓞 K) K (b * c) * (algebraMap (𝓞 K) K a / algebraMap (𝓞 K) K b)
        = algebraMap (𝓞 K) K a * algebraMap (𝓞 K) K c := by
      rw [map_mul]; field_simp
    rw [e1, e3, ← e2]
    exact L.smul_mem a hyc

theorem subLat_good (A : HLat K) (hA : A.Good) (S : Submodule K A.V) (X) (hX : ∀ v, IsUnit (X v).det) :
    (subLat A S X).Good := by
  refine ⟨hX, ?_, ?_⟩
  · show (A.L.comap (S.subtype.restrictScalars (𝓞 K))).FG
    have hN : IsNoetherian (𝓞 K) A.L := isNoetherian_of_fg_of_noetherian _ hA.2.1
    apply Submodule.fg_of_fg_map_injective (S.subtype.restrictScalars (𝓞 K)) Subtype.val_injective
    exact isNoetherian_submodule.mp hN _ (Submodule.map_comap_le _ _)
  · show Submodule.span K ((A.L.comap (S.subtype.restrictScalars (𝓞 K)) : Set S)) = ⊤
    rw [Submodule.eq_top_iff']
    intro x
    obtain ⟨c, hc, hcx⟩ := exists_smul_mem A.L hA.2.2 (x : A.V)
    have hmem : c • x ∈ A.L.comap (S.subtype.restrictScalars (𝓞 K)) := by
      show ((c • x : S) : A.V) ∈ A.L
      simpa using hcx
    have hc0 : algebraMap (𝓞 K) K c ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hc)
    have hx : x = (algebraMap (𝓞 K) K c)⁻¹ • (c • x) := by
      rw [← algebraMap_smul K c x, smul_smul, inv_mul_cancel₀ hc0, one_smul]
    rw [hx]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

end Std

section Forms

variable {R : Ranks} {LL : Type} [Field LL] [NumberField LL] [StarRing LL] {embLL : LL →+* ℂ}
  {Pl : Rows.Places LL} {Tau : Type} [Fintype Tau] {hc : Tau → HCParam R}
  {C : ColumnChain R Tau hc} {A : ColumnsAtT R C} {P : PeriodMap R C}
  (M : MemberForms LL embLL Pl Tau hc C A P)

theorem nm_rat (v : A.vT) (x : (M.lat 0).V) : ∃ y, M.emb 0 y = A.Nm v (M.emb 0 x) := by
  have key : ∀ a, ∀ x ∈ Submodule.span LL ((M.lat 0).L : Set (M.lat 0).V), ∃ y, M.emb 0 y = A.rhoT v a (M.emb 0 x) := by
    intro a x hx
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨y, -, hy⟩ := M.rhoT_lat v a x hx; exact ⟨y, hy⟩
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨x', hx⟩ := hx
      obtain ⟨y', hy⟩ := hy
      exact ⟨x' + y', by simp only [map_add, hx, hy]⟩
    | smul k x _ hx =>
      obtain ⟨x', hx⟩ := hx
      exact ⟨k • x', by rw [LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ, map_smul, hx]⟩
  choose y hy using fun a => key a x ((M.lat_good 0).2.2 ▸ Submodule.mem_top)
  exact ⟨∑ a, y a, by simp only [map_sum, hy, ColumnsAtT.Nm, LinearMap.sum_apply]⟩

theorem mram_le_span : A.Mram ≤ Submodule.span ℂ (M.emb 0 '' (M.ramSub : Set (M.lat 0).V)) := by
  intro φ hφ
  have hsp : Submodule.span ℂ (Set.range (fun a => M.emb 0 ((M.lat 0).b a))) = A.Mu0 :=
    (M.emb_basis 0).2.trans M.Fi_zero
  have h := ker_rational embLL (M.emb 0) (M.lat 0).b (M.emb_basis 0).1 A.Nm
    (fun v => descend (M.emb 0) (M.emb 0) (M.emb_inj 0) (A.Nm v) (nm_rat M v))
    (fun v x => descend_spec _ _ _ _ _ x) φ (hsp ▸ hφ.1) (fun v => (Submodule.mem_iInf _).1 hφ.2 v)
  refine Submodule.span_mono (Set.image_mono fun x hx => ?_) h
  refine ⟨hsp ▸ span_image_le embLL (M.emb 0) (M.lat 0).b x, (Submodule.mem_iInf _).2 fun v => ?_⟩
  rw [LinearMap.mem_ker, ← descend_spec (M.emb 0) (M.emb 0) (M.emb_inj 0) (A.Nm v) (nm_rat M v), hx v, map_zero]

def ramEmb : M.ramSub →ₛₗ[embLL] A.Mram :=
  LinearMap.codRestrict A.Mram ((M.emb 0).comp M.ramSub.subtype) (fun x => x.2)

theorem ramEmb_basis {ι : Type} [Fintype ι] (b : Module.Basis ι LL M.ramSub) :
    LinearIndependent ℂ (fun a => ramEmb M (b a)) ∧ Submodule.span ℂ (Set.range (fun a => ramEmb M (b a))) = ⊤ := by
  refine ⟨LinearIndependent.of_comp A.Mram.subtype
    (li_comp embLL (M.emb 0) (M.lat 0).b (M.emb_basis 0).1 M.ramSub.subtype Subtype.val_injective b), ?_⟩
  rw [eq_top_iff]
  rintro φ -
  have h1 : Submodule.span ℂ (M.emb 0 '' (M.ramSub : Set (M.lat 0).V)) ≤
      (Submodule.span ℂ (Set.range (fun a => ramEmb M (b a)))).map A.Mram.subtype := by
    rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨ramEmb M ⟨x, hx⟩, span_image_le embLL (ramEmb M) b _, rfl⟩
  obtain ⟨y, hy, hy'⟩ := h1 (mram_le_span M φ.2)
  rwa [← Subtype.ext hy']

end Forms

theorem exists_divStage (B : Base) (C : Cols B) (W : RowsRest B C) :
    ∃ V : DivStage B C W, V.div.AllGood ∧
      ∀ u, (V.div.Nu u).L = ((C.fm u).lat 0).L.comap ((V.nuIn u).restrictScalars (𝓞 B.LL)) := by
  have hX := fun u =>
    haveI : Module.Finite B.LL ((C.fm u).lat 0).V := Module.Finite.of_basis ((C.fm u).lat 0).b
    exists_frames ((C.fm u).lat 0) ((C.fm u).lat_good 0).1 (Module.finBasis B.LL (C.fm u).ramSub)
      (C.fm u).ramSub.subtype Subtype.val_injective
  choose X hX hn using hX
  let Nu : B.Word → HLat B.LL := fun u => subLat ((C.fm u).lat 0) (C.fm u).ramSub (X u)
  have hc : (fun i => coord B.embLL W.onb (Pi.basisFun B.LL (Fin W.Drows) i)) = W.onb.toBasis := by
    funext i; rw [coord_basisFun]; simp
  refine ⟨{ div := { RR := stdLat B.LL W.Drows
                     Nu := Nu
                     Bk := fun _ => 0
                     h := fun _ => 0
                     HH := sFrame Nu (fun _ => 0) + (stdLat B.LL W.Drows).muMax
                     HH_ge := le_rfl
                     etaF := 0
                     Dall := W.Dall
                     delP := W.delp
                     delP_le_one := W.delp_le_one }
            div_good := ⟨(stdLat_good _).1, hX⟩
            jEE := coord B.embLL W.onb
            jEE_basis := ?_
            jN := fun u => (W.eMu u).symm.toLinearMap.comp (ramEmb (C.fm u))
            jN_basis := fun u => ?_
            Dall_eq := rfl
            delP_eq := rfl
            nuIn := fun u => (C.fm u).ramSub.subtype
            nuIn_inj := fun u => Subtype.val_injective
            nuIn_range := fun u => Submodule.range_subtype _
            nuIn_jN := fun u x => ?_
            nuIn_norm := hn
            jEE_norm := fun x => normAt_id B.embLL W.onb x },
    ⟨stdLat_good _, fun u => subLat_good _ ((C.fm u).lat_good 0) _ _ (hX u)⟩, fun u => rfl⟩
  · refine ⟨?_, ?_⟩
    · show LinearIndependent ℂ (fun i => coord B.embLL W.onb (Pi.basisFun B.LL (Fin W.Drows) i))
      rw [hc]; exact W.onb.toBasis.linearIndependent
    · show Submodule.span ℂ (Set.range (fun i => coord B.embLL W.onb (Pi.basisFun B.LL (Fin W.Drows) i))) = ⊤
      rw [hc]; exact W.onb.toBasis.span_eq
  · obtain ⟨h1, h2⟩ := ramEmb_basis (C.fm u) (Nu u).b
    refine ⟨h1.map' (W.eMu u).symm.toLinearMap (W.eMu u).symm.ker, ?_⟩
    have h3 := congrArg (Submodule.map (W.eMu u).symm.toLinearMap) h2
    rw [Submodule.map_span, ← Set.range_comp, Submodule.map_top, LinearEquiv.range] at h3
    exact h3
  · show ((W.eMu u ((W.eMu u).symm (ramEmb (C.fm u) x)) : (C.mem u).A.Mram) :
      (C.mem u).C.cls 0 → (C.mem u).C.Y 0 → ℂ) = _
    rw [LinearEquiv.apply_symm_apply]; rfl

theorem RR_finrank {B : Base} {C : Cols B} {W : RowsRest B C} (V : DivStage B C W) :
    Module.finrank B.LL V.div.RR.V = W.Drows := by
  have h1 := Module.finrank_eq_card_basis V.div.RR.b
  have h2 := Module.finrank_eq_card_basis (Module.Basis.mk V.jEE_basis.1 (le_of_eq V.jEE_basis.2.symm))
  have h3 : Module.finrank ℂ W.EE = W.Drows := by simpa using Module.finrank_eq_card_basis W.onb.toBasis
  omega

theorem Nu_finrank {B : Base} {C : Cols B} {W : RowsRest B C} (V : DivStage B C W) (u : B.Word) :
    Module.finrank B.LL (V.div.Nu u).V = (C.mem u).A.du := by
  have h1 := Module.finrank_eq_card_basis (V.div.Nu u).b
  have h2 := Module.finrank_eq_card_basis (Module.Basis.mk (V.jN_basis u).1 (le_of_eq (V.jN_basis u).2.symm))
  have h3 : Module.finrank ℂ (W.Mu u) = (C.mem u).A.du := (W.eMu u).finrank_eq
  omega

end GlobalTheory.Mem.DivModel

end
