import Formalism.HarderNarasimhan.QuotRealize
import Formalism.LatticeSlopes.ExistsSaturatedSlopeEqMuMax
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.DiscreteSpanOfLinIndep
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.PlaceSplit
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.SlopeIneqMean

open Module NumberField Matrix

noncomputable section

namespace Formalism.HN

namespace QuotientRealization

section Covol

variable {E F M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [AddCommGroup M]

theorem eq_of_norm_eq (f : M →+ E) (g : M →+ F) (hn : ∀ m, ‖f m‖ = ‖g m‖) {m m' : M}
    (h : f m = f m') : g m = g m' := by
  have h0 : ‖g (m - m')‖ = 0 := by rw [← hn, map_sub, h, sub_self, norm_zero]
  rw [norm_eq_zero, map_sub, sub_eq_zero] at h0
  exact h0

def transport (f : M →+ E) (g : M →+ F) (L1 : Submodule ℤ E) (L2 : Submodule ℤ F)
    (h1 : ∀ y, y ∈ L1 ↔ ∃ m, f m = y) (h2 : ∀ y, y ∈ L2 ↔ ∃ m, g m = y)
    (hn : ∀ m, ‖f m‖ = ‖g m‖) : L1 →+ L2 where
  toFun y := ⟨g ((h1 y).1 y.2).choose, (h2 _).2 ⟨_, rfl⟩⟩
  map_zero' := by
    apply Subtype.ext
    have hs := ((h1 _).1 (0 : L1).2).choose_spec
    show g _ = 0
    rw [← map_zero g]
    exact eq_of_norm_eq f g hn (by rw [hs, map_zero]; rfl)
  map_add' y z := by
    apply Subtype.ext
    have hs := ((h1 _).1 (y + z).2).choose_spec
    have hy := ((h1 _).1 y.2).choose_spec
    have hz := ((h1 _).1 z.2).choose_spec
    show g _ = g _ + g _
    rw [← map_add]
    exact eq_of_norm_eq f g hn (by rw [hs, map_add, hy, hz]; rfl)

theorem transport_apply (f : M →+ E) (g : M →+ F) (L1 : Submodule ℤ E) (L2 : Submodule ℤ F)
    (h1 : ∀ y, y ∈ L1 ↔ ∃ m, f m = y) (h2 : ∀ y, y ∈ L2 ↔ ∃ m, g m = y)
    (hn : ∀ m, ‖f m‖ = ‖g m‖) (y : L1) (m : M) (hm : f m = y) :
    ((transport f g L1 L2 h1 h2 hn y : L2) : F) = g m := by
  show g ((h1 y).1 y.2).choose = g m
  exact eq_of_norm_eq f g hn (((h1 y).1 y.2).choose_spec.trans hm.symm)

theorem covol_eq_of_norm_eq (f : M →+ E) (g : M →+ F) (L1 : Submodule ℤ E) (L2 : Submodule ℤ F)
    [DiscreteTopology L1] [DiscreteTopology L2]
    (h1 : ∀ y, y ∈ L1 ↔ ∃ m, f m = y) (h2 : ∀ y, y ∈ L2 ↔ ∃ m, g m = y)
    (hn : ∀ m, ‖f m‖ = ‖g m‖) : Formalism.F.covol L1 = Formalism.F.covol L2 := by
  have hn' : ∀ m, ‖g m‖ = ‖f m‖ := fun m => (hn m).symm
  let φ := transport f g L1 L2 h1 h2 hn
  let ψ := transport g f L2 L1 h2 h1 hn'
  let e : L1 ≃+ L2 :=
    { toFun := φ
      invFun := ψ
      map_add' := φ.map_add
      left_inv := fun y => by
        obtain ⟨m, hm⟩ := (h1 _).1 y.2
        apply Subtype.ext
        rw [transport_apply g f L2 L1 h2 h1 hn' (φ y) m
          (transport_apply f g L1 L2 h1 h2 hn y m hm).symm, hm]
      right_inv := fun y => by
        obtain ⟨m, hm⟩ := (h2 _).1 y.2
        apply Subtype.ext
        rw [transport_apply f g L1 L2 h1 h2 hn (ψ y) m
          (transport_apply g f L2 L1 h2 h1 hn' y m hm).symm, hm] }
  let bL := Module.finBasis ℤ L1
  rw [Formalism.F.covolEqGram E L1 _ bL, Formalism.F.covolEqGram F L2 _ (bL.map e.toIntLinearEquiv)]
  congr 2
  ext i j
  obtain ⟨mi, hmi⟩ := (h1 _).1 (bL i).2
  obtain ⟨mj, hmj⟩ := (h1 _).1 (bL j).2
  have hi : ((bL.map e.toIntLinearEquiv) i : F) = g mi := by
    rw [Basis.map_apply]; exact transport_apply f g L1 L2 h1 h2 hn _ mi hmi
  have hj : ((bL.map e.toIntLinearEquiv) j : F) = g mj := by
    rw [Basis.map_apply]; exact transport_apply f g L1 L2 h1 h2 hn _ mj hmj
  simp only [Matrix.gram_apply]
  rw [hi, hj, ← hmi, ← hmj, real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two,
    real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two, ← map_add, ← map_add,
    hn, hn, hn]

end Covol

section Psi

variable {P ι : Type*} [Fintype P] [DecidableEq P] [Fintype ι]

theorem inner_psi_psi (u v : P) (y z : ι → ℂ) :
    inner ℝ (PlaceDecomposition.psi u y) (PlaceDecomposition.psi (ι := ι) v z) =
      if u = v then (inner ℂ (WithLp.toLp 2 y : EuclideanSpace ℂ ι) (WithLp.toLp 2 z)).re
      else 0 := by
  rw [PiLp.inner_apply]
  by_cases h : u = v
  · subst h
    rw [if_pos rfl, PiLp.inner_apply, Complex.re_sum, Fintype.sum_prod_type, Finset.sum_eq_single u]
    · rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      simp [PlaceDecomposition.psi, Fin.sum_univ_two, Complex.mul_re]
    · intro w _ hw
      apply Finset.sum_eq_zero
      rintro ⟨i, k⟩ -
      simp [PlaceDecomposition.psi, hw]
    · intro hu
      exact absurd (Finset.mem_univ u) hu
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    rintro ⟨w, i, k⟩ -
    by_cases hw : w = u
    · subst hw
      simp [PlaceDecomposition.psi, h]
    · simp [PlaceDecomposition.psi, hw]

theorem inner_sum_psi (y z : P → ι → ℂ) :
    inner ℝ (∑ u, PlaceDecomposition.psi u (y u)) (∑ v, PlaceDecomposition.psi (ι := ι) v (z v)) =
      ∑ v, (inner ℂ (WithLp.toLp 2 (y v) : EuclideanSpace ℂ ι) (WithLp.toLp 2 (z v))).re := by
  simp [sum_inner, inner_sum, inner_psi_psi]

end Psi

theorem zl_mono {R V E : Type*} [Ring R] [AddCommGroup V] [Module R V] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (ρ : V →+ E) {N N' : Submodule R V}
    (h : N ≤ N') : zl ρ N ≤ zl ρ N' := by
  rintro x ⟨y, hy, rfl⟩
  exact ⟨y, h hy, rfl⟩

theorem exists_mat {κ ι : Type} [Fintype κ] [DecidableEq κ] [Fintype ι]
    (T : (κ → ℂ) →ₗ[ℂ] EuclideanSpace ℂ ι) (hT : Function.Injective T) :
    ∃ M : Matrix κ κ ℂ, IsUnit M.det ∧ ∀ z, Formalism.HermitianLatticesTheory.cnorm (M *ᵥ z) = ‖T z‖ := by
  classical
  have hdim : Module.finrank ℂ (LinearMap.range T) = Fintype.card κ := by
    rw [LinearMap.finrank_range_of_inj hT, Module.finrank_fintype_fun_eq_card]
  let e : LinearMap.range T ≃ₗᵢ[ℂ] EuclideanSpace ℂ κ :=
    ((stdOrthonormalBasis ℂ (LinearMap.range T)).reindex
      (Fintype.equivFinOfCardEq hdim.symm).symm).repr
  let f : (κ → ℂ) →ₗ[ℂ] (κ → ℂ) := (WithLp.linearEquiv 2 ℂ (κ → ℂ)).toLinearMap ∘ₗ
    e.toLinearEquiv.toLinearMap ∘ₗ T.rangeRestrict
  have hf : ∀ z, ‖(WithLp.toLp 2 (f z) : EuclideanSpace ℂ κ)‖ = ‖T z‖ := by
    intro z
    simp [f, LinearIsometryEquiv.norm_map]
  have hinj : Function.Injective f := by
    intro z w hzw
    apply hT
    have h1 : T.rangeRestrict z = T.rangeRestrict w := by
      apply e.injective
      have := congrArg (WithLp.toLp 2) hzw
      simpa [f] using this
    simpa using congrArg Subtype.val h1
  refine ⟨LinearMap.toMatrix' f, ?_, fun z => ?_⟩
  · rw [LinearMap.det_toMatrix']
    first
      | simpa using (LinearEquiv.ofInjectiveEndo f hinj).isUnit_det'
      | exact (LinearEquiv.ofInjectiveEndo f hinj).isUnit_det'
  · rw [LinearMap.toMatrix'_mulVec, Formalism.HN.PlaceOperatorNorms.cnorm_eq, hf]

section Main

variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [Fintype ι] [DecidableEq ι]

def pv (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (U : Submodule K V)
    (v : InfinitePlace K) : Submodule ℂ (EuclideanSpace ℂ ι) :=
  Submodule.span ℂ ((fun y => (WithLp.equiv 2 (ι → ℂ)).symm (Formalism.HermitianLatticesTheory.fcoord b X v y)) '' (U : Set V))

private theorem fcoord_smul_harder_narasimhan (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (v : InfinitePlace K) (a : K) (x : V) :
    Formalism.HermitianLatticesTheory.fcoord b X v (a • x) = v.embedding a • Formalism.HermitianLatticesTheory.fcoord b X v x := by
  have h1 : Formalism.HermitianLatticesTheory.vecAt b v (a • x) = v.embedding a • Formalism.HermitianLatticesTheory.vecAt b v x := by
    funext i
    simp [Formalism.HermitianLatticesTheory.vecAt]
  simp only [Formalism.HermitianLatticesTheory.fcoord, h1, Matrix.mulVec_smul]

private theorem fcoord_finset_sum_smul {κ : Type} (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (v : InfinitePlace K) (s : Finset κ) (r : κ → K) (c : κ → V) :
    Formalism.HermitianLatticesTheory.fcoord b X v (∑ k ∈ s, r k • c k) =
      ∑ k ∈ s, v.embedding (r k) • Formalism.HermitianLatticesTheory.fcoord b X v (c k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Formalism.HermitianLatticesTheory.fcoord_zero]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, Formalism.HermitianLatticesTheory.fcoord_add, ih, fcoord_smul_harder_narasimhan]

theorem fcoord_mem_span (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (S : Submodule (𝓞 K) V) (v : InfinitePlace K) {y : V}
    (hy : y ∈ Submodule.span K (S : Set V)) :
    Formalism.HermitianLatticesTheory.fcoord b X v y ∈ Submodule.span ℂ (Formalism.HermitianLatticesTheory.fcoord b X v '' (S : Set V)) := by
  induction hy using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero => rw [Formalism.HermitianLatticesTheory.fcoord_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [Formalism.HermitianLatticesTheory.fcoord_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
      have h1 : Formalism.HermitianLatticesTheory.vecAt b v (a • x) = v.embedding a • Formalism.HermitianLatticesTheory.vecAt b v x := by
        funext i
        simp [Formalism.HermitianLatticesTheory.vecAt]
      have h2 : Formalism.HermitianLatticesTheory.fcoord b X v (a • x) = v.embedding a • Formalism.HermitianLatticesTheory.fcoord b X v x := by
        simp only [Formalism.HermitianLatticesTheory.fcoord, h1, Matrix.mulVec_smul]
      rw [h2]
      exact Submodule.smul_mem _ _ hx

theorem pv_le (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (S : Submodule (𝓞 K) V) (v : InfinitePlace K) (z : EuclideanSpace ℂ ι)
    (hz : z ∈ pv b X (Submodule.span K (S : Set V)) v) :
    WithLp.ofLp z ∈ Submodule.span ℂ (Formalism.HermitianLatticesTheory.fcoord b X v '' (S : Set V)) := by
  induction hz using Submodule.span_induction with
  | mem w hw =>
      obtain ⟨y, hy, rfl⟩ := hw
      simpa using fcoord_mem_span b X S v hy
  | zero => simp
  | add x y _ _ hx hy => simpa using Submodule.add_mem _ hx hy
  | smul a x _ hx => simpa using Submodule.smul_mem _ a hx

theorem psi_mem [DecidableEq (InfinitePlace K)] (b : Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) (S : Submodule (𝓞 K) V) (v : InfinitePlace K)
    (z : EuclideanSpace ℂ ι) (hz : z ∈ pv b X (Submodule.span K (S : Set V)) v) :
    PlaceDecomposition.psi v (WithLp.ofLp z) ∈ Submodule.span ℝ
      (zl (Formalism.HermitianLatticesTheory.realize b X) S : Set (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))) := by
  have h1 := pv_le b X S v z hz
  have h2 : WithLp.ofLp z ∈ Submodule.span ℝ (Formalism.HermitianLatticesTheory.fcoord b X v '' (S : Set V)) := by
    rw [← PlaceDecomposition.span_real_eq_complex b X S v]; exact h1
  have h3 := Submodule.mem_map_of_mem (f := PlaceDecomposition.psi v) h2
  rw [← PlaceDecomposition.piece_eq_map b X S v] at h3
  exact (Submodule.mem_inf.1 h3).1

theorem finrank_pv (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (U : Submodule K V) (v : InfinitePlace K) :
    finrank ℂ (pv b X U v) = finrank K U := by
  have h : pv b X U v = (Submodule.span ℂ (Formalism.HermitianLatticesTheory.fcoord b X v '' (U : Set V))).map
      ((WithLp.linearEquiv 2 ℂ (ι → ℂ)).symm : (ι → ℂ) →ₗ[ℂ] EuclideanSpace ℂ ι) := by
    rw [Submodule.map_span, Set.image_image]; rfl
  rw [h, LinearEquiv.finrank_map_eq]
  have := PlaceDecomposition.finrank_span_complex b X hX (U.restrictScalars (𝓞 K)) v
  rw [Submodule.coe_restrictScalars] at this
  rw [this, rkK, Submodule.coe_restrictScalars, Submodule.span_eq]

theorem pv_top (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (v : InfinitePlace K) : pv b X ⊤ v = ⊤ := by
  have hf : ∀ j, Formalism.HermitianLatticesTheory.fcoord b X v (b j) = (X v)⁻¹ *ᵥ Pi.single j 1 := by
    intro j
    simp only [Formalism.HermitianLatticesTheory.fcoord]
    congr 1
    funext i
    by_cases h : i = j
    · subst h; simp [Formalism.HermitianLatticesTheory.vecAt]
    · simp [Formalism.HermitianLatticesTheory.vecAt, Finsupp.single_apply, Pi.single_apply, h, Ne.symm h]
  have key : ∀ j, (WithLp.equiv 2 (ι → ℂ)).symm (Formalism.HermitianLatticesTheory.fcoord b X v (b j)) ∈ pv b X ⊤ v :=
    fun j => Submodule.subset_span ⟨b j, Submodule.mem_top, rfl⟩
  rw [eq_top_iff]
  rintro z -
  have hz : z = ∑ j, (X v *ᵥ WithLp.ofLp z) j •
      (WithLp.equiv 2 (ι → ℂ)).symm (Formalism.HermitianLatticesTheory.fcoord b X v (b j)) := by
    have e : WithLp.ofLp z = (X v)⁻¹ *ᵥ (X v *ᵥ WithLp.ofLp z) := by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (hX v), Matrix.one_mulVec]
    apply (WithLp.equiv 2 (ι → ℂ)).injective
    funext i
    simp only [hf]
    conv_lhs => rw [WithLp.equiv_apply, e]
    simp [Matrix.mulVec, dotProduct, Pi.single_apply, Finset.sum_apply, mul_comm]
  rw [hz]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (key j)

theorem proj_norm_sq [DecidableEq (InfinitePlace K)] (b : Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) (S : Submodule (𝓞 K) V) (x : V) :
    ‖(Submodule.span ℝ (zl (Formalism.HermitianLatticesTheory.realize b X) S :
        Set (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))))ᗮ.starProjection
        (Formalism.HermitianLatticesTheory.realize b X x)‖ ^ 2 =
      ∑ v, ‖(pv b X (Submodule.span K (S : Set V)) v)ᗮ.starProjection
        (WithLp.toLp 2 (Formalism.HermitianLatticesTheory.fcoord b X v x))‖ ^ 2 := by
  set W := Submodule.span ℝ (zl (Formalism.HermitianLatticesTheory.realize b X) S :
    Set (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))) with hW
  set P := fun v => pv b X (Submodule.span K (S : Set V)) v with hP
  let cv : InfinitePlace K → EuclideanSpace ℂ ι := fun v =>
    (P v)ᗮ.starProjection (WithLp.toLp 2 (Formalism.HermitianLatticesTheory.fcoord b X v x))
  let r := ∑ v, PlaceDecomposition.psi v (WithLp.ofLp (cv v))
  have hρ : ∀ y : V, Formalism.HermitianLatticesTheory.realize b X y =
      ∑ v, PlaceDecomposition.psi v (Formalism.HermitianLatticesTheory.fcoord b X v y) := by
    intro y
    rw [← PlaceDecomposition.sum_prj (Formalism.HermitianLatticesTheory.realize b X y)]
    exact Finset.sum_congr rfl fun v _ => PlaceDecomposition.prj_realize b X v y
  have hr_orth : r ∈ Wᗮ := by
    rw [Submodule.mem_orthogonal]
    intro u hu
    induction hu using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨s, hs, rfl⟩ := hu
      rw [hρ s, inner_sum_psi]
      refine Finset.sum_eq_zero fun v _ => ?_
      have h1 : WithLp.toLp 2 (Formalism.HermitianLatticesTheory.fcoord b X v s) ∈ P v :=
        Submodule.subset_span ⟨s, Submodule.subset_span hs, rfl⟩
      have h2 : cv v ∈ (P v)ᗮ := Submodule.starProjection_apply_mem _ _
      rw [show (WithLp.toLp 2 (WithLp.ofLp (cv v)) : EuclideanSpace ℂ ι) = cv v from rfl,
        Submodule.inner_right_of_mem_orthogonal h1 h2, Complex.zero_re]
    | zero => exact inner_zero_left _
    | add u w _ _ h1 h2 => rw [inner_add_left, h1, h2, add_zero]
    | smul a u _ h => rw [real_inner_smul_left, h, mul_zero]
  have hdiff : Formalism.HermitianLatticesTheory.realize b X x - r ∈ W := by
    rw [hρ x, ← Finset.sum_sub_distrib]
    refine Submodule.sum_mem _ fun v _ => ?_
    rw [← map_sub]
    have hz : Formalism.HermitianLatticesTheory.fcoord b X v x - WithLp.ofLp (cv v) =
        WithLp.ofLp ((P v).starProjection (WithLp.toLp 2 (Formalism.HermitianLatticesTheory.fcoord b X v x))) := by
      simp only [cv, Submodule.starProjection_orthogonal_val, WithLp.ofLp_sub, sub_sub_cancel]
    rw [hz]
    exact psi_mem b X S v _ (Submodule.starProjection_apply_mem _ _)
  have hproj : Wᗮ.starProjection (Formalism.HermitianLatticesTheory.realize b X x) = r := by
    apply Submodule.eq_starProjection_of_mem_orthogonal hr_orth
    rw [Submodule.orthogonal_orthogonal]
    exact hdiff
  rw [hproj, ← real_inner_self_eq_norm_sq, inner_sum_psi]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [show (WithLp.toLp 2 (WithLp.ofLp (cv v)) : EuclideanSpace ℂ ι) = cv v from rfl]
  have h := inner_self_eq_norm_sq (𝕜 := ℂ) (cv v)
  rw [RCLike.re_to_complex] at h
  exact h

section Lift

variable (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (U : Submodule K V)
  {κ : Type} [Fintype κ] [DecidableEq κ] (b'' : Basis κ K (V ⧸ U)) (c : κ → V)

def tv (v : InfinitePlace K) : (κ → ℂ) →ₗ[ℂ] EuclideanSpace ℂ ι :=
  Fintype.linearCombination ℂ
    (fun k => (pv b X U v)ᗮ.starProjection (WithLp.toLp 2 (Formalism.HermitianLatticesTheory.fcoord b X v (c k))))

theorem sub_mem_of_lift (hc : ∀ k, U.mkQ (c k) = b'' k) (x : V) :
    x - ∑ k, b''.repr (U.mkQ x) k • c k ∈ U := by
  apply (Submodule.Quotient.eq U).mp
  change U.mkQ x = U.mkQ (∑ k, b''.repr (U.mkQ x) k • c k)
  rw [map_sum]
  simp only [LinearMap.map_smul, hc]
  exact (b''.sum_repr (U.mkQ x)).symm

theorem proj_eq_tv (hc : ∀ k, U.mkQ (c k) = b'' k) (v : InfinitePlace K) (x : V) :
    (pv b X U v)ᗮ.starProjection (WithLp.toLp 2 (Formalism.HermitianLatticesTheory.fcoord b X v x)) =
      tv b X U c v (fun k => v.embedding (b''.repr (U.mkQ x) k)) := by
  set r := b''.repr (U.mkQ x) with hr
  let L : (ι → ℂ) →ₗ[ℂ] EuclideanSpace ℂ ι := ((pv b X U v)ᗮ.starProjection).toLinearMap ∘ₗ
    (WithLp.linearEquiv 2 ℂ (ι → ℂ)).symm.toLinearMap
  have hL : ∀ w, L w = (pv b X U v)ᗮ.starProjection (WithLp.toLp 2 w) := fun w => rfl
  have hm : WithLp.toLp 2 (Formalism.HermitianLatticesTheory.fcoord b X v (x - ∑ k, r k • c k)) ∈ pv b X U v :=
    Submodule.subset_span ⟨_, sub_mem_of_lift U b'' c hc x, rfl⟩
  have h0 : L (Formalism.HermitianLatticesTheory.fcoord b X v (x - ∑ k, r k • c k)) = 0 := by
    rw [hL]
    first
      | exact (Submodule.starProjection_apply_eq_zero_iff _).mpr (Submodule.le_orthogonal_orthogonal _ hm)
      | exact (Submodule.starProjection_eq_zero_iff _).mpr (Submodule.le_orthogonal_orthogonal _ hm)
      | simp [Submodule.le_orthogonal_orthogonal _ hm]
      | simpa using Submodule.le_orthogonal_orthogonal _ hm
  have hsplit : Formalism.HermitianLatticesTheory.fcoord b X v x = Formalism.HermitianLatticesTheory.fcoord b X v (x - ∑ k, r k • c k) +
      ∑ k, v.embedding (r k) • Formalism.HermitianLatticesTheory.fcoord b X v (c k) := by
    rw [← fcoord_finset_sum_smul, ← Formalism.HermitianLatticesTheory.fcoord_add, sub_add_cancel]
  rw [← hL, hsplit, map_add, h0, zero_add, map_sum, tv, Fintype.linearCombination_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, hL]

theorem tv_injective (hX : ∀ v, IsUnit (X v).det) (hc : ∀ k, U.mkQ (c k) = b'' k)
    (v : InfinitePlace K) : Function.Injective (tv b X U c v) := by
  have : FiniteDimensional K V := Module.Finite.of_basis b
  have hle : (pv b X U v)ᗮ ≤ LinearMap.range (tv b X U c v) := by
    intro w hw
    have hw' : (pv b X U v)ᗮ.starProjection w = w := Submodule.starProjection_eq_self_iff.2 hw
    have htop : w ∈ pv b X ⊤ v := by rw [pv_top b X hX v]; trivial
    have hmap : (pv b X ⊤ v).map
        ((pv b X U v)ᗮ.starProjection : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι).toLinearMap ≤
        LinearMap.range (tv b X U c v) := by
      unfold pv
      rw [Submodule.map_span_le]
      rintro _ ⟨y, -, rfl⟩
      exact LinearMap.mem_range.2 ⟨_, (proj_eq_tv b X U b'' c hc v y).symm⟩
    rw [← hw']
    exact hmap ⟨w, htop, rfl⟩
  have h1 := Submodule.finrank_mono hle
  have h2 := Submodule.finrank_add_finrank_orthogonal (pv b X U v)
  rw [finrank_pv b X hX, finrank_euclideanSpace] at h2
  have h3 := Submodule.finrank_quotient_add_finrank U
  rw [Module.finrank_eq_card_basis b, Module.finrank_eq_card_basis b''] at h3
  have h4 := LinearMap.finrank_range_add_finrank_ker (tv b X U c v)
  rw [Module.finrank_fintype_fun_eq_card] at h4
  have h5 : finrank ℂ (LinearMap.ker (tv b X U c v)) = 0 := by omega
  rw [← LinearMap.ker_eq_bot]
  exact Submodule.finrank_eq_zero.1 h5

end Lift

end Main

end QuotientRealization

theorem quotient_lattice_realization : QuotRealize := by
  intro K V ι _ _ _ _ _ _ _ _ _ _ b X hX A S hA hSat
  classical
  have hfinV : FiniteDimensional K V := Module.Finite.of_basis b
  set U := Submodule.span K (S : Set V) with hU
  let κ := Fin (finrank K (V ⧸ U))
  let b'' : Basis κ K (V ⧸ U) := Module.finBasis K (V ⧸ U)
  have hsurj : ∀ k, ∃ y, U.mkQ y = b'' k := fun k => U.mkQ_surjective _
  choose c hc using hsurj
  have hM := fun v => QuotientRealization.exists_mat (QuotientRealization.tv b X U c v)
    (QuotientRealization.tv_injective b X U b'' c hX hc v)
  choose M hMu hMn using hM
  let X'' : InfinitePlace K → Matrix κ κ ℂ := fun v => (M v)⁻¹
  have hX'' : ∀ v, IsUnit (X'' v).det := fun v => Matrix.isUnit_nonsing_inv_det _ (hMu v)
  have hnorm : ∀ v (x : V), Formalism.HermitianLatticesTheory.normAt b'' X'' v (U.mkQ x) =
      ‖(QuotientRealization.pv b X U v)ᗮ.starProjection (WithLp.toLp 2 (Formalism.HermitianLatticesTheory.fcoord b X v x))‖ := by
    intro v x
    rw [QuotientRealization.proj_eq_tv b X U b'' c hc v x, ← hMn v]
    simp only [Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.fcoord, X'', Matrix.nonsing_inv_nonsing_inv _ (hMu v)]
    rfl
  refine ⟨κ, inferInstance, inferInstance, b'', X'', hX'', hnorm, ?_⟩
  intro N hSN hNA
  have hNfg : N.FG := Submodule.FG.of_le hA hNA
  set N'' := N.map (U.mkQ.restrictScalars (𝓞 K)) with hN''

  have hUle : U ≤ Submodule.span K (N : Set V) := Submodule.span_mono hSN
  have hrk : rkK N'' + rkK S = rkK N := by
    have hspan : Submodule.span K (N'' : Set (V ⧸ U)) = (Submodule.span K (N : Set V)).map U.mkQ := by
      rw [hN'', Submodule.map_coe]
      exact Submodule.span_image U.mkQ
    let W := Submodule.span K (N : Set V)
    let fW : W →ₗ[K] V ⧸ U := U.mkQ ∘ₗ W.subtype
    have h1 := LinearMap.finrank_range_add_finrank_ker fW
    have hr : LinearMap.range fW = W.map U.mkQ := by
      rw [LinearMap.range_comp, Submodule.range_subtype]
    have hk : LinearMap.ker fW = U.comap W.subtype := by
      rw [LinearMap.ker_comp, Submodule.ker_mkQ]
    rw [hr, hk, (Submodule.comapSubtypeEquivOfLe hUle).finrank_eq] at h1
    unfold rkK
    rw [hspan]
    exact h1
  have hrkR : ((rkK N : ℝ) - rkK S) = rkK N'' := by
    rw [← hrk]; push_cast; ring

  let ρ := Formalism.HermitianLatticesTheory.realize b X
  let ρ'' := Formalism.HermitianLatticesTheory.realize b'' X''
  have hNlat := place_lattice_structure K V ι b X hX N hNfg
  have hN''lat := place_lattice_structure K (V ⧸ U) κ b'' X'' hX'' N'' (hNfg.map _)
  have : DiscreteTopology (zl ρ N) := hNlat.1.2
  have hsatN : Formalism.F.IsSaturated (zl ρ N) (zl ρ S) :=
    ⟨QuotientRealization.zl_mono ρ hSN, fun x hx hxs =>
      hSat.2.2 x (QuotientRealization.zl_mono ρ hNA hx) hxs⟩
  have : DiscreteTopology (Formalism.F.quot (zl ρ N) (zl ρ S)) :=
    (Formalism.F.degQuot _ _ _ inferInstance hsatN).1
  have : DiscreteTopology (zl ρ'' N'') := hN''lat.1.2
  let W := Submodule.span ℝ (zl ρ S : Set (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2)))
  let f : N →+ EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2) :=
    (Wᗮ.starProjection.toLinearMap.toAddMonoidHom).comp (ρ.comp N.subtype.toAddMonoidHom)
  let g : N →+ EuclideanSpace ℝ (InfinitePlace K × κ × Fin 2) :=
    ρ''.comp ((U.mkQ.toAddMonoidHom).comp N.subtype.toAddMonoidHom)
  have h1 : ∀ y, y ∈ Formalism.F.quot (zl ρ N) (zl ρ S) ↔ ∃ m : N, f m = y := by
    intro y
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
    · rintro ⟨⟨x, hx⟩, rfl⟩
      exact ⟨ρ x, ⟨x, hx, rfl⟩, rfl⟩
  have h2 : ∀ y, y ∈ zl ρ'' N'' ↔ ∃ m : N, g m = y := by
    intro y
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
    · rintro ⟨⟨x, hx⟩, rfl⟩
      exact ⟨U.mkQ x, ⟨x, hx, rfl⟩, rfl⟩
  have hn : ∀ m, ‖f m‖ = ‖g m‖ := by
    rintro ⟨x, hx⟩
    have hsq : ‖f ⟨x, hx⟩‖ ^ 2 = ‖g ⟨x, hx⟩‖ ^ 2 := by
      show ‖Wᗮ.starProjection (ρ x)‖ ^ 2 = ‖ρ'' (U.mkQ x)‖ ^ 2
      rw [QuotientRealization.proj_norm_sq b X S x, PlaceOperatorNorms.norm_sq_realize]
      simp only [hnorm]
      rfl
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 hsq
  have hcov := QuotientRealization.covol_eq_of_norm_eq f g _ _ h1 h2 hn
  have hht : htQ b X N S = ht b'' X'' N'' := by
    unfold htQ ht
    rw [hcov, hrkR, ← Nat.cast_mul, Real.rpow_natCast]
  refine ⟨hht, ?_⟩
  unfold sizeQ size
  rw [hht, hrkR]

end Formalism.HN
