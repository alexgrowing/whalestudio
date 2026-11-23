import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIntegralUnitRootNormOneAdeleStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenNsmulAdelicCompletionOfVectorSetStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAdeleRingTensorEquivInfiniteProdFiniteStatement

open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Topology Matrix

noncomputable section

namespace GlobalTheory.AdLat.RootNear

theorem inv_near {A R ι : Type} [CommRing A] [CommRing R] [Algebra A R] [TopologicalSpace A]
    [IsTopologicalRing A] [TopologicalSpace R] [IsModuleTopology A R] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι A R) (i : A → A) (hi : ContinuousAt i 1) (hi1 : i 1 = 1)
    (hii : ∀ᶠ a in 𝓝 (1 : A), a * i a = 1) :
    ∀ V ∈ 𝓝 (1 : R), ∀ᶠ x in 𝓝 (1 : R), ∃ y ∈ V, x * y = 1 := by
  intro V hV
  have : ContinuousAdd R := IsModuleTopology.toContinuousAdd A R
  have hM : Continuous (fun x : R => Algebra.leftMulMatrix b x) :=
    IsModuleTopology.continuous_of_linearMap (Algebra.leftMulMatrix b).toLinearMap
  have hb : Continuous (b.equivFun.symm) :=
    IsModuleTopology.continuous_of_linearMap b.equivFun.symm.toLinearMap
  let d : R → A := fun x => (Algebra.leftMulMatrix b x).det
  let adj : R → R := fun x => b.equivFun.symm ((Algebra.leftMulMatrix b x).adjugate *ᵥ b.equivFun 1)
  have hd : Continuous d := hM.matrix_det
  have hadj : Continuous adj := hb.comp (hM.matrix_adjugate.matrix_mulVec continuous_const)
  have hd1 : d 1 = 1 := by simp [d]
  have hadj1 : adj 1 = 1 := by simp [adj]
  have key : ∀ x, x * adj x = d x • (1 : R) := by
    intro x
    apply b.equivFun.injective
    have h1 : ∀ y : R, b.equivFun (x * y) = Algebra.leftMulMatrix b x *ᵥ b.equivFun y := by
      intro y
      have := Algebra.leftMulMatrix_mulVec_repr b x y
      simpa using this.symm
    rw [h1, map_smul]
    simp only [adj, d, LinearEquiv.apply_symm_apply, Matrix.mulVec_mulVec, Matrix.mul_adjugate,
      Matrix.smul_mulVec, Matrix.one_mulVec]
  have hdt : Filter.Tendsto d (𝓝 1) (𝓝 1) := by
    have := hd.tendsto 1
    rwa [hd1] at this
  have hy : Filter.Tendsto (fun x => i (d x) • adj x) (𝓝 1) (𝓝 1) := by
    have h1 : Filter.Tendsto (fun x => i (d x)) (𝓝 1) (𝓝 1) := by
      have := hi.tendsto
      rw [hi1] at this
      exact this.comp hdt
    have h2 := h1.smul (hadj.tendsto 1)
    simpa [hadj1] using h2
  filter_upwards [hy hV, hdt hii] with x h1 h2
  refine ⟨_, h1, ?_⟩
  rw [mul_smul_comm, key, smul_smul, mul_comm, h2, one_smul]

theorem unit_of_integral {A O : Type} [CommRing A] [CommRing O] (φ : A →+* O) (hφ : φ.IsIntegral) (j : A)
    (hj : ∀ a, IsUnit (1 + j * a)) (z : O) : IsUnit (1 + φ j * z) := by
  by_contra h
  obtain ⟨M, hM, hx⟩ := exists_max_ideal_of_mem_nonunits h
  have hm := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' φ hφ M
  have hjm : j ∈ M.comap φ := by
    have : j ∈ Ideal.jacobson (⊥ : Ideal A) := by
      rw [Ideal.mem_jacobson_bot]
      intro y
      rw [add_comm]; exact hj y
    exact Ideal.mem_sInf.1 this ⟨bot_le, hm⟩
  apply hM.ne_top
  rw [Ideal.eq_top_iff_one]
  have := M.sub_mem hx (M.mul_mem_right z (Ideal.mem_comap.1 hjm))
  simpa using this

theorem exists_idem {ι : Type} (O : ι → Type) [∀ v, CommRing (O v)] [∀ v, IsLocalRing (O v)] (n : ℕ) :
    ∃ e f : ∀ v, O v, e * e = e ∧ 1 - e = n * f ∧ ∀ a, IsUnit (1 + e * n * a) := by
  classical
  refine ⟨fun v => if IsUnit (n : O v) then 0 else 1,
    fun v => if IsUnit (n : O v) then Ring.inverse (n : O v) else 0, ?_, ?_, ?_⟩
  · funext v
    by_cases h : IsUnit (n : O v) <;> simp [h]
  · funext v
    by_cases h : IsUnit (n : O v) <;> simp [h, Ring.mul_inverse_cancel]
  · intro a
    rw [Pi.isUnit_iff]
    intro v
    by_cases h : IsUnit (n : O v)
    · simp [h]
    · have h2 : -((n : O v) * a v) ∈ nonunits (O v) := by
        intro h3
        exact h (isUnit_of_mul_isUnit_left ((IsUnit.neg_iff _).1 h3))
      simpa [h] using IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ h2

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def incl : (∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F) →+* FiniteAdeleRing (𝓞 F) F where
  toFun a := (⟨fun v => (a v : v.adicCompletion F), Filter.Eventually.of_forall fun v => (a v).2⟩ :
    RestrictedProduct (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => v.adicCompletionIntegers F) Filter.cofinite)
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

omit [NumberField E] in
theorem tmul_mem (a : FiniteAdeleRing (𝓞 F) F) (ha : ∀ v, a v ∈ v.adicCompletionIntegers F) (x : 𝓞 E) :
    a ⊗ₜ[F] (algebraMap (𝓞 E) E x) ∈ hat1 F (Set.range (algebraMap (𝓞 E) E)) :=
  AddSubgroup.subset_closure ⟨a, ha, _, ⟨x, rfl⟩, rfl⟩

omit [NumberField E] in
theorem mul_mem_hat {a b : RA F E} (ha : a ∈ hat1 F (Set.range (algebraMap (𝓞 E) E)))
    (hb : b ∈ hat1 F (Set.range (algebraMap (𝓞 E) E))) : a * b ∈ hat1 F (Set.range (algebraMap (𝓞 E) E)) := by
  induction ha, hb using AddSubgroup.closure_induction₂ with
  | mem x y hx hy =>
    obtain ⟨a, ha, _, ⟨s, rfl⟩, rfl⟩ := hx
    obtain ⟨b, hb, _, ⟨t, rfl⟩, rfl⟩ := hy
    rw [Algebra.TensorProduct.tmul_mul_tmul, ← map_mul]
    exact tmul_mem F E (a * b) (fun v => (v.adicCompletionIntegers F).mul_mem _ _ (ha v) (hb v)) (s * t)
  | zero_left x hx => rw [zero_mul]; exact AddSubgroup.zero_mem _
  | zero_right x hx => rw [mul_zero]; exact AddSubgroup.zero_mem _
  | add_left x y z _ _ _ h1 h2 => rw [add_mul]; exact AddSubgroup.add_mem _ h1 h2
  | add_right x y z _ _ _ h1 h2 => rw [mul_add]; exact AddSubgroup.add_mem _ h1 h2
  | neg_left x y _ _ h => rw [neg_mul]; exact AddSubgroup.neg_mem _ h
  | neg_right x y _ _ h => rw [mul_neg]; exact AddSubgroup.neg_mem _ h

def intHat : Subring (RA F E) where
  carrier := hat1 F (Set.range (algebraMap (𝓞 E) E))
  add_mem' := AddSubgroup.add_mem _
  zero_mem' := AddSubgroup.zero_mem _
  neg_mem' := AddSubgroup.neg_mem _
  one_mem' := by
    have := tmul_mem F E 1 (fun v => one_mem _) 1
    rw [map_one] at this
    exact this
  mul_mem' := mul_mem_hat F E

def inclHat : (∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F) →+* intHat F E :=
  ((Algebra.TensorProduct.includeLeftRingHom : FiniteAdeleRing (𝓞 F) F →+* RA F E).comp (incl F)).codRestrict
    (intHat F E) (fun a => by
      have := tmul_mem F E (incl F a) (fun v => (a v).2) 1
      rw [map_one] at this
      exact this)

def ratHat : 𝓞 E →+* intHat F E :=
  ((Algebra.TensorProduct.includeRight : E →ₐ[F] RA F E).toRingHom.comp (algebraMap (𝓞 E) E)).codRestrict
    (intHat F E) (fun x => tmul_mem F E 1 (fun v => one_mem _) x)

theorem inclHat_integral : (inclHat F E).IsIntegral := by
  letI := (inclHat F E).toAlgebra
  rintro ⟨z, hz⟩
  change IsIntegral (∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F) (⟨z, hz⟩ : intHat F E)
  induction hz using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, _, ⟨s, rfl⟩, rfl⟩ := hx
    have h1 : IsIntegral ℤ (ratHat F E s) :=
      (RingOfIntegers.isIntegral s).map (ratHat F E).toIntAlgHom
    have h2 : IsIntegral (∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F) (ratHat F E s) :=
      h1.tower_top
    have h3 := (isIntegral_algebraMap (A := intHat F E)
      (x := (fun v => ⟨a v, ha v⟩ : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F))).mul h2
    refine Eq.mpr (congrArg (IsIntegral _) (Subtype.ext ?_)) h3
    change _ = (a ⊗ₜ[F] (1 : E)) * ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (algebraMap (𝓞 E) E s))
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  | zero => exact isIntegral_zero
  | add x y _ _ h1 h2 => exact h1.add h2
  | neg x _ h => exact h.neg

omit [NumberField E] in
theorem half_root {A : Type} [CommRing A] [Algebra F A] (c : E ≃ₐ[F] E) (u x : A ⊗[F] E)
    (hu : u * sg A c u = 1) (hx : 2 * x = 1 + u) : x = u * sg A c x := by
  have h2 : IsUnit (2 : A ⊗[F] E) := by
    have := (IsUnit.mk0 (2 : F) two_ne_zero).map (algebraMap F (A ⊗[F] E))
    rwa [map_ofNat] at this
  apply h2.mul_left_cancel
  have := congrArg (sg A c) hx
  rw [map_mul, map_ofNat, map_add, map_one] at this
  linear_combination hx - u * this - hu

theorem finite_root (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hc : c ≠ 1)
    (hP : ∀ P : Ideal (𝓞 E), P.IsMaximal → ∃ t s : 𝓞 E, (s : E) = c (t : E) ∧ t - s ∉ P) (n : ℕ)
    (u z : RA F E) (hz : z ∈ intHat F E) (huz : u - 1 = (2 * n) • z)
    (hu : u * sg (FiniteAdeleRing (𝓞 F) F) c u = 1) :
    ∃ x y : RA F E, x * y = 1 ∧ x = u * sg (FiniteAdeleRing (𝓞 F) F) c x ∧
      (∃ p ∈ intHat F E, x = 1 + n • p) ∧ ∃ p ∈ intHat F E, y = 1 + n • p := by
  have hu1 : u = 1 + 2 * n * z := by
    rw [nsmul_eq_mul] at huz
    push_cast at huz
    linear_combination huz
  have huO : u ∈ intHat F E := by
    rw [hu1]
    exact add_mem (one_mem _) (mul_mem (mul_mem (ofNat_mem _ 2) (natCast_mem _ n)) hz)
  obtain ⟨x₁, hx₁, ⟨y₁, hy₁, hxy₁⟩, hr₁⟩ := GlobalTheory.T.exists_integral_unit_root_norm_one_adele F E c h2 hc hP u huO hu
  obtain ⟨e, f, hee, hef, hun⟩ :=
    exists_idem (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletionIntegers F) n
  obtain ⟨y₀, hy₀⟩ := (unit_of_integral (inclHat F E) (inclHat_integral F E) (e * n) hun ⟨z, hz⟩).exists_right_inv
  have hr₀ : (1 + n * z) = u * sg (FiniteAdeleRing (𝓞 F) F) c (1 + n * z) :=
    half_root F E c u _ hu (by rw [hu1]; ring)
  have hse : sg (FiniteAdeleRing (𝓞 F) F) c (inclHat F E e : RA F E) = (inclHat F E e : RA F E) := by
    change sg (FiniteAdeleRing (𝓞 F) F) c (incl F e ⊗ₜ[F] (1 : E)) = incl F e ⊗ₜ[F] (1 : E)
    simp [sg]
  have hee' : (inclHat F E e : RA F E) * inclHat F E e = inclHat F E e := by
    rw [← Subring.coe_mul, ← map_mul, hee]
  have hef' : 1 - (inclHat F E e : RA F E) = n * inclHat F E f := by
    have := congrArg (fun t => (inclHat F E t : RA F E)) hef
    simpa using this
  have hy₀' : (1 + (inclHat F E e : RA F E) * n * z) * y₀ = 1 := by
    have := congrArg (fun t : intHat F E => (t : RA F E)) hy₀
    simpa using this
  have heO := (inclHat F E e).2
  have hfO := (inclHat F E f).2
  have hy₀O := y₀.2
  generalize (inclHat F E e : RA F E) = e' at *
  generalize (inclHat F E f : RA F E) = f' at *
  generalize (y₀ : RA F E) = y' at *
  have hx₁' : x₁ ∈ intHat F E := hx₁
  have hy₁' : y₁ ∈ intHat F E := hy₁
  have hxy : (e' * (1 + n * z) + (1 - e') * x₁) * (e' * y' + (1 - e') * y₁) = 1 := by
    linear_combination e' * hy₀' + (1 - e') * hxy₁ +
      (y' - (1 + n * z) * y₁ - x₁ * y' + x₁ * y₁) * hee'
  have hp : e' * z + f' * (x₁ - 1) ∈ intHat F E :=
    add_mem (mul_mem heO hz) (mul_mem hfO (sub_mem hx₁' (one_mem _)))
  have hx : e' * (1 + n * z) + (1 - e') * x₁ = 1 + n * (e' * z + f' * (x₁ - 1)) := by
    linear_combination (x₁ - 1) * hef'
  refine ⟨_, _, hxy, ?_, ⟨_, hp, by rw [nsmul_eq_mul]; exact hx⟩,
    -((e' * y' + (1 - e') * y₁) * (e' * z + f' * (x₁ - 1))), ?_, ?_⟩
  · rw [map_add, map_mul, map_mul, map_sub, map_one, hse]
    linear_combination e' * hr₀ + (1 - e') * hr₁
  · exact neg_mem (mul_mem (add_mem (mul_mem heO hy₀O) (mul_mem (sub_mem (one_mem _) heO) hy₁')) hp)
  · rw [nsmul_eq_mul]
    rw [hx] at hxy
    linear_combination hxy

theorem finite_near (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hc : c ≠ 1)
    (hP : ∀ P : Ideal (𝓞 E), P.IsMaximal → ∃ t s : 𝓞 E, (s : E) = c (t : E) ∧ t - s ∉ P) :
    letI : TopologicalSpace (RA F E) := moduleTopology (FiniteAdeleRing (𝓞 F) F) (RA F E)
    ∀ V ∈ 𝓝 (1 : RA F E), ∀ᶠ u in 𝓝 (1 : RA F E), u * sg (FiniteAdeleRing (𝓞 F) F) c u = 1 →
      ∃ x ∈ V, ∃ y ∈ V, x * y = 1 ∧ x = u * sg (FiniteAdeleRing (𝓞 F) F) c x := by
  letI : TopologicalSpace (RA F E) := moduleTopology (FiniteAdeleRing (𝓞 F) F) (RA F E)
  have : IsModuleTopology (FiniteAdeleRing (𝓞 F) F) (RA F E) := ⟨rfl⟩
  have : ContinuousAdd (RA F E) := IsModuleTopology.toContinuousAdd (FiniteAdeleRing (𝓞 F) F) _
  intro V hV
  let L : Submodule (𝓞 E) (Fin 1 → E) :=
    Submodule.pi Set.univ (fun _ => LinearMap.range (Algebra.linearMap (𝓞 E) E))
  have hL : Submodule.span E (L : Set (Fin 1 → E)) = ⊤ := by
    rw [eq_top_iff]
    intro v _
    have h1 : (fun _ => (1 : E)) ∈ L := fun i _ => ⟨1, map_one (algebraMap (𝓞 E) E)⟩
    have h3 := Submodule.smul_mem _ (v 0) (Submodule.subset_span (R := E) h1)
    convert h3 using 1
    funext i
    rw [Subsingleton.elim i 0]
    simp
  obtain ⟨hopen, hbas⟩ := GlobalTheory.T.isOpen_nsmul_adelicCompletionOfVectorSet F E 1 L hL
  have hV0 : {y : RA F E | 1 + y ∈ V} ∈ 𝓝 (0 : RA F E) := by
    have : Continuous (fun y : RA F E => 1 + y) := continuous_const_add 1
    have h := this.tendsto 0
    rw [add_zero] at h
    exact h hV
  obtain ⟨n, hn, hnV⟩ := hbas _ hV0
  have hhat : ∀ y ∈ hat F (L : Set (Fin 1 → E)), y 0 ∈ intHat F E := by
    intro y hy
    induction hy using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨a, ha, w, hw, rfl⟩ := hx
      obtain ⟨s, hs⟩ := hw 0 (Set.mem_univ _)
      have := tmul_mem F E a ha s
      change a ⊗ₜ[F] (w 0) ∈ hat1 F (Set.range (algebraMap (𝓞 E) E))
      rw [← hs]
      exact this
    | zero => exact zero_mem _
    | add x y _ _ h1 h2 => exact add_mem h1 h2
    | neg x _ h => exact neg_mem h
  have hcont : Continuous (fun (u : RA F E) (_ : Fin 1) => u + (-1)) :=
    continuous_pi fun _ => continuous_id.add continuous_const
  have hN := ((hopen (2 * n) (by omega)).preimage hcont).mem_nhds (x := 1)
    ⟨0, zero_mem _, by funext i; simp⟩
  filter_upwards [hN] with u hu hn1
  obtain ⟨z, hz, hz2⟩ := hu
  have hz3 : u - 1 = (2 * n) • z 0 := by
    rw [sub_eq_add_neg]
    exact congrFun hz2 0
  obtain ⟨x, y, hxy, hx, ⟨p, hp, rfl⟩, ⟨q, hq, rfl⟩⟩ := finite_root F E c h2 hc hP n u (z 0) (hhat z hz) hz3 hn1
  exact ⟨_, hnV p hp, _, hnV q hq, hxy, hx⟩

theorem infinite_near (c : E ≃ₐ[F] E) :
    letI : TopologicalSpace (InfiniteAdeleRing F ⊗[F] E) :=
      moduleTopology (InfiniteAdeleRing F) (InfiniteAdeleRing F ⊗[F] E)
    ∀ V ∈ 𝓝 (1 : InfiniteAdeleRing F ⊗[F] E), ∀ᶠ u in 𝓝 (1 : InfiniteAdeleRing F ⊗[F] E),
      u * sg (InfiniteAdeleRing F) c u = 1 →
      ∃ x ∈ V, ∃ y ∈ V, x * y = 1 ∧ x = u * sg (InfiniteAdeleRing F) c x := by
  classical
  letI : TopologicalSpace (InfiniteAdeleRing F ⊗[F] E) :=
    moduleTopology (InfiniteAdeleRing F) (InfiniteAdeleRing F ⊗[F] E)
  have : IsModuleTopology (InfiniteAdeleRing F) (InfiniteAdeleRing F ⊗[F] E) := ⟨rfl⟩
  have : ContinuousAdd (InfiniteAdeleRing F ⊗[F] E) :=
    IsModuleTopology.toContinuousAdd (InfiniteAdeleRing F) _
  intro V hV
  have : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have hev : ∀ v : InfinitePlace F, Continuous (fun a : InfiniteAdeleRing F => a v) :=
    fun v => continuous_apply v
  have hinv := inv_near (Algebra.TensorProduct.basis (InfiniteAdeleRing F) (Module.finBasis F E))
    (fun a v => (a v)⁻¹)
    (continuousAt_pi.2 fun v => ((hev v).continuousAt (x := 1)).inv₀ (one_ne_zero))
    (funext fun v => inv_one)
    (by
      have : ∀ v : InfinitePlace F, ∀ᶠ a in 𝓝 (1 : InfiniteAdeleRing F), a v ≠ 0 :=
        fun v => ((hev v).continuousAt (x := 1)).eventually_ne one_ne_zero
      filter_upwards [Filter.eventually_all.2 this] with a ha
      exact funext fun v => mul_inv_cancel₀ (ha v)) V hV
  let h : InfiniteAdeleRing F := algebraMap F _ 2⁻¹
  have hh : ∀ w : InfiniteAdeleRing F ⊗[F] E, 2 * (h • w) = w := by
    intro w
    rw [algebraMap_smul, ← map_ofNat (algebraMap F (InfiniteAdeleRing F ⊗[F] E)) 2, ← Algebra.smul_def,
      smul_smul, mul_inv_cancel₀ two_ne_zero, one_smul]
  have hcont : Continuous (fun u : InfiniteAdeleRing F ⊗[F] E => h • (1 + u)) :=
    (continuous_const.add continuous_id).const_smul h
  have ht := hcont.tendsto 1
  have h11 : h • ((1 : InfiniteAdeleRing F ⊗[F] E) + 1) = 1 := by
    rw [smul_add, ← two_mul, hh]
  rw [h11] at ht
  filter_upwards [ht hV, ht hinv] with u h1 h3 hu
  obtain ⟨y, hy, hxy⟩ := h3
  exact ⟨_, h1, y, hy, hxy, half_root F E c u _ hu (hh _)⟩

theorem units_nhds {M : Type} [Monoid M] [TopologicalSpace M] (W : Set Mˣ) (hW : W ∈ 𝓝 (1 : Mˣ)) :
    ∃ V ∈ 𝓝 (1 : M), ∀ x : Mˣ, (x : M) ∈ V → ((x⁻¹ : Mˣ) : M) ∈ V → x ∈ W := by
  rw [Units.isInducing_embedProduct.nhds_eq_comap, Filter.mem_comap] at hW
  obtain ⟨T, hT, hTW⟩ := hW
  rw [map_one] at hT
  obtain ⟨V₁, h₁, V₂, h₂, hsub⟩ := mem_nhds_prod_iff.1 hT
  have h₃ : MulOpposite.op ⁻¹' V₂ ∈ 𝓝 (1 : M) := MulOpposite.continuous_op.continuousAt.preimage_mem_nhds h₂
  exact ⟨_, Filter.inter_mem h₁ h₃, fun x hx hy => hTW (hsub ⟨hx.1, hy.2⟩)⟩

omit [NumberField F] [NumberField E] in
theorem map_sg {A B : Type} [CommRing A] [Algebra F A] [CommRing B] [Algebra F B] (c : E ≃ₐ[F] E)
    (p : A →ₐ[F] B) (z : A ⊗[F] E) :
    Algebra.TensorProduct.map p (AlgHom.id F E) (sg A c z) =
      sg B c (Algebra.TensorProduct.map p (AlgHom.id F E) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => simp [sg]
  | add x y h1 h2 => simp only [map_add, h1, h2]

theorem exists_root_near : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E), Module.finrank F E = 2 → c ≠ 1 → (∀ P : Ideal (𝓞 E), P.IsMaximal → ∃ t s : 𝓞 E, (s : E) = c (t : E) ∧ t - s ∉ P) → letI : TopologicalSpace (AdeleRing (𝓞 F) F ⊗[F] E) := moduleTopology (AdeleRing (𝓞 F) F) (AdeleRing (𝓞 F) F ⊗[F] E); ∀ W ∈ 𝓝 (1 : (AdeleRing (𝓞 F) F ⊗[F] E)ˣ), ∃ N ∈ 𝓝 (1 : (AdeleRing (𝓞 F) F ⊗[F] E)ˣ), ∀ u ∈ N, (u : AdeleRing (𝓞 F) F ⊗[F] E) * sg (AdeleRing (𝓞 F) F) c u = 1 → ∃ x ∈ W, (x : AdeleRing (𝓞 F) F ⊗[F] E) = u * sg (AdeleRing (𝓞 F) F) c x := by
  intro F E _ _ _ _ _ c h2 hc hP
  letI : TopologicalSpace (AdeleRing (𝓞 F) F ⊗[F] E) :=
    moduleTopology (AdeleRing (𝓞 F) F) (AdeleRing (𝓞 F) F ⊗[F] E)
  letI : TopologicalSpace (RA F E) := moduleTopology (FiniteAdeleRing (𝓞 F) F) (RA F E)
  letI : TopologicalSpace (InfiniteAdeleRing F ⊗[F] E) :=
    moduleTopology (InfiniteAdeleRing F) (InfiniteAdeleRing F ⊗[F] E)
  intro W hW
  obtain ⟨V, hV, hVW⟩ := units_nhds W hW
  obtain ⟨e, he, hec, hes⟩ := GlobalTheory.T.exists_adeleRing_tensor_equiv_infinite_prod_finite F E
  have hs1 : ∀ z, (e (sg (AdeleRing (𝓞 F) F) c z)).1 = sg _ c (e z).1 := fun z => by
    rw [(he _).1, (he _).1]
    exact map_sg F E c _ z
  have hs2 : ∀ z, (e (sg (AdeleRing (𝓞 F) F) c z)).2 = sg _ c (e z).2 := fun z => by
    rw [(he _).2, (he _).2]
    exact map_sg F E c _ z
  have hV' : e.symm ⁻¹' V ∈ 𝓝 (1 : (InfiniteAdeleRing F ⊗[F] E) × RA F E) :=
    hes.continuousAt.preimage_mem_nhds (by rwa [map_one])
  obtain ⟨V₁, h₁, V₂, h₂, hsub⟩ := mem_nhds_prod_iff.1 hV'
  have ht : Filter.Tendsto (fun u : (AdeleRing (𝓞 F) F ⊗[F] E)ˣ => e u) (𝓝 1) (𝓝 1) := by
    have := (hec.comp Units.continuous_val).tendsto 1
    simpa [Function.comp_def] using this
  have ht1 := (continuous_fst.tendsto _).comp ht
  have ht2 := (continuous_snd.tendsto _).comp ht
  refine ⟨_, Filter.inter_mem (ht1 (infinite_near F E c V₁ h₁)) (ht2 (finite_near F E c h2 hc hP V₂ h₂)), ?_⟩
  rintro u ⟨hu1, hu2⟩ hu
  have heu := congrArg e hu
  rw [map_mul, map_one] at heu
  obtain ⟨x₁, hx₁, y₁, hy₁, hxy₁, hr₁⟩ := hu1 (by
    have := congrArg Prod.fst heu
    rw [Prod.fst_mul, hs1] at this
    exact this)
  obtain ⟨x₂, hx₂, y₂, hy₂, hxy₂, hr₂⟩ := hu2 (by
    have := congrArg Prod.snd heu
    rw [Prod.snd_mul, hs2] at this
    exact this)
  have hxy : e.symm (x₁, x₂) * e.symm (y₁, y₂) = 1 := by
    rw [← map_mul, Prod.mk_mul_mk, hxy₁, hxy₂]
    exact map_one _
  refine ⟨⟨e.symm (x₁, x₂), e.symm (y₁, y₂), hxy, by rw [mul_comm]; exact hxy⟩,
    hVW _ (hsub (⟨hx₁, hx₂⟩ : (x₁, x₂) ∈ V₁ ×ˢ V₂)) (hsub (⟨hy₁, hy₂⟩ : (y₁, y₂) ∈ V₁ ×ˢ V₂)), ?_⟩
  apply e.injective
  change e (e.symm (x₁, x₂)) = e (u * sg (AdeleRing (𝓞 F) F) c (e.symm (x₁, x₂)))
  rw [map_mul]
  apply Prod.ext
  · rw [Prod.fst_mul, hs1, e.apply_symm_apply]
    exact hr₁
  · rw [Prod.snd_mul, hs2, e.apply_symm_apply]
    exact hr₂

end GlobalTheory.AdLat.RootNear
