import Mathlib

set_option autoImplicit false

noncomputable section

open TensorProduct

namespace GlobalTheory.Serre

section Eigen

variable {R O O' : Type*} [CommRing R] [CommRing O] [CommRing O'] [Algebra O O'] [Algebra O R]
  [Algebra O' R] [IsScalarTower O O' R]

variable (R O O') in

def mulChar : R ⊗[O] O' →ₐ[R] R :=
  Algebra.TensorProduct.lift (AlgHom.id R R) (IsScalarTower.toAlgHom O O' R) fun _ _ ↦ .all _ _

@[simp] theorem mulChar_tmul (r : R) (x : O') :
    mulChar R O O' (r ⊗ₜ x) = r * algebraMap O' R x := rfl

theorem exists_elem_of_unramified {A : Type*} [CommRing A] [Algebra R A]
    [Algebra.FormallyUnramified R A] [Algebra.EssFiniteType R A] (χ : A →ₐ[R] R) :
    ∃ e : A, χ e = 1 ∧ ∀ x, x * e = χ x • e := by
  let f : A ⊗[R] A →ₐ[R] A :=
    Algebra.TensorProduct.lift ((Algebra.ofId R A).comp χ) (AlgHom.id R A) fun _ _ ↦ .all _ _
  refine ⟨f (Algebra.FormallyUnramified.elem R A), ?_, fun x ↦ ?_⟩
  · have : ∀ z, χ (f z) = χ (Algebra.TensorProduct.lmul' R z) := fun z ↦ by
      induction z with
      | zero => simp
      | tmul x y => simp [f]
      | add z w hz hw => simp only [map_add, hz, hw]
    rw [this, Algebra.FormallyUnramified.lmul_elem, map_one]
  · simpa [f, Algebra.smul_def] using
      congrArg f (Algebra.FormallyUnramified.one_tmul_mul_elem (R := R) x)

variable {M : Type*} [AddCommGroup M] [Module O M] [Module O' M] [IsScalarTower O O' M]

theorem exists_eigen_of_unramified (N : Type*) [AddCommGroup N] [Module R N] [Module O N]
    [Module O' N] [IsScalarTower O R N] [IsScalarTower O' R N] [IsScalarTower O O' N]
    [Algebra.FormallyUnramified R (R ⊗[O] O')] [Algebra.EssFiniteType R (R ⊗[O] O')] :
    ∃ s : N ⊗[O'] M →ₗ[R] N ⊗[O] M, Function.Injective s ∧ ∀ z, z ∈ LinearMap.range s ↔
      ∀ x : O', (Algebra.lsmul O O M x).lTensor N z = algebraMap O' R x • z := by
  obtain ⟨e, he₁, he₂⟩ := exists_elem_of_unramified (mulChar R O O')
  let g : O' →ₐ[O] Module.End R (N ⊗[O] M) :=
    { toFun x := AlgebraTensorModule.lTensor R N (Algebra.lsmul O O M x)
      map_one' := by ext; simp
      map_mul' x y := by ext; simp
      map_zero' := by ext; simp
      map_add' x y := by ext; simp
      commutes' x := by ext; simp }
  let ρ : R ⊗[O] O' →ₐ[R] Module.End R (N ⊗[O] M) :=
    Algebra.TensorProduct.lift (Algebra.ofId R _) g fun r x ↦ Algebra.commute_algebraMap_left _ _
  have hρ : ∀ (r : R) (x : O') z, ρ (r ⊗ₜ x) z = r • (Algebra.lsmul O O M x).lTensor N z :=
    fun r x z ↦ rfl
  have hρe : ∀ (x : O') z, (Algebra.lsmul O O M x).lTensor N (ρ e z) = algebraMap O' R x • ρ e z :=
    fun x z ↦ by
      have := congrArg (fun y ↦ ρ y z) (he₂ (1 ⊗ₜ x))
      simpa only [map_mul, map_smul, Module.End.mul_apply, hρ, one_smul, mulChar_tmul, one_mul,
        LinearMap.smul_apply] using this
  have hρe' : ∀ (x : O') z, ρ e ((Algebra.lsmul O O M x).lTensor N z) = algebraMap O' R x • ρ e z :=
    fun x z ↦ by
      have := congrArg (fun y ↦ ρ y z) ((mul_comm _ _).trans (he₂ (1 ⊗ₜ x)))
      simpa only [map_mul, map_smul, Module.End.mul_apply, hρ, one_smul, mulChar_tmul, one_mul,
        LinearMap.smul_apply] using this
  let s : N ⊗[O'] M →ₗ[R] N ⊗[O] M := AlgebraTensorModule.lift
    { toFun n :=
        { toFun m := ρ e (n ⊗ₜ m)
          map_add' m m' := by rw [tmul_add, map_add]
          map_smul' x m := (hρe' x (n ⊗ₜ m)).trans (algebraMap_smul R x _) }
      map_add' n n' := LinearMap.ext fun m ↦ (congrArg (ρ e) (add_tmul n n' m)).trans (map_add _ _ _)
      map_smul' r n := LinearMap.ext fun m ↦ map_smul (ρ e) r (n ⊗ₜ m) }
  let q : N ⊗[O] M →ₗ[R] N ⊗[O'] M := mapOfCompatibleSMul O' O R N M
  have hq : ∀ y z, q (ρ y z) = mulChar R O O' y • q z := fun y z ↦ by
    induction y with
    | zero => simp
    | add y y' hy hy' => simp only [map_add, LinearMap.add_apply, hy, hy', add_smul]
    | tmul r x =>
      induction z with
      | zero => simp
      | add z z' hz hz' => simp only [map_add, hz, hz', smul_add]
      | tmul n m => simp [hρ, q, mul_smul]
  have hqs : ∀ z, q (s z) = z := fun z ↦ by
    induction z with
    | zero => simp
    | add z z' hz hz' => simp only [map_add, hz, hz']
    | tmul n m => exact (hq e (n ⊗ₜ m)).trans (by rw [he₁, one_smul]; rfl)
  have hsq : ∀ z, s (q z) = ρ e z := fun z ↦ by
    induction z with
    | zero => simp
    | add z z' hz hz' => simp only [map_add, hz, hz']
    | tmul n m => rfl
  refine ⟨s, Function.LeftInverse.injective hqs, fun z ↦ ⟨?_, fun hz ↦ ⟨q z, ?_⟩⟩⟩
  · rintro ⟨z, rfl⟩ x
    rw [← hqs z, hsq, hρe]
  · have : ∀ y, ρ y z = mulChar R O O' y • z := fun y ↦ by
      induction y with
      | zero => simp
      | add y y' hy hy' => simp only [map_add, LinearMap.add_apply, hy, hy', add_smul]
      | tmul r x => rw [hρ, hz, mulChar_tmul, mul_smul]
    rw [hsq, this, he₁, one_smul]

omit [Algebra O R] in

theorem exists_eigen_of_projective (M : Type*) [AddCommGroup M] [Module O M] [Module.Finite O M]
    [Module.Projective O M] {N L : Type*} [AddCommGroup N] [Module R N] [Module O N]
    [SMulCommClass O R N] [AddCommGroup L] [Module R L] [Module O L] [SMulCommClass O R L]
    (τ : O → R) (i : N →ₗ[R] L) (hi : Function.Injective i)
    (hlin : ∀ (x : O) n, i (x • n) = x • i n)
    (hr : ∀ l, l ∈ LinearMap.range i ↔ ∀ x : O, x • l = τ x • l) :
    ∃ j : N ⊗[O] M →ₗ[R] L ⊗[O] M, (∀ n m, j (n ⊗ₜ m) = i n ⊗ₜ m) ∧ Function.Injective j ∧
      ∀ z, z ∈ LinearMap.range j ↔ ∀ x : O, x • z = τ x • z := by
  let i' : N →ₗ[O] L := { i.toAddHom with map_smul' := hlin }
  let j : N ⊗[O] M →ₗ[R] L ⊗[O] M :=
    { (i'.rTensor M).toAddHom with
      map_smul' := fun r z ↦ by
        change i'.rTensor M (r • z) = r • i'.rTensor M z
        induction z with
        | zero => simp
        | add z z' hz hz' => simp only [smul_add, map_add, hz, hz']
        | tmul n m => simp [smul_tmul', i'] }
  refine ⟨j, fun _ _ ↦ rfl, Module.Flat.rTensor_preserves_injective_linearMap i' hi,
    fun z ↦ ⟨?_, fun hz ↦ ?_⟩⟩
  · rintro ⟨z, rfl⟩ x
    induction z with
    | zero => simp
    | add z z' hz hz' => simp only [smul_add, map_add, hz, hz']
    | tmul n m =>
      change (x • i n) ⊗ₜ[O] m = (τ x • i n) ⊗ₜ[O] m
      rw [(hr _).mp ⟨n, rfl⟩]
  · obtain ⟨n, t, s, -, -, hst⟩ := Module.Finite.exists_comp_eq_id_of_projective O M
    let c (k : Fin n) : L ⊗[O] M →ₗ[O] L :=
      (TensorProduct.rid O L).toLinearMap ∘ₗ (LinearMap.proj k ∘ₗ s).lTensor L
    have hc : ∀ k (r : R) z, c k (r • z) = r • c k z := fun k r z ↦ by
      induction z with
      | zero => simp
      | add z z' hz hz' => simp only [smul_add, map_add, hz, hz']
      | tmul l m => simpa [smul_tmul', c] using smul_comm _ r l
    have hsum : ∀ z, ∑ k, c k z ⊗ₜ[O] t (Pi.single k 1) = z := fun z ↦ by
      induction z with
      | zero => simp
      | add z z' hz hz' => simp only [map_add, add_tmul, Finset.sum_add_distrib, hz, hz']
      | tmul l m =>
        have hm : t (s m) = m := congr($hst m)
        conv_rhs => rw [← hm, pi_eq_sum_univ' (s m)]
        simp [c, smul_tmul, tmul_sum]
    choose u hu using fun k ↦ (hr (c k z)).mpr fun x ↦ by rw [← map_smul, hz, hc]
    refine ⟨∑ k, u k ⊗ₜ t (Pi.single k 1), ?_⟩
    rw [map_sum, ← hsum z]
    exact Finset.sum_congr rfl fun k _ ↦ by rw [← hu]; rfl

theorem exists_eigen_tensor [Module.Finite O M] [Module.Projective O M]
    {N L : Type*} [AddCommGroup N] [Module R N] [Module O N]
    [Module O' N] [IsScalarTower O R N] [IsScalarTower O' R N] [IsScalarTower O O' N]
    [Algebra.FormallyUnramified R (R ⊗[O] O')] [Algebra.EssFiniteType R (R ⊗[O] O')]
    [AddCommGroup L] [Module R L] [Module O L] [SMulCommClass O R L]
    (i : N →ₗ[R] L) (hi : Function.Injective i)
    (hr : ∀ l, l ∈ LinearMap.range i ↔ ∀ x : O, x • l = algebraMap O R x • l) :
    ∃ s : N ⊗[O'] M →ₗ[R] L ⊗[O] M, Function.Injective s ∧ ∀ z, z ∈ LinearMap.range s ↔
      ∀ x : O', (Algebra.lsmul O O M x).lTensor L z = algebraMap O' R x • z := by
  obtain ⟨s, hs₁, hs₂⟩ := exists_eigen_of_unramified (R := R) (O := O) (O' := O') (M := M) N
  obtain ⟨j, hj₀, hj₁, hj₂⟩ := exists_eigen_of_projective M (algebraMap O R) i hi
    (fun x n ↦ by rw [(hr _).mp ⟨n, rfl⟩, ← map_smul, algebraMap_smul]) hr
  have hj : ∀ (x : O') z, j ((Algebra.lsmul O O M x).lTensor N z) =
      (Algebra.lsmul O O M x).lTensor L (j z) := fun x z ↦ by
    induction z with
    | zero => simp
    | add z z' hz hz' => simp only [map_add, hz, hz']
    | tmul n m => simp [hj₀]
  refine ⟨j ∘ₗ s, hj₁.comp hs₁, fun z ↦ ⟨?_, fun hz ↦ ?_⟩⟩
  · rintro ⟨w, rfl⟩ x
    rw [LinearMap.comp_apply, ← hj, (hs₂ _).mp ⟨w, rfl⟩, map_smul]
  · obtain ⟨w, rfl⟩ := (hj₂ z).mpr fun x ↦ by
      rw [IsScalarTower.algebraMap_apply O O' R, ← hz, AlgHom.commutes]
      simp [Module.algebraMap_end_eq_smul_id]
    obtain ⟨v, rfl⟩ := (hs₂ w).mpr fun x ↦ hj₁ (by rw [hj, hz, map_smul])
    exact ⟨v, rfl⟩

end Eigen

section Integers

open NumberField

variable (k K E : Type*) [Field k] [CharZero k] [Field K] [Field E] [NumberField K] [NumberField E]
  [Algebra K E]

omit [NumberField K] in

theorem ringOfIntegers_injective (τ : 𝓞 K →+* k) : Function.Injective τ := by
  rw [RingHom.injective_iff_ker_eq_bot]
  refine Ideal.eq_bot_of_comap_eq_bot (R := ℤ) ?_
  rw [RingHom.comap_ker, ← RingHom.injective_iff_ker_eq_bot]
  exact RingHom.injective_int _

theorem formallyUnramified_ringOfIntegers [Algebra (𝓞 K) k] :
    Algebra.FormallyUnramified k (k ⊗[𝓞 K] 𝓞 E) := by
  have hinj := ringOfIntegers_injective k K (algebraMap (𝓞 K) k)
  let : Algebra K k := (IsFractionRing.lift hinj).toAlgebra
  have : IsScalarTower (𝓞 K) K k :=
    .of_algebraMap_eq fun x ↦ (IsFractionRing.lift_algebraMap hinj x).symm
  have : IsLocalization (Algebra.algebraMapSubmonoid (𝓞 E) (nonZeroDivisors (𝓞 K))) E :=
    IsIntegralClosure.isLocalization (𝓞 K) K E (𝓞 E)
  have : Algebra.IsPushout (𝓞 K) K (𝓞 E) E :=
    (Algebra.isPushout_of_isLocalization (nonZeroDivisors (𝓞 K)) K (𝓞 E) E).symm
  have : Algebra.FormallyUnramified K E := Algebra.FormallyUnramified.of_isSeparable K E
  have : Algebra.FormallyUnramified K (K ⊗[𝓞 K] 𝓞 E) :=
    .of_equiv (Algebra.IsPushout.equiv (𝓞 K) K (𝓞 E) E).symm
  exact .of_equiv (Algebra.TensorProduct.cancelBaseChange (𝓞 K) K k k (𝓞 E))

omit [CharZero k] [NumberField K] in

theorem finrank_fractionalIdeal {I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E} (hI : I ≠ 0) :
    Module.finrank (𝓞 E) I = 1 := by
  have h₁ : Module.finrank (𝓞 E) E = 1 := by
    rw [← IsFractionRing.finrank_right_eq (𝓞 E) E E, Module.finrank_self]
  have : Module.Finite (𝓞 E) I :=
    Module.Finite.iff_fg.mpr (FractionalIdeal.fg_of_isNoetherianRing le_rfl I)
  have : Nontrivial I :=
    Submodule.nontrivial_iff_ne_bot.mpr (FractionalIdeal.coeToSubmodule_ne_bot.mpr hI)
  refine le_antisymm ?_ Module.finrank_pos
  refine Module.finrank_le_of_rank_le ((Submodule.rank_le (I : Submodule (𝓞 E) E)).trans ?_)
  rw [← IsFractionRing.rank_right_eq (𝓞 E) E E, Module.rank_self, Nat.cast_one]

omit [CharZero k] in

theorem finrank_fractionalIdeal_restrict {I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E}
    (hI : I ≠ 0) : Module.finrank (𝓞 K) I = Module.finrank K E := by
  have : Module.Finite (𝓞 E) I :=
    Module.Finite.iff_fg.mpr (FractionalIdeal.fg_of_isNoetherianRing le_rfl I)
  have : Module.Finite (𝓞 K) I := Module.Finite.trans (𝓞 E) I
  have : Nontrivial I :=
    Submodule.nontrivial_iff_ne_bot.mpr (FractionalIdeal.coeToSubmodule_ne_bot.mpr hI)
  obtain ⟨x, hx⟩ := exists_ne (0 : (I : Submodule (𝓞 E) E))
  refine le_antisymm (Module.finrank_le_of_rank_le ?_) ?_
  · rw [Module.finrank_eq_rank, IsFractionRing.rank_right_eq (𝓞 K) K E]
    exact Submodule.rank_le ((I : Submodule (𝓞 E) E).restrictScalars (𝓞 K))
  · rw [IsFractionRing.finrank_eq (𝓞 K) K (𝓞 E) E]
    exact LinearMap.finrank_le_finrank_of_injective
      (f := (LinearMap.toSpanSingleton (𝓞 E) I x).restrictScalars (𝓞 K)) (smul_left_injective _ hx)

end Integers

theorem iSupIndep_eigen {k V I : Type*} [Field k] [AddCommGroup V] [Module k V]
    (f : I → Module.End k V) (hf : ∀ i j, Commute (f i) (f j)) :
    iSupIndep fun χ : I → k ↦ ⨅ i, (f i).eigenspace (χ i) :=
  (Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo f fun i j φ ↦
    Module.End.mapsTo_maxGenEigenspace_of_comm (hf j i) φ).mono fun _ ↦
      iInf_mono fun i ↦ ((f i).genEigenspace _).monotone le_top

end GlobalTheory.Serre
