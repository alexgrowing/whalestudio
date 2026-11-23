import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IsCplAtSelf

open IsLocalRing TensorProduct

namespace UpperTheory.Reformulated.B.FlatnessPrecompleteProducts

open UpperTheory.V.AlgebraTools

private lemma mem_smul_top_pi {L : Type} [CommRing L] (I : Ideal L) {n : ℕ} (x : Fin n → L) :
    x ∈ (I • ⊤ : Submodule L (Fin n → L)) ↔ ∀ i, x i ∈ I := by
  constructor
  · intro hx i
    refine Submodule.smul_induction_on (p := fun y : Fin n → L => y i ∈ I) hx ?_ ?_
    · intro r hr y _
      exact I.mul_mem_right _ hr
    · intro y z hy hz
      exact I.add_mem hy hz
  · intro h
    rw [pi_eq_sum_univ x]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (h i) Submodule.mem_top

private lemma precomplete_pi {L : Type} [CommRing L] (I : Ideal L) [IsPrecomplete I L] (n : ℕ) :
    IsPrecomplete I (Fin n → L) := by
  refine ⟨fun f hf => ?_⟩
  have h : ∀ i, ∃ x : L, ∀ k, f k i ≡ x [SMOD (I ^ k • ⊤ : Submodule L L)] := by
    intro i
    refine IsPrecomplete.prec' (fun k => f k i) ?_
    intro a b hab
    have := (mem_smul_top_pi _ _).1 (SModEq.sub_mem.1 (hf hab)) i
    rw [SModEq.sub_mem]
    simpa using this
  choose x hx using h
  refine ⟨x, fun k => ?_⟩
  rw [SModEq.sub_mem, mem_smul_top_pi]
  intro i
  simpa using SModEq.sub_mem.1 (hx i k)

private lemma map_eq_max {R : Type} [CommRing R] {q : Ideal R} {B : Type} [CommRing B]
    [IsLocalRing B] [Algebra R B] (h : IsCplAt R q B) :
    q.map (algebraMap R B) = maximalIdeal B := by
  have := h.noeth
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap, h.comap_eq]
  · apply Submodule.le_of_le_smul_of_le_jacobson_bot (I := maximalIdeal B)
      (IsNoetherian.noetherian _) (maximalIdeal_le_jacobson _)
    intro x hx
    obtain ⟨a, s, hs, hsa⟩ := h.dense 2 x
    have hu : IsUnit (algebraMap R B s) := by
      by_contra hn
      apply hs
      rw [← h.comap_eq]
      exact hn
    have ha : a ∈ q := by
      rw [← h.comap_eq, Ideal.mem_comap]
      have h1 := Ideal.pow_le_self (two_ne_zero) hsa
      have h2 := (maximalIdeal B).sub_mem (Ideal.mul_mem_left _ (algebraMap R B s) hx) h1
      simpa using h2
    rw [← Ideal.unit_mul_mem_iff_mem _ hu]
    have : algebraMap R B s * x = algebraMap R B a + (algebraMap R B s * x - algebraMap R B a) := by
      ring
    rw [this]
    refine Submodule.add_mem_sup (Ideal.mem_map_of_mem _ ha) ?_
    rwa [smul_eq_mul, ← pow_two]

private lemma flat_of_isCplAt {R : Type} [CommRing R] [IsNoetherianRing R] {q : Ideal R}
    {B : Type} [CommRing B] [IsLocalRing B] [Algebra R B] (h : IsCplAt R q B) :
    Module.Flat R B := by
  have := h.isPrime
  have := h.complete
  have hu : ∀ s : q.primeCompl, IsUnit (algebraMap R B s) := by
    intro s
    by_contra hn
    apply s.2
    have : (s : R) ∈ (maximalIdeal B).comap (algebraMap R B) := hn
    rwa [h.comap_eq] at this
  let S := Localization.AtPrime q
  letI : Algebra S B := (IsLocalization.lift (M := q.primeCompl) hu).toAlgebra
  haveI : IsScalarTower R S B := IsScalarTower.of_algebraMap_eq fun x =>
    (IsLocalization.lift_eq (M := q.primeCompl) hu x).symm
  have hm : (maximalIdeal S).map (algebraMap S B) = maximalIdeal B := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, ← IsScalarTower.algebraMap_eq,
      map_eq_max h]
  have hmem : ∀ (n : ℕ) (b : B),
      b ∈ (maximalIdeal S ^ n • ⊤ : Submodule S B) ↔ b ∈ maximalIdeal B ^ n := by
    intro n b
    rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem, Ideal.map_pow, hm]
  haveI : IsAdicComplete (maximalIdeal S) B :=
    { toIsHausdorff := (IsHausdorff.map_algebraMap_iff (S := B)).1 (by rw [hm]; infer_instance)
      toIsPrecomplete := (IsPrecomplete.map_algebraMap_iff (S := B)).1 (by rw [hm]; infer_instance) }
  have hsurj : Function.Surjective
      (AdicCompletion.map (maximalIdeal S) (Algebra.linearMap S B)) := by
    apply AdicCompletion.map_surjective_of_mkQ_comp_surjective
    intro y
    obtain ⟨b, rfl⟩ := Submodule.mkQ_surjective _ y
    obtain ⟨a, s, hs, hsa⟩ := h.dense 1 b
    refine ⟨IsLocalization.mk' S a (⟨s, hs⟩ : q.primeCompl), ?_⟩
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply, Algebra.linearMap_apply]
    rw [eq_comm, Submodule.Quotient.eq, ← pow_one (maximalIdeal S), hmem,
      ← Ideal.unit_mul_mem_iff_mem _ (hu ⟨s, hs⟩), mul_sub]
    have : algebraMap R B s * algebraMap S B (IsLocalization.mk' S a (⟨s, hs⟩ : q.primeCompl))
        = algebraMap R B a := by
      rw [IsScalarTower.algebraMap_apply R S B s, ← map_mul,
        IsLocalization.mk'_spec' S a (⟨s, hs⟩ : q.primeCompl), ← IsScalarTower.algebraMap_apply]
    rw [this]
    exact hsa
  have hinj : Function.Injective
      (AdicCompletion.map (maximalIdeal S) (Algebra.linearMap S B)) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    ext n
    have h1 := AdicCompletion.map_val_apply (maximalIdeal S) (Algebra.linearMap S B) (n := n) x
    rw [hx] at h1
    obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (x.1 n)
    rw [← hy] at h1 ⊢
    have h2 : algebraMap S B y ∈ maximalIdeal B ^ n := by
      rw [← hmem, ← Submodule.Quotient.mk_eq_zero]
      exact h1.symm
    change _ = (0 : S ⧸ (maximalIdeal S ^ n • ⊤ : Submodule S S))
    rw [Submodule.Quotient.mk_eq_zero]
    obtain ⟨⟨a, t⟩, rfl⟩ := IsLocalization.mk'_surjective q.primeCompl y
    have h3 : algebraMap R B a ∈ maximalIdeal B ^ n := by
      rw [IsScalarTower.algebraMap_apply R S B a, ← IsLocalization.mk'_spec' S a t, map_mul]
      exact Ideal.mul_mem_left _ _ h2
    obtain ⟨s, hs, hsa⟩ := h.strict n a h3
    rw [smul_eq_mul, Ideal.mul_top, ← Localization.AtPrime.map_eq_maximalIdeal, ← Ideal.map_pow]
    exact (IsLocalization.mk'_mem_map_algebraMap_iff q.primeCompl S _ _ _).2 ⟨s, hs, hsa⟩
  let e : AdicCompletion (maximalIdeal S) S ≃ₗ[S] B :=
    ((LinearEquiv.ofBijective _ ⟨hinj, hsurj⟩).restrictScalars S).trans
      (AdicCompletion.ofLinearEquiv (maximalIdeal S) B).symm
  haveI : Module.Flat S B := Module.Flat.of_linearEquiv e.symm
  haveI : Module.Flat R S := IsLocalization.flat S q.primeCompl
  exact Module.Flat.trans R S B

private lemma smul_mem_of_dense {L R B W : Type} [CommRing L] [CommRing R] [CommRing B]
    [IsLocalRing B] [Algebra L B] [Algebra R B] [AddCommGroup W] [Module L W] [Module B W]
    [IsScalarTower L B W] [IsHausdorff (maximalIdeal B) W]
    (hd : ∀ (n : ℕ) (b : B), ∃ a s : R, IsUnit (algebraMap R B s) ∧
      algebraMap R B s * b - algebraMap R B a ∈ maximalIdeal B ^ n)
    (V : Submodule L W) [IsArtinian L V] (hV : ∀ (r : R), ∀ v ∈ V, algebraMap R B r • v ∈ V)
    (b : B) (v : W) (hv : v ∈ V) : b • v ∈ V := by
  have h1 : ∀ n : ℕ, ∃ w ∈ V, b • v - w ∈ (maximalIdeal B ^ n • ⊤ : Submodule B W) := by
    intro n
    obtain ⟨a, s, hs, hsa⟩ := hd n b
    let f : V →ₗ[L] V := ((LinearMap.lsmul B W (algebraMap R B s)).restrictScalars L).restrict
      (hV s)
    have hf : Function.Injective f := by
      intro x y hxy
      apply Subtype.ext
      have : algebraMap R B s • (x : W) = algebraMap R B s • (y : W) := congrArg Subtype.val hxy
      exact (hs.smul_left_cancel).1 this
    obtain ⟨w, hw⟩ := IsArtinian.surjective_of_injective_endomorphism f hf ⟨_, hV a v hv⟩
    have hw' : algebraMap R B s • (w : W) = algebraMap R B a • v := congrArg Subtype.val hw
    refine ⟨w, w.2, ?_⟩
    rw [← Submodule.smul_mem_iff_of_isUnit _ hs, smul_sub, hw', smul_smul, ← sub_smul]
    exact Submodule.smul_mem_smul hsa Submodule.mem_top
  choose w hwV hw using h1
  let g : ℕ →o (Submodule L V)ᵒᵈ :=
    ⟨fun n => ((maximalIdeal B ^ n • ⊤ : Submodule B W).restrictScalars L).comap V.subtype,
      fun m n hmn x hx => Submodule.pow_smul_top_le _ W hmn hx⟩
  obtain ⟨k, hk⟩ := IsArtinian.monotone_stabilizes g
  have h2 : b • v - w k = 0 := by
    apply IsHausdorff.haus' (I := maximalIdeal B)
    intro n
    rw [SModEq.zero]
    apply Submodule.pow_smul_top_le _ W (le_max_left n k)
    have h3 : (⟨w (max n k) - w k, V.sub_mem (hwV _) (hwV _)⟩ : V) ∈ OrderDual.ofDual (g k) := by
      have := Submodule.sub_mem _ (hw k)
        (Submodule.pow_smul_top_le _ W (le_max_right n k) (hw (max n k)))
      rw [sub_sub_sub_cancel_left] at this
      exact this
    rw [hk _ (le_max_right n k)] at h3
    have h4 : w (max n k) - w k ∈ (maximalIdeal B ^ (max n k) • ⊤ : Submodule B W) := h3
    have := Submodule.add_mem _ (hw (max n k)) h4
    rwa [sub_add_sub_cancel] at this
  rw [sub_eq_zero.1 h2]
  exact hwV k

private lemma finite_of_dense {L R B N : Type} [CommRing L] [IsLocalRing L] [CommRing R]
    [CommRing B] [IsLocalRing B] [IsNoetherianRing B] [Algebra L B] [Algebra R B]
    [AddCommGroup N] [Module L N] [Module B N] [IsScalarTower L B N] [Module.Finite B N]
    [IsPrecomplete (maximalIdeal L) L]
    (hloc : (maximalIdeal L).map (algebraMap L B) ≤ maximalIdeal B)
    (hd : ∀ (n : ℕ) (b : B), ∃ a s : R, IsUnit (algebraMap R B s) ∧
      algebraMap R B s * b - algebraMap R B a ∈ maximalIdeal B ^ n)
    (U : Submodule L N) (hfg : U.FG) (hU : ∀ (r : R), ∀ v ∈ U, algebraMap R B r • v ∈ U)
    (hspan : Submodule.span B (U : Set N) = ⊤) : Module.Finite L N := by
  obtain ⟨n, f, hf⟩ : ∃ (n : ℕ) (f : (Fin n → L) →ₗ[L] N), LinearMap.range f = U :=
    (Submodule.fg_iff_exists_fin_linearMap L N).1 hfg
  haveI := precomplete_pi (maximalIdeal L) n
  haveI : IsHausdorff (maximalIdeal L) N := IsHausdorff.of_map hloc
  refine Module.Finite.of_surjective f (surjective_of_mkQ_comp_surjective (I := maximalIdeal L) ?_)
  let P : Submodule B N := (maximalIdeal L).map (algebraMap L B) • ⊤
  have hP : ∀ x, x ∈ P ↔ x ∈ (maximalIdeal L • ⊤ : Submodule L N) := by
    intro x
    rw [← Submodule.restrictScalars_mem L, Submodule.restrictScalars_map_smul_eq,
      Submodule.restrictScalars_top]
  let π : N →ₗ[L] N ⧸ P := P.mkQ.restrictScalars L
  let F := Fin n → L
  let Q : Submodule L F := maximalIdeal L • ⊤
  have hQ : Q ≤ LinearMap.ker (π ∘ₗ f) := by
    intro x hx
    have : f x ∈ P := by
      rw [hP]
      have := Submodule.mem_map_of_mem (f := f) hx
      rw [Submodule.map_smul''] at this
      exact Submodule.smul_mono le_rfl le_top this
    exact (Submodule.Quotient.mk_eq_zero P).2 this
  haveI : IsArtinian L (F ⧸ Q) := by
    letI : Field (L ⧸ maximalIdeal L) := Ideal.Quotient.field _
    haveI : Module.Finite (L ⧸ maximalIdeal L) (F ⧸ Q) :=
      Module.Finite.of_restrictScalars_finite L _ _
    exact isArtinian_of_surjective_algebraMap (R := L ⧸ maximalIdeal L)
      Ideal.Quotient.mk_surjective
  let V : Submodule L (N ⧸ P) := LinearMap.range (Q.liftQ _ hQ)
  have hV : ∀ y, y ∈ V ↔ ∃ u ∈ U, P.mkQ u = y := by
    intro y
    simp only [V, Submodule.range_liftQ, ← hf, LinearMap.mem_range]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨_, ⟨x, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨x, rfl⟩
  have hall : ∀ x : N, P.mkQ x ∈ V := by
    intro x
    have hx : x ∈ Submodule.span B (U : Set N) := hspan ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem x hx => exact (hV _).2 ⟨x, hx, rfl⟩
    | zero => rw [map_zero]; exact V.zero_mem
    | add x y _ _ hx hy => rw [map_add]; exact V.add_mem hx hy
    | smul b x _ hx =>
      rw [map_smul]
      refine smul_mem_of_dense hd V ?_ b _ hx
      intro r v hv
      obtain ⟨u, hu, rfl⟩ := (hV _).1 hv
      exact (hV _).2 ⟨_, hU r u hu, map_smul _ _ _⟩
  intro y
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ y
  obtain ⟨u, hu, hux⟩ := (hV _).1 (hall x)
  rw [← hf] at hu
  obtain ⟨z, rfl⟩ := hu
  refine ⟨z, ?_⟩
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, hP] at hux
  exact (Submodule.Quotient.eq _).2 hux

private lemma flat_tensor {Λ R B M : Type} [CommRing Λ] [CommRing R] [CommRing B] [Algebra Λ R]
    [Algebra R B] [Algebra Λ B] [IsScalarTower Λ R B] [AddCommGroup M] [Module R M] [Module Λ M]
    [IsScalarTower Λ R M] [Module.Flat Λ M] [Module.Flat R B] : Module.Flat Λ (B ⊗[R] M) := by
  rw [Module.Flat.iff_lTensor_injective']
  intro I
  have h1 : Function.Injective (AlgebraTensorModule.lTensor R M I.subtype) :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := M) I.subtype I.injective_subtype
  have h2 := Module.Flat.lTensor_preserves_injective_linearMap (M := B) _ h1
  have h3 : ∀ x, AlgebraTensorModule.assoc Λ R B B M Λ (LinearMap.lTensor (B ⊗[R] M) I.subtype x)
      = LinearMap.lTensor B (AlgebraTensorModule.lTensor R M I.subtype)
        (AlgebraTensorModule.assoc Λ R B B M I x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul y i =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [add_tmul, map_add, hx, hy]
      | tmul b m => simp
  intro x y hxy
  apply (AlgebraTensorModule.assoc Λ R B B M I).injective
  apply h2
  rw [← h3, ← h3, hxy]

private lemma free_of_flat {Λ L N : Type} [CommRing Λ] [CommRing L] [IsLocalRing L]
    [IsNoetherianRing L] [Algebra Λ L] [AddCommGroup N] [Module Λ N] [Module L N]
    [IsScalarTower Λ L N] [Module.Flat Λ N] [Module.Finite L N] (p : Ideal Λ)
    (hp : p.map (algebraMap Λ L) = maximalIdeal L) : Module.Free L N := by
  haveI : Module.FinitePresentation L N := Module.finitePresentation_of_finite L N
  apply Module.free_of_maximalIdeal_rTensor_injective
  have hmem : ∀ x : p, algebraMap Λ L x ∈ maximalIdeal L := fun x =>
    hp ▸ Ideal.mem_map_of_mem _ x.2
  let j : p →ₗ[Λ] maximalIdeal L :=
    LinearMap.codRestrict ((maximalIdeal L).restrictScalars Λ)
      (Algebra.linearMap Λ L ∘ₗ p.subtype) hmem
  let ψ : p ⊗[Λ] N →ₗ[Λ] (maximalIdeal L) ⊗[L] N :=
    mapOfCompatibleSMul L Λ Λ (maximalIdeal L) N ∘ₗ j.rTensor N
  have hψ : ∀ (x : p) (n : N), ψ (x ⊗ₜ n) = (⟨_, hmem x⟩ : maximalIdeal L) ⊗ₜ n := fun _ _ => rfl
  have hsurj : ∀ z, z ∈ LinearMap.range ψ := by
    have key : ∀ (x : L) (hx : x ∈ Submodule.span L (algebraMap Λ L '' p))
        (hx' : x ∈ maximalIdeal L) (n : N),
        (⟨x, hx'⟩ : maximalIdeal L) ⊗ₜ[L] n ∈ LinearMap.range ψ := by
      have hle : ∀ x ∈ Submodule.span L (algebraMap Λ L '' p), x ∈ maximalIdeal L :=
        fun x hx => hp ▸ hx
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨a, ha, rfl⟩ := hx
        intro _ n
        exact ⟨_, hψ ⟨a, ha⟩ n⟩
      | zero =>
        intro _ n
        have : (⟨0, ‹_›⟩ : maximalIdeal L) = 0 := rfl
        rw [this, zero_tmul]
        exact zero_mem _
      | add x y hx hy ihx ihy =>
        intro _ n
        have : (⟨x + y, ‹_›⟩ : maximalIdeal L) = ⟨x, hle x hx⟩ + ⟨y, hle y hy⟩ := rfl
        rw [this, add_tmul]
        exact add_mem (ihx _ _) (ihy _ _)
      | smul l x hx ih =>
        intro _ n
        have : (⟨l • x, ‹_›⟩ : maximalIdeal L) = l • ⟨x, hle x hx⟩ := rfl
        rw [this, smul_tmul]
        exact ih _ _
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact zero_mem _
    | add x y hx hy => exact add_mem hx hy
    | tmul x n => exact key x.1 (hp.ge x.2) x.2 n
  have hcomp : ∀ y, TensorProduct.lid L N (LinearMap.rTensor N (maximalIdeal L).subtype (ψ y))
      = TensorProduct.lid Λ N (LinearMap.rTensor N p.subtype y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul x n => rw [hψ]; simp
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨y, rfl⟩ := hsurj z
  have h0 := hcomp y
  rw [hz, map_zero, eq_comm, LinearEquiv.map_eq_zero_iff] at h0
  have hy : y = 0 :=
    Module.Flat.rTensor_preserves_injective_linearMap (M := N) p.subtype p.injective_subtype
      (by rw [h0, map_zero])
  rw [hy, map_zero]

end UpperTheory.Reformulated.B.FlatnessPrecompleteProducts

theorem UpperTheory.Reformulated.B.FlatnessPrecompleteProducts.finite_free_baseChange :
    ∀ (Λ R : Type) [inst : CommRing Λ] [IsNoetherianRing Λ] [inst_2 : CommRing R] [IsNoetherianRing R]
      [inst_4 : Algebra Λ R] (p : Ideal Λ) (q : Ideal R) (L B : Type) [inst_5 : CommRing L] [inst_6 : IsLocalRing L]
      [inst_7 : CommRing B] [inst_8 : IsLocalRing B] [inst_9 : Algebra Λ L] [inst_10 : Algebra R B] [inst_11 : Algebra L B]
      [inst_12 : Algebra Λ B] [IsScalarTower Λ R B] [IsScalarTower Λ L B] (M : Type) [inst_15 : AddCommGroup M]
      [inst_16 : _root_.Module R M] [inst_17 : _root_.Module Λ M] [IsScalarTower Λ R M] [Module.Finite Λ M]
      [Module.Flat Λ M],
      UpperTheory.V.AlgebraTools.IsCplAt Λ p L →
        UpperTheory.V.AlgebraTools.IsCplAt R q B →
          Ideal.comap (Algebra.algebraMap Λ R) q = p →
            Module.Finite L (TensorProduct R B M) ∧ Module.Free L (TensorProduct R B M) := by
  intro Λ R _ _ _ _ _ p q L B _ _ _ _ _ _ _ _ _ _ M _ _ _ _ _ _ hL hB hpq
  have := hL.noeth
  have := hB.noeth
  have := hL.complete
  haveI : Module.Finite R M := Module.Finite.of_restrictScalars_finite Λ R M
  haveI : Module.Flat R B := flat_of_isCplAt hB
  haveI : Module.Flat Λ (B ⊗[R] M) := flat_tensor
  have hloc : (maximalIdeal L).map (algebraMap L B) ≤ maximalIdeal B := by
    rw [← map_eq_max hL, Ideal.map_map, ← IsScalarTower.algebraMap_eq, Ideal.map_le_iff_le_comap,
      IsScalarTower.algebraMap_eq Λ R B, ← Ideal.comap_comap, hB.comap_eq, hpq]
  have hd : ∀ (n : ℕ) (b : B), ∃ a s : R, IsUnit (algebraMap R B s) ∧
      algebraMap R B s * b - algebraMap R B a ∈ maximalIdeal B ^ n := by
    intro n b
    obtain ⟨a, s, hs, hsa⟩ := hB.dense n b
    refine ⟨a, s, ?_, hsa⟩
    by_contra hn
    apply hs
    rw [← hB.comap_eq]
    exact hn
  let φ : M →ₗ[Λ] B ⊗[R] M := (TensorProduct.mk R B M 1).restrictScalars Λ
  haveI : Module.Finite L (B ⊗[R] M) := by
    refine finite_of_dense hloc hd (Submodule.span L (Set.range φ)) ?_ ?_ ?_
    · obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := Λ) (M := M)
      rw [← LinearMap.coe_range, LinearMap.range_eq_map, ← hs, Submodule.map_span,
        Submodule.span_span_of_tower]
      exact Submodule.fg_span (s.finite_toSet.image _)
    · intro r v hv
      induction hv using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨m, rfl⟩ := hx
        refine Submodule.subset_span ⟨r • m, ?_⟩
        rw [algebraMap_smul]
        exact map_smul (TensorProduct.mk R B M 1) r m
      | zero => rw [smul_zero]; exact zero_mem _
      | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
      | smul l x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ _ hx
    · rw [Submodule.span_span_of_tower, eq_top_iff]
      rintro x -
      induction x using TensorProduct.induction_on with
      | zero => exact zero_mem _
      | add x y hx hy => exact add_mem hx hy
      | tmul b m =>
        have : b ⊗ₜ[R] m = b • φ m := by
          change _ = b • ((1 : B) ⊗ₜ[R] m)
          rw [smul_tmul', smul_eq_mul, mul_one]
        rw [this]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, rfl⟩)
  exact ⟨inferInstance, free_of_flat p (map_eq_max hL)⟩
