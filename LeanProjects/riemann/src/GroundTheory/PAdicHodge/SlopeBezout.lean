import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.PAdicHodge

open Module Submodule

section Embedding

variable {R : Type*} [CommRing R] [IsDomain R]
variable {M : Type*} [AddCommGroup M] [Module R M]

theorem exists_injective_linearMap_pi [Module.Finite R M] [IsTorsionFree R M] :
    ∃ (n : ℕ) (f : M →ₗ[R] (Fin n → R)), Function.Injective f := by
  classical
  obtain ⟨k, s, hs⟩ := Module.Finite.exists_fin (R := R) (M := M)
  obtain ⟨I, indepI, hI⟩ := exists_maximal_linearIndepOn R s
  let N := span R (Set.range (fun i : I => s i))
  let b : Basis I R N := Basis.span indepI
  have exists_a : ∀ i : Fin k, ∃ a : R, a ≠ 0 ∧ a • s i ∈ N := by
    intro i
    by_cases hi : i ∈ I
    · exact ⟨1, one_ne_zero, by
        rw [one_smul]; exact subset_span ⟨⟨i, hi⟩, rfl⟩⟩
    · obtain ⟨a, ha, ha'⟩ := hI i hi
      refine ⟨a, ha, ?_⟩
      have : s '' I = Set.range (fun i : I => s i) := Set.image_eq_range s I
      rw [this] at ha'
      exact ha'
  choose a ha ha' using exists_a
  let A : R := ∏ i, a i
  have hA : A ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => ha i)
  have hAM : ∀ x : M, A • x ∈ N := by
    intro x
    have hx : x ∈ span R (Set.range s) := by rw [hs]; trivial
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      have : A • s i = (∏ j ∈ ({i}ᶜ : Finset (Fin k)), a j) • a i • s i := by
        rw [← mul_smul, ← Fintype.prod_eq_prod_compl_mul i]
      rw [this]
      exact N.smul_mem _ (ha' i)
    | zero => simp
    | add y z _ _ hy hz => rw [smul_add]; exact N.add_mem hy hz
    | smul r y _ hy => rw [smul_comm]; exact N.smul_mem r hy
  let φ : M →ₗ[R] N := LinearMap.codRestrict N (A • LinearMap.id) (fun x => by simpa using hAM x)
  have hφ : Function.Injective φ := by
    intro x y hxy
    have : A • x = A • y := by simpa [φ] using congrArg Subtype.val hxy
    exact smul_right_injective M hA this
  have : Finite I := Set.toFinite I
  let b' := b.reindex (Finite.equivFin I)
  exact ⟨Nat.card I, b'.equivFun.toLinearMap.comp φ, b'.equivFun.injective.comp hφ⟩

end Embedding

section Bezout

variable {R : Type*} [CommRing R] [IsDomain R] [IsBezout R]

theorem free_of_fg_ideal (I : Ideal R) (hI : I.FG) : Module.Free R I := by
  obtain ⟨a, ha⟩ := (IsBezout.isPrincipal_of_FG I hI).principal
  by_cases h0 : a = 0
  · subst h0
    have : I = ⊥ := by rw [ha]; simp
    subst this
    infer_instance
  · exact Module.Free.of_equiv
      ((LinearEquiv.toSpanNonzeroSingleton R R a h0).trans (LinearEquiv.ofEq _ _ ha.symm))

theorem free_of_injective_linearMap_pi (n : ℕ) :
    ∀ (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M] (f : M →ₗ[R] (Fin n → R)),
      Function.Injective f → Module.Free R M := by
  induction n with
  | zero =>
    intro M _ _ _ f hf
    have : Subsingleton M := hf.subsingleton
    infer_instance
  | succ n ih =>
    intro M _ _ _ f hf
    let p : M →ₗ[R] R := (LinearMap.proj (Fin.last n)).comp f
    have : Module.Free R (LinearMap.range p) :=
      free_of_fg_ideal _ ((Module.Finite.iff_fg (R := R) (N := LinearMap.range p)).mp inferInstance)
    let g := p.rangeRestrict
    obtain ⟨l, hl⟩ := g.exists_rightInverse_of_surjective (LinearMap.range_rangeRestrict p)
    have hex : Function.Exact (LinearMap.ker g).subtype g := LinearMap.exact_subtype_ker_map g
    let e := ((hex.splitSurjectiveEquiv (LinearMap.ker g).injective_subtype) ⟨l, hl⟩).1
    have : Module.Finite R (LinearMap.ker g) :=
      Module.Finite.of_surjective ((LinearMap.fst R _ _).comp e.toLinearMap)
        (Prod.fst_surjective.comp e.surjective)
    let f' : LinearMap.ker g →ₗ[R] (Fin n → R) :=
      (LinearMap.funLeft R R Fin.castSucc).comp (f.comp (LinearMap.ker g).subtype)
    have hf' : Function.Injective f' := by
      intro x y hxy
      apply Subtype.ext
      apply hf
      funext i
      induction i using Fin.lastCases with
      | last =>
        have hx : g x = 0 := x.2
        have hy : g y = 0 := y.2
        have hx' : p x = 0 := congrArg Subtype.val hx
        have hy' : p y = 0 := congrArg Subtype.val hy
        simp only [p, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_proj,
          Function.eval] at hx' hy'
        rw [hx', hy']
      | cast i => exact congrFun hxy i
    have : Module.Free R (LinearMap.ker g) := ih _ f' hf'
    exact Module.Free.of_equiv e.symm

variable {M : Type*} [AddCommGroup M] [Module R M]

theorem free_of_finite_of_isTorsionFree [Module.Finite R M] [IsTorsionFree R M] :
    Module.Free R M := by
  obtain ⟨n, f, hf⟩ := exists_injective_linearMap_pi (R := R) (M := M)
  exact free_of_injective_linearMap_pi n M f hf

theorem free_of_finite_of_noZeroSMulDivisors [Module.Finite R M] [NoZeroSMulDivisors R M] :
    Module.Free R M :=
  free_of_finite_of_isTorsionFree

theorem free_iff_isTorsionFree [Module.Finite R M] : Module.Free R M ↔ IsTorsionFree R M :=
  ⟨fun _ => inferInstance, fun _ => free_of_finite_of_isTorsionFree⟩

end Bezout

section Compl

variable {R : Type*} [CommRing R]
variable {M P : Type*} [AddCommGroup M] [Module R M] [AddCommGroup P] [Module R P]

theorem isCompl_ker_range_of_comp_eq_id (g : M →ₗ[R] P) (l : P →ₗ[R] M)
    (hl : g ∘ₗ l = LinearMap.id) : IsCompl (LinearMap.ker g) (LinearMap.range l) := by
  have h1 : ∀ y, g (l y) = y := fun y => LinearMap.congr_fun hl y
  constructor
  · rw [Submodule.disjoint_def]
    rintro x hx ⟨y, rfl⟩
    rw [LinearMap.mem_ker, h1] at hx
    simp [hx]
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    rw [Submodule.mem_sup]
    exact ⟨x - l (g x), by simp [h1], l (g x), ⟨_, rfl⟩, by abel⟩

end Compl

section Saturated

variable {R : Type*} [CommRing R] [IsDomain R] [IsBezout R]
variable {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]
variable (N : Submodule R M) [IsTorsionFree R (M ⧸ N)]

theorem free_quotient_of_isTorsionFree : Module.Free R (M ⧸ N) :=
  free_of_finite_of_isTorsionFree

theorem exists_isCompl_of_isTorsionFree_quotient : ∃ N' : Submodule R M, IsCompl N N' := by
  have := free_quotient_of_isTorsionFree N
  obtain ⟨l, hl⟩ := N.mkQ.exists_rightInverse_of_surjective N.range_mkQ
  refine ⟨LinearMap.range l, ?_⟩
  have := isCompl_ker_range_of_comp_eq_id N.mkQ l hl
  rwa [Submodule.ker_mkQ] at this

theorem finite_of_isTorsionFree_quotient : Module.Finite R N := by
  obtain ⟨N', h⟩ := exists_isCompl_of_isTorsionFree_quotient N
  exact Module.Finite.equiv (Submodule.quotientEquivOfIsCompl N' N h.symm)

theorem free_of_isTorsionFree_quotient [IsTorsionFree R M] : Module.Free R N := by
  have := finite_of_isTorsionFree_quotient N
  exact free_of_finite_of_isTorsionFree

end Saturated

section Rank

variable {R : Type*} [CommRing R] [IsDomain R]
variable {M : Type*} [AddCommGroup M] [Module R M]

theorem finrank_add_finrank_quotient [Module.Finite R M] (N : Submodule R M) :
    finrank R N + finrank R (M ⧸ N) = finrank R M := by
  rw [add_comm]
  exact N.finrank_quotient_add_finrank

end Rank

section Saturation

variable {R : Type*} [CommRing R] [IsDomain R]
variable {M : Type*} [AddCommGroup M] [Module R M]

def saturation (N : Submodule R M) : Submodule R M where
  carrier := {x | ∃ r : R, r ≠ 0 ∧ r • x ∈ N}
  add_mem' := by
    rintro x y ⟨r, hr, hx⟩ ⟨s, hs, hy⟩
    refine ⟨r * s, mul_ne_zero hr hs, ?_⟩
    rw [smul_add]
    refine N.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact N.smul_mem s hx
    · rw [mul_smul]; exact N.smul_mem r hy
  zero_mem' := ⟨1, one_ne_zero, by simp⟩
  smul_mem' := by
    rintro c x ⟨r, hr, hx⟩
    exact ⟨r, hr, by rw [smul_comm]; exact N.smul_mem c hx⟩

variable {N N₁ N₂ : Submodule R M}

theorem mem_saturation {x : M} : x ∈ saturation N ↔ ∃ r : R, r ≠ 0 ∧ r • x ∈ N := Iff.rfl

variable (N) in

theorem le_saturation : N ≤ saturation N := fun x hx => ⟨1, one_ne_zero, by simpa using hx⟩

theorem saturation_mono (h : N₁ ≤ N₂) : saturation N₁ ≤ saturation N₂ :=
  fun _ ⟨r, hr, hx⟩ => ⟨r, hr, h hx⟩

variable (N) in

@[simp]
theorem saturation_saturation : saturation (saturation N) = saturation N := by
  refine le_antisymm ?_ (le_saturation _)
  rintro x ⟨r, hr, s, hs, hx⟩
  exact ⟨s * r, mul_ne_zero hs hr, by rw [mul_smul]; exact hx⟩

variable (N) in

instance isTorsionFree_quotient_saturation : IsTorsionFree R (M ⧸ saturation N) where
  isSMulRegular r hr := by
    intro a b hab
    obtain ⟨x, rfl⟩ := (saturation N).mkQ_surjective a
    obtain ⟨y, rfl⟩ := (saturation N).mkQ_surjective b
    simp only [Submodule.mkQ_apply, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq] at hab ⊢
    obtain ⟨s, hs, h⟩ := hab
    exact ⟨s * r, mul_ne_zero hs hr.ne_zero, by rw [mul_smul, smul_sub r x y]; exact h⟩

theorem saturation_eq_self_iff : saturation N = N ↔ IsTorsionFree R (M ⧸ N) := by
  constructor
  · intro h
    rw [← h]
    infer_instance
  · intro _
    refine le_antisymm ?_ (le_saturation N)
    rintro x ⟨r, hr, hx⟩
    have h1 : r • (N.mkQ x) = r • 0 := by
      rw [smul_zero, ← LinearMap.map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hx
    have h2 : N.mkQ x = 0 := smul_right_injective (M ⧸ N) hr h1
    rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h2

theorem saturation_eq_self [IsTorsionFree R (M ⧸ N)] : saturation N = N :=
  saturation_eq_self_iff.mpr inferInstance

variable (N) in

theorem rank_saturation : Module.rank R (saturation N) = Module.rank R N := by
  let N₀ : Submodule R (saturation N) := N.comap (saturation N).subtype
  have h0 : Module.rank R (saturation N ⧸ N₀) = 0 := by
    rw [rank_eq_zero_iff]
    intro q
    obtain ⟨x, rfl⟩ := N₀.mkQ_surjective q
    obtain ⟨r, hr, hx⟩ := x.2
    refine ⟨r, hr, ?_⟩
    rw [← LinearMap.map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hx
  have h := HasRankNullity.rank_quotient_add_rank N₀
  rw [h0, zero_add] at h
  rw [← h]
  exact (Submodule.comapSubtypeEquivOfLe (le_saturation N)).rank_eq

variable (N) in

theorem finrank_saturation : finrank R (saturation N) = finrank R N := by
  simp only [Module.finrank, rank_saturation N]

theorem eq_of_le_of_finrank_eq [Module.Finite R M] [IsTorsionFree R (M ⧸ N)] {N' : Submodule R M}
    (hle : N ≤ N') (hrank : finrank R N = finrank R N') : N = N' := by
  have hfin : ∀ P : Submodule R M, Module.rank R P < Cardinal.aleph0 :=
    fun P => lt_of_le_of_lt P.rank_le (Module.rank_lt_aleph0 (R := R) (M := M))
  let N₀ : Submodule R N' := N.comap N'.subtype
  have h := HasRankNullity.rank_quotient_add_rank N₀
  rw [(Submodule.comapSubtypeEquivOfLe hle).rank_eq] at h
  have heq : Module.rank R N = Module.rank R N' :=
    Cardinal.toNat_injOn (hfin N) (hfin N') hrank
  obtain ⟨m, hm⟩ := Cardinal.lt_aleph0.1 (hfin N)
  rw [← heq, hm] at h
  have hq : Module.rank R (N' ⧸ N₀) < Cardinal.aleph0 :=
    lt_of_le_of_lt (le_self_add.trans_eq h) Cardinal.natCast_lt_aleph0
  obtain ⟨j, hj⟩ := Cardinal.lt_aleph0.1 hq
  rw [hj] at h
  have hj0 : j = 0 := by
    have : ((j + m : ℕ) : Cardinal) = m := by push_cast; exact h
    have := Nat.cast_injective this
    omega
  have hzero : Module.rank R (N' ⧸ N₀) = 0 := by rw [hj, hj0, Nat.cast_zero]
  rw [rank_eq_zero_iff] at hzero
  refine le_antisymm hle ?_
  intro x hx
  obtain ⟨r, hr, hrx⟩ := hzero (N₀.mkQ ⟨x, hx⟩)
  rw [← LinearMap.map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hrx
  rw [← saturation_eq_self (N := N)]
  exact ⟨r, hr, hrx⟩

end Saturation

end GroundTheory.PAdicHodge
