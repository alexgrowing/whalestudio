import Mathlib

open Topology

namespace GlobalTheory

section Constructible

variable {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]

theorem interior_frontier_preimage_of_isConstructible {f : Y → Z} (hf : Continuous f)
    {C : Set Z} (hC : IsConstructible C) : interior (frontier (f ⁻¹' C)) = ∅ := by
  induction hC using IsConstructible.empty_union_induction with
  | open_retrocompact U hU _ =>
    rw [← frontier_compl]
    exact interior_frontier (hU.preimage hf).isClosed_compl
  | union s _ t _ hs ht =>
    rw [Set.preimage_union]
    have h1 : frontier (f ⁻¹' s ∪ f ⁻¹' t) ⊆ frontier (f ⁻¹' s) ∪ frontier (f ⁻¹' t) :=
      (frontier_union_subset _ _).trans
        (Set.union_subset_union Set.inter_subset_left Set.inter_subset_right)
    have h2 : interior (frontier (f ⁻¹' s) ∪ frontier (f ⁻¹' t)) = ∅ := by
      rw [interior_union_isClosed_of_interior_empty isClosed_frontier ht, hs]
    exact Set.eq_empty_of_subset_empty (h2 ▸ interior_mono h1)
  | compl s _ hs => rw [Set.preimage_compl, frontier_compl, hs]

theorem dense_interior_of_interior_frontier_eq_empty {S : Set Y} (hS : Dense S)
    (h : interior (frontier S) = ∅) : Dense (interior S) := by
  have h1 : frontier S = (interior S)ᶜ := by
    rw [frontier, hS.closure_eq, Set.compl_eq_univ_diff]
  rwa [h1, interior_eq_empty_iff_dense_compl, compl_compl] at h

theorem exists_isOpen_inter_closure_subset_of_isConstructible {f : Y → Z} (hf : Continuous f)
    {C : Set Z} (hC : IsConstructible C) :
    ∃ V : Set Y, IsOpen V ∧ V ∩ closure (f ⁻¹' C) ⊆ f ⁻¹' C ∧
      closure (V ∩ closure (f ⁻¹' C)) = closure (f ⁻¹' C) := by
  set S := f ⁻¹' C with hS
  have h1 := interior_frontier_preimage_of_isConstructible
    (hf.comp (continuous_subtype_val (p := fun y => y ∈ closure S))) hC
  rw [Set.preimage_comp, ← hS] at h1
  have hd : Dense ((↑) ⁻¹' S : Set (closure S)) := by
    rw [Subtype.dense_iff]
    refine closure_mono ?_
    intro y hy
    exact ⟨⟨y, subset_closure hy⟩, hy, rfl⟩
  have h2 := dense_interior_of_interior_frontier_eq_empty hd h1
  obtain ⟨V, hV, hVe⟩ := isOpen_induced_iff.1
    (isOpen_interior (s := ((↑) ⁻¹' S : Set (closure S))))
  refine ⟨V, hV, ?_, ?_⟩
  · rintro y ⟨hyV, hyS⟩
    have : (⟨y, hyS⟩ : closure S) ∈ interior ((↑) ⁻¹' S : Set (closure S)) := hVe ▸ hyV
    exact interior_subset (s := ((↑) ⁻¹' S : Set (closure S))) this
  · refine Set.Subset.antisymm (closure_minimal Set.inter_subset_right isClosed_closure) ?_
    rw [Subtype.dense_iff, ← hVe, Subtype.image_preimage_coe, Set.inter_comm] at h2
    exact h2

variable {G : Type*} [Group G] [TopologicalSpace G] [SeparatelyContinuousMul G] [ContinuousInv G]

theorem isClosed_subgroup_of_isOpen_inter_closure_subset (H : Subgroup G) {V : Set G}
    (hV : IsOpen V) (hVH : V ∩ closure (H : Set G) ⊆ H) (hne : (V ∩ closure (H : Set G)).Nonempty) :
    IsClosed (H : Set G) := by
  obtain ⟨u, huV, huK⟩ := hne
  have huH : u ∈ H := hVH ⟨huV, huK⟩
  have hmul : ∀ g ∈ closure (H : Set G), ∀ h ∈ H, g * h ∈ closure (H : Set G) := fun g hg h hh =>
    map_mem_closure (f := fun x => x * h) (continuous_mul_const h) hg fun x hx => H.mul_mem hx hh
  refine isClosed_of_closure_subset fun g hg => ?_
  have hg' : g⁻¹ ∈ closure (H : Set G) :=
    map_mem_closure continuous_inv hg fun x hx => H.inv_mem hx
  obtain ⟨h, hhV, hhH⟩ := mem_closure_iff.1 (hmul _ hg' u huH) ((fun y => g * y) ⁻¹' V)
    (hV.preimage (continuous_const_mul g)) (by simpa using huV)
  have : g * h ∈ H := hVH ⟨hhV, hmul g hg h hhH⟩
  simpa using H.mul_mem this (H.inv_mem hhH)

theorem isClosed_subgroup_of_eq_preimage_isConstructible (H : Subgroup G) {f : G → Z}
    (hf : Continuous f) {C : Set Z} (hC : IsConstructible C) (hH : (H : Set G) = f ⁻¹' C) :
    IsClosed (H : Set G) := by
  obtain ⟨V, hV, h1, h2⟩ := exists_isOpen_inter_closure_subset_of_isConstructible hf hC
  rw [← hH] at h1 h2
  refine isClosed_subgroup_of_isOpen_inter_closure_subset H hV h1 ?_
  rw [← closure_nonempty_iff, h2]
  exact ⟨1, subset_closure H.one_mem⟩

end Constructible

section Characters

variable {X H : Type*} [MulOneClass H]

theorem sum_eq_zero_of_factorsThrough_characters {R : Type*} [CommRing R] [IsDomain R]
    (χ : X → (H →* R)) (f : X →₀ R) (hf : ∀ s : H, f.sum (fun x a => a * χ x s) = 0)
    (c : X → R) (hc : ∀ x y, χ x = χ y → c x = c y) : f.sum (fun x a => a * c x) = 0 := by
  classical
  have h0 : Finsupp.mapDomain χ f = 0 := by
    refine linearIndependent_iff.1 (linearIndependent_monoidHom H R) _ ?_
    rw [Finsupp.linearCombination_mapDomain]
    funext s
    rw [Finsupp.linearCombination_apply, Finsupp.sum_apply', Pi.zero_apply, ← hf s]
    rfl
  have hfac : Function.FactorsThrough c χ := fun x y h => hc x y h
  have h1 : Finsupp.linearCombination R (Function.extend χ c 0) (Finsupp.mapDomain χ f) = 0 := by
    rw [h0, map_zero]
  rw [Finsupp.linearCombination_mapDomain, hfac.extend_comp, Finsupp.linearCombination_apply] at h1
  exact h1

end Characters

section Torus

open AddMonoidAlgebra

variable {R : Type*} [CommRing R] {X : Type*} [AddCommGroup X]

noncomputable def torusEval (t : Multiplicative X →* Rˣ) : AddMonoidAlgebra R X →ₐ[R] R :=
  AddMonoidAlgebra.lift R R X ((Units.coeHom R).comp t)

@[simp] theorem torusEval_single (t : Multiplicative X →* Rˣ) (x : X) (a : R) :
    torusEval t (single x a) = a * t (Multiplicative.ofAdd x) := by
  simp [torusEval]

theorem torusEval_apply (t : Multiplicative X →* Rˣ) (f : AddMonoidAlgebra R X) :
    torusEval t f = f.coeff.sum fun x a => a * t (Multiplicative.ofAdd x) := by
  simp [torusEval, lift_apply]

theorem torusEval_bijective :
    Function.Bijective (torusEval : (Multiplicative X →* Rˣ) → (AddMonoidAlgebra R X →ₐ[R] R)) := by
  constructor
  · intro s t h
    refine MonoidHom.ext fun x => Units.ext ?_
    simpa using congrArg (fun φ : AddMonoidAlgebra R X →ₐ[R] R => φ (single x.toAdd 1)) h
  · intro φ
    refine ⟨((AddMonoidAlgebra.lift R R X).symm φ).toHomUnits, ?_⟩
    rw [torusEval]
    conv_rhs => rw [← (AddMonoidAlgebra.lift R R X).apply_symm_apply φ]
    congr 1

def torusChar (x : X) : (Multiplicative X →* Rˣ) →* R where
  toFun t := t (Multiplicative.ofAdd x)
  map_one' := by simp
  map_mul' s t := by simp

@[simp] theorem torusChar_apply (x : X) (t : Multiplicative X →* Rˣ) :
    torusChar x t = t (Multiplicative.ofAdd x) := rfl

noncomputable def torusTranslate (s : Multiplicative X →* Rˣ) :
    AddMonoidAlgebra R X →ₐ[R] AddMonoidAlgebra R X :=
  AddMonoidAlgebra.lift R _ X
    { toFun x := single x.toAdd (s x : R)
      map_one' := by simp [one_def]
      map_mul' x y := by simp [single_mul_single] }

noncomputable def torusInvert : AddMonoidAlgebra R X →ₐ[R] AddMonoidAlgebra R X :=
  AddMonoidAlgebra.lift R _ X
    { toFun x := single (-x.toAdd) (1 : R)
      map_one' := by simp [one_def]
      map_mul' x y := by simp [single_mul_single, add_comm] }

variable [IsDomain R]

noncomputable def torusPrime (t : Multiplicative X →* Rˣ) : PrimeSpectrum (AddMonoidAlgebra R X) :=
  PrimeSpectrum.comap (torusEval t).toRingHom ⟨⊥, Ideal.isPrime_bot⟩

@[simp] theorem mem_torusPrime (t : Multiplicative X →* Rˣ) (f : AddMonoidAlgebra R X) :
    f ∈ (torusPrime t).asIdeal ↔ torusEval t f = 0 := by
  simp [torusPrime]

variable (R X) in

@[reducible] noncomputable def torusZariski : TopologicalSpace (Multiplicative X →* Rˣ) :=
  TopologicalSpace.induced torusPrime inferInstance

theorem isClosed_torusZariski_iff (H : Set (Multiplicative X →* Rˣ)) :
    IsClosed[torusZariski R X] H ↔
      ∃ S : Set (AddMonoidAlgebra R X), ∀ t, t ∈ H ↔ ∀ f ∈ S, torusEval t f = 0 := by
  rw [isClosed_induced_iff]
  constructor
  · rintro ⟨Z, hZ, rfl⟩
    obtain ⟨S, rfl⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus Z).1 hZ
    exact ⟨S, fun t => by simp [Set.subset_def]⟩
  · rintro ⟨S, hS⟩
    refine ⟨PrimeSpectrum.zeroLocus S, PrimeSpectrum.isClosed_zeroLocus S, ?_⟩
    ext t
    simp [Set.subset_def, hS]

theorem torusEval_eq_zero_of_forall_char (H : Subgroup (Multiplicative X →* Rˣ))
    {f : AddMonoidAlgebra R X} (hf : ∀ s ∈ H, torusEval s f = 0) {t : Multiplicative X →* Rˣ}
    (ht : ∀ x : Multiplicative X, (∀ s ∈ H, s x = 1) → t x = 1) : torusEval t f = 0 := by
  rw [torusEval_apply]
  refine sum_eq_zero_of_factorsThrough_characters
    (fun x => (torusChar x).comp H.subtype) f.coeff (fun s => ?_) _ fun x y hxy => ?_
  · rw [← hf s s.2, torusEval_apply]
    rfl
  · have := ht (Multiplicative.ofAdd x * (Multiplicative.ofAdd y)⁻¹) fun s hs => by
      have h := DFunLike.congr_fun hxy ⟨s, hs⟩
      rw [map_mul, map_inv, mul_inv_eq_one]
      exact Units.ext h
    rw [map_mul, map_inv, mul_inv_eq_one] at this
    rw [this]

theorem mem_of_isClosed_torusZariski {H : Subgroup (Multiplicative X →* Rˣ)}
    (hH : IsClosed[torusZariski R X] (H : Set (Multiplicative X →* Rˣ)))
    {t : Multiplicative X →* Rˣ}
    (ht : ∀ x : Multiplicative X, (∀ s ∈ H, s x = 1) → t x = 1) : t ∈ H := by
  obtain ⟨S, hS⟩ := (isClosed_torusZariski_iff _).1 hH
  exact (hS t).2 fun f hf => torusEval_eq_zero_of_forall_char H (fun s hs => (hS s).1 hs f hf) ht

theorem finite_setOf_pow_eq_one_torus [Module.Finite ℤ X] {m : ℕ} (hm : m ≠ 0) :
    {s : Multiplicative X →* Rˣ | s ^ m = 1}.Finite := by
  haveI : NeZero m := ⟨hm⟩
  haveI : AddGroup.FG X := Module.Finite.iff_addGroup_fg.1 inferInstance
  obtain ⟨T, hT⟩ := (Group.fg_def.1 (inferInstance : Group.FG (Multiplicative X)))
  let φ : {s : Multiplicative X →* Rˣ | s ^ m = 1} → (T → rootsOfUnity m R) := fun s x =>
    ⟨s.1 x, by simpa using DFunLike.congr_fun (show s.1 ^ m = 1 from s.2) x.1⟩
  refine Finite.of_injective φ fun s t h => Subtype.ext ?_
  refine MonoidHom.eq_of_eqOn_dense hT fun x hx => ?_
  exact congrArg Subtype.val (congrFun h ⟨x, hx⟩)

theorem exists_zpow_eq_one_of_isClosed_torusZariski [Module.Finite ℤ X] {n : ℕ} [NeZero n]
    [HasEnoughRootsOfUnity R n] {H : Subgroup (Multiplicative X →* Rˣ)}
    (hH : IsClosed[torusZariski R X] (H : Set (Multiplicative X →* Rˣ)))
    (hn : ∀ s ∈ H, s ^ n = 1 → s = 1) : ∃ r : ℤ, (n : ℤ) ∣ r - 1 ∧ ∀ s ∈ H, s ^ r = 1 := by
  let K : Submodule ℤ X := AddSubgroup.toIntSubmodule
    { carrier := {x | ∀ s ∈ H, s (Multiplicative.ofAdd x) = 1}
      add_mem' := fun {a b} ha hb s hs => by rw [ofAdd_add, map_mul, ha s hs, hb s hs, mul_one]
      zero_mem' := fun s _ => map_one s
      neg_mem' := fun {a} ha s hs => by rw [ofAdd_neg, map_inv, ha s hs, inv_one] }
  have hK : ∀ x, x ∈ K ↔ ∀ s ∈ H, s (Multiplicative.ofAdd x) = 1 := fun x => Iff.rfl
  let N : Submodule ℤ X := K ⊔ Ideal.span {(n : ℤ)} • ⊤
  have hnN : ∀ x : X, (n : ℤ) • x ∈ N := fun x =>
    Submodule.mem_sup_right (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) trivial)
  have hnQ : ∀ q : X ⧸ N, (n : ℤ) • q = 0 := fun q => by
    obtain ⟨x, rfl⟩ := N.mkQ_surjective q
    rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hnN x
  have hnQ' : ∀ q : Multiplicative (X ⧸ N), q ^ n = 1 := fun q => by
    have := hnQ q.toAdd
    rw [natCast_zsmul] at this
    exact congrArg Multiplicative.ofAdd this
  have hN : (⊤ : Submodule ℤ X) ≤ N := by
    intro x _
    by_contra hx
    haveI : Finite (X ⧸ N) := Module.finite_of_fg_torsion _ fun q =>
      ⟨⟨n, mem_nonZeroDivisors_of_ne_zero (Nat.cast_ne_zero.2 (NeZero.ne n))⟩, hnQ q⟩
    haveI : HasEnoughRootsOfUnity R (Monoid.exponent (Multiplicative (X ⧸ N))) :=
      HasEnoughRootsOfUnity.of_dvd R (Monoid.exponent_dvd_of_forall_pow_eq_one hnQ')
    obtain ⟨φ, hφ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity
      (Multiplicative (X ⧸ N)) R (a := Multiplicative.ofAdd (N.mkQ x))
      (by simpa using hx)
    let t : Multiplicative X →* Rˣ := φ.comp (AddMonoidHom.toMultiplicative N.mkQ.toAddMonoidHom)
    have ht : ∀ y, t y = φ (Multiplicative.ofAdd (N.mkQ y.toAdd)) := fun y => rfl
    have htH : t ∈ H := mem_of_isClosed_torusZariski hH fun y hy => by
      have : N.mkQ y.toAdd = 0 := by
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact Submodule.mem_sup_left ((hK _).2 hy)
      rw [ht, this, ofAdd_zero, map_one]
    have ht1 : t = 1 := hn t htH (MonoidHom.ext fun y => by
      rw [MonoidHom.pow_apply, ht, ← map_pow, hnQ', map_one, MonoidHom.one_apply])
    exact hφ (by simpa [ht] using DFunLike.congr_fun ht1 (Multiplicative.ofAdd x))
  obtain ⟨r, hr, hrK⟩ := Submodule.exists_sub_one_mem_and_smul_le_of_fg_of_le_sup
    (I := Ideal.span {(n : ℤ)}) (N := K) (N' := ⊤) (P := ⊤) Module.Finite.fg_top le_rfl hN
  refine ⟨r, Ideal.mem_span_singleton.1 hr, fun s hs => MonoidHom.ext fun y => ?_⟩
  have := (hK _).1 (hrK (Submodule.smul_mem_pointwise_smul y.toAdd r ⊤ trivial)) s hs
  rw [ofAdd_zsmul, map_zpow] at this
  exact this

theorem finite_of_isClosed_torusZariski_of_pow_eq_one [Module.Finite ℤ X] {n : ℕ} (h2 : 2 ≤ n)
    [HasEnoughRootsOfUnity R n] {H : Subgroup (Multiplicative X →* Rˣ)}
    (hH : IsClosed[torusZariski R X] (H : Set (Multiplicative X →* Rˣ)))
    (hn : ∀ s ∈ H, s ^ n = 1 → s = 1) : Finite H ∧ (Nat.card H).Coprime n := by
  haveI : NeZero n := ⟨by omega⟩
  obtain ⟨r, hr, hrH⟩ := exists_zpow_eq_one_of_isClosed_torusZariski hH hn
  have hr0 : r.natAbs ≠ 0 := by
    rw [Int.natAbs_ne_zero]
    rintro rfl
    have := Int.natAbs_dvd_natAbs.2 hr
    simp only [Int.natAbs_natCast, zero_sub, Int.reduceNeg, Int.natAbs_neg, Int.natAbs_one,
      Nat.dvd_one] at this
    omega
  have hfin : Finite H := (finite_setOf_pow_eq_one_torus (R := R) (X := X) hr0).subset
    (t := (H : Set (Multiplicative X →* Rˣ))) fun s hs => pow_natAbs_eq_one.2 (hrH s hs)
  refine ⟨hfin, Nat.coprime_of_dvd fun p hp hpH hpn => ?_⟩
  haveI := Fact.mk hp
  obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' p hpH
  have h1 : s ^ n = 1 := orderOf_dvd_iff_pow_eq_one.1 (hs ▸ hpn)
  have h3 : s = 1 := Subtype.ext (hn s s.2 (congrArg Subtype.val h1))
  rw [h3, orderOf_one] at hs
  exact hp.one_lt.ne hs

variable (R X) in

def torusPowTorsion (n : ℕ) : Subgroup (Multiplicative X →* Rˣ) where
  carrier := {t | ∃ j, t ^ n ^ j = 1}
  one_mem' := ⟨0, one_pow _⟩
  mul_mem' := by
    rintro s t ⟨i, hi⟩ ⟨j, hj⟩
    refine ⟨i + j, ?_⟩
    rw [mul_pow, pow_add, pow_mul, hi, mul_comm (n ^ i), pow_mul, hj, one_pow, one_pow, one_mul]
  inv_mem' := by
    rintro s ⟨i, hi⟩
    exact ⟨i, by rw [inv_pow, hi, inv_one]⟩

end Torus

section Coordinates

open AddMonoidAlgebra

variable {R : Type*} [CommRing R] {X : Type*} [AddCommGroup X] {ι : Type*}

variable (R) in

noncomputable def torusCoord (b : Module.Basis ι ℤ X) : (Multiplicative X →* Rˣ) ≃* (ι → Rˣ) where
  toFun t i := t (Multiplicative.ofAdd (b i))
  invFun u := AddMonoidHom.toMultiplicativeLeft
    (b.constr ℤ fun i => Additive.ofMul (u i)).toAddMonoidHom
  left_inv t := by
    have : (b.constr ℤ fun i => Additive.ofMul (t (Multiplicative.ofAdd (b i)))) =
        (AddMonoidHom.toMultiplicativeLeft.symm t).toIntLinearMap := b.ext fun i => by simp
    beta_reduce
    rw [this]
    rfl
  right_inv u := by
    funext i
    simp
  map_mul' s t := rfl

@[simp] theorem torusCoord_apply (b : Module.Basis ι ℤ X) (t : Multiplicative X →* Rˣ) (i : ι) :
    torusCoord R b t i = t (Multiplicative.ofAdd (b i)) := rfl

theorem torusCoord_symm_apply (b : Module.Basis ι ℤ X) (u : ι → Rˣ) (x : X) :
    (torusCoord R b).symm u (Multiplicative.ofAdd x) = (b.repr x).prod fun i m => u i ^ m := by
  change Additive.toMul ((b.constr ℤ fun i => Additive.ofMul (u i)) x) = _
  rw [Module.Basis.constr_apply, Finsupp.sum, Finsupp.prod, toMul_sum]
  rfl

noncomputable def laurentEval (u : ι → Rˣ) : AddMonoidAlgebra R (ι →₀ ℤ) →ₐ[R] R :=
  torusEval ((torusCoord R Finsupp.basisSingleOne).symm u)

@[simp] theorem laurentEval_single (u : ι → Rˣ) (x : ι →₀ ℤ) (a : R) :
    laurentEval u (single x a) = a * ((x.prod fun i m => u i ^ m : Rˣ) : R) := by
  rw [laurentEval, torusEval_single, torusCoord_symm_apply]
  rfl

end Coordinates

end GlobalTheory
