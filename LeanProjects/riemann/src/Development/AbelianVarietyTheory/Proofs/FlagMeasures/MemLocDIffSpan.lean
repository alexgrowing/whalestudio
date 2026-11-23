import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

noncomputable section

namespace GlobalTheory.Mass.SemiBasis

variable {K : Type} [Field K] [NumberField K]

open NumberField IsDedekindDomain in
private theorem natCast_not_isUnit_lemma_3 {F : Type} [Field F] [NumberField F] {N : ℕ} (hN : 2 ≤ N) :
    ¬ IsUnit (N : 𝓞 F) := by
  intro h
  have h1 : IsUnit (Algebra.norm ℤ (algebraMap ℤ (𝓞 F) (N : ℤ))) := by
    have : algebraMap ℤ (𝓞 F) (N : ℤ) = (N : 𝓞 F) := by simp
    rw [this]; exact h.map _
  rw [Algebra.norm_algebraMap, Int.isUnit_iff] at h1
  have hk : 0 < Module.finrank ℤ (𝓞 F) := Module.finrank_pos
  have h2 : (2 : ℤ) ≤ (N : ℤ) ^ Module.finrank ℤ (𝓞 F) := by
    calc (2 : ℤ) ≤ (N : ℤ) := by exact_mod_cast hN
      _ = (N : ℤ) ^ 1 := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ (by omega) hk
  omega

open NumberField IsDedekindDomain in
private theorem mem_primeTo_ne_zero_lemma_2 {F : Type} [Field F] [NumberField F] {N : ℕ} (hN : 2 ≤ N)
    {x : 𝓞 F} (hx : x ∈ _root_.GlobalTheory.Mass.primeTo (N : 𝓞 F)) : x ≠ 0 := by
  rintro rfl
  obtain ⟨Q, hQ, hle⟩ := Ideal.exists_le_maximal (Ideal.span {(N : 𝓞 F)})
    (by rw [Ne, Ideal.span_singleton_eq_top]; exact natCast_not_isUnit_lemma_3 hN)
  exact hx Q hQ (hle (Ideal.mem_span_singleton_self _)) Q.zero_mem

open NumberField IsDedekindDomain in
private theorem primeTo_le_nonZeroDivisors__lemma {F : Type} [Field F] [NumberField F] {N : ℕ}
    (hN : 2 ≤ N) : _root_.GlobalTheory.Mass.primeTo (N : 𝓞 F) ≤ nonZeroDivisors (𝓞 F) :=
  fun _ hx => mem_nonZeroDivisors_of_ne_zero (mem_primeTo_ne_zero_lemma_2 hN hx)

open NumberField Matrix in
open scoped ENNReal Classical in
variable {K : Type} [Field K] [NumberField K] in
theorem _root_.GlobalTheory.Mass.SemiBasis.primeTo_le {d : ℕ} (hd : 2 ≤ d) :
    _root_.GlobalTheory.Mass.primeTo (d : 𝓞 K) ≤ nonZeroDivisors (𝓞 K) :=
  primeTo_le_nonZeroDivisors__lemma hd

abbrev A (K : Type) [Field K] [NumberField K] {d : ℕ} (hd : 2 ≤ d) : Subalgebra (𝓞 K) K :=
  Localization.subalgebra.ofField K (primeTo (d : 𝓞 K)) (primeTo_le hd)

theorem mem_A {d : ℕ} (hd : 2 ≤ d) (x : K) :
    x ∈ A K hd ↔ ∃ (a s : 𝓞 K) (_ : s ∈ primeTo (d : 𝓞 K)),
      x = algebraMap (𝓞 K) K a * (algebraMap (𝓞 K) K s)⁻¹ :=
  Iff.rfl

theorem alg_ne_zero {d : ℕ} (hd : 2 ≤ d) {s : 𝓞 K}
    (hs : s ∈ primeTo (d : 𝓞 K)) : algebraMap (𝓞 K) K s ≠ 0 :=
  IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (primeTo_le hd hs)

theorem primes_finite {d : ℕ} (hd : 2 ≤ d) : {P : Ideal (A K hd) | P.IsPrime}.Finite := by
  have hd0 : (d : 𝓞 K) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  have hfin : {P : Ideal (𝓞 K) | P.IsMaximal ∧ (d : 𝓞 K) ∈ P}.Finite := by
    have h0 : Ideal.span {(d : 𝓞 K)} ≠ 0 := by
      simpa [Ideal.span_singleton_eq_bot] using hd0
    refine ((Ideal.finite_factors h0).image (fun v => v.asIdeal)).subset ?_
    rintro P ⟨hP, hdP⟩
    have hb : P ≠ ⊥ := by
      rintro rfl
      exact hd0 (by simpa using hdP)
    exact ⟨⟨P, hP.isPrime, hb⟩, Ideal.dvd_span_singleton.2 hdP, rfl⟩
  apply ((hfin.insert ⊥).image (Ideal.map (algebraMap (𝓞 K) (A K hd)))).subset
  intro P hP
  have hP' : P.IsPrime := hP
  obtain ⟨hQ, hdisj⟩ :=
    (IsLocalization.isPrime_iff_isPrime_disjoint (primeTo (d : 𝓞 K)) (A K hd) P).mp hP'
  refine ⟨P.comap (algebraMap (𝓞 K) (A K hd)), ?_,
    IsLocalization.map_under (primeTo (d : 𝓞 K)) (A K hd) P⟩
  set Q := P.comap (algebraMap (𝓞 K) (A K hd))
  have hsub : (Q : Set (𝓞 K)) ⊆ ⋃ i ∈ (hfin.toFinset : Set (Ideal (𝓞 K))), ((id i : Ideal (𝓞 K)) : Set (𝓞 K)) := by
    intro x hx
    by_contra hn
    refine Set.disjoint_left.mp hdisj (?_ : x ∈ primeTo (d : 𝓞 K)) hx
    intro I hI hdI hxI
    apply hn
    simp only [Set.mem_iUnion]
    exact ⟨I, by simpa using ⟨hI, hdI⟩, hxI⟩
  by_cases hb : Q = ⊥
  · exact Or.inl hb
  have hmax : Q.IsMaximal := hQ.isMaximal hb
  obtain ⟨I, hI, hle⟩ := (Ideal.subset_union_prime ⊥ ⊥ (fun i hi _ _ => by
    have : i.IsMaximal ∧ (d : 𝓞 K) ∈ i := by simpa using hi
    exact this.1.isPrime)).1 hsub
  have hI' : I.IsMaximal ∧ (d : 𝓞 K) ∈ I := by simpa using hI
  have : Q = I := hmax.eq_of_le hI'.1.ne_top hle
  right
  rw [this]
  exact hI'

theorem isPID {d : ℕ} (hd : 2 ≤ d) : IsPrincipalIdealRing (A K hd) := by
  have : IsDedekindDomain (A K hd) :=
    IsLocalization.isDedekindDomain (𝓞 K) (primeTo_le hd) (A K hd)
  exact IsPrincipalIdealRing.of_finite_primes (primes_finite hd)

variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem mem_locD_iff_span {d : ℕ} (hd : 2 ≤ d) (M : Submodule (𝓞 K) V) (x : V) :
    x ∈ locD (d : 𝓞 K) M ↔ x ∈ Submodule.span (A K hd) (M : Set V) := by
  constructor
  · rintro ⟨s, hs, hsx⟩
    have hs0 := alg_ne_zero hd hs
    have hu : (algebraMap (𝓞 K) K s)⁻¹ ∈ A K hd := (mem_A hd _).mpr ⟨1, s, hs, by simp⟩
    have hx : x = (⟨_, hu⟩ : A K hd) • (s • x) := by
      rw [Subalgebra.smul_def, ← algebraMap_smul K s x, smul_smul]
      simp [hs0]
    rw [hx]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hsx)
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact ⟨1, one_mem _, by simpa using hy⟩
    | zero => exact Submodule.zero_mem _
    | add y z _ _ hy hz => exact Submodule.add_mem _ hy hz
    | smul a y _ hy =>
      obtain ⟨s, hs, hsy⟩ := hy
      obtain ⟨r, t, ht, hat⟩ := (mem_A hd (a : K)).mp a.2
      refine ⟨t * s, mul_mem ht hs, ?_⟩
      have ht0 := alg_ne_zero hd ht
      have he : (t * s) • (a • y) = r • (s • y) := by
        rw [Subalgebra.smul_def, hat, ← algebraMap_smul K (t * s), ← algebraMap_smul K r,
          ← algebraMap_smul K s, smul_smul, smul_smul]
        congr 1
        rw [map_mul]
        field_simp
      rw [he]
      exact M.smul_mem r hsy

theorem mem_locD_one {d : ℕ} (hd : 2 ≤ d) (x : K) :
    x ∈ locD (d : 𝓞 K) (1 : Submodule (𝓞 K) K) ↔ x ∈ A K hd := by
  constructor
  · rintro ⟨s, hs, hsx⟩
    obtain ⟨r, hr⟩ := Submodule.mem_one.1 hsx
    refine (mem_A hd x).2 ⟨r, s, hs, ?_⟩
    have hs0 := alg_ne_zero hd hs
    rw [hr, Algebra.smul_def]
    field_simp
  · intro hx
    obtain ⟨r, s, hs, rfl⟩ := (mem_A hd x).1 hx
    refine ⟨s, hs, Submodule.mem_one.2 ⟨r, ?_⟩⟩
    have hs0 := alg_ne_zero hd hs
    rw [Algebra.smul_def]
    field_simp

theorem isLattice_span {d : ℕ} (hd : 2 ≤ d) (M : Submodule (𝓞 K) V) (hM : Submodule.IsLattice K M) :
    Submodule.IsLattice K (Submodule.span (A K hd) (M : Set V)) where
  fg := by
    obtain ⟨s, hs⟩ := hM.fg
    refine ⟨s, ?_⟩
    rw [← hs, Submodule.span_span_of_tower]
  span_eq_top := by
    rw [Submodule.span_span_of_tower, hM.span_eq_top]

theorem mem_iff_repr {d : ℕ} (hd : 2 ≤ d) {ι : Type} (L : Submodule (A K hd) V)
    [Submodule.IsLattice K L] (c : Module.Basis ι (A K hd) L) (x : V) :
    x ∈ L ↔ ∀ i, (c.extendOfIsLattice K).repr x i ∈ A K hd := by
  have h : Submodule.span (A K hd) (Set.range (c.extendOfIsLattice K)) = L := by
    have : Set.range (c.extendOfIsLattice K) = L.subtype '' Set.range c := by
      rw [← Set.range_comp]; congr 1; funext i; simp
    rw [this, Submodule.span_image, c.span_eq, Submodule.map_top, Submodule.range_subtype]
  conv_lhs => rw [← h]
  rw [Module.Basis.mem_span_iff_repr_mem]
  refine forall_congr' fun i => ⟨?_, fun h => ⟨⟨_, h⟩, rfl⟩⟩
  rintro ⟨y, hy⟩
  rw [← hy]
  exact y.2

theorem relIndex_of_repr {ι : Type} [Fintype ι] (b : Module.Basis ι K V) (L L' : AddSubgroup V)
    (B' : AddSubgroup K) (B : ι → AddSubgroup K)
    (h' : ∀ x, x ∈ L' ↔ ∀ i, b.repr x i ∈ B') (h : ∀ x, x ∈ L ↔ ∀ i, b.repr x i ∈ B i) :
    L.relIndex L' = ∏ i, (B i).relIndex B' := by
  let f : L' →+ (ι → B') :=
    { toFun := fun x i => ⟨b.repr x i, (h' x).1 x.2 i⟩
      map_zero' := by funext i; ext; simp
      map_add' := fun x y => by funext i; ext; simp }
  have hf : Function.Surjective f := by
    intro y
    refine ⟨⟨b.equivFun.symm fun i => (y i : K), (h' _).2 fun i => ?_⟩, ?_⟩
    · rw [← b.equivFun_apply, LinearEquiv.apply_symm_apply]
      exact (y i).2
    · funext i
      ext
      change b.repr (b.equivFun.symm fun i => (y i : K)) i = _
      rw [← b.equivFun_apply, LinearEquiv.apply_symm_apply]
  have hc : L.addSubgroupOf L' =
      (AddSubgroup.pi Set.univ fun i => (B i).addSubgroupOf B').comap f := by
    ext x
    rw [AddSubgroup.mem_addSubgroupOf, h, AddSubgroup.mem_comap, AddSubgroup.mem_pi]
    exact ⟨fun H i _ => H i, fun H i => H i trivial⟩
  rw [AddSubgroup.relIndex, hc, AddSubgroup.index_comap_of_surjective _ hf, AddSubgroup.index_pi]
  rfl

theorem main : ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (M M' : Submodule (𝓞 K) V) (d : ℕ), 2 ≤ d → Submodule.IsLattice K M → Submodule.IsLattice K M' → M ≤ M' → ∃ (b : Module.Basis (Fin (Module.finrank K V)) K V) (a : Fin (Module.finrank K V) → 𝓞 K), (∀ i, a i ≠ 0) ∧ (∀ x, x ∈ locD (d : 𝓞 K) M' ↔ ∀ i, b.repr x i ∈ locD (d : 𝓞 K) (1 : Submodule (𝓞 K) K)) ∧ (∀ x, x ∈ locD (d : 𝓞 K) M ↔ ∀ i, b.repr x i ∈ scl (a i) (locD (d : 𝓞 K) (1 : Submodule (𝓞 K) K))) ∧ idxN (locD (d : 𝓞 K) M') (locD (d : 𝓞 K) M) = ∏ i, idxN (locD (d : 𝓞 K) (1 : Submodule (𝓞 K) K)) (scl (a i) (locD (d : 𝓞 K) (1 : Submodule (𝓞 K) K))) := by
  intro K V _ _ _ _ _ _ _ M M' d hd hM hM' hle
  have := isPID (K := K) hd
  set N := Submodule.span (A K hd) (M : Set V) with hN
  set N' := Submodule.span (A K hd) (M' : Set V) with hN'
  have lN : Submodule.IsLattice K N := isLattice_span hd M hM
  have lN' : Submodule.IsLattice K N' := isLattice_span hd M' hM'
  have hNle : N ≤ N' := Submodule.span_mono hle
  have r : Module.finrank (A K hd) N = Module.finrank K V := by
    unfold Module.finrank; rw [Submodule.IsLattice.rank' K N]
  have r' : Module.finrank (A K hd) N' = Module.finrank K V := by
    unfold Module.finrank; rw [Submodule.IsLattice.rank' K N']
  have : Module.Free (A K hd) N' := Submodule.IsLattice.free K N'
  let e := Submodule.comapSubtypeEquivOfLe hNle
  obtain ⟨c', α, c, hc⟩ := Submodule.exists_smith_normal_form_of_rank_eq
    (N := N.comap N'.subtype) (Module.finBasisOfFinrankEq (A K hd) N' r')
    (by rw [e.finrank_eq, r, r'])
  choose a s hs has using fun i => (mem_A hd (α i : K)).1 (α i).2
  set b := c'.extendOfIsLattice K with hb
  set b₀ := (c.map e).extendOfIsLattice K with hb₀
  have hbb : ∀ i, b₀ i = (α i : K) • b i := by
    intro i
    have := congrArg Subtype.val (hc i)
    rw [hb₀, hb, Module.Basis.extendOfIsLattice_apply, Module.Basis.extendOfIsLattice_apply]
    exact this
  have hα : ∀ i, (α i : K) ≠ 0 := by
    intro i h0
    apply b₀.ne_zero i
    rw [hbb, h0, zero_smul]
  have ha : ∀ i, a i ≠ 0 := by
    intro i h0
    apply hα i
    rw [has, h0]; simp
  have hrep : ∀ x i, b.repr x i = (α i : K) * b₀.repr x i := by
    intro x i
    conv_lhs => rw [← b₀.sum_repr x]
    simp [hbb, smul_smul, Finsupp.single_apply, mul_comm]
  have h1 : ∀ x, x ∈ locD (d : 𝓞 K) M' ↔
      ∀ i, b.repr x i ∈ locD (d : 𝓞 K) (1 : Submodule (𝓞 K) K) := by
    intro x
    rw [mem_locD_iff_span hd, ← hN', mem_iff_repr hd N' c']
    simp only [mem_locD_one hd, hb]
  have h2 : ∀ x, x ∈ locD (d : 𝓞 K) M ↔
      ∀ i, b.repr x i ∈ scl (a i) (locD (d : 𝓞 K) (1 : Submodule (𝓞 K) K)) := by
    intro x
    rw [mem_locD_iff_span hd, ← hN, mem_iff_repr hd N (c.map e)]
    refine forall_congr' fun i => ?_
    rw [← hb₀, hrep, has]
    have hs0 := alg_ne_zero hd (hs i)
    have ha0 : algebraMap (𝓞 K) K (a i) ≠ 0 := by simpa using ha i
    simp only [scl, Submodule.mem_map, LinearMap.lsmul_apply, mem_locD_one hd, Algebra.smul_def]
    constructor
    · intro h
      refine ⟨(algebraMap (𝓞 K) K (s i))⁻¹ * b₀.repr x i,
        mul_mem ((mem_A hd _).mpr ⟨1, s i, hs i, by simp⟩) h, by ring⟩
    · rintro ⟨y, hy, hy'⟩
      have : b₀.repr x i = algebraMap (𝓞 K) K (s i) * y := by
        field_simp at hy' ⊢
        linear_combination -hy'
      rw [this]
      exact mul_mem (Subalgebra.algebraMap_mem _ _) hy
  exact ⟨b, a, ha, h1, h2, relIndex_of_repr b _ _ _ _ h1 h2⟩

end GlobalTheory.Mass.SemiBasis
