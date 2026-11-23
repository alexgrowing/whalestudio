import Mathlib
import GroundTheory.ProfiniteCohomology.CohomologyFunctoriality.QuotientToInvariantsFunctorPreservesZeroMorphism
import GroundTheory.ProfiniteCohomology.ContinuousCochains.LongExactSequence
import GroundTheory.ProfiniteCohomology.GaloisModules.CoeGalRootsOfUnityHomApply
import GroundTheory.ProfiniteCohomology.Colimit
import GroundTheory.ProfiniteCohomology.TorsionDualDefs
import GroundTheory.ProfiniteCohomology.GaloisCohomology.Kummer
import GroundTheory.ProfiniteCohomology.CupProducts
import GroundTheory.ProfiniteCohomology.CohomologicalDimension.SubsingletonCohomologyOfPrimaryOfFinite
import GroundTheory.ProfiniteCohomology.Procyclic
import GroundTheory.ProfiniteCohomology.FilteredHomology
import GroundTheory.ProfiniteCohomology.CupProducts.Cocycles
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory Limits

noncomputable section

section Triv

variable (G : Type) [Group G] (A : Type) [AddCommGroup A]

abbrev trivRep : Rep.{0} (ULift.{0} ℤ) G := Rep.of (intRep.{0} (1 : G →* AddMonoid.End A))

theorem trivRep_ρ_apply (g : G) (a : A) : (trivRep G A).ρ g a = a := rfl

instance isDiscreteRep_trivRep [TopologicalSpace G] [IsTopologicalGroup G] :
    IsDiscreteRep (trivRep G A) :=
  ⟨fun a => by
    have : stabilizer (trivRep G A).ρ a = ⊤ := by
      ext g
      simp only [mem_stabilizer, Subgroup.mem_top, iff_true]
      rfl
    rw [this]
    exact isOpen_univ⟩

end Triv

section DivFun

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {I : Type} {H : I → Type} [∀ i, Group (H i)] (φ : ∀ i, H i →* G) (A : Type) [AddCommGroup A]

def divFun : AddSubgroup (I → G → A) where
  carrier := {f | {i | f i ≠ 0}.Finite ∧
    ∀ i, IsLocallyConstant (f i) ∧ ∀ (h : H i) (x : G), f i (φ i h * x) = f i x}
  add_mem' {f g} hf hg := by
    refine ⟨(hf.1.union hg.1).subset fun i hi => ?_, fun i => ⟨(hf.2 i).1.add (hg.2 i).1, fun h x => ?_⟩⟩
    · by_contra hc
      simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hc
      exact hi (by rw [Pi.add_apply, hc.1, hc.2, add_zero])
    · simp only [Pi.add_apply, (hf.2 i).2, (hg.2 i).2]
  zero_mem' := ⟨by simp, fun i => ⟨IsLocallyConstant.const 0, fun _ _ => rfl⟩⟩
  neg_mem' {f} hf := by
    refine ⟨hf.1.subset fun i hi => ?_, fun i => ⟨(hf.2 i).1.neg, fun h x => ?_⟩⟩
    · simp only [Set.mem_ofPred_eq, Pi.neg_apply, ne_eq, neg_eq_zero] at hi ⊢
      exact hi
    · simp only [Pi.neg_apply, (hf.2 i).2]

omit [IsTopologicalGroup G] in
theorem mem_divFun {f : I → G → A} : f ∈ divFun φ A ↔ {i | f i ≠ 0}.Finite ∧
    ∀ i, IsLocallyConstant (f i) ∧ ∀ (h : H i) (x : G), f i (φ i h * x) = f i x :=
  Iff.rfl

def divFunAction : G →* AddMonoid.End (divFun φ A) where
  toFun g :=
    { toFun := fun f => ⟨fun i x => (f : I → G → A) i (x * g), by
        refine ⟨f.2.1.subset fun i hi => ?_, fun i => ⟨(f.2.2 i).1.comp_continuous
          (continuous_mul_const g), fun h x => ?_⟩⟩
        · intro hc
          apply hi
          show (fun x => (f : I → G → A) i (x * g)) = 0
          funext x
          rw [hc]
          rfl
        · simp only [mul_assoc, (f.2.2 i).2]⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  map_one' := by
    ext f i x
    simp only [mul_one]
    rfl
  map_mul' g₁ g₂ := by
    ext f i x
    show (f : I → G → A) i (x * (g₁ * g₂)) = (f : I → G → A) i (x * g₁ * g₂)
    rw [mul_assoc]

theorem coe_divFunAction_apply (g : G) (f : divFun φ A) (i : I) (x : G) :
    ((divFunAction φ A g f : divFun φ A) : I → G → A) i x = (f : I → G → A) i (x * g) :=
  rfl

omit [IsTopologicalGroup G] in

theorem exists_mem_nhds_one_forall_mul_eq {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] {X : Type*} {f : G → X} (hf : IsLocallyConstant f) :
    ∃ V ∈ nhds (1 : G), ∀ x : G, ∀ v ∈ V, f (x * v) = f x := by
  have hN : ∀ x : G, {w | f (x * w) = f x} ∈ nhds (1 : G) := fun x =>
    ((hf.isOpen_fiber (f x)).preimage (continuous_const_mul x)).mem_nhds (by simp)
  choose W hWo hW1 hWW using fun x => exists_open_nhds_one_split (hN x)
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => (fun y => x⁻¹ * y) ⁻¹' W x)
    (fun x => (hWo x).preimage (continuous_const_mul x⁻¹))
    (fun y _ => Set.mem_iUnion.2 ⟨y, by simpa using hW1 y⟩)
  refine ⟨⋂ x ∈ t, W x, (Filter.biInter_finset_mem t).2 fun x _ => (hWo x).mem_nhds (hW1 x), ?_⟩
  intro y v hv
  obtain ⟨x, hxt, hyx⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ y))
  have hv' : v ∈ W x := Set.mem_iInter₂.1 hv x hxt
  have h1 : f (x * (x⁻¹ * y * v)) = f x := hWW x _ hyx _ hv'
  have h2 : f (x * (x⁻¹ * y * 1)) = f x := hWW x _ hyx _ (hW1 x)
  rw [mul_one, mul_inv_cancel_left] at h2
  rw [mul_assoc x⁻¹, mul_inv_cancel_left] at h1
  rw [h1, h2]

abbrev divFunRep : Rep.{0} (ULift.{0} ℤ) G := Rep.of (intRep.{0} (divFunAction φ A))

instance isDiscreteRep_divFunRep [CompactSpace G] : IsDiscreteRep (divFunRep φ A) := by
  refine ⟨fun f => ?_⟩
  have hfin := f.2.1
  choose V hV hVf using fun i => exists_mem_nhds_one_forall_mul_eq ((f.2.2 i).1)
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
  refine Filter.mem_of_superset ((Filter.biInter_mem hfin).2 fun i _ => hV i) ?_
  intro g hg
  rw [SetLike.mem_coe, mem_stabilizer]
  apply Subtype.ext
  funext i x
  show (f : I → G → A) i (x * g) = (f : I → G → A) i x
  by_cases hi : i ∈ {i | (f : I → G → A) i ≠ 0}
  · exact hVf i x g (Set.mem_iInter₂.1 hg i hi)
  · simp only [Set.mem_ofPred_eq, ne_eq, not_not] at hi
    rw [hi]
    rfl

def divFunEval (i : I) : Rep.res (φ i) (divFunRep φ A) ⟶ trivRep (H i) A :=
  Rep.ofHom ⟨uliftIntLinearMap
    { toFun := fun f : divFun φ A => (f : I → G → A) i 1
      map_zero' := rfl
      map_add' := fun _ _ => rfl },
    fun h => LinearMap.ext fun f => by
      show (f : I → G → A) i (1 * φ i h) = (f : I → G → A) i 1
      rw [one_mul, ← mul_one (φ i h), (f.2.2 i).2]⟩

theorem divFunEval_hom_apply (i : I) (f : divFun φ A) :
    (divFunEval φ A i).hom f = (f : I → G → A) i 1 := rfl

def divFunMap {B : Type} [AddCommGroup B] (g : A →+ B) : divFunRep φ A ⟶ divFunRep φ B :=
  Rep.ofHom ⟨uliftIntLinearMap
    { toFun := fun f : divFun φ A => ⟨fun i x => g ((f : I → G → A) i x), by
        refine ⟨f.2.1.subset fun i hi => ?_, fun i => ⟨(f.2.2 i).1.comp g, fun h x => ?_⟩⟩
        · intro hc
          apply hi
          show (fun x => g ((f : I → G → A) i x)) = 0
          funext x
          rw [hc, Pi.zero_apply, Pi.zero_apply, map_zero]
        · show g ((f : I → G → A) i (φ i h * x)) = g ((f : I → G → A) i x)
          rw [(f.2.2 i).2]⟩
      map_zero' := Subtype.ext (funext fun _ => funext fun _ => map_zero g)
      map_add' := fun f₁ f₂ => Subtype.ext (funext fun _ => funext fun _ => map_add g _ _) },
    fun _ => LinearMap.ext fun _ => rfl⟩

theorem coe_divFunMap_hom_apply {B : Type} [AddCommGroup B] (g : A →+ B) (f : divFun φ A) :
    (((divFunMap φ A g).hom f : divFun φ B) : I → G → B) = fun i x => g ((f : I → G → A) i x) := rfl

abbrev ratToQZ : ℚ →+ QZ := QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℚ))

theorem ratToQZ_eq_zero_iff (q : ℚ) : ratToQZ q = 0 ↔ ∃ n : ℤ, (n : ℚ) = q := by
  have : ratToQZ q = 0 ↔ q ∈ AddSubgroup.zmultiples (1 : ℚ) := QuotientAddGroup.eq_zero_iff q
  rw [this, AddSubgroup.mem_zmultiples_iff]
  simp

theorem ratToQZ_surjective : Function.Surjective ratToQZ := QuotientAddGroup.mk'_surjective _

def divFunSequence : ShortComplex (Rep.{0} (ULift.{0} ℤ) G) :=
  ShortComplex.mk (divFunMap φ ℤ (Int.castAddHom ℚ)) (divFunMap φ ℚ ratToQZ) (by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    funext i x
    exact (ratToQZ_eq_zero_iff _).2 ⟨((f : divFun φ ℤ) : I → G → ℤ) i x, rfl⟩)

instance isDiscreteRep_divFunSequence_X₁ [CompactSpace G] : IsDiscreteRep (divFunSequence φ).X₁ :=
  inferInstanceAs (IsDiscreteRep (divFunRep φ ℤ))

instance isDiscreteRep_divFunSequence_X₂ [CompactSpace G] : IsDiscreteRep (divFunSequence φ).X₂ :=
  inferInstanceAs (IsDiscreteRep (divFunRep φ ℚ))

instance isDiscreteRep_divFunSequence_X₃ [CompactSpace G] : IsDiscreteRep (divFunSequence φ).X₃ :=
  inferInstanceAs (IsDiscreteRep (divFunRep φ QZ))

theorem divFunSequence_shortExact : (divFunSequence φ).ShortExact where
  exact := by
    apply shortComplex_exact_of_forall_exists
    intro f₀ hf
    let f : divFun φ ℚ := f₀
    have hint : ∀ i x, ((⌊(f : I → G → ℚ) i x⌋ : ℤ) : ℚ) = (f : I → G → ℚ) i x := fun i x => by
      have := congrArg (fun f : divFun φ QZ => (f : I → G → QZ) i x) (show
        (divFunMap φ ℚ ratToQZ).hom f = 0 from hf)
      obtain ⟨n, hn⟩ := (ratToQZ_eq_zero_iff _).1 this
      rw [← hn, Int.floor_intCast]
    refine ⟨⟨fun i x => ⌊(f : I → G → ℚ) i x⌋, ?_, fun i => ⟨(f.2.2 i).1.comp Int.floor, fun h x => ?_⟩⟩, ?_⟩
    · refine f.2.1.subset fun i hi => ?_
      intro hc
      apply hi
      funext x
      show ⌊(f : I → G → ℚ) i x⌋ = 0
      rw [hc]
      simp
    · show ⌊(f : I → G → ℚ) i (φ i h * x)⌋ = ⌊(f : I → G → ℚ) i x⌋
      rw [(f.2.2 i).2]
    · apply Subtype.ext
      funext i x
      exact hint i x
  mono_f := (Rep.mono_iff_injective _).2 fun f₁ f₂ h => by
    apply Subtype.ext
    funext i x
    have := congrArg (fun f : divFun φ ℚ => (f : I → G → ℚ) i x) h
    exact Int.cast_injective this
  epi_g := (Rep.epi_iff_surjective _).2 fun f₀ => by
    classical
    let f : divFun φ QZ := f₀
    let sec : QZ → ℚ := fun q => if q = 0 then 0 else Function.surjInv ratToQZ_surjective q
    have hsec : ∀ q, ratToQZ (sec q) = q := fun q => by
      by_cases hq : q = 0
      · simp [sec, hq]
      · simp only [sec, hq, if_false]
        exact Function.surjInv_eq ratToQZ_surjective q
    refine ⟨⟨fun i x => sec ((f : I → G → QZ) i x), ?_, fun i => ⟨(f.2.2 i).1.comp sec, fun h x => ?_⟩⟩, ?_⟩
    · refine f.2.1.subset fun i hi => ?_
      intro hc
      apply hi
      funext x
      show sec ((f : I → G → QZ) i x) = 0
      rw [hc]
      simp [sec]
    · show sec ((f : I → G → QZ) i (φ i h * x)) = sec ((f : I → G → QZ) i x)
      rw [(f.2.2 i).2]
    · apply Subtype.ext
      funext i x
      exact hsec _

end DivFun

section Cohomology

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]

theorem isZero_cohomology_of_bijective_nsmul_ulift (M : Rep.{0} (ULift.{0} ℤ) G) [IsDiscreteRep M]
    (hM : ∀ n : ℕ, n ≠ 0 → Function.Bijective (fun m : M.V => n • m)) {n : ℕ} (hn : 1 ≤ n) :
    IsZero (cohomology M n) := by
  refine @ModuleCat.isZero_of_subsingleton _ _ _ ⟨fun x y => ?_⟩
  suffices h : ∀ x : cohomology M n, x = 0 by rw [h x, h y]
  intro x
  obtain ⟨m, hm, hx⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.1 (isTorsion_cohomology M hn x)
  have hiso : IsIso (m • 𝟙 M) := by
    let : Module (ULift.{0} ℤ) M.V := M.hV2
    have hb : Function.Bijective (m • 𝟙 M).hom := by
      have : ⇑(m • 𝟙 M).hom = fun a : M.V => m • a := funext fun a => nsmul_id_hom_apply M m a
      rw [this]
      exact hM m hm.ne'
    have he : (Rep.mkIso ((m • 𝟙 M).hom.ofBijective hb)).hom = m • 𝟙 M := Rep.hom_ext rfl
    rw [← he]
    infer_instance
  have hinj : Function.Injective (cohomologyMap (m • 𝟙 M) n).hom := by
    have hH : IsIso (cohomologyMap (m • 𝟙 M) n) :=
      ⟨cohomologyMap (inv (m • 𝟙 M)) n, by rw [← cohomologyMap_comp, IsIso.hom_inv_id,
        cohomologyMap_id], by rw [← cohomologyMap_comp, IsIso.inv_hom_id, cohomologyMap_id]⟩
    exact (ModuleCat.mono_iff_injective _).1 inferInstance
  apply hinj
  rw [map_zero, cohomologyMap_nsmul_id_apply]
  exact hx

omit [TotallyDisconnectedSpace G] in

theorem exists_coprime_smul_cohomology_eq_zero (M : Rep.{0} (ULift.{0} ℤ) G) [IsDiscreteRep M]
    (ℓ : ℕ) (hM : ∀ m : M.V, ∃ N : ℕ, N.Coprime ℓ ∧ N • m = 0) (n : ℕ) (x : cohomology M n) :
    ∃ N : ℕ, N.Coprime ℓ ∧ N • x = 0 := by
  classical
  obtain ⟨z, rfl⟩ := cohomologyπ_surjective M n x
  set c := cochainOf M (cocycleι M n z) with hc
  have hlc : IsLocallyConstant c := (cocycleι M n z : locallyConstantCochains M n).2
  have hfin : (Set.range c).Finite := hlc.range_finite
  choose N hNc hNm using hM
  refine ⟨∏ m ∈ hfin.toFinset, N m, Nat.Coprime.prod_left fun m _ => hNc m, ?_⟩
  have hz : (∏ m ∈ hfin.toFinset, N m) • z = 0 := by
    apply cocycleι_injective
    apply cochainOf_injective
    rw [map_nsmul, map_zero, cochainOf_zero]
    funext g
    have hmem : c g ∈ hfin.toFinset := hfin.mem_toFinset.2 ⟨g, rfl⟩
    change (∏ m ∈ hfin.toFinset, N m) • c g = 0
    obtain ⟨d, hd⟩ := Finset.dvd_prod_of_mem N hmem
    rw [hd, mul_comm, ← smul_smul, hNm, smul_zero]
  rw [← map_nsmul, hz, map_zero]

omit [TotallyDisconnectedSpace G] in

theorem eq_zero_of_pow_smul_eq_zero_of_coprime (M : Rep.{0} (ULift.{0} ℤ) G) [IsDiscreteRep M] (ℓ : ℕ)
    (hM : ∀ m : M.V, ∃ N : ℕ, N.Coprime ℓ ∧ N • m = 0) (n : ℕ) (x : cohomology M n) (k : ℕ)
    (hx : ℓ ^ k • x = 0) : x = 0 := by
  obtain ⟨N, hN, hNx⟩ := exists_coprime_smul_cohomology_eq_zero M ℓ hM n x
  have h1 : addOrderOf x ∣ N := addOrderOf_dvd_of_nsmul_eq_zero hNx
  have h2 : addOrderOf x ∣ ℓ ^ k := addOrderOf_dvd_of_nsmul_eq_zero hx
  have h3 : addOrderOf x = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 (hN.pow_right k)) h2
  exact AddMonoid.addOrderOf_eq_one_iff.1 h3

variable {I : Type} {H : I → Type} [∀ i, Group (H i)] [∀ i, TopologicalSpace (H i)]
  [∀ i, IsTopologicalGroup (H i)] [∀ i, CompactSpace (H i)] [∀ i, TotallyDisconnectedSpace (H i)]
  (φ : ∀ i, H i →* G) (hφ : ∀ i, Continuous (φ i))

omit [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] [∀ i, TopologicalSpace (H i)]
  [∀ i, IsTopologicalGroup (H i)] [∀ i, CompactSpace (H i)] [∀ i, TotallyDisconnectedSpace (H i)] in

theorem bijective_nsmul_divFun_rat {n : ℕ} (hn : n ≠ 0) :
    Function.Bijective (fun f : divFun φ ℚ => n • f) := by
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn
  constructor
  · intro f g h
    apply Subtype.ext
    funext i x
    have := congrArg (fun f : divFun φ ℚ => (f : I → G → ℚ) i x) h
    simp only [AddSubgroup.coe_nsmul, Pi.smul_apply, nsmul_eq_mul] at this
    exact mul_left_cancel₀ hn' this
  · intro f
    refine ⟨⟨fun i x => (f : I → G → ℚ) i x / n, f.2.1.subset fun i hi => ?_,
      fun i => ⟨(f.2.2 i).1.comp (· / (n : ℚ)), fun h x => ?_⟩⟩, ?_⟩
    · intro hc
      apply hi
      funext x
      show (f : I → G → ℚ) i x / n = 0
      rw [hc]
      simp
    · show (f : I → G → ℚ) i (φ i h * x) / n = (f : I → G → ℚ) i x / n
      rw [(f.2.2 i).2]
    · apply Subtype.ext
      funext i x
      simp only [AddSubgroup.coe_nsmul, Pi.smul_apply, nsmul_eq_mul]
      field_simp

omit [∀ i, TopologicalSpace (H i)] [∀ i, IsTopologicalGroup (H i)] [∀ i, CompactSpace (H i)]
  [∀ i, TotallyDisconnectedSpace (H i)] in

theorem isZero_cohomology_one_divFunRep_int : IsZero (cohomology (divFunRep φ ℤ) 1) := by
  have hS := divFunSequence_shortExact φ
  have h1 : Subsingleton (cohomology (divFunSequence φ).X₂ 1) :=
    ModuleCat.subsingleton_of_isZero (isZero_cohomology_of_bijective_nsmul_ulift
      (divFunSequence φ).X₂ (fun n hn => bijective_nsmul_divFun_rat φ hn) le_rfl)
  refine @ModuleCat.isZero_of_subsingleton _ _ _ ⟨fun x y => ?_⟩
  suffices h : ∀ x : cohomology (divFunSequence φ).X₁ 1, x = 0 from (h x).trans (h y).symm
  intro x
  obtain ⟨v, rfl⟩ := exists_δ_H0Iso_inv_eq hS h1 x
  rw [δ_H0Iso_inv_eq_zero_iff]

  classical
  let a : divFun φ QZ := v.1
  have hconst : ∀ i x, (a : I → G → QZ) i x = (a : I → G → QZ) i 1 := fun i x => by
    have := congrArg (fun f : divFun φ QZ => (f : I → G → QZ) i 1) (v.2 x)
    change (a : I → G → QZ) i (1 * x) = (a : I → G → QZ) i 1 at this
    rwa [one_mul] at this
  let sec : QZ → ℚ := fun q => if q = 0 then 0 else Function.surjInv ratToQZ_surjective q
  have hsec : ∀ q, ratToQZ (sec q) = q := fun q => by
    by_cases hq : q = 0
    · simp [sec, hq]
    · simp only [sec, hq, if_false]
      exact Function.surjInv_eq ratToQZ_surjective q
  let b : divFun φ ℚ := ⟨fun i _ => sec ((a : I → G → QZ) i 1), a.2.1.subset fun i hi => ?_,
    fun i => ⟨IsLocallyConstant.const _, fun _ _ => rfl⟩⟩
  · refine ⟨⟨b, fun g => rfl⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    funext i x
    show ratToQZ (sec ((a : I → G → QZ) i 1)) = (a : I → G → QZ) i x
    rw [hsec]
    exact (hconst i x).symm
  · intro hc
    apply hi
    funext x
    show sec ((a : I → G → QZ) i 1) = 0
    rw [hc]
    simp [sec]

omit [CompactSpace G] [TotallyDisconnectedSpace G] in
theorem bijective_nsmul_rat {n : ℕ} (hn : n ≠ 0) : Function.Bijective (fun q : ℚ => n • q) := by
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn
  refine ⟨fun a b hab => ?_, fun a => ⟨a / n, ?_⟩⟩
  · simp only [nsmul_eq_mul] at hab
    exact mul_left_cancel₀ hn' hab
  · simp only [nsmul_eq_mul]
    field_simp

section TrivSeq

variable (Γ : Type) [Group Γ]

omit [CompactSpace G] [TotallyDisconnectedSpace G] in

def trivMap {A B : Type} [AddCommGroup A] [AddCommGroup B] (g : A →+ B) :
    trivRep Γ A ⟶ trivRep Γ B :=
  Rep.ofHom ⟨uliftIntLinearMap g, fun _ => LinearMap.ext fun _ => rfl⟩

def trivSequence : ShortComplex (Rep.{0} (ULift.{0} ℤ) Γ) :=
  ShortComplex.mk (trivMap Γ (Int.castAddHom ℚ)) (trivMap Γ ratToQZ) (by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro n
    exact (ratToQZ_eq_zero_iff _).2 ⟨(n : ℤ), rfl⟩)

theorem trivSequence_shortExact : (trivSequence Γ).ShortExact where
  exact := by
    apply shortComplex_exact_of_forall_exists
    intro q hq
    obtain ⟨n, hn⟩ := (ratToQZ_eq_zero_iff _).1 hq
    exact ⟨n, hn⟩
  mono_f := (Rep.mono_iff_injective _).2 fun a b h => Int.cast_injective (α := ℚ) h
  epi_g := (Rep.epi_iff_surjective _).2 ratToQZ_surjective

variable [TopologicalSpace Γ] [IsTopologicalGroup Γ]

instance isDiscreteRep_trivSequence_X₁ : IsDiscreteRep (trivSequence Γ).X₁ :=
  inferInstanceAs (IsDiscreteRep (trivRep Γ ℤ))

instance isDiscreteRep_trivSequence_X₂ : IsDiscreteRep (trivSequence Γ).X₂ :=
  inferInstanceAs (IsDiscreteRep (trivRep Γ ℚ))

instance isDiscreteRep_trivSequence_X₃ : IsDiscreteRep (trivSequence Γ).X₃ :=
  inferInstanceAs (IsDiscreteRep (trivRep Γ QZ))

end TrivSeq

def divFunEvalSequence (i : I) :
    (divFunSequence φ).map (Rep.resFunctor (φ i)) ⟶ trivSequence (H i) where
  τ₁ := divFunEval φ ℤ i
  τ₂ := divFunEval φ ℚ i
  τ₃ := divFunEval φ QZ i
  comm₁₂ := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro f
    rfl
  comm₂₃ := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro f
    rfl

theorem eq_zero_of_divFunEval_eq_zero (x : cohomology (divFunRep φ ℤ) 2)
    (hx : ∀ i, (cohomologyMapAlong (φ i) (hφ i) (divFunEval φ ℤ i) 2).hom x = 0) : x = 0 := by
  have hS := divFunSequence_shortExact φ
  have h2 : IsZero (cohomology (divFunSequence φ).X₂ 2) :=
    isZero_cohomology_of_bijective_nsmul_ulift (divFunSequence φ).X₂
      (fun n hn => bijective_nsmul_divFun_rat φ hn) (by norm_num)
  obtain ⟨y, rfl⟩ := (ShortComplex.moduleCat_exact_iff _).1 (cohomology_exact₁ hS 1 2 rfl) x
    ((ModuleCat.subsingleton_of_isZero h2).elim _ _)
  suffices hy : y = 0 by
    change (δ hS 1 2 rfl).hom y = 0
    rw [hy, map_zero]
  obtain ⟨z, rfl⟩ := cohomologyπ_surjective _ 1 y
  set c : (Fin 1 → G) → divFun φ QZ := cocycleFun (divFunSequence φ).X₃ z with hc

  have hloc : ∀ (i : I) (h : H i), ((c fun _ => φ i h : divFun φ QZ) : I → G → QZ) i 1 = 0 := by
    intro i h
    have hT := trivSequence_shortExact (H i)
    have e := congrArg (fun ψ => ψ.hom ((cohomologyπ _ 1) z))
      (δ_comp_cohomologyMapAlong (φ i) (hφ i) (divFunEvalSequence φ i) hS hT 1 2 rfl)
    simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at e
    have hzero := e.symm.trans (hx i)
    obtain ⟨w, hw⟩ := (ShortComplex.moduleCat_exact_iff _).1 (cohomology_exact₃ hT 1 2 rfl) _ hzero
    have hw0 : w = 0 := (ModuleCat.subsingleton_of_isZero
      (isZero_cohomology_of_bijective_nsmul_ulift (trivSequence (H i)).X₂
        (fun n hn => bijective_nsmul_rat hn) le_rfl)).elim _ _
    rw [hw0, map_zero] at hw
    have hyi : (cohomologyπ _ 1).hom (cocyclesMapAlong (φ i) (hφ i) (divFunEvalSequence φ i).τ₃ 1 z) =
        0 := by
      rw [show (cohomologyπ _ 1).hom (cocyclesMapAlong (φ i) (hφ i) (divFunEvalSequence φ i).τ₃ 1 z) =
        (cohomologyMapAlong (φ i) (hφ i) (divFunEvalSequence φ i).τ₃ 1).hom ((cohomologyπ _ 1).hom z)
        from (cohomologyMapAlong_cohomologyπ (φ i) (hφ i) (divFunEvalSequence φ i).τ₃ z).symm]
      exact hw.symm
    have hev := congrArg (H1Eval (trivSequence (H i)).X₃ h).hom hyi
    rw [map_zero, H1Eval_cohomology_class_apply, Submodule.Quotient.mk_eq_zero] at hev
    obtain ⟨a, ha⟩ := hev
    have h0 : ((trivSequence (H i)).X₃.ρ h - 1) a = 0 := by
      rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
      rfl
    rw [h0] at ha
    have key : cocycleFun (trivSequence (H i)).X₃
        (cocyclesMapAlong (φ i) (hφ i) (divFunEvalSequence φ i).τ₃ 1 z) =
        fun g => (divFunEval φ QZ i).hom (c (⇑(φ i) ∘ g)) :=
      cochainOf_cocycleι_cocyclesMapAlong (φ i) (hφ i) (divFunEvalSequence φ i).τ₃ z
    have := congrFun key fun _ => h
    rw [← ha] at this
    exact this.symm

  have hd := d_cocycleFun (divFunSequence φ).X₃ z
  have hmul : ∀ g h : G, c (fun _ => g * h) =
      divFunAction φ QZ g (c fun _ => h) + c fun _ => g :=
    fun g h => cocycle_mul_of_d_eq_zero hd g h
  have hlcc : IsLocallyConstant c := isLocallyConstant_cocycleFun _ z
  have hfin : (Set.range c).Finite := hlcc.range_finite
  have hlcx : IsLocallyConstant fun x : G => c fun _ => x :=
    hlcc.comp_continuous (continuous_pi fun _ => continuous_id)
  let b : divFun φ QZ := ⟨fun i x => ((c fun _ => x : divFun φ QZ) : I → G → QZ) i 1, by
    refine ⟨(hfin.biUnion fun f _ => f.2.1).subset fun i hi => ?_, fun i =>
      ⟨hlcx.comp fun f : divFun φ QZ => (f : I → G → QZ) i 1, fun h x => ?_⟩⟩
    · obtain ⟨x, hx⟩ := Function.ne_iff.1 hi
      refine Set.mem_iUnion₂.2 ⟨c fun _ => x, ⟨_, rfl⟩, fun hc => hx ?_⟩
      show ((c fun _ => x : divFun φ QZ) : I → G → QZ) i 1 = 0
      rw [hc]
      rfl
    · show ((c fun _ => φ i h * x : divFun φ QZ) : I → G → QZ) i 1 =
        ((c fun _ => x : divFun φ QZ) : I → G → QZ) i 1
      rw [hmul]
      show ((c fun _ => x : divFun φ QZ) : I → G → QZ) i (1 * φ i h) +
        ((c fun _ => φ i h : divFun φ QZ) : I → G → QZ) i 1 = _
      rw [hloc, add_zero, one_mul, ← mul_one (φ i h), ((c fun _ => x).2.2 i).2]⟩
  let b0 : (cochainsComplex (divFunSequence φ).X₃).X 0 :=
    (⟨fun _ => b, IsLocallyConstant.const _⟩ : locallyConstantCochains (divFunSequence φ).X₃ 0)
  have hz : z = ((cochainsComplex _).toCycles 0 1).hom b0 := by
    apply cocycleFun_injective
    rw [cocycleFun_toCycles]
    funext g
    rw [inhomogeneousD_zero_apply]
    have hg : g = fun _ => g 0 := funext fun j => by rw [Subsingleton.elim j 0]
    apply Subtype.ext
    funext i x
    change ((c g : divFun φ QZ) : I → G → QZ) i x = b.1 i (x * g 0) - b.1 i x
    show _ = ((c fun _ => x * g 0 : divFun φ QZ) : I → G → QZ) i 1 -
      ((c fun _ => x : divFun φ QZ) : I → G → QZ) i 1
    rw [hmul]
    show _ = ((c fun _ => g 0 : divFun φ QZ) : I → G → QZ) i (1 * x) +
      ((c fun _ => x : divFun φ QZ) : I → G → QZ) i 1 - ((c fun _ => x : divFun φ QZ) : I → G → QZ) i 1
    rw [add_sub_cancel_right, one_mul, ← hg]
  rw [hz]
  exact cohomologyπ_toCycles _ 0 1 b0

end Cohomology

end

end GroundTheory.ProfCoh
