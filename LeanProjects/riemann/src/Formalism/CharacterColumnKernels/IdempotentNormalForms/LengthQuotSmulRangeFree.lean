import Formalism.CharacterColumnKernels.StatementN
import Formalism.CharacterColumnKernels.IdempotentNormalForms.LenCokerOfDetNeZero

open Module IsDiscreteValuationRing

noncomputable section

namespace Formalism.NG

namespace QuotientPowerLengths

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

abbrev smulRange (M : Type*) [AddCommGroup M] [Module O M] (l : O) : Submodule O M :=
  LinearMap.range (l • (LinearMap.id : M →ₗ[O] M))

lemma mem_smulRange {M : Type*} [AddCommGroup M] [Module O M] (l : O) (x : M) :
    x ∈ smulRange M l ↔ ∃ y, l • y = x := by
  first
    | exact Iff.rfl
    | simp [smulRange, LinearMap.mem_range]

lemma quot_mono {M : Type*} [AddCommGroup M] [Module O M] {A B : Submodule O M} (h : A ≤ B) :
    Module.length O (M ⧸ B) ≤ Module.length O (M ⧸ A) := by
  exact Module.length_le_of_surjective (Submodule.factor h) (Submodule.factor_surjective h)

private theorem length_quot_span_pow_irreducible {ϖ : O} (hϖ : Irreducible ϖ) (k : ℕ) :
    Module.length O (O ⧸ Ideal.span {ϖ ^ k}) = k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hle : Ideal.span {ϖ ^ (k + 1)} ≤ Ideal.span {ϖ ^ k} := by
      rw [Ideal.span_singleton_le_span_singleton]
      exact pow_dvd_pow ϖ (Nat.le_add_right k 1)
    have hcomap : Ideal.span {ϖ} ≤
        Submodule.comap (LinearMap.mulLeft O (ϖ ^ k)) (Ideal.span {ϖ ^ (k + 1)}) := by
      intro a ha
      rw [Submodule.mem_comap, LinearMap.mulLeft_apply]
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      exact Ideal.mem_span_singleton'.mpr ⟨b, by ring⟩
    let f := Submodule.mapQ (Ideal.span {ϖ}) (Ideal.span {ϖ ^ (k + 1)})
      (LinearMap.mulLeft O (ϖ ^ k)) hcomap
    let g := Submodule.factor hle
    have hf : Function.Injective f := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro z hz
      obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective _ z
      have h0 : (Submodule.Quotient.mk (ϖ ^ k * a) : O ⧸ Ideal.span {ϖ ^ (k + 1)}) = 0 := hz
      rw [Submodule.Quotient.mk_eq_zero, Ideal.mem_span_singleton'] at h0
      obtain ⟨b, hb⟩ := h0
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Ideal.mem_span_singleton']
      refine ⟨b, ?_⟩
      have hne : ϖ ^ k ≠ 0 := pow_ne_zero _ hϖ.ne_zero
      apply mul_left_cancel₀ hne
      rw [← hb]
      ring
    have hg : Function.Surjective g := Submodule.factor_surjective hle
    have hex : Function.Exact f g := by
      intro z
      constructor
      · intro h0
        obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective _ z
        have h1 : (Submodule.Quotient.mk a : O ⧸ Ideal.span {ϖ ^ k}) = 0 := h0
        rw [Submodule.Quotient.mk_eq_zero, Ideal.mem_span_singleton'] at h1
        obtain ⟨b, rfl⟩ := h1
        refine ⟨Submodule.Quotient.mk b, ?_⟩
        show (Submodule.Quotient.mk (ϖ ^ k * b) : O ⧸ Ideal.span {ϖ ^ (k + 1)}) =
          Submodule.Quotient.mk (b * ϖ ^ k)
        rw [mul_comm (ϖ ^ k) b]
      · rintro ⟨y, rfl⟩
        obtain ⟨b, rfl⟩ := Submodule.mkQ_surjective _ y
        show (Submodule.Quotient.mk (ϖ ^ k * b) : O ⧸ Ideal.span {ϖ ^ k}) = 0
        rw [Submodule.Quotient.mk_eq_zero, Ideal.mem_span_singleton']
        exact ⟨b, mul_comm _ _⟩
    have hlen := Module.length_eq_add_of_exact f g hf hg hex
    have h1 : Module.length O (O ⧸ Ideal.span {ϖ}) = 1 := by
      rw [Module.length_eq_one_iff, isSimpleModule_iff_isCoatom]
      first
        | exact (PrincipalIdealRing.isMaximal_of_irreducible hϖ).out
        | exact Ideal.isMaximal_def.mp (PrincipalIdealRing.isMaximal_of_irreducible hϖ)
    rw [hlen, h1, ih]
    first
      | (push_cast; ring)
      | simp [add_comm]

private theorem length_quot_smulRange_eq_addVal (l : O) :
    Module.length O (O ⧸ smulRange O l) = addVal O l := by
  have hspan : smulRange O l = Ideal.span {l} := by
    ext x
    rw [mem_smulRange, Ideal.mem_span_singleton']
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, by rw [smul_eq_mul, mul_comm]⟩
    · rintro ⟨y, rfl⟩
      exact ⟨y, by rw [smul_eq_mul, mul_comm]⟩
  rw [hspan]
  have hirr : ∃ ϖ : O, Irreducible ϖ := by
    first
      | exact IsDiscreteValuationRing.exists_irreducible O
      | exact IsDiscreteValuationRing.exists_irreducible
  obtain ⟨ϖ, hϖ⟩ := hirr
  by_cases hl : l = 0
  · subst hl
    rw [addVal_zero]
    have hbound : ∀ k : ℕ, (k : ℕ∞) ≤ Module.length O (O ⧸ Ideal.span {(0 : O)}) := by
      intro k
      rw [← length_quot_span_pow_irreducible hϖ k]
      apply quot_mono
      rw [Ideal.span_singleton_eq_bot.mpr rfl]
      exact bot_le
    by_contra hne
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hne
    have h := hbound (m + 1)
    rw [← hm] at h
    have h' : m + 1 ≤ m := by exact_mod_cast h
    omega
  · obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hl hϖ
    rw [Ideal.span_singleton_mul_left_unit u.isUnit, length_quot_span_pow_irreducible hϖ k, addVal_mul,
      addVal_pow, addVal_uniformizer hϖ, IsDiscreteValuationRing.addVal_eq_zero_of_unit]
    simp

lemma length_quot_smulRange_pi (n : ℕ) (l : O) :
    Module.length O ((Fin n → O) ⧸ smulRange (Fin n → O) l) = n * addVal O l := by
  have hpi : smulRange (Fin n → O) l = Submodule.pi Set.univ (fun _ : Fin n => smulRange O l) := by
    ext x
    rw [mem_smulRange, Submodule.mem_pi]
    constructor
    · rintro ⟨y, rfl⟩ i _
      exact (mem_smulRange l _).mpr ⟨y i, rfl⟩
    · intro h
      choose y hy using fun i => (mem_smulRange l (x i)).mp (h i (Set.mem_univ i))
      exact ⟨y, by ext i; exact hy i⟩
  rw [hpi]
  let e := Submodule.quotientPi (fun _ : Fin n => smulRange O l)
  have hlen : Module.length O ((Fin n → O) ⧸ Submodule.pi Set.univ (fun _ : Fin n => smulRange O l)) =
      Module.length O (Fin n → (O ⧸ smulRange O l)) := by
    first
      | exact e.length_eq
      | exact le_antisymm (Module.length_le_of_injective e.toLinearMap e.injective)
          (Module.length_le_of_injective e.symm.toLinearMap e.symm.injective)
  rw [hlen, Module.length_pi_of_fintype, length_quot_smulRange_eq_addVal l]
  first
    | simp
    | simp [Finset.sum_const, nsmul_eq_mul]

lemma length_quot_smulRange_free (Q : Type*) [AddCommGroup Q] [Module O Q] [Module.Finite O Q]
    [IsTorsionFree O Q] (l : O) :
    Module.length O (Q ⧸ smulRange Q l) = finrank O Q * addVal O l := by
  haveI : NoZeroSMulDivisors O Q := by
    refine ⟨fun {c x} h => ?_⟩
    by_cases hc : c = 0
    · exact Or.inl hc
    · right
      have hreg : IsRegular c := isRegular_of_ne_zero hc
      apply (‹IsTorsionFree O Q›).1 hreg
      show c • x = c • 0
      rw [h, smul_zero]
  haveI : Module.Free O Q := by
    first
      | exact Module.free_of_finite_type_torsion_free'
      | infer_instance
  let e : Q ≃ₗ[O] (Fin (finrank O Q) → O) := (Module.finBasis O Q).equivFun
  have hmap : (smulRange Q l).map (e : Q →ₗ[O] (Fin (finrank O Q) → O)) =
      smulRange (Fin (finrank O Q) → O) l := by
    ext x
    rw [Submodule.mem_map, mem_smulRange]
    constructor
    · rintro ⟨q, hq, rfl⟩
      obtain ⟨y, rfl⟩ := (mem_smulRange l q).mp hq
      exact ⟨e y, by simp⟩
    · rintro ⟨y, rfl⟩
      exact ⟨l • e.symm y, (mem_smulRange l _).mpr ⟨_, rfl⟩, by simp⟩
  let e' := Submodule.Quotient.equiv (smulRange Q l) (smulRange (Fin (finrank O Q) → O) l) e hmap
  rw [← length_quot_smulRange_pi (finrank O Q) l]
  first
    | exact e'.length_eq
    | exact le_antisymm (Module.length_le_of_injective e'.toLinearMap e'.injective)
        (Module.length_le_of_injective e'.symm.toLinearMap e'.symm.injective)

variable {V : Type*} [AddCommGroup V] [Module (FractionRing O) V] [Module O V]
  [IsScalarTower O (FractionRing O) V] [FiniteDimensional (FractionRing O) V]

lemma isTorsionFree_quot (U : Submodule (FractionRing O) V) : IsTorsionFree O (V ⧸ U) := by
  refine ⟨fun r hr x y hxy => ?_⟩
  have hr0 : algebraMap O (FractionRing O) r ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective O (FractionRing O))).mpr hr.ne_zero
  have hxy' : algebraMap O (FractionRing O) r • x = algebraMap O (FractionRing O) r • y := by
    rw [algebraMap_smul, algebraMap_smul]
    exact hxy
  exact smul_right_injective (V ⧸ U) hr0 hxy'

lemma step1 (N : Submodule O V) (hN : N.FG) (W U : Submodule (FractionRing O) V)
    (hNWU : N ≤ (W ⊔ U).restrictScalars O) (l : O) :
    Module.length O (N ⧸ (smulRange N l ⊔
      LinearMap.ker ((U.mkQ.restrictScalars O) ∘ₗ N.subtype))) ≤
      (finrank (FractionRing O) W : ℕ∞) * addVal O l := by
  set g : N →ₗ[O] V ⧸ U := (U.mkQ.restrictScalars O) ∘ₗ N.subtype with hg
  haveI : Module.Finite O N := Module.Finite.iff_fg.mpr hN
  haveI : Module.Finite O (LinearMap.range g) := by
    first
      | exact Module.Finite.range g
      | infer_instance
  haveI hQtf : IsTorsionFree O (LinearMap.range g) :=
    ⟨fun r hr x y hxy => Subtype.ext ((isTorsionFree_quot U).1 hr (congrArg Subtype.val hxy))⟩
  have hlenQ := length_quot_smulRange_free (LinearMap.range g) l
  have hle : smulRange N l ⊔ LinearMap.ker g ≤
      LinearMap.ker ((smulRange (LinearMap.range g) l).mkQ ∘ₗ g.rangeRestrict) := by
    refine sup_le ?_ ?_
    · intro m hm
      obtain ⟨n, rfl⟩ := (mem_smulRange l m).mp hm
      rw [LinearMap.mem_ker, LinearMap.comp_apply, map_smul, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero]
      exact (mem_smulRange l _).mpr ⟨_, rfl⟩
    · intro m hm
      rw [LinearMap.mem_ker] at hm ⊢
      rw [LinearMap.comp_apply]
      have h0 : g.rangeRestrict m = 0 := Subtype.ext hm
      rw [h0, map_zero]
  have hker : LinearMap.ker ((smulRange (LinearMap.range g) l).mkQ ∘ₗ g.rangeRestrict) ≤
      smulRange N l ⊔ LinearMap.ker g := by
    intro n hn
    rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero] at hn
    obtain ⟨q, hq⟩ := (mem_smulRange l _).mp hn
    obtain ⟨n', hn'⟩ := LinearMap.surjective_rangeRestrict g q
    have hsplitn : n = l • n' + (n - l • n') := by abel
    rw [hsplitn]
    refine Submodule.add_mem _ (Submodule.mem_sup_left ((mem_smulRange l _).mpr ⟨n', rfl⟩))
      (Submodule.mem_sup_right ?_)
    rw [LinearMap.mem_ker, map_sub, map_smul]
    have h1 : g n' = (q : V ⧸ U) := congrArg Subtype.val hn'
    have h2 : g n = ((l • q : LinearMap.range g) : V ⧸ U) := (congrArg Subtype.val hq).symm
    rw [h1, h2, Submodule.coe_smul, sub_self]
  have hψ : Function.Injective ((smulRange N l ⊔ LinearMap.ker g).liftQ _ hle) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    obtain ⟨n, rfl⟩ := Submodule.mkQ_surjective _ z
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hker hz
  have hd := Module.length_le_of_injective _ hψ
  have he : finrank O (LinearMap.range g) ≤ finrank (FractionRing O) W := by
    haveI : NoZeroSMulDivisors O (LinearMap.range g) := by
      refine ⟨fun {c x} h => ?_⟩
      by_cases hc : c = 0
      · exact Or.inl hc
      · right
        have hreg : IsRegular c := isRegular_of_ne_zero hc
        apply hQtf.1 hreg
        show c • x = c • 0
        rw [h, smul_zero]
    haveI : Module.Free O (LinearMap.range g) := by
      first
        | exact Module.free_of_finite_type_torsion_free'
        | infer_instance
    let b := Module.Free.chooseBasis O (LinearMap.range g)
    have hmem : ∀ i, ((b i : LinearMap.range g) : V ⧸ U) ∈ W.map U.mkQ := by
      intro i
      obtain ⟨n, hn⟩ := LinearMap.mem_range.mp (b i).2
      rw [← hn, Submodule.mem_map]
      have hnWU : (n : V) ∈ W ⊔ U := hNWU n.2
      obtain ⟨a, ha, c, hc, hac⟩ := Submodule.mem_sup.mp hnWU
      refine ⟨a, ha, ?_⟩
      have hc0 : U.mkQ c = 0 := by
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact hc
      show U.mkQ a = U.mkQ (n : V)
      rw [← hac, map_add, hc0, add_zero]
    have hli : LinearIndependent O (fun i => ((b i : LinearMap.range g) : V ⧸ U)) :=
      b.linearIndependent.map' (LinearMap.range g).subtype (Submodule.ker_subtype _)
    have hliK := (LinearIndependent.iff_fractionRing O (FractionRing O)).mp hli
    have hliW : LinearIndependent (FractionRing O) (fun i => (⟨_, hmem i⟩ : W.map U.mkQ)) :=
      LinearIndependent.of_comp (W.map U.mkQ).subtype hliK
    calc finrank O (LinearMap.range g)
        = Fintype.card (Module.Free.ChooseBasisIndex O (LinearMap.range g)) := by
          first
            | exact Module.finrank_eq_card_chooseBasisIndex O _
            | exact Module.finrank_eq_card_chooseBasisIndex
            | simp [Module.finrank_eq_card_chooseBasisIndex]
      _ ≤ finrank (FractionRing O) (W.map U.mkQ) := hliW.fintype_card_le_finrank
      _ ≤ finrank (FractionRing O) W := Submodule.finrank_map_le _ _
  calc Module.length O (N ⧸ (smulRange N l ⊔ LinearMap.ker g))
      ≤ Module.length O ((LinearMap.range g) ⧸ smulRange (LinearMap.range g) l) := hd
    _ = (finrank O (LinearMap.range g) : ℕ∞) * addVal O l := hlenQ
    _ ≤ (finrank (FractionRing O) W : ℕ∞) * addVal O l := by
        first
          | gcongr
          | exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr he) (zero_le _)

lemma split {M P : Type*} [AddCommGroup M] [Module O M] [AddCommGroup P] [Module O P]
    (A B : Submodule O M) (hAB : A ≤ B) (i : P →ₗ[O] M) (C : Submodule O P)
    (hiB : ∀ p, i p ∈ B) (hC : C ≤ A.comap i) (hB : B ≤ A ⊔ LinearMap.range i) :
    Module.length O (M ⧸ A) ≤ Module.length O (M ⧸ B) + Module.length O (P ⧸ C) := by
  let q : (M ⧸ A) →ₗ[O] (M ⧸ B) := Submodule.factor hAB
  have hqs : Function.Surjective q := Submodule.factor_surjective hAB
  have hC' : C ≤ LinearMap.ker (A.mkQ ∘ₗ i) := by
    intro p hp
    rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hC hp
  let φ : (P ⧸ C) →ₗ[O] (M ⧸ A) := C.liftQ (A.mkQ ∘ₗ i) hC'
  have hker : LinearMap.ker q ≤ LinearMap.range φ := by
    intro z hz
    obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective A z
    rw [LinearMap.mem_ker] at hz
    have hmB : m ∈ B := by
      have h0 : (Submodule.Quotient.mk m : M ⧸ B) = 0 := hz
      rwa [Submodule.Quotient.mk_eq_zero] at h0
    obtain ⟨a, ha, y, hy, hay⟩ := Submodule.mem_sup.mp (hB hmB)
    obtain ⟨p, rfl⟩ := LinearMap.mem_range.mp hy
    refine ⟨Submodule.Quotient.mk p, ?_⟩
    show (Submodule.Quotient.mk (i p) : M ⧸ A) = Submodule.Quotient.mk m
    rw [Submodule.Quotient.eq]
    have he : i p - m = -a := by
      rw [← hay]
      abel
    rw [he]
    exact A.neg_mem ha
  have hex : Function.Exact (LinearMap.ker q).subtype q := by
    first
      | exact LinearMap.exact_subtype_ker_map q
      | exact fun y => ⟨fun hy => ⟨⟨y, hy⟩, rfl⟩, by rintro ⟨⟨z, hz⟩, rfl⟩; exact hz⟩
  have hlen := Module.length_eq_add_of_exact (LinearMap.ker q).subtype q
    (LinearMap.ker q).injective_subtype hqs hex
  have h1 : Module.length O (LinearMap.ker q) ≤ Module.length O (LinearMap.range φ) :=
    Module.length_le_of_injective (Submodule.inclusion hker) (Submodule.inclusion_injective hker)
  have h2 : Module.length O (LinearMap.range φ) ≤ Module.length O (P ⧸ C) :=
    Module.length_le_of_surjective φ.rangeRestrict φ.surjective_rangeRestrict
  rw [hlen, add_comm]
  exact add_le_add le_rfl (h1.trans h2)

def img (E : Set (Module.End (FractionRing O) V)) (N : Submodule O V) : Submodule O V :=
  Submodule.span O {v | ∃ f ∈ E, ∃ n ∈ N, f n = v}

def Dsub (E : Set (Module.End (FractionRing O) V)) (N : Submodule O V)
    (U : Submodule (FractionRing O) V) : Submodule O N :=
  (img E N ⊔ (U.restrictScalars O ⊓ N)).comap N.subtype

lemma img_le {E : Set (Module.End (FractionRing O) V)} {N : Submodule O V}
    (hNE : ∀ f ∈ E, ∀ n ∈ N, f n ∈ N) : img E N ≤ N := by
  unfold img
  rw [Submodule.span_le]
  rintro v ⟨f, hf, n, hn, rfl⟩
  exact hNE f hf n hn

lemma img_mono {E : Set (Module.End (FractionRing O) V)} {N N' : Submodule O V} (h : N ≤ N') :
    img E N ≤ img E N' := by
  unfold img
  refine Submodule.span_mono ?_
  rintro v ⟨f, hf, n, hn, rfl⟩
  exact ⟨f, hf, n, h hn, rfl⟩

theorem core {X : Type*} (E : Set (Module.End (FractionRing O) V))
    (W : X → Submodule (FractionRing O) V) (w : X → ℕ∞) (S : Finset X) :
    (∀ f ∈ E, ∀ x ∈ S, W x ≤ (W x).comap f) →
    (∀ x ∈ S, ∃ f ∈ E, ∃ l : O, (∀ v ∈ W x, f v = l • v) ∧ addVal O l ≤ w x) →
    ∀ U : Submodule (FractionRing O) V, (∀ f ∈ E, U ≤ U.comap f) →
    ∀ N : Submodule O V, N.FG → (∀ f ∈ E, ∀ n ∈ N, f n ∈ N) →
    N ≤ ((⨆ x ∈ S, W x) ⊔ U).restrictScalars O →
    Module.length O (N ⧸ Dsub E N U) ≤ ∑ x ∈ S, (finrank (FractionRing O) (W x) : ℕ∞) * w x := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro _ _ U _ N _ _ hNU
    have htop : Dsub E N U = ⊤ := by
      rw [eq_top_iff]
      rintro ⟨n, hn⟩ -
      have hnU : n ∈ U := by
        have h' : n ∈ (⨆ x ∈ (∅ : Finset X), W x) ⊔ U := hNU hn
        simpa using h'
      show n ∈ img E N ⊔ (U.restrictScalars O ⊓ N)
      exact Submodule.mem_sup_right (Submodule.mem_inf.mpr ⟨hnU, hn⟩)
    rw [htop, Finset.sum_empty]
    first
      | simp
      | exact (Module.length_eq_zero_iff.mpr inferInstance).le
      | exact le_of_eq (Module.length_eq_zero_iff.mpr ((Submodule.Quotient.subsingleton_iff _).mpr rfl))
  | @insert x S hxS ih =>
    intro h1 h2 U hU N hN hNE hNS
    obtain ⟨f, hfE, l, hfl, hlw⟩ := h2 x (Finset.mem_insert_self x S)
    obtain ⟨U₁, hU₁⟩ : ∃ U₁ : Submodule (FractionRing O) V, U₁ = (⨆ y ∈ S, W y) ⊔ U := ⟨_, rfl⟩
    have hEU₁ : ∀ g ∈ E, U₁ ≤ U₁.comap g := by
      intro g hg
      rw [hU₁]
      refine sup_le (iSup₂_le fun y hy => ?_) ?_
      · exact (h1 g hg y (Finset.mem_insert_of_mem hy)).trans
          (Submodule.comap_mono (le_sup_of_le_left (le_iSup₂_of_le y hy le_rfl)))
      · exact (hU g hg).trans (Submodule.comap_mono le_sup_right)
    have hNWU : N ≤ (W x ⊔ U₁).restrictScalars O := by
      have hle : (⨆ y ∈ insert x S, W y) ⊔ U ≤ W x ⊔ U₁ := by
        rw [hU₁]
        refine sup_le (iSup₂_le fun y hy => ?_) (le_sup_of_le_right le_sup_right)
        rcases Finset.mem_insert.mp hy with rfl | hy
        · exact le_sup_left
        · exact le_sup_of_le_right (le_sup_of_le_left (le_iSup₂_of_le y hy le_rfl))
      intro n hn
      have h : n ∈ (⨆ y ∈ insert x S, W y) ⊔ U := hNS hn
      exact hle h
    obtain ⟨N', hN'⟩ : ∃ N' : Submodule O V, N' = N ⊓ U₁.restrictScalars O := ⟨_, rfl⟩
    have hN'N : N' ≤ N := by rw [hN']; exact inf_le_left
    have hN'ge : N ⊓ U₁.restrictScalars O ≤ N' := hN'.ge
    have hN'U : N' ≤ U₁.restrictScalars O := by rw [hN']; exact inf_le_right
    have hN'fg : N'.FG := by
      haveI : IsNoetherian O N := isNoetherian_of_fg_of_noetherian N hN
      have hfg : (N'.comap N.subtype).FG := IsNoetherian.noetherian _
      have hmap := hfg.map N.subtype
      rwa [Submodule.map_comap_subtype, inf_eq_right.mpr hN'N] at hmap
    have hN'E : ∀ g ∈ E, ∀ n ∈ N', g n ∈ N' := by
      intro g hg n hn
      have hn1 : n ∈ N := hN'N hn
      have hn2 : n ∈ U₁ := hN'U hn
      have hg2 : g n ∈ U₁ := hEU₁ g hg hn2
      exact hN'ge (Submodule.mem_inf.mpr ⟨hNE g hg n hn1, hg2⟩)
    have hN'S : N' ≤ ((⨆ y ∈ S, W y) ⊔ U).restrictScalars O := by
      rw [← hU₁]; exact hN'U
    have hih := ih (fun g hg y hy => h1 g hg y (Finset.mem_insert_of_mem hy))
      (fun y hy => h2 y (Finset.mem_insert_of_mem hy)) U hU N' hN'fg hN'E hN'S
    obtain ⟨B₀, hB₀⟩ : ∃ B₀ : Submodule O N,
        B₀ = smulRange N l ⊔ LinearMap.ker ((U₁.mkQ.restrictScalars O) ∘ₗ N.subtype) := ⟨_, rfl⟩
    have hstep := step1 N hN (W x) U₁ hNWU l
    rw [← hB₀] at hstep
    have hiB : ∀ p : N', Submodule.inclusion hN'N p ∈ Dsub E N U ⊔ B₀ := by
      intro p
      rw [hB₀]
      refine Submodule.mem_sup_right (Submodule.mem_sup_right ?_)
      rw [LinearMap.mem_ker]
      have hpU : (p : V) ∈ U₁ := hN'U p.2
      show U₁.mkQ (p : V) = 0
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hpU
    have hC : Dsub E N' U ≤ (Dsub E N U).comap (Submodule.inclusion hN'N) := by
      intro p hp
      unfold Dsub at hp ⊢
      simp only [Submodule.mem_comap] at hp ⊢
      exact sup_le_sup (img_mono hN'N) (inf_le_inf_left _ hN'N) hp
    have hB : Dsub E N U ⊔ B₀ ≤ Dsub E N U ⊔ LinearMap.range (Submodule.inclusion hN'N) := by
      rw [hB₀]
      refine sup_le le_sup_left (sup_le ?_ ?_)
      · intro m hm
        obtain ⟨n, rfl⟩ := (mem_smulRange l m).mp hm
        have hfn : f (n : V) ∈ N := hNE f hfE n n.2
        have hdiff : f (n : V) - l • (n : V) ∈ N' := by
          apply hN'ge
          refine Submodule.mem_inf.mpr ⟨N.sub_mem hfn (N.smul_mem l n.2), ?_⟩
          have hnWU : (n : V) ∈ W x ⊔ U₁ := hNWU n.2
          obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hnWU
          have key : f (n : V) - l • (n : V) = f b - l • b := by
            rw [← hab, map_add, hfl a ha, smul_add]
            abel
          show f (n : V) - l • (n : V) ∈ U₁
          rw [key]
          refine U₁.sub_mem (hEU₁ f hfE hb) ?_
          rw [← algebraMap_smul (FractionRing O) l b]
          exact U₁.smul_mem _ hb
        have hA : (⟨f (n : V), hfn⟩ : N) ∈ Dsub E N U := by
          show f (n : V) ∈ img E N ⊔ (U.restrictScalars O ⊓ N)
          refine Submodule.mem_sup_left ?_
          unfold img
          exact Submodule.subset_span ⟨f, hfE, (n : V), n.2, rfl⟩
        have hR : (⟨f (n : V), hfn⟩ : N) - l • n ∈ LinearMap.range (Submodule.inclusion hN'N) :=
          ⟨⟨_, hdiff⟩, Subtype.ext rfl⟩
        rw [← sub_sub_cancel (⟨f (n : V), hfn⟩ : N) (l • n)]
        exact Submodule.sub_mem _ (Submodule.mem_sup_left hA) (Submodule.mem_sup_right hR)
      · intro m hm
        rw [LinearMap.mem_ker] at hm
        have hmU : (m : V) ∈ U₁ := by
          have h0 : U₁.mkQ (m : V) = 0 := hm
          rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h0
        have hmN' : (m : V) ∈ N' := hN'ge (Submodule.mem_inf.mpr ⟨m.2, hmU⟩)
        exact Submodule.mem_sup_right ⟨⟨(m : V), hmN'⟩, Subtype.ext rfl⟩
    have hsplit := split (Dsub E N U) (Dsub E N U ⊔ B₀) le_sup_left (Submodule.inclusion hN'N)
      (Dsub E N' U) hiB hC hB
    have hq := quot_mono (M := N) (le_sup_right : B₀ ≤ Dsub E N U ⊔ B₀)
    rw [Finset.sum_insert hxS]
    calc Module.length O (N ⧸ Dsub E N U)
        ≤ Module.length O (N ⧸ (Dsub E N U ⊔ B₀)) + Module.length O (N' ⧸ Dsub E N' U) := hsplit
      _ ≤ (finrank (FractionRing O) (W x) : ℕ∞) * addVal O l +
            ∑ y ∈ S, (finrank (FractionRing O) (W y) : ℕ∞) * w y :=
          add_le_add (hq.trans hstep) hih
      _ ≤ _ := by
          first
            | (gcongr; exact hlw)
            | gcongr
            | exact add_le_add_right (mul_le_mul_of_nonneg_left hlw (zero_le _)) _

section Eig

variable {X : Type*} {T : Subalgebra O (X → O)} {act : T →+* Module.End (FractionRing O) V}

lemma mem_Vx {x : X} {v : V} :
    v ∈ Vx T act x ↔ ∀ f : T, act f v = ((f : X → O) x) • v := by
  simp only [Vx, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero, algebraMap_smul]

lemma vx_pres (g : Module.End (FractionRing O) V) (hg : ∀ f : T, g * act f = act f * g) (x : X) :
    Vx T act x ≤ (Vx T act x).comap g := by
  intro v hv
  rw [Submodule.mem_comap, mem_Vx]
  rw [mem_Vx] at hv
  intro f
  calc act f (g v) = (act f * g) v := rfl
    _ = (g * act f) v := by rw [hg f]
    _ = g (act f v) := rfl
    _ = g (((f : X → O) x) • v) := by rw [hv f]
    _ = ((f : X → O) x) • g v := by
      rw [← algebraMap_smul (FractionRing O) ((f : X → O) x) v, map_smul, algebraMap_smul]

lemma VS_pres (g : Module.End (FractionRing O) V) (hg : ∀ y, Vx T act y ≤ (Vx T act y).comap g)
    (S : Set X) : VS T act S ≤ (VS T act S).comap g := by
  unfold VS
  exact iSup₂_le fun y hy => (hg y).trans (Submodule.comap_mono (le_iSup₂_of_le y hy le_rfl))

lemma VS_sup_compl (hsum : (⨆ x, Vx T act x) = ⊤) (S : Set X) :
    VS T act S ⊔ VS T act Sᶜ = ⊤ := by
  unfold VS
  rw [eq_top_iff, ← hsum]
  refine iSup_le fun x => ?_
  by_cases hx : x ∈ S
  · exact le_sup_of_le_left (le_iSup₂_of_le x hx le_rfl)
  · exact le_sup_of_le_right (le_iSup₂_of_le x (show x ∈ Sᶜ from hx) le_rfl)

lemma mem_cc {Z : Set X} {c : T} : c ∈ ccIdeal T Z ↔ ∀ y ∉ Z, (c : X → O) y = 0 := by
  unfold ccIdeal
  rw [RingHom.mem_ker]
  constructor
  · intro h y hy
    exact congrFun h ⟨y, hy⟩
  · intro h
    funext y
    exact h y.1 y.2

lemma cc_kill {Z : Set X} {c : T} (hc : c ∈ ccIdeal T Z) :
    VS T act Zᶜ ≤ LinearMap.ker (act c) := by
  unfold VS
  refine iSup₂_le fun y hy => ?_
  intro v hv
  rw [LinearMap.mem_ker, (mem_Vx.mp hv) c, (mem_cc.mp hc) y hy, zero_smul]

lemma cc_comm (c f : T) : act c * act f = act f * act c := by
  rw [← map_mul, ← map_mul, mul_comm c f]

lemma cc_mem_VS (hsum : (⨆ x, Vx T act x) = ⊤) {Z : Set X} {c : T} (hc : c ∈ ccIdeal T Z)
    (v : V) : act c v ∈ VS T act Z := by
  have hv : v ∈ VS T act Z ⊔ VS T act Zᶜ := by
    rw [VS_sup_compl hsum Z]
    exact Submodule.mem_top
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
  have hpres := VS_pres (act c) (fun y => vx_pres (act c) (fun f => cc_comm c f) y) Z
  rw [map_add, LinearMap.mem_ker.mp (cc_kill hc hb), add_zero]
  exact hpres ha

lemma vcc_attain (Z : Set X) (x : X) :
    ∃ c ∈ ccIdeal T Z, addVal O ((c : X → O) x) = vcc T Z x := by
  obtain ⟨c, hc⟩ : (⨅ c : ccIdeal T Z, addVal O (((c : T) : X → O) x)) ∈
      Set.range (fun c : ccIdeal T Z => addVal O (((c : T) : X → O) x)) :=
    csInf_mem ⟨_, ⟨0, rfl⟩⟩
  refine ⟨c, c.2, hc.trans ?_⟩
  unfold vcc
  rw [iInf_subtype]

theorem congMod_le (hsum : (⨆ x, Vx T act x) = ⊤) (L : Submodule O V) (hL : L.FG)
    (S : Finset X) (E : Set (Module.End (FractionRing O) V)) (w : X → ℕ∞)
    (hcomm : ∀ g ∈ E, ∀ f : T, g * act f = act f * g)
    (hEL : ∀ g ∈ E, ∀ v ∈ L, g v ∈ L) (hES : ∀ g ∈ E, ∀ v ∈ L, g v ∈ VS T act (S : Set X))
    (hmin : ∀ x ∈ S, ∃ g ∈ E, ∃ l : O, (∀ v ∈ Vx T act x, g v = l • v) ∧ addVal O l ≤ w x) :
    Module.length O (CongMod T act L (S : Set X)) ≤
      ∑ x ∈ S, (finrank (FractionRing O) (Vx T act x) : ℕ∞) * w x := by
  have hcore := core E (Vx T act) w S
    (fun f hf x _ => vx_pres f (hcomm f hf) x) hmin (VS T act ((S : Set X)ᶜ))
    (fun f hf => VS_pres f (fun y => vx_pres f (hcomm f hf) y) _) L hL hEL
    (by
      intro v _
      have hv : v ∈ VS T act (S : Set X) ⊔ VS T act ((S : Set X)ᶜ) := by
        rw [VS_sup_compl hsum (S : Set X)]
        exact Submodule.mem_top
      exact hv)
  refine le_trans (quot_mono ?_) hcore
  unfold Dsub
  refine Submodule.comap_mono (sup_le_sup_right ?_ _)
  refine le_inf ?_ (img_le hEL)
  unfold img
  rw [Submodule.span_le]
  rintro v ⟨f, hf, n, hn, rfl⟩
  exact hES f hf n hn

end Eig

end QuotientPowerLengths

open QuotientPowerLengths

theorem congBound : StatCongBound := by
  unfold StatCongBound
  intro O _ _ _ X _ T _ _ V _ _ _ _ _ act hsum L hL _ hLT Z
  refine congMod_le hsum L hL Z ((fun c : T => act c) '' (ccIdeal T (Z : Set X) : Set T))
    (vcc T (Z : Set X)) ?_ ?_ ?_ ?_
  · rintro g ⟨c, -, rfl⟩ f
    exact cc_comm c f
  · rintro g ⟨c, -, rfl⟩ v hv
    exact hLT c v hv
  · rintro g ⟨c, hc, rfl⟩ v -
    exact cc_mem_VS hsum hc v
  · intro x _
    obtain ⟨c, hc, hcx⟩ := vcc_attain (T := T) (Z : Set X) x
    exact ⟨act c, ⟨c, hc, rfl⟩, (c : X → O) x, fun v hv => (mem_Vx.mp hv) c, hcx.le⟩

theorem congBoundGood : StatCongBoundGood := by
  unfold StatCongBoundGood
  intro O _ _ _ X _ T _ _ V _ _ _ _ _ act hsum L hL _ hLT Z Zg _ a A haL hacomm hZgA hZ0
  have hVa : VS T act (Z : Set X) ≤ (VS T act (Zg : Set X)).comap a := by
    unfold VS
    refine iSup₂_le fun y hy => ?_
    intro v hv
    rw [Submodule.mem_comap]
    by_cases hyg : y ∈ Zg
    · rw [hZgA y hyg v hv]
      exact Submodule.smul_mem _ _
        ((le_iSup₂_of_le y (Finset.mem_coe.mpr hyg) le_rfl :
          Vx T act y ≤ ⨆ x ∈ (Zg : Set X), Vx T act x) hv)
    · rw [hZ0 y (Finset.mem_coe.mp hy) hyg v hv]
      exact Submodule.zero_mem _
  refine congMod_le hsum L hL Zg ((fun c : T => a * act c) '' (ccIdeal T (Z : Set X) : Set T))
    (fun x => vcc T (Z : Set X) x + addVal O (A : O)) ?_ ?_ ?_ ?_
  · rintro g ⟨c, -, rfl⟩ f
    show a * act c * act f = act f * (a * act c)
    rw [mul_assoc, cc_comm c f, ← mul_assoc, hacomm f, mul_assoc]
  · rintro g ⟨c, -, rfl⟩ v hv
    exact haL (act c v) (hLT c v hv)
  · rintro g ⟨c, hc, rfl⟩ v -
    exact hVa (cc_mem_VS hsum hc v)
  · intro x hx
    obtain ⟨c, hc, hcx⟩ := vcc_attain (T := T) (Z : Set X) x
    refine ⟨a * act c, ⟨c, hc, rfl⟩, (A : O) * (c : X → O) x, fun v hv => ?_, ?_⟩
    · show a (act c v) = _
      rw [(mem_Vx.mp hv) c, ← algebraMap_smul (FractionRing O) ((c : X → O) x) v, map_smul,
        hZgA x hx v hv, smul_smul,
        ← algebraMap_smul (FractionRing O) ((A : O) * (c : X → O) x) v, map_mul, map_intCast,
        mul_comm]
    · exact le_of_eq (by rw [addVal_mul, hcx, add_comm])

theorem congBoundLarge : StatCongBoundLarge := by
  unfold StatCongBoundLarge
  intro O _ _ _ X _ T _ _ V _ _ _ _ _ act hsum L hL _ hLT Z _
  refine congMod_le hsum L hL Z ((fun c : T => act c) '' (ccIdeal T (Z : Set X) : Set T))
    (vcc T (Z : Set X)) ?_ ?_ ?_ ?_
  · rintro g ⟨c, -, rfl⟩ f
    exact cc_comm c f
  · rintro g ⟨c, -, rfl⟩ v hv
    exact hLT c v hv
  · rintro g ⟨c, hc, rfl⟩ v -
    exact cc_mem_VS hsum hc v
  · intro x _
    obtain ⟨c, hc, hcx⟩ := vcc_attain (T := T) (Z : Set X) x
    exact ⟨act c, ⟨c, hc, rfl⟩, (c : X → O) x, fun v hv => (mem_Vx.mp hv) c, hcx.le⟩

theorem congBoundGoodLarge : StatCongBoundGoodLarge := by
  unfold StatCongBoundGoodLarge
  intro O _ _ _ X _ T _ _ V _ _ _ _ _ act hsum L hL _ hLT Z Zg _ _ a A haL hacomm hZgA hZ0
  have hVa : VS T act (Z : Set X) ≤ (VS T act (Zg : Set X)).comap a := by
    unfold VS
    refine iSup₂_le fun y hy => ?_
    intro v hv
    rw [Submodule.mem_comap]
    by_cases hyg : y ∈ Zg
    · rw [hZgA y hyg v hv]
      exact Submodule.smul_mem _ _
        ((le_iSup₂_of_le y (Finset.mem_coe.mpr hyg) le_rfl :
          Vx T act y ≤ ⨆ x ∈ (Zg : Set X), Vx T act x) hv)
    · rw [hZ0 y (Finset.mem_coe.mp hy) hyg v hv]
      exact Submodule.zero_mem _
  refine congMod_le hsum L hL Zg ((fun c : T => a * act c) '' (ccIdeal T (Z : Set X) : Set T))
    (fun x => vcc T (Z : Set X) x + addVal O (A : O)) ?_ ?_ ?_ ?_
  · rintro g ⟨c, -, rfl⟩ f
    show a * act c * act f = act f * (a * act c)
    rw [mul_assoc, cc_comm c f, ← mul_assoc, hacomm f, mul_assoc]
  · rintro g ⟨c, -, rfl⟩ v hv
    exact haL (act c v) (hLT c v hv)
  · rintro g ⟨c, hc, rfl⟩ v -
    exact hVa (cc_mem_VS hsum hc v)
  · intro x hx
    obtain ⟨c, hc, hcx⟩ := vcc_attain (T := T) (Z : Set X) x
    refine ⟨a * act c, ⟨c, hc, rfl⟩, (A : O) * (c : X → O) x, fun v hv => ?_, ?_⟩
    · show a (act c v) = _
      rw [(mem_Vx.mp hv) c, ← algebraMap_smul (FractionRing O) ((c : X → O) x) v, map_smul,
        hZgA x hx v hv, smul_smul,
        ← algebraMap_smul (FractionRing O) ((A : O) * (c : X → O) x) v, map_mul, map_intCast,
        mul_comm]
    · exact le_of_eq (by rw [addVal_mul, hcx, add_comm])

end Formalism.NG
