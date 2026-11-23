import Mathlib

open CategoryTheory AlgebraicGeometry IsLocalRing

universe u

namespace GlobalTheory

section Completion

variable {A R : Type*} [CommRing A] [CommRing R]

theorem factorPow_evalₐ (J : Ideal A) {m n : ℕ} (h : m ≤ n) (x : AdicCompletion J A) :
    Ideal.Quotient.factorPow J h (AdicCompletion.evalₐ J n x) = AdicCompletion.evalₐ J m x := by
  induction x using AdicCompletion.induction_on with
  | _ x =>
    rw [AdicCompletion.evalₐ_mk, AdicCompletion.evalₐ_mk, Ideal.Quotient.factorPow,
      Ideal.Quotient.factor_mk, Ideal.Quotient.eq]
    have := (x.property h).symm
    rw [SModEq.sub_mem] at this
    simpa using this

theorem pow_mul_le_comap_pow (φ : A →+* R) {J : Ideal A} {I : Ideal R} {k : ℕ}
    (hk : J.map φ ^ k ≤ I) (n : ℕ) : J ^ (k * n) ≤ (I ^ n).comap φ := by
  rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow, pow_mul]
  exact Ideal.pow_right_mono hk n

theorem exists_extend_adicCompletion (φ : A →+* R) (J : Ideal A) (I : Ideal R)
    [IsAdicComplete I R] {k : ℕ} (hk : J.map φ ^ k ≤ I) :
    ∃ ψ : AdicCompletion J A →+* R, ψ.comp (algebraMap A (AdicCompletion J A)) = φ ∧
      ∀ (n : ℕ) (x : AdicCompletion J A) (a : A),
        AdicCompletion.evalₐ J (k * n) x = Ideal.Quotient.mk _ a → ψ x - φ a ∈ I ^ n := by
  let f : (n : ℕ) → AdicCompletion J A →+* R ⧸ I ^ n := fun n =>
    (Ideal.quotientMap (I ^ n) φ (pow_mul_le_comap_pow φ hk n)).comp
      (AdicCompletion.evalₐ J (k * n)).toRingHom
  have hfa : ∀ n x a, AdicCompletion.evalₐ J (k * n) x = Ideal.Quotient.mk _ a →
      f n x = Ideal.Quotient.mk _ (φ a) := by
    intro n x a h
    change Ideal.quotientMap (I ^ n) φ (pow_mul_le_comap_pow φ hk n) (AdicCompletion.evalₐ J (k * n) x) = _
    rw [h, Ideal.quotientMap_mk]
  have hf : ∀ {m n : ℕ} (hle : m ≤ n), (Ideal.Quotient.factorPow I hle).comp (f n) = f m := by
    intro m n hle
    refine RingHom.ext fun x => ?_
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ J (k * n) x)
    have ha' : AdicCompletion.evalₐ J (k * m) x = Ideal.Quotient.mk _ a := by
      rw [← factorPow_evalₐ J (Nat.mul_le_mul_left k hle), ← ha]
      rfl
    rw [RingHom.comp_apply, hfa n x a ha.symm, hfa m x a ha']
    rfl
  have key : ∀ (n : ℕ) (x : AdicCompletion J A) (a : A),
      AdicCompletion.evalₐ J (k * n) x = Ideal.Quotient.mk _ a →
        IsAdicComplete.liftRingHom I f hf x - φ a ∈ I ^ n := by
    intro n x a h
    rw [← Ideal.Quotient.eq, IsAdicComplete.mk_liftRingHom, hfa n x a h]
  refine ⟨IsAdicComplete.liftRingHom I f hf, ?_, key⟩
  apply DFunLike.coe_injective
  apply IsHausdorff.funext' I
  intro n a
  exact Ideal.Quotient.eq.mpr (key n _ a (AdicCompletion.evalₐ_of J _ a))

theorem adicCompletion_ringHom_ext {J : Ideal A} (hJ : J.FG) (I : Ideal R) [IsHausdorff I R]
    {ψ ψ' : AdicCompletion J A →+* R} {k : ℕ}
    (hk : J.map (ψ.comp (algebraMap A (AdicCompletion J A))) ^ k ≤ I)
    (h : ψ.comp (algebraMap A (AdicCompletion J A)) =
      ψ'.comp (algebraMap A (AdicCompletion J A))) : ψ = ψ' := by
  apply DFunLike.coe_injective
  apply IsHausdorff.funext' I
  intro n x
  obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ (AdicCompletion.eval J A (k * n) x)
  have hx : x - algebraMap A _ a ∈ (J ^ (k * n)).map (algebraMap A (AdicCompletion J A)) := by
    rw [← Submodule.restrictScalars_mem A, ← Ideal.smul_top_eq_map,
      AdicCompletion.pow_smul_top_eq_ker_eval hJ, LinearMap.mem_ker, map_sub, ← ha, sub_eq_zero]
    exact (AdicCompletion.eval_of J A _ a).symm
  have hmem : ∀ χ : AdicCompletion J A →+* R,
      χ.comp (algebraMap A (AdicCompletion J A)) = ψ.comp (algebraMap A (AdicCompletion J A)) →
      χ x - ψ (algebraMap A _ a) ∈ I ^ n := by
    intro χ hχ
    have h1 : χ (algebraMap A _ a) = ψ (algebraMap A _ a) := congr($hχ a)
    rw [← h1, ← map_sub]
    have h2 := Ideal.mem_map_of_mem χ hx
    rw [Ideal.map_map, hχ] at h2
    exact Ideal.map_le_iff_le_comap.mpr (pow_mul_le_comap_pow _ hk n) h2
  rw [Ideal.Quotient.eq]
  have := sub_mem (hmem ψ rfl) (hmem ψ' h.symm)
  simpa using this

theorem existsUnique_extend_adicCompletion (φ : A →+* R) {J : Ideal A} (hJ : J.FG) (I : Ideal R)
    [IsAdicComplete I R] (hk : ∃ k : ℕ, J.map φ ^ k ≤ I) :
    ∃! ψ : AdicCompletion J A →+* R, ψ.comp (algebraMap A (AdicCompletion J A)) = φ := by
  obtain ⟨k, hk⟩ := hk
  obtain ⟨ψ, hψ, -⟩ := exists_extend_adicCompletion φ J I hk
  refine ⟨ψ, hψ, fun ψ' hψ' => ?_⟩
  exact adicCompletion_ringHom_ext hJ I (k := k) (by rwa [hψ']) (hψ'.trans hψ.symm)

theorem isLocalHom_of_extend_adicCompletion [IsLocalRing A] [IsLocalRing R]
    (hJ : (maximalIdeal A).FG) (ψ : AdicCompletion (maximalIdeal A) A →+* R)
    [hψ : IsLocalHom (ψ.comp (algebraMap A (AdicCompletion (maximalIdeal A) A)))] :
    IsLocalHom ψ := by
  have := AdicCompletion.isLocalRing_of_fg hJ
  apply ((IsLocalRing.local_hom_TFAE ψ).out 0 2).mpr
  rw [AdicCompletion.maximalIdeal_eq_map_of_fg hJ, Ideal.map_map]
  exact ((IsLocalRing.local_hom_TFAE _).out 0 2).mp hψ

end Completion

section Local

variable {R : Type u} [CommRing R] [IsLocalRing R] {X : Scheme.{u}}

theorem existsUnique_factor_stalk (f : Spec (.of R) ⟶ X) {x : X} (hx : f (closedPoint R) = x) :
    ∃! φ : X.presheaf.stalk x ⟶ .of R, Spec.map φ ≫ X.fromSpecStalk x = f := by
  subst hx
  refine ⟨Scheme.stalkClosedPointTo (R := .of R) f,
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := .of R) f, fun φ hφ => ?_⟩
  apply Spec.map_injective
  rw [← cancel_mono (X.fromSpecStalk _), hφ]
  exact (Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := .of R) f).symm

theorem isLocalHom_of_factor_stalk {f : Spec (.of R) ⟶ X} {x : X} (hx : f (closedPoint R) = x)
    {φ : X.presheaf.stalk x ⟶ .of R} (hφ : Spec.map φ ≫ X.fromSpecStalk x = f) :
    IsLocalHom φ.hom := by
  subst hx
  rw [(existsUnique_factor_stalk f rfl).unique hφ
    (Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := .of R) f)]
  exact Scheme.isLocalHom_stalkClosedPointTo' f

theorem range_subset_of_closedPoint_mem (f : Spec (.of R) ⟶ X) {U : X.Opens}
    (hU : f (closedPoint R) ∈ U) : Set.range f ⊆ U := by
  rintro _ ⟨y, rfl⟩
  have : y ∈ f ⁻¹ᵁ U := by
    rw [Scheme.preimage_eq_top_of_closedPoint_mem (R := .of R) f hU]; trivial
  exact this

noncomputable def fromSpecCompletedStalk (X : Scheme.{u}) (x : X) :
    Spec (.of (AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x))) ⟶ X :=
  Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x)
    (AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x)))) ≫
    X.fromSpecStalk x

omit [IsLocalRing R] in

theorem existsUnique_factor_completedStalk (I : Ideal R) [IsAdicComplete I R]
    {f : Spec (.of R) ⟶ X} {x : X}
    {φ : X.presheaf.stalk x ⟶ .of R} (hφ : Spec.map φ ≫ X.fromSpecStalk x = f)
    (hfg : (maximalIdeal (X.presheaf.stalk x)).FG)
    (hk : ∃ k : ℕ, (maximalIdeal (X.presheaf.stalk x)).map φ.hom ^ k ≤ I) :
    ∃! ψ : AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x) →+* R,
      Spec.map (CommRingCat.ofHom ψ) ≫ fromSpecCompletedStalk X x = f := by
  refine (existsUnique_congr fun ψ => ?_).mp
    (existsUnique_extend_adicCompletion (R := R) φ.hom hfg I hk)
  rw [fromSpecCompletedStalk, ← Spec.map_comp_assoc, ← hφ, cancel_mono, ← CommRingCat.ofHom_comp]
  constructor
  · intro h; rw [h]; rfl
  · intro h; exact congr($(Spec.map_injective h).hom)

omit [IsLocalRing R] in

theorem existsUnique_factor_completedStalk' (I : Ideal R) [IsAdicComplete I R]
    {f : Spec (.of R) ⟶ X} {x : X}
    {φ : X.presheaf.stalk x ⟶ .of R} (hφ : Spec.map φ ≫ X.fromSpecStalk x = f)
    (hfg : (maximalIdeal (X.presheaf.stalk x)).FG)
    (hk : ∃ k : ℕ, (maximalIdeal (X.presheaf.stalk x)).map φ.hom ^ k ≤ I) :
    ∃! g, g ≫ fromSpecCompletedStalk X x = f := by
  obtain ⟨ψ, hψ, hu⟩ := existsUnique_factor_completedStalk I hφ hfg hk
  refine ⟨_, hψ, fun g hg => ?_⟩
  obtain ⟨χ, rfl⟩ := Spec.map_surjective g
  rw [← hu χ.hom hg]
  rfl

theorem isLocalHom_of_factor_completedStalk {f : Spec (.of R) ⟶ X} {x : X}
    (hx : f (closedPoint R) = x) (hfg : (maximalIdeal (X.presheaf.stalk x)).FG)
    {ψ : AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x) →+* R}
    (hψ : Spec.map (CommRingCat.ofHom ψ) ≫ fromSpecCompletedStalk X x = f) : IsLocalHom ψ := by
  rw [fromSpecCompletedStalk, ← Spec.map_comp_assoc] at hψ
  exact isLocalHom_of_extend_adicCompletion hfg ψ (hψ := isLocalHom_of_factor_stalk hx hψ)

end Local

section Limit

variable {R : Type u} [CommRing R] (I : Ideal R)

noncomputable abbrev adicLevelι (n : ℕ) : Spec (.of (R ⧸ I ^ n)) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ n)))

noncomputable abbrev adicLevelMap {m n : ℕ} (h : m ≤ n) :
    Spec (.of (R ⧸ I ^ m)) ⟶ Spec (.of (R ⧸ I ^ n)) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.factorPow I h))

@[reassoc]
theorem adicLevelMap_ι {m n : ℕ} (h : m ≤ n) :
    adicLevelMap I h ≫ adicLevelι I n = adicLevelι I m := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

@[reassoc]
theorem adicLevelMap_comp {l m n : ℕ} (h : l ≤ m) (h' : m ≤ n) :
    adicLevelMap I h ≫ adicLevelMap I h' = adicLevelMap I (h.trans h') := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact Ideal.Quotient.ringHom_ext rfl

theorem adicLevelMap_self (n : ℕ) : adicLevelMap I (le_refl n) = 𝟙 _ := by
  have : Ideal.Quotient.factorPow I (le_refl n) = RingHom.id _ := Ideal.Quotient.ringHom_ext rfl
  rw [adicLevelMap, this, CommRingCat.ofHom_id, Spec.map_id]

def IsAdicFamily {X : Scheme.{u}} (f : ∀ n : ℕ, Spec (.of (R ⧸ I ^ (n + 1))) ⟶ X) : Prop :=
  ∀ n, adicLevelMap I (Nat.le_succ (n + 1)) ≫ f (n + 1) = f n

variable {I}

theorem isAdicFamily_restrict {X : Scheme.{u}} (g : Spec (.of R) ⟶ X) :
    IsAdicFamily I fun n => adicLevelι I (n + 1) ≫ g :=
  fun _ => adicLevelMap_ι_assoc I _ g

theorem IsAdicFamily.of_le {X : Scheme.{u}} {f : ∀ n : ℕ, Spec (.of (R ⧸ I ^ (n + 1))) ⟶ X}
    (hf : IsAdicFamily I f) {m n : ℕ} (h : m ≤ n) :
    adicLevelMap I (Nat.succ_le_succ h) ≫ f n = f m := by
  induction n, h using Nat.le_induction with
  | base => rw [adicLevelMap_self, Category.id_comp]
  | succ n h ih => rw [← ih, ← hf n, adicLevelMap_comp_assoc]

theorem IsAdicFamily.comp {X Y : Scheme.{u}} {f : ∀ n : ℕ, Spec (.of (R ⧸ I ^ (n + 1))) ⟶ X}
    (hf : IsAdicFamily I f) (p : X ⟶ Y) : IsAdicFamily I fun n => f n ≫ p :=
  fun n => by rw [← Category.assoc, hf n]

variable [IsLocalRing R]

theorem ne_top_of_isHausdorff (I : Ideal R) [IsHausdorff I R] : I ≠ ⊤ := by
  rintro rfl
  exact not_subsingleton R (IsHausdorff.subsingleton (R := R) (M := R) ‹_›)

theorem isLocalRing_quotient_pow (hI : I ≠ ⊤) (n : ℕ) : IsLocalRing (R ⧸ I ^ (n + 1)) :=
  have : Nontrivial (R ⧸ I ^ (n + 1)) := Ideal.Quotient.nontrivial_iff.mpr
    (fun h => hI (top_le_iff.mp (h ▸ Ideal.pow_le_self n.succ_ne_zero)))
  IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

theorem adicLevelι_closedPoint (hI : I ≠ ⊤) (n : ℕ) :
    haveI := isLocalRing_quotient_pow hI n
    adicLevelι I (n + 1) (closedPoint (R ⧸ I ^ (n + 1))) = closedPoint R := by
  have := isLocalRing_quotient_pow hI n
  have : IsLocalHom (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))).hom :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  exact Spec_closedPoint

theorem adicLevelMap_closedPoint (hI : I ≠ ⊤) {m n : ℕ} (h : m + 1 ≤ n + 1) :
    haveI := isLocalRing_quotient_pow hI m
    haveI := isLocalRing_quotient_pow hI n
    adicLevelMap I h (closedPoint (R ⧸ I ^ (m + 1))) = closedPoint (R ⧸ I ^ (n + 1)) := by
  have := isLocalRing_quotient_pow hI m
  have := isLocalRing_quotient_pow hI n
  have : IsLocalHom (CommRingCat.ofHom (Ideal.Quotient.factorPow I h)).hom :=
    IsLocalHom.of_surjective _ (Ideal.Quotient.factor_surjective (Ideal.pow_le_pow_right h))
  exact Spec_closedPoint

theorem IsAdicFamily.closedPoint_eq (hI : I ≠ ⊤) {X : Scheme.{u}}
    {f : ∀ n : ℕ, Spec (.of (R ⧸ I ^ (n + 1))) ⟶ X} (hf : IsAdicFamily I f) (n : ℕ) :
    haveI := isLocalRing_quotient_pow hI n
    haveI := isLocalRing_quotient_pow hI 0
    f n (closedPoint (R ⧸ I ^ (n + 1))) = f 0 (closedPoint (R ⧸ I ^ (0 + 1))) := by
  rw [← hf.of_le (Nat.zero_le n)]
  refine Eq.trans ?_ (Scheme.Hom.comp_apply _ _ _).symm
  exact congrArg (f n) (adicLevelMap_closedPoint hI _).symm

theorem IsAdicFamily.range_subset (hI : I ≠ ⊤) {X : Scheme.{u}}
    {f : ∀ n : ℕ, Spec (.of (R ⧸ I ^ (n + 1))) ⟶ X} (hf : IsAdicFamily I f) {U : X.Opens}
    (hU : haveI := isLocalRing_quotient_pow hI 0; f 0 (closedPoint (R ⧸ I ^ (0 + 1))) ∈ U)
    (n : ℕ) : Set.range (f n) ⊆ U :=
  haveI := isLocalRing_quotient_pow hI n
  range_subset_of_closedPoint_mem (f n) (by rwa [hf.closedPoint_eq hI n])

theorem hom_ext_of_isHausdorff (I : Ideal R) [IsHausdorff I R] {X : Scheme.{u}}
    {g g' : Spec (.of R) ⟶ X}
    (h : ∀ n, adicLevelι I (n + 1) ≫ g = adicLevelι I (n + 1) ≫ g') : g = g' := by
  have hI := ne_top_of_isHausdorff I
  have hx : g' (closedPoint R) = g (closedPoint R) := by
    rw [← adicLevelι_closedPoint hI 0]
    refine (Scheme.Hom.comp_apply _ _ _).symm.trans (Eq.trans ?_ (Scheme.Hom.comp_apply _ _ _))
    rw [h]
  obtain ⟨φ, hφ, -⟩ := existsUnique_factor_stalk g rfl
  obtain ⟨φ', hφ', -⟩ := existsUnique_factor_stalk g' hx
  have : φ = φ' := by
    ext1
    apply DFunLike.coe_injective
    apply IsHausdorff.StrictMono.funext' I (a := fun n => n + 1) (strictMono_id.add_const 1)
    intro n a
    have h1 : adicLevelι I (n + 1) ≫ Spec.map φ = adicLevelι I (n + 1) ≫ Spec.map φ' := by
      rw [← cancel_mono (X.fromSpecStalk _), Category.assoc, Category.assoc, hφ, hφ', h]
    rw [← Spec.map_comp, ← Spec.map_comp] at h1
    exact congr($(Spec.map_injective h1).hom a)
  rw [← hφ', ← this, hφ]

theorem existsUnique_of_isAdicFamily [IsAdicComplete I R] {X : Scheme.{u}}
    {f : ∀ n : ℕ, Spec (.of (R ⧸ I ^ (n + 1))) ⟶ X} (hf : IsAdicFamily I f) :
    ∃! g : Spec (.of R) ⟶ X, ∀ n, adicLevelι I (n + 1) ≫ g = f n := by
  have hI := ne_top_of_isHausdorff I
  refine existsUnique_of_exists_of_unique ?_ fun g g' hg hg' =>
    hom_ext_of_isHausdorff I fun n => (hg n).trans (hg' n).symm
  have hloc := isLocalRing_quotient_pow hI
  let x : X := f 0 (closedPoint (R ⧸ I ^ (0 + 1)))
  have hφ := fun n => (existsUnique_factor_stalk (f n) (x := x) (hf.closedPoint_eq hI n)).exists
  choose φ hφ using hφ
  have ha : StrictMono fun n : ℕ => n + 1 := strictMono_id.add_const 1
  have hc : ∀ {m : ℕ}, (Ideal.Quotient.factorPow I (ha.monotone m.le_succ)).comp
      (φ (m + 1)).hom = (φ m).hom := by
    intro m
    have h1 : adicLevelMap I (Nat.le_succ (m + 1)) ≫ Spec.map (φ (m + 1)) = Spec.map (φ m) := by
      rw [← cancel_mono (X.fromSpecStalk _), Category.assoc, hφ, hφ, hf m]
    rw [← Spec.map_comp] at h1
    exact congr($(Spec.map_injective h1).hom)
  refine ⟨Spec.map (CommRingCat.ofHom
    (IsAdicComplete.StrictMono.liftRingHom I ha (fun n => (φ n).hom) hc)) ≫ X.fromSpecStalk x,
    fun n => ?_⟩
  rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp,
    IsAdicComplete.StrictMono.mk_comp_liftRingHom I ha (fun n => (φ n).hom) hc (n := n)]
  exact hφ n

theorem existsUnique_over_of_isAdicFamily [IsAdicComplete I R] {X S : Scheme.{u}}
    (s : Spec (.of R) ⟶ S) (p : X ⟶ S)
    {f : ∀ n : ℕ, Spec (.of (R ⧸ I ^ (n + 1))) ⟶ X} (hf : IsAdicFamily I f)
    (hs : ∀ n, f n ≫ p = adicLevelι I (n + 1) ≫ s) :
    ∃! g : Spec (.of R) ⟶ X, g ≫ p = s ∧ ∀ n, adicLevelι I (n + 1) ≫ g = f n := by
  obtain ⟨g, hg, hu⟩ := existsUnique_of_isAdicFamily hf
  refine ⟨g, ⟨hom_ext_of_isHausdorff I fun n => ?_, hg⟩, fun g' hg' => hu g' hg'.2⟩
  rw [← Category.assoc, hg, hs]

variable (I)

omit [IsLocalRing R] in

noncomputable def adicRestrict (X : Scheme.{u}) (g : Spec (.of R) ⟶ X) :
    {f : ∀ n : ℕ, Spec (.of (R ⧸ I ^ (n + 1))) ⟶ X // IsAdicFamily I f} :=
  ⟨fun n => adicLevelι I (n + 1) ≫ g, isAdicFamily_restrict g⟩

omit [IsLocalRing R] in

noncomputable def adicRestrictOver {X S : Scheme.{u}} (s : Spec (.of R) ⟶ S) (p : X ⟶ S)
    (g : {g : Spec (.of R) ⟶ X // g ≫ p = s}) :
    {f : ∀ n : ℕ, Spec (.of (R ⧸ I ^ (n + 1))) ⟶ X //
      IsAdicFamily I f ∧ ∀ n, f n ≫ p = adicLevelι I (n + 1) ≫ s} :=
  ⟨fun n => adicLevelι I (n + 1) ≫ g.1, isAdicFamily_restrict g.1,
    fun n => by rw [Category.assoc, g.2]⟩

end Limit

end GlobalTheory
