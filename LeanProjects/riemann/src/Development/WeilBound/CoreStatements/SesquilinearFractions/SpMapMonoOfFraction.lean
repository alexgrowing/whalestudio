import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsTransition
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl

noncomputable section

namespace PositivityTheory.Xgf.BaseChangeTangents

section Comb

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {R : Type} [CommRing R] {x : Sp R ⟶ S}

theorem isComb_iff {n : ℕ} (c : Fin n → R) (v : Fin n → (epsAt x ⟶ G)) (w : epsAt x ⟶ G) :
    IsComb c v w ↔ w = (List.ofFn fun i => LieTangent.epsScale x (c i) ≫ v i).prod := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine congrArg (fun f => (List.ofFn f).prod) (funext fun i => ?_)
    apply Over.OverMorphism.ext
    rw [hu i]
    rfl
  · intro hw
    exact ⟨_, fun i => rfl, hw⟩

theorem prod_pt {E : Type} [AddCommGroup E] [Module R E] (M : LieModel G x E) :
    ∀ {n : ℕ} (c : Fin n → R) (z : Fin n → E),
      (List.ofFn fun i => LieTangent.epsScale x (c i) ≫ M.pt (z i)).prod = M.pt (∑ i, c i • z i)
  | 0, c, z => by simp [LieModel.pt_zero]
  | n + 1, c, z => by
    rw [List.ofFn_succ, List.prod_cons, prod_pt M (fun i => c i.succ) (fun i => z i.succ), Fin.sum_univ_succ, M.add,
      LieModel.pt_smul]

end Comb

section BC

variable {V K : Type} [CommRing V] [CommRing K] (VK : V →+* K) {G : Over (Sp V)} [GrpObj G] {G' : Over (Sp K)}
  [GrpObj G'] {φ' : G'.left ⟶ G.left} (h : IsGrpPullback G' G (spMap VK) φ')

private theorem bc_cond_lemma :
    spMap (dualMap VK) ≫ (epsAt (𝟙 (Sp V))).hom = (epsAt (𝟙 (Sp K))).hom ≫ spMap VK := by
  simp only [epsAt, Over.mk_hom, Category.comp_id, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_
  · simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  · simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem bc_cond (w : epsAt (𝟙 (Sp V)) ⟶ G) :
    (spMap (dualMap VK) ≫ w.left) ≫ G.hom = (epsAt (𝟙 (Sp K))).hom ≫ spMap VK := by
  rw [Category.assoc, Over.w]
  exact bc_cond_lemma VK

def bcTan (w : epsAt (𝟙 (Sp V)) ⟶ G) : epsAt (𝟙 (Sp K)) ⟶ G' :=
  Over.homMk (h.1.lift (spMap (dualMap VK) ≫ w.left) (epsAt (𝟙 (Sp K))).hom (bc_cond VK w)) (h.1.lift_snd _ _ _)

theorem bcTan_left (w : epsAt (𝟙 (Sp V)) ⟶ G) : (bcTan VK h w).left ≫ φ' = spMap (dualMap VK) ≫ w.left :=
  h.1.lift_fst _ _ _

theorem bcTan_unique (w : epsAt (𝟙 (Sp V)) ⟶ G) (s : epsAt (𝟙 (Sp K)) ⟶ G')
    (hs : s.left ≫ φ' = spMap (dualMap VK) ≫ w.left) : s = bcTan VK h w := by
  apply Over.OverMorphism.ext
  apply h.1.hom_ext
  · rw [hs, bcTan_left]
  · rw [Over.w s, Over.w (bcTan VK h w)]

theorem bcTan_mul (w w' : epsAt (𝟙 (Sp V)) ⟶ G) :
    bcTan VK h (w * w') = bcTan VK h w * bcTan VK h w' := by
  symm
  apply bcTan_unique
  let g : Over.mk ((epsAt (𝟙 (Sp K))).hom ≫ spMap VK) ⟶ epsAt (𝟙 (Sp V)) :=
    Over.homMk (spMap (dualMap VK)) (bc_cond_lemma VK)
  have := h.2 (epsAt (𝟙 (Sp K))) (bcTan VK h w) (bcTan VK h w') (g ≫ w) (g ≫ w')
    (bcTan_left VK h w).symm (bcTan_left VK h w').symm
  rw [← this, ← MonObj.comp_mul]
  rfl

theorem bcTan_one : bcTan VK h (1 : epsAt (𝟙 (Sp V)) ⟶ G) = 1 := by
  have := bcTan_mul VK h 1 1
  rw [_root_.mul_one] at this
  exact mul_eq_left.1 this.symm

def bcHom : (epsAt (𝟙 (Sp V)) ⟶ G) →* (epsAt (𝟙 (Sp K)) ⟶ G') where
  toFun := bcTan VK h
  map_one' := bcTan_one VK h
  map_mul' := bcTan_mul VK h

private theorem scale_lemma (c : V) :
    (GlobalTheory.CompanionTheory.Ar.epsMul (VK c)).comp (dualMap VK) = (dualMap VK).comp (GlobalTheory.CompanionTheory.Ar.epsMul c) := by
  refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_
  · simp [dualMap, GlobalTheory.CompanionTheory.Ar.epsMul]
  · simp [dualMap, GlobalTheory.CompanionTheory.Ar.epsMul, smul_eq_mul, map_mul, mul_comm]

theorem bcTan_scale (c : V) (w : epsAt (𝟙 (Sp V)) ⟶ G) :
    bcTan VK h (LieTangent.epsScale _ c ≫ w) = LieTangent.epsScale _ (VK c) ≫ bcTan VK h w := by
  symm
  apply bcTan_unique
  rw [Over.comp_left, Over.comp_left, Category.assoc, bcTan_left]
  simp only [LieTangent.epsScale, Over.homMk_left, spMap, ← Category.assoc, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, scale_lemma]

theorem bcTan_comb {n : ℕ} (c : Fin n → V) (w : Fin n → (epsAt (𝟙 (Sp V)) ⟶ G)) :
    bcTan VK h (List.ofFn fun i => LieTangent.epsScale _ (c i) ≫ w i).prod =
      (List.ofFn fun i => LieTangent.epsScale _ (VK (c i)) ≫ bcTan VK h (w i)).prod := by
  induction n with
  | zero =>
    simp only [List.ofFn_zero, List.prod_nil]
    exact bcTan_one VK h
  | succ n ih =>
    simp only [List.ofFn_succ, List.prod_cons]
    rw [bcTan_mul, bcTan_scale, ih (fun i => c i.succ) (fun i => w i.succ)]

private theorem prime_lemma_2 {R : Type} [CommRing R] (p : PrimeSpectrum (DualNumber R)) :
    PrimeSpectrum.comap (TrivSqZeroExt.fstHom R R R).toRingHom
      (PrimeSpectrum.comap (algebraMap R (DualNumber R)) p) = p := by
  ext x
  simp only [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
  show algebraMap R (DualNumber R) x.fst ∈ p.asIdeal ↔ x ∈ p.asIdeal
  have hn : (x - algebraMap R (DualNumber R) x.fst) ^ 2 = 0 := by
    ext <;> simp [pow_two, TrivSqZeroExt.algebraMap_eq_inl]
  have hmem : x - algebraMap R (DualNumber R) x.fst ∈ p.asIdeal :=
    p.isPrime.mem_of_pow_mem 2 (by rw [hn]; exact p.asIdeal.zero_mem)
  constructor
  · intro hx
    simpa using p.asIdeal.add_mem hmem hx
  · intro hx
    simpa using p.asIdeal.sub_mem hx hmem

private theorem cancel_lemma {R B : Type} [CommRing R] [CommRing B] {X : Scheme.{0}} (j : R →+* B)
    (hj : Function.Injective j) (a b : Spec (CommRingCat.of R) ⟶ X) (c : Spec (CommRingCat.of R))
    (hc : a c = b c) (hsp : ∀ p : Spec (CommRingCat.of R), p ⤳ c)
    (e : Spec.map (CommRingCat.ofHom j) ≫ a = Spec.map (CommRingCat.ofHom j) ≫ b) : a = b := by
  obtain ⟨U, hU, hcU, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
    (show a c ∈ (⊤ : X.Opens) from trivial)
  haveI : IsAffine U := hU
  have ha : Set.range a ⊆ Set.range (Scheme.Opens.ι U) := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨p, rfl⟩
    exact ((hsp p).map a.continuous).mem_open U.isOpen hcU
  have hb : Set.range b ⊆ Set.range (Scheme.Opens.ι U) := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨p, rfl⟩
    exact ((hsp p).map b.continuous).mem_open U.isOpen (hc ▸ hcU)
  rw [← IsOpenImmersion.lift_fac (Scheme.Opens.ι U) a ha, ← IsOpenImmersion.lift_fac (Scheme.Opens.ι U) b hb]
  congr 1
  apply ext_of_isAffine
  have e' : Spec.map (CommRingCat.ofHom j) ≫ IsOpenImmersion.lift (Scheme.Opens.ι U) a ha =
      Spec.map (CommRingCat.ofHom j) ≫ IsOpenImmersion.lift (Scheme.Opens.ι U) b hb := by
    rw [← cancel_mono (Scheme.Opens.ι U), Category.assoc, Category.assoc, IsOpenImmersion.lift_fac,
      IsOpenImmersion.lift_fac, e]
  haveI : Mono (CommRingCat.ofHom j) := ConcreteCategory.mono_of_injective _ hj
  have hnat := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom j)
  haveI : Mono ((Spec.map (CommRingCat.ofHom j)).appTop ≫ (Scheme.ΓSpecIso _).hom) := by
    rw [hnat]
    infer_instance
  haveI : Mono (Spec.map (CommRingCat.ofHom j)).appTop := mono_of_mono _ (Scheme.ΓSpecIso _).hom
  rw [← cancel_mono (Spec.map (CommRingCat.ofHom j)).appTop]
  have := congrArg Scheme.Hom.appTop e'
  simpa using this

theorem bcTan_inj [IsLocalRing V] (hVK : Function.Injective VK) {w w' : epsAt (𝟙 (Sp V)) ⟶ G}
    (hw : IsTanAt G _ w) (hw' : IsTanAt G _ w') (e : bcTan VK h w = bcTan VK h w') : w = w' := by
  have hl : spMap (dualMap VK) ≫ w.left = spMap (dualMap VK) ≫ w'.left := by
    rw [← bcTan_left VK h w, ← bcTan_left VK h w', e]
  have ht := hw.trans hw'.symm
  apply Over.OverMorphism.ext
  refine cancel_lemma (dualMap VK) (LieTangent.dualMap_injective hVK) w.left w'.left
    (PrimeSpectrum.comap (TrivSqZeroExt.fstHom V V V).toRingHom (IsLocalRing.closedPoint V)) ?_ ?_ hl
  · exact congrArg (fun f => f.base (IsLocalRing.closedPoint V)) ht
  · intro p
    rw [← prime_lemma_2 p]
    exact (IsLocalRing.specializes_closedPoint _).map (PrimeSpectrum.continuous_comap _)

theorem bcTan_act (α' : G' ⟶ G') (α : G ⟶ G) (hα : α'.left ≫ φ' = φ' ≫ α.left) (w : epsAt (𝟙 (Sp V)) ⟶ G) :
    bcTan VK h (w ≫ α) = bcTan VK h w ≫ α' := by
  symm
  apply bcTan_unique
  simp only [Over.comp_left, Category.assoc, hα]
  rw [← Category.assoc, bcTan_left, Category.assoc]

omit [GrpObj G] [GrpObj G'] in
theorem spMap_mono_of_fraction [IsDomain V] [Algebra V K] [IsFractionRing V K] (hVK : VK = algebraMap V K)
    {A : Type} [CommRing A] (f₁ f₂ : Sp A ⟶ Sp K) (e : f₁ ≫ spMap VK = f₂ ≫ spMap VK) : f₁ = f₂ := by
  subst hVK
  haveI : Epi (CommRingCat.ofHom (algebraMap V K)) := IsLocalization.epi (nonZeroDivisors V) K
  haveI : Mono (Scheme.Spec.map (CommRingCat.ofHom (algebraMap V K)).op) := inferInstance
  exact (cancel_mono (Scheme.Spec.map (CommRingCat.ofHom (algebraMap V K)).op)).1 e

theorem eq_bcTan_left [IsDomain V] [Algebra V K] [IsFractionRing V K] (hVK : VK = algebraMap V K)
    (w : epsAt (𝟙 (Sp V)) ⟶ G) (s : Sp (DualNumber K) ⟶ G'.left)
    (hs : s ≫ φ' = spMap (dualMap VK) ≫ w.left) : s = (bcTan VK h w).left := by
  apply h.1.hom_ext
  · rw [hs, bcTan_left]
  · apply spMap_mono_of_fraction VK hVK
    rw [Category.assoc, ← h.1.w, ← Category.assoc, hs, bc_cond, Over.w]

end BC

section Push

variable {S : Scheme.{0}} {K : Type} [CommRing K] {G : Over S} [GrpObj G] {G' : Over (Sp K)} [GrpObj G']
  {y₀ : Sp K ⟶ S} {φ : G'.left ⟶ G.left} (hp : IsGrpPullback G' G y₀ φ)

include hp

theorem push_cond (s : epsAt (𝟙 (Sp K)) ⟶ G') : (s.left ≫ φ) ≫ G.hom = (epsAt y₀).hom := by
  rw [Category.assoc, hp.1.w, ← Category.assoc, Over.w s]
  show (Spec.map (CommRingCat.ofHom (algebraMap K (DualNumber K))) ≫ 𝟙 _) ≫ y₀ = _
  rw [Category.comp_id]
  rfl

def push (s : epsAt (𝟙 (Sp K)) ⟶ G') : epsAt y₀ ⟶ G := Over.homMk (s.left ≫ φ) (push_cond hp s)

theorem push_left (s : epsAt (𝟙 (Sp K)) ⟶ G') : (push hp s).left = s.left ≫ φ := rfl

theorem push_mul (s s' : epsAt (𝟙 (Sp K)) ⟶ G') : push hp (s * s') = push hp s * push hp s' := by
  let g : Over.mk ((epsAt (𝟙 (Sp K))).hom ≫ y₀) ⟶ epsAt y₀ := Over.homMk (𝟙 _) (by simp [epsAt])
  have := hp.2 (epsAt (𝟙 (Sp K))) s s' (g ≫ push hp s) (g ≫ push hp s') (by simp [g, push_left])
    (by simp [g, push_left])
  rw [← MonObj.comp_mul] at this
  apply Over.OverMorphism.ext
  rw [push_left, ← this]
  simp [g]

theorem push_inj {s s' : epsAt (𝟙 (Sp K)) ⟶ G'} (e : push hp s = push hp s') : s = s' := by
  apply Over.OverMorphism.ext
  apply hp.1.hom_ext
  · exact congrArg (·.left) e
  · rw [Over.w s, Over.w s']

theorem push_scale (c : K) (s : epsAt (𝟙 (Sp K)) ⟶ G') :
    push hp (LieTangent.epsScale _ c ≫ s) = LieTangent.epsScale _ c ≫ push hp s := by
  apply Over.OverMorphism.ext
  rw [push_left, Over.comp_left, Over.comp_left, push_left, Category.assoc]
  rfl

theorem push_act (α' : G' ⟶ G') (α : G ⟶ G) (hα : α'.left ≫ φ = φ ≫ α.left) (s : epsAt (𝟙 (Sp K)) ⟶ G') :
    push hp (s ≫ α') = push hp s ≫ α := by
  apply Over.OverMorphism.ext
  rw [push_left, Over.comp_left, Over.comp_left, push_left, Category.assoc, hα, Category.assoc]

def pushHom : (epsAt (𝟙 (Sp K)) ⟶ G') →* (epsAt y₀ ⟶ G) where
  toFun := push hp
  map_one' := by
    have := push_mul hp 1 1
    rw [_root_.mul_one] at this
    exact mul_eq_left.1 this.symm
  map_mul' := push_mul hp

theorem push_comb {n : ℕ} (c : Fin n → K) (w : Fin n → (epsAt (𝟙 (Sp K)) ⟶ G')) :
    push hp (List.ofFn fun i => LieTangent.epsScale _ (c i) ≫ w i).prod =
      (List.ofFn fun i => LieTangent.epsScale _ (c i) ≫ push hp (w i)).prod := by
  induction n with
  | zero =>
    simp only [List.ofFn_zero, List.prod_nil]
    exact (pushHom hp).map_one
  | succ n ih =>
    simp only [List.ofFn_succ, List.prod_cons]
    rw [push_mul, push_scale, ih (fun i => c i.succ) (fun i => w i.succ)]

end Push

end PositivityTheory.Xgf.BaseChangeTangents
