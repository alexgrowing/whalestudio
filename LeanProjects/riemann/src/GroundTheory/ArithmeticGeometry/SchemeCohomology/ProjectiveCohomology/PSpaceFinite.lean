import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.TwistingSheaf
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology
import GroundTheory.ArithmeticGeometry.SchemeCohomology.CechNaturality.NaturalLeray
import GroundTheory.ArithmeticGeometry.SchemeCohomology.CechNaturality.Ordered
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits MonoidalCategory
  MvPolynomial

universe w' u

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

section General

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

lemma ι_appTop_toSpecZero (z : 𝒜 0) :
    (Proj.basicOpen 𝒜 1).ι.appTop ((Proj.toSpecZero 𝒜).appTop ((Scheme.ΓSpecIso _).inv z)) =
      (Proj.basicOpen 𝒜 1).topIso.inv
        (Proj.awayToSection 𝒜 1 (HomogeneousLocalization.fromZeroRingHom 𝒜 _ z)) := by
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop]
  have h1 : (Proj.basicOpen 𝒜 1).ι ≫ (Proj 𝒜).topIso.inv ≫
      ((Proj 𝒜).isoOfEq (Proj.basicOpen_one 𝒜)).inv = 𝟙 _ := by
    rw [← cancel_mono (Proj.basicOpen 𝒜 1).ι]
    simp
  have h : (Proj.basicOpen 𝒜 1).ι ≫ Proj.toSpecZero 𝒜 = Proj.basicOpenToSpec 𝒜 1 ≫
      Spec.map (CommRingCat.ofHom (HomogeneousLocalization.fromZeroRingHom 𝒜 _)) := by
    rw [Proj.toSpecZero, reassoc_of% h1]
  rw [h, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
    ← CommRingCat.comp_apply (Scheme.ΓSpecIso _).inv, ← Scheme.ΓSpecIso_inv_naturality,
    CommRingCat.comp_apply, Scheme.Hom.appTop, Proj.basicOpenToSpec_app_top]
  simp
  rfl

def projValue {U : (Proj 𝒜).Opens} (s : Γ(Proj 𝒜, U)) (x : Proj 𝒜) (hx : x ∈ U) :
    ProjTwist.Loc 𝒜 x :=
  ((show (ProjectiveSpectrum.Proj.structureSheaf 𝒜).1.obj (op U) from s).1 ⟨x, hx⟩).val

lemma projValue_toSpecZero (z : 𝒜 0) (x : Proj 𝒜) :
    projValue 𝒜 ((Proj.toSpecZero 𝒜).appTop ((Scheme.ΓSpecIso _).inv z)) x trivial =
      algebraMap A _ (z : A) := by
  have hx : x ∈ Proj.basicOpen 𝒜 1 := by rw [Proj.basicOpen_one]; trivial
  have hx' : x ∈ (Proj.basicOpen 𝒜 1).ι ''ᵁ ⊤ := by rw [Scheme.Opens.ι_image_top]; exact hx
  have e := congrArg (fun s => projValue 𝒜 (U := (Proj.basicOpen 𝒜 1).ι ''ᵁ ⊤) s x hx')
    (ι_appTop_toSpecZero 𝒜 z)
  simp only [Scheme.Opens.ι_appTop, Scheme.Opens.topIso_inv] at e
  have e' : projValue 𝒜 ((Proj.toSpecZero 𝒜).appTop ((Scheme.ΓSpecIso _).inv z)) x trivial =
      projValue 𝒜 (Proj.awayToSection 𝒜 1 (HomogeneousLocalization.fromZeroRingHom 𝒜 _ z)) x hx := e
  refine e'.trans ?_
  unfold projValue
  erw [ProjectiveSpectrum.Proj.awayToSection_apply]
  change (IsLocalization.map _ (RingHom.id A) _) (HomogeneousLocalization.mk _).val = _
  rw [HomogeneousLocalization.val_mk, Localization.mk_eq_mk', IsLocalization.map_mk',
    IsLocalization.mk'_eq_iff_eq_mul]
  simp

end General

namespace ProjSpace

variable {A : Type u} [CommRing A] {n : ℕ}

attribute [local instance] algebraOfOver

lemma algebraMap_eq_toSpecZero (a : A) : algebraMap A Γ(projectiveSpace A n, ⊤) a =
    (Proj.toSpecZero (grading A n)).appTop
      ((Scheme.ΓSpecIso _).inv (algebraMap A (grading A n 0) a)) := by
  change (toSpecBase A n).appTop ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a) = _
  rw [toSpecBase, Scheme.Hom.comp_appTop, ← CommRingCat.comp_apply, ← Category.assoc,
    ← Scheme.ΓSpecIso_inv_naturality]
  rfl

lemma projValue_algebraMap (a : A) (x : projectiveSpace A n) :
    projValue (grading A n) (algebraMap A Γ(projectiveSpace A n, ⊤) a) x trivial =
      algebraMap (MvPolynomial (Fin (n + 1)) A) _ (C a) := by
  rw [algebraMap_eq_toSpecZero, projValue_toSpecZero]
  rfl

def smulLDeg (a : A) {s : Set (Fin (n + 1))} {k : ℤ} (ℓ : LDeg A s k) : LDeg A s k :=
  ⟨a • ℓ.1, fun m hm => ℓ.2 m fun h => hm (by rw [AddMonoidAlgebra.coeff_smul_apply, h, smul_zero])⟩

@[simp] lemma smulLDeg_val (a : A) {s : Set (Fin (n + 1))} {k : ℤ} (ℓ : LDeg A s k) :
    (smulLDeg a ℓ).1 = a • ℓ.1 := rfl

lemma toLaurent_C (a : A) : toLaurent A n (C a) = AddMonoidAlgebra.single 0 a := by
  rw [MvPolynomial.C_apply, toLaurent_monomial, map_zero]

lemma single_zero_mul_eq_smul (a : A) (ℓ : Laurent A n) :
    AddMonoidAlgebra.single 0 a * ℓ = a • ℓ := by
  apply AddMonoidAlgebra.coeff_injective
  ext m
  rw [AddMonoidAlgebra.coeff_single_zero_mul, AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul]

lemma algebraMap_C_mem_awayDeg {p : ℕ} (i : Fin (p + 1) → Fin (n + 1)) (a : A) :
    algebraMap (MvPolynomial (Fin (n + 1)) A) (Localization.Away (xprod (A := A) i)) (C a) ∈
      ProjTwist.awayDeg (grading A n) (xprod_mem i) (Nat.succ_pos p) 0 := by
  have h := ProjTwist.mk_mem_awayDeg (xprod_mem i) (Nat.succ_pos p) (k := 0) (n := 0)
    (j := 0) (a := C a) (MvPolynomial.isHomogeneous_C _ a) (by simp)
  have e : ProjTwist.fpow (xprod (A := A) i) 0 = 1 := Subtype.ext (pow_zero _)
  rwa [e, Localization.mk_one_eq_algebraMap] at h

lemma theta_smulLDeg {p : ℕ} (i : Fin (p + 1) → Fin (n + 1)) (k : ℤ) (a : A)
    (ℓ : LDeg A (Set.range i) k) :
    theta i k (smulLDeg a ℓ) =
      (restrictTop (inter (cover A n) i) (algebraMap A Γ(projectiveSpace A n, ⊤) a) •
        (show Γ(twistingSheaf (grading A n) k, inter (cover A n) i) from theta i k ℓ)) := by
  set z := (awayDegEquiv (A := A) i k).symm ℓ with hz
  have hmem : algebraMap (MvPolynomial (Fin (n + 1)) A) (Localization.Away (xprod (A := A) i)) (C a) *
      z.1 ∈ ProjTwist.awayDeg (grading A n) (xprod_mem i) (Nat.succ_pos p) k := by
    have := ProjTwist.mul_mem_awayDeg (xprod_mem i) (Nat.succ_pos p)
      (algebraMap_C_mem_awayDeg i a) z.2
    rwa [zero_add] at this
  have h2 : (awayDegEquiv (A := A) i k).symm (smulLDeg a ℓ) = ⟨_, hmem⟩ := by
    rw [AddEquiv.symm_apply_eq]
    apply Subtype.ext
    rw [awayDegEquiv_apply, map_mul, awayToLaurent_algebraMap, smulLDeg_val, toLaurent_C,
      single_zero_mul_eq_smul]
    congr 1
    rw [← awayDegEquiv_apply, hz, AddEquiv.apply_symm_apply]
  apply ProjTwist.ext
  funext x
  rw [ProjTwist.val_smul, val_theta, val_theta, h2]
  change ProjTwist.locMap x.1 _ (_ * _) = _
  rw [map_mul]
  congr 1
  exact (ProjTwist.locMap_algebraMap (𝒜 := grading A n) x.1 _ (C a)).trans
    (projValue_algebraMap a x.1).symm

lemma lval_push_smul {k : ℤ} {p : ℕ} (a : A) (σ : Cochain (twistAb A n k) (cover A n) p)
    (i : Fin (p + 1) → Fin (n + 1)) :
    lval (push (cover A n) (smulAbRingHom (twistingSheaf (grading A n) k)
      (algebraMap A Γ(projectiveSpace A n, ⊤) a)).hom p σ) i = a • lval σ i := by
  have h : push (cover A n) (smulAbRingHom (twistingSheaf (grading A n) k)
      (algebraMap A Γ(projectiveSpace A n, ⊤) a)).hom p σ i =
      theta i k (smulLDeg a ⟨lval σ i, lval_mem σ i⟩) := by
    rw [theta_smulLDeg, theta_lval]
    rfl
  rw [lval, h, AddEquiv.symm_apply_apply]
  rfl

section Leray

variable [HasExt.{w'} (Sheaf (Opens.grothendieckTopology (projectiveSpace A n).toTopCat) AddCommGrpCat.{u})]

def cechHLinearEquivTwist (k : ℤ) (p : ℕ) :
    cechH (twistAb A n k) (cover A n) p ≃ₗ[A]
      Sheaf.H.{w'} (modulesAb (twistingSheaf (grading A n) k)) p :=
  (cechHEquiv (isCoverSystem_affineUnder (fun j : Fin (n + 1) => (X j : MvPolynomial (Fin (n + 1)) A)))
    (cover A n) iSup_stdOpen (fun {_} i => ⟨isAffineOpen_inter i, i 0, inter_le _ i 0⟩) p _
    (goodAcyclic_twist _ (fun j => X_mem j) k)).toLinearEquiv fun a x => by
      rw [cechH.smul_def, H.smul_def]
      exact cechHEquiv_naturality _ (cover A n) iSup_stdOpen
        (fun {_} i => ⟨isAffineOpen_inter i, i 0, inter_le _ i 0⟩) p _ _
        (smulAbRingHom (twistingSheaf (grading A n) k) (algebraMap A Γ(projectiveSpace A n, ⊤) a)) x

end Leray

lemma smul_cls {k : ℤ} {p : ℕ} (a : A) (σ : Cochain (twistAb A n k) (cover A n) p)
    (hσ : d _ _ p σ = 0) :
    a • cls σ hσ = cls (push (cover A n) (smulAbRingHom (twistingSheaf (grading A n) k)
      (algebraMap A Γ(projectiveSpace A n, ⊤) a)).hom p σ)
        (by rw [← push_d, hσ, map_zero]) :=
  cechHMap_cls (cover A n) _ σ hσ

instance finite_negMon (m : ℕ) (k : ℤ) : Finite (NegMon m k) := by
  refine Finite.of_injective (β := Fin (m + 1) → Set.Icc k (-1))
    (fun e j => ⟨e.1 j, ?_, ?_⟩) fun e e' h => Subtype.ext (funext fun j => ?_)
  · have hsum := Finset.add_sum_erase Finset.univ e.1 (Finset.mem_univ j)
    have hle : ∑ i ∈ Finset.univ.erase j, e.1 i ≤ 0 :=
      Finset.sum_nonpos fun i _ => (e.2.1 i).le
    rw [e.2.2] at hsum
    omega
  · have := e.2.1 j
    omega
  · exact congrArg Subtype.val (congrFun h j)

theorem finite_cechH_top (k : ℤ) (m : ℕ) :
    Module.Finite A (cechH (twistAb A (m + 1) k) (cover A (m + 1)) (m + 1)) := by
  refine Module.Finite.equiv ((AddEquiv.ofBijective _
    (topMap_bijective (A := A) (k := k) (m := m))).toLinearEquiv fun a c => ?_).symm
  obtain ⟨σ, hσ, rfl⟩ := exists_cls c
  change topMap (a • cls σ hσ) = a • topMap (cls σ hσ)
  rw [smul_cls, topMap_cls, topMap_cls]
  ext e
  rw [topCoeff_apply, Finsupp.smul_apply, topCoeff_apply, lval_push_smul,
    AddMonoidAlgebra.coeff_smul_apply]

def zeroL (k : ℤ) : cechH (twistAb A n k) (cover A n) 0 →+ Laurent A n :=
  QuotientAddGroup.lift _
    ((AddMonoidHom.mk' (fun σ : Cochain (twistAb A n k) (cover A n) 0 => lval σ fun _ => 0)
      fun σ τ => lval_add σ τ _).comp (cocycles _ _ 0).subtype) (by
    intro x hx
    rw [AddSubgroup.mem_addSubgroupOf, coboundaries_zero, AddSubgroup.mem_bot] at hx
    simp [hx])

lemma zeroL_cls {k : ℤ} (σ : Cochain (twistAb A n k) (cover A n) 0) (hσ : d _ _ 0 σ = 0) :
    zeroL k (cls σ hσ) = lval σ fun _ => 0 := rfl

lemma zeroL_smul {k : ℤ} (a : A) (c : cechH (twistAb A n k) (cover A n) 0) :
    zeroL k (a • c) = a • zeroL k c := by
  obtain ⟨σ, hσ, rfl⟩ := exists_cls c
  rw [smul_cls, zeroL_cls, zeroL_cls, lval_push_smul]

lemma zeroL_injective {k : ℤ} : Function.Injective (zeroL (A := A) (n := n) k) := by
  rw [injective_iff_map_eq_zero]
  intro c hc
  obtain ⟨σ, hσ, rfl⟩ := exists_cls c
  rw [zeroL_cls] at hc
  have : σ = 0 := cochain_ext fun j => by
    rw [lval_eq_of_cocycle σ hσ j (fun _ => 0), hc, lval_zero]
  subst this
  exact cls_zero

lemma zeroL_mem {k : ℤ} (c : cechH (twistAb A n k) (cover A n) 0) (j : Fin (n + 1)) :
    zeroL k c ∈ LDeg A {j} k := by
  obtain ⟨σ, hσ, rfl⟩ := exists_cls c
  rw [zeroL_cls, lval_eq_of_cocycle σ hσ (fun _ => 0) (fun _ => j)]
  have := lval_mem σ (fun _ => j)
  rwa [range_const_fin_one] at this

lemma exists_zeroL_eq {k : ℤ} (ℓ : Laurent A n) (hℓ : ∀ j, ℓ ∈ LDeg A {j} k) :
    ∃ c, zeroL k c = ℓ := by
  let σ : Cochain (twistAb A n k) (cover A n) 0 :=
    ofL fun i => ⟨ℓ, by rw [range_const_fin_one]; exact hℓ (i 0)⟩
  have hσ : d _ _ 0 σ = 0 := by
    refine cochain_ext fun i => ?_
    rw [lval_d, lval_zero, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_zero]
    simp [σ]
  exact ⟨cls σ hσ, by rw [zeroL_cls]; simp [σ]⟩

lemma allowed_bound {k : ℤ} {m : Fin (n + 1) → ℤ} (h : ∀ j, Allowed {j} k m) (j : Fin (n + 1)) :
    m j ∈ Set.Icc (-|k|) |k| := by
  by_cases hn : ∃ j', j' ≠ j
  · obtain ⟨j', hj'⟩ := hn
    have hnn : ∀ i, 0 ≤ m i := fun i => by
      by_cases hi : i = j
      · subst hi
        exact (h j').2 i (by simpa [eq_comm] using hj'.symm)
      · exact (h j).2 i (by simpa using hi)
    have hle : m j ≤ ∑ i, m i := Finset.single_le_sum (fun i _ => hnn i) (Finset.mem_univ j)
    rw [(h j).1] at hle
    have := hnn j
    constructor <;> [skip; skip] <;> cases abs_cases k <;> omega
  · push Not at hn
    have hs : ∑ i, m i = m j := Finset.sum_eq_single j (fun i _ hi => absurd (hn i) hi) (by simp)
    rw [(h j).1] at hs
    constructor <;> cases abs_cases k <;> omega

lemma finite_allowed (k : ℤ) : {m : Fin (n + 1) → ℤ | ∀ j, Allowed {j} k m}.Finite :=
  (Set.Finite.pi (t := fun _ : Fin (n + 1) => Set.Icc (-|k|) |k|)
    fun _ => Set.finite_Icc _ _).subset fun m hm => by
      simp only [Set.mem_pi, Set.mem_univ, true_implies]
      exact fun j => allowed_bound hm j

theorem finite_cechH_zero (k : ℤ) : Module.Finite A (cechH (twistAb A n k) (cover A n) 0) := by
  let ζ : cechH (twistAb A n k) (cover A n) 0 →ₗ[A] Laurent A n :=
    { zeroL k with map_smul' := zeroL_smul }
  have hζ : Function.Injective ζ := zeroL_injective
  let T : Set (Laurent A n) :=
    (fun m => AddMonoidAlgebra.single m (1 : A)) '' {m | ∀ j, Allowed {j} k m}
  have hrange : LinearMap.range ζ = Submodule.span A T := by
    apply le_antisymm
    · rintro _ ⟨c, rfl⟩
      have hmem := zeroL_mem (A := A) c
      set ℓ := zeroL k c
      have hℓ : ℓ = ∑ m ∈ ℓ.coeff.support, ℓ.coeff m • AddMonoidAlgebra.single m (1 : A) := by
        apply AddMonoidAlgebra.coeff_injective
        ext m
        rw [coeff_sum']
        simp only [AddMonoidAlgebra.coeff_smul_apply, AddMonoidAlgebra.coeff_single,
          Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
        rw [Finset.sum_ite_eq']
        split_ifs with hm
        · rfl
        · exact Finsupp.notMem_support_iff.mp hm
      change ℓ ∈ _
      rw [hℓ]
      refine Submodule.sum_mem _ fun m hm => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
      exact ⟨m, fun j => hmem j m (Finsupp.mem_support_iff.mp hm), rfl⟩
    · rw [Submodule.span_le]
      rintro _ ⟨m, hm, rfl⟩
      obtain ⟨c, hc⟩ := exists_zeroL_eq (A := A) (k := k) _ fun j => single_mem_LDeg (hm j) 1
      exact ⟨c, hc⟩
  have : Module.Finite A (LinearMap.range ζ) := by
    rw [Module.Finite.iff_fg, hrange]
    exact Submodule.fg_span ((finite_allowed k).image _)
  exact Module.Finite.equiv (LinearEquiv.ofInjective ζ hζ).symm

theorem finite_cechH (k : ℤ) (p : ℕ) : Module.Finite A (cechH (twistAb A n k) (cover A n) p) := by
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · exact finite_cechH_zero k
  rcases lt_trichotomy p n with h | rfl | h
  · have := subsingleton_cechH_of_lt (A := A) (k := k) hp h
    infer_instance
  · obtain ⟨m, rfl⟩ : ∃ m, p = m + 1 := ⟨p - 1, by omega⟩
    exact finite_cechH_top k m
  · have := subsingleton_cechH_of_gt (A := A) (k := k) h
    infer_instance

end ProjSpace

namespace ProjSpace

variable {A : Type u} [CommRing A] {n : ℕ}
  [HasExt.{w'} (Sheaf (Opens.grothendieckTopology (projectiveSpace A n).toTopCat) AddCommGrpCat.{u})]

attribute [local instance] algebraOfOver

theorem finite_H_twistingSheaf (k : ℤ) (p : ℕ) :
    Module.Finite A (Sheaf.H.{w'} (modulesAb (twistingSheaf (grading A n) k)) p) :=
  have := finite_cechH (A := A) (n := n) k p
  Module.Finite.equiv (cechHLinearEquivTwist k p)

theorem subsingleton_H_twistingSheaf {k : ℤ} (hk : 0 ≤ k) {p : ℕ} (hp : 0 < p) :
    Subsingleton (Sheaf.H.{w'} (modulesAb (twistingSheaf (grading A n) k)) p) := by
  rcases eq_or_ne p n with rfl | hpn
  · obtain ⟨e⟩ := nonempty_HTop_equiv.{w'} (A := A) k hp
    have : IsEmpty (NegMon p k) := ⟨fun m => by
      have hlt : ∑ j, m.1 j < 0 :=
        Finset.sum_neg (fun j _ => m.2.1 j) Finset.univ_nonempty
      rw [m.2.2] at hlt
      omega⟩
    exact e.toEquiv.subsingleton
  · exact subsingleton_H.{w'} k hp hpn

theorem subsingleton_H_of_lt (G : (projectiveSpace A n).Modules) [G.IsQuasicoherent] {p : ℕ}
    (hp : n < p) : Subsingleton (Sheaf.H.{w'} (modulesAb G) p) := by
  obtain ⟨e⟩ : Nonempty (cechH (modulesAb G).obj (stdOpen A n) p ≃+ Sheaf.H.{w'} (modulesAb G) p) :=
    SchemeCoh.nonempty_cechH_equiv_H G (stdOpen A n) iSup_stdOpen
      (fun _ i => by rw [← inter_eq_iInf]; exact isAffineOpen_inter i) p
  have : Subsingleton (cechH (modulesAb G).obj (stdOpen A n) p) :=
    cechH_subsingleton _ _ (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega)
  exact e.symm.toEquiv.subsingleton

end ProjSpace

end

end GroundTheory.Arith.SchemeCoh
