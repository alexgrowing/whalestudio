import Mathlib
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.OpensRangeChartYSupOpensRangeChartZ
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddXYZOrChordXYZOrOriginXYZNeZero

open AlgebraicGeometry CategoryTheory Limits

universe u

noncomputable section

namespace GlobalTheory

section Ext

variable {T Y S : Scheme.{u}}

theorem hom_eq_iff_forall_field [IsReduced T] (s : Y ⟶ S) [IsSeparated s] {f g : T ⟶ Y}
    (h : f ≫ s = g ≫ s) :
    f = g ↔ ∀ (k : Type u) [Field k] (x : Spec (.of k) ⟶ T), x ≫ f = x ≫ g :=
  ⟨fun e _ _ _ => e ▸ rfl, fun H => ext_of_fromSpecResidueField_eq f g s Set.univ dense_univ
    (fun x _ => H (T.residueField x) (T.fromSpecResidueField x)) h⟩

theorem hom_eq_iff_forall_isAlgClosed [IsReduced T] (s : Y ⟶ S) [IsSeparated s] {f g : T ⟶ Y}
    (h : f ≫ s = g ≫ s) :
    f = g ↔ ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (.of k) ⟶ T), x ≫ f = x ≫ g := by
  refine ⟨fun e _ _ _ _ => e ▸ rfl, fun H => (hom_eq_iff_forall_field s h).mpr fun k _ x => ?_⟩
  let ι : Spec (.of (AlgebraicClosure k)) ⟶ Spec (.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))
  have : Surjective ι := ⟨fun y => ⟨default, Subsingleton.elim _ _⟩⟩
  refine ext_of_isDominant_of_isSeparated s (by simp only [Category.assoc, h]) ι ?_
  simpa only [Category.assoc] using H _ (ι ≫ x)

theorem over_hom_eq_iff_forall_field {T Y : Over S} [IsReduced T.left] [IsSeparated Y.hom]
    {f g : T ⟶ Y} :
    f = g ↔ ∀ (k : Type u) [Field k] (t : Spec (.of k) ⟶ S) (x : Over.mk t ⟶ T),
      x ≫ f = x ≫ g := by
  refine ⟨fun e _ _ _ _ => e ▸ rfl, fun H => Over.OverMorphism.ext ?_⟩
  refine (hom_eq_iff_forall_field Y.hom ((Over.w f).trans (Over.w g).symm)).mpr fun k _ x => ?_
  exact congrArg (·.left) (H k (x ≫ T.hom) (Over.homMk x rfl))

variable {R : Type u} [CommRing R]

theorem over_hom_eq_iff_forall_isAlgClosed_algebra {T Y : Over (Spec (.of R))} [IsReduced T.left]
    [IsSeparated Y.hom] {f g : T ⟶ Y} :
    f = g ↔ ∀ (k : Type u) [Field k] [IsAlgClosed k] [Algebra R k]
      (x : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R k))) ⟶ T), x ≫ f = x ≫ g := by
  refine ⟨fun e _ _ _ _ _ => e ▸ rfl, fun H => Over.OverMorphism.ext ?_⟩
  refine (hom_eq_iff_forall_isAlgClosed Y.hom ((Over.w f).trans (Over.w g).symm)).mpr
    fun k _ _ x => ?_
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (x ≫ T.hom)
  letI : Algebra R k := φ.hom.toAlgebra
  exact congrArg (·.left) (H k (Over.homMk x hφ.symm))

theorem over_hom_eq_iff_forall_field_algebra {T Y : Over (Spec (.of R))} [IsReduced T.left]
    [IsSeparated Y.hom] {f g : T ⟶ Y} :
    f = g ↔ ∀ (k : Type u) [Field k] [Algebra R k]
      (x : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R k))) ⟶ T), x ≫ f = x ≫ g :=
  ⟨fun e _ _ _ _ => e ▸ rfl,
    fun H => over_hom_eq_iff_forall_isAlgClosed_algebra.mpr fun k _ _ _ x => H k x⟩

theorem eq_zero_of_forall_field {A : Type u} [CommRing A] [_root_.IsReduced A] {a : A}
    (h : ∀ (k : Type u) [Field k] (φ : A →+* k), φ a = 0) : a = 0 :=
  IsNilpotent.eq_zero (nilpotent_iff_mem_prime.mpr fun p _ =>
    Ideal.algebraMap_residueField_eq_zero.mp (h p.ResidueField (algebraMap A _)))

end Ext

namespace WeierstrassCurve

section Algebra

variable {A : Type*} [CommRing A]

theorem exists_unit_smul_of_minors {ι : Type*} [Fintype ι] {P Q : ι → A}
    (hP : Ideal.span (Set.range P) = ⊤) (hQ : Ideal.span (Set.range Q) = ⊤)
    (h : ∀ i j, P i * Q j = P j * Q i) : ∃ u : Aˣ, Q = (u : A) • P := by
  obtain ⟨a, ha⟩ := Ideal.mem_span_range_iff_exists_fun.mp (hP.ge (Submodule.mem_top (x := 1)))
  have e : Q = (∑ i, a i * Q i) • P := by
    ext j
    rw [Pi.smul_apply, smul_eq_mul, Finset.sum_mul, ← one_mul (Q j), ← ha, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by linear_combination a i * h i j
  have hu : IsUnit (∑ i, a i * Q i) := by
    rw [← Ideal.span_singleton_eq_top, _root_.eq_top_iff, ← hQ, Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    rw [congrFun e j]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
  exact ⟨hu.unit, e⟩

theorem IsUnimodularSol.exists_isUnit [IsLocalRing A] {V : WeierstrassCurve A} {P : Fin 3 → A}
    (h : IsUnimodularSol V P) : ∃ i, IsUnit (P i) := by
  by_contra! H
  have : Ideal.span (Set.range P) ≤ IsLocalRing.maximalIdeal A := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact H i
  exact (IsLocalRing.maximalIdeal.isMaximal A).ne_top (top_le_iff.mp (h.span_eq_top ▸ this))

theorem isUnimodularSol_iff_ne_zero {k : Type*} [Field k] {V : WeierstrassCurve k}
    {P : Fin 3 → k} : IsUnimodularSol V P ↔ V.toProjective.Equation P ∧ P ≠ 0 := by
  refine ⟨fun h => ⟨h.equation, ?_⟩, fun ⟨h, h0⟩ => ?_⟩
  · obtain ⟨i, hi⟩ := h.exists_isUnit
    rintro rfl
    exact hi.ne_zero rfl
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp h0
    exact .of_isUnit h i (Ne.isUnit hi)

theorem IsUnimodularSol.of_nonsingular {k : Type*} [Field k] {V : WeierstrassCurve k}
    {P : Fin 3 → k} (h : V.toProjective.Nonsingular P) : IsUnimodularSol V P :=
  isUnimodularSol_iff_ne_zero.mpr ⟨h.left, AddLaw.ne_zero_of_nonsingular h⟩

theorem isUnimodularSol_iff_nonsingular {k : Type*} [Field k] {V : WeierstrassCurve k}
    [V.IsElliptic] {P : Fin 3 → k} : IsUnimodularSol V P ↔ V.toProjective.Nonsingular P :=
  isUnimodularSol_iff_ne_zero.trans
    (AddLaw.nonsingular_iff_of_Δ_ne_zero V.isUnit_Δ.ne_zero P).symm

theorem IsUnimodularSol.nonsingular {k : Type*} [Field k] {V : WeierstrassCurve k}
    [V.IsElliptic] {P : Fin 3 → k} (h : IsUnimodularSol V P) : V.toProjective.Nonsingular P :=
  isUnimodularSol_iff_nonsingular.mp h

theorem equation_of_forall_field {A : Type u} [CommRing A] [_root_.IsReduced A]
    {V : WeierstrassCurve A} {P : Fin 3 → A}
    (h : ∀ (k : Type u) [Field k] (φ : A →+* k), (V.map φ).toProjective.Equation (φ ∘ P)) :
    V.toProjective.Equation P := by
  refine eq_zero_of_forall_field fun k _ φ => ?_
  have := h k φ
  change (V.toProjective.map φ).Equation _ at this
  rwa [WeierstrassCurve.Projective.Equation, WeierstrassCurve.Projective.map_polynomial,
    MvPolynomial.eval_map, ← MvPolynomial.eval₂_comp] at this

def unimodularSetoid (V : WeierstrassCurve A) : Setoid {P : Fin 3 → A // IsUnimodularSol V P} :=
  (MulAction.orbitRel Aˣ (Fin 3 → A)).comap Subtype.val

theorem unimodularSetoid_iff {V : WeierstrassCurve A}
    (P Q : {P : Fin 3 → A // IsUnimodularSol V P}) :
    unimodularSetoid V P Q ↔ ∃ u : Aˣ, Q.1 = (u : A) • P.1 :=
  ⟨fun h => ((unimodularSetoid V).symm h).imp fun _ e => e.symm,
    fun h => (unimodularSetoid V).symm (h.imp fun _ e => e.symm)⟩

abbrev UnimodularClass (V : WeierstrassCurve A) : Type _ := Quotient (unimodularSetoid V)

end Algebra

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

section Injective

variable {A : Type u} [CommRing A]

private theorem basicOpen_eq_top_iff (a : A) : PrimeSpectrum.basicOpen a = ⊤ ↔ IsUnit a := by
  rw [← Ideal.span_singleton_eq_top, ← PrimeSpectrum.iSup_basicOpen_eq_top_iff',
    iSup_singleton]

private theorem minors_of_isUnit {ρ : R →+* A} {P Q : Fin 3 → A}
    {hP : IsUnimodularSol (W.map ρ) P} {hQ : IsUnimodularSol (W.map ρ) Q}
    (e : ptHom W ρ P hP = ptHom W ρ Q hQ) {i : Fin 3} (hi : IsUnit (P i)) (j l : Fin 3) :
    P j * Q l = P l * Q j := by
  have hi' : IsUnit (Q i) := by
    have h₁ := ptHom_preimage_coordOpen W ρ P hP i
    rw [e, ptHom_preimage_coordOpen] at h₁
    exact (basicOpen_eq_top_iff _).mp (h₁.trans ((basicOpen_eq_top_iff _).mpr hi))
  rw [ptHom_eq_awayChart W i ρ P hP hi, ptHom_eq_awayChart W i ρ Q hQ hi', cancel_mono] at e
  have e' : awayEval W i ρ P hP.equation hi = awayEval W i ρ Q hQ.equation hi' :=
    congrArg (·.hom) (Spec.map_injective e)
  rw [← awayEval_awayCoord_mul W i ρ P hP.equation hi j,
    ← awayEval_awayCoord_mul W i ρ P hP.equation hi l,
    ← awayEval_awayCoord_mul W i ρ Q hQ.equation hi' j,
    ← awayEval_awayCoord_mul W i ρ Q hQ.equation hi' l, e']
  ring

theorem ptHom_eq_ptHom_iff_minors {ρ : R →+* A} {P Q : Fin 3 → A}
    (hP : IsUnimodularSol (W.map ρ) P) (hQ : IsUnimodularSol (W.map ρ) Q) :
    ptHom W ρ P hP = ptHom W ρ Q hQ ↔ ∀ j l, P j * Q l = P l * Q j := by
  refine ⟨fun e j l => ?_, fun h => ?_⟩
  · rw [← sub_eq_zero, ← Submodule.mem_bot A]
    refine Submodule.mem_of_span_eq_top_of_smul_pow_mem _ (Set.range P) hP.span_eq_top _ ?_
    rintro ⟨_, i, rfl⟩
    let φ := algebraMap A (Localization.Away (P i))
    have e' : ptHom W (φ.comp ρ) (φ ∘ P) (hP.map_comp φ) =
        ptHom W (φ.comp ρ) (φ ∘ Q) (hQ.map_comp φ) := by
      rw [← SpecMap_ptHom W ρ P hP, ← SpecMap_ptHom W ρ Q hQ, e]
    have h := minors_of_isUnit W e' (i := i) (IsLocalization.Away.algebraMap_isUnit (P i)) j l
    have h0 : φ (P j * Q l - P l * Q j) = 0 := by
      rw [map_sub, map_mul, map_mul, sub_eq_zero]
      exact h
    obtain ⟨⟨_, n, rfl⟩, hn⟩ := (IsLocalization.map_eq_zero_iff (.powers (P i)) _ _).mp h0
    exact ⟨n, hn⟩
  · obtain ⟨v, rfl⟩ := exists_unit_smul_of_minors hP.span_eq_top hQ.span_eq_top h
    exact (ptHom_smul W ρ P hP v.isUnit).symm

theorem ptHom_eq_ptHom_iff {ρ : R →+* A} {P Q : Fin 3 → A}
    (hP : IsUnimodularSol (W.map ρ) P) (hQ : IsUnimodularSol (W.map ρ) Q) :
    ptHom W ρ P hP = ptHom W ρ Q hQ ↔ ∃ v : Aˣ, Q = (v : A) • P := by
  refine ⟨fun e => exists_unit_smul_of_minors hP.span_eq_top hQ.span_eq_top
    ((ptHom_eq_ptHom_iff_minors W hP hQ).mp e), ?_⟩
  rintro ⟨v, rfl⟩
  exact (ptHom_smul W ρ P hP v.isUnit).symm

variable [Algebra R A] {P Q : Fin 3 → A}

theorem pt_eq_pt_iff_minors (hP : IsUnimodularSol (W.baseChange A) P)
    (hQ : IsUnimodularSol (W.baseChange A) Q) :
    pt W P hP = pt W Q hQ ↔ ∀ j l, P j * Q l = P l * Q j :=
  ptHom_eq_ptHom_iff_minors W hP.of_baseChange hQ.of_baseChange

theorem pt_eq_pt_iff (hP : IsUnimodularSol (W.baseChange A) P)
    (hQ : IsUnimodularSol (W.baseChange A) Q) :
    pt W P hP = pt W Q hQ ↔ ∃ v : Aˣ, Q = (v : A) • P :=
  ptHom_eq_ptHom_iff W hP.of_baseChange hQ.of_baseChange

theorem ptOver_eq_ptOver_iff (hP : IsUnimodularSol (W.baseChange A) P)
    (hQ : IsUnimodularSol (W.baseChange A) Q) :
    ptOver W P hP = ptOver W Q hQ ↔ ∃ v : Aˣ, Q = (v : A) • P :=
  Iff.trans ⟨fun e => congrArg (·.left) e, fun e => Over.OverMorphism.ext e⟩
    (pt_eq_pt_iff W hP hQ)

end Injective

section Local

variable {A : Type u} [CommRing A]

theorem exists_eq_ptHom_of_preimage_eq_top (ρ : R →+* A) (f : Spec (.of A) ⟶ scheme W)
    (hf : f ≫ toSpec W = Spec.map (CommRingCat.ofHom ρ)) (i : Fin 3)
    (hi : f ⁻¹ᵁ coordOpen W i = ⊤) :
    ∃ (P : Fin 3 → A) (h : IsUnimodularSol (W.map ρ) P), P i = 1 ∧ f = ptHom W ρ P h := by
  have hr : Set.range f ⊆ Set.range (awayChart W i) := by
    rintro _ ⟨x, rfl⟩
    rw [← Scheme.Hom.coe_opensRange, opensRange_awayChart]
    exact hi.ge (Set.mem_univ x)
  obtain ⟨g, hg⟩ := Spec.map_surjective (IsOpenImmersion.lift (awayChart W i) f hr)
  have e : f = ptHom W (g.hom.comp (awayConst W i)) (g.hom ∘ awayCoord W i)
      ((isUnimodularSol_awayCoord W i).map_comp g.hom) := by
    rw [← SpecMap_awayChart, CommRingCat.ofHom_hom, hg, IsOpenImmersion.lift_fac]
  have hρ : g.hom.comp (awayConst W i) = ρ := by
    rw [e, ptHom_toSpec] at hf
    exact congrArg (·.hom) (Spec.map_injective hf)
  subst hρ
  exact ⟨_, _, by simp, e⟩

theorem exists_eq_ptHom [IsLocalRing A] (ρ : R →+* A) (f : Spec (.of A) ⟶ scheme W)
    (hf : f ≫ toSpec W = Spec.map (CommRingCat.ofHom ρ)) :
    ∃ (P : Fin 3 → A) (h : IsUnimodularSol (W.map ρ) P), f = ptHom W ρ P h := by
  have : ∃ i, f (IsLocalRing.closedPoint A) ∈ coordOpen W i := by
    rcases (coordOpen_one_sup_coordOpen_two W).ge
      (Set.mem_univ (f (IsLocalRing.closedPoint A))) with h | h
    exacts [⟨_, h⟩, ⟨_, h⟩]
  obtain ⟨i, hi⟩ := this
  obtain ⟨P, h, -, e⟩ := exists_eq_ptHom_of_preimage_eq_top W ρ f hf i
    (Scheme.preimage_eq_top_of_closedPoint_mem (R := .of A) f hi)
  exact ⟨P, h, e⟩

variable [Algebra R A]

theorem exists_eq_pt [IsLocalRing A] (f : Spec (.of A) ⟶ scheme W)
    (hf : f ≫ toSpec W = Spec.map (CommRingCat.ofHom (algebraMap R A))) :
    ∃ (P : Fin 3 → A) (h : IsUnimodularSol (W.baseChange A) P), f = pt W P h :=
  exists_eq_ptHom W _ f hf

theorem exists_eq_ptOver [IsLocalRing A]
    (f : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R A))) ⟶ schemeOver W) :
    ∃ (P : Fin 3 → A) (h : IsUnimodularSol (W.baseChange A) P), f = ptOver W P h := by
  obtain ⟨P, h, e⟩ := exists_eq_pt W f.left (Over.w f)
  exact ⟨P, h, Over.OverMorphism.ext e⟩

variable (A) in

def ptClass : UnimodularClass (W.baseChange A) →
    (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R A))) ⟶ schemeOver W) :=
  Quotient.lift (fun P => ptOver W P.1 P.2) fun P Q h =>
    (ptOver_eq_ptOver_iff W P.2 Q.2).mpr ((unimodularSetoid_iff P Q).mp h)

@[simp] theorem ptClass_mk (P : Fin 3 → A) (h : IsUnimodularSol (W.baseChange A) P) :
    ptClass W A (Quotient.mk _ ⟨P, h⟩) = ptOver W P h := rfl

variable (A) in

theorem ptClass_injective : Function.Injective (ptClass W A) := by
  rintro ⟨P⟩ ⟨Q⟩ e
  exact Quotient.sound ((unimodularSetoid_iff P Q).mpr ((ptOver_eq_ptOver_iff W P.2 Q.2).mp e))

variable (A) in

theorem ptClass_bijective [IsLocalRing A] : Function.Bijective (ptClass W A) := by
  refine ⟨ptClass_injective W A, fun f => ?_⟩
  obtain ⟨P, h, rfl⟩ := exists_eq_ptOver W f
  exact ⟨Quotient.mk _ ⟨P, h⟩, rfl⟩

variable (A) in

def ptClassEquiv [IsLocalRing A] : UnimodularClass (W.baseChange A) ≃
    (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R A))) ⟶ schemeOver W) :=
  Equiv.ofBijective _ (ptClass_bijective W A)

@[simp] theorem ptClassEquiv_mk [IsLocalRing A] (P : Fin 3 → A)
    (h : IsUnimodularSol (W.baseChange A) P) :
    ptClassEquiv W A (Quotient.mk _ ⟨P, h⟩) = ptOver W P h := rfl

end Local

section Field

instance isElliptic_baseChange [W.IsElliptic] (A : Type*) [CommRing A] [Algebra R A] :
    (W.baseChange A).IsElliptic :=
  inferInstanceAs (W.map (algebraMap R A)).IsElliptic

def zeroOver (A : Type u) [CommRing A] [Algebra R A] :
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R A))) ⟶ schemeOver W :=
  Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ zero W) (by simp)

@[simp] theorem zeroOver_left (A : Type u) [CommRing A] [Algebra R A] :
    (zeroOver W A).left = Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ zero W := rfl

theorem zeroOver_eq_ptOver (A : Type u) [CommRing A] [Algebra R A] :
    zeroOver W A = ptOver W (A := A) ![0, 1, 0] (isUnimodularSol_zero _) :=
  Over.OverMorphism.ext (SpecMap_algebraMap_zero W A)

variable (k K : Type u) [Field k] [Field K] [Algebra R k] [Algebra R K]

def ofProjectivePoint (p : (W.baseChange k).toProjective.Point) :
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R k))) ⟶ schemeOver W :=
  Quotient.hrecOn p.point (motive := fun c => (W.baseChange k).toProjective.NonsingularLift c →
      (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R k))) ⟶ schemeOver W))
    (fun P h => ptOver W P (.of_nonsingular h))
    (fun P Q e => Function.hfunext
      (propext (WeierstrassCurve.Projective.nonsingular_of_equiv e)) fun hP hQ _ =>
        heq_of_eq ((ptOver_eq_ptOver_iff W (.of_nonsingular hQ) (.of_nonsingular hP)).mpr
          (e.imp fun _ e => e.symm)).symm)
    p.nonsingular

variable {k} in

@[simp] theorem ofProjectivePoint_mk {P : Fin 3 → k}
    (h : (W.baseChange k).toProjective.NonsingularLift (Quotient.mk _ P)) :
    ofProjectivePoint W k ⟨h⟩ = ptOver W P (.of_nonsingular h) := rfl

@[simp] theorem ofProjectivePoint_zero : ofProjectivePoint W k 0 = zeroOver W k :=
  (zeroOver_eq_ptOver W k).symm

theorem ofProjectivePoint_injective : Function.Injective (ofProjectivePoint W k) := by
  rintro @⟨⟨P⟩, hP⟩ @⟨⟨Q⟩, hQ⟩ e
  obtain ⟨v, hv⟩ := (ptOver_eq_ptOver_iff W (.of_nonsingular hQ) (.of_nonsingular hP)).mp e.symm
  exact WeierstrassCurve.Projective.Point.ext (Quotient.sound ⟨v, hv.symm⟩)

def ofAffinePoint (p : (W.baseChange k).toAffine.Point) :
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R k))) ⟶ schemeOver W :=
  ofProjectivePoint W k (WeierstrassCurve.Projective.Point.fromAffine p)

@[simp] theorem ofAffinePoint_zero : ofAffinePoint W k 0 = zeroOver W k :=
  ofProjectivePoint_zero W k

variable {k} in

@[simp] theorem ofAffinePoint_some {a b : k} (h : (W.baseChange k).toAffine.Nonsingular a b) :
    ofAffinePoint W k (.some a b h) = ptOver W ![a, b, 1] (isUnimodularSol_some h.left) := rfl

variable {k} in

@[simp] theorem ofAffinePoint_toAffineLift (p : (W.baseChange k).toProjective.Point) :
    ofAffinePoint W k p.toAffineLift = ofProjectivePoint W k p := by
  classical
  exact congrArg (ofProjectivePoint W k)
    ((WeierstrassCurve.Projective.Point.toAffineAddEquiv _).symm_apply_apply p)

variable {k} in

theorem ofAffinePoint_toAffine {P : Fin 3 → k} (h : (W.baseChange k).toProjective.Nonsingular P) :
    ofAffinePoint W k (WeierstrassCurve.Projective.Point.toAffine (W.baseChange k).toProjective P) =
      ptOver W P (.of_nonsingular h) :=
  ofAffinePoint_toAffineLift W ⟨(WeierstrassCurve.Projective.nonsingularLift_iff P).mpr h⟩

variable {k} in

theorem ofAffinePoint_of_represents {P : Fin 3 → k} {p : (W.baseChange k).toAffine.Point}
    (h : AddLaw.Represents (W.baseChange k).toProjective P p) :
    ofAffinePoint W k p = ptOver W P (.of_nonsingular h.left) :=
  h.right ▸ ofAffinePoint_toAffine W h.left

theorem ofAffinePoint_injective : Function.Injective (ofAffinePoint W k) := by
  classical
  exact (ofProjectivePoint_injective W k).comp
    (WeierstrassCurve.Projective.Point.toAffineAddEquiv
      (W.baseChange k).toProjective).symm.injective

variable {k K} in

theorem ofProjectivePoint_comp_left (f : k →ₐ[R] K) {P : Fin 3 → k}
    (h : (W.baseChange k).toProjective.NonsingularLift (Quotient.mk _ P))
    (h' : (W.baseChange K).toProjective.NonsingularLift (Quotient.mk _ (f ∘ P))) :
    (ofProjectivePoint W K ⟨h'⟩).left =
      Spec.map (CommRingCat.ofHom (f : k →+* K)) ≫ (ofProjectivePoint W k ⟨h⟩).left :=
  (SpecMap_pt W P (.of_nonsingular h) f).symm

variable {k K} in

theorem ofAffinePoint_map_left [DecidableEq k] [DecidableEq K] {S : Type*} [CommRing S]
    [Algebra R S] [Algebra S k] [IsScalarTower R S k] [Algebra S K] [IsScalarTower R S K]
    (f : k →ₐ[S] K) (p : (W.baseChange k).toAffine.Point) :
    (ofAffinePoint W K (WeierstrassCurve.Affine.Point.map (W' := W.toAffine) f p)).left =
      Spec.map (CommRingCat.ofHom (f : k →+* K)) ≫ (ofAffinePoint W k p).left := by
  rcases p with _ | ⟨a, b, h⟩
  · refine Eq.trans ?_ (SpecMap_pt W ![0, 1, 0] (isUnimodularSol_zero _) (f.restrictScalars R)).symm
    exact pt_congr W ![0, 1, 0] (isUnimodularSol_zero _) (by ext i; fin_cases i <;> simp) _
  · refine Eq.trans ?_
      (SpecMap_pt W ![a, b, 1] (isUnimodularSol_some h.left) (f.restrictScalars R)).symm
    exact pt_congr W ![f a, f b, 1] (isUnimodularSol_some
      ((W.toAffine.baseChange_nonsingular f.injective ..).mpr h).left)
      (by ext i; fin_cases i <;> simp) _

variable [(W.baseChange k).IsElliptic] [(W.baseChange K).IsElliptic]

theorem ofProjectivePoint_bijective : Function.Bijective (ofProjectivePoint W k) := by
  refine ⟨ofProjectivePoint_injective W k, fun f => ?_⟩
  obtain ⟨P, h, rfl⟩ := exists_eq_ptOver W f
  exact ⟨⟨(WeierstrassCurve.Projective.nonsingularLift_iff P).mpr h.nonsingular⟩, rfl⟩

theorem ofAffinePoint_bijective : Function.Bijective (ofAffinePoint W k) := by
  classical
  exact (ofProjectivePoint_bijective W k).comp
    (WeierstrassCurve.Projective.Point.toAffineAddEquiv
      (W.baseChange k).toProjective).symm.bijective

def projectivePointEquiv : (W.baseChange k).toProjective.Point ≃
    (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R k))) ⟶ schemeOver W) :=
  Equiv.ofBijective _ (ofProjectivePoint_bijective W k)

def affinePointEquiv : (W.baseChange k).toAffine.Point ≃
    (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R k))) ⟶ schemeOver W) :=
  Equiv.ofBijective _ (ofAffinePoint_bijective W k)

@[simp] theorem projectivePointEquiv_apply (p : (W.baseChange k).toProjective.Point) :
    projectivePointEquiv W k p = ofProjectivePoint W k p := rfl

@[simp] theorem affinePointEquiv_apply (p : (W.baseChange k).toAffine.Point) :
    affinePointEquiv W k p = ofAffinePoint W k p := rfl

@[simp] theorem projectivePointEquiv_symm_zeroOver :
    (projectivePointEquiv W k).symm (zeroOver W k) = 0 :=
  (Equiv.symm_apply_eq _).mpr (ofProjectivePoint_zero W k).symm

@[simp] theorem affinePointEquiv_symm_zeroOver :
    (affinePointEquiv W k).symm (zeroOver W k) = 0 :=
  (Equiv.symm_apply_eq _).mpr (ofAffinePoint_zero W k).symm

variable {k} in

theorem projectivePointEquiv_symm_ptOver (P : Fin 3 → k)
    (h : IsUnimodularSol (W.baseChange k) P) :
    (projectivePointEquiv W k).symm (ptOver W P h) =
      ⟨(WeierstrassCurve.Projective.nonsingularLift_iff P).mpr h.nonsingular⟩ :=
  (Equiv.symm_apply_eq _).mpr rfl

variable {k} in

theorem affinePointEquiv_symm_ptOver (P : Fin 3 → k) (h : IsUnimodularSol (W.baseChange k) P) :
    (affinePointEquiv W k).symm (ptOver W P h) =
      WeierstrassCurve.Projective.Point.toAffine (W.baseChange k).toProjective P :=
  (Equiv.symm_apply_eq _).mpr (ofAffinePoint_toAffine W h.nonsingular).symm

variable {k K} in

theorem affinePointEquiv_symm_of_left_eq [DecidableEq k] [DecidableEq K] {S : Type*} [CommRing S]
    [Algebra R S] [Algebra S k] [IsScalarTower R S k] [Algebra S K] [IsScalarTower R S K]
    (f : k →ₐ[S] K)
    (x : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R k))) ⟶ schemeOver W)
    (y : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R K))) ⟶ schemeOver W)
    (h : y.left = Spec.map (CommRingCat.ofHom (f : k →+* K)) ≫ x.left) :
    (affinePointEquiv W K).symm y =
      WeierstrassCurve.Affine.Point.map (W' := W.toAffine) f ((affinePointEquiv W k).symm x) := by
  obtain ⟨p, rfl⟩ := (affinePointEquiv W k).surjective x
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_eq]
  exact Over.OverMorphism.ext (h.trans (ofAffinePoint_map_left W f p).symm)

end Field

theorem hom_schemeOver_eq_iff {T : Over (Spec (.of R))} [IsReduced T.left]
    {f g : T ⟶ schemeOver W} :
    f = g ↔ ∀ (k : Type u) [Field k] [Algebra R k]
      (x : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R k))) ⟶ T), x ≫ f = x ≫ g :=
  have : IsSeparated (schemeOver W).hom := inferInstanceAs (IsSeparated (toSpec W))
  over_hom_eq_iff_forall_field_algebra

theorem points :
    (∀ (A : Type u) [CommRing A] [Algebra R A] (P Q : Fin 3 → A)
      (hP : IsUnimodularSol (W.baseChange A) P) (hQ : IsUnimodularSol (W.baseChange A) Q),
      pt W P hP = pt W Q hQ ↔ ∃ v : Aˣ, Q = (v : A) • P) ∧
    (∀ (A : Type u) [CommRing A] [Algebra R A] [IsLocalRing A],
      ∃ e : UnimodularClass (W.baseChange A) ≃
        (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R A))) ⟶ schemeOver W),
        ∀ P h, (e (Quotient.mk _ ⟨P, h⟩)).left = pt W P h) ∧
    (W.IsElliptic →
      ∃ (e : ∀ (k : Type u) [Field k] [Algebra R k], (W.baseChange k).toAffine.Point ≃
          (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R k))) ⟶ schemeOver W))
        (e' : ∀ (k : Type u) [Field k] [Algebra R k], (W.baseChange k).toProjective.Point ≃
          (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R k))) ⟶ schemeOver W)),
        (∀ (k : Type u) [Field k] [Algebra R k],
          (e k 0).left = Spec.map (CommRingCat.ofHom (algebraMap R k)) ≫ zero W ∧
          (e' k 0).left = Spec.map (CommRingCat.ofHom (algebraMap R k)) ≫ zero W ∧
          (∀ a b h, (e k (.some a b h)).left = pt W ![a, b, 1] (isUnimodularSol_some h.left)) ∧
          (∀ (P : Fin 3 → k)
            (h : (W.baseChange k).toProjective.NonsingularLift (Quotient.mk _ P)),
            (e' k ⟨h⟩).left = pt W P (.of_nonsingular h)) ∧
          (∀ p, e k p.toAffineLift = e' k p)) ∧
        ∀ (k K : Type u) [Field k] [Field K] [Algebra R k] [Algebra R K] [DecidableEq k]
          [DecidableEq K] (f : k →ₐ[R] K),
          (∀ p : (W.baseChange k).toAffine.Point,
            (e K (WeierstrassCurve.Affine.Point.map (W' := W.toAffine) f p)).left =
              Spec.map (CommRingCat.ofHom (f : k →+* K)) ≫ (e k p).left) ∧
          ∀ (P : Fin 3 → k)
            (h : (W.baseChange k).toProjective.NonsingularLift (Quotient.mk _ P))
            (h' : (W.baseChange K).toProjective.NonsingularLift (Quotient.mk _ (f ∘ P))),
            (e' K ⟨h'⟩).left = Spec.map (CommRingCat.ofHom (f : k →+* K)) ≫ (e' k ⟨h⟩).left) ∧
    (∀ (T Y : Over (Spec (.of R))) [IsReduced T.left] [IsSeparated Y.hom] (f g : T ⟶ Y),
      f = g ↔ ∀ (k : Type u) [Field k] (x : Spec (.of k) ⟶ T.left), x ≫ f.left = x ≫ g.left) :=
  ⟨fun _ _ _ _ _ hP hQ => pt_eq_pt_iff W hP hQ,
    fun A _ _ _ => ⟨ptClassEquiv W A, fun _ _ => rfl⟩,
    fun _ => ⟨fun k _ _ => affinePointEquiv W k, fun k _ _ => projectivePointEquiv W k,
      fun k _ _ => ⟨congrArg (·.left) (ofAffinePoint_zero W k),
        congrArg (·.left) (ofProjectivePoint_zero W k), fun _ _ _ => rfl, fun _ _ => rfl,
        ofAffinePoint_toAffineLift W⟩,
      fun _ _ _ _ _ _ _ _ f => ⟨ofAffinePoint_map_left W f,
        fun _ h h' => ofProjectivePoint_comp_left W f h h'⟩⟩,
    fun _ Y _ _ f g => Iff.trans ⟨fun e => congrArg (·.left) e, fun e => Over.OverMorphism.ext e⟩
      (hom_eq_iff_forall_field Y.hom ((Over.w f).trans (Over.w g).symm))⟩

example : pt (⟨0, 0, 1, -1, 0⟩ : WeierstrassCurve ℤ) (A := ℤ) ![0, 0, 1]
    (isUnimodularSol_some (by simp [WeierstrassCurve.baseChange])) ≠
    pt (⟨0, 0, 1, -1, 0⟩ : WeierstrassCurve ℤ) (A := ℤ) ![0, -1, 1]
      (isUnimodularSol_some (by
        simp [WeierstrassCurve.baseChange, WeierstrassCurve.Affine.equation_iff])) := by
  intro e
  simpa using (pt_eq_pt_iff_minors _ _ _).mp e 1 2

example (k : Type) [Field k] [Algebra ℚ k] : Function.Bijective
    (ofAffinePoint (⟨0, 0, 1, -1, 0⟩ : WeierstrassCurve ℚ) k) :=
  have : (⟨0, 0, 1, -1, 0⟩ : WeierstrassCurve ℚ).IsElliptic := ⟨Ne.isUnit (by
    norm_num [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
      WeierstrassCurve.b₈])⟩
  ofAffinePoint_bijective _ k

end WeierstrassCurve

end GlobalTheory
