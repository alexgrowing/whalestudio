import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPerHolOne
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AnalyticDictionaryIsPointPeriodOrigin
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ContinuousOnThetaFrameValueHolomorphicFamily

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi
  ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace GlobalTheory.PeriodSpan.TorusExp

section Torus

variable {Λ : Type} [AddCommGroup Λ]

def expRing (m : Λ →+ ℂ) : torusRing ZU Λ →+* ℂ :=
  AddMonoidAlgebra.liftNCRingHom ((Int.castRingHom ℂ).comp (ULift.ringEquiv : ULift.{0} ℤ ≃+* ℤ).toRingHom)
    { toFun := fun x => Complex.exp (m (Multiplicative.toAdd x))
      map_one' := by simp
      map_mul' := fun x y => by simp [Complex.exp_add] }
    (fun _ _ => Commute.all _ _)

theorem expRing_single (m : Λ →+ ℂ) (x : Λ) (r : ULift.{0} ℤ) :
    expRing m (AddMonoidAlgebra.single x r) = (r.down : ℂ) * Complex.exp (m x) := by
  simp [expRing, AddMonoidAlgebra.liftNCRingHom_single]
  rfl

def expPt (m : Λ →+ ℂ) : Over.mk (𝟙 (Sp ℂ)) ⟶ splitTorus (Spec (.of ℂ)) Λ :=
  SplitTorus.ofCoord (CommRingCat.ofHom (expRing m) ≫ (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv)

theorem val_expPt (m : Λ →+ ℂ) (x : Λ) :
    SplitTorus.val (expPt m) x = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom (Complex.exp (m x)) := by
  unfold SplitTorus.val expPt
  rw [SplitTorus.coord_ofCoord]
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]
  erw [expRing_single]
  simp

theorem expPt_add (m m' : Λ →+ ℂ) : expPt (m + m') = expPt m * expPt m' := by
  apply SplitTorus.hom_ext
  intro a
  simp only [SplitTorus.val_mul, val_expPt, AddMonoidHom.add_apply, Complex.exp_add, map_mul]

theorem expPt_zero : expPt (0 : Λ →+ ℂ) = 1 := by
  apply SplitTorus.hom_ext
  intro a
  simp only [val_expPt, SplitTorus.val_one, AddMonoidHom.zero_apply, Complex.exp_zero, map_one]

theorem expPt_sum_mem {κ : Type} (s : Finset κ) (m : κ → Λ →+ ℂ)
    (H : Subgroup (Over.mk (𝟙 (Sp ℂ)) ⟶ splitTorus (Spec (.of ℂ)) Λ)) (h : ∀ i, expPt (m i) ∈ H) :
    expPt (∑ i ∈ s, m i) ∈ H := by
  classical
  refine Finset.induction_on s (by rw [Finset.sum_empty, expPt_zero]; exact H.one_mem) ?_
  intro j s hj ih
  rw [Finset.sum_insert hj, expPt_add]
  exact H.mul_mem (h j) ih

theorem exists_eq_expPt [Module.Free ℤ Λ] (t : Over.mk (𝟙 (Sp ℂ)) ⟶ splitTorus (Spec (.of ℂ)) Λ) :
    ∃ l : Λ →+ ℂ, t = expPt ((2 * Real.pi * Complex.I : ℂ) • l) := by
  let φ : Λ → ℂˣ := fun x =>
    ((SplitTorus.isUnit_val t x).map (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom).unit
  have hφ : ∀ x, (φ x : ℂ) = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom (SplitTorus.val t x) :=
    fun x => rfl
  obtain ⟨l, hl⟩ := GlobalTheory.Ex.Arch.exists_log_of_character φ (fun x y => by
    ext
    simp only [Units.val_mul, hφ, SplitTorus.val_add, map_mul])
  refine ⟨l, SplitTorus.hom_ext fun a => ?_⟩
  rw [val_expPt]
  have h1 := hl a
  rw [hφ] at h1
  unfold eTwoPi at h1
  rw [AddMonoidHom.smul_apply, smul_eq_mul, ← h1]
  simp

private theorem isHolTo_comp_continuousLinearMap {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {X Y : Scheme.{0}}
    {B : Set V} {f : V → (Sp ℂ ⟶ X)} (hf : IsHolTo B f) (g : X ⟶ Y) : IsHolTo B fun b => f b ≫ g := by
  intro U s
  obtain ⟨h1, h2⟩ := hf (g ⁻¹ᵁ U) ((g.app U).hom s)
  have key : ∀ b, valAt' (f b ≫ g) U s = valAt' (f b) (g ⁻¹ᵁ U) ((g.app U).hom s) := by
    intro b
    unfold valAt'
    by_cases hb : ⊤ ≤ (f b ≫ g) ⁻¹ᵁ U
    · have hb' : ⊤ ≤ f b ⁻¹ᵁ g ⁻¹ᵁ U := hb
      rw [dif_pos hb, dif_pos hb']
      unfold valAt
      rw [Scheme.Hom.comp_appLE]
      rfl
    · have hb' : ¬ ⊤ ≤ f b ⁻¹ᵁ g ⁻¹ᵁ U := hb
      rw [dif_neg hb, dif_neg hb']
  exact ⟨h1, h2.congr fun b _ => key b⟩

theorem isHolTo_expPt {m : ℂ → Λ →+ ℂ} (hm : ∀ x, Differentiable ℂ fun s => m s x) :
    IsHolTo Set.univ fun s => (show Sp ℂ ⟶ _ from (expPt (m s)).left) := by
  let ψ : ℂ → (AddMonoidAlgebra ℂ Λ →+* ℂ) := fun s =>
    AddMonoidAlgebra.liftNCRingHom (RingHom.id ℂ)
      { toFun := fun x => Complex.exp (m s (Multiplicative.toAdd x))
        map_one' := by simp
        map_mul' := fun x y => by simp [Complex.exp_add] }
      (fun _ _ => Commute.all _ _)
  have hψs : ∀ s a c, ψ s (AddMonoidAlgebra.single a c) = c * Complex.exp (m s a) := by
    intro s a c
    simp [ψ, AddMonoidAlgebra.liftNCRingHom_single]
  have hψ0 : ∀ s, (ψ s).comp (algebraMap ℂ (AddMonoidAlgebra ℂ Λ)) = RingHom.id ℂ := by
    intro s
    ext c
    simp [AddMonoidAlgebra.coe_algebraMap, hψs]
  have hs : ∀ s, Spec.map (CommRingCat.ofHom ((ψ s).comp (algebraMap (CommRingCat.of ℂ)
      (AddMonoidAlgebra (CommRingCat.of ℂ) Λ)))) ≫ 𝟙 (Spec (CommRingCat.of ℂ)) = 𝟙 (Sp ℂ) := by
    intro s
    rw [hψ0 s, Category.comp_id]
    exact Spec.map_id _
  have key : ∀ s, expPt (m s) = SplitTorus.ptOf (S := Spec (CommRingCat.of ℂ)) (X := Λ) (A := CommRingCat.of ℂ)
      (B := CommRingCat.of ℂ) (s := 𝟙 (Sp ℂ)) (𝟙 _) (ψ s) (hs s) := by
    intro s
    apply SplitTorus.pull_ext
    intro a
    rw [SplitTorus.pull_ptOf, SplitTorus.ev_chi, SplitTorus.pull_chi, val_expPt]
    erw [hψs]
    simp
  have hd : ∀ u : AddMonoidAlgebra ℂ Λ, DifferentiableOn ℂ (fun s => ψ s u) Set.univ := by
    intro u
    refine AddMonoidAlgebra.induction_linear u ?_ ?_ ?_
    · simp
    · intro f g hf hg
      simp only [map_add]
      exact hf.add hg
    · intro a c
      simp only [hψs]
      exact ((hm a).cexp.const_mul c).differentiableOn
  have hhol := isHolTo_comp_continuousLinearMap (GlobalTheory.ThetaValueCont.isHolTo_spMap isOpen_univ ψ hd)
    (SplitTorus.univPt Λ (𝟙 (Spec (CommRingCat.of ℂ)))).left
  convert hhol using 1
  funext s
  rw [key s]
  rfl

def oneParam (n : Λ →+ ℤ) (s : ℂ) : Over.mk (𝟙 (Sp ℂ)) ⟶ splitTorus (Spec (.of ℂ)) Λ :=
  expPt (s • (Int.castAddHom ℂ).comp n)

theorem oneParam_add (n : Λ →+ ℤ) (s s' : ℂ) : oneParam n (s + s') = oneParam n s * oneParam n s' := by
  simp only [oneParam, add_smul, expPt_add]

theorem oneParam_period (n : Λ →+ ℤ) : oneParam n (2 * Real.pi * Complex.I) = 1 := by
  apply SplitTorus.hom_ext
  intro a
  simp only [oneParam, val_expPt, SplitTorus.val_one, AddMonoidHom.smul_apply, AddMonoidHom.comp_apply,
    Int.coe_castAddHom, smul_eq_mul]
  rw [mul_comm (2 * (Real.pi : ℂ) * Complex.I), Complex.exp_int_mul_two_pi_mul_I, map_one]

theorem isHolTo_oneParam (n : Λ →+ ℤ) : IsHolTo Set.univ fun s => (show Sp ℂ ⟶ _ from (oneParam n s).left) := by
  refine isHolTo_expPt fun x => ?_
  simp only [AddMonoidHom.smul_apply, AddMonoidHom.comp_apply, smul_eq_mul]
  fun_prop

theorem mem_closure_oneParam [Module.Free ℤ Λ] [Module.Finite ℤ Λ]
    (t : Over.mk (𝟙 (Sp ℂ)) ⟶ splitTorus (Spec (.of ℂ)) Λ) :
    t ∈ Subgroup.closure (⋃ n : Λ →+ ℤ, Set.range (oneParam n)) := by
  obtain ⟨l, rfl⟩ := exists_eq_expPt t
  set M : Λ →+ ℂ := (2 * Real.pi * Complex.I : ℂ) • l
  let b := Module.Free.chooseBasis ℤ Λ
  have hM : M = ∑ j, M (b j) • (Int.castAddHom ℂ).comp (b.coord j).toAddMonoidHom := by
    ext x
    simp
    conv_lhs => rw [← b.sum_repr x]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_zsmul, zsmul_eq_mul]
    ring
  rw [hM]
  refine expPt_sum_mem _ _ _ fun j => Subgroup.subset_closure ?_
  exact Set.mem_iUnion.2 ⟨(b.coord j).toAddMonoidHom, M (b j), rfl⟩

end Torus

section Push

variable {X : Scheme.{0}} {G : Over X} [GrpObj G] {y : Sp ℂ ⟶ X} {Λ : Type} [AddCommGroup Λ]
  (i : splitTorus (Spec (.of ℂ)) Λ ⟶ (Over.pullback y).obj G)

theorem left_mul_congr {y' : Sp ℂ ⟶ X} (hy : y' = y) {a b : Over.mk y' ⟶ G} {a' b' : Over.mk y ⟶ G}
    (ha : (show Sp ℂ ⟶ G.left from a.left) = a'.left) (hb : (show Sp ℂ ⟶ G.left from b.left) = b'.left) :
    (show Sp ℂ ⟶ G.left from (a * b).left) = (a' * b').left := by
  subst hy
  have h1 : a = a' := Over.OverMorphism.ext ha
  have h2 : b = b' := Over.OverMorphism.ext hb
  subst h1 h2
  rfl

omit [GrpObj G] in
theorem push_w (t : Over.mk (𝟙 (Sp ℂ)) ⟶ splitTorus (Spec (.of ℂ)) Λ) :
    ((t ≫ i).left ≫ pullback.fst G.hom y) ≫ G.hom = (Over.mk (𝟙 (Sp ℂ))).hom ≫ y := by
  rw [Category.assoc, pullback.condition, ← Category.assoc]
  congr 1
  exact Over.w (t ≫ i)

def push (t : Over.mk (𝟙 (Sp ℂ)) ⟶ splitTorus (Spec (.of ℂ)) Λ) : Over.mk y ⟶ G :=
  Over.homMk ((t ≫ i).left ≫ pullback.fst G.hom y) ((push_w i t).trans (Category.id_comp y))

theorem push_mul [IsMonHom i] (t t' : Over.mk (𝟙 (Sp ℂ)) ⟶ splitTorus (Spec (.of ℂ)) Λ) :
    push i (t * t') = push i t * push i t' := by
  apply Over.OverMorphism.ext
  have hx := SplitTorus.mul_left_comp_fst G y (t ≫ i) (t' ≫ i)
    (Over.homMk ((t ≫ i).left ≫ pullback.fst G.hom y) (push_w i t))
    (Over.homMk ((t' ≫ i).left ≫ pullback.fst G.hom y) (push_w i t')) rfl rfl
  have hc := left_mul_congr (G := G) (Category.id_comp y)
    (a := Over.homMk ((t ≫ i).left ≫ pullback.fst G.hom y) (push_w i t))
    (b := Over.homMk ((t' ≫ i).left ≫ pullback.fst G.hom y) (push_w i t'))
    (a' := push i t) (b' := push i t') rfl rfl
  calc (push i (t * t')).left = ((t * t') ≫ i).left ≫ pullback.fst G.hom y := rfl
    _ = ((t ≫ i) * (t' ≫ i)).left ≫ pullback.fst G.hom y := by rw [MonObj.mul_comp]
    _ = _ := hx.symm
    _ = _ := hc

def pushHom [IsMonHom i] : (Over.mk (𝟙 (Sp ℂ)) ⟶ splitTorus (Spec (.of ℂ)) Λ) →* (Over.mk y ⟶ G) :=
  MonoidHom.mk' (push i) (push_mul i)

theorem isPerHol_push [IsMonHom i] (n : Λ →+ ℤ) : IsPerHol G y fun s => pushHom i (oneParam n s) := by
  unfold IsPerHol
  refine ⟨fun s t => by simp only [oneParam_add, map_mul], ?_, by simp only [oneParam_period, map_one]⟩
  exact isHolTo_comp_continuousLinearMap (isHolTo_comp_continuousLinearMap (isHolTo_oneParam n) i.left) (pullback.fst G.hom y)

end Push

end GlobalTheory.PeriodSpan.TorusExp

namespace GlobalTheory.PeriodSpan

open TorusExp in

theorem torusPts_subset_perHolSub (X : Scheme.{0}) (G : Over X) [GrpObj G] (y : Sp ℂ ⟶ X)
    (E : TorusExtension ((Over.pullback y).obj G)) :
    torusPts G y E ⊆ (perHolSub G y : Set (Over.mk y ⟶ G)) := by
  let _ := E.addCommGroup
  have : Module.Free ℤ E.X := E.free
  have : Module.Finite ℤ E.X := E.finite
  have : IsMonHom E.i := E.i_hom
  rintro x ⟨t, ht⟩
  have hx : x = pushHom E.i t := Over.OverMorphism.ext ht.symm
  rw [hx, SetLike.mem_coe]
  unfold perHolSub
  have hmap := Subgroup.mem_map_of_mem (pushHom E.i) (mem_closure_oneParam t)
  rw [MonoidHom.map_closure] at hmap
  refine Subgroup.closure_mono ?_ hmap
  rintro _ ⟨z, hz, rfl⟩
  obtain ⟨n, s, rfl⟩ := Set.mem_iUnion.1 hz
  exact Set.mem_iUnion₂.2 ⟨_, isPerHol_push E.i n, s, rfl⟩

end GlobalTheory.PeriodSpan
