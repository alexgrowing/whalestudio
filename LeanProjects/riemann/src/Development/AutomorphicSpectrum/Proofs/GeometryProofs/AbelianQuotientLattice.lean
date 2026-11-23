import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GermSys
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.QQuasiCompact
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FormalGermLieBasisStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFunctorialMap
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelExistsUniqueAct
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelPullbackEquivalence
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsCocharacterLieModelStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SmoothQ
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LeftEqIffLieVecSmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.Torus2GammaBijective

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.LieSeq

theorem exists_stalkTo {R : Type} [CommRing R] [IsLocalRing R] {Y : Scheme.{0}} (u : Sp R ⟶ Y) (z : Y)
    (h : u (IsLocalRing.closedPoint R) = z) :
    ∃ β : Y.presheaf.stalk z ⟶ CommRingCat.of R, Spec.map β ≫ Y.fromSpecStalk z = u := by
  subst h
  exact ⟨_, Scheme.Spec_stalkClosedPointTo_fromSpecStalk u⟩

theorem exists_dual_lift {Y Z : Scheme.{0}} (f : Y ⟶ Z) [Smooth f] {k : Type} [Field k] (y : Sp k ⟶ Y)
    (w : Sp (DualNumber k) ⟶ Z) (h : spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ w = y ≫ f) :
    ∃ v : Sp (DualNumber k) ⟶ Y, spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ v = y ∧ v ≫ f = w := by
  let fs : DualNumber k →+* k := (TrivSqZeroExt.fstHom k k k).toRingHom
  have hfs : Function.Surjective fs := fun c => ⟨TrivSqZeroExt.inl c, rfl⟩
  haveI : IsLocalHom fs := ⟨fun a ha => TrivSqZeroExt.isUnit_iff_isUnit_fst.2 ha⟩
  let c : Sp k := IsLocalRing.closedPoint k
  let yp : Y := y c
  have hpt : (spMap fs) c = IsLocalRing.closedPoint (DualNumber k) :=
    IsLocalRing.comap_closedPoint fs
  have hw : w (IsLocalRing.closedPoint (DualNumber k)) = f yp := by
    have e : (spMap fs ≫ w) c = (y ≫ f) c := by rw [show spMap fs ≫ w = y ≫ f from h]
    simpa [Scheme.Hom.comp_apply, hpt] using e
  obtain ⟨βy, hβy⟩ := exists_stalkTo y yp rfl
  obtain ⟨βw, hβw⟩ := exists_stalkTo w (f yp) hw
  have hsm : (f.stalkMap yp).hom.FormallySmooth :=
    Scheme.Hom.mem_smoothLocus.mp (f.smoothLocus_eq_top.ge (Set.mem_univ yp))
  have hcomp : βw ≫ CommRingCat.ofHom fs = f.stalkMap yp ≫ βy := by
    apply Spec.map_injective
    rw [← cancel_mono (Z.fromSpecStalk (f yp))]
    rw [Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc, hβw,
      Scheme.SpecMap_stalkMap_fromSpecStalk, ← Category.assoc, hβy]
    exact h
  algebraize [(f.stalkMap yp).hom]
  letI : Algebra (Z.presheaf.stalk (f yp)) k := ((βy.hom).comp (f.stalkMap yp).hom).toAlgebra
  letI : Algebra (Z.presheaf.stalk (f yp)) (DualNumber k) := (βw.hom).toAlgebra
  have e1 : ∀ b, fs (βw.hom b) = βy.hom ((f.stalkMap yp).hom b) := fun b =>
    congrArg (fun φ => φ.hom b) hcomp
  let F : Y.presheaf.stalk yp →ₐ[Z.presheaf.stalk (f yp)] k :=
    { βy.hom with commutes' := fun _ => rfl }
  let G : DualNumber k →ₐ[Z.presheaf.stalk (f yp)] k :=
    { fs with commutes' := fun b => e1 b }
  have hnil : IsNilpotent (RingHom.ker (G : DualNumber k →+* k)) := by
    refine ⟨2, ?_⟩
    rw [pow_two, Ideal.zero_eq_bot, eq_bot_iff, Ideal.mul_le]
    intro a ha b hb
    have ha : a.fst = 0 := ha
    have hb : b.fst = 0 := hb
    rw [Ideal.mem_bot]
    ext <;> simp [ha, hb]
  let l := Algebra.FormallySmooth.liftOfSurjective F G hfs hnil
  have hl : ∀ a, fs (l a) = βy.hom a := fun a =>
    Algebra.FormallySmooth.liftOfSurjective_apply F G hfs hnil a
  have hl2 : ∀ b, l ((f.stalkMap yp).hom b) = βw.hom b := fun b => l.commutes b
  refine ⟨Spec.map (CommRingCat.ofHom (l : Y.presheaf.stalk yp →+* DualNumber k)) ≫ Y.fromSpecStalk yp, ?_, ?_⟩
  · rw [← hβy, ← Category.assoc, spMap, ← Spec.map_comp]
    congr 2
    ext a
    exact hl a
  · rw [Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk, ← Category.assoc, ← Spec.map_comp, ← hβw]
    exact congrArg (fun φ => Spec.map φ ≫ Z.fromSpecStalk (f yp))
      (CommRingCat.hom_ext (RingHom.ext fun b => hl2 b))

section Torus

variable {k : Type} [Field k] {Ch : Type} [AddCommGroup Ch]

open Rosenlicht GlobalTheory.Diag in
theorem chi_injective {a b : Ch} (h : chi (S := Sp k) Ch a = chi (S := Sp k) Ch b) : a = b := by
  have := congrArg (torusGamma k Ch).hom h
  rw [torusGamma_chi, torusGamma_chi] at this
  by_contra hab
  have h3 := congrArg (fun p => p.coeff a) this
  simp [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, Ne.symm hab] at h3

open Rosenlicht GlobalTheory.Diag in

theorem exists_diagMap [TwoUniqueSums Ch] (t : splitTorus (Sp k) Ch ⟶ splitTorus (Sp k) Ch) [IsMonHom t] :
    ∃ h : Ch →+ Ch, t = diagMap (Sp k) h := by
  have key : ∀ y, ∃ a, (coord t).hom (AddMonoidAlgebra.single y 1) = chi (S := Sp k) Ch a := by
    intro y
    obtain ⟨c, a, hc, e⟩ := torus_hom_coord k Ch t y
    refine ⟨a, ?_⟩
    let p : Over.mk (𝟙 (Sp k)) ⟶ splitTorus (Sp k) Ch := 1
    have hp : p ≫ t = p := by
      simp [p, MonObj.one_comp]
    have e1 : GlobalTheory.Diag.charVal (p ≫ t) y = (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom
        (p.left.appTop.hom ((coord t).hom (AddMonoidAlgebra.single y 1))) := by
      rw [GlobalTheory.Diag.charVal_eq_coord, coord_comp]; rfl
    rw [hp, GlobalTheory.Diag.charVal_one, e, map_mul, map_mul] at e1
    have e2 : (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom (p.left.appTop.hom (chi (S := Sp k) Ch a)) = 1 :=
      GlobalTheory.Diag.charVal_one (g := 𝟙 (Sp k)) a
    have e3 : p.left.appTop.hom ((splitTorus (Sp k) Ch).hom.appTop.hom c) = c := by
      have w := Over.w p
      simp only [Over.mk_hom] at w
      rw [← appTop_comp_apply, w]; rfl
    rw [e2, e3, _root_.mul_one] at e1
    have hc1 : c = 1 := (cr_iso_bij (Scheme.ΓSpecIso (CommRingCat.of k))).1 (by rw [← e1, map_one])
    rw [e, hc1, map_one, _root_.one_mul]
  choose h hh using key
  have hadd : ∀ y y', h (y + y') = h y + h y' := by
    intro y y'
    apply chi_injective (k := k)
    have hs : AddMonoidAlgebra.single (y + y') (1 : ZU) = AddMonoidAlgebra.single y 1 * AddMonoidAlgebra.single y' 1 := by
      rw [AddMonoidAlgebra.single_mul_single, _root_.mul_one]
    have h1 := hh (y + y')
    rw [hs, map_mul, hh, hh] at h1
    apply (torusGamma_bijective k Ch).1
    rw [← h1, map_mul, torusGamma_chi, torusGamma_chi, torusGamma_chi, AddMonoidAlgebra.single_mul_single, _root_.mul_one]
  refine ⟨AddMonoidHom.mk' h hadd, hom_ext fun y => ?_⟩
  rw [← Category.id_comp (diagMap (Sp k) _), coord_comp_diagMap_single, hh]
  rfl

end Torus

section Seq

variable {k : Type} [Field k] {G B K : Over (Sp k)} [GrpObj G] [GrpObj B] [GrpObj K]

theorem pt_zero {A : Over (Sp k)} [GrpObj A] {L : Type} [AddCommGroup L] [Module k L] (M : LieModel A (𝟙 _) L) :
    M.pt 0 = 1 := by
  have h := M.add 0 0
  rw [add_zero] at h
  exact left_eq_mul.1 h

theorem lie_kernel (i : K ⟶ G) (q : G ⟶ B) [IsMonHom i] [IsMonHom q]
    (ker : IsPullback i (toUnit _) q (η : 𝟙_ _ ⟶ B))
    {LK LG LB : Type} [AddCommGroup LK] [Module k LK] [AddCommGroup LG] [Module k LG] [AddCommGroup LB] [Module k LB]
    (MK : LieModel K (𝟙 _) LK) (MG : LieModel G (𝟙 _) LG) (MB : LieModel B (𝟙 _) LB)
    (di : LK →ₗ[k] LG) (dq : LG →ₗ[k] LB) (hdi : ∀ e, MG.pt (di e) = MK.pt e ≫ i)
    (hdq : ∀ e, MB.pt (dq e) = MG.pt e ≫ q) :
    Function.Injective di ∧ ∀ w, dq w = 0 ↔ w ∈ LinearMap.range di := by
  have hinj : ∀ {T : Over (Sp k)} {a b : T ⟶ K}, a ≫ i = b ≫ i → a = b :=
    fun e => ker.hom_ext e (toUnit_unique _ _)
  refine ⟨fun u u' e => MK.inj (hinj (by rw [← hdi, ← hdi, e])), fun w => ⟨fun e => ?_, ?_⟩⟩
  · have e' : MG.pt w ≫ q = toUnit _ ≫ η := by
      rw [← hdq, e, pt_zero]; rfl
    let l := ker.lift (MG.pt w) (toUnit _) (by rw [e'])
    have hl : l ≫ i = MG.pt w := ker.lift_fst _ _ _
    have htan : IsTanAt K (𝟙 _) l := by
      let fs := Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom)
      have hw : fs ≫ l.left ≫ K.hom = 𝟙 (Sp k) := by
        have w := Over.w l
        simp only [Over.mk_hom] at w
        rw [w, Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
        have : ((TrivSqZeroExt.fstHom k k k).toRingHom).comp (algebraMap k (DualNumber k)) = RingHom.id k := by
          ext r; simp
        rw [this]; simp
      let p : Over.mk (𝟙 (Sp k)) ⟶ K := Over.homMk (fs ≫ l.left) (by simpa using hw)
      have hp : p = 1 := by
        apply hinj
        rw [MonObj.one_comp]
        apply Over.OverMorphism.ext
        have := MG.tan w
        unfold IsTanAt at this
        rw [← hl] at this
        simpa [p, fs] using this
      exact congrArg (fun t => t.left) hp
    obtain ⟨u, hu⟩ := MK.onto l htan
    exact ⟨u, MG.inj (by rw [hdi, hu, hl])⟩
  · rintro ⟨u, rfl⟩
    apply MB.inj
    rw [hdq, hdi, Category.assoc, ker.w, pt_zero, ← Category.assoc, toUnit_unique (MK.pt u ≫ toUnit K) (toUnit _)]
    rfl

theorem lie_surjective (q : G ⟶ B) [IsMonHom q] (hs : Smooth q.left)
    {LG LB : Type} [AddCommGroup LG] [Module k LG] [AddCommGroup LB] [Module k LB]
    (MG : LieModel G (𝟙 _) LG) (MB : LieModel B (𝟙 _) LB)
    (dq : LG →ₗ[k] LB) (hdq : ∀ e, MB.pt (dq e) = MG.pt e ≫ q) : Function.Surjective dq := by
  intro w
  have h0 : (1 : Over.mk (𝟙 (Sp k)) ⟶ G) ≫ q = 1 := MonObj.one_comp _
  obtain ⟨v, hv1, hv2⟩ := exists_dual_lift q.left (1 : Over.mk (𝟙 (Sp k)) ⟶ G).left (MB.pt w).left (by
    have := MB.tan w
    unfold IsTanAt at this
    rw [this, ← h0]; rfl)
  have hb : v ≫ G.hom = (epsAt (𝟙 (Sp k))).hom := by
    have e1 := Over.w q
    have e2 := Over.w (MB.pt w)
    rw [← e1, ← Category.assoc, hv2]
    exact e2
  let vv : epsAt (𝟙 (Sp k)) ⟶ G := Over.homMk v hb
  obtain ⟨e, he⟩ := MG.onto vv hv1
  refine ⟨e, MB.inj ?_⟩
  rw [hdq, he]
  exact Over.OverMorphism.ext hv2

end Seq

section Act

variable {k : Type} [Field k] {G B : Over (Sp k)} [GrpObj G] [GrpObj B] {Ch : Type} [AddCommGroup Ch]

open GlobalTheory.Diag in
theorem diagMap_injective {u v : Ch →+ Ch} (h : diagMap (Sp k) u = diagMap (Sp k) v) : u = v := by
  ext y
  apply chi_injective (k := k)
  rw [← diagMap_chi, ← diagMap_chi, h]

theorem isMonHom_of_comp {A A' C : Over (Sp k)} [GrpObj A] [GrpObj A'] [GrpObj C] (i : A' ⟶ C) [IsMonHom i]
    (hinj : ∀ {T : Over (Sp k)} {a b : T ⟶ A'}, a ≫ i = b ≫ i → a = b) (t : A ⟶ A') (f : A ⟶ C) [IsMonHom f]
    (h : t ≫ i = f) : IsMonHom t where
  one_hom := hinj (by
    rw [Category.assoc, h, IsMonHom.one_hom, IsMonHom.one_hom])
  mul_hom := hinj (by
    rw [Category.assoc, Category.assoc, h, IsMonHom.mul_hom, IsMonHom.mul_hom,
      tensorHom_comp_tensorHom_assoc, h])

open GlobalTheory.Diag in

theorem exists_charAct [TwoUniqueSums Ch] (i : splitTorus (Sp k) Ch ⟶ G) (q : G ⟶ B) [IsMonHom i] [IsMonHom q]
    (ker : IsPullback i (toUnit _) q (η : 𝟙_ _ ⟶ B)) {O : Type} [CommRing O]
    (act : O → (G ⟶ G)) (actB : O → (B ⟶ B)) (hm : ∀ a, IsMonHom (act a)) (hmB : ∀ a, IsMonHom (actB a))
    (h1 : act 1 = 𝟙 G) (hmul : ∀ a b, act (a * b) = act a ≫ act b) (hadd : ∀ a b, act (a + b) = act a * act b)
    (hq : ∀ a, act a ≫ q = q ≫ actB a) :
    ∃ h : O →+* AddMonoid.End Ch, ∀ a, diagMap (Sp k) (h a : Ch →+ Ch) ≫ i = i ≫ act a := by
  have hinj : ∀ {T : Over (Sp k)} {a b : T ⟶ splitTorus (Sp k) Ch}, a ≫ i = b ≫ i → a = b :=
    fun e => ker.hom_ext e (toUnit_unique _ _)
  have ex : ∀ a, ∃ u : Ch →+ Ch, diagMap (Sp k) u ≫ i = i ≫ act a := by
    intro a
    haveI := hm a
    haveI := hmB a
    have e : (i ≫ act a) ≫ q = toUnit _ ≫ η := by
      rw [Category.assoc, hq, ← Category.assoc, ker.w, Category.assoc, IsMonHom.one_hom]
    let t := ker.lift (i ≫ act a) (toUnit _) (by rw [e])
    have ht : t ≫ i = i ≫ act a := ker.lift_fst _ _ _
    haveI : IsMonHom t := isMonHom_of_comp i hinj t (i ≫ act a) ht
    obtain ⟨u, hu⟩ := exists_diagMap t
    exact ⟨u, by rw [← hu, ht]⟩
  choose A hA using ex
  have one : A 1 = AddMonoidHom.id Ch := by
    apply diagMap_injective (k := k)
    apply hinj
    rw [hA, h1, diagMap_id, Category.comp_id, Category.id_comp]
  have mul : ∀ a b, A (a * b) = (A a).comp (A b) := by
    intro a b
    apply diagMap_injective (k := k)
    apply hinj
    rw [hA, diagMap_comp, Category.assoc, hA, ← Category.assoc, hA, hmul, Category.assoc]
  have add : ∀ a b, A (a + b) = A a + A b := by
    intro a b
    apply diagMap_injective (k := k)
    apply hinj
    haveI : ∀ a, IsMonHom (act a) := hm
    rw [hA, diagMap_add, MonObj.mul_comp, hA, hA, hadd, MonObj.comp_mul]
  exact ⟨RingHom.mk' ⟨⟨A, one⟩, mul⟩ add, hA⟩

end Act

section abelian₂

def abelian₂ (Ch : Type) [AddCommGroup Ch] : Type := Ch →+ ℤ

variable {Ch : Type} [AddCommGroup Ch]

instance : AddCommGroup (abelian₂ Ch) := inferInstanceAs (AddCommGroup (Ch →+ ℤ))

def lamDual : abelian₂ Ch ≃ₗ[ℤ] Module.Dual ℤ Ch :=
  AddEquiv.toIntLinearEquiv
    { toFun := fun l => AddMonoidHom.toIntLinearMap l
      invFun := fun f => (f.toAddMonoidHom : Ch →+ ℤ)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }

instance [Module.Free ℤ Ch] [Module.Finite ℤ Ch] : Module.Free ℤ (abelian₂ Ch) :=
  Module.Free.of_equiv (lamDual (Ch := Ch)).symm

instance [Module.Free ℤ Ch] [Module.Finite ℤ Ch] : Module.Finite ℤ (abelian₂ Ch) :=
  Module.Finite.equiv (lamDual (Ch := Ch)).symm

variable (k : Type) [Field k]

def lamTo : abelian₂ Ch →ₗ[ℤ] (Ch →+ k) :=
  AddMonoidHom.toIntLinearMap
    { toFun := fun l => (Int.castAddHom k).comp (show Ch →+ ℤ from l)
      map_zero' := by ext; exact Int.cast_zero
      map_add' := fun a b => by ext χ; exact Int.cast_add _ _ }

def tenMap : TensorProduct ℤ k (abelian₂ Ch) →ₗ[k] (Ch →+ k) := LinearMap.liftBaseChange k (lamTo k)

theorem tenMap_tmul (c : k) (l : abelian₂ Ch) : tenMap k (c ⊗ₜ[ℤ] l) = c • lamTo k l := by
  simp [tenMap]

theorem tenMap_bijective [Module.Free ℤ Ch] [Module.Finite ℤ Ch] : Function.Bijective (tenMap (Ch := Ch) k) := by
  let e : TensorProduct ℤ k (abelian₂ Ch) ≃ₗ[ℤ] (Ch →+ k) :=
    (TensorProduct.congr (LinearEquiv.refl ℤ k) lamDual) ≪≫ₗ (TensorProduct.comm ℤ k (Module.Dual ℤ Ch)) ≪≫ₗ
      (dualTensorHomEquiv ℤ Ch k) ≪≫ₗ (addMonoidHomLequivInt ℤ).symm
  have : (tenMap (Ch := Ch) k : _ → _) = e := by
    funext z
    induction z with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul c l =>
      rw [tenMap_tmul]
      refine AddMonoidHom.ext fun χ => ?_
      have e2 : ((dualTensorHomEquiv ℤ Ch k) (lamDual l ⊗ₜ[ℤ] c)) χ = (lamDual l χ) • c := by
        simp [dualTensorHomEquiv]
      have e3 : (e (c ⊗ₜ[ℤ] l)) χ = ((dualTensorHomEquiv ℤ Ch k) (lamDual l ⊗ₜ[ℤ] c)) χ := rfl
      rw [e3, e2, zsmul_eq_mul, _root_.mul_comm]
      rfl
  rw [this]
  exact e.bijective

def lamEnd {O : Type} [CommRing O] (h : O →+* AddMonoid.End Ch) : O →+* Module.End ℤ (abelian₂ Ch) :=
  RingHom.mk'
    { toFun := fun a => AddMonoidHom.toIntLinearMap
        { toFun := fun l => (show Ch →+ ℤ from l).comp (h a : Ch →+ Ch)
          map_zero' := rfl
          map_add' := fun _ _ => rfl }
      map_one' := LinearMap.ext fun l => AddMonoidHom.ext fun χ => by
        change (show Ch →+ ℤ from l) ((h 1 : Ch →+ Ch) χ) = (show Ch →+ ℤ from l) χ
        rw [map_one]
        rfl
      map_mul' := fun a b => LinearMap.ext fun l => AddMonoidHom.ext fun χ => by
        change (show Ch →+ ℤ from l) ((h (a * b) : Ch →+ Ch) χ) =
          (show Ch →+ ℤ from l) ((h b : Ch →+ Ch) ((h a : Ch →+ Ch) χ))
        rw [_root_.mul_comm a b, map_mul]
        rfl }
    (fun a b => LinearMap.ext fun l => AddMonoidHom.ext fun χ => by
      change (show Ch →+ ℤ from l) ((h (a + b) : Ch →+ Ch) χ) =
        (show Ch →+ ℤ from l) ((h a : Ch →+ Ch) χ) + (show Ch →+ ℤ from l) ((h b : Ch →+ Ch) χ)
      have e : (h (a + b) : Ch →+ Ch) χ = (h a : Ch →+ Ch) χ + (h b : Ch →+ Ch) χ := by
        rw [map_add]; rfl
      rw [e]
      exact map_add (show Ch →+ ℤ from l) _ _)

end abelian₂

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}}

theorem pt_sum {t : SAB H X} {S : Type} [CommRing S] {x : Sp S ⟶ X} {V : Type} [AddCommGroup V] [Module S V]
    (M : LieModel t.G x V) :
    ∀ {m : ℕ} (c : Fin m → V), (List.ofFn fun l => M.pt (c l)).prod = M.pt (∑ l, c l)
  | 0, c => by
    simp only [List.ofFn_zero, List.prod_nil, Finset.univ_eq_empty, Finset.sum_empty]
    have h := M.add 0 0
    rw [add_zero] at h
    exact (mul_left_cancel (h.symm.trans (_root_.mul_one _).symm)).symm
  | m + 1, c => by
    rw [List.ofFn_succ, List.prod_cons, pt_sum M (fun l => c l.succ), Fin.sum_univ_succ, M.add]

theorem isCombAtG_lie {t : SAB H X} {S : Type} [CommRing S] {x : Sp S ⟶ X} {V : Type} [AddCommGroup V] [Module S V]
    (M : LieModel t.G x V) {m : ℕ} (b : Fin m → V) (cf : Fin m → S) :
    Formalism.L2.Pj.IsCombAtG t x (fun l => (M.pt (b l)).left) cf (M.pt (∑ l, cf l • b l)).left :=
  ⟨fun l => M.pt (cf l • b l), fun l => by rw [M.smul]; rfl, by rw [pt_sum]⟩

variable [StarRing (𝓞 E)]

theorem germ_coord {t : SAB H X} {S : Type} [CommRing S] {x : Sp S ⟶ X} {d : ℕ} (g : GermAt t x d)
    {V : Type} [AddCommGroup V] [Module S V] (M : LieModel t.G x V) (e : V ≃ₗ[S] (Fin d → S))
    (he : ∀ v, Formalism.L2.Pj.IsCombAtG t x g.tg (e v) (M.pt v).left) (l : Fin d) :
    (M.pt (e.symm (Pi.single l 1))).left = g.tg l := by
  have tan : ∀ l, ∃ b : V, (M.pt b).left = g.tg l := fun l => by
    have ht := g.tan l
    obtain ⟨b, hb⟩ := M.onto (Over.homMk (g.tg l) ht.1) ht.2
    exact ⟨b, congrArg (fun u => u.left) hb⟩
  choose b hb using tan
  have hg : (fun l => (M.pt (b l)).left) = g.tg := funext hb
  have h1 : Formalism.L2.Pj.IsCombAtG t x g.tg (Pi.single l 1) (M.pt (b l)).left := by
    have := isCombAtG_lie M b (Pi.single l 1)
    rw [hg] at this
    have e2 : ∑ i, (Pi.single l (1 : S) : Fin d → S) i • b i = b l := by
      simp [Pi.single_apply, ite_smul]
    rwa [e2] at this
  have h2 := he (b l)
  have h3 := (g.basis (M.pt (b l)).left (by rw [hb]; exact g.tan l)).unique h1 h2
  rw [h3, LinearEquiv.symm_apply_apply, hb]

end Main

section Fin

theorem charVal_eq {S : Scheme.{0}} {Ch : Type} [AddCommGroup Ch] {A : Type} [CommRing A] {a : Sp A ⟶ S}
    (w : Over.mk a ⟶ splitTorus S Ch) (χ : Ch) : GlobalTheory.CompanionTheory.Ar.charVal w χ = GlobalTheory.Diag.charVal w χ :=
  (GlobalTheory.Diag.charVal_eq_torusFst w χ).symm

theorem pt_comp_diagMap {k : Type} [Field k] {Ch : Type} [AddCommGroup Ch]
    (MT : LieModel (splitTorus (Sp k) Ch) (𝟙 _) (Ch →+ k)) (hMT : IsCocharLie MT) (δ : Ch →+ k) (u : Ch →+ Ch) :
    MT.pt (δ.comp u) = MT.pt δ ≫ GlobalTheory.Diag.diagMap (Sp k) u := by
  apply GlobalTheory.Diag.charVal_ext
  intro χ
  rw [GlobalTheory.Diag.charVal_comp_diagMap, ← charVal_eq, ← charVal_eq, hMT, hMT]
  rfl

theorem tenMap_end {k : Type} [Field k] {Ch : Type} [AddCommGroup Ch] {O : Type} [CommRing O]
    (h : O →+* AddMonoid.End Ch) (a : O) (z : TensorProduct ℤ k (abelian₂ Ch)) :
    tenMap k (LinearMap.baseChange k (lamEnd h a) z) = (tenMap k z).comp (h a : Ch →+ Ch) := by
  induction z with
  | zero =>
    simp only [map_zero]
    rfl
  | add x y hx hy =>
    rw [map_add, map_add, hx, hy, map_add]
    rfl
  | tmul c l =>
    rw [LinearMap.baseChange_tmul, tenMap_tmul, tenMap_tmul]
    rfl

end Fin

theorem lie_seq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X : Scheme.{0}) (t : SAB H X) (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] (x : Sp k ⟶ X) (Q : AbQuot t x) (d d' : ℕ) (g : GermAt t x d) (gB : GermAt Q.tB (𝟙 (Sp k)) d'), ∃ (Λ : Type) (_ : AddCommGroup Λ) (_ : Module (𝓞 E) Λ) (_ : Module.Free ℤ Λ) (_ : Module.Finite ℤ Λ) (P : Matrix (Fin d') (Fin d) k) (j : TensorProduct ℤ k Λ →ₗ[k] (Fin d → k)), Q.IsDiff g gB P ∧ Function.Surjective P.mulVec ∧ Function.Injective j ∧ (∀ u, P.mulVec u = 0 ↔ u ∈ LinearMap.range j) ∧ (∀ a, P * rho g.B a = rho gB.B a * P) ∧ ∀ a v, j (LinearMap.baseChange k ((LinearMap.lsmul (𝓞 E) Λ a).restrictScalars ℤ) v) = (rho g.B a).mulVec (j v) := by
  intro E _ _ _ H _ hstar X t k _ _ p _ _ x Q d d' g gB
  haveI := Q.q_hom
  haveI := Q.i_hom
  let Gk := (Over.pullback x).obj t.G
  let actk : 𝓞 E → (Gk ⟶ Gk) := fun a => (Over.pullback x).map (t.act.act a)
  obtain ⟨LG, _, _, ⟨Mk⟩⟩ := lieModel_exists (Sp k) Gk k (𝟙 _)
  obtain ⟨LB, _, _, ⟨MB⟩⟩ := lieModel_exists (Sp k) Q.tB.G k (𝟙 _)
  obtain ⟨MT, hMT⟩ := GlobalTheory.T.exists_cocharacter_lie_model (Sp k) Q.Ch k (𝟙 _)
  have hgp : IsGrpPullback Gk t.G x (pullback.fst t.G.hom x) := isGrpPullback_pullback t.G x
  obtain ⟨M, hM⟩ : ∃ M : LieModel t.G x LG, ∀ e, (Mk.pt e).left ≫ pullback.fst t.G.hom x = (M.pt e).left := by
    have := (LiePull.lieModel_pullback X (Sp k) t.G Gk x _ hgp k (𝟙 _) LG).2 Mk
    rwa [Category.id_comp] at this
  obtain ⟨rG, hrG, -⟩ := lieModel_exists_unique_act X t.G k x LG M (𝓞 E) t.act.act t.act.hom t.act.one t.act.mul
    t.act.add
  obtain ⟨rB, hrB, -⟩ := lieModel_exists_unique_act (Sp k) Q.tB.G k (𝟙 _) LB MB (𝓞 E) Q.tB.act.act Q.tB.act.hom
    Q.tB.act.one Q.tB.act.mul Q.tB.act.add
  have hleft : ∀ a, (actk a).left ≫ pullback.fst t.G.hom x = pullback.fst t.G.hom x ≫ (t.act.act a).left :=
    fun a => pullback.lift_fst _ _ _
  have hMk : ∀ a e, Mk.pt (rG a e) = Mk.pt e ≫ actk a := by
    intro a e
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · rw [hM, Over.comp_left, Category.assoc, hleft, ← Category.assoc, hM, hrG a e]
      rfl
    · exact (Over.w (Mk.pt (rG a e))).trans (Over.w (Mk.pt e ≫ actk a)).symm
  obtain ⟨dq, hdq, -⟩ := lieModel_exists_unique_diff (Sp k) Gk Q.tB.G k (𝟙 _) LG LB Mk MB Q.q
  obtain ⟨di, hdi, -⟩ := lieModel_exists_unique_diff (Sp k) (splitTorus (Sp k) Q.Ch) Gk k (𝟙 _) _ LG MT Mk Q.i
  obtain ⟨hinj, hex⟩ := lie_kernel Q.i Q.q Q.isKernel MT Mk MB di dq hdi hdq
  have hsurj := lie_surjective Q.q (smooth_q Q) Mk MB dq hdq
  have hequiv : ∀ a e, dq (rG a e) = rB a (dq e) := by
    intro a e
    apply MB.inj
    rw [hdq, hMk, Category.assoc, Q.act_q, ← Category.assoc, ← hdq]
    exact (hrB a (dq e)).symm
  obtain ⟨h, hh⟩ := exists_charAct Q.i Q.q Q.isKernel actk Q.tB.act.act
    (fun a => by haveI := t.act.hom a; infer_instance) Q.tB.act.hom
    (by simp only [actk, t.act.one]; exact (Over.pullback x).map_id _)
    (fun a b => by simp only [actk, t.act.mul]; exact (Over.pullback x).map_comp _ _)
    (fun a b => by simp only [actk, t.act.add]; exact Functor.map_mul (Over.pullback x) _ _)
    Q.act_q
  have hT : ∀ a δ, di (δ.comp (h a : Q.Ch →+ Q.Ch)) = rG a (di δ) := by
    intro a δ
    apply Mk.inj
    rw [hdi, hMk, hdi, show MT.pt (δ.comp (h a : Q.Ch →+ Q.Ch)) = _ from pt_comp_diagMap MT hMT δ (h a),
      Category.assoc, Category.assoc, hh]
  obtain ⟨eG, hcG, hrhoG⟩ := GlobalTheory.T.formal_germ_lie_basis E H hstar X t k x d g LG M
  obtain ⟨eB, hcB, hrhoB⟩ := GlobalTheory.T.formal_germ_lie_basis E H hstar (Sp k) Q.tB k (𝟙 _) d' gB LB MB
  let f : (Fin d → k) →ₗ[k] (Fin d' → k) := eB.toLinearMap ∘ₗ dq ∘ₗ eG.symm.toLinearMap
  let P : Matrix (Fin d') (Fin d) k := LinearMap.toMatrix' f
  have hP : ∀ u, P.mulVec u = f u := fun u => LinearMap.toMatrix'_mulVec f u
  let j : TensorProduct ℤ k (abelian₂ Q.Ch) →ₗ[k] (Fin d → k) := eG.toLinearMap ∘ₗ di ∘ₗ tenMap k
  letI modL : Module (𝓞 E) (abelian₂ Q.Ch) := Module.compHom _ (lamEnd h)
  refine ⟨abelian₂ Q.Ch, inferInstance, modL, inferInstance, inferInstance, P, j, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro l v hv1 hv2
    have hv : v = (Mk.pt (eG.symm (Pi.single l 1))).left := by
      apply pullback.hom_ext
      · rw [hM, germ_coord g M eG hcG l]
        exact hv1
      · exact hv2.trans (Over.w (Mk.pt (eG.symm (Pi.single l 1)))).symm
    have e1 : v ≫ Q.q.left = (MB.pt (dq (eG.symm (Pi.single l 1)))).left := by
      rw [hdq, hv]; rfl
    rw [e1]
    have e2 : (fun i => P i l) = eB (dq (eG.symm (Pi.single l 1))) := by
      funext i
      have := congrFun (hP (Pi.single l 1)) i
      rw [Matrix.mulVec_single_one] at this
      exact this
    rw [e2]
    exact hcB _
  · intro w
    obtain ⟨u, hu⟩ := hsurj (eB.symm w)
    exact ⟨eG u, by rw [hP]; simp [f, hu]⟩
  · exact eG.injective.comp (hinj.comp (tenMap_bijective k).1)
  · intro u
    rw [hP]
    constructor
    · intro hu
      have h0 : dq (eG.symm u) = 0 := eB.map_eq_zero_iff.1 hu
      obtain ⟨δ, hδ⟩ := (hex _).1 h0
      obtain ⟨z, rfl⟩ := (tenMap_bijective k).2 δ
      exact ⟨z, by simp [j, hδ]⟩
    · rintro ⟨z, rfl⟩
      have : dq (di (tenMap k z)) = 0 := (hex _).2 ⟨_, rfl⟩
      simp [f, j, this]
  · intro a
    have key : ∀ u, (P * rho g.B a).mulVec u = (rho gB.B a * P).mulVec u := by
      intro u
      obtain ⟨w, rfl⟩ := eG.surjective u
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hP, hP, ← hrhoG rG hrG a w]
      simp only [f, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
      rw [hequiv, hrhoB rB hrB]
    exact Matrix.toLin'.injective (LinearMap.ext fun u => by simpa [Matrix.toLin'_apply] using key u)
  · intro a v
    have e : (LinearMap.lsmul (𝓞 E) (abelian₂ Q.Ch) a).restrictScalars ℤ = lamEnd h a := rfl
    rw [e]
    simp only [j, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [tenMap_end, hT, hrhoG rG hrG]

end GlobalTheory.CompanionTheory.Ar.LieSeq
