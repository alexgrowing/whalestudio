import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsLocalUnitOfWeight
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UniqueFactorizationMonoidAddMonoidAlgebraOfFree

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS.LiftTorus

open GlobalTheory.TorsorUnit

section Algebra

variable {X : Type} [AddCommGroup X] {A C : Type} [CommRing A] [CommRing C]
  {α : A →+* C} {ρ : C →+* AddMonoidAlgebra C X}

theorem coaction_base (h : ∀ (R : Type) [CommRing R], IsTorsorOn R α ρ) (a : A) :
    ρ (α a) = AddMonoidAlgebra.single 0 (α a) := by
  have := RingHom.congr_fun ((h _).2.1 (cst X C) (univ X C)) a
  rwa [ev_univ] at this

theorem exists_eq_of_invariant (hα : α.FaithfullyFlat)
    (h : ∀ (R : Type) [CommRing R], IsTorsorOn R α ρ) (c : C)
    (hc : ρ c = AddMonoidAlgebra.single 0 c) : ∃ a, α a = c := by
  letI : Algebra A C := α.toAlgebra
  haveI : Module.FaithfullyFlat A C := hα
  obtain ⟨φ, hφ⟩ := (h (TensorProduct A C C)).2.2.2
    (Algebra.TensorProduct.includeRight : C →ₐ[A] TensorProduct A C C).toRingHom
    Algebra.TensorProduct.includeLeftRingHom
    (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap (R := A) (A := C) (B := C)).symm
  have h1 := RingHom.congr_fun hφ c
  rw [RingHom.comp_apply, hc, ev_single] at h1
  refine (Algebra.IsEffective.of_faithfullyFlat A C c).1 ?_
  rw [Algebra.TensorProduct.includeLeftSubRight_apply, sub_eq_zero]
  simpa using h1

theorem exists_homogeneous_cofactor (h : ∀ (R : Type) [CommRing R], IsTorsorOn R α ρ) {χ : X}
    {c c' : C} {a : A} (hcc : c * c' = α a) (hc : ρ c = AddMonoidAlgebra.single χ c) :
    ∃ d, c * d = α a ∧ ρ d = AddMonoidAlgebra.single (-χ) d := by
  refine ⟨(ρ c').coeff (-χ), ?_, coaction_coeff (h _) _ _⟩
  have h1 := congrArg (fun z => (ρ z).coeff 0) hcc
  simp only [map_mul, hc, coaction_base h] at h1
  simpa using h1

theorem exists_unit [Subsingleton (CommRing.Pic A)] (hα : α.FaithfullyFlat)
    (h : ∀ (R : Type) [CommRing R], IsTorsorOn R α ρ) (χ : X) :
    ∃ u : Cˣ, ρ u.val = AddMonoidAlgebra.single χ u.val := by
  letI : Algebra A C := α.toAlgebra
  haveI : Module.FaithfullyFlat A C := hα
  let M : X → Submodule A C := fun x =>
    { carrier := {c | ρ c = AddMonoidAlgebra.single x c}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [map_add, ha, hb, AddMonoidAlgebra.single_add]
      zero_mem' := by simp
      smul_mem' := fun a c hc => by
        simp only [Set.mem_setOf_eq] at hc ⊢
        change ρ (α a * c) = AddMonoidAlgebra.single x (α a * c)
        rw [map_mul, coaction_base h, hc, AddMonoidAlgebra.single_mul_single, zero_add] }
  have hM : ∀ x c, c ∈ M x ↔ ρ c = AddMonoidAlgebra.single x c := fun _ _ => Iff.rfl
  have hmul : M χ * M (-χ) = 1 := by
    apply le_antisymm
    · refine Submodule.mul_le.2 fun c hc d hd => ?_
      obtain ⟨a, ha⟩ := exists_eq_of_invariant hα h (c * d) (by
        rw [map_mul, (hM _ _).1 hc, (hM _ _).1 hd, AddMonoidAlgebra.single_mul_single,
          add_neg_cancel])
      exact Submodule.mem_one.2 ⟨a, ha⟩
    · rw [Submodule.one_le]
      let p : Ideal A := (M χ * M (-χ)).comap (Algebra.linearMap A C)
      by_cases hp : p = ⊤
      · have : (1 : A) ∈ p := hp ▸ Submodule.mem_top
        simpa [p] using this
      · obtain ⟨a, ha, c, c', hcc, hc⟩ := exists_homogeneous hα h χ p hp
        obtain ⟨d, hd, hd'⟩ := exists_homogeneous_cofactor h hcc hc
        refine absurd ?_ ha
        change α a ∈ M χ * M (-χ)
        rw [← hd]
        exact Submodule.mul_mem_mul hc hd'
  let I : (Submodule A C)ˣ := Units.mkOfMulEqOne _ _ hmul
  have hI : I ∈ (Submodule.unitsToPic A C).ker := Subsingleton.elim _ _
  rw [Submodule.ker_unitsToPic] at hI
  obtain ⟨u, hu⟩ := hI
  refine ⟨u, (hM _ _).1 ?_⟩
  have h1 : Submodule.span A {u.val} = M χ := congrArg Units.val hu
  rw [← h1]
  exact Submodule.mem_span_singleton_self _

theorem exists_units [Subsingleton (CommRing.Pic A)] [Module.Free ℤ X] (hα : α.FaithfullyFlat)
    (h : ∀ (R : Type) [CommRing R], IsTorsorOn R α ρ) :
    ∃ u : Multiplicative X →* Cˣ, ∀ x,
      ρ (u (Multiplicative.ofAdd x)).val =
        AddMonoidAlgebra.single x (u (Multiplicative.ofAdd x)).val := by
  choose v hv using exists_unit hα h
  let b := Module.Free.chooseBasis ℤ X
  let l : X →ₗ[ℤ] Additive Cˣ := b.constr ℤ fun j => Additive.ofMul (v (b j))
  let u : Multiplicative X →* Cˣ := AddMonoidHom.toMultiplicativeLeft l.toAddMonoidHom
  let w₁ : Multiplicative X →* (AddMonoidAlgebra C X)ˣ := (Units.map ρ.toMonoidHom).comp u
  let w₂ : Multiplicative X →* (AddMonoidAlgebra C X)ˣ :=
    univ X C * (Units.map (cst X C).toMonoidHom).comp u
  have hw₂ : ∀ x, (w₂ (Multiplicative.ofAdd x)).val =
      AddMonoidAlgebra.single x (u (Multiplicative.ofAdd x)).val := fun x => by
    change AddMonoidAlgebra.single x 1 * AddMonoidAlgebra.single 0 _ = _
    rw [AddMonoidAlgebra.single_mul_single, add_zero, _root_.one_mul]
  have hw : (MonoidHom.toAdditiveRight w₁).toIntLinearMap =
      (MonoidHom.toAdditiveRight w₂).toIntLinearMap := by
    refine b.ext fun j => ?_
    have hu : u (Multiplicative.ofAdd (b j)) = v (b j) :=
      congrArg Additive.toMul (b.constr_basis ℤ (fun j => Additive.ofMul (v (b j))) j)
    refine congrArg Additive.ofMul (Units.ext ?_)
    refine Eq.trans ?_ (hw₂ (b j)).symm
    change ρ (u (Multiplicative.ofAdd (b j))).val = _
    rw [hu, hv]
  refine ⟨u, fun x => Eq.trans ?_ (hw₂ x)⟩
  exact congrArg (fun z => (Additive.toMul z).val) (LinearMap.congr_fun hw x)

theorem exists_retraction [Subsingleton (CommRing.Pic A)] [Module.Free ℤ X]
    (hα : α.FaithfullyFlat) (h : ∀ (R : Type) [CommRing R], IsTorsorOn R α ρ) :
    ∃ σ : C →+* A, σ.comp α = RingHom.id A := by
  obtain ⟨u, hu⟩ := exists_units hα h
  let τ : C →+* C := (ev (RingHom.id C) u⁻¹).comp ρ
  have hτα : τ.comp α = α := (h C).2.1 _ _
  have hτ : ∀ c, ∃ a, α a = τ c := fun c => by
    refine exists_eq_of_invariant hα h _ ?_
    change ρ (ev (RingHom.id C) u⁻¹ (ρ c)) = cst X C (ev (RingHom.id C) u⁻¹ (ρ c))
    rw [← AddMonoidAlgebra.sum_coeff_single (ρ c), Finsupp.sum]
    simp only [map_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    have h1 : u⁻¹ (Multiplicative.ofAdd x) = u (Multiplicative.ofAdd (-x)) := by
      rw [ofAdd_neg, map_inv]; rfl
    rw [ev_single, h1, RingHom.id_apply, map_mul, coaction_coeff (h _), hu,
      AddMonoidAlgebra.single_mul_single, add_neg_cancel, cst_apply]
  choose σ hσ using hτ
  have inj := hα.injective
  refine ⟨⟨⟨⟨σ, inj ?_⟩, fun a b => inj ?_⟩, inj ?_, fun a b => inj ?_⟩, RingHom.ext fun a => inj ?_⟩
  · rw [hσ, map_one, map_one]
  · simp only [hσ, map_mul]
  · simp only [hσ, map_zero]
  · simp only [hσ, map_add]
  · exact (hσ _).trans (RingHom.congr_fun hτα a)

end Algebra

theorem exists_pullback_grp {C : Type*} [Category C] [CartesianMonoidalCategory C] [HasPullbacks C]
    {G B H : C} [GrpObj G] [GrpObj B] [GrpObj H] (q : G ⟶ B) (f : H ⟶ B) [IsMonHom q] [IsMonHom f] :
    ∃ (E : C) (_ : GrpObj E) (p : E ⟶ G) (r : E ⟶ H), IsMonHom p ∧ IsMonHom r ∧ IsPullback p r q f := by
  let q' : Grp.mk G ⟶ Grp.mk B := Grp.homMk q
  let f' : Grp.mk H ⟶ Grp.mk B := Grp.homMk f
  have h := (IsPullback.of_hasPullback q' f').map (Grp.forget C)
  exact ⟨(pullback q' f').X, inferInstance, (pullback.fst q' f').hom.hom, (pullback.snd q' f').hom.hom,
    inferInstance, inferInstance, h⟩

theorem exists_ker_pullback {C : Type*} [Category C] [CartesianMonoidalCategory C]
    {T G B H E : C} [GrpObj T] [GrpObj G] [GrpObj B] [GrpObj H] [GrpObj E] {i : T ⟶ G} {q : G ⟶ B}
    {f : H ⟶ B} {p : E ⟶ G} {r : E ⟶ H} [IsMonHom i] [IsMonHom f] [IsMonHom p] [IsMonHom r]
    (hi : IsPullback i (toUnit _) q η[B]) (h : IsPullback p r q f) :
    ∃ j : T ⟶ E, IsMonHom j ∧ IsPullback j (toUnit _) r η[H] := by
  have w : i ≫ q = (toUnit T ≫ η[H]) ≫ f := by
    rw [hi.w, Category.assoc, IsMonHom.one_hom]
  refine ⟨h.lift i _ w, ⟨h.hom_ext ?_ ?_, h.hom_ext ?_ ?_⟩, ?_⟩
  · simp
  · simp
  · simp [tensorHom_comp_tensorHom_assoc]
  · simp only [Category.assoc, h.lift_snd, IsMonHom.mul_hom, tensorHom_comp_tensorHom_assoc]
  · refine IsPullback.of_right ?_ (h.lift_snd _ _ _) h
    rw [h.lift_fst, IsMonHom.one_hom]
    exact hi

theorem exists_section {S : Scheme.{0}} {X : Type} [AddCommGroup X] [Module.Free ℤ X] {G B : Over S}
    [GrpObj G] [GrpObj B] {q : G ⟶ B} {i : splitTorus S X ⟶ G} [IsMonHom q] [IsMonHom i]
    [Flat q.left] [Surjective q.left] [IsAffineHom q.left] [IsAffine B.left]
    [Subsingleton (CommRing.Pic Γ(B.left, ⊤))]
    (hi : IsPullback i (toUnit _) q η[B]) : ∃ s : B ⟶ G, s ≫ q = 𝟙 B := by
  have hV : IsAffineOpen (⊤ : B.left.Opens) := isAffineOpen_top _
  have hU : IsAffineOpen (q.left ⁻¹ᵁ ⊤) := hV.preimage q.left
  obtain ⟨ρ, hρ⟩ := exists_coaction hi hU
  have htor : ∀ (R : Type) [CommRing R], IsTorsorOn R (q.left.appLE ⊤ _ le_rfl).hom ρ :=
    fun R _ => (isTorsorOn hi hV hU hρ (Spec (.of R))).of_equiv
      (Scheme.ΓSpecIso (.of R)).symm.commRingCatIsoToRingEquiv
  obtain ⟨σ, hσ⟩ := exists_retraction (faithfullyFlat_appLE q.left hV hU) htor
  have h1 : pt hU σ ≫ q.left = 𝟙 B.left := by
    rw [pt_comp hU hV q.left le_rfl, hσ]
    obtain ⟨θ, hθ⟩ := exists_eq_pt hV (𝟙 B.left) le_rfl
    have h2 := pt_appLE hV θ (le_pt_preimage hV θ)
    have h3 : ∀ (g : B.left ⟶ B.left) (e : ⊤ ≤ g ⁻¹ᵁ ⊤), g = 𝟙 _ →
        (g.appLE ⊤ ⊤ e).hom = RingHom.id _ := by
      rintro _ e rfl
      simp only [Scheme.Hom.appLE, Scheme.Hom.id_app]
      exact congrArg CommRingCat.Hom.hom ((Category.id_comp _).trans (B.left.presheaf.map_id _))
    rw [hθ, ← h2, h3 _ _ hθ.symm]
  refine ⟨Over.homMk (pt hU σ) ?_, Over.OverMorphism.ext h1⟩
  rw [← Over.w q, ← Category.assoc, h1, Category.id_comp]

theorem subsingleton_pic_torus (k : Type) [Field k] (X : Type) [AddCommGroup X] [Module.Free ℤ X] :
    Subsingleton (CommRing.Pic Γ((splitTorus (Sp k) X).left, ⊤)) := by
  have := GlobalTheory.subsingleton_pic_addMonoidAlgebra_of_free k X
  let e : Γ((splitTorus (Sp k) X).left, ⊤) ≃+* AddMonoidAlgebra k X :=
    RingEquiv.ofBijective (Rosenlicht.torusGamma k X).hom (Rosenlicht.torusGamma_bijective k X)
  have key : ∀ x : CommRing.Pic Γ((splitTorus (Sp k) X).left, ⊤), x =
      CommRing.Pic.mapRingHom e.symm.toRingHom (CommRing.Pic.mapRingHom e.toRingHom x) := fun x => by
    rw [CommRing.Pic.mapRingHom_mapRingHom, e.symm_toRingHom_comp_toRingHom,
      CommRing.Pic.mapRingHom_id_apply]
  refine ⟨fun x y => ?_⟩
  rw [key x, key y, Subsingleton.elim (CommRing.Pic.mapRingHom e.toRingHom x) _]

end GlobalTheory.SS.LiftTorus

namespace GlobalTheory.SS

open LiftTorus in

theorem exists_lift_oneParameter : ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G], SmConn G → ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (B : Over (Sp k)) [GrpObj B] (i : splitTorus (Sp k) X ⟶ G) (q : G ⟶ B), IsQuot i q → ∀ f : Gm (Sp k) ⟶ B, IsMonHom f → ∃ j : Gm (Sp k) ⟶ G, IsMonHom j ∧ j ≫ q = f := by
  intro k _ _ G _ _ X _ _ _ B _ i q ⟨_, _, hfl, hsu, haf, hi, _⟩ f _
  obtain ⟨E, _, p, r, _, _, hE⟩ := exists_pullback_grp q f
  obtain ⟨i', _, hi'⟩ := exists_ker_pullback hi hE
  have hE' : IsPullback p.left r.left q.left f.left := hE.map (Over.forget _)
  haveI : Flat r.left := MorphismProperty.of_isPullback hE' hfl
  haveI : Surjective r.left := MorphismProperty.of_isPullback hE' hsu
  haveI : IsAffineHom r.left := MorphismProperty.of_isPullback hE' haf
  haveI : IsAffine (Gm (Sp k)).left := .of_isIso (Rosenlicht.torusIso k (ULift.{0} ℤ)).inv
  haveI := subsingleton_pic_torus k (ULift.{0} ℤ)
  obtain ⟨s, hs⟩ := exists_section hi'
  have hs₀ : (s ≫ p) ≫ q = f := by rw [Category.assoc, hE.w, ← Category.assoc, hs, Category.id_comp]
  have hone : ∀ {Z : Over (Sp k)}, (1 : Z ⟶ Gm (Sp k)) ≫ f = 1 := fun {Z} => MonObj.one_comp f
  let j : Gm (Sp k) ⟶ G := (s ≫ p) * ((1 : Gm (Sp k) ⟶ Gm (Sp k)) ≫ s ≫ p)⁻¹
  have hj : j ≫ q = f := by
    rw [MonObj.mul_comp, GrpObj.inv_comp, Category.assoc 1, hs₀, hone, inv_one, _root_.mul_one]
  have hj1 : ∀ {Z : Over (Sp k)}, (1 : Z ⟶ Gm (Sp k)) ≫ j = 1 := fun {Z} => by
    rw [MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc 1 1, MonObj.comp_one, mul_inv_cancel]
  clear_value j
  let c : Gm (Sp k) ⊗ Gm (Sp k) ⟶ G :=
    ((fst _ _ * snd _ _) ≫ j) * ((fst _ _ ≫ j) * (snd _ _ ≫ j))⁻¹
  have hc : c ≫ q = toUnit _ ≫ η[B] := by
    rw [MonObj.mul_comp _ _ q, GrpObj.inv_comp, MonObj.mul_comp _ _ q, Category.assoc, Category.assoc,
      Category.assoc, hj, MonObj.mul_comp _ _ f, mul_inv_cancel, Hom.one_def]
  have hcomp : ∀ a b : Gm (Sp k) ⟶ Gm (Sp k),
      lift a b ≫ c = ((a * b) ≫ j) * ((a ≫ j) * (b ≫ j))⁻¹ := fun a b => by
    rw [MonObj.comp_mul, GrpObj.comp_inv, MonObj.comp_mul, ← Category.assoc, MonObj.comp_mul,
      lift_fst_assoc, lift_snd_assoc, lift_fst, lift_snd]
  have hax : ∀ z : Gm (Sp k) ⟶ Gm (Sp k) ⊗ Gm (Sp k), z ≫ c = 1 →
      z ≫ hi.lift c _ hc = toUnit _ ≫ η := fun z hz => by
    refine hi.hom_ext ?_ (toUnit_unique _ _)
    rw [Category.assoc, hi.lift_fst, hz, Category.assoc, IsMonHom.one_hom, Hom.one_def]
  haveI : TwoUniqueSums (ULift.{0} ℤ) :=
    (TwoUniqueSums.of_injective_addHom (AddEquiv.ulift : ULift.{0} ℤ ≃+ ℤ).toAddHom
      (AddEquiv.ulift : ULift.{0} ℤ ≃+ ℤ).injective inferInstance)
  have h0 := splitTorus_rigidity k (ULift.{0} ℤ) X (hi.lift c _ hc)
    (hax _ (by rw [← Hom.one_def, hcomp, hj1, _root_.mul_one, _root_.mul_one, mul_inv_cancel]))
    (hax _ (by rw [← Hom.one_def, hcomp, hj1, _root_.one_mul, _root_.one_mul, mul_inv_cancel]))
  have h1 : c = 1 := by
    rw [← hi.lift_fst c _ hc, h0, Category.assoc, IsMonHom.one_hom, Hom.one_def]
  have h2 := mul_inv_eq_one.1 h1
  refine ⟨j, ⟨?_, ?_⟩, hj⟩
  · have := hj1 (Z := 𝟙_ _)
    simpa [Hom.one_def] using this
  · rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp, lift_fst_comp_snd_comp] at h2
    exact h2

end GlobalTheory.SS
