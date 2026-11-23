import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistSectionsLocallyGeneratedStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory.EtC.TwMulSurj

variable {R : Type} [CommRing R]

theorem loc_top (U : Scheme.{0}) {P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : ∀ V g, P V g) : Loc U P :=
  ⟨⊤, Scheme.etaleTopology.top_mem U, fun V g _ => h V g⟩

theorem loc_mono {U : Scheme.{0}} {P P' : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P) (h' : ∀ V g, P V g → P' V g) :
    Loc U P' := by
  obtain ⟨S, hS, hP⟩ := h
  exact ⟨S, hS, fun V g hg => h' V g (hP V g hg)⟩

theorem loc_and {U : Scheme.{0}} {P P' : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P) (h' : Loc U P') :
    Loc U fun V g => P V g ∧ P' V g := by
  obtain ⟨S, hS, hP⟩ := h
  obtain ⟨S', hS', hP'⟩ := h'
  exact ⟨S ⊓ S', GrothendieckTopology.intersection_covering _ hS hS', fun V g hg => ⟨hP V g hg.1, hP' V g hg.2⟩⟩

theorem loc_bind {U : Scheme.{0}} {P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} {P' : ∀ V : Scheme.{0}, (V ⟶ U) → Prop}
    (h : Loc U P) (h' : ∀ V g, P V g → Loc V fun W k => P' W (k ≫ g)) : Loc U P' := by
  classical
  obtain ⟨S, hS, hP⟩ := h
  let Rs : ∀ ⦃V : Scheme.{0}⦄ ⦃g : V ⟶ U⦄, S.arrows g → Sieve V := fun V g hg => (h' V g (hP V g hg)).choose
  refine ⟨Sieve.bind S.arrows Rs, Scheme.etaleTopology.bind_covering hS fun V g hg => (h' V g (hP V g hg)).choose_spec.1, ?_⟩
  rintro W _ ⟨V, k, g, hg, hk, rfl⟩
  exact (h' V g (hP V g hg)).choose_spec.2 W k hk

theorem map_comp_apply {F G H : Shv R} (f : F ⟶ G) (g : G ⟶ H) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (f ≫ g) x = Sec.map g (Sec.map f x) := rfl

theorem map_id_apply {F : Shv R} {U : Scheme.{0}} (x : Sec F U) : Sec.map (𝟙 F) x = x := rfl

theorem res_map {F G : Shv R} (f : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map f x) = Sec.map f (Sec.res g x) := by
  have := congrArg (fun m => m.hom x) (f.hom.naturality g.op)
  simpa using this.symm

theorem res_comp {F : Shv R} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (x : Sec F U) :
    Sec.res (k ≫ g) x = Sec.res k (Sec.res g x) := by
  simp [Sec.res]

theorem smap_add {F G : Shv R} (f : F ⟶ G) {U : Scheme.{0}} (x y : Sec F U) :
    Sec.map f (x + y) = Sec.map f x + Sec.map f y := map_add _ x y

theorem sres_add {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (x y : Sec F U) :
    Sec.res g (x + y) = Sec.res g x + Sec.res g y := map_add _ x y

theorem smap_nsmul {F G : Shv R} (f : F ⟶ G) {U : Scheme.{0}} (n : ℕ) (x : Sec F U) :
    Sec.map f (n • x) = n • Sec.map f x := map_nsmul _ n x

theorem sres_nsmul {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (n : ℕ) (x : Sec F U) :
    Sec.res g (n • x) = n • Sec.res g x := map_nsmul _ n x

theorem smap_zero {F G : Shv R} (f : F ⟶ G) {U : Scheme.{0}} : Sec.map f (0 : Sec F U) = 0 := map_zero _

theorem map_zero_hom {F G : Shv R} {U : Scheme.{0}} (x : Sec F U) : Sec.map (0 : F ⟶ G) x = 0 := by
  rfl

theorem eq_zero_of_isZero {F : Shv R} (hF : IsZero F) {U : Scheme.{0}} (x : Sec F U) : x = 0 := by
  rw [← map_id_apply x, hF.eq_of_src (𝟙 F) 0, map_zero_hom]

def Good {F G : Shv R} (φ : F ⟶ G) (U : Scheme.{0}) (x : Sec G U) : Prop :=
  Loc U fun V g => ∃ z : Sec F V, Sec.map φ z = Sec.res g x

theorem good_of {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} {x : Sec G U} (h : ∃ z, Sec.map φ z = x) : Good φ U x := by
  obtain ⟨z, rfl⟩ := h
  exact loc_top U fun V g => ⟨Sec.res g z, (res_map φ g z).symm⟩

theorem good_bind {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (x : Sec G U) {P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop}
    (hP : Loc U P) (h : ∀ V g, P V g → Good φ V (Sec.res g x)) : Good φ U x := by
  refine loc_bind hP fun V g hg => ?_
  obtain ⟨S, hS, hS'⟩ := h V g hg
  exact ⟨S, hS, fun W k hk => by obtain ⟨z, hz⟩ := hS' W k hk; exact ⟨z, by rw [hz, res_comp]⟩⟩

theorem good_add {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} {x x' : Sec G U} (h : Good φ U x) (h' : Good φ U x') :
    Good φ U (x + x') :=
  loc_mono (loc_and h h') fun _ g ⟨⟨z, hz⟩, ⟨z', hz'⟩⟩ => ⟨z + z', by rw [smap_add, sres_add, hz, hz']⟩

theorem good_zero {F G : Shv R} (φ : F ⟶ G) (U : Scheme.{0}) : Good φ U 0 := good_of φ ⟨0, smap_zero _⟩

end GlobalTheory.EtC.TwMulSurj

namespace GlobalTheory.EtC

open TwMulSurj in

theorem tw_mul_locSurj : ∀ (q : ℕ) [NeZero q] (i j k : ℤ), i + j = k → ∀ {K : Cx (ZMod q)}
    (τ : Pair (sgl (tw q i)) (sgl (tw q j)) K), τ.IsTensor → ∀ φ : tw q k ⟶ K.X 0,
    (∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)), Sec.map φ (twGen k ζ) =
      τ.mul U 0 0 0 (add_zero 0) (Sec.map (sglι _) (twGen i ζ)) (Sec.map (sglι _) (twGen j ζ))) →
    ∀ (U : Scheme.{0}) (y : Sec (K.X 0) U), Loc U fun V g => ∃ z : Sec (tw q k) V, Sec.map φ z = Sec.res g y := by
  intro q _ i j k hk K τ hτ φ hφ
  have hT := GlobalTheory.T.tateTwist_sections_locally_generated
  have key_gen : ∀ V (a : Sec (tw q i) V) (b : Sec (tw q j) V),
      Good φ V (τ.mul V 0 0 0 (add_zero 0) (Sec.map (sglι _) a) (Sec.map (sglι _) b)) := by
    intro V a b
    refine good_bind φ _ ((hT q i).1 V a) ?_
    rintro W g (ha | ⟨ζ, c, ha⟩)
    · apply good_of
      refine ⟨0, ?_⟩
      rw [smap_zero, τ.nat, res_map, res_map, ha, smap_zero]
      simp
    · refine good_bind φ _ ((hT q j).2.1 W ζ (Sec.res g b)) ?_
      rintro W' g' ⟨c', hb⟩
      apply good_of
      refine ⟨(c * c') • twGen k (ζ.map g'.appTop.hom), ?_⟩
      rw [smap_nsmul, hφ, τ.nat, τ.nat, res_map, res_map, res_map, res_map, ha, hb, sres_nsmul, (hT q i).2.2.2.1, smap_nsmul, smap_nsmul]
      simp [mul_comm, mul_smul]
  have key : ∀ V (x : Tens (sgl (tw q i)) (sgl (tw q j)) V 0), Good φ V (τ.lift V 0 x) := by
    intro V x
    induction x using DirectSum.induction_on with
    | zero => rw [map_zero]; exact good_zero φ V
    | of p t =>
      obtain ⟨⟨s, t'⟩, hst⟩ := p
      induction t using TensorProduct.induction_on with
      | zero => rw [map_zero, map_zero]; exact good_zero φ V
      | add u u' hu hu' => rw [map_add, map_add]; exact good_add φ hu hu'
      | tmul a b =>
        have hlift : τ.lift V 0 (DirectSum.of _ ⟨(s, t'), hst⟩ (a ⊗ₜ b)) = τ.mul V s t' 0 hst a b := by
          unfold Pair.lift
          erw [DirectSum.toModule_lof]
          rfl
        rw [hlift]
        by_cases hs : s = 0
        · subst hs
          obtain rfl : t' = 0 := by omega
          have ea : Sec.map (sglι _) (Sec.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (tw q i)).hom a) = a := by
            refine (map_comp_apply _ (sglι _) a).symm.trans ?_
            simp [sglι]; rfl
          have eb : Sec.map (sglι _) (Sec.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (tw q j)).hom b) = b := by
            refine (map_comp_apply _ (sglι _) b).symm.trans ?_
            simp [sglι]; rfl
          rw [← ea, ← eb]
          exact key_gen V _ _
        · have h0 : τ.mul V s t' 0 hst a b = 0 := by
            rw [eq_zero_of_isZero (F := (sgl (tw q i)).X s) (HomologicalComplex.isZero_single_obj_X _ _ _ _ hs) a]
            simp
          rw [h0]
          exact good_zero φ V
    | add x x' hx hx' => rw [map_add]; exact good_add φ hx hx'
  intro U y
  exact good_bind φ y (hτ.1 U 0 y) fun V g ⟨x, hx⟩ => hx ▸ key V x

end GlobalTheory.EtC
