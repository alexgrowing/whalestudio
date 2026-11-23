import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteOrderSt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDetGen
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FixTorsionOfForallGeometric
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AmpleRigid

open GlobalTheory.CechPic GlobalTheory.RealMult

set_option autoImplicit false in
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField in
attribute [local instance] Over.cartesianMonoidalCategory in

theorem _root_.GlobalTheory.AmpleRigid.mul_comp_of_grpPullback_id {S : Scheme.{0}} {G' G : Over S} [GrpObj G'] [GrpObj G]
    (f : G' ⟶ G) (h : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback G' G (𝟙 S) f.left) {T : Over S} (x y : T ⟶ G') :
    (x * y) ≫ f = (x ≫ f) * (y ≫ f) := by
  have H := h.2 T x y
  revert H
  generalize hg : T.hom ≫ 𝟙 S = g
  rw [Category.comp_id] at hg
  subst hg
  intro H
  exact Over.OverMorphism.ext (H (x ≫ f) (y ≫ f) rfl rfl).symm

set_option autoImplicit false in
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField in
attribute [local instance] Over.cartesianMonoidalCategory in

theorem _root_.GlobalTheory.AmpleRigid.isMonHom_of_mul_comp {S : Scheme.{0}} {G H : Over S} [GrpObj G] [GrpObj H]
    (e : G ⟶ H) (mul : ∀ (T : Over S) (x y : T ⟶ G), (x * y) ≫ e = (x ≫ e) * (y ≫ e)) :
    IsMonHom e := by
  have hone : (1 : 𝟙_ (Over S) ⟶ G) ≫ e = 1 := by
    have h1 := mul (𝟙_ (Over S)) 1 1
    rw [_root_.mul_one] at h1
    exact _root_.left_eq_mul.mp h1
  refine ⟨?_, ?_⟩
  · simpa [Hom.one_def] using hone
  · have h2 := mul (G ⊗ G) (fst G G) (snd G G)
    simpa [Hom.mul_def] using h2

variable {F : Type} [Field F] [NumberField F] {𝔠 : FracId F}

theorem exists_totPos_mem (𝔠 : FracId F) : ∃ c : 𝔠.elt, IsTotPos (c : F) := by
  obtain ⟨x, hx0, hx⟩ := FractionalIdeal.exists_ne_zero_mem_isInteger (𝔠.ne_zero)
  refine ⟨⟨x • algebraMap (𝓞 F) F x, Submodule.smul_mem _ x hx⟩, fun τ => ?_⟩
  have hx' : algebraMap (𝓞 F) F x ≠ 0 := (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 F) F)).2 hx0
  have hτ : τ (algebraMap (𝓞 F) F x) ≠ 0 := (map_ne_zero τ).2 hx'
  show 0 < τ (x • algebraMap (𝓞 F) F x)
  rw [Algebra.smul_def, map_mul]
  exact mul_self_pos.2 hτ

theorem pull_cls_diag {S : Scheme.{0}} (X : Obj F 𝔠 S) (ψ : X.A.left ⟶ X.A.left) (hψ : X.IsPullBy X (𝟙 _) ψ)
    (c : 𝔠.elt) :
    pull ψ (cls (X.diag c) (pull_isLB (X.isLB c) _)) = cls (X.diag c) (pull_isLB (X.isLB c) _) := by
  obtain ⟨φ₂, hsq, hiso⟩ := hψ.pol
  have hw : ψ ≫ X.A.hom = X.A.hom := by simpa using hψ.grp.1.w
  have hw2 : φ₂ ≫ (X.A ⊗ X.A).hom = (X.A ⊗ X.A).hom := by
    calc φ₂ ≫ (X.A ⊗ X.A).hom = φ₂ ≫ (fst X.A X.A).left ≫ X.A.hom := by rw [Over.w]
      _ = (fst X.A X.A).left ≫ ψ ≫ X.A.hom := by rw [← Category.assoc, hsq.1, Category.assoc]
      _ = (X.A ⊗ X.A).hom := by rw [hw, Over.w]
  let Ψ : X.A ⟶ X.A := Over.homMk ψ hw
  let Φ : X.A ⊗ X.A ⟶ X.A ⊗ X.A := Over.homMk φ₂ hw2
  have e : Ψ ≫ lift (𝟙 X.A) (𝟙 X.A) = lift (𝟙 X.A) (𝟙 X.A) ≫ Φ := by
    apply CartesianMonoidalCategory.hom_ext
    · apply Over.OverMorphism.ext
      simp only [Category.assoc, lift_fst, Category.comp_id, Over.comp_left]
      rw [show Φ.left = φ₂ from rfl, hsq.1, ← Category.assoc, ← Over.comp_left, lift_fst]
      rfl
    · apply Over.OverMorphism.ext
      simp only [Category.assoc, lift_snd, Category.comp_id, Over.comp_left]
      rw [show Φ.left = φ₂ from rfl, hsq.2, ← Category.assoc, ← Over.comp_left, lift_snd]
      rfl
  have e' : ψ ≫ (lift (𝟙 X.A) (𝟙 X.A)).left = (lift (𝟙 X.A) (𝟙 X.A)).left ≫ φ₂ := congrArg (·.left) e
  have h1 : pull φ₂ (cls (X.P c) (X.isLB c)) = cls (X.P c) (X.isLB c) :=
    ((cls_eq_iff (X.isLB c) (pull_isLB (X.isLB c) φ₂)).2 (hiso c)).symm
  unfold Obj.diag
  rw [cls_pull (X.isLB c), ← pull_comp, e', pull_comp, h1]

theorem eq_id_of_level_fixed (hS : SerreAmpleSt) {K : Type} [Field K] [IsAlgClosed K] (X : Obj F 𝔠 (Sp K))
    {N : ℕ} (hN : 3 ≤ N) (hNK : (N : K) ≠ 0) (β : X.Level N) (ψ : X.A.left ⟶ X.A.left)
    (hψ : X.IsPullBy X (𝟙 _) ψ) (hfix : ∀ i, (β.pt i).left ≫ ψ = (β.pt i).left) : ψ = 𝟙 _ := by
  have hw : ψ ≫ X.A.hom = X.A.hom := by simpa using hψ.grp.1.w
  haveI : IsIso ψ := hψ.grp.1.isIso_fst_of_isIso
  let σ : X.A ≅ X.A := Over.isoMk (asIso ψ) hw
  have hσl : σ.hom.left = ψ := rfl
  have hmul : ∀ (T : Over (Sp K)) (x y : T ⟶ X.A), (x * y) ≫ σ.hom = (x ≫ σ.hom) * (y ≫ σ.hom) :=
    fun T x y => mul_comp_of_grpPullback_id σ.hom hψ.grp x y
  haveI hmon : IsMonHom σ.hom := isMonHom_of_mul_comp σ.hom hmul
  obtain ⟨c, hc⟩ := exists_totPos_mem 𝔠
  have hpt : ∀ i, β.pt i ≫ σ.hom = β.pt i := fun i => Over.OverMorphism.ext (hfix i)
  have hact : ∀ a, X.rm.act a ≫ σ.hom = σ.hom ≫ X.rm.act a := fun a => Over.OverMorphism.ext (hψ.act a)
  have key := hS K X.A X.ab (X.diag c) (pull_isLB (X.isLB c) _) (X.pos c hc) N hN hNK σ hmon
    (pull_cls_diag X ψ hψ c) (fun Ω _ _ t x hx => by
      obtain ⟨a, b, rfl⟩ := β.surj Ω t x hx
      rw [hmul, Category.assoc, Category.assoc, hact, ← Category.assoc (β.pt 0), hpt, Category.assoc,
        Category.assoc, hact, ← Category.assoc (β.pt 1), hpt])
  exact congrArg (·.left) key

theorem levelRigid_of_serreAmple : SerreAmpleSt → LevelRigidSt := by
  intro hS F _ _ 𝔠 N hN R _ hNR X β g hg hfix
  have hw : g ≫ X.A.hom = X.A.hom := by simpa using hg.grp.1.w
  let σ : X.A ⟶ X.A := Over.homMk g hw
  haveI : IsMonHom σ := isMonHom_of_mul_comp σ (fun T x y => mul_comp_of_grpPullback_id σ hg.grp x y)
  have key : σ = 𝟙 _ := by
    refine eq_id_of_forall_geometric_fibre laws_without_cohomology.1 X.A X.ab σ (IsMonHom.one_hom σ)
      fun t => ?_
    let K : Type := AlgebraicClosure ((Sp R).residueField t)
    let f : Sp K ⟶ Sp R :=
      Spec.map (CommRingCat.ofHom (algebraMap ((Sp R).residueField t) K)) ≫ (Sp R).fromSpecResidueField t
    obtain ⟨X', β', φ, hφ, hpt⟩ := Obj.exists_isLevelPull β f
    have h1 : X'.IsPullBy X (𝟙 _ ≫ f) (φ ≫ g) := by
      have := hφ.comp hg
      rwa [Category.comp_id, ← Category.id_comp f] at this
    obtain ⟨ψ, hψ, hψφ⟩ := h1.cancel hφ
    have hNK : (N : K) ≠ 0 := by
      have hu := hNR.map (Spec.preimage f).hom
      rw [map_natCast] at hu
      exact hu.ne_zero
    have hψw : ψ ≫ X'.A.hom = X'.A.hom := by simpa using hψ.grp.1.w
    have hψ1 : ψ = 𝟙 _ := eq_id_of_level_fixed hS X' hN hNK β' ψ hψ fun i => by
      refine hφ.grp.1.hom_ext ?_ ?_
      · rw [Category.assoc, hψφ, ← Category.assoc, hpt i, Category.assoc, hfix i]
      · rw [Category.assoc, hψw]
    refine ⟨Sp K, X'.A.left, f, φ, X'.A.hom, (default : PrimeSpectrum K), ?_, hφ.grp.1, ?_⟩
    · exact (Scheme.Hom.comp_apply _ _ _).trans (Scheme.fromSpecResidueField_apply t _)
    · change φ ≫ g = φ
      rw [← hψφ, hψ1, Category.id_comp]
  exact congrArg (·.left) key

end GlobalTheory.AmpleRigid
