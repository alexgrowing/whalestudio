import Mathlib
import ReciprocityTheory.DualLattices.CotangentSurjective
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.StepOrderRes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsFinFlatSub
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.QuotientByFiniteFlatStatement
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.ZarhinStatement
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.HodgeTateDatumStatement
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.OrdinaryCurveStatement
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.PolarisedFlagStatement

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace PositivityTheory.HtPt.Rg

open scoped TensorProduct

section
variable {R : Type} [CommRing R] {G G' : Over (Spec (CommRingCat.of R))} [GrpObj G] [GrpObj G']

theorem lift_mul' {X : Over (Spec (CommRingCat.of R))} (a b : X ⟶ G) (a' b' : X ⟶ G') :
    lift (a * b) (a' * b') = lift a a' * lift b b' := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [MonObj.mul_comp]
  · simp [MonObj.mul_comp]

theorem pow_eq_one_iff' {X : Over (Spec (CommRingCat.of R))} (z : X ⟶ G ⊗ G') (p : ℕ) :
    z ^ p = 1 ↔ (z ≫ fst G G') ^ p = 1 ∧ (z ≫ snd G G') ^ p = 1 := by
  have key : z ^ p = lift ((z ≫ fst G G') ^ p) ((z ≫ snd G G') ^ p) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [MonObj.pow_comp]
  have one : (1 : X ⟶ G ⊗ G') = lift 1 1 := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [MonObj.one_comp]
  rw [key, one]
  constructor
  · intro h
    exact ⟨by simpa using congrArg (· ≫ fst G G') h, by simpa using congrArg (· ≫ snd G G') h⟩
  · rintro ⟨h1, h2⟩
    rw [h1, h2]

theorem lift_right {A B S : Type} [CommRing A] [CommRing B] [CommRing S] [Algebra R A] [Algebra R B]
    [Algebra R S] (f : A →ₐ[R] S) (g : B →ₐ[R] S) (h : ∀ x y, Commute (f x) (g y)) :
    (Algebra.TensorProduct.lift f g h).comp Algebra.TensorProduct.includeRight = g :=
  Algebra.TensorProduct.lift_comp_includeRight f g h

variable {p : ℕ}

def prodPt (T : TorsRep G p) (T' : TorsRep G' p) : sp (R₀ := R) (T.A ⊗[R] T'.A) ⟶ G ⊗ G' :=
  lift (spMap (Algebra.TensorProduct.includeLeft : T.A →ₐ[R] T.A ⊗[R] T'.A) ≫ T.y)
    (spMap (Algebra.TensorProduct.includeRight : T'.A →ₐ[R] T.A ⊗[R] T'.A) ≫ T'.y)

theorem prodPt_iff (T : TorsRep G p) (T' : TorsRep G' p) {S : Type} [CommRing S] [Algebra R S]
    (φ : T.A ⊗[R] T'.A →ₐ[R] S) (z : sp (R₀ := R) S ⟶ G ⊗ G') :
    spMap φ ≫ prodPt T T' = z ↔
      spMap (φ.comp Algebra.TensorProduct.includeLeft) ≫ T.y = z ≫ fst G G' ∧
      spMap (φ.comp Algebra.TensorProduct.includeRight) ≫ T'.y = z ≫ snd G G' := by
  constructor
  · rintro rfl
    refine ⟨?_, ?_⟩
    · rw [prodPt, Category.assoc, lift_fst, ← Category.assoc, Chart.spMap_comp]
    · rw [prodPt, Category.assoc, lift_snd, ← Category.assoc, Chart.spMap_comp]
  · rintro ⟨h1, h2⟩
    apply CartesianMonoidalCategory.hom_ext
    · rw [prodPt, Category.assoc, lift_fst, ← Category.assoc, Chart.spMap_comp, h1]
    · rw [prodPt, Category.assoc, lift_snd, ← Category.assoc, Chart.spMap_comp, h2]

def prodRep (T : TorsRep G p) (T' : TorsRep G' p) : TorsRep (G ⊗ G') p where
  A := T.A ⊗[R] T'.A
  free := by
    have := T.free
    have := T'.free
    infer_instance
  fin := by
    have := T.fin
    have := T'.fin
    infer_instance
  y := prodPt T T'
  y_p := by
    rw [pow_eq_one_iff', prodPt, lift_fst, lift_snd, ← MonObj.comp_pow, ← MonObj.comp_pow, T.y_p, T'.y_p]
    exact ⟨MonObj.comp_one _, MonObj.comp_one _⟩
  univ := by
    intro S _ _ z hz
    rw [pow_eq_one_iff'] at hz
    obtain ⟨φ, hφ, uφ⟩ := T.univ S _ hz.1
    obtain ⟨ψ, hψ, uψ⟩ := T'.univ S _ hz.2
    refine ⟨Algebra.TensorProduct.lift φ ψ fun _ _ => Commute.all _ _, ?_, ?_⟩
    · show _ ≫ _ = _
      rw [prodPt_iff, Algebra.TensorProduct.lift_comp_includeLeft, lift_right]
      exact ⟨hφ, hψ⟩
    · intro χ hχ
      obtain ⟨h, h'⟩ := (prodPt_iff T T' χ z).1 hχ
      apply Algebra.TensorProduct.ext
      · rw [Algebra.TensorProduct.lift_comp_includeLeft]
        exact uφ _ h
      · exact (uψ _ h').trans (Algebra.TensorProduct.lift_comp_includeRight _ _ _).symm

theorem isTorsPts_prod {N N' : Type} [AddCommGroup N] [AddCommGroup N']
    {pt : N → (sp (R₀ := R) R ⟶ G)} {pt' : N' → (sp (R₀ := R) R ⟶ G')}
    (h : IsTorsPts G p pt) (h' : IsTorsPts G' p pt') :
    IsTorsPts (G ⊗ G') p (fun z : N × N' => lift (pt z.1) (pt' z.2)) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨a, a'⟩ ⟨b, b'⟩ e
    have e1 := congrArg (· ≫ fst G G') e
    have e2 := congrArg (· ≫ snd G G') e
    simp only [lift_fst, lift_snd] at e1 e2
    exact Prod.ext (h.inj e1) (h'.inj e2)
  · rintro ⟨a, a'⟩ ⟨b, b'⟩
    simp only [Prod.fst_add, Prod.snd_add, h.add, h'.add]
    exact lift_mul' _ _ _ _
  · intro z
    rw [pow_eq_one_iff', h.range, h'.range]
    constructor
    · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
      refine ⟨(a, b), ?_⟩
      apply CartesianMonoidalCategory.hom_ext <;> simp [ha, hb]
    · rintro ⟨⟨a, b⟩, rfl⟩
      exact ⟨⟨a, by simp⟩, ⟨b, by simp⟩⟩

theorem exists_ev (T : TorsRep G p) {N : Type} [AddCommGroup N] {pt : N → (sp (R₀ := R) R ⟶ G)}
    (h : IsTorsPts G p pt) : ∃ e : N → (T.A →ₐ[R] R), (∀ x, spMap (e x) ≫ T.y = pt x) ∧
      ∀ x φ, spMap φ ≫ T.y = pt x → φ = e x := by
  choose e he ue using fun x => T.univ R (pt x) ((h.range _).2 ⟨x, rfl⟩)
  exact ⟨e, he, ue⟩

theorem mem_torsFun_iff {C : Type} [Field C] [Algebra R C] (T : TorsRep G p) {N : Type}
    {pt : N → (sp (R₀ := R) R ⟶ G)} {e : N → (T.A →ₐ[R] R)} (he : ∀ x, spMap (e x) ≫ T.y = pt x)
    (ue : ∀ x φ, spMap φ ≫ T.y = pt x → φ = e x) (f : N → C) :
    f ∈ torsFun C T pt ↔ ∃ a : T.A, f = fun x => algebraMap R C (e x a) := by
  show (∃ a : T.A, ∀ x φ, spMap φ ≫ T.y = pt x → f x = algebraMap R C (φ a)) ↔ _
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, funext fun x => ha x (e x) (he x)⟩
  · rintro ⟨a, rfl⟩
    refine ⟨a, fun x φ hφ => ?_⟩
    rw [ue x φ hφ]

theorem torsFun_prod (C : Type) [Field C] [Algebra R C] (T : TorsRep G p) (T' : TorsRep G' p)
    {N N' : Type} [AddCommGroup N] [AddCommGroup N']
    {pt : N → (sp (R₀ := R) R ⟶ G)} {pt' : N' → (sp (R₀ := R) R ⟶ G')}
    (h : IsTorsPts G p pt) (h' : IsTorsPts G' p pt') :
    torsFun C (prodRep T T') (fun z : N × N' => lift (pt z.1) (pt' z.2)) =
      tens (torsFun C T pt) (torsFun C T' pt') := by
  obtain ⟨e, he, ue⟩ := exists_ev T h
  obtain ⟨e', he', ue'⟩ := exists_ev T' h'
  let E : N × N' → (T.A ⊗[R] T'.A →ₐ[R] R) := fun z =>
    Algebra.TensorProduct.lift (e z.1) (e' z.2) (fun _ _ => Commute.all _ _)
  have hE : ∀ z, spMap (E z) ≫ (prodRep T T').y = lift (pt z.1) (pt' z.2) := by
    intro z
    show spMap (E z) ≫ prodPt T T' = _
    rw [prodPt_iff]
    refine ⟨?_, ?_⟩
    · simp only [E]
      rw [Algebra.TensorProduct.lift_comp_includeLeft, he, lift_fst]
    · simp only [E]
      rw [lift_right, he', lift_snd]
  have uE : ∀ z (φ : T.A ⊗[R] T'.A →ₐ[R] R), spMap φ ≫ (prodRep T T').y = lift (pt z.1) (pt' z.2) →
      φ = E z := by
    intro z φ hφ
    obtain ⟨h1, h2⟩ := (prodPt_iff T T' φ _).1 hφ
    rw [lift_fst] at h1
    rw [lift_snd] at h2
    apply Algebra.TensorProduct.ext
    · simp only [E]
      rw [Algebra.TensorProduct.lift_comp_includeLeft]
      exact ue _ _ h1
    · exact (ue' _ _ h2).trans (lift_right (e z.1) (e' z.2) (fun _ _ => Commute.all _ _)).symm
  have hS := mem_torsFun_iff (C := C) T he ue
  have hS' := mem_torsFun_iff (C := C) T' he' ue'
  have hP := mem_torsFun_iff (C := C) (prodRep T T') hE uE
  have hten : ∀ (z : N × N') (a : T.A) (b : T'.A),
      algebraMap R C (E z (a ⊗ₜ[R] b)) = algebraMap R C (e z.1 a) * algebraMap R C (e' z.2 b) := by
    intro z a b
    simp [E]
  have aux : ∀ t : T.A ⊗[R] T'.A,
      (fun z : N × N' => algebraMap R C (E z t)) ∈ tens (torsFun C T pt) (torsFun C T' pt') := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero =>
      have h0 : (fun z : N × N' => algebraMap R C (E z 0)) = 0 := by
        funext z
        simp
      rw [h0]
      exact zero_mem _
    | tmul a b =>
      apply Submodule.subset_span
      refine ⟨fun x => algebraMap R C (e x a), (hS _).2 ⟨a, rfl⟩,
        fun x => algebraMap R C (e' x b), (hS' _).2 ⟨b, rfl⟩, ?_⟩
      funext z
      exact hten z a b
    | add s t hs ht =>
      have h2 : (fun z : N × N' => algebraMap R C (E z (s + t))) =
          (fun z => algebraMap R C (E z s)) + (fun z => algebraMap R C (E z t)) := by
        funext z
        simp
      rw [h2]
      exact add_mem hs ht
  apply le_antisymm
  · intro f hf
    obtain ⟨t, rfl⟩ := (hP f).1 hf
    exact aux t
  · unfold tens
    rw [Submodule.span_le]
    rintro F ⟨g, hg, k, hk, rfl⟩
    obtain ⟨a, rfl⟩ := (hS g).1 hg
    obtain ⟨b, rfl⟩ := (hS' k).1 hk
    exact (hP _).2 ⟨(a ⊗ₜ[R] b : T.A ⊗[R] T'.A), funext fun z => (hten z a b).symm⟩

end

end PositivityTheory.HtPt.Rg
