import Development.EtaleCohomology.EtaleTrace.GenOutPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

namespace LateralTheory.EtaleTrace.Cov

def LocOpen : Prop := ∀ (X : Scheme.{0}) [IsIntegral X] (z : X.functionField), IsOpen {y : X | z ∈ loc X y}

def ChartMap : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k) (N : ℕ)
  (w : Fin (N + 1) → X.functionField) (i : Fin (N + 1)), w i ≠ 0 → ∀ (U : X.Opens),
  (∀ y ∈ U, ∀ j, w j / w i ∈ loc X y) →
  ∃ πU : U.toScheme ⟶ PN k N, πU ≫ PNto k N = U.ι ≫ p ∧ GenOn p w U πU

theorem GenOutChart_of_cut (h1 : LocOpen) (h2 : ChartMap) : GenOutChart := by
  intro k _ X _ p N w hw x
  obtain ⟨i, hi, hx⟩ := hw x
  have hop : IsOpen {y : X | ∀ j, w j / w i ∈ loc X y} := by
    have : {y : X | ∀ j, w j / w i ∈ loc X y} = ⋂ j, {y : X | w j / w i ∈ loc X y} := by
      ext y; simp
    rw [this]
    exact isOpen_iInter_of_finite fun j => h1 X (w j / w i)
  obtain ⟨πU, h1U, h2U⟩ := h2 k p N w i hi ⟨_, hop⟩ (fun y hy => hy)
  exact ⟨⟨_, hop⟩, πU, hx, h1U, h2U⟩

theorem LocOpen_pf (X : Scheme.{0}) [IsIntegral X] (z : X.functionField) : IsOpen {y : X | z ∈ loc X y} := by
  rw [isOpen_iff_forall_mem_open]
  rintro y ⟨a, rfl⟩
  obtain ⟨V, hyV, s, rfl⟩ := X.presheaf.exists_germ_eq (x := y) a
  have : Nonempty V := ⟨⟨y, hyV⟩⟩
  refine ⟨V, fun y' hy' => ?_, V.isOpen, hyV⟩
  refine ⟨X.presheaf.germ V y' hy' s, ?_⟩
  simp only [Scheme.algebraMap_germ_eq_germToFunctionField]

def ChartRing : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k) (N : ℕ)
  (w : Fin (N + 1) → X.functionField) (i : Fin (N + 1)), w i ≠ 0 → ∀ (U : X.Opens),
  (∀ y ∈ U, ∀ j, w j / w i ∈ loc X y) →
  ∀ (hx : (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) k) ∈ homogeneousSubmodule (Fin (N + 1)) k 1),
  ∃ φ : HomogeneousLocalization.Away (homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i) →+* Γ(X, U),
    ∀ (y : X) (hy : y ∈ U) (m : ℕ) (g : MvPolynomial (Fin (N + 1)) k)
      (hg : g ∈ homogeneousSubmodule (Fin (N + 1)) k (m • 1)),
      algebraMap (X.presheaf.stalk y) X.functionField
        (X.presheaf.germ U y hy (φ (HomogeneousLocalization.Away.mk _ hx m g hg))) = eval₂ (kHom p) w g / w i ^ m

def ChartGen : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k) (N : ℕ)
  (w : Fin (N + 1) → X.functionField) (i : Fin (N + 1)), w i ≠ 0 → ∀ (U : X.Opens)
  (hx : (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) k) ∈ homogeneousSubmodule (Fin (N + 1)) k 1)
  (φ : HomogeneousLocalization.Away (homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i) →+* Γ(X, U)),
  (∀ (y : X) (hy : y ∈ U) (m : ℕ) (g : MvPolynomial (Fin (N + 1)) k)
      (hg : g ∈ homogeneousSubmodule (Fin (N + 1)) k (m • 1)),
      algebraMap (X.presheaf.stalk y) X.functionField
        (X.presheaf.germ U y hy (φ (HomogeneousLocalization.Away.mk _ hx m g hg))) = eval₂ (kHom p) w g / w i ^ m) →
  ∃ πU : U.toScheme ⟶ PN k N, πU ≫ PNto k N = U.ι ≫ p ∧ GenOn p w U πU

theorem ChartMap_pf (h1 : ChartRing) (h2 : ChartGen) : ChartMap := by
  intro k _ X _ p N w i hi U hU
  have hx : (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) k) ∈ homogeneousSubmodule (Fin (N + 1)) k 1 :=
    (mem_homogeneousSubmodule _ _).2 (isHomogeneous_X k i)
  obtain ⟨φ, hφ⟩ := h1 k p N w i hi U hU hx
  exact h2 k p N w i hi U hx φ hφ

theorem GenOutChart_of (h1 : ChartRing) (h2 : ChartGen) : GenOutChart :=
  GenOutChart_of_cut (fun X _ z => LocOpen_pf X z) (ChartMap_pf h1 h2)

end LateralTheory.EtaleTrace.Cov
