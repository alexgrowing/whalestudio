import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.LawsChart
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegOUnif
import ReciprocityTheory.DualLattices.CotangentSurjective

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.LieMatrixCoordinates

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Out

attribute [local instance] Over.cartesianMonoidalCategory

section Chart

variable {T : Type} [CommRing T]

def jetOf {κ : Type} [Fintype κ] [DecidableEq κ] (m : ℕ) (f : MvPowerSeries κ T) : JetR T κ m :=
  Ideal.Quotient.mk _
    (MvPowerSeries.trunc' T (Finsupp.equivFunOnFinite.symm fun _ : κ => m) f)

abbrev JetFam (G : Over (Sp T)) (d : ℕ) : Type := ∀ m : ℕ, algOver T (JetR T (Fin d) m) ⟶ G

def IsJetChart (G : Over (Sp T)) [GrpObj G] {d : ℕ} (x : JetFam G d) : Prop :=
  (∀ m, algOverHom (jetTruncR T (Fin d) m) ≫ x (m + 1) = x m) ∧
  (∀ m, algOverHom (jetZeroR T (Fin d) m) ≫ x m = toUnit _ ≫ η[G]) ∧
  ∀ (κ : Type) (m : ℕ) (y : algOver T (JetR T κ m) ⟶ G),
    algOverHom (jetZeroR T κ m) ≫ y = toUnit _ ≫ η[G] →
    ∃! ψ : JetR T (Fin d) m →ₐ[T] JetR T κ m,
      (∀ j, jetZeroR T κ m (ψ (zR m j)) = 0) ∧ y = algOverHom ψ ≫ x m

def HasCoords {G : Over (Sp T)} {d : ℕ} (x : JetFam G d) {κ : Type} [Fintype κ] [DecidableEq κ]
    (m : ℕ) (a : Fin d → MvPowerSeries κ T) (y : algOver T (JetR T κ m) ⟶ G) : Prop :=
  ∃ ψ : JetR T (Fin d) m →ₐ[T] JetR T κ m,
    (∀ j, ψ (zR m j) = jetOf m (a j)) ∧ y = algOverHom ψ ≫ x m

def IsLawOf (G : Over (Sp T)) [GrpObj G] {d : ℕ} (x : JetFam G d) (F : FGLaw T d) : Prop :=
  ∀ m : ℕ, ∃ y₀ y₁ : algOver T (JetR T (Fin 2 × Fin d) m) ⟶ G,
    HasCoords x m (pt T (n := 2) d 0) y₀ ∧ HasCoords x m (pt T (n := 2) d 1) y₁ ∧
      HasCoords x m F.F (lift y₀ y₁ ≫ μ[G])

def IsActOf (G : Over (Sp T)) [GrpObj G] [IsCommMonObj G] {d : ℕ} (x : JetFam G d)
    {Λ : Type} [CommRing Λ] (ιG : RingAct G Λ) {F : FGLaw T d} (α : Germ.OAct Λ F) : Prop :=
  ∀ (m : ℕ) (a : Λ), ∃ y : algOver T (JetR T (Fin 1 × Fin d) m) ⟶ G,
    HasCoords x m (pt T (n := 1) d 0) y ∧ HasCoords x m (α.act a) (y ≫ ιG.act a)

end Chart

section Characters

variable {O : Type} [CommRing O] {d : ℕ}

def IsMultSeries (F : Fin d → PS O 2 d) (χ : PS O 1 d) : Prop :=
  MvPowerSeries.constantCoeff χ = 1 ∧
    ev (n := 2) ![F] χ = ev (n := 2) ![pt O d 0] χ * ev (n := 2) ![pt O d 1] χ

def linCoeff (χ : PS O 1 d) : Fin d → O :=
  fun j => MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j) 1) χ

def dlogSpan (F : Fin d → PS O 2 d) {s : ℕ} (u : Fin s → Fin d → O) : Submodule O (Fin s → O) :=
  Submodule.span O {l | ∃ χ : PS O 1 d, IsMultSeries F χ ∧ l = fun i => linCoeff χ ⬝ᵥ u i}

example (F : Fin d → PS O 2 d) : IsMultSeries F 1 := ⟨by simp, by simp⟩

example :
    IsMultSeries (O := O) (d := 1)
      (fun i => MvPowerSeries.X (0, i) + MvPowerSeries.X (1, i) +
        MvPowerSeries.X (0, i) * MvPowerSeries.X (1, i))
      (1 + MvPowerSeries.X (0, 0)) ∧
    linCoeff (O := O) (d := 1) (1 + MvPowerSeries.X (0, 0)) 0 = 1 := by
  have key : ∀ a : Fin 1 → Pt O 2 1, (∀ i j, MvPowerSeries.constantCoeff (a i j) = 0) →
      ev a (1 + MvPowerSeries.X (0, 0) : PS O 1 1) = 1 + a 0 0 := by
    intro a ha
    have hs : MvPowerSeries.HasSubst (fun q : Fin 1 × Fin 1 => a q.1 q.2) :=
      MvPowerSeries.hasSubst_of_constantCoeff_zero fun q => ha q.1 q.2
    have h1 := ev_one a
    unfold ev at h1 ⊢
    rw [MvPowerSeries.subst_add hs, h1, MvPowerSeries.subst_X hs]
  refine ⟨⟨by simp, ?_⟩, ?_⟩
  · rw [key, key, key]
    · simp only [Matrix.cons_val_fin_one, pt]; ring
    all_goals (intro i j; fin_cases i; simp [pt])
  · simp [linCoeff, MvPowerSeries.coeff_one, MvPowerSeries.coeff_X]

end Characters

section Types

variable {T : Type} [CommRing T] {O : Type} [CommRing O] {C : Type} [Field C] [Algebra O C]
  {E : Type} [Field E] {d : ℕ}

def lieMat {F : FGLaw T d} (α : Germ.OAct (𝓞 E) F) (io : T →+* O) (a : 𝓞 E) :
    Matrix (Fin d) (Fin d) O :=
  Matrix.of fun i j => io (linCoeff (α.act a i) j)

def lieTau {F : FGLaw T d} (α : Germ.OAct (𝓞 E) F) (io : T →+* O) (τ : E →+* C) :
    Submodule O (Fin d → O) where
  carrier := {u | ∀ (a : 𝓞 E) (i : Fin d),
    algebraMap O C ((lieMat α io a).mulVec u i) = τ (a : E) * algebraMap O C (u i)}
  zero_mem' := by intro a i; simp
  add_mem' := by
    intro u u' hu hu' a i
    simp only [Matrix.mulVec_add, Pi.add_apply, map_add, hu a i, hu' a i, mul_add]
  smul_mem' := by
    intro c u hu a i
    simp only [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, map_mul, hu a i]
    ring

def IsEigenBasis {F : FGLaw T d} (α : Germ.OAct (𝓞 E) F) (io : T →+* O) (τ : E →+* C) {s : ℕ}
    (u : Fin s → Fin d → O) : Prop :=
  LinearIndependent O u ∧ Submodule.span O (Set.range u) = lieTau α io τ

def HasColength_vp (p : ℕ) (v : Valuation C NNReal) (F : FGLaw T d) (io : T →+* O) {s : ℕ}
    (u : Fin s → Fin d → O) (a : ℝ) : Prop :=
  ReciprocityTheory.PGsh.Up.HasLen v O ((Fin s → O) ⧸ dlogSpan (F.mapF io) u) (v (p : C) ^ a)

def Induces (v : Valuation C NNReal) (τ : E →+* C) (w : Ideal (𝓞 E)) : Prop :=
  ∀ a : 𝓞 E, a ∈ w ↔ v (τ (a : E)) < 1

end Types

section Place

variable {E : Type} [Field E] [NumberField E]

def ramIdx (p : ℕ) (w : Ideal (𝓞 E)) : ℕ :=
  (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(p : 𝓞 E)})).count w

def localDeg (p : ℕ) (w : Ideal (𝓞 E)) : ℕ :=
  ramIdx p w * padicValNat p (Ideal.absNorm w)

def vd_vp (p : ℕ) (w : Ideal (𝓞 E)) : ℝ :=
  ((UniqueFactorizationMonoid.normalizedFactors (differentIdeal ℤ (𝓞 E))).count w : ℝ) /
    (ramIdx p w : ℝ)

end Place

open Classical in

def AvChartSt : Prop :=
  ∀ (p : ℕ) [Fact p.Prime]
    (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [IsNoetherianRing T] [CharZero T]
    [IsAdicComplete (IsLocalRing.maximalIdeal T) T], ¬ IsUnit (p : T) →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [StarRing (𝓞 E)],
    (∀ a : 𝓞 E, ((star a : 𝓞 E) : E) = IsCMField.complexConj E (a : E)) →
  ∀ (I : Ideal T), I ≠ ⊤ →
  ∀ (D : DegData T I) [Module (𝓞 E) D.toPre.X]
    (A : PolAV (Spec (CommRingCat.of (FractionRing T))))
    (G : Over (Sp T)) [GrpObj G] [IsCommMonObj G]
    (U : UnifPre I D A G)
    (ιD : D.OAct (𝓞 E)) (ιA : A.OAct (𝓞 E)) (ιG : RingAct G (𝓞 E)),
    U.OLinear (𝓞 E) ιD ιA ιG →
  ∀ (d : ℕ) (x : JetFam G d) (F : FGLaw T d) (α : Germ.OAct (𝓞 E) F),
    IsJetChart G x → IsLawOf G x F → IsActOf G x ιG α →
  ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal)
    (O : Type) [CommRing O] [Algebra O C] [IsAdicComplete (Ideal.span {(p : O)}) O],
    v.Integers O →
  ∀ (io : T →+* O), IsLocalHom io →
  ∀ (w : Ideal (𝓞 E)), w.IsPrime → (p : 𝓞 E) ∈ w → w ≠ w.comap (starRingEnd (𝓞 E)) →
  ∀ (rp rm : ℕ) (u : (E →+* C) → Fin rp → Fin d → O) (u' : (E →+* C) → Fin rm → Fin d → O),
    (∀ τ, Induces v τ w → IsEigenBasis α io τ (u τ)) →
    (∀ σ, Induces v σ (w.comap (starRingEnd (𝓞 E))) → IsEigenBasis α io σ (u' σ)) →
    (∀ τ, Induces v τ w → ∃ a : ℝ, HasColength_vp p v F io (u τ) a) ∧
    ∀ a : (E →+* C) → ℝ, (∀ τ, Induces v τ w → HasColength_vp p v F io (u τ) (a τ)) →
      ∑ τ ∈ Finset.univ.filter (fun τ : E →+* C => Induces v τ w), a τ ≤
        (localDeg p w : ℝ) * ((rm : ℝ) - (Module.finrank (𝓞 E) D.toPre.X : ℝ)) *
          (1 / ((p : ℝ) - 1) + vd_vp p w / 2)

end GlobalTheory.IndefiniteRowSideFullHecke.LieMatrixCoordinates
