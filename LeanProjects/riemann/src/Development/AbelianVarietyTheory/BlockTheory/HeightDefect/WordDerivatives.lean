import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.MinfDensity

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta IsDedekindDomain NumberField Matrix
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies

attribute [local instance] Formalism.BasicNotions.Host.cmStar

attribute [local instance 100] LieRing.ofAssociativeRing

def lieU {n : ℕ} (J : Matrix (Fin n) (Fin n) ℂ) : LieSubalgebra ℝ (Matrix (Fin n) (Fin n) ℂ) where
  carrier := {X | Xᴴ * J + J * X = 0}
  zero_mem' := by simp
  add_mem' := by
    intro X Y hX hY
    simp only [Set.mem_setOf_eq] at hX hY ⊢
    rw [conjTranspose_add, add_mul, mul_add, add_add_add_comm, hX, hY, add_zero]
  smul_mem' := by
    intro c X hX
    simp only [Set.mem_setOf_eq] at hX ⊢
    rw [conjTranspose_smul, star_trivial, smul_mul_assoc, mul_smul_comm, ← smul_add, hX, smul_zero]
  lie_mem' := by
    intro X Y hX hY
    simp only [Set.mem_setOf_eq] at hX hY ⊢
    have h1 : Xᴴ * J = -(J * X) := eq_neg_of_add_eq_zero_left hX
    have h2 : Yᴴ * J = -(J * Y) := eq_neg_of_add_eq_zero_left hY
    rw [Ring.lie_def, conjTranspose_sub, conjTranspose_mul, conjTranspose_mul, sub_mul, mul_assoc, mul_assoc, h1, h2,
      mul_neg, mul_neg, ← mul_assoc, ← mul_assoc, h1, h2, mul_sub]
    simp only [neg_mul, neg_neg, mul_assoc]
    abel

variable {D : D7}

abbrev LieAt (V : HSp D) (τ : D.what₂.Tau) : Type := lieU (gramAt D V τ)

abbrev LieInf (V : HSp D) : Type := ∀ τ : D.what₂.Tau, LieAt V τ

open Classical in

def atPlace (V : HSp D) (τ : D.what₂.Tau) (X : LieAt V τ) : LieInf V := Pi.single τ X

def IsExpFam (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (e : LieInf V → GA D V) : Prop :=
  ∀ X, e X ∈ GinfC V ∧
    ∀ τ, infMat D.sp.cm.sig V.gram (θ τ) (e X) = NormedSpace.exp (X τ : Matrix (Fin V.rank) (Fin V.rank) ℂ)

section Smooth

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def IsSmoothInf (V : HSp D) (e : LieInf V → GA D V) (φ : GA D V → ℂ) : Prop :=
  ∀ g, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
    (fun X : (∀ τ : D.what₂.Tau, (lieU (gramAt D V τ)).toSubmodule) => φ (g * e fun τ => ⟨(X τ).1, (X τ).2⟩))

theorem isSmoothInf_const (V : HSp D) (e : LieInf V → GA D V) (c : ℂ) : IsSmoothInf V e fun _ => c :=
  fun _ => contDiff_const

end Smooth

def lieDer (V : HSp D) (e : LieInf V → GA D V) (X : LieInf V) (φ : GA D V → ℂ) : GA D V → ℂ :=
  fun g => deriv (fun t : ℝ => φ (g * e (t • X))) 0

def wordDer (V : HSp D) (e : LieInf V → GA D V) (l : List (LieInf V)) (φ : GA D V → ℂ) : GA D V → ℂ :=
  l.foldr (lieDer V e) φ

abbrev EnvAt (V : HSp D) (τ : D.what₂.Tau) : Type := UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] LieAt V τ)

def envOf (V : HSp D) (τ : D.what₂.Tau) (w : List (LieAt V τ) →₀ ℂ) : EnvAt V τ :=
  w.sum fun l c => c • (l.map fun X => UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] X)).prod

def envDer (V : HSp D) (e : LieInf V → GA D V) (τ : D.what₂.Tau) (w : List (LieAt V τ) →₀ ℂ) (φ : GA D V → ℂ) :
    GA D V → ℂ :=
  w.sum fun l c => c • wordDer V e (l.map (atPlace V τ)) φ

def IsZFiniteAt (V : HSp D) (e : LieInf V → GA D V) (τ : D.what₂.Tau) (φ : GA D V → ℂ) : Prop :=
  FiniteDimensional ℂ (Submodule.span ℂ {ψ : GA D V → ℂ |
    ∃ w : List (LieAt V τ) →₀ ℂ, envOf V τ w ∈ Subalgebra.center ℂ (EnvAt V τ) ∧ ψ = envDer V e τ w φ})

def finCoord (D : D7) (y : Af D.host.F ⊗[D.host.F] D.host.E) : Fin (Module.finrank D.host.F D.host.E) → Af D.host.F :=
  (Algebra.TensorProduct.basis (Af D.host.F) (Module.finBasis D.host.F D.host.E)).repr y

def finNorm (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (g : GA D V) : NNReal :=
  Finset.univ.sup fun p : Fin V.rank × Fin V.rank × Fin (Module.finrank D.host.F D.host.E) =>
    ‖evalV D.host.F v (finCoord D (finMat D.sp.cm.sig V.gram g p.1 p.2.1) p.2.2)‖₊

def finHt (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (g : GA D V) : NNReal :=
  max 1 (max (finNorm V v g) (finNorm V v g⁻¹))

def infNorm (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (τ : D.what₂.Tau) (g : GA D V) :
    NNReal :=
  ‖Matrix.toEuclideanCLM (n := Fin V.rank) (𝕜 := ℂ) (infMat D.sp.cm.sig V.gram (θ τ) g)‖₊

def infHt (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (τ : D.what₂.Tau) (g : GA D V) :
    NNReal :=
  max 1 (max (infNorm θ V τ g) (infNorm θ V τ g⁻¹))

theorem eventually_finNorm_le_one (V : HSp D) (g : GA D V) : ∀ᶠ v in Filter.cofinite, finNorm V v g ≤ 1 := by
  have h : ∀ p : Fin V.rank × Fin V.rank × Fin (Module.finrank D.host.F D.host.E), ∀ᶠ v in Filter.cofinite,
      ‖evalV D.host.F v (finCoord D (finMat D.sp.cm.sig V.gram g p.1 p.2.1) p.2.2)‖₊ ≤ 1 := by
    intro p
    refine (finCoord D (finMat D.sp.cm.sig V.gram g p.1 p.2.1) p.2.2).2.mono fun v hv => ?_
    exact_mod_cast Valued.toNormedField.norm_le_one_iff.2 hv
  refine (Filter.eventually_all.2 h).mono fun v hv => ?_
  exact Finset.sup_le fun p _ => hv p

theorem finHt_mulSupport_finite (V : HSp D) (g : GA D V) : (Function.mulSupport fun v => finHt V v g).Finite := by
  have h := (eventually_finNorm_le_one V g).and (eventually_finNorm_le_one V g⁻¹)
  refine (Filter.eventually_cofinite.1 h).subset fun v hv hv' => hv ?_
  exact max_eq_left (max_le hv'.1 hv'.2)

def height (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (g : GA D V) : NNReal :=
  (∏ τ, infHt θ V τ g) * ∏ᶠ v, finHt V v g

theorem one_le_height (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (g : GA D V) :
    1 ≤ height θ V g :=
  one_le_mul_of_one_le_of_one_le (Finset.one_le_prod' fun _ _ => le_max_left _ _)
    (one_le_finprod' fun _ => le_max_left _ _)

def IsUnifModerate (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (e : LieInf V → GA D V)
    (φ : GA D V → ℂ) : Prop :=
  ∃ N : ℕ, ∀ l : List (LieInf V), ∃ C : ℝ, ∀ g, ‖wordDer V e l φ g‖ ≤ C * (height θ V g : ℝ) ^ N

def IsSmoothAutForm (V : HSp D) (φ : GA D V → ℂ) : Prop :=
  IsAutFun V φ ∧
    AllSome (IsInfFam (D := D)) fun θ => AllSome (IsExpFam θ V) fun e =>
      IsSmoothInf V e φ ∧ (∀ τ, IsZFiniteAt V e τ φ) ∧ IsUnifModerate θ V e φ

def FormsTied {X : ThetaX D} (T : ThetaTied D X) : Prop :=
  ∀ (V : HSp D) (φ : GA D V → ℂ), (∃ F : X.AF V, T.ev V F = φ) ↔ IsSmoothAutForm V φ

theorem wordDer_const (V : HSp D) (e : LieInf V → GA D V) (l : List (LieInf V)) (c : ℂ) :
    ∃ c' : ℂ, wordDer V e l (fun _ => c) = fun _ => c' := by
  induction l with
  | nil => exact ⟨c, rfl⟩
  | cons X l ih =>
    obtain ⟨c', h⟩ := ih
    refine ⟨0, ?_⟩
    change lieDer V e X (wordDer V e l fun _ => c) = _
    rw [h]; funext g; simp [lieDer]

end GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies

end
