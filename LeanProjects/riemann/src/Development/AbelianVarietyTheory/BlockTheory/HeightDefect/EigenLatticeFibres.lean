import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.CMCurveHermitianForms
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.ArakelovDegreeEqDegreeOfFamily
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.EigLatBasis

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.EigenLatticeFibres

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.CMCurveHermitianForms

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {K : Type} [Field K] [NumberField K]

structure GenFib (t : SAB H (Sp (𝓞 K))) where

  tK : SAB H (Sp K)

  m : SABMap tK t (spMap (algebraMap (𝓞 K) K))

  g : ℕ

  v : Fin g → (epsR K ⟶ tK.G)
  basis : IsLieBasis v

namespace GenFib

variable {t t' : SAB H (Sp (𝓞 K))} (F : GenFib t) (F' : GenFib t')

def IsVec (c : Fin F.g → K) (x : Sp (DualNumber K) ⟶ t.G.left) : Prop :=
  ∃ w : epsR K ⟶ F.tK.G, IsLieComb c F.v w ∧ x = w.left ≫ F.m.φ

def IsIntegralVec (c : Fin F.g → K) : Prop :=
  ∃ w : epsR (𝓞 K) ⟶ t.G, IsTangent w ∧ F.IsVec c (spMap (Chart.dualMapR (algebraMap (𝓞 K) K)) ≫ w.left)

def lieLat : Submodule (𝓞 K) (Fin F.g → K) := Submodule.span (𝓞 K) {c | F.IsIntegralVec c}

def IsDiff (f : t.G ⟶ t'.G) (D : (Fin F.g → K) →ₗ[K] (Fin F'.g → K)) : Prop :=
  ∀ c x, F.IsVec c x → F'.IsVec (D c) (x ≫ f.left)

def IsEigenVec (τ : E →+* K) (c : Fin F.g → K) : Prop :=
  ∀ (a : 𝓞 E) x, F.IsVec c x → F.IsVec (τ (a : E) • c) (x ≫ (t.act.act a).left)

def eigenSp (τ : E →+* K) : Submodule K (Fin F.g → K) := Submodule.span K {c | F.IsEigenVec τ c}

def eigenLat (τ : E →+* K) : Submodule (𝓞 K) (Fin F.g → K) :=
  F.lieLat ⊓ (F.eigenSp τ).restrictScalars (𝓞 K)

structure CxFib (σ : K →+* ℂ) where

  A : Over (Sp ℂ)
  [grp : GrpObj A]

  φ : A.left ⟶ F.tK.G.left
  cart : IsGrpPullback A F.tK.G (spMap σ) φ

  u : HolUnif A (F.tK.PP.L.pull φ) F.g

  Hm : Matrix (Fin F.g) (Fin F.g) ℂ

  χ : u.Λ → ℂ
  ah : u.IsAH Hm χ

  vC : Fin F.g → (epsR ℂ ⟶ A)
  vC_base : ∀ i, (vC i).left ≫ φ = spMap (Chart.dualMapR σ) ≫ (F.v i).left

  W : Fin F.g → (Fin F.g → ℂ)
  diff : ∀ i, u.IsDiff (W i) (vC i)

attribute [instance] CxFib.grp

variable {F} in

def CxFib.vec {σ : K →+* ℂ} (C : F.CxFib σ) (c : Fin F.g → K) : Fin F.g → ℂ := ∑ i, σ (c i) • C.W i

variable {F} in

def CxFib.piH {σ : K →+* ℂ} (C : F.CxFib σ) (x y : Fin F.g → K) : ℂ :=
  (Real.pi : ℂ) * hermForm C.Hm (C.vec x) (C.vec y)

def IsPiH (h : ReciprocityTheory.GeometryOfNumbersTheory.HermFam K (Fin F.g → K)) : Prop :=
  ∀ σ : K →+* ℂ, ∃ C : F.CxFib σ, ∀ x y, h.form σ x y = C.piH y x

end GenFib

section Sum

variable {S : Scheme.{0}}

def sumPow {A B : Over S} [GrpObj B] {n : ℕ} (f : Fin n → (A ⟶ B)) : (∏ᶜ fun _ : Fin n => A) ⟶ B :=
  (List.ofFn fun i => Pi.π (fun _ : Fin n => A) i ≫ f i).prod

def sumMap {A A' B : Over S} [GrpObj B] {p q : ℕ} (f : Fin p → (A ⟶ B)) (f' : Fin q → (A' ⟶ B)) :
    (∏ᶜ fun _ : Fin p => A) ⊗ (∏ᶜ fun _ : Fin q => A') ⟶ B :=
  (fst _ _ ≫ sumPow f) * (snd _ _ ≫ sumPow f')

def IsFinFlatSurj {X Y : Over S} (f : X ⟶ Y) : Prop := IsFinite f.left ∧ Flat f.left ∧ Surjective f.left

def IsLinHom {t t' : SAB H S} (f : t.G ⟶ t'.G) : Prop :=
  IsMonHom f ∧ ∀ a : 𝓞 E, t.act.act a ≫ f = f ≫ t'.act.act a

def PolId {t t' : SAB H S} (f : t.G ⟶ t'.G) (h : 𝓞 E) : Prop :=
  WeilEq t'.PP.L f f t.PP.L (t.act.act h) (𝟙 t.G)

end Sum

structure CMObj (H : Host E) (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (p q : ℕ) where

  A : SAB H (Sp (𝓞 K))

  A' : SAB H (Sp (𝓞 K))

  B : SAB H (Sp (𝓞 K))
  prinA : IsPrincipal A
  prinA' : IsPrincipal A'
  prinB : IsPrincipal B
  sigA : HasSig H 1 0 A.act ρ
  sigA' : HasSig H 0 1 A'.act ρ
  sigB : HasSig H p q B.act ρ

  ph : Fin p → (A.G ⟶ B.G)

  ph' : Fin q → (A'.G ⟶ B.G)
  lin : ∀ i, IsLinHom (ph i)
  lin' : ∀ j, IsLinHom (ph' j)
  isog : IsFinFlatSurj (sumMap ph ph')

  h : Fin p → 𝓞 E

  h' : Fin q → 𝓞 E
  pol : ∀ i, PolId (ph i) (h i)
  pol' : ∀ j, PolId (ph' j) (h' j)

namespace CMObj

variable {ρ : 𝓞 K} {p q : ℕ} (X : CMObj H K ρ p q)

def line (F : GenFib X.A) (τ : E →+* K) : Submodule (𝓞 K) (Fin F.g → K) := F.eigenLat τ

def line' (F : GenFib X.A') (τ : E →+* K) : Submodule (𝓞 K) (Fin F.g → K) := F.eigenLat τ

def Bdd (La : ℝ) : Prop :=
  ∀ τ : E →+* ℂ, (∀ i, ‖τ (X.h i : E)‖ ≤ La ^ 2) ∧ ∀ j, ‖τ (X.h' j : E)‖ ≤ La ^ 2

end CMObj

def SplitsE (E K : Type) [Field E] [NumberField E] [Field K] : Prop := Nat.card (E →+* K) = Module.finrank ℚ E

theorem GenFib.exists_isVec {t : SAB H (Sp (𝓞 K))} (F : GenFib t) (c : Fin F.g → K) : ∃ x, F.IsVec c x := by
  have hw : ∀ i, (spMap (epsScaleR (c i)) ≫ (F.v i).left) ≫ F.tK.G.hom = (epsR K).hom := fun i => by
    rw [Category.assoc, Over.w (F.v i)]
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext a <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]
  exact ⟨_, _, ⟨fun i => Over.homMk _ (hw i), fun _ => rfl, rfl⟩, rfl⟩

example {t : SAB H (Sp (𝓞 K))} (F : GenFib t) : F.IsDiff F (𝟙 t.G) LinearMap.id := by
  intro c x hx
  simpa using hx

example {t t' t'' : SAB H (Sp (𝓞 K))} (F : GenFib t) (F' : GenFib t') (F'' : GenFib t'') (f : t.G ⟶ t'.G)
    (f' : t'.G ⟶ t''.G) (D D') (h : F.IsDiff F' f D) (h' : F'.IsDiff F'' f' D') :
    F.IsDiff F'' (f ≫ f') (D' ∘ₗ D) := by
  intro c x hx
  simpa using h' _ _ (h c x hx)

example {S : Scheme.{0}} (t : SAB H S) : IsLinHom (𝟙 t.G) ∧ PolId (𝟙 t.G) 1 := by
  refine ⟨⟨inferInstance, by simp⟩, ?_⟩
  intro k _ T x y _ _ c
  rw [t.act.one]

end GlobalTheory.IndefiniteRowSideFullHecke.EigenLatticeFibres
