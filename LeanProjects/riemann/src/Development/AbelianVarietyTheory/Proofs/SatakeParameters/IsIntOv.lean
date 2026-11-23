import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.Columns.HeckeSp
import Formalism.SatakeDualWeyl.KpqSubgroupCompact

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.NTheta IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitHecke

section Pure

variable (O : Type) [CommRing O] {K : Type} [Field K] [Algebra O K]

def IsInt (x : K) : Prop := ∃ o : O, algebraMap O K o = x

def IntM {m n : ℕ} (x : Matrix (Fin m) (Fin n) K) : Prop := ∀ i j, IsInt O (x i j)

def GInt {n : ℕ} (x : GL (Fin n) K) : Prop := IntM O x.1 ∧ IntM O (x⁻¹).1

def Hk (p : O) (j : ℕ) {n : ℕ} (x : GL (Fin n) K) : Prop :=
  IntM O x.1 ∧ IntM O (algebraMap O K p • (x⁻¹).1) ∧ ∃ u : Oˣ, x.1.det = algebraMap O K (p ^ j * u)

def Reps {n : ℕ} {ι : Type} (x : GL (Fin n) K) (R : Finset ι) (ρ : ι → GL (Fin n) K) : Prop :=
  (∀ γ ∈ R, ∃ k₁ k₂, GInt O k₁ ∧ GInt O k₂ ∧ ρ γ = k₁ * x * k₂) ∧
    ∀ k₁ k₂, GInt O k₁ → GInt O k₂ → ∃! γ, γ ∈ R ∧ GInt O ((ρ γ)⁻¹ * (k₁ * x * k₂))

variable {O}

theorem isInt_iff {x : K} : IsInt O x ↔ x ∈ (algebraMap O K).range := Iff.rfl

theorem intM_iff {m n : ℕ} {x : Matrix (Fin m) (Fin n) K} :
    IntM O x ↔ ∃ A : Matrix (Fin m) (Fin n) O, A.map (algebraMap O K) = x := by
  constructor
  · intro h
    choose A hA using h
    exact ⟨Matrix.of A, by ext i j; simp [hA]⟩
  · rintro ⟨A, rfl⟩ i j
    exact ⟨A i j, rfl⟩

theorem IntM.mul {l m n : ℕ} {x : Matrix (Fin l) (Fin m) K} {y : Matrix (Fin m) (Fin n) K} (hx : IntM O x)
    (hy : IntM O y) : IntM O (x * y) := by
  rw [intM_iff] at hx hy ⊢
  obtain ⟨A, rfl⟩ := hx
  obtain ⟨B, rfl⟩ := hy
  exact ⟨A * B, Matrix.map_mul⟩

theorem IntM.add {m n : ℕ} {x y : Matrix (Fin m) (Fin n) K} (hx : IntM O x) (hy : IntM O y) : IntM O (x + y) := fun i j => by
  obtain ⟨a, ha⟩ := hx i j
  obtain ⟨b, hb⟩ := hy i j
  exact ⟨a + b, by simp [ha, hb]⟩

theorem IntM.sub {m n : ℕ} {x y : Matrix (Fin m) (Fin n) K} (hx : IntM O x) (hy : IntM O y) : IntM O (x - y) := fun i j => by
  obtain ⟨a, ha⟩ := hx i j
  obtain ⟨b, hb⟩ := hy i j
  exact ⟨a - b, by simp [ha, hb]⟩

theorem IntM.transpose {m n : ℕ} {x : Matrix (Fin m) (Fin n) K} (hx : IntM O x) : IntM O xᵀ := fun i j => hx j i

theorem intM_one {n : ℕ} : IntM O (1 : Matrix (Fin n) (Fin n) K) := fun i j => by
  by_cases h : i = j
  · subst h
    exact ⟨1, by simp⟩
  · exact ⟨0, by simp [Matrix.one_apply_ne h]⟩

theorem gInt_one {n : ℕ} : GInt O (1 : GL (Fin n) K) := ⟨intM_one, by rw [inv_one]; exact intM_one⟩

theorem GInt.mul {n : ℕ} {x y : GL (Fin n) K} (hx : GInt O x) (hy : GInt O y) : GInt O (x * y) := ⟨IntM.mul hx.1 hy.1, by rw [_root_.mul_inv_rev]; exact IntM.mul hy.2 hx.2⟩

theorem GInt.inv {n : ℕ} {x : GL (Fin n) K} (hx : GInt O x) : GInt O x⁻¹ := ⟨hx.2, by rw [inv_inv]; exact hx.1⟩

end Pure

variable {D : D7}

abbrev Ov (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) : Type := v.adicCompletionIntegers D.host.F

theorem isInt_Ov {v : HeightOneSpectrum (𝓞 D.host.F)} {x : Fv D.host.F v} :
    IsInt (Ov D v) x ↔ x ∈ v.adicCompletionIntegers D.host.F := ⟨fun ⟨o, h⟩ => h ▸ o.2, fun h => ⟨⟨x, h⟩, rfl⟩⟩

def Chart (e : AE D) (v : HeightOneSpectrum (𝓞 D.host.F)) (π : AE D →+* Fv D.host.F v) : Prop :=
  Function.Surjective π ∧ (∀ a, π a = 0 ↔ e * a = 0) ∧
    (∀ y : AF D.host.F, π (algebraMap (AF D.host.F) (AE D) y) = evalV D.host.F v (sndA D.host.F y)) ∧
    ∀ a, finPart D (e * a) ∈ intAE D ↔ IsInt (Ov D v) (π a)

def Frame (V : HSp D) (e : AE D) {v : HeightOneSpectrum (𝓞 D.host.F)} (π : AE D →+* Fv D.host.F v)
    (β : GL (Fin V.rank) (Fv D.host.F v)) : Prop :=
  ∀ y : Fin V.rank → AE D, (fun i => finPart D (e * y i)) ∈ LamHat V ↔
    ∀ i, IsInt (Ov D v) (((β⁻¹).1 *ᵥ fun k => π (y k)) i)

def rho (V : HSp D) {v : HeightOneSpectrum (𝓞 D.host.F)} (π : AE D →+* Fv D.host.F v)
    (β : GL (Fin V.rank) (Fv D.host.F v)) : GA D V →* GL (Fin V.rank) (Fv D.host.F v) :=
  (MulAut.conj β⁻¹).toMonoidHom.comp ((Matrix.GeneralLinearGroup.map π).comp (matHom V))

theorem rho_val (V : HSp D) {v : HeightOneSpectrum (𝓞 D.host.F)} (π : AE D →+* Fv D.host.F v)
    (β : GL (Fin V.rank) (Fv D.host.F v)) (g : GA D V) :
    (rho V π β g).1 = (β⁻¹).1 * (mt V g).map π * β.1 := by
  simp only [rho, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, Units.val_mul]
  rfl

end GlobalTheory.SplitHecke

end
