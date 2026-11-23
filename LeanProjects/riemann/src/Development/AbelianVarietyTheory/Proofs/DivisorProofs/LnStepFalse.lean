import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelSt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieCoordLat
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LetterConjugation
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IoOfLeOneIff
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj
open GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.Toroidal GlobalTheory.LocM.Frm GlobalTheory.HeightParts
open GlobalTheory.GradedNorm GlobalTheory.LieHt
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.LieSmooth

section Loc

variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

def grIdeal (E : Submodule (𝓞 K) V) {r : ℕ} (v : Fin r → V) (i : Fin r) : Submodule (𝓞 K) K where
  carrier := {a | ∃ c : Fin r → K, c i = a ∧ (∀ k, i < k → c k = 0) ∧ ∑ k, c k • v k ∈ E}
  add_mem' := by
    rintro _ _ ⟨c, rfl, h1, h2⟩ ⟨c', rfl, h1', h2'⟩
    refine ⟨c + c', rfl, fun k hk => by simp [h1 k hk, h1' k hk], ?_⟩
    simpa only [Pi.add_apply, add_smul, Finset.sum_add_distrib] using E.add_mem h2 h2'
  zero_mem' := ⟨0, rfl, fun _ _ => rfl, by simp⟩
  smul_mem' := by
    rintro a _ ⟨c, rfl, h1, h2⟩
    refine ⟨a • c, rfl, fun k hk => by simp [h1 k hk], ?_⟩
    simpa only [Pi.smul_apply, smul_assoc, ← Finset.smul_sum] using E.smul_mem a h2

open Classical in

def idealLog (𝔞 : Submodule (𝓞 K) K) : ℝ :=
  if ha : ∃ a ∈ 𝔞, a ≠ 0 then
    Real.log ((Submodule.span (𝓞 K) {ha.choose}).toAddSubgroup.relIndex 𝔞.toAddSubgroup : ℝ) -
      ∑ σ : K →+* ℂ, Real.log ‖σ ha.choose‖
  else 0

def lineHt (h : HermFam K V) (E : Submodule (𝓞 K) V) {r : ℕ} (v : Fin r → V) (i : Fin r) : ℝ :=
  (idealLog (grIdeal E v i) - (1 / 2) * ∑ σ : K →+* ℂ, Real.log (grSq (h.gram σ v) i)) / Module.finrank ℚ K

def latC {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C] (j : K →+* C) {n : ℕ}
    (L : Submodule (𝓞 K) (Fin n → K)) : Submodule ↥(intO C) (Fin n → C) :=
  Submodule.span ↥(intO C) ((fun (v : Fin n → K) i => j (v i)) '' (L : Set (Fin n → K)))

end Loc

section Emb

variable {F : Type} [Field F] [NumberField F] {K : Type} [Field K] [NumberField K]

def EmbOver (φ : F →+* K) : Type :=
  {θ : K →+* AlgebraicClosure F // θ.comp φ = algebraMap F (AlgebraicClosure F)}

instance (φ : F →+* K) : Fintype (EmbOver φ) := by
  classical exact Subtype.fintype _

def extOf (v : HeightOneSpectrum (𝓞 F)) : TrueGeo.Ext v := (inferInstance : Nonempty (TrueGeo.Ext v)).some

variable {Y : Var F} {φ : F →+* K} (p : Sp K ⟶ Y.X) (hp : p ≫ Y.str = spMap φ)

def cxPtOf (σ : K →+* ℂ) : Pts Y (σ.comp φ) :=
  ⟨spMap σ ≫ p, by rw [Category.assoc, hp, ← Spec.map_comp]; rfl⟩

def algPtOf (θ : EmbOver φ) : AlgPt Y :=
  ⟨spMap θ.1 ≫ p, by rw [Category.assoc, hp, ← Spec.map_comp]; exact congrArg spMap θ.2⟩

end Emb

section Steps

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

def stepNorm {X : Scheme.{0}} (t : SAB H X) {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C] (x : Sp C ⟶ X)
    (u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber C) ⟶ t.G.left)) : ((E →+* ℂ) × ℕ) ⊕ ℕ → ℝ
  | .inl (τ, k) => if h : k < Dw.mult τ then grNorm t x (latDR t x) (u τ) ⟨k, h⟩ else 1
  | .inr k => if h : k < (letters Dw).length then
      grNorm t x (latDR t x) (fun i => u ((letters Dw).get i).1 ((letters Dw).get i).2) ⟨k, h⟩ else 1

theorem lnStep_false {X : Scheme.{0}} (t : SAB H X) {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C]
    (x : Sp C ⟶ X) (u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber C) ⟶ t.G.left)) (p : ℕ)
    (st : ((E →+* ℂ) × ℕ) ⊕ ℕ) : lnStep t x u p false st = Real.log (stepNorm t x u st) := by
  rcases st with ⟨τ, k⟩ | k <;> simp only [lnStep, stepNorm, lat] <;> split_ifs <;> simp_all

section Tan

open MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

variable {X : Scheme.{0}} (t : SAB H X) {k : Type} [Field k] {x : Sp k ⟶ X} {n : ℕ}

def TanIndep (b : Fin n → TanM x t.G) : Prop := LinearIndependent k b

def TanBasis (b : Fin n → TanM x t.G) : Prop := LinearIndependent k b ∧ Submodule.span k (Set.range b) = ⊤

def combLeft (b : Fin n → TanM x t.G) (d : Fin n → k) : Sp (DualNumber k) ⟶ t.G.left := (tv (∑ i, d i • b i)).left

end Tan

variable (K : Type) [Field K] [NumberField K] {n : ℕ} (e : Fin n ≃ Letter Dw)

def tauFr (τ : E →+* ℂ) : Fin (Dw.mult τ) → Fin n → K := fun j => Pi.single (e.symm ⟨τ, j⟩) 1

def allFr : Fin (letters Dw).length → Fin n → K := fun j => Pi.single (e.symm ((letters Dw).get j)) 1

variable {K} in

def stepId (L : Submodule (𝓞 K) (Fin n → K)) : ((E →+* ℂ) × ℕ) ⊕ ℕ → Submodule (𝓞 K) K
  | .inl (τ, k) => if hk : k < Dw.mult τ then grIdeal L (tauFr K e τ) ⟨k, hk⟩ else ⊥
  | .inr k => if hk : k < (letters Dw).length then grIdeal L (allFr K e) ⟨k, hk⟩ else ⊥

end Steps

end GlobalTheory.LieSmooth

end
