import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriHeckeInjectivity.HeckeInj
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary

noncomputable section

open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E
open GlobalTheory.PRep GlobalTheory.SmGL Formalism.BasicNotions GlobalTheory.CuspRep
open scoped TensorProduct Classical

namespace UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks

section Abstract

variable {G H Γ V Y : Type} [Group G] [Group H] [Group Γ] [AddCommGroup V] [Module ℂ V] [AddCommGroup Y] [Module ℂ Y]

def Schur (ρ : Representation ℂ G V) : Prop :=
  ∀ T : V →ₗ[ℂ] V, (∀ g v, T (ρ g v) = ρ g (T v)) → ∃ c : ℂ, ∀ v, T v = c • v

def lawSp (j : H →* G) (y : Representation ℂ H Y) (X : Submodule ℂ Y) : Submodule ℂ (G → Y) where
  carrier := {f | (∀ g, f g ∈ X) ∧ ∀ h g, f (j h * g) = y h (f g)}
  add_mem' ha hb := ⟨fun g => X.add_mem (ha.1 g) (hb.1 g), fun h g => by simp [ha.2 h g, hb.2 h g]⟩
  zero_mem' := ⟨fun _ => X.zero_mem, fun h g => by simp⟩
  smul_mem' c _ hf := ⟨fun g => X.smul_mem c (hf.1 g), fun h g => by simp [hf.2 h g]⟩

def SimpleIn (ρ : Representation ℂ G V) (X : Submodule ℂ V) : Prop :=
  (∀ g, ∀ v ∈ X, ρ g v ∈ X) ∧ ∀ Q ≤ X, (∀ g, ∀ v ∈ Q, ρ g v ∈ Q) → Q = ⊥ ∨ Q = X

def SchurIn (ρ : Representation ℂ G V) (X : Submodule ℂ V) : Prop :=
  ∀ T : X →ₗ[ℂ] X, (∀ g (v v' : X), (v' : V) = ρ g v → (T v' : V) = ρ g (T v)) → ∃ c : ℂ, ∀ v, T v = c • v

def hopR (ρ : Representation ℂ G V) (U : Subgroup G) (g : G) (v : V) : V :=
  ∑ᶠ c ∈ {c : G ⧸ U | ∃ u ∈ U, c = QuotientGroup.mk (u * g)}, ρ c.out v

variable [TopologicalSpace G] [IsTopologicalGroup G]

def IndF (j : H →* G) (y : Representation ℂ H Y) (X : Submodule ℂ Y) : Submodule ℂ (G → Y) :=
  lawSp j y X ⊓ smoothPart (rightReg ℂ G Y)

def SimpleG (Z : Submodule ℂ (G → Y)) (γ : Γ → Y →ₗ[ℂ] Y) : Prop :=
  ∀ Q ≤ Z, (∀ g, ∀ f ∈ Q, rightReg ℂ G Y g f ∈ Q) → (∀ c, ∀ f ∈ Q, (fun x => γ c (f x)) ∈ Q) → Q = ⊥ ∨ Q = Z

structure LocOk (P : Subgroup G) (ρ : Representation ℂ P V) : Prop where
  iwa : ∃ K : Subgroup G, CO K ∧ ∀ g : G, ∃ p ∈ P, ∃ k ∈ K, g = p * k
  small : ∀ N ∈ nhds (1 : G), ∃ U : Subgroup G, IsOpen (U : Set G) ∧ (U : Set G) ⊆ N
  irr : ρ.IsIrreducible
  schur : Schur ρ
  indIrr : (smInd P ρ).IsIrreducible
  indSchur : Schur (smInd P ρ)

end Abstract

def piIncl {r : ℕ} {G : Fin r → Type} [∀ i, Group (G i)] (P : ∀ i, Subgroup (G i)) : (∀ i, P i) →* (∀ i, G i) :=
  MonoidHom.pi fun i => (P i).subtype.comp (Pi.evalMonoidHom (fun i => P i) i)

def tensFn {A B : Type} (X₁ : Submodule ℂ (A → ℂ)) (X₂ : Submodule ℂ (B → ℂ)) : Submodule ℂ (A × B → ℂ) :=
  Submodule.span ℂ {F | ∃ φ ∈ X₁, ∃ ψ ∈ X₂, F = fun x => φ x.1 * ψ x.2}

section Global

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {K : Type} [Field K] [NumberField K] {n r : ℕ}

abbrev PW (w : Pl K) : Subgroup (Gw (2 + 2) w) := parab (w.adicCompletion K) (two (stdSum (rfl : 2 + 2 = 2 + 2)))

def lev₂ (w : Pl K) : PW w →* Gw 2 w × Gw 2 w :=
  (leviTwo (w.adicCompletion K) (Fin 2) (Fin 2)).symm.toMonoidHom.comp (leviProj (w.adicCompletion K) (two (stdSum (rfl : 2 + 2 = 2 + 2))))

def dl (w : Pl K) : PW w →* ℂˣ :=
  (deltaHalf (w.adicCompletion K) (Two (Fin 2) (Fin 2))).comp (leviProj (w.adicCompletion K) (two (stdSum (rfl : 2 + 2 = 2 + 2))))

def rhoW (w : Pl K) (σ₁ σ₂ : SmIrr (Gw 2 w)) : Representation ℂ (PW w) (σ₁.V ⊗[ℂ] σ₂.V) :=
  twist ((extTensor σ₁.ρ σ₂.ρ).comp (lev₂ w)) (dl w)

abbrev GS (n : ℕ) (w : Fin r → Pl K) : Type := ∀ i, Gw n (w i)

def IsEmb (w : Fin r → Pl K) (ι : GS n w →* FA K n) : Prop := ∀ i g, ι (Pi.mulSingle i g) = AdelicGLn.localEmbedding (w i) g

def rS {w : Fin r → Pl K} (ι : GS n w →* FA K n) : Representation ℂ (GS n w) (G1 K n → ℂ) :=
  (rightReg ℂ (G1 K n) ℂ).comp ((MultiplicityOne.finProj K n).comp ι)

abbrev im (w : Fin r → Pl K) : Finset (Pl K) := Finset.univ.image w

def IsX (μ : Measure (G1 K n)) (τ : Submodule ℂ (L2 μ)) (κ : Measure (archCompact K n)) (p : archCompact K n → ℂ) (S : Finset (Pl K))
    (φ : G1 K n → ℂ) : Prop :=
  Continuous φ ∧ (∃ v ∈ τ, Reps μ v φ) ∧ FixA κ p φ ∧ ∃ U, Lev U ∧ FixF (levOn S U) φ

def Xs (μ : Measure (G1 K n)) (τ : Submodule ℂ (L2 μ)) (κ : Measure (archCompact K n)) (p : archCompact K n → ℂ) (S : Finset (Pl K)) :
    Submodule ℂ (G1 K n → ℂ) := Submodule.span ℂ {φ | IsX μ τ κ p S φ}

def InH (μ : Measure (G1 K n)) [μ.IsHaarMeasure] (τ : Submodule ℂ (L2 μ)) (κ : Measure (archCompact K n)) (p : archCompact K n → ℂ)
    (S : Finset (Pl K)) (v : L2 μ) : Prop := v ∈ τ ∧ pOp μ κ p v = v ∧ v ∈ sphOff μ S

def blocks {w : Fin r → Pl K} (ι : GS 2 w →* FA K 2) : (∀ i, PW (w i)) →* G1 K 2 × G1 K 2 :=
  (((MultiplicityOne.finProj K 2).comp ι).comp
      (MonoidHom.pi fun i => (MonoidHom.fst _ _).comp ((lev₂ (w i)).comp (Pi.evalMonoidHom (fun i => PW (w i)) i)))).prod
    (((MultiplicityOne.finProj K 2).comp ι).comp
      (MonoidHom.pi fun i => (MonoidHom.snd _ _).comp ((lev₂ (w i)).comp (Pi.evalMonoidHom (fun i => PW (w i)) i))))

def dS (w : Fin r → Pl K) : (∀ i, PW (w i)) →* ℂˣ := ∏ i, (dl (w i)).comp (Pi.evalMonoidHom (fun i => PW (w i)) i)

def xS {w : Fin r → Pl K} (ι : GS 2 w →* FA K 2) : Representation ℂ (∀ i, PW (w i)) (G1 K 2 × G1 K 2 → ℂ) :=
  twist ((rightReg ℂ (G1 K 2 × G1 K 2) ℂ).comp (blocks ι)) (dS w)

variable {μ₂ : Measure (G1 K 2)}

def IsZ (τ₁ τ₂ : Submodule ℂ (L2 μ₂)) (κ : Measure (archCompact K (2 + 2))) (e : archCompact K (2 + 2) → ℂ) (S : Finset (Pl K))
    (φ : G1 K (2 + 2) → ℂ) : Prop :=
  ∃ f, IsSec τ₁ τ₂ f ∧ FixA κ e f ∧ (∃ U, Lev U ∧ FixF (levOn S U) f) ∧ φ = flat 0 f

def Zs (τ₁ τ₂ : Submodule ℂ (L2 μ₂)) (κ : Measure (archCompact K (2 + 2))) (e : archCompact K (2 + 2) → ℂ) (S : Finset (Pl K)) :
    Submodule ℂ (G1 K (2 + 2) → ℂ) := Submodule.span ℂ {φ | IsZ τ₁ τ₂ κ e S φ}

def ev {w : Fin r → Pl K} (ι : GS (2 + 2) w →* FA K (2 + 2)) (k₀ : archCompact K (2 + 2)) :
    (G1 K (2 + 2) → ℂ) →ₗ[ℂ] (GS (2 + 2) w → G1 K 2 × G1 K 2 → ℂ) where
  toFun φ g m := φ (lv m.1 m.2 0 * arc1 k₀ * fin1 (ι g))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end Global

end UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks
