import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.HeckeTraceSemi
import Development.AbelianVarietyTheory.Definitions.Divisors.IwahoriRegularSeparable
import Development.AbelianVarietyTheory.Definitions.Divisors.GenOf

set_option autoImplicit false

noncomputable section

open MeasureTheory Matrix NumberField Polynomial GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCx GlobalTheory.LKDef GlobalTheory.RootSumWeights GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open UpperTheory.Gal.CertificateRingHomMap (wop wmul)
open UpperTheory.Gal.LocalSmoothExtension
open Formalism.UG (Hecke conv)
open scoped TensorProduct Classical

namespace UpperTheory.Gal.Spc

def NoConst {k : Type} [Field k] [TopologicalSpace k] [MeasurableSpace k] {n : ℕ} (f : GL (Fin n) k → ℂ) : Prop :=
  ∀ (a b : ℕ) (ε : Fin n ≃ Fin a ⊕ Fin b), 0 < a → 0 < b → ∀ μ : Measure (Fin a → Fin b → k), μ.IsAddHaarMeasure →
    ∀ u : (Fin a → Fin b → k) → GL (Fin n) k,
      (∀ X, (u X : Matrix (Fin n) (Fin n) k) = Matrix.reindex ε.symm ε.symm (Matrix.fromBlocks 1 (Matrix.of X) 0 1)) →
      ∀ g h : GL (Fin n) k, ∫ X, f (g * (h⁻¹ * u X * h)) ∂μ = 0

variable {p : ℕ} [Fact p.Prime]

structure Pl (G : HTGroup p) (k : Type) [Field k] [Algebra G.F k] where
  κ : AfP p ⊗[ℚ] G.C →+* Matrix (Fin G.n) (Fin G.n) k
  ι : G.C →ₐ[G.F] Matrix (Fin G.n) (Fin G.n) k
  κ_ι : ∀ y, κ (1 ⊗ₜ y) = ι y

def Pl.at {G : HTGroup p} {k : Type} [Field k] [Algebra G.F k] (P : Pl G k) (g : G.GAf) : Matrix (Fin G.n) (Fin G.n) k :=
  P.κ (((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C)

structure Split {G : HTGroup p} {k : Type} [Field k] [TopologicalSpace k] [Algebra G.F k] (P : Pl G k) (K : Subgroup G.GAf)
    (H : Type) [Group H] [TopologicalSpace H] where
  e : G.GAf ≃* GL (Fin G.n) k × H
  e_at : ∀ g, ((e g).1 : Matrix (Fin G.n) (Fin G.n) k) = P.at g
  K₀ : Subgroup (GL (Fin G.n) k)
  K' : Subgroup H
  open₀ : IsOpen (K₀ : Set (GL (Fin G.n) k))
  cpt₀ : IsCompact (K₀ : Set (GL (Fin G.n) k))
  open' : IsOpen (K' : Set H)
  cpt' : IsCompact (K' : Set H)
  map_eq : K.map e.toMonoidHom = K₀.prod K'

def Split.Cusp {G : HTGroup p} {k : Type} [Field k] [TopologicalSpace k] [MeasurableSpace k] [Algebra G.F k] {P : Pl G k}
    {K : Subgroup G.GAf} {H : Type} [Group H] [TopologicalSpace H] (S : Split P K H) (f : G.GAf → ℂ) : Prop :=
  ∀ h : H, NoConst fun g => f (S.e.symm (g, h))

def op {G : HTGroup p} {V : Type} [AddCommGroup V] [Module ℂ V] (K : Subgroup G.GAf) (f : G.GAf → ℂ) (Φ : G.GAf × Gr G 1 → V) :
    G.GAf × Gr G 1 → V := fun g => ∑ᶠ h : G.GAf ⧸ K, f h.out • Φ (g * (h.out, 1))

def HasEig (G : HTGroup p) {V : Type} [AddCommGroup V] [Module ℂ V] (ξ : Representation ℂ (G.Cˣ × ℚˣ) V) (K : Subgroup G.GAf)
    {J : Type} (ψ : J → G.GAf → ℂ) (θ : J → ℂ) (e : G.GAf → ℂ) : Prop :=
  ∃ (B : DForm G) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) B.β x t),
    ∃ Φ ∈ HeckeTraceForms.forms (B.embAt x t hx) (K.prod (Kp G)) (ξ.comp (grp G B.β).subtype),
      Φ ≠ 0 ∧ op K e Φ = Φ ∧ ∀ j, op K (ψ j) Φ = θ j • Φ

def HasEigCls (G : HTGroup p) {V : Type} [AddCommGroup V] [Module ℂ V] (ξ : Representation ℂ (G.Cˣ × ℚˣ) V) (K : Subgroup G.GAf)
    {J : Type} (ψ : J → G.GAf → ℂ) (θ : J → ℂ) (e : G.GAf → ℂ) : Prop :=
  ∃ q : DFCls G, ∃ Φ ∈ HeckeTraceForms.forms (Quot.out q).emb (K.prod (Kp G)) (ξ.comp (grp G (Quot.out q).β).subtype),
    Φ ≠ 0 ∧ op K e Φ = Φ ∧ ∀ j, op K (ψ j) Φ = θ j • Φ

structure Rel {A J : Type} (m : A → A → A) (T : J → A) (e u u' : A) : Prop where
  idem : m e e = e
  eT : ∀ j, m e (m (T j) e) = m (T j) e
  eu : m e (m u e) = m u e
  TT : ∀ j j', m (T j) (m (T j') e) = m (T j') (m (T j) e)
  uT : ∀ j, m u (m (T j) e) = m (T j) (m u e)
  inv : m u' (m u e) = e

def powFn {H : Type} [Group H] (K : Subgroup H) (u e : H → ℂ) (j : ℕ) : H → ℂ := (conv K u)^[j] e

def ForPlaces (q : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (Lv : G.Level) (_ : (G.GAf → ℂ) → Prop) (_ : G.GAf → Prop), Prop) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → ∀ (Lv : G.Level)
    (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
    [Algebra G.F k] (P : Pl G k) (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
    (S : Split P Lv.K.toSubgroup H) (k₁ : Type) [Field k₁] [Algebra G.F k₁] (P₁ : Pl G k₁),
    q p G Lv S.Cusp fun g => (P₁.at g).charpoly.Separable

def VanForms : Prop := ForPlaces fun p _ G Lv C R => ∀ f ∈ Hecke ℂ Lv.K.toSubgroup, C f → (∀ g, f g ≠ 0 → R g) →
  ∀ (B : DForm G) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) B.β x t) (y : grp G B.β),
    ¬ RegIrr G ((y.1.1 : G.Cˣ) : G.C) →
    GlobalTheory.LKCount.orbK (MonoidHom.id _) (Lv.K.toSubgroup.prod (Kp G)) (B.embAt x t hx y) (fun h => f h.1 * oneP G h.2) = 0

def VanPairs : Prop := ForPlaces fun _ _ G Lv C R => ∀ f ∈ Hecke ℂ Lv.K.toSubgroup, C f → (∀ g, f g ≠ 0 → R g) →
  ∀ P : Pair G, (∃ μ, P.Mark μ) → ¬ Irreducible P.pol → P.term Lv.K.toSubgroup f 1 (Kp G) (oneP G) = 0

def CuspIdeal : Prop := ForPlaces fun _ _ _ Lv C _ =>
  (∀ a ∈ Hecke ℂ Lv.K.toSubgroup, ∀ f ∈ Hecke ℂ Lv.K.toSubgroup, C f → C (conv Lv.K.toSubgroup a f)) ∧ C 0 ∧
  ∀ f ∈ Hecke ℂ Lv.K.toSubgroup, ∀ f' ∈ Hecke ℂ Lv.K.toSubgroup, ∀ c : ℂ, C f → C f' → C (c • f + f')

def Words : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (Lv : G.Level) (J : Type) (ψ : J → G.GAf → ℂ) (e u u' : G.GAf → ℂ),
    (∀ j, ψ j ∈ Hecke ℂ Lv.K.toSubgroup) → e ∈ Hecke ℂ Lv.K.toSubgroup → u ∈ Hecke ℂ Lv.K.toSubgroup →
    Rel (conv Lv.K.toSubgroup) ψ e u u' → ∀ n : ℕ,
    powFn Lv.K.toSubgroup u e n ∈ Hecke ℂ Lv.K.toSubgroup ∧
    (∀ s, polyFn Lv.K.toSubgroup ψ s (powFn Lv.K.toSubgroup u e n) ∈ Hecke ℂ Lv.K.toSubgroup) ∧
    (∀ j j' w, wordFn Lv.K.toSubgroup ψ (j :: j' :: w) (powFn Lv.K.toSubgroup u e n) =
      wordFn Lv.K.toSubgroup ψ (j' :: j :: w) (powFn Lv.K.toSubgroup u e n)) ∧
    ∀ R : Set G.GAf, (∀ j a, ψ j a ≠ 0 → ∀ g ∈ R, a * g ∈ R) → (∀ g, powFn Lv.K.toSubgroup u e n g ≠ 0 → g ∈ R) →
      ∀ s g, polyFn Lv.K.toSubgroup ψ s (powFn Lv.K.toSubgroup u e n) g ≠ 0 → g ∈ R

def ClsMove : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (V : Type) [AddCommGroup V] [Module ℂ V] (ξ : Representation ℂ (G.Cˣ × ℚˣ) V)
    (K : Subgroup G.GAf) (J : Type) (ψ : J → G.GAf → ℂ) (θ : J → ℂ) (e : G.GAf → ℂ), HasEig G ξ K ψ θ e → HasEigCls G ξ K ψ θ e

def FinData : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → Finite (DFCls G) ∧ ∀ (Lv : G.Level) (V : Type) [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ξ : Representation ℂ (G.Cˣ × ℚˣ) V) (B : DForm G),
    FiniteDimensional ℂ (HeckeTraceForms.forms B.emb (Lv.K.toSubgroup.prod (Kp G)) (ξ.comp (grp G B.β).subtype))

def OpAlg : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (Lv : G.Level) (V : Type) [AddCommGroup V] [Module ℂ V]
    (ξ : Representation ℂ (G.Cˣ × ℚˣ) V) (B : DForm G),
    ∃ T : (G.GAf → ℂ) → Module.End ℂ (HeckeTraceForms.forms B.emb (Lv.K.toSubgroup.prod (Kp G)) (ξ.comp (grp G B.β).subtype)), T 0 = 0 ∧
      ∀ f ∈ Hecke ℂ Lv.K.toSubgroup, (∀ Φ, (T f Φ : G.GAf × Gr G 1 → V) = op Lv.K.toSubgroup f Φ) ∧
        B.trace ξ Lv.K.toSubgroup f (Kp G) (oneP G) = LinearMap.trace ℂ _ (T f) ∧
        ∀ f' ∈ Hecke ℂ Lv.K.toSubgroup, T (conv Lv.K.toSubgroup f f') = T f * T f' ∧ ∀ c : ℂ, T (c • f + f') = c • T f + T f'

def SpecAlg : Prop :=
  ∀ (Q J : Type) [Fintype Q] (W : Q → Type) [∀ q, AddCommGroup (W q)] [∀ q, Module ℂ (W q)] [∀ q, FiniteDimensional ℂ (W q)]
    (T : ∀ q, J → Module.End ℂ (W q)) (e u u' : ∀ q, Module.End ℂ (W q)) (θ : J → ℂ),
    (∀ q, Rel (· * ·) (T q) (e q) (u q) (u' q)) → (∃ q, ∃ x : W q, x ≠ 0 ∧ e q x = x ∧ ∀ j, T q j x = θ j • x) →
    ∃ n : ℕ, 1 ≤ n ∧ ∃ a : List J →₀ ℂ, ∀ s : List J →₀ ℂ, wop θ s ≠ 0 →
      ∑ q, LinearMap.trace ℂ (W q) (wop (T q) (wmul a s) * (u q ^ n * e q)) ≠ 0

def SpecOf : Prop := ForPlaces fun p _ G Lv C R =>
  ∀ (D : Datum p) (L : GlobalTheory.LKGeo.Link D G) (lam : (D.F →+* ℂ) → Fin G.n → ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ξ : Representation ℂ (G.Cˣ × ℚˣ) V), IsWt L lam ξ →
    ∀ (J : Type) (ψ : J → G.GAf → ℂ) (θ : J → ℂ) (e u u' : G.GAf → ℂ),
    (∀ j, ψ j ∈ Hecke ℂ Lv.K.toSubgroup) → e ∈ Hecke ℂ Lv.K.toSubgroup → u ∈ Hecke ℂ Lv.K.toSubgroup →
    u' ∈ Hecke ℂ Lv.K.toSubgroup → Rel (conv Lv.K.toSubgroup) ψ e u u' → C e →
    (∀ n : ℕ, 1 ≤ n → ∃ A : Set G.GAf, (∀ g ∈ A, R g ∧ RegAf G g) ∧ (∀ j a, ψ j a ≠ 0 → ∀ g ∈ A, a * g ∈ A) ∧
      ∀ g, powFn Lv.K.toSubgroup u e n g ≠ 0 → g ∈ A) →
    HasEig G ξ Lv.K.toSubgroup ψ θ e → ∃ n : ℕ, 1 ≤ n ∧ Spec L lam Lv.K.toSubgroup ψ θ (powFn Lv.K.toSubgroup u e n)

def TypeSlice : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (n : ℕ)
    (J : Subgroup (GL (Fin n) k)), IsOpen (J : Set (GL (Fin n) k)) → IsCompact (J : Set (GL (Fin n) k)) →
    ∀ χ : J →* ℂˣ, IsOpen (χ.ker : Set J) →
    (∀ (σ : GlobalTheory.CuspRep.SmIrr (GL (Fin n) k)) (v : σ.V), v ≠ 0 → (∀ g : J, σ.ρ g v = ((χ g : ℂˣ) : ℂ) • v) → GlobalTheory.SmGL.IsCuspidal σ.ρ) →
    ∀ (a b : ℕ) (ε : Fin n ≃ Fin a ⊕ Fin b), 0 < a → 0 < b → ∀ u : (Fin a → Fin b → k) → GL (Fin n) k,
      (∀ X, (u X : Matrix (Fin n) (Fin n) k) = Matrix.reindex ε.symm ε.symm (Matrix.fromBlocks 1 (Matrix.of X) 0 1)) →
      ∀ h : GL (Fin n) k, ∃ X, ∃ hX : h⁻¹ * u X * h ∈ J, χ ⟨_, hX⟩ ≠ 1

end UpperTheory.Gal.Spc
