import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.GlCongr

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.BZMir

namespace PositivityTheory.RgUd.Form

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable (k) in

def colEl (m N : ℕ) (h : m + 2 ≤ N) (x : Fin (m + 1) → k) : GL (Fin N) k :=
  blkAt k (m + 2) N h (unip k (m + 1) (Multiplicative.ofAdd x))

variable (k) in

def xi0 (m : ℕ) : Fin (m + 1) → k := Pi.single (Fin.last m) 1

def AvgData (ψ : AddChar k Circle) {m N : ℕ} (h : m + 2 ≤ N) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) (ξ : Fin (m + 1) → k) (A : AddSubgroup (Fin (m + 1) → k)) (v : V)
    (p : AddSubgroup (Fin (m + 1) → k) × Finset (Fin (m + 1) → k)) : Prop :=
  p.1 ≤ A ∧ IsOpen (p.1 : Set (Fin (m + 1) → k)) ∧ (∀ a ∈ p.1, π (colEl k m N h a) v = v) ∧ (∀ a ∈ p.1, ψ (ξ ⬝ᵥ a) = 1) ∧
    (∀ t ∈ p.2, t ∈ A) ∧ ∀ a ∈ A, ∃! t, t ∈ p.2 ∧ a - t ∈ p.1

open Classical in

def avg (ψ : AddChar k Circle) {m N : ℕ} (h : m + 2 ≤ N) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) (ξ : Fin (m + 1) → k) (A : AddSubgroup (Fin (m + 1) → k)) (v : V) : V :=
  if hd : ∃ p, AvgData ψ h π ξ A v p then
    ((hd.choose.2.card : ℂ)⁻¹) • ∑ t ∈ hd.choose.2, (starRingEnd ℂ ((ψ (ξ ⬝ᵥ t) : Circle) : ℂ)) • π (colEl k m N h t) v
  else 0

def IsLat {m : ℕ} (A : AddSubgroup (Fin (m + 1) → k)) : Prop :=
  IsCompact (A : Set (Fin (m + 1) → k)) ∧ IsOpen (A : Set (Fin (m + 1) → k))

def IsDens (ψ : AddChar k Circle) {m N : ℕ} (h : m + 2 ≤ N) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) (A₀ : AddSubgroup (Fin (m + 1) → k)) (B B' : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) : Prop :=
  ∀ v w, ∃ A₁, IsLat A₁ ∧ A₀ ≤ A₁ ∧ ∀ A, IsLat A → A₁ ≤ A →
    B' v w = ((A₀.relIndex A : ℕ) : ℂ) * B (avg ψ h π (xi0 k m) A v) w

def IsAtom {m N : ℕ} (h : m + 2 ≤ N) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) (B B₀ : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) : Prop :=
  ∀ v w, Filter.Tendsto (fun A : {A : AddSubgroup (Fin (m + 1) → k) // IsLat A} =>
      B (avg (1 : AddChar k Circle) h π 0 A.1 v) w) Filter.atTop (nhds (B₀ v w))

end PositivityTheory.RgUd.Form
