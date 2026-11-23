import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PresDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.GLinkQuot

noncomputable section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

namespace UpperTheory.V.Z.J

section Gen

variable {D N : Type} [Group D] [TopologicalSpace D] [AddCommGroup N]

def Zc (ρ : Representation ℤ D N) : Set (D → N) := {z | IsLocallyConstant z ∧ ∀ s t, z (s * t) = z s + ρ s (z t)}

def HomMu {D N : Type} [Group D] [AddCommGroup N] (l : ℕ) [Fact l.Prime] (k : ℕ) (ε : D →* ℤ_[l]ˣ) (ρ : Representation ℤ D N) :
    Set (N →+ ZMod (l ^ k)) := {f | ∀ s x, f (ρ s x) = PadicInt.toZModPow k (ε s : ℤ_[l]) * f x}

end Gen

def LE (l : ℕ) [Fact l.Prime] (D : Type) [Group D] [TopologicalSpace D] (ε : D →* ℤ_[l]ˣ) (d : ℕ) : Prop :=
  ∀ (k : ℕ), 0 < k → ∀ (N : Type) [AddCommGroup N] [Finite N] (ρ : Representation ℤ D N), (∀ x : N, l ^ k • x = 0) →
    IsOpen (ρ.ker : Set D) → (Zc ρ).Finite ∧ (Zc ρ).ncard = Nat.card N ^ (1 + d) * (HomMu l k ε ρ).ncard

def GenI (l : ℕ) {D : Type} [Group D] [TopologicalSpace D] (I : Subgroup D) (d : ℕ) : Prop :=
  ∃ u : Fin d → D, (∀ a, u a ∈ I) ∧ ∀ (k : ℕ) (A : Type) [AddCommGroup A] [Finite A], (∀ x : A, l ^ k • x = 0) →
    ∀ a : D → A, IsLocallyConstant a → (∀ s t, a (s * t) = a s + a t) → (∀ j, a (u j) = 0) → ∀ g ∈ I, a g = 0

variable {l : ℕ} [Fact l.Prime]

def LocE {κ : Type} [Field κ] (F : Frame l κ) : Prop := ∀ v, LE l (F.Gv v) (F.eps.comp (F.loc v)) (F.dv v)

def ZL {κ : Type} [Field κ] (F : Frame l κ) {N : Type} [AddCommGroup N] (ρ : Representation ℤ F.Γ N)
    (Z : ∀ v, Set (F.Gv v → N)) : Set (F.Γ → N) := {z | z ∈ Zc ρ ∧ ∀ v, (fun s => z (F.loc v s)) ∈ Z v}

def GWL {κ : Type} [Field κ] (F : Frame l κ) : Prop :=
  ∀ (k : ℕ), 0 < k → ∀ (N : Type) [AddCommGroup N] [Finite N] (ρ : Representation ℤ F.Γ N), (∀ x : N, l ^ k • x = 0) →
    IsOpen (ρ.ker : Set F.Γ) → ∀ Z : ∀ v, AddSubgroup (F.Gv v → N), (∀ v, (Z v : Set (F.Gv v → N)) ⊆ Zc (ρ.comp (F.loc v))) →
    (∀ v (Y : N), (fun s => ρ (F.loc v s) Y - Y) ∈ Z v) →
    (ZL F ρ fun v => Z v).Finite ∧
    Nat.card N * ∏ v, Nat.card (Z v) ≤ (ZL F ρ fun v => Z v).ncard * (HomMu l k F.eps ρ).ncard *
      (∏ w, {x : N | ρ (F.cw w) x = x}.ncard) * Nat.card N ^ Fintype.card F.V

section Pt

variable {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O]

abbrev Ok (l : ℕ) (O : Type) [CommRing O] (k : ℕ) : Type := O ⧸ Ideal.span {(l : O) ^ k}

def UnitStep {D : Type} [Group D] [TopologicalSpace D] (I : Subgroup D) (ε : D →* ℤ_[l]ˣ) (t : D →* GL (Fin 3) O) (i : Fin 2) : Prop :=
  (∀ s, (t s : Matrix (Fin 3) (Fin 3) O) i.castSucc i.castSucc =
    algebraMap ℤ_[l] O (ε s) * (t s : Matrix (Fin 3) (Fin 3) O) i.succ i.succ) ∧
  ∃ u β : D → O, AdicCont (maximalIdeal O) u ∧ AdicCont (maximalIdeal O) β ∧ (∀ s s', u (s * s') = u s + u s') ∧
    (∀ s ∈ I, u s = 0) ∧ (∃ s, u s ≠ 0) ∧ ∀ s s', β (s * s') = β s + algebraMap ℤ_[l] O (ε s) * β s' -
      (t s : Matrix (Fin 3) (Fin 3) O) i.castSucc i.succ * ((t s)⁻¹ : GL (Fin 3) O) i.succ i.succ * u s'

structure TriRep {D : Type} [Group D] [TopologicalSpace D] (t : D →* GL (Fin 3) O) : Prop where
  cont : ∀ i j, AdicCont (maximalIdeal O) fun s => (t s : Matrix (Fin 3) (Fin 3) O) i j
  tri : ∀ s, UpT (t s : Matrix (Fin 3) (Fin 3) O)
  dist : ∃ s, ∀ i j, i ≠ j → IsUnit ((t s : Matrix (Fin 3) (Fin 3) O) i i - (t s : Matrix (Fin 3) (Fin 3) O) j j)

def cj {D : Type} [Group D] (k : ℕ) (t : D →* GL (Fin 3) O) (s : D) (X : Matrix (Fin 3) (Fin 3) (Ok l O k)) :
    Matrix (Fin 3) (Fin 3) (Ok l O k) :=
  (t s : Matrix (Fin 3) (Fin 3) O).map (Ideal.Quotient.mk _) * X * (((t s)⁻¹ : GL (Fin 3) O) : Matrix (Fin 3) (Fin 3) O).map (Ideal.Quotient.mk _)

def ZF {D : Type} [Group D] [TopologicalSpace D] (I : Subgroup D) (k : ℕ) (t : D →* GL (Fin 3) O) :
    Set (D → Matrix (Fin 3) (Fin 3) (Ok l O k)) :=
  {z | IsLocallyConstant z ∧ (∀ s s', z (s * s') = z s + cj k t s (z s')) ∧ (∀ s, UpT (z s)) ∧ ∀ s ∈ I, ∀ i, z s i i = 0}

variable {F : Frame l (ResidueField O)}

def Linked (ρ : NRep F 3 O) (v : F.V) (i : Fin 2) : Prop :=
  ∀ s, (ρ.ψ v i.castSucc s : O) = algebraMap ℤ_[l] O (F.eps (F.loc v s)) * (ρ.ψ v i.succ s : O)

def UnitAt (ρ : NRep F 3 O) (v : F.V) (i : Fin 2) : Prop :=
  ∃ (g : GL (Fin 3) O) (t : F.Gv v →* GL (Fin 3) O),
    (∀ s, (t s : Matrix (Fin 3) (Fin 3) O) = (g : Matrix (Fin 3) (Fin 3) O) * ρ.r (F.loc0 v s) * ((g⁻¹ : GL (Fin 3) O) : Matrix (Fin 3) (Fin 3) O)) ∧
    (∀ s, UpT (t s : Matrix (Fin 3) (Fin 3) O)) ∧ (∀ s j, (t s : Matrix (Fin 3) (Fin 3) O) j j = (ρ.ψ v j s : O)) ∧
    UnitStep (F.Iv v) (F.eps.comp (F.loc v)) t i

def WDer {R : Type} [CommRing R] [Algebra O R] (ρ : NRep F 3 R) (ξ : R →ₐ[O] O) (X : Type) [AddCommGroup X] [Module O X] :
    Set (R →ₗ[O] X) :=
  {δ | (∀ a b, δ (a * b) = ξ a • δ b + ξ b • δ a) ∧ ∀ v j, ∀ s ∈ F.Iv v, δ (ρ.ψ v j s : R) = 0}

def triOf {C : Type} [CommRing C] {κ : Type} [Field κ] {F : Frame l κ} (B : Box F 3 C) (v : F.V) : F.Gv v →* GL (Fin 3) C where
  toFun s := B.g v * (B.r (F.loc v s)).left * (B.g v)⁻¹
  map_one' := by simp
  map_mul' s t := by
    have h : (B.r (F.loc v s)).right = 1 := by rw [B.nu]; exact (F.loc0 v s).2
    rw [map_mul, map_mul, SemidirectProduct.mul_left, h, map_one]
    simp [mul_assoc]

abbrev boxK (B : Box F 3 O) (k : ℕ) : Box F 3 (Ok l O k) := B.map (Ideal.Quotient.mk _)

def adK (B : Box F 3 O) (k : ℕ) : Representation ℤ F.Γ (Matrix (Fin 3) (Fin 3) (Ok l O k)) where
  toFun s := ((boxK B k).ad s).toAddMonoidHom.toIntLinearMap
  map_one' := by ext X : 1; simp
  map_mul' s t := by ext X : 1; simp

def Zv (B : Box F 3 O) (k : ℕ) (v : F.V) : Set (F.Gv v → Matrix (Fin 3) (Fin 3) (Ok l O k)) :=
  {z | ∃ z' ∈ ZF (F.Iv v) k (triOf B v), ∃ Y, ∀ s, z s =
    ((((boxK B k).g v)⁻¹ : GL (Fin 3) (Ok l O k)) : Matrix (Fin 3) (Fin 3) (Ok l O k)) * z' s * ((boxK B k).g v : Matrix (Fin 3) (Fin 3) (Ok l O k)) +
      (adK B k (F.loc v s) Y - Y)}

def ZN (B : Box F 3 O) (k : ℕ) : Set (F.Γ → Matrix (Fin 3) (Fin 3) (Ok l O k)) :=
  {z | z ∈ ZL F (adK B k) (Zv B k) ∧ z F.c = 0 ∧ ∀ i j, i ≠ j →
    (z F.g0 * ((boxK B k).r F.g0).mat - z (F.star F.g0) * ((boxK B k).r (F.star F.g0)).mat) i j = 0}

end Pt

def TAN : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O]
    (F : Frame l (ResidueField O)) (C₀ : ℕ), F.Ok C₀ → (l : O) ≠ 0 → GWL F → LocE F → ∀ (S : Space O F 3) (ξ : S.R →ₐ[O] O)
    (v : F.V) (i : Fin 2), UnitAt (S.ρ.map (ξ : S.R →+* O)) v i →
    ∃ δ ∈ WDer S.ρ ξ O, ∃ δ' ∈ WDer S.ρ ξ O, LinearIndependent O ![δ, δ']

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal in

def CountsOf : Prop :=
  GC.Hypotheses₂ → ∀ (l : ℕ) [Fact l.Prime] (κ : Type) [Field κ] (Φ : Frame l κ) (F Ω : Type) [Field F] [NumberField F] [Field Ω]
    [Algebra F Ω] [IsAlgClosure F Ω] S K π ι A pl e c, GC.FLink (F := F) (Ω := Ω) l Φ S K π ι A pl e c → GWL Φ ∧ LocE Φ

end UpperTheory.V.Z.J

end
