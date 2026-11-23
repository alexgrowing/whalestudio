import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.FlipTwoThree
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.IsUnitOrIsUnitOfAddOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.LeAdicClosure
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.UniversalOrdinaryDeterminantRing

noncomputable section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

namespace UpperTheory.V.Pr

section Nice

variable {l : ℕ} [Fact l.Prime] {k : Type} [Field k] {F : Frame l k} {n : ℕ} {R : Type} [CommRing R]

structure Nice (ρ : NRep F n R) (p : Ideal R) : Prop where
  prime : p.IsPrime
  dim : qdim p = 1
  char : (l : R) ∈ p
  off : ρ.OffTri p
  sep : ∀ v i j, i ≠ j → ¬ ρ.Coin p v i j

def ThickLink [IsLocalRing R] (ρ : NRep F 3 R) (p q : Ideal R) : Prop :=
  Nice ρ p ∧ ρ.TE p ∧ Nice ρ q ∧ ρ.TE q ∧ ∃ e : Ideal R, e.IsPrime ∧ Thick ρ e ∧ e ≤ p ∧ e ≤ q

end Nice

section Input

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] {F : Frame l (ResidueField O)} {n : ℕ}

def P1' (S : Space O F n) (M : Ideal S.B) : Prop :=
  ∀ (x : Ideal S.A) (L : S.Loc x) (p : Ideal L.R), Nice L.ρ p → L.ρ.TI p → M ≤ L.π p →
    ∀ P : Ideal L.R, P.IsPrime → P ≤ p → M ≤ L.π P

def P23' (S : Space O F 3) (M : Ideal S.B) : Prop :=
  ∀ (x : Ideal S.A) (L : S.Loc x) (p q : Ideal L.R), Nice L.ρ p → L.ρ.TE p → Relation.ReflTransGen (ThickLink L.ρ) p q →
    (∃ P : Ideal L.R, P.IsPrime ∧ P ≤ p ∧ L.ρ.TI P ∧ M ≤ L.π P) →
    ∀ P' : Ideal L.R, P'.IsPrime → P' ≤ q → L.ρ.TI P' → M ≤ L.π P'

def SeedIn (S : Space O F n) (M : Ideal S.B) : Prop :=
  ∃ (ξ : Ideal S.A) (Z : Ideal S.B), ξ.IsPrime ∧ S.u.TI ξ ∧ Z.IsPrime ∧ M ≤ Z ∧ Z ≤ S.π ξ ∧
    qdim Z = ((1 + n * F.d : ℕ) : WithBot ℕ∞)

def AllGood (S : Space O F n) (M : Ideal S.B) : Prop := ∀ p : Ideal S.A, p.IsPrime → S.u.TI p → M ≤ S.π p

def OffFin (S : Space O F n) : Prop := ∃ I : Ideal S.B, S.FinLam I ∧ ∀ p : Ideal S.A, p.IsPrime → S.u.OffTri p → I ≤ S.π p

end Input

def PropagationTheoremGL2 : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O]
    (F : Frame l (ResidueField O)) (C₀ : ℕ), F.Ok C₀ → F.Big C₀ → ∀ (S : Space O F 2) (M : Ideal S.B),
    S.FinLam M → P1' S M → SeedIn S M → AllGood S M

def PropagationTheoremGL3 : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O]
    (F : Frame l (ResidueField O)) (C₀ : ℕ), F.Ok C₀ → F.Big C₀ → ∀ (S₂ : Space O F 2) (M₂ : Ideal S₂.B),
    S₂.FinLam M₂ → AllGood S₂ M₂ → ∀ (S : Space O F 3) (M : Ideal S.B),
    S.FinLam M → P1' S M → P23' S M → SeedIn S M → AllGood S M ∧ OffFin S

section Points

variable {l : ℕ} [Fact l.Prime] (O : Type) [CommRing O] [IsLocalRing O] {F : Frame l (ResidueField O)} {n : ℕ}

structure IsLiftA {A : Type} [CommRing A] [IsLocalRing A] [Algebra O A] [IsLocalHom (algebraMap O A)]
    (ρ : NRep F n A) : Prop where
  cont : ρ.Cont (maximalIdeal A)
  bar : (ρ.map (residue A)).IsBar (ResidueField.map (algebraMap O A))
  diag : (ρ.map (residue A)).IsDiag

variable (F n) in

def FinPt : Prop :=
  ∀ (A : Type) [CommRing A] [Algebra O A] [IsCD O A] [Algebra (ResidueField O) A] [IsScalarTower O (ResidueField O) A]
    (ρ : NRep F n A), IsLiftA O ρ → (∀ v i, ∀ g ∈ F.Iv v, F.Ψ (F.loc v g) = 1 → ρ.ψ v i g = 1) →
    ∀ g, (ρ.r g).charpoly =
      ∏ i, (Polynomial.X - Polynomial.C (algebraMap (ResidueField O) A ((F.Ψ g ^ w n i : (ResidueField O)ˣ) : ResidueField O)))

end Points

def FinPtOf : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O]
    (F : Frame l (ResidueField O)) (C₀ : ℕ), F.Ok C₀ → ∀ S : Space O F 3, OffFin S → FinPt O F 3

section Link

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O]
  (F : Frame l (ResidueField O)) {n : ℕ} {G : W.GFrame l} (r : W.Resid G O n)

structure TwLink where
  π : G.G₀ →* F.G0
  π_cont : Continuous π
  π_surj : Function.Surjective π
  π_conj : ∀ g, π (G.conj g) = F.conj (π g)
  π_eps : ∀ g : G.G₀, F.eps (π g) = G.ε g
  e : G.Vl ≃ F.V
  lam : ∀ v, G.Gv v ≃ₜ* F.Gv (e v)
  lam_loc : ∀ v g, F.loc0 (e v) (lam v g) = π (G.φ v g)
  lam_I : ∀ v g, lam v g ∈ F.Iv (e v) ↔ g ∈ G.Iv v
  κ : G.G₀ →* Oˣ
  κ_cont : AdicCont (maximalIdeal O) fun g => (κ g : O)
  κ_conj : ∀ g, κ g * κ (G.conj g) = G.eps O O g ^ (1 - (n : ℤ))
  chib : ∀ i g, r.chib i g = F.Ψ (π g) ^ w n i * W.pushCh (residue O) κ g
  psib : ∀ v i g, r.psib v i g = r.chib i (G.φ v g)
  mu : ∀ v, G.mu v ≤ (commutator (G.Gv v)).topologicalClosure
  tame : ∀ u, ∀ g ∈ G.Iu u, ∃ m : ℕ, ¬ l ∣ m ∧ π g ^ m = 1 ∧ κ g ^ m = 1
  ramκ : ∀ g ∈ G.I0, κ g = 1
  ker : ∀ N : Subgroup G.G₀, N.Normal → IsClosed (N : Set G.G₀) → (∀ g ∈ N, G.conj g ∈ N) →
    (∀ u, ∀ g ∈ G.Iu u, F.Ψ (π g) = 1 → g ∈ N) → G.I0 ≤ N → π.ker ≤ N

namespace TwLink

variable {F r} (K : TwLink F r) {A : Type} [CommRing A] [Algebra O A]

def κA (A : Type) [CommRing A] [Algebra O A] : G.G₀ →* Aˣ := W.pushCh (algebraMap O A) K.κ

def tw (ρ : NRep F n A) : G.G₀ →* Matrix (Fin n) (Fin n) A where
  toFun g := ((K.κA A g : Aˣ) : A) • ρ.r (K.π g)
  map_one' := by simp
  map_mul' g h := by simp [smul_smul, mul_comm]

def twψ (ρ : NRep F n A) (v : G.Vl) (i : Fin n) : G.Gv v →* Aˣ :=
  (ρ.ψ (K.e v) i).comp (K.lam v).toMulEquiv.toMonoidHom * (K.κA A).comp (G.φ v)

def IsPhi (B : W.UniversalOrdinaryDeterminantRing r) (S : Space O F n) (Φ : B.B →ₐ[O] S.B) : Prop :=
  B.u.Maps ((S.B.val.comp Φ : B.B →ₐ[O] S.R) : B.B →+* S.R) (W.GDet.ofRep (K.tw S.ρ)) (K.twψ S.ρ)

end TwLink

end Link

end UpperTheory.V.Pr

end
