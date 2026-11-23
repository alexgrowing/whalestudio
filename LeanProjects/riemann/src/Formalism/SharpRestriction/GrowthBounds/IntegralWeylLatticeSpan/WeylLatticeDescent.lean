import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TieLat

open MvPolynomial Matrix Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.BasicNotions Formalism.L2.Forms

noncomputable section

namespace Formalism.L2.G.RelativeIndexFlags

open Formalism.L2.G.Cmp

section Gen

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  (P : Places p O Kf) {Tau : Type} [Fintype Tau] {n : ℕ} {LL : Type} [Field LL]

def IntSpanG (embLL : LL →+* ℂ) (R0 : Subring LL) (lam : Tau → DomWeight n) :
    AddSubgroup (MvPolynomial (Tau × Fin n × Fin n) ℂ) :=
  AddSubgroup.closure {q | ∃ (r : LL) (f : Tau → MvPolynomial (Fin n × Fin n) ℤ), r ∈ R0 ∧ (∀ τ, f τ ∈ delSq ℤ n (lam τ)) ∧
    q = embLL r • ten (fun τ => MvPolynomial.map (Int.castRingHom ℂ) (f τ))}

def nAt (h : P.m + 1 = n) (pos : (Σ v : Fin P.nV, Fin (P.n' v)) ≃ Tau) (N : Tau → GL (Fin n) LL)
    (v : Fin P.nV) (s : Fin (P.n' v)) : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) LL :=
  if Even s.val then (N (pos ⟨v, s⟩) : Matrix (Fin n) (Fin n) LL).submatrix (finCongr h) (finCongr h)
  else (((N (pos ⟨v, s⟩))⁻¹ : GL (Fin n) LL) : Matrix (Fin n) (Fin n) LL)ᵀ.submatrix (finCongr h) (finCongr h)

def CoreAt (h : P.m + 1 = n) (pos : (Σ v : Fin P.nV, Fin (P.n' v)) ≃ Tau) (G : Tau → Matrix (Fin n) (Fin n) ℂ)
    (embLL : LL →+* ℂ) (e : LL →+* Kf) (R0 : Subring LL) (lam : Tau → DomWeight n) (M N : Tau → GL (Fin n) LL)
    (L : P.Tup) (Q : XR P LL) : Prop :=
  MvPolynomial.map e Q ∈ P.HtupW L ↔ ∃ Pp ∈ IntSpanG embLL R0 lam, ∀ z : Frames G,
    evC P h pos G (fun τ => (M τ : Matrix (Fin n) (Fin n) LL).map embLL) (MvPolynomial.map embLL Q) z =
      fnOf G (shiftOf lam) (fun τ => (((N τ)⁻¹ * M τ : GL (Fin n) LL) : Matrix (Fin n) (Fin n) LL).map embLL) Pp z

end Gen

def WeylLatticeDescent : Prop :=
  ∀ {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (P : Places p O Kf) {Tau : Type} [Fintype Tau] {n : ℕ} {LL : Type} [Field LL] (h : P.m + 1 = n)
    (pos : (Σ v : Fin P.nV, Fin (P.n' v)) ≃ Tau) (G : Tau → Matrix (Fin n) (Fin n) ℂ)
    (embLL : LL →+* ℂ) (e : LL →+* Kf) (R0 : Subring LL), IsFractionRing O Kf →
    (∀ x, x ∈ R0 ↔ e x ∈ Set.range (algebraMap O Kf)) → ∀ lam : Tau → DomWeight n, WtTie P h pos lam →
    ∀ (M N : Tau → GL (Fin n) LL) (L : P.Tup),
    (∀ v (s : Fin (P.n' v)), extO O (P.ι v) (P.σ v) s.val (L v) = colSpan O ((nAt P h pos N v s).map e)) →
    ∀ Q : XR P LL, CoreAt P h pos G embLL e R0 lam M N L Q

def DescVal : Prop :=
  ∀ {LL Kf O ι : Type} [Field LL] [Field Kf] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O Kf]
    [IsFractionRing O Kf] (e : LL →+* Kf) (R0 : Subring LL), (∀ x, x ∈ R0 ↔ e x ∈ Set.range (algebraMap O Kf)) →
    ∀ (S : Set (MvPolynomial ι LL)) (Q : MvPolynomial ι LL),
    MvPolynomial.map e Q ∈ Submodule.span O ((fun q => MvPolynomial.map e q) '' S) → Q ∈ Submodule.span R0 S

end Formalism.L2.G.RelativeIndexFlags
