import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.MemPolKIff

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.PlaneGram

namespace TwistData

variable {K : Type} [Field K] (D : TwistData K)

abbrev EA := D.OL × Fin D.r →₀ ℕ

abbrev EM := D.ML × Fin D.r →₀ ℕ

def collapseExponent (p : ℕ) (ζ : D.EM) : D.EA :=
  Finsupp.equivFunOnFinite.symm fun x => Sum.elim (fun b => ζ (D.mb b, x.2))
    (fun t => ζ (D.mlab t, x.2) + D.P p t * ζ (D.mw t, x.2)) x.1

def tpE (ζ : D.EM) : D.EA :=
  Finsupp.equivFunOnFinite.symm fun x => Sum.elim (fun _ => 0) (fun t => ζ (D.mtp t, x.2)) x.1

def phE (p : ℕ) (ζ : D.EM) : D.EA := D.collapseExponent p ζ + D.tpE ζ

def GoodE (p : ℕ) (ζ : D.EM) : Prop :=
  (∀ t a, ζ (D.mlab t, a) < D.P p t) ∧
  (∀ (j : Fin D.J) (m : Fin D.r), m.val = 0 → ∀ a, ζ (D.mtp (j, m), a) = 0) ∧
  (∀ b, ldeg ζ (D.mb b) = D.dB b) ∧
  (∀ t, ldeg ζ (D.mlab t) + D.P p t * ldeg ζ (D.mw t) + ldeg ζ (D.mtp t) = D.dT t) ∧
  (∀ t : D.Tau, ldeg ζ (D.mtp t) ≤ D.dLL t.1)

def Good (p : ℕ) (Z : MvPolynomial (D.ML × Fin D.r) K) : Prop := ∀ ζ ∈ Z.support, D.GoodE p ζ

def abelian₂ (p : ℕ) (F : MvPolynomial (D.OL × Fin D.r) K) (Z : MvPolynomial (D.ML × Fin D.r) K) : K :=
  fock F (D.gaAct (D.ph p Z))

def labF (ζ : D.EM) (t : D.Tau) : Fin D.r → ℕ := fun a => ζ (D.mlab t, a)

def wF (ζ : D.EM) (t : D.Tau) : Fin D.r → ℕ := fun a => ζ (D.mw t, a)

def LabLowE (p : ℕ) (ζ : D.EM) : Prop := ∀ t a, ζ (D.mlab t, a) < D.P p t

def DigOK (v : AddValuation K (WithTop ℚ)) (p : ℕ) (cst : D.Tau → (Fin D.r → ℕ) → ℕ → K)
    (gam : D.Tau → (Fin D.r → ℕ) → (Fin D.r → ℕ) → K) : Prop :=
  (∀ (t : D.Tau) (ρ : Fin D.r → ℕ), (∀ a, ρ a < D.P p t) →
    (∀ n, cst t ρ n ≠ 0) ∧
    (∀ β : Fin D.r → ℕ, v (gam t ρ β) = 0 ∧
      ((∏ a, (ρ a + D.P p t * β a).factorial : ℕ) : K) =
        cst t ρ (∑ a, β a) * ((∏ a, (β a).factorial : ℕ) : K) * gam t ρ β)) ∧
  ∀ ρ : D.Tau → Fin D.r → ℕ, (∀ t a, ρ t a < D.P p t) → ∀ ε : ℤ, (ε = 1 ∨ ε = -1) →
    ∃ (T : Finset (D.Tau × Fin D.r → ℕ)) (lam : (D.Tau × Fin D.r → ℕ) → K),
      (∀ m ∈ T, 0 ≤ v (lam m) ∧ ∑ x, m x ≤ 6 * D.c) ∧
      ∀ β : D.Tau × Fin D.r → ℕ, ((D.c : ℕ) : WithTop ℚ) ≤
        v ((∏ t, gam t (ρ t) (fun a => β (t, a))) ^ ε - binomComb T lam β)

def gaP (p : ℕ) (gam : D.Tau → (Fin D.r → ℕ) → (Fin D.r → ℕ) → K) (ζ : D.EM) : K :=
  D.ga (D.collapseExponent p ζ) * ∏ t, gam t (D.labF ζ t) (D.wF ζ t)

end TwistData

section Steps

variable (K : Type) [Field K] [CharZero K] (v : AddValuation K (WithTop ℚ)) (p : ℕ) (C0 : ℝ)

def StepB : Prop :=
  DVRHyp v p → ∀ D : TwistData K, D.Valid v p → D.Hc p C0 →
    ∀ F : MvPolynomial (D.OL × Fin D.r) K, D.InXX p F → vBB v F = 0 →
      ∃ Gt : MvPolynomial (D.OL × Fin D.r) K, Gt ∈ PolO v D.r D.dO ∧
        (∀ (j : Fin D.J) (m : Fin D.r), m.val + 2 ≤ D.r →
          vala D.osg (D.Tset j m) (D.thl j m - 6 * D.c) Gt) ∧
        vle v (D.n0 v + D.Dl p C0 + 1) (fock F (D.gaAct Gt))

def StepC : Prop :=
  DVRHyp v p → ∀ D : TwistData K, 0 < D.r → 0 < D.J → ∀ (θ : Fin D.J → Fin D.r → ℝ)
    (Gt : MvPolynomial (D.OL × Fin D.r) K), Gt ∈ PolO v D.r D.dO →
      (∀ (j : Fin D.J) (m : Fin D.r), m.val + 2 ≤ D.r → vala D.osg (D.Tset j m) (θ j m) Gt) →
      ∃ Z : MvPolynomial (D.ML × Fin D.r) K, Integral v Z ∧ D.Good p Z ∧ D.ph p Z = Gt ∧
        ∀ (j : Fin D.J) (m : Fin D.r), m.val + 2 ≤ D.r → vala D.msg (D.Yset j m) (θ j m) Z

def StepBC : Prop :=
  DVRHyp v p → ∀ D : TwistData K, D.Valid v p → D.Hc p C0 →
    ∀ F : MvPolynomial (D.OL × Fin D.r) K, D.InXX p F → vBB v F = 0 →
      ∃ Z : MvPolynomial (D.ML × Fin D.r) K, Integral v Z ∧ D.Good p Z ∧
        (∀ (j : Fin D.J) (m : Fin D.r), m.val + 2 ≤ D.r →
          vala D.msg (D.Yset j m) (D.thl j m - 6 * D.c) Z) ∧
        vle v (D.n0 v + D.Dl p C0 + 1) (D.abelian₂ p F Z)

def StepDEF : Prop :=
  DVRHyp v p → ∀ D : TwistData K, D.Valid v p → D.HypH p 13 → D.Hc p C0 →
    ∀ F : MvPolynomial (D.OL × Fin D.r) K, D.InXX p F → vBB v F = 0 →
      ∃ (Ω : MvPolynomial (D.ML × Fin D.r) K →ₗ[K] MvPolynomial (D.ML × Fin D.r) K) (N2 : ℕ),
        (N2 : ℝ) ≤ D.Dm p C0 + D.kapD p / 2 + 1 ∧
        (∀ Z, Integral v Z → D.Good p Z → Integral v (((p : K) ^ N2) • Ω Z)) ∧
        (∀ Z, D.Good p Z → D.Good p (Ω Z)) ∧
        (∀ Z, D.Good p Z → ∀ (j : Fin D.J) (i : Fin (D.nch j)),
          vala D.msg (D.chainSet j i) (D.th j i - D.sl j i - 12 * D.c) (Ω Z)) ∧
        (∀ Z, D.Good p Z → ∀ (j : Fin D.J) (m : Fin D.r) (θ : ℝ), m.val + 2 ≤ D.r →
          vala D.msg (D.Yset j m) θ Z → vala D.msg (D.Yset j m) (θ - 24 * D.c) (Ω Z)) ∧
        (∀ Z, Integral v Z → D.Good p Z →
          vge v (D.c + D.n0 v - 2 * D.kapD p - D.Dm p C0) (D.abelian₂ p F (Ω Z) - D.abelian₂ p F Z))

def StepG : Prop :=
  DVRHyp v p → ∀ D : TwistData K, D.Valid v p → ∀ cst gam, D.DigOK v p cst gam →
    ∃ gp gm : D.EM → K, (∀ ζ, 0 ≤ v (gp ζ)) ∧ (∀ ζ, 0 ≤ v (gm ζ)) ∧
      (∀ ζ, D.LabLowE p ζ → ((D.c : ℕ) : WithTop ℚ) ≤ v (gp ζ - D.gaP p gam ζ) ∧
        ((D.c : ℕ) : WithTop ℚ) ≤ v (gm ζ - (D.gaP p gam ζ)⁻¹)) ∧
      ∀ S : Finset D.ML, (∀ t, D.mlab t ∉ S) → ∀ (θ : ℝ) (Z : MvPolynomial (D.ML × Fin D.r) K),
        vala D.msg S θ Z → vala D.msg S (θ - 12 * D.c) (dg gp Z) ∧ vala D.msg S (θ - 12 * D.c) (dg gm Z)

def StepP : Prop :=
  DVRHyp v p → ∀ D : TwistData K, D.Valid v p →
    ∃ Pj : MvPolynomial (D.ML × Fin D.r) K →ₗ[K] MvPolynomial (D.ML × Fin D.r) K,
      (∀ ζ ζ' : D.EM, ζ' ∈ (Pj (monomial ζ 1)).support → (∀ i, ldeg ζ' i = ldeg ζ i) ∧
        (∀ t a, ζ' (D.mlab t, a) = ζ (D.mlab t, a)) ∧ (∀ t a, ζ' (D.mtp t, a) = ζ (D.mtp t, a))) ∧
      (∀ ζ : D.EM, D.GoodE p ζ → bge v (vN v (fact ζ) / 2 - D.Dm p C0) (Pj (monomial ζ 1))) ∧
      (∀ Z (j : Fin D.J) (i : Fin (D.nch j)), vala D.msg (D.chainSet j i) (D.th j i - D.sl j i) (Pj Z)) ∧
      (∀ (A : MvPolynomial (D.ML × Fin D.r) K) (ζ : D.EM), A ∈ PolK K D.r (fun i => ldeg ζ i) →
        (∀ (j : Fin D.J) (i : Fin (D.nch j)), vala D.msg (D.chainSet j i) (D.th j i - D.sl j i) A) →
        fock A (Pj (monomial ζ 1)) = fock A (monomial ζ 1)) ∧
      (∀ (j : Fin D.J) (m : Fin D.r) (θ : ℝ) Z, vala D.msg (D.Yset j m) θ Z → vala D.msg (D.Yset j m) θ (Pj Z))

def StepE : Prop :=
  DVRHyp v p → ∀ D : TwistData K, D.Valid v p → D.HypH p 13 →
    ∀ F : MvPolynomial (D.OL × Fin D.r) K, D.InXX p F → bge v 0 F →
      ∀ M : D.EA, (∀ b a, M (Sum.inl b, a) = 0) → (∀ t : D.Tau, ldeg M (Sum.inr t) ≤ D.dLL t.1) →
        ∀ ρ : D.Tau → Fin D.r → ℕ, ∃ Q0 E : MvPolynomial (D.ML × Fin D.r) K,
          D.digitPart p ρ (dg (fun α => (D.ga α)⁻¹) (ddiv M (D.gaAct F))) = Q0 + E ∧
          (∀ (j : Fin D.J) (i : Fin (D.nch j)), vala D.msg (D.chainSet j i) (D.th j i - D.sl j i) Q0) ∧
          cge v (D.c - D.n0 v) E

end Steps

end Formalism.MainNotions.PlaneGram
