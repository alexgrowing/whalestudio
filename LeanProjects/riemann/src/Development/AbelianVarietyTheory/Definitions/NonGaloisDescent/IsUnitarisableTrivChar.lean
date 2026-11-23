import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitAtOfIsSplitPl
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.InfOfIsBaseChange

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DefiniteBC

namespace GlobalTheory.BcSpeh

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n c : ℕ}

structure Parts (π : Submodule ℂ (UA E n → ℂ)) (a d : Fin c → ℕ) (h : ∑ i, d i * a i = n) (P : ∀ i, CuspSub E (a i))
    (ρ : ∀ i (w : HeightOneSpectrum (𝓞 E)), LocIrr w (a i)) (m : Fin c → (E →+* ℂ) → Multiset ℂ) : Prop where

  pos : ∀ i, 1 ≤ a i ∧ 1 ≤ d i

  csd : ∀ i, (P i).IsCsd

  loc : ∀ i w, (P i).IsLocComp w (ρ i w)

  inf : ∀ i τ, (P i).HasInfChar τ (m i τ)

  weight : ∀ τ lam, HasWeightAt π τ lam → ∑ i, spehInf (d i) (m i τ) = infOfWeight lam

  distinct : ∀ i j, d i = d j → (⟨a i, CG.mk (P i)⟩ : Σ b, CG E b) = ⟨a j, CG.mk (P j)⟩ → i = j

  inert : ∀ (w : HeightOneSpectrum (𝓞 E)) (s : w.adicCompletion E →+* w.adicCompletion E) (ϖ : w.adicCompletion E) (q : ℕ),
    (∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)) → Formalism.UG.IsUnramInv ϖ s q →
    ∀ α, HasSatAt π w s ϖ q α → ∃ S : Fin c → Multiset ℂˣ, (∀ i, GlobalTheory.LFun.HasSatGL w (ρ i w).ρ (S i)) ∧
      ∑ i, ∑ k : Fin (d i), (S i).map (fun z => (z : ℂ) * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (((d i : ℂ) - 1) / 2 - (k : ℕ))) =
        (GlobalTheory.LGrp.bcParam n α).map (fun z => (z : ℂ))

def BcSpeh : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E],
    (∀ w : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal) →
    ∀ n : ℕ, 1 ≤ n → ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π →
      ∃ (c : ℕ) (a d : Fin c → ℕ) (h : ∑ i, d i * a i = n) (P : ∀ i, CuspSub E (a i)) (ρ : ∀ i (w : HeightOneSpectrum (𝓞 E)), LocIrr w (a i))
        (m : Fin c → (E →+* ℂ) → Multiset ℂ) (σ : ∀ i (w : HeightOneSpectrum (𝓞 E)), LocIrr w (d i * a i)), Parts π a d h P ρ m ∧
        (∀ i w, IsUnitarisable (ρ i w).ρ ∧ IsUnitarisable (σ i w).ρ ∧ GlobalTheory.LocGL.IsSpeh (GlobalTheory.LocGL.IrrGL.of (ρ i w).ρ (ρ i w).smooth (ρ i w).irred) (d i) (σ i w).ρ) ∧
        ∀ w, IsSplitAt w → IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) (locProd h w (σ · w))

def BcString : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E],
    (∀ w : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal) →
    ∀ n : ℕ, 1 ≤ n → ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π →
      ∃ (c : ℕ) (a d : Fin c → ℕ) (h : ∑ i, d i * a i = n) (P : ∀ i, CuspSub E (a i)) (ρ : ∀ i (w : HeightOneSpectrum (𝓞 E)), LocIrr w (a i))
        (m : Fin c → (E →+* ℂ) → Multiset ℂ), Parts π a d h P ρ m ∧
        ∀ w, IsSplitAt w → ∃ (τ : LocIrr w n) (s : Fin c → Multiset (GlobalTheory.LocGL.IrrGL (w.adicCompletion E))),
          IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ ∧ (∀ i, GlobalTheory.LocGL.HasSupport (ρ i w).ρ (s i)) ∧
          GlobalTheory.LocGL.HasSupport τ.ρ (∑ i, ∑ k : Fin (d i), (s i).map fun y => y.nu (((d i : ℂ) - 1) / 2 - (k : ℕ)))

section Trivial

open GlobalTheory.PRep GlobalTheory.UnitaryBC.Model

example {q : ℕ} (hq : q ≠ 0) :
    ∑ k : Fin 3, ({1} : Multiset ℂˣ).map (fun z : ℂˣ => (z : ℂ) * ((q ^ 2 : ℕ) : ℂ) ^ ((((3 : ℕ) : ℂ) - 1) / 2 - (k : ℕ))) =
      (GlobalTheory.LGrp.bcParam 3 (fun _ => Units.mk0 (q : ℂ) (by exact_mod_cast hq) ^ 2)).map fun z : ℂˣ => (z : ℂ) := by
  have e1 : ((((3 : ℕ) : ℂ) - 1) / 2 - ((0 : Fin 3) : ℕ)) = 1 := by norm_num
  have e2 : ((((3 : ℕ) : ℂ) - 1) / 2 - ((1 : Fin 3) : ℕ)) = 0 := by norm_num
  have e3 : ((((3 : ℕ) : ℂ) - 1) / 2 - ((2 : Fin 3) : ℕ)) = -1 := by norm_num
  rw [Fin.sum_univ_three, e1, e2, e3, Complex.cpow_neg, add_right_comm]
  simp [GlobalTheory.LGrp.bcParam]

end Trivial

end GlobalTheory.BcSpeh
