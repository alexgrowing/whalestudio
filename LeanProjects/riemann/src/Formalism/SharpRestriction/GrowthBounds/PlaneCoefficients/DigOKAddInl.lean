import Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.ValuationGeOfLeAddOne

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.PairMembershipBlocks

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords Formalism.MainNotions.G.GLWeightTheory

variable {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {r J : ℕ} (Dt : SignedChainData p O r J)

def Pof : TL J Dt.nL r × Fin r → ℕ
  | (⟨_, Sum.inl _⟩, _) => 1
  | (⟨j, Sum.inr m⟩, _) => Dt.P j m

def keyOf : TL J Dt.nL r × Fin r → Option ((ZMod J × Fin r) × Fin r)
  | (⟨_, Sum.inl _⟩, _) => none
  | (⟨j, Sum.inr m⟩, a) => some ((j, m), a)

theorem liftExp_eq (mo : TL J Dt.nL r × Fin r →₀ ℕ) (v : TL J Dt.nL r × Fin r) :
    Dt.liftExp mo v = mo v / Pof Dt v := by
  rcases v with ⟨⟨j, l | m⟩, a⟩
  · exact (Nat.div_one _).symm
  · rfl

theorem liftVar_inj : Function.Injective Dt.liftVar := by
  rintro ⟨⟨j, l | m⟩, a⟩ ⟨⟨j', l' | m'⟩, a'⟩ h <;>
    simp only [SignedChainData.liftVar, Prod.mk.injEq, reduceCtorEq, ML.ll.injEq, ML.wc.injEq, false_and] at h
  · obtain ⟨⟨rfl, h1⟩, rfl⟩ := h
    cases h1
    rfl
  · obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
    rfl

def liftE (mo : TL J Dt.nL r × Fin r →₀ ℕ) : TL J Dt.nL r × Fin r →₀ ℕ :=
  Finsupp.onFinset mo.support (fun v => mo v / Pof Dt v) (by
    intro v hv
    rw [Finsupp.mem_support_iff]
    intro h0
    apply hv
    simp [h0])

theorem liftE_apply (mo : TL J Dt.nL r × Fin r →₀ ℕ) (v : TL J Dt.nL r × Fin r) :
    liftE Dt mo v = mo v / Pof Dt v := rfl

def liftMon (mo : TL J Dt.nL r × Fin r →₀ ℕ) : ML J Dt.nL r × Fin r →₀ ℕ :=
  Finsupp.mapDomain Dt.liftVar (liftE Dt mo)

theorem prod_lift (mo : TL J Dt.nL r × Fin r →₀ ℕ) :
    ∏ v ∈ mo.support, (X (Dt.liftVar v) : MvPolynomial (ML J Dt.nL r × Fin r) (KK O)) ^ Dt.liftExp mo v =
      monomial (liftMon Dt mo) 1 := by
  have hsub : (liftE Dt mo).support ⊆ mo.support := by
    intro v hv
    rw [Finsupp.mem_support_iff] at hv ⊢
    rw [liftE_apply] at hv
    intro h0
    apply hv
    simp [h0]
  rw [liftMon, MvPolynomial.monomial_eq, C_1, one_mul,
    Finsupp.prod_mapDomain_index (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _),
    Finsupp.prod_of_support_subset _ hsub _ (fun _ _ => pow_zero _)]
  refine Finset.prod_congr rfl (fun v _ => ?_)
  rw [liftE_apply, liftExp_eq]

theorem Fdig_mono (rho : (ZMod J × Fin r) × Fin r → ℕ) (mo : TL J Dt.nL r × Fin r →₀ ℕ) (c : KK O) :
    Dt.Fdig rho (monomial mo c) = if Dt.digOK rho mo then monomial (liftMon Dt mo) c else 0 := by
  unfold SignedChainData.Fdig
  by_cases hc : c = 0
  · subst hc
    simp
  · rw [support_monomial, if_neg hc, Finset.filter_singleton]
    split_ifs with h
    · rw [Finset.sum_singleton, coeff_monomial, if_pos rfl, prod_lift, C_mul_monomial, mul_one]
    · simp

theorem liftMon_w (mo : TL J Dt.nL r × Fin r →₀ ℕ) (v : TL J Dt.nL r × Fin r) :
    liftMon Dt mo (Dt.liftVar v) = mo v / Pof Dt v := by
  rw [liftMon, Finsupp.mapDomain_apply (liftVar_inj Dt)]
  rfl

def Oth (ke : (ZMod J × Fin r) × Fin r) (rho : (ZMod J × Fin r) × Fin r → ℕ) (mo : TL J Dt.nL r × Fin r →₀ ℕ) : Prop :=
  ∀ (j : ZMod J) (m : Fin r) (a : Fin r), ((j, m), a) ≠ ke → mo (⟨j, Sum.inr m⟩, a) % Dt.P j m = rho ((j, m), a)

end Formalism.MainNotions.PairMembershipBlocks
