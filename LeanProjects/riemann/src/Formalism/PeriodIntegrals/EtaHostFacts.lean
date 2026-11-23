import Formalism.FrobeniusOrbits.HostCorollaries
import Formalism.LocalRingCardinality.DataHost
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host

namespace PI.EtaHostFacts

instance psiFintype (φ : Formalism.HC.Frame) : Fintype φ.Psi := Fintype.ofFinite _

def Unram : Prop := ∀ (R : Formalism.BasicNotions.Ranks) (H : Formalism.BasicNotions.Host R),
  ∀ P : HeightOneSpectrum (𝓞 H.E), (aboveF (L := H.E) H.F (P.under (𝓞 H.F))).card = 1 →
    P.asIdeal.ramificationIdx (𝓞 H.F) = 1

def TotReal : Prop := ∀ (R : Formalism.BasicNotions.Ranks) (H : Formalism.BasicNotions.Host R), ∀ w : InfinitePlace H.F, w.IsReal

open Classical in

def OnePsi : Prop := Formalism.BasicNotions.FactCardPsi → Formalism.BasicNotions.FactEmb → ∀ (R : Formalism.BasicNotions.Ranks) (H : Formalism.BasicNotions.Host R),
  ∀ w : InfinitePlace H.F,
    (Finset.univ.filter (fun i : R.Psi =>
      InfinitePlace.mk (H.emb (i : R.GG)) ∈ aboveInf (L := H.E) H.F w)).card = 1

def Conj : Prop := ∀ (R : Formalism.BasicNotions.Ranks) (H : Formalism.BasicNotions.Host R),
  ∃ c : H.E →ₐ[H.F] H.E, (∀ x, c (c x) = x) ∧ (∀ x, c x = x → ∃ a : H.F, algebraMap H.F H.E a = x) ∧
    (∀ (φ : H.E →+* ℂ) (x : H.E), φ (c x) = starRingEnd ℂ (φ x)) ∧ c H.sqrtMinusD = -H.sqrtMinusD

def Roots : Prop := ∀ (R : Formalism.BasicNotions.Ranks) (H : Formalism.BasicNotions.Host R),
  ∀ z : H.E, (∃ n : ℕ, 0 < n ∧ z ^ n = 1) → Algebra.norm H.K z = 1

def SqrtNe : Prop := ∀ (R : Formalism.BasicNotions.Ranks) (H : Formalism.BasicNotions.Host R), H.sqrtMinusD ≠ 0

def SqrtPos : Prop := ∀ (R : Formalism.BasicNotions.Ranks) (H : Formalism.BasicNotions.Host R),
  ∀ s : H.Eˣ, (s : H.E) = H.sqrtMinusD → ∀ i : R.Psi,
    ∃ r : ℝ, 0 < r ∧ H.emb (i : R.GG) (s : H.E) = Complex.I * r

def Card4 : Prop := Formalism.BasicNotions.FactCardPsi → ∀ (R : Formalism.BasicNotions.Ranks) (_H : Formalism.BasicNotions.Host R),
  4 ∣ Fintype.card (R.Psi)

def DSplit : Prop := ∀ (R : Formalism.BasicNotions.Ranks) (H : Formalism.BasicNotions.Host R),
  ∀ s : H.Eˣ, (s : H.E) = H.sqrtMinusD →
    ∀ P : HeightOneSpectrum (𝓞 H.E), ordF P s ≠ 0 → (aboveF (L := H.E) H.F (P.under (𝓞 H.F))).card ≠ 1

def Target : Prop := Unram ∧ TotReal ∧ OnePsi ∧ Conj ∧ Roots ∧ SqrtNe ∧ SqrtPos ∧ Card4 ∧ DSplit

end PI.EtaHostFacts
