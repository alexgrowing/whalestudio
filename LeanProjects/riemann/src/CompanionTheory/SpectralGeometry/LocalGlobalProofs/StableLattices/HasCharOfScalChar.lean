import Mathlib
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.SimpleDistinctness.ScalarCharacterOfL2Embedding
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.Development

noncomputable section

open Finset

namespace GlobalTheory.CompanionTheory.RgExhFin

open CompanionTheory.RgExh CompanionTheory.RgExh.Fin
open Formalism.REAL (GlRel IsUnitary KHighest IsWeight)
open CompanionTheory.D.LK (IsKMod LocFin IsMin)

variable {n : ℕ}

theorem hasChar_path (hS : StepChar) (ss : List (Fin n)) :
    ∀ (X : GMod n) (χ : Fin n → ℂ), HasChar X χ → HasChar (path X χ ss) (pathEnd χ ss) := by
  induction ss with
  | nil => intro X χ h; exact h
  | cons s ss ih => intro X χ h; exact ih _ _ (hS n X χ s h)

theorem hasChar_of_scalChar {X : GMod n} {χ : Fin n → ℂ} (h : ScalChar X χ) : HasChar X χ :=
  ⟨1, fun Y => by rw [pow_one, h Y, sub_self]⟩

theorem capelliPoly_eq_of_perm {χ χ₂ : Fin n → ℂ} (τ τ₂ : Equiv.Perm (Fin n)) (h : ∀ a, χ (τ a) = χ₂ (τ₂ a)) :
    Formalism.QuantumDeterminants.capP χ = Formalism.QuantumDeterminants.capP χ₂ := by
  funext Y
  unfold Formalism.QuantumDeterminants.capP
  rw [← Equiv.prod_comp τ (fun s => Y + χ s), ← Equiv.prod_comp τ₂ (fun s => Y + χ₂ s)]
  exact Finset.prod_congr rfl fun a _ => by rw [h a]

def EndOf (ε : Fin n → Bool) (M : GMod n) (χ : Fin n → ℂ) (ss : List (Fin n))
    (d : Equiv.Perm (Fin n) × (Fin n → ℝ)) : Prop :=
  ∃ (V : Type) (_ : NormedAddCommGroup V) (_ : InnerProductSpace ℂ V) (E : Fin n → Fin n → Module.End ℂ V)
    (hE : GlRel E), IsUnitary ε E ∧ LocFin ε E ∧ IsSimple ⟨V, E, hE⟩ ∧ AlgDS ε ⟨V, E, hE⟩ d.1 d.2 ∧
      Iso (path M χ ss) ⟨V, E, hE⟩

theorem iso_of_ends (hH : Hecke) (hI : IsoFacts) (hU : AlgUniq) {ε : Fin n → Bool} {M M' : GMod n}
    {χ : Fin n → ℂ} {ss : List (Fin n)} {d : Equiv.Perm (Fin n) × (Fin n → ℝ)}
    (hg : GoodPath χ ss) (hM : IsSimple M) (hM' : IsSimple M') (hc : HasChar M χ) (hc' : HasChar M' χ)
    (hs : ScalChar (path M χ ss) (pathEnd χ ss)) (e : EndOf ε M χ ss d) (e' : EndOf ε M' χ ss d) :
    Iso M M' := by
  obtain ⟨V, i1, i2, E, hE, u, l, sm, a, iso⟩ := e
  obtain ⟨V', j1, j2, E', hE', u', l', sm', a', iso'⟩ := e'
  have h := hU n ε V V' E E' hE hE' d.1 d.2 u u' l l' sm sm' a a'
  have h1 := (hI n ε (path M χ ss) ⟨V, E, hE⟩ ⟨V', E', hE'⟩).2.2.1 iso h
  have h2 := (hI n ε (path M' χ ss) ⟨V', E', hE'⟩ (path M' χ ss)).2.1 iso'
  have h3 := (hI n ε (path M χ ss) ⟨V', E', hE'⟩ (path M' χ ss)).2.2.1 h1 h2
  exact (hH n M χ ss hg hM hc hs).2.2 M' hM' hc' h3

theorem finish : StartMod → PathFin → PathExists → PathEndNat → SimpleDistinct → ScalarCharacterOfL2Embedding → UnitarizableOfL2Embedding →
    IsoFacts → CharOfAlgDS → AlgUniq → DataUniq → DSOfArr → DSOfData → KModOf → ArrCount → Finish := by
  intro hSM hPF hPE hPN hSD hSc hUn hI hCh hU hDU hDA hDD hKM hAC hS hH hDec hFR n ε H _ _ σ hσ
  obtain ⟨hcpl, hnt, hur, hir, hsq⟩ := id hσ
  haveI := hcpl
  obtain ⟨D, E, hK⟩ := hKM n ε H σ hur hir
  obtain ⟨hsim, ⟨χ, hχ⟩, hiw⟩ := hSM n ε H σ hur hir hnt D E hK
  obtain ⟨B, hB⟩ := hDec n
  obtain ⟨C, δ, hδ, hP⟩ := hPE n χ B
  obtain ⟨N₀, hN₀⟩ := hFR n C δ hδ
  obtain ⟨ss, N, hN, hg, hfar, hall, hgap, hbd⟩ := hP N₀
  have key : ∀ (H' : Type) [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
      (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')) (D' : Submodule ℂ H')
      (E' : Fin n → Fin n → Module.End ℂ D') (hK' : IsKMod ε σ' D' E'), GlobalTheory.Dec.IsSqIntIrr ε σ' →
      IsSimple ⟨D', E', hK'.gl⟩ → ScalChar ⟨D', E', hK'.gl⟩ χ → IntWt ⟨D', E', hK'.gl⟩ →
      SimplePath χ ss ∧ ScalChar (path ⟨D', E', hK'.gl⟩ χ ss) (pathEnd χ ss) ∧
        ∃ d : Equiv.Perm (Fin n) × (Fin n → ℝ), EndOf ε ⟨D', E', hK'.gl⟩ χ ss d ∧
          Formalism.QuantumDeterminants.IsHCParam d.2 ∧ (∀ a b, a < b → ε (d.1 a) = ε (d.1 b) → d.1 a < d.1 b) ∧
          ∃ τ : Equiv.Perm (Fin n), ∀ a, ((d.2 a : ℝ) : ℂ) = pathEnd χ ss (τ a) := by
    intro H' _ _ _ σ' D' E' hK' hs' hsm' hsc' hiw'
    obtain ⟨_, _, ur, ir, sq⟩ := id hs'
    have hcX := hasChar_of_scalChar hsc'
    have hL := hB ε H' σ' D' E' hK' χ ss ur ir sq hcX hg hfar
    have hce := hasChar_path hS ss _ χ hcX
    have hse := hSc n ε _ _ hL hce
    obtain ⟨sp, sm, -⟩ := hH n _ χ ss hg hsm' hcX hse
    obtain ⟨V, i1, i2, EV, hEV, hun, iso⟩ := hUn n ε _ hL sm
    have facts := hI n ε (path ⟨D', E', hK'.gl⟩ χ ss) ⟨V, EV, hEV⟩ ⟨V, EV, hEV⟩
    have smV : IsSimple ⟨V, EV, hEV⟩ := (facts.2.2.2.1 iso).1 sm
    have scV : ScalChar ⟨V, EV, hEV⟩ (pathEnd χ ss) := (facts.2.2.2.2.1 iso _).1 hse
    have lfV : LocFin ε EV := (facts.2.2.2.2.2.2.1 iso).1 ((hPF n ε _ χ ss).1 hK'.locFin)
    have iwV : IntWt ⟨V, EV, hEV⟩ := (facts.2.2.2.2.2.2.2.1 iso).1 ((hPF n ε _ χ ss).2 hiw')
    obtain ⟨s', mu', hAlg⟩ := hN₀ ε V EV hEV (pathEnd χ ss) N smV.1 hun lfV iwV scV hN hgap hbd
    obtain ⟨τ, hτ⟩ := hCh n ε V EV hEV (pathEnd χ ss) s' mu' hun lfV scV hAlg
    exact ⟨sp, hse, (s', mu'), ⟨V, i1, i2, EV, hEV, hun, lfV, smV, hAlg, iso⟩, hAlg.1, hAlg.2.1, τ, hτ⟩
  obtain ⟨sp, hse, d₀, e₀, hc₀, ho₀, τ₀, hτ₀⟩ := key H σ D E hK hσ hsim hχ hiw
  have hend : ∀ a, pathEnd χ ss a = ((d₀.2 (τ₀.symm a) : ℝ) : ℂ) := fun a => by
    rw [hτ₀, Equiv.apply_symm_apply]
  have hinj' : Function.Injective (pathEnd χ ss) := fun a b h => by
    rw [hend, hend] at h
    exact τ₀.symm.injective (hc₀.1.injective (Complex.ofReal_injective h))
  have hr' : ∀ a, (pathEnd χ ss a).im = 0 ∧ ∃ m : ℤ, (pathEnd χ ss a).re - ((n : ℝ) - 1) / 2 = m := fun a => by
    rw [hend]
    exact ⟨Complex.ofReal_im _, by simpa using hc₀.2 (τ₀.symm a)⟩
  obtain ⟨m, hm, -⟩ := hPN n χ ss
  have hχa : ∀ a, χ a = pathEnd χ ss a - (m a : ℂ) := fun a => by
    rw [hm]; simp
  have hr : ∀ a, (χ a).im = 0 ∧ ∃ m : ℤ, (χ a).re - ((n : ℝ) - 1) / 2 = m := fun a => by
    obtain ⟨h1, k, h2⟩ := hr' a
    refine ⟨by rw [hχa]; simp [h1], k - m a, ?_⟩
    rw [hχa]
    simp only [Complex.sub_re, Complex.natCast_re]
    push_cast
    linarith
  have hinj := hSD n χ ss sp hall
  obtain ⟨A, A', hcard, hA, hA'⟩ := hAC n ε χ (pathEnd χ ss) hinj hinj' hr hr'
  have per : ∀ d : Equiv.Perm (Fin n) × (Fin n → ℝ), ∃ (M : GMod n) (e : Equiv.Perm (Fin n) × (Fin n → ℝ)),
      d ∈ A → e ∈ A' ∧ IsSimple M ∧ HasChar M χ ∧ ScalChar (path M χ ss) (pathEnd χ ss) ∧
        EndOf ε M χ ss e ∧ AlgDS ε M d.1 d.2 ∧ ConeDS ε M d.1 d.2 := by
    intro d
    by_cases hd : d ∈ A
    · obtain ⟨hhc, hord, τ, hτ⟩ := (hA d).1 hd
      obtain ⟨H', i1, i2, i3, σ', hsi, hall'⟩ := hDA n ε d.1 d.2 hhc hord
      obtain ⟨_, hnt', ur', ir', _⟩ := id hsi
      obtain ⟨D', E', hK'⟩ := hKM n ε H' σ' ur' ir'
      obtain ⟨s1, ⟨χd, hχd⟩, iw⟩ := hSM n ε H' σ' ur' ir' hnt' D' E' hK'
      obtain ⟨hAlg, hCone⟩ := hall' D' E' hK'
      obtain ⟨τ', hτ'⟩ := hCh n ε D' E' hK'.gl χd d.1 d.2 hK'.unit hK'.locFin hχd hAlg
      have hcap : Formalism.QuantumDeterminants.capP χd = Formalism.QuantumDeterminants.capP χ :=
        capelliPoly_eq_of_perm τ' τ fun a => by rw [← hτ', ← hτ]
      have hsc : ScalChar ⟨D', E', hK'.gl⟩ χ := fun Y => by rw [hχd Y, hcap]
      obtain ⟨-, hse', e, he, hce, hoe, τe, hτe⟩ := key H' σ' D' E' hK' hsi s1 hsc iw
      exact ⟨⟨D', E', hK'.gl⟩, e, fun _ => ⟨(hA' e).2 ⟨hce, hoe, τe, hτe⟩, s1, hasChar_of_scalChar hsc, hse', he,
        hAlg, hCone⟩⟩
    · exact ⟨triv n, d, fun h => absurd h hd⟩
  haveI : Nonempty (GMod n) := ⟨triv n⟩
  choose! M e hMe using per
  have hmaps : Set.MapsTo e (A : Set _) (A' : Set _) := fun d hd => (hMe d hd).1
  have hinjA : Set.InjOn e (A : Set _) := by
    intro d₁ h₁ d₂ h₂ heq
    obtain ⟨-, s1, c1, p1, n1, a1, k1⟩ := hMe d₁ h₁
    obtain ⟨-, s2, c2, p2, n2, a2, k2⟩ := hMe d₂ h₂
    rw [← heq] at n2
    have hiso := iso_of_ends hH hI hU hg s1 s2 c1 c2 p1 n1 n2
    have a2' : AlgDS ε (M d₁) d₂.1 d₂.2 :=
      ((hI n ε (M d₁) (M d₂) (M d₁)).2.2.2.2.2.2.2.2.1 hiso _ _).2 a2
    obtain ⟨q1, q2⟩ := hDU n ε (M d₁) _ _ _ _ a1 k1 a2'
    exact Prod.ext q1 q2
  have hsurj := Finset.surjOn_of_injOn_of_card_le e hmaps hinjA hcard.symm.le
  obtain ⟨d, hd, hde⟩ := hsurj ((hA' d₀).2 ⟨hc₀, ho₀, τ₀, hτ₀⟩)
  obtain ⟨-, s2, c2, p2, n2, a2, -⟩ := hMe d hd
  rw [hde] at n2
  have hiso := iso_of_ends hH hI hU hg hsim s2 (hasChar_of_scalChar hχ) c2 hse e₀ n2
  have aX : AlgDS ε ⟨D, E, hK.gl⟩ d.1 d.2 :=
    ((hI n ε ⟨D, E, hK.gl⟩ (M d) ⟨D, E, hK.gl⟩).2.2.2.2.2.2.2.2.1 hiso _ _).2 a2
  obtain ⟨hhc, hord, -⟩ := (hA d).1 hd
  exact ⟨d.1, d.2, hhc, hord, hDD n ε H σ D E hK d.1 d.2 hσ aX⟩

end GlobalTheory.CompanionTheory.RgExhFin
