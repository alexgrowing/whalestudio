import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterDeRham
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.DeRhamJacobian.IsdRJ
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LineOfSingleJump
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamComponentsCrystallineLettersFinrank
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinrankDdRFinsum

noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal
open scoped Classical

namespace GlobalTheory.CompanionTheory.HLCMul

open Formalism.MainNotions.N Module

theorem char_mul {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI)
    (K LL : FinExt l) (hcard : Nat.card (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) = finrank ℚ_[l] ↥K.1)
    (ν₁ ν₂ ν₃ : Representation ↥LL.1 ↥(GK K) (Fin 1 → ↥LL.1)) (χ₁ χ₂ : ↥(GK K) → ↥LL.1)
    (h₂ : ∀ g x, ν₂ g x = χ₂ g • x) (h₁ : ∀ g x, ν₁ g x = χ₁ g • x)
    (h₃ : ∀ g x, ν₃ g x = (χ₁ g * χ₂ g) • x)
    (J₁ J₂ : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → ℤ)
    (d₂ : IsDR (P.PD K) ν₂)
    (m₁ : ∀ τ a, multV (P.PD K) ν₁ τ a = if a = J₁ τ then 1 else 0)
    (m₂ : ∀ τ a, multV (P.PD K) ν₂ τ a = if a = J₂ τ then 1 else 0) :
    IsDR (P.PD K) ν₃ ∧ ∀ τ a, multV (P.PD K) ν₃ τ a = if a = J₁ τ + J₂ τ then 1 else 0 := by
  have hm : ∀ τ a, multV (P.PD K) ν₃ τ a = if a = J₁ τ + J₂ τ then 1 else 0 := by
    intro τ a
    have := GlobalTheory.TwistJump.multV_twist_char l P AI T K LL (Fin 1 → ↥LL.1) ν₁ ν₃ ν₂ χ₂ h₂
      (fun g x => by rw [h₃, h₁, smul_smul, mul_comm]) d₂ τ (J₂ τ) (m₂ τ) (a - J₂ τ)
    rw [sub_add_cancel] at this
    rw [this, m₁]
    simp only [sub_eq_iff_eq_add]
  refine ⟨?_, hm⟩
  haveI := K.2
  haveI := (GlobalTheory.Per.TiedDdR.ddR_finrank_le l P AI T K LL _ ν₃).1
  have hc : Fintype.card (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) = finrank ℚ_[l] ↥K.1 := by
    rw [← hcard, Nat.card_eq_fintype_card]
  have hone : ∀ τ, finrank ↥LL.1 ↥(DdRE (P.PD K) ν₃ τ) = 1 := by
    intro τ
    obtain ⟨hf, hle, -⟩ := (GlobalTheory.Per.Components.components_finrank l P AI T K LL _ ν₃).1 τ
    have hm1 := hm τ (J₁ τ + J₂ τ)
    rw [if_pos rfl, multV] at hm1
    have hfil : finrank ↥LL.1 ↥(FildR (P.PD K) ν₃ τ (J₁ τ + J₂ τ)) ≤ finrank ↥LL.1 ↥(DdRE (P.PD K) ν₃ τ) :=
      Submodule.finrank_mono (inf_le_left : FildR (P.PD K) ν₃ τ _ ≤ DdRE (P.PD K) ν₃ τ)
    simp only [finrank_fin_fun, finrank_self, Module.finrank_pi, Fintype.card_fin] at hle
    omega
  obtain ⟨e1, -⟩ := GlobalTheory.DeRhamSplit.finrank_DdR (P.PD K) ν₃ hc 0
  rw [IsDR, e1, Finset.sum_congr rfl fun τ _ => hone τ]
  simp [hc]

theorem repE_apply {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
    {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : LocBridge l E Ω Gw O) (LL' : FinExt l) (ψ : ↥Gw →* (↥LL'.1)ˣ) (g : ↥(GK Bw.Kw))
    (x : Fin 1 → ↥LL'.1) :
    Bw.repE LL' ((PositivityTheory.HodgeLocalCharacter.HLC.toGL1 ↥LL'.1).comp ψ) g x = ((ψ (Bw.e.symm g) : (↥LL'.1)ˣ) : ↥LL'.1) • x := by
  ext i
  obtain rfl : i = 0 := Subsingleton.elim _ _
  simp [LocBridge.repE, PositivityTheory.HodgeLocalCharacter.HLC.toGL1, Matrix.mulVec, dotProduct]

theorem isdRJ_mul : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), IsPlaceOver A w →
    ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O),
      GlobalTheory.Pst.Induces Bw →
    ∀ (LL' : FinExt l), Bw.LL.1 ≤ LL'.1 → ∀ (ψ₁ ψ₂ : ↥(Dec (F := E) A) →* (↥LL'.1)ˣ)
      (J₁ J₂ : (↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1) → ℤ),
      PositivityTheory.HodgeLocalCharacter.HLC.IsdRJ Bw P LL' ψ₁ J₁ → PositivityTheory.HodgeLocalCharacter.HLC.IsdRJ Bw P LL' ψ₂ J₂ →
      PositivityTheory.HodgeLocalCharacter.HLC.IsdRJ Bw P LL' (ψ₁ * ψ₂) (J₁ + J₂) := by
  rintro E Ω _ _ _ _ _ l _ P AI ⟨T⟩ w A _ O _ _ _ Bw _ LL' hLL ψ₁ ψ₂ J₁ J₂ ⟨-, m₁⟩ ⟨d₂, m₂⟩
  have hcard := GlobalTheory.DeRhamSplit.card_emb Bw.Kw LL' fun τ x => hLL (Bw.LL_split τ x)
  obtain ⟨a, b⟩ := char_mul P AI T Bw.Kw LL' hcard
    (Bw.repE LL' ((PositivityTheory.HodgeLocalCharacter.HLC.toGL1 ↥LL'.1).comp ψ₁))
    (Bw.repE LL' ((PositivityTheory.HodgeLocalCharacter.HLC.toGL1 ↥LL'.1).comp ψ₂))
    (Bw.repE LL' ((PositivityTheory.HodgeLocalCharacter.HLC.toGL1 ↥LL'.1).comp (ψ₁ * ψ₂)))
    (fun g => ((ψ₁ (Bw.e.symm g) : (↥LL'.1)ˣ) : ↥LL'.1)) (fun g => ((ψ₂ (Bw.e.symm g) : (↥LL'.1)ˣ) : ↥LL'.1))
    (fun g x => repE_apply Bw LL' ψ₂ g x) (fun g x => repE_apply Bw LL' ψ₁ g x)
    (fun g x => by rw [repE_apply]; simp) J₁ J₂
    (by unfold IsDR; simpa [LocBridge.IsdRE] using d₂) m₁ m₂
  refine ⟨?_, fun τ c => ?_⟩
  · unfold IsDR at a
    simpa [LocBridge.IsdRE] using a
  · simpa [LocBridge.multE] using b τ c

end GlobalTheory.CompanionTheory.HLCMul
