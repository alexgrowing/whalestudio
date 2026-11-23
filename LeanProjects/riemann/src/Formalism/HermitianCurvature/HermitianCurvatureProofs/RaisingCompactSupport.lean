import Formalism.HermitianCurvature.HermitianCurvatureProofs.RadAATopOfParts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CapelliWordSumExpansion
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheoremPIntegralOfPlaces
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormDiagonalEntryDilationGeneratorLeOne
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ContDiffHerm

open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.GaugeNormPower

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.CapelliWordSumExpansion

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section closed

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem aa_closed (P : (Mat k r → E) → Prop)
    (hRd : ∀ (X : Mat k r) (f : Mat k r → E), inLie k r X → P f → P (RdV X f))
    (hadd : ∀ f₁ f₂ : Mat k r → E, P f₁ → P f₂ → P (fun x => f₁ x + f₂ x))
    (hmul : ∀ (φ : Mat k r → ℂ), ContDiff ℝ (⊤ : ℕ∞) φ → ∀ f : Mat k r → E, P f → P (fun x => φ x • f x))
    (hzero : P (fun _ => 0)) (m : ℕ) (hm : m ≤ r) (u : ℂ) (f : Mat k r → E) (hf : P f) :
    P (C3.AAop k r m hm u f) :=
  _root_.UpperTheory.Reformulated.B.Qj20.aa_closed P hRd hadd hmul hzero m hm u f hf

theorem loc_add' {m : ℕ∞} {f₁ f₂ : Mat k r → E} {g : Mat k r} (h₁ : Loc m f₁ g) (h₂ : Loc m f₂ g) :
    Loc m (fun x => f₁ x + f₂ x) g := by
  obtain ⟨U₁, f₁', hU₁, hg₁, hf₁, he₁⟩ := h₁
  obtain ⟨U₂, f₂', hU₂, hg₂, hf₂, he₂⟩ := h₂
  exact ⟨U₁ ∩ U₂, fun x => f₁' x + f₂' x, hU₁.inter hU₂, ⟨hg₁, hg₂⟩,
    (hf₁.mono Set.inter_subset_left).add (hf₂.mono Set.inter_subset_right),
    fun x hx hxG => by show f₁ x + f₂ x = f₁' x + f₂' x; rw [he₁ x hx.1 hxG, he₂ x hx.2 hxG]⟩

theorem loc_smulFun {m : ℕ∞} (φ : Mat k r → ℂ) {V : Set (Mat k r)} (hV : IsOpen V)
    (hφ : ContDiffOn ℝ (m : WithTop ℕ∞) φ V) {f : Mat k r → E} {g : Mat k r} (hgV : g ∈ V) (h : Loc m f g) :
    Loc m (fun x => φ x • f x) g := by
  obtain ⟨U, f', hU, hgU, hf, he⟩ := h
  exact ⟨U ∩ V, fun x => φ x • f' x, hU.inter hV, ⟨hgU, hgV⟩,
    (hφ.mono Set.inter_subset_right).smul (hf.mono Set.inter_subset_left),
    fun x hx hxG => by show φ x • f x = φ x • f' x; rw [he x hx.1 hxG]⟩

theorem loc_zero' {m : ℕ∞} {g : Mat k r} : Loc m (fun _ => (0 : E)) g :=
  ⟨Set.univ, fun _ => 0, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩

theorem loc_AAop {f : Mat k r → E} {g : Mat k r} (h : Loc ⊤ f g) (m : ℕ) (hm : m ≤ r) (u : ℂ) :
    Loc ⊤ (C3.AAop k r m hm u f) g := by
  refine aa_closed (fun f => Loc ⊤ f g) (fun X f hX hf => ?_) (fun _ _ h₁ h₂ => loc_add' h₁ h₂)
    (fun φ hφ f hf => loc_smulFun φ isOpen_univ hφ.contDiffOn (Set.mem_univ g) hf) loc_zero' m hm u f h
  have hf' : Loc ((⊤ : ℕ∞) + 1) f g := by rw [top_add]; exact hf
  exact loc_RdV hX hf'

theorem zero_AAop {f : Mat k r → E} {U : Set (Mat k r)} (hU : IsOpen U) (h : ∀ x ∈ U, x ∈ GV k r → f x = 0)
    (m : ℕ) (hm : m ≤ r) (u : ℂ) : ∀ x ∈ U, x ∈ GV k r → C3.AAop k r m hm u f x = 0 := by
  refine aa_closed (fun f => ∀ x ∈ U, x ∈ GV k r → f x = 0) (fun X f hX hf => ?_)
    (fun f₁ f₂ h₁ h₂ x hx hxG => by simp [h₁ x hx hxG, h₂ x hx hxG])
    (fun φ _ f hf x hx hxG => by simp [hf x hx hxG]) (fun _ _ _ => rfl) m hm u f h
  intro x hx hxG
  rw [rdV_congr (f₂ := fun _ => (0 : E)) hU hx hxG hX (fun y hy hyG => hf y hy hyG)]
  simp [RdV]

end closed

end Formalism.FourierDecayAlt.P.GaugeNormPower

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.CapelliWordSumExpansion Formalism.FourierDecayAlt.P.GaugeNormPower

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem raising_compact_support : PBN.AACpt := by
  intro k r Wp Wq _ _ _ _ Bs F y hF
  obtain ⟨hs, ⟨R, hR⟩, ⟨ε, hε, hG⟩⟩ := hF
  have hGc : Continuous fun g : Mat k r => Gf k r Bs.z Bs.z' g :=
    (Formalism.FourierDecayAlt.P.JCx1.contDiff_Gf Bs.z Bs.z').continuous
  have hvan : ∀ U : Set (Mat k r), IsOpen U → (∀ x ∈ U, x ∈ GV k r → F x = 0) →
      ∀ x ∈ U, x ∈ GV k r → PBN.aaTop Bs y F x = 0 := by
    intro U hU hF0 x hx hxG
    have := zero_AAop hU hF0 r le_rfl ((y : ℂ) + ((2 * r + k : ℕ) : ℂ) / 2) x hx hxG
    simp only [PBN.aaTop, this, smul_zero]
  have hUε : IsOpen {x : Mat k r | Gf k r Bs.z Bs.z' x < ε} := isOpen_lt hGc continuous_const
  have hFε : ∀ x ∈ {x : Mat k r | Gf k r Bs.z Bs.z' x < ε}, x ∈ GV k r → F x = 0 := by
    intro x hx hxG
    by_contra h
    exact absurd (hG x hxG h) (not_le.mpr hx)
  refine ⟨?_, ⟨R, ?_⟩, ⟨ε, hε, ?_⟩⟩
  · intro g₀ hg₀
    by_cases hlt : Gf k r Bs.z Bs.z' g₀ < ε
    · exact ⟨_, fun _ => 0, hUε, hlt, contDiffOn_const, fun x hx hxG => hvan _ hUε hFε x hx hxG⟩
    · push Not at hlt
      have hD : Dmin k r Bs.z Bs.z' g₀ (Fin.last (r + 1)) ≠ 0 := by
        intro h0
        have h1 : 0 ≤ Tz k r Bs.z * Tz k r Bs.z' * Complex.normSq (Dmin k r Bs.z Bs.z' g₀ ⟨r, by omega⟩) :=
          mul_nonneg (mul_pos Bs.T_pos Bs.T'_pos).le (Complex.normSq_nonneg _)
        simp only [Gf, h0, map_zero] at hlt
        linarith
      have hDc : ContDiff ℝ (⊤ : ℕ∞) fun x : Mat k r => Dmin k r Bs.z Bs.z' x (Fin.last (r + 1)) :=
        Formalism.FourierDecayAlt.P.JCx1.contDiff_Dmin Bs.z Bs.z' _
      have hV : IsOpen {x : Mat k r | Dmin k r Bs.z Bs.z' x (Fin.last (r + 1)) ≠ 0} :=
        isOpen_ne_fun hDc.continuous continuous_const
      have hloc : Loc ⊤ (C3.AAop k r r le_rfl ((y : ℂ) + ((2 * r + k : ℕ) : ℂ) / 2) F) g₀ :=
        loc_AAop (hs g₀ hg₀) r le_rfl _
      exact loc_smulFun (fun x => (Dmin k r Bs.z Bs.z' x (Fin.last (r + 1)))⁻¹) hV
        (hDc.contDiffOn.inv fun x hx => hx) hD hloc
  · intro g hg hne
    by_contra hgt
    push Not at hgt
    have hU : IsOpen {x : Mat k r | R < gN x} := isOpen_lt continuous_const Formalism.FourierDecayAlt.P.B6.gN_continuous
    refine hne (hvan _ hU (fun x hx hxG => ?_) g hgt hg)
    by_contra h
    exact absurd (hR x hxG h) (not_le.mpr hx)
  · intro g hg hne
    by_contra hlt
    push Not at hlt
    exact hne (hvan _ hUε hFε g hlt hg)

end Formalism.FourierDecayAlt.P
