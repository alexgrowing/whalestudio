import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.VolumePerpendicular

open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

section Spaces

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def IsKind (W : HSpace E) (M P Q : ℕ) : Prop :=
  W.rank = M ∧ W.SigOK ∧ ∀ τ : E →+* ℂ, W.sig τ = (P, Q)

def IsPerp (W : HSpace E) (x : W.V) (W' : HSpace E) (ι : W'.V →ₗ[E] W.V) : Prop :=
  Function.Injective ι ∧ (∀ a b, W.hD (ι a) (ι b) = W'.hD a b) ∧
    ∀ y : W.V, (∃ a, ι a = y) ↔ W.hD y x = 0

end Spaces

def IsVol (D : D7) : letI := D.host.cmStar; HSpace D.host.E → ℕ → ℕ → ℝ → Prop :=
  letI := D.host.cmStar
  fun W P Q V =>
    0 < V ∧
    AllSome (IsVolMeas D W P Q) fun μ =>
    AllSome (fun 𝓕 => IsFundamentalDomain (HFinIn (AF D.host.F) D.sp.cm.sig W.gram) 𝓕 μ) fun 𝓕 =>
      μ 𝓕 = ENNReal.ofReal V

def Concl (D : D7) : letI := D.host.cmStar;
    HSpace D.host.E → ℕ → ℕ → ℕ → D.host.E → ℕ → ℕ → Prop :=
  letI := D.host.cmStar
  fun W M P Q β P' Q' =>
    (∃ x : W.V, W.hD x x = β) ∧
    ∀ x : W.V, W.hD x x = β →
      (∃ (W' : HSpace D.host.E) (ι : W'.V →ₗ[D.host.E] W.V),
        IsPerp W x W' ι ∧ IsKind W' (M - 1) P' Q') ∧
      ∀ (W' : HSpace D.host.E) (ι : W'.V →ₗ[D.host.E] W.V), IsPerp W x W' ι → W'.SigOK →
        IsKind W' (M - 1) P' Q' ∧
        ∃ V V' : ℝ, IsVol D W P Q V ∧ IsVol D W' P' Q' V' ∧
          V / V' = Formalism.HermitianLatticesTheory.massRatioRightSide D.host.E M

def VolumeRatio (D : D7) : Prop :=
  letI := D.host.cmStar
  ∀ (W : HSpace D.host.E) (M P Q : ℕ), IsKind W M P Q → 3 ≤ M →
    (1 ≤ P → Concl D W M P Q 1 (P - 1) Q) ∧ (1 ≤ Q → Concl D W M P Q (-1) P (Q - 1))

theorem IsVol.unique (D : D7) : letI := D.host.cmStar;
    ∀ (W : HSpace D.host.E) (P Q : ℕ) (V V' : ℝ), IsVol D W P Q V → IsVol D W P Q V' → V = V' := by
  intro W P Q V V' h h'
  obtain ⟨hV, ⟨μ, hμ⟩, hall⟩ := h
  obtain ⟨hV', -, hall'⟩ := h'
  obtain ⟨⟨𝓕, h𝓕⟩, h1⟩ := hall μ hμ
  have h2 := (hall' μ hμ).2 𝓕 h𝓕
  exact (ENNReal.ofReal_eq_ofReal_iff hV.le hV'.le).1 ((h1 𝓕 h𝓕).symm.trans h2)

theorem volumeComparison_of_ratio (D : D7) (h : VolumeRatio D) (ht : VolTie D) : Conclusion2 D := by
  let _ := D.host.cmStar
  have key : ∀ (W : HSpace D.host.E) (P Q : ℕ) (β : D.host.E) (P' Q' : ℕ), W.SigOK →
      (∀ τ, W.sig τ = (P, Q)) → Concl D W W.rank P Q β P' Q' →
      ∃ x : W.V, W.hT x x = β ∧
        ∃ (W' : HSpace D.host.E) (ι : W'.V →ₗ[D.host.E] W.V),
          HSpace.IsIsomEmb W' W ι ∧ LinearMap.range ι = LinearMap.ker (W.hT x) ∧ W'.SigOK ∧
          (∀ τ, W'.sig τ = (P', Q')) ∧
          D.vol W / D.vol W' = Formalism.HermitianLatticesTheory.massRatioRightSide D.host.E W.rank := by
    intro W P Q β P' Q' hs hsig hc
    obtain ⟨⟨x, hx⟩, hall⟩ := hc
    obtain ⟨⟨W', ι, hp, hk⟩, hall'⟩ := hall x hx
    obtain ⟨-, V, V', hV, hV', hr⟩ := hall' W' ι hp hk.2.1
    have e1 : V = D.vol W := IsVol.unique D W P Q _ _ hV ⟨D.vol_pos W, ht W P Q hs hsig⟩
    have e2 : V' = D.vol W' :=
      IsVol.unique D W' P' Q' _ _ hV' ⟨D.vol_pos W', ht W' P' Q' hk.2.1 hk.2.2⟩
    refine ⟨x, hx, W', ι, fun a b => hp.2.1 b a, ?_, hk.2.1, hk.2.2, by rw [← e1, ← e2, hr]⟩
    ext y
    exact hp.2.2 y
  intro W P Q hs hsig h3 s hPQ
  have hW := h W W.rank P Q ⟨rfl, hs, hsig⟩ h3
  cases s with
  | true => simpa using key W P Q 1 (P - 1) Q hs hsig (hW.1 (by simpa using hPQ))
  | false => simpa using key W P Q (-1) P (Q - 1) hs hsig (hW.2 (by simpa using hPQ))

end GlobalTheory.IndefiniteRowSideFullHecke.VolumePerpendicular
