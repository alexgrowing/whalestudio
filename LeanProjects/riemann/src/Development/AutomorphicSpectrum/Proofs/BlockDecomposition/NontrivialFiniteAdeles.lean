import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.GlobalCharacterOfInputs

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
open GlobalTheory.BCT PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.G8
open scoped Classical

namespace GlobalTheory.CompanionTheory.TwistCent

theorem map_thetaR {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (c : R →+* R) (c' : S →+* S)
    (h : ∀ x, f (c x) = c' (f x)) (n : ℕ) (g : GL (Fin n) R) :
    GeneralLinearGroup.map f (thetaR c n g) = thetaR c' n (GeneralLinearGroup.map f g) := by
  apply Units.ext
  ext i j
  rw [GeneralLinearGroup.map_apply, thetaR_val, thetaR_val, ← map_inv]
  simp only [Matrix.transpose_apply, Matrix.map_apply, GeneralLinearGroup.map_apply, h]

theorem map_phiU {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (n : ℕ) :
    GeneralLinearGroup.map f (PhiU n R) = PhiU n S := by
  apply Units.ext
  ext i j
  simp only [GeneralLinearGroup.map_apply, phiU_val, GlobalTheory.Tw.Phi, Matrix.of_apply]
  split_ifs <;> simp

theorem map_thetaGL {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (c : R →+* R) (c' : S →+* S)
    (h : ∀ x, f (c x) = c' (f x)) (n : ℕ) (g : GL (Fin n) R) :
    GeneralLinearGroup.map f (thetaGL n c g) = thetaGL n c' (GeneralLinearGroup.map f g) := by
  rw [thetaGL_eq, thetaGL_eq, map_mul, map_mul, map_inv, map_phiU, map_thetaR f c c' h]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem thF_ratF (g : GL (Fin n) E) : thF E n (ratF E n g) = ratF E n (thE E n g) :=
  (map_thetaGL (algebraMap E (Af E)) _ _
    (fun x => (conjFin_algebraMap (IsCMField.complexConj E).toRingEquiv x).symm) n g).symm

theorem nontrivial_finiteAdeles : Nontrivial (Af E) := by
  obtain ⟨m₀, hm₀⟩ := Ideal.exists_maximal (𝓞 E)
  let v₀ : HeightOneSpectrum (𝓞 E) :=
    ⟨m₀, hm₀.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hm₀ (RingOfIntegers.not_isField E)⟩
  exact ⟨⟨0, 1, fun h => zero_ne_one (congrArg (fun x : Af E => x v₀) h)⟩⟩

theorem ratF_injective : Function.Injective (ratF E n) := by
  haveI : Nontrivial (Af E) := nontrivial_finiteAdeles
  intro g h e
  apply Units.ext
  ext i j
  have := congrArg (fun x : GL (Fin n) (Af E) => x.val i j) e
  exact (algebraMap E (Af E)).injective this

theorem pFin_ratGL (g : GL (Fin n) E) : GeneralLinearGroup.map (pFin E) (ratGL E n g) = ratF E n g := by
  apply Units.ext
  ext i j
  rfl

theorem cV_ratGL (v : InfinitePlace E) (g : GL (Fin n) E) :
    GeneralLinearGroup.map (cV v) (ratGL E n g) = GeneralLinearGroup.map v.embedding g := by
  apply Units.ext
  ext i j
  exact pInf_algebraMap (g.val i j) v

theorem mem_twCent_iff {u : GL (Fin n) E} (hu : IsTransl u) (g d : GL (Fin n) E) :
    g ∈ PositivityTheory.Rg.Tf.Loc.twCent (thetaE E n) d ↔ g * (d * u⁻¹) = d * u⁻¹ * thE E n g := by
  rw [PositivityTheory.Rg.Tf.Loc.mem_twCent, hu.1 g]
  constructor
  · intro h
    have h' : g * d = d * thetaE E n g := by
      calc g * d = g * (g⁻¹ * d * thetaE E n g) := by rw [h]
        _ = d * thetaE E n g := by group
    calc g * (d * u⁻¹) = g * d * u⁻¹ := by group
      _ = d * thetaE E n g * u⁻¹ := by rw [h']
      _ = d * u⁻¹ * (u * thetaE E n g * u⁻¹) := by group
  · intro h
    have h' : g * d = d * thetaE E n g := by
      calc g * d = g * (d * u⁻¹) * u := by group
        _ = d * u⁻¹ * (u * thetaE E n g * u⁻¹) * u := by rw [h]
        _ = d * thetaE E n g := by group
    calc g⁻¹ * d * thetaE E n g = g⁻¹ * (d * thetaE E n g) := by group
      _ = g⁻¹ * (g * d) := by rw [h']
      _ = d := by group

theorem mem_twCent_iff_ratF {u : GL (Fin n) E} (hu : IsTransl u) (g d : GL (Fin n) E) :
    g ∈ PositivityTheory.Rg.Tf.Loc.twCent (thetaE E n) d ↔
      ratF E n g * ratF E n (d * u⁻¹) = ratF E n (d * u⁻¹) * thF E n (ratF E n g) := by
  rw [mem_twCent_iff hu, thF_ratF, ← map_mul, ← map_mul]
  exact ratF_injective.eq_iff.symm

theorem map_mem_twCent (v : InfinitePlace E) {g d : GL (Fin n) E}
    (h : g ∈ PositivityTheory.Rg.Tf.Loc.twCent (thetaE E n) d) :
    GeneralLinearGroup.map v.embedding g ∈
      PositivityTheory.Rg.Tf.Loc.twCent (thetaR (starRingEnd ℂ) n) (GeneralLinearGroup.map v.embedding d) := by
  have h' : g⁻¹ * d * thetaE E n g = d := h
  rw [PositivityTheory.Rg.Tf.Loc.mem_twCent]
  rw [← map_thetaR v.embedding (conjE E) (starRingEnd ℂ)
    (fun x => IsCMField.complexEmbedding_complexConj E v.embedding x) n g, ← map_inv, ← map_mul, ← map_mul]
  exact congrArg _ h'

theorem centEq : CentEq := by
  intro E _ _ _ a b u₁ u₂ h₁ h₂ d₁ d₂
  refine ⟨fun y => ⟨?_, ?_⟩, ?_⟩
  · rintro ⟨⟨⟨g₁, g₂⟩, rfl⟩, hc⟩
    have hc' := Prod.ext_iff.1 hc
    refine ⟨(ratGL E a g₁, ratGL E b g₂), ?_, ?_⟩
    · exact ⟨⟨g₁, (mem_twCent_iff_ratF h₁ g₁ d₁).2 hc'.1, rfl⟩, ⟨g₂, (mem_twCent_iff_ratF h₂ g₂ d₂).2 hc'.2, rfl⟩⟩
    · exact Prod.ext (pFin_ratGL g₁) (pFin_ratGL g₂)
  · rintro ⟨⟨γ₁, γ₂⟩, ⟨⟨g₁, hg₁, rfl⟩, ⟨g₂, hg₂, rfl⟩⟩, rfl⟩
    have e : (comps (ratGL E a g₁, ratGL E b g₂)).2 = (ratF E a g₁, ratF E b g₂) :=
      Prod.ext (pFin_ratGL g₁) (pFin_ratGL g₂)
    rw [e]
    exact ⟨⟨(g₁, g₂), rfl⟩, Prod.ext ((mem_twCent_iff_ratF h₁ g₁ d₁).1 hg₁) ((mem_twCent_iff_ratF h₂ g₂ d₂).1 hg₂)⟩
  · rintro ⟨γ₁, γ₂⟩ ⟨⟨g₁, hg₁, rfl⟩, ⟨g₂, hg₂, rfl⟩⟩
    refine ⟨fun h => ?_, fun v => ?_⟩
    · have e : (comps (ratGL E a g₁, ratGL E b g₂)).2 = (ratF E a g₁, ratF E b g₂) :=
        Prod.ext (pFin_ratGL g₁) (pFin_ratGL g₂)
      rw [e] at h
      have e₁ : g₁ = 1 := ratF_injective ((congrArg Prod.fst h).trans (map_one _).symm)
      have e₂ : g₂ = 1 := ratF_injective ((congrArg Prod.snd h).trans (map_one _).symm)
      subst e₁ e₂
      exact Prod.ext (map_one _) (map_one _)
    · constructor
      · show GeneralLinearGroup.map (cV v) (ratGL E a g₁) ∈ _
        rw [cV_ratGL]
        exact map_mem_twCent v hg₁
      · show GeneralLinearGroup.map (cV v) (ratGL E b g₂) ∈ _
        rw [cV_ratGL]
        exact map_mem_twCent v hg₂

end GlobalTheory.CompanionTheory.TwistCent

end
