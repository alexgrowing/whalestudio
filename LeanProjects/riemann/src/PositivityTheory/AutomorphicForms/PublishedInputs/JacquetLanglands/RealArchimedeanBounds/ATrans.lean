import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.IsHolVOf

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix NNReal

namespace UpperTheory.Esk

abbrev K0 (F : Type) [Field F] [NumberField F] : Subgroup (GF F) := Kc (F := F) fun _ => 0

def rowF {F : Type} [Field F] [NumberField F] (s : Fin 2 → F) (x : GF F) : Fin 2 → Af F := (fun i => algebraMap F (Af F) (s i)) ᵥ* x.val

abbrev sg {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (v : InfinitePlace F) : F →+* ℝ :=
  InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v)

def AMem : Prop := ∀ (F : Type) [Field F] [NumberField F],
  (∀ g : GF F, g ∈ K0 F ↔ (∀ i j, g.val i j ∈ Ohat F) ∧ ∀ i j, (g⁻¹ : GF F).val i j ∈ Ohat F) ∧
  (∀ x : Af F, x ∈ Ohat F ↔ ∀ w : Pl F, Valued.v (pLoc F w x) ≤ 1) ∧
  (∀ c : Pl F → ℕ, Kc c ≤ K0 F) ∧ (∀ (c : Pl F → ℕ) (h : GF F), h ∈ Hc c ↔ ∃ k ∈ Kc c, ∃ z, h = k * zc F z) ∧
  (∀ k ∈ K0 F, ∀ w : Pl F, Valued.v (pLoc F w ((Matrix.GeneralLinearGroup.det k : (Af F)ˣ) : Af F)) = 1 ∧
    max (Valued.v (pLoc F w (k.val 1 0))) (Valued.v (pLoc F w (k.val 1 1))) = 1) ∧
  (∀ t : F, IsIntegral ℤ t ↔ algebraMap F (Af F) t ∈ Ohat F) ∧
  (∀ g : GF F, ∃ N : ℕ, N ≠ 0 ∧ ∀ i j, (N : Af F) * g.val i j ∈ Ohat F) ∧
  ∀ u : (Af F)ˣ, (∀ w : Pl F, Valued.v (pLoc F w (u : Af F)) = 1) → zc F u ∈ K0 F ∧ ∀ t ∈ Ohat F, aff u t ∈ K0 F

def AIw : Prop := ∀ (F : Type) [Field F] [NumberField F] (x : GF F), ∃ (d a : (Af F)ˣ) (u : Af F), ∃ k ∈ K0 F, x = zc F d * aff a u * k

def AMono : Prop := ∀ (F : Type) [Field F] [NumberField F] (t t' : (Af F)ˣ),
  (∀ w : Pl F, Valued.v (pLoc F w (t : Af F)) ≤ Valued.v (pLoc F w (t' : Af F))) → absF t ≤ absF t'

def ARow : Prop := ∀ (F : Type) [Field F] [NumberField F] (s : Fin 2 → F) (x : GF F),
  (s ≠ 0 → ∃ t : (Af F)ˣ, ∃ k ∈ K0 F, ∀ i, rowF s x i = t * k.val 1 i) ∧
  ∀ t : (Af F)ˣ, ∀ k ∈ K0 F, (∀ i, rowF s x i = t * k.val 1 i) → nF s x = absF t

def ACls : Prop := ∀ (F : Type) [Field F] [NumberField F], ∃ T : Finset (Af F)ˣ, ∀ z : (Af F)ˣ, ∃ (y : Fˣ) (u : (Af F)ˣ), ∃ r ∈ T,
  (∀ w : Pl F, Valued.v (pLoc F w (u : Af F)) = 1) ∧ z = ratU F y * r * u

def AAdd : Prop := ∀ (F : Type) [Field F] [NumberField F] (t : (Af F)ˣ) (u : Af F), ∃ y : F,
  ((t⁻¹ : (Af F)ˣ) : Af F) * (u - algebraMap F (Af F) y) ∈ Ohat F

def ABnf : Prop := ∀ (F : Type) [Field F] [NumberField F], ∃ S : Finset (GF F), ∀ x : GF F, ∃ b : GL (Fin 2) F, b 1 0 = 0 ∧
  ∃ x' ∈ S, ∃ k ∈ K0 F, jF F b * x = x' * k

def AOrb : Prop := ∀ (F : Type) [Field F] [NumberField F] (c : Pl F → ℕ), {w | c w ≠ 0}.Finite → ∀ x : GF F, ∃ S : Finset (GF F),
  ∀ k ∈ K0 F, ∃ x' ∈ S, ∃ h ∈ Kc c, k * x = x' * h

def ABnfH : Prop := ∀ (F : Type) [Field F] [NumberField F] (c : Pl F → ℕ), {w | c w ≠ 0}.Finite → ∃ S : Finset (GF F), ∀ x : GF F,
  ∃ b : GL (Fin 2) F, b 1 0 = 0 ∧ ∃ x' ∈ S, ∃ h ∈ Kc c, jF F b * x = x' * h

def AMink : Prop := ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], ∃ C : ℝ, 0 < C ∧ ∀ z : InfinitePlace F → ℂ, (∀ v, (z v).im ≠ 0) →
  ∃ s : Fin 2 → F, s ≠ 0 ∧ (∀ i, IsIntegral ℤ (s i)) ∧ ∀ v, ‖(sg v (s 0) : ℂ) * z v + (sg v (s 1) : ℂ)‖ ^ 2 ≤ C * |(z v).im|

def AUnit : Prop := ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], ∃ C : ℝ, 0 < C ∧ ∀ y : InfinitePlace F → ℝ, (∀ v, y v ≠ 0) →
  ∃ u : F, u ≠ 0 ∧ IsIntegral ℤ u ∧ IsIntegral ℤ u⁻¹ ∧ ∀ v v', |sg v u * y v| ≤ C * |sg v' u * y v'|

def ATrans : Prop := ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], ∃ C : ℝ, 0 < C ∧ ∀ x : InfinitePlace F → ℝ,
  ∃ t : F, IsIntegral ℤ t ∧ ∀ v, |x v + sg v t| ≤ C

theorem dAx_of (h1 : DCount) (h2 : DHt) (h3 : DMul) (h4 : DProd) (h5 : DMink) (h6 : DNormal) (h7 : DCnt) : DAx := by
  intro F _ _ _ hd c hc χ hχ
  obtain ⟨m, hm, hχ⟩ := hχ
  have : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
  refine ⟨inferInstance, (h1 F c hc χ).1, ?_, fun h => ?_, (h2 F c hc χ).1, (h2 F c hc χ).2.1, (h2 F c hc χ).2.2, (h3 F c hc χ).1,
    (h3 F c hc χ).2, (h1 F c hc χ).2, h4 F c hc χ, h5 F c hc χ, h6 F c hc χ, h7 F c hc χ⟩
  · rw [← Fintype.one_lt_card_iff_nontrivial, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      IsTotallyReal.nrComplexPlaces_eq_zero, add_zero, ← IsTotallyReal.finrank]
    omega
  · have h0 : ‖((χ h : ℂˣ) : ℂ)‖ ^ m = 1 := by rw [← norm_pow, ← Units.val_pow_eq_pow_val, hχ h]; simp
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm.ne').1 h0

end UpperTheory.Esk
