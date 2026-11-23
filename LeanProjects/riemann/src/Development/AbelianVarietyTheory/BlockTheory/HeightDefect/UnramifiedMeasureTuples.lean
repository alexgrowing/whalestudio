import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.MinfDensity
import Formalism.LocalRingCardinality.DataDIV

noncomputable section

open Formalism.BasicNotions Formalism.L2.Theta IsDedekindDomain NumberField
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedMeasureTuples

theorem inv_lower_mem {O : Type} [CommRing O] (I : Ideal O) (r d : ℕ) (h : GL (Fin (r + d)) O)
    (hh : ∀ i k : Fin (r + d), r ≤ i.1 → k.1 < r → (h : Matrix _ _ O) i k ∈ I) :
    ∀ i k : Fin (r + d), r ≤ i.1 → k.1 < r → ((h⁻¹ : GL (Fin (r + d)) O) : Matrix _ _ O) i k ∈ I := by
  intro i k hi hk
  let π := Ideal.Quotient.mk I
  let g : GL (Fin (r + d)) (O ⧸ I) := Matrix.GeneralLinearGroup.map π h
  let b : Fin (r + d) → ℕ := fun a => if r ≤ a.1 then 1 else 0
  have hg : Matrix.BlockTriangular (g : Matrix (Fin (r + d)) (Fin (r + d)) (O ⧸ I)) b := by
    intro a c hac
    have h1 : r ≤ a.1 := by
      by_contra h1
      simp [b, h1] at hac
    have h2 : c.1 < r := by
      by_contra h2
      have h2' : r ≤ c.1 := not_lt.mp h2
      simp [b, h1, h2'] at hac
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hh a c h1 h2)
  letI : Invertible (g : Matrix (Fin (r + d)) (Fin (r + d)) (O ⧸ I)) := g.invertible
  have hinv := Matrix.blockTriangular_inv_of_blockTriangular hg
  have hb : b k < b i := by
    have : ¬ r ≤ k.1 := not_le.mpr hk
    simp [b, hi, this]
  have h0 := hinv hb
  rw [← Matrix.GeneralLinearGroup.coe_inv, ← map_inv] at h0
  exact Ideal.Quotient.eq_zero_iff_mem.mp h0

def parahoric {O : Type} [CommRing O] (I : Ideal O) (r d : ℕ) : Subgroup (GL (Fin (r + d)) O) where
  carrier := {h : GL (Fin (r + d)) O | ∀ i k : Fin (r + d), r ≤ i.1 → k.1 < r →
    (h : Matrix (Fin (r + d)) (Fin (r + d)) O) i k ∈ I}
  one_mem' := by
    intro i k hi hk
    have : i ≠ k := fun e => by subst e; omega
    simp [Matrix.one_apply_ne this]
  mul_mem' := by
    intro a c ha hc i k hi hk
    rw [Units.val_mul, Matrix.mul_apply]
    refine I.sum_mem fun l _ => ?_
    by_cases hl : l.1 < r
    · exact I.mul_mem_right _ (ha i l hi hl)
    · exact I.mul_mem_left _ (hc l k (not_lt.mp hl) hk)
  inv_mem' := fun {h} hh => inv_lower_mem I r d h hh

def localIndex {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (r d : ℕ) : ℕ :=
  (parahoric (IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)) r d).index

def indexValue (q : ℝ) (r d : ℕ) : ℝ :=
  q ^ (r * d) * (∏ i ∈ Finset.Icc 1 (r + d), (1 - (q ^ i)⁻¹)) /
    ((∏ i ∈ Finset.Icc 1 r, (1 - (q ^ i)⁻¹)) * ∏ i ∈ Finset.Icc 1 d, (1 - (q ^ i)⁻¹))

def IndexFormula : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (r d : ℕ),
    (localIndex v r d : ℝ) = indexValue (Ideal.absNorm v.asIdeal : ℝ) r d

def compAt (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (x : AE D) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v ⊗[D.host.F] D.host.E :=
  Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F v) (AlgHom.id D.host.F D.host.E) (finPart D x)

def IsUnramifiedAt (D : D7) (χ : (AE D)ˣ →* Circle) (v : HeightOneSpectrum (𝓞 D.host.F)) : Prop :=
  ∀ x : (AE D)ˣ, infPart D (x : AE D) = 1 → finPart D (x : AE D) ∈ intAE D →
    finPart D ((x⁻¹ : (AE D)ˣ) : AE D) ∈ intAE D → (∀ v', v' ≠ v → compAt D v' (x : AE D) = 1) → χ x = 1

variable {D : D7} {X : ThetaX D}

def twistChar (T : ThetaTied D X) (μ : D.what₂.Tup) (i : ℕ) : (AE D)ˣ →* Circle :=
  T.eChr (X.chrOf μ i * (X.chrOf D.what₂.mu0 i)⁻¹)

def ramPlaces (T : ThetaTied D X) (μ : D.what₂.Tup) : Set (HeightOneSpectrum (𝓞 D.host.F)) :=
  {v | ∃ i, 1 ≤ i ∧ i ≤ D.R.m ∧ ¬ IsUnramifiedAt D (twistChar T μ i) v}

def IsSplit (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) : Prop :=
  ∃ P P' : HeightOneSpectrum (𝓞 D.host.E), P ≠ P' ∧
    P.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = v.asIdeal ∧
    P'.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = v.asIdeal

def MeasFactor (T : ThetaTied D X) : Prop :=
  ∀ μ : D.what₂.Tup, ∃ S : Finset (HeightOneSpectrum (𝓞 D.host.F)), (↑S : Set _) = ramPlaces T μ ∧
    ∀ j, j ≤ D.R.m → X.mY μ j = ∏ v ∈ S, (localIndex v D.R.r (j * D.R.t) : ℝ)

def PlacesTied (T : ThetaTied D X) (XD : DivX D) : Prop :=
  ∀ μ : D.what₂.Tup, ∃ e : XD.QPl μ ≃ ramPlaces T μ, ∀ x, XD.qv μ x = Ideal.absNorm (e x).1.asIdeal

def MeasFactorAbstract (X : ThetaX D) (XD : DivX D) : Prop :=
  ∀ (μ : D.what₂.Tup) (j : ℕ), j ≤ D.R.m →
    X.mY μ j = ∏ x : XD.QPl μ, indexValue (XD.qv μ x : ℝ) D.R.r (j * D.R.t)

structure MeasTupleTied (T : ThetaTied D X) (XD : DivX D) : Prop where

  split : ∀ μ, ∀ v ∈ ramPlaces T μ, IsSplit D v

  places : PlacesTied T XD

  factor : MeasFactor T

example : indexValue 2 1 1 = 3 := by
  simp [indexValue, Finset.prod_Icc_succ_top]
  norm_num

end GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedMeasureTuples

end
