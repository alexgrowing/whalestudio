import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsInertTop
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemLatAtIffHat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesThird
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRepsOfFiniteIndex
import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameTwistFamilySpecializationGood
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumPowersUnramifiedEtaTilde
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceIdempotentComponentsConjValuationStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBaseChangeFiniteAdeleRingEquiv
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdentityClassLatticeEqSelfDualFrameLattice
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BndMul
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.StdAtPrime

namespace GlobalTheory.StdAtPrimeLat

variable {E : Type} [Field E] [NumberField E]

theorem val_intMul_le_one (c : 𝓞 E) (z : FiniteAdeleRing (𝓞 E) E) (Q : HeightOneSpectrum (𝓞 E))
    (hz : Valued.v (z Q) ≤ 1) :
    Valued.v ((algebraMap E (FiniteAdeleRing (𝓞 E) E) (c : E) * z) Q) ≤ 1 := by
  let ev : FiniteAdeleRing (𝓞 E) E →+* Q.adicCompletion E := RestrictedProduct.evalRingHom _ Q
  have hev : ∀ x : FiniteAdeleRing (𝓞 E) E, x Q = ev x := fun _ => rfl
  rw [hev, map_mul, Valuation.map_mul, ← hev, ← hev]
  refine mul_le_one' ?_ hz
  exact (GlobalTheory.CharLocProd.val_algebraMap Q (c : E)).trans_le (Q.valuation_le_one c)

theorem val_smul_mulVec_le_one {n : ℕ} (M : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)) (m : ℕ)
    (hM : ∀ i j (Q : HeightOneSpectrum (𝓞 E)), Valued.v ((((m : FiniteAdeleRing (𝓞 E) E) * M i j)) Q) ≤ 1)
    (y : Fin n → FiniteAdeleRing (𝓞 E) E) (hy : ∀ j (Q : HeightOneSpectrum (𝓞 E)), Valued.v (y j Q) ≤ 1)
    (c : 𝓞 E) (i : Fin n) (Q : HeightOneSpectrum (𝓞 E)) :
    Valued.v ((((algebraMap E (FiniteAdeleRing (𝓞 E) E) (c : E)) * (m : FiniteAdeleRing (𝓞 E) E)) •
      (M *ᵥ y)) i Q) ≤ 1 := by
  let ev : FiniteAdeleRing (𝓞 E) E →+* Q.adicCompletion E := RestrictedProduct.evalRingHom _ Q
  have hev : ∀ x : FiniteAdeleRing (𝓞 E) E, x Q = ev x := fun _ => rfl
  have e : (((algebraMap E (FiniteAdeleRing (𝓞 E) E) (c : E)) * (m : FiniteAdeleRing (𝓞 E) E)) • (M *ᵥ y)) i =
      ∑ j, algebraMap E (FiniteAdeleRing (𝓞 E) E) (c : E) * (((m : FiniteAdeleRing (𝓞 E) E) * M i j) * y j) := by
    rw [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [e, hev, map_sum]
  refine Valuation.map_sum_le _ fun j _ => ?_
  rw [← hev]
  refine val_intMul_le_one c _ Q ?_
  rw [hev, map_mul, Valuation.map_mul, ← hev, ← hev]
  exact mul_le_one' (hM i j Q) (hy j Q)

end GlobalTheory.StdAtPrimeLat

open GlobalTheory.StdAtPrimeLat in

theorem GlobalTheory.StdAtPrimeLat.trivAt_hLat_of_bnd : ∀ (D : D7) (ι : (Af D.host.F ⊗[D.host.F] D.host.E) ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E), (∀ x : D.host.E, ι ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) = algebraMap D.host.E _ x) → (∀ y, y ∈ intAE D ↔ ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι y P) ≤ 1) → ∀ (V : HSp D), Bridge.hLat V 1 = Formalism.L2.Pj.stdLat D.host.E V.rank → ∀ (p : ℕ) (g : Bridge.Gf V), Bnd p (Matrix.GeneralLinearGroup.map ι.toRingHom g.1).1 → Bnd p (Matrix.GeneralLinearGroup.map ι.toRingHom g.1)⁻¹.1 → (⟨Bridge.hLat V g⟩ : GenLat D.host.E V.rank).TrivAt p := by
  intro D ι h1 h2 V hL p g hA hB
  obtain ⟨m₁, hm₁, hA⟩ := hA
  obtain ⟨m₂, hm₂, hB⟩ := hB
  set A := (Matrix.GeneralLinearGroup.map ι.toRingHom g.1).1 with hAdef
  set B := (Matrix.GeneralLinearGroup.map ι.toRingHom g.1)⁻¹.1 with hBdef
  have hAB : A * B = 1 := Units.mul_inv _
  have memH := fun x => GlobalTheory.ClassScalarValue.mem_hLat ι h1 h2 V hL g x
  have memS : ∀ x : Fin V.rank → D.host.E, x ∈ Formalism.L2.Pj.stdLat D.host.E V.rank ↔
      ∀ i Q, Valued.v ((fun j => algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) (x j)) i Q) ≤ 1 := by
    intro x
    rw [← hL, GlobalTheory.ClassScalarValue.mem_hLat ι h1 h2 V hL 1 x]
    simp
  have hsm : ∀ (r : 𝓞 D.host.E) (x : Fin V.rank → D.host.E),
      (fun j => algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) ((r • x) j)) =
        algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) (r : D.host.E) •
          fun j => algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) (x j) :=
    fun r x => funext fun j => map_mul _ (r : D.host.E) (x j)
  refine ⟨m₁ * m₂, Nat.Coprime.mul hm₁ hm₂, ?_, ?_⟩
  · rw [Submodule.smul_le]
    intro r hr x hx
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hr
    rw [memS, hsm]
    rw [memH] at hx
    have ex : (fun j => algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) (x j)) =
        A *ᵥ (B *ᵥ fun j => algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) (x j)) := by
      rw [Matrix.mulVec_mulVec, hAB, Matrix.one_mulVec]
    have ec : algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) ((a * ((m₁ * m₂ : ℕ) : 𝓞 D.host.E) : 𝓞 D.host.E) : D.host.E) =
        algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) ((a * (m₂ : 𝓞 D.host.E) : 𝓞 D.host.E) : D.host.E) *
          (m₁ : FiniteAdeleRing (𝓞 D.host.E) D.host.E) := by
      push_cast
      ring
    intro i Q
    rw [ec, ex]
    exact val_smul_mulVec_le_one A m₁ hA _ hx _ i Q
  · rw [Submodule.smul_le]
    intro r hr x hx
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hr
    rw [memH, hsm]
    rw [memS] at hx
    have ec : algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) ((a * ((m₁ * m₂ : ℕ) : 𝓞 D.host.E) : 𝓞 D.host.E) : D.host.E) =
        algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) ((a * (m₁ : 𝓞 D.host.E) : 𝓞 D.host.E) : D.host.E) *
          (m₂ : FiniteAdeleRing (𝓞 D.host.E) D.host.E) := by
      push_cast
      ring
    intro i Q
    rw [ec, Matrix.mulVec_smul]
    exact val_smul_mulVec_le_one B m₂ hB _ hx _ i Q
