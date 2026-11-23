import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockDetBlockTriangular
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLatticeHomApproxIntegralMatrixMod
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHomLatticeCosetIndicatorEqLatticeHomCoset
import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.CosRatApprox

open GlobalTheory.FunObj.Comparison₂

theorem infPart_idemSum_mul {D : D7} {e : AE D} {P : Finset (Formalism.L2.DIV.Pl D.host.E)} (he : IsIdemSum e P) (a : AE D) :
    infPart D (e * a) = 0 := by
  obtain ⟨e0, -, -⟩ := cpt_idemSum he
  rw [(infPart D).map_mul, e0, zero_mul]

set_option maxHeartbeats 1000000 in

theorem exists_rat_approx : ∀ {D : D7} {m n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} {Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E)} {𝔪 : Ideal (𝓞 D.host.E)}, 𝔪 ≠ ⊥ → Submodule.IsLattice D.host.E Λ → Submodule.IsLattice D.host.E Λ' → ∀ {e : AE D} {P : Finset (Formalism.L2.DIV.Pl D.host.E)}, IsIdemSum e P → ∀ z : Mx D m n, IsHalf e z → z ∈ hatMx (homLat Λ Λ') → ∃ x₁ : homLat Λ Λ', z - e • (x₁ : Matrix (Fin m) (Fin n) D.host.E).map (incA D) ∈ hatMx (𝔪 • homLat Λ Λ') := by
  intro D m n Λ Λ' 𝔪 h𝔪 hΛ hΛ' e P he z hz hzmem
  obtain ⟨β, hβ⟩ := Formalism.L2.DIV.frame_exists_alt D.host.F D.host.E n Λ hΛ
  obtain ⟨β', hβ'⟩ := Formalism.L2.DIV.frame_exists_alt D.host.F D.host.E m Λ' hΛ'
  have hz' : z ∈ hatMx ((⊤ : Ideal (𝓞 D.host.E)) • homLat Λ Λ') := by rwa [Submodule.top_smul]
  obtain ⟨-, hs⟩ := (mem_hatMx_iff hβ hβ' ⊤ z).1 hz'
  choose s _ hs' using hs
  obtain ⟨x₀, hx₀, ht⟩ := GlobalTheory.FunObj.HatFrame.homLat_approx_mod Λ Λ' β β' hβ hβ' 𝔪 h𝔪 s
  choose t htI htv using ht
  have k1 : ∀ i j, (z - e • x₀.map (incA D)) i j = e * (z i j - incA D (x₀ i j)) :=
    fun i j => by rw [mul_sub, hz i j]; rfl
  have k2 : ∀ i j, fr β' β ((z - e • x₀.map (incA D)).map (toEAf D)) i j =
      toEAf D e * (fr β' β (z.map (toEAf D)) i j - fr β' β (x₀.map (eToEAf D)) i j) := fun i j => by
    have : (z - e • x₀.map (incA D)).map (toEAf D) = toEAf D e • (z.map (toEAf D) - x₀.map (eToEAf D)) :=
      Matrix.ext fun i j => by rw [Matrix.map_apply, k1, RingHom.map_mul, RingHom.map_sub]; rfl
    rw [this, fr_smul, fr_sub]; rfl
  refine ⟨⟨x₀, hx₀⟩, ?_⟩
  show z - e • x₀.map (incA D) ∈ hatMx (𝔪 • homLat Λ Λ')
  refine (mem_hatMx_iff hβ hβ' 𝔪 _).2 ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [k1 i j]; exact infPart_idemSum_mul he _
  · let eS : {x // x ∈ Formalism.L2.Herm.intAf D.host.F D.host.E} := ⟨toEAf D e, GlobalTheory.CosToCoset.idem_mem_OA he⟩
    refine ⟨eS * -t i j, Ideal.mul_mem_left _ eS (neg_mem (htI i j)), ?_⟩
    rw [k2, ← hs' i j]
    show toEAf D e * -((t i j : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) = _
    rw [htv i j, neg_sub]

end GlobalTheory.CosRatApprox
