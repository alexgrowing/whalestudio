import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsBaseClassLevelAdapted
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.AnChartAsm
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HermitianFormAtFrameLaws
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeSelfDualSemicharacterIndex

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict

theorem AnFib.exists_anPt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (x : Frame X.Ψ r) (L : Lt E r) (y : FrPt Xo c ℂ) (A : AnFib X bas idx e x L y), IsSympl X bas → x ∈ X.dom → SelfD X L → ∃ Φ : AnVal.AnPt y g (fun j => rowType X (idx j)) e, (∀ z, Φ.e z = A.ex z) ∧ Φ.fr = A.fr ∧ (∀ z, z ∈ Φ.lat ↔ ∃ v ∈ L, z = pv X idx x v) ∧ (∀ z w, hermForm Φ.Hm z w = hx X bas idx x z w) ∧ (∀ v ∈ L, Φ.χ (pv X idx x v) = A.χ v) ∧ (∀ (k : ℤ) F θ, Φ.toAnFr.Rd k F θ ↔ A.Reads k F θ) ∧ ∀ (k : ℕ) a θ, AnVal.fock Φ.Hm (k : ℤ) a θ = Dict.fock X bas idx x k a θ := by
  intro E _ _ _ H Dw l Xo c _ r g X bas idx e x L y A hs hx hL
  obtain ⟨-, -, -, hadj, -, hinj, hsp, -⟩ := hx_laws E r X g bas idx 0 hs Even.zero x hx
  let lat : AddSubgroup (Fin g → ℂ) :=
    { carrier := {z | ∃ v ∈ L, z = pv X idx x v}
      add_mem' := by
        rintro _ _ ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩
        exact ⟨u + v, add_mem hu hv, by rw [pv, pv, pv, per_add]; rfl⟩
      zero_mem' := ⟨0, zero_mem _, by rw [pv, per_zero]; rfl⟩
      neg_mem' := by
        rintro _ ⟨u, hu, rfl⟩
        exact ⟨-u, neg_mem hu, by rw [pv, pv, per_neg]; rfl⟩ }
  have hχ (v) : Function.invFun (pv X idx x) (pv X idx x v) = v := Function.leftInverse_invFun hinj v
  let Φ : AnVal.AnPt y g (fun j => rowType X (idx j)) e :=
    { e := A.ex
      lat := lat
      span := by
        rw [← (hsp L (SW.TensLat.span_of_selfD X hL)).1]
        congr 1
        ext z
        exact ⟨fun ⟨v, hv, h⟩ => ⟨v, hv, h.symm⟩, fun ⟨v, hv, h⟩ => ⟨v, hv, h.symm⟩⟩
      e_add := A.ex_add
      e_onto := A.ex_onto
      e_ker := A.ex_ker
      hol := fun U f => by
        obtain ⟨h1, h2⟩ := A.hol U f
        simp only [Set.mem_univ, true_and] at h1 h2
        exact ⟨h1, h2⟩
      Hm := ThFr.Hm X bas idx x
      herm := Hm_isHermitian idx hs hx
      χ := fun z => A.χ (Function.invFun (pv X idx x) z)
      fr := A.fr
      fr_hol := A.fr_hol
      fr_ne := A.fr_ne
      fr_g := A.fr_g
      fr_0 := A.fr_0
      χ_norm := by
        rintro _ ⟨v, hv, rfl⟩
        rw [hχ]
        exact A.χ_norm v hv
      fr_per := by
        rintro _ ⟨v, hv, rfl⟩ j z hz
        rw [hχ, ← hx_eq_hermForm, ← hx_eq_hermForm]
        exact A.fr_per v hv j z hz
      lin := A.ex_lin
      adj := fun a z w => by
        rw [← hx_eq_hermForm, ← hx_eq_hermForm]
        have hb : cc (a : E) = ((H.bar a : 𝓞 E) : E) := (H.bar_eq a).symm
        have h := hadj (a : E) z w
        rw [hb] at h
        exact h
      der := A.der }
  refine ⟨Φ, fun _ => rfl, rfl, fun _ => Iff.rfl, fun z w => (hx_eq_hermForm idx x z w).symm,
    fun v _ => congrArg A.χ (hχ v), fun _ _ _ => Iff.rfl, fun k a θ => ?_⟩
  funext z
  change cexp _ * θ (z + a) = cexp _ * θ (z + a)
  congr 2
  rw [hx_eq_hermForm]
  change _ - _ * _ * hermForm (ThFr.Hm X bas idx x) a a / 2 = _
  change -(_ * _ * hermForm (ThFr.Hm X bas idx x) z a) - _ = _
  simp only [hermForm, add_dotProduct, smul_dotProduct, smul_eq_mul, Int.cast_natCast]
  ring

end GlobalTheory.Dict
