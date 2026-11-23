import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadingsExistRow

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace
open GlobalTheory.GalLift

namespace GlobalTheory.GalLift

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem ringHom_eq_on_adjoin_simple {E : Type} [Field E] [Algebra ℚ E] (f g : E →+* ℂ) (s : E) (h : f s = g s) (x : E)
    (hx : x ∈ IntermediateField.adjoin ℚ ({s} : Set E)) : f x = g x := by
  induction hx using IntermediateField.adjoin_induction with
  | mem y hy => rw [Set.mem_singleton_iff.1 hy]; exact h
  | algebraMap q => simp
  | add a b _ _ ha hb => rw [map_add, map_add, ha, hb]
  | inv a _ ha => rw [map_inv₀, map_inv₀, ha]
  | mul a b _ _ ha hb => rw [map_mul, map_mul, ha, hb]

theorem overK_iff_sqrt {D : D7} (σ : D.what₂.LL →+* ℂ) :
    OverK σ ↔ σ (D.embE D.host.sqrtMinusD) = D.what₂.embLL (D.embE D.host.sqrtMinusD) :=
  ⟨fun h => h _ (IntermediateField.mem_adjoin_simple_self ℚ D.host.sqrtMinusD),
    fun h x hx => ringHom_eq_on_adjoin_simple (σ.comp D.embE) (D.what₂.embLL.comp D.embE) D.host.sqrtMinusD h x hx⟩

theorem overK_iff_good_of_pins {D : D7} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (ha : AlgTie T) (hp : T.Q.Pins)
    (σ : D.what₂.LL →+* ℂ) : OverK σ ↔ GoodEmb T.Q.c (res T σ) := by
  have e0 := res_embLL T ha hp.2.2.1
  have h1 : D.what₂.embLL (D.embE D.host.sqrtMinusD) = T.Q.H.rt0 :=
    (RingHom.congr_fun D.embE_φ₀ D.host.sqrtMinusD).trans hp.1.2.2.1.symm
  have h2 : GoodEmb T.Q.c (res T D.what₂.embLL) := e0 ▸ T.toCore.good_σ₀
  have hx : D.embE D.host.sqrtMinusD = algebraMap T.Q.c.F D.what₂.LL
      (IntermediateField.inclusion T.Q.c.le (ReciprocityTheory.ChartRestriction.G.Geo.Tor.baseKA T.Q.l).ρ) :=
    D.what₂.embLL.injective (h1.trans (Eq.symm h2))
  refine (overK_iff_sqrt σ).trans ⟨fun h => ?_, fun h => ?_⟩
  · exact (congrArg σ hx).symm.trans (h.trans h1)
  · exact (congrArg σ hx).trans (Eq.trans h h1.symm)

theorem overK_iff_good : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κw : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.Char F → ∀ (fw : FWTie T R κw v₀) (i : Fin D.R.m), ∀ (σ : D.what₂.LL →+* ℂ), OverK σ ↔ GoodEmb T.Q.c (res T σ) :=
  fun T _ _ _ _ _ _ fw _ σ => overK_iff_good_of_pins T fw.alg_eq fw.laws.pins σ

end GlobalTheory.GalLift
