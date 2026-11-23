import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Ker.LatTens

noncomputable def gen {D : D7} (S T : HSp D) (α : Af D.host.F) :
    Matrix (Fin S.rank) (Fin T.rank) D.host.E →+ WO S T :=
  AddMonoidHom.mk' (fun y => Matrix.of fun a k => (pairA D.host.F 0 α) ⊗ₜ[D.host.F] y k a)
    fun y y' => Matrix.ext fun a k => TensorProduct.tmul_add _ (y k a) (y' k a)

def vmv {E : Type} [Field E] {n r : ℕ} (v : Fin n → E) : (Fin r → E) →+ Matrix (Fin n) (Fin r) E :=
  AddMonoidHom.mk' (fun u => vecMulVec v u)
    fun u u' => Matrix.ext fun k a => mul_add (v k) (u a) (u' a)

theorem gen_eq {D : D7} (S T : HSp D) (hS : S.gram = 1) (α : Af D.host.F) (a : D.host.E)
    (s : Fin S.rank → D.host.E) (t : Fin T.rank → D.host.E) :
    (Matrix.of fun i j => (pairA D.host.F 0 α) ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j) : WO S T)
      = gen S T α (vecMulVec (star s) (a • t)) := by
  refine Matrix.ext fun i j => ?_
  simp only [gen, AddMonoidHom.mk'_apply, Matrix.of_apply]
  congr 1
  rw [hS]
  simp only [Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, vecMulVec_apply, Pi.star_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem latO_eq_hatA : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ (LS Λ : Lt D.host.E S.rank) (LT L : Lt D.host.E T.rank), (∀ v, v ∈ Λ ↔ star v ∈ LS) → IsAA L LT → latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (fun _ => True) = hatA S T (tens Λ L) := by
  intro D S T C LS Λ LT L hΛ hL
  have hS : S.gram = 1 := C.m.gS

  have hmem : ∀ α : Af D.host.F, α ∈ intAf D.host.F → ∀ a : D.host.E, a ∈ D.host.AA →
      ∀ v : Fin S.rank → D.host.E, v ∈ Λ → ∀ t : Fin T.rank → D.host.E, t ∈ LT →
      gen S T α (vecMulVec v (a • t)) ∈ latO S T (LS : Set (Fin S.rank → D.host.E))
        (LT : Set (Fin T.rank → D.host.E)) (fun _ => True) := by
    intro α hα a ha v hv t ht
    unfold latO
    apply AddSubgroup.subset_closure
    refine ⟨α, hα, fun _ h => absurd trivial h, a, ha, star v, (hΛ v).1 hv, t, ht, ?_⟩
    rw [gen_eq S T hS α a (star v) t, star_star]
  apply le_antisymm
  · unfold latO
    rw [AddSubgroup.closure_le]
    rintro w ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩
    rw [gen_eq S T hS α a s t]
    unfold hatA
    apply AddSubgroup.subset_closure
    have hsΛ : star s ∈ Λ := (hΛ (star s)).2 (by rw [star_star]; exact hs)
    have htL : a • t ∈ L := (hL (a • t)).2 (AddSubgroup.subset_closure ⟨a, ha, t, ht, rfl⟩)
    exact ⟨α, hα, vecMulVec (star s) (a • t),
      AddSubgroup.subset_closure ⟨star s, hsΛ, a • t, htL, rfl⟩, rfl⟩
  · unfold hatA
    rw [AddSubgroup.closure_le]
    rintro w ⟨α, hα, y, hy, rfl⟩

    have hT : tens Λ L ≤ (latO S T (LS : Set (Fin S.rank → D.host.E))
        (LT : Set (Fin T.rank → D.host.E)) (fun _ => True)).comap (gen S T α) := by
      unfold tens
      rw [AddSubgroup.closure_le]
      rintro _ ⟨v, hv, u, hu, rfl⟩
      have hL' : AddSubgroup.closure {u | ∃ a : D.host.E, a ∈ D.host.AA ∧ ∃ t ∈ LT, u = a • t} ≤
          (latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
            (fun _ => True)).comap ((gen S T α).comp (vmv v)) := by
        rw [AddSubgroup.closure_le]
        rintro _ ⟨a, ha, t, ht, rfl⟩
        exact hmem α hα a ha v hv t ht
      exact hL' ((hL u).1 hu)
    exact hT hy

end GlobalTheory.Ker.LatTens
