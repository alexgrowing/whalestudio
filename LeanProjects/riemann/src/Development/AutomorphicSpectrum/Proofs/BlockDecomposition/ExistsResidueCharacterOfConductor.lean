import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KvFintype
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.Jp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.Jp.ResChar

theorem local_component_additive_character_add {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ)
    (v : HeightOneSpectrum (𝓞 F)) (r s : Fv F v) :
    psiV F ψ v (r + s) = psiV F ψ v r * psiV F ψ v s := by
  have h1 : singleV F v (r + s) = singleV F v r + singleV F v s := by
    classical
    unfold singleV
    first
    | exact Subtype.ext (Pi.single_add v r s)
    | (apply Subtype.ext
       exact Pi.single_add v r s)
    | (apply Subtype.ext
       funext w
       show Pi.single v (r + s) w = Pi.single v r w + Pi.single v s w
       rw [Pi.single_add]
       rfl)
  have h2 : pairA F 0 (singleV F v (r + s)) = pairA F 0 (singleV F v r) + pairA F 0 (singleV F v s) := by
    rw [h1]
    show ((0 : Ainf F), singleV F v r + singleV F v s) = ((0 : Ainf F) + 0, singleV F v r + singleV F v s)
    rw [add_zero]
  simp only [psiV]
  rw [h2, AddChar.map_add_eq_mul]

theorem dvd_of_nonunit {R : Type*} [CommRing R] [IsDomain R] [ValuationRing R] {p x : R}
    (hp : Irreducible p) (hx : ¬ IsUnit x) : p ∣ x := by
  rcases ValuationRing.dvd_total p x with h | ⟨c, hc⟩
  · exact h
  · rcases hp.isUnit_or_isUnit hc with h | h
    · exact absurd h hx
    · exact ⟨↑h.unit⁻¹, by rw [hc, mul_assoc, IsUnit.mul_val_inv, mul_one]⟩

theorem main : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (v : Pl D), GoodPsi D ψ v → ∀ ϖ : Ov D v, Irreducible ϖ → ∀ w : (Lv D v)ˣ, (w : Lv D v) = algebraMap (Ov D v) (Lv D v) ϖ → ∃ ψ₀ : AddChar (kv D v) ℂ, ψ₀ ≠ 1 ∧ ∀ c : Ov D v, psiV D.host.F ψ v (((w⁻¹ : (Lv D v)ˣ) : Lv D v) * algebraMap (Ov D v) (Lv D v) c) = ψ₀ (IsLocalRing.residue (Ov D v) c) := by
  intro D ψ v hψ ϖ hϖ w hw
  classical
  set f : Ov D v → ℂ := fun c => psiV D.host.F ψ v (((w⁻¹ : (Lv D v)ˣ) : Lv D v) * algebraMap (Ov D v) (Lv D v) c) with hf
  have hadd : ∀ a b, f (a + b) = f a * f b := by
    intro a b
    simp only [hf, map_add, mul_add]
    exact local_component_additive_character_add ψ v _ _
  have hker : ∀ d, f (ϖ * d) = 1 := by
    intro d
    have e : ((w⁻¹ : (Lv D v)ˣ) : Lv D v) * algebraMap (Ov D v) (Lv D v) (ϖ * d) = algebraMap (Ov D v) (Lv D v) d := by
      rw [map_mul, ← hw, ← mul_assoc, Units.inv_mul, one_mul]
    simp only [hf, e]
    exact hψ.1 _ d.2
  have hwd : ∀ a b, IsLocalRing.residue (Ov D v) a = IsLocalRing.residue (Ov D v) b → f a = f b := by
    intro a b h
    have h0 : IsLocalRing.residue (Ov D v) (a - b) = 0 := by rw [map_sub, h, sub_self]
    have hm := (IsLocalRing.residue_eq_zero_iff _).mp h0
    obtain ⟨d, hd⟩ := dvd_of_nonunit hϖ (mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp hm))
    have e : a = b + ϖ * d := by rw [← hd]; ring
    rw [e, hadd, hker, mul_one]
  have hf0 : f 0 = 1 := by simpa using hker 0
  let g : kv D v → Ov D v := fun z => Classical.choose (IsLocalRing.residue_surjective z)
  have hg : ∀ z, IsLocalRing.residue (Ov D v) (g z) = z := fun z =>
    Classical.choose_spec (IsLocalRing.residue_surjective z)
  let ψ₀ : AddChar (kv D v) ℂ :=
    { toFun := fun z => f (g z)
      map_zero_eq_one' := by
        show f (g 0) = 1
        rw [hwd (g 0) 0 (by rw [hg, map_zero]), hf0]
      map_add_eq_mul' := by
        intro z z'
        show f (g (z + z')) = f (g z) * f (g z')
        rw [← hadd]
        exact hwd _ _ (by rw [hg, map_add, hg, hg]) }
  have hψ₀ : ∀ c, ψ₀ (IsLocalRing.residue (Ov D v) c) = f c := fun c => by
    show f (g _) = f c
    exact hwd _ _ (hg _)
  refine ⟨ψ₀, ?_, ?_⟩
  · obtain ⟨b, hb⟩ := hψ.2 ϖ hϖ
    intro h1
    apply hb
    have e1 : ψ₀ (IsLocalRing.residue (Ov D v) b) = 1 := by rw [h1]; exact AddChar.one_apply _
    rw [hψ₀] at e1
    have e : ((w⁻¹ : (Lv D v)ˣ) : Lv D v) * algebraMap (Ov D v) (Lv D v) b = (b : Fv D.host.F v) / (ϖ : Fv D.host.F v) := by
      rw [Units.val_inv_eq_inv_val, hw, div_eq_inv_mul]; rfl
    rw [← e]
    exact e1
  · intro c
    exact (hψ₀ c).symm

end GlobalTheory.CompanionTheory.Jp.ResChar

end
