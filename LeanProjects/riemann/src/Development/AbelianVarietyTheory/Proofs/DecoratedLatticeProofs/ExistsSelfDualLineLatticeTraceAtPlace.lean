import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormOneAtOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

noncomputable section

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000

open Formalism.MainNotions.StandardLattice

namespace GlobalTheory.Core.Mi.LineSD

variable {D : D7}

theorem mul_mem_intAt {v : GlobalTheory.FinPl.Pl D} {a b : AE D} (ha : a ∈ intAt D (· = v)) (hb : b ∈ intAt D (· = v)) :
    a * b ∈ intAt D (· = v) :=
  ⟨Ideal.mul_mem_right _ _ ha.1, by rw [map_mul]; exact GlobalTheory.FinPl.FrameLat.mul_mem_intAE ha.2 hb.2⟩

theorem one_mem_intAf : (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ∈ intAf D.host.F := fun w => by
  rw [map_one]; exact one_mem _

theorem incA_mem_intAE (x : 𝓞 D.host.E) : finPart D (incA D (x : D.host.E)) ∈ intAE D :=
  AddSubgroup.subset_closure ⟨1, one_mem_intAf, x, rfl⟩

theorem mul_incA_mem {v : GlobalTheory.FinPl.Pl D} {a : AE D} (ha : a ∈ intAt D (· = v)) (x : 𝓞 D.host.E) :
    a * incA D (x : D.host.E) ∈ intAt D (· = v) :=
  ⟨Ideal.mul_mem_right _ _ ha.1, by
    rw [map_mul]; exact GlobalTheory.FinPl.FrameLat.mul_mem_intAE ha.2 (incA_mem_intAE x)⟩

theorem cA_mem_intAt {v : GlobalTheory.FinPl.Pl D} {a : AE D} (ha : a ∈ intAt D (· = v)) : cA D a ∈ intAt D (· = v) := by
  refine ⟨?_, (GlobalTheory.FinPl.FrameLat.cA_int_iff a).2 ha.2⟩
  have h := (GlobalTheory.FinPlLoc.mem_idAt_iff _ a).1 ha.1
  rw [GlobalTheory.FinPlLoc.mem_idAt_iff, ← GlobalTheory.FinPlLoc.cA_idem, ← map_mul, h]

theorem unit_at {v : GlobalTheory.FinPl.Pl D} {T : ℕ} (hT : (T : 𝓞 D.host.F) ∉ v.asIdeal) :
    GlobalTheory.FinPlLoc.idem D (· = v) * incA D ((T : D.host.E)⁻¹) ∈ intAt D (· = v) := by
  refine ⟨Ideal.mul_mem_right _ _ (GlobalTheory.FinPlLoc.idem_mem_idAt _), ?_⟩
  have hc : ((T : D.host.E)⁻¹) = algebraMap D.host.F D.host.E ((T : D.host.F)⁻¹) := by simp
  have e : finPart D (GlobalTheory.FinPlLoc.idem D (· = v) * incA D ((T : D.host.E)⁻¹)) =
      ((T : D.host.F)⁻¹ • GlobalTheory.FinPlLoc.ePl D (· = v)) ⊗ₜ[D.host.F] (1 : D.host.E) := by
    rw [map_mul, GlobalTheory.FinPlLoc.idem, GlobalTheory.FinPlLoc.finPart_pair]
    show (GlobalTheory.FinPlLoc.ePl D (· = v) ⊗ₜ[D.host.F] (1 : D.host.E)) *
      ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] ((T : D.host.E)⁻¹)) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, hc, Algebra.algebraMap_eq_smul_one,
      TensorProduct.tmul_smul, TensorProduct.smul_tmul']
  rw [e]
  refine AddSubgroup.subset_closure ⟨(T : D.host.F)⁻¹ • GlobalTheory.FinPlLoc.ePl D (· = v), fun w => ?_, (1 : 𝓞 D.host.E), ?_⟩
  swap
  · rfl
  rw [Algebra.smul_def, map_mul, AlgHom.commutes, GlobalTheory.FinPlLoc.evalV_ePl]
  by_cases hw : w = v
  · subst hw
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, if_pos rfl, mul_one]
    show Valued.v (((T : D.host.F)⁻¹ : D.host.F) : w.adicCompletion D.host.F) ≤ 1
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', map_inv₀]
    have h1 : w.valuation D.host.F (T : D.host.F) = 1 := by
      have := HeightOneSpectrum.valuation_of_algebraMap (K := D.host.F) w (T : 𝓞 D.host.F)
      rw [HeightOneSpectrum.intValuation_eq_one_iff.2 hT] at this
      simpa using this
    rw [h1, inv_one]
  · rw [if_neg hw, mul_zero]; exact zero_mem _

def traceLine {S A L : HSp D} (o : OrthDec S A L) (M' : Lat S) (v : GlobalTheory.FinPl.Pl D) :
    AddSubgroup (Fin L.rank → AE D) where
  carrier := {l | (∀ i, l i ∈ idAt D (· = v)) ∧ o.jB *ᵥ l ∈ latV S M' (· = v)}
  add_mem' := fun {a b} ha hb => ⟨fun i => add_mem (ha.1 i) (hb.1 i), by
    show o.jB *ᵥ (a + b) ∈ _
    rw [mulVec_add]; exact add_mem ha.2 hb.2⟩
  zero_mem' := ⟨fun i => zero_mem _, by
    show o.jB *ᵥ 0 ∈ _
    rw [mulVec_zero]; exact zero_mem _⟩
  neg_mem' := fun {a} ha => ⟨fun i => neg_mem (ha.1 i), by
    show o.jB *ᵥ (-a) ∈ _
    rw [mulVec_neg]; exact neg_mem ha.2⟩

theorem exists_isSDAt_line : ∀ (D : D7) (S A L : HSp D) (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) (M' : Lat S) (μ : D.host.E) (T : ℕ) (v : GlobalTheory.FinPl.Pl D), IsLineVec L ζ → μ ≠ 0 → LineAt (vecB o ζ) μ M' v → star ζ ⬝ᵥ L.gram *ᵥ ζ = -(μ * star μ * (T : D.host.E)) → (T : 𝓞 D.host.F) ∉ v.asIdeal → ∃ Λ' : AddSubgroup (Fin L.rank → AE D), GlobalTheory.IwaPlace.IsSDAt L v Λ' ∧ ∀ l : Fin L.rank → AE D, (∀ i, l i ∈ idAt D (· = v)) → (l ∈ Λ' ↔ o.jB *ᵥ l ∈ latV S M' (· = v)) := by
  intro D S A L o ζ M' μ T v hζ hμ hline hgram hT
  obtain ⟨hr, hne⟩ := hζ
  obtain ⟨i₀, hall⟩ : ∃ i₀ : Fin L.rank, ∀ i, i = i₀ :=
    ⟨⟨0, by omega⟩, fun i => Fin.ext (by have := i.2; simp only; omega)⟩
  have hs : ∀ {M : Type} [AddCommMonoid M] (f : Fin L.rank → M), ∑ i, f i = f i₀ := fun f =>
    Fintype.sum_eq_single _ fun i hi => absurd (hall i) hi
  have hdot : star ζ ⬝ᵥ L.gram *ᵥ ζ = star (ζ i₀) * L.gram i₀ i₀ * ζ i₀ := by
    simp only [dotProduct, mulVec, hs, Pi.star_apply]; ring
  have hz0 : ζ i₀ ≠ 0 := by
    intro h; apply hne; rw [hdot, h, mul_zero]
  have hsz : star (ζ i₀) ≠ 0 := star_ne_zero.2 hz0
  have hT0 : (T : D.host.E) ≠ 0 := by
    have : T ≠ 0 := by rintro rfl; exact hT (by simp)
    exact_mod_cast this
  have hq : star (ζ i₀) * L.gram i₀ i₀ * ζ i₀ = -(μ * star μ * (T : D.host.E)) := by rw [← hdot, hgram]
  have hjB : ∀ l : Fin L.rank → AE D, o.jB *ᵥ l = (l i₀ * incA D (ζ i₀)⁻¹) • ratV (vecB o ζ) := by
    intro l; funext r
    simp only [OrthDec.jB, rat, vecB, ratV, mulVec, dotProduct, Matrix.map_apply, Pi.smul_apply, smul_eq_mul, hs]
    rw [map_mul]
    have h1 : incA D (ζ i₀)⁻¹ * incA D (ζ i₀) = 1 := by rw [← map_mul, inv_mul_cancel₀ hz0, map_one]
    linear_combination (-(incA D (o.iB r i₀) * l i₀)) * h1
  have hK : ∀ l : Fin L.rank → AE D, (∀ i, l i ∈ idAt D (· = v)) →
      (o.jB *ᵥ l ∈ latV S M' (· = v) ↔ l i₀ * incA D (μ / ζ i₀) ∈ intAt D (· = v)) := by
    intro l hl
    rw [hjB, hline _ (Ideal.mul_mem_right _ _ (hl i₀))]
    have : incA D μ * (l i₀ * incA D (ζ i₀)⁻¹) = l i₀ * incA D (μ / ζ i₀) := by
      rw [div_eq_mul_inv, map_mul]; ring
    rw [this]
  let Λ' := traceLine o M' v
  have hmem : ∀ l, l ∈ Λ' ↔ (∀ i, l i ∈ idAt D (· = v)) ∧ o.jB *ᵥ l ∈ latV S M' (· = v) := fun l => Iff.rfl
  have hΛ : ∀ x, x ∈ Λ' ↔ (∀ i, x i ∈ idAt D (· = v)) ∧ x i₀ * incA D (μ / ζ i₀) ∈ intAt D (· = v) :=
    fun x => (hmem x).trans (and_congr_right fun hx => hK x hx)
  refine ⟨Λ', ⟨fun y hy => hy.1, ?_, ?_⟩, fun l hl => by rw [hmem]; exact ⟨fun h => h.2, fun h => ⟨hl, h⟩⟩⟩
  · obtain ⟨y, hy0, hyint⟩ :=
      exists_integral_multiples ℤ ℚ (L := D.host.E) {μ / ζ i₀}
    replace hyint := hyint _ (Finset.mem_singleton_self _)
    have hn : IsIntegral ℤ ((y.natAbs : D.host.E) * (μ / ζ i₀)) := by
      rcases Int.natAbs_eq y with h | h
      · rw [h, zsmul_eq_mul, Int.cast_natCast] at hyint; exact hyint
      · rw [h, neg_smul, zsmul_eq_mul, Int.cast_natCast] at hyint; simpa using hyint.neg
    refine ⟨y.natAbs, Int.natAbs_pos.2 hy0, fun x hx => ?_⟩
    refine (hΛ _).2 ⟨fun i => ?_, ?_⟩
    · rw [Pi.smul_apply, smul_eq_mul]; exact Ideal.mul_mem_left _ _ (hx i).1
    · have : ((y.natAbs : AE D) • x) i₀ * incA D (μ / ζ i₀) =
          x i₀ * incA D ((y.natAbs : D.host.E) * (μ / ζ i₀)) := by
        rw [Pi.smul_apply, smul_eq_mul, map_mul, map_natCast]; ring
      rw [this]; exact mul_incA_mem (hx i₀) ⟨_, hn⟩
  · intro y hy
    have hherm : ∀ x : Fin L.rank → AE D, GlobalTheory.IwaPlace.hermAt L y x = cA D (x i₀) * incA D (L.gram i₀ i₀) * y i₀ := by
      intro x; simp only [GlobalTheory.IwaPlace.hermAt, hs, gA, rat, Matrix.map_apply]
    have hG : L.gram i₀ i₀ = star (μ / ζ i₀) * (-(T : D.host.E)) * (μ / ζ i₀) := by
      have h1 : L.gram i₀ i₀ = -(μ * star μ * (T : D.host.E)) / (star (ζ i₀) * ζ i₀) := by
        rw [eq_div_iff (mul_ne_zero hsz hz0)]; linear_combination hq
      rw [h1, div_eq_mul_inv μ, star_mul', star_inv₀]
      field_simp
    have hid : ∀ a : AE D, cA D a * incA D (L.gram i₀ i₀) * y i₀ =
        cA D (a * incA D (μ / ζ i₀)) * (y i₀ * incA D (μ / ζ i₀)) * incA D (-(T : D.host.E)) := by
      intro a
      rw [hG]; simp only [map_mul, GlobalTheory.FinPl.FrameLat.cA_incA]; ring
    have hay : y i₀ * incA D (μ / ζ i₀) ∈ idAt D (· = v) := Ideal.mul_mem_right _ _ (hy i₀)
    have he : GlobalTheory.FinPlLoc.idem D (· = v) * incA D (ζ i₀ / μ) * incA D (μ / ζ i₀) = GlobalTheory.FinPlLoc.idem D (· = v) := by
      rw [mul_assoc, ← map_mul, show ζ i₀ / μ * (μ / ζ i₀) = 1 by field_simp, map_one, mul_one]
    constructor
    · intro hyΛ x hx
      obtain ⟨-, hyK⟩ := (hΛ y).1 hyΛ
      obtain ⟨-, hxK⟩ := (hΛ x).1 hx
      rw [hherm, hid]
      have := mul_incA_mem (mul_mem_intAt (cA_mem_intAt hxK) hyK) (-(T : 𝓞 D.host.E))
      simpa using this
    · intro h
      refine (hΛ y).2 ⟨hy, ?_⟩
      have hx₁ : (fun _ => GlobalTheory.FinPlLoc.idem D (· = v) * incA D (ζ i₀ / μ) : Fin L.rank → AE D) ∈ Λ' := by
        refine (hΛ _).2 ⟨fun i => Ideal.mul_mem_right _ _ (GlobalTheory.FinPlLoc.idem_mem_idAt _), ?_⟩
        show GlobalTheory.FinPlLoc.idem D (· = v) * incA D (ζ i₀ / μ) * incA D (μ / ζ i₀) ∈ _
        rw [he]; exact GlobalTheory.FinPlLoc.idem_mem_intAt _
      have h1 := h _ hx₁
      rw [hherm, hid] at h1
      rw [he, GlobalTheory.FinPlLoc.cA_idem, (GlobalTheory.FinPlLoc.mem_idAt_iff _ _).1 hay] at h1
      have h2 := mul_incA_mem (mul_mem_intAt h1 (unit_at hT)) (-1 : 𝓞 D.host.E)
      have hT' : incA D (-(T : D.host.E)) * incA D ((T : D.host.E)⁻¹) * incA D (((-1 : 𝓞 D.host.E)) : D.host.E) = 1 := by
        rw [← map_mul, ← map_mul]; push_cast; rw [neg_mul, mul_inv_cancel₀ hT0]; simp
      have hay' := (GlobalTheory.FinPlLoc.mem_idAt_iff _ _).1 hay
      have e2 : y i₀ * incA D (μ / ζ i₀) * incA D (-(T : D.host.E)) *
          (GlobalTheory.FinPlLoc.idem D (· = v) * incA D ((T : D.host.E)⁻¹)) * incA D (((-1 : 𝓞 D.host.E)) : D.host.E) =
          y i₀ * incA D (μ / ζ i₀) := by
        linear_combination (GlobalTheory.FinPlLoc.idem D (· = v) * (y i₀ * incA D (μ / ζ i₀))) * hT' + hay'
      rw [e2] at h2; exact h2

end GlobalTheory.Core.Mi.LineSD
