import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.ExistsCombComb

open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

private theorem scalar_comm' {K : Type} [Field K] {n : ℕ} (y : Kˣ) (g : GL (Fin n) K) :
    GeneralLinearGroup.scalar (Fin n) y * g = g * GeneralLinearGroup.scalar (Fin n) y :=
  Units.ext (Matrix.scalar_commute (y : K) (fun _ => Commute.all _ _) g.val).eq

private theorem finsum_top {K : Type} [Field K] {n : ℕ} (O : Subring K) (ϖ : Kˣ) (W : GL (Fin n) K → ℂ)
    (hW : ∀ g, ∀ k ∈ Formalism.UG.GLint (Fin n) O, W (g * k) = W g) (g : GL (Fin n) K) :
    ∑ᶠ c : GL (Fin n) K ⧸ Formalism.UG.GLint (Fin n) O, Formalism.UG.Tj ℂ n O (ϖ : K) n c.out * W (g * c.out) =
      W (g * GeneralLinearGroup.scalar (Fin n) ϖ) := by
  set z : GL (Fin n) K := GeneralLinearGroup.scalar (Fin n) ϖ with hz
  have hd : Formalism.UG.diagJ n (ϖ : K) n = z.val := by
    simp [Formalism.UG.diagJ, hz]
  rw [finsum_eq_single _ (z : GL (Fin n) K ⧸ Formalism.UG.GLint (Fin n) O)]
  · obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (Formalism.UG.GLint (Fin n) O) z
    rw [hk, ← mul_assoc, hW _ _ k.2, Formalism.UG.Tj, Set.indicator_of_mem, Pi.one_apply, one_mul]
    exact ⟨1, one_mem _, k, k.2, by simp [hd]⟩
  · intro c hc
    rw [Formalism.UG.Tj, Set.indicator_of_notMem, zero_mul]
    rintro ⟨a, ha, b, hb, e⟩
    refine hc ?_
    have e' : c.out = z * (a * b) := by
      rw [← mul_assoc, hz, scalar_comm', ← hz]
      exact Units.ext (by rw [e, hd]; rfl)
    rw [← QuotientGroup.out_eq' c, e']
    exact QuotientGroup.mk_mul_of_mem _ (mul_mem ha hb)

private theorem scalar_mem {K : Type} [Field K] {n : ℕ} (O : Subring K) (u : Kˣ) (h : (u : K) ∈ O)
    (h' : ((u⁻¹ : Kˣ) : K) ∈ O) : GeneralLinearGroup.scalar (Fin n) u ∈ Formalism.UG.GLint (Fin n) O := by
  have key : ∀ x : Kˣ, (x : K) ∈ O → ∀ i j, (GeneralLinearGroup.scalar (Fin n) x).val i j ∈ O := fun x hx i j => by
    change Matrix.diagonal (fun _ => (x : K)) i j ∈ O
    rw [Matrix.diagonal_apply]
    split_ifs
    · exact hx
    · exact zero_mem _
  refine GlobalTheory.AdelicU.mem_GLint_iff.2 ⟨key u h, ?_⟩
  rw [← map_inv]
  exact key _ h'

theorem UpperTheory.V.Af.Smo.centLoc :
    UpperTheory.V.Af.Smo.CentLoc := by
  intro E _ _ n w B y
  by_cases hB : B.card = n
  swap
  · exact ⟨0, fun W hW => absurd hW.card hB⟩
  let H : Subgroup (w.adicCompletion E)ˣ :=
    { carrier := {y | ∃ c : ℂ, c ≠ 0 ∧ ∀ W : GL (Fin n) (w.adicCompletion E) → ℂ, Eig w B W →
        ∀ g, W (g * GeneralLinearGroup.scalar (Fin n) y) = c * W g}
      one_mem' := ⟨1, one_ne_zero, fun W _ g => by simp⟩
      mul_mem' := by
        rintro a b ⟨c, hc, h⟩ ⟨d, hd, h'⟩
        exact ⟨d * c, mul_ne_zero hd hc, fun W hW g => by rw [map_mul, ← mul_assoc, h' W hW, h W hW, mul_assoc]⟩
      inv_mem' := by
        rintro a ⟨c, hc, h⟩
        refine ⟨c⁻¹, inv_ne_zero hc, fun W hW g => ?_⟩
        have := h W hW (g * GeneralLinearGroup.scalar (Fin n) a⁻¹)
        rw [mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one] at this
        rw [this, inv_mul_cancel_left₀ hc] }
  suffices hy : y ∈ H from hy.imp fun _ h => h.2
  obtain ⟨p, hp⟩ : ∃ p, Formalism.UG.IsUnifV E w p := w.valuedAdicCompletion_surjective E _
  have hp0 : p ≠ 0 := fun h0 => by simp [Formalism.UG.IsUnifV, h0] at hp
  have hne : GlobalTheory.LFun.satEig (Formalism.UG.qV E w) n B n ≠ 0 := by
    have hq := Multiset.powersetCard_self (B.map fun b : ℂˣ => (b : ℂ))
    rw [Multiset.card_map, hB] at hq
    simp [GlobalTheory.LFun.satEig, Multiset.esymm, hq]
  have hpH : Units.mk0 p hp0 ∈ H := ⟨_, hne, fun W hW g =>
    (finsum_top (Formalism.UG.Ov E w) (Units.mk0 p hp0) W hW.inv g).symm.trans (hW.eig p hp n le_rfl g)⟩
  have hu : ∀ u : (w.adicCompletion E)ˣ, Valued.v (u : w.adicCompletion E) = 1 → u ∈ H := fun u h =>
    ⟨1, one_ne_zero, fun W hW g => by
      rw [one_mul]
      refine hW.inv g _ (scalar_mem (Formalism.UG.Ov E w) u h.le ?_)
      change Valued.v ((u⁻¹ : (w.adicCompletion E)ˣ) : w.adicCompletion E) ≤ 1
      rw [Units.val_inv_eq_inv_val, map_inv₀, h, inv_one]⟩
  have hy0 : Valued.v (y : w.adicCompletion E) ≠ 0 := by simp
  have := hu (y * Units.mk0 p hp0 ^ WithZero.log (Valued.v (y : w.adicCompletion E))) (by
    have hp' : Valued.v p = WithZero.exp (-1 : ℤ) := hp
    rw [Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, Units.val_mk0, hp', ← WithZero.exp_zsmul]
    simp [WithZero.exp_log hy0])
  exact (H.mul_mem_cancel_right (H.zpow_mem hpH _)).1 this
