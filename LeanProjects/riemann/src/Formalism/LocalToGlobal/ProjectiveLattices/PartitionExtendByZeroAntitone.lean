import Formalism.SharpRestriction.Divisibility.WeightAlgebra
import Formalism.LocalToGlobal.ProjectiveLattices.EmbKCoe

noncomputable section

namespace Formalism.L2.Pj

open Formalism.BasicNotions Formalism.MainNotions NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

instance instCMHost (D : D7) : IsCMField D.host.E := D.host.isCMField_hostE

def InR (D : D7) (j : ℕ) : Prop := 1 ≤ j ∧ j ≤ D.R.m

structure Par (D : D7) : Type 1 where
  H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E
  l : Level H
  c : Coeff l
  Dw : ℕ → Datum H
  Xo : ∀ j, Moduli (Dw j) l
  eO : 𝓞 c.F ≃+* D.what₂.O

variable {D : D7}

def IsDatW (D : D7) {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} (j : ℕ) (Dw : Datum H) : Prop :=
  letI := D.host.cmStar
  Dw.p = (D.R.sigW j).1 ∧ Dw.q = (D.R.sigW j).2 ∧
  ∃ (φ : Dw.La →ₗ[𝓞 D.host.E] (D.sp.W j).V) (ε : ℤˣ), Function.Injective φ ∧
    LinearMap.range φ = Submodule.span (𝓞 D.host.E)
      {v | ∃ a : D.host.E, a ∈ D.host.AA ∧ ∃ x ∈ (D.sp.W j).L0, v = a • x} ∧
    ∀ x y, ((Dw.EF x y : ℤ) : ℚ) =
      ((ε : ℤ) : ℚ) * Algebra.trace ℚ D.host.E (D.host.xi0 * (D.sp.W j).hT (φ x) (φ y))

namespace Par

variable (Q : Par D)

abbrev K : Type := Q.c.F

def PinHost : Prop :=
  Q.H.d = D.host.d ∧ (Q.H.rt : D.host.E) = D.host.sqrtMinusD ∧ Q.H.rt0 = D.host.φ₀ D.host.sqrtMinusD ∧
    ∀ t : D.what₂.Tau, DV.tauEmb D t (Q.H.rt : D.host.E) = Q.H.rt0

def PinLevel : Prop := Q.l.M = D.host.g 0 * D.host.g 1 ∧ Q.l.A = 1

def PinField : Prop := ∀ x : 𝓞 Q.c.F, D.what₂.embLL (D.what₂.OtoLL (Q.eO x)) = ((x : Q.c.F) : ℂ)

def PinDat : Prop := ∀ j, InR D j → IsDatW D j (Q.Dw j)

def Pins : Prop := Q.PinHost ∧ Q.PinLevel ∧ Q.PinField ∧ Q.PinDat

end Par

def ext0 {p : ℕ} (f : Fin p → ℕ) (i : ℕ) : ℕ := if h : i < p then f ⟨i, h⟩ else 0

theorem matrixExtendByZero_add {p : ℕ} (f g : Fin p → ℕ) (i : ℕ) : ext0 (fun k => f k + g k) i = ext0 f i + ext0 g i := by
  unfold ext0; split_ifs <;> rfl

theorem partitionExtendByZero_antitone {p : ℕ} {f : Fin p → ℕ} (hf : Antitone f) : Antitone (ext0 f) := by
  intro i k hik
  unfold ext0
  by_cases hk : k < p
  · rw [dif_pos hk, dif_pos (lt_of_le_of_lt hik hk)]; exact hf hik
  · rw [dif_neg hk]; exact Nat.zero_le _

open Classical in

def wtA {j : ℕ} (w : WeightFamilies.Wt D j) (x : (D.host.E →+* ℂ) × ℕ) : ℕ :=
  ∑ t : D.what₂.Tau, ((if x.1 = DV.tauEmb D t then ext0 (w.aP t) x.2 else 0) +
    if x.1 = conjEmb (DV.tauEmb D t) then ext0 (w.aM t) x.2 else 0)

theorem wtA_wadd {j : ℕ} (w w' : WeightFamilies.Wt D j) : wtA (WeightAlgebra.wadd w w') = wtA w + wtA w' := by
  funext x
  simp only [wtA, Pi.add_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  have h1 : ext0 ((WeightAlgebra.wadd w w').aP t) x.2 = ext0 (w.aP t) x.2 + ext0 (w'.aP t) x.2 := matrixExtendByZero_add _ _ _
  have h2 : ext0 ((WeightAlgebra.wadd w w').aM t) x.2 = ext0 (w.aM t) x.2 + ext0 (w'.aM t) x.2 := matrixExtendByZero_add _ _ _
  rw [h1, h2]
  split_ifs <;> omega

theorem n_wadd {j : ℕ} (w w' : WeightFamilies.Wt D j) : (WeightAlgebra.wadd w w').n = w.n + w'.n := rfl

theorem dom_wtA {j : ℕ} (w : WeightFamilies.Wt D j) : Dom (wtA w) w.n := by
  refine ⟨fun τ i k hik => ?_, w.n_even⟩
  simp only [wtA]
  refine Finset.sum_le_sum fun t _ => add_le_add ?_ ?_
  · split_ifs
    · exact partitionExtendByZero_antitone (w.aPlus_antitone t) hik
    · exact le_rfl
  · split_ifs
    · exact partitionExtendByZero_antitone (w.aM_anti t) hik
    · exact le_rfl

end Formalism.L2.Pj
