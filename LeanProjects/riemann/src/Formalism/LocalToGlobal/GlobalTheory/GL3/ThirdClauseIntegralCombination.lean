import Mathlib
import Formalism.LocalToGlobal.GlobalTheory.GL3.DlAppendSingle

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.RestC

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker Classical

section Int

variable {σ : Type*} {p : ℕ} [Fact p.Prime]

theorem isPadicIntegral_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ_[p]) (h : ∀ i ∈ s, IsIntP (f i)) :
    IsIntP (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => unfold IsIntP; simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact isPadicIntegral_add (h i (Finset.mem_insert_self i s)) (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem isPadicIntegral_mul {x y : ℂ_[p]} (hx : IsIntP x) (hy : IsIntP y) : IsIntP (x * y) := by
  unfold IsIntP at *
  rw [norm_mul]; exact mul_le_one₀ hx (norm_nonneg _) hy

theorem integralMv_mul {F G : MvPowerSeries σ ℂ_[p]} (hF : IntegralMv F) (hG : IntegralMv G) :
    IntegralMv (F * G) := fun n => by
  classical
  rw [MvPowerSeries.coeff_mul]
  exact isPadicIntegral_sum _ _ fun x _ => isPadicIntegral_mul (hF _) (hG _)

theorem integralMv_C {c : ℂ_[p]} (hc : IsIntP c) :
    IntegralMv (algebraMap ℂ_[p] (MvPowerSeries σ ℂ_[p]) c) := fun n => by
  classical
  have e : MvPowerSeries.coeff n (algebraMap ℂ_[p] (MvPowerSeries σ ℂ_[p]) c) = if n = 0 then c else 0 := by
    first
      | exact MvPowerSeries.coeff_C n c
      | exact MvPowerSeries.coeff_C (σ := σ) n c
      | (rw [MvPowerSeries.algebraMap_apply']; exact MvPowerSeries.coeff_C n c)
      | simp [MvPowerSeries.coeff_C]
      | simp [MvPowerSeries.coeff_C, MvPowerSeries.algebraMap_apply']
  rw [e]
  split_ifs
  · exact hc
  · unfold IsIntP; simp

end Int

section Subst

variable {p : ℕ} [Fact p.Prime]

theorem cc_psubst' {ι : Type*} {a : MvPowerSeries ι ℂ_[p]} (ha : MvPowerSeries.constantCoeff a = 0)
    {f : PowerSeries ℂ_[p]} (hf : PowerSeries.constantCoeff f = 0) :
    MvPowerSeries.constantCoeff (PowerSeries.subst a f) = 0 := by
  obtain ⟨g, rfl⟩ := PowerSeries.X_dvd_iff.mpr hf
  have hs := PowerSeries.HasSubst.of_constantCoeff_zero ha
  rw [PowerSeries.subst_mul hs, PowerSeries.subst_X hs, map_mul, ha, zero_mul]

theorem cc_flog (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) :
    PowerSeries.constantCoeff (flog W wq) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, flog, PowerSeries.coeff_mk, if_pos rfl]

variable {D : D7} {N N' r : ℕ} (lam : Qbar →+* ℂ_[p]) (Λ : AddSubgroup ℂ)
  (C : WeierstrassCurve.VariableChange ℂ_[p]) (wq : PowerSeries ℂ_[p]) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E)

def atLogA : D.what₂.Tau × Fin N' × Fin N → MvPowerSeries (Fin r) ℂ_[p] :=
  fun k => ∑ i, algebraMap ℂ_[p] (MvPowerSeries (Fin r) ℂ_[p])
      (((C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * lamC lam (embT D k.1 (b i k.2.1 k.2.2))) *
      PowerSeries.subst (MvPowerSeries.X i) (flog (C • wModel lam Λ) wq)

theorem atLogA_hasSubst : MvPowerSeries.HasSubst (atLogA lam Λ C wq b) := by
  apply MvPowerSeries.hasSubst_of_constantCoeff_zero
  intro k
  simp only [atLogA, map_sum, map_mul]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [cc_psubst' (MvPowerSeries.constantCoeff_X i) (cc_flog _ wq), mul_zero]

theorem atLog_eq (F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]) :
    atLog D lam Λ C wq b F = MvPowerSeries.substAlgHom (atLogA_hasSubst lam Λ C wq b) F := by
  rw [MvPowerSeries.coe_substAlgHom]; rfl

end Subst

section Clauses

variable {D : D7} (T : Tor D) {N N' : ℕ} {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p])
  (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))

def Cl1 (F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]) : Prop :=
  ∀ (C : WeierstrassCurve.VariableChange ℂ_[p]) (wq : PowerSeries ℂ_[p]) (r : ℕ)
      (b : Fin r → Matrix (Fin N') (Fin N) D.host.E),
    IsModel lam T.abelian₂ C → IsWq (C • wModel lam T.abelian₂) wq → LocBasis D p (YYl D L L') b →
    Orthonormal D b →
    IntegralMv (atLog D lam T.abelian₂ C wq b F * ePh lam T.abelian₂ C wq r)

def Cl3 (F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]) : Prop :=
  ∀ (C : WeierstrassCurve.VariableChange ℂ_[p]) (wq : PowerSeries ℂ_[p]) (r : ℕ)
      (b : Fin r → Matrix (Fin N') (Fin N) D.host.E),
    IsModel lam T.abelian₂ C → IsWq (C • wModel lam T.abelian₂) wq → LocBasis D p (YYl D L L') b →
    IntegralMv (atLog D lam T.abelian₂ C wq b F)

end Clauses

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.RestC
