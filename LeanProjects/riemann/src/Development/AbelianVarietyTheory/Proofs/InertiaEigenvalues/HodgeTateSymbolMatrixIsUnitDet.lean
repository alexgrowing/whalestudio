import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoordFMemFil
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSymbolBasis
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.HTBasis

noncomputable section

namespace GlobalTheory.HTBasis

open GlobalTheory.DeRhamSymbol Formalism.MainNotions.LocalSituation GlobalTheory.Cyc

theorem colHT_isUnit_det {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P}
    (J : Formalism.MainNotions.LocalSituation.ThetaL P AI) {K : FinExt l} {m : ℕ} (u : Fin m → Fin m → P.R.BdR) (k : Fin m → ℤ)
    (hu : ∀ i j, u i j ∈ (P.PD K).Fil (k i))
    (hspan : ∀ (n : ℤ) (y : Fin m → P.R.BdR), (∀ j, y j ∈ (P.PD K).Fil n) →
      ∃ f : Fin m → P.R.BdR, (∀ i, f i ∈ (P.PD K).Fil (n - k i)) ∧ y = ∑ i, f i • u i)
    (hli : LinearIndependent P.R.BdR u) : IsUnit (colHT J u k).det := by
  rw [isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨c, hc0, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  apply hc0
  set s : Fin m → Fin m → P.R.BdR := fun i j => ((tU P ^ (-k i) : P.R.BdRˣ) : P.R.BdR) * u i j with hs
  have hs0 : ∀ i j, s i j ∈ (P.PD (botExt l)).Fil 0 := fun i j =>
    (shift_iff J (k i) 0 _).2 (by rw [add_zero]; exact (mem_iff K _ _).1 (hu i j))
  choose γ hγ0 hγ using J.θ_onto
  set z : Fin m → P.R.BdR := fun j => ∑ i, γ (c i) * s i j with hz
  have hz0 : ∀ j, z j ∈ (P.PD (botExt l)).Fil 0 := fun j => by
    have := Submodule.sum_mem ((P.PD (botExt l)).Fil 0) (t := Finset.univ)
      (f := fun i => γ (c i) * s i j) fun i _ => by
        simpa using (P.PD (botExt l)).Fil_mul 0 0 _ _ (hγ0 (c i)) (hs0 i j)
    exact this
  have hz1 : ∀ j, z j ∈ (P.PD K).Fil 1 := fun j => by
    rw [mem_iff K]
    refine (J.θ_ker _ (hz0 j)).1 ?_
    have h1 := congrFun hc j
    simp only [Matrix.mulVec, dotProduct, colHT, Matrix.of_apply, Pi.zero_apply] at h1
    rw [hz, GlobalTheory.DeRhamSymbolBasis.theta_sum J _ _ fun i => by
      simpa using (P.PD (botExt l)).Fil_mul 0 0 _ _ (hγ0 (c i)) (hs0 i j)]
    rw [← h1]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [J.θ_mul _ (hγ0 (c i)) _ (hs0 i j), hγ, mul_comm]
  obtain ⟨f, hf, hfz⟩ := hspan 1 z hz1
  have hz' : z = ∑ i, (γ (c i) * ((tU P ^ (-k i) : P.R.BdRˣ) : P.R.BdR)) • u i := by
    funext j
    simp only [hz, hs, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_assoc]
  have hdiff := Fintype.linearIndependent_iff.1 hli
    (fun i => f i - γ (c i) * ((tU P ^ (-k i) : P.R.BdRˣ) : P.R.BdR)) (by
      simp only [sub_smul, Finset.sum_sub_distrib, ← hfz, ← hz', sub_self])
  funext i
  have hfi : f i = γ (c i) * ((tU P ^ (-k i) : P.R.BdRˣ) : P.R.BdR) := sub_eq_zero.1 (hdiff i)
  have hγi : γ (c i) = f i * ((tU P ^ (k i) : P.R.BdRˣ) : P.R.BdR) := by
    rw [hfi, mul_assoc, ← Units.val_mul, ← zpow_add, neg_add_cancel, zpow_zero, Units.val_one, mul_one]
  have hmem : γ (c i) ∈ (P.PD (botExt l)).Fil 1 := by
    have := (P.PD (botExt l)).Fil_mul _ _ _ _ ((mem_iff K _ _).1 (hf i)) (zpow_mem J (k i))
    rw [sub_add_cancel] at this
    rwa [hγi]
  rw [Pi.zero_apply, ← hγ (c i)]
  exact (J.θ_ker _ (hγ0 (c i))).2 hmem

end GlobalTheory.HTBasis
