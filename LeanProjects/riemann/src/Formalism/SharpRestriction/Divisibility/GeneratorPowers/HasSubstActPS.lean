import Formalism.SharpRestriction.Divisibility.GeneratorPowers.JetSubstPSEqJetMap
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.UnitIdSt

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGG

open MvPowerSeries NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGU

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {S : Type} [CommRing S] (c : Coeff l) [Algebra c.F S]

theorem const_actPS (a : 𝓞 E) (q : Fin 1 × Fin (dL Dw)) : constantCoeff (actPS (Dw := Dw) (S := S) c a q) = 0 := by
  simp [actPS]

theorem hasSubst_actPS (a : 𝓞 E) : HasSubst (actPS (Dw := Dw) (S := S) c a) :=
  hasSubst_of_constantCoeff_zero (fun q => const_actPS c a q)

theorem actPS_comp (u v : 𝓞 E) (q : Fin 1 × Fin (dL Dw)) :
    subst (actPS (Dw := Dw) (S := S) c v) (actPS (Dw := Dw) (S := S) c u q) = actPS (Dw := Dw) (S := S) c (u * v) q := by
  have hv := hasSubst_actPS (Dw := Dw) (S := S) c v
  have e : actPS (Dw := Dw) (S := S) c u q =
      algebraMap c.F S (embK c ((ltIdx Dw).symm q.2).1 u) • MvPowerSeries.X q := rfl
  rw [e, subst_smul hv, subst_X hv]
  simp only [actPS, smul_smul, map_mul]

theorem φa_mul {d : ℕ} (φ : Fin d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S) (u v : 𝓞 E) (j : Fin d) :
    subst (actPS (Dw := Dw) c v) (φa c φ u j) = φa c φ (u * v) j := by
  simp only [φa]
  rw [subst_comp_subst_apply (hasSubst_actPS c u) (hasSubst_actPS c v)]
  congr 1
  funext q
  exact actPS_comp c u v q

theorem φa_one {d : ℕ} (φ : Fin d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S) : φa c φ 1 = φ := by
  have e : actPS (Dw := Dw) (S := S) c 1 = MvPowerSeries.X := by
    funext q
    simp [actPS]
  funext j
  simp only [φa, e, subst_self, id]

theorem actPS_add (u v : 𝓞 E) (q : Fin 1 × Fin (dL Dw)) :
    actPS (Dw := Dw) (S := S) c u q + actPS (Dw := Dw) (S := S) c v q = actPS (Dw := Dw) (S := S) c (u + v) q := by
  simp only [actPS, map_add, add_smul]

theorem const_φa {d : ℕ} (φ : Fin d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S) (hφ : ∀ j, constantCoeff (φ j) = 0)
    (u : 𝓞 E) (j : Fin d) : constantCoeff (φa c φ u j) = 0 :=
  ExpGF.const_substPS _ (fun q => const_actPS c u q) _ (hφ j)

theorem law_φa {d : ℕ} {F : Fin d → MvPowerSeries (Fin 2 × Fin d) S} {uvec : Lt1 Dw → Fin d → S}
    {φ : Fin d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S} (hφ : IsExpOf F uvec φ) (u v : 𝓞 E) (j : Fin d) :
    subst (fun p : Fin 2 × Fin d => φa c φ (![u, v] p.1) p.2) (F j) = φa c φ (u + v) j := by
  let b : Fin 2 × Fin (dL Dw) → MvPowerSeries (Fin 1 × Fin (dL Dw)) S :=
    fun p => actPS (Dw := Dw) (S := S) c (![u, v] p.1) ((0 : Fin 1), p.2)
  have hb : HasSubst b := hasSubst_of_constantCoeff_zero (fun p => const_actPS c _ _)
  have hX : ∀ i : Fin 2, HasSubst (fun q : Fin 1 × Fin (dL Dw) =>
      (MvPowerSeries.X (i, q.2) : MvPowerSeries (Fin 2 × Fin (dL Dw)) S)) :=
    fun i => hasSubst_of_constantCoeff_zero (fun q => by simp)
  have hA : HasSubst (fun p : Fin 2 × Fin d => atPt p.1 (φ p.2)) :=
    hasSubst_of_constantCoeff_zero (fun p => ExpGF.const_substPS _ (fun q => by simp) _ (hφ.const p.2))
  have hS : HasSubst (fun q : Fin 1 × Fin (dL Dw) =>
      (MvPowerSeries.X ((0 : Fin 2), q.2) + MvPowerSeries.X ((1 : Fin 2), q.2) :
        MvPowerSeries (Fin 2 × Fin (dL Dw)) S)) :=
    hasSubst_of_constantCoeff_zero (fun q => by simp)
  have key := congrArg (MvPowerSeries.subst b) (hφ.hom j)
  rw [subst_comp_subst_apply hA hb, subst_comp_subst_apply hS hb] at key
  have e1 : (fun p : Fin 2 × Fin d => MvPowerSeries.subst b (atPt p.1 (φ p.2))) =
      fun p => φa c φ (![u, v] p.1) p.2 := by
    funext ⟨i, k⟩
    simp only [atPt, φa]
    rw [subst_comp_subst_apply (hX i) hb]
    congr 1
    funext ⟨q1, q2⟩
    rw [subst_X hb]
    have h1 : q1 = 0 := Subsingleton.elim _ _
    subst h1
    rfl
  have e2 : (fun q : Fin 1 × Fin (dL Dw) => MvPowerSeries.subst b
      (MvPowerSeries.X ((0 : Fin 2), q.2) + MvPowerSeries.X ((1 : Fin 2), q.2) :
        MvPowerSeries (Fin 2 × Fin (dL Dw)) S)) = actPS (Dw := Dw) (S := S) c (u + v) := by
    funext ⟨q1, q2⟩
    have h1 : q1 = 0 := Subsingleton.elim _ _
    subst h1
    rw [subst_add hb, subst_X hb, subst_X hb]
    exact actPS_add c u v _
  rw [e1, e2] at key
  exact key

theorem act_φa {d : ℕ} {act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S}
    {φ : Fin d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S} (hφ : ∀ j, constantCoeff (φ j) = 0)
    (hact : ∀ a j, subst (fun p : Fin 1 × Fin d => φ p.2) (act a j) = subst (actPS (Dw := Dw) c a) (φ j))
    (a u : 𝓞 E) (j : Fin d) :
    subst (fun p : Fin 1 × Fin d => φa c φ u p.2) (act a j) = φa c φ (a * u) j := by
  have hP : HasSubst (fun p : Fin 1 × Fin d => φ p.2) :=
    hasSubst_of_constantCoeff_zero (fun p => hφ p.2)
  have h := subst_comp_subst_apply hP (hasSubst_actPS (Dw := Dw) (S := S) c u) (act a j)
  rw [hact a j] at h
  exact h.symm.trans (φa_mul c φ a u j)

end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGG
