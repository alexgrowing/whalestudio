import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothReal
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitDetRoot
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TameHeckeCharTrivialOnFiniteUnitsCongOne

open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolRead

theorem mu_eq_one_of_mem_level : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F), LawsJ T → R.toLevCh.Is A.μ0 → ChiR T R → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), GoodEmb T.Q.c (res T σ) → ∀ k ∈ T.Kf ((i : ℕ) + 1) (res T σ), T.mu ((i : ℕ) + 1) (res T σ) k = 1 := by
  intro D G _ _ Pl0 T0 A T _ R hT hL hC i σ hσ k hk
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩
  have hodd : Odd (D.host.g 0 * D.host.g 1) :=
    ((D.host.g_prime 0).odd_of_ne_two (g_ne_two D 0)).mul ((D.host.g_prime 1).odd_of_ne_two (g_ne_two D 1))
  obtain ⟨hk1, hk2⟩ := (hT.levelK _ hj _ hσ k).1 hk
  obtain ⟨x, hxu, hxr, hxc⟩ := GlobalTheory.UnitDetRoot.exists_unit_detRoot D _ _ hodd k hk1 hk2
  have h0 : R.mu0 ((i : ℕ) + 1) x = 1 := by
    refine GlobalTheory.tame_heckeChar_eq_one_of_finUnit D _ _ (hL.mu0 i) (R.C.isMu0 i).tame _ (fun P hP => ?_) x hxu hxc
    refine (R.C.isMu0 i).unr P fun l hl => hP ?_
    have hl' : ((D.host.g l : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := hl
    rw [Nat.cast_mul]
    fin_cases l
    · exact P.asIdeal.mul_mem_right _ hl'
    · exact P.asIdeal.mul_mem_left _ hl'
  obtain ⟨y, hy1, hy2⟩ := (hC i σ hσ).2.2.2.1 x hxu.1
  rw [h0, Circle.coe_one] at hy1
  have hy : algebraMap T.Q.c.F D.what₂.LL y = 1 :=
    D.what₂.embLL.injective (hy1.symm.trans (map_one _).symm)
  rw [hy, map_one] at hy2
  exact ((hT.muVal _ hj _ hσ).2 k x hxr).trans hy2

end GlobalTheory.HolRead
