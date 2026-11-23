import Formalism.LocalToGlobal.GlobalTheory.UnramifiedTrace.DUAllOfPt
import Formalism.LocalToGlobal.GlobalTheory.GL6.DiagonalSlopes.LocalUnitaryOfMatchingZero

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.UnramifiedTrace

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.LocalLatticeBases Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0 NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct Classical

variable {D : D7} {u : D.what₂.Word}

set_option maxHeartbeats 4000000 in

theorem val_of_mem (T : Forms0 D u) (v : (D.mem u).A.vT)
    (y h1 h2 : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (hs1 : ∀ v', v' ≠ (T.atT.eV v).1 → bc (prV (E := D.host.E) v') h1.1 = 1)
    (hs2 : ∀ v', v' ≠ (T.atT.eV v).1 → bc (prV (E := D.host.E) v') h2.1 = 1)
    (hm : h1.1⁻¹ * h2.1 ∈ T.cls0.lev.U)
    (G : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) → Fr D 0 (Nat.zero_le _) → ℂ)
    (hG : G ∈ AdFun T.cls0.lev (embT D)) :
    G (y * h2) = G (y * h1) := by
  have hx : (y * h2).1 = bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
      (1 : GL (Fin (D.R.N 0)) D.host.E) * (y * h1).1 * (⟨h1.1⁻¹ * h2.1, hm⟩ : T.cls0.lev.U).1 := by
    simp [mul_assoc]
  have key := hG 1 (one_mem _) (y * h1) (y * h2) ⟨h1.1⁻¹ * h2.1, hm⟩ hx
  have hχ : ((T.cls0.lev.chi ⟨h1.1⁻¹ * h2.1, hm⟩ : ℂˣ) : ℂ) = 1 := by
    rw [T.cls0.lev.chi_triv ⟨h1.1⁻¹ * h2.1, hm⟩ (fun w hw => ?_)]
    · rfl
    have hne : w ≠ (T.atT.eV v).1 := fun h => Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0.level_places_not_bad T.atT v (h ▸ hw)
    show bc (prV (E := D.host.E) w) (h1.1⁻¹ * h2.1) = 1
    rw [map_mul, map_inv, hs1 w hne, hs2 w hne, inv_one, one_mul]
  funext s
  rw [key s s (fun τ => by simp [atInf, Matrix.map_one]), hχ, one_mul]

set_option maxHeartbeats 8000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem trip_mem (T : Forms0 D u) (v : (D.mem u).A.vT) (c c1 c3 : (D.mem u).C.cls 0)
    (Γ1 Γ3 : UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)))
    (h1 h3 : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (k1 k3 : T.cls0.lev.U)
    (hs1 : ∀ v', v' ≠ (T.atT.eV v).1 → bc (prV (E := D.host.E) v') h1.1 = 1)
    (hs3 : ∀ v', v' ≠ (T.atT.eV v).1 → bc (prV (E := D.host.E) v') h3.1 = 1)
    (e1 : bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) Γ1.1 * (T.cls0.y c1).1 = (T.cls0.y c).1 * h1.1 * k1.1)
    (e3 : bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) Γ3.1 * (T.cls0.y c3).1 = (T.cls0.y c).1 * h3.1 * k3.1)
    (hP : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat ((Γ3.1⁻¹ * Γ1.1 : GL (Fin (D.R.N 0)) D.host.E) : Matrix _ _ D.host.E)
      (clsCrd D u 0 (Nat.zero_le _) c1)) = Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c3))
    (hPd : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat ((Γ3.1⁻¹ * Γ1.1 : GL (Fin (D.R.N 0)) D.host.E) : Matrix _ _ D.host.E)
      (Ld D u 0 (Nat.zero_le _) c1)) = Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (Ld D u 0 (Nat.zero_le _) c3))
    (hF : ∀ z (hz : z ∈ Ld D u 0 (Nat.zero_le _) c1), ∃ a : 𝓞 D.host.F, a ∉ (T.atT.eV v).1.asIdeal ∧
      ∃ h : (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a) •
          (((Γ3.1⁻¹ * Γ1.1 : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ z) ∈
          Ld D u 0 (Nat.zero_le _) c3,
        (D.fm u).fv 0 v c3 (T.lv0.pr v c3 ⟨_, h⟩) =
          (D.fm u).fv 0 v c1 (T.lv0.pr v c1 ⟨(algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a) • z,
            Submodule.smul_mem _ _ hz⟩)) :
    h3.1⁻¹ * h1.1 ∈ T.cls0.lev.U := by
  have hΓ : ((Γ3.1⁻¹ * Γ1.1 : GL (Fin (D.R.N 0)) D.host.E)) ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)) :=
    mul_mem (inv_mem Γ3.2) Γ1.2
  have hX : (T.cls0.y c3).1⁻¹ * bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (Γ3.1⁻¹ * Γ1.1) *
      (T.cls0.y c1).1 = k3.1⁻¹ * (h3.1⁻¹ * h1.1) * k1.1 := by
    rw [map_mul, map_inv]
    rw [show (T.cls0.y c3).1⁻¹ * ((bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) Γ3.1)⁻¹ *
        bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) Γ1.1) * (T.cls0.y c1).1 =
        (bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) Γ3.1 * (T.cls0.y c3).1)⁻¹ *
        (bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) Γ1.1 * (T.cls0.y c1).1) by group, e1, e3]
    group
  have hmem := fun x => T.cls0.lev.21 x
  have H := Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0.local_unitary_of_matching_zero T v c3 c1 (Γ3.1⁻¹ * Γ1.1) hΓ (by
    rw [hX]
    exact mul_mem (mul_mem (inv_mem ((hmem _).1 k3.2).1) (mul_mem (inv_mem h3.2) h1.2)) ((hmem _).1 k1.2).1) hP hPd hF
  have hh : h3.1⁻¹ * h1.1 = k3.1 * ((T.cls0.y c3).1⁻¹ *
      bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (Γ3.1⁻¹ * Γ1.1) * (T.cls0.y c1).1) * k1.1⁻¹ := by
    rw [hX]; group
  refine (hmem _).2 ⟨mul_mem (inv_mem h3.2) h1.2, fun w => ?_⟩
  by_cases hw : w = (T.atT.eV v).1
  · rw [hw, hh, map_mul, map_mul, map_inv]
    exact mul_mem (mul_mem (((hmem _).1 k3.2).2 _) H) (inv_mem (((hmem _).1 k1.2).2 _))
  · rw [map_mul, map_inv, hs1 w hw, hs3 w hw, inv_one, one_mul]
    exact one_mem _

end Formalism.L2.GlobalTheoryTheory.UnramifiedTrace

end
