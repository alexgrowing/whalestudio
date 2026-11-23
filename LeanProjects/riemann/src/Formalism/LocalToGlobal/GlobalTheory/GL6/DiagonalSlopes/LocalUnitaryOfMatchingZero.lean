import Formalism.LocalToGlobal.GlobalTheory.GL6.DiagonalSlopes.StabiliserOfLocalTransport

noncomputable section

open NumberField Ideal IsDedekindDomain
open scoped TensorProduct

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0

open Formalism.BasicNotions Formalism.L2.Forms Matrix Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

section Loc

variable {D : D7} {u : D.what₂.Word} {i : ℕ} {hi : i ≤ D.R.m}

set_option synthInstance.maxHeartbeats 400000 in

theorem stabiliser_of_class_local_eq (A : AtTTied u) (K : ClsTied u i hi) (v : (D.mem u).A.vT) (c c2 : (D.mem u).C.cls i)
    (g : GL (Fin (D.R.N i)) D.host.E)
    (hP : Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (mulLat (g : Matrix _ _ D.host.E) (clsCrd D u i hi c2)) =
      Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (clsCrd D u i hi c))
    (hQ : Formalism.HermitianLatticesTheory.localization₂ (rlvQ A v) (mulLat (g : Matrix _ _ D.host.E) (clsCrd D u i hi c2)) =
      Formalism.HermitianLatticesTheory.localization₂ (rlvQ A v) (clsCrd D u i hi c)) :
    bc (prV (E := D.host.E) (A.eV v).1) ((K.y c).1⁻¹ *
      bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) g * (K.y c2).1) ∈
      stabGL (latS (F := D.host.F) ((A.eV v).1.adicCompletion D.host.F) (intV D.host.E (A.eV v).1) K.lev.Lb) := by
  have hN := rlv_norm A v
  exact rlv_stab (A.eV v).1 (K.y c).1 (K.y c2).1 (K.y_lat c) (K.y_lat c2) g
    (rlv_locV (A.eV v).1 (A.Pv v) (rlvQ A v) hN hP.le hQ.le)
    (rlv_locV (A.eV v).1 (A.Pv v) (rlvQ A v) hN hP.ge hQ.ge)

set_option maxHeartbeats 2000000 in

theorem local_Q_eq_of_dual_P (A : AtTTied u) (v : (D.mem u).A.vT) (c c2 : (D.mem u).C.cls i)
    (g : GL (Fin (D.R.N i)) D.host.E) (hgU : g ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi))
    (hPd : Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (mulLat (g : Matrix _ _ D.host.E) (Ld D u i hi c2)) =
      Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (Ld D u i hi c)) :
    Formalism.HermitianLatticesTheory.localization₂ (rlvQ A v) (mulLat (g : Matrix _ _ D.host.E) (clsCrd D u i hi c2)) =
      Formalism.HermitianLatticesTheory.localization₂ (rlvQ A v) (clsCrd D u i hi c) := by
  obtain ⟨hdd, hfg, hH⟩ := rlv_coordFacts (D := D) (u := u) i hi
  have hgU' : g⁻¹ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi) := inv_mem hgU
  have hg1 : cT (sigD D : D.host.E →+* D.host.E) (g : Matrix _ _ D.host.E) * gramN D i hi * (g : Matrix _ _ D.host.E) =
      gramN D i hi := hgU
  have hg1' : cT (sigD D : D.host.E →+* D.host.E) ((g⁻¹ : GL (Fin (D.R.N i)) D.host.E) : Matrix _ _ D.host.E) * gramN D i hi *
      ((g⁻¹ : GL (Fin (D.R.N i)) D.host.E) : Matrix _ _ D.host.E) = gramN D i hi := hgU'
  have hPd' : Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (Formalism.L2.GlobalTheoryTheory.Comp.dl (sigD D) (gramN D i hi) (clsCrd D u i hi c)) ≤
      Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (mulLat (g : Matrix _ _ D.host.E)
        (Formalism.L2.GlobalTheoryTheory.Comp.dl (sigD D) (gramN D i hi) (clsCrd D u i hi c2))) := hPd.ge
  have hPd'' : Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (mulLat (g : Matrix _ _ D.host.E)
        (Formalism.L2.GlobalTheoryTheory.Comp.dl (sigD D) (gramN D i hi) (clsCrd D u i hi c2))) ≤
      Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (Formalism.L2.GlobalTheoryTheory.Comp.dl (sigD D) (gramN D i hi) (clsCrd D u i hi c)) := hPd.le
  apply le_antisymm
  · exact rlv_dualQ (sigD D) rlv_sig_sig (gramN D i hi) hH _ hg1 (A.Pv v) (hfg c) (hdd c).le hPd'
  · have h1 : Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (Formalism.L2.GlobalTheoryTheory.Comp.dl (sigD D) (gramN D i hi) (clsCrd D u i hi c2)) ≤
        Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (mulLat ((g⁻¹ : GL (Fin (D.R.N i)) D.host.E) : Matrix _ _ D.host.E)
          (Formalism.L2.GlobalTheoryTheory.Comp.dl (sigD D) (gramN D i hi) (clsCrd D u i hi c))) := by
      have := rlv_locP_mulLat_le (A.Pv v) ((g⁻¹ : GL (Fin (D.R.N i)) D.host.E) : Matrix _ _ D.host.E) hPd''
      rwa [rlv_mulLat_inv] at this
    have h2 := rlv_dualQ (sigD D) rlv_sig_sig (gramN D i hi) hH _ hg1' (A.Pv v) (hfg c2) (hdd c2).le h1
    have h3 := rlv_locP_mulLat_le (rlvQ A v) (g : Matrix _ _ D.host.E) h2
    have e3 := rlv_mulLat_inv g⁻¹ (clsCrd D u i hi c)
    rw [inv_inv] at e3
    rw [e3] at h3
    exact h3

set_option maxHeartbeats 2000000 in

theorem local_dual_Q_eq_of_P (A : AtTTied u) (v : (D.mem u).A.vT) (c c2 : (D.mem u).C.cls i)
    (g : GL (Fin (D.R.N i)) D.host.E) (hgU : g ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi))
    (hP : Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (mulLat (g : Matrix _ _ D.host.E) (clsCrd D u i hi c2)) =
      Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (clsCrd D u i hi c)) :
    Formalism.HermitianLatticesTheory.localization₂ (rlvQ A v) (mulLat (g : Matrix _ _ D.host.E) (Formalism.L2.GlobalTheoryTheory.Comp.dl (sigD D) (gramN D i hi) (clsCrd D u i hi c2))) =
      Formalism.HermitianLatticesTheory.localization₂ (rlvQ A v) (Formalism.L2.GlobalTheoryTheory.Comp.dl (sigD D) (gramN D i hi) (clsCrd D u i hi c)) := by
  obtain ⟨hdd, -, hH⟩ := rlv_coordFacts (D := D) (u := u) i hi
  have hfgL : ∀ c1, (Formalism.L2.GlobalTheoryTheory.Comp.dl (sigD D) (gramN D i hi) (Formalism.L2.GlobalTheoryTheory.Comp.dl (sigD D) (gramN D i hi) (clsCrd D u i hi c1))).FG := fun c1 => by
    rw [hdd c1]; exact Module.Finite.iff_fg.1 (tld_isLat (D := D) (u := u) i hi c1).1
  have hBB : ∀ c1, Formalism.L2.GlobalTheoryTheory.Comp.dl (sigD D) (gramN D i hi)
      (Formalism.L2.GlobalTheoryTheory.Comp.dl (sigD D) (gramN D i hi) (Formalism.L2.GlobalTheoryTheory.Comp.dl (sigD D) (gramN D i hi) (clsCrd D u i hi c1))) ≤ Formalism.L2.GlobalTheoryTheory.Comp.dl (sigD D) (gramN D i hi) (clsCrd D u i hi c1) := fun c1 => by
    rw [hdd c1]
  have hgU' : g⁻¹ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi) := inv_mem hgU
  have hg1 : cT (sigD D : D.host.E →+* D.host.E) (g : Matrix _ _ D.host.E) * gramN D i hi * (g : Matrix _ _ D.host.E) =
      gramN D i hi := hgU
  have hg1' : cT (sigD D : D.host.E →+* D.host.E) ((g⁻¹ : GL (Fin (D.R.N i)) D.host.E) : Matrix _ _ D.host.E) * gramN D i hi *
      ((g⁻¹ : GL (Fin (D.R.N i)) D.host.E) : Matrix _ _ D.host.E) = gramN D i hi := hgU'
  apply le_antisymm
  · apply rlv_dualQ (sigD D) rlv_sig_sig (gramN D i hi) hH _ hg1 (A.Pv v) (hfgL c) (hBB c)
    rw [hdd c, hdd c2]
    exact hP.ge
  · have h1 : Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (Formalism.L2.GlobalTheoryTheory.Comp.dl (sigD D) (gramN D i hi) (Formalism.L2.GlobalTheoryTheory.Comp.dl (sigD D) (gramN D i hi) (clsCrd D u i hi c2))) ≤
        Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (mulLat ((g⁻¹ : GL (Fin (D.R.N i)) D.host.E) : Matrix _ _ D.host.E)
          (Formalism.L2.GlobalTheoryTheory.Comp.dl (sigD D) (gramN D i hi) (Formalism.L2.GlobalTheoryTheory.Comp.dl (sigD D) (gramN D i hi) (clsCrd D u i hi c)))) := by
      rw [hdd c, hdd c2]
      have := rlv_locP_mulLat_le (A.Pv v) ((g⁻¹ : GL (Fin (D.R.N i)) D.host.E) : Matrix _ _ D.host.E) hP.le
      rwa [rlv_mulLat_inv] at this
    have h2 := rlv_dualQ (sigD D) rlv_sig_sig (gramN D i hi) hH _ hg1' (A.Pv v) (hfgL c2) (hBB c2) h1
    have h3 := rlv_locP_mulLat_le (rlvQ A v) (g : Matrix _ _ D.host.E) h2
    have e3 := rlv_mulLat_inv g⁻¹ (Formalism.L2.GlobalTheoryTheory.Comp.dl (sigD D) (gramN D i hi) (clsCrd D u i hi c))
    rw [inv_inv] at e3
    rw [e3] at h3
    exact h3

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem stabiliser_of_dual_local_eq (A : AtTTied u) (K : ClsTied u i hi) (v : (D.mem u).A.vT) (c c2 : (D.mem u).C.cls i)
    (g : GL (Fin (D.R.N i)) D.host.E)
    (hP : Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (mulLat (g : Matrix _ _ D.host.E) (Ld D u i hi c2)) =
      Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (Ld D u i hi c))
    (hQ : Formalism.HermitianLatticesTheory.localization₂ (rlvQ A v) (mulLat (g : Matrix _ _ D.host.E) (Ld D u i hi c2)) =
      Formalism.HermitianLatticesTheory.localization₂ (rlvQ A v) (Ld D u i hi c)) :
    bc (prV (E := D.host.E) (A.eV v).1) ((K.y c).1⁻¹ *
      bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) g * (K.y c2).1) ∈
      stabGL (latS (F := D.host.F) ((A.eV v).1.adicCompletion D.host.F)
        (intV D.host.E (A.eV v).1)
        (Formalism.L2.GlobalTheoryTheory.Comp.dl (sigD D) (gramN D i hi) K.lev.Lb)) := by
  have hN := rlv_norm A v
  have hy : ∀ c1 (x : Fin (D.R.N i) → D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F),
      x ∈ Formalism.L2.GlobalTheoryTheory.Comp.hat D.host.F (Ld D u i hi c1) ↔
        (((K.y c1).1⁻¹ : GL (Fin (D.R.N i)) _) : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) _) *ᵥ x ∈
          Formalism.L2.GlobalTheoryTheory.Comp.hat D.host.F (Formalism.L2.GlobalTheoryTheory.Comp.dl (sigD D) (gramN D i hi) K.lev.Lb) := by
    intro c1 x
    rw [dual_class_lattice_eq_global K c1]
    exact Formalism.L2.GlobalTheoryTheory.Comp.mem_hat_glob (dual_base_lattice_full K) _ x
  exact rlv_stab (A.eV v).1 (K.y c).1 (K.y c2).1 (hy c) (hy c2) g
    (rlv_locV (A.eV v).1 (A.Pv v) (rlvQ A v) hN hP.le hQ.le)
    (rlv_locV (A.eV v).1 (A.Pv v) (rlvQ A v) hN hP.ge hQ.ge)

end Loc

section ULoc

variable {D : D7} {u : D.what₂.Word} {i : ℕ} {hi : i ≤ D.R.m}

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem local_unitary_of_matching {A : AtTTied u} (K : ClsTied u i hi) (L : LvTied u A i hi)
    (fMe : ∀ v, K.lev.fM (A.eV v).1 (A.eV v).2 ≃+ (D.mem u).A.Fv v) (hfv : FvTie L K fMe)
    (v : (D.mem u).A.vT) (c c2 : (D.mem u).C.cls i) (Γ : GL (Fin (D.R.N i)) D.host.E)
    (hΓ : Γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi))
    (hU : (K.y c).1⁻¹ * bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) Γ * (K.y c2).1 ∈
      UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (hP : Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (mulLat (Γ : Matrix _ _ D.host.E) (clsCrd D u i hi c2)) =
      Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (clsCrd D u i hi c))
    (hPd : Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (mulLat (Γ : Matrix _ _ D.host.E) (Ld D u i hi c2)) =
      Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (Ld D u i hi c))
    (hF : ∀ z (hz : z ∈ Ld D u i hi c2), ∃ a : 𝓞 D.host.F, a ∉ (A.eV v).1.asIdeal ∧
      ∃ h : (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a) • ((Γ : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E) *ᵥ z) ∈
          Ld D u i hi c,
        (D.fm u).fv i v c (L.pr v c ⟨_, h⟩) =
          (D.fm u).fv i v c2 (L.pr v c2 ⟨(algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a) • z,
            Submodule.smul_mem _ _ hz⟩)) :
    bc (prV (E := D.host.E) (A.eV v).1) ((K.y c).1⁻¹ * bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) Γ * (K.y c2).1) ∈ K.lev.Uloc (A.eV v).1 := by
  rw [K.lev.UlocAlt _ (A.eV v).2]
  refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨Formalism.UG.P.afsplit_bc_mem _ _ _ _ hU, ?_⟩, ?_⟩
  · exact stabiliser_of_class_local_eq A K v c c2 Γ hP (local_Q_eq_of_dual_P A v c c2 Γ hΓ hPd)
  · exact stabiliser_of_local_transport K L fMe hfv v c c2 Γ (stabiliser_of_dual_local_eq A K v c c2 Γ hPd (local_dual_Q_eq_of_P A v c c2 Γ hΓ hP)) hF

end ULoc

section Match

variable {D : D7} {u : D.what₂.Word} {i : ℕ} {hi : i ≤ D.R.m}

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem matching_unitary_eq (K : ClsTied u i hi) (c c1 c2 c3 : (D.mem u).C.cls i) (γ γ2 γd : GL (Fin (D.R.N i)) D.host.E)
    (η η2 δ : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (κ κ2 κd : K.lev.U)
    (h1 : bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ * (K.y c1).1 = (K.y c).1 * η.1 * κ.1)
    (h2 : bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ2 * (K.y c3).1 = (K.y c2).1 * η2.1 * κ2.1)
    (h3 : (K.y c).1 * δ.1 = bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γd * (K.y c2).1 * κd.1) :
    (K.y c3).1⁻¹ * bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (γ2⁻¹ * γd⁻¹ * γ) * (K.y c1).1 ∈ UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) := by
  have hk : ∀ k : K.lev.U, (k.1 : GL (Fin (D.R.N i)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) ∈
      UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) := by
    intro k
    first
      | exact ((K.lev.U_eq _).1 k.2).1
      | exact (K.lev.U_eq _).1 k.2
      | exact ((K.lev.U_eq _).mp k.2).1
  have e1 := eq_mul_inv_of_mul_eq h1
  have e2 := eq_mul_inv_of_mul_eq h2
  have e3 : bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γd =
      (K.y c).1 * δ.1 * κd.1⁻¹ * (K.y c2).1⁻¹ := by
    rw [← mul_inv_eq_iff_eq_mul.mpr h3.symm]; group
  have e : (K.y c3).1⁻¹ * bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (γ2⁻¹ * γd⁻¹ * γ) * (K.y c1).1 =
      κ2.1⁻¹ * η2.1⁻¹ * κd.1 * δ.1⁻¹ * η.1 * κ.1 := by
    rw [map_mul, map_mul, map_inv, map_inv, e1, e2, e3]; group
  rw [e]
  have H := fun (x : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) => x.2
  exact mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (inv_mem (hk κ2)) (inv_mem (H η2))) (hk κd)) (inv_mem (H δ))) (H η)) (hk κ)

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem matching_move_mem_level {A : AtTTied u} (K : ClsTied u i hi) (v : (D.mem u).A.vT)
    (c c1 c2 c3 : (D.mem u).C.cls i) (γ γ2 γd : GL (Fin (D.R.N i)) D.host.E)
    (η η2 δ : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (κ κ2 κd : K.lev.U)
    (hη : ∀ v', v' ≠ (A.eV v).1 → bc (prV (E := D.host.E) v') η.1 = 1)
    (hη2 : ∀ v', v' ≠ (A.eV v).1 → bc (prV (E := D.host.E) v') η2.1 = 1)
    (hδ : bc (prV (E := D.host.E) (A.eV v).1) δ.1 = 1)
    (h1 : bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ * (K.y c1).1 = (K.y c).1 * η.1 * κ.1)
    (h2 : bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ2 * (K.y c3).1 = (K.y c2).1 * η2.1 * κ2.1)
    (h3 : (K.y c).1 * δ.1 = bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γd * (K.y c2).1 * κd.1)
    (hloc : bc (prV (E := D.host.E) (A.eV v).1) ((K.y c3).1⁻¹ * bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (γ2⁻¹ * γd⁻¹ * γ) * (K.y c1).1) ∈ K.lev.Uloc (A.eV v).1) :
    η2.1⁻¹ * κd.1 * η.1 ∈ K.lev.U := by
  have hκ := (K.lev.U_eq _).1 κ.2
  have hκ2 := (K.lev.U_eq _).1 κ2.2
  have hκd := (K.lev.U_eq _).1 κd.2
  rw [K.lev.U_eq]
  refine ⟨mul_mem (mul_mem (inv_mem η2.2) hκd.1) η.2, fun v' => ?_⟩
  by_cases h : v' = (A.eV v).1
  · subst h
    have eη : η.1 = (K.y c).1⁻¹ * (bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ * (K.y c1).1) * κ.1⁻¹ := by rw [h1]; group
    have eη2 : η2.1 = (K.y c2).1⁻¹ * (bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ2 * (K.y c3).1) * κ2.1⁻¹ := by rw [h2]; group
    have eκd : κd.1 = (K.y c2).1⁻¹ * (bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γd)⁻¹ * ((K.y c).1 * δ.1) := by rw [h3]; group
    have e2 : bc (prV (E := D.host.E) (A.eV v).1) (η2.1⁻¹ * κd.1 * η.1) = bc (prV (E := D.host.E) (A.eV v).1) κ2.1 *
        bc (prV (E := D.host.E) (A.eV v).1) ((K.y c3).1⁻¹ * bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (γ2⁻¹ * γd⁻¹ * γ) * (K.y c1).1) * (bc (prV (E := D.host.E) (A.eV v).1) κ.1)⁻¹ := by
      rw [eη, eη2, eκd]
      simp only [map_mul, map_inv, hδ]
      group
    rw [e2]
    exact mul_mem (mul_mem (hκ2.2 _) hloc) (inv_mem (hκ.2 _))
  · rw [map_mul, map_mul, map_inv, hη2 v' h, hη v' h, inv_one, one_mul, mul_one]
    exact hκd.2 v'

end Match

section OnForms0

variable {D : D7} {u : D.what₂.Word}

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem local_unitary_of_matching_zero (T : Forms0 D u)
    (v : (D.mem u).A.vT) (c c2 : (D.mem u).C.cls 0) (Γ : GL (Fin (D.R.N 0)) D.host.E)
    (hΓ : Γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)))
    (hU : (T.cls0.y c).1⁻¹ * bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) Γ * (T.cls0.y c2).1 ∈
      UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (hP : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat (Γ : Matrix _ _ D.host.E) (clsCrd D u 0 (Nat.zero_le _) c2)) =
      Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c))
    (hPd : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat (Γ : Matrix _ _ D.host.E) (Ld D u 0 (Nat.zero_le _) c2)) =
      Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (Ld D u 0 (Nat.zero_le _) c))
    (hF : ∀ z (hz : z ∈ Ld D u 0 (Nat.zero_le _) c2), ∃ a : 𝓞 D.host.F, a ∉ (T.atT.eV v).1.asIdeal ∧
      ∃ h : (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a) • ((Γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ z) ∈
          Ld D u 0 (Nat.zero_le _) c,
        (D.fm u).fv 0 v c (T.lv0.pr v c ⟨_, h⟩) =
          (D.fm u).fv 0 v c2 (T.lv0.pr v c2 ⟨(algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a) • z,
            Submodule.smul_mem _ _ hz⟩)) :
    bc (prV (E := D.host.E) (T.atT.eV v).1) ((T.cls0.y c).1⁻¹ * bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) Γ * (T.cls0.y c2).1) ∈ T.cls0.lev.Uloc (T.atT.eV v).1 := local_unitary_of_matching T.cls0 T.lv0 T.fMe0 T.fv0 v c c2 Γ hΓ hU hP hPd hF

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem matching_move_mem_level_zero (T : Forms0 D u) (v : (D.mem u).A.vT)
    (c c1 c2 c3 : (D.mem u).C.cls 0) (γ γ2 γd : GL (Fin (D.R.N 0)) D.host.E)
    (η η2 δ : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (κ κ2 κd : T.cls0.lev.U)
    (hη : ∀ v', v' ≠ (T.atT.eV v).1 → bc (prV (E := D.host.E) v') η.1 = 1)
    (hη2 : ∀ v', v' ≠ (T.atT.eV v).1 → bc (prV (E := D.host.E) v') η2.1 = 1)
    (hδ : bc (prV (E := D.host.E) (T.atT.eV v).1) δ.1 = 1)
    (h1 : bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ * (T.cls0.y c1).1 = (T.cls0.y c).1 * η.1 * κ.1)
    (h2 : bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ2 * (T.cls0.y c3).1 = (T.cls0.y c2).1 * η2.1 * κ2.1)
    (h3 : (T.cls0.y c).1 * δ.1 = bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γd * (T.cls0.y c2).1 * κd.1)
    (hloc : bc (prV (E := D.host.E) (T.atT.eV v).1) ((T.cls0.y c3).1⁻¹ * bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (γ2⁻¹ * γd⁻¹ * γ) * (T.cls0.y c1).1) ∈ T.cls0.lev.Uloc (T.atT.eV v).1) :
    η2.1⁻¹ * κd.1 * η.1 ∈ T.cls0.lev.U := matching_move_mem_level (A := T.atT) T.cls0 v c c1 c2 c3 γ γ2 γd η η2 δ κ κ2 κd hη hη2 hδ h1 h2 h3 hloc

end OnForms0

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0

end
