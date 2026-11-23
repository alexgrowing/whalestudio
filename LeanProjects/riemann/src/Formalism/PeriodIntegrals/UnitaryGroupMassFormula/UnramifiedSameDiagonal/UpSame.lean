import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnramifiedSameDiagonal.UpFSame
import Formalism.LocalToGlobal.GlobalTheory.UnramifiedDiagonal.DiaConj
import Formalism.LocalToGlobal.GlobalTheory.UnramifiedDiagonal.HeckeRamifiedZeroOfMatchingsAndDu

noncomputable section

namespace SameDiaZero

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.LocalLatticeBases Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0 Formalism.UG
open NumberField IsDedekindDomain Matrix CrossDiaZero

variable {D : D7} {u : D.what₂.Word}

set_option maxHeartbeats 8000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem upSame_one (T : Forms0 D u) (v : (D.mem u).A.vT) (a : ((D.mem u).A.Fv v)ˣ) (k : ℤ)
    (hk : (k : (D.mem u).A.Fv v) = a) (δ : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (hδ : IsDia T.cls0.lev (T.atT.eV v).1 (T.atT.eV v).2 k δ) (c c2 : (D.mem u).C.cls 0)
    (γd : GL (Fin (D.R.N 0)) D.host.E) (hγd : γd ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _))) (κd : T.cls0.lev.U)
    (hx : (T.cls0.y c * δ).1 = bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γd * (T.cls0.y c2).1 * κd.1)
    (c1 c3 : (D.mem u).C.cls 0) (z : Fin (D.R.N 0) → D.host.E) (hz : z ∈ Ld D u 0 (Nat.zero_le _) c)
    (m : 𝓞 D.host.E) (hmP : m ∉ T.atT.Pv v)
    (γ γ2 : UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _))) (η η2 : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (κ κ2 : T.cls0.lev.U)
    (h1 : ∀ v', v' ≠ (T.atT.eV v).1 → bc (prV (E := D.host.E) v') η.1 = 1)
    (h2 : bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 * (T.cls0.y c1).1 = (T.cls0.y c).1 * η.1 * κ.1)
    (h3 : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat γ.1.1 (clsCrd D u 0 (Nat.zero_le _) c1)) = Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (Ld D u 0 (Nat.zero_le _) c))
    (h4 : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat γ.1.1 (Ld D u 0 (Nat.zero_le _) c1)) =
      Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (Ld D u 0 (Nat.zero_le _) c ⊔ Submodule.span (𝓞 D.host.E) {(((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • z}))
    (h5 : ∀ (x : ↥(Ld D u 0 (Nat.zero_le _) c1)) (hx : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (γ.1.1 *ᵥ x.1) ∈ Ld D u 0 (Nat.zero_le _) c),
      (D.fm u).fv 0 v c1 (T.lv0.pr v c1 x) = (D.fm u).fv 0 v c (T.lv0.pr v c ⟨_, hx⟩))
    (g1 : ∀ v', v' ≠ (T.atT.eV v).1 → bc (prV (E := D.host.E) v') η2.1 = 1)
    (g2 : bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ2.1 * (T.cls0.y c3).1 = (T.cls0.y c2).1 * η2.1 * κ2.1)
    (g3 : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat γ2.1.1 (clsCrd D u 0 (Nat.zero_le _) c3)) = Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (Ld D u 0 (Nat.zero_le _) c2))
    (g4 : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat γ2.1.1 (Ld D u 0 (Nat.zero_le _) c3)) =
      Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (Ld D u 0 (Nat.zero_le _) c2 ⊔ Submodule.span (𝓞 D.host.E) {(((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • (m • (((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ z))}))
    (g5 : ∀ (x : ↥(Ld D u 0 (Nat.zero_le _) c3)) (hx : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (γ2.1.1 *ᵥ x.1) ∈ Ld D u 0 (Nat.zero_le _) c2),
      (D.fm u).fv 0 v c3 (T.lv0.pr v c3 x) = (D.fm u).fv 0 v c2 (T.lv0.pr v c2 ⟨_, hx⟩)) :
    η2.1⁻¹ * κd.1 * (δ.1⁻¹ * η.1 * δ.1) ∈ T.cls0.lev.U := by

  have hδ' := Formalism.L2.GlobalTheoryTheory.UnramifiedDiagonal.isDia_conj T.cls0.lev (T.atT.eV v).1 (T.atT.eV v).2 hδ κ
  have hcl := T.val0.dil v a k hk c1 _ hδ'
  obtain ⟨hh, hhH, κ0, hκK, e⟩ := (DoubleCoset.eq _ _ _ _).1 hcl
  have hκ0 : κ0.1 ∈ T.cls0.lev.U := hκK
  obtain ⟨γ', hγ', hge⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hhH)
  have hx1 : (T.cls0.y c1 * Formalism.L2.GlobalTheoryTheory.UnramifiedDiagonal.conjPt T.cls0.lev δ κ).1 =
      bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ' * (T.cls0.y ((D.fm u).dil 0 v a c1)).1 * κ0.1 := by
    rw [e]
    simp only [Subgroup.coe_mul]
    rw [← hge]
  generalize hc1' : (D.fm u).dil 0 v a c1 = c1' at hx1
  have hLat1 := diamond_lattice_transport T v k _ hδ' c1 c1' γ' hγ' ⟨κ0.1, hκ0⟩ hx1
  have hLat := diamond_lattice_transport T v k δ hδ c c2 γd hγd κd hx
  have hInv : mulLat ((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (Ld D u 0 (Nat.zero_le _) c) = Ld D u 0 (Nat.zero_le _) c2 := by
    rw [← hLat.2, rlv_mulLat_inv]

  have hκdP := ((T.cls0.lev.U_eq _).1 κd.2).1
  obtain ⟨ε, hε1⟩ : ∃ ε : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F), ε.1 = κd.1 * δ.1⁻¹ * η.1 * δ.1 * κd.1⁻¹ :=
    ⟨⟨_, mul_mem (mul_mem (mul_mem (mul_mem hκdP (inv_mem δ.2)) η.2) δ.2) (inv_mem hκdP)⟩, rfl⟩
  obtain ⟨κε, hκε⟩ : ∃ κε : T.cls0.lev.U, κε.1 = κd.1 * κ.1 * κ0.1⁻¹ :=
    ⟨⟨_, mul_mem (mul_mem κd.2 κ.2) (inv_mem hκ0)⟩, rfl⟩
  have hγε : (γd⁻¹ * γ.1 * γ' : GL (Fin (D.R.N 0)) D.host.E) ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)) := mul_mem (mul_mem (inv_mem hγd) γ.2) hγ'
  have hε : ∀ v', v' ≠ (T.atT.eV v).1 → bc (prV (E := D.host.E) v') ε.1 = 1 := by
    intro v' hv'
    rw [hε1]
    simp only [map_mul, map_inv, h1 v' hv', hδ.1 v' hv', inv_one, mul_one, one_mul, mul_inv_cancel]
  have h1ε : bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (γd⁻¹ * γ.1 * γ') * (T.cls0.y c1').1 = (T.cls0.y c2).1 * ε.1 * κε.1 := by
    have eγ : bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 = (T.cls0.y c).1 * η.1 * κ.1 * (T.cls0.y c1).1⁻¹ := by rw [← h2]; group
    have hx' : (T.cls0.y c).1 * δ.1 = bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γd * (T.cls0.y c2).1 * κd.1 := hx
    have eγd : bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γd = (T.cls0.y c).1 * δ.1 * κd.1⁻¹ * (T.cls0.y c2).1⁻¹ := by rw [hx']; group
    have hx1' : (T.cls0.y c1).1 * (κ.1⁻¹ * δ.1 * κ.1) = bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ' * (T.cls0.y c1').1 * κ0.1 := hx1
    have eγ' : bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ' = (T.cls0.y c1).1 * (κ.1⁻¹ * δ.1 * κ.1) * κ0.1⁻¹ * (T.cls0.y c1').1⁻¹ := by
      rw [hx1']; group
    rw [hε1, hκε, map_mul, map_mul, map_inv, eγ, eγd, eγ']
    group
  have htriv : (T.cls0.y c2).1 * (1 : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)).1 = bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (1 : GL (Fin (D.R.N 0)) D.host.E) * (T.cls0.y c2).1 * (1 : T.cls0.lev.U).1 := by
    simp only [OneMemClass.coe_one, map_one, mul_one, one_mul]

  have s1 := use₄ (T.atT.Pv v) γ2.1 g3
  have s2 : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat ((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (Ld D u 0 (Nat.zero_le _) c)) = Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (Ld D u 0 (Nat.zero_le _) c2) := by rw [hInv]
  have hP0 : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat ((γ2.1⁻¹ * γd⁻¹ * γ.1 : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (clsCrd D u 0 (Nat.zero_le _) c1)) = Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c3) := by
    rw [Units.val_mul, Units.val_mul]
    exact rlv_chainP (T.atT.Pv v) _ _ (rlv_chainP (T.atT.Pv v) _ _ s1 s2) h3
  have t1 := use₄ (T.atT.Pv v) γ2.1 g4
  have eG : mulLat ((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (Ld D u 0 (Nat.zero_le _) c ⊔ Submodule.span (𝓞 D.host.E) {(((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • z}) =
      Ld D u 0 (Nat.zero_le _) c2 ⊔ Submodule.span (𝓞 D.host.E) {(((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • (((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ z)} := by
    rw [show mulLat ((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (Ld D u 0 (Nat.zero_le _) c ⊔ Submodule.span (𝓞 D.host.E) {(((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • z}) =
        mulLat ((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (Ld D u 0 (Nat.zero_le _) c) ⊔
          mulLat ((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (Submodule.span (𝓞 D.host.E) {(((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • z}) from
        Submodule.map_sup _ _ _, hInv]
    congr 1
    unfold mulLat
    rw [Submodule.map_span, Set.image_singleton]
    congr 2
    show ((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ ((((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • z) = (((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • (((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ z)
    rw [Matrix.mulVec_smul]
  have sc : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (Ld D u 0 (Nat.zero_le _) c2 ⊔ Submodule.span (𝓞 D.host.E) {(((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • (m • (((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ z))}) =
      Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (Ld D u 0 (Nat.zero_le _) c2 ⊔ Submodule.span (𝓞 D.host.E) {(((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • (((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ z)}) := by
    rw [smul_comm_OE]
    exact localization_LshKer_eq_localization_sup _ _ _ m hmP
  have s2' : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat ((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (Ld D u 0 (Nat.zero_le _) c ⊔ Submodule.span (𝓞 D.host.E) {(((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • z})) =
      Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (Ld D u 0 (Nat.zero_le _) c2 ⊔ Submodule.span (𝓞 D.host.E) {(((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • (m • (((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ z))}) := by
    rw [eG, sc]
  have hPd0 : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat ((γ2.1⁻¹ * γd⁻¹ * γ.1 : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (Ld D u 0 (Nat.zero_le _) c1)) = Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (Ld D u 0 (Nat.zero_le _) c3) := by
    rw [Units.val_mul, Units.val_mul]
    exact rlv_chainP (T.atT.Pv v) _ _ (rlv_chainP (T.atT.Pv v) _ _ t1 s2') h4
  have eΓ : ((γ2.1⁻¹ * 1⁻¹ * (γd⁻¹ * γ.1 * γ') : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) =
      ((γ2.1⁻¹ * γd⁻¹ * γ.1 : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) * (γ' : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) := by
    simp only [inv_one, mul_one, Units.val_mul, mul_assoc]
  have s3 : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat (γ' : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (clsCrd D u 0 (Nat.zero_le _) c1')) = Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c1) := by rw [hLat1.1]
  have s3' : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat (γ' : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (Ld D u 0 (Nat.zero_le _) c1')) = Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (Ld D u 0 (Nat.zero_le _) c1) := by rw [hLat1.2]
  have hP : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat ((γ2.1⁻¹ * 1⁻¹ * (γd⁻¹ * γ.1 * γ') : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (clsCrd D u 0 (Nat.zero_le _) c1')) = Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c3) := by
    rw [eΓ]; exact rlv_chainP (T.atT.Pv v) _ _ hP0 s3
  have hPd : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat ((γ2.1⁻¹ * 1⁻¹ * (γd⁻¹ * γ.1 * γ') : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (Ld D u 0 (Nat.zero_le _) c1')) = Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (Ld D u 0 (Nat.zero_le _) c3) := by
    rw [eΓ]; exact rlv_chainP (T.atT.Pv v) _ _ hPd0 s3'

  have hF : ∀ w (hw : w ∈ Ld D u 0 (Nat.zero_le _) c1'), ∃ r : 𝓞 D.host.F, r ∉ (T.atT.eV v).1.asIdeal ∧
      ∃ h : (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r) • (((γ2.1⁻¹ * 1⁻¹ * (γd⁻¹ * γ.1 * γ') : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ w) ∈ Ld D u 0 (Nat.zero_le _) c3,
        (D.fm u).fv 0 v c3 (T.lv0.pr v c3 ⟨_, h⟩) =
          (D.fm u).fv 0 v c1' (T.lv0.pr v c1' ⟨(algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r) • w, Submodule.smul_mem _ _ hw⟩) := by
    intro w hw
    have hw1 : (γ' : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ w ∈ Ld D u 0 (Nat.zero_le _) c1 := by rw [← hLat1.2]; exact ⟨w, hw, rfl⟩
    obtain ⟨r, hr, hmem, hf⟩ := upFSame T v k δ hδ c c1 c2 c3 γd hγd κd hx γ.1 γ2.1 γ.2 γ2.2 z hz h3 h4 h5 g5
      hP0 hPd0 _ hw1
    have eΓw : (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r) • (((γ2.1⁻¹ * 1⁻¹ * (γd⁻¹ * γ.1 * γ') : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ w) =
        (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r) • (((γ2.1⁻¹ * γd⁻¹ * γ.1 : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ ((γ' : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ w)) := by
      rw [Matrix.mulVec_mulVec, eΓ]
    have h : (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r) • (((γ2.1⁻¹ * 1⁻¹ * (γd⁻¹ * γ.1 * γ') : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ w) ∈ Ld D u 0 (Nat.zero_le _) c3 := by
      rw [eΓw]; exact hmem
    refine ⟨r, hr, h, ?_⟩
    have hz1 : (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r) • ((γ' : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ w) ∈ Ld D u 0 (Nat.zero_le _) c1 := Submodule.smul_mem _ _ hw1
    have eback : ((γ'⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r) • ((γ' : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ w)) = (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r) • w := by
      rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
    have hz2 : ((γ'⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r) • ((γ' : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ w)) ∈ Ld D u 0 (Nat.zero_le _) c1' := by
      rw [eback]; exact Submodule.smul_mem _ _ hw
    have d := Formalism.L2.GlobalTheoryTheory.UnramifiedDiagonal.diaFun_same T v k _ hδ' c1 c1' γ' ⟨κ0.1, hκ0⟩ hx1 _ hz1 hz2
    rw [pr_congr T v c3 ⟨_, h⟩ ⟨_, hmem⟩ eΓw, hf, ← d,
      pr_congr T v c1' ⟨_, hz2⟩ ⟨_, Submodule.smul_mem _ _ hw⟩ eback]

  have hΓ : (γ2.1⁻¹ * 1⁻¹ * (γd⁻¹ * γ.1 * γ') : GL (Fin (D.R.N 0)) D.host.E) ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)) :=
    mul_mem (mul_mem (inv_mem γ2.2) (inv_mem (one_mem _))) hγε
  have hU := matching_unitary_eq T.cls0 c2 c1' c2 c3 _ γ2.1 1 ε η2 1 κε κ2 1 h1ε g2 htriv
  have hloc := local_unitary_of_matching_zero T v c3 c1' _ hΓ hU hP hPd hF
  have hmm := matching_move_mem_level_zero T v c2 c1' c2 c3 _ γ2.1 1 ε η2 1 κε κ2 1 hε g1
    (by simp only [OneMemClass.coe_one, map_one]) h1ε g2 htriv hloc
  have efin : η2.1⁻¹ * κd.1 * (δ.1⁻¹ * η.1 * δ.1) = η2.1⁻¹ * (1 : T.cls0.lev.U).1 * ε.1 * κd.1 := by
    rw [hε1, OneMemClass.coe_one]
    group
  rw [efin]
  exact mul_mem hmm κd.2

set_option maxHeartbeats 8000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem upSame (T : Forms0 D u) : Formalism.L2.GlobalTheoryTheory.UnramifiedDiagonal.UpDiaSame0F T := by
  intro v a k hk δ hδ c γd hγd κd hx
  set c2 := (D.fm u).dil 0 v a c with hc2
  have hLat := diamond_lattice_transport T v k δ hδ c c2 γd hγd κd hx
  have hInv : mulLat ((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (Ld D u 0 (Nat.zero_le _) c) = Ld D u 0 (Nat.zero_le _) c2 := by
    rw [← hLat.2, rlv_mulLat_inv]
  have memInv : ∀ y ∈ Ld D u 0 (Nat.zero_le _) c, ((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ y ∈ Ld D u 0 (Nat.zero_le _) c2 := by
    intro y hy
    rw [← hLat.2, mem_mul_lattice_iff] at hy
    exact hy
  have memFwd : ∀ y ∈ Ld D u 0 (Nat.zero_le _) c2, (γd : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ y ∈ Ld D u 0 (Nat.zero_le _) c := by
    intro y hy
    rw [← hLat.2]
    exact ⟨y, hy, rfl⟩
  have eInvFwd : ∀ y : Fin (D.R.N 0) → D.host.E, ((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ ((γd : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ y) = y := by
    intro y
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  have eFwdInv : ∀ y : Fin (D.R.N 0) → D.host.E, (γd : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ (((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ y) = y := by
    intro y
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

  obtain ⟨m, hm⟩ := T.atT.res_surj v ((a⁻¹ : ((D.mem u).A.Fv v)ˣ) : (D.mem u).A.Fv v)
  have hmP : m ∉ T.atT.Pv v := by
    intro h
    rw [AtTTied.Pv, RingHom.mem_ker, hm] at h
    exact Units.ne_zero _ h
  have hkm : T.atT.res v (k : 𝓞 D.host.E) * T.atT.res v m = 1 := by
    rw [map_intCast, hk, hm, Units.mul_inv]
  have hmk : T.atT.res v m * T.atT.res v (k : 𝓞 D.host.E) = 1 := by
    rw [mul_comm]; exact hkm
  have hDFz : ∀ y : ↥(Ld D u 0 (Nat.zero_le _) c), (D.fm u).fv 0 v c2 (T.lv0.pr v c2 ⟨((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ y.1, memInv _ y.2⟩) =
      k • (D.fm u).fv 0 v c (T.lv0.pr v c y) :=
    fun y => Formalism.L2.GlobalTheoryTheory.UnramifiedDiagonal.diaFun_same T v k δ hδ c c2 γd κd hx y.1 y.2 (memInv _ y.2)

  choose zf hzf using fun x : {x : (D.fm u).lv 0 v c // (D.fm u).fv 0 v c x = 1} => T.lv0.pr_surj v c x.1
  have hz1 : ∀ x, (D.fm u).fv 0 v c (T.lv0.pr v c (zf x)) = 1 := fun x => by rw [hzf x]; exact x.2
  choose γ η κ h1 h2 h3 h4 h5 h6 using fun x => T.up_natural_level_zero v c (zf x) (hz1 x)

  let z2 : {x : (D.fm u).lv 0 v c // (D.fm u).fv 0 v c x = 1} → ↥(Ld D u 0 (Nat.zero_le _) c2) :=
    fun x => m • (⟨((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ (zf x).1, memInv _ (zf x).2⟩ : ↥(Ld D u 0 (Nat.zero_le _) c2))
  have hz2 : ∀ x, (D.fm u).fv 0 v c2 (T.lv0.pr v c2 (z2 x)) = 1 := by
    intro x
    show (D.fm u).fv 0 v c2 (T.lv0.pr v c2 (m • (⟨((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ (zf x).1, memInv _ (zf x).2⟩ :
      ↥(Ld D u 0 (Nat.zero_le _) c2)))) = 1
    rw [T.lv0.pr_smul, map_smul, hDFz (zf x), hz1 x, smul_eq_mul, zsmul_eq_mul, mul_one, hk, hm, Units.inv_mul]
  choose γ2 η2 κ2 g1 g2 g3 g4 g5 g6 using fun x => T.up_natural_level_zero v c2 (z2 x) (hz2 x)

  choose zl hzl using fun y : {y : (D.fm u).lv 0 v c2 // (D.fm u).fv 0 v c2 y = 1} => T.lv0.pr_surj v c2 y.1
  let w1 : {y : (D.fm u).lv 0 v c2 // (D.fm u).fv 0 v c2 y = 1} → ↥(Ld D u 0 (Nat.zero_le _) c) :=
    fun y => (k : 𝓞 D.host.E) • (⟨(γd : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ (zl y).1, memFwd _ (zl y).2⟩ : ↥(Ld D u 0 (Nat.zero_le _) c))
  have hinvf : ∀ y, (D.fm u).fv 0 v c (T.lv0.pr v c (w1 y)) = 1 := by
    intro y
    have e := hDFz ⟨(γd : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ (zl y).1, memFwd _ (zl y).2⟩
    rw [pr_congr T v c2 ⟨_, memInv _ (memFwd _ (zl y).2)⟩ (zl y) (eInvFwd _), hzl y, y.2] at e
    show (D.fm u).fv 0 v c (T.lv0.pr v c ((k : 𝓞 D.host.E) •
      (⟨(γd : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ (zl y).1, memFwd _ (zl y).2⟩ : ↥(Ld D u 0 (Nat.zero_le _) c)))) = 1
    rw [T.lv0.pr_smul, map_smul, smul_eq_mul, map_intCast, ← zsmul_eq_mul]
    exact e.symm
  let σ : {x : (D.fm u).lv 0 v c // (D.fm u).fv 0 v c x = 1} ≃
      {y : (D.fm u).lv 0 v c2 // (D.fm u).fv 0 v c2 y = 1} :=
    { toFun := fun x => ⟨T.lv0.pr v c2 (z2 x), hz2 x⟩
      invFun := fun y => ⟨T.lv0.pr v c (w1 y), hinvf y⟩
      left_inv := by
        intro x
        apply Subtype.ext
        have hm1 : (γd : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ (z2 x).1 ∈ Ld D u 0 (Nat.zero_le _) c := memFwd _ (z2 x).2
        have e1 := pr_tr T v c2 c (γd : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) hLat.2 (zl ⟨T.lv0.pr v c2 (z2 x), hz2 x⟩) (z2 x) (hzl _)
          (memFwd _ (zl _).2) hm1
        have e2 : (γd : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ (z2 x).1 = (m • zf x).1 := by
          show (γd : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ (m • (((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ (zf x).1)) = m • (zf x).1
          rw [Matrix.mulVec_smul, eFwdInv]
        show T.lv0.pr v c ((k : 𝓞 D.host.E) • (⟨(γd : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ (zl ⟨T.lv0.pr v c2 (z2 x), hz2 x⟩).1,
          memFwd _ (zl _).2⟩ : ↥(Ld D u 0 (Nat.zero_le _) c))) = x.1
        rw [T.lv0.pr_smul, e1, pr_congr T v c ⟨_, hm1⟩ (m • zf x) e2, T.lv0.pr_smul, hzf x, smul_smul, hkm,
          one_smul]
      right_inv := by
        intro y
        apply Subtype.ext
        have hm1 : ((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ (w1 y).1 ∈ Ld D u 0 (Nat.zero_le _) c2 := memInv _ (w1 y).2
        have e1 := pr_tr T v c c2 ((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) hInv (zf ⟨T.lv0.pr v c (w1 y), hinvf y⟩) (w1 y) (hzf _)
          (memInv _ (zf _).2) hm1
        have e2 : ((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ (w1 y).1 = ((k : 𝓞 D.host.E) • zl y).1 := by
          show ((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ ((k : 𝓞 D.host.E) • ((γd : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ (zl y).1)) = (k : 𝓞 D.host.E) • (zl y).1
          rw [Matrix.mulVec_smul, eInvFwd]
        show T.lv0.pr v c2 (m • (⟨((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ (zf ⟨T.lv0.pr v c (w1 y), hinvf y⟩).1,
          memInv _ (zf _).2⟩ : ↥(Ld D u 0 (Nat.zero_le _) c2))) = y.1
        rw [T.lv0.pr_smul, e1, pr_congr T v c2 ⟨_, hm1⟩ ((k : 𝓞 D.host.E) • zl y) e2, T.lv0.pr_smul, hzl y,
          smul_smul, hmk, one_smul] }
  refine ⟨σ, η, fun y => η2 (σ.symm y), ?_, ?_, ?_⟩
  · intro x
    have hmv : IsUpMvF T v c (T.lv0.pr v c (zf x)) (η x) :=
      ⟨γ x, κ x, h1 x, h2 x, fun h => by
        funext s
        rw [h6 x h s _ (is_translate_inverse T (γ x) s), Units.val_inv_eq_inv_val]
        rfl⟩
    rw [hzf x] at hmv
    exact hmv
  · intro y
    have hmv : IsUpMvF T v c2 (T.lv0.pr v c2 (z2 (σ.symm y))) (η2 (σ.symm y)) :=
      ⟨γ2 _, κ2 _, g1 _, g2 _, fun h => by
        funext s
        rw [g6 _ h s _ (is_translate_inverse T (γ2 _) s), Units.val_inv_eq_inv_val]
        rfl⟩
    have e : T.lv0.pr v c2 (z2 (σ.symm y)) = y.1 := congrArg Subtype.val (σ.apply_symm_apply y)
    rw [e] at hmv
    exact hmv
  · intro x
    show (η2 (σ.symm (σ x))).1⁻¹ * κd.1 * (δ.1⁻¹ * (η x).1 * δ.1) ∈ T.cls0.lev.U
    rw [σ.symm_apply_apply]
    exact upSame_one T v a k hk δ hδ c c2 γd hγd κd hx _ _ (zf x).1 (zf x).2 m hmP (γ x) (γ2 x) (η x) (η2 x)
      (κ x) (κ2 x) (h1 x) (h2 x) (h3 x) (h4 x) (h5 x) (g1 x) (g2 x) (g3 x) (g4 x) (g5 x)

end SameDiaZero

end
