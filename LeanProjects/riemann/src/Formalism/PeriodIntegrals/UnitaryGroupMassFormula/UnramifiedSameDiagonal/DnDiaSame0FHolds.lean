import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CrossDiagonalMatching.DnDiaMatch0FHolds
import Formalism.LocalToGlobal.GlobalTheory.UnramifiedDiagonal.DiaSame
import Formalism.LocalToGlobal.GlobalTheory.UnramifiedDiagonal.DiaConj
import Formalism.LocalToGlobal.GlobalTheory.UnramifiedDiagonal.DiaFun
import Formalism.LocalToGlobal.GlobalTheory.UnramifiedDiagonal.HeckeRamifiedZeroOfMatchingsAndDu

noncomputable section

namespace SameDiaZero

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.LocalLatticeBases Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0 Formalism.UG
open Formalism.L2.GlobalTheoryTheory.UnramifiedDiagonal CrossDiaZero
open NumberField IsDedekindDomain Matrix

variable {D : D7} {u : D.what₂.Word}

theorem inv_mulVec_self {E : Type} [Field E] {n : ℕ} (g : GL (Fin n) E) (z : Fin n → E) :
    ((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ ((g : Matrix (Fin n) (Fin n) E) *ᵥ z) = z := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 4000000 in

theorem dnk_latP_smul (T : Forms0 D u) (v : (D.mem u).A.vT) (c c1 c2 : (D.mem u).C.cls 0)
    (g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c)) (μ : (D.mem u).A.Fv v) (hμ : μ ≠ 0)
    (γ γ' : GL (Fin (D.R.N 0)) D.host.E)
    (hl : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (Ld D u 0 (Nat.zero_le _) c1)) =
      Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c))
    (hfun : ∀ (x : ↥(Ld D u 0 (Nat.zero_le _) c1)) (hx : (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ x.1 ∈ Lk T.atT 0 (Nat.zero_le _) v c),
      (D.fm u).fv 0 v c1 (T.lv0.pr v c1 x) = g (T.lv0.prk v c ⟨_, hx⟩))
    (hl' : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat (γ' : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (Ld D u 0 (Nat.zero_le _) c2)) =
      Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c))
    (hfun' : ∀ (x : ↥(Ld D u 0 (Nat.zero_le _) c2)) (hx : (γ' : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ x.1 ∈ Lk T.atT 0 (Nat.zero_le _) v c),
      (D.fm u).fv 0 v c2 (T.lv0.pr v c2 x) = μ • g (T.lv0.prk v c ⟨_, hx⟩)) :
    Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat ((γ⁻¹ * γ' : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E)
      (clsCrd D u 0 (Nat.zero_le _) c2)) =
      Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c1) := by
  have hfun2 : ∀ (x : ↥(Ld D u 0 (Nat.zero_le _) c2)) (hx : (γ' : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ x.1 ∈ Lk T.atT 0 (Nat.zero_le _) v c),
      (D.fm u).fv 0 v c2 (T.lv0.pr v c2 x) = (μ • g) (T.lv0.prk v c ⟨_, hx⟩) := fun x hx =>
    (hfun' x hx).trans (LinearMap.smul_apply μ g _).symm
  have eq1 : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat (γ' : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (Lk T.atT 0 (Nat.zero_le _) v c2)) =
      Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (Lk T.atT 0 (Nat.zero_le _) v c1)) := by
    ext y
    rw [dnk_char T v c c2 (μ • g) γ' hl' hfun2 y, dnk_char T v c c1 g γ hl hfun y]
    simp only [LinearMap.smul_apply, smul_eq_zero, hμ, false_or]
  have L1 : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (Lk T.atT 0 (Nat.zero_le _) v c1) =
      Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c1) :=
    le_antisymm (dnk_lk_locP T v c1) (localization_mono₂ _ le_sup_left)
  have L2 : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (Lk T.atT 0 (Nat.zero_le _) v c2) =
      Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c2) :=
    le_antisymm (dnk_lk_locP T v c2) (localization_mono₂ _ le_sup_left)
  have M1 : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (Lk T.atT 0 (Nat.zero_le _) v c1)) =
      Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (clsCrd D u 0 (Nat.zero_le _) c1)) :=
    le_antisymm (rlv_locP_mulLat_le _ _ L1.le) (rlv_locP_mulLat_le _ _ L1.ge)
  have M2 : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat (γ' : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (Lk T.atT 0 (Nat.zero_le _) v c2)) =
      Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat (γ' : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (clsCrd D u 0 (Nat.zero_le _) c2)) :=
    le_antisymm (rlv_locP_mulLat_le _ _ L2.le) (rlv_locP_mulLat_le _ _ L2.ge)
  rw [M1, M2] at eq1
  exact localization_smul_cancel _ γ γ' eq1

set_option maxHeartbeats 8000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem dn_same_loc (T : Forms0 D u) (v : (D.mem u).A.vT) (k : ℤ) (hμ : ((k : ℤ) : (D.mem u).A.Fv v) ≠ 0)
    (c c2 c1 c3 c1' : (D.mem u).C.cls 0) (γd : GL (Fin (D.R.N 0)) D.host.E) (hγd : γd ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)))
    (hLc : mulLat (γd : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (clsCrd D u 0 (Nat.zero_le _) c2) = clsCrd D u 0 (Nat.zero_le _) c)
    (hLd : mulLat (γd : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (Ld D u 0 (Nat.zero_le _) c2) = Ld D u 0 (Nat.zero_le _) c)
    (x : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c)) (x2 : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c2))
    (hxy : ∀ w, x2 w = ((k : ℤ) : (D.mem u).A.Fv v) • x (dniEquiv T v c2 c γd hLc hLd w))
    (γ γ2 : UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)))
    (hl1 : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat γ.1.1 (Ld D u 0 (Nat.zero_le _) c1)) = Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c))
    (hl2 : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat γ2.1.1 (Ld D u 0 (Nat.zero_le _) c3)) = Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c2))
    (hf1 : ∀ (w : ↥(Ld D u 0 (Nat.zero_le _) c1)) (hw : γ.1.1 *ᵥ w.1 ∈ Lk T.atT 0 (Nat.zero_le _) v c),
      (D.fm u).fv 0 v c1 (T.lv0.pr v c1 w) = x (T.lv0.prk v c ⟨_, hw⟩))
    (hf2 : ∀ (w : ↥(Ld D u 0 (Nat.zero_le _) c3)) (hw : γ2.1.1 *ᵥ w.1 ∈ Lk T.atT 0 (Nat.zero_le _) v c2),
      (D.fm u).fv 0 v c3 (T.lv0.pr v c3 w) = x2 (T.lv0.prk v c2 ⟨_, hw⟩))
    (γe : GL (Fin (D.R.N 0)) D.host.E) (hγe : γe ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)))
    (hLc1 : mulLat (γe : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (clsCrd D u 0 (Nat.zero_le _) c1') = clsCrd D u 0 (Nat.zero_le _) c1)
    (hLd1 : mulLat (γe : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (Ld D u 0 (Nat.zero_le _) c1') = Ld D u 0 (Nat.zero_le _) c1)
    (hdf : ∀ z (hz : z ∈ Ld D u 0 (Nat.zero_le _) c1)
      (hz2 : ((γe⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ z ∈ Ld D u 0 (Nat.zero_le _) c1'),
      (D.fm u).fv 0 v c1' (T.lv0.pr v c1' ⟨_, hz2⟩) = k • (D.fm u).fv 0 v c1 (T.lv0.pr v c1 ⟨z, hz⟩))
    (hU : (T.cls0.y c3).1⁻¹ * bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (γ2.1⁻¹ * 1⁻¹ * (γd⁻¹ * γ.1 * γe)) * (T.cls0.y c1').1 ∈ UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) :
    bc (prV (E := D.host.E) (T.atT.eV v).1) ((T.cls0.y c3).1⁻¹ * bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (γ2.1⁻¹ * 1⁻¹ * (γd⁻¹ * γ.1 * γe)) *
      (T.cls0.y c1').1) ∈ T.cls0.lev.Uloc (T.atT.eV v).1 := by
  classical
  set g' : GL (Fin (D.R.N 0)) D.host.E := γd * γ2.1 with hg'
  have hl' : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat (g' : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (Ld D u 0 (Nat.zero_le _) c3)) = Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c) := by
    rw [hg', Units.val_mul]
    exact rlv_chainP _ _ _ (by rw [hLc]) hl2
  have hLkinv : mulLat ((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (Lk T.atT 0 (Nat.zero_le _) v c) = Lk T.atT 0 (Nat.zero_le _) v c2 :=
    dni_inv_eq γd (dni_lk T v c2 c _ hLc hLd)
  have hf' : ∀ (w : ↥(Ld D u 0 (Nat.zero_le _) c3)) (hw : (g' : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ w.1 ∈ Lk T.atT 0 (Nat.zero_le _) v c),
      (D.fm u).fv 0 v c3 (T.lv0.pr v c3 w) = ((k : ℤ) : (D.mem u).A.Fv v) • x (T.lv0.prk v c ⟨_, hw⟩) := by
    intro w hw
    have e1 : ((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ ((g' : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ w.1) = γ2.1.1 *ᵥ w.1 := by
      rw [hg', Matrix.mulVec_mulVec, ← Units.val_mul, ← mul_assoc, inv_mul_cancel, one_mul]
    have hw2 : γ2.1.1 *ᵥ w.1 ∈ Lk T.atT 0 (Nat.zero_le _) v c2 := by
      rw [← e1]; exact dni_mem_of _ hLkinv hw
    rw [hf2 w hw2, hxy, dniEquiv_prk]
    refine congrArg (fun t => ((k : ℤ) : (D.mem u).A.Fv v) • x (T.lv0.prk v c t)) (Subtype.ext ?_)
    show (γd : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ (γ2.1.1 *ᵥ w.1) = (g' : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ w.1
    rw [hg', Units.val_mul, Matrix.mulVec_mulVec]
  have hPc := dnk_latP_smul T v c c1 c3 x ((k : ℤ) : (D.mem u).A.Fv v) hμ γ.1 g' hl1 hf1 hl' hf'
  set Γ : GL (Fin (D.R.N 0)) D.host.E := γ2.1⁻¹ * γd⁻¹ * γ.1 with hΓdef
  have hPΓ : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat (Γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (clsCrd D u 0 (Nat.zero_le _) c1)) = Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c3) := by
    have e2 : (γ.1⁻¹ * g')⁻¹ = Γ := by rw [hg', hΓdef]; group
    have := localization_inv_smul_eq _ (γ.1⁻¹ * g') hPc
    rwa [e2] at this
  have hPdΓ : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat (Γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (Ld D u 0 (Nat.zero_le _) c1)) = Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (Ld D u 0 (Nat.zero_le _) c3) := by
    have e3 : g'⁻¹ * γ.1 = Γ := by rw [hg', hΓdef]; group
    have := localization_smul_cancel _ g' γ.1 (hl1.trans hl'.symm)
    rwa [e3] at this
  have hΓU : Γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)) := mul_mem (mul_mem (inv_mem γ2.2) (inv_mem hγd)) γ.2
  have hQd : Formalism.HermitianLatticesTheory.localization₂ (rlvQ T.atT v) (mulLat (Γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (Ld D u 0 (Nat.zero_le _) c1)) =
      Formalism.HermitianLatticesTheory.localization₂ (rlvQ T.atT v) (Ld D u 0 (Nat.zero_le _) c3) :=
    local_dual_Q_eq_of_P T.atT v c3 c1 Γ hΓU hPΓ
  have eΓ : ∀ z, (g' : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ ((Γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ z) = γ.1.1 *ᵥ z := by
    intro z
    have e4 : g' * Γ = γ.1 := by rw [hg', hΓdef]; group
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, e4]
  have hFc : ∀ z (hz : z ∈ Ld D u 0 (Nat.zero_le _) c1), ∃ r : 𝓞 D.host.F, r ∉ (T.atT.eV v).1.asIdeal ∧
      ∃ h : (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r) • ((Γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ z) ∈ Ld D u 0 (Nat.zero_le _) c3,
        (D.fm u).fv 0 v c3 (T.lv0.pr v c3 ⟨_, h⟩) =
          ((k : ℤ) : (D.mem u).A.Fv v) • (D.fm u).fv 0 v c1 (T.lv0.pr v c1 ⟨(algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r) • z, Submodule.smul_mem _ _ hz⟩) := by
    intro z hz
    obtain ⟨b, hbP, hbQ, hb⟩ := rlv_two (T.atT.Pv v) (rlvQ T.atT v) hPdΓ.le hQd.le
      (x := (Γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ z) ⟨z, hz, rfl⟩
    obtain ⟨r, hr, b', hb'⟩ := rlv_norm T.atT v b hbP hbQ
    have hmem : (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r) • ((Γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ z) ∈ Ld D u 0 (Nat.zero_le _) c3 := by
      rw [hb', mul_smul]; exact Submodule.smul_mem _ _ hb
    refine ⟨r, hr, hmem, ?_⟩
    have hγz : γ.1.1 *ᵥ z ∈ Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c) := by
      rw [← hl1]; exact mem_localization_of_mem₂ _ ⟨z, hz, rfl⟩
    obtain ⟨s, hs, hsz⟩ := (rlv_mem_locP _ _ _).1 hγz
    set R := (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r) with hR
    have e4 : (g' : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ (s • (R • ((Γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ z))) = R • (s • (γ.1.1 *ᵥ z)) := by
      rw [Matrix.mulVec_smul, Matrix.mulVec_smul, eΓ, smul_comm]
    have e5 : γ.1.1 *ᵥ (s • (R • z)) = R • (s • (γ.1.1 *ᵥ z)) := by
      rw [Matrix.mulVec_smul, Matrix.mulVec_smul, smul_comm]
    have hin : R • (s • (γ.1.1 *ᵥ z)) ∈ Lk T.atT 0 (Nat.zero_le _) v c := Submodule.mem_sup_left (Submodule.smul_mem _ R hsz)
    have hRz : R • z ∈ Ld D u 0 (Nat.zero_le _) c1 := Submodule.smul_mem _ _ hz
    obtain ⟨w3, hw3def⟩ : ∃ w3 : ↥(Ld D u 0 (Nat.zero_le _) c3), w3.1 = s • (R • ((Γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ z)) :=
      ⟨s • (⟨_, hmem⟩ : ↥(Ld D u 0 (Nat.zero_le _) c3)), rfl⟩
    obtain ⟨w1, hw1def⟩ : ∃ w1 : ↥(Ld D u 0 (Nat.zero_le _) c1), w1.1 = s • (R • z) :=
      ⟨s • (⟨R • z, hRz⟩ : ↥(Ld D u 0 (Nat.zero_le _) c1)), rfl⟩
    have hw3 : (g' : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ w3.1 ∈ Lk T.atT 0 (Nat.zero_le _) v c := by rw [hw3def, e4]; exact hin
    have hw1 : γ.1.1 *ᵥ w1.1 ∈ Lk T.atT 0 (Nat.zero_le _) v c := by rw [hw1def, e5]; exact hin
    have hA := hf' w3 hw3
    have hB := hf1 w1 hw1
    have ew3 : w3 = s • (⟨_, hmem⟩ : ↥(Ld D u 0 (Nat.zero_le _) c3)) := Subtype.ext hw3def
    have ew1 : w1 = s • (⟨R • z, hRz⟩ : ↥(Ld D u 0 (Nat.zero_le _) c1)) := Subtype.ext hw1def
    have pA : T.lv0.pr v c3 w3 = T.atT.res v s • T.lv0.pr v c3 ⟨_, hmem⟩ := by rw [ew3, T.lv0.pr_smul]
    have pB : T.lv0.pr v c1 w1 = T.atT.res v s • T.lv0.pr v c1 ⟨R • z, hRz⟩ := by rw [ew1, T.lv0.pr_smul]
    rw [pA, map_smul] at hA
    rw [pB, map_smul] at hB
    have hres : T.atT.res v s ≠ 0 := fun h0 => hs (RingHom.mem_ker.2 h0)
    have key : T.atT.res v s • (D.fm u).fv 0 v c3 (T.lv0.pr v c3 ⟨_, hmem⟩) =
        T.atT.res v s • (((k : ℤ) : (D.mem u).A.Fv v) • (D.fm u).fv 0 v c1 (T.lv0.pr v c1 ⟨R • z, hRz⟩)) := by
      rw [smul_comm (T.atT.res v s) ((k : ℤ) : (D.mem u).A.Fv v), hB]
      refine hA.trans ?_
      refine congrArg (fun t => ((k : ℤ) : (D.mem u).A.Fv v) • x (T.lv0.prk v c t)) (Subtype.ext ?_)
      show (g' : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ w3.1 = γ.1.1 *ᵥ w1.1
      rw [hw3def, hw1def, e4, e5]
    exact smul_right_injective _ hres key
  have eΓ2 : γ2.1⁻¹ * 1⁻¹ * (γd⁻¹ * γ.1 * γe) = Γ * γe := by rw [hΓdef]; group
  have hΓ2 : γ2.1⁻¹ * 1⁻¹ * (γd⁻¹ * γ.1 * γe) ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)) := by rw [eΓ2]; exact mul_mem hΓU hγe
  have hP2 : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat ((γ2.1⁻¹ * 1⁻¹ * (γd⁻¹ * γ.1 * γe) : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (clsCrd D u 0 (Nat.zero_le _) c1')) =
      Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c3) := by
    rw [eΓ2, Units.val_mul, rlv_mulLat_mul, hLc1]; exact hPΓ
  have hPd2 : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat ((γ2.1⁻¹ * 1⁻¹ * (γd⁻¹ * γ.1 * γe) : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (Ld D u 0 (Nat.zero_le _) c1')) =
      Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (Ld D u 0 (Nat.zero_le _) c3) := by
    rw [eΓ2, Units.val_mul, rlv_mulLat_mul, hLd1]; exact hPdΓ
  refine local_unitary_of_matching_zero T v c3 c1' _ hΓ2 hU hP2 hPd2 ?_
  intro z hz
  have hz1 : (γe : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ z ∈ Ld D u 0 (Nat.zero_le _) c1 := dni_mem_of _ hLd1 hz
  obtain ⟨r, hr, hmem, hval⟩ := hFc _ hz1
  have eΓz : ((γ2.1⁻¹ * 1⁻¹ * (γd⁻¹ * γ.1 * γe) : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ z = (Γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ ((γe : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ z) := by
    rw [eΓ2, Units.val_mul, Matrix.mulVec_mulVec]
  have hmem2 : (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r) • (((γ2.1⁻¹ * 1⁻¹ * (γd⁻¹ * γ.1 * γe) : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ z) ∈ Ld D u 0 (Nat.zero_le _) c3 := by
    rw [eΓz]; exact hmem
  refine ⟨r, hr, hmem2, ?_⟩
  have hRz1 : (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r) • ((γe : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ z) ∈ Ld D u 0 (Nat.zero_le _) c1 := Submodule.smul_mem _ _ hz1
  have eback : ((γe⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r) • ((γe : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ z)) = (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r) • z := by
    rw [Matrix.mulVec_smul, inv_mulVec_self]
  have hz2 : ((γe⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r) • ((γe : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ z)) ∈ Ld D u 0 (Nat.zero_le _) c1' := by
    rw [eback]; exact Submodule.smul_mem _ _ hz
  have hd := hdf _ hRz1 hz2
  rw [← Int.cast_smul_eq_zsmul ((D.mem u).A.Fv v)] at hd
  rw [pr_congr T v c3 ⟨_, hmem2⟩ ⟨_, hmem⟩ (congrArg (fun t => (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r) • t) eΓz), hval, pr_congr T v c1' ⟨(algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r) • z, Submodule.smul_mem _ _ hz⟩ ⟨_, hz2⟩ eback.symm, hd]

set_option maxHeartbeats 8000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem dn_same_one (T : Forms0 D u) (v : (D.mem u).A.vT) (a : ((D.mem u).A.Fv v)ˣ) (k : ℤ)
    (hk : (k : (D.mem u).A.Fv v) = a) (δ : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (hδ : IsDia T.cls0.lev (T.atT.eV v).1 (T.atT.eV v).2 k δ) (c c2 c1 c3 : (D.mem u).C.cls 0)
    (γd : GL (Fin (D.R.N 0)) D.host.E) (hγd : γd ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _))) (κd : T.cls0.lev.U)
    (hrel : (T.cls0.y c).1 * δ.1 = bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γd * (T.cls0.y c2).1 * κd.1)
    (hLc : mulLat (γd : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (clsCrd D u 0 (Nat.zero_le _) c2) = clsCrd D u 0 (Nat.zero_le _) c)
    (hLd : mulLat (γd : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (Ld D u 0 (Nat.zero_le _) c2) = Ld D u 0 (Nat.zero_le _) c)
    (x : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c)) (x2 : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c2))
    (hxy : ∀ w, x2 w = ((k : ℤ) : (D.mem u).A.Fv v) • x (dniEquiv T v c2 c γd hLc hLd w))
    (γ γ2 : UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _))) (η η2 : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (κ κ2 : T.cls0.lev.U)
    (hs1 : ∀ w, w ≠ (T.atT.eV v).1 → bc (prV (E := D.host.E) w) η.1 = 1)
    (hs2 : ∀ w, w ≠ (T.atT.eV v).1 → bc (prV (E := D.host.E) w) η2.1 = 1)
    (h1 : bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 * (T.cls0.y c1).1 = (T.cls0.y c).1 * η.1 * κ.1)
    (h2 : bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ2.1 * (T.cls0.y c3).1 = (T.cls0.y c2).1 * η2.1 * κ2.1)
    (hl1 : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat γ.1.1 (Ld D u 0 (Nat.zero_le _) c1)) = Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c))
    (hl2 : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat γ2.1.1 (Ld D u 0 (Nat.zero_le _) c3)) = Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c2))
    (hf1 : ∀ (w : ↥(Ld D u 0 (Nat.zero_le _) c1)) (hw : γ.1.1 *ᵥ w.1 ∈ Lk T.atT 0 (Nat.zero_le _) v c),
      (D.fm u).fv 0 v c1 (T.lv0.pr v c1 w) = x (T.lv0.prk v c ⟨_, hw⟩))
    (hf2 : ∀ (w : ↥(Ld D u 0 (Nat.zero_le _) c3)) (hw : γ2.1.1 *ᵥ w.1 ∈ Lk T.atT 0 (Nat.zero_le _) v c2),
      (D.fm u).fv 0 v c3 (T.lv0.pr v c3 w) = x2 (T.lv0.prk v c2 ⟨_, hw⟩)) :
    η2.1⁻¹ * κd.1 * (δ.1⁻¹ * η.1 * δ.1) ∈ T.cls0.lev.U := by
  classical
  have hμ : ((k : ℤ) : (D.mem u).A.Fv v) ≠ 0 := by rw [hk]; exact a.ne_zero

  have hδ' := isDia_conj T.cls0.lev (T.atT.eV v).1 (T.atT.eV v).2 hδ κ
  have hcl := T.val0.dil v a k hk c1 _ hδ'
  obtain ⟨c1', hc1'⟩ : ∃ c1', (D.fm u).dil 0 v a c1 = c1' := ⟨_, rfl⟩
  rw [hc1'] at hcl
  obtain ⟨hh, hhH, κ0, hκK, e⟩ := (DoubleCoset.eq _ _ _ _).1 hcl
  have hκ0 : κ0.1 ∈ T.cls0.lev.U := hκK
  obtain ⟨γe, hγe, hge⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hhH)
  have hx1 : (T.cls0.y c1 * conjPt T.cls0.lev δ κ).1 = bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γe * (T.cls0.y c1').1 * κ0.1 := by
    rw [e]
    simp only [Subgroup.coe_mul]
    rw [← hge]
  obtain ⟨hLc1, hLd1⟩ := diamond_lattice_transport T v k _ hδ' c1 c1' γe hγe ⟨κ0.1, hκ0⟩ hx1
  have hdf : ∀ z (hz : z ∈ Ld D u 0 (Nat.zero_le _) c1)
      (hz2 : ((γe⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ z ∈ Ld D u 0 (Nat.zero_le _) c1'),
      (D.fm u).fv 0 v c1' (T.lv0.pr v c1' ⟨_, hz2⟩) = k • (D.fm u).fv 0 v c1 (T.lv0.pr v c1 ⟨z, hz⟩) :=
    fun z hz hz2 => diaFun_same T v k _ hδ' c1 c1' γe ⟨κ0.1, hκ0⟩ hx1 z hz hz2

  have hκdU : κd.1 ∈ UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) := ((T.cls0.lev.U_eq _).1 κd.2).1
  obtain ⟨η', hη'⟩ : ∃ η' : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F), η'.1 = κd.1 * (δ.1⁻¹ * η.1 * δ.1) * κd.1⁻¹ :=
    ⟨⟨_, mul_mem (mul_mem hκdU (mul_mem (mul_mem (inv_mem δ.2) η.2) δ.2)) (inv_mem hκdU)⟩, rfl⟩
  obtain ⟨κ', hκ'⟩ : ∃ κ' : T.cls0.lev.U, κ'.1 = κd.1 * κ.1 * κ0.1⁻¹ :=
    ⟨κd * κ * (⟨κ0.1, hκ0⟩ : T.cls0.lev.U)⁻¹, rfl⟩
  have hs' : ∀ w, w ≠ (T.atT.eV v).1 → bc (prV (E := D.host.E) w) η'.1 = 1 := by
    intro w hw
    rw [hη']
    simp only [map_mul, map_inv, hs1 w hw, hδ.1 w hw, inv_one, mul_one, mul_inv_cancel]
  have ey2 : (T.cls0.y c2).1 = (bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γd)⁻¹ * ((T.cls0.y c).1 * δ.1) * κd.1⁻¹ := by
    rw [hrel]; group
  have ey1 : (T.cls0.y c1').1 = (bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γe)⁻¹ * ((T.cls0.y c1).1 * (κ.1⁻¹ * δ.1 * κ.1)) * κ0.1⁻¹ := by
    have h := hx1
    simp only [Subgroup.coe_mul, conjPt_coe] at h
    rw [h]; group
  have ey : (T.cls0.y c).1 = bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 * (T.cls0.y c1).1 * κ.1⁻¹ * η.1⁻¹ := by
    rw [h1]; group
  have h1' : bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (γd⁻¹ * γ.1 * γe) * (T.cls0.y c1').1 = (T.cls0.y c2).1 * η'.1 * κ'.1 := by
    rw [hη', hκ', ey1, ey2, ey]
    simp only [map_mul, map_inv]
    group
  have h3 : (T.cls0.y c2).1 * (1 : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)).1 = bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (1 : GL (Fin (D.R.N 0)) D.host.E) * (T.cls0.y c2).1 * (1 : T.cls0.lev.U).1 := by
    simp only [OneMemClass.coe_one, map_one, one_mul, mul_one]
  have hU := matching_unitary_eq T.cls0 c2 c1' c2 c3 (γd⁻¹ * γ.1 * γe) γ2.1 1 η' η2 1 κ' κ2 1 h1' h2 h3
  have hloc := dn_same_loc T v k hμ c c2 c1 c3 c1' γd hγd hLc hLd x x2 hxy γ γ2 hl1 hl2 hf1 hf2 γe hγe hLc1 hLd1 hdf hU
  have hm := matching_move_mem_level_zero T v c2 c1' c2 c3 (γd⁻¹ * γ.1 * γe) γ2.1 1 η' η2 1 κ' κ2 1 hs' hs2
    (by simp only [OneMemClass.coe_one, map_one]) h1' h2 h3 hloc
  have e2 : η2.1⁻¹ * κd.1 * (δ.1⁻¹ * η.1 * δ.1) = (η2.1⁻¹ * (1 : T.cls0.lev.U).1 * η'.1) * κd.1 := by
    rw [hη', OneMemClass.coe_one]; group
  rw [e2]
  exact mul_mem hm κd.2

set_option maxHeartbeats 8000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem dnDiaSame0F_holds (T : Forms0 D u) : DnDiaSame0F T := by
  intro v a k hk δ hδ c γd hγd κd hrel
  obtain ⟨hLc, hLd⟩ := diamond_lattice_transport T v k δ hδ c ((D.fm u).dil 0 v a c) γd hγd κd hrel

  obtain ⟨z, hz⟩ := dni_exists_one T v ((D.fm u).dil 0 v a c)
  have hw : (γd : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ z.1 ∈ Ld D u 0 (Nat.zero_le _) c := dni_mem_of _ hLd z.2
  have hz2 : ((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ ((γd : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ z.1) ∈ Ld D u 0 (Nat.zero_le _) ((D.fm u).dil 0 v a c) := by
    rw [inv_mulVec_self]; exact z.2
  have hdf := diaFun_same T v k δ hδ c _ γd κd hrel _ hw hz2
  rw [pr_congr T v _ ⟨_, hz2⟩ z (inv_mulVec_self γd z.1), hz] at hdf
  set φ : (D.fm u).lk 0 v ((D.fm u).dil 0 v a c) ≃ₗ[(D.mem u).A.Fv v] (D.fm u).lk 0 v c :=
    (dniEquiv T v ((D.fm u).dil 0 v a c) c γd hLc hLd).trans (LinearEquiv.smulOfUnit a) with hφdef
  have hφ : ∀ w, φ w = ((k : ℤ) : (D.mem u).A.Fv v) • dniEquiv T v ((D.fm u).dil 0 v a c) c γd hLc hLd w := by
    intro w; rw [hk]; rfl
  have h1 : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • z.1 ∈ Lk T.atT 0 (Nat.zero_le _) v ((D.fm u).dil 0 v a c) :=
    Submodule.mem_sup_left (dnk_tld T _ z.1 z.2)
  have hTw : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • ((γd : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ z.1) ∈ Lk T.atT 0 (Nat.zero_le _) v c :=
    Submodule.mem_sup_left (dnk_tld T c _ hw)
  have hkw : (D.fm u).fv 0 v c (T.lv0.pr v c (k • (⟨_, hw⟩ : ↥(Ld D u 0 (Nat.zero_le _) c)))) = 1 := by
    rw [map_zsmul, map_zsmul]; exact hdf.symm
  have hTkw : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (k • (⟨_, hw⟩ : ↥(Ld D u 0 (Nat.zero_le _) c))).1 ∈
      Lk T.atT 0 (Nat.zero_le _) v c :=
    Submodule.mem_sup_left (dnk_tld T c _ (k • (⟨_, hw⟩ : ↥(Ld D u 0 (Nat.zero_le _) c))).2)
  have hte : φ ((D.fm u).te 0 v ((D.fm u).dil 0 v a c)) = (D.fm u).te 0 v c := by
    rw [← T.lv0.te v _ z hz h1, ← T.lv0.te v c _ hkw hTkw, hφ, dniEquiv_prk]
    have e : (⟨(((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (k • (⟨_, hw⟩ : ↥(Ld D u 0 (Nat.zero_le _) c))).1, hTkw⟩ :
        ↥(Lk T.atT 0 (Nat.zero_le _) v c)) = k • (⟨_, hTw⟩ : ↥(Lk T.atT 0 (Nat.zero_le _) v c)) := by
      apply Subtype.ext
      show (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (k • ((γd : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ z.1)) =
        k • ((((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • ((γd : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ z.1))
      exact smul_comm _ _ _
    rw [e, map_zsmul, ← Int.cast_smul_eq_zsmul ((D.mem u).A.Fv v)]
    refine congrArg (fun t => ((k : ℤ) : (D.mem u).A.Fv v) • T.lv0.prk v c t) (Subtype.ext ?_)
    show (γd : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ ((((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • z.1) =
      (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • ((γd : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ z.1)
    exact Matrix.mulVec_smul _ _ _
  have hne0 : ∀ {c0 : (D.mem u).C.cls 0} (x : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c0)),
      x ((D.fm u).te 0 v c0) = 1 → x ≠ 0 := by
    intro c0 x hx h0
    rw [h0, LinearMap.zero_apply] at hx
    exact zero_ne_one hx
  choose γ1 η1 κ1 hs1 hr1 hl1 hf1 ht1 using fun x : {x : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c) //
    x ((D.fm u).te 0 v c) = 1} => T.down_natural_level_zero v c x.1 (hne0 x.1 x.2)
  choose γ2 η2 κ2 hs2 hr2 hl2 hf2 ht2 using fun x : {x : Module.Dual ((D.mem u).A.Fv v)
    ((D.fm u).lk 0 v ((D.fm u).dil 0 v a c)) // x ((D.fm u).te 0 v ((D.fm u).dil 0 v a c)) = 1} =>
    T.down_natural_level_zero v ((D.fm u).dil 0 v a c) x.1 (hne0 x.1 x.2)
  refine ⟨dualSigma φ _ _ hte, η1, η2,
    fun x => ⟨γ1 x, κ1 x, hs1 x, hr1 x, fun h => ?_⟩, fun x => ⟨γ2 x, κ2 x, hs2 x, hr2 x, fun h => ?_⟩, fun x => ?_⟩
  · funext s
    rw [ht1 x h s _ (is_translate_inverse T (γ1 x) s), Units.val_inv_eq_inv_val]
    rfl
  · funext s
    rw [ht2 x h s _ (is_translate_inverse T (γ2 x) s), Units.val_inv_eq_inv_val]
    rfl
  · exact dn_same_one T v a k hk δ hδ c _ _ _ γd hγd κd hrel hLc hLd x.1 _
      (fun w => by rw [dualSigma_apply, hφ, map_smul]) (γ1 x) (γ2 _) (η1 x) (η2 _) (κ1 x) (κ2 _) (hs1 x) (hs2 _)
      (hr1 x) (hr2 _) (hl1 x) (hl2 _) (hf1 x) (hf2 _)

theorem dnSameAll_holds : DnSameAll := fun _ _ T => dnDiaSame0F_holds T

end SameDiaZero

end
