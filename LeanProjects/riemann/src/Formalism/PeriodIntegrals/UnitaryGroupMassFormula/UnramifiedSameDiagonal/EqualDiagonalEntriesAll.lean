import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnramifiedSameDiagonal.MatchGen
import Formalism.LocalToGlobal.GlobalTheory.UnramifiedDiagonal.DiaFun
import Formalism.LocalToGlobal.GlobalTheory.UnramifiedDiagonal.DiaConj
import Formalism.LocalToGlobal.GlobalTheory.UnramifiedDiagonal.HeckeRamifiedZeroOfMatchingsAndDu

noncomputable section

namespace SameDiaZero

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.LocalLatticeBases Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0 Formalism.UG
open NumberField IsDedekindDomain Matrix CrossDiaZero

variable {D : D7} {u : D.what₂.Word}

theorem mulLat_one_GL {n : ℕ} (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) :
    mulLat ((1 : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) L = L := by
  unfold mulLat
  simp

set_option maxHeartbeats 8000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem eSame_one (T : Forms0 D u) (v : (D.mem u).A.vT) (a : ((D.mem u).A.Fv v)ˣ) (k : ℤ)
    (hk : (k : (D.mem u).A.Fv v) = a) (δ : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (hδ : IsDia T.cls0.lev (T.atT.eV v).1 (T.atT.eV v).2 k δ) (c c1 c3 : (D.mem u).C.cls 0)
    (g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c))
    (γ γ2 : UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _))) (η η2 : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (κ κ2 : T.cls0.lev.U)
    (h1 : ∀ v', v' ≠ (T.atT.eV v).1 → bc (prV (E := D.host.E) v') η.1 = 1)
    (h2 : bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 * (T.cls0.y c1).1 = (T.cls0.y c).1 * η.1 * κ.1)
    (hl : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat γ.1.1 (Ld D u 0 (Nat.zero_le _) c1)) = Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c))
    (hf : ∀ (w : ↥(Ld D u 0 (Nat.zero_le _) c1)) (hw : γ.1.1 *ᵥ w.1 ∈ Lk T.atT 0 (Nat.zero_le _) v c),
      (D.fm u).fv 0 v c1 (T.lv0.pr v c1 w) = g (T.lv0.prk v c ⟨_, hw⟩))
    (g1 : ∀ v', v' ≠ (T.atT.eV v).1 → bc (prV (E := D.host.E) v') η2.1 = 1)
    (g2 : bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ2.1 * (T.cls0.y c3).1 = (T.cls0.y c).1 * η2.1 * κ2.1)
    (gl : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat γ2.1.1 (Ld D u 0 (Nat.zero_le _) c3)) = Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c))
    (gf : ∀ (w : ↥(Ld D u 0 (Nat.zero_le _) c3)) (hw : γ2.1.1 *ᵥ w.1 ∈ Lk T.atT 0 (Nat.zero_le _) v c),
      (D.fm u).fv 0 v c3 (T.lv0.pr v c3 w) = ((a : (D.mem u).A.Fv v) • g) (T.lv0.prk v c ⟨_, hw⟩)) :
    η2.1⁻¹ * (η.1 * δ.1) ∈ T.cls0.lev.U := by

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

  obtain ⟨ε, hε1⟩ : ∃ ε : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F), ε.1 = η.1 * δ.1 := ⟨η * δ, rfl⟩
  obtain ⟨κε, hκε⟩ : ∃ κε : T.cls0.lev.U, κε.1 = κ.1 * κ0.1⁻¹ := ⟨⟨_, mul_mem κ.2 (inv_mem hκ0)⟩, rfl⟩
  obtain ⟨γε, hγε⟩ : ∃ γε : UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)), γε.1 = γ.1 * γ' := ⟨⟨_, mul_mem γ.2 hγ'⟩, rfl⟩
  have hε : ∀ v', v' ≠ (T.atT.eV v).1 → bc (prV (E := D.host.E) v') ε.1 = 1 := by
    intro v' hv'
    rw [hε1, map_mul, h1 v' hv', hδ.1 v' hv', one_mul]
  have h1ε : bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γε.1 * (T.cls0.y c1').1 = (T.cls0.y c).1 * ε.1 * κε.1 := by
    have eγ : bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 = (T.cls0.y c).1 * η.1 * κ.1 * (T.cls0.y c1).1⁻¹ := by rw [← h2]; group
    have hx1' : (T.cls0.y c1).1 * (κ.1⁻¹ * δ.1 * κ.1) = bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ' * (T.cls0.y c1').1 * κ0.1 := hx1
    have eγ' : bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ' = (T.cls0.y c1).1 * (κ.1⁻¹ * δ.1 * κ.1) * κ0.1⁻¹ * (T.cls0.y c1').1⁻¹ := by
      rw [hx1']; group
    rw [hγε, hε1, hκε, map_mul, eγ, eγ']
    group
  have hlε : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat γε.1.1 (Ld D u 0 (Nat.zero_le _) c1')) = Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c) := by
    rw [hγε, Units.val_mul]
    exact rlv_chainP _ _ _ hl (by rw [hLat1.2])
  have hfε : ∀ (w : ↥(Ld D u 0 (Nat.zero_le _) c1')) (hw : γε.1.1 *ᵥ w.1 ∈ Lk T.atT 0 (Nat.zero_le _) v c),
      (D.fm u).fv 0 v c1' (T.lv0.pr v c1' w) = ((a : (D.mem u).A.Fv v) • g) (T.lv0.prk v c ⟨_, hw⟩) := by
    intro w hw
    have hw1 : (γ' : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ w.1 ∈ Ld D u 0 (Nat.zero_le _) c1 := by rw [← hLat1.2]; exact ⟨w.1, w.2, rfl⟩
    have eback : ((γ'⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ ((γ' : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ w.1) = w.1 := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
    have hz2 : ((γ'⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ ((γ' : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ w.1) ∈ Ld D u 0 (Nat.zero_le _) c1' := by rw [eback]; exact w.2
    have ew : γε.1.1 *ᵥ w.1 = γ.1.1 *ᵥ ((γ' : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ w.1) := by
      rw [hγε, Units.val_mul, Matrix.mulVec_mulVec]
    have hw' : γ.1.1 *ᵥ (⟨_, hw1⟩ : ↥(Ld D u 0 (Nat.zero_le _) c1)).1 ∈ Lk T.atT 0 (Nat.zero_le _) v c := by
      show γ.1.1 *ᵥ ((γ' : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ w.1) ∈ _
      rw [← ew]; exact hw
    have d := Formalism.L2.GlobalTheoryTheory.UnramifiedDiagonal.diaFun_same T v k _ hδ' c1 c1' γ' ⟨κ0.1, hκ0⟩ hx1 _ hw1 hz2
    rw [pr_congr T v c1' w ⟨_, hz2⟩ eback.symm, d, hf ⟨_, hw1⟩ hw', LinearMap.smul_apply, zsmul_eq_mul, hk,
      smul_eq_mul]
    have ep : T.lv0.prk v c ⟨_, hw'⟩ = T.lv0.prk v c ⟨_, hw⟩ := congrArg (T.lv0.prk v c) (Subtype.ext ew.symm)
    rw [ep]

  have hL1 := mulLat_one_GL (D := D) (clsCrd D u 0 (Nat.zero_le _) c)
  have hLd1 := mulLat_one_GL (D := D) (Ld D u 0 (Nat.zero_le _) c)
  have hxy : ∀ w, ((a : (D.mem u).A.Fv v) • g) w = ((a : (D.mem u).A.Fv v) • g) (dniEquiv T v c c 1 hL1 hLd1 w) := by
    intro w
    obtain ⟨z, rfl⟩ := T.lv0.prk_surj v c w
    rw [dniEquiv_prk]
    congr 2
    apply Subtype.ext
    show z.1 = ((1 : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ z.1
    rw [Units.val_one, Matrix.one_mulVec]
  have htriv : (T.cls0.y c).1 * (1 : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)).1 = bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (1 : GL (Fin (D.R.N 0)) D.host.E) * (T.cls0.y c).1 * (1 : T.cls0.lev.U).1 := by
    simp only [OneMemClass.coe_one, map_one, mul_one, one_mul]
  have hm := dn_match_gen T v 1 (by simp only [OneMemClass.coe_one, map_one]) c c c1' c3 1 (one_mem _) 1 htriv
    hL1 hLd1 ((a : (D.mem u).A.Fv v) • g) ((a : (D.mem u).A.Fv v) • g) hxy γε γ2 ε η2 κε κ2 hε g1 h1ε g2 hlε gl hfε gf
  have efin : η2.1⁻¹ * (η.1 * δ.1) = η2.1⁻¹ * (1 : T.cls0.lev.U).1 * ε.1 := by
    rw [hε1, OneMemClass.coe_one, mul_one]
  rw [efin]
  exact hm

set_option maxHeartbeats 8000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem eSame (T : Forms0 D u) : Formalism.L2.GlobalTheoryTheory.UnramifiedDiagonal.EDiaSame0F T := by
  intro v a k hk δ hδ c
  classical
  choose γ1 η1 κ1 hs1 hr1 hl1 hf1 ht1 using fun x : {x : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c) // x ≠ 0} => T.down_natural_level_zero v c x.1 x.2
  let σ : {x : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c) // x ≠ 0} ≃ {x : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c) // x ≠ 0} :=
    { toFun := fun x => ⟨(a : (D.mem u).A.Fv v) • x.1, smul_ne_zero (Units.ne_zero a) x.2⟩
      invFun := fun x => ⟨((a⁻¹ : ((D.mem u).A.Fv v)ˣ) : (D.mem u).A.Fv v) • x.1, smul_ne_zero (Units.ne_zero _) x.2⟩
      left_inv := fun x => Subtype.ext (by
        show ((a⁻¹ : ((D.mem u).A.Fv v)ˣ) : (D.mem u).A.Fv v) • ((a : (D.mem u).A.Fv v) • x.1) = x.1
        rw [smul_smul, Units.inv_mul, one_smul])
      right_inv := fun x => Subtype.ext (by
        show (a : (D.mem u).A.Fv v) • (((a⁻¹ : ((D.mem u).A.Fv v)ˣ) : (D.mem u).A.Fv v) • x.1) = x.1
        rw [smul_smul, Units.mul_inv, one_smul]) }
  refine ⟨σ, η1, fun x => ⟨γ1 x, κ1 x, hs1 x, hr1 x, fun h => ?_⟩, fun x => ?_⟩
  · funext s
    rw [ht1 x h s _ (is_translate_inverse T (γ1 x) s), Units.val_inv_eq_inv_val]
    rfl
  · exact eSame_one T v a k hk δ hδ c _ _ x.1 (γ1 x) (γ1 (σ x)) (η1 x) (η1 (σ x)) (κ1 x) (κ1 (σ x))
      (hs1 x) (hr1 x) (hl1 x) (hf1 x) (hs1 (σ x)) (hr1 (σ x)) (hl1 (σ x)) (hf1 (σ x))

theorem equal_diagonal_entries_all : Formalism.L2.GlobalTheoryTheory.UnramifiedDiagonal.ESameAll := fun _ _ T => eSame T

end SameDiaZero

end
