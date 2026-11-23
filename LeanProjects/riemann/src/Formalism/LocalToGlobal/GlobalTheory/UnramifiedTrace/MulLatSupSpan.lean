import Formalism.LocalToGlobal.GlobalTheory.UnramifiedTrace.TripMem
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnramifiedSameDiagonal.SameCommon

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.UnramifiedTrace

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.LocalLatticeBases Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0 NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct Classical

theorem localization_sup_congr {R W : Type} [CommRing R] [AddCommGroup W] [Module R W] (P : Ideal R) [P.IsPrime]
    {X Y : Submodule R W} (S : Submodule R W) (h : Formalism.HermitianLatticesTheory.localization₂ P X = Formalism.HermitianLatticesTheory.localization₂ P Y) :
    Formalism.HermitianLatticesTheory.localization₂ P (X ⊔ S) = Formalism.HermitianLatticesTheory.localization₂ P (Y ⊔ S) := by
  have key : ∀ {X Y : Submodule R W}, Formalism.HermitianLatticesTheory.localization₂ P X = Formalism.HermitianLatticesTheory.localization₂ P Y →
      Formalism.HermitianLatticesTheory.localization₂ P (X ⊔ S) ≤ Formalism.HermitianLatticesTheory.localization₂ P (Y ⊔ S) := by
    intro X Y h x hx
    obtain ⟨s, hs, hsx⟩ := hx
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 hsx
    have ha0 : a ∈ Formalism.HermitianLatticesTheory.localization₂ P X := ⟨1, P.primeCompl.one_mem, by simpa using ha⟩
    rw [h] at ha0
    obtain ⟨t, ht, hta⟩ := ha0
    refine ⟨t * s, P.primeCompl.mul_mem ht hs, ?_⟩
    rw [mul_smul, ← hab, smul_add]
    exact Submodule.add_mem_sup hta (S.smul_mem t hb)
  exact le_antisymm (key h) (key h.symm)

theorem mulLat_sup_span {E : Type} [Field E] [NumberField E] {n : ℕ} (g : Matrix (Fin n) (Fin n) E)
    (L : Submodule (𝓞 E) (Fin n → E)) (y : Fin n → E) :
    mulLat g (L ⊔ Submodule.span (𝓞 E) {y}) = mulLat g L ⊔ Submodule.span (𝓞 E) {g *ᵥ y} := by
  unfold mulLat
  rw [Submodule.map_sup, Submodule.map_span, Set.image_singleton]
  rfl

variable {D : D7} {u : D.what₂.Word}

def IsCompMv (T : Forms0 D u) (v : (D.mem u).A.vT) (c c1 : (D.mem u).C.cls 0) (w : Fin (D.R.N 0) → D.host.E)
    (g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c))
    (Γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)))
    (h : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (k : T.cls0.lev.U) : Prop :=
  (∀ v', v' ≠ (T.atT.eV v).1 → bc (prV (E := D.host.E) v') h.1 = 1) ∧
  bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) Γ.1 * (T.cls0.y c1).1 = (T.cls0.y c).1 * h.1 * k.1 ∧
  Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat Γ.1.1 (clsCrd D u 0 (Nat.zero_le _) c1)) =
    Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c) ∧
  Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat Γ.1.1 (Ld D u 0 (Nat.zero_le _) c1)) =
    Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c ⊔
      Submodule.span (𝓞 D.host.E) {(((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • w}) ∧
  ∀ (x : ↥(Ld D u 0 (Nat.zero_le _) c1))
    (hx : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (Γ.1.1 *ᵥ x.1) ∈ Lk T.atT 0 (Nat.zero_le _) v c),
    (D.fm u).fv 0 v c1 (T.lv0.pr v c1 x) = g (T.lv0.prk v c ⟨_, hx⟩)

set_option maxHeartbeats 8000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem comp_of_moves (T : Forms0 D u) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls 0)
    (g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c))
    (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)))
    (η : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (κ : T.cls0.lev.U)
    (d1 : ∀ v', v' ≠ (T.atT.eV v).1 → bc (prV (E := D.host.E) v') η.1 = 1)
    (d2 : bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 *
      (T.cls0.y ((D.fm u).dn 0 v c g)).1 = (T.cls0.y c).1 * η.1 * κ.1)
    (d3 : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat γ.1.1 (Ld D u 0 (Nat.zero_le _) ((D.fm u).dn 0 v c g))) =
      Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c))
    (d4 : ∀ (x : ↥(Ld D u 0 (Nat.zero_le _) ((D.fm u).dn 0 v c g))) (hx : γ.1.1 *ᵥ x.1 ∈ Lk T.atT 0 (Nat.zero_le _) v c),
      (D.fm u).fv 0 v _ (T.lv0.pr v _ x) = g (T.lv0.prk v c ⟨_, hx⟩))
    (z : ↥(Ld D u 0 (Nat.zero_le _) ((D.fm u).dn 0 v c g)))
    (γ' : UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)))
    (η' : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (κ' : T.cls0.lev.U)
    (u1 : ∀ v', v' ≠ (T.atT.eV v).1 → bc (prV (E := D.host.E) v') η'.1 = 1)
    (u2 : bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ'.1 *
      (T.cls0.y ((D.fm u).up 0 v ((D.fm u).dn 0 v c g) (T.lv0.pr v _ z))).1 =
        (T.cls0.y ((D.fm u).dn 0 v c g)).1 * η'.1 * κ'.1)
    (u3 : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat γ'.1.1 (clsCrd D u 0 (Nat.zero_le _)
        ((D.fm u).up 0 v ((D.fm u).dn 0 v c g) (T.lv0.pr v _ z)))) =
      Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (Ld D u 0 (Nat.zero_le _) ((D.fm u).dn 0 v c g)))
    (u4 : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat γ'.1.1 (Ld D u 0 (Nat.zero_le _)
        ((D.fm u).up 0 v ((D.fm u).dn 0 v c g) (T.lv0.pr v _ z)))) =
      Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (Ld D u 0 (Nat.zero_le _) ((D.fm u).dn 0 v c g) ⊔
        Submodule.span (𝓞 D.host.E) {(((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • z.1}))
    (u5 : ∀ (x : ↥(Ld D u 0 (Nat.zero_le _) ((D.fm u).up 0 v ((D.fm u).dn 0 v c g) (T.lv0.pr v _ z))))
      (hx : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (γ'.1.1 *ᵥ x.1) ∈ Ld D u 0 (Nat.zero_le _) ((D.fm u).dn 0 v c g)),
      (D.fm u).fv 0 v _ (T.lv0.pr v _ x) = (D.fm u).fv 0 v _ (T.lv0.pr v _ ⟨_, hx⟩)) :
    IsCompMv T v c ((D.fm u).up 0 v ((D.fm u).dn 0 v c g) (T.lv0.pr v _ z)) (γ.1.1 *ᵥ z.1) g (γ * γ')
      (hcomp T η κ η') (κ * κ') := by
  have eM : ((γ * γ').1.1 : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) = γ.1.1 * γ'.1.1 := by
    simp only [Subgroup.coe_mul, Units.val_mul]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro v' hv'
    simp only [hcomp, kU, Subgroup.coe_mul, InvMemClass.coe_inv, map_mul, map_inv, d1 v' hv', u1 v' hv', one_mul, mul_one,
      mul_inv_cancel]
  · simp only [hcomp, kU, Subgroup.coe_mul, InvMemClass.coe_inv, map_mul]
    rw [mul_assoc, u2, ← mul_assoc, ← mul_assoc, d2]
    group
  · rw [eM]
    exact rlv_chainP (T.atT.Pv v) _ _ d3 u3
  · rw [eM]
    refine rlv_chainP (T.atT.Pv v) _ _ ?_ u4
    rw [mulLat_sup_span, Matrix.mulVec_smul]
    exact localization_sup_congr _ _ d3
  · intro x hx
    have hmem : γ'.1.1 *ᵥ x.1 ∈ Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (Ld D u 0 (Nat.zero_le _) ((D.fm u).dn 0 v c g) ⊔
        Submodule.span (𝓞 D.host.E) {(((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • z.1}) := by
      rw [← u4]; exact mem_localization_of_mem₂ _ ⟨x.1, x.2, rfl⟩
    obtain ⟨t, ht, htx⟩ := (rlv_mem_locP _ _ _).1 hmem
    obtain ⟨a, ha, b, hb, e⟩ := Submodule.mem_sup.1 htx
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 hb
    have hTE : ((((D.mem u).A.T : ℕ) : 𝓞 D.host.E) : D.host.E) = (((D.mem u).A.T : ℕ) : D.host.E) := by simp
    have hTne : (((D.mem u).A.T : ℕ) : D.host.E) ≠ 0 := by
      exact_mod_cast (D.mem u).A.T_prime.ne_zero

    have e1 : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (γ'.1.1 *ᵥ (t • x).1) =
        (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • a + r • z.1 := by
      have : (t • x).1 = t • x.1 := rfl
      rw [this, Matrix.mulVec_smul, ← e, smul_add]
      congr 1
      rw [smul_comm, ← algebraMap_smul D.host.E (((D.mem u).A.T : ℕ) : 𝓞 D.host.E), ← algebraMap_smul D.host.E r,
        ← algebraMap_smul D.host.E r, smul_smul, smul_smul]
      congr 1
      simp only [map_natCast]
      field_simp
    have hin : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (γ'.1.1 *ᵥ (t • x).1) ∈ Ld D u 0 (Nat.zero_le _) ((D.fm u).dn 0 v c g) := by
      rw [e1]
      exact add_mem (Submodule.smul_mem _ _ ha) (Submodule.smul_mem _ _ z.2)
    have e2 : γ.1.1 *ᵥ ((((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (γ'.1.1 *ᵥ (t • x).1)) =
        t • ((((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • ((γ * γ').1.1 *ᵥ x.1)) := by
      have : (t • x).1 = t • x.1 := rfl
      rw [this, eM, Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_mulVec, smul_comm]
    have hin2 : γ.1.1 *ᵥ ((((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (γ'.1.1 *ᵥ (t • x).1)) ∈ Lk T.atT 0 (Nat.zero_le _) v c := by
      rw [e2]; exact Submodule.smul_mem _ _ hx
    have f1 := u5 (t • x) hin
    have f2 := d4 ⟨_, hin⟩ hin2
    have p1 : T.lv0.prk v c ⟨_, hin2⟩ = T.atT.res v t • T.lv0.prk v c ⟨_, hx⟩ := by
      rw [← T.lv0.prk_smul]
      exact congrArg _ (Subtype.ext e2)
    rw [T.lv0.pr_smul, map_smul, f2, p1, map_smul] at f1
    have hres : T.atT.res v t ≠ 0 := fun h0 => ht (RingHom.mem_ker.2 h0)
    exact smul_right_injective _ hres f1

end Formalism.L2.GlobalTheoryTheory.UnramifiedTrace

end
