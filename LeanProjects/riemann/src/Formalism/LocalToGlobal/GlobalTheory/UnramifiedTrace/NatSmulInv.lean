import Formalism.LocalToGlobal.GlobalTheory.UnramifiedTrace.TNotinSq

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.UnramifiedTrace

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.LocalLatticeBases Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0 NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct Classical

theorem nat_smul_inv {E : Type} [Field E] [NumberField E] {n : ℕ} (N : ℕ) (hN : (N : E) ≠ 0) (a : 𝓞 E) (w : Fin n → E) :
    ((N : ℕ) : 𝓞 E) • (a • (((N : ℕ) : E)⁻¹ • w)) = a • w := by
  ext i
  simp only [Pi.smul_apply, smul_eq_mul]
  simp only [Algebra.smul_def, map_natCast]
  rw [mul_left_comm, mul_inv_cancel_left₀ hN]

variable {D : D7} {u : D.what₂.Word}

set_option maxHeartbeats 16000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem comp_cmp (T : Forms0 D u) (v : (D.mem u).A.vT) (c c1 c3 : (D.mem u).C.cls 0)
    (w1 w3 : Fin (D.R.N 0) → D.host.E)
    (g1 g3 : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c))
    (Γ1 Γ3 : UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)))
    (h1 h3 : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (k1 k3 : T.cls0.lev.U)
    (H1 : IsCompMv T v c c1 w1 g1 Γ1 h1 k1) (H3 : IsCompMv T v c c3 w3 g3 Γ3 h3 k3)
    (hw : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c ⊔
        Submodule.span (𝓞 D.host.E) {(((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • w1}) =
      Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c ⊔
        Submodule.span (𝓞 D.host.E) {(((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • w3}))
    (hw1 : w1 ∈ Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c))
    (hg : ∀ l ∈ clsCrd D u 0 (Nat.zero_le _) c, ∀ (e : 𝓞 D.host.E)
      (hY : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • l + e • w1 ∈ Lk T.atT 0 (Nat.zero_le _) v c),
      g1 (T.lv0.prk v c ⟨_, hY⟩) = g3 (T.lv0.prk v c ⟨_, hY⟩)) :
    h3.1⁻¹ * h1.1 ∈ T.cls0.lev.U := by
  obtain ⟨s1, e1, p1, d1, f1⟩ := H1
  obtain ⟨s3, e3, p3, d3, f3⟩ := H3
  have hTne : (((D.mem u).A.T : ℕ) : D.host.E) ≠ 0 := by exact_mod_cast (D.mem u).A.T_prime.ne_zero
  have eM : ((Γ3.1⁻¹ * Γ1.1 : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) =
      ((Γ3.1⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) * Γ1.1.1 := Units.val_mul _ _
  have hP : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat ((Γ3.1⁻¹ * Γ1.1 : GL (Fin (D.R.N 0)) D.host.E) : Matrix _ _ D.host.E)
      (clsCrd D u 0 (Nat.zero_le _) c1)) = Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c3) := by
    rw [eM]
    exact rlv_chainP (T.atT.Pv v) _ _ (CrossDiaZero.use₄ (T.atT.Pv v) Γ3.1 p3) p1
  have hPd : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat ((Γ3.1⁻¹ * Γ1.1 : GL (Fin (D.R.N 0)) D.host.E) : Matrix _ _ D.host.E)
      (Ld D u 0 (Nat.zero_le _) c1)) = Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (Ld D u 0 (Nat.zero_le _) c3) := by
    rw [eM]
    exact rlv_chainP (T.atT.Pv v) _ _ (CrossDiaZero.use₄ (T.atT.Pv v) Γ3.1 d3) (d1.trans hw)
  have hΓU : Γ3.1⁻¹ * Γ1.1 ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)) :=
    mul_mem (inv_mem Γ3.2) Γ1.2
  have hQd := local_dual_Q_eq_of_P T.atT v c3 c1 (Γ3.1⁻¹ * Γ1.1) hΓU hP
  have eback : ∀ y : Fin (D.R.N 0) → D.host.E,
      Γ3.1.1 *ᵥ (((Γ3.1⁻¹ * Γ1.1 : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ y) =
        Γ1.1.1 *ᵥ y := by
    intro y
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel_left]
  refine trip_mem T v c c1 c3 Γ1 Γ3 h1 h3 k1 k3 s1 s3 e1 e3 hP hPd ?_
  intro z hz
  obtain ⟨b, hbP, hbQ, hb⟩ := rlv_two (T.atT.Pv v) (rlvQ T.atT v) hPd.le hQd.le
    (x := ((Γ3.1⁻¹ * Γ1.1 : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ z) ⟨z, hz, rfl⟩
  obtain ⟨r, hr, b', hb'⟩ := rlv_norm T.atT v b hbP hbQ
  set R := algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r with hR
  have hmem : R • (((Γ3.1⁻¹ * Γ1.1 : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ z) ∈
      Ld D u 0 (Nat.zero_le _) c3 := by
    rw [hb', mul_smul]; exact Submodule.smul_mem _ _ hb
  refine ⟨r, hr, hmem, ?_⟩
  have hRz : R • z ∈ Ld D u 0 (Nat.zero_le _) c1 := Submodule.smul_mem _ _ hz

  have hloc : Γ1.1.1 *ᵥ (R • z) ∈ Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c ⊔
      Submodule.span (𝓞 D.host.E) {(((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • w1}) := by
    rw [← d1]; exact mem_localization_of_mem₂ _ ⟨_, hRz, rfl⟩
  obtain ⟨t0, ht0, ht0m⟩ := (rlv_mem_locP _ _ _).1 hloc
  obtain ⟨l0, hl0, m0, hm0, em⟩ := Submodule.mem_sup.1 ht0m
  obtain ⟨e0, rfl⟩ := Submodule.mem_span_singleton.1 hm0
  obtain ⟨t1, ht1, ht1w⟩ := (rlv_mem_locP _ _ _).1 hw1
  set t := t1 * t0 with ht
  have htP : t ∉ T.atT.Pv v := fun h => (Ideal.IsPrime.mem_or_mem inferInstance h).elim ht1 ht0
  have eW : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (Γ1.1.1 *ᵥ (t • (R • z))) =
      (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (t1 • l0) + (e0 * t1) • w1 := by
    rw [Matrix.mulVec_smul, ht, mul_smul, ← em, smul_add, smul_add]
    congr 1
    rw [show t1 • (e0 • ((((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • w1)) = (t1 * e0) • ((((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • w1) from
      smul_smul _ _ _, nat_smul_inv _ hTne, mul_comm]
  have hl : t1 • l0 ∈ clsCrd D u 0 (Nat.zero_le _) c := Submodule.smul_mem _ _ hl0
  have hYL : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (t1 • l0) + (e0 * t1) • w1 ∈ clsCrd D u 0 (Nat.zero_le _) c := by
    refine add_mem (Submodule.smul_mem _ _ hl) ?_
    rw [mul_smul]; exact Submodule.smul_mem _ _ ht1w
  have hY : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (t1 • l0) + (e0 * t1) • w1 ∈ Lk T.atT 0 (Nat.zero_le _) v c :=
    Submodule.mem_sup_left hYL
  have hX1m : t • (R • z) ∈ Ld D u 0 (Nat.zero_le _) c1 := Submodule.smul_mem _ _ hRz
  have hX1 : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (Γ1.1.1 *ᵥ (⟨_, hX1m⟩ : ↥(Ld D u 0 (Nat.zero_le _) c1)).1) ∈
      Lk T.atT 0 (Nat.zero_le _) v c := by
    show (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (Γ1.1.1 *ᵥ (t • (R • z))) ∈ _
    rw [eW]; exact hY
  have hX3m : t • (R • (((Γ3.1⁻¹ * Γ1.1 : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ z)) ∈
      Ld D u 0 (Nat.zero_le _) c3 := Submodule.smul_mem _ _ hmem
  have eX3 : Γ3.1.1 *ᵥ (t • (R • (((Γ3.1⁻¹ * Γ1.1 : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ z))) =
      Γ1.1.1 *ᵥ (t • (R • z)) := by
    rw [Matrix.mulVec_smul, Matrix.mulVec_smul, eback, Matrix.mulVec_smul, Matrix.mulVec_smul]
  have hX3 : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (Γ3.1.1 *ᵥ (⟨_, hX3m⟩ : ↥(Ld D u 0 (Nat.zero_le _) c3)).1) ∈
      Lk T.atT 0 (Nat.zero_le _) v c := by
    show (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (Γ3.1.1 *ᵥ _) ∈ _
    rw [eX3]; exact hX1
  have q1 := f1 ⟨_, hX1m⟩ hX1
  have q3 := f3 ⟨_, hX3m⟩ hX3
  have qg := hg _ hl _ hY
  have k1e : T.lv0.prk v c ⟨_, hX1⟩ = T.lv0.prk v c ⟨_, hY⟩ := congrArg _ (Subtype.ext eW)
  have k3e : T.lv0.prk v c ⟨_, hX3⟩ = T.lv0.prk v c ⟨_, hY⟩ := by
    refine congrArg _ (Subtype.ext ?_)
    show (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (Γ3.1.1 *ᵥ _) = _
    rw [eX3, eW]
  rw [k1e] at q1
  rw [k3e] at q3
  have pr1 : T.lv0.pr v c1 ⟨_, hX1m⟩ = T.atT.res v t • T.lv0.pr v c1 ⟨_, Submodule.smul_mem _ _ hz⟩ :=
    T.lv0.pr_smul v c1 t ⟨_, Submodule.smul_mem _ _ hz⟩
  have pr3 : T.lv0.pr v c3 ⟨_, hX3m⟩ = T.atT.res v t • T.lv0.pr v c3 ⟨_, hmem⟩ :=
    T.lv0.pr_smul v c3 t ⟨_, hmem⟩
  rw [pr1, map_smul] at q1
  rw [pr3, map_smul] at q3
  have hres : T.atT.res v t ≠ 0 := fun h0 => htP (RingHom.mem_ker.2 h0)
  exact smul_right_injective _ hres (q3.trans (qg.symm.trans q1.symm))

end Formalism.L2.GlobalTheoryTheory.UnramifiedTrace

end
