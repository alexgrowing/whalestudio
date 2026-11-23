import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnramifiedSameDiagonal.SameCommon

noncomputable section

namespace SameDiaZero

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.LocalLatticeBases Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0 Formalism.UG
open NumberField IsDedekindDomain Matrix CrossDiaZero

variable {D : D7} {u : D.what₂.Word}

set_option maxHeartbeats 8000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem upFSame (T : Forms0 D u) (v : (D.mem u).A.vT) (k : ℤ)
    (δ : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (hδ : IsDia T.cls0.lev (T.atT.eV v).1 (T.atT.eV v).2 k δ)
    (c c1 c2 c3 : (D.mem u).C.cls 0)
    (γd : GL (Fin (D.R.N 0)) D.host.E) (hγd : γd ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)))
    (κd : T.cls0.lev.U)
    (hx : (T.cls0.y c * δ).1 = bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γd *
      (T.cls0.y c2).1 * κd.1)
    (γ γ2 : GL (Fin (D.R.N 0)) D.host.E) (hγ : γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)))
    (hγ2 : γ2 ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)))
    (z : Fin (D.R.N 0) → D.host.E) (hz : z ∈ Ld D u 0 (Nat.zero_le _) c)
    (h3 : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (clsCrd D u 0 (Nat.zero_le _) c1)) =
      Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (Ld D u 0 (Nat.zero_le _) c))
    (h4 : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (Ld D u 0 (Nat.zero_le _) c1)) =
      Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (Ld D u 0 (Nat.zero_le _) c ⊔
        Submodule.span (𝓞 D.host.E) {(((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • z}))
    (h5 : ∀ (x : ↥(Ld D u 0 (Nat.zero_le _) c1))
        (hx : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • ((γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ x.1) ∈ Ld D u 0 (Nat.zero_le _) c),
        (D.fm u).fv 0 v c1 (T.lv0.pr v c1 x) = (D.fm u).fv 0 v c (T.lv0.pr v c ⟨_, hx⟩))
    (g5 : ∀ (x : ↥(Ld D u 0 (Nat.zero_le _) c3))
        (hx : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • ((γ2 : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ x.1) ∈ Ld D u 0 (Nat.zero_le _) c2),
        (D.fm u).fv 0 v c3 (T.lv0.pr v c3 x) = (D.fm u).fv 0 v c2 (T.lv0.pr v c2 ⟨_, hx⟩))
    (hP : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat ((γ2⁻¹ * γd⁻¹ * γ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E)
        (clsCrd D u 0 (Nat.zero_le _) c1)) = Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c3))
    (hPd : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat ((γ2⁻¹ * γd⁻¹ * γ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E)
        (Ld D u 0 (Nat.zero_le _) c1)) = Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (Ld D u 0 (Nat.zero_le _) c3)) :
    ∀ w (hw : w ∈ Ld D u 0 (Nat.zero_le _) c1), ∃ a : 𝓞 D.host.F, a ∉ (T.atT.eV v).1.asIdeal ∧
      ∃ h : (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a) •
          (((γ2⁻¹ * γd⁻¹ * γ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ w) ∈
          Ld D u 0 (Nat.zero_le _) c3,
        (D.fm u).fv 0 v c3 (T.lv0.pr v c3 ⟨_, h⟩) =
          k • (D.fm u).fv 0 v c1 (T.lv0.pr v c1 ⟨(algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a) • w,
            Submodule.smul_mem _ _ hw⟩) := by
  intro w hw
  have hT0 : (((D.mem u).A.T : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (D.mem u).A.T_prime.ne_zero
  obtain ⟨hdd, hfg, hH⟩ := rlv_coordFacts (D := D) (u := u) 0 (Nat.zero_le _)
  have hLat := diamond_lattice_transport T v k δ hδ c c2 γd hγd κd hx
  have memInv : ∀ y ∈ Ld D u 0 (Nat.zero_le _) c,
      ((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ y ∈
        Ld D u 0 (Nat.zero_le _) c2 := by
    intro y hy
    rw [← hLat.2, mem_mul_lattice_iff] at hy
    exact hy
  have hΓU : (γ2⁻¹ * γd⁻¹ * γ : GL (Fin (D.R.N 0)) D.host.E) ∈
      UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)) :=
    mul_mem (mul_mem (inv_mem hγ2) (inv_mem hγd)) hγ
  have hne1 : (1 : 𝓞 D.host.E) ∉ T.atT.Pv v := (T.atT.Pv v).ne_top_iff_one.1 (Ideal.IsPrime.ne_top inferInstance)

  have hQd := local_dual_Q_eq_of_P T.atT v c3 c1 _ hΓU hP
  obtain ⟨a1, ha1P, ha1Q, ha1⟩ := rlv_two (T.atT.Pv v) (rlvQ T.atT v) hPd.le hQd.le
    (x := ((γ2⁻¹ * γd⁻¹ * γ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ w)
    ⟨w, hw, rfl⟩

  have hPw : (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ w ∈
      Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (Ld D u 0 (Nat.zero_le _) c1)) :=
    (rlv_mem_locP _ _ _).2 ⟨1, hne1, by rw [one_smul]; exact ⟨w, hw, rfl⟩⟩
  rw [h4, rlv_mem_locP] at hPw
  obtain ⟨s, hs, hsw⟩ := hPw
  have hs' : s • ((((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • ((γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ w)) ∈
      Ld D u 0 (Nat.zero_le _) c := by
    rw [smul_comm]; exact natSmul_mem_of_sup _ _ hT0 z hz _ hsw
  have e1 : Formalism.L2.GlobalTheoryTheory.Comp.dl (sigD D) (gramN D 0 (Nat.zero_le _)) (Ld D u 0 (Nat.zero_le _) c1) =
      clsCrd D u 0 (Nat.zero_le _) c1 := hdd c1
  have hQ : Formalism.HermitianLatticesTheory.localization₂ (rlvQ T.atT v) (mulLat (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (Ld D u 0 (Nat.zero_le _) c1)) ≤
      Formalism.HermitianLatticesTheory.localization₂ (rlvQ T.atT v) (clsCrd D u 0 (Nat.zero_le _) c) := by
    have hg1 : cT (sigD D : D.host.E →+* D.host.E) (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *
        gramN D 0 (Nat.zero_le _) * (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) = gramN D 0 (Nat.zero_le _) := hγ
    refine rlv_dualQ (sigD D) rlv_sig_sig (gramN D 0 (Nat.zero_le _)) hH _ hg1 (T.atT.Pv v) (hfg c) (hdd c).le ?_
    rw [e1]; exact h3.ge
  have hne1Q : (1 : 𝓞 D.host.E) ∉ rlvQ T.atT v := (rlvQ T.atT v).ne_top_iff_one.1 (Ideal.IsPrime.ne_top inferInstance)
  have hQw := hQ ((rlv_mem_locP _ _ _).2 ⟨1, hne1Q, by rw [one_smul]; exact ⟨w, hw, rfl⟩⟩)
  obtain ⟨t, ht, htw⟩ := (rlv_mem_locP _ _ _).1 hQw
  have ht' : t • ((((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • ((γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ w)) ∈
      Ld D u 0 (Nat.zero_le _) c := by
    rw [smul_comm]; exact Submodule.smul_mem _ _ (cls_le_ld T c htw)
  obtain ⟨a2, ha2P, ha2Q, ha2⟩ := avoid_two _ _ _ _ s t hs ht hs' ht'

  have haP : a1 * a2 ∉ T.atT.Pv v := fun h => (Ideal.IsPrime.mem_or_mem inferInstance h).elim ha1P ha2P
  have haQ : a1 * a2 ∉ rlvQ T.atT v := fun h => (Ideal.IsPrime.mem_or_mem inferInstance h).elim ha1Q ha2Q
  obtain ⟨r, hr, b, hb⟩ := rlv_norm T.atT v (a1 * a2) haP haQ
  have m1 : (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r) •
      (((γ2⁻¹ * γd⁻¹ * γ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ w) ∈
      Ld D u 0 (Nat.zero_le _) c3 := by
    rw [hb, show b * (a1 * a2) = (b * a2) * a1 by ring, mul_smul]
    exact Submodule.smul_mem _ _ ha1
  have m2 : (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r) •
      ((((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • ((γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ w)) ∈ Ld D u 0 (Nat.zero_le _) c := by
    rw [hb, show b * (a1 * a2) = (b * a1) * a2 by ring, mul_smul]
    exact Submodule.smul_mem _ _ ha2
  refine ⟨r, hr, m1, ?_⟩
  have eV1 : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • ((γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ
      ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r) • w)) =
      (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r) •
        ((((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • ((γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ w)) := by
    rw [Matrix.mulVec_smul, smul_comm]
  have hB : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • ((γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ
      ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r) • w)) ∈ Ld D u 0 (Nat.zero_le _) c := by
    rw [eV1]; exact m2
  have eV2 : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • ((γ2 : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ
      ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r) •
        (((γ2⁻¹ * γd⁻¹ * γ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ w))) =
      ((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ
        ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r) •
          ((((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • ((γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ w))) := by
    have eg : (γ2 : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ
        (((γ2⁻¹ * γd⁻¹ * γ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ w) =
        ((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ
          ((γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ w) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul, ← mul_assoc, ← mul_assoc,
        mul_inv_cancel, one_mul]
    rw [Matrix.mulVec_smul, eg, Matrix.mulVec_smul, Matrix.mulVec_smul, smul_comm]
  have hA : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • ((γ2 : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ
      ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r) •
        (((γ2⁻¹ * γd⁻¹ * γ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ w))) ∈
      Ld D u 0 (Nat.zero_le _) c2 := by
    rw [eV2]; exact memInv _ m2
  calc (D.fm u).fv 0 v c3 (T.lv0.pr v c3 ⟨_, m1⟩)
      = (D.fm u).fv 0 v c2 (T.lv0.pr v c2 ⟨_, hA⟩) := g5 ⟨_, m1⟩ hA
    _ = (D.fm u).fv 0 v c2 (T.lv0.pr v c2 ⟨_, memInv _ m2⟩) := congrArg _ (pr_congr T v c2 ⟨_, hA⟩ ⟨_, memInv _ m2⟩ eV2)
    _ = k • (D.fm u).fv 0 v c (T.lv0.pr v c ⟨_, m2⟩) :=
        Formalism.L2.GlobalTheoryTheory.UnramifiedDiagonal.diaFun_same T v k δ hδ c c2 γd κd hx _ m2 (memInv _ m2)
    _ = k • (D.fm u).fv 0 v c (T.lv0.pr v c ⟨_, hB⟩) := by
        rw [pr_congr T v c ⟨_, m2⟩ ⟨_, hB⟩ eV1.symm]
    _ = _ := congrArg (fun t => k • t) (h5 ⟨_, Submodule.smul_mem _ _ hw⟩ hB).symm

end SameDiaZero

end
