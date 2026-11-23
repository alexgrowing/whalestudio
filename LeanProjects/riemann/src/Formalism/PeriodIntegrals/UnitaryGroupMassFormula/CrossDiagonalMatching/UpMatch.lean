import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CrossDiagonalMatching.UpF

noncomputable section

namespace CrossDiaZero

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.LocalLatticeBases Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0 Formalism.UG
open NumberField IsDedekindDomain Matrix

variable {D : D7} {u : D.what₂.Word}

set_option maxHeartbeats 8000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem upMatch (T : Forms0 D u) : UpDiaMatch0F T := by
  intro v v' hvv a k hk δ hδ c γd hγd κd hx
  set c2 := (D.fm u).dil 0 v' a c with hc2
  have hLat := diamond_lattice_transport T v' k δ hδ c c2 γd hγd κd hx
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
  have hne : (T.atT.eV v).1 ≠ (T.atT.eV v').1 := fun h => hvv (T.atT.eV.injective (Subtype.ext h))
  have hδv : bc (prV (E := D.host.E) (T.atT.eV v).1) δ.1 = 1 := hδ.1 _ hne
  have h3d : (T.cls0.y c).1 * δ.1 = bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γd *
      (T.cls0.y c2).1 * κd.1 := hx

  choose zf hzf using fun x : {x : (D.fm u).lv 0 v c // (D.fm u).fv 0 v c x = 1} => T.lv0.pr_surj v c x.1
  have hz1 : ∀ x, (D.fm u).fv 0 v c (T.lv0.pr v c (zf x)) = 1 := fun x => by rw [hzf x]; exact x.2
  choose γ η κ h1 h2 h3 h4 h5 h6 using fun x => T.up_natural_level_zero v c (zf x) (hz1 x)

  let z2 : {x : (D.fm u).lv 0 v c // (D.fm u).fv 0 v c x = 1} → ↥(Ld D u 0 (Nat.zero_le _) c2) :=
    fun x => ⟨((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ (zf x).1, memInv _ (zf x).2⟩
  have hz2 : ∀ x, (D.fm u).fv 0 v c2 (T.lv0.pr v c2 (z2 x)) = 1 := fun x =>
    (diamond_class_function T v v' hvv k δ hδ c c2 γd κd hx (zf x).1 (zf x).2 (memInv _ (zf x).2)).trans (hz1 x)
  choose γ2 η2 κ2 g1 g2 g3 g4 g5 g6 using fun x => T.up_natural_level_zero v c2 (z2 x) (hz2 x)

  choose zl hzl using fun y : {y : (D.fm u).lv 0 v c2 // (D.fm u).fv 0 v c2 y = 1} => T.lv0.pr_surj v c2 y.1
  have hinvf : ∀ y, (D.fm u).fv 0 v c (T.lv0.pr v c ⟨(γd : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ (zl y).1, memFwd _ (zl y).2⟩) = 1 := by
    intro y
    have hm : ((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ ((γd : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ (zl y).1) ∈ Ld D u 0 (Nat.zero_le _) c2 := by
      rw [eInvFwd]; exact (zl y).2
    rw [← diamond_class_function T v v' hvv k δ hδ c c2 γd κd hx _ (memFwd _ (zl y).2) hm,
      pr_congr T v c2 ⟨_, hm⟩ (zl y) (eInvFwd _), hzl y]
    exact y.2
  let σ : {x : (D.fm u).lv 0 v c // (D.fm u).fv 0 v c x = 1} ≃
      {y : (D.fm u).lv 0 v c2 // (D.fm u).fv 0 v c2 y = 1} :=
    { toFun := fun x => ⟨T.lv0.pr v c2 (z2 x), hz2 x⟩
      invFun := fun y => ⟨T.lv0.pr v c ⟨(γd : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ (zl y).1, memFwd _ (zl y).2⟩, hinvf y⟩
      left_inv := by
        intro x
        apply Subtype.ext
        have hzz : T.lv0.pr v c2 (zl ⟨T.lv0.pr v c2 (z2 x), hz2 x⟩) = T.lv0.pr v c2 (z2 x) := hzl _
        have hm : (γd : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ (z2 x).1 ∈ Ld D u 0 (Nat.zero_le _) c := by
          show (γd : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ (((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ (zf x).1) ∈ _
          rw [eFwdInv]; exact (zf x).2
        exact (pr_tr T v c2 c (γd : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) hLat.2 _ (z2 x) hzz (memFwd _ (zl _).2) hm).trans
          ((pr_congr T v c ⟨_, hm⟩ (zf x) (eFwdInv _)).trans (hzf x))
      right_inv := by
        intro y
        apply Subtype.ext
        have hzz := hzf ⟨T.lv0.pr v c ⟨(γd : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ (zl y).1, memFwd _ (zl y).2⟩, hinvf y⟩
        have hm : ((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ ((γd : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ (zl y).1) ∈ Ld D u 0 (Nat.zero_le _) c2 := by
          rw [eInvFwd]; exact (zl y).2
        exact (pr_tr T v c c2 _ hInv _ ⟨_, memFwd _ (zl y).2⟩ hzz (memInv _ (zf _).2) hm).trans
          ((pr_congr T v c2 ⟨_, hm⟩ (zl y) (eInvFwd _)).trans (hzl y)) }
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
    show (η2 (σ.symm (σ x))).1⁻¹ * κd.1 * (η x).1 ∈ T.cls0.lev.U
    rw [σ.symm_apply_apply]
    have hΓU : ((γ2 x).1⁻¹ * γd⁻¹ * (γ x).1 : GL (Fin (D.R.N 0)) D.host.E) ∈
        UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)) :=
      mul_mem (mul_mem (inv_mem (γ2 x).2) (inv_mem hγd)) (γ x).2
    have eΓ : (((γ2 x).1⁻¹ * γd⁻¹ * (γ x).1 : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) =
        (((γ2 x).1⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) * ((((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E)) * ((γ x).1 : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E)) := by
      rw [Units.val_mul, Units.val_mul, mul_assoc]

    have stepB : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat ((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (Ld D u 0 (Nat.zero_le _) c)) =
        Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (Ld D u 0 (Nat.zero_le _) c2) := by rw [hInv]
    have ch1 := rlv_chainP (T.atT.Pv v) ((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) ((γ x).1 : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) stepB (h3 x)
    have ch2 := rlv_chainP (T.atT.Pv v) (((γ2 x).1⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) _ (use₄ (T.atT.Pv v) (γ2 x).1 (g3 x)) ch1
    have hP : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat (((γ2 x).1⁻¹ * γd⁻¹ * (γ x).1 : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E)
        (clsCrd D u 0 (Nat.zero_le _) ((D.fm u).up 0 v c (T.lv0.pr v c (zf x))))) =
        Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) ((D.fm u).up 0 v c2 (T.lv0.pr v c2 (z2 x)))) := by
      rw [eΓ]; exact ch2

    have eG : mulLat ((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (Ld D u 0 (Nat.zero_le _) c ⊔ Submodule.span (𝓞 D.host.E) {(((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • (zf x).1}) =
        Ld D u 0 (Nat.zero_le _) c2 ⊔ Submodule.span (𝓞 D.host.E) {(((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • (z2 x).1} := by
      rw [show mulLat ((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (Ld D u 0 (Nat.zero_le _) c ⊔ Submodule.span (𝓞 D.host.E) {(((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • (zf x).1}) =
          mulLat ((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (Ld D u 0 (Nat.zero_le _) c) ⊔
            mulLat ((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (Submodule.span (𝓞 D.host.E) {(((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • (zf x).1}) from
          Submodule.map_sup _ _ _, hInv]
      congr 1
      unfold mulLat
      rw [Submodule.map_span, Set.image_singleton]
      congr 2
      show ((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ ((((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • (zf x).1) = (((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • (((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ (zf x).1)
      rw [Matrix.mulVec_smul]
    have stepB' : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat ((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E)
        (Ld D u 0 (Nat.zero_le _) c ⊔ Submodule.span (𝓞 D.host.E) {(((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • (zf x).1})) =
        Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (Ld D u 0 (Nat.zero_le _) c2 ⊔ Submodule.span (𝓞 D.host.E) {(((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • (z2 x).1}) := by rw [eG]
    have ch1' := rlv_chainP (T.atT.Pv v) ((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) ((γ x).1 : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) stepB' (h4 x)
    have ch2' := rlv_chainP (T.atT.Pv v) (((γ2 x).1⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) _ (use₄ (T.atT.Pv v) (γ2 x).1 (g4 x)) ch1'
    have hPd : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat (((γ2 x).1⁻¹ * γd⁻¹ * (γ x).1 : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E)
        (Ld D u 0 (Nat.zero_le _) ((D.fm u).up 0 v c (T.lv0.pr v c (zf x))))) =
        Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (Ld D u 0 (Nat.zero_le _) ((D.fm u).up 0 v c2 (T.lv0.pr v c2 (z2 x)))) := by
      rw [eΓ]; exact ch2'
    have hF := upF T v v' hvv k δ hδ c _ c2 _ γd hγd κd hx (γ x).1 (γ2 x).1 (γ x).2 (γ2 x).2 (zf x).1 (zf x).2
      (h3 x) (h4 x) (h5 x) (g5 x) hP hPd
    have hU := matching_unitary_eq T.cls0 c _ c2 _ (γ x).1 (γ2 x).1 γd (η x) (η2 x) δ (κ x) (κ2 x) κd (h2 x) (g2 x) h3d
    exact matching_move_mem_level_zero T v c _ c2 _ (γ x).1 (γ2 x).1 γd (η x) (η2 x) δ (κ x) (κ2 x) κd (h1 x) (g1 x) hδv
      (h2 x) (g2 x) h3d (local_unitary_of_matching_zero T v _ _ _ hΓU hU hP hPd hF)

end CrossDiaZero

end
