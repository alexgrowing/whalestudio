import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CrossDiagonalMatching.DnkLkLocP

noncomputable section

namespace CrossDiaZero

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.LocalLatticeBases Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0 Formalism.UG
open NumberField IsDedekindDomain Matrix

def dualSigma {K V W : Type} [CommRing K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (φ : W ≃ₗ[K] V) (tv : V) (tw : W) (h : φ tw = tv) :
    {x : Module.Dual K V // x tv = 1} ≃ {y : Module.Dual K W // y tw = 1} where
  toFun x := ⟨x.1 ∘ₗ φ.toLinearMap, by rw [LinearMap.comp_apply, LinearEquiv.coe_coe, h]; exact x.2⟩
  invFun y := ⟨y.1 ∘ₗ φ.symm.toLinearMap, by
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe, ← h, LinearEquiv.symm_apply_apply]; exact y.2⟩
  left_inv x := Subtype.ext (LinearMap.ext fun w => by simp)
  right_inv y := Subtype.ext (LinearMap.ext fun w => by simp)

theorem dualSigma_apply {K V W : Type} [CommRing K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (φ : W ≃ₗ[K] V) (tv : V) (tw : W) (h : φ tw = tv) (x : {x : Module.Dual K V // x tv = 1}) (w : W) :
    (dualSigma φ tv tw h x).1 w = x.1 (φ w) := rfl

variable {D : D7} {u : D.what₂.Word}

set_option maxHeartbeats 2000000 in

theorem dni_lk (T : Forms0 D u) (v : (D.mem u).A.vT) (c c' : (D.mem u).C.cls 0)
    (g : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E)
    (hL : mulLat g (clsCrd D u 0 (Nat.zero_le _) c) = clsCrd D u 0 (Nat.zero_le _) c')
    (hLd : mulLat g (Ld D u 0 (Nat.zero_le _) c) = Ld D u 0 (Nat.zero_le _) c') :
    mulLat g (Lk T.atT 0 (Nat.zero_le _) v c) = Lk T.atT 0 (Nat.zero_le _) v c' := by
  show mulLat g (clsCrd D u 0 (Nat.zero_le _) c ⊔ T.atT.Pv v • Ld D u 0 (Nat.zero_le _) c) =
    clsCrd D u 0 (Nat.zero_le _) c' ⊔ T.atT.Pv v • Ld D u 0 (Nat.zero_le _) c'
  unfold mulLat at hL hLd ⊢
  rw [Submodule.map_sup, Submodule.map_smul'', hL, hLd]

theorem dni_mem_of {E : Type} [Field E] [NumberField E] {n : ℕ} (g : Matrix (Fin n) (Fin n) E)
    {M M' : Submodule (𝓞 E) (Fin n → E)} (h : mulLat g M = M') {z : Fin n → E} (hz : z ∈ M) : g *ᵥ z ∈ M' := by
  rw [← h]
  exact Submodule.mem_map_of_mem hz

set_option maxHeartbeats 2000000 in
theorem dni_mem (T : Forms0 D u) (v : (D.mem u).A.vT) (c c' : (D.mem u).C.cls 0)
    (g : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E)
    (hL : mulLat g (clsCrd D u 0 (Nat.zero_le _) c) = clsCrd D u 0 (Nat.zero_le _) c')
    (hLd : mulLat g (Ld D u 0 (Nat.zero_le _) c) = Ld D u 0 (Nat.zero_le _) c')
    {z : Fin (D.R.N 0) → D.host.E} (hz : z ∈ Lk T.atT 0 (Nat.zero_le _) v c) :
    g *ᵥ z ∈ Lk T.atT 0 (Nat.zero_le _) v c' :=
  dni_mem_of g (dni_lk T v c c' g hL hLd) hz

set_option maxHeartbeats 2000000 in
theorem dni_mem_ker (T : Forms0 D u) (v : (D.mem u).A.vT) (c c' : (D.mem u).C.cls 0)
    (g : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E)
    (hL : mulLat g (clsCrd D u 0 (Nat.zero_le _) c) = clsCrd D u 0 (Nat.zero_le _) c')
    (hLd : mulLat g (Ld D u 0 (Nat.zero_le _) c) = Ld D u 0 (Nat.zero_le _) c')
    {z : Fin (D.R.N 0) → D.host.E} (hz : z ∈ T.atT.Pv v • Lk T.atT 0 (Nat.zero_le _) v c) :
    g *ᵥ z ∈ T.atT.Pv v • Lk T.atT 0 (Nat.zero_le _) v c' := by
  have h := dni_lk T v c c' g hL hLd
  have h2 : mulLat g (T.atT.Pv v • Lk T.atT 0 (Nat.zero_le _) v c) =
      T.atT.Pv v • Lk T.atT 0 (Nat.zero_le _) v c' := by
    unfold mulLat at h ⊢
    rw [Submodule.map_smul'', h]
  exact dni_mem_of g h2 hz

def dniFun (T : Forms0 D u) (v : (D.mem u).A.vT) (c c' : (D.mem u).C.cls 0)
    (g : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E)
    (hL : mulLat g (clsCrd D u 0 (Nat.zero_le _) c) = clsCrd D u 0 (Nat.zero_le _) c')
    (hLd : mulLat g (Ld D u 0 (Nat.zero_le _) c) = Ld D u 0 (Nat.zero_le _) c')
    (w : (D.fm u).lk 0 v c) : (D.fm u).lk 0 v c' :=
  T.lv0.prk v c' ⟨g *ᵥ (Function.surjInv (T.lv0.prk_surj v c) w).1,
    dni_mem T v c c' g hL hLd (Function.surjInv (T.lv0.prk_surj v c) w).2⟩

set_option maxHeartbeats 2000000 in
theorem dniFun_prk (T : Forms0 D u) (v : (D.mem u).A.vT) (c c' : (D.mem u).C.cls 0)
    (g : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E)
    (hL : mulLat g (clsCrd D u 0 (Nat.zero_le _) c) = clsCrd D u 0 (Nat.zero_le _) c')
    (hLd : mulLat g (Ld D u 0 (Nat.zero_le _) c) = Ld D u 0 (Nat.zero_le _) c')
    (z : ↥(Lk T.atT 0 (Nat.zero_le _) v c)) :
    dniFun T v c c' g hL hLd (T.lv0.prk v c z) = T.lv0.prk v c' ⟨g *ᵥ z.1, dni_mem T v c c' g hL hLd z.2⟩ := by
  have hs := Function.surjInv_eq (T.lv0.prk_surj v c) (T.lv0.prk v c z)
  have hd : (Function.surjInv (T.lv0.prk_surj v c) (T.lv0.prk v c z) - z).1 ∈
      T.atT.Pv v • Lk T.atT 0 (Nat.zero_le _) v c := by
    rw [← T.lv0.prk_ker, map_sub, hs, sub_self]
  have hg := dni_mem_ker T v c c' g hL hLd hd
  unfold dniFun
  rw [← sub_eq_zero, ← map_sub, T.lv0.prk_ker]
  simpa [Matrix.mulVec_sub] using hg

set_option maxHeartbeats 2000000 in

def dniLin (T : Forms0 D u) (v : (D.mem u).A.vT) (c c' : (D.mem u).C.cls 0)
    (g : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E)
    (hL : mulLat g (clsCrd D u 0 (Nat.zero_le _) c) = clsCrd D u 0 (Nat.zero_le _) c')
    (hLd : mulLat g (Ld D u 0 (Nat.zero_le _) c) = Ld D u 0 (Nat.zero_le _) c') :
    (D.fm u).lk 0 v c →ₗ[(D.mem u).A.Fv v] (D.fm u).lk 0 v c' where
  toFun := dniFun T v c c' g hL hLd
  map_add' w1 w2 := by
    obtain ⟨z1, rfl⟩ := T.lv0.prk_surj v c w1
    obtain ⟨z2, rfl⟩ := T.lv0.prk_surj v c w2
    rw [← map_add, dniFun_prk, dniFun_prk, dniFun_prk, ← map_add]
    congr 1
    apply Subtype.ext
    show g *ᵥ (z1.1 + z2.1) = g *ᵥ z1.1 + g *ᵥ z2.1
    exact Matrix.mulVec_add _ _ _
  map_smul' r w := by
    obtain ⟨a, rfl⟩ := T.atT.res_surj v r
    obtain ⟨z, rfl⟩ := T.lv0.prk_surj v c w
    rw [RingHom.id_apply, ← T.lv0.prk_smul, dniFun_prk, dniFun_prk, ← T.lv0.prk_smul]
    congr 1
    apply Subtype.ext
    show g *ᵥ (a • z.1) = a • (g *ᵥ z.1)
    exact Matrix.mulVec_smul _ _ _

theorem dniLin_prk (T : Forms0 D u) (v : (D.mem u).A.vT) (c c' : (D.mem u).C.cls 0)
    (g : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E)
    (hL : mulLat g (clsCrd D u 0 (Nat.zero_le _) c) = clsCrd D u 0 (Nat.zero_le _) c')
    (hLd : mulLat g (Ld D u 0 (Nat.zero_le _) c) = Ld D u 0 (Nat.zero_le _) c')
    (z : ↥(Lk T.atT 0 (Nat.zero_le _) v c)) :
    dniLin T v c c' g hL hLd (T.lv0.prk v c z) = T.lv0.prk v c' ⟨g *ᵥ z.1, dni_mem T v c c' g hL hLd z.2⟩ :=
  dniFun_prk T v c c' g hL hLd z

theorem dni_inv_eq {E : Type} [Field E] [NumberField E] {n : ℕ} (g : GL (Fin n) E)
    {M M' : Submodule (𝓞 E) (Fin n → E)} (h : mulLat (g : Matrix (Fin n) (Fin n) E) M = M') :
    mulLat ((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) M' = M := by
  have hid : ((Matrix.mulVecLin ((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E)).restrictScalars (𝓞 E)).comp
      ((Matrix.mulVecLin (g : Matrix (Fin n) (Fin n) E)).restrictScalars (𝓞 E)) = LinearMap.id := by
    refine LinearMap.ext fun x => ?_
    simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, Matrix.mulVecLin_apply,
      LinearMap.id_apply]
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  rw [← h]
  unfold mulLat
  rw [← Submodule.map_comp, hid, Submodule.map_id]

set_option maxHeartbeats 2000000 in

def dniEquiv (T : Forms0 D u) (v : (D.mem u).A.vT) (c c' : (D.mem u).C.cls 0) (g : GL (Fin (D.R.N 0)) D.host.E)
    (hL : mulLat (g : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (clsCrd D u 0 (Nat.zero_le _) c) =
      clsCrd D u 0 (Nat.zero_le _) c')
    (hLd : mulLat (g : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (Ld D u 0 (Nat.zero_le _) c) =
      Ld D u 0 (Nat.zero_le _) c') :
    (D.fm u).lk 0 v c ≃ₗ[(D.mem u).A.Fv v] (D.fm u).lk 0 v c' :=
  LinearEquiv.ofLinear (dniLin T v c c' _ hL hLd) (dniLin T v c' c _ (dni_inv_eq g hL) (dni_inv_eq g hLd))
    (LinearMap.ext fun w => by
      obtain ⟨z, rfl⟩ := T.lv0.prk_surj v c' w
      rw [LinearMap.comp_apply, dniLin_prk, dniLin_prk, LinearMap.id_apply]
      congr 1
      apply Subtype.ext
      show (g : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ
        (((g⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ z.1) = z.1
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec])
    (LinearMap.ext fun w => by
      obtain ⟨z, rfl⟩ := T.lv0.prk_surj v c w
      rw [LinearMap.comp_apply, dniLin_prk, dniLin_prk, LinearMap.id_apply]
      congr 1
      apply Subtype.ext
      show ((g⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ
        ((g : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ z.1) = z.1
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec])

theorem dniEquiv_prk (T : Forms0 D u) (v : (D.mem u).A.vT) (c c' : (D.mem u).C.cls 0) (g : GL (Fin (D.R.N 0)) D.host.E)
    (hL : mulLat (g : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (clsCrd D u 0 (Nat.zero_le _) c) =
      clsCrd D u 0 (Nat.zero_le _) c')
    (hLd : mulLat (g : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (Ld D u 0 (Nat.zero_le _) c) =
      Ld D u 0 (Nat.zero_le _) c')
    (z : ↥(Lk T.atT 0 (Nat.zero_le _) v c)) :
    dniEquiv T v c c' g hL hLd (T.lv0.prk v c z) =
      T.lv0.prk v c' ⟨(g : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ z.1, dni_mem T v c c' _ hL hLd z.2⟩ :=
  dniLin_prk T v c c' _ hL hLd z

set_option maxHeartbeats 2000000 in

theorem dniEquiv_te (T : Forms0 D u) (v : (D.mem u).A.vT) (c c' : (D.mem u).C.cls 0) (g : GL (Fin (D.R.N 0)) D.host.E)
    (hL : mulLat (g : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (clsCrd D u 0 (Nat.zero_le _) c) =
      clsCrd D u 0 (Nat.zero_le _) c')
    (hLd : mulLat (g : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (Ld D u 0 (Nat.zero_le _) c) =
      Ld D u 0 (Nat.zero_le _) c')
    (z : ↥(Ld D u 0 (Nat.zero_le _) c)) (hz : (D.fm u).fv 0 v c (T.lv0.pr v c z) = 1)
    (hgz : (g : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ z.1 ∈ Ld D u 0 (Nat.zero_le _) c')
    (hz' : (D.fm u).fv 0 v c' (T.lv0.pr v c' ⟨_, hgz⟩) = 1) :
    dniEquiv T v c c' g hL hLd ((D.fm u).te 0 v c) = (D.fm u).te 0 v c' := by
  have e1 := T.lv0.te v c z hz
    (Submodule.mem_sup_right (Submodule.smul_mem_smul (bwA_T_mem_Pv D u T.atT v) z.2))
  have e2 := T.lv0.te v c' ⟨_, hgz⟩ hz'
    (Submodule.mem_sup_right (Submodule.smul_mem_smul (bwA_T_mem_Pv D u T.atT v) hgz))
  rw [← e1, ← e2, dniEquiv_prk]
  congr 1
  apply Subtype.ext
  simp only [Matrix.mulVec_smul]

theorem dni_exists_one (T : Forms0 D u) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls 0) :
    ∃ z : ↥(Ld D u 0 (Nat.zero_le _) c), (D.fm u).fv 0 v c (T.lv0.pr v c z) = 1 := by
  obtain ⟨w, hw⟩ : ∃ w, (D.fm u).fv 0 v c w ≠ 0 := by
    by_contra h
    push_neg at h
    exact (D.fm u).fv_ne 0 v c (LinearMap.ext h)
  obtain ⟨z, hz⟩ := T.lv0.pr_surj v c (((D.fm u).fv 0 v c w)⁻¹ • w)
  refine ⟨z, ?_⟩
  rw [hz, map_smul, smul_eq_mul, inv_mul_cancel₀ hw]

end CrossDiaZero

end
