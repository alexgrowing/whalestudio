import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRedDual

set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.Dieu.EtFromConn

namespace GlobalTheory.Dieu.EtFromConn

theorem rigToLie_toBase_rig {p : ℕ} [Fact p.Prime] {k k' : Type} [Field k] [CharP k p] [Field k']
    [CharP k' p] [Algebra k k'] (G : PDivGroup p k) (r : G.RigExt) (w : G.dual.omega) :
    (G.baseChange k').rigToLie (p_eq_zero p k') ((G.toBase k').rig r)
      (omegaMap _ _ (PerfdLat.dualBaseChange k' G).hom ((G.dual.toBase k').omega w)) =
      algebraMap k k' (G.rigToLie (p_eq_zero p k) r w) := by
  rw [rigToLie_apply, rigToLie_apply, SemiHom.rigToExt_rig,
    SemiHom.extChar_vecExt _ (p_eq_zero p k)]
  exact primLie_toBase G _ w

theorem linearMap_eq_of_liftSemi_surjective {R R' M N : Type} [CommRing R] [CommRing R']
    [Algebra R R'] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R' N]
    (f : M →ₛₗ[algebraMap R R'] N) (hf : Function.Surjective (liftSemi f)) (F₁ F₂ : N →ₗ[R'] R')
    (h : ∀ m, F₁ (f m) = F₂ (f m)) : F₁ = F₂ := by
  refine LinearMap.ext fun v => ?_
  obtain ⟨t, rfl⟩ := hf v
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul r m => rw [liftSemi_tmul, map_smul, map_smul, h]

set_option maxHeartbeats 2000000 in
theorem red_of_isTr (p : ℕ) [Fact p.Prime] (B : Base p (fun _ _ G => G.IsConn)) (k k' : Type)
    [Field k] [CharP k p] [PerfectRing k p] [Field k'] [CharP k' p] [PerfectRing k' p]
    (σ : k →+* k') (G' : PDivGroup p k') (G : PDivGroup p k) (h' : G'.IsEt) (h : G.IsEt)
    (s : SemiHom σ G' G) (l : Mod B G h) (l' : Mod B G' h') (hT : IsTr B σ h' h s l l') :
    red B G' h' l' = s.rig (red B G h l) := by
  letI : Algebra k k' := σ.toAlgebra
  obtain ⟨hb, lb, h1, h2⟩ := hT
  haveI := B.free _ hb
  haveI := B.finite _ hb
  obtain ⟨r', hr', -, -⟩ := wittDual_reduction p k' _ _ (B.red _ hb) (B.red_surjective _ hb)
    (B.red_eq_zero _ hb)
  have hψ : ∀ m, r' lb (B.red _ hb m) = WittVector.constantCoeff (lb m) := hr' lb
  have key1 : ∀ w : G.dual.omega,
      r' lb ((G.dual.baseChange k').rigOfOmega ((G.dual.toBase k').omega w)) =
        σ (G.rigToLie (p_eq_zero p k) (red B G h l) w) := by
    intro w
    obtain ⟨x, hx⟩ := B.red_surjective _ (dual_conn h) (G.dual.rigOfOmega w)
    have e1 : (G.dual.baseChange k').rigOfOmega ((G.dual.toBase k').omega w) =
        B.red _ hb (B.smap hb (dual_conn h) (G.dual.toBase k') x) := by
      rw [B.red_smap, hx, SemiHom.rig_rigOfOmega]
    have e2 : G.rigToLie (p_eq_zero p k) (red B G h l) w = WittVector.constantCoeff (l x) := by
      rw [rigToLie_red, LinearMap.dualMap_apply, ← hx]
      exact (redDual_spec B G h).1 l x
    have e3 : WittVector.constantCoeff (WittVector.map σ (l x)) = σ (WittVector.constantCoeff (l x)) := by
      simp [WittVector.constantCoeff_apply, WittVector.map_coeff]
    exact (congrArg (r' lb) e1).trans ((hψ _).trans ((congrArg _ (h1 x)).trans (e3.trans (congrArg σ e2.symm))))
  have key2 : ((G.baseChange k').rigToLie (p_eq_zero p k') ((G.toBase k').rig (red B G h l))).comp
      (omegaMap _ _ (PerfdLat.dualBaseChange k' G).hom) =
      (r' lb).comp (G.dual.baseChange k').rigOfOmega :=
    linearMap_eq_of_liftSemi_surjective (G.dual.toBase k').omega
      (T.omega_baseChange_bijective_of_p_eq_zero G.dual k' (p_eq_zero p k)).2 _ _ fun w => by
        rw [LinearMap.comp_apply, LinearMap.comp_apply, rigToLie_toBase_rig, key1]
        rfl
  have hinj := (PDivGroup.rigToLie_bijective_and_dual_rigOfOmega_bijective_of_isEt p k'
    (p_eq_zero p k') G' h').1.1
  apply hinj
  rw [rigToLie_red]
  refine LinearMap.ext fun w' => ?_
  rw [LinearMap.dualMap_apply]
  obtain ⟨x', hx'⟩ := B.red_surjective _ (dual_conn h') (G'.dual.rigOfOmega w')
  have hs : ∀ n a, s.app n a = (SemiHom.ofHom s.lift).app n ((G.toBase k').app n a) := fun n a => by
    rw [SemiHom.ofHom_app, toBase_app, SemiHom.lift_app, one_smul]
  have e4 : B.red _ hb (B.map hb (dual_conn h')
      ((PerfdLat.dualBaseChange k' G).inv ≫ dualHom G' (G.baseChange k') s.lift) x') =
      (G.dual.baseChange k').rigOfOmega (omegaMap _ _ (PerfdLat.dualBaseChange k' G).inv
        (omegaMap _ _ (dualHom G' (G.baseChange k') s.lift) w')) := by
    change B.red _ hb (B.smap hb (dual_conn h') (SemiHom.ofHom _) x') = _
    rw [B.red_smap, hx', SemiHom.rig_rigOfOmega, SemiHom.ofHom_omega, omegaMap_comp,
      LinearMap.comp_apply]
  have e5 : G'.rigToLie (p_eq_zero p k') (s.rig (red B G h l)) w' =
      (G.baseChange k').rigToLie (p_eq_zero p k') ((G.toBase k').rig (red B G h l))
        (omegaMap _ _ (dualHom G' (G.baseChange k') s.lift) w') := by
    rw [← (G.toBase k').rig_rig (SemiHom.ofHom s.lift) s hs, SemiHom.ofHom_rig,
      rigToLie_rigExtMap, lieMap_apply]
  have e6 : ∀ v, omegaMap _ _ (PerfdLat.dualBaseChange k' G).hom
      (omegaMap _ _ (PerfdLat.dualBaseChange k' G).inv v) = v := fun v => by
    rw [← LinearMap.comp_apply, ← omegaMap_comp, Iso.hom_inv_id, omegaMap_id, LinearMap.id_apply]
  rw [← hx', (redDual_spec B G' h').1, h2, ← hψ, e4, e5]
  have e7 := LinearMap.congr_fun key2 (omegaMap _ _ (PerfdLat.dualBaseChange k' G).inv
    (omegaMap _ _ (dualHom G' (G.baseChange k') s.lift) w'))
  rw [LinearMap.comp_apply, LinearMap.comp_apply, e6] at e7
  exact e7.symm

end GlobalTheory.Dieu.EtFromConn
