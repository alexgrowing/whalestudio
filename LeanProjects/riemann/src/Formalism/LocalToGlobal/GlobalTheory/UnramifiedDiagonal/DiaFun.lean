import Formalism.LocalToGlobal.GlobalTheory.GL6.DiagonalSlopes.NaturalTranslateAdelicFunction

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.UnramifiedDiagonal

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Formalism.L2.GlobalTheoryTheory.LocalLatticeBases Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0 NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

variable {D : D7} {u : D.what₂.Word}

set_option maxHeartbeats 20000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem diaFun_same (T : Forms0 D u) (v : (D.mem u).A.vT) (k : ℤ)
    (δ : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (hδ : IsDia T.cls0.lev (T.atT.eV v).1 (T.atT.eV v).2 k δ) (c c2 : (D.mem u).C.cls 0)
    (γd : GL (Fin (D.R.N 0)) D.host.E) (κd : T.cls0.lev.U)
    (h : (T.cls0.y c * δ).1 = bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γd *
      (T.cls0.y c2).1 * κd.1)
    (z : Fin (D.R.N 0) → D.host.E) (hz : z ∈ Ld D u 0 (Nat.zero_le _) c)
    (hz2 : ((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ z ∈
      Ld D u 0 (Nat.zero_le _) c2) :
    (D.fm u).fv 0 v c2 (T.lv0.pr v c2 ⟨_, hz2⟩) = k • (D.fm u).fv 0 v c (T.lv0.pr v c ⟨z, hz⟩) := by
  have h1 := (mem_local_dual_lattice_iff' T.cls0 c (T.atT.eV v).1
    (fun a => inclE (F := D.host.F) ((T.atT.eV v).1.adicCompletion D.host.F) (z a))).1
    (Submodule.subset_span ⟨z, hz, rfl⟩)
  have h2 := (mem_local_dual_lattice_iff' T.cls0 c2 (T.atT.eV v).1
    (fun a => inclE (F := D.host.F) ((T.atT.eV v).1.adicCompletion D.host.F)
      ((((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ z) a))).1
    (Submodule.subset_span ⟨_, hz2, rfl⟩)
  rw [T.fv0 v c2 ⟨_, hz2⟩ h2, T.fv0 v c ⟨z, hz⟩ h1]
  refine (congrArg (T.fMe0 v) ?_).trans (map_zsmul (T.fMe0 v) k _)
  have hκ : bc (prV (E := D.host.E) (T.atT.eV v).1) κd.1 ∈ T.cls0.lev.Uloc (T.atT.eV v).1 :=
    ((T.cls0.lev.U_eq _).1 κd.2).2 _
  rw [T.cls0.lev.UlocAlt _ (T.atT.eV v).2] at hκ
  obtain ⟨hgκ, hfix⟩ := (Subgroup.mem_inf.1 hκ).2
  obtain ⟨-, -, hgδ, hfδ⟩ := hδ
  have hw' : bc (prV (E := D.host.E) (T.atT.eV v).1) (T.cls0.y c).1 * bc (prV (E := D.host.E) (T.atT.eV v).1) δ.1 =
      bc (prV (E := D.host.E) (T.atT.eV v).1) (bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γd) *
        bc (prV (E := D.host.E) (T.atT.eV v).1) (T.cls0.y c2).1 * bc (prV (E := D.host.E) (T.atT.eV v).1) κd.1 := by
    have e0 := congrArg (bc (prV (E := D.host.E) (T.atT.eV v).1)) h
    simp only [Subgroup.coe_mul, map_mul] at e0
    exact e0
  have eg : (fun a => inclE (F := D.host.F) ((T.atT.eV v).1.adicCompletion D.host.F)
      ((((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ z) a)) =
      (((bc (prV (E := D.host.E) (T.atT.eV v).1)
        (bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γd))⁻¹ : GL _ _) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) _) *ᵥ
        (fun a => inclE (F := D.host.F) ((T.atT.eV v).1.adicCompletion D.host.F) (z a)) := by
    rw [← map_inv, ← map_inv]
    funext a
    rw [RingHom.map_mulVec]
    rfl
  have hdd : (((bc (prV (E := D.host.E) (T.atT.eV v).1) δ.1) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) _)) *ᵥ ((((bc (prV (E := D.host.E) (T.atT.eV v).1) δ.1)⁻¹ : GL _ _) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) _) *ᵥ ((((bc (prV (E := D.host.E) (T.atT.eV v).1) (T.cls0.y c).1)⁻¹ : GL _ _) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) _) *ᵥ (fun a => inclE (F := D.host.F) ((T.atT.eV v).1.adicCompletion D.host.F) (z a)))) = ((((bc (prV (E := D.host.E) (T.atT.eV v).1) (T.cls0.y c).1)⁻¹ : GL _ _) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) _) *ᵥ (fun a => inclE (F := D.host.F) ((T.atT.eV v).1.adicCompletion D.host.F) (z a))) := by
    rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
  have hu : (((bc (prV (E := D.host.E) (T.atT.eV v).1) δ.1)⁻¹ : GL _ _) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) _) *ᵥ ((((bc (prV (E := D.host.E) (T.atT.eV v).1) (T.cls0.y c).1)⁻¹ : GL _ _) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) _) *ᵥ (fun a => inclE (F := D.host.F) ((T.atT.eV v).1.adicCompletion D.host.F) (z a))) ∈
      latS (F := D.host.F) ((T.atT.eV v).1.adicCompletion D.host.F) (intV D.host.E (T.atT.eV v).1)
        (Submodule.span (𝓞 D.host.E) (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)) T.cls0.lev.Lb)) := by
    refine (hgδ _).2 ?_
    rw [hdd]
    exact h1
  have key : (((bc (prV (E := D.host.E) (T.atT.eV v).1) (T.cls0.y c2).1)⁻¹ : GL _ _) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) _) *ᵥ
      (fun a => inclE (F := D.host.F) ((T.atT.eV v).1.adicCompletion D.host.F)
        ((((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ z) a)) =
      ((bc (prV (E := D.host.E) (T.atT.eV v).1) κd.1 : GL _ _) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) _) *ᵥ
        ((((bc (prV (E := D.host.E) (T.atT.eV v).1) δ.1)⁻¹ : GL _ _) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) _) *ᵥ ((((bc (prV (E := D.host.E) (T.atT.eV v).1) (T.cls0.y c).1)⁻¹ : GL _ _) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) _) *ᵥ (fun a => inclE (F := D.host.F) ((T.atT.eV v).1.adicCompletion D.host.F) (z a)))) := by
    have gid : ∀ (Yc Dl Y2 G K : GL (Fin (D.R.N 0)) (D.host.E ⊗[D.host.F] (T.atT.eV v).1.adicCompletion D.host.F)),
        Yc * Dl = G * Y2 * K → Y2⁻¹ * G⁻¹ = K * Dl⁻¹ * Yc⁻¹ := by
      intro Yc Dl Y2 G K e0
      have : Y2 = G⁻¹ * (Yc * Dl) * K⁻¹ := by rw [e0]; group
      rw [this]; group
    have gm := congrArg Units.val (gid _ _ _ _ _ hw')
    rw [Units.val_mul, Units.val_mul, Units.val_mul] at gm
    rw [eg, mulVec_mulVec, mulVec_mulVec, mulVec_mulVec, gm]
  have e1 : T.cls0.lev.fT (T.atT.eV v).1 (T.atT.eV v).2 ⟨_, h2⟩ =
      T.cls0.lev.fT (T.atT.eV v).1 (T.atT.eV v).2 ⟨_, hu⟩ := by
    refine Eq.trans ?_ (hfix ⟨_, hu⟩)
    congr 1
    exact Subtype.ext key
  have e2 := hfδ ⟨_, hu⟩
  have e3 : (⟨(bc (prV (E := D.host.E) (T.atT.eV v).1) δ.1).1 *ᵥ ((((bc (prV (E := D.host.E) (T.atT.eV v).1) δ.1)⁻¹ : GL _ _) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) _) *ᵥ ((((bc (prV (E := D.host.E) (T.atT.eV v).1) (T.cls0.y c).1)⁻¹ : GL _ _) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) _) *ᵥ (fun a => inclE (F := D.host.F) ((T.atT.eV v).1.adicCompletion D.host.F) (z a)))), (hgδ _).1 hu⟩ :
      latS (F := D.host.F) ((T.atT.eV v).1.adicCompletion D.host.F) (intV D.host.E (T.atT.eV v).1)
        (Submodule.span (𝓞 D.host.E) (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)) T.cls0.lev.Lb))) =
      ⟨((((bc (prV (E := D.host.E) (T.atT.eV v).1) (T.cls0.y c).1)⁻¹ : GL _ _) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) _) *ᵥ (fun a => inclE (F := D.host.F) ((T.atT.eV v).1.adicCompletion D.host.F) (z a))), h1⟩ := Subtype.ext hdd
  calc T.cls0.lev.fT (T.atT.eV v).1 (T.atT.eV v).2 ⟨_, h2⟩
      = T.cls0.lev.fT (T.atT.eV v).1 (T.atT.eV v).2 ⟨_, hu⟩ := e1
    _ = k • T.cls0.lev.fT (T.atT.eV v).1 (T.atT.eV v).2 ⟨(bc (prV (E := D.host.E) (T.atT.eV v).1) δ.1).1 *ᵥ ((((bc (prV (E := D.host.E) (T.atT.eV v).1) δ.1)⁻¹ : GL _ _) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) _) *ᵥ ((((bc (prV (E := D.host.E) (T.atT.eV v).1) (T.cls0.y c).1)⁻¹ : GL _ _) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) _) *ᵥ (fun a => inclE (F := D.host.F) ((T.atT.eV v).1.adicCompletion D.host.F) (z a)))), (hgδ _).1 hu⟩ := e2.symm
    _ = k • T.cls0.lev.fT (T.atT.eV v).1 (T.atT.eV v).2 ⟨((((bc (prV (E := D.host.E) (T.atT.eV v).1) (T.cls0.y c).1)⁻¹ : GL _ _) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) _) *ᵥ (fun a => inclE (F := D.host.F) ((T.atT.eV v).1.adicCompletion D.host.F) (z a))), h1⟩ := by rw [e3]

end Formalism.L2.GlobalTheoryTheory.UnramifiedDiagonal

end
