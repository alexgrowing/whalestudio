import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SiteSystemRanksEqDatumRanks
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV.Xc.ChiPow

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)

theorem exists_upts_det {n : ℕ} (hn : 0 < n) (Gm : Matrix (Fin n) (Fin n) E) (C : GL (Fin n) E)
    (hC : cT (σ : E →+* E) C.1 * C.1 = Gm) (x : (E ⊗[F] FiniteAdeleRing (𝓞 F) F)ˣ)
    (hx : (x : E ⊗[F] FiniteAdeleRing (𝓞 F) F) * sigR σ _ x = 1) :
    ∃ Y : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F), Y ∈ UPts σ Gm (FiniteAdeleRing (𝓞 F) F) ∧
      Matrix.GeneralLinearGroup.det Y = x := by
  set R := FiniteAdeleRing (𝓞 F) F
  let f : Fin n → (E ⊗[F] R)ˣ := Pi.mulSingle ⟨0, hn⟩ x
  have hf : f = Pi.mulSingle ⟨0, hn⟩ x := rfl
  let d : GL (Fin n) (E ⊗[F] R) := Units.map (Matrix.diagonalRingHom (Fin n) (E ⊗[F] R)).toMonoidHom
    (MulEquiv.piUnits.symm f)
  have hd : (d : Matrix (Fin n) (Fin n) (E ⊗[F] R)) = Matrix.diagonal (fun k => ((f k : (E ⊗[F] R)ˣ) : E ⊗[F] R)) := rfl
  let Cb := bc (inclE (F := F) R) C
  refine ⟨Cb⁻¹ * d * Cb, ?_, ?_⟩
  · have hsig : (inclE (F := F) R).comp (σ : E →+* E) = (sigR σ R).comp (inclE R) := by
      ext e
      simp [sigR, inclE, Algebra.TensorProduct.includeLeftRingHom_apply]
    have hG : Gm.map (inclE (F := F) R) = cT (sigR σ R) (Cb : Matrix (Fin n) (Fin n) (E ⊗[F] R)) * (Cb : Matrix (Fin n) (Fin n) (E ⊗[F] R)) := by
      rw [← hC, Matrix.map_mul, ← Formalism.UG.P.cT_map (σ : E →+* E) (sigR σ R) (inclE R) hsig]
      rfl
    have hdd : cT (sigR σ R) (d : Matrix (Fin n) (Fin n) (E ⊗[F] R)) * (d : Matrix (Fin n) (Fin n) (E ⊗[F] R)) = 1 := by
      rw [hd]
      unfold cT
      rw [Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext k
      by_cases hk : k = ⟨0, hn⟩
      · subst hk
        rw [hf, Pi.mulSingle_eq_same, mul_comm]
        exact hx
      · rw [hf, Pi.mulSingle_eq_of_ne hk, Units.val_one, map_one, one_mul]
    have h1 : cT (sigR σ R) ((Cb⁻¹ : GL (Fin n) (E ⊗[F] R)) : Matrix (Fin n) (Fin n) (E ⊗[F] R)) *
        cT (sigR σ R) (Cb : Matrix (Fin n) (Fin n) (E ⊗[F] R)) = 1 := by
      rw [← cT_mul, Units.mul_inv, cT_one]
    have h2 : (Cb : Matrix (Fin n) (Fin n) (E ⊗[F] R)) * ((Cb⁻¹ : GL (Fin n) (E ⊗[F] R)) : Matrix (Fin n) (Fin n) (E ⊗[F] R)) = 1 :=
      Units.mul_inv Cb
    show cT (sigR σ R) (((Cb⁻¹ * d * Cb : GL (Fin n) (E ⊗[F] R))) : Matrix (Fin n) (Fin n) (E ⊗[F] R)) * Gm.map (inclE (F := F) R) *
      (((Cb⁻¹ * d * Cb : GL (Fin n) (E ⊗[F] R))) : Matrix (Fin n) (Fin n) (E ⊗[F] R)) = Gm.map (inclE (F := F) R)
    rw [hG, Units.val_mul, Units.val_mul, cT_mul, cT_mul]
    calc _ = cT (sigR σ R) (Cb : Matrix (Fin n) (Fin n) (E ⊗[F] R)) * cT (sigR σ R) (d : Matrix (Fin n) (Fin n) (E ⊗[F] R)) *
          (cT (sigR σ R) ((Cb⁻¹ : GL (Fin n) (E ⊗[F] R)) : Matrix (Fin n) (Fin n) (E ⊗[F] R)) * cT (sigR σ R) (Cb : Matrix (Fin n) (Fin n) (E ⊗[F] R))) *
          ((Cb : Matrix (Fin n) (Fin n) (E ⊗[F] R)) * ((Cb⁻¹ : GL (Fin n) (E ⊗[F] R)) : Matrix (Fin n) (Fin n) (E ⊗[F] R))) *
          (d : Matrix (Fin n) (Fin n) (E ⊗[F] R)) * (Cb : Matrix (Fin n) (Fin n) (E ⊗[F] R)) := by
            simp only [Matrix.mul_assoc]
      _ = cT (sigR σ R) (Cb : Matrix (Fin n) (Fin n) (E ⊗[F] R)) *
          (cT (sigR σ R) (d : Matrix (Fin n) (Fin n) (E ⊗[F] R)) * (d : Matrix (Fin n) (Fin n) (E ⊗[F] R))) *
          (Cb : Matrix (Fin n) (Fin n) (E ⊗[F] R)) := by
            rw [h1, h2]
            simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = _ := by rw [hdd, Matrix.mul_one]
  · ext
    simp only [Matrix.GeneralLinearGroup.val_det_apply, Units.val_mul, Matrix.det_mul, hd, Matrix.det_diagonal]
    rw [← Units.coe_prod, hf, Finset.prod_pi_mulSingle', if_pos (Finset.mem_univ _)]
    calc _ = (Matrix.det ((Cb⁻¹ : GL (Fin n) (E ⊗[F] R)) : Matrix (Fin n) (Fin n) (E ⊗[F] R)) *
          Matrix.det (Cb : Matrix (Fin n) (Fin n) (E ⊗[F] R))) * (x : E ⊗[F] R) := by ring
      _ = _ := by rw [← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one, one_mul]

end Gen

end GlobalTheory.TwV.Xc.ChiPow

namespace GlobalTheory.TwV.Xc.ChiPow

set_option maxHeartbeats 4000000 in

theorem tw_ch_rat {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
    {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P} {p : ℕ} {i : ℕ} {hi : i ≤ D.R.m} {G : GAtP p}
    (S : StepIn M i hi G) (β : S.Ch) (hr : S.ChRat β)
    (X : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) :
    ∃ r : D.what₂.LL, D.what₂.embLL r = ((S.tw β).ch X : ℂ) := by
  obtain ⟨cl, hcl⟩ := (S.K β).y_bij.2 (Quotient.mk'' X)
  have hrel := Quotient.eq''.1 hcl
  rw [DoubleCoset.rel_iff] at hrel
  obtain ⟨h, hh, k, hk, hX⟩ := hrel
  obtain ⟨γ, hγ, hγh⟩ := hh
  have h1 := (S.tw β).ch_rat γ hγ h hγh.symm
  have h2 := (S.tw β).ch_U k hk
  obtain ⟨rc, hrc⟩ := hr cl
  refine ⟨(∏ τ, (tEL D τ (γ : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E).det) ^ (cTw D i))⁻¹ * rc, ?_⟩
  rw [hX, map_mul (S.tw β).ch, map_mul (S.tw β).ch, h2, mul_one, Units.val_mul, map_mul D.what₂.embLL, hrc, map_inv₀, map_prod]
  congr 1
  have e1 : ∏ τ, D.what₂.embLL (tEL D τ (γ : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E).det ^ cTw D i) =
      ∏ τ, (embT D τ (γ : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E).det) ^ cTw D i :=
    Finset.prod_congr rfl fun τ _ => by rw [map_zpow₀, tEL_emb]
  rw [e1]
  exact (eq_inv_of_mul_eq_one_left h1).symm

end GlobalTheory.TwV.Xc.ChiPow

namespace GlobalTheory.TwV.Xc

set_option maxHeartbeats 4000000 in

theorem chiI_pow_rat : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ j (hj : j ≤ D.R.m), (sysS H X std).Lv.comp j → ∀ x ∈ U1 (sigD D), ∃ r : D.what₂.LL, D.what₂.embLL r = chiI J x ^ (((j * ((sysS H X std).t + 1) / 2 : ℕ) : ℤ))) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S _ _ j hj c x hx
  cases j with
  | zero => exact ⟨1, by simp⟩
  | succ i =>
    have hi : i + 1 ≤ D.R.m := hj
    have hxc : (x : AfE D.host.F D.host.E) * sigR (sigD D) _ x = 1 := congrArg Units.val (MonoidHom.mem_ker.1 hx)
    obtain ⟨Y, hY, hYd⟩ := ChiPow.exists_upts_det (sigD D) Nat.one_pos (1 : Matrix (Fin 1) (Fin 1) D.host.E) 1
      (by rw [Units.val_one, cT_one, Matrix.one_mul]) x hxc
    have hex : ∃ y : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm, Matrix.GeneralLinearGroup.det y.1 = x := ⟨⟨Y, hY⟩, hYd⟩
    have hchi : chiI J x = ((D.chiD (J.dtU hex.choose) : ℂˣ) : ℂ) := by
      unfold chiI
      rw [dif_pos hex]
    obtain ⟨Z, hZ, hZd⟩ := ChiPow.exists_upts_det (sigD D) (D.R.N_pos (i + 1)) (gramN D (i + 1) hi) (J.A.crd (i + 1) hi)
      (J.pins.crd_orth (i + 1) hi) x hxc
    let β := ((I.at' i hi).st.eC.symm c).1
    have htw := J.tw i hi β ⟨Z, hZ⟩ hex.choose (hex.choose_spec.trans hZd.symm)
    obtain ⟨r, hr⟩ := ChiPow.tw_ch_rat (I.at' i hi).st β (H.core i hi β).chRat ⟨Z, hZ⟩
    have ht : (sysS H X std).t = D.R.t := (GlobalTheory.TwV.DelB.sysS_ranks S).2.1
    refine ⟨r, ?_⟩
    rw [hr, htw, hchi, ht, Units.val_zpow_eq_zpow_val]
    rfl

end GlobalTheory.TwV.Xc

end
