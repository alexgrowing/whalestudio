import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFundamentalDomainMulRight
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.AdelicIsomorphismStatement
import Formalism.SharpRestriction.CuspSpanNormBounds.NonemptyParameterModels.UnitaryPointsRankZeroSubsingleton
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BridgeSIsBridge
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability GlobalTheory.ThetaCplV
open Matrix
open scoped TensorProduct
noncomputable section

namespace GlobalTheory.HCFinU.KinfBridge

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.AdBridge

theorem bridgeS_mat (I : Formalism.MainNotions.S.AutInst) (s : I.E →ₐ[I.F] I.E) (hs : s = I.cm.sig) (x : I.GA) :
    ((HA.mat (AF I.F) s I.J (bridgeS I s hs x) : GL (Fin I.n) (AF I.F ⊗[I.F] I.E)) :
      Matrix (Fin I.n) (Fin I.n) (AF I.F ⊗[I.F] I.E)) = hmat I (bridgeS I I.cm.sig rfl x) := by
  subst hs
  rfl

theorem smul_eq_zero_of_tauF (I : Formalism.MainNotions.S.AutInst) (z : AF I.F ⊗[I.F] I.E) (hz : tauF I z = 0)
    (u : AF I.F) (hu : u.1 = 0) : u • z = 0 := by
  let ι : Formalism.MainNotions.S.Af I.F →ₗ[I.F] AF I.F := LinearMap.inr I.F (InfiniteAdeleRing I.F) (Formalism.MainNotions.S.Af I.F)
  let Φ : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F →ₗ[I.F] AF I.F ⊗[I.F] I.E :=
    (TensorProduct.comm I.F I.E (AF I.F)).toLinearMap ∘ₗ
      (LinearMap.lTensor I.E (ι ∘ₗ LinearMap.mulLeft I.F u.2))
  have key : ∀ y : AF I.F ⊗[I.F] I.E, u • y = Φ (tauF I y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul b x =>
      rw [tauF_tmul]
      have hb : u * b = ι (u.2 * b.2) := Prod.ext (by show u.1 * b.1 = 0; rw [hu, zero_mul]) rfl
      simp only [Φ, LinearMap.coe_comp, Function.comp_apply, LinearMap.lTensor_tmul, LinearEquiv.coe_coe,
        TensorProduct.comm_tmul, LinearMap.mulLeft_apply]
      rw [TensorProduct.smul_tmul', smul_eq_mul, hb]
    | add x y hx hy => rw [smul_add, hx, hy, map_add, map_add]
  rw [key, hz, map_zero]

theorem thetaV_eq (I : Formalism.MainNotions.S.AutInst) (v : InfinitePlace I.F) (τ : EmbOver I.E v) (hτ : I.φ v = τ.1)
    (z : AF I.F ⊗[I.F] I.E) : thetaV I v z = piInf τ z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    rw [thetaV_tmul, hτ]
    have h : compInf I.F I.E v (a ⊗ₜ[I.F] x) = (a.1 v) ⊗ₜ[I.F] x := rfl
    show _ = infEmb τ (compInf I.F I.E v (a ⊗ₜ[I.F] x))
    rw [h, infEmb_tmul]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem commute_of_conj {n : ℕ} (P M T : Matrix (Fin n) (Fin n) ℂ) (hP : IsUnit P)
    (h : Commute (P⁻¹ * M * P) (P⁻¹ * T * P)) : Commute M T := by
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det _).1 hP
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have key : ∀ X Y : Matrix (Fin n) (Fin n) ℂ, P * ((P⁻¹ * X * P) * (P⁻¹ * Y * P)) * P⁻¹ = X * Y := by
    intro X Y
    calc P * ((P⁻¹ * X * P) * (P⁻¹ * Y * P)) * P⁻¹
        = (P * P⁻¹) * X * (P * P⁻¹) * Y * (P * P⁻¹) := by simp only [Matrix.mul_assoc]
      _ = X * Y := by rw [h1]; simp
  show M * T = T * M
  rw [← key M T, ← key T M, h.eq]

theorem bridge_kinf (I : Formalism.MainNotions.S.AutInst) (k : GlobalTheory.Dec.Kinf I) :
    At (evI I.F) (hmat I (bridgeS I I.cm.sig rfl ((fun v => (k v).1), 1)) - 1) ∧
    ∀ v (T : Matrix (Fin I.n) (Fin I.n) ℂ),
      ((I.P v)⁻¹ * T * I.P v = Formalism.REAL.Jm (I.ε v) ∨ (I.P v)⁻¹ * T * I.P v = -Formalism.REAL.Jm (I.ε v)) →
      Commute ((hmat I (bridgeS I I.cm.sig rfl ((fun v => (k v).1), 1))).map (thetaV I v)) T := by
  obtain ⟨h1, h2⟩ := bridgeS_isBridge I ((fun v => (k v).1), 1)
  refine ⟨fun u hu => ?_, fun v T hT => ?_⟩
  · have hu1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace I.F).injective (hu.trans (map_zero _).symm)
    ext i j
    rw [Matrix.smul_apply, Matrix.zero_apply]
    refine smul_eq_zero_of_tauF I _ ?_ u hu1
    have h3 : (1 : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) =
        (hmat I (bridgeS I I.cm.sig rfl ((fun v => (k v).1), 1))).map (tauF I) := h2
    have h4 := congrFun (congrFun h3 i) j
    rw [Matrix.map_apply] at h4
    rw [Matrix.sub_apply, map_sub, ← h4]
    by_cases hij : i = j
    · subst hij; simp
    · simp [Matrix.one_apply_ne hij]
  · refine commute_of_conj (I.P v) _ T (I.P_unit v) ?_
    have h3 : Formalism.REAL.toM (k v).1 = (I.P v)⁻¹ *
        (hmat I (bridgeS I I.cm.sig rfl ((fun v => (k v).1), 1))).map (thetaV I v) * I.P v := h1 v
    have h4 : Formalism.REAL.toM (k v).1 ∈ Formalism.REAL.Kset (I.ε v) := (k v).2
    have h5 : Commute (Formalism.REAL.toM (k v).1) (Formalism.REAL.Jm (I.ε v)) := h4.2
    rw [← h3]
    rcases hT with hT | hT
    · rw [hT]; exact h5
    · rw [hT]; exact h5.neg_right

theorem main : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (B : Base F E) (d r s : ℕ) (W : Spc F E d), B.IsGood σ → W.IsSkew σ B r s → ∀ (c : E) (hc : c ≠ 0), σ c = -c → ∀ (cm : @Formalism.BasicNotions.CMData F E _ _ _ _ (GlobalTheory.HCFinU.starOf σ hσ) _) (hJ : ∀ i j, σ ((c • W.J.map σ) j i) = (c • W.J.map σ) i j) (hdet : (c • W.J.map σ).det ≠ 0) (L : Submodule (𝓞 E) (Fin d → E)) (hfg : L.FG) (hspan : Submodule.span E (L : Set (Fin d → E)) = ⊤) (hdual : ∀ x : Fin d → E, x ∈ L ↔ ∀ y ∈ L, Formalism.UG.hform (σ : E →+* E) (c • W.J.map σ) y x ∈ (algebraMap (𝓞 E) E).range) (ε : InfinitePlace F → Fin d → Bool) (hφ : ∀ v (a : F), (B.emb v).1 (algebraMap F E a) = v.embedding a) (P : InfinitePlace F → Matrix (Fin d) (Fin d) ℂ) (hPu : ∀ v, IsUnit (P v)) (hP : ∀ v, (P v)ᴴ * (c • W.J.map σ).map (B.emb v).1 * P v = Formalism.REAL.Jm (ε v)), (∀ v, (P v)⁻¹ * W.θ v * P v = Formalism.REAL.Jm (ε v) ∨ (P v)⁻¹ * W.θ v * P v = -Formalism.REAL.Jm (ε v)) → ∀ (hs : σ = (GlobalTheory.HCFinU.mkI σ hσ cm (c • W.J.map σ) hJ hdet L hfg hspan hdual ε (fun v => (B.emb v).1) hφ P hPu hP).cm.sig) (k : GlobalTheory.Dec.Kinf (GlobalTheory.HCFinU.mkI σ hσ cm (c • W.J.map σ) hJ hdet L hfg hspan hdual ε (fun v => (B.emb v).1) hφ P hPu hP)), (toGAd hσ W.J hc).symm (GlobalTheory.HCFinU.bridgeS (GlobalTheory.HCFinU.mkI σ hσ cm (c • W.J.map σ) hJ hdet L hfg hspan hdual ε (fun v => (B.emb v).1) hφ P hPu hP) σ hs ((fun v => (k v).1), 1)) ∈ KInf σ W B.emb := by
  intro F E _ _ _ _ _ σ hσ B d r s W _ _ c hc _ cm hJ hdet L hfg hspan hdual ε hφ P hPu hP hθ hs k
  have hb := bridge_kinf (GlobalTheory.HCFinU.mkI σ hσ cm (c • W.J.map σ) hJ hdet L hfg hspan hdual ε (fun v => (B.emb v).1) hφ P hPu hP) k
  have hm := bridgeS_mat (GlobalTheory.HCFinU.mkI σ hσ cm (c • W.J.map σ) hJ hdet L hfg hspan hdual ε (fun v => (B.emb v).1) hφ P hPu hP) σ hs ((fun v => (k v).1), 1)
  rw [← hm] at hb
  generalize GlobalTheory.HCFinU.bridgeS (GlobalTheory.HCFinU.mkI σ hσ cm (c • W.J.map σ) hJ hdet L hfg hspan hdual ε (fun v => (B.emb v).1) hφ P hPu hP) σ hs ((fun v => (k v).1), 1) = h at hb ⊢
  have hg := toGAd_mat hσ W.J hc ((toGAd hσ W.J hc).symm h)
  replace hg := (congrArg (HA.mat (AF F) σ (c • W.J.map σ)) ((toGAd hσ W.J hc).apply_symm_apply h)).symm.trans hg
  have hg' : mat ((toGAd hσ W.J hc).symm h) =
      ((HA.mat (AF F) σ (c • W.J.map σ) h : GL (Fin d) (AF F ⊗[F] E)) : Matrix (Fin d) (Fin d) (AF F ⊗[F] E)) :=
    (congrArg Units.val hg).symm
  refine ⟨?_, fun w => ?_⟩
  · show At (evI F) (mat ((toGAd hσ W.J hc).symm h) - 1)
    rw [hg']
    exact hb.1
  · rw [hg']
    have h2 := hb.2 w (W.θ w) (hθ w)
    have h3 : (thetaV (GlobalTheory.HCFinU.mkI σ hσ cm (c • W.J.map σ) hJ hdet L hfg hspan hdual ε (fun v => (B.emb v).1) hφ P hPu hP) w : AF F ⊗[F] E → ℂ) = piInf (B.emb w) :=
      funext fun z => thetaV_eq (GlobalTheory.HCFinU.mkI σ hσ cm (c • W.J.map σ) hJ hdet L hfg hspan hdual ε (fun v => (B.emb v).1) hφ P hPu hP) w (B.emb w) rfl z
    rw [← h3]
    exact h2

end GlobalTheory.HCFinU.KinfBridge
