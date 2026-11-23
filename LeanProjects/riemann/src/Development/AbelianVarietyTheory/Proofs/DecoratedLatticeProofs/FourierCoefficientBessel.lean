import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ThetaIdentityOfMapsAll
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.KerJoinS
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.HermitianETransportInvariant
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHAlg
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CovariantRepresentation
import Formalism.LocalToGlobal.IndefiniteReal.RationalEmbedding
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Core.Mi.PhCol

variable {D : D7}

theorem one_le_level (X : HidaSetting D) : 1 ≤ X.B.g := by
  rw [X.g_eq]
  exact Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos

theorem one_mem_level (X : HidaSetting D) : (1 : X.B.I.Gf) ∈ X.B.I.Kg X.B.g := by
  refine ⟨(Formalism.UG.stabGL X.B.I.Lf).one_mem, fun y _ => ⟨0, zero_mem _, ?_⟩⟩
  have h1 : X.B.I.fmat 1 = 1 := rfl
  rw [h1, sub_self, Matrix.zero_mulVec, smul_zero]

theorem psiInfU_of_mem_Hinf (X : HidaSetting D) (u : D.what₂.Word) (η : X.B.I.Ginf) (hη : η ∈ Hinf X u) :
    X.psiInfU u η = 1 := by
  have e := Formalism.L2.SG.PoincareInHH.Cut.psiInf_mul_H X u 1 η hη
  rw [one_mul] at e
  rw [e]
  exact Formalism.L2.SG.CovariantRepresentation.psiInfU_one X u

theorem castGA_mem_rat {I I' : Formalism.MainNotions.S.AutInst} (e : I = I') (x : I.GA) :
    x ∈ I.GFset ↔ castGA e x ∈ I'.GFset := by
  subst e; rfl

theorem iotaX_mem_rat (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (g : GA D (D.sp.Y 0))
    (hg : g ∈ GQ (D.sp.Y 0)) : iotaX X h g ∈ X.B.I.GFset := by
  have e : iotaX X h g = castGA h.symm (Formalism.IndefR.RationalEmbedding.iota D g) := rfl
  rw [e]
  exact (castGA_mem_rat h.symm _).1 ((Formalism.IndefR.RationalEmbedding.iota_rat D g).1 hg)

theorem Ph_of_dec (X : HidaSetting D) (u : D.what₂.Word) (hK : X.LevelSubgroupCharacter) (T : Cu X u hK) (y : X.B.I.GA)
    (n : X.B.I.Gf) (hh : Hfin X u) (k : X.B.I.Gf) (hd : IsDec X u y.2 n hh k) :
    Ph X u hK T y = phVal X u hK T y.1 n hh k := by
  have hex : ∃ n h k, IsDec X u y.2 n h k := ⟨n, hh, k, hd⟩
  unfold Ph
  rw [dif_pos hex]
  exact Formalism.L2.SG.Pf.phWellDef_holds X u T y.1 y.2 _ n _ k _ hh hex.choose_spec.choose_spec.choose_spec hd

variable {X : HidaSetting D} {h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D} {u : D.what₂.Word}
  {ψ : AddChar (AF D.host.F) ℂ} {A : HSp D}

theorem continuous_toH (B : SBes X h u ψ A) : Continuous B.toH := by
  have he : Continuous (embA B.d B.o) := by
    have e : (embA B.d B.o : GA D A → GA D (D.sp.Y 0)) = fun a => B.d.emb0 (B.o.emb (a, 1)) := rfl
    rw [e]
    exact B.d.continuous_embed.comp (B.o.continuous_emb.comp (continuous_id.prodMk continuous_const))
  have hc : Continuous fun a => iotaX X h (embA B.d B.o a) := (iotaX X h).continuous.comp he
  unfold SBes.toH
  exact (hc.fst.subtype_mk _).prodMk (hc.snd.subtype_mk _)

theorem continuous_col (hK : X.LevelSubgroupCharacter) (T : Cu X u hK) (ξ : X.Vpi u) :
    Continuous fun p : Hinf X u × Hfin X u => (T : X.Vpi u →ₗ[ℂ] (Hinf X u × Hfin X u → ℂ)) ξ p := by
  obtain ⟨hT1, hT2⟩ := T.2
  have hL := Formalism.L2.SG.Closed.level_subgroup_properties X
  rw [continuous_iff_continuousAt]
  intro p0
  have hπ : Continuous fun η : Hinf X u => X.piU u η ξ :=
    ((X.piU_rep u).2.2.2.2 ξ).comp_continuous continuous_subtype_val (fun η => hinf_le_sinf X u _ η.2)
  let L : X.Vpi u →ₗ[ℂ] ℂ :=
    (LinearMap.proj (R := ℂ) (φ := fun _ : Hinf X u × Hfin X u => ℂ) ((1 : Hinf X u), p0.2)).comp
      (T : X.Vpi u →ₗ[ℂ] (Hinf X u × Hfin X u → ℂ))
  have hG : Continuous fun p : Hinf X u × Hfin X u => L (X.piU u p.1 ξ) :=
    L.continuous_of_finiteDimensional.comp (hπ.comp continuous_fst)
  have hUo : IsOpen {p : Hinf X u × Hfin X u |
      (X.xu u)⁻¹ * ((p0.2⁻¹ * p.2 : Hfin X u) : X.B.I.Gf) * X.xu u ∈ X.B.I.Kg X.B.g} := by
    refine (X.B.I.topf_open X.B.g (one_le_level X)).preimage ?_
    exact (continuous_const.mul (continuous_subtype_val.comp (continuous_const.mul continuous_snd))).mul
      continuous_const
  have hp0 : p0 ∈ {p : Hinf X u × Hfin X u |
      (X.xu u)⁻¹ * ((p0.2⁻¹ * p.2 : Hfin X u) : X.B.I.Gf) * X.xu u ∈ X.B.I.Kg X.B.g} := by
    show (X.xu u)⁻¹ * ((p0.2⁻¹ * p0.2 : Hfin X u) : X.B.I.Gf) * X.xu u ∈ X.B.I.Kg X.B.g
    rw [inv_mul_cancel]
    simpa using one_mem_level X
  refine hG.continuousAt.congr (Filter.eventually_of_mem (hUo.mem_nhds hp0) fun p hp => ?_)
  obtain ⟨η, k⟩ := p
  have hp' : (X.xu u)⁻¹ * ((p0.2⁻¹ * k : Hfin X u) : X.B.I.Gf) * X.xu u ∈ X.B.I.Kg X.B.g := hp
  obtain ⟨hK2, hχ⟩ := hL.1 _ hp'
  let κ : Ku X u hK := ⟨p0.2⁻¹ * k, hK2⟩
  have e1 : ((η, k) : Hinf X u × Hfin X u) = (η, p0.2) * (1, ((κ : Hfin X u))) := by
    ext
    · simp
    · simp [κ]
  have e2 : ((η, p0.2) : Hinf X u × Hfin X u) = (1, p0.2) * (η, 1) := by
    ext <;> simp
  have hψ : ((psiK X u hK κ : ℂˣ) : ℂ) = 1 := hχ
  show L (X.piU u η ξ) = (T : X.Vpi u →ₗ[ℂ] (Hinf X u × Hfin X u → ℂ)) ξ (η, k)
  rw [e1, (hT1 ξ).2 (η, p0.2) κ, hψ, one_mul, e2, ← hT2 η ξ (1, p0.2)]
  rfl

end GlobalTheory.Core.Mi.PhCol

namespace GlobalTheory.Core.Mi.PhCol

theorem ph_colForm : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (A : HSp D) (B : SBes X h u ψ A) (hK : X.LevelSubgroupCharacter) (T : Cu X u hK),
    (∀ ξ, IsContAut A (B.colForm T.1 ξ)) ∧ ∀ n ∈ flagN B.d, ∀ (a : GA D A) (y : X.B.I.Ginf),
      Ph X u hK T (iotaX X h (n * embA B.d B.o a) * (y, X.xu u)) =
        star (psiBes ψ B.d 1 (vecB B.o B.ζ) n) * B.colForm T.1 (X.Wu u y) a := by
  intro D X h u ψ A B hK T
  obtain ⟨hT1, hT2⟩ := T.2
  refine ⟨fun ξ => ⟨fun γ hγ g => ?_, ?_⟩, fun n hn a y => ?_⟩
  ·
    have hrat : embA B.d B.o γ ∈ GQ (D.sp.Y 0) := by
      have e : embA B.d B.o γ = B.d.emb0 (B.o.emb (γ, 1)) := rfl
      rw [e]
      exact B.d.wittDecomp_anisotropicEmbedding_mem_rationalPoints (B.o.emb_mem_GQ hγ (one_mem _))
    have hr := iotaX_mem_rat X h _ hrat
    have hH := (B.tieH (embA B.d B.o γ)).1 ⟨γ, rfl⟩
    let γ' : Gam X u := ⟨iotaX X h (embA B.d B.o γ), Subgroup.mem_inf.2 ⟨hr, Subgroup.mem_prod.2 hH⟩⟩
    have e : B.toH (γ * g) = (iotaI X u γ', iotaF X u γ') * B.toH g := by
      refine Prod.ext ?_ ?_ <;> apply Subtype.ext
      · show (iotaX X h (embA B.d B.o (γ * g))).1 = (iotaX X h (embA B.d B.o γ)).1 * (iotaX X h (embA B.d B.o g)).1
        rw [map_mul, map_mul, Prod.fst_mul]
      · show (iotaX X h (embA B.d B.o (γ * g))).2 = (iotaX X h (embA B.d B.o γ)).2 * (iotaX X h (embA B.d B.o g)).2
        rw [map_mul, map_mul, Prod.snd_mul]
    show (T : X.Vpi u →ₗ[ℂ] (Hinf X u × Hfin X u → ℂ)) ξ (B.toH (γ * g)) =
      (T : X.Vpi u →ₗ[ℂ] (Hinf X u × Hfin X u → ℂ)) ξ (B.toH g)
    rw [e]
    exact (hT1 ξ).1 γ' (B.toH g)
  ·
    exact (continuous_col hK T ξ).comp (continuous_toH B)
  ·
    obtain ⟨hn1, hn2⟩ := (B.tieN n).1 hn
    obtain ⟨ha1, ha2⟩ := (B.tieH (embA B.d B.o a)).1 ⟨a, rfl⟩
    set m := iotaX X h n with hm
    set b := iotaX X h (embA B.d B.o a) with hb
    have e : iotaX X h (n * embA B.d B.o a) * (y, X.xu u) = (m.1 * b.1 * y, m.2 * b.2 * X.xu u * 1) := by
      rw [map_mul, ← hm, ← hb]
      ext <;> simp [mul_assoc]
    have hd : IsDec X u (m.1 * b.1 * y, m.2 * b.2 * X.xu u * 1).2 m.2 ⟨b.2, ha2⟩ 1 :=
      ⟨hn2, one_mem_level_subgroup X, rfl⟩
    rw [e, Ph_of_dec X u hK T _ _ _ _ hd]
    unfold phVal
    have hm1S : m.1 ∈ X.SinfU u := fun v => (hn1 v).1
    have hb1S : b.1 ∈ X.SinfU u := hinf_le_sinf X u _ ha1
    have hW : X.Wu u (m.1 * b.1 * y) = X.psiInfU u m.1 • X.piU u b.1 (X.Wu u y) := by
      rw [mul_assoc, (X.Wu_spec u).1 m.1 hm1S, (X.piU_rep u).2.2.2.1 m.1 hn1, ContinuousLinearMap.one_apply,
        (X.Wu_spec u).1 b.1 hb1S]
      have hpsi : X.psiInfU u b.1 = 1 := psiInfU_of_mem_Hinf X u b.1 ha1
      change X.psiInfU u m.1 • (X.psiInfU u b.1 • X.piU u b.1 (X.Wu u y)) = _
      rw [hpsi, one_smul]
    have hC : (T : X.Vpi u →ₗ[ℂ] (Hinf X u × Hfin X u → ℂ)) (X.piU u b.1 (X.Wu u y)) (1, ⟨b.2, ha2⟩) =
        B.colForm T.1 (X.Wu u y) a := by
      have := hT2 ⟨b.1, ha1⟩ (X.Wu u y) (1, ⟨b.2, ha2⟩)
      refine this.trans ?_
      show (T : X.Vpi u →ₗ[ℂ] (Hinf X u × Hfin X u → ℂ)) (X.Wu u y) ((1, ⟨b.2, ha2⟩) * (⟨b.1, ha1⟩, 1)) =
        (T : X.Vpi u →ₗ[ℂ] (Hinf X u × Hfin X u → ℂ)) (X.Wu u y) (B.toH a)
      refine congrArg ((T : X.Vpi u →ₗ[ℂ] (Hinf X u × Hfin X u → ℂ)) (X.Wu u y)) ?_
      refine Prod.ext ?_ ?_ <;> apply Subtype.ext
      · show (1 : X.B.I.Ginf) * b.1 = (iotaX X h (embA B.d B.o a)).1
        rw [one_mul]
      · show b.2 * (1 : X.B.I.Gf) = (iotaX X h (embA B.d B.o a)).2
        rw [mul_one]
    rw [hW, map_smul, Pi.smul_apply, smul_eq_mul, hC, chi2_apply_one X hK, B.tieψ n hn]
    ring

end GlobalTheory.Core.Mi.PhCol
