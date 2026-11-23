import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawWeilBiActionCommutesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittDecompositionMixedCoordsRankZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SetIntegralFundamentalDomainRightTranslateInvari
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousIntegralCompactAutomorphicQuotientPara
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumTransportSourceRationalIsometry
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittHyperbolicRankZeroProjMulEmb
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HermitianLinkMapAdditiveRationalEquivariant
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LastRed

variable {D : D7}

theorem sympl_zero_l (S T : HSp D) (x : WO S T) : symplOH S T 0 x = 0 := by
  simp [symplOH, symplO, hO]

theorem sympl_zero_r (S T : HSp D) (x : WO S T) : symplOH S T x 0 = 0 := by
  simp [symplOH, symplO, hO]

set_option maxHeartbeats 1000000 in

theorem biTheta_of_maps {ψ : AddChar (AF D.host.F) ℂ} {V₀ A S X T : HSp D} (a : WO A S →+ WO V₀ S) (b : WO S X →+ WO V₀ S)
    (p : WO S X →+ WO S T) (ca : Continuous a) (cb : Continuous b) (cp : Continuous p)
    (ra : ∀ γ, ∃ γ', a (ratW S A γ) = ratW S V₀ γ') (rb : ∀ γ, ∃ γ', b (ratW X S γ) = ratW S V₀ γ')
    (rp : ∀ γ, ∃ γ', p (ratW X S γ) = ratW T S γ')
    (fa : ∀ x : WO A S, x.map (finPart D) = 0 → (a x).map (finPart D) = 0)
    (fb : ∀ x : WO S X, x.map (finPart D) = 0 → (b x).map (finPart D) = 0)
    (fp : ∀ x : WO S X, x.map (finPart D) = 0 → (p x).map (finPart D) = 0)
    (ia : ∀ x : WO A S, x.map (infPart D) = 0 → (a x).map (infPart D) = 0)
    (ib : ∀ x : WO S X, x.map (infPart D) = 0 → (b x).map (infPart D) = 0)
    (ip : ∀ x : WO S X, x.map (infPart D) = 0 → (p x).map (infPart D) = 0)
    (hs : ∀ u v u' v', symplOH S T (p v) (p v') + symplOH V₀ S (a u + b v) (a u' + b v') =
      symplOH A S u u' + symplOH S X v v')
    {Ξ : WO V₀ S → ℂ} {Φ : WO S T → ℂ} (hΞ : IsThetaFunO ψ V₀ S Ξ) (hΦ : IsThetaFunO ψ S T Φ) :
    IsBiTheta ψ A S X fun u v => Φ (p v) * Ξ (a u + b v) where
  cont := (hΦ.cont.comp (cp.comp continuous_snd)).mul
    (hΞ.cont.comp ((ca.comp continuous_fst).add (cb.comp continuous_snd)))
  smooth n L L' hL hL' h0 h0' u v := by
    have h1 := hΦ.smooth n (p.comp L') (cp.comp hL') (fun t => fp _ (h0' t)) (p v)
    have h2 := hΞ.smooth n (a.comp L + b.comp L') ((ca.comp hL).add (cb.comp hL')) (fun t => by
      show (a (L t) + b (L' t)).map (finPart D) = 0
      rw [Matrix.map_add _ (map_add (finPart D)), fa _ (h0 t), fb _ (h0' t), add_zero]) (a u + b v)
    have e : (fun t => Φ (p (v + L' t)) * Ξ (a (u + L t) + b (v + L' t))) =
        fun t => Φ (p v + (p.comp L') t) * Ξ (a u + b v + (a.comp L + b.comp L') t) := by
      funext t
      simp only [map_add, AddMonoidHom.add_apply, AddMonoidHom.comp_apply, add_add_add_comm (a u) (a (L t))]
    rw [e]
    exact h1.mul h2
  quasiL γ u v := by
    obtain ⟨γ', e⟩ := ra γ
    have h := hs (ratW S A γ) 0 u v
    simp only [map_zero, add_zero, sympl_zero_l, zero_add] at h
    show Φ (p v) * Ξ (a (ratW S A γ + u) + b v) = _ * (Φ (p v) * Ξ (a u + b v))
    rw [map_add, add_assoc, ← h, e, hΞ.quasi]
    ring
  quasiR γ u v := by
    obtain ⟨γ', e⟩ := rb γ
    obtain ⟨γ'', e'⟩ := rp γ
    have h := hs 0 (ratW X S γ) u v
    simp only [map_zero, sympl_zero_l, zero_add] at h
    show Φ (p (ratW X S γ + v)) * Ξ (a u + b (ratW X S γ + v)) = _ * (Φ (p v) * Ξ (a u + b v))
    rw [map_add, map_add, add_left_comm, ← h, e, e', hΞ.quasi, hΦ.quasi, neg_add, AddChar.map_add_eq_mul]
    ring
  levL := by
    obtain ⟨U, hU, k⟩ := hΞ.level
    refine ⟨U.comap a, hU.preimage ca, fun x hx h0 v => funext fun u => ?_⟩
    have e := congrFun (k (a x) hx (ia x h0)) (a u + b v)
    have h := hs u v x 0
    simp only [map_zero, add_zero, sympl_zero_r, zero_add] at h
    simp only [heisO] at e ⊢
    rw [← h, map_add, add_right_comm, mul_left_comm, e]
  levR := by
    obtain ⟨U, hU, k⟩ := hΞ.level
    obtain ⟨U', hU', k'⟩ := hΦ.level
    refine ⟨U.comap b ⊓ U'.comap p, (hU.preimage cb).inter (hU'.preimage cp), fun x hx h0 u => funext fun v => ?_⟩
    have e := congrFun (k (b x) hx.1 (ib x h0)) (a u + b v)
    have e' := congrFun (k' (p x) hx.2 (ip x h0)) (p v)
    have h := hs u v 0 x
    simp only [map_zero, sympl_zero_r, zero_add] at h
    simp only [heisO] at e e' ⊢
    rw [← h, map_add p, map_add b, ← add_assoc, AddChar.map_add_eq_mul, mul_mul_mul_comm, e, e']

theorem lastBi_biTheta : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V₀ A L S X T L'' : HSp D) (o : OrthDec V₀ A L) (o'' : OrthDec X T L'') (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E), τᴴ ⬝ (L.gram ⬝ τ) = (-(D.host.xi0 * star D.host.xi0)) • L''.gram → ∀ (Ξ : WO V₀ S → ℂ) (Φ₂ : WO S T → ℂ), IsThetaFunO ψ V₀ S Ξ → IsThetaFunO ψ S T Φ₂ → IsBiTheta ψ A S X (lastBi o o'' τ Ξ Φ₂) := by
  intro D ψ V₀ A L S X T L'' o o'' τ hτ Ξ Φ₂ hΞ hΦ
  obtain ⟨kadd, kc, kr, -, ks, kz⟩ := GlobalTheory.LinkKappa.kappa_props D L L'' S τ (-1)
    (by rw [hτ]; congr 1; push_cast; ring) (kap τ S) (fun _ => rfl)
  let κ : WO S L'' →+ WO L S := AddMonoidHom.mk' (kap τ S) kadd
  let a : WO A S →+ WO V₀ S := (o.resS S).symm.toAddMonoidHom.comp (AddMonoidHom.inl _ _)
  let q : WO S X →+ WO S L'' := (AddMonoidHom.snd _ _).comp (o''.resT S).toAddMonoidHom
  let b : WO S X →+ WO V₀ S := (o.resS S).symm.toAddMonoidHom.comp ((AddMonoidHom.inr _ _).comp (κ.comp q))
  let p : WO S X →+ WO S T := (AddMonoidHom.fst _ _).comp (o''.resT S).toAddMonoidHom
  have ha : ∀ u, a u = u ⬝ o.pA := fun u => by
    show (o.resS S).symm (u, 0) = _
    rw [o.resS_symm_apply, Matrix.zero_mul, add_zero]
  have hb : ∀ v, b v = kap τ S (o''.pB ⬝ v) ⬝ o.pB := fun v => by
    show (o.resS S).symm (0, kap τ S (o''.pB ⬝ v)) = _
    rw [o.resS_symm_apply, Matrix.zero_mul, zero_add]
  have hp : ∀ v, p v = o''.pA ⬝ v := fun _ => rfl
  have hab : ∀ u v, a u + b v = (o.resS S).symm (u, kap τ S (o''.resT S v).2) := fun u v => by
    rw [ha, hb]; rfl
  have e : lastBi o o'' τ Ξ Φ₂ = fun u v => Φ₂ (p v) * Ξ (a u + b v) := by
    funext u v
    rw [hab]; rfl
  rw [e]
  refine biTheta_of_maps a b p ?_ ?_ ?_ (fun γ => ?_) (fun γ => ?_) (fun γ => ?_) (fun x hx => ?_) (fun x hx => ?_)
    (fun x hx => ?_) (fun x hx => ?_) (fun x hx => ?_) (fun x hx => ?_) (fun u v u' v' => ?_) hΞ hΦ
  · exact (o.continuous_resS_symm S).comp (continuous_id.prodMk continuous_const)
  · exact (o.continuous_resS_symm S).comp (continuous_const.prodMk
      (kc.comp (continuous_snd.comp (o''.continuous_resT S))))
  · exact continuous_fst.comp (o''.continuous_resT S)
  · obtain ⟨γ', h⟩ := ratMx_mul (rat_mem γ) (rat_mem o.qA)
    exact ⟨γ', (ha _).trans h.symm⟩
  · obtain ⟨γ', h⟩ := ratMx_mul (kr _ (ratMx_mul (rat_mem o''.qB) (rat_mem γ))) (rat_mem o.qB)
    exact ⟨γ', (hb _).trans h.symm⟩
  · obtain ⟨γ', h⟩ := ratMx_mul (rat_mem o''.qA) (rat_mem γ)
    exact ⟨γ', (hp _).trans h.symm⟩
  · rw [ha]; exact map_mul_eq_zero_left _ hx _
  · rw [hb]; exact map_mul_eq_zero_left _ ((kz _).2 (map_mul_eq_zero_right _ _ hx)) _
  · rw [hp]; exact map_mul_eq_zero_right _ _ hx
  · rw [ha]; exact map_mul_eq_zero_left _ hx _
  · rw [hb]; exact map_mul_eq_zero_left _ ((kz _).1 (map_mul_eq_zero_right _ _ hx)) _
  · rw [hp]; exact map_mul_eq_zero_right _ _ hx
  · have k : ∀ w w', symplOH L S (kap τ S w) (kap τ S w') = symplOH S L'' w w' := fun w w' => by
      rw [symplOH, symplOH, ks]; push_cast; ring
    rw [hab, hab, o.symplOH_resS, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, o''.symplOH_resT S v v', k]
    show symplOH S T (o''.resT S v).1 (o''.resT S v').1 + _ = _
    ring

end GlobalTheory.LastRed

namespace GlobalTheory.LastRed

theorem integral_automorphic_rankZeroWittEmbedding : ∀ (D : D7) (S S₀ : HSp D) (d : HypDec S S₀ 0) (v : Vol S) (v₀ : Vol S₀), v.μ = Measure.map d.emb0 v₀.μ → ∀ f : GA D S → ℂ, (∀ γ ∈ GQ S, ∀ g, f (γ * g) = f g) → ∫ g in v.𝓕, f g ∂v.μ = ∫ g in v₀.𝓕, f (d.emb0 g) ∂v₀.μ := by
  intro D S S₀ d v v₀ hμ f hf
  haveI : BorelSpace (GA D S) := ⟨rfl⟩
  haveI : BorelSpace (GA D S₀) := ⟨rfl⟩
  haveI : IsTopologicalGroup (GA D S₀) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  haveI : Countable (GQ S₀) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig S₀.gram
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableConstSMul_subgroup (GQ S₀)
  haveI := v₀.haar
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.smulInvariant_subgroup (GQ S₀) v₀.μ
  have hbkc : Continuous (GlobalTheory.WeilSrc.Zero.back d) := continuous_of_mt S₀ (by
    simp only [GlobalTheory.WeilSrc.Zero.back, mt_ofMat]
    exact (continuous_const.matrix_mul (continuous_mt S)).matrix_mul continuous_const)
  have hli : ∀ g, GlobalTheory.WeilSrc.Zero.back d (d.emb0 g) = g := fun g =>
    d.wittDecomp_anisotropicEmbedding_injective (GlobalTheory.WeilSrc.Zero.witt_decomposition_zero_embedding_left_inverse d _)
  let e : GA D S₀ ≃ₜ GA D S :=
    { toFun := d.emb0, invFun := GlobalTheory.WeilSrc.Zero.back d, left_inv := hli, right_inv := GlobalTheory.WeilSrc.Zero.witt_decomposition_zero_embedding_left_inverse d,
      continuous_toFun := d.continuous_embed, continuous_invFun := hbkc }
  let em := e.toMeasurableEquiv
  have hmap : Measure.map d.emb0 v₀.μ = Measure.map em v₀.μ := rfl
  have hmem : ∀ γ : GQ S, GlobalTheory.WeilSrc.Zero.back d γ ∈ GQ S₀ := fun γ => by
    rw [mem_GQ_iff]
    simp only [GlobalTheory.WeilSrc.Zero.back, mt_ofMat]
    exact ratMx_mul (ratMx_mul (rat_mem _) ((mem_GQ_iff S γ).1 γ.2)) (rat_mem _)
  have hfd : IsFundamentalDomain (GQ S₀) (em ⁻¹' v.𝓕) v₀.μ := by
    have h := v.fund
    rw [hμ, hmap] at h
    refine h.preimage_of_equiv (em.measurable.measurePreserving v₀.μ).quasiMeasurePreserving
      (e := fun γ : GQ S => (⟨GlobalTheory.WeilSrc.Zero.back d γ, hmem γ⟩ : GQ S₀)) ⟨fun a b hab => ?_, fun γ₀ => ?_⟩ ?_
    · apply Subtype.ext
      have := congrArg (fun x : GQ S₀ => d.emb0 x) hab
      simpa [GlobalTheory.WeilSrc.Zero.witt_decomposition_zero_embedding_left_inverse] using this
    · exact ⟨⟨d.emb0 γ₀, d.wittDecomp_anisotropicEmbedding_mem_rationalPoints γ₀.2⟩, Subtype.ext (hli _)⟩
    · intro γ x
      show d.emb0 (GlobalTheory.WeilSrc.Zero.back d γ * x) = (γ : GA D S) * d.emb0 x
      rw [map_mul, GlobalTheory.WeilSrc.Zero.witt_decomposition_zero_embedding_left_inverse]
  rw [hμ, hmap, em.restrict_map, integral_map_equiv]
  exact hfd.setIntegral_eq v₀.fund (fun γ x => by
    show f (d.emb0 ((γ : GA D S₀) * x)) = f (d.emb0 x)
    rw [map_mul]
    exact hf _ (d.wittDecomp_anisotropicEmbedding_mem_rationalPoints γ.2) _)

end GlobalTheory.LastRed

namespace GlobalTheory.LastRed

theorem flatBF_rankZero : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (B : BesLev D 0) (J : JacLev D 0) (s : StepBF ψ B J) (Ψ : WO B.V J.W → ℂ), flatBF s Ψ = fun w => Ψ (B.d.ext0 J.W (J.d.inc0 B.V₀ w)) := by
  intro D ψ B J s Ψ
  funext w
  have hS := (GlobalTheory.Unf.mixRankZero D ψ).1 B.V B.V₀ J.W B.d s.vS.μ s.vS.𝓕 s.vS.covol
  have hT := (GlobalTheory.Unf.mixRankZero D ψ).2.1 B.V₀ J.W J.W₀ J.d s.vT.μ s.vT.𝓕 s.vT.covol
  simp only [flatBF, flat, flatAt, flatFun, evalAt, hS, hT]
  have hpsi : ∀ u : UX D 0, psiUni ψ u.1 = 1 := fun u => by
    simp [psiUni, upSum, psiE]
  simp only [hpsi, star_one, one_mul, integral_const, smul_eq_mul]
  obtain ⟨-, 𝓤, -, h𝓤⟩ := s.vU.unit
  have hsub : Subsingleton (UX D 0) := by
    refine ⟨fun x y => Subtype.ext (Units.ext (Subsingleton.elim _ _))⟩
  have hne : 𝓤.Nonempty := by
    by_contra hc
    rw [Set.not_nonempty_iff_eq_empty] at hc
    simp [hc] at h𝓤
  have hU : 𝓤 = Set.univ := by
    obtain ⟨x, hx⟩ := hne
    ext y
    simp [Subsingleton.elim y x, hx]
  have h1 : s.vU.ν Set.univ = 1 := by rw [← hU, h𝓤]
  simp [Measure.real, h1]

end GlobalTheory.LastRed

namespace GlobalTheory.LastRed

variable {D : D7}

theorem ker_inv {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle} {om : Om S T}
    (hom : IsWeilDatumO ψ S T χS χT om) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) {γ : GA D S} (hγ : γ ∈ GQ S)
    {γ' : GA D T} (hγ' : γ' ∈ GQ T) (g : GA D S) (h : GA D T) : om (γ * g, γ' * h) f 0 = om (g, h) f 0 := by
  have e : ((γ * g, γ' * h) : GA D S × GA D T) = (γ, γ') * (g, h) := rfl
  rw [e, map_mul, Module.End.mul_apply]
  exact hom.om_aut γ hγ γ' hγ' _ (hom.om_pres _ _ hf)

theorem ker_inv_right {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle} {om : Om S T}
    (hom : IsWeilDatumO ψ S T χS χT om) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) {γ' : GA D T} (hγ' : γ' ∈ GQ T)
    (g : GA D S) (h : GA D T) : om (g, γ' * h) f 0 = om (g, h) f 0 := by
  simpa using ker_inv hom hf (one_mem (GQ S)) hγ' g h

theorem ker_inv_left {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle} {om : Om S T}
    (hom : IsWeilDatumO ψ S T χS χT om) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) {γ : GA D S} (hγ : γ ∈ GQ S)
    (g : GA D S) (h : GA D T) : om (γ * g, h) f 0 = om (g, h) f 0 := by
  simpa using ker_inv hom hf hγ (one_mem (GQ T)) g h

theorem liftS_contAut {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle} {om : Om S T}
    (hom : IsWeilDatumO ψ S T χS χT om) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hT : CoCpt T) (v : Vol T)
    {G : GA D T → ℂ} (hG : IsContAut T G) : IsContAut S (liftS om v.μ v.𝓕 G f) := by
  refine ⟨fun γ hγ g => ?_, ?_⟩
  · simp only [liftS_apply]
    congr 1
    funext h
    rw [ker_inv_left hom hf hγ g h]
  · have hc : Continuous (Function.uncurry fun (h : GA D T) (g : GA D S) => om (g, h) f 0 * G h) :=
      ((hom.om_cont f hf 0).comp (continuous_snd.prodMk continuous_fst)).mul (hG.2.comp continuous_fst)
    exact (GlobalTheory.CocompactParam.continuous_integral_param D T hT v (GA D S) (fun h g => om (g, h) f 0 * G h) hc
      (fun γ hγ h g => by rw [ker_inv_right hom hf hγ g h, hG.1 γ hγ h])).2.1

theorem liftS_trans {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle} {om : Om S T}
    (hom : IsWeilDatumO ψ S T χS χT om) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (v : Vol T)
    {G : GA D T → ℂ} (hG : ∀ γ ∈ GQ T, ∀ h, G (γ * h) = G h) (g : GA D S) (b : GA D T) :
    liftS om v.μ v.𝓕 (rTrans b G) (om (g, b) f) = rTrans g (liftS om v.μ v.𝓕 G f) := by
  funext x
  simp only [liftS_apply, rTrans]
  have e : ∀ h, om (x, h) (om (g, b) f) 0 = om (x * g, h * b) f 0 := fun h => by
    have : om (x * g, h * b) = om (x, h) * om (g, b) := by
      rw [← map_mul]; rfl
    rw [this, Module.End.mul_apply]
  simp only [e]
  exact GlobalTheory.ChainOnto.setIntegral_fd_mul_right D T v.μ v.𝓕 v.haar v.fund (fun h => om (x * g, h) f 0 * G h)
    (fun γ hγ h => by rw [ker_inv_right hom hf hγ, hG γ hγ]) b

theorem contAut_rTrans {V : HSp D} {F : GA D V → ℂ} (hF : IsContAut V F) (b : GA D V) : IsContAut V (rTrans b F) :=
  ⟨fun γ hγ g => by simp only [rTrans]; rw [mul_assoc, hF.1 γ hγ], hF.2.comp (continuous_mul_right b)⟩

theorem cocpt_zero {S S₀ : HSp D} (d : HypDec S S₀ 0) (h : CoCpt S₀) : CoCpt S := by
  obtain ⟨K, hK, hKs⟩ := h
  refine ⟨d.emb0 '' K, hK.image d.continuous_embed, fun g => ?_⟩
  obtain ⟨g₀, rfl⟩ := (GlobalTheory.WeilSrc.Zero.witt_decomposition_zero_embedding_bijective d).2 g
  obtain ⟨γ, hγ, hγK⟩ := hKs g₀
  exact ⟨d.emb0 γ, d.wittDecomp_anisotropicEmbedding_mem_rationalPoints hγ, γ * g₀, hγK, map_mul _ _ _⟩

theorem val_zero {ψ : AddChar (AF D.host.F) ℂ} {B : BesLev D 0} {J : JacLev D 0} (s : StepBF ψ B J)
    {Ψ : WO B.V J.W → ℂ} (hΨ : IsThetaFunO ψ B.V J.W Ψ) :
    IsThetaFunO ψ B.V₀ J.W₀ (flatBF s Ψ) ∧ ∀ g h, s.om (B.d.emb0 g, J.d.emb0 h) Ψ 0 = s.om₀ (g, h) (flatBF s Ψ) 0 := by
  have hstd := s.weil.std
  obtain ⟨-, -, hthS, hwS⟩ := GlobalTheory.WeilSrc.om0_ext0_eq_om_emb0_of_isWeilDatumO D ψ B.V B.V₀ J.W B.d hstd
  obtain ⟨-, hthT, hwT⟩ := GlobalTheory.TargetIsom.transport D ψ B.V₀ J.W J.W₀ J.d hstd
  have hpull := GlobalTheory.WeilSrc.Zero.isWeilDatumO_pull B.d s.weil
  have h1 : IsThetaFunO ψ B.V₀ J.W (fun w => Ψ (B.d.ext0 J.W w)) := (hthS Ψ).2 hΨ
  have h2 : IsThetaFunO ψ B.V₀ J.W₀ (fun w => Ψ (B.d.ext0 J.W (J.d.inc0 B.V₀ w))) := (hthT _).2 h1
  rw [flatBF_rankZero D ψ B J s Ψ]
  refine ⟨h2, fun g h => ?_⟩
  have e1 := hwT s.χV s.χW (GlobalTheory.WeilSrc.Zero.pull B.d s.om) s.om₀ hpull s.weil₀ g h _ h1
  have e2 := hwS s.χV s.χW s.om (GlobalTheory.WeilSrc.Zero.pull B.d s.om) s.weil hpull g (J.d.emb0 h) Ψ hΨ
  rw [e1]
  simp only
  rw [e2]
  simp only [map_zero]

end GlobalTheory.LastRed

namespace GlobalTheory.LastRed

theorem main : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c), c.Is → c.VolLast → t.Is → WeilOK (t := t) v → LastLaw D → SeeLast D → ∀ j (h : j + 2 * 0 + 2 = D.R.m) Φ₁ Φ₂ φ F, IsThetaFunO c.ψ _ _ Φ₁ → IsThetaFunO c.ψ _ _ Φ₂ → IsContAut (c.X j) φ → IsContAut c.T F → IsContAut (c.V j) (liftS (t.om j) (c.vol (j + 1)).μ (c.vol (j + 1)).𝓕 (liftS (t.omT j h) c.volT.μ c.volT.𝓕 F Φ₂) Φ₁) ∧ ∀ g b bT, (c.B j 0 h).per c.ψ φ (rTrans g (liftS (t.om j) (c.vol (j + 1)).μ (c.vol (j + 1)).𝓕 (liftS (t.omT j h) c.volT.μ c.volT.𝓕 F Φ₂) Φ₁)) = ∫ h' in c.volT.𝓕, rTrans bT F h' * c.bl j (t.kom j) (t.kom (j + 1)) φ (c.lst j h (v.τ j h) (t.sBF j 0 h) (t.om j (g, b) Φ₁) (t.omT j h (b, bT) Φ₂)) ((c.oT (j + 1 + 1) h).emb (h', 1)) ∂c.volT.μ := by
  intro D c v t hc hvol ht hW hLL hSL j h Φ₁ Φ₂ φ F hΦ₁ hΦ₂ hφ hF
  obtain ⟨hsom, hsvW⟩ := ht.sBF j 0 h
  have hWs : IsWeilDatumO c.ψ (c.V j) (c.V (j + 1)) (t.sBF j 0 h).χV (t.sBF j 0 h).χW (t.om j) := by
    have := (t.sBF j 0 h).weil
    rw [hsom] at this
    exact this
  obtain ⟨χA, χz, χS', χT, omz, omT, omz'', hχV, hWa, hWz, hWX, hWT, hWTb, hWz''⟩ := hW.last j h
  have hcS : CoCpt (c.V (j + 1)) := cocpt_zero (c.jac j 0 h).d (c.jac j 0 h).cpt
  have hG : IsContAut (c.V (j + 1)) (liftS (t.omT j h) c.volT.μ c.volT.𝓕 F Φ₂) :=
    liftS_contAut hWTb hΦ₂ hc.cpt c.volT hF
  refine ⟨liftS_contAut hWs hΦ₁ hcS (c.vol (j + 1)) hG, fun g b bT => ?_⟩
  have e1 : liftS (t.omT j h) c.volT.μ c.volT.𝓕 (rTrans bT F) (t.omT j h (b, bT) Φ₂) =
      rTrans b (liftS (t.omT j h) c.volT.μ c.volT.𝓕 F Φ₂) := liftS_trans hWTb hΦ₂ c.volT hF.1 b bT
  have e2 : liftS (t.om j) (c.vol (j + 1)).μ (c.vol (j + 1)).𝓕 (rTrans b (liftS (t.omT j h) c.volT.μ c.volT.𝓕 F Φ₂))
      (t.om j (g, b) Φ₁) = rTrans g (liftS (t.om j) (c.vol (j + 1)).μ (c.vol (j + 1)).𝓕
        (liftS (t.omT j h) c.volT.μ c.volT.𝓕 F Φ₂) Φ₁) := liftS_trans hWs hΦ₁ (c.vol (j + 1)) hG.1 g b
  rw [← e2, ← e1]
  let lt : Last c.ψ c.T (c.B j 0 h) :=
    { J := c.J j 0 h, s := t.sBF j 0 h, cptS := hcS, cptT := hc.cpt, χS := χS', χT := χT, om := t.omT j h,
      weil := hWTb, vT := c.volT }
  have hΦ₁' := hWs.om_pres (g, b) Φ₁ hΦ₁
  have hΦ₂' := hWTb.om_pres (b, bT) Φ₂ hΦ₂
  have hLL' : (c.B j 0 h).per c.ψ φ (liftS (t.om j) (c.vol (j + 1)).μ (c.vol (j + 1)).𝓕
      (liftS (t.omT j h) c.volT.μ c.volT.𝓕 (rTrans bT F) (t.omT j h (b, bT) Φ₂)) (t.om j (g, b) Φ₁)) =
      lt.Q φ (t.om j (g, b) Φ₁) (t.omT j h (b, bT) Φ₂) (rTrans bT F) := by
    have := hLL c.ψ c.T (c.B j 0 h) lt φ (t.om j (g, b) Φ₁) (t.omT j h (b, bT) Φ₂) (rTrans bT F) hφ
      (contAut_rTrans hF bT) hΦ₁' hΦ₂'
    have e3 : ∀ G Φ, lt.s.lift G Φ = liftS (t.om j) (c.vol (j + 1)).μ (c.vol (j + 1)).𝓕 G Φ := fun G Φ => by
      show liftS (t.sBF j 0 h).om (t.sBF j 0 h).vW.μ (t.sBF j 0 h).vW.𝓕 G Φ = _
      rw [hsom, hsvW]
    rw [e3] at this
    exact this
  rw [hLL']
  have hstd : IsStdChar D c.ψ (-1) := hc.std
  set s := t.sBF j 0 h with hs
  set Φ₁' := t.om j (g, b) Φ₁ with hΦ₁'def
  set Φ₂' := t.omT j h (b, bT) Φ₂ with hΦ₂'def
  have hΦ₁s : IsThetaFunO c.ψ (c.B j 0 h).V (c.J j 0 h).W Φ₁' := hΦ₁'
  obtain ⟨hΞ, hval⟩ := val_zero s hΦ₁s
  obtain ⟨-, -, hthS, hwS⟩ := GlobalTheory.WeilSrc.om0_ext0_eq_om_emb0_of_isWeilDatumO D c.ψ (c.V (j + 1)) (c.X (j + 1)) c.T (c.jac j 0 h).d hstd
  have hΦ₂'' : IsThetaFunO c.ψ (c.X (j + 1)) c.T (fun w => Φ₂' ((c.jac j 0 h).d.ext0 c.T w)) := (hthS Φ₂').2 hΦ₂'
  have hτ := (hW.tau j h).2
  have hSL' := (hSL c.ψ (c.bes j 0 h).V₀ (c.X j) (c.bes j 0 h).L (c.X (j + 1)) (c.X (j + 1 + 1)) c.T c.Lz (c.bes j 0 h).o
    (c.oT (j + 1 + 1) h) (v.τ j h) (c.bes j 0 h).line.1 (hW.tau j h).1 hτ χA χz s.χW χS' χT s.om₀ (t.kom j) omz
    (t.kom (j + 1)) omT omz'' (hχV ▸ s.weil₀) hWa hWz hWX hWT hWz'' (flatBF s Φ₁') _ hΞ hΦ₂'').2
  have hC := lastBi_biTheta D c.ψ (c.bes j 0 h).V₀ (c.X j) (c.bes j 0 h).L (c.X (j + 1)) (c.X (j + 1 + 1)) c.T c.Lz
    (c.bes j 0 h).o (c.oT (j + 1 + 1) h) (v.τ j h) hτ (flatBF s Φ₁') _ hΞ hΦ₂''
  have hBA := (GlobalTheory.T.seeSawWeilBiAction_commutes D c.ψ (c.X j) (c.X (j + 1)) (c.X (j + 1 + 1)) χA s.χW χS' (χT * χz⁻¹) (t.kom j) (t.kom (j + 1))
    hWa hWX _ hC).2.2.1
  show ∫ h' in c.volT.𝓕, rTrans bT F h' * (∫ x in s.vW.𝓕, t.omT j h (x, h') Φ₂' 0 *
      (∫ h₀ in (c.x j).vol.𝓕, φ h₀ * s.om (embA (c.bes j 0 h).d (c.bes j 0 h).o h₀, x) Φ₁' 0 ∂(c.x j).vol.μ) ∂s.vW.μ)
      ∂c.volT.μ = _
  congr 1
  funext h'
  congr 1
  rw [hsvW]
  rw [integral_automorphic_rankZeroWittEmbedding D _ _ (c.jac j 0 h).d (c.vol (j + 1)) (c.x (j + 1)).vol (hvol j h) _ (fun γ hγ x => by
    rw [ker_inv_left hWTb hΦ₂' hγ x h']
    congr 1
    congr 1
    funext h₀
    rw [ker_inv_right s.weil hΦ₁s hγ])]
  simp only [Comm.bl, biLift]
  congr 1
  funext h₁
  rw [← integral_const_mul]
  congr 1
  funext h₀
  have v1 := hval ((c.bes j 0 h).o.emb (h₀, 1)) h₁
  have v2 := congrFun (hwS χS' χT (t.omT j h) omT hWTb hWT h₁ h' Φ₂' hΦ₂') 0
  simp only [map_zero] at v2
  have v3 := hSL' h₀ h₁ h'
  have v4 := hBA (h₀, h₁) (h₁, (c.oT (j + 1 + 1) h).emb (h', 1)) 0 0
  rw [embA_apply, v1, ← v2]
  calc _ = φ h₀ * (omT (h₁, h') (fun w => Φ₂' ((c.jac j 0 h).d.ext0 c.T w)) 0 * s.om₀ ((c.bes j 0 h).o.emb (h₀, 1), h₁) (flatBF s Φ₁') 0) := by ring
    _ = _ := by rw [v3]; exact congrArg (φ h₀ * ·) v4.symm

end GlobalTheory.LastRed

end
