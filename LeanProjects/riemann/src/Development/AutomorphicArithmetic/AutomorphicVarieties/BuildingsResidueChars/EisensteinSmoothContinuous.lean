import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.PerDeriv
open UpperTheory.V.Sd.Eis
open NumberField Topology Matrix Neutral.B1 GlobalTheory.CuspRep Formalism.L2.Host UpperTheory.V

private theorem cont_map {R S : Type} [CommRing R] [CommRing S] [TopologicalSpace R] [TopologicalSpace S]
    (a : ℕ) (f : R →+* S) (hf : Continuous f) :
    Continuous (fun g : GL (Fin a) R => GeneralLinearGroup.map f g) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact Units.continuous_val.matrix_map hf
  · exact Units.continuous_coe_inv.matrix_map hf

private theorem cont_pInf (F : Type) [Field F] [NumberField F] [IsTotallyReal F] : Continuous (TR.pInf F) := by
  have h : Continuous (TR.infEq F).symm :=
    continuous_pi fun w =>
      (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).continuous.comp
        (continuous_apply w)
  exact h.comp continuous_fst

theorem UpperTheory.eisenstein_smooth_continuous :
    UpperTheory.V.Sd.Eis.SmCont := by
  intro F _ _ _ a φ hU
  have hy := cont_map a (TR.pInf F) (cont_pInf F)
  have hk := cont_map a (pFin F) continuous_snd
  refine continuous_iff_continuousAt.2 fun g₀ => ?_
  set k₀ := GeneralLinearGroup.map (pFin F) g₀ with hk₀
  have hy' : Continuous fun g : GA F a => TR.toL (GeneralLinearGroup.map (TR.pInf F) g).val :=
    (Units.continuous_val (M := Matrix (Fin a) (Fin a) (TR.Rinf F))).comp hy
  have hc : ContinuousAt (fun g : GA F a =>
      TR.chart φ.1 (finGL F a k₀) (TR.toL (GeneralLinearGroup.map (TR.pInf F) g).val)) g₀ :=
    ContinuousAt.comp (f := fun g : GA F a => TR.toL (GeneralLinearGroup.map (TR.pInf F) g).val)
      (TR.contDiffAt_chart φ.2 _ (TR.val_mem_invSet _)).continuousAt hy'.continuousAt
  refine hc.congr ?_
  have hk' : Continuous fun g : GA F a => k₀⁻¹ * GeneralLinearGroup.map (pFin F) g :=
    continuous_const.mul hk
  have hn : ∀ᶠ g : GA F a in 𝓝 g₀, TR.finRep F a (k₀⁻¹ * GeneralLinearGroup.map (pFin F) g) φ = φ := by
    refine (hU.preimage hk').mem_nhds ?_
    change TR.finRep F a (k₀⁻¹ * k₀) φ = φ
    rw [inv_mul_cancel, map_one]; rfl
  filter_upwards [hn] with g hg
  rw [TR.chart_val]
  have e := congrFun (congrArg Subtype.val hg) (finGL F a k₀ * TR.infGL F a (GeneralLinearGroup.map (TR.pInf F) g))
  rw [← e]
  change φ.1 (_ * finGL F a _) = _
  rw [← TR.infGL_comm, mul_assoc, ← map_mul, mul_inv_cancel_left, TR.infGL_mul_finGL]
