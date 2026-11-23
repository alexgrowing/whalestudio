import Development.WeilBound.ThetaLifts.CartanFactorisation.ArchimedeanEvaluationVector
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThetaBasicK
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkFacStmt

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace PositivityTheory.ThKF.A
open scoped TensorProduct NNReal ENNReal Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Real RealInnerProductSpace Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKF.W GlobalTheory.HeisSchA GlobalTheory.RealWeil
section Gen
variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
end Gen
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {X : Spc F E n} {W : Spc F E d}
variable {B : Base F E} {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W} {r s r' s' : ℕ}
theorem impl_of_k (hP : _root_.GlobalTheory.ThK.IsPair_k B M χX χW om r s r' s') (C : Coord F (Fin n × Fin d)) {x}
    {T : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d)}
    (h : ∀ f : SInf F _, ∀ g ∈ SB (Fin n × Fin d → Af F), om x (pureA F f g) = pureA F (T f) g) :
    PositivityTheory.ThKF.E.Impl (C.P ≪≫ₗ phL M x ≪≫ₗ C.P.symm) (C.S.toLinearEquiv.toLinearMap ∘ₗ T ∘ₗ C.S.symm.toLinearEquiv.toLinearMap) := by
  have hs := IsUWeilPair.isUSplitting hP.weil
  obtain ⟨g₀, h₀, h₁⟩ := exists_sb_one (F := F) (κ := Fin n × Fin d)
  refine ⟨fun f => ?_, fun w f g hg => ?_⟩
  · obtain ⟨f, rfl⟩ := C.S.surjective f
    have := C.norm_eq (lintegral_eq (fun μ hμ => hs.unit μ hμ x) (h f))
    simpa using this
  · obtain ⟨f, rfl⟩ := C.S.surjective f
    obtain ⟨g, rfl⟩ := C.S.surjective g
    rw [C.rho_iff hP.base.std] at hg
    have : ⇑(T g) = schrInf F B.ψ (C.P (C.P.symm (phL M x (C.P w)))) (T f) := by
      refine pureA_inj h₁ ?_
      rw [← h g _ h₀, hg, pureA_schrInf, pureA_schrInf, ← h f _ h₀, LinearEquiv.apply_symm_apply, ← phL_spec]
      obtain ⟨u, hu⟩ := M.co.e.surjective (mixedSpaceVecPairAsAdeles F (C.P w))
      rw [← hu, phB_e]
      exact hs.impl x u _ (pureA_mem f h₀)
    simpa using (C.rho_iff hP.base.std _ _ _).2 this
theorem exists_T_k (hP : _root_.GlobalTheory.ThK.IsPair_k B M χX χW om r s r' s') {g h} (hg : g ∈ UAt σ X (evI F)) (hh : h ∈ UAt σ W (evI F)) :
    ∃ T : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d),
      ∀ f : SInf F _, ∀ φ ∈ SB (Fin n × Fin d → Af F), om (g, h) (pureA F f φ) = pureA F (T f) φ := by
  have hs := IsUWeilPair.isUSplitting hP.weil
  refine exists_lin hP.base.std _ (hs.pres _) fun m Φ hΦ => ?_
  obtain ⟨u, hu⟩ := M.co.e.surjective (finE2 F m)
  have := hs.impl (g, h) u Φ hΦ
  simp only [Darboux.rho] at this
  rw [← phB_e, hu, phB_fin M hg hh] at this
  exact this
theorem surj_of_k (hP : _root_.GlobalTheory.ThK.IsPair_k B M χX χW om r s r' s') {g h} (hg : g ∈ UAt σ X (evI F)) (hh : h ∈ UAt σ W (evI F))
    {T : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d)}
    (hT : ∀ f : SInf F _, ∀ φ ∈ SB (Fin n × Fin d → Af F), om (g, h) (pureA F f φ) = pureA F (T f) φ) :
    Function.Surjective T := fun f => by
  obtain ⟨T', hT'⟩ := _root_.PositivityTheory.ThKF.A.exists_T_k hP (inv_mem_UAt hg) (inv_mem_UAt hh)
  obtain ⟨g₀, h₀, h₁⟩ := exists_sb_one (F := F) (κ := Fin n × Fin d)
  refine ⟨T' f, DFunLike.coe_injective (pureA_inj h₁ ?_)⟩
  rw [← hT _ _ h₀, ← hT' _ _ h₀, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_inv_cancel, mul_inv_cancel]
  exact LinearMap.congr_fun om.map_one _
theorem T_D_k (hP : _root_.GlobalTheory.ThK.IsPair_k B M χX χW om r s r' s') (C : Coord F (Fin n × Fin d)) {g h} (hg : g ∈ UAt σ X (evI F))
    (hh : h ∈ UAt σ W (evI F)) {T : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d)}
    (hT : ∀ f : SInf F _, ∀ φ ∈ SB (Fin n × Fin d → Af F), om (g, h) (pureA F f φ) = pureA F (T f) φ) (v) (f) :
    T (C.D v f) = C.D (phL M (g, h) v) (T f) := by
  have := PositivityTheory.ThKF.E.Impl.dRho (s := (C.P ≪≫ₗ phL M (g, h) ≪≫ₗ C.P.symm).toLinearMap) (_root_.PositivityTheory.ThKF.A.impl_of_k hP C hT)
    (C.S.surjective.comp ((_root_.PositivityTheory.ThKF.A.surj_of_k hP hg hh hT).comp C.S.symm.surjective)) (C.P.symm v) (C.S f)
  apply C.S.injective
  simpa [Coord.D] using this
theorem exists_op_k (hP : _root_.GlobalTheory.ThK.IsPair_k B M χX χW om r s r' s') {g h} (hg : g ∈ UAt σ X (evI F)) (hh : h ∈ UAt σ W (evI F)) :
    ∃ T, IsArchOp om (g, h) T := by
  obtain ⟨T, hT⟩ := _root_.PositivityTheory.ThKF.A.exists_T_k hP hg hh
  obtain ⟨C⟩ := nonempty_coord (F := F) (κ := Fin n × Fin d)
  have hc := (_root_.PositivityTheory.ThKF.A.impl_of_k hP C hT).continuous (C.S.surjective.comp ((_root_.PositivityTheory.ThKF.A.surj_of_k hP hg hh hT).comp C.S.symm.surjective))
  have hc' : Continuous T := by
    have := C.S.symm.continuous.comp (hc.comp C.S.continuous)
    convert this using 1
    funext f
    simp
  exact ⟨⟨T, hc'⟩, hT, acts_of hT⟩
theorem map_Pol_k (hP : _root_.GlobalTheory.ThK.IsPair_k B M χX χW om r s r' s') {X₂ : Spc F E n} {W₂ : Spc F E d} (M₂ : Model σ (reS X X₂) (reS W W₂))
    (hco : M₂.co = M.co) {g h} (hg : g ∈ UAt σ X (evI F)) (hh : h ∈ UAt σ W (evI F))
    (eg : ∀ w, (mat g).map (piInf (B.emb w)) * X₂.θ w = X.θ w * (mat g).map (piInf (B.emb w)))
    (eh : ∀ w, (mat h).map (piInf (B.emb w)) * W₂.θ w = W.θ w * (mat h).map (piInf (B.emb w)))
    {T} (hT : IsArchOp om (g, h) T) : ∀ f ∈ M₂.Pol B.ψ B.emb, T f ∈ M.Pol B.ψ B.emb := by
  obtain ⟨C⟩ := nonempty_coord (F := F) (κ := Fin n × Fin d)
  have hψ := hP.base.std
  have hl : ∀ u, M₂.heisLine B.ψ u = M.heisLine B.ψ u := fun u => funext fun t => by
    unfold Model.heisLine
    rw [hco]
    rfl
  have uq := fun f f₁ f₂ => (archUniq F (Fin n × Fin d) f f₁ f₂).2
  have hD := _root_.PositivityTheory.ThKF.A.T_D_k hP C hg hh (T := T.toLinearMap) hT.1
  intro f hf
  refine Submodule.mem_sInf.1 hf ((M.Pol B.ψ B.emb).comap T.toLinearMap) ⟨fun f₀ ⟨ε, hε⟩ => ?_, fun u hu f hf f₁ h₁ => ?_⟩
  · refine Submodule.mem_sInf.2 fun N hN => hN.1 _ ⟨ε, fun u u' hu hu' e f f' h1 h2 => ?_⟩
    have k : ∀ z, actAB (cA σ) (g, h) (actAB (cA σ) (g⁻¹, h⁻¹) z) = z := fun z => (actLin (R := AF F) (cA σ) (g, h)).right_inv z
    have a1 := at_act (g⁻¹, h⁻¹) hu
    have a2 := at_act (g⁻¹, h⁻¹) hu'
    have hA : ∀ z, At (evI F) z → ActsD (evI F) (M₂.heisLine B.ψ z) f₀ (C.D (vec M z) f₀) := fun z hz => by
      rw [hl]
      exact actsD_heis hψ M C hz f₀
    have hD' : ∀ z, At (evI F) z → C.D (vec M (actAB (cA σ) (g, h) z)) (T f₀) = T (C.D (vec M z) f₀) := fun z hz => by
      rw [← phL_vec M _ hz]
      exact (hD _ _).symm
    have b1 := hD' _ a1
    have b2 := hD' _ a2
    rw [k] at b1 b2
    have key := hε _ _ a1 a2 (fun w => ?_) _ _ (hA _ a1) (hA _ a2)
    · have c1 : f = C.D (vec M u) (T f₀) := uq _ _ _ _ h1 (actsD_heis hψ M C hu (T f₀))
      have c2 : f' = C.D (vec M u') (T f₀) := uq _ _ _ _ h2 (actsD_heis hψ M C hu' (T f₀))
      rw [c1, c2, b1, b2, key, map_smul]
    · have inv : ∀ {m : ℕ} (a b θ θ' : Matrix (Fin m) (Fin m) ℂ), b * a = 1 → a * θ' = θ * a → b * θ = θ' * b :=
        fun a b θ θ' h1 h2 => by
          have h3 := mul_eq_one_comm.1 h1
          calc b * θ = b * (θ * a) * b := by rw [Matrix.mul_assoc, Matrix.mul_assoc, h3, Matrix.mul_one]
            _ = θ' * b := by rw [← h2, ← Matrix.mul_assoc, h1, Matrix.one_mul]
      have i1 := inv _ ((mat g⁻¹).map (piInf (B.emb w))) _ _ (by
        rw [← Matrix.map_mul, show mat g⁻¹ * mat g = 1 from Units.inv_mul g.1, Matrix.map_one _ (map_zero _) (map_one _)]) (eg w)
      have i2 := inv _ ((mat h⁻¹).map (piInf (B.emb w))) _ _ (by
        rw [← Matrix.map_mul, show mat h⁻¹ * mat h = 1 from Units.inv_mul h.1, Matrix.map_one _ (map_zero _) (map_one _)]) (eh w)
      have i3 := congrArg Matrix.transpose i2
      rw [Matrix.transpose_mul, Matrix.transpose_mul] at i3
      show (mat g⁻¹ * u' * (mat h⁻¹)ᵀ).map _ = _ • (X₂.θ w * (mat g⁻¹ * u * (mat h⁻¹)ᵀ).map _ * (W₂.θ w)ᵀ)
      simp only [Matrix.map_mul, e w, Matrix.transpose_map, Matrix.mul_smul, Matrix.smul_mul]
      congr 1
      simp only [← Matrix.mul_assoc, i1]
      simp only [Matrix.mul_assoc, i3]
  · rw [hl] at h₁
    rw [uq _ _ _ _ h₁ (actsD_heis hψ M C hu _), Submodule.mem_comap, hD]
    exact D_mem_Pol hψ M C _ _ hf
theorem archOp_k : _root_.PositivityTheory.ThKF.ArchOp_k := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP g hg h hh
  obtain ⟨T, hT⟩ := _root_.PositivityTheory.ThKF.A.exists_op_k hP hg hh
  exact ⟨T, hT, fun kg kh => _root_.PositivityTheory.ThKF.A.map_Pol_k hP (X₂ := X) (W₂ := W) M rfl hg hh (fun w => (kg.2 w).eq) (fun w => (kh.2 w).eq) hT⟩
end PositivityTheory.ThKF.A
end
end
