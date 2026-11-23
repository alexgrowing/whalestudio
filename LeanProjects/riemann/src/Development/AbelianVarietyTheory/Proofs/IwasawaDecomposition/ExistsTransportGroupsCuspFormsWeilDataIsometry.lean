import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousKapSymm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GelfandOperatorCommutesIsometryStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCuspidalIsometryTransportHermitianStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHaarFundamentalDomainIsometryTransportStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormInfIsometryConjLeConstMulStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem Formalism.IndefR.Datum
open scoped InnerProductSpace

namespace GlobalTheory.Mem.Isom

variable {D : D7}

theorem gelf_tr {V V' : HSp D} (I : IsoMat V V') {θ : InfF D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) (k : ℕ) {φ : GA D V → ℂ}
    (hφ : φ ∈ GlobalTheory.Mem.AutSpace.SmFun θ V) : gelf θ V' τ k (I.tr φ) = I.tr (gelf θ V τ k φ) :=
  GlobalTheory.T.gelfand_operator_commutes_isometry D V V' I θ hθ τ k φ hφ

theorem cusp_tr {V V' : HSp D} (I : IsoMat V V') {φ : GA D V → ℂ} (hφ : IsCuspFun V φ) : IsCuspFun V' (I.tr φ) :=
  GlobalTheory.T.isCuspidal_isometryTransport_hermitian D V V' I φ hφ

theorem haar_tr {V V' : HSp D} (I : IsoMat V V') (S : HSp D) (μ : Measure (WO S V')) (𝓕 : Set (WO S V')) (hμ : μ.IsAddHaarMeasure)
    (h𝓕 : IsAddFundamentalDomain (ratL V' S) 𝓕 μ) : ∃ (ν : Measure (WO S V)) (𝓖 : Set (WO S V)), ν.IsAddHaarMeasure ∧
      IsAddFundamentalDomain (ratL V S) 𝓖 ν ∧
        ∀ u : WO S V → ENNReal, ∫⁻ w in 𝓕, u ((I.phi S).symm w) ∂μ = ∫⁻ w in 𝓖, u w ∂ν :=
  GlobalTheory.T.exists_haar_fundamentalDomain_isometryTransport D V V' I S μ 𝓕 hμ h𝓕

theorem entries_fix {A : Type} [CommRing A] {m n : ℕ} (c : A) {M : Matrix (Fin n) (Fin n) A} (hM : ∀ i j, c * M i j = M i j)
    (P : Matrix (Fin m) (Fin n) A) (Q : Matrix (Fin n) (Fin m) A) (i j : Fin m) : c * (P * M * Q) i j = (P * M * Q) i j := by
  simp only [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  conv_rhs => rw [← hM l k]
  ring

theorem entries_fix' {A : Type} [CommRing A] {m n k : ℕ} (c : A) {M : Matrix (Fin n) (Fin k) A} (hM : ∀ i j, c * M i j = M i j)
    (P : Matrix (Fin m) (Fin n) A) (i : Fin m) (j : Fin k) : c * (P * M) i j = (P * M) i j := by
  simp only [Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  conv_rhs => rw [← hM l j]
  ring

theorem sub_one_conj {A : Type} [CommRing A] {m n : ℕ} {P : Matrix (Fin m) (Fin n) A} {Q : Matrix (Fin n) (Fin m) A} (PQ : P * Q = 1)
    (M : Matrix (Fin n) (Fin n) A) : P * M * Q - 1 = P * (M - 1) * Q := by
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, PQ]

theorem det_conj_rect {A : Type} [CommRing A] {m n : ℕ} (h : n = m) {P : Matrix (Fin m) (Fin n) A} {Q : Matrix (Fin n) (Fin m) A}
    (QP : Q * P = 1) (M : Matrix (Fin n) (Fin n) A) : (P * M * Q).det = M.det := by
  subst h
  rw [Matrix.det_mul, Matrix.det_mul, mul_comm (P.det), mul_assoc, ← Matrix.det_mul, mul_eq_one_comm.1 QP, Matrix.det_one, mul_one]

namespace IsoMat
variable {V V' : HSp D} (I : IsoMat V V') {θ : InfF D}

theorem isAutFun_tr {φ : GA D V → ℂ} (h : IsAutFun V φ) : IsAutFun V' (I.tr φ) := by
  haveI : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  refine ⟨fun γ hγ g => ?_, ?_, h.cont.comp I.continuous_kap_symm⟩
  · unfold tr
    rw [map_mul]
    exact h.left _ (I.symm.kap_mem_GQ hγ) _
  · obtain ⟨U, hU, e⟩ := h.level
    refine ⟨U.comap I.kap.symm.toMonoidHom, hU.preimage I.continuous_kap_symm, fun k hk hf g => ?_⟩
    unfold tr
    rw [map_mul]
    exact e _ hk (I.symm.kap_mem_GfC hf) _

theorem normInf_kap_le (hθ : IsInfFam θ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ g : GA D V, normInf θ V' (I.kap g) ≤ C * normInf θ V g :=
  GlobalTheory.T.normInf_isometryConj_le_const_mul D V V' I θ hθ

theorem foldr_tr (hθ : IsInfFam θ) (φ : GA D V → ℂ) (l : List (D.what₂.Tau × Matrix (Fin V'.rank) (Fin V'.rank) ℂ))
    (hl : ∀ p ∈ l, p.2 ∈ lieAt V' p.1) :
    l.foldr (fun p f => Rder θ V' p.1 p.2 f) (I.tr φ) =
      I.tr ((l.map fun p => (p.1, I.symm.adP p.1 p.2)).foldr (fun p f => Rder θ V p.1 p.2 f) φ) := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    rw [List.map_cons, List.foldr_cons, List.foldr_cons, ih fun q hq => hl q (List.mem_cons_of_mem _ hq),
      I.Rder_tr hθ (hl p List.mem_cons_self)]

def trLin : (GA D V → ℂ) →ₗ[ℂ] (GA D V' → ℂ) where
  toFun := I.tr
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem isAutFunSm_tr (hθ : IsInfFam θ) {φ : GA D V → ℂ} (hφ : IsAutFunSm θ V φ) : IsAutFunSm θ V' (I.tr φ) := by
  have ha := I.isAutFun_tr hφ.toIsAutFun
  refine { left := ha.left, level := ha.level, cont := ha.cont, smooth := I.tr_mem_SmFun hθ hφ.smooth, zfin := ?_, growth := ?_ }
  · obtain ⟨W, hW, m, s⟩ := hφ.zfin
    refine ⟨(W ⊓ GlobalTheory.Mem.AutSpace.SmFun θ V).map I.trLin, inferInstance, ⟨φ, ⟨m, hφ.smooth⟩, rfl⟩, ?_⟩
    rintro τ k _ ⟨f, hf, rfl⟩
    exact ⟨_, ⟨s τ k f hf.1, (GlobalTheory.Mem.AutSpace.linOnSm_gelf τ k).mem f hf.2⟩, (_root_.GlobalTheory.Mem.Isom.gelf_tr I hθ τ k hf.2).symm⟩
  · obtain ⟨N, hN⟩ := hφ.growth
    obtain ⟨c, hc0, hc⟩ := I.symm.normInf_kap_le hθ
    refine ⟨N, fun l hl x => ?_⟩
    obtain ⟨C, hC⟩ := hN (l.map fun p => (p.1, I.symm.adP p.1 p.2)) (fun p hp => by
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
      exact I.symm.adP_mem (hl q hq)) (I.kap.symm x)
    refine ⟨|C| * c ^ N, fun g hg => ?_⟩
    rw [I.foldr_tr hθ φ l hl]
    unfold tr
    rw [map_mul, mul_assoc |C|, ← mul_pow]
    exact (hC _ (I.symm.kap_mem_GinfC hg)).trans (mul_le_mul (le_abs_self _)
      (pow_le_pow_left₀ (GlobalTheory.SmoothForms.normInf_nonneg _) (hc g) N) (pow_nonneg (GlobalTheory.SmoothForms.normInf_nonneg _) N)
      (abs_nonneg _))

theorem isThetaFunO_tr (S : HSp D) {ψ : AddChar (AF D.host.F) ℂ} {f : WO S V → ℂ} (hf : IsThetaFunO ψ S V f) :
    IsThetaFunO ψ S V' (I.trW S f) := by
  have hinf : ∀ w : WO S V', w.map (infPart D) = 0 → ((I.phi S).symm w).map (infPart D) = 0 := fun w h => by
    show (HMul.hMul I.aQ w).map (infPart D) = 0
    rw [Matrix.map_mul, h, Matrix.mul_zero]
  have hfin : ∀ w : WO S V', w.map (finPart D) = 0 → ((I.phi S).symm w).map (finPart D) = 0 := fun w h => by
    show (HMul.hMul I.aQ w).map (finPart D) = 0
    rw [Matrix.map_mul, h, Matrix.mul_zero]
  refine ⟨fun γ w => ?_, ?_, hf.cont.comp (I.continuous_phi_symm S), fun k L hL h0 w => ?_⟩
  · obtain ⟨w, rfl⟩ := (I.phi S).surjective w
    have e : ratW V' S γ = I.phi S (ratW V S (I.Q * γ)) := by
      rw [phi_ratW, ← Matrix.mul_assoc, I.PQ, Matrix.one_mul]
    rw [e, ← map_add, I.symplOH_phi]
    simp only [trW, AddEquiv.symm_apply_apply]
    exact hf.quasi _ _
  · obtain ⟨U, hU, e⟩ := hf.level
    refine ⟨U.map (I.phi S).toAddMonoidHom, ?_, ?_⟩
    · have e : ((U.map (I.phi S).toAddMonoidHom : AddSubgroup (WO S V')) : Set (WO S V')) = (I.phi S).symm ⁻¹' U := by
        ext w
        simp only [AddSubgroup.coe_map, Set.mem_image, Set.mem_preimage, SetLike.mem_coe]
        constructor
        · rintro ⟨u, hu, rfl⟩
          simpa using hu
        · intro hw
          exact ⟨_, hw, by simp⟩
      rw [e]
      exact hU.preimage (I.continuous_phi_symm S)
    · rintro _ ⟨u, hu, rfl⟩ h0
      have h1 : u.map (infPart D) = 0 := by
        have := hinf _ h0
        simpa using this
      show heisO ψ S V' (I.phi S u) (I.trW S f) = I.trW S f
      rw [I.heisO_trW, e u hu h1]
  · have := hf.smooth k ((I.phi S).symm.toAddMonoidHom.comp L) ((I.continuous_phi_symm S).comp hL) (fun t => hfin _ (h0 t))
      ((I.phi S).symm w)
    simpa [trW] using this

end IsoMat

namespace IsoMat
variable {V V' : HSp D} (I : IsoMat V V')

theorem isWeilDatumO_tr (S : HSp D) {ψ : AddChar (AF D.host.F) ℂ} {χ χ' : IdC D} {om : GA D S × GA D V →* Module.End ℂ (WO S V → ℂ)}
    (h : IsWeilDatumO ψ S V χ χ' om) : IsWeilDatumO ψ S V' χ χ' (I.omT S om) := by
  have hT : ∀ f, IsThetaFunO ψ S V' f → IsThetaFunO ψ S V (I.symm.trW S f) := fun f hf => I.symm.isThetaFunO_tr S hf
  refine ⟨h.std, h.hecS, h.hecT, h.resS, I.rank_eq ▸ h.resT, fun p f hf => ?_, fun g k w₀ f hf => ?_, fun γ hγ γ' hγ' f hf => ?_,
    fun f hf w => ?_, fun μ 𝓕 hμ h𝓕 p f hf => ?_, fun e he g k hg hk x y hx hy => ?_⟩
  · exact I.isThetaFunO_tr S (h.om_pres _ _ (hT f hf))
  · rw [omT_apply, omT_apply, ← I.symm.heisO_trW S ψ w₀ f, h.om_heis _ _ _ _ (hT f hf), ← I.heisO_trW, I.actO_phi]
    congr 2
    · exact I.kap.apply_symm_apply k
    · exact (I.phi S).apply_symm_apply w₀
  · rw [omT_apply]
    show om (γ, I.kap.symm γ') (I.symm.trW S f) ((I.phi S).symm 0) = f 0
    have := h.om_aut γ hγ (I.kap.symm γ') (I.symm.kap_mem_GQ hγ') _ (hT f hf)
    rw [map_zero, this]
    show f ((I.phi S) 0) = f 0
    rw [map_zero]
  · exact (h.om_cont _ (hT f hf) ((I.phi S).symm w)).comp
      (continuous_fst.prodMk ((I.continuous_kap_symm).comp continuous_snd))
  · obtain ⟨ν, 𝓖, hν, h𝓖, hu⟩ := haar_tr I S μ 𝓕 hμ h𝓕
    have e1 := hu fun x => ‖om (p.1, I.kap.symm p.2) (I.symm.trW S f) x‖ₑ ^ 2
    have e2 := hu fun x => ‖I.symm.trW S f x‖ₑ ^ 2
    have e3 : ∀ w, I.symm.trW S f ((I.phi S).symm w) = f w := fun w => congrArg f ((I.phi S).apply_symm_apply w)
    simp only [e3] at e2
    rw [omT_apply]
    exact e1.trans ((h.om_unit ν 𝓖 hν h𝓖 _ _ (hT f hf)).trans e2.symm)
  · have e0 : mt V (I.kap.symm k) - 1 = _ := sub_one_conj I.aQ_aP (mt V' k)
    have hsupp : SuppAt e V (I.kap.symm k) := fun i j => by
      unfold SuppAt at hk
      rw [e0]
      exact entries_fix _ hk _ _ i j
    have e1 : (mt V (I.kap.symm k)).det = (mt V' k).det := det_conj_rect I.rank_eq.symm I.aP_aQ (mt V' k)
    have hdet : IsDetAt e V (I.kap.symm k) y := by
      unfold IsDetAt at hy ⊢
      rw [e1]
      exact hy
    obtain ⟨r, hr, H⟩ := h.om_split e he g (I.kap.symm k) hg hsupp x y hx hdet
    refine ⟨r, hr, fun ℓ hℓ f hf => ?_⟩
    have hinv : ∀ u : WO S V, (∀ i j, cA D e * u i j = u i j) → ∀ f, IsThetaFunO ψ S V f →
        (ℓ ∘ₗ I.trL S) (heisO ψ S V u f) = (ℓ ∘ₗ I.trL S) f := by
      intro u hu f hf
      show ℓ (I.trW S (heisO ψ S V u f)) = ℓ (I.trW S f)
      rw [← I.heisO_trW]
      exact hℓ _ (fun i j => entries_fix' _ hu I.aP i j) _ (I.isThetaFunO_tr S hf)
    have := H (ℓ ∘ₗ I.trL S) hinv _ (hT f hf)
    have e1 : (ℓ ∘ₗ I.trL S) (I.symm.trW S f) = ℓ f := congrArg ℓ (I.symm.trW_symm_trW S f)
    rw [e1] at this
    exact this

end IsoMat

theorem exists_isom_transport : ∀ (D : D7) (V V' : HSp D) (e : V.V ≃ₗ[D.host.E] V'.V), HSpace.IsIsomEmb V V' e.toLinearMap →
    ∃ κ : GA D V ≃* GA D V', Continuous κ ∧ Continuous κ.symm ∧ (∀ g, κ g ∈ GQ V' ↔ g ∈ GQ V) ∧
      (∀ θ : InfF D, IsInfFam θ → ∀ F, IsCuspForm θ V F → IsCuspForm θ V' fun h => F (κ.symm h)) ∧
      ∀ (ψ : AddChar (AF D.host.F) ℂ) (S : HSp D) (χ χ' : IdC D) om, IsWeilDatumO ψ S V χ χ' om →
        ∃ om', IsWeilDatumO ψ S V' χ χ' om' ∧ ∀ f, IsThetaFunO ψ S V f → ∃ f', IsThetaFunO ψ S V' f' ∧ (f ≠ 0 → f' ≠ 0) ∧
          ∀ g h, thetaKO om' g (κ h) f' = thetaKO om g h f := by
  intro D V V' e he
  let I := IsoMat.ofEquiv e he
  refine ⟨I.kap, I.continuous_kap, I.continuous_kap_symm, fun g => ⟨fun hg => ?_, I.kap_mem_GQ⟩,
    fun θ hθ F hF => ⟨I.isAutFunSm_tr hθ hF.1, cusp_tr I hF.2⟩, fun ψ S χ χ' om hom => ?_⟩
  · have := I.symm.kap_mem_GQ hg
    rwa [← I.kap_symm_apply, I.kap.symm_apply_apply] at this
  · refine ⟨I.omT S om, I.isWeilDatumO_tr S hom, fun f hf => ⟨I.trW S f, I.isThetaFunO_tr S hf, fun hne h0 => hne ?_, fun g h => ?_⟩⟩
    · have := I.trW_symm_trW S f
      rw [h0] at this
      rw [← this]
      rfl
    · show I.trW S (om (g, I.kap.symm (I.kap h)) (I.symm.trW S (I.trW S f))) 0 = om (g, h) f 0
      rw [I.kap.symm_apply_apply, I.trW_symm_trW]
      show om (g, h) f ((I.phi S).symm 0) = om (g, h) f 0
      rw [map_zero]

end GlobalTheory.Mem.Isom
end
