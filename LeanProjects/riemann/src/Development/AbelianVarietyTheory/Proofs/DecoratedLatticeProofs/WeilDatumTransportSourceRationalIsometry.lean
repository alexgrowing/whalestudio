import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumUniqueOnThetaFunctions

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.WeilSrc

variable {D : D7}

def rmul {k m n : ℕ} (P : Mx D m n) : Mx D k m →+ Mx D k n where
  toFun w := w * P
  map_zero' := Matrix.zero_mul _
  map_add' x y := Matrix.add_mul _ _ _

@[simp] theorem rmul_apply {k m n : ℕ} (P : Mx D m n) (w : Mx D k m) : rmul P w = w * P := rfl

theorem continuous_rmul {k m n : ℕ} (P : Mx D m n) : Continuous (rmul (k := k) P) :=
  continuous_id.matrix_mul continuous_const

theorem theta_comp {ψ : AddChar (AF D.host.F) ℂ} {A B T : HSp D} (P : Matrix (Fin A.rank) (Fin B.rank) D.host.E)
    (h : ∀ x y : WO A T, symplOH B T (x * rat P) (y * rat P) = symplOH A T x y) {f : WO B T → ℂ}
    (hf : IsThetaFunO ψ B T f) : IsThetaFunO ψ A T fun w => f (w * rat P) where
  quasi γ w := by
    have e : ratW T A γ * rat P = ratW T B (γ * P) := by rw [ratW_eq, ratW_eq, rat_mul]
    show f ((ratW T A γ + w) * rat P) = _
    rw [Matrix.add_mul, e, hf.quasi, ← e, h]
  level := by
    obtain ⟨U, hU, k⟩ := hf.level
    refine ⟨U.comap (rmul (rat P)), hU.preimage (continuous_rmul _), fun u hu h0 => ?_⟩
    funext w
    have e := congrFun (k _ hu (map_mul_eq_zero_left _ h0 _)) (w * rat P)
    simp only [heisO, rmul_apply] at e ⊢
    rw [Matrix.add_mul, ← h]
    exact e
  cont := hf.cont.comp (continuous_rmul _)
  smooth k L hL h0 w := by
    have := hf.smooth k ((rmul (rat P)).comp L) ((continuous_rmul _).comp hL)
      (fun t => map_mul_eq_zero_left _ (h0 t) _) (w * rat P)
    simpa only [Matrix.add_mul, AddMonoidHom.comp_apply, rmul_apply] using this

theorem entries_fix_conj {A : Type} [CommRing A] {m n : ℕ} (c : A) {M : Matrix (Fin n) (Fin n) A}
    (hM : ∀ i j, c * M i j = M i j) (P : Matrix (Fin m) (Fin n) A) (Q : Matrix (Fin n) (Fin m) A) (i j : Fin m) :
    c * (P * M * Q) i j = (P * M * Q) i j := by
  simp only [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  conv_rhs => rw [← hM l k]
  ring

theorem entries_fix_right {A : Type} [CommRing A] {k m n : ℕ} (c : A) {M : Matrix (Fin k) (Fin n) A}
    (hM : ∀ i j, c * M i j = M i j) (P : Matrix (Fin n) (Fin m) A) (i : Fin k) (j : Fin m) :
    c * (M * P) i j = (M * P) i j := by
  simp only [Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  conv_rhs => rw [← hM i l]
  ring

theorem det_conj_sq {A : Type} [CommRing A] {m n : ℕ} (h : n = m) {P : Matrix (Fin m) (Fin n) A}
    {Q : Matrix (Fin n) (Fin m) A} (QP : Q * P = 1) (M : Matrix (Fin n) (Fin n) A) : (P * M * Q).det = M.det := by
  subst h
  rw [Matrix.det_mul, Matrix.det_mul, mul_comm (P.det), mul_assoc, ← Matrix.det_mul, mul_eq_one_comm.1 QP,
    Matrix.det_one, mul_one]

theorem mul_empty_zero {k l : ℕ} (x : Mx D k 0) (y : Mx D 0 l) : x ⬝ y = 0 := by
  ext i j
  simp [Matrix.mul_apply]

theorem haar_pull {G H : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [MeasurableSpace G]
    [BorelSpace G] [AddCommGroup H] [TopologicalSpace H] [IsTopologicalAddGroup H] [MeasurableSpace H] [BorelSpace H]
    (e : G ≃+ H) (he : Continuous e) (hes : Continuous e.symm) (Γ : AddSubgroup G) (Λ : AddSubgroup H)
    (hΓ : ∀ x, e x ∈ Λ ↔ x ∈ Γ) (μ : Measure H) (𝓕 : Set H) (hμ : μ.IsAddHaarMeasure)
    (h𝓕 : IsAddFundamentalDomain Λ 𝓕 μ) : ∃ ν : Measure G, ν.IsAddHaarMeasure ∧ IsAddFundamentalDomain Γ (e ⁻¹' 𝓕) ν ∧
      ∀ u : H → ENNReal, ∫⁻ w in e ⁻¹' 𝓕, u (e w) ∂ν = ∫⁻ w in 𝓕, u w ∂μ := by
  let m : G ≃ᵐ H :=
    { toEquiv := e.toEquiv
      measurable_toFun := he.measurable
      measurable_invFun := hes.measurable }
  have hmp : MeasurePreserving m (μ.map e.symm) μ :=
    (MeasurePreserving.symm m.symm ⟨m.symm.measurable, rfl⟩)
  have hmp' : MeasurePreserving e (μ.map e.symm) μ := hmp
  refine ⟨μ.map e.symm, AddEquiv.isAddHaarMeasure_map μ e.symm hes (by simpa using he), ?_, ?_⟩
  · let f : Λ → Γ := fun y => ⟨e.symm y, (hΓ _).1 (by simpa using y.2)⟩
    have hf : Function.Bijective f := by
      constructor
      · intro a b hab
        exact Subtype.ext (e.symm.injective (congrArg Subtype.val hab))
      · intro x
        exact ⟨⟨e x, (hΓ _).2 x.2⟩, Subtype.ext (by simp [f])⟩
    refine h𝓕.preimage_of_equiv hmp'.quasiMeasurePreserving hf ?_
    intro y x
    simp [f, AddSubgroup.vadd_def]
  · intro u
    exact hmp.setLIntegral_comp_preimage_emb m.measurableEmbedding u 𝓕

namespace Zero

variable {S S₀ : HSp D} (d : HypDec S S₀ 0)

theorem rank_eq (d : HypDec S S₀ 0) : S₀.rank = S.rank := by
  have := d.rank_add
  omega

theorem witt_decomposition_zero_section_embed_eq_one : d.j0 ⬝ d.p0 = 1 := by
  have h := d.sum_eq_one
  rwa [mul_empty_zero, mul_empty_zero, zero_add, add_zero] at h

theorem unitaryMatrix_wittCoreEmbedding (g : GA D S₀) : mt S (d.emb0 g) = d.j0 ⬝ mt S₀ g ⬝ d.p0 := by
  rw [d.unitaryMatrix_wittCoreEmbedding, mul_empty_zero, mul_empty_zero, zero_add, add_zero]

theorem gA_eq : adj d.p0 ⬝ (gA S₀ ⬝ d.p0) = gA S := by
  have h := d.gA_eq
  rw [mul_empty_zero, mul_empty_zero, zero_add, add_zero] at h
  exact h.symm

def back (k : GA D S) : GA D S₀ :=
  ofMat S₀ (d.p0 ⬝ mt S k ⬝ d.j0) (by
    have e1 : ∀ X : Mx D S.rank S₀.rank, adj d.p0 ⬝ (gA S₀ ⬝ (d.p0 ⬝ X)) = gA S ⬝ X := fun X => by
      rw [← gA_eq d]; simp only [Matrix.mul_assoc]
    have e2 : ∀ X : Mx D S.rank S₀.rank, adj (mt S k) ⬝ (gA S ⬝ (mt S k ⬝ X)) = gA S ⬝ X := fun X => by
      conv_rhs => rw [← mt_unitary S k]
      simp only [Matrix.mul_assoc]
    simp only [adj_mul, Matrix.mul_assoc, e1, e2]
    exact d.gram_00)

theorem witt_decomposition_zero_embedding_left_inverse (k : GA D S) : d.emb0 (back d k) = k := by
  apply mt_injective S
  rw [unitaryMatrix_wittCoreEmbedding, back, mt_ofMat]
  calc d.j0 * (d.p0 * mt S k * d.j0) * d.p0 = (d.j0 ⬝ d.p0) * mt S k * (d.j0 ⬝ d.p0) := by
        simp only [Matrix.mul_assoc]
    _ = mt S k := by rw [witt_decomposition_zero_section_embed_eq_one, Matrix.one_mul, Matrix.mul_one]

theorem witt_decomposition_zero_embedding_bijective : Function.Bijective d.emb0 :=
  ⟨d.wittDecomp_anisotropicEmbedding_injective, fun k => ⟨back d k, witt_decomposition_zero_embedding_left_inverse d k⟩⟩

variable (T : HSp D)

def eqv : WO S₀ T ≃+ WO S T where
  toFun w := w ⬝ d.p0
  invFun x := x ⬝ d.j0
  left_inv w := by
    show w ⬝ d.p0 ⬝ d.j0 = w
    rw [Matrix.mul_assoc, d.p0_j0, Matrix.mul_one]
  right_inv x := by
    show x * d.j0 ⬝ d.p0 = x
    rw [Matrix.mul_assoc, witt_decomposition_zero_section_embed_eq_one, Matrix.mul_one]
  map_add' x y := Matrix.add_mul _ _ _

theorem eqv_apply (w : WO S₀ T) : eqv d T w = d.ext0 T w := rfl

theorem eqv_symm_apply (x : WO S T) : (eqv d T).symm x = x ⬝ d.j0 := rfl

theorem continuous_eqv : Continuous (eqv d T) := continuous_id.matrix_mul continuous_const

theorem continuous_eqv_symm : Continuous (eqv d T).symm := continuous_id.matrix_mul continuous_const

theorem sympl_eqv (w w' : WO S₀ T) : symplOH S T (eqv d T w) (eqv d T w') = symplOH S₀ T w w' :=
  d.wittDecomp_sympl_extAnisotropic_extAnisotropic T w w'

theorem sympl_eqv_symm (x y : WO S T) : symplOH S₀ T ((eqv d T).symm x) ((eqv d T).symm y) = symplOH S T x y := by
  rw [← sympl_eqv, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]

variable {T} {ψ : AddChar (AF D.host.F) ℂ}

theorem theta_eqv {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) : IsThetaFunO ψ S₀ T fun w => f (eqv d T w) :=
  theta_comp d.q0 (sympl_eqv d T) hf

theorem theta_eqv_symm {f : WO S₀ T → ℂ} (hf : IsThetaFunO ψ S₀ T f) :
    IsThetaFunO ψ S T fun x => f ((eqv d T).symm x) :=
  theta_comp d.i₀ (sympl_eqv_symm d T) hf

theorem theta_iff (f : WO S T → ℂ) : IsThetaFunO ψ S₀ T (fun w => f (d.ext0 T w)) ↔ IsThetaFunO ψ S T f := by
  refine ⟨fun h => ?_, fun h => theta_eqv d h⟩
  have := theta_eqv_symm d h
  simpa only [← eqv_apply, AddEquiv.apply_symm_apply] using this

theorem heisO_eqv (v : WO S₀ T) (K : WO S T → ℂ) :
    (fun w => heisO ψ S T (eqv d T v) K (eqv d T w)) = heisO ψ S₀ T v fun w => K (eqv d T w) := by
  funext w
  simp only [heisO, sympl_eqv, map_add]

def pull (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) : GA D S₀ × GA D T →* Module.End ℂ (WO S₀ T → ℂ) where
  toFun p :=
    { toFun := fun F w => om (d.emb0 p.1, p.2) (fun x => F ((eqv d T).symm x)) (eqv d T w)
      map_add' := fun F G => by
        funext w
        have e : (fun x => (F + G) ((eqv d T).symm x)) = (fun x => F ((eqv d T).symm x)) + fun x => G ((eqv d T).symm x) :=
          rfl
        show om _ (fun x => (F + G) _) _ = om _ (fun x => F _) _ + om _ (fun x => G _) _
        rw [e, map_add]; rfl
      map_smul' := fun c F => by
        funext w
        have e : (fun x => (c • F) ((eqv d T).symm x)) = c • fun x => F ((eqv d T).symm x) := rfl
        show om _ (fun x => (c • F) _) _ = c • om _ (fun x => F _) _
        rw [e, map_smul]; rfl }
  map_one' := by
    refine LinearMap.ext fun F => funext fun w => ?_
    have e : ((d.emb0 (1 : GA D S₀ × GA D T).1, (1 : GA D S₀ × GA D T).2) : GA D S × GA D T) = 1 := by
      simp
    simp only [LinearMap.coe_mk, AddHom.coe_mk, e, map_one, Module.End.one_apply, AddEquiv.symm_apply_apply]
  map_mul' p q := by
    refine LinearMap.ext fun F => funext fun w => ?_
    have e : ((d.emb0 (p * q).1, (p * q).2) : GA D S × GA D T) = (d.emb0 p.1, p.2) * (d.emb0 q.1, q.2) := by
      simp
    simp only [LinearMap.coe_mk, AddHom.coe_mk, e, map_mul, Module.End.mul_apply, AddEquiv.apply_symm_apply]

theorem pull_apply (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (g : GA D S₀) (h : GA D T)
    (F : WO S₀ T → ℂ) : pull d om (g, h) F = fun w => om (d.emb0 g, h) (fun x => F ((eqv d T).symm x)) (eqv d T w) :=
  rfl

end Zero

namespace Zero

variable {S S₀ : HSp D} (d : HypDec S S₀ 0) {T : HSp D} {ψ : AddChar (AF D.host.F) ℂ}

theorem rat_iff (x : WO S T) : (eqv d T).symm x ∈ ratL T S₀ ↔ x ∈ ratL T S := by
  rw [ratL_eq, ratL_eq, eqv_symm_apply]
  constructor
  · intro hx
    have := ratMx_mul hx (rat_mem d.q0)
    rwa [show rat d.q0 = d.p0 from rfl, Matrix.mul_assoc, witt_decomposition_zero_section_embed_eq_one, Matrix.mul_one] at this
  · intro hx
    exact ratMx_mul hx (rat_mem d.i₀)

theorem isWeilDatumO_pull {χS χT : (AE D)ˣ →* Circle} {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
    (H : IsWeilDatumO ψ S T χS χT om) : IsWeilDatumO ψ S₀ T χS χT (pull d om) := by
  have hT : ∀ F, IsThetaFunO ψ S₀ T F → IsThetaFunO ψ S T (fun x => F ((eqv d T).symm x)) := fun F hF =>
    theta_eqv_symm d hF
  refine ⟨H.std, H.hecS, H.hecT, (rank_eq d) ▸ H.resS, H.resT, fun p F hF => ?_, fun g h w₀ F hF => ?_,
    fun γ hγ γ' hγ' F hF => ?_, fun F hF w => ?_, fun μ 𝓕 hμ h𝓕 p F hF => ?_, fun e he g h hg hh x y hx hy => ?_⟩
  · obtain ⟨g, h⟩ := p
    rw [pull_apply]
    exact theta_eqv d (H.om_pres _ _ (hT F hF))
  · rw [pull_apply, pull_apply]
    have e1 : (fun x => heisO ψ S₀ T w₀ F ((eqv d T).symm x)) =
        heisO ψ S T (eqv d T w₀) (fun x => F ((eqv d T).symm x)) := by
      funext x
      simp only [heisO]
      rw [← sympl_eqv_symm d T x (eqv d T w₀), map_add, AddEquiv.symm_apply_apply]
    rw [e1, H.om_heis _ _ _ _ (hT F hF)]
    rw [show actO S T (d.emb0 g) h (eqv d T w₀) = eqv d T (actO S₀ T g h w₀) from d.wittDecomp_homAction_extAnisotropic_equivariant T g h w₀]
    exact heisO_eqv d _ _
  · rw [pull_apply]
    show om _ _ (eqv d T 0) = F 0
    rw [map_zero, H.om_aut _ (d.wittDecomp_anisotropicEmbedding_mem_rationalPoints hγ) γ' hγ' _ (hT F hF)]
    show F ((eqv d T).symm 0) = F 0
    rw [map_zero]
  · exact (H.om_cont _ (hT F hF) (eqv d T w)).comp ((d.continuous_embed.comp continuous_fst).prodMk continuous_snd)
  · haveI : BorelSpace (WO S T) := ⟨rfl⟩
    haveI : BorelSpace (WO S₀ T) := ⟨rfl⟩
    obtain ⟨ν, hν, h𝓖, hu⟩ := haar_pull (eqv d T).symm (continuous_eqv_symm d T) (continuous_eqv d T) (ratL T S)
      (ratL T S₀) (rat_iff d) μ 𝓕 hμ h𝓕
    have e1 := hu fun w => ‖pull d om p F w‖ₑ ^ 2
    have e2 := hu fun w => ‖F w‖ₑ ^ 2
    have e3 : ∀ x, pull d om p F ((eqv d T).symm x) = om (d.emb0 p.1, p.2) (fun x => F ((eqv d T).symm x)) x :=
      fun x => by
        show om _ _ (eqv d T ((eqv d T).symm x)) = _
        rw [AddEquiv.apply_symm_apply]
    simp only [e3] at e1
    rw [← e1, ← e2]
    exact H.om_unit ν _ hν h𝓖 _ _ (hT F hF)
  · have hmt : mt S (d.emb0 g) - 1 = d.j0 ⬝ (mt S₀ g - 1) ⬝ d.p0 := by
      rw [unitaryMatrix_wittCoreEmbedding, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, witt_decomposition_zero_section_embed_eq_one]
    have hsupp : SuppAt e S (d.emb0 g) := by
      unfold SuppAt at hg ⊢
      intro i j
      rw [hmt]
      exact entries_fix_conj _ hg _ _ i j
    have hdet : IsDetAt e S (d.emb0 g) x := by
      unfold IsDetAt at hx ⊢
      rw [unitaryMatrix_wittCoreEmbedding, det_conj_sq (rank_eq d) d.p0_j0 (mt S₀ g)]
      exact hx
    obtain ⟨r, hr, Hs⟩ := H.om_split e he (d.emb0 g) h hsupp hh x y hdet hy
    refine ⟨r, hr, fun ℓ hℓ F hF => ?_⟩
    let ℓ' : (WO S T → ℂ) →ₗ[ℂ] ℂ := ℓ ∘ₗ LinearMap.funLeft ℂ ℂ (eqv d T)
    have hinv : ∀ u : WO S T, (∀ i j, cA D e * u i j = u i j) → ∀ G, IsThetaFunO ψ S T G →
        ℓ' (heisO ψ S T u G) = ℓ' G := by
      intro u hu G hG
      show ℓ (fun w => heisO ψ S T u G (eqv d T w)) = ℓ (fun w => G (eqv d T w))
      have e := heisO_eqv (ψ := ψ) d ((eqv d T).symm u) G
      rw [AddEquiv.apply_symm_apply] at e
      rw [e]
      exact hℓ _ (fun i j => entries_fix_right _ hu d.j0 i j) _ (theta_eqv d hG)
    have := Hs ℓ' hinv _ (hT F hF)
    have e1 : ℓ' (fun x => F ((eqv d T).symm x)) = ℓ F := by
      show ℓ (fun w => F ((eqv d T).symm (eqv d T w))) = ℓ F
      simp only [AddEquiv.symm_apply_apply]
    rw [e1] at this
    exact this

end Zero

theorem om0_ext0_eq_om_emb0_of_isWeilDatumO : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S S₀ T : HSp D) (d : HypDec S S₀ 0),
    IsStdChar D ψ (-1) → Function.Bijective d.emb0 ∧ Function.Bijective (d.ext0 T) ∧
      (∀ f : WO S T → ℂ, IsThetaFunO ψ S₀ T (fun w => f (d.ext0 T w)) ↔ IsThetaFunO ψ S T f) ∧
      ∀ (χS χT : (AE D)ˣ →* Circle) (om : Om S T) (om₀ : Om S₀ T), IsWeilDatumO ψ S T χS χT om →
        IsWeilDatumO ψ S₀ T χS χT om₀ → ∀ g h f, IsThetaFunO ψ S T f →
          om₀ (g, h) (fun w => f (d.ext0 T w)) = fun w => om (d.emb0 g, h) f (d.ext0 T w) := by
  intro D ψ S S₀ T d hψ
  refine ⟨Zero.witt_decomposition_zero_embedding_bijective d, (Zero.eqv d T).bijective, fun f => Zero.theta_iff d f,
    fun χS χT om om₀ H H₀ g h f hf => ?_⟩
  have hf₀ := (Zero.theta_iff d f).2 hf
  rw [GlobalTheory.WeilUniq.weilDatum_unique D ψ hψ S₀ T χS χT om₀ (Zero.pull d om) H₀ (Zero.isWeilDatumO_pull d H) (g, h) _ hf₀,
    Zero.pull_apply]
  funext w
  show om _ (fun x => f (Zero.eqv d T ((Zero.eqv d T).symm x))) _ = _
  simp only [AddEquiv.apply_symm_apply]
  rfl

end GlobalTheory.WeilSrc
