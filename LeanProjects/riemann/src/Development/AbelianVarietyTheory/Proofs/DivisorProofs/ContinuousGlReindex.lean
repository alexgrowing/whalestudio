import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteDimensional
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemThInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThLiftMemLiftSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocFieldLP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSBZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitUnitaryLiftTendstoOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearFunctionalGoodPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepRationalDarbouxFixesThetaDistributionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxSymplecticHermitianSkewStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicIntegrableOnDomainStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzSpanLocalTensorsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralCombinationGlNormalFormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralCombinationGlLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeterminantInducedIsAdmissibleStatement

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar GlobalTheory.ThK.TowerInt
open GlobalTheory.ThK.LiftConst GlobalTheory.ThK.SplitInv GlobalTheory.ThK.CoinvFin GlobalTheory.SplitUnitLift

namespace GlobalTheory.ThK.LiftAdm

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

section Tens

variable {κ : Type} {v : Pl F}

def setAt (v : Pl F) (x : κ → AF F) (t : κ → Fv F v) : κ → AF F :=
  x + ((fun i => GlobalTheory.LatVac.liftV v (t i)) - partFin v x)

theorem tens_setAt {r : (κ → AF F) → ℂ} (hr : ∀ x z, At (evFin F v) z → r (x + z) = r x) (φ : (κ → Fv F v) → ℂ)
    (x : κ → AF F) (t : κ → Fv F v) : tens (evFin F v) φ r (setAt v x t) = φ t * r x := by
  have hz : At (evFin F v) ((fun i => GlobalTheory.LatVac.liftV v (t i)) - partFin v x) := fun u hu => by
    rw [smul_sub, at_partFin v x u hu, sub_zero]
    exact funext fun i => GlobalTheory.LatVac.at_liftV v _ u hu
  have he : (fun i => evFin F v (setAt v x t i)) = t := funext fun i => by
    simp [setAt, partFin, GlobalTheory.LatVac.evFin_liftV]
  rw [tens, he, setAt, hr x _ hz]

theorem tens_inj {r : (κ → AF F) → ℂ} (hr : ∀ x z, At (evFin F v) z → r (x + z) = r x) (h0 : r ≠ 0)
    {φ φ' : (κ → Fv F v) → ℂ} (h : tens (evFin F v) φ r = tens (evFin F v) φ' r) : φ = φ' := by
  obtain ⟨x, hx⟩ := Function.ne_iff.1 h0
  funext t
  have := congrFun h (setAt v x t)
  rw [tens_setAt hr, tens_setAt hr] at this
  exact mul_right_cancel₀ hx this

def tensL (v : Pl F) (r : (κ → AF F) → ℂ) : ((κ → Fv F v) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ) where
  toFun φ := tens (evFin F v) φ r
  map_add' φ φ' := by funext x; simp [tens, add_mul]
  map_smul' c φ := by funext x; simp [tens, mul_assoc]

variable [Fintype κ]

theorem mem_SB_of_rest {φ : (κ → Fv F v) → ℂ} {r : (κ → AF F) → ℂ} (hr : Rest (evFin F v) φ r) (h0 : r ≠ 0) :
    φ ∈ SB (κ → Fv F v) := by
  obtain ⟨x, hx⟩ := Function.ne_iff.1 h0
  let p : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → Fv F v) → ℂ) := LinearMap.funLeft ℂ ℂ (setAt v x)
  have hp : ∀ (χ : (κ → Fv F v) → ℂ) (s : (κ → AF F) → ℂ), (∀ x z, At (evFin F v) z → s (x + z) = s x) →
      p (tens (evFin F v) χ s) = s x • χ := fun χ s hs => funext fun t => by
    show tens (evFin F v) χ s (setAt v x t) = _
    rw [tens_setAt hs, mul_comm]; rfl
  have h : p (tens (evFin F v) φ r) ∈ SB (κ → Fv F v) := by
    refine (Submodule.span_le (p := (SB (κ → Fv F v)).comap p)).2 ?_ (GlobalTheory.T.schwartz_span_local_tensors F v κ hr.2)
    rintro _ ⟨χ, s, hχ, hs, rfl⟩
    show p (tens (evFin F v) χ s) ∈ SB (κ → Fv F v)
    rw [hp χ s (hs χ hχ).1]
    exact Submodule.smul_mem _ _ hχ
  rw [hp φ r hr.1] at h
  exact (Submodule.smul_mem_iff _ hx).1 h

theorem exists_rests (v : Pl F) {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) :
    ∃ (J : Type) (_ : Finite J) (r : J → (κ → AF F) → ℂ), (∀ j, ∀ φ ∈ SB (κ → Fv F v), Rest (evFin F v) φ (r j)) ∧
      ∀ Φ', (Φ' = Φ ∨ (Φ ≠ 0 ∧ ∃ (φ φ' : (κ → Fv F v) → ℂ) (s : (κ → AF F) → ℂ),
        Rest (evFin F v) φ s ∧ Φ = tens (evFin F v) φ s ∧ Rest (evFin F v) φ' s ∧ Φ' = tens (evFin F v) φ' s)) →
        Φ' ∈ ⨆ j, (SB (κ → Fv F v)).map (tensL v (r j)) := by
  obtain ⟨T, hT, hmem⟩ := Submodule.mem_span_finite_of_mem_span (GlobalTheory.T.schwartz_span_local_tensors F v κ hΦ)
  choose χ r hχ hr he using fun j : T => hT j.2
  have h1 : Φ ∈ ⨆ j, (SB (κ → Fv F v)).map (tensL v (r j)) := by
    refine Submodule.span_le.2 (fun y hy => ?_) hmem
    exact Submodule.mem_iSup_of_mem (⟨y, hy⟩ : T) ⟨_, hχ ⟨y, hy⟩, (he ⟨y, hy⟩).symm⟩
  refine ⟨T, inferInstance, r, hr, ?_⟩
  rintro Φ' (rfl | ⟨hne, φ, φ', s, hs, rfl, hs', rfl⟩)
  · exact h1
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact hne (funext fun x => mul_zero _)
  obtain ⟨t, ht⟩ : ∃ t, φ t ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (funext fun x => by simp [tens, h])
  have hφ' := mem_SB_of_rest hs' hs0
  let Q : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ) :=
    { toFun := fun Ψ => tens (evFin F v) φ' fun x => Ψ (setAt v x t)
      map_add' := fun _ _ => by funext x; simp [tens, mul_add]
      map_smul' := fun _ _ => by funext x; simp [tens, mul_left_comm] }
  have hQ : ∀ (ψ : (κ → Fv F v) → ℂ) (u : (κ → AF F) → ℂ), (∀ x z, At (evFin F v) z → u (x + z) = u x) →
      Q (tens (evFin F v) ψ u) = ψ t • tens (evFin F v) φ' u := fun ψ u hu => funext fun x => by
    show φ' _ * tens (evFin F v) ψ u (setAt v x t) = ψ t * (φ' _ * u x)
    rw [tens_setAt hu, mul_left_comm]
  have h2 : Q (tens (evFin F v) φ s) ∈ ⨆ j, (SB (κ → Fv F v)).map (tensL v (r j)) := by
    refine (iSup_le fun j => ?_ : _ ≤ Submodule.comap Q (⨆ j, (SB (κ → Fv F v)).map (tensL v (r j)))) h1
    rintro _ ⟨ψ, hψ, rfl⟩
    show Q (tens (evFin F v) ψ (r j)) ∈ ⨆ j, (SB (κ → Fv F v)).map (tensL v (r j))
    rw [hQ ψ _ (hr j ψ hψ).1]
    exact Submodule.smul_mem _ _ (Submodule.mem_iSup_of_mem j ⟨φ', hφ', rfl⟩)
  rw [hQ φ s hs.1] at h2
  exact (Submodule.smul_mem_iff _ ht).1 h2

end Tens

theorem eq_liftU (h : IsCMExt F E σ) {v : Pl F} (t : E →ₐ[F] Fv F v) {n : ℕ}
    (X : Spc F E n) (ε : F) (herm : ∀ i j, σ (X.J j i) = algebraMap F E ε * X.J i j) (hJ : IsUnit (X.J.map t).det)
    (g : UA σ X.J) (hg : g ∈ UAt σ X (evFin F v)) :
    g = liftU h t X.J ε herm hJ (Matrix.GeneralLinearGroup.map (piW t) g.1) := by
  set g' := Matrix.GeneralLinearGroup.map (piW t) g.1 with hg'
  have hv : g'.val = (mat g).map (piW t) := rfl
  set L := liftU h t X.J ε herm hJ g' with hL
  have hU : (mat g)ᵀ * incM F X.J * (mat g).map (cA σ) = incM F X.J := g.2
  have tr : ∀ (A B C : Matrix (Fin n) (Fin n) (AE F E)),
      (Aᵀ * B * C).map (piW t) = (A.map (piW t))ᵀ * B.map (piW t) * C.map (piW t) := fun A B C => by
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
  have hJm : (incM F X.J).map (piW t) = X.J.map t := by
    unfold incM
    rw [Matrix.map_map]
    exact Matrix.ext fun i j => GlobalTheory.SplitGLLift.piW_inclR t (X.J i j)
  have hcm : ((mat g).map (cA σ)).map (piW t) = (mat g).map (piW (t.comp σ)) := by
    rw [Matrix.map_map]
    exact Matrix.ext fun i j => GlobalTheory.VacIso.piW_cA σ t _
  have hUt : ((mat g)ᵀ * incM F X.J * (mat g).map (cA σ)).map (piW t) = (incM F X.J).map (piW t) := by rw [hU]
  rw [tr, hJm, hcm, ← hv] at hUt
  set gs := (mat g).map (piW (t.comp σ)) with hgs
  have hσ : gs = (X.J.map t)⁻¹ * ((g'⁻¹ : GL (Fin n) (Fv F v)).val)ᵀ * X.J.map t := by
    have e : gs = ((X.J.map t)⁻¹ * ((g'⁻¹ : GL (Fin n) (Fv F v)).val)ᵀ) * ((g'.val)ᵀ * X.J.map t * gs) := by
      rw [show ((X.J.map t)⁻¹ * ((g'⁻¹ : GL (Fin n) (Fv F v)).val)ᵀ) * ((g'.val)ᵀ * X.J.map t * gs) =
          (X.J.map t)⁻¹ * (((g'⁻¹ : GL (Fin n) (Fv F v)).val)ᵀ * (g'.val)ᵀ) * X.J.map t * gs by
            simp only [Matrix.mul_assoc],
        ← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one, Matrix.mul_one,
        Matrix.nonsing_inv_mul _ hJ, Matrix.one_mul]
    rw [e, hUt]
  have hgA : At (evFin F v) (mat g - 1) := hg
  have hLA : At (evFin F v) (mat L - 1) := liftU_mem_UAt h t X ε herm hJ g'
  have hLt : (mat L).map (piW t) = g'.val := liftU_piW h t X.J ε herm hJ g'
  have hLs : (mat L).map (piW (t.comp σ)) = (X.J.map t)⁻¹ * ((g'⁻¹ : GL (Fin n) (Fv F v)).val)ᵀ * X.J.map t :=
    liftU_piW_comp h t X.J ε herm hJ g'
  apply Subtype.ext
  apply Units.ext
  show mat g = mat L
  ext i j
  rw [← sub_eq_zero]
  have hz : mat g i j - mat L i j = (mat g - 1) i j - (mat L - 1) i j := by
    simp only [Matrix.sub_apply]; ring
  refine GlobalTheory.VacIso.eq_zero_of_at_split h t ?_ ?_ ?_
  · intro u hu
    have e1 := congrFun (congrFun (hgA u hu) i) j
    have e2 := congrFun (congrFun (hLA u hu) i) j
    simp only [Matrix.smul_apply, Matrix.zero_apply] at e1 e2
    rw [hz, smul_sub, e1, e2, sub_zero]
  · have e1 := congrFun (congrFun hLt i) j
    have e2 := congrFun (congrFun hv i) j
    simp only [Matrix.map_apply] at e1 e2
    rw [map_sub, e1, ← e2, sub_self]
  · have e1 := congrFun (congrFun hLs i) j
    have e2 := congrFun (congrFun hσ i) j
    simp only [hgs, Matrix.map_apply] at e1 e2
    rw [map_sub, e1, e2, sub_self]

theorem glReindex_surj {k : Type} [Field k] {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (e : m ≃ n) (g : GL n k) : GlobalTheory.LocTypeGood.glReindex e (GlobalTheory.LocTypeGood.glReindex e.symm g) = g := by
  ext i j
  simp [GlobalTheory.LocTypeGood.glReindex]

theorem continuous_glReindex {k : Type} [Field k] [TopologicalSpace k] {m n : Type} [Fintype m] [DecidableEq m] [Fintype n]
    [DecidableEq n] (e : m ≃ n) : Continuous (GlobalTheory.LocTypeGood.glReindex (k := k) e) :=
  Continuous.units_map _ (continuous_matrix fun i j => continuous_id.matrix_elem (e.symm i) (e.symm j))

variable {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

theorem det_ne_zero_of_map {m : ℕ} {J : Matrix (Fin m) (Fin m) E} {v : Pl F} (τ : E →ₐ[F] Fv F v)
    (h : IsUnit (J.map τ).det) : J.det ≠ 0 := by
  intro h0
  rw [show (J.map τ).det = τ J.det from (AlgHom.map_det τ J).symm, h0, map_zero] at h
  exact not_isUnit_zero h

theorem exists_form (hK : KP) {B : Base F E} {Mo : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W} {r s r' s' : ℕ}
    (hP : IsPair B Mo χX χW om r s r' s') (hXd : X.J.det ≠ 0) (hYd : W.J.det ≠ 0)
    (f : UA σ W.J → ℂ) (hfc : Continuous f) (hfl : ∀ γ ∈ ratU σ W.J, ∀ h, f (γ * h) = f h)
    (hfd : ∀ N : ℕ, ∃ C : ℝ, ∀ h, ‖f h‖ * (qht h : ℝ) ^ N ≤ C)
    (μ : Measure (UA σ W.J)) (𝓕 : Set (UA σ W.J)) (hμ : μ.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (ratU σ W.J) 𝓕 μ)
    {G : Type} [Group G] (L : G →* UA σ W.J) :
    ∃ b : orb ((GlobalTheory.PRep.rightReg ℂ (UA σ W.J) ℂ).comp L) f →ₗ[ℂ] schA F (Fin n × Fin d) →ₗ⋆[ℂ] (UA σ X.J → ℂ),
      (∀ u Ψ, b u Ψ = thLift om Ψ.1 μ 𝓕 u.1) ∧
      ∀ u ∈ orb ((GlobalTheory.PRep.rightReg ℂ (UA σ W.J) ℂ).comp L) f, ∀ Ψ ∈ schA F (Fin n × Fin d), ∀ x,
        thLift om (om (1, x) Ψ) μ 𝓕 (rt x u) = thLift om Ψ μ 𝓕 u := by
  set M := orb ((GlobalTheory.PRep.rightReg ℂ (UA σ W.J) ℂ).comp L) f with hM
  have hcm := hP.base.cm
  have hom := hP.weil
  have pres : ∀ x, ∀ Φ ∈ schA F (Fin n × Fin d), om x Φ ∈ schA F (Fin n × Fin d) := fun x Φ hΦ =>
    (IsUWeilPair.isUSplitting hom).pres x Φ hΦ
  have omg : ∀ g (h x : UA σ W.J) Φ, om (g, h) (om (1, x) Φ) = om (g, h * x) Φ := fun g h x Φ => by
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
  have thInv : ∀ g, ∀ γ ∈ ratU σ W.J, ∀ Φ ∈ schA F (Fin n × Fin d), ∀ h,
      thetaSum F (om (g, γ * h) Φ) = thetaSum F (om (g, h) Φ) := fun g γ hγ Φ hΦ h => by
    have e : om (g, γ * h) Φ = om (1, γ) (om (g, h) Φ) := by
      rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul]
    rw [e]
    exact GlobalTheory.T.weilRep_rationalDarboux_fixes_thetaDistribution F E σ hcm B.ψ hP.base.std n d X.J W.J hP.herm.herm hXd hP.skew.skew hYd Mo.co hP.good.rat χX χW
      hP.hX hP.hW om hom 1 (one_mem _) γ hγ _ (pres _ _ hΦ)
  have memL : ∀ u ∈ M, ∀ γ ∈ ratU σ W.J, ∀ h, u (γ * h) = u h := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem u h =>
      obtain ⟨a, rfl⟩ := h
      intro γ hγ h
      show f (γ * h * L a) = f (h * L a)
      rw [mul_assoc]
      exact hfl γ hγ _
    | zero => intro γ _ h; rfl
    | add u w _ _ hu hw => intro γ hγ h; simp [hu γ hγ h, hw γ hγ h]
    | smul c u _ hu => intro γ hγ h; simp [hu γ hγ h]
  have intg : ∀ g, ∀ u ∈ M, ∀ Φ ∈ schA F (Fin n × Fin d),
      IntegrableOn (fun h => u h * (starRingEnd ℂ) (thetaSum F (om (g, h) Φ))) 𝓕 μ := by
    intro g u hu
    induction hu using Submodule.span_induction with
    | mem u h =>
      obtain ⟨a, rfl⟩ := h
      intro Φ hΦ
      have h1 := GlobalTheory.T.darboux_symplectic_hermitian_skew F E σ hK hcm B.ψ hP.base.std n d X.J W.J hP.herm.herm hXd hP.skew.skew hYd Mo.co hP.good.rat
        χX χW hP.hX hP.hW om hom f hfc hfl hfd (om (1, (L a)⁻¹) Φ) (pres _ _ hΦ) g μ 𝓕 hμ h𝓕
      have h2 := (GlobalTheory.T.automorphic_integrable_on_domain F E σ hcm d W.J hP.skew.skew hYd μ 𝓕 hμ h𝓕 _ (fun γ hγ h => by
        rw [hfl γ hγ h, thInv g γ hγ _ (pres _ _ hΦ) h]) (L a)).1 h1
      have e : (fun h => f (h * L a) * (starRingEnd ℂ) (thetaSum F (om (g, h * L a) (om (1, (L a)⁻¹) Φ)))) =
          fun h => f (h * L a) * (starRingEnd ℂ) (thetaSum F (om (g, h) Φ)) := funext fun h => by
        rw [omg, mul_inv_cancel_right]
      rw [e] at h2
      exact h2
    | zero => intro Φ _; simp [integrableOn_zero]
    | add u w _ _ hu hw =>
      intro Φ hΦ
      refine ((hu Φ hΦ).add (hw Φ hΦ)).congr (Eventually.of_forall fun h => ?_)
      simp [add_mul]
    | smul c u _ hu =>
      intro Φ hΦ
      refine ((hu Φ hΦ).const_mul c).congr (Eventually.of_forall fun h => ?_)
      simp [mul_assoc]
  refine ⟨LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun u Ψ => thLift om Ψ.1 μ 𝓕 u.1) ?_ ?_ ?_ ?_,
    fun _ _ => rfl, ?_⟩
  · intro u w Φ
    funext g
    simp only [thLift_def, theta, Pi.add_apply, ← integral_add (intg g u.1 u.2 Φ.1 Φ.2) (intg g w.1 w.2 Φ.1 Φ.2)]
    refine integral_congr_ae (Eventually.of_forall fun h => ?_)
    simp [add_mul]
  · intro c u Φ
    funext g
    simp only [thLift_def, theta, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun h => ?_)
    simp [mul_assoc]
  · intro u Φ Ψ
    funext g
    simp only [thLift_def, theta, Pi.add_apply, ← integral_add (intg g u.1 u.2 Φ.1 Φ.2) (intg g u.1 u.2 Ψ.1 Ψ.2)]
    refine integral_congr_ae (Eventually.of_forall fun h => ?_)
    simp only [Submodule.coe_add, map_add]
    rw [thetaSum_add F (pres _ _ Φ.2) (pres _ _ Ψ.2), map_add, mul_add]
  · intro c u Φ
    funext g
    simp only [thLift_def, theta, Pi.smul_apply, smul_eq_mul, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun h => ?_)
    simp only [Submodule.coe_smul, map_smul]
    rw [thetaSum_smul, map_mul]
    ring
  · intro u hu Φ hΦ x
    funext g
    have h2 := (GlobalTheory.T.automorphic_integrable_on_domain F E σ hcm d W.J hP.skew.skew hYd μ 𝓕 hμ h𝓕
      (fun h => u h * (starRingEnd ℂ) (thetaSum F (om (g, h) Φ)))
      (fun γ hγ h => by rw [memL u hu γ hγ h, thInv g γ hγ Φ hΦ h]) x).2
    simp only [thLift_def, theta, rt, omg]
    exact h2

theorem fin_gen (hK : KP) {B : Base F E} {Mo : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W} {r s r' s' : ℕ}
    (hP : IsPair B Mo χX χW om r s r' s') (hXd : X.J.det ≠ 0) (hYd : W.J.det ≠ 0) (v : Pl F) (τ : E →ₐ[F] Fv F v)
    (L₁ : GL (Fin n) (Fv F v) →* UA σ X.J) (hL₁c : Continuous L₁) (hL₁ : ∀ g, L₁ g ∈ UAt σ X (evFin F v))
    (hL₁t : ∀ g, (mat (L₁ g)).map (piW τ) = g.val)
    (hW : ∀ h : GL (Fin d) (Fv F v), ∃ y ∈ UAt σ W (evFin F v), (mat y).map (piW τ) = h.val)
    (ρ : (Fin n × Fin d → AF F) → ℂ) (hρ : ∀ φ ∈ SB (Fin n × Fin d → Fv F v), Rest (evFin F v) φ ρ)
    (K : Subgroup (GL (Fin n) (Fv F v))) (hKo : IsOpen (K : Set (GL (Fin n) (Fv F v)))) :
    ∃ A : Set ((Fin n × Fin d → Fv F v) → ℂ), A.Finite ∧ (∀ a ∈ A, a ∈ SB (Fin n × Fin d → Fv F v)) ∧
      ∀ χ ∈ SB (Fin n × Fin d → Fv F v), (∀ k ∈ K, om (L₁ k, 1) (tens (evFin F v) χ ρ) = tens (evFin F v) χ ρ) →
        tens (evFin F v) χ ρ ∈ Submodule.span ℂ
          {x | ∃ a ∈ A, ∃ y ∈ UAt σ W (evFin F v), x = om (1, y) (tens (evFin F v) a ρ)} := by
  by_cases h0 : ρ = 0
  · refine ⟨∅, Set.finite_empty, by simp, fun χ _ _ => ?_⟩
    rw [h0, show tens (evFin F v) χ (0 : (Fin n × Fin d → AF F) → ℂ) = 0 from funext fun x => mul_zero _]
    exact zero_mem _
  have hcm := hP.base.cm
  have hA := GlobalTheory.T.theta_action_exists hK.base F E σ B n d X W Mo χX χW om r s r' s' hP v
  have hinv := (hρ 0 (zero_mem _)).1
  have h1X := GlobalTheory.SplitTransportPair.one_mem_UAt (σ := σ) X v
  have h1W := GlobalTheory.SplitTransportPair.one_mem_UAt (σ := σ) W v
  obtain ⟨ι, hι⟩ := GlobalTheory.SplitTransportPair.exists_isLinW hcm Mo B.ψ hP.base.std hP.herm.herm hXd hP.skew.skew hYd v τ
  have hbij := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model.IsLin.bij hι
  have hsh := fun g hg h hh => GlobalTheory.SplitTransportPair.shape hcm Mo B.ψ hP.base.std hP.herm.herm hXd hP.skew.skew hYd χX χW om
    hP.weil v τ ι hι g h (fun φ hφ => (hA.1 g hg h hh φ hφ).exists)
  have hfix : ∀ g, ∀ χ ∈ SB (Fin n × Fin d → Fv F v), om (L₁ g, 1) (tens (evFin F v) χ ρ) = tens (evFin F v) χ ρ →
      Acts (evFin F v) (om (L₁ g, 1)) χ χ := fun g χ hχ h => by
    obtain ⟨χ₁, -, ha⟩ := (hA.1 _ (hL₁ g) 1 h1W χ hχ).exists
    have := tens_inj hinv h0 ((ha ρ (hρ χ hχ)).symm.trans h)
    rwa [this] at ha
  obtain ⟨f₀, hf₀, hf0⟩ := GlobalTheory.SplitTransportPair.exists_SB_zero v n d
  obtain ⟨φ₀, hφ₀, rfl⟩ := hbij.surjOn hf₀
  let ω₁ : Representation ℂ (GL (Fin n) (Fv F v)) ((Fin n × Fin d → AF F) → ℂ) := (om.comp (MonoidHom.inl _ _)).comp L₁
  have hso : IsOpen (stab ω₁ (tens (evFin F v) φ₀ ρ) : Set (GL (Fin n) (Fv F v))) := by
    obtain ⟨U, hU, hU'⟩ := hA.2.2 φ₀ hφ₀
    have hc : Continuous fun g => ((L₁ g, 1) : UA σ X.J × UA σ W.J) := hL₁c.prodMk continuous_const
    refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (mem_of_superset (hc.continuousAt.preimage_mem_nhds (t := U) ?_) ?_)
    · rw [map_one]; exact hU
    · intro g hg
      exact hU' _ hg (hL₁ g) h1W ρ (hρ _ hφ₀)
  obtain ⟨A₀, hA₀, hA₀S, hspan⟩ := GlobalTheory.T.integral_combination_gl_lattice (Fv F v) n d (GlobalTheory.T.integral_combination_gl_normal_form (Fv F v) n d)
    (K ⊓ stab ω₁ (tens (evFin F v) φ₀ ρ)) (hKo.inter hso)
  have kex : ∀ a : A₀, ∃ φ ∈ SB (Fin n × Fin d → Fv F v), ι φ = a.1 := fun a => hbij.surjOn (hA₀S a.1 a.2)
  choose kap hkS hk using kex
  haveI : Finite A₀ := hA₀
  refine ⟨Set.range kap, Set.finite_range _, by rintro _ ⟨a, rfl⟩; exact hkS a, fun χ hχ hχK => ?_⟩
  set T := Submodule.span ℂ
    {x | ∃ a ∈ Set.range kap, ∃ y ∈ UAt σ W (evFin F v), x = om (1, y) (tens (evFin F v) a ρ)} with hT
  have h1 := hspan (ι χ) (hbij.mapsTo hχ) fun g hg Y => by
    obtain ⟨c, hc⟩ := hsh _ (hL₁ g) 1 h1W
    simp only [hL₁t, GlobalTheory.SplitTransportPair.mat_one_map, Matrix.transpose_one, Matrix.mul_one] at hc
    have e := hc φ₀ hφ₀ φ₀ (hfix g φ₀ hφ₀ hg.2) 0
    rw [Matrix.mul_zero] at e
    have hc1 : c = 1 := (mul_right_cancel₀ hf0 ((one_mul _).trans e)).symm
    rw [hc χ hχ χ (hfix g χ hχ (hχK g hg.1)) Y, hc1, one_mul]
  have h2 : ι χ ∈ (SB (Fin n × Fin d → Fv F v) ⊓ T.comap (tensL v ρ)).map ι := by
    refine Submodule.span_le.2 ?_ h1
    rintro _ ⟨a, ha, h, rfl⟩
    obtain ⟨y, hy, hyt⟩ := hW (GlobalTheory.SplitFlip.invT h)
    obtain ⟨c, hc⟩ := hsh 1 h1X y hy
    simp only [hyt, GlobalTheory.SplitTransportPair.mat_one_map, Matrix.one_mul, GlobalTheory.SplitFlip.invT_val,
      Matrix.transpose_transpose] at hc
    obtain ⟨φ₁, hφ₁, ha₁⟩ := (hA.1 1 h1X y hy _ (hkS ⟨a, ha⟩)).exists
    have e : ι φ₁ = c • fun Y => a (Y * h.val) := funext fun Y => by
      have := hc _ (hkS ⟨a, ha⟩) φ₁ ha₁ (Y * h.val)
      rwa [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one, hk] at this
    have e2 := ha₁ ρ (hρ _ (hkS ⟨a, ha⟩))
    by_cases hc0 : c = 0
    · have z1 : φ₁ = 0 := hbij.injOn hφ₁ (zero_mem _) (by rw [e, hc0, zero_smul, map_zero])
      have z2 : tens (evFin F v) (kap ⟨a, ha⟩) ρ = tens (evFin F v) 0 ρ := by
        have z0 : tens (evFin F v) (0 : (Fin n × Fin d → Fv F v) → ℂ) ρ = 0 := funext fun x => zero_mul _
        have := congrArg (om ((1, y) : UA σ X.J × UA σ W.J)⁻¹) e2
        rwa [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply, z1, z0, map_zero,
          ← z0] at this
      have z3 : a = 0 := by
        have := hk ⟨a, ha⟩
        rw [tens_inj hinv h0 z2, map_zero] at this
        exact this.symm
      rw [z3]
      exact zero_mem _
    · have hm : φ₁ ∈ SB (Fin n × Fin d → Fv F v) ⊓ T.comap (tensL v ρ) :=
        ⟨hφ₁, Submodule.subset_span ⟨_, ⟨⟨a, ha⟩, rfl⟩, y, hy, e2.symm⟩⟩
      have := Submodule.mem_map_of_mem (f := ι) hm
      rw [e] at this
      exact (Submodule.smul_mem_iff _ hc0).1 this
  obtain ⟨ψ, hψ, e⟩ := h2
  rw [← hbij.injOn hψ.1 hχ e]
  exact hψ.2

theorem smAdm_of_locType (hK : KP) {B : Base F E} {Mo : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W} {r s r' s' : ℕ}
    (hP : IsPair B Mo χX χW om r s r' s')
    (f : UA σ W.J → ℂ) (hfc : Continuous f) (hfl : ∀ γ ∈ ratU σ W.J, ∀ h, f (γ * h) = f h)
    (hfd : ∀ N : ℕ, ∃ C : ℝ, ∀ h, ‖f h‖ * (qht h : ℝ) ^ N ≤ C)
    (μ : Measure (UA σ W.J)) (𝓕 : Set (UA σ W.J)) (hμ : μ.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (ratU σ W.J) 𝓕 μ)
    {Φ : (Fin n × Fin d → AF F) → ℂ} (hΦ : Φ ∈ schA F (Fin n × Fin d)) (v : Pl F) (τ : E →ₐ[F] Fv F v)
    (herm : ∀ i j, σ (W.J j i) = algebraMap F E (-1) * W.J i j) (hJ : IsUnit (W.J.map τ).det) {x x' : ℕ}
    (e : Fin (x + x') ≃ Fin d) (χ₁ χ₂ : (Fv F v)ˣ →* ℂˣ)
    (hf : GlobalTheory.LocTypeGood.HasLocType hP.base.cm τ W.J (-1) herm hJ e χ₁ χ₂ f) :
    ∃ 𝒦 : Set (Subgroup (UA σ X.J)), SmAdm (UAtSub σ X (evFin F v)) (liftSpace om Φ μ 𝓕 f v) 𝒦 := by
  have hcm := hP.base.cm
  have hermX : ∀ i j, σ (X.J j i) = algebraMap F E 1 * X.J i j := fun i j => by
    rw [map_one, one_mul]; exact hP.herm.herm i j
  have hJX : IsUnit (X.J.map τ).det := by
    have w := Classical.arbitrary (InfinitePlace F)
    exact isUnit_det_of_cartan X.J τ (B.emb w).1 1 one_ne_zero (X.θ w) (by rw [one_smul]; exact hP.herm.cartan w)
  have hXd := det_ne_zero_of_map τ hJX
  have hYd := det_ne_zero_of_map τ hJ
  have hA := GlobalTheory.T.theta_action_exists hK.base F E σ B n d X W Mo χX χW om r s r' s' hP v
  have h1X := GlobalTheory.SplitTransportPair.one_mem_UAt (σ := σ) X v
  have h1W := GlobalTheory.SplitTransportPair.one_mem_UAt (σ := σ) W v
  have pres : ∀ x, ∀ Φ ∈ schA F (Fin n × Fin d), om x Φ ∈ schA F (Fin n × Fin d) := fun x Φ hΦ =>
    (IsUWeilPair.isUSplitting hP.weil).pres x Φ hΦ
  let L₁ := liftU hcm τ X.J 1 hermX hJX
  let L₂ := (liftU hcm τ W.J (-1) herm hJ).comp (GlobalTheory.LocTypeGood.glReindex e)
  have hL₁ : ∀ g, L₁ g ∈ UAt σ X (evFin F v) := liftU_mem_UAt hcm τ X 1 hermX hJX
  have hL₂ : ∀ g, L₂ g ∈ UAt σ W (evFin F v) := fun g => liftU_mem_UAt hcm τ W (-1) herm hJ _
  have hL₁c : Continuous L₁ := GlobalTheory.SplitUnitLiftCont.continuous_liftU hcm τ X.J 1 hermX hJX
  have hL₂c : Continuous L₂ := (GlobalTheory.SplitUnitLiftCont.continuous_liftU hcm τ W.J (-1) herm hJ).comp (continuous_glReindex e)
  have hL₁t : ∀ g, (mat (L₁ g)).map (piW τ) = g.val := liftU_piW hcm τ X.J 1 hermX hJX
  have hL₁i : Function.Injective L₁ := fun g g' h => Units.ext (by rw [← hL₁t, h, hL₁t])
  have hL₂s : ∀ y ∈ UAt σ W (evFin F v), ∃ h, y = L₂ h := fun y hy =>
    ⟨GlobalTheory.LocTypeGood.glReindex e.symm (Matrix.GeneralLinearGroup.map (piW τ) y.1), by
      show y = liftU hcm τ W.J (-1) herm hJ (GlobalTheory.LocTypeGood.glReindex e _)
      rw [glReindex_surj]
      exact eq_liftU hcm τ W (-1) herm hJ y hy⟩
  let ρ : Representation ℂ (GL (Fin (x + x')) (Fv F v)) (UA σ W.J → ℂ) := (GlobalTheory.PRep.rightReg ℂ (UA σ W.J) ℂ).comp L₂
  have hπ : GlobalTheory.PRep.IsAdmissible (GlobalTheory.PRep.sub ρ (orb ρ f) (orb_stable ρ f)) :=
    isAdmissible_orb _ ρ (GlobalTheory.T.determinant_induced_isAdmissible (Fv F v) x x' χ₁ χ₂) f (by have h := hf 1; simp only [mul_one] at h; exact h)
  obtain ⟨b, hb, hbinv⟩ := exists_form hK hP hXd hYd f hfc hfl hfd μ 𝓕 hμ h𝓕 L₂
  obtain ⟨J, _, R, hR, hΦ'⟩ := exists_rests v hΦ
  let ω₁ : Representation ℂ (GL (Fin n) (Fv F v)) (schA F (Fin n × Fin d)) :=
    GlobalTheory.PRep.sub ((om.comp (MonoidHom.inl _ _)).comp L₁) _ fun g Ψ hΨ => pres (L₁ g, 1) Ψ hΨ
  let ω₂ : Representation ℂ (GL (Fin (x + x')) (Fv F v)) (schA F (Fin n × Fin d)) :=
    GlobalTheory.PRep.sub ((om.comp (MonoidHom.inr _ _)).comp L₂) _ fun g Ψ hΨ => pres (1, L₂ g) Ψ hΨ
  let ζ : Representation ℂ (GL (Fin n) (Fv F v)) (UA σ X.J → ℂ) := (GlobalTheory.PRep.rightReg ℂ (UA σ X.J) ℂ).comp L₁
  have hζ : ∀ g φ, ζ g φ = rt (L₁ g) φ := fun _ _ => rfl
  let D₀ : J → Submodule ℂ ((Fin n × Fin d → AF F) → ℂ) := fun j => (SB (Fin n × Fin d → Fv F v)).map (tensL v (R j))
  let D : J → Submodule ℂ (schA F (Fin n × Fin d)) := fun j => (D₀ j).comap (Submodule.subtype _)
  have hD₀ : ∀ j, ∀ g ∈ UAt σ X (evFin F v), ∀ y ∈ UAt σ W (evFin F v), ∀ Ψ ∈ D₀ j, om (g, y) Ψ ∈ D₀ j := by
    rintro j g hg y hy _ ⟨χ, hχ, rfl⟩
    obtain ⟨χ₁, h₁, ha⟩ := (hA.1 g hg y hy χ hχ).exists
    exact ⟨χ₁, h₁, (ha _ (hR j χ hχ)).symm⟩
  have hD₀S : ∀ j, D₀ j ≤ schA F (Fin n × Fin d) := by
    rintro j _ ⟨χ, hχ, rfl⟩
    exact (hR j χ hχ).2
  have eq1 : ∀ g u Ψ, ζ g (b u Ψ) = b u (ω₁ g Ψ) := fun g u Ψ => by
    rw [hb, hb, hζ]
    funext y
    have e : ∀ h, om (y, h) (om (L₁ g, 1) Ψ.1) = om (y * L₁ g, h) Ψ.1 := fun h => by
      rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
    show thLift om Ψ.1 μ 𝓕 u.1 (y * L₁ g) = thLift om (om (L₁ g, 1) Ψ.1) μ 𝓕 u.1 y
    simp only [thLift_def, theta, e]
  have eq2 : ∀ h u Ψ, b (GlobalTheory.PRep.sub ρ (orb ρ f) (orb_stable ρ f) h u) (ω₂ h Ψ) = b u Ψ := fun h u Ψ => by
    rw [hb, hb]
    exact hbinv u.1 u.2 Ψ.1 Ψ.2 (L₂ h)
  have sm1 : ∀ j, ∀ Ψ ∈ D j, IsOpen (stab ω₁ Ψ : Set (GL (Fin n) (Fv F v))) := by
    rintro j Ψ ⟨χ, hχ, hΨ⟩
    obtain ⟨U, hU, hU'⟩ := hA.2.2 χ hχ
    have hc : Continuous fun g => ((L₁ g, 1) : UA σ X.J × UA σ W.J) := hL₁c.prodMk continuous_const
    refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (mem_of_superset (hc.continuousAt.preimage_mem_nhds (t := U) ?_) ?_)
    · rw [map_one]; exact hU
    · intro g hg
      refine Subtype.ext (show om (L₁ g, 1) Ψ.1 = Ψ.1 from ?_)
      rw [← show tens (evFin F v) χ (R j) = Ψ.1 from hΨ]
      exact hU' _ hg (hL₁ g) h1W _ (hR j _ hχ)
  have sm2 : ∀ j, ∀ Ψ ∈ D j, IsOpen (stab ω₂ Ψ : Set (GL (Fin (x + x')) (Fv F v))) := by
    rintro j Ψ ⟨χ, hχ, hΨ⟩
    obtain ⟨U, hU, hU'⟩ := hA.2.2 χ hχ
    have hc : Continuous fun g => ((1, L₂ g) : UA σ X.J × UA σ W.J) := continuous_const.prodMk hL₂c
    refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (mem_of_superset (hc.continuousAt.preimage_mem_nhds (t := U) ?_) ?_)
    · rw [map_one]; exact hU
    · intro g hg
      refine Subtype.ext (show om (1, L₂ g) Ψ.1 = Ψ.1 from ?_)
      rw [← show tens (evFin F v) χ (R j) = Ψ.1 from hΨ]
      exact hU' _ hg h1X (hL₂ g) _ (hR j _ hχ)
  set S := Submodule.span ℂ {y | ∃ j u, ∃ Ψ ∈ D j, y = b u Ψ} with hS
  have hle : liftSpace om Φ μ 𝓕 f v ≤ S := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨_, ⟨k, hk, h, hh, Φ', hΦ₁, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩
    obtain ⟨y', rfl⟩ := hL₂s y hy
    let u : orb ρ f := ⟨rt (L₂ y') f, Submodule.subset_span ⟨y', rfl⟩⟩
    have key : ∀ Ψ ∈ ⨆ j, D₀ j, ∃ hΨ : Ψ ∈ schA F (Fin n × Fin d), b u ⟨om (k, h) Ψ, pres _ _ hΨ⟩ ∈ S := by
      intro Ψ hΨ
      induction hΨ using Submodule.iSup_induction' with
      | mem j Ψ hΨ => exact ⟨hD₀S j hΨ, Submodule.subset_span ⟨j, u, _, hD₀ j k hk h hh Ψ hΨ, rfl⟩⟩
      | zero =>
        refine ⟨zero_mem _, ?_⟩
        rw [show (⟨om (k, h) 0, pres _ _ (zero_mem _)⟩ : schA F (Fin n × Fin d)) = 0 from Subtype.ext (map_zero _), map_zero]
        exact zero_mem _
      | add Ψ Ψ' _ _ h1 h2 =>
        obtain ⟨m1, h1⟩ := h1
        obtain ⟨m2, h2⟩ := h2
        refine ⟨add_mem m1 m2, ?_⟩
        rw [show (⟨om (k, h) (Ψ + Ψ'), pres _ _ (add_mem m1 m2)⟩ : schA F (Fin n × Fin d)) =
          ⟨om (k, h) Ψ, pres _ _ m1⟩ + ⟨om (k, h) Ψ', pres _ _ m2⟩ from Subtype.ext (map_add _ _ _), map_add]
        exact add_mem h1 h2
    obtain ⟨m, hm⟩ := key Φ' (hΦ' Φ' hΦ₁)
    rw [hb] at hm
    exact hm
  have hKo : IsOpen (GlobalTheory.SplitWeil.KO (Fv F v) (Fin n) : Set (GL (Fin n) (Fv F v))) := GlobalTheory.SplitFlip.isOpen_KO
  have hKc : IsCompact (GlobalTheory.SplitWeil.KO (Fv F v) (Fin n) : Set (GL (Fin n) (Fv F v))) := GlobalTheory.SplitFlip.isCompact_KO
  refine ⟨{K' | ∃ K : Subgroup (GL (Fin n) (Fv F v)), IsOpen (K : Set (GL (Fin n) (Fv F v))) ∧
    IsCompact (K : Set (GL (Fin n) (Fv F v))) ∧ K' = K.map L₁}, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨K, -, -, rfl⟩ _ ⟨g, -, rfl⟩
    exact hL₁ g
  · rintro _ ⟨K, o, c, rfl⟩ _ ⟨K', o', c', rfl⟩
    rw [← Subgroup.map_inf _ _ _ hL₁i]
    refine ⟨⟨K ⊓ K', o.inter o', c.inter_right (K'.isClosed_of_isOpen o'), rfl⟩, ⟨?_⟩⟩
    have := Subgroup.relIndex_map_map_of_injective (K ⊓ K') K hL₁i
    rw [Subgroup.relIndex] at this
    rw [this]
    haveI := finite_quot (K' := K ⊓ K') c (o.inter o')
    exact Subgroup.index_ne_zero_of_finite
  · intro φ hφ
    have hsm : ∀ φ ∈ S, (stab ζ φ : Set (GL (Fin n) (Fv F v))) ∈ 𝓝 (1 : GL (Fin n) (Fv F v)) := by
      intro φ hφ
      induction hφ using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨j, u, Ψ, hΨ, rfl⟩ := hy
        refine mem_of_superset ((sm1 j Ψ hΨ).mem_nhds (one_mem _)) fun g hg => ?_
        show ζ g (b u Ψ) = b u Ψ
        rw [eq1, show ω₁ g Ψ = Ψ from hg]
      | zero => exact mem_of_superset univ_mem fun g _ => map_zero _
      | add y z _ _ hy hz =>
        refine mem_of_superset (inter_mem hy hz) fun g hg => ?_
        show ζ g (y + z) = y + z
        rw [map_add, show ζ g y = y from hg.1, show ζ g z = z from hg.2]
      | smul c y _ hy =>
        refine mem_of_superset hy fun g hg => ?_
        show ζ g (c • y) = c • y
        rw [map_smul, show ζ g y = y from hg]
    have ho := (stab ζ φ).isOpen_of_mem_nhds (hsm φ (hle hφ))
    refine ⟨_, ⟨stab ζ φ ⊓ GlobalTheory.SplitWeil.KO (Fv F v) (Fin n), ho.inter hKo,
      hKc.inter_left ((stab ζ φ).isClosed_of_isOpen ho), rfl⟩, ?_⟩
    rintro _ ⟨g, hg, rfl⟩
    exact hg.1
  · rintro _ ⟨K, o, c, rfl⟩
    obtain ⟨W₀, hW₀, hW⟩ := exists_finiteDimensional _ ω₁ ω₂ ζ b D hπ
      (fun j g Ψ hΨ => hD₀ j _ (hL₁ g) 1 h1W _ hΨ) eq1 eq2 sm1 sm2
      (GlobalTheory.SplitWeil.KO (Fv F v) (Fin (x + x'))) GlobalTheory.SplitFlip.isOpen_KO GlobalTheory.SplitFlip.isCompact_KO K c (fun j => by
        obtain ⟨A, hAf, hAS, hA'⟩ := fin_gen hK hP hXd hYd v τ L₁ hL₁c hL₁ hL₁t
          (fun h => ⟨_, liftU_mem_UAt hcm τ W (-1) herm hJ h, liftU_piW hcm τ W.J (-1) herm hJ h⟩) (R j) (hR j) K o
        haveI : Finite A := hAf
        refine ⟨Set.range fun a : A => ⟨tens (evFin F v) a.1 (R j), (hR j _ (hAS a.1 a.2)).2⟩, Set.finite_range _, ?_, ?_⟩
        · rintro _ ⟨a, rfl⟩
          exact ⟨a.1, hAS a.1 a.2, rfl⟩
        · rintro ⟨_, m⟩ ⟨χ, hχ, rfl⟩ hfix
          have h1 := hA' χ hχ fun k hk => congrArg Subtype.val (hfix k hk)
          rw [← Submodule.apply_mem_span_image_iff_mem_span (Submodule.injective_subtype _)]
          refine Submodule.span_mono ?_ h1
          rintro _ ⟨a, ha, y, hy, rfl⟩
          obtain ⟨h, rfl⟩ := hL₂s y hy
          exact ⟨_, ⟨_, ⟨⟨a, ha⟩, rfl⟩, h, rfl⟩, rfl⟩)
    exact Submodule.finiteDimensional_of_le (S₂ := W₀) fun φ hφ =>
      hW φ (hle hφ.1) fun k hk => hφ.2 _ ⟨k, hk, rfl⟩

end GlobalTheory.ThK.LiftAdm

end
