import Development.WeilBound.ThetaLifts.FrameEstimates.TowerRallisLemma
import Development.WeilBound.ThetaLifts.FrameEstimates.LinDerA
import Development.AutomorphicSpectrum.Proofs.TwistedProofs.ExtensionEmbeddingEvInfRealAd
import Development.AutomorphicSpectrum.Proofs.TwistedProofs.EqZeroOfPiInf
import Development.AutomorphicSpectrum.Proofs.TwistedProofs.ExistsAdelePiInf

noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace LinDerPf

section Cx

variable {ι : Type} [Fintype ι] {d : ℕ}

def adj (J : ι → Matrix (Fin d) (Fin d) ℂ) : (ι → Matrix (Fin d) (Fin d) ℂ) →ₗ[ℝ] (ι → Matrix (Fin d) (Fin d) ℂ) where
  toFun x w := ((J w)⁻¹ * (x w)ᵀ * J w).map star
  map_add' x y := by
    funext w
    ext i j
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.transpose_add, Pi.add_apply, Matrix.map_apply, Matrix.add_apply,
      star_add]
  map_smul' r x := by
    funext w
    ext i j
    simp only [Matrix.transpose_smul, Pi.smul_apply, Matrix.mul_smul, Matrix.smul_mul, Matrix.map_apply,
      Matrix.smul_apply, star_smul, RingHom.id_apply, star_trivial]

omit [Fintype ι] in
theorem adj_iff {J : ι → Matrix (Fin d) (Fin d) ℂ} (hJ : ∀ w, IsUnit (J w).det) (Y : ι → Matrix (Fin d) (Fin d) ℂ) :
    adj J Y = -Y ↔ ∀ w, (Y w)ᵀ * J w + J w * (Y w).map star = 0 := by
  rw [funext_iff]
  refine forall_congr' fun w => ?_
  change ((J w)⁻¹ * (Y w)ᵀ * J w).map star = -Y w ↔ _
  have e : ((J w)⁻¹ * (Y w)ᵀ * J w).map star = -Y w ↔ (J w)⁻¹ * (Y w)ᵀ * J w = -(Y w).map star := by
    simp only [← Matrix.ext_iff, Matrix.map_apply, Matrix.neg_apply]
    refine forall_congr' fun i => forall_congr' fun j => ?_
    rw [star_eq_iff_star_eq, star_neg, eq_comm]
  rw [e, add_eq_zero_iff_eq_neg, ← Matrix.mul_neg]
  constructor
  · intro h
    rw [← h, Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ (hJ w)]
  · intro h
    rw [Matrix.mul_assoc, h, Matrix.nonsing_inv_mul_cancel_left _ _ (hJ w)]

set_option backward.isDefEq.respectTransparency false in
open scoped Matrix.Norms.Operator in
theorem mainM {J : ι → Matrix (Fin d) (Fin d) ℂ} (hJ : ∀ w, IsUnit (J w).det) :
    ∃ (m : ℕ) (Y : Fin m → ι → Matrix (Fin d) (Fin d) ℂ) (c : Fin m → (ι → Matrix (Fin d) (Fin d) ℂ) →ₗ[ℝ] ℝ),
      (∀ i w, (Y i w)ᵀ * J w + J w * (Y i w).map star = 0) ∧ ∀ Z Z' : ι → Matrix (Fin d) (Fin d) ℂ,
      (∀ w, (Z' w)ᵀ * J w + J w * (Z' w).map star = 0) →
      (∀ w (t : ℝ), NormedSpace.exp ((t : ℂ) • Z w) = NormedSpace.exp ((t : ℂ) • Z' w)) →
      ∃ s : Fin m → ℝ → ℝ, (∀ i, s i 0 = 0) ∧ (∀ i, HasDerivAt (s i) (c i Z) 0) ∧
        ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), ∀ w, NormedSpace.exp ((t : ℂ) • Z w) =
          (List.ofFn fun i => NormedSpace.exp ((s i t : ℂ) • Y i w)).prod := by
  let a : (ι → Matrix (Fin d) (Fin d) ℂ) →L[ℝ] (ι → Matrix (Fin d) (Fin d) ℂ) := LinearMap.toContinuousLinearMap (adj J)
  have ha : ∀ x y, a (x * y) = a y * a x := fun x y => by
    funext w
    change ((J w)⁻¹ * (x w * y w)ᵀ * J w).map (starRingEnd ℂ) =
      ((J w)⁻¹ * (y w)ᵀ * J w).map (starRingEnd ℂ) * ((J w)⁻¹ * (x w)ᵀ * J w).map (starRingEnd ℂ)
    rw [← Matrix.map_mul, Matrix.transpose_mul]
    congr 1
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ (hJ w)]
  have h1 : a 1 = 1 := by
    funext w
    change ((J w)⁻¹ * (1 : Matrix (Fin d) (Fin d) ℂ)ᵀ * J w).map (starRingEnd ℂ) = 1
    rw [Matrix.transpose_one, Matrix.mul_one, Matrix.nonsing_inv_mul _ (hJ w), Matrix.map_one _ (map_zero _) (map_one _)]
  have hx : ∀ (t : ℝ) (x : ι → Matrix (Fin d) (Fin d) ℂ) w,
      NormedSpace.exp (t • x) w = NormedSpace.exp ((t : ℂ) • x w) := fun t x w => by
    rw [Pi.coe_exp, Pi.smul_apply, Complex.coe_smul]
  obtain ⟨m, Y, c, hY, h⟩ := main (a := a) ha h1
  refine ⟨m, Y, c, fun i => (adj_iff hJ _).1 (hY i), fun Z Z' hZ e => ?_⟩
  obtain ⟨s, s0, sd, se⟩ := h Z fun t => by
    have e' : NormedSpace.exp (t • Z) = NormedSpace.exp (t • Z') := funext fun w => by rw [hx, hx, e]
    rw [e']
    refine gr_exp ha h1 ?_
    rw [map_smul, ← smul_neg]
    exact congrArg _ ((adj_iff hJ _).2 hZ)
  refine ⟨s, s0, sd, se.mono fun t ht w => ?_⟩
  rw [← hx, ht, Pi.list_prod_apply, List.map_ofFn]
  congr 2
  funext i
  exact hx _ _ _

end Cx

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {d : ℕ}

omit [NumberField E] in
theorem uat_prod {W : Spc F E d} (l : List (UA σ W.J)) (hl : ∀ g ∈ l, g ∈ UAt σ W (evI F)) :
    l.prod ∈ UAt σ W (evI F) := by
  induction l with
  | nil =>
    intro c _
    change c • ((1 : Matrix (Fin d) (Fin d) (AE F E)) - 1) = 0
    rw [sub_self, smul_zero]
  | cons x l ih =>
    intro c hc
    have h1 := hl x (by simp) c hc
    have h2 := ih (fun g hg => hl g (by simp [hg])) c hc
    rw [List.prod_cons]
    change c • (mat x * mat l.prod - 1) = 0
    have e : mat x * mat l.prod - 1 = mat x * (mat l.prod - 1) + (mat x - 1) := by
      rw [Matrix.mul_sub, Matrix.mul_one, sub_add_sub_cancel]
    rw [e, smul_add, ← Matrix.mul_smul, h1, h2, Matrix.mul_zero, add_zero]

omit [NumberField E] in
theorem mat_prod {J : Matrix (Fin d) (Fin d) E} (p : AE F E →+* ℂ) (l : List (UA σ J)) :
    (mat l.prod).map p = (l.map fun g => (mat g).map p).prod := by
  induction l with
  | nil => exact Matrix.map_one _ (map_zero _) (map_one _)
  | cons x l ih =>
    rw [List.prod_cons, List.map_cons, List.prod_cons, ← ih, ← Matrix.map_mul]
    rfl

theorem uat_ext (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) {W : Spc F E d} {u v : UA σ W.J}
    (hu : u ∈ UAt σ W (evI F)) (hv : v ∈ UAt σ W (evI F))
    (e : ∀ w, (mat u).map (piInf (τ w)) = (mat v).map (piInf (τ w))) : u = v := by
  refine Subtype.ext (Units.ext ?_)
  change mat u = mat v
  ext i j
  refine sub_eq_zero.1 (GlobalTheory.CompanionTheory.CMAdele.eq_zero_of_piInf σ h τ _ (fun c hc => ?_) fun w => ?_)
  · have e1 : c • (mat u - mat v) = 0 := by
      rw [← sub_sub_sub_cancel_right _ _ 1, smul_sub, hu c hc, hv c hc, sub_zero]
    exact congrFun (congrFun e1 i) j
  · rw [map_sub]
    exact sub_eq_zero.2 (congrFun (congrFun (e w) i) j)

end LinDerPf

open LinDerPf in
theorem linDer_of (hG : LineGen) (hX : LineEx) : LinDer := by
  intro F E _ _ _ _ _ σ h τ d W hW
  have hJ : ∀ w, IsUnit (W.J.map (τ w).1).det := fun w => by
    have e : (W.J.map (τ w).1).det = (τ w).1 W.J.det := (RingHom.map_det (τ w).1 W.J).symm
    rw [e]
    exact ((map_ne_zero (τ w).1).2 hW.2).isUnit
  have : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have : IsTopologicalGroup (GL (Fin d) (AE F E)) := inferInstance
  have : IsTopologicalGroup (UA σ W.J) := inferInstance
  obtain ⟨m, Y, c, hY, hm⟩ := mainM hJ
  choose β hβ hβY _ using fun i => hX F E σ h τ d W hW (Y i) (hY i)
  refine ⟨m, β, c, hβ, fun f f' hf γ hγ Z hZ g => ?_⟩
  obtain ⟨Z', hZ', hZZ⟩ := hG F E σ h τ d W hW γ hγ
  obtain ⟨s, s0, sd, se⟩ := hm Z Z' hZ' fun w t => (hZ w t).symm.trans (hZZ w t)
  have h1 := chain f m β (fun i => (hβ i).1) f' (fun i => (hf i).1) (fun i => (hf i).2) (fun _ => g)
    continuousAt_const s (fun i => c i Z) sd s0 0 (hasDerivAt_const _ _)
  rw [zero_add] at h1
  refine h1.congr_of_eventuallyEq (se.mono fun t ht => ?_)
  have e : γ (Multiplicative.ofAdd t) = (List.ofFn fun i => β i (Multiplicative.ofAdd (s i t))).prod := by
    refine uat_ext h τ (hγ.2 _) (uat_prod _ fun x hx => ?_) fun w => ?_
    · obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hx
      exact (hβ i).2 _
    · rw [hZ w t, ht w, mat_prod, List.map_ofFn]
      congr 2
      funext i
      exact (hβY i w _).symm
  simp only [e]

end PositivityTheory.ThKEst

end
