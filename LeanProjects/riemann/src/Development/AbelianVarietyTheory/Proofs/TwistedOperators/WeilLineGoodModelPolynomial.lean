import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionUnitaryCompact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchimedeanLineIntertwinesRealSchrodinger
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OneParameterOperatorUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPairingCoordinatesSchrodingerFolland
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticGroupMatrixOfPreservesPhaseSpace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzOneParameterGroupFormulaStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSymplecticLieEqExpOneParamStatement

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open GlobalTheory.ArchUniq MeasureTheory Filter Topology
open scoped SchwartzMap Classical Matrix

noncomputable section

namespace GlobalTheory.ArchLinePair

private theorem matrix_ext_of_mulVec_eq {l : Type} [Fintype l] [DecidableEq l] {A B : Matrix l l ℝ}
    (h : ∀ w, A *ᵥ w = B *ᵥ w) : A = B :=
  Matrix.toLin'.injective (LinearMap.ext fun w => by simp only [Matrix.toLin'_apply]; exact h w)

theorem tendsto_slope_of_pairing (hP : GlobalTheory.FunPr.Hypotheses₂) {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (P : V → V → ℝ) (hp : IsPairing P)
    (A : ℝ → (V × V) →ₗ[ℝ] (V × V)) (T : ℝ → 𝓢(V, ℂ) →ₗ[ℂ] 𝓢(V, ℂ))
    (hAc : ∀ v, Continuous fun t => A t v) (hA0 : ∀ v, A 0 v = v) (hAm : ∀ s t v, A (s + t) v = A s (A t v))
    (hAo : ∀ t v v', omega P (A t v) (A t v') = omega P v v')
    (hT0 : ∀ f, T 0 f = f) (hTm : ∀ s t f, T (s + t) f = T s (T t f))
    (hTi : ∀ t v (f f₁ : 𝓢(V, ℂ)), ⇑f₁ = schrF P v ⇑f → ⇑(T t f₁) = schrF P (A t v) ⇑(T t f))
    (hTu : ∀ μ : Measure V, μ.IsAddHaarMeasure → ∀ t f, ∫⁻ x, ‖T t f x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ)
    (hTc : ∀ f y, Continuous fun t => T t f y) (f : 𝓢(V, ℂ)) :
    ∃ g : 𝓢(V, ℂ), Tendsto (fun t : ℝ => t⁻¹ • (T t f - f)) (𝓝[≠] 0) (𝓝 g) := by
  obtain ⟨n, hn⟩ : ∃ n, Module.finrank ℝ V = n := ⟨_, rfl⟩
  obtain ⟨C, φ, hφs, hφρ⟩ := GlobalTheory.ArchUniq.exists_pairing_coords V P hp n hn
  have hφc : Continuous fun v => φ v := LinearMap.continuous_of_finiteDimensional φ.toLinearMap

  have hsym : ∀ t, ∃ Mt : Matrix.symplecticGroup (Fin n) ℝ,
      ∀ w, (Mt : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) *ᵥ w = φ (A t (φ.symm w)) := by
    intro t
    refine GlobalTheory.exists_symplecticGroup_of_sympl (Fin n) (φ.toLinearMap ∘ₗ A t ∘ₗ φ.symm.toLinearMap) fun w w' => ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hφs, hAo]
    rw [← hφs, φ.apply_symm_apply, φ.apply_symm_apply]
  choose Mt hMt using hsym
  have hg0 : (Mt 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) = 1 :=
    matrix_ext_of_mulVec_eq fun w => by rw [hMt, Matrix.one_mulVec, hA0, φ.apply_symm_apply]
  have hgm : ∀ s t, (Mt (s + t) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) =
      (Mt s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) * (Mt t : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) :=
    fun s t => matrix_ext_of_mulVec_eq fun w => by
      simp only [← Matrix.mulVec_mulVec, hMt, hAm, LinearEquiv.symm_apply_apply]
  have hgc : Continuous fun t => (Mt t : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) := by
    refine continuous_matrix fun i j => ?_
    have e : ∀ t, (Mt t : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) i j =
        φ (A t (φ.symm (Pi.single j 1))) i := fun t => by
      rw [← hMt t, Matrix.mulVec_single]
      simp
    simp only [e]
    exact (continuous_apply i).comp (hφc.comp (hAc _))
  obtain ⟨Z, hZ, hgZ⟩ := GlobalTheory.T.exists_symplecticLie_eq_exp_oneParam (Fin n) (fun t => (Mt t : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)) hgc hg0 hgm
    fun t => (Mt t).2

  obtain ⟨K, hK⟩ : ∃ K : 𝓢(EuclideanSpace ℝ (Fin n), ℂ) →L[ℂ] 𝓢(V, ℂ), ∀ h x, K h x = h (C x) :=
    ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ C, fun _ _ => rfl⟩
  obtain ⟨K', hK'⟩ : ∃ K' : 𝓢(V, ℂ) →L[ℂ] 𝓢(EuclideanSpace ℝ (Fin n), ℂ), ∀ h x, K' h x = h (C.symm x) :=
    ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ C.symm, fun _ _ => rfl⟩
  have hKK' : ∀ h, K (K' h) = h := fun h => SchwartzMap.ext fun x => by rw [hK, hK', C.symm_apply_apply]
  have hK'K : ∀ h, K' (K h) = h := fun h => SchwartzMap.ext fun x => by rw [hK', hK, C.apply_symm_apply]
  obtain ⟨T', hT'⟩ : ∃ T' : ℝ → GlobalTheory.RealWeil.Sch (Fin n) →ₗ[ℂ] GlobalTheory.RealWeil.Sch (Fin n),
      ∀ t h, T' t h = K' (T t (K h)) :=
    ⟨fun t => (K' : 𝓢(V, ℂ) →ₗ[ℂ] _) ∘ₗ T t ∘ₗ (K : _ →ₗ[ℂ] 𝓢(V, ℂ)), fun _ _ => rfl⟩
  have hT'0 : T' 0 = LinearMap.id := LinearMap.ext fun h => by rw [hT', hT0, hK'K, LinearMap.id_apply]
  have hT'm : ∀ s t, T' (s + t) = T' s ∘ₗ T' t := fun s t => LinearMap.ext fun h => by
    simp only [LinearMap.comp_apply, hT', hTm, hKK']
  have hT'i : ∀ (t : ℝ) (w : Fin n ⊕ Fin n → ℝ) (h h₁ : GlobalTheory.RealWeil.Sch (Fin n)),
      ⇑h₁ = GlobalTheory.RealWeil.rhoFun w ⇑h → ⇑(T' t h₁) = GlobalTheory.RealWeil.rhoFun (NormedSpace.exp (t • Z) *ᵥ w) ⇑(T' t h) := by
    intro t w h h₁ e
    have hg' : NormedSpace.exp (t • Z) = (Mt t : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) := (hgZ t).symm
    rw [hg', hMt]
    have e1 : ⇑(K h₁) = schrF P (φ.symm w) ⇑(K h) := by
      have e0 : ⇑(K h) = ⇑h ∘ C := funext (hK h)
      rw [e0, hφρ, φ.apply_symm_apply, ← e]
      exact funext (hK h₁)
    have e2 := hTi t _ _ _ e1
    funext x
    rw [hT', hK', e2, hT']
    have e3 : ⇑(T t (K h)) = ⇑(K' (T t (K h))) ∘ C :=
      funext fun y => by rw [Function.comp_apply, hK', C.symm_apply_apply]
    rw [e3, hφρ]
    simp only [Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply]
  have hT'u : ∀ (t : ℝ) (h : GlobalTheory.RealWeil.Sch (Fin n)), ∫⁻ x, ‖T' t h x‖ₑ ^ 2 = ∫⁻ x, ‖h x‖ₑ ^ 2 := by
    intro t h
    have hmeas : Measurable (C.symm : EuclideanSpace ℝ (Fin n) → V) := C.symm.continuous.measurable
    have key : ∀ u : 𝓢(V, ℂ), ∫⁻ x, ‖u (C.symm x)‖ₑ ^ 2 =
        ∫⁻ y, ‖u y‖ₑ ^ 2 ∂(Measure.map (C.symm : EuclideanSpace ℝ (Fin n) → V) volume) := fun u =>
      (lintegral_map (u.continuous.enorm.measurable.pow_const 2) hmeas).symm
    calc ∫⁻ x, ‖T' t h x‖ₑ ^ 2 = ∫⁻ x, ‖T t (K h) (C.symm x)‖ₑ ^ 2 := by simp only [hT', hK']
      _ = ∫⁻ y, ‖T t (K h) y‖ₑ ^ 2 ∂(Measure.map (C.symm : EuclideanSpace ℝ (Fin n) → V) volume) := key _
      _ = ∫⁻ y, ‖K h y‖ₑ ^ 2 ∂(Measure.map (C.symm : EuclideanSpace ℝ (Fin n) → V) volume) :=
        hTu _ inferInstance t (K h)
      _ = ∫⁻ x, ‖K h (C.symm x)‖ₑ ^ 2 := (key _).symm
      _ = ∫⁻ x, ‖h x‖ₑ ^ 2 := by simp only [hK, C.apply_symm_apply]
  have hT'c : ∀ (h : GlobalTheory.RealWeil.Sch (Fin n)) (x : EuclideanSpace ℝ (Fin n)), Continuous fun t => T' t h x :=
    fun h x => by simp only [hT', hK']; exact hTc _ _
  obtain ⟨a, ha⟩ := GlobalTheory.T.schwartz_one_parameter_group_formula hP (Fin n) Z hZ T' hT'0 hT'm hT'i hT'u hT'c
  refine ⟨K (a • K' f + GlobalTheory.RealWeil.quad Z (K' f)), ?_⟩
  have hlim := (K.continuous.tendsto _).comp (ha (K' f))
  refine Filter.Tendsto.congr (fun t => ?_) hlim
  ext x
  simp only [Function.comp_apply, hK, SchwartzMap.smul_apply, SchwartzMap.sub_apply, hT', hKK', hK',
    C.symm_apply_apply]

theorem acts_of_comm {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ)
    (T : Module.End ℂ ((κ → AF F) → ℂ)) (hpres : ∀ Φ ∈ schA F κ, T Φ ∈ schA F κ)
    (hcomm : ∀ u : AF F, evI F u = 0 → ∀ p q : κ → AF F, ∀ Φ ∈ schA F κ,
      T (schr ψ (u • p, u • q) Φ) = schr ψ (u • p, u • q) (T Φ)) (f : SInf F κ) :
    ∃ f₁ : SInf F κ, Acts (evI F) T f f₁ := by
  obtain ⟨r₀, hr₀1, hr₀⟩ := GlobalTheory.ArchLocality.ref_fun (F := F) κ
  have hΦ₀ : tens (evI F) (⇑f) r₀ ∈ schA F κ := (hr₀ f).2
  obtain ⟨f₁, hf₁⟩ := GlobalTheory.ArchLocality.res_arch _ (hpres _ hΦ₀)
  refine ⟨f₁, fun r hr => funext fun y => ?_⟩
  set u : AF F := (0, 1) with hu_def
  have hu : evI F u = 0 := GlobalTheory.ArchLocality.evI_fin
  have hmul : ∀ a : AF F, u * a = (0, a.2) := fun a => Prod.ext (zero_mul _) (one_mul _)
  set ya : κ → AF F := fun i => ((y i).1, 0) with hya
  have hy : ∀ i, y i = ya i + u * y i := fun i => by
    rw [hmul]
    exact Prod.ext (add_zero _).symm (zero_add _).symm

  have hτx : ∀ (Φ : (κ → AF F) → ℂ) x, schr ψ (u • y, u • (0 : κ → AF F)) Φ x = Φ (x + u • y) := fun Φ x => by
    simp only [schr, smul_zero, dotProduct_zero, mul_zero, add_zero, AddChar.map_zero_eq_one, one_mul]
  have step1 : T (tens (evI F) ⇑f r) y = T (schr ψ (u • y, u • (0 : κ → AF F)) (tens (evI F) ⇑f r)) ya := by
    have e : ya + u • y = y := funext fun i => (hy i).symm
    rw [hcomm u hu y 0 _ hr.2, hτx, e]
  have hmemτ : schr ψ (u • y, u • (0 : κ → AF F)) (tens (evI F) ⇑f r) ∈ schA F κ := by
    have e : schr ψ (u • y, u • (0 : κ → AF F)) (tens (evI F) ⇑f r) = fun x => tens (evI F) ⇑f r (x + u • y) :=
      funext fun x => hτx _ x
    rw [e]
    exact GlobalTheory.SchwartzTranslate.schA_translate F (u • y) hr.2
  have hΨ : schr ψ (u • y, u • (0 : κ → AF F)) (tens (evI F) ⇑f r) - r y • tens (evI F) ⇑f r₀ ∈ schA F κ :=
    Submodule.sub_mem _ hmemτ (Submodule.smul_mem _ _ hΦ₀)
  have hvan : ∀ z, At (evI F) z →
      (schr ψ (u • y, u • (0 : κ → AF F)) (tens (evI F) ⇑f r) - r y • tens (evI F) ⇑f r₀) (ya + z) = 0 := by
    intro z hz
    have hz2 : ∀ i, (z i).2 = 0 := GlobalTheory.ArchLocality.snd_eq_zero_of_at hz
    have e1 : ya + z + u • y = y + z := by
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      conv_rhs => rw [hy i]
      abel
    have e2 : (fun i => evI F ((ya + z) i)) = fun i => evI F ((y + z) i) := rfl
    have e3 : r₀ (ya + z) = 1 := hr₀1 _ fun i => by
      show (0 : FiniteAdeleRing (𝓞 F) F) + (z i).2 = 0
      rw [hz2 i, add_zero]
    rw [Pi.sub_apply, Pi.smul_apply, hτx, e1]
    simp only [tens]
    rw [hr.1 y z hz, e2, e3, smul_eq_mul]
    ring
  have hfib := GlobalTheory.ArchLocality.fibre ψ hψ T hcomm _ hΨ ya hvan
  rw [map_sub, map_smul, Pi.sub_apply, Pi.smul_apply, sub_eq_zero, smul_eq_mul] at hfib
  have hya' : ya = fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (evI F (y i)), 0) := by
    funext i
    simp only [hya, evI, RingEquiv.symm_apply_apply]
    rfl
  have hf₁' := hf₁ (fun i => evI F (y i))
  rw [step1, hfib, hya', hf₁']
  simp only [tens]
  ring

private theorem hTens_eq_trace_twisted_operators {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E) {α β : Type}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] (JA : Matrix α α E) (JB : Matrix β β E) (x y : Matrix α β E) :
    hTens c JA JB x y = Matrix.trace (xᵀ * (JA * y.map c * JBᵀ)) := by
  simp only [hTens, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

private theorem map_mul_lemma_2 {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E) {α β γ : Type}
    [Fintype β] (A : Matrix α β E) (B : Matrix β γ E) : (A * B).map c = A.map c * B.map c :=
  Matrix.map_mul (f := c.toRingHom)

theorem hTens_actAB {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E) {α β : Type} [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] {JA : Matrix α α E} {JB : Matrix β β E} (p : UG c JA × UG c JB)
    (x y : Matrix α β E) : hTens c JA JB (actAB c p x) (actAB c p y) = hTens c JA JB x y := by
  obtain ⟨⟨G, hG⟩, ⟨H, hH⟩⟩ := p
  have hG' : (G : Matrix α α E)ᵀ * JA * (G : Matrix α α E).map c = JA := hG
  have hH' : (H : Matrix β β E)ᵀ * JB * (H : Matrix β β E).map c = JB := hH
  have hG2 : ∀ N : Matrix α β E, (G : Matrix α α E)ᵀ * (JA * ((G : Matrix α α E).map c * N)) = JA * N :=
    fun N => by simpa only [Matrix.mul_assoc] using congrArg (· * N) hG'
  have hH2 : ((H : Matrix β β E).map c)ᵀ * (JBᵀ * (H : Matrix β β E)) = JBᵀ := by
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc] using congrArg Matrix.transpose hH'
  simp only [actAB, hTens_eq_trace_twisted_operators, map_mul_lemma_2, Matrix.transpose_map, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc, hG2, hH2]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

theorem actAB_smul (p : UA σ X.J × UA σ W.J) (u : AF F) (w : Matrix (Fin n) (Fin d) (AE F E)) :
    actAB (cA σ) p (u • w) = u • actAB (cA σ) p w := by
  simp only [actAB, Matrix.mul_smul, Matrix.smul_mul]

theorem actAB_add (p : UA σ X.J × UA σ W.J) (w w' : Matrix (Fin n) (Fin d) (AE F E)) :
    actAB (cA σ) p (w + w') = actAB (cA σ) p w + actAB (cA σ) p w' := by
  simp only [actAB, Matrix.mul_add, Matrix.add_mul]

theorem actAB_mul (p q : UA σ X.J × UA σ W.J) (w : Matrix (Fin n) (Fin d) (AE F E)) :
    actAB (cA σ) (p * q) w = actAB (cA σ) p (actAB (cA σ) q w) := by
  simp only [actAB, Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul, Units.val_mul, Matrix.transpose_mul, Matrix.mul_assoc]

theorem actAB_one (w : Matrix (Fin n) (Fin d) (AE F E)) : actAB (cA σ) (1 : UA σ X.J × UA σ W.J) w = w := by
  simp only [actAB, Prod.fst_one, Prod.snd_one, OneMemClass.coe_one, Units.val_one, Matrix.transpose_one, Matrix.one_mul,
    Matrix.mul_one]

theorem actAB_fin {p : UA σ X.J × UA σ W.J} (h1 : p.1 ∈ UAt σ X (evI F)) (h2 : p.2 ∈ UAt σ W (evI F)) (u : AF F)
    (hu : evI F u = 0) (w : Matrix (Fin n) (Fin d) (AE F E)) : actAB (cA σ) p (u • w) = u • w := by
  have e1 : u • mat p.1 = u • (1 : Matrix (Fin n) (Fin n) (AE F E)) := by
    have h := h1 u hu
    rwa [smul_sub, sub_eq_zero] at h
  have e2 : u • mat p.2 = u • (1 : Matrix (Fin d) (Fin d) (AE F E)) := by
    have h := h2 u hu
    rwa [smul_sub, sub_eq_zero] at h
  simp only [mat] at e1 e2
  simp only [actAB]
  rw [Matrix.mul_smul, ← Matrix.smul_mul, e1, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul, ← Matrix.mul_smul,
    ← Matrix.transpose_smul, e2, Matrix.transpose_smul, Matrix.transpose_one, Matrix.mul_smul, Matrix.mul_one]

def amap (M : Model σ X W) (p : UA σ X.J × UA σ W.J) :
    ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) →ₗ[ℝ]
      ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) where
  toFun v := Coord.coordI M (actAB (cA σ) p (GlobalTheory.ArchFam.wv M v))
  map_add' v v' := by
    simp only [GlobalTheory.ArchFam.wv, Prod.fst_add, Prod.snd_add, Coord.lift_add, ← Prod.mk_add_mk, map_add, actAB_add,
      Coord.coordI_add]
  map_smul' c v := by
    simp only [GlobalTheory.ArchFam.wv, Prod.smul_fst, Prod.smul_snd, Coord.lift_smul, ← Prod.smul_mk, map_smul, actAB_smul,
      Coord.coordI_smul, RingHom.id_apply]

theorem amap_coordI (M : Model σ X W) (p : UA σ X.J × UA σ W.J) (w : Matrix (Fin n) (Fin d) (AE F E)) :
    amap M p (Coord.coordI M w) = Coord.coordI M (actAB (cA σ) p w) := by
  simp only [amap, LinearMap.coe_mk, AddHom.coe_mk, GlobalTheory.ArchFam.wv]
  rw [Coord.lift_coordI, actAB_smul, Coord.coordI_one]

theorem continuous_amap (M : Model σ X W) (v) : Continuous fun p : UA σ X.J × UA σ W.J => amap M p v := by
  have : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) (AE F E)
  have : IsModuleTopology (AF F) (Matrix (Fin n) (Fin d) (AE F E)) :=
    (inferInstance : IsModuleTopology (AF F) (Fin n → Fin d → AE F E))
  have hev : Continuous (evI F) := by
    show Continuous fun a : AF F => InfiniteAdeleRing.ringEquiv_mixedSpace F a.1
    simp only [InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
    refine Continuous.prodMk (continuous_pi fun w => ?_) (continuous_pi fun w => ?_)
    · exact (NumberField.InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal w.2).continuous.comp
        ((continuous_apply _).comp continuous_fst)
    · exact (NumberField.InfinitePlace.Completion.isometry_extensionEmbedding w.1).continuous.comp
        ((continuous_apply _).comp continuous_fst)
  have hloc : Continuous fun x : Fin n × Fin d → AF F => locV x :=
    continuous_pi fun i => hev.comp (continuous_apply i)
  have he : Continuous fun u : Matrix (Fin n) (Fin d) (AE F E) => M.co.e u :=
    IsModuleTopology.continuous_of_linearMap M.co.e.toLinearMap
  have hg : Continuous fun p : UA σ X.J × UA σ W.J => ((p.1 : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) :=
    Units.continuous_val.comp (continuous_subtype_val.comp continuous_fst)
  have hh : Continuous fun p : UA σ X.J × UA σ W.J => ((p.2 : GL (Fin d) (AE F E)) : Matrix (Fin d) (Fin d) (AE F E)) :=
    Units.continuous_val.comp (continuous_subtype_val.comp continuous_snd)
  have hact : Continuous fun p : UA σ X.J × UA σ W.J => actAB (cA σ) p (GlobalTheory.ArchFam.wv M v) :=
    (hg.matrix_mul continuous_const).matrix_mul hh.matrix_transpose
  simp only [amap, LinearMap.coe_mk, AddHom.coe_mk, Coord.coordI]
  exact (hloc.comp (continuous_fst.comp (he.comp hact))).prodMk (hloc.comp (continuous_snd.comp (he.comp hact)))

theorem exists_orbit_pair (hP : GlobalTheory.FunPr.Hypotheses₂) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E)
    (om : Rep σ X W) (hψ : IsStd ψ) (hW : M.IsWeil ψ χX χW om) (δ : ℝ → UA σ X.J × UA σ W.J) (hδc : Continuous δ)
    (hδ0 : δ 0 = 1) (hδm : ∀ s t, δ (s + t) = δ s * δ t) (hδ1 : ∀ t, (δ t).1 ∈ UAt σ X (evI F))
    (hδ2 : ∀ t, (δ t).2 ∈ UAt σ W (evI F)) (f : SInf F (Fin n × Fin d)) :
    ∃ (c : ℝ → SInf F (Fin n × Fin d)) (g : SInf F (Fin n × Fin d)), c 0 = f ∧
      Tendsto (fun t : ℝ => t⁻¹ • (c t - f)) (𝓝[≠] 0) (𝓝 g) ∧ ∀ t, Acts (evI F) (om (δ t)) ⇑f ⇑(c t) := by
  have hS : IsUSplitting (adeleClass F) ψ M.co (actAB (cA σ)) om := IsUWeilPair.isUSplitting hW
  obtain ⟨r₀, hr₀1, hr₀⟩ := GlobalTheory.ArchLocality.ref_fun (F := F) (Fin n × Fin d)
  have hr₀0 : r₀ 0 ≠ 0 := by
    rw [hr₀1 0 fun i => rfl]
    exact one_ne_zero
  have hinj : ∀ φ₁ φ₂ : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ,
      tens (evI F) φ₁ r₀ = tens (evI F) φ₂ r₀ → φ₁ = φ₂ :=
    fun φ₁ φ₂ h => GlobalTheory.ArchFam.tens_inj r₀ (hr₀ 0).1 0 hr₀0 φ₁ φ₂ h
  have hpres : ∀ t, ∀ Φ ∈ schA F (Fin n × Fin d), om (δ t) Φ ∈ schA F (Fin n × Fin d) :=
    fun t Φ hΦ => hS.pres (δ t) Φ hΦ
  have hcomm : ∀ t (u : AF F), evI F u = 0 → ∀ p q : Fin n × Fin d → AF F, ∀ Φ ∈ schA F (Fin n × Fin d),
      om (δ t) (schr ψ (u • p, u • q) Φ) = schr ψ (u • p, u • q) (om (δ t) Φ) := by
    intro t u hu p q Φ hΦ
    have hw : M.co.e.symm (u • p, u • q) = u • M.co.e.symm (p, q) := by
      rw [← Prod.smul_mk, LinearEquiv.map_smul]
    have h := hS.impl (δ t) (M.co.e.symm (u • p, u • q)) Φ hΦ
    rw [hw, actAB_fin (hδ1 t) (hδ2 t) u hu] at h
    simpa only [Darboux.rho, LinearEquiv.map_smul, LinearEquiv.apply_symm_apply, Prod.smul_mk] using h
  have hex : ∀ t (g : SInf F (Fin n × Fin d)), ∃ g₁ : SInf F (Fin n × Fin d), Acts (evI F) (om (δ t)) g g₁ :=
    fun t g => acts_of_comm ψ hψ (om (δ t)) (hpres t) (hcomm t) g
  choose Tf hTf using hex
  have hK : ∀ t (g : SInf F (Fin n × Fin d)), om (δ t) (tens (evI F) ⇑g r₀) = tens (evI F) ⇑(Tf t g) r₀ :=
    fun t g => hTf t g r₀ (hr₀ g)
  have htl : ∀ (a : ℂ) (φ₁ φ₂ : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ),
      tens (evI F) (a • φ₁ + φ₂) r₀ = a • tens (evI F) φ₁ r₀ + tens (evI F) φ₂ r₀ := by
    intro a φ₁ φ₂
    funext x
    simp only [tens, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hlin : ∀ t (a : ℂ) (g h : SInf F (Fin n × Fin d)), Tf t (a • g + h) = a • Tf t g + Tf t h := by
    intro t a g h
    have e1 : (⇑(a • g + h) : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ) = a • ⇑g + ⇑h := rfl
    have h1 : tens (evI F) ⇑(Tf t (a • g + h)) r₀ = tens (evI F) (a • ⇑(Tf t g) + ⇑(Tf t h)) r₀ := by
      rw [← hK, e1, htl, map_add, map_smul, hK, hK, htl]
    have h2 := hinj _ _ h1
    exact SchwartzMap.ext fun x => congrFun h2 x
  have hz : ∀ t, Tf t 0 = 0 := fun t => by
    have h := hlin t 1 0 0
    simp only [smul_zero, add_zero, one_smul] at h
    calc Tf t 0 = Tf t 0 + Tf t 0 - Tf t 0 := (add_sub_cancel_right _ _).symm
      _ = 0 := by rw [← h, sub_self]
  obtain ⟨T, hT⟩ : ∃ T : ℝ → SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d), ∀ t g, T t g = Tf t g :=
    ⟨fun t => { toFun := Tf t
                map_add' := fun g h => by simpa only [one_smul] using hlin t 1 g h
                map_smul' := fun a g => by
                  simpa only [add_zero, hz, RingHom.id_apply] using hlin t a g 0 }, fun _ _ => rfl⟩
  have hTf0 : ∀ g, Tf 0 g = g := fun g => by
    have h1 : tens (evI F) ⇑(Tf 0 g) r₀ = tens (evI F) ⇑g r₀ := by
      rw [← hK, hδ0, map_one]
      rfl
    exact SchwartzMap.ext fun x => congrFun (hinj _ _ h1) x
  suffices H : ∃ g, Tendsto (fun t : ℝ => t⁻¹ • (T t f - f)) (𝓝[≠] 0) (𝓝 g) by
    obtain ⟨g, hg⟩ := H
    refine ⟨fun t => T t f, g, by simp only [hT, hTf0], hg, fun t => ?_⟩
    simp only [hT]
    exact hTf t f
  have hB : BorelSpace (Fin n × Fin d → mixedEmbedding.mixedSpace F) := Pi.borelSpace
  refine tendsto_slope_of_pairing hP _ (Coord.isPairing_trP (F := F) (Fin n × Fin d)) (fun t => amap M (δ t)) T
    (fun v => (continuous_amap M v).comp hδc) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ f
  · intro v
    show Coord.coordI M (actAB (cA σ) (δ 0) (GlobalTheory.ArchFam.wv M v)) = v
    rw [hδ0, actAB_one, GlobalTheory.ArchFam.wv, Coord.coordI_lift]
  · intro s t v
    show Coord.coordI M (actAB (cA σ) (δ (s + t)) (GlobalTheory.ArchFam.wv M v)) =
      amap M (δ s) (Coord.coordI M (actAB (cA σ) (δ t) (GlobalTheory.ArchFam.wv M v)))
    rw [amap_coordI, hδm, actAB_mul]
  · intro t v v'
    show omega _ (Coord.coordI M (actAB (cA σ) (δ t) (GlobalTheory.ArchFam.wv M v)))
      (Coord.coordI M (actAB (cA σ) (δ t) (GlobalTheory.ArchFam.wv M v'))) = omega _ v v'
    conv_rhs => rw [← Coord.coordI_lift M v, ← Coord.coordI_lift M v']
    rw [Coord.omega_coordI, Coord.omega_coordI]
    simp only [Coord.sympM, symp, hTens_actAB, GlobalTheory.ArchFam.wv]
  · intro g
    rw [hT, hTf0]
  · intro s t g
    simp only [hT]
    have h1 : tens (evI F) ⇑(Tf (s + t) g) r₀ = tens (evI F) ⇑(Tf s (Tf t g)) r₀ := by
      rw [← hK, hδm, map_mul, Module.End.mul_apply, hK, hK]
    exact SchwartzMap.ext fun x => congrFun (hinj _ _ h1) x
  · intro t v g g₁ e
    simp only [hT]
    have hw := GlobalTheory.ArchFam.at_wv M v
    have hco : (locV (M.co.e (GlobalTheory.ArchFam.wv M v)).1, locV (M.co.e (GlobalTheory.ArchFam.wv M v)).2) = v :=
      Coord.coordI_lift M v
    have e1 : tens (evI F) ⇑g₁ r₀ = M.co.rho ψ (GlobalTheory.ArchFam.wv M v) (tens (evI F) ⇑g r₀) := by
      rw [GlobalTheory.ArchFam.rho_tens ψ hψ M.co _ hw _ _ (hr₀ g).1, hco, e]
    have hat : At (evI F) (actAB (cA σ) (δ t) (GlobalTheory.ArchFam.wv M v)) := fun u hu => by
      rw [← actAB_smul, hw u hu]
      simp only [actAB, Matrix.mul_zero, Matrix.zero_mul]
    have e2 : tens (evI F) ⇑(Tf t g₁) r₀ =
        tens (evI F) (schrF (trP F (Fin n × Fin d)) (amap M (δ t) v) ⇑(Tf t g)) r₀ := by
      rw [← hK, e1, hS.impl (δ t) _ _ (hr₀ g).2, hK, GlobalTheory.ArchFam.rho_tens ψ hψ M.co _ hat _ _ (hr₀ g).1]
      rfl
    exact hinj _ _ e2
  · intro μ hμ t g
    simp only [hT]
    have hg : GlobalTheory.ArchLocality.intInd (F := F) (Fin n × Fin d) ∈ SB (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F) :=
      GlobalTheory.ArchLocality.intInd_mem _
    have hmem0 : (0 : Fin n × Fin d → FiniteAdeleRing (𝓞 F) F) ∈
        Set.pi Set.univ fun _ : Fin n × Fin d =>
          (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (FiniteAdeleRing (𝓞 F) F)) :=
      fun i _ => zero_mem (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F)
    have hg0 : GlobalTheory.ArchLocality.intInd (F := F) (Fin n × Fin d) 0 ≠ 0 := by
      simp only [GlobalTheory.ArchLocality.intInd]
      rw [Set.indicator_of_mem hmem0]
      exact one_ne_zero
    obtain ⟨μA, hμA, c, hc0, hctop, hc⟩ := GlobalTheory.ArchimedeanUnitaryL2.exists_haar F (Fin n × Fin d) μ _ hg hg0
    have hR : ∀ φ : SInf F (Fin n × Fin d),
        Rest (evI F) ⇑φ (fun x => GlobalTheory.ArchLocality.intInd (F := F) (Fin n × Fin d) fun i => (x i).2) :=
      fun φ => ⟨fun x z hz => by
          have e : (fun i => ((x + z) i).2) = fun i => (x i).2 := funext fun i => by
            show (x i).2 + (z i).2 = (x i).2
            rw [GlobalTheory.ArchLocality.snd_eq_zero_of_at hz i, add_zero]
          show GlobalTheory.ArchLocality.intInd (F := F) (Fin n × Fin d) (fun i => ((x + z) i).2) =
            GlobalTheory.ArchLocality.intInd (F := F) (Fin n × Fin d) (fun i => (x i).2)
          rw [e],
        Submodule.subset_span ⟨φ, _, hg, rfl⟩⟩
    have h1 := hS.unit μA hμA (δ t) _ (hR g).2
    rw [hTf t g _ (hR g)] at h1
    have h2 : ∀ φ : SInf F (Fin n × Fin d),
        tens (evI F) ⇑φ (fun x => GlobalTheory.ArchLocality.intInd (F := F) (Fin n × Fin d) fun i => (x i).2) =
          pureA F ⇑φ (GlobalTheory.ArchLocality.intInd (F := F) (Fin n × Fin d)) := fun φ => rfl
    rw [h2, h2, hc, hc] at h1
    exact (ENNReal.mul_right_inj hc0 hctop).1 h1
  · intro g y
    simp only [hT]
    have hy' : (fun i => evI F (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y i), 0) : AF F)) = y :=
      funext fun i => by simp only [evI, RingEquiv.apply_symm_apply]
    have hr1 : r₀ (fun i => (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y i), 0) : AF F)) = 1 :=
      hr₀1 _ fun i => rfl
    have hl : (LinearMap.proj (R := ℂ) (φ := fun _ : Fin n × Fin d → AF F => ℂ)
        (fun i => (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y i), 0) : AF F))) ∈
          (adeleClass F).adm (Fin n × Fin d) := fun q _ =>
      ⟨q (fun i => ((((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y i), 0) : AF F)).2) •
          (BoundedContinuousFunction.evalCLM ℂ y).comp (SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ ℂ),
        fun φ => by
          show φ (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F
              ((((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y i), 0) : AF F)).1) *
              q (fun i => ((((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y i), 0) : AF F)).2) =
            q (fun i => ((((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y i), 0) : AF F)).2) * φ y
          rw [show (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F
              ((((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y i), 0) : AF F)).1) = y from hy', mul_comm]⟩
    refine ((hS.cont _ hl _ (hr₀ g).2).comp hδc).congr fun t => ?_
    show (om (δ t) (tens (evI F) ⇑g r₀))
        (fun i => (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y i), 0) : AF F)) = Tf t g y
    rw [hK]
    show Tf t g (fun i => evI F (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y i), 0) : AF F)) *
        r₀ (fun i => (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y i), 0) : AF F)) = Tf t g y
    rw [hy', hr1, mul_one]

theorem exists_curve_lineY : GlobalTheory.FunPr.Hypotheses₂ → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd) (ψ : AddChar (AF F) ℂ)
    (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Y Wd),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → M.IsGood ψ → M.IsWeil ψ χX χW om →
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ Y, ∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) (r : (Fin n × Fin d → AF F) → ℂ),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) f r →
    ∃ (c : ℝ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) (g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)),
      (∀ t : ℝ, om (γ (Multiplicative.ofAdd t), 1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) f r) =
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (c t) r) ∧
      Tendsto (fun t : ℝ => t⁻¹ • (c t - c 0)) (𝓝[≠] 0) (𝓝 g) := by
  intro hP F E _ _ _ _ _ σ n d Y Wd M ψ χX χW om hψ _ hW γ hγ f r hr
  obtain ⟨c, g, hc0, hlim, hact⟩ := exists_orbit_pair hP M ψ χX χW om hψ hW
    (fun t => (γ (Multiplicative.ofAdd t), 1)) ((hγ.1.comp continuous_ofAdd).prodMk continuous_const)
    (Prod.ext (by simp only [ofAdd_zero, map_one, Prod.fst_one]) rfl)
    (fun s t => Prod.ext (by simp only [ofAdd_add, map_mul, Prod.fst_mul]) (one_mul 1).symm)
    (fun t => hγ.2 _)
    (fun _ u _ => by simp only [mat, OneMemClass.coe_one, Units.val_one, sub_self, smul_zero]) f
  refine ⟨c, g, fun t => hact t r hr, ?_⟩
  rw [hc0]
  exact hlim

end GlobalTheory.ArchLinePair
