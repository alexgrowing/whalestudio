import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.LAbove
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.ContinuousEntryCharacters.PiLaws
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.ContinuousEntryCharacters.KillsIrreducible
import GroundTheory.AutomorphicForms.MultiplicityOne.GL2ProductCompleteness.EqSmulOfMemWindowOrbitClosure

open MeasureTheory NumberField Filter Topology Matrix
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.ArchWhittakerC UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA
open scoped ComplexConjugate Classical InnerProductSpace

namespace UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA.RI

section Avg

variable {A : Type*} [Group A] [TopologicalSpace A] [IsTopologicalGroup A] [CompactSpace A]
  [SecondCountableTopology A] [MeasurableSpace A] [BorelSpace A]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem int_left {κ : Measure A} (hl : ∀ k, MeasurePreserving (k * ·) κ κ)
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (k : A) (F : A → X) :
    ∫ x, F (k * x) ∂κ = ∫ x, F x ∂κ :=
  (hl k).integral_comp (MeasurableEquiv.mulLeft k).measurableEmbedding F

private theorem int_inv {κ : Measure A} [IsProbabilityMeasure κ]
    (hl : ∀ k, MeasurePreserving (k * ·) κ κ) {F : A → ℂ} (hF : Continuous F) :
    ∫ x, F x⁻¹ ∂κ = ∫ x, F x ∂κ := by
  have hc : Continuous (Function.uncurry fun k h : A => F (k⁻¹ * h)) :=
    hF.comp ((continuous_fst.inv).mul continuous_snd)
  have hi : Integrable (Function.uncurry fun k h : A => F (k⁻¹ * h)) (κ.prod κ) :=
    hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h1 : ∫ k, ∫ h, F (k⁻¹ * h) ∂κ ∂κ = ∫ x, F x ∂κ := by
    simp_rw [int_left hl _ F]
    simp
  have h2 : ∫ h, ∫ k, F (k⁻¹ * h) ∂κ ∂κ = ∫ x, F x⁻¹ ∂κ := by
    have : ∀ h, ∫ k, F (k⁻¹ * h) ∂κ = ∫ x, F x⁻¹ ∂κ := fun h => by
      rw [← int_left hl h (fun k => F (k⁻¹ * h))]
      simp [_root_.mul_inv_rev, mul_assoc]
    simp [this]
  rw [← h2, ← h1, integral_integral_swap hi]

private noncomputable def avg (κ : Measure A) (π : UnitaryRep A H) (e : A → ℂ) (v : H) : H :=
  ∫ k, e k • π k v ∂κ

variable {κ : Measure A} [IsProbabilityMeasure κ] {π : UnitaryRep A H} {e : A → ℂ}

private theorem avg_int (he : Continuous e) (v : H) : Integrable (fun k => e k • π k v) κ :=
  (he.smul (π.continuous_orbit v)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

private theorem avg_inner (hl : ∀ k, MeasurePreserving (k * ·) κ κ) (he : Continuous e)
    (hs : ∀ k, e k⁻¹ = conj (e k)) (u v : H) :
    ⟪u, avg κ π e v⟫_ℂ = ⟪avg κ π e u, v⟫_ℂ := by
  have h1 : ⟪u, avg κ π e v⟫_ℂ = ∫ k, e k * ⟪u, π k v⟫_ℂ ∂κ := by
    unfold avg
    rw [← integral_inner (avg_int he v)]
    simp only [inner_smul_right]
  have h2 : ⟪avg κ π e u, v⟫_ℂ = ∫ k, e k⁻¹ * ⟪u, π k⁻¹ v⟫_ℂ ∂κ := by
    rw [← inner_conj_symm]
    unfold avg
    rw [← integral_inner (avg_int he u), ← integral_conj]
    refine integral_congr_ae (Eventually.of_forall fun k => ?_)
    simp only [inner_smul_right, map_mul, inner_conj_symm, hs, UnitaryRep.inner_map_left]
  rw [h1, h2]
  refine (int_inv hl (F := fun k => e k * ⟪u, π k v⟫_ℂ) ?_).symm
  exact he.mul (continuous_const.inner (π.continuous_orbit v))

private theorem avg_avg (hl : ∀ k, MeasurePreserving (k * ·) κ κ) (he : Continuous e)
    (hi : ∀ k, ∫ h, e h * e (h⁻¹ * k) ∂κ = e k) (v : H) :
    avg κ π e (avg κ π e v) = avg κ π e v := by
  have step : ∀ h, e h • π h (avg κ π e v) = ∫ k, (e h * e (h⁻¹ * k)) • π k v ∂κ := by
    intro h
    have e1 : π h (avg κ π e v) = ∫ k, e k • π h (π k v) ∂κ := by
      unfold avg
      rw [← ContinuousLinearMap.integral_comp_comm _ (avg_int he v)]
      simp only [map_smul]
    rw [e1, ← integral_smul, ← int_left hl h⁻¹ (fun k => e h • e k • π h (π k v))]
    refine integral_congr_ae (Eventually.of_forall fun k => ?_)
    simp only [smul_smul, ← UnitaryRep.map_mul_apply, mul_inv_cancel_left]
  have hc : Continuous (Function.uncurry fun h k : A => (e h * e (h⁻¹ * k)) • π k v) := by
    refine Continuous.smul ((he.comp continuous_fst).mul (he.comp ((continuous_fst.inv).mul continuous_snd))) ?_
    exact (π.continuous_orbit v).comp continuous_snd
  have hI : Integrable (Function.uncurry fun h k : A => (e h * e (h⁻¹ * k)) • π k v) (κ.prod κ) :=
    hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  show ∫ h, e h • π h (avg κ π e v) ∂κ = ∫ k, e k • π k v ∂κ
  simp_rw [step]
  rw [integral_integral_swap hI]
  refine integral_congr_ae (Eventually.of_forall fun k => ?_)
  show ∫ h, (e h * e (h⁻¹ * k)) • π k v ∂κ = e k • π k v
  rw [integral_smul_const, hi]

end Avg

section Window

variable {G : Type*} [Group G] [TopologicalSpace G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem compress_scalar (R : UnitaryRep G H) (τ : Submodule ℂ H) (hcl : IsClosed (τ : Set H))
    (hinv : ∀ g, ∀ v ∈ τ, R g v ∈ τ)
    (hirr : ∀ ρ : Submodule ℂ H, ρ ≤ τ → IsClosed (ρ : Set H) → (∀ g, ∀ v ∈ ρ, R g v ∈ ρ) → ρ = ⊥ ∨ ρ = τ)
    (P : H →L[ℂ] H) (hPs : IsSelfAdjoint P) (hPP : P ∘L P = P) (hPτ : ∀ v ∈ τ, P v ∈ τ) (a : G)
    (hc : ∀ g, Commute (P ∘L R a ∘L P) (P ∘L R g ∘L P))
    (hc' : ∀ g, Commute (P ∘L R a⁻¹ ∘L P) (P ∘L R g ∘L P)) :
    ∃ c : ℂ, ∀ v ∈ τ, P v = v → P (R a v) = c • v := by
  have hsym : ∀ x y, ⟪P x, y⟫_ℂ = ⟪x, P y⟫_ℂ :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.1 hPs
  have hP2 : ∀ y, P (P y) = P y := fun y => DFunLike.congr_fun hPP y
  set D : Submodule ℂ H := τ ⊓ LinearMap.ker (((1 : H →L[ℂ] H) - P : H →L[ℂ] H) : H →ₗ[ℂ] H) with hD
  have memD : ∀ {x}, x ∈ D ↔ x ∈ τ ∧ P x = x := by
    intro x
    simp only [hD, Submodule.mem_inf, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, sub_eq_zero]
    exact and_congr_right fun _ => eq_comm
  have hDcl : IsClosed (D : Set H) := by
    have : (D : Set H) = (τ : Set H) ∩ {x | P x = x} := by
      ext x
      exact memD
    rw [this]
    exact hcl.inter (isClosed_eq P.continuous continuous_id)
  have : CompleteSpace D := hDcl.completeSpace_coe
  by_cases hbot : D = ⊥
  · refine ⟨0, fun v hv hPv => ?_⟩
    have : v ∈ D := memD.2 ⟨hv, hPv⟩
    rw [hbot, Submodule.mem_bot] at this
    simp [this]
  have hnt : Nontrivial D := by
    obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff D).1 hbot
    exact ⟨⟨⟨x, hx⟩, 0, fun h => hx0 (congrArg Subtype.val h)⟩⟩
  have hmem : ∀ g (x : D), (P ∘L (R g ∘L D.subtypeL)) x ∈ D := fun g x =>
    memD.2 ⟨hPτ _ (hinv g _ (memD.1 x.2).1), hP2 _⟩
  let cp : G → (D →L[ℂ] D) := fun g => (P ∘L (R g ∘L D.subtypeL)).codRestrict D (hmem g)
  have cp_coe : ∀ g (x : D), ((cp g x : D) : H) = P (R g x) := fun _ _ => rfl
  have cp_inner : ∀ g (x y : D), ⟪(y : H), P (R g x)⟫_ℂ = ⟪(y : H), R g x⟫_ℂ := by
    intro g x y
    rw [← hsym, (memD.1 y.2).2]
  have cp_star : ∀ g, star (cp g) = cp g⁻¹ := by
    intro g
    rw [ContinuousLinearMap.star_eq_adjoint, eq_comm, ContinuousLinearMap.eq_adjoint_iff]
    intro x y
    rw [Submodule.coe_inner, Submodule.coe_inner, cp_coe, cp_coe, hsym, (memD.1 y.2).2, cp_inner,
      R.inner_map_left, inv_inv]
  have cp_comm : ∀ b g, Commute (P ∘L R b ∘L P) (P ∘L R g ∘L P) → Commute (cp b) (cp g) := by
    intro b g h
    ext1 x
    apply Subtype.ext
    have hx := (memD.1 x.2).2
    have := DFunLike.congr_fun h.eq (x : H)
    simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.comp_apply, hx, hP2] at this
    exact this
  have hirrD : ∀ U : Submodule ℂ D, IsClosed (U : Set D) →
      (∀ s ∈ Set.range cp, ∀ v ∈ U, s v ∈ U) → U = ⊥ ∨ U = ⊤ := by
    intro U hU hUinv
    by_cases hU0 : U = ⊥
    · exact Or.inl hU0
    right
    obtain ⟨x', hx'U, hx'0⟩ := (Submodule.ne_bot_iff U).1 hU0
    have : CompleteSpace U := hU.completeSpace_coe
    rw [← Submodule.orthogonal_eq_bot_iff, eq_bot_iff]
    intro y hy
    rw [Submodule.mem_bot]
    let ρ : Submodule ℂ H :=
      { carrier := {z | z ∈ τ ∧ ∀ g, ⟪R g (y : H), z⟫_ℂ = 0}
        add_mem' := fun {a b} ha hb => ⟨τ.add_mem ha.1 hb.1, fun g => by
          rw [inner_add_right, ha.2 g, hb.2 g, add_zero]⟩
        zero_mem' := ⟨τ.zero_mem, fun g => inner_zero_right _⟩
        smul_mem' := fun c z hz => ⟨τ.smul_mem c hz.1, fun g => by
          rw [inner_smul_right, hz.2 g, mul_zero]⟩ }
    have hρcl : IsClosed (ρ : Set H) := by
      have : (ρ : Set H) = (τ : Set H) ∩ ⋂ g, {z | ⟪R g (y : H), z⟫_ℂ = 0} := by
        ext z
        simp [ρ]
      rw [this]
      exact hcl.inter (isClosed_iInter fun g =>
        isClosed_eq (continuous_const.inner continuous_id) continuous_const)
    have hρinv : ∀ g, ∀ v ∈ ρ, R g v ∈ ρ := by
      intro g v hv
      refine ⟨hinv g v hv.1, fun h => ?_⟩
      rw [R.inner_map_right, ← UnitaryRep.map_mul_apply]
      exact hv.2 _
    have hx'ρ : ((x' : D) : H) ∈ ρ := by
      refine ⟨(memD.1 (x' : D).2).1, fun g => ?_⟩
      have h0 : ⟪(cp g⁻¹ (x' : D) : D), y⟫_ℂ = 0 :=
        (Submodule.mem_orthogonal U y).1 hy _ (hUinv _ ⟨g⁻¹, rfl⟩ _ hx'U)
      rw [Submodule.coe_inner, cp_coe, hsym, (memD.1 y.2).2, R.inner_map_left, inv_inv] at h0
      rw [← inner_conj_symm, h0, map_zero]
    rcases hirr ρ (fun z hz => hz.1) hρcl hρinv with h | h
    · exfalso
      apply hx'0
      apply Subtype.ext
      have : ((x' : D) : H) ∈ (⊥ : Submodule ℂ H) := h ▸ hx'ρ
      simpa using this
    · have hy' : (y : H) ∈ ρ := h ▸ (memD.1 y.2).1
      have := hy'.2 1
      rw [UnitaryRep.map_one_apply, inner_self_eq_zero] at this
      exact Subtype.ext this
  obtain ⟨c, hcs⟩ := GL2ProductCompleteness.eq_smul_one_of_commute_of_star (S := Set.range cp) hirrD
    (T := cp a) (by rintro _ ⟨g, rfl⟩; exact cp_comm _ _ (hc g))
    (by rintro _ ⟨g, rfl⟩; rw [cp_star]; exact cp_comm _ _ (hc' g))
  refine ⟨c, fun v hv hPv => ?_⟩
  have := congrArg (fun T : D →L[ℂ] D => ((T ⟨v, memD.2 ⟨hv, hPv⟩⟩ : D) : H)) hcs
  have h2 : ((cp a ⟨v, memD.2 ⟨hv, hPv⟩⟩ : D) : H) = c • v := by simpa using this
  exact h2

private theorem places {X ι : Type*} [Group X] (R : UnitaryRep G H) (τ : Submodule ℂ H)
    (hcl : IsClosed (τ : Set H)) (hinv : ∀ g, ∀ v ∈ τ, R g v ∈ τ)
    (hirr : ∀ ρ : Submodule ℂ H, ρ ≤ τ → IsClosed (ρ : Set H) → (∀ g, ∀ v ∈ ρ, R g v ∈ ρ) → ρ = ⊥ ∨ ρ = τ)
    (gl : ι → X → G) (hmul : ∀ i a b, gl i (a * b) = gl i a * gl i b)
    (hcomm : ∀ i j, i ≠ j → ∀ a b, Commute (gl i a) (gl j b))
    (hdec : ∀ i g, ∃ a h, g = gl i a * h ∧ ∀ b, Commute h (gl i b))
    (Q : ι → (H →L[ℂ] H)) (hPs : ∀ i, IsSelfAdjoint (Q i)) (hPP : ∀ i, Q i ∘L Q i = Q i)
    (hPc : ∀ i a b, Commute (Q i ∘L R (gl i a) ∘L Q i) (Q i ∘L R (gl i b) ∘L Q i))
    (hPh : ∀ i (h : G), (∀ b, Commute h (gl i b)) → Commute (Q i) (R h))
    (hPτ : ∀ i, ∀ v ∈ τ, Q i v ∈ τ)
    (E : H → H) (Einner : ∀ u v, ⟪u, E v⟫_ℂ = ⟪E u, v⟫_ℂ) (Eidem : ∀ v, E (E v) = E v)
    (hEQ : ∀ v, E v = v ↔ ∀ i, Q i v = v)
    (a : ι → X) (L : List ι) (hL : L.Nodup) :
    (∀ i, i ∈ L) → ∃ d : ℂ, ∀ v ∈ τ, E v = v → E (R (L.map fun i => gl i (a i)).prod v) = d • v := by
  intro hall
  have key : ∀ i a g, Commute (Q i ∘L R (gl i a) ∘L Q i) (Q i ∘L R g ∘L Q i) := by
    intro i a g
    obtain ⟨b, h, rfl, hh⟩ := hdec i g
    have hq : Commute (Q i) (R h) := hPh i h hh
    have hra : Commute (R h) (R (gl i a)) := by
      show R h * R (gl i a) = R (gl i a) * R h
      rw [← UnitaryRep.map_mul, ← UnitaryRep.map_mul, (hh a).eq]
    have e : Q i ∘L R (gl i b * h) ∘L Q i = (Q i ∘L R (gl i b) ∘L Q i) * R h := by
      ext1 v
      have := DFunLike.congr_fun hq.eq v
      simp only [ContinuousLinearMap.mul_apply] at this
      simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.comp_apply, UnitaryRep.map_mul_apply, this]
    rw [e]
    refine Commute.mul_right (hPc i a b) ?_
    show Commute (Q i * (R (gl i a) * Q i)) (R h)
    exact hq.mul_left (hra.symm.mul_left hq)
  have hinvg : ∀ i a, (gl i a)⁻¹ = gl i a⁻¹ := fun i a =>
    ((MonoidHom.mk' (gl i) (hmul i)).map_inv a).symm
  have one : ∀ i a, ∃ c : ℂ, ∀ v ∈ τ, Q i v = v → Q i (R (gl i a) v) = c • v := by
    intro i a
    refine compress_scalar R τ hcl hinv hirr (Q i) (hPs i) (hPP i) (hPτ i) (gl i a) (key i a) fun g => ?_
    rw [hinvg]
    exact key i a⁻¹ g
  have hsym : ∀ i x y, ⟪Q i x, y⟫_ℂ = ⟪x, Q i y⟫_ℂ := fun i =>
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.1 (hPs i)
  choose c hc using one
  have hlist : ∀ l : List ι, l.Nodup → ∃ d : ℂ, ∀ y ∈ τ, (∀ i ∈ l, Q i y = y) → ∀ u, (∀ i, Q i u = u) →
      ⟪u, R (l.map fun i => gl i (a i)).prod y⟫_ℂ = d * ⟪u, y⟫_ℂ := by
    intro l
    induction l with
    | nil => intro _; exact ⟨1, fun y _ _ u _ => by simp⟩
    | cons i l ih =>
      intro hnd
      obtain ⟨hi, hnd'⟩ := List.nodup_cons.1 hnd
      obtain ⟨d, hd⟩ := ih hnd'
      refine ⟨c i (a i) * d, fun y hy hyl u hu => ?_⟩
      have hpc : ∀ b, Commute (l.map fun i => gl i (a i)).prod (gl i b) := by
        intro b
        apply Commute.list_prod_left
        intro x hx
        obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
        exact hcomm j i (fun h => hi (h ▸ hj)) _ _
      have hq : Commute (Q i) (R (l.map fun i => gl i (a i)).prod) := hPh i _ hpc
      have hy' : Q i (R (l.map fun i => gl i (a i)).prod y) = R (l.map fun i => gl i (a i)).prod y := by
        have := DFunLike.congr_fun hq.eq y
        simp only [ContinuousLinearMap.mul_apply] at this
        rw [this, hyl i List.mem_cons_self]
      have hyτ : R (l.map fun i => gl i (a i)).prod y ∈ τ := hinv _ _ hy
      rw [List.map_cons, List.prod_cons, UnitaryRep.map_mul_apply]
      calc ⟪u, R (gl i (a i)) (R (l.map fun i => gl i (a i)).prod y)⟫_ℂ
          = ⟪Q i u, R (gl i (a i)) (R (l.map fun i => gl i (a i)).prod y)⟫_ℂ := by rw [hu i]
        _ = ⟪u, Q i (R (gl i (a i)) (R (l.map fun i => gl i (a i)).prod y))⟫_ℂ := hsym _ _ _
        _ = c i (a i) * ⟪u, R (l.map fun i => gl i (a i)).prod y⟫_ℂ := by
          rw [hc i (a i) _ hyτ hy', inner_smul_right]
        _ = c i (a i) * (d * ⟪u, y⟫_ℂ) := by
          rw [hd y hy (fun j hj => hyl j (List.mem_cons_of_mem _ hj)) u hu]
        _ = c i (a i) * d * ⟪u, y⟫_ℂ := by ring
  obtain ⟨d, hd⟩ := hlist L hL
  refine ⟨d, fun v hv hvf => ?_⟩
  have hvQ := (hEQ v).1 hvf
  generalize hw0 : R (L.map fun i => gl i (a i)).prod v = w0
  have hd' : ∀ u, (∀ i, Q i u = u) → ⟪u, w0⟫_ℂ = d * ⟪u, v⟫_ℂ := fun u hu => by
    rw [← hw0]
    exact hd v hv (fun i _ => hvQ i) u hu
  have hw : ∀ i, Q i (E w0) = E w0 := (hEQ _).1 (Eidem w0)
  have hx : ∀ i, Q i (E w0 - d • v) = E w0 - d • v := fun i => by
    rw [map_sub, map_smul, hw, hvQ]
  have hxE := (hEQ _).2 hx
  have h1 : ⟪E w0 - d • v, E w0⟫_ℂ = ⟪E w0 - d • v, w0⟫_ℂ := by rw [Einner, hxE]
  have h2 := hd' _ hx
  have h3 : ⟪E w0 - d • v, E w0 - d • v⟫_ℂ = 0 := by
    conv_lhs => rw [inner_sub_right (𝕜 := ℂ) (E w0 - d • v) (E w0) (d • v)]
    rw [h1, h2, inner_smul_right, sub_self]
  exact sub_eq_zero.1 (inner_self_eq_zero.1 h3)

end Window

end UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA.RI

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA.rankInf :
    ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (ι : Type) [Fintype ι] (C : Co K ι) (μ : Measure (G1 K 2)) [μ.IsHaarMeasure] (τ : Submodule ℂ (LL μ)), CuspIrr μ τ → ∀ (n : ι → ℕ) (q : ι → ℤ), (∀ i, ∃ v ∈ τ, C.Pi μ i (n i) (q i) v ≠ 0) → RankInf μ τ C.κ₂ (C.p n q) := by
  intro K _ _ _ ι _ C μ _ τ hτ n q hocc
  obtain ⟨hP, hfix, hid, -⟩ := piLaws K ι C μ
  obtain ⟨-, -, -, -, hmul, hcomm, -, hdec, hprod, -⟩ := coLaws K ι C
  set R := rightRegularRep (Gam K 2) μ with hR
  choose P hPv hPs hPP hPc hPh hPτ using hP
  set Q : ι → (LL μ →L[ℂ] LL μ) := fun i => P i (n i) (q i) with hQ
  have hfix' : ∀ v, pOp μ C.κ₂ (C.p n q) v = v ↔ ∀ i, Q i v = v := fun v => by
    rw [hfix n q v]
    exact forall_congr' fun i => by rw [hPv]

  have hex : ∃ v ∈ τ, v ≠ 0 ∧ pOp μ C.κ₂ (C.p n q) v = v := by
    obtain ⟨v, hv, hv0, hvf⟩ := occ K ι C μ τ hτ τ Finset.univ n q le_rfl hτ.ne
      (fun i a v hv => hτ.inv _ v hv) (fun i n q v hv => by rw [← hPv]; exact hPτ i n q τ hτ v hv) hocc
    exact ⟨v, hv, hv0, (hfix n q v).2 fun i => hvf i (Finset.mem_univ i)⟩
  refine ⟨hid n q, hex, fun g => ?_⟩
  obtain ⟨a, ha⟩ := hprod g
  let π : UnitaryRep (archCompact K 2) (LL μ) :=
    R.compHom ((archP K 2).comp (archCompact K 2).subtype) (continuous_archP.comp continuous_subtype_val)
  have hE : ∀ v, pOp μ C.κ₂ (C.p n q) v = RI.avg C.κ₂ π (C.p n q) v := fun _ => rfl
  have hk := (hid n q).haar
  haveI := hk.prob
  have Einner : ∀ u v, ⟪u, pOp μ C.κ₂ (C.p n q) v⟫_ℂ = ⟪pOp μ C.κ₂ (C.p n q) u, v⟫_ℂ := fun u v => by
    rw [hE, hE]
    exact RI.avg_inner hk.left (hid n q).cont (hid n q).star u v
  have Eidem : ∀ v, pOp μ C.κ₂ (C.p n q) (pOp μ C.κ₂ (C.p n q) v) = pOp μ C.κ₂ (C.p n q) v := fun v => by
    rw [hE, hE]
    exact RI.avg_avg hk.left (hid n q).cont (hid n q).idem v
  have hall : ∀ i, i ∈ (Finset.univ : Finset ι).toList := fun i => Finset.mem_toList.2 (Finset.mem_univ i)
  obtain ⟨d, hd⟩ := RI.places R τ hτ.closed hτ.inv hτ.irr C.gl hmul hcomm hdec Q (fun i => hPs i _ _)
    (fun i => hPP i _ _) (fun i a b => hPc i _ _ a b) (fun i h hh => hPh i _ _ h hh)
    (fun i => hPτ i _ _ τ hτ) (pOp μ C.κ₂ (C.p n q)) Einner Eidem hfix' a (Finset.univ : Finset ι).toList
    (Finset.nodup_toList _) hall
  refine ⟨d, fun v hv hvf => ?_⟩
  rw [ha _ (Finset.nodup_toList _) hall]
  exact hd v hv hvf
