import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Euler
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LemmaU
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdA
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFactorNonzero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneHermitianIdealCoprimeLt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneSkewIdealCoprimeLtStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMultilinearFactorization
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open Classical

noncomputable section

namespace GlobalTheory.ThK.ConeEulerPure

theorem ne_zero_of_hasProd {ι : Type} {f : ι → ℂ} {a : ℂ} (h : HasProd f a) (ha : a ≠ 0) (i : ι) : f i ≠ 0 := by
  intro hi
  apply ha
  have h0 : HasProd f 0 := by
    unfold HasProd
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop {i}] with s hs
    exact (Finset.prod_eq_zero (hs (Finset.mem_singleton_self i)) hi).symm
  exact h.unique h0

theorem cone_pure_eq_smul : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a'))
    (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W),
    CfgA B G G₁ H H' → IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e →
    ∀ (ei : SInf F (Fin (b + 2) × Fin (b + 2 + a')) →L[ℂ] SInf F (Fin b × Fin (b + a')))
      (ev : ∀ v : Pl F, ((Fin (b + 2) × Fin (b + 2 + a') → Fv F v) → ℂ) →ₗ[ℂ] (Fin b × Fin (b + a') → Fv F v) → ℂ),
      ei ≠ 0 → (∀ v, ev v (G.M.vac v) = G₁.M.vac v ∧ (SB _).map (ev v) = SB _) →
      (∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = G.M.vac v) → e (pure f φ) = pure (ei f) fun v => ev v (φ v)) →
    ∀ (K : Subgroup (UA σ G.V.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ), IsStab B K → μK.IsHaarMeasure → μ.IsHaarMeasure →
    ∀ (μKi : Measure (KAt K (evI F))) (μi : Measure (idelesAt E (evI F))) (μKf : ∀ v : Pl F, Measure (KAt K (evFin F v)))
      (μf : ∀ v : Pl F, Measure (idelesAt E (evFin F v))), IsNormK K (evI F) μKi → μi.IsHaarMeasure →
      (∀ v, IsNormK K (evFin F v) (μKf v)) → (∀ v, IsNormE E v (μf v)) → ∀ T : Finset (Pl F), X.T ⊆ T →
    ∃ κ : ℂ, κ ≠ 0 ∧ ∀ f ∈ G.M.Pol B.ψ B.emb, ∀ (φ : ∀ v : Pl F, (Fin (b + 2) × Fin (b + 2 + a') → Fv F v) → ℂ),
      (∀ v, φ v ∈ SB _) → (∀ v ∉ T, φ v = G.M.vac v) →
      cone B G.M om e K μK μ (shiftA H H') X.ν ((b + 2 - a') / 2) (pure f φ) =
        κ • pure (coneInf B G.M om ei K μKi μi (shiftA H H') X.ν ((b + 2 - a') / 2) f) (fun v => if v ∈ T then coneFin B G.M om v (ev v) K (μKf v) (μf v) (shiftA H H') X.ν ((b + 2 - a') / 2) (φ v) else G₁.M.vac v) := by
  intro hKP F E _ _ _ _ _ σ B b a' G G₁ H H' X om om' om₁ om₁' hC hX hX₁ e he ei ev hei hev hfac K μK μ hK hμK hμ
    μKi μi μKf μf hKi hμi hKf hEf T hTT
  haveI := hμK
  haveI := hμ
  haveI := hμi
  have hM₁ : G₁.M.IsGood B.ψ := hX₁.geo.hM
  obtain ⟨κ₀, hκ₀, hE⟩ := GlobalTheory.ThK.ConeEuler.euler hKP.base B G G₁ H H' hC e he ei ev ⟨hei, hev, hfac⟩ K hK μK μ
    μKf hKf μf hEf μKi hKi μi
  obtain ⟨hE1, hE2⟩ := hE X om om' hX hM₁

  let u : Pl F → ℂ := fun v => GlobalTheory.UnrEuler.unrFac X.ν (GlobalTheory.UnrEuler.idA σ H.𝔟 H'.𝔟) (((b + 2 - a') / 2 : ℕ) : ℂ) v
  obtain ⟨-, hP⟩ := GlobalTheory.UnrEuler.glob σ B G G₁ H H' hC X om om' hX
  set P : ℂ := ((idealVal X.ν H.𝔟 * idealVal X.ν H'.𝔟 : ℂˣ) : ℂ) *
      (GlobalTheory.UnrEuler.nrm (GlobalTheory.UnrEuler.idA σ H.𝔟 H'.𝔟) : ℂ) ^ (-((((b + 2 - a') / 2 : ℕ) : ℂ))) *
        charL X.ν (X.S₀ : Set (Pl F)) (((b + 2 - a') / 2 : ℕ) : ℂ) with hPdef
  have h𝔞 : GlobalTheory.UnrEuler.idA σ H.𝔟 H'.𝔟 ≠ 0 := by
    obtain ⟨h𝔟0, -⟩ := GlobalTheory.PlaneIdeal.plane_ideal_trivial σ B H G.V G₁.V 0 (b + 1) _ _ hX.base hX.geo.hV hC.hH
      (by omega) (by omega)
    obtain ⟨h𝔠0, -⟩ := GlobalTheory.T.adapted_plane_skew_ideal_coprime_lt σ B H' G.W G₁.W 0 (b + 1) _ _ hX.base hX.geo.hW hC.hH' (by omega) (by omega)
    exact mul_ne_zero (mul_ne_zero h𝔟0 (inv_ne_zero (GlobalTheory.UnrEuler.conjI_ne_zero σ h𝔠0)))
      (inv_ne_zero GlobalTheory.UnrEuler.diffE_ne_zero)
  have hP0 : P ≠ 0 := by
    have hk : 2 ≤ (b + 2 - a') / 2 := by have := hX.geo.eBig; omega
    refine mul_ne_zero (mul_ne_zero (Units.ne_zero _) ?_) (GlobalTheory.StepFacNe.charL_ne_zero X.ν _ _ hk)
    have hn : (GlobalTheory.UnrEuler.nrm (GlobalTheory.UnrEuler.idA σ H.𝔟 H'.𝔟) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.2 (GlobalTheory.UnrEuler.nrm_pos h𝔞).ne'
    intro h0
    exact hn ((Complex.cpow_eq_zero_iff _ _).1 h0).1
  let Fu : Pl F → ℂ := fun v => if v ∈ X.T then 1 else u v
  have hFu : HasProd Fu P := by
    have hsub : Function.mulSupport Fu ⊆ {v | v ∉ (X.T : Set (Pl F))} := by
      intro v hv
      by_contra h
      simp only [Set.mem_setOf_eq, not_not] at h
      exact hv (if_pos h)
    have e1 : (fun v : {v // v ∉ (X.T : Set (Pl F))} => Fu v.1) = fun v => u v.1 := funext fun v => if_neg v.2
    have hP' : HasProd (fun v : {v // v ∉ (X.T : Set (Pl F))} => Fu v.1) P := by rw [e1]; exact hP
    exact (hasProd_subtype_iff_of_mulSupport_subset hsub).1 hP'
  have hu0 : ∀ v ∉ X.T, u v ≠ 0 := fun v hv => by
    have := ne_zero_of_hasProd hFu hP0 v
    simpa only [Fu, if_neg hv] using this
  let D : Pl F → ℂ := fun v => if v ∈ T ∧ v ∉ X.T then (u v)⁻¹ else 1
  have hD : HasProd D (∏ v ∈ T, D v) := hasProd_prod_of_ne_finset_one fun v hv => if_neg fun h => hv h.1
  let c : Pl F → ℂ := fun v => if v ∈ T then 1 else u v
  have hcFD : ∀ v, c v = Fu v * D v := fun v => by
    by_cases h1 : v ∈ X.T
    · simp [c, Fu, D, h1, hTT h1]
    · by_cases h2 : v ∈ T
      · simp [c, Fu, D, h1, h2, hu0 v h1]
      · simp [c, Fu, D, h1, h2]
  set Q : ℂ := P * ∏ v ∈ T, D v with hQdef
  have hc : HasProd c Q := by
    have := hFu.mul hD
    convert this using 1
    funext v
    exact hcFD v
  have hQ0 : Q ≠ 0 := by
    refine mul_ne_zero hP0 (Finset.prod_ne_zero_iff.2 fun v _ => ?_)
    simp only [D]
    split_ifs with h
    · exact inv_ne_zero (hu0 v h.2)
    · exact one_ne_zero
  refine ⟨κ₀ * Q, mul_ne_zero hκ₀ hQ0, fun f _ φ hφ hφT => ?_⟩
  funext y
  obtain ⟨g, hg, -⟩ := hE2 f
  have hci := GlobalTheory.ThK.coe_coneInf ⟨g, hg⟩
  have hmain := (hE1 f φ T hφ hφT y).2.2
  let ψ : ∀ v : Pl F, (Fin b × Fin (b + a') → Fv F v) → ℂ := fun v =>
    if v ∈ T then coneFin B G.M om v (ev v) K (μKf v) (μf v) (shiftA H H') X.ν ((b + 2 - a') / 2) (φ v) else G₁.M.vac v
  have hfac' : ∀ v, coneFin B G.M om v (ev v) K (μKf v) (μf v) (shiftA H H') X.ν ((b + 2 - a') / 2) (φ v)
      (fun i => evFin F v (y i)) = c v * ψ v (fun i => evFin F v (y i)) := fun v => by
    by_cases hv : v ∈ T
    · simp [c, ψ, hv]
    · have hvX : v ∉ X.T := fun h => hv (hTT h)
      rw [hφT v hv, GlobalTheory.UnrLocA.lemmaU σ B G G₁ H H' hC X om om' hX hM₁ e he ei ev hei hev hfac K hK v hvX
        (μKf v) (hKf v) (μf v) (hEf v)]
      simp [c, ψ, hv, u]
  have hfin : (Function.mulSupport fun v => ψ v (fun i => evFin F v (y i))).Finite := by
    have hev1 : ∀ᶠ v in cofinite, G₁.M.vac v (fun i => evFin F v (y i)) = 1 := by
      have h1 : ∀ᶠ v in cofinite, ∀ i, evFin F v (y i) ∈ v.adicCompletionIntegers F :=
        Filter.eventually_all.2 fun i => GlobalTheory.PureML.eventually_evFin_mem (y i)
      filter_upwards [hM₁.std, h1] with v hv h1v
      rw [hv]
      exact Set.indicator_of_mem (s := {x : Fin b × Fin (b + a') → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F}) h1v 1
    refine ((T.finite_toSet).union (Filter.eventually_cofinite.1 hev1)).subset ?_
    intro v hv
    by_cases hvT : v ∈ T
    · exact Or.inl hvT
    · right
      intro h
      apply hv
      simp only [ψ, if_neg hvT]
      exact h
  have hg' : HasProd (fun v => ψ v (fun i => evFin F v (y i))) (∏ᶠ v, ψ v (fun i => evFin F v (y i))) := by
    rw [finprod_eq_prod_of_mulSupport_subset _ hfin.coe_toFinset.symm.subset]
    exact hasProd_prod_of_ne_finset_one fun v hv => by
      by_contra h
      exact hv (hfin.mem_toFinset.2 h)
  have htp : ∏' v, coneFin B G.M om v (ev v) K (μKf v) (μf v) (shiftA H H') X.ν ((b + 2 - a') / 2) (φ v)
      (fun i => evFin F v (y i)) = Q * ∏ᶠ v, ψ v (fun i => evFin F v (y i)) := by
    rw [tprod_congr hfac']
    exact (hc.mul hg').tprod_eq
  rw [hmain, Pi.smul_apply, smul_eq_mul]
  show _ = (κ₀ * Q) * (coneInf B G.M om ei K μKi μi (shiftA H H') X.ν ((b + 2 - a') / 2) f (fun i => evI F (y i)) *
    ∏ᶠ v, ψ v (fun i => evFin F v (y i)))
  rw [hci, htp]
  ring

end GlobalTheory.ThK.ConeEulerPure
