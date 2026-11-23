import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFinsetOfEventually
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LintegralFintypeProdEqProd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdemSmulUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocCharEqValZpow
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MemConfTOfDetNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneHermitianIdealCoprimeLt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneSkewIdealCoprimeLtStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodModelEigenContinuous
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigALocalUnitLevi
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitIntegralAtPlaceForConfiguration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAIdeleUnitIntegralIdentity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabilizerFixesSphericalVacuumVectorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnitIndicatorIntegralValue
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedAdelicLatticeClosure
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdeleCharacterEqOneIntegralUnitsUnramifiedAdelic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalLFactorProductBoundedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnitaryIntegralIdelesFactorStatement

noncomputable section

open scoped TensorProduct NNReal Matrix ENNReal nonZeroDivisors
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.ConeEuler GlobalTheory.UnrEuler
open GlobalTheory.Doubling (absE absEv unitFin ideleAt)
open scoped GlobalTheory.VacAny
open Formalism.L2.Host (aboveF)

namespace GlobalTheory.ThK.UnrBound

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem euler_bound (s : ℕ) (hs : 2 ≤ s) : ∃ C : ℝ, ∀ S : Finset (Pl F),
    ∏ v ∈ S, ‖Lv (fun _ : HeightOneSpectrum (𝓞 E) => ({1} : Multiset ℂˣ)) v (s : ℂ)‖ ≤ C :=
  GlobalTheory.T.local_l_factor_product_bounded s hs

theorem integral_reduce (σ : E →ₐ[F] E) {n : ℕ} {X : Spc F E n} (K : Subgroup (UA σ X.J))
    (hKc : IsClosed (K : Set (UA σ X.J))) (v : Pl F) (μK : Measure (KAt K (evFin F v))) (hμK : IsNormK K (evFin F v) μK)
    (μE : Measure (idelesAt E (evFin F v))) (hμE : IsNormE E v μE) (g : UA σ X.J × (AE F E)ˣ → ℝ)
    (r : idelesAt E (evFin F v) → ℝ)
    (hg : ∀ k ∈ KAt K (evFin F v), ∀ (l : (AE F E)ˣ) (hl : l ∈ idelesAt E (evFin F v)), g (k, l) = r ⟨l, hl⟩) :
    ∫ q, g q ∂((μK.map Subtype.val).prod (μE.map Subtype.val)) = ∫ l, r l ∂μE :=
  GlobalTheory.T.local_unitary_integral_ideles_factor σ K hKc v μK hμK μE hμE g r hg

theorem int_vac (σ : E →ₐ[F] E) (B : Base F E) {b a' : ℕ} (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b)
    (H' : Plane E (b + 2 + a') (b + a')) (hC : CfgA B G G₁ H H') (X : Chars F E) (om : Rep σ G.V G.W)
    (om' : Rep σ G.V' G.W) (hX : IsTriple B G X om om') (hM₁ : G₁.M.IsGood B.ψ)
    (e : Fn F (b + 2) (b + 2 + a') →ₗ[ℂ] Fn F b (b + a')) (he : IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e)
    (ei : SInf F (Fin (b + 2) × Fin (b + 2 + a')) →L[ℂ] SInf F (Fin b × Fin (b + a')))
    (ev : ∀ v : Pl F, ((Fin (b + 2) × Fin (b + 2 + a') → Fv F v) → ℂ) →ₗ[ℂ] (Fin b × Fin (b + a') → Fv F v) → ℂ)
    (hei : ei ≠ 0) (hev : ∀ v, ev v (G.M.vac v) = G₁.M.vac v ∧ (SB _).map (ev v) = SB _)
    (hfac : ∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = G.M.vac v) → e (pure f φ) = pure (ei f) fun v => ev v (φ v))
    (K : Subgroup (UA σ G.V.J)) (hK : IsStab B K) (v : Pl F) (hv : v ∉ X.T) (k : UA σ G.V.J) (hk : k ∈ KAt K (evFin F v))
    (l : (AE F E)ˣ) (hl : l ∈ idelesAt E (evFin F v)) (y : Fin b × Fin (b + a') → Fv F v) (z : ℕ) :
    coneFinInt B G.M om v (ev v) (shiftA H H') X.ν z (G.M.vac v) k l y =
      Set.indicator {l : (AE F E)ˣ | (unitFin F E v l : Fv F v ⊗[F] E) ∈ GlobalTheory.SnMass.locId v (idA σ H.𝔟 H'.𝔟)}
        (fun l => (X.ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ z) l * G₁.M.vac v y := by
  have hψ : Continuous B.ψ := hX.base.std.1
  have hM := hX.geo.hM
  have hvac : G.M.vac v ∈ SB _ := (hM.vac v).1
  have hfix : locOp v (om (k, 1)) (G.M.vac v) = G.M.vac v :=
    locOp_eq hvac hvac (GlobalTheory.T.stabilizer_fixes_spherical_vacuum_vector σ B G X om om' hX K hK v hv k hk)
  rw [coneFinInt, hfix, (locOp_rho G.M.co hψ v (shiftA H H' l) hvac).2]
  by_cases hl' : (unitFin F E v l : Fv F v ⊗[F] E) ∈ GlobalTheory.SnMass.locId v (idA σ H.𝔟 H'.𝔟)
  · rw [GlobalTheory.VacShift.vac_fixed σ B G G₁ H H' X om om' hX hC v l hl hl', (hev v).1,
      Set.indicator_of_mem (show l ∈ {l : (AE F E)ˣ | (unitFin F E v l : Fv F v ⊗[F] E) ∈
        GlobalTheory.SnMass.locId v (idA σ H.𝔟 H'.𝔟)} from hl')]
    ring
  · have h0 : ev v (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M.co v (shiftA H H' l)) (G.M.vac v)) = 0 := by
      obtain ⟨γ, hγv, hγ0, hγL, hne⟩ := GlobalTheory.SuppOut.exists_lat_pair_ne_one σ B G G₁ H H' X om om' hX hC v l hl hl'
      have hsb : schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M.co v (shiftA H H' l)) (G.M.vac v) ∈ SB _ :=
        GlobalTheory.SchrSB.schr_mem_SB B.ψ hψ v _ _ hvac
      have h1 := GlobalTheory.ThK.EvLocInv.ev_schr_of_mem B G.M G₁.M H.ι H'.ι (isoA H H') e he hψ hM hM₁ ei ev hei hev hfac v γ
        (Or.inl hγ0) hγv _ hsb
      rw [GlobalTheory.CommVac.commVac σ B G G₁ H H' X om om' hX hC v γ hγv hγ0 hγL, map_smul] at h1
      have h2 : (GlobalTheory.LatVac.psiAt B.ψ v (evFin F v (symp (cA σ) (-1) (incM F G.V.J) (incM F G.W.J) γ (shiftA H H' l))) - 1) •
          ev v (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M.co v (shiftA H H' l)) (G.M.vac v)) = 0 := by
        rw [sub_smul, one_smul, h1, sub_self]
      exact (smul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hne)
    rw [h0, Set.indicator_of_notMem (show l ∉ {l : (AE F E)ˣ | (unitFin F E v l : Fv F v ⊗[F] E) ∈
        GlobalTheory.SnMass.locId v (idA σ H.𝔟 H'.𝔟)} from hl')]
    simp

theorem integral_abs (𝔞 : FractionalIdeal (𝓞 E)⁰ E) (h𝔞 : 𝔞 ≠ 0) (v : Pl F)
    (h0 : ∀ w ∈ aboveF (L := E) F v, FractionalIdeal.count E w 𝔞 = 0) (s : ℕ) (hs : 0 < s)
    (μ : Measure (idelesAt E (evFin F v))) (hμ : IsNormE E v μ) :
    ∫ l : idelesAt E (evFin F v), Set.indicator
        {l : idelesAt E (evFin F v) | (unitFin F E v l.1 : Fv F v ⊗[F] E) ∈ GlobalTheory.SnMass.locId v 𝔞}
        (fun l => (absE F E l.1 : ℝ) ^ s) l ∂μ =
      ‖Lv (fun _ : HeightOneSpectrum (𝓞 E) => ({1} : Multiset ℂˣ)) v (s : ℂ)‖ := by
  have h1 := GlobalTheory.UnrTate.integral_locId_eq_unrFac (1 : Chr F E) 𝔞 h𝔞 v (fun w _ x _ => by simp [locChar]) s hs μ hμ
  have e : ∀ l : idelesAt E (evFin F v), Set.indicator
      {l : idelesAt E (evFin F v) | (unitFin F E v l.1 : Fv F v ⊗[F] E) ∈ GlobalTheory.SnMass.locId v 𝔞}
      (fun l => ((1 : Chr F E) l.1 : ℂ) * ((absE F E l.1 : ℝ) : ℂ) ^ s) l =
      ((Set.indicator {l : idelesAt E (evFin F v) | (unitFin F E v l.1 : Fv F v ⊗[F] E) ∈ GlobalTheory.SnMass.locId v 𝔞}
        (fun l => (absE F E l.1 : ℝ) ^ s) l : ℝ) : ℂ) := by
    intro l
    by_cases h : l ∈ {l : idelesAt E (evFin F v) | (unitFin F E v l.1 : Fv F v ⊗[F] E) ∈ GlobalTheory.SnMass.locId v 𝔞}
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]; simp
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h]; simp
  simp_rw [e, integral_complex_ofReal] at h1
  have h2 : unrFac (1 : Chr F E) 𝔞 (s : ℂ) v = Lv (fun _ : HeightOneSpectrum (𝓞 E) => ({1} : Multiset ℂˣ)) v (s : ℂ) := by
    rw [unrFac, Finset.prod_eq_one, one_mul]
    · congr 1
      funext w
      simp [charFam, UnrAt, locChar]
    · intro w hw
      rw [h0 w hw]
      simp [npow]
  rw [h2] at h1
  rw [← h1, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun l => ?_)]
  exact Set.indicator_nonneg (fun _ _ => by positivity) _

end GlobalTheory.ThK.UnrBound

namespace GlobalTheory.ThK.UnrBound

theorem unr_integrand_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), GlobalTheory.FunPr.Hypotheses₂ → ∀ (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b)
    (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ (e : Fn F (b + 2) (b + 2 + a') →ₗ[ℂ] Fn F b (b + a')), IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e →
    ∀ (ei : SInf F (Fin (b + 2) × Fin (b + 2 + a')) →L[ℂ] SInf F (Fin b × Fin (b + a')))
      (ev : ∀ v : Pl F, ((Fin (b + 2) × Fin (b + 2 + a') → Fv F v) → ℂ) →ₗ[ℂ] (Fin b × Fin (b + a') → Fv F v) → ℂ),
    (ei ≠ 0 ∧ (∀ v, ev v (G.M.vac v) = G₁.M.vac v ∧ (SB _).map (ev v) = SB _) ∧
      ∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = G.M.vac v) → e (pure f φ) = pure (ei f) fun v => ev v (φ v)) →
    ∀ (K : Subgroup (UA σ G.V.J)), IsStab B K →
    ∀ (μKv : ∀ v : Pl F, Measure (KAt K (evFin F v))), (∀ v, IsNormK K (evFin F v) (μKv v)) →
    ∀ (μEv : ∀ v : Pl F, Measure (idelesAt E (evFin F v))), (∀ v, IsNormE E v (μEv v)) →
    ∀ (μKi : Measure (KAt K (evI F))), IsNormK K (evI F) μKi → ∀ (μEi : Measure (idelesAt E (evI F))), μEi.IsHaarMeasure →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → G₁.M.IsGood B.ψ →
    ∀ (φ : ∀ v : Pl F, (Fin (b + 2) × Fin (b + 2 + a') → Fv F v) → ℂ) (T : Finset (Pl F)), (∀ v, φ v ∈ SB _) →
      (∀ v ∉ T, φ v = G.M.vac v) → ∀ y : Fin b × Fin (b + a') → AF F, ∃ (S₀ : Finset (Pl F)) (C : ℝ),
      (∀ v ∉ S₀, ∀ k ∈ KAt K (evFin F v), ∀ l ∈ unitsAt E v,
        coneFinInt B G.M om v (ev v) (shiftA H H') X.ν ((b + 2 - a') / 2) (φ v) k l (fun i => evFin F v (y i)) = 1) ∧
      ∀ S : Finset (Pl F), S₀ ⊆ S → ∏ v ∈ S, ∫ q : UA σ G.V.J × (AE F E)ˣ,
        ‖coneFinInt B G.M om v (ev v) (shiftA H H') X.ν ((b + 2 - a') / 2) (φ v) q.1 q.2 (fun i => evFin F v (y i))‖
          ∂(((μKv v).map Subtype.val).prod ((μEv v).map Subtype.val)) ≤ C := by
  intro F E _ _ _ _ _ σ _hP B b a' G G₁ H H' hC e he ei ev hE K hK μKv hμKv μEv hμEv μKi _ μEi _ X om om' hX hM₁ φ T hφ hT y
  obtain ⟨hei, hev, hfac⟩ := hE
  have hz2 : 2 ≤ (b + 2 - a') / 2 := by have := hX.geo.eBig; omega
  have h𝔞 : idA σ H.𝔟 H'.𝔟 ≠ 0 := by
    obtain ⟨h𝔟0, -⟩ := GlobalTheory.PlaneIdeal.plane_ideal_trivial σ B H G.V G₁.V 0 (b + 1) _ _ hX.base hX.geo.hV hC.hH
      (by omega) (by omega)
    obtain ⟨h𝔠0, -⟩ := GlobalTheory.T.adapted_plane_skew_ideal_coprime_lt σ B H' G.W G₁.W 0 (b + 1) _ _ hX.base hX.geo.hW hC.hH' (by omega) (by omega)
    exact mul_ne_zero (mul_ne_zero h𝔟0 (inv_ne_zero (conjI_ne_zero σ h𝔠0))) (inv_ne_zero diffE_ne_zero)
  have hstd : {v : Pl F | ¬ G₁.M.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1}.Finite :=
    Filter.eventually_cofinite.1 hM₁.std
  have hyf : {v : Pl F | ¬ ∀ i, evFin F v (y i) ∈ v.adicCompletionIntegers F}.Finite :=
    Filter.eventually_cofinite.1 (Filter.eventually_all.2 fun i => (y i).2.2)
  have haf : {v : Pl F | ∃ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v ∧
      FractionalIdeal.count E w (idA σ H.𝔟 H'.𝔟) ≠ 0}.Finite := by
    refine ((Filter.eventually_cofinite.1 (FractionalIdeal.finite_factors (idA σ H.𝔟 H'.𝔟))).image
      (fun w : HeightOneSpectrum (𝓞 E) => w.under (𝓞 F))).subset ?_
    rintro v ⟨w, rfl, hw⟩
    exact ⟨w, hw, rfl⟩
  classical
  let S₀ : Finset (Pl F) := T ∪ X.T ∪ (hstd.union (hyf.union haf)).toFinset
  have hgood : ∀ v ∉ S₀, v ∉ T ∧ v ∉ X.T ∧ G₁.M.vac v (fun i => evFin F v (y i)) = 1 ∧
      ∀ w ∈ aboveF (L := E) F v, FractionalIdeal.count E w (idA σ H.𝔟 H'.𝔟) = 0 := by
    intro v hv
    simp only [S₀, Finset.mem_union, Set.Finite.mem_toFinset, Set.mem_union, Set.mem_setOf_eq, not_or, not_not,
      not_exists, not_and] at hv
    obtain ⟨⟨hvT, hvX⟩, hvs, hvy, hva⟩ := hv
    refine ⟨hvT, hvX, ?_, fun w hw => ?_⟩
    · rw [hvs, Set.indicator_of_mem (show (fun i => evFin F v (y i)) ∈ {x : Fin b × Fin (b + a') → Fv F v |
        ∀ i, x i ∈ v.adicCompletionIntegers F} from hvy)]
      rfl
    · exact hva w (mem_aboveF.1 hw)
  have hunr : ∀ v ∉ X.T, ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → UnrAt X.ν w := by
    intro v hv w hw
    rw [Chars.ν, div_eq_mul_inv]
    exact (hX.chars.unrα w fun h => hv (hw ▸ h)).mul (hX.chars.unrβ w fun h => hv (hw ▸ h)).inv
  have hpt : ∀ v ∉ S₀, ∀ k ∈ KAt K (evFin F v), ∀ l ∈ idelesAt E (evFin F v),
      coneFinInt B G.M om v (ev v) (shiftA H H') X.ν ((b + 2 - a') / 2) (φ v) k l (fun i => evFin F v (y i)) =
        Set.indicator {l : (AE F E)ˣ | (unitFin F E v l : Fv F v ⊗[F] E) ∈ GlobalTheory.SnMass.locId v (idA σ H.𝔟 H'.𝔟)}
          (fun l => (X.ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ ((b + 2 - a') / 2)) l := by
    intro v hv k hk l hl
    obtain ⟨hvT, hvX, hy1, -⟩ := hgood v hv
    rw [hT v hvT, int_vac σ B G G₁ H H' hC X om om' hX hM₁ e he ei ev hei hev hfac K hK v hvX k hk l hl _ _, hy1, mul_one]
  have hKc : IsClosed (K : Set (UA σ G.V.J)) := by
    have e1 : (K : Set (UA σ G.V.J)) = (GlobalTheory.StabHaar.stabK (σ := σ) B G.V : Set (UA σ G.V.J)) :=
      Set.ext fun g => (hK g).trans (GlobalTheory.StabHaar.isStab_stabK (σ := σ) B G.V g).symm
    rw [e1]
    exact GlobalTheory.StabHaar.isClosed_stabK B G.V (GlobalTheory.LatHatClosed.isClosed_latHat F E _ G.V hX.geo.hV.lat)
  have hI : ∀ v ∉ S₀, ∫ q : UA σ G.V.J × (AE F E)ˣ, ‖coneFinInt B G.M om v (ev v) (shiftA H H') X.ν ((b + 2 - a') / 2)
      (φ v) q.1 q.2 (fun i => evFin F v (y i))‖ ∂(((μKv v).map Subtype.val).prod ((μEv v).map Subtype.val)) =
      ‖Lv (fun _ : HeightOneSpectrum (𝓞 E) => ({1} : Multiset ℂˣ)) v (((b + 2 - a') / 2 : ℕ) : ℂ)‖ := by
    intro v hv
    obtain ⟨-, -, -, h0⟩ := hgood v hv
    rw [integral_reduce σ K hKc v (μKv v) (hμKv v) (μEv v) (hμEv v) _ (Set.indicator
      {l : idelesAt E (evFin F v) | (unitFin F E v l.1 : Fv F v ⊗[F] E) ∈ GlobalTheory.SnMass.locId v (idA σ H.𝔟 H'.𝔟)}
      (fun l => (absE F E l.1 : ℝ) ^ ((b + 2 - a') / 2))) ?_]
    · exact integral_abs _ h𝔞 v h0 _ (by omega) (μEv v) (hμEv v)
    · intro k hk l hl
      show ‖coneFinInt B G.M om v (ev v) (shiftA H H') X.ν ((b + 2 - a') / 2) (φ v) k l (fun i => evFin F v (y i))‖ = _
      rw [hpt v hv k hk l hl]
      by_cases h : (unitFin F E v l : Fv F v ⊗[F] E) ∈ GlobalTheory.SnMass.locId v (idA σ H.𝔟 H'.𝔟)
      · rw [Set.indicator_of_mem (show l ∈ {l : (AE F E)ˣ | (unitFin F E v l : Fv F v ⊗[F] E) ∈
            GlobalTheory.SnMass.locId v (idA σ H.𝔟 H'.𝔟)} from h),
          Set.indicator_of_mem (show (⟨l, hl⟩ : idelesAt E (evFin F v)) ∈ {l : idelesAt E (evFin F v) |
            (unitFin F E v l.1 : Fv F v ⊗[F] E) ∈ GlobalTheory.SnMass.locId v (idA σ H.𝔟 H'.𝔟)} from h)]
        rw [norm_mul, Circle.norm_coe, one_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (NNReal.coe_nonneg _)]
      · rw [Set.indicator_of_notMem (show l ∉ {l : (AE F E)ˣ | (unitFin F E v l : Fv F v ⊗[F] E) ∈
            GlobalTheory.SnMass.locId v (idA σ H.𝔟 H'.𝔟)} from h),
          Set.indicator_of_notMem (show (⟨l, hl⟩ : idelesAt E (evFin F v)) ∉ {l : idelesAt E (evFin F v) |
            (unitFin F E v l.1 : Fv F v ⊗[F] E) ∈ GlobalTheory.SnMass.locId v (idA σ H.𝔟 H'.𝔟)} from h), norm_zero]
  obtain ⟨Cζ, hCζ⟩ := euler_bound (F := F) (E := E) ((b + 2 - a') / 2) hz2
  let I : Pl F → ℝ := fun v => ∫ q : UA σ G.V.J × (AE F E)ˣ, ‖coneFinInt B G.M om v (ev v) (shiftA H H') X.ν
    ((b + 2 - a') / 2) (φ v) q.1 q.2 (fun i => evFin F v (y i))‖ ∂(((μKv v).map Subtype.val).prod ((μEv v).map Subtype.val))
  refine ⟨S₀, (∏ v ∈ S₀, I v) * Cζ, fun v hv k hk l hl => ?_, fun S hS => ?_⟩
  · have hl' := unitsAt_le v hl
    obtain ⟨-, hvX, -, h0⟩ := hgood v hv
    have hord := (GlobalTheory.UnrTate.mem_unitsAt_iff v hl').1 hl
    have hmem : (unitFin F E v l : Fv F v ⊗[F] E) ∈ GlobalTheory.SnMass.locId v (idA σ H.𝔟 H'.𝔟) :=
      (GlobalTheory.UnrTate.memLocId_iff v h𝔞 _).2 fun w hw => by rw [h0 w hw, hord w hw]
    have hν : (X.ν l : ℂ) = 1 := by
      rw [← ideleAt_unitFin hl', GlobalTheory.UnrTate.nu_ideleAt X.ν v (hunr v hvX)]
      exact Finset.prod_eq_one fun w hw => by rw [hord w hw, zpow_zero]
    rw [hpt v hv k hk l hl', Set.indicator_of_mem (show l ∈ {l : (AE F E)ˣ | (unitFin F E v l : Fv F v ⊗[F] E) ∈
      GlobalTheory.SnMass.locId v (idA σ H.𝔟 H'.𝔟)} from hmem), hν, absE_of_mem_unitsAt hl]
    simp
  · calc ∏ v ∈ S, I v = (∏ v ∈ S₀, I v) * ∏ v ∈ S \ S₀, I v := by
          rw [mul_comm, Finset.prod_sdiff hS]
      _ = (∏ v ∈ S₀, I v) * ∏ v ∈ S \ S₀,
          ‖Lv (fun _ : HeightOneSpectrum (𝓞 E) => ({1} : Multiset ℂˣ)) v (((b + 2 - a') / 2 : ℕ) : ℂ)‖ := by
          congr 1
          exact Finset.prod_congr rfl fun v hv => hI v (Finset.mem_sdiff.1 hv).2
      _ ≤ (∏ v ∈ S₀, I v) * Cζ :=
          mul_le_mul_of_nonneg_left (hCζ (S \ S₀))
            (Finset.prod_nonneg fun v _ => integral_nonneg fun _ => norm_nonneg _)

end GlobalTheory.ThK.UnrBound
