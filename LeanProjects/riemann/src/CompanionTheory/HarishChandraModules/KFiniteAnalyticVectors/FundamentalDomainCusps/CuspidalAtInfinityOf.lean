import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.FundamentalDomainCusps.ShortIsot
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.RightRegularIsometricMultiplicative
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.ConcreteLevelAdelicSubset

open MeasureTheory Topology Filter Set Matrix NumberField
open scoped ENNReal Pointwise

noncomputable section

namespace CompanionTheory.D.gk.RF

open Formalism.MainNotions.S Formalism.L2.SG.ProjRows Formalism.MainNotions.LeviCoordinates

theorem cuspidal_at_infinity_of : Sel → Avg → NWSub → RealPar → ParPi → Transp → GamSub → GeoInf → CuspInf := by
  classical
  intro hSel hAvg hNW hRP hPi hT hGam hGeo I M hM ph hph hconv U hU
  obtain ⟨K, hKn, hKU, hK⟩ := local_compact_nhds hU
  obtain ⟨C, hC, hy⟩ := hGeo I M hM (interior K) (interior_mem_nhds.2 hKn)
  refine ⟨C, hC, fun y => (hy y).imp_right ?_⟩
  rintro ⟨W, hW0, hWi, hcov⟩
  obtain ⟨-, -, -, hperp, hne, -⟩ := hT I
  have hiso : ∀ v, Isot (Formalism.REAL.Jm (I.ε v)) (Wv I W v) := fun v => by
    unfold Isot
    rw [← hperp]
    exact Submodule.span_mono (image_mono hWi)
  choose Nv hNv using fun v => (hNW _ _ _ (hiso v)).2
  let N : Subgroup I.Ginf := Subgroup.pi univ Nv
  have hNm : ∀ g, g ∈ N ↔ g ∈ NInf I W := fun g => by
    simp only [N, Subgroup.mem_pi, mem_univ, forall_true_left, NInf, mem_ofPred_eq, ← hNv, SetLike.mem_coe]
  have hNc : IsClosed (N : Set I.Ginf) := by
    rw [Subgroup.coe_pi]
    exact isClosed_set_pi fun v _ => by rw [hNv]; exact (hNW _ _ _ (hiso v)).1
  obtain ⟨Γ, hΓ, hΓd⟩ := hGam I M
  have hc : Continuous fun m : I.Ginf => y⁻¹ * m * y := by fun_prop
  have hcK : IsCompact ((fun m : I.Ginf => y⁻¹ * m * y) ⁻¹' K) :=
    (((Homeomorph.mulLeft y⁻¹).trans (Homeomorph.mulRight y)).isCompact_preimage).2 hK
  obtain ⟨ν, hν, hνV, hinv⟩ := hAvg I.Ginf N (Γ ⊓ N) hNc inf_le_right
    (fun B hB => (hΓd B hB).subset fun x hx => ⟨hx.1, hx.2.1⟩) ((fun m => y⁻¹ * m * y) ⁻¹' interior K)
    (isOpen_interior.preimage hc)
    (hcK.of_isClosed_subset isClosed_closure (closure_minimal (preimage_mono interior_subset) hcK.isClosed))
    fun m hm => by
      obtain ⟨γ, hγ, hγN, h⟩ := hcov m ((hNm m).1 hm)
      exact ⟨γ, ⟨hΓ.ge hγ, (hNm γ).2 hγN⟩, h⟩
  refine ⟨ν, hν, hνV.mono fun m hm => hKU (interior_subset hm), fun u hu huΓ hrep x => ?_⟩
  obtain ⟨huc, B, hB⟩ := id hu
  have hc2 : Continuous fun p : I.Ginf × I.Ginf => u (p.1 * p.2) := huc.comp continuous_mul
  let F : I.Ginf → ℂ := fun x => ∫ m, u (m * x) ∂ν
  have hFb : BC F := ⟨continuous_of_dominated (bound := fun _ => B)
      (fun x => (hc2.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable)
      (fun x => Eventually.of_forall fun _ => hB _) (integrable_const _)
      (Eventually.of_forall fun m => hc2.comp (continuous_const.prodMk continuous_id)),
    B, fun x => by simpa using norm_integral_le_of_norm_le_const (μ := ν) (Eventually.of_forall fun m => hB (m * x))⟩
  have hFN : LInv N F := fun m hm x => hinv u hu (fun γ hγ => huΓ γ (by rw [← hΓ]; exact hγ.1)) m hm x
  obtain ⟨v₀⟩ : Nonempty (InfinitePlace I.F) := inferInstance
  obtain ⟨a, Ht, P⟩ := hRP _ _ _ (hne v₀ W hW0) (hiso v₀) (Nv v₀) (hNv v₀)
  have h0 := hSel I.Ginf (muInf I) ph hph hconv _ _ _ (hPi _ _ v₀ _ a Ht P) F hFb (by
    rintro _ ⟨m, hm, rfl⟩
    refine hFN _ fun v _ => ?_
    by_cases hv : v = v₀
    · subst hv; simpa using hm
    · simp [Pi.mulSingle_eq_of_ne hv]) x
  have hI : Integrable (fun p : I.Ginf × I.Ginf => ph p.2 * u (p.1 * x * p.2)) (ν.prod (muInf I)) :=
    (hph.comp_snd ν).mul_bdd
      (huc.comp (by fun_prop) : Continuous fun p : I.Ginf × I.Ginf => u (p.1 * x * p.2)).aestronglyMeasurable
      (Eventually.of_forall fun _ => hB _)
  rw [← h0, integral_congr_ae (Eventually.of_forall fun m => hrep (m * x)), integral_integral_swap hI]
  simp only [F, integral_const_mul, mul_assoc]

theorem level_structure_of : LevelOf := by
  intro I e hlc hs
  let K : Subgroup I.Gf := (Formalism.UG.stabGL I.Lf).comap (Formalism.UG.UPts I.cm.sig I.J (Af I.F)).subtype
  have hK : IsCompact (K : Set I.Gf) := PI.WAU.maximal_compact_isCompact I
  have hKo : IsOpen (K : Set I.Gf) := Formalism.L2.SG.Pf.kset_open I
  let Kp : Subgroup I.Gf :=
    { carrier := {k | k ∈ K ∧ ∀ x, e (k * x) = e x}
      mul_mem' := fun ha hb => ⟨K.mul_mem ha.1 hb.1, fun x => by rw [mul_assoc, ha.2, hb.2]⟩
      one_mem' := ⟨K.one_mem, fun x => by rw [one_mul]⟩
      inv_mem' := fun {k} hk => ⟨K.inv_mem hk.1, fun x => by rw [← hk.2 (k⁻¹ * x), mul_inv_cancel_left]⟩ }
  have h1 : ∀ᶠ k in 𝓝 (1 : I.Gf), ∀ x ∈ (K : Set I.Gf), e (k * x) = e x := by
    refine hK.eventually_forall_of_forall_eventually fun x _ => ?_
    have a1 := (hlc.comp_continuous (continuous_mul (M := I.Gf))).eventually_eq (1, x)
    have a2 := (hlc.comp_continuous (continuous_snd (X := I.Gf))).eventually_eq (1, x)
    filter_upwards [a1, a2] with p h1 h2
    simp only [Function.comp_apply, one_mul] at h1 h2
    rw [h1, h2]
  have hop : IsOpen (Kp : Set I.Gf) := by
    refine Kp.isOpen_of_mem_nhds (g := 1) ?_
    filter_upwards [h1, hKo.mem_nhds K.one_mem] with k hk hkK
    refine ⟨hkK, fun x => ?_⟩
    by_cases hx : x ∈ K
    · exact hk x hx
    · have a1 : e x = 0 := by by_contra h; exact hx (hs x h)
      have a2 : e (k * x) = 0 := by by_contra h; exact hx ((K.mul_mem_cancel_left hkK).1 (hs _ h))
      rw [a1, a2]
  exact ⟨Kp, hop, hK.of_isClosed_subset (Kp.isClosed_of_isOpen hop) fun k hk => hk.1, fun k hk => hk.2⟩

end CompanionTheory.D.gk.RF
