import Development.WeilBound.ThetaLifts.LatticeBasics.ThetaBox
import Development.WeilBound.ThetaLifts.LatticeBasics.SecondFromFirstStatement

noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GroundTheory.Automorphic.GJMatrix GroundTheory.Global GlobalTheory.HeisSchA

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] {ψ : AddChar (AF F) ℂ}

variable (F) in

def epsF : AF F := mk 0 1

theorem epsF_mul (t : AF F) : epsF F * t = mk 0 (p2 t) := Prod.ext (zero_mul _) (one_mul _)

theorem epsF_sq : epsF F * epsF F = epsF F := epsF_mul _

theorem evI_epsF (t : AF F) : evI F (epsF F * t) = 0 := by
  rw [epsF_mul]; exact map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)

theorem epsF_of {t : AF F} (h : evI F t = 0) : epsF F * t = t := by
  rw [epsF_mul]
  exact Prod.ext ((InfiniteAdeleRing.ringEquiv_mixedSpace F).injective ((map_zero _).trans h.symm)) rfl

theorem level (hψ : Continuous ψ) {Φ : (κ → AF F) → ℂ} (h : Φ ∈ schA F κ) :
    ∀ᶠ w : (κ → AF F) × (κ → AF F) in 𝓝 0, schr ψ (epsF F • w) Φ = Φ := by
  rw [sch_eq, schwartzBruhatPi_eq_cosetSpanPi] at h
  induction h using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨f, J, b, rfl⟩ := hG
    have m := finiteTensor_mem fun i => cosetIndicator_mem_finiteSchwartzBruhat J (b i)
    have c := continuous_finPartPi (K := F) (ι := κ)
    have h1 : ∀ᶠ w : (κ → AF F) × (κ → AF F) in 𝓝 0, ∀ i, finPartPi w.1 i ∈ idealFiniteAdeles J :=
      eventually_all.2 fun i => ((continuous_apply i).comp (c.comp continuous_fst)).continuousAt.preimage_mem_nhds
        ((isOpen_idealFiniteAdeles J).mem_nhds (zero_mem _))
    have h2 : ∀ᶠ w : (κ → AF F) × (κ → AF F) in 𝓝 0, ∀ z ∈ tsupport (finiteTensor fun i => cosetIndicator J (b i)),
        finChar ψ (z ⬝ᵥ finPartPi w.2 + p2 ⅟(2 : AF F) * (finPartPi w.1 ⬝ᵥ finPartPi w.2)) = 1 :=
      m.2.isCompact.eventually_forall_of_forall_eventually fun z _ => by
        have := ((finChar_isLocallyConstant ψ hψ).comp_continuous (f := fun y : ((κ → AF F) × (κ → AF F)) × (κ → Af F) =>
          y.2 ⬝ᵥ finPartPi y.1.2 + p2 ⅟(2 : AF F) * (finPartPi y.1.1 ⬝ᵥ finPartPi y.1.2)) (by fun_prop)).eventually_eq (0, z)
        simpa [show finPartPi (0 : κ → AF F) = 0 from rfl] using this
    filter_upwards [h1, h2] with w h1 h2
    funext x
    have e1 : infPartPi (x + epsF F • w.1) = infPartPi x := funext fun i => by
      have := evI_epsF (w.1 i)
      exact (map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F) _ _).trans ((congrArg _ this).trans (add_zero _))
    have e2 : finiteTensor (fun i => cosetIndicator J (b i)) (finPartPi (x + epsF F • w.1)) =
        finiteTensor (fun i => cosetIndicator J (b i)) (finPartPi x) := Finset.prod_congr rfl fun i _ => by
      beta_reduce
      rw [cosetIndicator_apply, cosetIndicator_apply,
        show finPartPi (x + epsF F • w.1) i - b i = finPartPi x i - b i + finPartPi w.1 i from by
          rw [sub_add_eq_add_sub]; exact congrArg (finPartPi x i + · - b i) (one_mul _)]
      simp only [AddSubgroup.add_mem_cancel_right _ (h1 i)]
    simp only [schr, schwartzBruhatTensorPi, Prod.smul_fst, Prod.smul_snd, e1, e2]
    by_cases h0 : finiteTensor (fun i => cosetIndicator J (b i)) (finPartPi x) = 0
    · simp [h0]
    · rw [dotProduct_smul, dotProduct_smul, smul_dotProduct, smul_smul, epsF_sq, smul_eq_mul, smul_eq_mul, mul_left_comm ⅟(2 : AF F),
        ← mul_add, epsF_mul, ← finChar_apply, map_add, map_mul, RingHom.map_dotProduct, RingHom.map_dotProduct]
      exact (congrArg (· * _) (h2 _ (subset_tsupport _ h0))).trans (one_mul _)
  | zero => exact .of_forall fun w => funext fun x => mul_zero _
  | add G H _ _ hG hH =>
    filter_upwards [hG, hH] with w hG hH
    funext x
    exact (mul_add _ _ _).trans (congrArg₂ _ (congrFun hG x) (congrFun hH x))
  | smul c G _ hG =>
    filter_upwards [hG] with w hG
    funext x
    exact (mul_left_comm _ _ _).trans (congrArg _ (congrFun hG x))

theorem finite_values (hψ : IsStd ψ) {N : Set ((κ → AF F) × (κ → AF F))} (hN : N ∈ 𝓝 0) :
    ∃ s : Finset (κ → AF F), (∀ y ∈ s, ∀ i, evI F (y i) = 0) ∧ ∀ Ψ : (κ → AF F) → ℂ, (∀ w ∈ N, schr ψ (epsF F • w) Ψ = Ψ) →
      ∀ x : κ → AF F, At (evI F) x → (∀ y ∈ s, Ψ (x + y) = 0) → ∀ y : κ → AF F, (∀ i, evI F (y i) = 0) → Ψ (x + y) = 0 := by
  obtain ⟨ξ, hξ, e⟩ := std_eq hψ
  obtain ⟨N₁, h₁, N₂, h₂, hN⟩ := mem_nhds_prod_iff.1 hN
  have cm : Continuous fun a : Af F => (mk 0 a : AF F) := continuous_const.prodMk continuous_id
  have : ∀ᶠ a : Af F in 𝓝 0, ∀ i, (Pi.single i (mk 0 a) : κ → AF F) ∈ N₂ := eventually_all.2 fun i =>
    ((continuous_single i).comp cm).continuousAt.preimage_mem_nhds (by
      rwa [Function.comp_apply, show (mk 0 0 : AF F) = 0 from rfl, Pi.single_zero])
  obtain ⟨J, hJ⟩ := exists_idealFiniteAdeles_subset this
  have hC := (isCompact_univ_pi fun _ : κ => isCompact_idealFiniteAdeles (traceDualIdeal F J)).image
    (f := fun y i => (mk 0 (algebraMap F (Af F) ξ⁻¹ * y i) : AF F))
    (continuous_pi fun i => cm.comp (continuous_const.mul (continuous_apply i)))
  obtain ⟨s, hs, hc⟩ := hC.elim_nhds_subcover (fun t => {y | y - t ∈ N₁}) fun t _ =>
    (continuous_sub_right t).continuousAt.preimage_mem_nhds (by rwa [sub_self])
  have hs' : ∀ y ∈ s, ∀ i, evI F (y i) = 0 := fun y hy i => by
    obtain ⟨z, -, rfl⟩ := hs y hy
    exact map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)
  refine ⟨s, hs', fun Ψ hΨ x hx h0 y hy => by_contra fun hn => ?_⟩
  have hx0 : epsF F • x = 0 := hx _ (map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F))
  refine (fun hm => ?_ : y ∈ _ → False) (hc ⟨fun i => algebraMap F (Af F) ξ * p2 (y i), fun i _ => ?_, ?_⟩)
  · obtain ⟨t, ht, hty⟩ := Set.mem_iUnion₂.1 hm
    have := congrFun (hΨ (y - t, 0) (hN ⟨hty, mem_of_mem_nhds h₂⟩)) (x + t)
    have e : epsF F • (y - t) = y - t := funext fun i => by
      rw [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, mul_sub, epsF_of (hy i), epsF_of (hs' t ht i)]
    simp [schr, e, h0 t ht, hn] at this
  · refine (forall_finiteAdelicChar_mul_eq_one_iff J _).1 fun a ha => Circle.ext ?_
    have := congrFun (hΨ (0, Pi.single i (mk 0 a)) (hN ⟨mem_of_mem_nhds h₁, hJ ha i⟩)) (x + y)
    simp only [schr, Prod.smul_fst, Prod.smul_snd, smul_zero, zero_dotProduct, mul_zero, add_zero] at this
    rw [mul_eq_right₀ hn, dotProduct_smul, ← smul_dotProduct, smul_add, hx0, zero_add, dotProduct_single, e] at this
    refine Eq.trans (congrArg (fun z => ((adelicChar F z : Circle) : ℂ)) (Prod.ext ?_ ?_)) this
    · exact (mul_zero _).symm.trans (congrArg _ (mul_zero _).symm)
    · show a * (algebraMap F (Af F) ξ * p2 (y i)) = algebraMap F (Af F) ξ * (1 * p2 (y i) * a)
      ring
  · funext i
    beta_reduce
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hξ, map_one, one_mul, ← epsF_mul, epsF_of (hy i)]

theorem finLevel : FinLevel := by
  intro F E _ _ _ _ _ σ B m n A Y hB κ _ dd K hK Φ hΦ
  have lin : ∀ (k : G2 σ Y) (u : Matrix (Fin m) (Fin n ⊕ Fin n) (AE F E)),
      actB (cA σ) k (epsF F • u) = epsF F • actB (cA σ) k u := fun k u => Matrix.smul_mul _ _ _
  have : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI : ∀ {α β : Type} [Finite α] [Finite β], IsModuleTopology (AF F) (Matrix α β (AE F E)) :=
    inferInstanceAs (IsModuleTopology (AF F) (_ → _ → AE F E))
  have c : Continuous fun y : ((κ → AF F) × (κ → AF F)) × G2 σ Y => dd.e (actB (cA σ) y.2 (dd.e.symm y.1)) :=
    (IsModuleTopology.continuous_of_linearMap dd.e.toLinearMap).comp
      (((IsModuleTopology.continuous_of_linearMap dd.e.symm.toLinearMap).comp continuous_fst).matrix_mul
        (Units.continuous_val.comp (continuous_subtype_val.comp continuous_snd)).matrix_transpose)
  obtain ⟨s, hs, h⟩ := finite_values hB.std (hK.eventually_forall_of_forall_eventually
    (P := fun w k => schr B.ψ (epsF F • dd.e (actB (cA σ) k (dd.e.symm w))) Φ = Φ) fun k _ =>
      (c.tendsto' (0, k) 0 (by simp [actB])).eventually (level hB.std.1 hΦ))
  refine ⟨{u | epsF F • u = u ∧ ∀ k ∈ K, dd.rho B.ψ (actB (cA σ) k u) Φ = Φ}, fun u hu => ⟨fun i => ?_, fun i => ?_,
    fun k hk => ⟨by rw [← lin, hu.1], fun k' hk' => ?_⟩⟩, fun u hu => ?_, s, hs, fun Ψ hΨ => h Ψ fun w hw => ?_⟩
  · rw [← hu.1, map_smul]; exact evI_epsF _
  · rw [← hu.1, map_smul]; exact evI_epsF _
  · have := hu.2 _ (mul_mem hk' hk)
    simpa [actB, Matrix.mul_assoc] using this
  · simpa [actB] using hu.2 1 (one_mem _)
  · have := hΨ (epsF F • dd.e.symm w) ⟨by rw [smul_smul, epsF_sq], fun k hk => by
      rw [lin, Darboux.rho, map_smul]; exact hw k hk⟩
    rwa [Darboux.rho, map_smul, LinearEquiv.apply_symm_apply] at this

end GlobalTheory.ThK.Dbl

end
