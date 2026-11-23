import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalGermIntegrallyClosed
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StZariskiAnalyticNormality
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StRueckertNullstellensatz
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.OsgoodSeparate
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Topology Filter

noncomputable section

namespace NormalGermIntegrallyClosed

theorem analyticAt_of_differentiableOn {σ : Type} [Fintype σ] {N : Set (σ → ℂ)} {f : (σ → ℂ) → ℂ}
    (hN : IsOpen N) (hf : DifferentiableOn ℂ f N) {z : σ → ℂ} (hz : z ∈ N) : AnalyticAt ℂ f z := by
  let L : (Fin (Fintype.card σ) → ℂ) ≃L[ℂ] (σ → ℂ) :=
    (LinearEquiv.funCongrLeft ℂ ℂ (Fintype.equivFin σ)).toContinuousLinearEquiv
  have hO : IsOpen (L ⁻¹' N) := hN.preimage L.continuous
  have hg : DifferentiableOn ℂ (f ∘ L) (L ⁻¹' N) :=
    hf.comp L.differentiable.differentiableOn fun x hx => hx
  have hA : AnalyticOnNhd ℂ (f ∘ L) (L ⁻¹' N) := by
    refine analyticOnNhd_of_continuousOn_of_separately hO hg.continuousOn fun x hx i => ?_
    have h1 : DifferentiableAt ℂ (f ∘ L) (Function.update x i (x i)) := by
      rw [Function.update_eq_self]
      exact hg.differentiableAt (hO.mem_nhds hx)
    exact h1.comp (x i) (hasFDerivAt_update x (x i)).differentiableAt
  have hz' : L.symm z ∈ L ⁻¹' N := by simpa using hz
  have h2 := (hA _ hz').comp ((L.symm : (σ → ℂ) →L[ℂ] (Fin (Fintype.card σ) → ℂ)).analyticAt z)
  simpa [Function.comp_def] using h2

def anFun {σ : Type} [Fintype σ] (w : σ → ℂ) : Subring ((σ → ℂ) → ℂ) where
  carrier := {f | AnalyticAt ℂ f w}
  mul_mem' := fun hf hg => hf.mul hg
  one_mem' := analyticAt_const
  add_mem' := fun hf hg => hf.add hg
  zero_mem' := analyticAt_const
  neg_mem' := fun hf => hf.neg

def toGerm {σ : Type} [Fintype σ] (w : σ → ℂ) : anFun w →+* holGerms w :=
  ((Germ.coeRingHom (𝓝 w)).comp (anFun w).subtype).codRestrict (holGerms w) fun u => ⟨u.1, u.2, rfl⟩

theorem toGerm_surjective {σ : Type} [Fintype σ] (w : σ → ℂ) : Function.Surjective (toGerm w) := by
  rintro ⟨φ, f, hf, rfl⟩
  exact ⟨⟨f, hf⟩, rfl⟩

theorem toGerm_eq_iff {σ : Type} [Fintype σ] {w : σ → ℂ} {u v : anFun w} :
    toGerm w u = toGerm w v ↔ (u : (σ → ℂ) → ℂ) =ᶠ[𝓝 w] v := by
  rw [Subtype.ext_iff]
  exact Germ.coe_eq

theorem vanish_of_mem_map {σ : Type} [Fintype σ] {I : Ideal (MvPolynomial σ ℂ)} {w : σ → ℂ} {u : anFun w}
    (hu : toGerm w u ∈ I.map (polyGerm w)) :
    ∀ᶠ z in 𝓝[zeroSetIn I] w, (u : (σ → ℂ) → ℂ) z = 0 := by
  have key : ∀ x, x ∈ Submodule.span (holGerms w) (polyGerm w '' (I : Set (MvPolynomial σ ℂ))) →
      ∃ v : anFun w, toGerm w v = x ∧ ∀ᶠ z in 𝓝[zeroSetIn I] w, (v : (σ → ℂ) → ℂ) z = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨q, hq, rfl⟩ := hx
      exact ⟨⟨fun z => eval z q, analyticAt_eval_polynomial w q⟩, rfl,
        eventually_nhdsWithin_of_forall fun z hz => hz q hq⟩
    | zero => exact ⟨0, map_zero _, Eventually.of_forall fun z => by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨u, rfl, hu⟩ := hx
      obtain ⟨v, rfl, hv⟩ := hy
      exact ⟨u + v, map_add _ _ _, by filter_upwards [hu, hv] with z h1 h2; simp [h1, h2]⟩
    | smul c x _ hx =>
      obtain ⟨v, rfl, hv⟩ := hx
      obtain ⟨b, rfl⟩ := toGerm_surjective w c
      exact ⟨b * v, by rw [map_mul, smul_eq_mul], by filter_upwards [hv] with z h; simp [h]⟩
  obtain ⟨v, hv, hv0⟩ := key _ hu
  have he : (u : (σ → ℂ) → ℂ) =ᶠ[𝓝 w] v := toGerm_eq_iff.1 hv.symm
  filter_upwards [nhdsWithin_le_nhds he, hv0] with z h1 h2
  rw [h1, h2]

theorem exists_eq_mul_of_integral_relation {S : Type*} [CommRing S] [IsDomain S] [IsIntegrallyClosed S]
    {d : ℕ} (f g : S) (a : Fin d → S) (hg : g ≠ 0)
    (hrel : f ^ d + ∑ j, a j * f ^ (j : ℕ) * g ^ (d - (j : ℕ)) = 0) : ∃ y, f = g * y := by
  let K := FractionRing S
  have hinj : Function.Injective (algebraMap S K) := IsFractionRing.injective S K
  have hrelK : algebraMap S K f ^ d + ∑ j, algebraMap S K (a j) * algebraMap S K f ^ (j : ℕ) *
      algebraMap S K g ^ (d - (j : ℕ)) = 0 := by
    have h2 := congrArg (algebraMap S K) hrel
    simp only [map_add, map_sum, map_mul, map_pow, map_zero] at h2
    exact h2
  have hg0 : algebraMap S K g ≠ 0 := fun h0 => hg (hinj (by rw [h0, map_zero]))
  generalize hfK : algebraMap S K f = fK at hrelK
  generalize hgK : algebraMap S K g = gK at hrelK hg0
  have hint : IsIntegral S (fK / gK) := by
    refine ⟨Polynomial.X ^ d + ∑ j : Fin d, Polynomial.C (a j) * Polynomial.X ^ (j : ℕ),
      Polynomial.monic_X_pow_add (Polynomial.degree_sum_fin_lt _), ?_⟩
    have hterm : ∀ j : Fin d, algebraMap S K (a j) * (fK / gK) ^ (j : ℕ) =
        algebraMap S K (a j) * fK ^ (j : ℕ) * gK ^ (d - (j : ℕ)) / gK ^ d := by
      intro j
      rw [eq_div_iff (pow_ne_zero _ hg0), div_pow,
        show gK ^ d = gK ^ (j : ℕ) * gK ^ (d - (j : ℕ)) by rw [← pow_add, Nat.add_sub_cancel' j.2.le]]
      have hj : gK ^ (j : ℕ) ≠ 0 := pow_ne_zero _ hg0
      rw [show algebraMap S K (a j) * (fK ^ (j : ℕ) / gK ^ (j : ℕ)) * (gK ^ (j : ℕ) * gK ^ (d - (j : ℕ))) =
          algebraMap S K (a j) * fK ^ (j : ℕ) * gK ^ (d - (j : ℕ)) * (gK ^ (j : ℕ) / gK ^ (j : ℕ)) by ring,
        div_self hj, mul_one]
    simp only [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finsetSum,
      Polynomial.eval₂_mul, Polynomial.eval₂_C]
    rw [Finset.sum_congr rfl fun j _ => hterm j, div_pow, ← Finset.sum_div, ← add_div, hrelK, zero_div]
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
  refine ⟨y, hinj ?_⟩
  rw [map_mul, hy, hfK, hgK, mul_div_assoc', eq_div_iff hg0, mul_comm]

theorem proof (hRueckert : RueckertNullstellensatz.Statement)
    (hZariski : ZariskiAnalyticNormality.Statement) : NormalGermIntegrallyClosed.Statement := by
  intro σ _ I w N F G d a hI hIc hw hN hwN hF hG ha hGnz hrel
  have hFa : AnalyticAt ℂ F w := analyticAt_of_differentiableOn hN hF hwN
  have hGa : AnalyticAt ℂ G w := analyticAt_of_differentiableOn hN hG hwN
  have haa : ∀ j, AnalyticAt ℂ (a j) w := fun j => analyticAt_of_differentiableOn hN (ha j) hwN

  obtain ⟨k, p, hp⟩ := Submodule.fg_iff_exists_fin_generating_family.1 (IsNoetherian.noetherian I)
  have hpI : ∀ i, p i ∈ I := fun i => hp ▸ Submodule.subset_span ⟨i, rfl⟩
  have hZp : ∀ z, (∀ i, eval z (p i) = 0) → z ∈ zeroSetIn I := by
    intro z hz q hq
    have hle : I ≤ RingHom.ker (eval z) := by
      rw [← hp]
      exact Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hz i)
    exact RingHom.mem_ker.1 (hle hq)

  obtain ⟨hJ, hJc⟩ := hZariski σ I w hI hIc hw
  let J := I.map (polyGerm w)
  have : J.IsPrime := hJ
  let S := holGerms w ⧸ J
  have : IsIntegrallyClosed S := hJc
  let π : anFun w →+* S := (Ideal.Quotient.mk J).comp (toGerm w)
  have hπ0 : ∀ u : anFun w, π u = 0 → ∀ᶠ z in 𝓝[zeroSetIn I] w, (u : (σ → ℂ) → ℂ) z = 0 :=
    fun u hu => vanish_of_mem_map (Ideal.Quotient.eq_zero_iff_mem.1 hu)
  have hπpoly : ∀ q ∈ I, π ⟨fun z => eval z q, analyticAt_eval_polynomial w q⟩ = 0 := fun q hq =>
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ hq)
  have hπeq : ∀ u v : anFun w, (u : (σ → ℂ) → ℂ) =ᶠ[𝓝 w] v → π u = π v := fun u v h => by
    simp only [π, RingHom.comp_apply, toGerm_eq_iff.2 h]

  let FA : anFun w := ⟨F, hFa⟩
  let GA : anFun w := ⟨G, hGa⟩
  let aA : Fin d → anFun w := fun j => ⟨a j, haa j⟩
  let PA : anFun w := FA ^ d + ∑ j, aA j * FA ^ (j : ℕ) * GA ^ (d - (j : ℕ))
  have hPA : ∀ z, (PA : (σ → ℂ) → ℂ) z =
      F z ^ d + ∑ j, a j z * F z ^ (j : ℕ) * G z ^ (d - (j : ℕ)) := by
    intro z
    simp [PA, FA, GA, aA, Finset.sum_apply]

  have hGS : π GA ≠ 0 := by
    intro h
    exact hGnz (eventually_nhdsWithin_iff.1 (hπ0 GA h))

  have hvan : ∀ᶠ z in 𝓝 w, (∀ i, eval z (p i) = 0) → (PA : (σ → ℂ) → ℂ) z * G z = 0 := by
    filter_upwards [hN.mem_nhds hwN] with z hzN hz
    by_cases hG0 : G z = 0
    · rw [hG0, mul_zero]
    · rw [hPA, hrel z ⟨⟨hZp z hz, hzN⟩, hG0⟩, zero_mul]
  obtain ⟨m, h, hm, hh, hgm⟩ := hRueckert σ w k (fun i z => eval z (p i))
    (fun z => (PA : (σ → ℂ) → ℂ) z * G z) (fun i => analyticAt_eval_polynomial w (p i))
    (PA.2.mul hGa) hvan
  let hA : Fin k → anFun w := fun i => ⟨h i, hh i⟩
  let pA : Fin k → anFun w := fun i => ⟨fun z => eval z (p i), analyticAt_eval_polynomial w (p i)⟩
  have hprod : π ((PA * GA) ^ m) = π (∑ i, hA i * pA i) := by
    apply hπeq
    filter_upwards [hgm] with z hz
    simpa [hA, pA, GA, Finset.sum_apply, mul_pow] using hz
  have hPS : π PA = 0 := by
    have h1 : (π PA * π GA) ^ m = 0 := by
      rw [← map_mul, ← map_pow, hprod, map_sum]
      exact Finset.sum_eq_zero fun i _ => by rw [map_mul, hπpoly _ (hpI i), mul_zero]
    exact (mul_eq_zero.1 ((pow_eq_zero_iff (Nat.pos_iff_ne_zero.1 hm)).1 h1)).resolve_right hGS

  have : IsDomain S := Ideal.Quotient.isDomain J
  obtain ⟨y, hy⟩ := exists_eq_mul_of_integral_relation (π FA) (π GA) (fun j => π (aA j)) hGS (by
    rw [← hPS]
    simp only [PA, map_add, map_sum, map_mul, map_pow])
  obtain ⟨φ, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨HA, rfl⟩ := toGerm_surjective w φ
  have hdiff : π (FA - GA * HA) = 0 := by
    rw [map_sub, map_mul, hy]
    exact sub_self _
  have hv := eventually_nhdsWithin_iff.1 (hπ0 _ hdiff)
  obtain ⟨V, hV, hVo, hwV⟩ := eventually_nhds_iff.1 (hv.and HA.2.eventually_analyticAt)
  refine ⟨V, hVo, hwV, HA, fun z hz => (hV z hz).2.differentiableAt.differentiableWithinAt, ?_⟩
  rintro z ⟨hzZ, hzV⟩
  have h3 := (hV z hzV).1 hzZ
  change F z - G z * (HA : (σ → ℂ) → ℂ) z = 0 at h3
  exact sub_eq_zero.1 h3

end NormalGermIntegrallyClosed

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
