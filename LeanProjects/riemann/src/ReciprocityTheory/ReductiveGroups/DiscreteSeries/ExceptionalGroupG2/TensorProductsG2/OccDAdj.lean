import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.OccDAdjB
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.StdGap
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.AnyDec
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.DataGenSubIrred
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.HasGelfandCharSigLam

noncomputable section

open Finset
open scoped Matrix

namespace ReciprocityTheory.ChartRestriction.DS.G2

variable {n : ℕ}

section Amb

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ D}

theorem adjB_K (dual : Bool) (hσ : IsURepOn (UJset ε) σ) {M : Submodule ℂ D}
    (hMK : ∀ k ∈ Kset ε, ∀ x ∈ M, ∃ y ∈ M, (y : H) = σ k x) {ps : (Fin n → D) →ₗ[ℂ] D}
    (hps3 : ∀ k ∈ Kset ε, ∀ f ∈ tensSub M, ∀ f' ∈ tensSub M,
      (fun c => ((f' c : D) : H)) = kDiag dual σ k (fun c => ((f c : D) : H)) →
      ((ps f' : D) : H) = σ k ((ps f : D) : H))
    {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) {x x'' : D} (hxx : (x'' : H) = σ k (x : H))
    {u : Fin n → D} (h : adjR ε M ps x u) {f' : Fin n → D} (hf' : f' ∈ tensSub M)
    (hff : (fun c => ((f' c : D) : H)) = kDiag dual σ k (fun c => ((u c : D) : H))) :
    adjR ε M ps x'' f' := by
  classical
  refine ⟨hf', fun c y hy => ?_⟩
  have hkh := adjB_star_Kset hk
  obtain ⟨y', hy'M, hy'⟩ := hMK kᴴ hkh y hy
  have hL : inner ℂ (f' c) y = ∑ d, (starRingEnd ℂ) (cond dual (star (k c d)) (k c d)) * inner ℂ (u d) y' := by
    rw [Submodule.coe_inner, show ((f' c : D) : H) = kDiag dual σ k (fun c => ((u c : D) : H)) c from congrFun hff c]
    simp only [kDiag, sum_inner, inner_smul_left]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [adjB_inner hσ hk, ← hy', ← Submodule.coe_inner]
  set g : Fin n → D := fun d => (starRingEnd ℂ) (cond dual (star (k c d)) (k c d)) • y'
  have hg : g ∈ tensSub M := tset_mem.2 fun d => M.smul_mem _ hy'M
  have hgk : (fun d => ((g d : D) : H)) =
      kDiag dual σ kᴴ (fun d => (((Pi.single c y : Fin n → D) d : D) : H)) := by
    funext d
    simp only [kDiag, g, Submodule.coe_smul]
    rw [Finset.sum_eq_single c (fun e _ he => by simp [he]) (by simp)]
    simp only [Pi.single_eq_same, hy']
    congr 1
    cases dual <;> simp [Matrix.conjTranspose_apply]
  have hps := hps3 kᴴ hkh _ (adjA_single_mem c hy) g hg hgk
  have hgsum : g = ∑ d, (starRingEnd ℂ) (cond dual (star (k c d)) (k c d)) • (Pi.single d y' : Fin n → D) := by
    funext e
    simp [g, Finset.sum_apply, Pi.single_apply]
  have hR : inner ℂ x'' (ps (Pi.single c y)) =
      ∑ d, (starRingEnd ℂ) (cond dual (star (k c d)) (k c d)) * (adjSg ε d * inner ℂ (u d) y') := by
    rw [Submodule.coe_inner, hxx, adjB_inner hσ hk, ← hps, ← Submodule.coe_inner, hgsum, map_sum, inner_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [map_smul, inner_smul_right, adjR_inv h d hy'M]
  rw [hL, hR, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  have := adjB_sgn hk dual c d
  linear_combination (-inner ℂ (u d) y') * this

theorem adjB_emb (dual : Bool) (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {lam lam' : Fin n → ℝ} {V V' : Submodule ℂ D} (hgap : StdGap ε lam) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v) (hgap' : StdGap ε lam')
    (hV' : IsKIrrHW ε E (lowK ε lam') V') (hc' : ∀ v ∈ V', casimir E v = (casVal lam' : ℂ) • v)
    (hVK' : ∀ k ∈ Kset ε, ∀ v ∈ V', ∃ w ∈ V', (w : H) = σ k v) {ps : (Fin n → D) →ₗ[ℂ] D}
    (hps1 : ∀ f ∈ tensSub (genSub E V), ps f ∈ genSub E V')
    (hps2 : ∀ a b, ∀ f ∈ tensSub (genSub E V), ps (tensF dual E a b f) = E a b (ps f))
    (hps3 : ∀ k ∈ Kset ε, ∀ f ∈ tensSub (genSub E V), ∀ f' ∈ tensSub (genSub E V),
      (fun c => ((f' c : D) : H)) = kDiag dual σ k (fun c => ((f c : D) : H)) →
      ((ps f' : D) : H) = σ k ((ps f : D) : H))
    (hne : ∃ f ∈ tensSub (genSub E V), ps f ≠ 0) :
    ∃ ι : D →ₗ[ℂ] (Fin n → D), IsGKEmb dual ε σ E (genSub E V) (genSub E V') ι := by
  classical
  have hU := isInfUnitary_of_isDerivedOn hσ hD
  have hME : ∀ a b, ∀ v ∈ genSub E V, E a b v ∈ genSub E V := fun a b v hv => closure_E_mem_genSub a b hv
  have hME' : ∀ a b, ∀ v ∈ genSub E V', E a b v ∈ genSub E V' := fun a b v hv => closure_E_mem_genSub a b hv
  have hMK : ∀ k ∈ Kset ε, ∀ x ∈ genSub E V, ∃ y ∈ genSub E V, (y : H) = σ k x :=
    fun k hk x hx => occD_genSub_K hσ hD hV.1 hV.2.1 hk hx
  have hM'K : ∀ k ∈ Kset ε, ∀ x ∈ genSub E V', ∃ y ∈ genSub E V', (y : H) = σ k x :=
    fun k hk x hx => occD_genSub_K hσ hD hV'.1 hV'.2.1 hk hx
  have hex : ∀ x ∈ genSub E V', ∃ u, adjR ε (genSub E V) ps x u := by
    intro x hx
    choose z hz hzr using fun c => adjA_rep dual hσ hD hgap hV hc hV'.1 hV'.2.1 hps2 hx c
    refine ⟨fun c => adjSg ε c • z c, tset_mem.2 fun c => Submodule.smul_mem _ _ (hz c), fun c y hy => ?_⟩
    rw [inner_smul_left, adjSg_conj, hzr c y hy]
  obtain ⟨ι, hι⟩ := adjR_linear hex
  have hEcl : ∀ a b, ∀ x ∈ genSub E V', ι (E a b x) = tensF dual E a b (ι x) := fun a b x hx =>
    adjR_unique (hι _ (hME' a b x hx)) (adjB_E dual hU hME hps2 (hι x hx) a b)
  have hKcl : ∀ k ∈ Kset ε, ∀ x ∈ genSub E V', ∀ x'' ∈ genSub E V', (x'' : H) = σ k (x : H) →
      (fun c => ((ι x'' c : D) : H)) = kDiag dual σ k (fun c => ((ι x c : D) : H)) := by
    intro k hk x hx x'' hx'' hxx
    choose w hw hwe using fun d => hMK k hk _ (tset_mem.1 (hι x hx).1 d)
    set f' : Fin n → D := fun c => ∑ d, (cond dual (star (k c d)) (k c d)) • w d
    have hf' : f' ∈ tensSub (genSub E V) :=
      tset_mem.2 fun c => Submodule.sum_mem _ fun d _ => Submodule.smul_mem _ _ (hw d)
    have hff : (fun c => ((f' c : D) : H)) = kDiag dual σ k (fun c => ((ι x c : D) : H)) := by
      funext c
      simp only [f', kDiag, Submodule.coe_sum, Submodule.coe_smul, hwe]
    rw [adjR_unique (hι x'' hx'') (adjB_K dual hσ hMK hps3 hk hxx (hι x hx) hf' hff)]
    exact hff
  refine ⟨ι, fun x hx => (hι x hx).1, ?_, hEcl, hKcl⟩
  intro x hx hx0
  set N : Submodule ℂ D := genSub E V' ⊓ LinearMap.ker ι
  have hNE : ∀ a b, ∀ y ∈ N, E a b y ∈ N := by
    intro a b y hy
    refine ⟨hME' a b y hy.1, ?_⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, hEcl a b y hy.1, LinearMap.mem_ker.1 hy.2, map_zero]
  have hNK : ∀ k ∈ Kset ε, ∀ y ∈ N, ∃ y' ∈ N, (y' : H) = σ k y := by
    intro k hk y hy
    obtain ⟨y', hy'M, hy'⟩ := hM'K k hk y hy.1
    refine ⟨y', ⟨hy'M, ?_⟩, hy'⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    have h1 := hKcl k hk y hy.1 y' hy'M hy'
    rw [LinearMap.mem_ker.1 hy.2] at h1
    funext c
    have h2 := congrFun h1 c
    simp only [kDiag, Pi.zero_apply, ZeroMemClass.coe_zero, map_zero, smul_zero, Finset.sum_const_zero] at h2
    exact Subtype.ext h2
  rcases data_genSub_irred hgap' hσ hD hV' hc' hVK' N inf_le_left hNE hNK with h | h
  · have : x ∈ N := ⟨hx, LinearMap.mem_ker.2 hx0⟩
    rw [h] at this
    exact (Submodule.mem_bot ℂ).1 this
  · exfalso
    obtain ⟨f₀, hf₀, hps0⟩ := hne
    have hm : ps f₀ ∈ N := h ▸ hps1 f₀ hf₀
    have hR := hι _ (hps1 f₀ hf₀)
    rw [LinearMap.mem_ker.1 hm.2] at hR
    have h0 : ∀ c, inner ℂ (ps f₀) (ps (Pi.single c (f₀ c))) = (0 : ℂ) := by
      intro c
      rw [adjR_inv hR c (tset_mem.1 hf₀ c)]
      simp
    apply hps0
    rw [← inner_self_eq_zero (𝕜 := ℂ)]
    calc inner ℂ (ps f₀) (ps f₀) = ∑ c, inner ℂ (ps f₀) (ps (Pi.single c (f₀ c))) := by
          rw [← inner_sum, ← map_sum, Finset.univ_sum_single]
      _ = 0 := Finset.sum_eq_zero fun c _ => h0 c

end Amb

section Psi

variable {ε : Fin n → Bool} {lam lam' : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)} {T' : S7.KType ε (lowK ε lam')}
  {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {Ψ' : Matrix (Fin n) (Fin n) ℂ → (T'.V →L[ℂ] T'.V)}
  {v₀ : T.V} {v₀' : T'.V}

theorem occAdj_emb (dual : Bool) (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0)
    (hgap' : StdGap ε lam') (hP' : IsPsiFor ε lam' T' Ψ') (hv₀' : v₀' ≠ 0)
    {ps : (Fin n → smD ε (rreg ε)) →ₗ[ℂ] smD ε (rreg ε)}
    (hps : occPsOK dual ε (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)) (genSub (smE ε (rreg ε)) (datumV ε Ψ' v₀')) ps)
    (hne : ∃ f ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)), ps f ≠ 0) :
    ∃ ι : smD ε (rreg ε) →ₗ[ℂ] (Fin n → smD ε (rreg ε)),
      IsGKEmb dual ε (rreg ε) (smE ε (rreg ε)) (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀))
        (genSub (smE ε (rreg ε)) (datumV ε Ψ' v₀')) ι := by
  have hσ := rreg_isURepOn ε
  exact adjB_emb dual hσ (isDerivedOn_smE hσ) hgap (datumV_isKIrrHW hP hv₀) (datumV_casimir hP v₀) hgap'
    (datumV_isKIrrHW hP' hv₀') (datumV_casimir hP' v₀') (datumV_kStable hP' v₀') hps.1 hps.2.1 hps.2.2 hne

end Psi

end ReciprocityTheory.ChartRestriction.DS.G2
