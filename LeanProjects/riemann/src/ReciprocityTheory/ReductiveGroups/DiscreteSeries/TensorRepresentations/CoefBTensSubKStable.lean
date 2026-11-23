import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.HidaSetting
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.TensorV
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirAlgebra.CasimirKKhwVec
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirAlgebra.MulMulSubMulMulEqAdd
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.CasimirGapAtNoncompactWeight
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.KUnitB
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.CoefAInnerEqZero

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section admitted

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {lam : Fin n → ℝ} {V : Submodule ℂ M}

theorem coefB_khw_le (hE : IsGlRep E) (hU : IsInfUnitary ε E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hgap : StdGap ε lam) (C : ℝ) :
    ∃ k : ℕ, ∀ w ∈ genSub E V, ∀ μ : Fin n → ℝ, IsKHWVec ε E μ w → casValK ε μ ≤ C →
      w ∈ layer ε E V k := by
  obtain ⟨hmono, h, hh, hbig⟩ := hgap
  refine ⟨⌈(C - casValK ε (lowK ε lam)) / (2 * (h - n + 1))⌉₊, fun w hw μ hμ hμC => ?_⟩
  obtain ⟨w₀, hw₀, -, m, ws, hsum, hws⟩ := k_highest_weight_layer_decomp hE hU hV hc hmono hh hbig hw hμ
  rw [hsum]
  refine Submodule.add_mem _ (layer_mono (Nat.zero_le _) (show w₀ ∈ layer ε E V 0 from hw₀))
    (Submodule.sum_mem _ fun j _ => ?_)
  by_cases h0 : ws j = 0
  · rw [h0]
    exact Submodule.zero_mem _
  obtain ⟨-, hpos, hle⟩ := (hws j).2 h0
  refine layer_mono ?_ (hws j).1
  have hj : ((j : ℕ) : ℝ) + 1 ≤ (C - casValK ε (lowK ε lam)) / (2 * (h - n + 1)) := by
    rw [le_div_iff₀ (mul_pos two_pos hpos)]
    linarith
  have := hj.trans (Nat.le_ceil _)
  exact_mod_cast this

theorem coefB_adm (hE : IsGlRep E) (hU : IsInfUnitary ε E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hgap : StdGap ε lam) (C : ℝ) :
    ∃ k : ℕ, ∀ y ∈ genSub E V, ∀ θ : ℝ, θ ≤ C → casimirK ε E y = (θ : ℂ) • y →
      y ∈ layer ε E V k := by
  obtain ⟨K, hK⟩ := coefB_khw_le hE hU hV hc hgap C
  refine ⟨K, fun y hy θ hθ hyθ => ?_⟩
  have hUk := isKUnitary_of_isInfUnitary hU
  obtain ⟨m, hm⟩ := exists_layer_of_mem_genSub hE hV.2.1 hy
  have hfm : FiniteDimensional ℂ (layer ε E V m) := finiteDimensional_layer hV.1 m
  set T : Submodule ℂ M := layer ε E V m ⊓ LinearMap.ker (casimirK ε E - (θ : ℂ) • 1) with hTdef
  have memT : ∀ x, x ∈ T ↔ x ∈ layer ε E V m ∧ casimirK ε E x = (θ : ℂ) • x := by
    intro x
    simp only [T, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
      Module.End.one_apply, sub_eq_zero]
  have hTd : FiniteDimensional ℂ T := Submodule.finiteDimensional_of_le inf_le_left
  have hTs : IsKStableSub ε E T := by
    intro a b hab x hx
    rw [memT] at hx ⊢
    refine ⟨layer_kStable hE hV.2.1 m a b hab x hx.1, ?_⟩
    have := congrArg (fun F : Module.End ℂ M => F x) (casimirK_comm ε hE a b hab)
    simp only [Module.End.mul_apply] at this
    rw [this, hx.2, map_smul]
  set T₀ : Submodule ℂ M := T ⊓ layer ε E V K
  have hT0d : FiniteDimensional ℂ T₀ := Submodule.finiteDimensional_of_le inf_le_left
  have hT0s : IsKStableSub ε E T₀ := fun a b hab x hx =>
    ⟨hTs a b hab x hx.1, layer_kStable hE hV.2.1 K a b hab x hx.2⟩
  have hyT : y ∈ T := (memT y).2 ⟨hm, hyθ⟩
  set r := y - T₀.starProjection y
  by_cases hr : r = 0
  · have : y = T₀.starProjection y := sub_eq_zero.1 hr
    rw [this]
    exact (Submodule.starProjection_apply_mem T₀ y).2
  exfalso
  set S : Submodule ℂ M := T ⊓ T₀ᗮ
  have hrS : r ∈ S := ⟨T.sub_mem hyT (Submodule.starProjection_apply_mem T₀ y).1,
    Submodule.sub_starProjection_mem_orthogonal y⟩
  have hSd : FiniteDimensional ℂ S := Submodule.finiteDimensional_of_le inf_le_left
  have hSs : IsKStableSub ε E S := fun a b hab x hx =>
    ⟨hTs a b hab x hx.1, orthogonal_kStable hUk hT0s a b hab x hx.2⟩
  have hne : S ≠ ⊥ := by
    intro h
    have := hrS
    rw [h, Submodule.mem_bot] at this
    exact hr this
  obtain ⟨w, hwS, hw0, μ, hμ⟩ := exists_khw hE hUk hSd hSs hne
  have hwT := (memT w).1 hwS.1
  have h1 := casimirK_khwVec ε hE hμ
  rw [hwT.2] at h1
  have h2 : (θ : ℂ) = ((nsq (μ + rhoC ε) - nsq (rhoC ε) : ℝ) : ℂ) := smul_left_injective ℂ hw0 h1
  have h3 : casValK ε μ = θ := by
    have := Complex.ofReal_injective h2
    rw [this]; rfl
  have hwK := hK w (layer_le_genSub m hwT.1) μ hμ (h3 ▸ hθ)
  have hwT0 : w ∈ T₀ := ⟨hwS.1, hwK⟩
  have := Submodule.inner_right_of_mem_orthogonal hwT0 hwS.2
  exact hw0 (inner_self_eq_zero.1 this)

end admitted

section Tr

variable {D : Type*} [NormedAddCommGroup D] [InnerProductSpace ℂ D]

def coefTr (A : Module.End ℂ (Fin n → D)) : Module.End ℂ (WithLp 2 (Fin n → D)) :=
  (WithLp.linearEquiv 2 ℂ (Fin n → D)).symm.toLinearMap ∘ₗ A ∘ₗ
    (WithLp.linearEquiv 2 ℂ (Fin n → D)).toLinearMap

theorem coefTr_apply (A : Module.End ℂ (Fin n → D)) (u : WithLp 2 (Fin n → D)) :
    coefTr A u = WithLp.toLp 2 (A (WithLp.ofLp u)) := rfl

theorem coefTr_casimirK (ε : Fin n → Bool) (A : Fin n → Fin n → Module.End ℂ (Fin n → D)) :
    casimirK ε (fun a b => coefTr (A a b)) = coefTr (casimirK ε A) := by
  refine LinearMap.ext fun u => ?_
  simp only [casimirK, coefTr, LinearMap.sum_apply, Module.End.mul_apply,
    LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, map_sum]

theorem coefB_sum_ite_left (a : Fin n) (x : D) (v : Fin n → D) :
    ∑ c, inner ℂ (if c = a then x else 0) (v c) = inner ℂ x (v a) := by
  rw [Finset.sum_eq_single a]
  · simp
  · intro c _ hc
    simp [hc]
  · simp

theorem coefB_sum_ite_right (a : Fin n) (x : D) (v : Fin n → D) :
    ∑ c, inner ℂ (v c) (if c = a then x else 0) = inner ℂ (v a) x := by
  rw [Finset.sum_eq_single a]
  · simp
  · intro c _ hc
    simp [hc]
  · simp

private lemma tensF_apply {M : Type*} [AddCommGroup M] [Module ℂ M] (dual : Bool)
    (E : Fin n → Fin n → Module.End ℂ M) (a b c : Fin n) (u : Fin n → M) :
    tensF dual E a b u c =
      E a b (u c) + cond dual (-(if c = b then u a else 0)) (if c = a then u b else 0) := by
  cases dual
  · by_cases h : c = a <;> simp [tensF, tensV, coordV, h]
  · by_cases h : c = b <;> simp [tensF, tensVd, coordV, h, sub_eq_add_neg]

theorem coefB_isKUnitary (dual : Bool) {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ D}
    (hU : IsKUnitary ε E) : IsKUnitary ε (fun a b => coefTr (tensF dual E a b)) := by
  intro a b hab x y
  cases dual <;>
  simp only [PiLp.inner_apply, coefTr_apply, PiLp.toLp_apply, tensF_apply, cond_false,
    cond_true, inner_add_left, inner_add_right, inner_neg_left, inner_neg_right,
    Finset.sum_add_distrib, Finset.sum_neg_distrib, hU a b hab, coefB_sum_ite_left,
    coefB_sum_ite_right]

end Tr

section Exist

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ D}

theorem coefB_tensSub_kStable (dual : Bool) {S : Submodule ℂ D} (hS : IsKStableSub ε E S) :
    IsKStableSub ε (tensF dual E) (tensSub S) := by
  intro a b hab v hv
  have hv' : ∀ d, v d ∈ S := fun d => (Submodule.mem_pi.mp hv) d (Set.mem_univ d)
  refine Submodule.mem_pi.mpr fun c _ => ?_
  rw [tensF_apply]
  refine Submodule.add_mem _ (hS a b hab _ (hv' c)) ?_
  cases dual
  · by_cases h : c = a <;> simp [h, hv']
  · by_cases h : c = b <;> simp [h, hv']

theorem coefB_casimirK_mem {X : Type*} [AddCommGroup X] [Module ℂ X]
    {A : Fin n → Fin n → Module.End ℂ X} {S : Submodule ℂ X} (hS : IsKStableSub ε A S) {x : X}
    (hx : x ∈ S) : casimirK ε A x ∈ S := by
  simp only [casimirK, LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b hb => ?_
  have hb' : ε b = ε a := (Finset.mem_filter.mp hb).2
  exact hS a b hb'.symm _ (hS b a hb' _ hx)

theorem coefB_locFin (hE : IsGlRep E) {V : Submodule ℂ D} (hVf : FiniteDimensional ℂ V)
    (hVk : IsKStableSub ε E V) : CoefLocFin (casimirK ε E) (genSub E V) := by
  intro y hy
  obtain ⟨m, hm⟩ := exists_layer_of_mem_genSub hE hVk hy
  exact ⟨layer ε E V m, finiteDimensional_layer hVf m, layer_le_genSub m,
    fun x hx => casimirK_mem_of_kStable (layer_kStable hE hVk m) hx, hm⟩

theorem coefB_ι_casimirK (dual : Bool) {S' : Submodule ℂ D} {ι : D →ₗ[ℂ] (Fin n → D)}
    (hS' : ∀ a b, ∀ v ∈ S', E a b v ∈ S')
    (hι : ∀ a b, ∀ x ∈ S', ι (E a b x) = tensF dual E a b (ι x)) {y : D} (hy : y ∈ S') :
    ι (casimirK ε E y) = casimirK ε (tensF dual E) (ι y) := by
  simp only [casimirK, LinearMap.sum_apply, map_sum, Module.End.mul_apply]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [hι a b _ (hS' b a y hy), hι b a y hy]

theorem coefB_toSum_exists (dual : Bool) (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {lam' : Fin n → ℝ} {V V' : Submodule ℂ D} (hVf : FiniteDimensional ℂ V)
    (hVk : IsKStableSub ε E V) (hgap' : StdGap ε lam') (hV' : IsKIrrHW ε E (lowK ε lam') V')
    (hc' : ∀ v ∈ V', casimir E v = (casVal lam' : ℂ) • v) {ι : D →ₗ[ℂ] (Fin n → D)}
    (hι : IsGKEmb dual ε σ E (genSub E V) (genSub E V') ι) :
    ∀ f ∈ tensSub (genSub E V), ∃ z ∈ genSub E V', ∀ y ∈ genSub E V',
      inner ℂ z y = ∑ c, inner ℂ (f c) (ι y c) := by
  intro f hf
  have hE := hD.glRep
  have hU := isInfUnitary_of_isDerivedOn hσ hD
  have hUk := isKUnitary_of_isInfUnitary hU
  have hf' : ∀ c, ∃ m, f c ∈ layer ε E V m := fun c =>
    exists_layer_of_mem_genSub hE hVk ((Submodule.mem_pi.1 hf) c (Set.mem_univ c))
  choose m hm using hf'
  set k := Finset.univ.sup m
  have hk : ∀ c, f c ∈ layer ε E V k := fun c =>
    layer_mono (Finset.le_sup (f := m) (Finset.mem_univ c)) (hm c)
  set e := WithLp.linearEquiv 2 ℂ (Fin n → D)
  set TY := casimirK ε (fun a b => coefTr (tensF dual E a b))
  have hTY : ∀ x y, inner ℂ (TY x) y = inner ℂ x (TY y) :=
    casimirK_inner_symm (coefB_isKUnitary dual hUk)
  have hTYa : ∀ u, TY (WithLp.toLp 2 u) = WithLp.toLp 2 (casimirK ε (tensF dual E) u) := by
    intro u
    simp only [TY, coefTr_casimirK, coefTr_apply]
  set Lk := tensSub (n := n) (layer ε E V k)
  set L : Submodule ℂ (WithLp 2 (Fin n → D)) := Lk.comap e.toLinearMap
  have hLd : FiniteDimensional ℂ L := by
    set P : (Fin n → layer ε E V k) →ₗ[ℂ] WithLp 2 (Fin n → D) :=
      e.symm.toLinearMap ∘ₗ LinearMap.pi (fun c => (layer ε E V k).subtype ∘ₗ LinearMap.proj c)
    have : FiniteDimensional ℂ (layer ε E V k) := finiteDimensional_layer hVf k
    have hle : L ≤ LinearMap.range P := by
      intro u hu
      have hu' : ∀ c, WithLp.ofLp u c ∈ layer ε E V k := fun c =>
        (Submodule.mem_pi.1 hu) c (Set.mem_univ c)
      exact ⟨fun c => ⟨WithLp.ofLp u c, hu' c⟩, rfl⟩
    exact Submodule.finiteDimensional_of_le hle
  have hLs : ∀ x ∈ L, TY x ∈ L := by
    intro x hx
    have : TY x = WithLp.toLp 2 (casimirK ε (tensF dual E) (WithLp.ofLp x)) := hTYa _
    have h2 : casimirK ε (tensF dual E) (WithLp.ofLp x) ∈ Lk :=
      coefB_casimirK_mem (coefB_tensSub_kStable dual (layer_kStable hE hVk k)) hx
    show WithLp.ofLp (TY x) ∈ Lk
    rw [this]
    exact h2
  obtain ⟨C, hC⟩ := coefA_high hTY hLd hLs
  obtain ⟨K, hK⟩ := coefB_adm hE hU hV' hc' hgap' C
  set ℓ : D →ₗ[ℂ] ℂ := (innerₛₗ ℂ (WithLp.toLp 2 f)).comp (e.symm.toLinearMap ∘ₗ ι)
  have hℓ : ∀ y, ℓ y = ∑ c, inner ℂ (f c) (ι y c) := by
    intro y
    show inner ℂ (WithLp.toLp 2 f) (WithLp.toLp 2 (ι y)) = _
    rw [PiLp.inner_apply]
  have hfL : WithLp.toLp 2 f ∈ L := Submodule.mem_pi.2 fun c _ => hk c
  have hTsym : ∀ x y, inner ℂ (casimirK ε E x) y = inner ℂ x (casimirK ε E y) :=
    casimirK_inner_symm hUk
  obtain ⟨z, hzM, hz⟩ := coefA_toSum hTsym (coefB_locFin hE hV'.1 hV'.2.1) ℓ C
    (finiteDimensional_layer hV'.1 K) (layer_le_genSub K) (fun y hy θ hθ hyθ => hK y hy θ hθ hyθ)
    (fun y hy θ hθ hyθ => by
      refine hC _ hfL (WithLp.toLp 2 (ι y)) θ hθ ?_
      rw [hTYa, ← coefB_ι_casimirK dual (fun a b v hv => closure_E_mem_genSub a b hv) hι.2.2.1 hy,
        hyθ, map_smul]
      rfl)
  exact ⟨z, hzM, fun y hy => by rw [hz y hy, hℓ]⟩

theorem coefB_ofSum_exists (dual : Bool) (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {lam' : Fin n → ℝ} {V V' : Submodule ℂ D} (hgap' : StdGap ε lam')
    (hV' : IsKIrrHW ε E (lowK ε lam') V')
    (hc' : ∀ v ∈ V', casimir E v = (casVal lam' : ℂ) • v) {ι : D →ₗ[ℂ] (Fin n → D)}
    (hι : IsGKEmb dual ε σ E (genSub E V) (genSub E V') ι) :
    ∀ z ∈ genSub E V', ∃ f ∈ tensSub (genSub E V), ∀ y ∈ genSub E V',
      inner ℂ z y = ∑ c, inner ℂ (f c) (ι y c) := by
  intro z hz
  have hE := hD.glRep
  have hU := isInfUnitary_of_isDerivedOn hσ hD
  have hUk := isKUnitary_of_isInfUnitary hU
  set e := WithLp.linearEquiv 2 ℂ (Fin n → D)
  set TY := casimirK ε (fun a b => coefTr (tensF dual E a b))
  have hTY : ∀ x y, inner ℂ (TY x) y = inner ℂ x (TY y) :=
    casimirK_inner_symm (coefB_isKUnitary dual hUk)
  have hTYa : ∀ u, TY (WithLp.toLp 2 u) = WithLp.toLp 2 (casimirK ε (tensF dual E) u) := by
    intro u
    simp only [TY, coefTr_casimirK, coefTr_apply]
  have hTsym : ∀ x y, inner ℂ (casimirK ε E x) y = inner ℂ x (casimirK ε E y) :=
    casimirK_inner_symm hUk
  set ιY : D →ₗ[ℂ] WithLp 2 (Fin n → D) := e.symm.toLinearMap ∘ₗ ι
  have hιT : ∀ y ∈ genSub E V', ιY (casimirK ε E y) = TY (ιY y) := by
    intro y hy
    show WithLp.toLp 2 (ι (casimirK ε E y)) = TY (WithLp.toLp 2 (ι y))
    rw [hTYa, coefB_ι_casimirK dual (fun a b v hv => closure_E_mem_genSub a b hv) hι.2.2.1 hy]
  have hinj : ∀ y ∈ genSub E V', ιY y = 0 → y = 0 := by
    intro y hy h0
    refine hι.2.1 y hy ?_
    have := congrArg WithLp.ofLp h0
    exact this
  have hfin : ∀ θ : ℝ, ∃ Z : Submodule ℂ D, FiniteDimensional ℂ Z ∧
      ∀ y ∈ genSub E V', casimirK ε E y = (θ : ℂ) • y → y ∈ Z := by
    intro θ
    obtain ⟨K, hK⟩ := coefB_adm hE hU hV' hc' hgap' θ
    exact ⟨layer ε E V' K, finiteDimensional_layer hV'.1 K, fun y hy hyθ => hK y hy θ le_rfl hyθ⟩
  obtain ⟨f, hfM, hf⟩ := coefA_ofSum hTsym hTY (coefB_locFin hE hV'.1 hV'.2.1) ιY hιT hinj hfin z hz
  obtain ⟨y₀, hy₀, rfl⟩ := hfM
  refine ⟨ι y₀, hι.1 y₀ hy₀, fun y hy => ?_⟩
  rw [← hf y hy, PiLp.inner_apply]
  rfl

end Exist

end ReciprocityTheory.ChartRestriction.DS
