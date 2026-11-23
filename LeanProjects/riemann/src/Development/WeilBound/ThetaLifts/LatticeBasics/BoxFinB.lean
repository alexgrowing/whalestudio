import Mathlib
import Development.WeilBound.ThetaLifts.LatticeBasics.BoxFinA

noncomputable section

namespace GlobalTheory.ThK.Dbl.Box

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl.Dense

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] {ψ : AddChar (AF F) ℂ}

def nf (z : κ → AF F) : κ → mixedEmbedding.mixedSpace F := fun i => evI F (z i)

def fn (z : κ → AF F) : κ → Af F := fun i => (z i).2

omit [Fintype κ] in
theorem pt_self (z : κ → AF F) : pt (nf z) (fn z) = z :=
  funext fun i => Prod.ext ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm_apply_apply _) rfl

theorem nf_pt (x : κ → mixedEmbedding.mixedSpace F) (y : κ → Af F) : nf (pt x y) = x := evI_pt x y

omit [Fintype κ] in
theorem nf_add (z z' : κ → AF F) : nf (z + z') = nf z + nf z' := funext fun _ => evI_add _ _

def DP (a : κ → mixedEmbedding.mixedSpace F) (L : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ) (Φ : (κ → AF F) → ℂ) :
    (κ → AF F) → ℂ :=
  fun z => fderiv ℝ (fun x => Φ (pt x (fn z))) (nf z) a + (-(2 * Real.pi * Complex.I) * (L (nf z) : ℂ)) * Φ z

def D (w : (κ → AF F) × (κ → AF F)) : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ := DP (nf w.1) (linForm (nf w.2))

theorem linForm_add (b b' : κ → mixedEmbedding.mixedSpace F) : linForm (b + b') = linForm b + linForm b' := by
  ext y
  simp only [ContinuousLinearMap.add_apply, linForm_apply, Pi.add_apply, mul_add, Finset.sum_add_distrib, map_add]

theorem DP_add_left (a a' L L') (Φ : (κ → AF F) → ℂ) : DP (a + a') (L + L') Φ = DP a L Φ + DP a' L' Φ := by
  funext z
  simp only [DP, map_add, ContinuousLinearMap.add_apply, Pi.add_apply]
  push_cast
  ring

theorem DP_smul_left (t : ℝ) (a L) (Φ : (κ → AF F) → ℂ) : DP (t • a) (t • L) Φ = (t : ℂ) • DP a L Φ := by
  funext z
  simp only [DP, map_smul, ContinuousLinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, Complex.real_smul]
  push_cast
  ring

theorem D_add_left (w w') (Φ : (κ → AF F) → ℂ) : D (w + w') Φ = D w Φ + D w' Φ := by
  rw [D, Prod.fst_add, Prod.snd_add, nf_add, nf_add, linForm_add, DP_add_left]; rfl

theorem slice {Φ : (κ → AF F) → ℂ} (h : Φ ∈ schA F κ) (y : κ → Af F) : ∃ f : SInf F κ, ∀ x, Φ (pt x y) = f x := by
  induction h using Submodule.span_induction with
  | mem Φ h => obtain ⟨f, g, -, rfl⟩ := h; exact ⟨g y • f, fun x => by rw [pureA_pt, mul_comm]; rfl⟩
  | zero => exact ⟨0, fun _ => rfl⟩
  | add _ _ _ _ h h' => obtain ⟨f, e⟩ := h; obtain ⟨f', e'⟩ := h'; exact ⟨f + f', fun x => by rw [Pi.add_apply, e, e']; rfl⟩
  | smul c _ _ h => obtain ⟨f, e⟩ := h; exact ⟨c • f, fun x => by rw [Pi.smul_apply, e]; rfl⟩

theorem DP_pt {Φ : (κ → AF F) → ℂ} {y : κ → Af F} {f : SInf F κ} (e : ∀ x, Φ (pt x y) = f x) (a L x) :
    DP a L Φ (pt x y) = dop a L f x := by
  rw [dop_apply, DP, nf_pt, e]
  exact congrArg (fun g => fderiv ℝ g x a + _) (funext e)

theorem DP_add {Φ Ψ : (κ → AF F) → ℂ} (h : Φ ∈ schA F κ) (h' : Ψ ∈ schA F κ) (a L) : DP a L (Φ + Ψ) = DP a L Φ + DP a L Ψ := by
  funext z
  obtain ⟨f, e⟩ := slice h (fn z)
  obtain ⟨g, e'⟩ := slice h' (fn z)
  rw [← pt_self z, Pi.add_apply, DP_pt e, DP_pt e', DP_pt (f := f + g) fun x => by rw [Pi.add_apply, e, e']; rfl]
  exact congrArg (fun k : SInf F κ => k (nf z)) ((dopL a L).map_add f g)

theorem DP_smul {Φ : (κ → AF F) → ℂ} (h : Φ ∈ schA F κ) (c : ℂ) (a L) : DP a L (c • Φ) = c • DP a L Φ := by
  funext z
  obtain ⟨f, e⟩ := slice h (fn z)
  rw [← pt_self z, Pi.smul_apply, DP_pt e, DP_pt (f := c • f) fun x => by rw [Pi.smul_apply, e]; rfl]
  exact congrArg (fun k : SInf F κ => k (nf z)) ((dopL a L).map_smul c f)

theorem DP_zero (a L) : DP a L (0 : (κ → AF F) → ℂ) = 0 := funext fun z => by simp [DP]

theorem DP_pure (f : SInf F κ) (g : (κ → Af F) → ℂ) (a L) : DP a L (pureA F f g) = pureA F (dop a L f) g := by
  funext z
  rw [← pt_self z, DP_pt (f := g (fn z) • f) fun x => by rw [pureA_pt, mul_comm]; rfl, pureA_pt, mul_comm]
  exact congrArg (fun k : SInf F κ => k (nf z)) ((dopL a L).map_smul _ f)

theorem DP_mem {Φ : (κ → AF F) → ℂ} (h : Φ ∈ schA F κ) (a L) : DP a L Φ ∈ schA F κ := by
  induction h using Submodule.span_induction with
  | mem Φ h => obtain ⟨f, g, hg, rfl⟩ := h; rw [DP_pure]; exact Submodule.subset_span ⟨_, g, hg, rfl⟩
  | zero => rw [DP_zero]; exact zero_mem _
  | add _ _ h1 h2 h h' => rw [DP_add h1 h2]; exact add_mem h h'
  | smul c _ h1 h => rw [DP_smul h1]; exact Submodule.smul_mem _ _ h

theorem schr_pt (hψ : IsStd ψ) {w : (κ → AF F) × (κ → AF F)} (hw : At (evI F) w) (Ψ : (κ → AF F) → ℂ) (t : ℝ) (x y) :
    schr ψ (realAd F t • w) Ψ (pt x y) = hl (nf w.1) (linForm (nf w.2)) t (fun x => Ψ (pt x y)) x := by
  have ha : At (evI F) w.1 := fun s hs => congrArg Prod.fst (hw s hs)
  have hb : At (evI F) w.2 := fun s hs => congrArg Prod.snd (hw s hs)
  have e : pt x y + realAd F t • w.1 = pt (x + t • nf w.1) y := by
    rw [← pt_self (pt x y + realAd F t • w.1)]
    congr 1
    · rw [nf_add, nf_pt]; congr 1; funext i; simp [nf, evI_mul, evI_realAd, Algebra.smul_def]
    · funext i
      show y i + (realAd F t).2 * (w.1 i).2 = y i
      rw [snd_eq_zero ha, mul_zero, add_zero]
  show ψ (pt x y ⬝ᵥ (realAd F t • w.2) + ⅟(2 : AF F) * ((realAd F t • w.1) ⬝ᵥ (realAd F t • w.2))) * Ψ (pt x y + realAd F t • w.1) = _
  rw [phase_line ψ hψ _ _ _ hb t, e, evI_half_trace, evI_pt]
  simp only [hl, linForm_apply]
  rfl

theorem hasD (hψ : IsStd ψ) {w : (κ → AF F) × (κ → AF F)} (hw : At (evI F) w) {Φ : (κ → AF F) → ℂ} (h : Φ ∈ schA F κ) (z) :
    HasDerivAt (fun t : ℝ => schr ψ (realAd F t • w) Φ z) (D w Φ z) 0 := by
  obtain ⟨f, e⟩ := slice h (fn z)
  rw [← pt_self z, D, DP_pt e]
  simp only [schr_pt hψ hw, e]
  exact hasDerivAt_hl _ _ f _

theorem eval_adm (z : κ → AF F) : (LinearMap.proj z : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) ∈ (adeleClass F).adm κ := fun g _ =>
  ⟨g (fn z) • (BoundedContinuousFunction.evalCLM ℂ (nf z) ∘L SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ ℂ),
    fun _ => mul_comm _ _⟩

structure Imp (ψ : AddChar (AF F) ℂ) (T : Module.End ℂ ((κ → AF F) → ℂ)) (g : (κ → AF F) × (κ → AF F) → (κ → AF F) × (κ → AF F)) :
    Prop where
  pres : ∀ φ ∈ schA F κ, T φ ∈ schA F κ
  adm : ∀ l ∈ (adeleClass F).adm κ, l ∘ₗ T ∈ (adeleClass F).adm κ
  add : ∀ w w', g (w + w') = g w + g w'
  smul : ∀ (c : AF F) w, g (c • w) = c • g w
  impl : ∀ w, ∀ φ ∈ schA F κ, T (schr ψ w φ) = schr ψ (g w) (T φ)

variable {T : Module.End ℂ ((κ → AF F) → ℂ)} {g : (κ → AF F) × (κ → AF F) → (κ → AF F) × (κ → AF F)}

theorem Imp.at (h : Imp ψ T g) {w} (hw : At (evI F) w) : At (evI F) (g w) := fun s hs => by
  rw [← h.smul, hw s hs, ← zero_smul (AF F) (0 : (κ → AF F) × (κ → AF F)), h.smul, zero_smul, zero_smul]

theorem Imp.of_ne (hψ : IsStd ψ) (h : Imp ψ T g) {w} (hw : At (evI F) w) (ha : nf w.1 ≠ 0) {Φ} (hΦ : Φ ∈ schA F κ) :
    T (D w Φ) = D (g w) (T Φ) := by
  induction hΦ using Submodule.span_induction with
  | mem Φ hm =>
    have hs : Φ ∈ schA F κ := Submodule.subset_span hm
    obtain ⟨f, φ, hφ, rfl⟩ := hm
    obtain ⟨G, hG, hD⟩ := hl_line_deriv (nf w.1) (linForm (nf w.2)) f
    funext z
    obtain ⟨S, hS⟩ := h.adm _ (eval_adm z) φ hφ
    have h1 := hD ha S
    have e : (fun t => S (G t)) = fun t : ℝ => schr ψ (realAd F t • g w) (T (pureA F f φ)) z := funext fun t => by
      rw [← hS, ← h.smul, ← h.impl _ _ hs]
      refine congrArg (fun Ψ => T Ψ z) (funext fun z' => ?_)
      rw [← pt_self z', schr_pt hψ hw, pureA_pt, hG]
      simp only [pureA_pt, hl, mul_assoc]
    rw [e, ← hS] at h1
    rw [D, DP_pure]
    exact h1.unique (hasD hψ (h.at hw) (h.pres _ hs) z)
  | zero => simp only [D, DP_zero, map_zero]
  | add _ _ h1 h2 i1 i2 => simp only [D] at *; rw [DP_add h1 h2, map_add, map_add, DP_add (h.pres _ h1) (h.pres _ h2), i1, i2]
  | smul c _ h1 i1 => simp only [D] at *; rw [DP_smul h1, map_smul, map_smul, DP_smul (h.pres _ h1), i1]

theorem at_pt (x : κ → mixedEmbedding.mixedSpace F) : At (evI F) (pt x (0 : κ → Af F)) := fun s hs => by
  have h1 : s.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).map_eq_zero_iff.1 hs
  funext i
  refine Prod.ext ?_ ?_
  · show s.1 * _ = 0
    rw [h1, zero_mul]
  · show s.2 * 0 = 0
    rw [mul_zero]

theorem Imp.inter (hψ : IsStd ψ) (h : Imp ψ T g) {w} (hw : At (evI F) w) {Φ} (hΦ : Φ ∈ schA F κ) : T (D w Φ) = D (g w) (T Φ) := by
  by_cases ha : nf w.1 = 0
  · rcases subsingleton_or_nontrivial (κ → mixedEmbedding.mixedSpace F) with hV | hV
    · have z : ∀ a L (Ψ : (κ → AF F) → ℂ), DP a L Ψ = 0 := fun a L Ψ => funext fun z => by
        simp [DP, Subsingleton.elim a 0, Subsingleton.elim (nf z) 0]
      simp only [D, z, map_zero]
    · obtain ⟨ξ, hξ⟩ := exists_ne (0 : κ → mixedEmbedding.mixedSpace F)
      have hv : At (evI F) ((pt ξ 0, 0) : (κ → AF F) × (κ → AF F)) := fun s hs => Prod.ext (at_pt ξ s hs) (smul_zero _)
      have h1 := h.of_ne hψ (w := w + (pt ξ 0, 0)) (fun s hs => by rw [smul_add, hw s hs, hv s hs, add_zero])
        (by rwa [Prod.fst_add, nf_add, ha, zero_add, nf_pt]) hΦ
      have h2 := h.of_ne hψ hv (by rwa [nf_pt]) hΦ
      rw [D_add_left, map_add, h.add, D_add_left, h2] at h1
      exact add_right_cancel h1
  · exact h.of_ne hψ hw ha hΦ

theorem exists_D_fin (N : Submodule ℂ ((κ → AF F) → ℂ)) [FiniteDimensional ℂ N] (hN : N ≤ schA F κ) :
    ∃ N' : Submodule ℂ ((κ → AF F) → ℂ), FiniteDimensional ℂ N' ∧ ∀ a L, ∀ Φ ∈ N, DP a L Φ ∈ N' := by
  let b := Module.finBasis ℝ ((κ → mixedEmbedding.mixedSpace F) × ((κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ))
  let l : _ → N →ₗ[ℂ] ((κ → AF F) → ℂ) := fun i =>
    ⟨⟨fun Φ => DP (b i).1 (b i).2 Φ.1, fun Φ Ψ => DP_add (hN Φ.2) (hN Ψ.2) _ _⟩, fun c Φ => DP_smul (hN Φ.2) c _ _⟩
  refine ⟨⨆ i, LinearMap.range (l i), inferInstance, fun a L Φ hΦ => ?_⟩
  have : ∀ q ∈ Submodule.span ℝ (Set.range b), DP q.1 q.2 Φ ∈ ⨆ i, LinearMap.range (l i) := fun q hq => by
    induction hq using Submodule.span_induction with
    | mem q h => obtain ⟨i, rfl⟩ := h; exact Submodule.mem_iSup_of_mem i ⟨⟨Φ, hΦ⟩, rfl⟩
    | zero => convert Submodule.zero_mem _; funext z; simp [DP]
    | add x y _ _ hx hy => rw [Prod.fst_add, Prod.snd_add, DP_add_left]; exact add_mem hx hy
    | smul t q _ h => rw [Prod.smul_fst, Prod.smul_snd, DP_smul_left]; exact Submodule.smul_mem _ _ h
  exact this (a, L) (b.span_eq ▸ trivial)

end GlobalTheory.ThK.Dbl.Box

end
