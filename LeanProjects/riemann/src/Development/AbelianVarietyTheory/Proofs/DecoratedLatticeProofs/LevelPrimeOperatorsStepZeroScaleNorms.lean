import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PairForm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeterssonStepZeroScalarFormsEqPosMulInnerStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.FinPl GlobalTheory.SeeSaw ValuativeRel IsLocalRing
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RamStepZero

theorem isLinearMap_of_inner {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (f : E → E) (Q : ℝ)
    (h : ∀ x y, inner ℂ (f x) (f y) = (Q : ℂ) * inner ℂ x y) : IsLinearMap ℂ f := by
  constructor
  · intro x y
    have key : inner ℂ (f (x + y) - (f x + f y)) (f (x + y) - (f x + f y)) = 0 := by
      simp only [inner_sub_left, inner_sub_right, inner_add_left, inner_add_right, h]
      ring
    exact (sub_eq_zero.mp (inner_self_eq_zero.mp key))
  · intro a x
    have key : inner ℂ (f (a • x) - a • f x) (f (a • x) - a • f x) = 0 := by
      simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, h]
      ring
    exact (sub_eq_zero.mp (inner_self_eq_zero.mp key))

theorem norm_of_inner {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (f : E → E) (Q : ℝ) (hQ : 0 ≤ Q)
    (h : ∀ x y, inner ℂ (f x) (f y) = (Q : ℂ) * inner ℂ x y) (x : E) : ‖f x‖ = Real.sqrt Q * ‖x‖ := by
  have h1 := h x x
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h1
  have h2 : ‖f x‖ ^ 2 = Q * ‖x‖ ^ 2 := by
    apply Complex.ofReal_injective
    push_cast
    exact h1
  rw [← Real.sqrt_sq (norm_nonneg (f x)), h2, Real.sqrt_mul hQ, Real.sqrt_sq (norm_nonneg x)]

end GlobalTheory.RamStepZero

namespace GlobalTheory.RamStepZero

theorem comm_of_sub_one_mul {R : Type*} [Ring R] (M N : R) (h1 : (M - 1) * (N - 1) = 0) (h2 : (N - 1) * (M - 1) = 0) :
    M * N = N * M := by
  have e1 : (M - 1) * (N - 1) = M * N - M - N + 1 := by noncomm_ring
  have e2 : (N - 1) * (M - 1) = N * M - N - M + 1 := by noncomm_ring
  have key : M * N - M - N + 1 = N * M - N - M + 1 := by rw [← e1, ← e2, h1, h2]
  calc M * N = (M * N - M - N + 1) + (M + N - 1) := by abel
    _ = (N * M - N - M + 1) + (M + N - 1) := by rw [key]
    _ = N * M := by abel

theorem placeIdem_mul {D : D7} {v v' : HeightOneSpectrum (𝓞 D.host.F)} {ε ε' : AF D.host.F}
    (h : IsPlaceIdem D v ε) (h' : IsPlaceIdem D v' ε') (hv : v ≠ v') : ε * ε' = 0 := by
  obtain ⟨α, rfl, h1, h0⟩ := h
  obtain ⟨α', rfl, h1', h0'⟩ := h'
  have hα : α * α' = 0 := by
    apply RestrictedProduct.ext
    intro w
    have e : evalV D.host.F w (α * α') = 0 := by
      rw [map_mul]
      by_cases hw : w = v
      · subst hw
        rw [h0' w hv, mul_zero]
      · rw [h0 w hw, zero_mul]
    exact e
  show ((0 : Ainf D.host.F), α) * ((0 : Ainf D.host.F), α') = 0
  rw [Prod.mk_mul_mk, mul_zero, hα]
  rfl

theorem gl_comm_other : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p p' : SplitPt D k) (S : HSp D) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (β : Frame p S n) (β' : Frame p' S n') (g : GL n k) (h : GL n' k), p.v ≠ p'.v → β.gl g * β'.gl h = β'.gl h * β.gl g := by
  intro D k _ _ _ _ p p' S n n' _ _ _ _ β β' g h hv
  obtain ⟨ε, hε, he⟩ := p.above
  obtain ⟨ε', hε', he'⟩ := p'.above
  have hεε : algebraMap (AF D.host.F) (AE D) ε * algebraMap (AF D.host.F) (AE D) ε' = 0 := by
    rw [← map_mul, placeIdem_mul hε hε' hv, map_zero]
  have hM := β.gl_supp g
  have hN := β'.gl_supp h
  unfold SuppAt at hM hN
  rw [he] at hM
  rw [he'] at hN
  set M := mt S (β.gl g)
  set N := mt S (β'.gl h)
  have h1 : (M - 1) * (N - 1) = 0 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [← hM i l, ← hN l j]
    calc _ = (algebraMap (AF D.host.F) (AE D) ε * algebraMap (AF D.host.F) (AE D) ε') * ((M - 1) i l * (N - 1) l j) := by ring
      _ = 0 := by rw [hεε, zero_mul]
  have h2 : (N - 1) * (M - 1) = 0 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [← hM l j, ← hN i l]
    calc _ = (algebraMap (AF D.host.F) (AE D) ε * algebraMap (AF D.host.F) (AE D) ε') * ((N - 1) i l * (M - 1) l j) := by ring
      _ = 0 := by rw [hεε, zero_mul]
  have hMN : M * N = N * M := comm_of_sub_one_mul M N h1 h2
  have hinj : Function.Injective (matHom S) := Subtype.val_injective
  apply hinj
  rw [map_mul, map_mul]
  exact Units.ext hMN

end GlobalTheory.RamStepZero

namespace GlobalTheory.RamStepZero

section
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {p p' : SplitPt D k} {S : HSp D} {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

theorem rep_comm (β : Frame p S n) (β' : Frame p' S n') (hv : p.v ≠ p'.v) (g : GL n k) (h : GL n' k) (f : GA D S → ℂ) :
    β.rep g (β'.rep h f) = β'.rep h (β.rep g f) := by
  funext x
  simp only [Frame.rep, MonoidHom.coe_mk, OneHom.coe_mk, LinearMap.funLeft_apply]
  rw [mul_assoc, gl_comm_other D k p p' S n n' β β' g h hv, ← mul_assoc]

theorem sOp_ramAt_other' (β : Frame p S n) (β' : Frame p' S n') (P : Pair k n) (P' : Pair k n') (q : Unif k)
    (χ : AddChar 𝓀[k] ℂ) (ε : 𝓀[k]ˣ) (φ₀ : GA D S → ℂ) (hv : p.v ≠ p'.v) (h : RamAt β' P' φ₀) :
    RamAt β' P' (sOp β P q χ ε φ₀) := by
  classical
  obtain ⟨φ, ⟨hEq, hM, hC⟩, rfl⟩ := h
  let T : (GA D S → ℂ) →ₗ[ℂ] (GA D S → ℂ) := ∑ P₁ ∈ withKer (ε • P).lat,
    χ (-cross q P₁ (ε • P)) • β.rep (Classical.epsilon fun g : GL n k => g • P = P₁)
  have hT : ∀ f, T f = ∑ P₁ ∈ withKer (ε • P).lat,
      χ (-cross q P₁ (ε • P)) • β.rep (Classical.epsilon fun g : GL n k => g • P = P₁) f := by
    intro f
    simp [T, LinearMap.sum_apply]
  have hTc : ∀ h' : GL n' k, ∀ f, T (β'.rep h' f) = β'.rep h' (T f) := by
    intro h' f
    rw [hT, hT, map_sum]
    refine Finset.sum_congr rfl fun P₁ _ => ?_
    rw [map_smul, rep_comm β β' hv]
  refine ⟨fun P₂ => T (φ P₂), ⟨?_, ?_, ?_⟩, ?_⟩
  · intro g P₂
    show T (φ (g • P₂)) = β'.rep g (T (φ P₂))
    rw [hEq g P₂, hTc]
  · let _ := Fintype.ofFinite 𝓀[k]ˣ
    rw [mem_Mram] at hM ⊢
    intro P₂
    rw [← map_sum, hM P₂, map_zero]
  · intro P₂
    show IsContAut S (T (φ P₂))
    rw [hT]
    refine ⟨?_, ?_⟩
    · intro γ hγ x
      simp only [Finset.sum_apply, Pi.smul_apply]
      refine Finset.sum_congr rfl fun P₁ _ => ?_
      simp only [Frame.rep, MonoidHom.coe_mk, OneHom.coe_mk, LinearMap.funLeft_apply]
      rw [mul_assoc, (hC P₂).1 γ hγ]
    · rw [Finset.sum_fn]
      refine continuous_finsetSum _ fun P₁ _ => ?_
      simp only [Frame.rep, MonoidHom.coe_mk, OneHom.coe_mk]
      exact continuous_const.mul ((hC P₂).2.comp (continuous_mul_const _))
  · show T (φ P') = _
    rw [hT]
    rfl

end
end GlobalTheory.RamStepZero

namespace GlobalTheory.RamStepZero

theorem normStepZero : ∀ (D : D7) (u : D.what₂.Word) (F : Formalism.L2.Forms.Forms0 D u) (θ : InfFam D), IsInfFam θ → CoCpt (D.sp.X 0) → ∀ (vS : Vol (D.sp.X 0)) (y : (D.mem u).C.Y 0), ∃ c : ℝ, 0 < c ∧ ∀ φ ψ : D.what₂.Mu u, ∫ g in vS.𝓕, (GlobalTheory.Core.Mi.chart0 F).rd θ (D.eMu u φ).1 y g * star ((GlobalTheory.Core.Mi.chart0 F).rd θ (D.eMu u ψ).1 y g) ∂vS.μ = (c : ℂ) * inner ℂ ψ φ := GlobalTheory.T.petersson_stepZeroScalarForms_eq_pos_mul_inner

theorem sOp_ramAt_other : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p p' : SplitPt D k) (S : HSp D) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (β : Frame p S n) (β' : Frame p' S n') (P : Pair k n) (P' : Pair k n') (q : Unif k) (χ : AddChar 𝓀[k] ℂ) (ε : 𝓀[k]ˣ) (φ₀ : GA D S → ℂ), p.v ≠ p'.v → RamAt β' P' φ₀ → RamAt β' P' (sOp β P q χ ε φ₀) :=
  by
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ β β' P P' q χ ε φ₀ hv h
  exact sOp_ramAt_other' β β' P P' q χ ε φ₀ hv h

section Fold

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}
  (p : ι → SplitPt D k) {S : HSp D} {n : Type} [Fintype n] [DecidableEq n] (β : ∀ i, Frame (p i) S n) (Q : ι → Pair k n)
  (q : Unif k) (χ' : ι → AddChar 𝓀[k] ℂ) (η : ι → 𝓀[k]ˣ)

theorem ramAt_foldr (i : ι) (f : GA D S → ℂ) : ∀ I : List ι, (∀ j ∈ I, (p j).v ≠ (p i).v) → RamAt (β i) (Q i) f →
    RamAt (β i) (Q i) (I.foldr (fun j g => sOp (β j) (Q j) q (χ' j) (η j) g) f)
  | [], _, h => h
  | j :: I, hI, h => by
    simp only [List.foldr_cons]
    exact sOp_ramAt_other D k (p j) (p i) S n n (β j) (β i) (Q j) (Q i) q (χ' j) (η j) _ (hI j (by simp))
      (ramAt_foldr i f I (fun j' hj' => hI j' (by simp [hj'])) h)

theorem inner_foldr (hRU : RamUnitary D) (hS : CoCpt S) (vS : Vol S) (χ : ι → AddChar k Circle)
    (hχ : ∀ i, HasConductor (χ i) 1) (hinj : Function.Injective fun i => (p i).v) :
    ∀ I : List ι, I.Nodup → ∀ f f' : GA D S → ℂ, (∀ i ∈ I, RamAt (β i) (Q i) f) → (∀ i ∈ I, RamAt (β i) (Q i) f') →
      ∫ g in vS.𝓕, I.foldr (fun j h => sOp (β j) (Q j) q (resChar (χ j) (hχ j) q) (η j) h) f g *
          star (I.foldr (fun j h => sOp (β j) (Q j) q (resChar (χ j) (hχ j) q) (η j) h) f' g) ∂vS.μ =
        (resCard k : ℂ) ^ (Fintype.card n * I.length) * ∫ g in vS.𝓕, f g * star (f' g) ∂vS.μ
  | [], _, f, f', _, _ => by simp
  | i :: I, hnd, f, f', hf, hf' => by
    have hnd' := List.nodup_cons.mp hnd
    have hne : ∀ j ∈ I, (p j).v ≠ (p i).v := fun j hj h => hnd'.1 (hinj h ▸ hj)
    simp only [List.foldr_cons]
    rw [hRU k (p i) n q (χ i) (hχ i) (η i) S hS vS (β i) (Q i) _ _
        (ramAt_foldr p β Q q (fun j => resChar (χ j) (hχ j) q) η i f I hne (hf i (by simp)))
        (ramAt_foldr p β Q q (fun j => resChar (χ j) (hχ j) q) η i f' I hne (hf' i (by simp))),
      inner_foldr hRU hS vS χ hχ hinj I hnd'.2 f f' (fun j hj => hf j (by simp [hj])) (fun j hj => hf' j (by simp [hj]))]
    rw [List.length_cons, Nat.mul_succ, pow_add]
    ring

end Fold

end GlobalTheory.RamStepZero

namespace GlobalTheory.RamStepZero

theorem opsStepZero_norm : ∀ (D : D7) (u : D.what₂.Word) (F : Formalism.L2.Forms.Forms0 D u) (θ : InfFam D), IsInfFam θ → RamUnitary D → CoCpt (D.sp.X 0) → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (q : Unif k) (χ : ι → AddChar k Circle) (hχ : ∀ i, HasConductor (χ i) 1) (β : ∀ i, Frame (p i) (D.sp.X 0) (Fin (D.sp.X 0).rank)) (Q : ι → Pair k (Fin (D.sp.X 0).rank)), I.Nodup → (Function.Injective fun i => (p i).v) → (∀ (φ : D.what₂.Mu u) y i, RamAt (β i) (Q i) ((GlobalTheory.Core.Mi.chart0 F).rd θ (D.eMu u φ).1 y)) → ∀ η : ι → 𝓀[k]ˣ, (∀ φ : D.what₂.Mu u, ∃ φ' : D.what₂.Mu u, ∀ y, (GlobalTheory.Core.Mi.chart0 F).rd θ (D.eMu u φ').1 y = I.foldr (fun i f => sOp (β i) (Q i) q (resChar (χ i) (hχ i) q) (η i) f) ((GlobalTheory.Core.Mi.chart0 F).rd θ (D.eMu u φ).1 y)) → ∃ (S : D.what₂.Mu u ≃ₗ[ℂ] D.what₂.Mu u) (r : ℝ), 0 < r ∧ (∀ φ, ‖S φ‖ = r * ‖φ‖) ∧ ∀ φ y, (GlobalTheory.Core.Mi.chart0 F).rd θ (D.eMu u (S φ)).1 y = I.foldr (fun i f => sOp (β i) (Q i) q (resChar (χ i) (hχ i) q) (η i) f) ((GlobalTheory.Core.Mi.chart0 F).rd θ (D.eMu u φ).1 y) := by
  intro D u F θ hθ hRU hcpt k _ _ _ _ ι p I q χ hχ β Q hnd hinj hram η hS
  classical
  obtain ⟨vS⟩ := GlobalTheory.Unf.Inhab.nonempty_vol (D.sp.X 0)
  by_cases hY : Nonempty ((D.mem u).C.Y 0)
  swap
  · exact ⟨LinearEquiv.refl ℂ _, 1, one_pos, fun φ => by simp, fun φ y => (hY ⟨y⟩).elim⟩
  obtain ⟨y₀⟩ := hY
  obtain ⟨c, hc, hN⟩ := normStepZero D u F θ hθ hcpt vS y₀
  choose Sf hSf using hS
  have hk : (0 : ℝ) < resCard k := by
    unfold resCard
    exact_mod_cast Nat.card_pos
  set Q0 : ℝ := (resCard k : ℝ) ^ (Fintype.card (Fin (D.sp.X 0).rank) * I.length) with hQ0def
  have hQ0 : 0 < Q0 := pow_pos hk _
  have hinner : ∀ φ ψ, inner ℂ (Sf φ) (Sf ψ) = (Q0 : ℂ) * inner ℂ φ ψ := by
    intro φ ψ
    have h1 := hN (Sf ψ) (Sf φ)
    rw [hSf ψ y₀, hSf φ y₀,
      inner_foldr p β Q q η hRU hcpt vS χ hχ hinj I hnd _ _ (fun i _ => hram ψ y₀ i) (fun i _ => hram φ y₀ i),
      hN ψ φ] at h1
    have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
    rw [hQ0def]
    push_cast
    apply mul_left_cancel₀ hc'
    rw [← h1]
    ring
  have hlin := isLinearMap_of_inner Sf Q0 hinner
  let L : D.what₂.Mu u →ₗ[ℂ] D.what₂.Mu u := hlin.mk' Sf
  have hL : ∀ φ, L φ = Sf φ := fun φ => rfl
  have hnorm : ∀ φ, ‖Sf φ‖ = Real.sqrt Q0 * ‖φ‖ := norm_of_inner Sf Q0 hQ0.le hinner
  have hinjL : Function.Injective L := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    have h := hnorm a
    rw [← hL, ha, norm_zero] at h
    have hs : 0 < Real.sqrt Q0 := Real.sqrt_pos.mpr hQ0
    exact norm_eq_zero.mp (by nlinarith [norm_nonneg a])
  refine ⟨LinearEquiv.ofInjectiveEndo L hinjL, Real.sqrt Q0, Real.sqrt_pos.mpr hQ0, fun φ => ?_, fun φ y => ?_⟩
  · rw [LinearEquiv.coe_ofInjectiveEndo, hL]
    exact hnorm φ
  · rw [LinearEquiv.coe_ofInjectiveEndo, hL]
    exact hSf φ y

end GlobalTheory.RamStepZero
