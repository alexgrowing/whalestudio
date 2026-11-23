import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.TraceFormula
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.MomentMatch

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

open MeasureTheory

section Generic

variable {W : Type*} [AddCommGroup W] [Module ℂ W]

theorem pm_pow_eig (A : Module.End ℂ W) {z : ℂ} {f : W} (h : A f = z • f) (k : ℕ) :
    (A ^ k) f = z ^ k • f := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', Module.End.mul_apply, ih, map_smul, h, smul_smul, pow_succ]

theorem pm_proj_decomp (A Q : Module.End ℂ W) (T : Submodule ℂ W) (B : Finset ℝ) (z : ℂ)
    (hQ1 : ∀ f ∈ T, A f = z • f → Q f = f) (hQ0 : ∀ f ∈ T, ∀ z' : ℂ, z' ≠ z → A f = z' • f → Q f = 0)
    (fb : ℝ → W) (hfb : ∀ b, fb b ∈ T ∧ A (fb b) = ((b : ℝ) : ℂ) • fb b) :
    Q (∑ b ∈ B, fb b) = ∑ b ∈ B, if ((b : ℝ) : ℂ) = z then fb b else 0 := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  split_ifs with h
  · exact hQ1 _ (hfb b).1 (by rw [← h]; exact (hfb b).2)
  · exact hQ0 _ (hfb b).1 _ h (hfb b).2

theorem pm_agree (A : Module.End ℂ W) (T : Submodule ℂ W) (B : Finset ℝ)
    (hdec : ∀ f ∈ T, ∃ fb : ℝ → W, (∀ b, fb b ∈ T ∧ A (fb b) = ((b : ℝ) : ℂ) • fb b) ∧ f = ∑ b ∈ B, fb b)
    (P : ℝ → Module.End ℂ W)
    (hP1 : ∀ b, ∀ f ∈ T, A f = ((b : ℝ) : ℂ) • f → P b f = f)
    (hP0 : ∀ b, ∀ f ∈ T, ∀ z' : ℂ, z' ≠ ((b : ℝ) : ℂ) → A f = z' • f → P b f = 0) :
    (∀ f ∈ T, ∀ k : ℕ, (A ^ k) f = ∑ b ∈ B, ((b : ℝ) : ℂ) ^ k • P b f) ∧
      ∀ (Q : Module.End ℂ W) (z : ℂ), (∀ f ∈ T, A f = z • f → Q f = f) →
        (∀ f ∈ T, ∀ z' : ℂ, z' ≠ z → A f = z' • f → Q f = 0) →
        ∀ f ∈ T, Q f = ∑ b ∈ B, if ((b : ℝ) : ℂ) = z then P b f else 0 := by
  have hPb : ∀ fb : ℝ → W, (∀ b, fb b ∈ T ∧ A (fb b) = ((b : ℝ) : ℂ) • fb b) →
      ∀ b ∈ B, P b (∑ b' ∈ B, fb b') = fb b := by
    intro fb hfb b hb
    rw [pm_proj_decomp A (P b) T B _ (hP1 b) (hP0 b) fb hfb]
    simp [Complex.ofReal_inj, hb]
  refine ⟨fun f hf k => ?_, fun Q z hQ1 hQ0 f hf => ?_⟩
  · obtain ⟨fb, hfb, rfl⟩ := hdec f hf
    rw [map_sum]
    refine Finset.sum_congr rfl fun b hb => ?_
    rw [hPb fb hfb b hb, pm_pow_eig A (hfb b).2]
  · obtain ⟨fb, hfb, rfl⟩ := hdec f hf
    rw [pm_proj_decomp A Q T B z hQ1 hQ0 fb hfb]
    refine Finset.sum_congr rfl fun b hb => ?_
    rw [hPb fb hfb b hb]

end Generic

theorem pm_single_mem {M : Type*} [AddCommGroup M] [Module ℂ M] (S : Submodule ℂ M) {x : M} (hx : x ∈ S)
    (c : Fin n) : Pi.single c x ∈ tensSub (n := n) S := by
  refine (Submodule.mem_pi).2 fun i _ => ?_
  by_cases h : i = c <;> simp [h, hx]

theorem pm_ptr {M : Type*} [AddCommGroup M] [Module ℂ M] (S : Submodule ℂ M)
    (Q : Module.End ℂ (Fin n → M)) (R : ℝ → Module.End ℂ (Fin n → M)) (B : Finset ℝ) (g : ℝ → ℂ)
    (hQ : ∀ f ∈ tensSub S, Q f = ∑ b ∈ B, g b • R b f) {x : M} (hx : x ∈ S) :
    ptr Q x = ∑ b ∈ B, g b • ptr (R b) x := by
  simp only [ptr_apply, hQ _ (pm_single_mem S hx _), Finset.sum_apply, Pi.smul_apply, Finset.smul_sum]
  exact Finset.sum_comm

theorem pm_resid (dual : Bool) (lam : Fin n → ℝ) (s : Fin n) :
    resid (poleF dual lam) s = ((ratioF dual lam s : ℝ) : ℂ) := by
  cases dual
  · exact resid_poleV lam s
  · exact resid_poleVd lam s

theorem pm_pole_inj (dual : Bool) {lam : Fin n → ℝ} (hl : StrictAnti lam) : Function.Injective (poleF dual lam) := by
  cases dual
  · exact poleV_injective hl.injective
  · exact poleVd_injective hl.injective

theorem pm_char (dual : Bool) {M : Type*} [AddCommGroup M] [Module ℂ M] {E : Fin n → Fin n → Module.End ℂ M}
    {lam : Fin n → ℝ} {S : Submodule ℂ M} (hS : HasGelfandChar E lam S) (k : ℕ) (x : M) (hx : x ∈ S) :
    ptr (eeF dual E ^ k) x = PowerSeries.coeff (k + 1) (resSeries (poleF dual lam)) • x := by
  cases dual
  · exact ptr_eeV_pow_char hS k x hx
  · exact ptr_eeVd_pow_char hS k x hx

theorem pm_core (dual : Bool) {lam : Fin n → ℝ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {ε : Fin n → Bool}
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}
    (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) (hsm : ∀ v : D, IsSmoothVecU ε σ v)
    {V : Submodule ℂ D} (hgap : StdGap ε lam) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) (hW : ∀ v ∈ genSub E V, ∀ w ∈ genSub E V, MemLp (fun g : Formalism.REAL.UJ ε =>
      ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) * inner ℂ ((w : D) : H) (σ (Formalism.MainNotions.S.umat g) ((v : D) : H)))
      2 (Formalism.REAL.muG ε)) (hG : HasGelfandChar E lam (genSub E V)) :
    ∃ B : Finset ℝ, ∃ c : ℝ → ℂ, ∃ P : ℝ → Module.End ℂ (Fin n → D),
      (∀ z : ℂ, ∀ f ∈ tensSub (genSub E V), f ≠ 0 → eeF dual E f = z • f → ∃ b ∈ B, z = ((b : ℝ) : ℂ)) ∧
      (∀ b, ∀ f ∈ tensSub (genSub E V), P b f ∈ tensSub (genSub E V)) ∧
      (∀ b, ∀ f ∈ tensSub (genSub E V), eeF dual E (P b f) = ((b : ℝ) : ℂ) • P b f) ∧
      (∀ b, ∀ f ∈ tensSub (genSub E V), eeF dual E f = ((b : ℝ) : ℂ) • f → P b f = f) ∧
      (∀ b, ∀ x ∈ genSub E V, ptr (P b) x = c b • x) ∧
      (∀ b, c b = 0 → ∀ f ∈ tensSub (genSub E V), P b f = 0) ∧
      (∀ (Q : Module.End ℂ (Fin n → D)) (z : ℂ), (∀ f ∈ tensSub (genSub E V), eeF dual E f = z • f → Q f = f) →
        (∀ f ∈ tensSub (genSub E V), ∀ z' : ℂ, z' ≠ z → eeF dual E f = z' • f → Q f = 0) →
        ∀ x ∈ genSub E V, ptr Q x = (∑ b ∈ B, if ((b : ℝ) : ℂ) = z then c b else 0) • x) ∧
      (∀ p : ℂ, (∑ b ∈ B, if ((b : ℝ) : ℂ) = p then c b else 0) =
        ∑ s ∈ univ.filter (fun s => poleF dual lam s = p), ((ratioF dual lam s : ℝ) : ℂ)) ∧
      ∃ x₀ ∈ genSub E V, x₀ ≠ 0 := by
  obtain ⟨B, hdec, hev⟩ := ee_decomp dual hσ hD hgap hV hc hVK hW
  have hPex := fun b : ℝ => eigenProj_exists dual hσ hD hgap hV hc hVK hW ((b : ℝ) : ℂ)
  choose P hPG hPP hPz hP1 hP0 using hPex
  have hsc := fun b => ptr_scalar dual hσ hD hgap hV hc hVK (hPG b)
  choose c hcb using hsc
  have hPB := fun b => eigenProj_formB dual hσ hD hgap hV hc hVK hW _ (hPG b).1 (hPz b) (hP1 b) (hP0 b)
  have htr := fun b => trace_nonneg dual hσ hD hsm hgap hV hc hVK hW (hPG b) (hPP b) (hPB b) (hPz b) (hcb b)
  obtain ⟨hpow, hagr⟩ := pm_agree (eeF dual E) (tensSub (genSub E V)) B hdec P hP1 hP0
  have hQ : ∀ (Q : Module.End ℂ (Fin n → D)) (z : ℂ),
      (∀ f ∈ tensSub (genSub E V), eeF dual E f = z • f → Q f = f) →
      (∀ f ∈ tensSub (genSub E V), ∀ z' : ℂ, z' ≠ z → eeF dual E f = z' • f → Q f = 0) →
      ∀ x ∈ genSub E V, ptr Q x = (∑ b ∈ B, if ((b : ℝ) : ℂ) = z then c b else 0) • x := by
    intro Q z hQ1 hQ0 x hx
    rw [pm_ptr (genSub E V) Q P B (fun b => if ((b : ℝ) : ℂ) = z then 1 else 0)
      (fun f hf => by
        rw [hagr Q z hQ1 hQ0 f hf]
        exact sum_congr rfl fun b _ => by split_ifs <;> simp) hx, Finset.sum_smul]
    refine sum_congr rfl fun b _ => ?_
    rw [hcb b x hx]
    split_ifs <;> simp
  have hVle : V ≤ genSub E V := by
    unfold genSub
    exact le_sInf fun T hT => hT.1
  obtain ⟨x₀, hx₀V, hx₀0, -⟩ := hV.2.2.2
  have hx₀ : x₀ ∈ genSub E V := hVle hx₀V
  have hmom : ∀ k : ℕ, ∑ i : B, c i * ((i : ℝ) : ℂ) ^ k =
      ∑ s, resid (poleF dual lam) s * poleF dual lam s ^ k := by
    intro k
    rw [Finset.sum_coe_sort B (fun b => c b * ((b : ℝ) : ℂ) ^ k), ← resSeries_coeff_succ (pm_pole_inj dual hgap.1) k]
    apply smul_left_injective ℂ hx₀0
    beta_reduce
    rw [← pm_char dual hG k x₀ hx₀, pm_ptr (genSub E V) _ P B (fun b => ((b : ℝ) : ℂ) ^ k)
      (fun f hf => hpow f hf k) hx₀, Finset.sum_smul]
    refine sum_congr rfl fun b _ => ?_
    rw [hcb b x₀ hx₀, smul_smul, mul_comm (c b)]
  refine ⟨B, c, P, hev, fun b => (hPG b).1, hPz, hP1, hcb, fun b h0 => (htr b).2.2 h0, hQ, fun p => ?_,
    x₀, hx₀, hx₀0⟩
  have hf := moment_fibre (fun i : B => ((i : ℝ) : ℂ)) (fun i => c i) (poleF dual lam) (resid (poleF dual lam)) hmom p
  rw [Finset.sum_filter, Finset.sum_coe_sort B (fun b => if ((b : ℝ) : ℂ) = p then c b else 0)] at hf
  rw [hf]
  exact sum_congr rfl fun s _ => pm_resid dual lam s

theorem pm_filter_pole (dual : Bool) {lam : Fin n → ℝ} (hl : StrictAnti lam) (s : Fin n) :
    univ.filter (fun s' => poleF dual lam s' = poleF dual lam s) = {s} := by
  ext t
  simp [(pm_pole_inj dual hl).eq_iff]

theorem pm_sum_single {B : Finset ℝ} {b : ℝ} (hb : b ∈ B) (c : ℝ → ℂ) :
    (∑ b' ∈ B, if ((b' : ℝ) : ℂ) = ((b : ℝ) : ℂ) then c b' else 0) = c b := by
  simp [Complex.ofReal_inj, hb]

end ReciprocityTheory.ChartRestriction.DS
