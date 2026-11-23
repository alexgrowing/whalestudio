import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsAdapted

open NumberField TensorProduct Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

namespace GlobalTheory.CompanionTheory.Ar.Cusp.PhiBaseChange

theorem phiNormSq_baseChange : ∀ (E L Ψ : Type) [Field E] [NumberField E] [Field L] [NumberField L] [Fintype Ψ] (V : Type) [AddCommGroup V] [Module L V] [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] (A : LinPt E L Ψ V) (lab : Ψ → Ψ ⊕ Ψ) (r k m : ℕ) (h : r + k = m) (v : Fin r → V) (q : Ψ → Fin k → A.Λ) (bL : Ψ → Fin m → V) (T : Ψ → Matrix (Fin m) (Fin m) L), IsOFamily A.ρ A.I v → (∀ τ, A.IsAdapted (lab τ) v (q τ) ∧ ∀ i, (q τ i : V) ∈ A.eig (lab τ)) → (∀ τ i, A.fam (lab τ) v (q τ) i = ∑ j, T τ j (Fin.cast h i) • bL τ j) → (∀ τ, (T τ).det ≠ 0) → ∀ (e : L →+* ℂ) (V' : Type) [AddCommGroup V'] [Module ℂ V'] (j : V →+ V'), (∀ (c : L) x, j (c • x) = e c • j x) → Function.Injective j → ∀ (ρ' : 𝓞 E →+* Module.End ℂ V'), (∀ a x, ρ' a (j x) = j (A.ρ a x)) → (∀ τ a, eigComp ρ' (e.comp (A.σ (lab τ))) (j (v a)) = j (eigComp A.ρ (A.σ (lab τ)) (v a))) → ∀ hb : V' → V' → ℂ, (∀ τ c c', hb (j (q τ c)) (j (q τ c')) = (A.Bq.metric.form e).inner ((1 : GroundTheory.Heights₂.Heights.ComplexAt e) ⊗ₜ[𝓞 L] A.f (q τ c)) ((1 : GroundTheory.Heights₂.Heights.ComplexAt e) ⊗ₜ[𝓞 L] A.f (q τ c'))) → PhiNormSq ρ' hb (A.I.map j) (4 * Real.pi)⁻¹ (fun τ => e.comp (A.σ (lab τ))) (fun τ i => j (bL τ i)) ((((oSpan A.ρ v).relIndex A.I : ℕ) : ℝ) * ∏ τ, (4 * Real.pi)⁻¹ ^ r * A.gramDet e (q τ) / ‖e (T τ).det‖ ^ 2) := by
  intro E L Ψ _ _ _ _ _ V _ _ _ _ A lab r k m h v q bL T hv hq hfam hT e V' _ _ j hjs hji ρ' hρ' heig hb hhb
  classical
  obtain ⟨hvI, hvind, hvrel⟩ := hv
  have hsum : ∀ a : Fin r → 𝓞 E, ∑ i, ρ' (a i) (j (v i)) = j (∑ i, A.ρ (a i) (v i)) := by
    intro a
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => hρ' _ _
  have hspan : oSpan ρ' (fun i => j (v i)) = (oSpan A.ρ v).map j := by
    unfold GlobalTheory.CompanionTheory.Ar.Cusp.oSpan
    rw [AddMonoidHom.map_closure]
    congr 1
    ext x
    constructor
    · rintro ⟨a, i, rfl⟩
      exact ⟨A.ρ a (v i), ⟨a, i, rfl⟩, (hρ' a (v i)).symm⟩
    · rintro ⟨y, ⟨a, i, rfl⟩, rfl⟩
      exact ⟨a, i, (hρ' a (v i)).symm⟩
  have hrel : (oSpan ρ' (fun i => j (v i))).relIndex (A.I.map j) = (oSpan A.ρ v).relIndex A.I := by
    rw [hspan]
    exact AddSubgroup.relIndex_map_map_of_injective _ _ hji
  have hOF : IsOFamily ρ' (A.I.map j) (fun i => j (v i)) := by
    unfold GlobalTheory.CompanionTheory.Ar.Cusp.IsOFamily
    refine ⟨fun i => AddSubgroup.mem_map_of_mem j (hvI i), fun a ha => hvind a (hji ?_), ?_⟩
    · rw [map_zero, ← hsum a]
      exact ha
    · rw [hrel]
      exact hvrel
  have hqe : ∀ τ c, j (q τ c) ∈ eigSp ρ' (e.comp (A.σ (lab τ))) := by
    intro τ c
    have hx0 := (hq τ).2 c
    unfold GlobalTheory.CompanionTheory.Ar.Cusp.LinPt.eig at hx0
    rw [Submodule.mem_inf, Submodule.restrictScalars_mem] at hx0
    have hx := hx0.2
    simp only [GlobalTheory.CompanionTheory.Ar.eigSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply] at hx ⊢
    intro a
    rw [hρ', RingHom.comp_apply, ← hjs, ← map_sub, hx a, map_zero]
  have happ : ∀ τ i, Fin.append (fun a => eigComp ρ' (e.comp (A.σ (lab τ))) (j (v a))) (fun c => j (q τ c)) i =
      ∑ j', (T τ).map e j' (Fin.cast h i) • j (bL τ j') := by
    intro τ i
    have hfi := hfam τ i
    have hap : Fin.append (fun a => eigComp ρ' (e.comp (A.σ (lab τ))) (j (v a))) (fun c => j (q τ c)) i =
        j (A.fam (lab τ) v (q τ) i) := by
      unfold GlobalTheory.CompanionTheory.Ar.Cusp.LinPt.fam
      refine Fin.addCases (fun a => ?_) (fun c => ?_) i
      · simp only [Fin.append_left, heig]
      · simp only [Fin.append_right]
    rw [hap, hfi, map_sum]
    refine Finset.sum_congr rfl fun j' _ => ?_
    rw [hjs, Matrix.map_apply]
  have hdet : ∀ τ, ((T τ).map e).det = e (T τ).det := by
    intro τ
    rw [RingHom.map_det]
    rfl
  have hg : ∀ τ, (Matrix.of fun c c' => hb (j (q τ c)) (j (q τ c'))).det.re = A.gramDet e (q τ) := by
    intro τ
    unfold GlobalTheory.CompanionTheory.Ar.Cusp.LinPt.gramDet
    congr 2
    ext c c'
    exact hhb τ c c'
  unfold GlobalTheory.CompanionTheory.Ar.Cusp.PhiNormSq
  refine ⟨r, k, h, fun i => j (v i), fun τ c => j (q τ c), fun τ => (T τ).map e, hOF, hqe, happ, ?_, ?_⟩
  · intro τ
    rw [hdet τ]
    exact (map_ne_zero e).mpr (hT τ)
  · rw [hrel]
    congr 1
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [hdet τ, hg τ]

end GlobalTheory.CompanionTheory.Ar.Cusp.PhiBaseChange
