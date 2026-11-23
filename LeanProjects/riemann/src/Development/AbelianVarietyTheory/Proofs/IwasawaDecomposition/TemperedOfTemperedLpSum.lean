import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RestrictHomApply
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.WeilDeligne.PrimDecomp GlobalTheory.LocLanglands

namespace GlobalTheory.WeilDeligne.TemperedSummand

theorem map_pow_apply_of_comm {V V' : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup V']
    [Module ℂ V'] {N : Module.End ℂ V} {M : Module.End ℂ V'} (e : V →ₗ[ℂ] V')
    (hN : ∀ v, e (N v) = M (e v)) (i : ℕ) (v : V) : e ((N ^ i) v) = (M ^ i) (e v) := by
  induction i generalizing v with
  | zero => simp
  | succ i ih => rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, hN]

theorem isPurePair_of_retract {V V' : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup V']
    [Module ℂ V'] {q : ℝ} {f N : Module.End ℂ V} {g M : Module.End ℂ V'} (s : V' →ₗ[ℂ] V)
    (p : V →ₗ[ℂ] V') (hps : ∀ v, p (s v) = v) (hsf : ∀ v, s (g v) = f (s v))
    (hsN : ∀ v, s (M v) = N (s v)) (hpf : ∀ v, p (f v) = g (p v)) (hpN : ∀ v, p (N v) = M (p v))
    (hp : IsPurePair q f N) : IsPurePair q g M := by
  have hs : ∀ r v, v ∈ absSpace g r → s v ∈ absSpace f r :=
    fun r v hv => map_absSpace_le s hsf r ⟨v, hv, rfl⟩
  have hp' : ∀ r v, v ∈ absSpace f r → p v ∈ absSpace g r :=
    fun r v hv => map_absSpace_le p hpf r ⟨v, hv, rfl⟩
  have hr : LinearMap.range p = ⊤ := LinearMap.range_eq_top.mpr fun v => ⟨s v, hps v⟩
  refine ⟨?_, fun i => ⟨fun v hv => ?_, fun v hv v' hv' hvv => ?_, fun v hv => ?_⟩⟩
  · rw [eq_top_iff, ← hr, LinearMap.range_eq_map, ← hp.1, Submodule.map_iSup]
    exact iSup_mono fun i => map_absSpace_le p hpf _
  · have h1 := hp' _ _ ((hp.2 i).1 (hs _ v hv))
    rw [map_pow_apply_of_comm p hpN, hps] at h1
    exact h1
  · have h1 : s v = s v' := (hp.2 i).2.1 (hs _ v hv) (hs _ v' hv') (by
      rw [← map_pow_apply_of_comm s hsN, ← map_pow_apply_of_comm s hsN, hvv])
    rw [← hps v, h1, hps]
  · obtain ⟨u, hu, huv⟩ := (hp.2 i).2.2 (hs _ v hv)
    refine ⟨p u, hp' _ u hu, ?_⟩
    rw [← map_pow_apply_of_comm p hpN, huv, hps]

theorem tempered_of_tempered_lpSum : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω]
    [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E))
    (h : IsPlaceOver A w) (x y : WD h), (x.lpSum y).tempered → y.tempered := by
  intro E Ω _ _ _ _ _ A w h x y
  induction x using WD.ind with
  | hP m b =>
    induction y using WD.ind with
    | hP n c =>
      rw [WD.lpSum_mk, WD.tempered_mk, WD.tempered_mk]
      intro ht φ hφ
      exact isPurePair_of_retract (LinearMap.inr ℂ _ _) (LinearMap.snd ℂ _ _) (fun _ => rfl)
        (fun v => by simp) (fun v => by simp) (fun v => by simp) (fun v => by simp) (ht φ hφ)

end GlobalTheory.WeilDeligne.TemperedSummand
