import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.HoweDuality.FactorApply
import Development.WeilBound.ThetaLifts.SphericalLattices.ThetaSubSup
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelInfAlt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsGaussianTransform
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsOrbitKernel
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsGaussianIdentity

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open UpperTheory.Lit.HoweDuality GlobalTheory.HoweGlobalPair

theorem UpperTheory.Lit.HoweDuality.radSph :
    ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {ψ : AddChar (AF F) ℂ} {om : Rep σ X W} {v : Pl F} {ω : UA σ X.J × UA σ W.J → Module.End ℂ (PositivityTheory.ThK.Fn F n d v)} {ρ : Matrix (Fin n) (Fin d) (AE F E) → Module.End ℂ (PositivityTheory.ThK.Fn F n d v)}, PositivityTheory.ThK.IsLocRep M ψ om v ω ρ → PositivityTheory.Sph.SphAt M ψ om v → ∀ K : Submodule ℂ ↥(SB (Fin n × Fin d → Fv F v)), relFin om v ≤ K → Stable (opFin om v) K → K ≠ ⊤ → Rad (opFin om v) (relFin om v) K := by
  intro F E _ _ _ _ _ σ n d X W M ψ om v ω ρ hL hS K hrel hst hne
  have one_mem : (1 : UA σ X.J) ∈ UAt σ X (evFin F v) := by
    show At _ (mat 1 - 1)
    have h1 : mat (1 : UA σ X.J) = 1 := Matrix.ext fun i => congrFun rfl
    rw [h1, sub_self]
    intro _ _
    simp
  have aug_le : augAt om v ≤ SB (Fin n × Fin d → Fv F v) := by
    refine Submodule.span_le.mpr ?_
    rintro z ⟨g, -, φ, hφ, φ₁, hφ₁, -, rfl⟩
    exact Submodule.sub_mem _ hφ₁ hφ
  have hG : ∀ h ∈ UAt σ W (evFin F v), ∃ g ∈ opFin om v,
      ∀ x : ↥(SB (Fin n × Fin d → Fv F v)), (g x : (Fin n × Fin d → Fv F v) → ℂ) = ω (1, h) x := by
    intro h hh
    refine ⟨{ toFun := fun x => ⟨ω (1, h) x, hL.pres 1 one_mem h hh x x.2⟩
              map_add' := fun x y => by ext1; simp
              map_smul' := fun c x => by ext1; simp }, ⟨h, hh, fun φ => ?_⟩, fun x => rfl⟩
    exact (hL.acts 1 one_mem h hh φ φ.2 _).mpr rfl
  choose g hgOp hgapp using hG
  obtain ⟨s, hs⟩ := hS ω ρ hL
  let s' : ↥(SB (Fin n × Fin d → Fv F v)) := ⟨s, hs.mem⟩
  have hgen : Gen (opFin om v) (relFin om v) s' := by
    intro P hP hPs hsP
    have hle : augAt om v ⊔ Submodule.span ℂ {z | ∃ h ∈ UAt σ W (evFin F v), z = ω (1, h) s} ≤
        P.map (SB (Fin n × Fin d → Fv F v)).subtype := by
      refine sup_le ?_ ?_
      · intro z hz
        exact ⟨⟨z, aug_le hz⟩, hP hz, rfl⟩
      · refine Submodule.span_le.mpr ?_
        rintro z ⟨h, hh, rfl⟩
        exact ⟨g h hh s', hPs _ (hgOp h hh) _ hsP, hgapp h hh s'⟩
    rw [eq_top_iff]
    intro x _
    obtain ⟨y, hy, hyx⟩ := hle (hs.gen x x.2)
    have hyx' : y = x := Subtype.ext hyx
    rw [← hyx']
    exact hy
  refine ⟨s', hgen, ?_⟩
  intro k hk
  obtain ⟨m, kk, w, c, hkw, hsum⟩ := hs.line k k.2
  let e : Module.End ℂ ↥(SB (Fin n × Fin d → Fv F v)) :=
    ((m + 1 : ℂ))⁻¹ • ∑ i, w i • g (kk i) (hkw i).1
  have he_app : ∀ x : ↥(SB (Fin n × Fin d → Fv F v)),
      (e x : (Fin n × Fin d → Fv F v) → ℂ) = ((m + 1 : ℂ))⁻¹ • ∑ i, w i • ω (1, kk i) x := by
    intro x
    simp [e, hgapp]
  have hm : (m + 1 : ℂ) ≠ 0 := by
    norm_cast
  have hes : e s' = s' := by
    ext1
    rw [he_app]
    have hsum' : ∑ i : Fin (m + 1), w i • ω (1, kk i) s = ∑ _i : Fin (m + 1), s :=
      Finset.sum_congr rfl (fun i _ => (hkw i).2)
    show ((m + 1 : ℂ))⁻¹ • ∑ i, w i • ω (1, kk i) s = s
    rw [hsum', Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ,
      smul_smul]
    push_cast
    rw [inv_mul_cancel₀ hm, one_smul]
  have heK : e k ∈ K := by
    show (((m + 1 : ℂ))⁻¹ • ∑ i, w i • g (kk i) (hkw i).1) k ∈ K
    rw [LinearMap.smul_apply, LinearMap.sum_apply]
    refine K.smul_mem _ (K.sum_mem fun i _ => ?_)
    rw [LinearMap.smul_apply]
    exact K.smul_mem _ (hst _ (hgOp _ _) k hk)
  have hrelv : e k - (((m + 1 : ℂ))⁻¹ * c) • s' ∈ relFin om v := by
    show ((e k - (((m + 1 : ℂ))⁻¹ * c) • s' : ↥(SB (Fin n × Fin d → Fv F v))) :
      (Fin n × Fin d → Fv F v) → ℂ) ∈ augAt om v
    rw [Submodule.coe_sub, Submodule.coe_smul, he_app]
    have hh := (augAt om v).smul_mem ((m + 1 : ℂ))⁻¹ hsum
    rw [smul_sub, smul_smul] at hh
    exact hh
  by_cases hc : ((m + 1 : ℂ))⁻¹ * c = 0
  · refine ⟨e, ?_, hes, ?_⟩
    · exact Subalgebra.smul_mem _ (Subalgebra.sum_mem _ fun i _ =>
        Subalgebra.smul_mem _ (Algebra.subset_adjoin (hgOp _ _)) _) _
    · rw [hc, zero_smul, sub_zero] at hrelv
      exact hrelv
  · exfalso
    apply hne
    apply hgen K hrel hst
    have h1 : (((m + 1 : ℂ))⁻¹ * c) • s' ∈ K := by
      have h2 := K.sub_mem heK (hrel hrelv)
      rwa [sub_sub_cancel] at h2
    have h3 := K.smul_mem (((m + 1 : ℂ))⁻¹ * c)⁻¹ h1
    rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at h3
