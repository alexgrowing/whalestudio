import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactZeroInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBStabilizerGlobalEval
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSeminormWeylAlg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzValuedIntegralLinear
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableIdelesPowerDecay
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzMapBarrelledSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigALocalPartProduct
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilActionMapsSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaStabilizerExists
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine GlobalTheory.ThK.RealB
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ConeArchBCont

open GlobalTheory.ConeArchB GlobalTheory.ArchUniq GlobalTheory.RealWeil
open scoped Classical

theorem exists_bound_of_pointwise {D₁ D₂ : Type} [NormedAddCommGroup D₁] [NormedSpace ℝ D₁] [FiniteDimensional ℝ D₁]
    [NormedAddCommGroup D₂] [NormedSpace ℝ D₂] {ι : Type} (A : ι → SchwartzMap D₁ ℂ →L[ℂ] SchwartzMap D₂ ℂ)
    (h : ∀ f (a n : ℕ), ∃ C : ℝ, ∀ i, SchwartzMap.seminorm ℂ a n (A i f) ≤ C) (a n : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), ∀ i f,
      SchwartzMap.seminorm ℂ a n (A i f) ≤ C * (s.sup (schwartzSeminormFamily ℂ D₁ ℂ)) f := by
  haveI : BarrelledSpace ℂ (SchwartzMap D₁ ℂ) := GlobalTheory.schwartzMap_barrelledSpace D₁
  have hp := schwartz_withSeminorms ℂ D₁ ℂ
  have hq := schwartz_withSeminorms ℂ D₂ ℂ
  have hUE : UniformEquicontinuous ((↑) ∘ A) := hq.banach_steinhaus fun q x => by
    obtain ⟨C, hC⟩ := h x q.1 q.2
    exact ⟨C, Set.forall_mem_range.2 fun i => hC i⟩
  obtain ⟨p, hpc, hpk⟩ := (hq.uniformEquicontinuous_iff_exists_continuous_seminorm
    (fun i => (A i : SchwartzMap D₁ ℂ →ₗ[ℂ] SchwartzMap D₂ ℂ))).1 hUE (a, n)
  obtain ⟨s, C, -, hC⟩ := Seminorm.bound_of_continuous hp p hpc
  refine ⟨s, C, fun i f => ?_⟩
  calc SchwartzMap.seminorm ℂ a n (A i f) ≤ p f := hpk i f
    _ ≤ (C • s.sup (schwartzSeminormFamily ℂ D₁ ℂ)) f := hC f
    _ = _ := by rw [Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul]

end GlobalTheory.ConeArchBCont

namespace GlobalTheory.ConeArchBCont

open GlobalTheory.ConeArchB GlobalTheory.ArchUniq GlobalTheory.RealWeil
open scoped Classical

variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem shift_decay_lin {B : Base F E} {n d n₁ d₁ r s i₀ i₁ j₀ j₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁}
    {W₁ : Spc F E d₁} {M : Model σ X W} {M₁ : Model σ X₁ W₁} {H : Plane E n n₁} {H' : Plane E d d₁} (hB : B.IsGood σ)
    (hX : X.IsHerm σ B r s) (hH : H.IsAdapted σ B X X₁ i₀ i₁) (hH' : H'.IsAdapted σ B W W₁ j₀ j₁)
    (hM : M.IsGood B.ψ) (hM₁ : M₁.IsGood B.ψ) {e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁} (he : IsEv B M M₁ H.ι H'.ι (isoB H H') e)
    {ei : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n₁ × Fin d₁)} (hei : ∀ f, e (pure f M.vac) = pure (ei f) M₁.vac)
    (a k N : ℕ) : ∃ (s' : Finset (ℕ × ℕ)) (C : ℝ), ∀ (h : SInf F (Fin n × Fin d)) (l : (AE F E)ˣ),
      (1 + ∑ w, ‖piInf (B.emb w) (l : AE F E)‖) ^ N *
          SchwartzMap.seminorm ℂ a k (ei (locOpInf (M.co.rho B.ψ (partInf F (shiftB σ H H' l))) h)) ≤
        C * (s'.sup (schwartzSeminormFamily ℂ (Fin n × Fin d → mixedEmbedding.mixedSpace F) ℂ)) h := by
  have hψ := hB.std
  let L : (AE F E)ˣ → SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d) := fun l =>
    { toFun := fun f => locOpInf (M.co.rho B.ψ (partInf F (shiftB σ H H' l))) f
      map_add' := fun f g => by
        rw [(locOpInf_rho_eq hψ hM _ (f + g)).2, (locOpInf_rho_eq hψ hM _ f).2, (locOpInf_rho_eq hψ hM _ g).2, map_add]
      map_smul' := fun c f => by
        rw [(locOpInf_rho_eq hψ hM _ (c • f)).2, (locOpInf_rho_eq hψ hM _ f).2, map_smul, RingHom.id_apply]
      cont := GlobalTheory.ArchWeilCont.continuous_locOpInf_rho M.co hψ _ }
  let P : (AE F E)ˣ → ℝ := fun l => 1 + ∑ w, ‖piInf (B.emb w) (l : AE F E)‖
  have hP : ∀ l, 0 < P l := fun l => by positivity
  let A : (AE F E)ˣ → SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n₁ × Fin d₁) := fun l =>
    ((P l ^ N : ℝ) : ℂ) • ei.comp (L l)
  have hA : ∀ l h, SchwartzMap.seminorm ℂ a k (A l h) =
      P l ^ N * SchwartzMap.seminorm ℂ a k (ei (locOpInf (M.co.rho B.ψ (partInf F (shiftB σ H H' l))) h)) := by
    intro l h
    change SchwartzMap.seminorm ℂ a k (((P l ^ N : ℝ) : ℂ) • ei (L l h)) = _
    rw [map_smul_eq_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (pow_pos (hP l) N)]
    rfl
  obtain ⟨s', C, hC⟩ := exists_bound_of_pointwise A (fun f a' k' => by
    obtain ⟨C, hC⟩ := shift_decay hB hX hH hH' hM hM₁ he hei (T := Unit) (fun _ => f)
      (fun p _ => ⟨p f, fun _ => le_rfl⟩) (SchwartzMap.seminorm ℂ a' k')
      ((schwartz_withSeminorms ℂ _ ℂ).continuous_seminorm (a', k')) N
    refine ⟨C, fun l => ?_⟩
    change SchwartzMap.seminorm ℂ a' k' (((P l ^ N : ℝ) : ℂ) • ei (L l f)) ≤ C
    rw [map_smul_eq_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (pow_pos (hP l) N)]
    have h1 := hC () l
    change SchwartzMap.seminorm ℂ a' k' (ei (L l f)) ≤ C / P l ^ N at h1
    rw [le_div_iff₀ (pow_pos (hP l) N)] at h1
    linarith) a k
  exact ⟨s', C, fun h l => (hA l h).symm.le.trans (hC l h)⟩

theorem locOpInf_unif_bound_of_weil (hP : GlobalTheory.FunPr.Hypotheses₂) {n d : ℕ} {X : Spc F E n} {W : Spc F E d}
    (M : Model σ X W) {ψ : AddChar (AF F) ℂ} {χX χW : Chr F E} {om : Rep σ X W} (hcm : IsCMExt F E σ) (hψ : IsStd ψ)
    (hW : M.IsWeil ψ χX χW om) {S : Set (UA σ X.J)} (hS : IsCompact S) (hSU : ∀ k ∈ S, k ∈ UAt σ X (evI F)) (hSi : ∀ k ∈ S, k⁻¹ ∈ S)
    (s : Finset (ℕ × ℕ)) : ∃ (s' : Finset (ℕ × ℕ)) (C : ℝ), ∀ k ∈ S, ∀ f : SInf F (Fin n × Fin d),
      (s.sup (schwartzSeminormFamily ℂ (Fin n × Fin d → mixedEmbedding.mixedSpace F) ℂ)) (locOpInf (om (k, 1)) f) ≤
        C * (s'.sup (schwartzSeminormFamily ℂ (Fin n × Fin d → mixedEmbedding.mixedSpace F) ℂ)) f := by
  obtain ⟨Mb, hMb⟩ := GlobalTheory.ArchKX.archActX_bound M S hS
  obtain ⟨s', C, hC⟩ := GlobalTheory.ArchKX.unif_bound F ψ hψ (Fin n × Fin d) Mb s
  refine ⟨s', C, fun k hk f => ?_⟩
  have hkU : k ∈ UAt σ X (evI F) := hSU k hk
  have hex := GlobalTheory.ArchLocalityX.acts_arch_left hP F E σ n d X W M ψ χX χW om hcm hψ hW k hkU
  have hlin : IsLinearMap ℂ ⇑(om (k, 1)) := (om (k, 1)).isLinear
  let A : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d) :=
    { toFun := locOpInf (om (k, 1))
      map_add' := fun f g => by simpa using locOpInf_lin hlin hex 1 1 f g
      map_smul' := fun c f => by simpa using locOpInf_lin hlin hex c 0 f f }
  let L := IsLinearMap.mk' _ (GlobalTheory.ArchKX.isLinearMap_archActX M k)
  let N := IsLinearMap.mk' _ (GlobalTheory.ArchKX.isLinearMap_archActX M k⁻¹)
  have hLN : ∀ v, L (N v) = v := GlobalTheory.ArchKX.archActX_inv M k
  have hN : ∀ v, ‖N v‖ ≤ Mb * ‖v‖ := hMb k⁻¹ (hSi k hk)
  have h2 : ∀ f, ∫⁻ z, ‖A f z‖ₑ ^ 2 ≤ ∫⁻ z, ‖f z‖ₑ ^ 2 := fun f =>
    (GlobalTheory.ArchKX.lintegral_acts_eq_volume M ψ χX χW om hW k f (A f) (acts_locOpInf (hex f))).le
  have hI : ∀ v (f f' : SInf F (Fin n × Fin d)), ⇑f' = schrF (trP F (Fin n × Fin d)) v ⇑f →
      ⇑(A f') = schrF (trP F (Fin n × Fin d)) (L v) ⇑(A f) := fun v f f' h =>
    GlobalTheory.ArchKX.locOpInf_schrF M ψ χX χW om hψ hW k hkU hex v f f' h
  exact hC A L N hLN hN h2 hI f

end GlobalTheory.ConeArchBCont

namespace GlobalTheory.ThK.RealB

open GlobalTheory.ConeArchB GlobalTheory.ConeArchBCont GlobalTheory.ConeSoB GlobalTheory.XTermDecay GlobalTheory.HeisSchA GlobalTheory.DiffDecay GlobalTheory.EvZeroInf GlobalTheory.Published.Metaplectic
open scoped Classical

end GlobalTheory.ThK.RealB
