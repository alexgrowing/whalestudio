import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrPApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerPreservesSchwartzRealStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TracePairingNondegenerateStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxSchroedingerArchimedeanActsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrangianInvariantFunctionalUniqueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrangianSetAdditiveSubgroupStatement

noncomputable section

namespace GlobalTheory.ArchSch

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

theorem ech_add (s t : ℝ) : ech (s + t) = ech s * ech t := by
  simp only [ech, ← Complex.exp_add, Complex.ofReal_add]; ring_nf

theorem ech_zero : ech 0 = 1 := by simp [ech]

theorem sch_add {Y : Type} [AddCommGroup Y] [Module ℝ Y] (β : LinearMap.BilinForm ℝ Y) (a b a' b' : Y)
    (h : β a b' = β a' b) (f : Y → ℂ) : sch β (a + a') (b + b') f = sch β a b (sch β a' b' f) := by
  funext x
  simp only [sch, map_add, LinearMap.add_apply]
  rw [show x + (a + a') = x + a + a' by abel, ← mul_assoc, ← ech_add]
  congr 2
  rw [h]; ring

variable {F : Type} [Field F] [NumberField F]

theorem evI_add (a b : AF F) : evI F (a + b) = evI F a + evI F b := by
  exact map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1 b.1

theorem evI_zero : evI F 0 = 0 := by
  exact map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)

theorem evI_liftA (ξ : mixedEmbedding.mixedSpace F) : evI F (liftA F ξ) = ξ := by
  simp [evI, liftA]

theorem at_liftA (ξ : mixedEmbedding.mixedSpace F) (u : AF F) (hu : evI F u = 0) : u * liftA F ξ = 0 := by
  have h1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hu)
  refine Prod.ext ?_ ?_
  · show u.1 * ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm ξ) = 0
    rw [h1, zero_mul]
  · show u.2 * 0 = 0
    rw [mul_zero]

theorem arch_add {κ : Type} (v w : κ → AF F) : arch F (v + w) = arch F v + arch F w := by
  funext i; simp [arch, evI_add]

theorem arch_zero {κ : Type} : arch F (0 : κ → AF F) = 0 := by
  funext i; simp [arch, evI_zero]

end GlobalTheory.ArchSch

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

open GlobalTheory.ArchSch in

theorem GlobalTheory.ArchSch.infRel_proportional : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d d₁ r s r' s' i₀ i₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (M : Model σ X W)
    (M₁ : Model σ X W₁), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' → M.IsGood B.ψ → H'.IsAdapted σ B W W₁ i₀ i₁ →
    M₁.IsGood B.ψ → ∀ T T' : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d₁), T ≠ 0 →
    GlobalTheory.ThK.EvUniq.InfRel B M M₁ H' T → GlobalTheory.ThK.EvUniq.InfRel B M M₁ H' T' → ∃ c : ℂ, T' = c • T := by
  intro hP F E _ _ _ _ _ σ B n d d₁ r s r' s' i₀ i₁ X W W₁ H' M M₁ hB hX hW hM hH hM₁ T T' hT hR hR'
  classical
  have atι : ∀ z : Matrix (Fin n) (Fin d₁) (AE F E), At (evI F) z → At (evI F) (incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ) := by
    intro z hz u hu
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, hz u hu]
    simp
  have F1 : ∀ S : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d₁), GlobalTheory.ThK.EvUniq.InfRel B M M₁ H' S →
      ∀ z, At (evI F) z → ∀ f f₁ : SInf F (Fin n × Fin d), ∀ g₁ : SInf F (Fin n × Fin d₁),
        ⇑f₁ = sch (trP F _) (arch F (M.co.e (incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ)).1) (arch F (M.co.e (incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ)).2) ⇑f →
        ⇑g₁ = sch (trP F _) (arch F (M₁.co.e z).1) (arch F (M₁.co.e z).2) ⇑(S f) → S f₁ = g₁ := by
    intro S hS z hz f f₁ g₁ h1 h2
    exact hS.1 z hz f f₁ (GlobalTheory.T.darboux_schroedinger_archimedean_acts M.co B.ψ hB.std (incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ) (atι z hz) f f₁ h1) g₁
      (GlobalTheory.T.darboux_schroedinger_archimedean_acts M₁.co B.ψ hB.std z hz (S f) g₁ h2)
  have F2 : ∀ S : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d₁), GlobalTheory.ThK.EvUniq.InfRel B M M₁ H' S →
      ∀ u ∈ iso0 (F := F) n H', At (evI F) u → ∀ f f₁ : SInf F (Fin n × Fin d),
        ⇑f₁ = sch (trP F _) (arch F (M.co.e u).1) (arch F (M.co.e u).2) ⇑f → S f₁ = S f :=
    fun S hS u hu hat f f₁ h => hS.2 u hu hat f f₁ (GlobalTheory.T.darboux_schroedinger_archimedean_acts M.co B.ψ hB.std u hat f f₁ h)
  obtain ⟨h0, hadd, hsmul, hiso, hco⟩ := GlobalTheory.T.plane_transform_restriction B n d d₁ r s r' s' i₀ i₁ X W W₁ H' M M₁ hB hX hW hH
  let Λ : Submodule ℝ ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) :=
    { carrier := lagSet M M₁ H'
      add_mem' := fun ha hb => hadd _ ha _ hb
      zero_mem' := h0
      smul_mem' := fun t l hl => hsmul t l hl }
  let ℓ : (SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d₁)) → SInf F (Fin n × Fin d) →L[ℂ] ℂ := fun S =>
    ((BoundedContinuousFunction.evalCLM ℂ (0 : Fin n × Fin d₁ → mixedEmbedding.mixedSpace F)).comp
      (SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ ℂ)).comp S
  have hℓ : ∀ S f, ℓ S f = S f 0 := fun _ _ => rfl
  have inv : ∀ S : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d₁), GlobalTheory.ThK.EvUniq.InfRel B M M₁ H' S →
      ∀ l ∈ Λ, ∀ f g : SInf F (Fin n × Fin d), ⇑g = sch (trP F _) l.1 l.2 ⇑f → ℓ S g = ℓ S f := by
    intro S hS l hl f g hg
    obtain ⟨u, hu, hat, z, hz, hz1, rfl⟩ := hl
    have mu : (arch F (M.co.e u).1, arch F (M.co.e u).2) ∈ lagSet M M₁ H' :=
      ⟨u, hu, hat, 0, fun _ _ => smul_zero _, by simp [arch_zero], by simp⟩
    have mz : (arch F (M.co.e (incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ)).1, arch F (M.co.e (incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ)).2) ∈ lagSet M M₁ H' :=
      ⟨0, ⟨0, by simp⟩, fun _ _ => smul_zero _, z, hz, hz1, by simp⟩
    have hsplit : ⇑g = sch (trP F _) (arch F (M.co.e u).1) (arch F (M.co.e u).2)
        (sch (trP F _) (arch F (M.co.e (incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ)).1) (arch F (M.co.e (incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ)).2) ⇑f) := by
      have e1 : arch F (M.co.e (u + (incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ))).1 = arch F (M.co.e u).1 + arch F (M.co.e (incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ)).1 := by
        rw [map_add, Prod.fst_add, arch_add]
      have e2 : arch F (M.co.e (u + (incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ))).2 = arch F (M.co.e u).2 + arch F (M.co.e (incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ)).2 := by
        rw [map_add, Prod.snd_add, arch_add]
      rw [hg]
      dsimp only
      rw [e1, e2, sch_add _ _ _ _ _ (hiso _ mu _ mz)]
    obtain ⟨h₁, hh₁⟩ := GlobalTheory.T.schroedinger_preserves_schwartz_real (trP F _) (arch F (M.co.e (incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ)).1) (arch F (M.co.e (incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ)).2) f
    obtain ⟨g₁, hg₁⟩ := GlobalTheory.T.schroedinger_preserves_schwartz_real (trP F _) (arch F (M₁.co.e z).1) (arch F (M₁.co.e z).2) (S f)
    rw [← hh₁] at hsplit
    rw [hℓ, hℓ, F2 S hS u hu hat h₁ g hsplit, F1 S hS z hz f h₁ g₁ hh₁ hg₁, hg₁]
    simp [sch, hz1, ech_zero]
  have zξ : ∀ ξ : Fin n × Fin d₁ → mixedEmbedding.mixedSpace F, ∃ z : Matrix (Fin n) (Fin d₁) (AE F E),
      At (evI F) z ∧ arch F (M₁.co.e z).1 = ξ ∧ arch F (M₁.co.e z).2 = 0 := by
    intro ξ
    refine ⟨M₁.co.e.symm (fun i => liftA F (ξ i), 0), fun u hu => ?_, ?_, ?_⟩
    · rw [← LinearEquiv.map_smul]
      have : u • ((fun i => liftA F (ξ i), 0) : (Fin n × Fin d₁ → AF F) × (Fin n × Fin d₁ → AF F)) = 0 := by
        refine Prod.ext (funext fun i => ?_) (by simp)
        simp [at_liftA (ξ i) u hu]
      rw [this, map_zero]
    · funext i; simp [arch, evI_liftA]
    · simp [arch_zero]
  have key : ∀ (f : SInf F (Fin n × Fin d)) (ξ : Fin n × Fin d₁ → mixedEmbedding.mixedSpace F),
      ∃ h : SInf F (Fin n × Fin d), ∀ S : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d₁),
        GlobalTheory.ThK.EvUniq.InfRel B M M₁ H' S → S h 0 = S f ξ := by
    intro f ξ
    obtain ⟨z, hz, hz1, hz2⟩ := zξ ξ
    obtain ⟨h, hh⟩ := GlobalTheory.T.schroedinger_preserves_schwartz_real (trP F _) (arch F (M.co.e (incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ)).1) (arch F (M.co.e (incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ)).2) f
    refine ⟨h, fun S hS => ?_⟩
    obtain ⟨g₁, hg₁⟩ := GlobalTheory.T.schroedinger_preserves_schwartz_real (trP F _) (arch F (M₁.co.e z).1) (arch F (M₁.co.e z).2) (S f)
    rw [F1 S hS z hz f h g₁ hh hg₁, hg₁]
    simp [sch, hz1, hz2, ech_zero]
  have hne : ℓ T ≠ 0 := by
    intro h
    apply hT
    refine ContinuousLinearMap.ext fun f => SchwartzMap.ext fun ξ => ?_
    obtain ⟨h', hh'⟩ := key f ξ
    have := congrArg (fun L => L h') h
    simp only [hℓ, ContinuousLinearMap.zero_apply] at this
    rw [← hh' T hR, this]
    rfl
  have hiso' : ∀ l ∈ Λ, ∀ l' ∈ Λ, trP F (Fin n × Fin d) l.1 l'.2 = trP F (Fin n × Fin d) l'.1 l.2 := fun l hl l' hl' => hiso l hl l' hl'
  have hco' : ∀ v : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F),
      (∀ l ∈ Λ, trP F (Fin n × Fin d) v.1 l.2 = trP F (Fin n × Fin d) l.1 v.2) → v ∈ Λ := fun v hv => hco v hv
  have hT1 := inv T hR
  have hT2 := inv T' hR'
  obtain ⟨C, hC⟩ := GlobalTheory.T.aux_statement_2 (Y := Fin n × Fin d → mixedEmbedding.mixedSpace F) (trP F (Fin n × Fin d))
    (GlobalTheory.T.trace_pairing_nondegenerate F (Fin n × Fin d)) Λ hiso' hco' (ℓ T) (ℓ T') hT1 hT2 hne
  refine ⟨C, ContinuousLinearMap.ext fun f => SchwartzMap.ext fun ξ => ?_⟩
  obtain ⟨h', hh'⟩ := key f ξ
  have := congrArg (fun L => L h') hC
  simp only [hℓ, ContinuousLinearMap.smul_apply, smul_eq_mul] at this
  rw [← hh' T' hR', this, hh' T hR]
  rfl
