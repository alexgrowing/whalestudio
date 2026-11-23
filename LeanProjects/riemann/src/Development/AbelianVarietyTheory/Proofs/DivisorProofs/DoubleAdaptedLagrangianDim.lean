import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrPApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AtVecMulVecRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRelG
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLagrangianSetArchimedean
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerPreservesSchwartzRealStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TracePairingNondegenerateStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxSchroedingerArchimedeanActsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrangianInvariantFunctionalUniqueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrangianSetAdditiveSubgroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlanesGoodModelsDescentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlanesGoodModelsLocalStatement

noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ArchSch GlobalTheory.ArchSchB GlobalTheory.ArchSchA

namespace GlobalTheory.ArchSchA

theorem echA_add (s t : ℝ) : ech (s + t) = ech s * ech t := by
  simp only [ech, ← Complex.exp_add, Complex.ofReal_add]; ring_nf

theorem echA_zero : ech 0 = 1 := by simp [ech]

theorem schA_add {Y : Type} [AddCommGroup Y] [Module ℝ Y] (β : LinearMap.BilinForm ℝ Y) (a b a' b' : Y)
    (h : β a b' = β a' b) (f : Y → ℂ) : sch β (a + a') (b + b') f = sch β a b (sch β a' b' f) := by
  funext x
  simp only [sch, map_add, LinearMap.add_apply]
  rw [show x + (a + a') = x + a + a' by abel, ← mul_assoc, ← echA_add]
  congr 2
  rw [h]; ring

variable {F : Type} [Field F] [NumberField F]

theorem evIA_add (a b : AF F) : evI F (a + b) = evI F a + evI F b :=
  map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1 b.1

theorem evIA_zero : evI F 0 = 0 := map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)

theorem evIA_liftA (ξ : mixedEmbedding.mixedSpace F) : evI F (liftA F ξ) = ξ := by
  simp [evI, liftA]

theorem atA_liftA (ξ : mixedEmbedding.mixedSpace F) (u : AF F) (hu : evI F u = 0) : u * liftA F ξ = 0 := by
  have h1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hu)
  refine Prod.ext ?_ ?_
  · show u.1 * ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm ξ) = 0
    rw [h1, zero_mul]
  · show u.2 * 0 = 0
    rw [mul_zero]

theorem archA_add {κ : Type} (v w : κ → AF F) : arch F (v + w) = arch F v + arch F w := by
  funext i; simp [arch, evIA_add]

theorem archA_zero {κ : Type} : arch F (0 : κ → AF F) = 0 := by
  funext i; simp [arch, evIA_zero]

end GlobalTheory.ArchSchA

open GlobalTheory.ArchSch GlobalTheory.ArchSchB GlobalTheory.ArchSchA in

theorem GlobalTheory.ArchSchA.lagSetA_submodule : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁} (M : Model σ X W) (M₁ : Model σ X₁ W₁) (H : Plane E n n₁) (H' : Plane E d d₁),
    (0 ∈ lagSetA M M₁ H H') ∧ (∀ l ∈ lagSetA M M₁ H H', ∀ l' ∈ lagSetA M M₁ H H', l + l' ∈ lagSetA M M₁ H H') ∧
    ∀ t : ℝ, ∀ l ∈ lagSetA M M₁ H H', t • l ∈ lagSetA M M₁ H H' := by
  intro F E _ _ _ _ _ σ n d n₁ d₁ X W X₁ W₁ M M₁ H H'
  have e2 : ∀ (a : AF F) (c : Fin d₁ → AE F E),
      Matrix.vecMulVec (incV F H.x) (incM F H'.ι *ᵥ (a • c)) = a • Matrix.vecMulVec (incV F H.x) (incM F H'.ι *ᵥ c) := by
    intro a c
    rw [Matrix.mulVec_smul]
    ext i j; simp [Matrix.vecMulVec_apply, mul_smul_comm]
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨0, 0, 0, lagL_at_zero, lagL_at_zero, lagL_at_zero, by simp [lagL_arch_zero], ?_⟩
    simp [lagL_arch_zero, zero_vecMulVec', vecMulVec_zero']
    rfl
  · rintro l ⟨y, c, z, hy, hc, hz, hz1, rfl⟩ l' ⟨y', c', z', hy', hc', hz', hz1', rfl⟩
    refine ⟨y + y', c + c', z + z', lagL_at_add hy hy', lagL_at_add hc hc', lagL_at_add hz hz', ?_, ?_⟩
    · rw [map_add, Prod.fst_add, lagL_arch_add, hz1, hz1', add_zero]
    · have : Matrix.vecMulVec (y + y') (incV F H'.x) + Matrix.vecMulVec (incV F H.x) (incM F H'.ι *ᵥ (c + c')) +
            incM F H.ι * (z + z') * (incM F H'.ι)ᵀ =
          (Matrix.vecMulVec y (incV F H'.x) + Matrix.vecMulVec (incV F H.x) (incM F H'.ι *ᵥ c) +
            incM F H.ι * z * (incM F H'.ι)ᵀ) +
          (Matrix.vecMulVec y' (incV F H'.x) + Matrix.vecMulVec (incV F H.x) (incM F H'.ι *ᵥ c') +
            incM F H.ι * z' * (incM F H'.ι)ᵀ) := by
        rw [Matrix.add_vecMulVec, Matrix.mulVec_add, Matrix.vecMulVec_add, Matrix.mul_add, Matrix.add_mul]; abel
      rw [this]
      ext : 1 <;> simp only [Prod.fst_add, Prod.snd_add, LinearEquiv.map_add, lagL_arch_add] <;> abel
  · rintro t l ⟨y, c, z, hy, hc, hz, hz1, rfl⟩
    refine ⟨realAd F t • y, realAd F t • c, realAd F t • z, lagL_at_smul _ hy, lagL_at_smul _ hc, lagL_at_smul _ hz,
      ?_, ?_⟩
    · rw [map_smul, Prod.smul_fst, lagL_arch_smul, hz1, smul_zero]
    · have : Matrix.vecMulVec (realAd F t • y) (incV F H'.x) +
            Matrix.vecMulVec (incV F H.x) (incM F H'.ι *ᵥ (realAd F t • c)) +
            incM F H.ι * (realAd F t • z) * (incM F H'.ι)ᵀ =
          realAd F t • (Matrix.vecMulVec y (incV F H'.x) + Matrix.vecMulVec (incV F H.x) (incM F H'.ι *ᵥ c) +
            incM F H.ι * z * (incM F H'.ι)ᵀ) := by
        rw [← lagL_smul_vmv, e2, smul_add, smul_add, Matrix.mul_smul, Matrix.smul_mul]
      rw [this, map_smul, Prod.smul_fst, Prod.smul_snd, lagL_arch_smul, lagL_arch_smul]
      rfl

open GlobalTheory.ArchSch GlobalTheory.ArchSchB GlobalTheory.ArchSchA in

theorem GlobalTheory.ArchSchA.infRelA_proportional : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d n₁ d₁ r s r' s' i₀ i₁ j₀ j₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁) (H : Plane E n n₁)
    (H' : Plane E d d₁) (M : Model σ X W) (M₁ : Model σ X₁ W₁), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' →
    M.IsGood B.ψ → H.IsAdapted σ B X X₁ j₀ j₁ → H'.IsAdapted σ B W W₁ i₀ i₁ → M₁.IsGood B.ψ →
    ∀ T T' : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n₁ × Fin d₁), T ≠ 0 →
    GlobalTheory.ThK.EvFactor.InfRelG B M M₁ H.ι H'.ι (isoA H H') T → GlobalTheory.ThK.EvFactor.InfRelG B M M₁ H.ι H'.ι (isoA H H') T' →
    ∃ c : ℂ, T' = c • T := by
  intro _hP F E _ _ _ _ _ σ B n d n₁ d₁ r s r' s' i₀ i₁ j₀ j₁ X W X₁ W₁ H H' M M₁ hB hX hW _hM hH hH' _hM₁ T T' hT hR hR'
  classical
  have atι : ∀ z : Matrix (Fin n₁) (Fin d₁) (AE F E), At (evI F) z →
      At (evI F) (incM F H.ι * z * (incM F H'.ι)ᵀ) := by
    intro z hz u hu
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, hz u hu]
    simp
  have F1 : ∀ S : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n₁ × Fin d₁),
      GlobalTheory.ThK.EvFactor.InfRelG B M M₁ H.ι H'.ι (isoA H H') S →
      ∀ z, At (evI F) z → ∀ f f₁ : SInf F (Fin n × Fin d), ∀ g₁ : SInf F (Fin n₁ × Fin d₁),
        ⇑f₁ = sch (trP F _) (arch F (M.co.e (incM F H.ι * z * (incM F H'.ι)ᵀ)).1)
          (arch F (M.co.e (incM F H.ι * z * (incM F H'.ι)ᵀ)).2) ⇑f →
        ⇑g₁ = sch (trP F _) (arch F (M₁.co.e z).1) (arch F (M₁.co.e z).2) ⇑(S f) → S f₁ = g₁ := by
    intro S hS z hz f f₁ g₁ h1 h2
    exact hS.1 z hz f f₁ (GlobalTheory.T.darboux_schroedinger_archimedean_acts M.co B.ψ hB.std (incM F H.ι * z * (incM F H'.ι)ᵀ) (atι z hz) f f₁ h1) g₁
      (GlobalTheory.T.darboux_schroedinger_archimedean_acts M₁.co B.ψ hB.std z hz (S f) g₁ h2)
  have F2 : ∀ S : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n₁ × Fin d₁),
      GlobalTheory.ThK.EvFactor.InfRelG B M M₁ H.ι H'.ι (isoA H H') S →
      ∀ u ∈ isoA (F := F) H H', At (evI F) u → ∀ f f₁ : SInf F (Fin n × Fin d),
        ⇑f₁ = sch (trP F _) (arch F (M.co.e u).1) (arch F (M.co.e u).2) ⇑f → S f₁ = S f :=
    fun S hS u hu hat f f₁ h => hS.2 u hu hat f f₁ (GlobalTheory.T.darboux_schroedinger_archimedean_acts M.co B.ψ hB.std u hat f f₁ h)
  obtain ⟨h0, hadd, hsmul⟩ := GlobalTheory.ArchSchA.lagSetA_submodule M M₁ H H'
  have hiso := GlobalTheory.T.adapted_planes_good_models_descent B M M₁ H H' hB hX hW hH hH'
  have hco := GlobalTheory.T.adapted_planes_good_models_local B M M₁ H H' hB hX hW hH hH'
  let Λ : Submodule ℝ ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) :=
    { carrier := lagSetA M M₁ H H'
      add_mem' := fun ha hb => hadd _ ha _ hb
      zero_mem' := h0
      smul_mem' := fun t l hl => hsmul t l hl }
  let ℓ : (SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n₁ × Fin d₁)) → SInf F (Fin n × Fin d) →L[ℂ] ℂ := fun S =>
    ((BoundedContinuousFunction.evalCLM ℂ (0 : Fin n₁ × Fin d₁ → mixedEmbedding.mixedSpace F)).comp
      (SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ ℂ)).comp S
  have hℓ : ∀ S f, ℓ S f = S f 0 := fun _ _ => rfl
  have eadd : ∀ x y : Matrix (Fin n) (Fin d) (AE F E),
      arch F (M.co.e (x + y)).1 = arch F (M.co.e x).1 + arch F (M.co.e y).1 ∧
      arch F (M.co.e (x + y)).2 = arch F (M.co.e x).2 + arch F (M.co.e y).2 := fun x y =>
    ⟨by rw [map_add, Prod.fst_add, archA_add], by rw [map_add, Prod.snd_add, archA_add]⟩
  have inv : ∀ S : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n₁ × Fin d₁),
      GlobalTheory.ThK.EvFactor.InfRelG B M M₁ H.ι H'.ι (isoA H H') S →
      ∀ l ∈ Λ, ∀ f g : SInf F (Fin n × Fin d), ⇑g = sch (trP F _) l.1 l.2 ⇑f → ℓ S g = ℓ S f := by
    intro S hS l hl f g hg
    obtain ⟨y, c, z, hy, hc, hz, hz1, rfl⟩ := hl
    set u₁ := Matrix.vecMulVec y (incV F H'.x) with hu₁
    set u₂ := Matrix.vecMulVec (incV F H.x) (incM F H'.ι *ᵥ c) with hu₂
    set w := incM F H.ι * z * (incM F H'.ι)ᵀ with hw
    have hat1 : At (evI F) u₁ := at_vecMulVec_left hy _
    have hat2 : At (evI F) u₂ := at_vecMulVec_right _ (at_mulVec _ hc)
    have m1 : (arch F (M.co.e u₁).1, arch F (M.co.e u₁).2) ∈ lagSetA M M₁ H H' :=
      mem_lagSetA_y M M₁ H H' hy
    have m2 : (arch F (M.co.e (u₂ + w)).1, arch F (M.co.e (u₂ + w)).2) ∈ lagSetA M M₁ H H' :=
      mem_lagSetA_cz M M₁ H H' hc hz hz1
    have m3 : (arch F (M.co.e u₂).1, arch F (M.co.e u₂).2) ∈ lagSetA M M₁ H H' :=
      mem_lagSetA_c M M₁ H H' hc
    have m4 : (arch F (M.co.e w).1, arch F (M.co.e w).2) ∈ lagSetA M M₁ H H' :=
      mem_lagrangian_set_archimedean M M₁ H H' hz hz1
    have hsplit : ⇑g = sch (trP F _) (arch F (M.co.e u₁).1) (arch F (M.co.e u₁).2)
        (sch (trP F _) (arch F (M.co.e u₂).1) (arch F (M.co.e u₂).2)
          (sch (trP F _) (arch F (M.co.e w).1) (arch F (M.co.e w).2) ⇑f)) := by
      rw [hg]
      dsimp only
      rw [add_assoc, (eadd _ _).1, (eadd _ _).2, schA_add _ _ _ _ _ (hiso _ m1 _ m2), (eadd _ _).1, (eadd _ _).2,
        schA_add _ _ _ _ _ (hiso _ m3 _ m4)]
    obtain ⟨h₃, hh₃⟩ := GlobalTheory.T.schroedinger_preserves_schwartz_real (trP F _) (arch F (M.co.e w).1) (arch F (M.co.e w).2) f
    obtain ⟨h₂, hh₂⟩ := GlobalTheory.T.schroedinger_preserves_schwartz_real (trP F _) (arch F (M.co.e u₂).1) (arch F (M.co.e u₂).2) h₃
    obtain ⟨g₁, hg₁⟩ := GlobalTheory.T.schroedinger_preserves_schwartz_real (trP F _) (arch F (M₁.co.e z).1) (arch F (M₁.co.e z).2) (S f)
    rw [← hh₃, ← hh₂] at hsplit
    rw [hℓ, hℓ, F2 S hS u₁ (Or.inl ⟨y, rfl⟩) hat1 h₂ g hsplit, F2 S hS u₂ (Or.inr ⟨c, rfl⟩) hat2 h₃ h₂ hh₂,
      F1 S hS z hz f h₃ g₁ hh₃ hg₁, hg₁]
    simp [sch, hz1, echA_zero]
  have zξ : ∀ ξ : Fin n₁ × Fin d₁ → mixedEmbedding.mixedSpace F, ∃ z : Matrix (Fin n₁) (Fin d₁) (AE F E),
      At (evI F) z ∧ arch F (M₁.co.e z).1 = ξ ∧ arch F (M₁.co.e z).2 = 0 := by
    intro ξ
    refine ⟨M₁.co.e.symm (fun i => liftA F (ξ i), 0), fun u hu => ?_, ?_, ?_⟩
    · rw [← LinearEquiv.map_smul]
      have : u • ((fun i => liftA F (ξ i), 0) : (Fin n₁ × Fin d₁ → AF F) × (Fin n₁ × Fin d₁ → AF F)) = 0 := by
        refine Prod.ext (funext fun i => ?_) (by simp)
        simp [atA_liftA (ξ i) u hu]
      rw [this, map_zero]
    · funext i; simp [arch, evIA_liftA]
    · simp [archA_zero]
  have key : ∀ (f : SInf F (Fin n × Fin d)) (ξ : Fin n₁ × Fin d₁ → mixedEmbedding.mixedSpace F),
      ∃ h : SInf F (Fin n × Fin d), ∀ S : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n₁ × Fin d₁),
        GlobalTheory.ThK.EvFactor.InfRelG B M M₁ H.ι H'.ι (isoA H H') S → S h 0 = S f ξ := by
    intro f ξ
    obtain ⟨z, hz, hz1, hz2⟩ := zξ ξ
    obtain ⟨h, hh⟩ := GlobalTheory.T.schroedinger_preserves_schwartz_real (trP F _) (arch F (M.co.e (incM F H.ι * z * (incM F H'.ι)ᵀ)).1)
      (arch F (M.co.e (incM F H.ι * z * (incM F H'.ι)ᵀ)).2) f
    refine ⟨h, fun S hS => ?_⟩
    obtain ⟨g₁, hg₁⟩ := GlobalTheory.T.schroedinger_preserves_schwartz_real (trP F _) (arch F (M₁.co.e z).1) (arch F (M₁.co.e z).2) (S f)
    rw [F1 S hS z hz f h g₁ hh hg₁, hg₁]
    simp [sch, hz1, hz2, echA_zero]
  have hne : ℓ T ≠ 0 := by
    intro h
    apply hT
    refine ContinuousLinearMap.ext fun f => SchwartzMap.ext fun ξ => ?_
    obtain ⟨h', hh'⟩ := key f ξ
    have := congrArg (fun L => L h') h
    simp only [hℓ, ContinuousLinearMap.zero_apply] at this
    rw [← hh' T hR, this]
    rfl
  have hiso' : ∀ l ∈ Λ, ∀ l' ∈ Λ, trP F (Fin n × Fin d) l.1 l'.2 = trP F (Fin n × Fin d) l'.1 l.2 :=
    fun l hl l' hl' => hiso l hl l' hl'
  have hco' : ∀ v : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F),
      (∀ l ∈ Λ, trP F (Fin n × Fin d) v.1 l.2 = trP F (Fin n × Fin d) l.1 v.2) → v ∈ Λ := fun v hv => hco v hv
  have hT1 := inv T hR
  have hT2 := inv T' hR'
  obtain ⟨C, hC'⟩ := GlobalTheory.T.aux_statement_2 (Y := Fin n × Fin d → mixedEmbedding.mixedSpace F)
    (trP F (Fin n × Fin d)) (GlobalTheory.T.trace_pairing_nondegenerate F (Fin n × Fin d)) Λ hiso' hco' (ℓ T) (ℓ T') hT1 hT2 hne
  refine ⟨C, ContinuousLinearMap.ext fun f => SchwartzMap.ext fun ξ => ?_⟩
  obtain ⟨h', hh'⟩ := key f ξ
  have := congrArg (fun L => L h') hC'
  simp only [hℓ, ContinuousLinearMap.smul_apply, smul_eq_mul] at this
  rw [← hh' T' hR', this, hh' T hR]
  rfl
