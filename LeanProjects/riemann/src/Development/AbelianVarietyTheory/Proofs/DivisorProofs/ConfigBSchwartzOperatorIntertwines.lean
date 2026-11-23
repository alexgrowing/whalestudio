import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrPApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRelAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerArchimedean
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AtVecMulVecRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrangianSetSubspaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleAdaptedLagrangianEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleAdaptedLagrangianIntersectStatement

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

open GlobalTheory.ArchSch GlobalTheory.ArchSchB in

theorem GlobalTheory.ArchSchB.infRelB_proportional : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b)
    (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ T T' : SInf F (Fin (b + 2) × Fin (a + (b + 2))) →L[ℂ] SInf F (Fin b × Fin (a + b)), T ≠ 0 →
    GlobalTheory.ThK.EvUniqB.InfRel B G.M' G₁.M' H.ι H'.ι (isoB H H') T → GlobalTheory.ThK.EvUniqB.InfRel B G.M' G₁.M' H.ι H'.ι (isoB H H') T' →
    ∃ c : ℂ, T' = c • T := by
  intro _hP F E _ _ _ _ _ σ B a b G G₁ H H' hC X om om' om₁ om₁' hT3 _hT3₁ T T' hT hR hR'
  classical
  have hB : B.IsGood σ := hT3.base
  have hX : G.V'.IsHerm σ B G.q (b + 2 - G.q) := hT3.geo.hV'
  have hW : G.W.IsSkew σ B (a + (b + 2) - (G.p + G.q)) (G.p + G.q) := hT3.geo.hW
  have hH : H.IsAdapted σ B G.V' G₁.V' 0 (b + 1) := hC.hH
  have hH' : H'.IsAdapted σ B G.W G₁.W a (a + b + 1) := hC.hH'
  have atι : ∀ z : Matrix (Fin b) (Fin (a + b)) (AE F E), At (evI F) z →
      At (evI F) (incM F H.ι * z * (incM F H'.ι)ᵀ) := by
    intro z hz u hu
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, hz u hu]
    simp
  have F1 : ∀ S : SInf F (Fin (b + 2) × Fin (a + (b + 2))) →L[ℂ] SInf F (Fin b × Fin (a + b)),
      GlobalTheory.ThK.EvUniqB.InfRel B G.M' G₁.M' H.ι H'.ι (isoB H H') S →
      ∀ z, At (evI F) z → ∀ f f₁ : SInf F (Fin (b + 2) × Fin (a + (b + 2))), ∀ g₁ : SInf F (Fin b × Fin (a + b)),
        ⇑f₁ = sch (trP F _) (arch F (G.M'.co.e (incM F H.ι * z * (incM F H'.ι)ᵀ)).1)
          (arch F (G.M'.co.e (incM F H.ι * z * (incM F H'.ι)ᵀ)).2) ⇑f →
        ⇑g₁ = sch (trP F _) (arch F (G₁.M'.co.e z).1) (arch F (G₁.M'.co.e z).2) ⇑(S f) → S f₁ = g₁ := by
    intro S hS z hz f f₁ g₁ h1 h2
    exact hS.1 z hz f f₁ (GlobalTheory.T.darboux_schroedinger_archimedean_acts G.M'.co B.ψ hB.std (incM F H.ι * z * (incM F H'.ι)ᵀ) (atι z hz) f f₁ h1) g₁
      (GlobalTheory.T.darboux_schroedinger_archimedean_acts G₁.M'.co B.ψ hB.std z hz (S f) g₁ h2)
  have F2 : ∀ S : SInf F (Fin (b + 2) × Fin (a + (b + 2))) →L[ℂ] SInf F (Fin b × Fin (a + b)),
      GlobalTheory.ThK.EvUniqB.InfRel B G.M' G₁.M' H.ι H'.ι (isoB H H') S →
      ∀ u ∈ isoB (F := F) H H', At (evI F) u → ∀ f f₁ : SInf F (Fin (b + 2) × Fin (a + (b + 2))),
        ⇑f₁ = sch (trP F _) (arch F (G.M'.co.e u).1) (arch F (G.M'.co.e u).2) ⇑f → S f₁ = S f :=
    fun S hS u hu hat f f₁ h => hS.2 u hu hat f f₁ (GlobalTheory.T.darboux_schroedinger_archimedean_acts G.M'.co B.ψ hB.std u hat f f₁ h)
  obtain ⟨h0, hadd, hsmul⟩ := GlobalTheory.T.lagrangian_set_subspace G.M' G₁.M' H H'
  have hiso := GlobalTheory.T.double_adapted_lagrangian_eq B G.M' G₁.M' H H' hB hX hW hH hH'
  have hco := GlobalTheory.T.double_adapted_lagrangian_intersect B G.M' G₁.M' H H' hB hX hW hH hH'
  let Λ : Submodule ℝ ((Fin (b + 2) × Fin (a + (b + 2)) → mixedEmbedding.mixedSpace F) ×
      (Fin (b + 2) × Fin (a + (b + 2)) → mixedEmbedding.mixedSpace F)) :=
    { carrier := lagSetB G.M' G₁.M' H H'
      add_mem' := fun ha hb => hadd _ ha _ hb
      zero_mem' := h0
      smul_mem' := fun t l hl => hsmul t l hl }
  let ℓ : (SInf F (Fin (b + 2) × Fin (a + (b + 2))) →L[ℂ] SInf F (Fin b × Fin (a + b))) →
      SInf F (Fin (b + 2) × Fin (a + (b + 2))) →L[ℂ] ℂ := fun S =>
    ((BoundedContinuousFunction.evalCLM ℂ (0 : Fin b × Fin (a + b) → mixedEmbedding.mixedSpace F)).comp
      (SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ ℂ)).comp S
  have hℓ : ∀ S f, ℓ S f = S f 0 := fun _ _ => rfl
  have at0a : At (evI F) (0 : Fin (a + (b + 2)) → AE F E) := fun _ _ => smul_zero _
  have at0c : At (evI F) (0 : Fin b → AE F E) := fun _ _ => smul_zero _
  have at0z : At (evI F) (0 : Matrix (Fin b) (Fin (a + b)) (AE F E)) := fun _ _ => smul_zero _
  have ez0 : arch F (G₁.M'.co.e (0 : Matrix (Fin b) (Fin (a + b)) (AE F E))).1 = 0 := by simp [arch_zero]
  have eadd : ∀ x y : Matrix (Fin (b + 2)) (Fin (a + (b + 2))) (AE F E),
      arch F (G.M'.co.e (x + y)).1 = arch F (G.M'.co.e x).1 + arch F (G.M'.co.e y).1 ∧
      arch F (G.M'.co.e (x + y)).2 = arch F (G.M'.co.e x).2 + arch F (G.M'.co.e y).2 := fun x y =>
    ⟨by rw [map_add, Prod.fst_add, arch_add], by rw [map_add, Prod.snd_add, arch_add]⟩
  have inv : ∀ S : SInf F (Fin (b + 2) × Fin (a + (b + 2))) →L[ℂ] SInf F (Fin b × Fin (a + b)),
      GlobalTheory.ThK.EvUniqB.InfRel B G.M' G₁.M' H.ι H'.ι (isoB H H') S →
      ∀ l ∈ Λ, ∀ f g : SInf F (Fin (b + 2) × Fin (a + (b + 2))), ⇑g = sch (trP F _) l.1 l.2 ⇑f → ℓ S g = ℓ S f := by
    intro S hS l hl f g hg
    obtain ⟨x, c, z, hx, hc, hz, hz1, rfl⟩ := hl
    set u₁ := Matrix.vecMulVec (incV F H.x) x with hu₁
    set u₂ := Matrix.vecMulVec (incM F H.ι *ᵥ c) (incV F H'.x) with hu₂
    set w := incM F H.ι * z * (incM F H'.ι)ᵀ with hw
    have hat1 : At (evI F) u₁ := at_vecMulVec_right _ hx
    have hat2 : At (evI F) u₂ := at_vecMulVec_left (at_mulVec _ hc) _
    have m1 : (arch F (G.M'.co.e u₁).1, arch F (G.M'.co.e u₁).2) ∈ lagSetB G.M' G₁.M' H H' :=
      mem_lagSetB_x G.M' G₁.M' H H' hx
    have m2 : (arch F (G.M'.co.e (u₂ + w)).1, arch F (G.M'.co.e (u₂ + w)).2) ∈ lagSetB G.M' G₁.M' H H' :=
      mem_lagSetB_cz G.M' G₁.M' H H' hc hz hz1
    have m3 : (arch F (G.M'.co.e u₂).1, arch F (G.M'.co.e u₂).2) ∈ lagSetB G.M' G₁.M' H H' :=
      mem_lagSetB_c G.M' G₁.M' H H' hc
    have m4 : (arch F (G.M'.co.e w).1, arch F (G.M'.co.e w).2) ∈ lagSetB G.M' G₁.M' H H' :=
      mem_lagSetB_z G.M' G₁.M' H H' hz hz1
    have hsplit : ⇑g = sch (trP F _) (arch F (G.M'.co.e u₁).1) (arch F (G.M'.co.e u₁).2)
        (sch (trP F _) (arch F (G.M'.co.e u₂).1) (arch F (G.M'.co.e u₂).2)
          (sch (trP F _) (arch F (G.M'.co.e w).1) (arch F (G.M'.co.e w).2) ⇑f)) := by
      rw [hg]
      dsimp only
      rw [add_assoc, (eadd _ _).1, (eadd _ _).2, sch_add _ _ _ _ _ (hiso _ m1 _ m2), (eadd _ _).1, (eadd _ _).2,
        sch_add _ _ _ _ _ (hiso _ m3 _ m4)]
    obtain ⟨h₃, hh₃⟩ := GlobalTheory.T.schroedinger_preserves_schwartz_real (trP F _) (arch F (G.M'.co.e w).1) (arch F (G.M'.co.e w).2) f
    obtain ⟨h₂, hh₂⟩ := GlobalTheory.T.schroedinger_preserves_schwartz_real (trP F _) (arch F (G.M'.co.e u₂).1) (arch F (G.M'.co.e u₂).2) h₃
    obtain ⟨g₁, hg₁⟩ := GlobalTheory.T.schroedinger_preserves_schwartz_real (trP F _) (arch F (G₁.M'.co.e z).1) (arch F (G₁.M'.co.e z).2) (S f)
    rw [← hh₃, ← hh₂] at hsplit
    rw [hℓ, hℓ, F2 S hS u₁ (Or.inl ⟨x, rfl⟩) hat1 h₂ g hsplit, F2 S hS u₂ (Or.inr ⟨c, rfl⟩) hat2 h₃ h₂ hh₂,
      F1 S hS z hz f h₃ g₁ hh₃ hg₁, hg₁]
    simp [sch, hz1, ech_zero]
  have zξ : ∀ ξ : Fin b × Fin (a + b) → mixedEmbedding.mixedSpace F, ∃ z : Matrix (Fin b) (Fin (a + b)) (AE F E),
      At (evI F) z ∧ arch F (G₁.M'.co.e z).1 = ξ ∧ arch F (G₁.M'.co.e z).2 = 0 := by
    intro ξ
    refine ⟨G₁.M'.co.e.symm (fun i => liftA F (ξ i), 0), fun u hu => ?_, ?_, ?_⟩
    · rw [← LinearEquiv.map_smul]
      have : u • ((fun i => liftA F (ξ i), 0) : (Fin b × Fin (a + b) → AF F) × (Fin b × Fin (a + b) → AF F)) = 0 := by
        refine Prod.ext (funext fun i => ?_) (by simp)
        simp [at_liftA (ξ i) u hu]
      rw [this, map_zero]
    · funext i; simp [arch, evI_liftA]
    · simp [arch_zero]
  have key : ∀ (f : SInf F (Fin (b + 2) × Fin (a + (b + 2)))) (ξ : Fin b × Fin (a + b) → mixedEmbedding.mixedSpace F),
      ∃ h : SInf F (Fin (b + 2) × Fin (a + (b + 2))), ∀ S : SInf F (Fin (b + 2) × Fin (a + (b + 2))) →L[ℂ] SInf F (Fin b × Fin (a + b)),
        GlobalTheory.ThK.EvUniqB.InfRel B G.M' G₁.M' H.ι H'.ι (isoB H H') S → S h 0 = S f ξ := by
    intro f ξ
    obtain ⟨z, hz, hz1, hz2⟩ := zξ ξ
    obtain ⟨h, hh⟩ := GlobalTheory.T.schroedinger_preserves_schwartz_real (trP F _) (arch F (G.M'.co.e (incM F H.ι * z * (incM F H'.ι)ᵀ)).1)
      (arch F (G.M'.co.e (incM F H.ι * z * (incM F H'.ι)ᵀ)).2) f
    refine ⟨h, fun S hS => ?_⟩
    obtain ⟨g₁, hg₁⟩ := GlobalTheory.T.schroedinger_preserves_schwartz_real (trP F _) (arch F (G₁.M'.co.e z).1) (arch F (G₁.M'.co.e z).2) (S f)
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
  have hiso' : ∀ l ∈ Λ, ∀ l' ∈ Λ, trP F (Fin (b + 2) × Fin (a + (b + 2))) l.1 l'.2 =
      trP F (Fin (b + 2) × Fin (a + (b + 2))) l'.1 l.2 := fun l hl l' hl' => hiso l hl l' hl'
  have hco' : ∀ v : (Fin (b + 2) × Fin (a + (b + 2)) → mixedEmbedding.mixedSpace F) ×
      (Fin (b + 2) × Fin (a + (b + 2)) → mixedEmbedding.mixedSpace F),
      (∀ l ∈ Λ, trP F (Fin (b + 2) × Fin (a + (b + 2))) v.1 l.2 = trP F (Fin (b + 2) × Fin (a + (b + 2))) l.1 v.2) →
      v ∈ Λ := fun v hv => hco v hv
  have hT1 := inv T hR
  have hT2 := inv T' hR'
  obtain ⟨C, hC'⟩ := GlobalTheory.T.aux_statement_2 (Y := Fin (b + 2) × Fin (a + (b + 2)) → mixedEmbedding.mixedSpace F)
    (trP F (Fin (b + 2) × Fin (a + (b + 2)))) (GlobalTheory.T.trace_pairing_nondegenerate F (Fin (b + 2) × Fin (a + (b + 2)))) Λ hiso' hco'
    (ℓ T) (ℓ T') hT1 hT2 hne
  refine ⟨C, ContinuousLinearMap.ext fun f => SchwartzMap.ext fun ξ => ?_⟩
  obtain ⟨h', hh'⟩ := key f ξ
  have := congrArg (fun L => L h') hC'
  simp only [hℓ, ContinuousLinearMap.smul_apply, smul_eq_mul] at this
  rw [← hh' T' hR', this, hh' T hR]
  rfl
