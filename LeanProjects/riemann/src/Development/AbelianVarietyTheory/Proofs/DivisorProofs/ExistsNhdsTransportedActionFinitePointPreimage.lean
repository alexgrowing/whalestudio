import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransportF
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsContOnOfLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportedWeilDatumCMPreservesSchwartzHeisenberStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenNsmulAdelicCompletionOfVectorSet
import Formalism.LocalToGlobal.Columns.RecLevelTop
import Formalism.LocalToGlobal.SiegelLatticeTheory.FundamentalEquivalence.FundamentalContinuity.AdelicIsomorphismStatement
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical

noncomputable section

open Topology Filter

namespace GlobalTheory.WeilTransNbhd

variable (F : Type) [Field F] [NumberField F]

theorem exists_compact_open_subgroup (κ : Type) [Fintype κ] {S : Set (κ → FiniteAdeleRing (𝓞 F) F)}
    (hS : S ∈ 𝓝 0) : ∃ U : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F), IsOpen (U : Set (κ → FiniteAdeleRing (𝓞 F) F)) ∧
      IsCompact (U : Set (κ → FiniteAdeleRing (𝓞 F) F)) ∧ (U : Set (κ → FiniteAdeleRing (𝓞 F) F)) ⊆ S := by
  classical
  have hS' : S ∈ 𝓝 (fun _ : κ => (0 : FiniteAdeleRing (𝓞 F) F)) := hS
  rw [nhds_pi, Filter.mem_pi] at hS'
  obtain ⟨I, -, t, ht, hsub⟩ := hS'
  have hO : (⋂ i, t i) ∈ 𝓝 (0 : FiniteAdeleRing (𝓞 F) F) := Filter.iInter_mem.2 ht
  have hbox : ∀ u : κ → FiniteAdeleRing (𝓞 F) F, (∀ i, u i ∈ ⋂ i, t i) → u ∈ S :=
    fun u hu => hsub fun i _ => Set.mem_iInter.1 (hu i) i
  obtain ⟨N, hN, hNO⟩ := GlobalTheory.AdLat.OpenLat.exists_nsmul_adele F _ hO
  let c : FiniteAdeleRing (𝓞 F) F := algebraMap F _ ((N : F)⁻¹)
  have hcN : (N : FiniteAdeleRing (𝓞 F) F) * c = 1 := by
    rw [← map_natCast (algebraMap F (FiniteAdeleRing (𝓞 F) F)) N, ← map_mul,
      mul_inv_cancel₀ (Nat.cast_ne_zero.2 hN.ne'), map_one]
  have hNc : c * (N : FiniteAdeleRing (𝓞 F) F) = 1 := by rw [mul_comm]; exact hcN
  let h : (κ → FiniteAdeleRing (𝓞 F) F) ≃ₜ (κ → FiniteAdeleRing (𝓞 F) F) :=
    { toFun := fun u i => c * u i
      invFun := fun u i => (N : FiniteAdeleRing (𝓞 F) F) * u i
      left_inv := fun u => funext fun i => by
        show (N : FiniteAdeleRing (𝓞 F) F) * (c * u i) = u i
        rw [← mul_assoc, hcN, one_mul]
      right_inv := fun u => funext fun i => by
        show c * ((N : FiniteAdeleRing (𝓞 F) F) * u i) = u i
        rw [← mul_assoc, hNc, one_mul]
      continuous_toFun := continuous_pi fun i => continuous_const.mul (continuous_apply i)
      continuous_invFun := continuous_pi fun i => continuous_const.mul (continuous_apply i) }
  let φ : (κ → FiniteAdeleRing (𝓞 F) F) →+ (κ → FiniteAdeleRing (𝓞 F) F) :=
    { toFun := fun u i => c * u i
      map_zero' := by funext i; exact mul_zero c
      map_add' := fun u w => by funext i; exact mul_add c (u i) (w i) }
  let U : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F) :=
    (AddSubgroup.pi Set.univ fun _ => (Formalism.UG.intAd F).toAddSubgroup).comap φ
  have hUset : (U : Set (κ → FiniteAdeleRing (𝓞 F) F)) =
      h ⁻¹' Set.univ.pi fun _ => (Formalism.UG.intAd F : Set (FiniteAdeleRing (𝓞 F) F)) := rfl
  have hint_c : IsCompact (Formalism.UG.intAd F : Set (FiniteAdeleRing (𝓞 F) F)) := Formalism.L2.Col.rlt_isCompact_intAd
  have hint_o : IsOpen (Formalism.UG.intAd F : Set (FiniteAdeleRing (𝓞 F) F)) := Formalism.L2.SG.Pf.top_isOpen_intAd F
  refine ⟨U, ?_, ?_, ?_⟩
  · rw [hUset]; exact (isOpen_set_pi Set.finite_univ fun _ _ => hint_o).preimage h.continuous
  · rw [hUset]; exact h.isCompact_preimage.2 (isCompact_univ_pi fun _ => hint_c)
  · intro u hu
    refine hbox u fun i => ?_
    have hi : c * u i ∈ Formalism.UG.intAd F := hu i (Set.mem_univ i)
    have := hNO (c * u i) hi
    rwa [nsmul_eq_mul, ← mul_assoc, hcN, one_mul] at this

def finIdem : AF F := ((0 : InfiniteAdeleRing F), (1 : FiniteAdeleRing (𝓞 F) F))

variable {F}

theorem finIdem_smul_eq {κ : Type} (w : κ → AF F) :
    finIdem F • w = GlobalTheory.WeilCont.adeleJoin F 0 (fun i => (w i).2) := by
  funext i
  refine Prod.ext ?_ ?_
  · show (0 : InfiniteAdeleRing F) * (w i).1 = (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm ((0 : κ → mixedEmbedding.mixedSpace F) i)
    rw [zero_mul, Pi.zero_apply, map_zero]
  · show (1 : FiniteAdeleRing (𝓞 F) F) * (w i).2 = (w i).2
    exact one_mul _

theorem finIdem_smul_adeleJoin {κ : Type} (x : κ → FiniteAdeleRing (𝓞 F) F) :
    finIdem F • GlobalTheory.WeilCont.adeleJoin F 0 x = GlobalTheory.WeilCont.adeleJoin F 0 x :=
  finIdem_smul_eq _

theorem adeleJoin_zero_zero {κ : Type} :
    GlobalTheory.WeilCont.adeleJoin F (0 : κ → mixedEmbedding.mixedSpace F) 0 = 0 := by
  funext i
  refine Prod.ext ?_ rfl
  show (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm ((0 : κ → mixedEmbedding.mixedSpace F) i) = 0
  rw [Pi.zero_apply, map_zero]

theorem continuous_adeleJoin_zero {κ : Type} :
    Continuous fun x : κ → FiniteAdeleRing (𝓞 F) F => GlobalTheory.WeilCont.adeleJoin F 0 x :=
  continuous_pi fun i => (continuous_const.prodMk (continuous_apply i) :
    Continuous fun x : κ → FiniteAdeleRing (𝓞 F) F =>
      (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm ((0 : κ → mixedEmbedding.mixedSpace F) i), x i) :
        InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))

end GlobalTheory.WeilTransNbhd

end

noncomputable section

open Topology Filter

namespace GlobalTheory.WeilTransNbhd

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem actAB_smul (σ : E →ₐ[F] E) {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    {JA : Matrix α α (AF F ⊗[F] E)} {JB : Matrix β β (AF F ⊗[F] E)} (p : UG (cA σ) JA × UG (cA σ) JB) (r : AF F)
    (X : Matrix α β (AF F ⊗[F] E)) : actAB (cA σ) p (r • X) = r • actAB (cA σ) p X := by
  unfold actAB
  rw [Matrix.mul_smul, Matrix.smul_mul]

theorem actAB_mul_inv (σ : E →ₐ[F] E) {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    {JA : Matrix α α (AF F ⊗[F] E)} {JB : Matrix β β (AF F ⊗[F] E)} (p : UG (cA σ) JA × UG (cA σ) JB)
    (X : Matrix α β (AF F ⊗[F] E)) : actAB (cA σ) p (actAB (cA σ) p⁻¹ X) = X := by
  unfold actAB
  have h1 : ((p.1 : GL α (AF F ⊗[F] E)) : Matrix α α (AF F ⊗[F] E)) * (((p⁻¹).1 : GL α (AF F ⊗[F] E)) : Matrix α α (AF F ⊗[F] E)) = 1 := by
    show ((p.1 : GL α (AF F ⊗[F] E)) : Matrix α α (AF F ⊗[F] E)) * (((p.1)⁻¹ : GL α (AF F ⊗[F] E)) : Matrix α α (AF F ⊗[F] E)) = 1
    exact Units.mul_inv _
  have h2 : (((p⁻¹).2 : GL β (AF F ⊗[F] E)) : Matrix β β (AF F ⊗[F] E))ᵀ * ((p.2 : GL β (AF F ⊗[F] E)) : Matrix β β (AF F ⊗[F] E))ᵀ = 1 := by
    rw [← Matrix.transpose_mul]
    show ((p.2 : GL β (AF F ⊗[F] E)) * ((p.2)⁻¹ : GL β (AF F ⊗[F] E)) : Matrix β β (AF F ⊗[F] E))ᵀ = 1
    rw [Units.mul_inv, Matrix.transpose_one]
  calc _ = ((p.1 : GL α (AF F ⊗[F] E)) : Matrix α α (AF F ⊗[F] E)) * (((p⁻¹).1 : GL α (AF F ⊗[F] E)) : Matrix α α (AF F ⊗[F] E)) * X *
        ((((p⁻¹).2 : GL β (AF F ⊗[F] E)) : Matrix β β (AF F ⊗[F] E))ᵀ * ((p.2 : GL β (AF F ⊗[F] E)) : Matrix β β (AF F ⊗[F] E))ᵀ) := by
        simp only [Matrix.mul_assoc]
    _ = X := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]

theorem exists_nhds_finite_preimage : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (a b : ℕ) (JA : Matrix (Fin a) (Fin a) E) (JB : Matrix (Fin b) (Fin b) E) (ξ : AF F ⊗[F] E) (κ : Type) [Fintype κ]
    (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ) (L₁ L₂ : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F)),
    IsOpen (L₁ : Set (κ → FiniteAdeleRing (𝓞 F) F)) → IsOpen (L₂ : Set (κ → FiniteAdeleRing (𝓞 F) F)) →
    ∀ p0 : UG (cA σ) (incM F JA) × UG (cA σ) (incM F JB),
    ∃ N ∈ nhds p0, ∃ L₁' L₂' : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F),
      IsOpen (L₁' : Set (κ → FiniteAdeleRing (𝓞 F) F)) ∧ IsCompact (L₁' : Set (κ → FiniteAdeleRing (𝓞 F) F)) ∧
      IsOpen (L₂' : Set (κ → FiniteAdeleRing (𝓞 F) F)) ∧
      ∀ p ∈ N, ∀ x ∈ L₁', ∀ y ∈ L₂', ∃ x' ∈ L₁, ∃ y' ∈ L₂,
        co.e (actAB (cA σ) p (co.e.symm (GlobalTheory.WeilCont.adeleJoin F 0 x', GlobalTheory.WeilCont.adeleJoin F 0 y'))) =
          (GlobalTheory.WeilCont.adeleJoin F 0 x, GlobalTheory.WeilCont.adeleJoin F 0 y) := by
  intro F E _ _ _ _ _ σ a b JA JB ξ κ _ co L₁ L₂ hL₁ hL₂ p0
  haveI hmt : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI : IsModuleTopology (AF F) (Matrix (Fin a) (Fin b) (AF F ⊗[F] E)) :=
    inferInstanceAs (IsModuleTopology (AF F) (Fin a → Fin b → AF F ⊗[F] E))
  haveI : ContinuousSMul (AF F) (Matrix (Fin a) (Fin b) (AF F ⊗[F] E)) :=
    inferInstanceAs (ContinuousSMul (AF F) (Fin a → Fin b → AF F ⊗[F] E))
  have hce : Continuous co.e := IsModuleTopology.continuous_of_linearMap co.e.toLinearMap
  have hcs : Continuous co.e.symm := IsModuleTopology.continuous_of_linearMap co.e.symm.toLinearMap
  let Ψ : (UG (cA σ) (incM F JA) × UG (cA σ) (incM F JB)) ×
      ((κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F)) → (κ → AF F) × (κ → AF F) :=
    fun q => co.e (actAB (cA σ) q.1⁻¹ (co.e.symm (GlobalTheory.WeilCont.adeleJoin F 0 q.2.1, GlobalTheory.WeilCont.adeleJoin F 0 q.2.2)))
  let Φ : (UG (cA σ) (incM F JA) × UG (cA σ) (incM F JB)) ×
      ((κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F)) →
      (κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F) :=
    fun q => (fun i => ((Ψ q).1 i).2, fun i => ((Ψ q).2 i).2)
  have hinv : Continuous fun q : (UG (cA σ) (incM F JA) × UG (cA σ) (incM F JB)) ×
      ((κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F)) => q.1⁻¹ := continuous_fst.inv
  have hm1 : Continuous fun q : (UG (cA σ) (incM F JA) × UG (cA σ) (incM F JB)) ×
      ((κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F)) =>
      (((q.1⁻¹).1 : GL (Fin a) (AF F ⊗[F] E)) : Matrix (Fin a) (Fin a) (AF F ⊗[F] E)) :=
    Units.continuous_val.comp (continuous_subtype_val.comp (continuous_fst.comp hinv))
  have hm2 : Continuous fun q : (UG (cA σ) (incM F JA) × UG (cA σ) (incM F JB)) ×
      ((κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F)) =>
      (((q.1⁻¹).2 : GL (Fin b) (AF F ⊗[F] E)) : Matrix (Fin b) (Fin b) (AF F ⊗[F] E)) :=
    Units.continuous_val.comp (continuous_subtype_val.comp (continuous_snd.comp hinv))
  have hv : Continuous fun q : (UG (cA σ) (incM F JA) × UG (cA σ) (incM F JB)) ×
      ((κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F)) =>
      co.e.symm (GlobalTheory.WeilCont.adeleJoin F 0 q.2.1, GlobalTheory.WeilCont.adeleJoin F 0 q.2.2) :=
    hcs.comp ((continuous_adeleJoin_zero.comp (continuous_fst.comp continuous_snd)).prodMk
      (continuous_adeleJoin_zero.comp (continuous_snd.comp continuous_snd)))
  have hΨ : Continuous Ψ := hce.comp ((hm1.matrix_mul hv).matrix_mul hm2.matrix_transpose)
  have hΦ : Continuous Φ :=
    (continuous_pi fun i => continuous_snd.comp ((continuous_apply i).comp (continuous_fst.comp hΨ))).prodMk
      (continuous_pi fun i => continuous_snd.comp ((continuous_apply i).comp (continuous_snd.comp hΨ)))
  have hΦ0 : Φ (p0, (0, 0)) = (0, 0) := by
    have : Ψ (p0, (0, 0)) = 0 := by
      simp only [Ψ, adeleJoin_zero_zero]
      rw [show ((0 : κ → AF F), (0 : κ → AF F)) = 0 from rfl, map_zero]
      rw [show actAB (cA σ) p0⁻¹ (0 : Matrix (Fin a) (Fin b) (AF F ⊗[F] E)) = 0 by
        unfold actAB; rw [Matrix.mul_zero, Matrix.zero_mul], map_zero]
    simp only [Φ, this]
    rfl
  have hopen : IsOpen (Φ ⁻¹' ((L₁ : Set (κ → FiniteAdeleRing (𝓞 F) F)) ×ˢ (L₂ : Set (κ → FiniteAdeleRing (𝓞 F) F)))) :=
    (hL₁.prod hL₂).preimage hΦ
  have hmem : (p0, ((0 : κ → FiniteAdeleRing (𝓞 F) F), (0 : κ → FiniteAdeleRing (𝓞 F) F))) ∈
      Φ ⁻¹' ((L₁ : Set (κ → FiniteAdeleRing (𝓞 F) F)) ×ˢ (L₂ : Set (κ → FiniteAdeleRing (𝓞 F) F))) := by
    rw [Set.mem_preimage, hΦ0]
    exact ⟨L₁.zero_mem, L₂.zero_mem⟩
  obtain ⟨N, hN, V, hV, hNV⟩ := mem_nhds_prod_iff.1 (hopen.mem_nhds hmem)
  rw [← Prod.zero_eq_mk, nhds_prod_eq] at hV
  obtain ⟨V₁, hV₁, V₂, hV₂, hV12⟩ := mem_prod_iff.1 hV
  obtain ⟨L₁', hL₁'o, hL₁'c, hL₁'s⟩ := exists_compact_open_subgroup F κ hV₁
  obtain ⟨L₂', hL₂'o, -, hL₂'s⟩ := exists_compact_open_subgroup F κ hV₂
  refine ⟨N, hN, L₁', L₂', hL₁'o, hL₁'c, hL₂'o, fun p hp x hx y hy => ?_⟩
  have hin := hNV (Set.mk_mem_prod hp (hV12 (Set.mk_mem_prod (hL₁'s hx) (hL₂'s hy))))
  refine ⟨(Φ (p, (x, y))).1, hin.1, (Φ (p, (x, y))).2, hin.2, ?_⟩

  have hfin : (GlobalTheory.WeilCont.adeleJoin F 0 (Φ (p, (x, y))).1, GlobalTheory.WeilCont.adeleJoin F 0 (Φ (p, (x, y))).2) =
      Ψ (p, (x, y)) := by
    have e1 : Ψ (p, (x, y)) = finIdem F • Ψ (p, (x, y)) := by
      simp only [Ψ]
      conv_lhs => rw [← finIdem_smul_adeleJoin x, ← finIdem_smul_adeleJoin y, ← Prod.smul_mk, map_smul,
        actAB_smul, map_smul]
    rw [e1]
    refine Prod.ext ?_ ?_
    · rw [Prod.smul_fst, finIdem_smul_eq]
    · rw [Prod.smul_snd, finIdem_smul_eq]
  rw [hfin]
  simp only [Ψ, LinearEquiv.symm_apply_apply, actAB_mul_inv, LinearEquiv.apply_symm_apply]

end GlobalTheory.WeilTransNbhd

end
