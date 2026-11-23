import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFrameOfBijectiveStalk
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortExactVectorBundlesRankAddStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CkAdditiveCompositionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CkPresentationInvariantStatement
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.MixedLocalChains.ExtAdd

theorem cok_lift_iso {C : Type*} [Category C] [Abelian C] {E' E M : C} (ψ : E' ⟶ E) (g : cokernel ψ ⟶ M)
    [Epi g] : Nonempty (cokernel (kernel.lift (cokernel.π ψ ≫ g) ψ (by simp)) ≅ kernel g) := by
  let f := cokernel.π ψ ≫ g
  let ι : E' ⟶ kernel f := kernel.lift f ψ (by simp [f])
  let u : kernel f ⟶ kernel g := kernel.lift g (kernel.ι f ≫ cokernel.π ψ) (by
    rw [Category.assoc]; exact kernel.condition f)
  have hιu : ι ≫ u = 0 := by
    ext; simp [ι, u]
  let T : ShortComplex C := ShortComplex.mk ι u hιu
  have hC : (ShortComplex.mk ψ (cokernel.π ψ) (cokernel.condition ψ)).Exact :=
    ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel ψ)
  have hu : Epi u := by
    rw [epi_iff_surjective_up_to_refinements]
    intro A y
    obtain ⟨A', π', hπ', x, hx⟩ := surjective_up_to_refinements_of_epi (cokernel.π ψ) (y ≫ kernel.ι g)
    refine ⟨A', π', hπ', kernel.lift f x (by simp [f, ← reassoc_of% hx]), ?_⟩
    rw [← cancel_mono (kernel.ι g)]
    simp [u, hx]
  have hT : T.Exact := by
    rw [ShortComplex.exact_iff_exact_up_to_refinements]
    intro A x₂ hx₂
    have h0 : (x₂ ≫ kernel.ι f) ≫ cokernel.π ψ = 0 := by
      have := congrArg (· ≫ kernel.ι g) hx₂
      simpa [T, u] using this
    obtain ⟨A', π', hπ', x₁, hx₁⟩ := hC.exact_up_to_refinements (x₂ ≫ kernel.ι f) h0
    refine ⟨A', π', hπ', x₁, ?_⟩
    rw [← cancel_mono (kernel.ι f)]
    simpa [T, ι] using hx₁
  exact ⟨IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) (hT.gIsCokernel)⟩

theorem mono_ψ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {B : Vert.Model O} (P : Pres B) :
    Mono P.ψ := by
  have := P.iso
  let j := B.gen.ι
  have hR : IsIso ((Scheme.Modules.restrictFunctor j).map P.ψ) := by
    let e := Scheme.Modules.restrictFunctorIsoPullback j
    have h : (Scheme.Modules.restrictFunctor j).map P.ψ = e.hom.app _ ≫ B.genRes.map P.ψ ≫ e.inv.app _ := by
      rw [← e.hom.naturality_assoc, Iso.hom_inv_id_app, Category.comp_id]
    rw [h]; infer_instance
  have hinj : ∀ U : B.gen.toScheme.Opens, Function.Injective (P.ψ.app (j ''ᵁ U)) := fun U =>
    app_injective_of_mono ((Scheme.Modules.restrictFunctor j).map P.ψ) U
  refine mono_of_locally_app_injective _ fun W x hx => ⟨W, hx, le_rfl, fun a b e => ?_⟩
  have hηW : genericPoint B.X ∈ W := (genericPoint_specializes x).mem_open W.isOpen hx
  have hV : j ''ᵁ (j ⁻¹ᵁ W) = B.gen ⊓ W := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
  have hVW : j ''ᵁ (j ⁻¹ᵁ W) ≤ W := hV.le.trans inf_le_right
  have hηV : genericPoint B.X ∈ j ''ᵁ (j ⁻¹ᵁ W) := by
    rw [hV]; exact ⟨B.genericPoint_mem_gen, hηW⟩
  refine sub_eq_zero.1 (P.vb'.isTorsionFree W hηW _ ?_)
  have h0 : Twist.resM _ hVW (a - b) = 0 := by
    apply hinj (j ⁻¹ᵁ W)
    rw [Twist.app_resM, map_sub, e, sub_self, map_zero, map_zero]
  rw [← Twist.germ_resM hVW hηV, h0, map_zero]

theorem isVB_kernel {X : Scheme.{0}} {E E₃' E₃ : X.Modules} (ψ : E₃' ⟶ E₃) [Mono ψ] (f : E ⟶ cokernel ψ) [Epi f]
    {r s : ℕ} (hE : GlobalTheory.VB.IsVB E r) (h₃ : GlobalTheory.VB.IsVB E₃ s) (h₃' : GlobalTheory.VB.IsVB E₃' s) :
    GlobalTheory.VB.IsVB (kernel f) r := by
  let a : E₃' ⟶ pullback f (cokernel.π ψ) := pullback.lift 0 ψ (by simp)
  let b : kernel f ⟶ pullback f (cokernel.π ψ) := pullback.lift (kernel.ι f) 0 (by simp)
  have ha₁ : a ≫ pullback.fst f (cokernel.π ψ) = 0 := pullback.lift_fst _ _ _
  have ha₂ : a ≫ pullback.snd f (cokernel.π ψ) = ψ := pullback.lift_snd _ _ _
  have hb₁ : b ≫ pullback.fst f (cokernel.π ψ) = kernel.ι f := pullback.lift_fst _ _ _
  have hb₂ : b ≫ pullback.snd f (cokernel.π ψ) = 0 := pullback.lift_snd _ _ _
  have hC : (ShortComplex.mk ψ (cokernel.π ψ) (cokernel.condition ψ)).Exact :=
    ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel ψ)
  let S₁ : ShortComplex X.Modules := ShortComplex.mk a (pullback.fst f (cokernel.π ψ)) ha₁
  have hS₁ : S₁.ShortExact := by
    refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
    · rw [ShortComplex.exact_iff_exact_up_to_refinements]
      intro A x₂ hx₂
      have hx₂' : x₂ ≫ pullback.fst f (cokernel.π ψ) = 0 := hx₂
      have h0 : (x₂ ≫ pullback.snd f (cokernel.π ψ)) ≫ cokernel.π ψ = 0 := by
        rw [Category.assoc, ← pullback.condition, ← Category.assoc, hx₂', zero_comp]
      obtain ⟨A', π', hπ', x₁, hx₁⟩ := hC.exact_up_to_refinements _ h0
      refine ⟨A', π', hπ', x₁, ?_⟩
      apply pullback.hom_ext
      · change (π' ≫ x₂) ≫ _ = (x₁ ≫ a) ≫ _
        rw [Category.assoc, Category.assoc, hx₂', ha₁, comp_zero, comp_zero]
      · change (π' ≫ x₂) ≫ _ = (x₁ ≫ a) ≫ _
        rw [Category.assoc, Category.assoc, ha₂]
        exact hx₁
    · have : Mono (a ≫ pullback.snd f (cokernel.π ψ)) := by rw [ha₂]; infer_instance
      exact mono_of_mono a (pullback.snd f (cokernel.π ψ))
    · exact Abelian.epi_pullback_of_epi_g f (cokernel.π ψ)
  let S₂ : ShortComplex X.Modules := ShortComplex.mk b (pullback.snd f (cokernel.π ψ)) hb₂
  have hS₂ : S₂.ShortExact := by
    refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
    · rw [ShortComplex.exact_iff_exact_up_to_refinements]
      intro A x₂ hx₂
      have hx₂' : x₂ ≫ pullback.snd f (cokernel.π ψ) = 0 := hx₂
      have h0 : (x₂ ≫ pullback.fst f (cokernel.π ψ)) ≫ f = 0 := by
        rw [Category.assoc, pullback.condition, ← Category.assoc, hx₂', zero_comp]
      refine ⟨A, 𝟙 A, inferInstance, kernel.lift f _ h0, ?_⟩
      apply pullback.hom_ext
      · change (𝟙 A ≫ x₂) ≫ _ = (kernel.lift f _ h0 ≫ b) ≫ _
        rw [Category.assoc, Category.assoc, hb₁, kernel.lift_ι, Category.id_comp]
      · change (𝟙 A ≫ x₂) ≫ _ = (kernel.lift f _ h0 ≫ b) ≫ _
        rw [Category.assoc, Category.assoc, hb₂, comp_zero, Category.id_comp, hx₂']
    · have : Mono (b ≫ pullback.fst f (cokernel.π ψ)) := by rw [hb₁]; infer_instance
      exact mono_of_mono b (pullback.fst f (cokernel.π ψ))
    · exact Abelian.epi_pullback_of_epi_f f (cokernel.π ψ)
  have hF : GlobalTheory.VB.IsVB (pullback f (cokernel.π ψ)) (r + s) := by
    have := GlobalTheory.T.short_exact_vector_bundles_rank_add X S₁ s r hS₁ h₃' hE
    rwa [add_comm] at this
  exact GlobalTheory.VB.isVB_X₁_of_shortExact X S₂ r s hS₂ hF h₃

theorem ck_add_of_isExt : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime]
    [CharZero O] [CharP (ResidueField O) p] (B : GlobalTheory.Vert.Model O), GlobalTheory.IsNormalScheme B.X →
    ∀ (P₁ P₂ P₃ : Pres B), IsExt P₁.mod P₂.mod P₃.mod → ∀ k : ℕ, P₂.ck p k = P₁.ck p k + P₃.ck p k := by
  intro O _ _ _ p _ _ _ B hB P₁ P₂ P₃ ⟨S, hS, ⟨e₁⟩, ⟨e₂⟩, ⟨e₃⟩⟩ k
  have := hS.epi_g
  let g : cokernel P₂.ψ ⟶ P₃.mod := e₂.inv ≫ S.g ≫ e₃.hom
  haveI h3 : Epi (S.g ≫ e₃.hom) := @epi_comp _ _ _ _ _ S.g hS.epi_g e₃.hom _
  haveI hg : Epi g := @epi_comp _ _ _ _ _ e₂.inv _ (S.g ≫ e₃.hom) h3
  let f : P₂.E ⟶ P₃.mod := cokernel.π P₂.ψ ≫ g
  haveI hf : Epi f := by dsimp only [f]; infer_instance
  let j : kernel f ⟶ P₂.E := kernel.ι f
  let ι : P₂.E' ⟶ kernel f := kernel.lift f P₂.ψ (by simp [f])
  have hψ : ι ≫ j = P₂.ψ := kernel.lift_ι _ _ _
  have := mono_ψ P₃
  let f' : P₂.E ⟶ cokernel P₃.ψ := f
  haveI : Epi f' := hf
  have hK : GlobalTheory.VB.IsVB (kernel f) P₂.r := isVB_kernel P₃.ψ f' P₂.vb P₃.vb P₃.vb'
  have := hK.isQuasicoherent
  have := P₂.vb.isQuasicoherent
  have := P₂.iso
  have hmj : Mono (B.genRes.map j) := mono_pullback_map _ j
  have hij : IsIso (B.genRes.map j) := by
    have hc : IsIso (B.genRes.map ι ≫ B.genRes.map j) := by rw [← Functor.map_comp, hψ]; infer_instance
    have : IsSplitEpi (B.genRes.map j) := ⟨⟨inv (B.genRes.map ι ≫ B.genRes.map j) ≫ B.genRes.map ι, by simp⟩⟩
    exact isIso_of_mono_of_isSplitEpi _
  have hiι : IsIso (B.genRes.map ι) := by
    have hc : IsIso (B.genRes.map ι ≫ B.genRes.map j) := by rw [← Functor.map_comp, hψ]; infer_instance
    exact IsIso.of_isIso_comp_right _ (B.genRes.map j)
  let Q₁ : Pres B := ⟨P₂.r, kernel f, P₂.E', hK, P₂.vb', ι, hiι⟩
  let Q₃ : Pres B := ⟨P₂.r, P₂.E, kernel f, P₂.vb, hK, j, hij⟩
  have h₁ : Nonempty (Q₁.mod ≅ P₁.mod) := by
    obtain ⟨e⟩ := cok_lift_iso P₂.ψ g
    exact ⟨e ≪≫ kernelIsIsoComp e₂.inv (S.g ≫ e₃.hom) ≪≫ kernelCompMono S.g e₃.hom ≪≫
      (IsLimit.conePointUniqueUpToIso hS.fIsKernel (kernelIsKernel S.g)).symm ≪≫ e₁⟩
  have h₃ : Nonempty (Q₃.mod ≅ P₃.mod) := by
    exact ⟨IsColimit.coconePointUniqueUpToIso (colimit.isColimit _)
      (Abelian.epiIsCokernelOfKernel _ (kernelIsKernel f))⟩
  have hcomp : (haveI := P₂.iso; Vert.Model.GenIso.ofHom P₂.ψ) =
      Vert.Model.GenIso.ofHom j ≪≫ Vert.Model.GenIso.ofHom ι := by
    ext1
    simp only [Vert.Model.GenIso.ofHom, Iso.trans_hom, Iso.symm_hom, asIso_inv]
    apply IsIso.inv_eq_of_hom_inv_id
    rw [← hψ, Functor.map_comp]
    simp
  have hba := (GlobalTheory.T.ck_additive_composition O p B hB _ _ _ (Vert.Model.GenIso.ofHom j) (Vert.Model.GenIso.ofHom ι) P₂.r k
    P₂.vb hK P₂.vb').1
  have hm₁ := GlobalTheory.T.ck_presentation_invariant O p B hB Q₁ P₁ h₁ k
  have hm₃ := GlobalTheory.T.ck_presentation_invariant O p B hB Q₃ P₃ h₃ k
  rw [← hm₁, ← hm₃, add_comm]
  change ckP p _ P₂.r k = ckP p _ P₂.r k + ckP p _ P₂.r k
  rw [hcomp]
  exact hba

end GlobalTheory.MixedLocalChains.ExtAdd
