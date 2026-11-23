import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PresentationMapMono

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains

namespace GlobalTheory.MixedLocalChains.FlagFilt

open GlobalTheory.VB TopologicalSpace

theorem exists_shortExact_cokernel {C : Type*} [Category C] [Abelian C] {L₁ L₂ : ShortComplex C}
    (h₁ : L₁.ShortExact) (h₂ : L₂.ShortExact) (v : L₁ ⟶ L₂) [Mono v.τ₃] :
    ∃ S : ShortComplex C, S.ShortExact ∧ Nonempty (S.X₁ ≅ cokernel v.τ₁) ∧
      Nonempty (S.X₂ ≅ cokernel v.τ₂) ∧ Nonempty (S.X₃ ≅ cokernel v.τ₃) := by
  haveI := h₁.epi_g
  haveI := h₂.mono_f
  haveI := h₂.epi_g
  let D : ShortComplex.SnakeInput C :=
    { L₀ := kernel v, L₁ := L₁, L₂ := L₂, L₃ := cokernel v
      v₀₁ := kernel.ι v, v₁₂ := v, v₂₃ := cokernel.π v
      h₀ := kernelIsKernel v
      h₃ := cokernelIsCokernel v
      L₁_exact := h₁.exact, epi_L₁_g := inferInstance
      L₂_exact := h₂.exact, mono_L₂_f := inferInstance }
  have hz : IsZero D.L₀.X₃ := by
    have h0 : D.v₀₁.τ₃ = 0 := by
      rw [← cancel_mono v.τ₃, zero_comp]
      exact D.w₀₂_τ₃
    haveI := D.mono_v₀₁_τ₃
    exact IsZero.of_mono_eq_zero _ h0
  have hm : Mono D.L₃.f := D.L₂'_exact.mono_g (hz.eq_of_src _ _)
  haveI : Epi D.L₂.g := h₂.epi_g
  have he : Epi D.L₃.g := @ShortComplex.SnakeInput.epi_L₃_g _ _ _ D h₂.epi_g
  refine ⟨D.L₃, { exact := D.L₃_exact, mono_f := hm, epi_g := he }, ⟨?_⟩, ⟨?_⟩, ⟨?_⟩⟩
  · exact IsColimit.coconePointUniqueUpToIso D.h₃τ₁ (colimit.isColimit _)
  · exact IsColimit.coconePointUniqueUpToIso D.h₃τ₂ (colimit.isColimit _)
  · exact IsColimit.coconePointUniqueUpToIso D.h₃τ₃ (colimit.isColimit _)

theorem eq_zero_of_pullback_ι {X : Scheme.{0}} [IsIntegral X] {F G : X.Modules}
    (h : IsTorsionFree G) (f : F ⟶ G) (U : X.Opens) (hU : genericPoint X ∈ U)
    (hf : (Scheme.Modules.pullback U.ι).map f = 0) : f = 0 := by
  have hr : (Scheme.Modules.restrictFunctor U.ι).map f = 0 := by
    rw [← cancel_mono ((Scheme.Modules.restrictFunctorIsoPullback U.ι).hom.app G), zero_comp,
      (Scheme.Modules.restrictFunctorIsoPullback U.ι).hom.naturality f, hf, comp_zero]
  refine Scheme.Modules.hom_ext _ _ fun W => ?_
  ext s
  change f.app W s = 0
  refine GlobalTheory.Twist.sec_ext_of_cover (ι := W) (fun _ => W) (fun _ => le_rfl)
    (fun x hx => Opens.mem_iSup.2 ⟨⟨x, hx⟩, hx⟩) fun k => ?_
  rw [GlobalTheory.Twist.resM_self, GlobalTheory.Twist.resM_self]
  have hη : genericPoint X ∈ W := genericPoint_mem k.2
  have hle : U.ι ''ᵁ (U.ι ⁻¹ᵁ W) ≤ W := U.ι.image_preimage_le W
  have hη' : genericPoint X ∈ U.ι ''ᵁ (U.ι ⁻¹ᵁ W) := ⟨⟨_, hU⟩, hη, rfl⟩
  have e0 : f.app (U.ι ''ᵁ (U.ι ⁻¹ᵁ W)) = 0 :=
    congrArg (fun φ => Scheme.Modules.Hom.app φ (U.ι ⁻¹ᵁ W)) hr
  refine h W hη _ ?_
  rw [← G.presheaf.germ_res_apply (homOfLE hle) _ hη' (f.app W s)]
  have e1 : G.presheaf.map (homOfLE hle).op (f.app W s) = 0 := by
    have := (GlobalTheory.Twist.app_resM f hle s).symm
    refine this.trans ?_
    rw [e0]
    rfl
  rw [e1, map_zero]

theorem comp_smulHom' {X : Scheme.{0}} {G H : X.Modules} (φ : G ⟶ H) (r : Γ(X, ⊤)) :
    φ ≫ smulHom H r = smulHom G r ≫ φ := by
  ext U x
  simp [Scheme.Modules.Hom.app_smul]

section Kills

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {B : Vert.Model O}

theorem kills_of_mono {g : Γ(B.X, ⊤)} {F G : B.X.Modules} (m : F ⟶ G) [Mono m] (h : Kills g G) :
    Kills g F := by
  unfold Kills at *
  rw [← cancel_mono m, zero_comp, ← comp_smulHom', h, comp_zero]

theorem kills_of_epi {g : Γ(B.X, ⊤)} {F G : B.X.Modules} (e : F ⟶ G) [Epi e] (h : Kills g F) :
    Kills g G := by
  unfold Kills at *
  rw [← cancel_epi e, comp_zero, comp_smulHom', h, zero_comp]

theorem kills_of_isExt {g : Γ(B.X, ⊤)} {F₁ F₂ F₃ : B.X.Modules} (hE : IsExt F₁ F₂ F₃)
    (h : Kills g F₂) : Kills g F₁ ∧ Kills g F₃ := by
  obtain ⟨S, hS, ⟨e₁⟩, ⟨e₂⟩, ⟨e₃⟩⟩ := hE
  haveI := hS.mono_f
  haveI := hS.epi_g
  have h2 : Kills g S.X₂ := kills_of_mono e₂.hom h
  exact ⟨kills_of_mono (e₁.inv ≫ S.f) h2, kills_of_epi (S.g ≫ e₃.hom) h2⟩

end Kills

end GlobalTheory.MixedLocalChains.FlagFilt

namespace GlobalTheory.MixedLocalChains.FlagFilt

open GlobalTheory.VB

section Main

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {B : Vert.Model O}
  {P : Pres B} [IsIso (B.genRes.map P.ψ)]
  (FP : Vert.Model.FlagPair (Vert.Model.GenIso.ofHom P.ψ) P.r)

theorem genRes_ι_ψ (i : Fin (P.r + 1)) :
    B.genRes.map (FP.fl'.ι i ≫ P.ψ) = (FP.gen i).inv ≫ B.genRes.map (FP.fl.ι i) := by
  have h := FP.gen_ι i
  rw [Functor.map_comp, Iso.eq_inv_comp, ← Category.assoc, h]
  simp [Vert.Model.GenIso.ofHom]

theorem comp_π_eq_zero (i : Fin (P.r + 1)) :
    FP.fl'.ι i ≫ P.ψ ≫ cokernel.π (FP.fl.ι i) = 0 := by
  refine eq_zero_of_pullback_ι (FP.fl.isVB_cokernel i).isTorsionFree _ B.gen
    B.genericPoint_mem_gen ?_
  change B.genRes.map _ = 0
  rw [← Category.assoc, Functor.map_comp, genRes_ι_ψ, Category.assoc, ← Functor.map_comp,
    cokernel.condition, Functor.map_zero, comp_zero]

def stepψ (i : Fin (P.r + 1)) : FP.fl'.F i ⟶ FP.fl.F i :=
  (ShortComplex.exact_cokernel (FP.fl.ι i)).lift (FP.fl'.ι i ≫ P.ψ)
    ((Category.assoc _ _ _).trans (comp_π_eq_zero FP i))

@[reassoc]
theorem stepψ_ι (i : Fin (P.r + 1)) : stepψ FP i ≫ FP.fl.ι i = FP.fl'.ι i ≫ P.ψ :=
  (ShortComplex.exact_cokernel (FP.fl.ι i)).lift_f _ _

theorem genRes_stepψ (i : Fin (P.r + 1)) : B.genRes.map (stepψ FP i) = (FP.gen i).inv := by
  rw [← cancel_mono (B.genRes.map (FP.fl.ι i)), ← Functor.map_comp, stepψ_ι, genRes_ι_ψ]

def stepPres (i : Fin (P.r + 1)) : Pres B where
  r := i
  E := FP.fl.F i
  E' := FP.fl'.F i
  vb := FP.fl.isVB i
  vb' := FP.fl'.isVB i
  ψ := stepψ FP i
  iso := by rw [genRes_stepψ]; infer_instance

theorem step_stepψ (i : Fin P.r) :
    FP.fl'.step i ≫ stepψ FP i.succ = stepψ FP i.castSucc ≫ FP.fl.step i := by
  rw [← cancel_mono (FP.fl.ι i.succ), Category.assoc, stepψ_ι, Category.assoc, Vert.Flag.step_ι,
    stepψ_ι, Vert.Flag.step_ι_assoc]

def grψ (i : Fin P.r) : FP.fl'.gr i ⟶ FP.fl.gr i :=
  cokernel.map (FP.fl'.step i) (FP.fl.step i) (stepψ FP i.castSucc) (stepψ FP i.succ)
    (step_stepψ FP i)

@[reassoc]
theorem π_grψ (i : Fin P.r) : FP.fl'.π i ≫ grψ FP i = stepψ FP i.succ ≫ FP.fl.π i := by
  simp [grψ, Vert.Flag.π]

theorem genRes_grψ (i : Fin P.r) : B.genRes.map (grψ FP i) = (FP.grIso i).inv := by
  rw [← Iso.comp_hom_eq_id, ← cancel_epi (B.genRes.map (FP.fl'.π i)), ← Functor.map_comp_assoc,
    π_grψ, Functor.map_comp, Category.assoc, Vert.Model.FlagPair.π_grIso_hom, genRes_stepψ,
    Iso.inv_hom_id_assoc, Category.comp_id]

def grPres (i : Fin P.r) : Pres B where
  r := 1
  E := FP.fl.gr i
  E' := FP.fl'.gr i
  vb := FP.fl.isVB_gr i
  vb' := FP.fl'.isVB_gr i
  ψ := grψ FP i
  iso := by rw [genRes_grψ]; infer_instance

theorem isZero_stepPres_zero : IsZero (stepPres FP 0).mod := by
  have hZ : IsZero (FP.fl.F 0) := VB.isVB_zero_iff.1 (by simpa using FP.fl.isVB 0)
  exact IsZero.of_epi_eq_zero (cokernel.π (stepψ FP 0)) (hZ.eq_of_src _ _)

def stepPresLastIso : (stepPres FP (Fin.last P.r)).mod ≅ P.mod :=
  cokernel.mapIso (stepψ FP (Fin.last P.r)) P.ψ (asIso (FP.fl'.ι (Fin.last P.r)))
    (asIso (FP.fl.ι (Fin.last P.r))) (stepψ_ι FP _)

theorem isExt_step (i : Fin P.r) :
    IsExt (stepPres FP i.castSucc).mod (stepPres FP i.succ).mod (grPres FP i).mod := by
  let L₁ : ShortComplex B.X.Modules :=
    ShortComplex.mk (FP.fl'.step i) (cokernel.π (FP.fl'.step i)) (cokernel.condition _)
  let L₂ : ShortComplex B.X.Modules :=
    ShortComplex.mk (FP.fl.step i) (cokernel.π (FP.fl.step i)) (cokernel.condition _)
  have h₁ : L₁.ShortExact := { exact := ShortComplex.exact_cokernel _ }
  have h₂ : L₂.ShortExact := { exact := ShortComplex.exact_cokernel _ }
  let v : L₁ ⟶ L₂ :=
    { τ₁ := stepψ FP i.castSucc
      τ₂ := stepψ FP i.succ
      τ₃ := grψ FP i
      comm₁₂ := (step_stepψ FP i).symm
      comm₂₃ := (π_grψ FP i).symm }
  haveI : Mono v.τ₃ := Pres.mono_ψ O B (grPres FP i)
  obtain ⟨S, hS, e₁, e₂, e₃⟩ := exists_shortExact_cokernel h₁ h₂ v
  exact ⟨S, hS, e₁, e₂, e₃⟩

end Main

end GlobalTheory.MixedLocalChains.FlagFilt

namespace GlobalTheory.MixedLocalChains.FlagFilt

theorem exists_filtration : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p] (B : GlobalTheory.Vert.Model O),
    GlobalTheory.IsNormalScheme B.X → ∀ (P : Pres B) (g : Γ(B.X, ⊤)), Kills g P.mod →
    (haveI := P.iso; Nonempty (GlobalTheory.Vert.Model.FlagPair (GlobalTheory.Vert.Model.GenIso.ofHom P.ψ) P.r)) →
    ∃ (Qs : Fin (P.r + 1) → Pres B) (Rs : Fin P.r → Pres B), IsZero (Qs 0).mod ∧
      Nonempty ((Qs (Fin.last P.r)).mod ≅ P.mod) ∧ (∀ i, (Rs i).r = 1) ∧
      (∀ i, Kills g (Qs i).mod) ∧ (∀ i, Kills g (Rs i).mod) ∧
      ∀ i : Fin P.r, IsExt (Qs i.castSucc).mod (Qs i.succ).mod (Rs i).mod := by
  intro O _ _ _ p _ _ _ B _ P g hg hFP
  haveI := P.iso
  obtain ⟨FP⟩ := hFP
  have hK : ∀ i, Kills g (stepPres FP i).mod := fun i =>
    Fin.reverseInduction (motive := fun i => Kills g (stepPres FP i).mod)
      (kills_of_mono (stepPresLastIso FP).hom hg)
      (fun j h => (kills_of_isExt (isExt_step FP j) h).1) i
  exact ⟨stepPres FP, grPres FP, isZero_stepPres_zero FP, ⟨stepPresLastIso FP⟩, fun _ => rfl, hK,
    fun i => (kills_of_isExt (isExt_step FP i) (hK i.succ)).2, isExt_step FP⟩

end GlobalTheory.MixedLocalChains.FlagFilt
