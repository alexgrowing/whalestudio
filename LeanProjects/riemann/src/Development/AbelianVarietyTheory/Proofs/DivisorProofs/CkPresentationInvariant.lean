import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PresentationShortExactCompatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PresentationMapMonoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PresentationCkVanishesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsVBAndClsDetOfShortExact
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PresMod

theorem shortExact_pullback {C : Type*} [Category C] [Abelian C] {A A₁ Q K K₁ : C} (f : A ⟶ Q) (f₁ : A₁ ⟶ Q)
    (ι : K ⟶ A) (ι₁ : K₁ ⟶ A₁) (h : ι ≫ f = 0) (h₁ : ι₁ ≫ f₁ = 0)
    (hS : (ShortComplex.mk ι f h).ShortExact) (hS₁ : (ShortComplex.mk ι₁ f₁ h₁).ShortExact) :
    (ShortComplex.mk (pullback.lift 0 ι₁ (by simp [h₁]) : K₁ ⟶ pullback f f₁) (pullback.fst f f₁)
      (pullback.lift_fst _ _ _)).ShortExact ∧
    (ShortComplex.mk (pullback.lift ι 0 (by simp [h]) : K ⟶ pullback f f₁) (pullback.snd f f₁)
      (pullback.lift_snd _ _ _)).ShortExact := by
  have hm₁ := hS₁.mono_f
  have hm := hS.mono_f
  have he₁ := hS₁.epi_g
  have he := hS.epi_g
  dsimp at hm₁ hm he₁ he
  constructor
  · have : Mono (pullback.lift 0 ι₁ (by simp [h₁]) : K₁ ⟶ pullback f f₁) :=
      mono_of_mono_fac (pullback.lift_snd _ _ _)
    refine ShortComplex.ShortExact.mk' (ShortComplex.exact_of_f_is_kernel _ ?_) this
      (inferInstanceAs (Epi (pullback.fst f f₁)))
    refine KernelFork.IsLimit.ofι _ _
      (fun {W} g hg => (KernelFork.IsLimit.lift' hS₁.fIsKernel (g ≫ pullback.snd f f₁)
        (by dsimp; rw [Category.assoc, ← pullback.condition, ← Category.assoc, hg, zero_comp])).1)
      (fun {W} g hg => ?_) (fun {W} g hg m hm' => ?_)
    · apply pullback.hom_ext
      · simp only [Category.assoc, hg]; erw [pullback.lift_fst]; simp
      · have := (KernelFork.IsLimit.lift' hS₁.fIsKernel (g ≫ pullback.snd f f₁)
          (by dsimp; rw [Category.assoc, ← pullback.condition, ← Category.assoc, hg, zero_comp])).2
        dsimp at this ⊢; rw [Category.assoc]; try (erw [pullback.lift_snd]; exact this)
    · rw [← cancel_mono (pullback.lift 0 ι₁ (by first | done | simp [h₁]) : K₁ ⟶ pullback f f₁)]
      refine hm'.trans ?_
      apply pullback.hom_ext
      · simp only [Category.assoc, hg]; erw [pullback.lift_fst]; simp
      · have := (KernelFork.IsLimit.lift' hS₁.fIsKernel (g ≫ pullback.snd f f₁)
          (by dsimp; rw [Category.assoc, ← pullback.condition, ← Category.assoc, hg, zero_comp])).2
        dsimp at this ⊢; rw [Category.assoc, pullback.lift_snd] <;> try exact this.symm
  · have : Mono (pullback.lift ι 0 (by simp [h]) : K ⟶ pullback f f₁) :=
      mono_of_mono_fac (pullback.lift_fst _ _ _)
    refine ShortComplex.ShortExact.mk' (ShortComplex.exact_of_f_is_kernel _ ?_) this
      (inferInstanceAs (Epi (pullback.snd f f₁)))
    refine KernelFork.IsLimit.ofι _ _
      (fun {W} g hg => (KernelFork.IsLimit.lift' hS.fIsKernel (g ≫ pullback.fst f f₁)
        (by dsimp; rw [Category.assoc, pullback.condition, ← Category.assoc, hg, zero_comp])).1)
      (fun {W} g hg => ?_) (fun {W} g hg m hm' => ?_)
    · apply pullback.hom_ext
      · have := (KernelFork.IsLimit.lift' hS.fIsKernel (g ≫ pullback.fst f f₁)
          (by dsimp; rw [Category.assoc, pullback.condition, ← Category.assoc, hg, zero_comp])).2
        dsimp at this ⊢; rw [Category.assoc]; try (erw [pullback.lift_fst]; exact this)
      · simp only [Category.assoc, hg]; erw [pullback.lift_snd]; simp
    · rw [← cancel_mono (pullback.lift ι 0 (by first | done | simp [h]) : K ⟶ pullback f f₁)]
      refine hm'.trans ?_
      apply pullback.hom_ext
      · have := (KernelFork.IsLimit.lift' hS.fIsKernel (g ≫ pullback.fst f f₁)
          (by dsimp; rw [Category.assoc, pullback.condition, ← Category.assoc, hg, zero_comp])).2
        dsimp at this ⊢; rw [Category.assoc, pullback.lift_fst] <;> try exact this.symm
      · simp only [Category.assoc, hg]; erw [pullback.lift_snd]; simp

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] [CharZero O]
  [CharP (ResidueField O) p] {B : Vert.Model O}

def idPres (E : B.X.Modules) (r : ℕ) (h : GlobalTheory.VB.IsVB E r) : Pres B where
  r := r
  E := E
  E' := E
  vb := h
  vb' := h
  ψ := 𝟙 E
  iso := by rw [CategoryTheory.Functor.map_id]; infer_instance

theorem ck_eq_of_mod_iso (hB : GlobalTheory.IsNormalScheme B.X) (P P' : Pres B) (e : P.mod ≅ P'.mod) (k : ℕ) :
    P.ck p k = P'.ck p k := by
  have hm := GlobalTheory.T.presentation_map_mono O B P
  have hm' := GlobalTheory.T.presentation_map_mono O B P'
  obtain ⟨π₀, hπd⟩ : ∃ π₀ : P.E ⟶ P.mod, π₀ = cokernel.π P.ψ := ⟨_, rfl⟩
  have hπ₀ : P.ψ ≫ π₀ = 0 := by rw [hπd]; exact cokernel.condition _
  have hπe : Epi π₀ := by rw [hπd]; exact (inferInstance : Epi (cokernel.π P.ψ))
  obtain ⟨q, hqd⟩ : ∃ q : P.E ⟶ P'.mod, q = π₀ ≫ e.hom := ⟨_, rfl⟩
  obtain ⟨q₁, hqd₁⟩ : ∃ q₁ : P'.E ⟶ P'.mod, q₁ = cokernel.π P'.ψ := ⟨_, rfl⟩
  have hq : P.ψ ≫ q = 0 := by rw [hqd, ← Category.assoc, hπ₀, zero_comp]
  have hq₁ : P'.ψ ≫ q₁ = 0 := by rw [hqd₁]; exact cokernel.condition _
  have hS : (ShortComplex.mk P.ψ q hq).ShortExact := by
    haveI : Epi q := by rw [hqd]; exact epi_comp' hπe (IsIso.epi_of_iso e.hom)
    refine ShortComplex.ShortExact.mk' ?_ hm this
    subst hqd hπd
    exact ShortComplex.exact_of_g_is_cokernel _
      ((cokernelIsCokernel P.ψ).ofIsoColimit (Cofork.ext e rfl))
  have hS₁ : (ShortComplex.mk P'.ψ q₁ hq₁).ShortExact := by
    haveI : Epi q₁ := by rw [hqd₁]; exact (inferInstance : Epi (cokernel.π P'.ψ))
    refine ShortComplex.ShortExact.mk' ?_ hm' this
    subst hqd₁
    exact ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel P'.ψ)
  obtain ⟨h1, h2⟩ := shortExact_pullback q q₁ P.ψ P'.ψ hq hq₁ hS hS₁
  obtain ⟨hvF, -⟩ := GlobalTheory.VBExt.isVB_and_cls_det_of_shortExact B.X _ P.r P'.r h2 P.vb' P'.vb
  let ψ₂ : pullback q q₁ ⟶ P.E ⊞ P'.E := biprod.lift (pullback.fst q q₁) (pullback.snd q q₁)
  have hbi := (ShortComplex.Splitting.ofHasBinaryBiproduct P.E P'.E).shortExact
  let φ : ShortComplex.mk (pullback.lift P.ψ 0 (by simp [hq]) : P.E' ⟶ pullback q q₁) (pullback.snd q q₁)
      (pullback.lift_snd _ _ _) ⟶ ShortComplex.mk (biprod.inl : P.E ⟶ P.E ⊞ P'.E) biprod.snd (by simp) :=
    { τ₁ := P.ψ, τ₂ := ψ₂, τ₃ := 𝟙 _,
      comm₁₂ := by
        apply biprod.hom_ext <;>
          simp only [ψ₂, Category.assoc, biprod.inl_fst, biprod.inl_snd, biprod.lift_fst,
            biprod.lift_snd, Category.comp_id, comp_zero] <;>
          first | exact (pullback.lift_fst _ _ _).symm | exact (pullback.lift_snd _ _ _).symm,
      comm₂₃ := by simp [ψ₂] }
  have hgen : IsIso (B.genRes.map ψ₂) := by
    have := hvF.isQuasicoherent
    have := P.vb'.isQuasicoherent
    have := P.vb.isQuasicoherent
    have := (P.vb.biprod P'.vb).isQuasicoherent
    have h₁ := GlobalTheory.QCoh.shortExact_map_pullback B.gen.ι h2
    have h₂ := GlobalTheory.QCoh.shortExact_map_pullback B.gen.ι hbi
    exact ShortComplex.isIso₂_of_shortExact_of_isIso₁₃' (B.genRes.mapShortComplex.map φ) h₁ h₂ P.iso
      (by change IsIso (B.genRes.map (𝟙 P'.E)); rw [CategoryTheory.Functor.map_id]; infer_instance)
  let P₂ : Pres B := ⟨P.r + P'.r, P.E ⊞ P'.E, pullback q q₁, P.vb.biprod P'.vb, hvF, ψ₂, hgen⟩
  have hsp : (ShortComplex.mk (biprod.inr : P'.E ⟶ P.E ⊞ P'.E) biprod.fst biprod.inr_fst).ShortExact :=
    ShortComplex.Splitting.shortExact
      { r := biprod.snd, s := biprod.inl, f_r := biprod.inr_snd, s_g := biprod.inl_fst,
        id := by rw [add_comm]; exact biprod.total }
  have e1 := GlobalTheory.T.presentation_short_exact_compat _ p B hB P' P₂ (idPres P.E P.r P.vb) biprod.inr biprod.fst
    (pullback.lift 0 P'.ψ (by simp [hq₁])) (pullback.fst q q₁) biprod.inr_fst (pullback.lift_fst _ _ _)
    hsp h1
    (by
      change P'.ψ ≫ biprod.inr = _ ≫ ψ₂
      apply biprod.hom_ext <;>
        simp only [ψ₂, Category.assoc, biprod.inr_fst, biprod.inr_snd, biprod.lift_fst,
          biprod.lift_snd, Category.comp_id, comp_zero] <;>
        first | exact (pullback.lift_fst _ _ _).symm | exact (pullback.lift_snd _ _ _).symm)
    (by change ψ₂ ≫ biprod.fst = pullback.fst q q₁ ≫ 𝟙 _; simp [ψ₂]) k
  have e2 := GlobalTheory.T.presentation_short_exact_compat _ p B hB P P₂ (idPres P'.E P'.r P'.vb) biprod.inl biprod.snd
    (pullback.lift P.ψ 0 (by simp [hq])) (pullback.snd q q₁) biprod.inl_snd (pullback.lift_snd _ _ _)
    hbi h2 φ.comm₁₂ (by change ψ₂ ≫ biprod.snd = pullback.snd q q₁ ≫ 𝟙 _; simp [ψ₂]) k
  have z1 := GlobalTheory.T.presentation_ck_vanishes O p B hB (idPres P.E P.r P.vb) (inferInstanceAs (IsIso (𝟙 P.E))) k
  have z2 := GlobalTheory.T.presentation_ck_vanishes O p B hB (idPres P'.E P'.r P'.vb) (inferInstanceAs (IsIso (𝟙 P'.E))) k
  rw [z1, add_zero] at e1
  rw [z2, add_zero] at e2
  exact e2.symm.trans e1

end GlobalTheory.PresMod

theorem GlobalTheory.PresMod.ck_eq_of_iso : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p] (B : GlobalTheory.Vert.Model O), GlobalTheory.IsNormalScheme B.X → ∀ (P P' : Pres B), Nonempty (P.mod ≅ P'.mod) → ∀ k : ℕ, P.ck p k = P'.ck p k := by
  intro O _ _ _ p _ _ _ B hB P P' e k
  exact GlobalTheory.PresMod.ck_eq_of_mod_iso p hB P P' e.some k
