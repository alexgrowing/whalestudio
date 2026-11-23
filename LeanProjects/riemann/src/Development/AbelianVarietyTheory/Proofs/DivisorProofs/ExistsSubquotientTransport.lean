import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsGenericIffIsGenericFor
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittRankLeSkewSignature
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSplitChartSplitChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundDomLtTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripSizesSum
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousRingEquivLocalFieldPreservesValuation
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.CuspBlock GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.FieldTransportInd

open GlobalTheory.PRep

section Gen

variable {G G' W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G'] [AddCommGroup W] [Module ℂ W]

theorem ind_eq_iff {H : Subgroup G} {σ : Representation ℂ H W} (g : G) (x : indSpace H σ) :
    ind H σ g x = x ↔ ∀ y, x.1 (y * g) = x.1 y := by
  rw [Subtype.ext_iff, funext_iff]
  rfl

variable (Φ : G ≃* G') (hΦ : Continuous Φ.symm) {H : Subgroup G} {H' : Subgroup G'}
    (hH : ∀ g, Φ g ∈ H' ↔ g ∈ H) {σ : Representation ℂ H W} {σ' : Representation ℂ H' W}
    (hσ : ∀ h : H, σ' ⟨Φ h, (hH h).2 h.2⟩ = σ h)

include hσ in
theorem comp_symm_mem (f : indSpace H σ) : f.1 ∘ Φ.symm ∈ indSpace H' σ' := by
  intro h' g'
  have hh : Φ.symm h' ∈ H := (hH _).1 (by simpa using h'.2)
  simp only [Function.comp, map_mul]
  rw [f.2 ⟨Φ.symm h', hh⟩ (Φ.symm g'), ← hσ]
  congr 2
  exact Subtype.ext (by simp)

include hΦ in

def transportFun (f : smoothPart (ind H σ)) : smoothPart (ind H' σ') :=
  ⟨⟨f.1.1 ∘ Φ.symm, comp_symm_mem Φ hH hσ f.1⟩, by
    show IsOpen {g' : G' | ind H' σ' g' _ = _}
    have : {g' : G' | ind H' σ' g' ⟨f.1.1 ∘ Φ.symm, comp_symm_mem Φ hH hσ f.1⟩ =
        ⟨f.1.1 ∘ Φ.symm, comp_symm_mem Φ hH hσ f.1⟩} = Φ.symm ⁻¹' {g : G | ind H σ g f.1 = f.1} := by
      ext g'
      simp only [Set.mem_setOf_eq, Set.mem_preimage, ind_eq_iff, Function.comp, map_mul]
      exact (Φ.symm.surjective.forall (p := fun y => f.1.1 (y * Φ.symm g') = f.1.1 y)).symm
    rw [this]
    exact hΦ.isOpen_preimage _ f.2⟩

def transport : (smInd H σ).IntertwiningMap ((smInd H' σ').comp Φ.toMonoidHom) where
  toFun := transportFun Φ hΦ hH hσ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  isIntertwining' g := by
    ext f y
    show f.1.1 (Φ.symm y * g) = f.1.1 (Φ.symm (y * Φ g))
    simp [map_mul]

theorem transport_injective : Function.Injective (transport Φ hΦ hH hσ) := by
  intro f f' h
  refine Subtype.ext (Subtype.ext (funext fun g => ?_))
  have := congrArg (fun x : smoothPart (ind H' σ') => x.1.1 (Φ g)) h
  have h2 : f.1.1 (Φ.symm (Φ g)) = f'.1.1 (Φ.symm (Φ g)) := this
  simpa using h2

end Gen

section Field

open GlobalTheory.SmGL

variable {K L : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]

def glMap (ψ : K ≃+* L) (ι : Type) [Fintype ι] [DecidableEq ι] : GL ι K ≃* GL ι L :=
  Units.mapEquiv ψ.mapMatrix.toMulEquiv

theorem det_glMap (ψ : K ≃+* L) {ι : Type} [Fintype ι] [DecidableEq ι] (g : GL ι K) :
    Matrix.GeneralLinearGroup.det (glMap ψ ι g) = Units.map ψ.toRingHom.toMonoidHom (Matrix.GeneralLinearGroup.det g) := by
  ext
  simp only [Matrix.GeneralLinearGroup.val_det_apply, Units.coe_map]
  exact (RingHom.map_det ψ.toRingHom (g : Matrix ι ι K)).symm

theorem absPow_map (ψ : K ≃+* L) (hψ : Continuous ψ) (s : ℂ) (u : Kˣ) :
    absPow L s (Units.map ψ.toRingHom.toMonoidHom u) = absPow K s u := by
  ext
  rw [val_absPow, val_absPow, GlobalTheory.LocalFieldIso.nabs_map ψ hψ]

variable {α : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
  {N : ℕ}

def levMap (ψ : K ≃+* L) : Levi K m →* Levi L m :=
  MonoidHom.pi fun a => (glMap ψ (m a)).toMonoidHom.comp (Pi.evalMonoidHom (fun a => GL (m a) K) a)

theorem levMap_apply (ψ : K ≃+* L) (g : Levi K m) (a : α) : levMap ψ g a = glMap ψ (m a) (g a) := rfl

theorem deltaHalf_levMap (ψ : K ≃+* L) (hψ : Continuous ψ) (g : Levi K m) :
    deltaHalf L m (levMap ψ g) = deltaHalf K m g := by
  rw [deltaHalf_apply, deltaHalf_apply]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [levMap_apply, det_glMap, absPow_map ψ hψ]

theorem glEquiv_mem_parab (ψ : K ≃+* L) (e : (Σ a, m a) ≃ Fin N) (g : GL (Fin N) K) :
    GlobalTheory.LFun.SplitTie.glEquiv N ψ g ∈ GlobalTheory.SmGL.parab L e ↔ g ∈ GlobalTheory.SmGL.parab K e := by
  simp only [GlobalTheory.SmGL.mem_parab]
  refine forall₂_congr fun i j => imp_congr_right fun _ => ?_
  show ψ ((g : Matrix (Fin N) (Fin N) K) i j) = 0 ↔ _
  exact map_eq_zero_iff ψ ψ.injective

theorem leviProj_glEquiv (ψ : K ≃+* L) (e : (Σ a, m a) ≃ Fin N) (p : GlobalTheory.SmGL.parab K e) :
    GlobalTheory.SmGL.leviProj L e ⟨GlobalTheory.LFun.SplitTie.glEquiv N ψ p, (glEquiv_mem_parab ψ e p).2 p.2⟩ =
      levMap ψ (GlobalTheory.SmGL.leviProj K e p) := by
  funext a
  ext i j
  rfl

theorem continuous_glEquiv_symm (ψ : K ≃+* L) (hψ : Continuous ψ) :
    Continuous (GlobalTheory.LFun.SplitTie.glEquiv N ψ).symm := by
  have hs : Continuous ψ.symm := GlobalTheory.LocalFieldIso.continuous_symm ψ hψ
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · show Continuous fun g : GL (Fin N) L => (g : Matrix (Fin N) (Fin N) L).map ψ.symm
    exact Units.continuous_val.matrix_map hs
  · show Continuous fun g : GL (Fin N) L => ((g⁻¹ : GL (Fin N) L) : Matrix (Fin N) (Fin N) L).map ψ.symm
    exact Units.continuous_coe_inv.matrix_map hs

theorem parInd_transport (ψ : K ≃+* L) (hψ : Continuous ψ) (e : (Σ a, m a) ≃ Fin N)
    {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Levi K m) W)
    (ρ' : Representation ℂ (Levi L m) W) (hρ : ∀ g, ρ' (levMap ψ g) = ρ g) :
    ∃ T : (parInd e ρ).IntertwiningMap ((parInd e ρ').comp (GlobalTheory.LFun.SplitTie.glEquiv N ψ).toMonoidHom),
      Function.Injective T :=
  ⟨transport _ (continuous_glEquiv_symm ψ hψ) (glEquiv_mem_parab ψ e) (fun p => by
      ext w
      show (deltaHalf L m (GlobalTheory.SmGL.leviProj L e _) : ℂ) • ρ' (GlobalTheory.SmGL.leviProj L e _) w =
        (deltaHalf K m (GlobalTheory.SmGL.leviProj K e p) : ℂ) • ρ (GlobalTheory.SmGL.leviProj K e p) w
      rw [leviProj_glEquiv, deltaHalf_levMap ψ hψ, hρ]),
    transport_injective _ _ _ _⟩

end Field

section Prod

open GlobalTheory.SmGL
open scoped TensorProduct

variable {K L : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]

theorem detRep_glMap (ψ : K ≃+* L) {ι : Type} [Fintype ι] [DecidableEq ι] (χ : Kˣ →* ℂˣ) (χ' : Lˣ →* ℂˣ)
    (hχ : ∀ u, χ' (Units.map ψ.toRingHom.toMonoidHom u) = χ u) (g : GL ι K) :
    detRep ι χ' (glMap ψ ι g) = detRep ι χ g := by
  ext z
  simp only [detRep, ofChar_apply, detChar_apply, det_glMap, hχ]

theorem transported_char (ψ : K ≃+* L) (hψ : Continuous ψ) (χ : Kˣ →* ℂˣ) (s : ℂ) (u : Kˣ) :
    (χ.comp (Units.map ψ.symm.toRingHom.toMonoidHom) * absPow L s) (Units.map ψ.toRingHom.toMonoidHom u) =
      (χ * absPow K s) u := by
  have : Units.map ψ.symm.toRingHom.toMonoidHom (Units.map ψ.toRingHom.toMonoidHom u) = u :=
    Units.ext (ψ.symm_apply_apply _)
  rw [MonoidHom.mul_apply, MonoidHom.mul_apply, MonoidHom.comp_apply, this, absPow_map ψ hψ]

theorem prod₂_transport (ψ : K ≃+* L) (hψ : Continuous ψ) (x x' : ℕ) (χ₁ χ₂ : Kˣ →* ℂˣ) (s₁ s₂ : ℂ) :
    ∃ T : (prod₂ (detRep (Fin x) (χ₁ * absPow K s₁)) (detRep (Fin x') (χ₂ * absPow K s₂))).IntertwiningMap
      ((prod₂ (detRep (Fin x) (χ₁.comp (Units.map ψ.symm.toRingHom.toMonoidHom) * absPow L s₁))
        (detRep (Fin x') (χ₂.comp (Units.map ψ.symm.toRingHom.toMonoidHom) * absPow L s₂))).comp
          (GlobalTheory.LFun.SplitTie.glEquiv (x + x') ψ).toMonoidHom), Function.Injective T := by
  refine parInd_transport ψ hψ _ _ _ fun g => ?_
  refine TensorProduct.ext' fun u w => ?_
  change extTensor _ _ (levMap ψ g false, levMap ψ g true) (u ⊗ₜ w) =
    extTensor _ _ (g false, g true) (u ⊗ₜ w)
  rw [extTensor_tmul, extTensor_tmul]
  change detRep (Fin x) _ (glMap ψ _ (g false)) u ⊗ₜ detRep (Fin x') _ (glMap ψ _ (g true)) w = _
  rw [detRep_glMap ψ _ _ (transported_char ψ hψ χ₁ s₁), detRep_glMap ψ _ _ (transported_char ψ hψ χ₂ s₂)]

end Prod

section Main

open GlobalTheory.SmGL

theorem isSubquotient_comp {G G' V W : Type} [Group G] [Group G'] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ G W} {ρ : Representation ℂ G V}
    (h : IsSubquotient σ ρ) (s : G' →* G) : IsSubquotient (σ.comp s) (ρ.comp s) := by
  obtain ⟨S, f, hf⟩ := h
  exact ⟨⟨S.toSubmodule, fun g _ hv => S.apply_mem_toSubmodule (s g) hv⟩,
    ⟨f.toLinearMap, fun g => f.isIntertwining' (s g)⟩, hf⟩

theorem isSubquotient_comp_symm {G G' V : Type} [Group G] [Group G'] [AddCommGroup V] [Module ℂ V]
    (Φ : G ≃* G') (ρ : Representation ℂ G' V) :
    IsSubquotient ((ρ.comp Φ.toMonoidHom).comp Φ.symm.toMonoidHom) ρ :=
  IsSubquotient.of_surjective ⟨LinearMap.id, fun g => by ext w; simp⟩ Function.surjective_id

theorem exists_subquotient_transport : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (t : E →ₐ[F] Fv F v) (x x' : ℕ) (χ₁ χ₂ : (Fv F v)ˣ →* ℂˣ) (s₁ s₂ : ℝ)
    (Vy : Type) [AddCommGroup Vy] [Module ℂ Vy]
    (Y : Representation ℂ (GL (Fin (x + x')) ((splitPrime t).adicCompletion E)) Vy)
    (V' : Type) [AddCommGroup V'] [Module ℂ V'] (Q : Representation ℂ (GL (Fin (x + x')) (Fv F v)) V'),
    IsSubquotient Q (prod₂ (detRep (Fin x) (χ₁ * absPow (Fv F v) (s₁ : ℂ)))
      (detRep (Fin x') (χ₂ * absPow (Fv F v) (s₂ : ℂ)))) →
    ∀ f : Q.IntertwiningMap (Y.comp (glEquiv (x + x') (complEquiv t (splitPrime_under t))).toMonoidHom), f ≠ 0 →
    ∃ (V'' : Type) (_ : AddCommGroup V'') (_ : Module ℂ V'')
      (Q'' : Representation ℂ (GL (Fin (x + x')) ((splitPrime t).adicCompletion E)) V''),
      IsSubquotient Q'' (prod₂
        (detRep (Fin x) (χ₁.comp (Units.map (complEquiv t (splitPrime_under t)).symm.toRingHom.toMonoidHom) *
          absPow ((splitPrime t).adicCompletion E) (s₁ : ℂ)))
        (detRep (Fin x') (χ₂.comp (Units.map (complEquiv t (splitPrime_under t)).symm.toRingHom.toMonoidHom) *
          absPow ((splitPrime t).adicCompletion E) (s₂ : ℂ)))) ∧
      ∃ f'' : Q''.IntertwiningMap Y, f'' ≠ 0 := by
  intro F E _ _ _ _ _ v t x x' χ₁ χ₂ s₁ s₂ Vy _ _ Y V' _ _ Q hQ f hf
  have hψ : Continuous (complEquiv t (splitPrime_under t)) := GlobalTheory.LFun.SplitChart.continuous_complMap _
  obtain ⟨T, hT⟩ := prod₂_transport _ hψ x x' χ₁ χ₂ (s₁ : ℂ) (s₂ : ℂ)
  let Φ := glEquiv (x + x') (complEquiv t (splitPrime_under t))
  refine ⟨V', inferInstance, inferInstance, Q.comp Φ.symm.toMonoidHom, ?_,
    ⟨f.toLinearMap, fun g => ?_⟩, ?_⟩
  · have h1 := hQ.trans (IsSubquotient.of_injective T hT)
    have h2 := isSubquotient_comp h1 Φ.symm.toMonoidHom
    exact h2.trans (isSubquotient_comp_symm Φ _)
  · have := f.isIntertwining' (Φ.symm g)
    simpa [Φ] using this
  · intro h0
    apply hf
    ext w
    exact congrArg (fun φ : Representation.IntertwiningMap (Q.comp Φ.symm.toMonoidHom) Y => φ w) h0

end Main

end GlobalTheory.FieldTransportInd
