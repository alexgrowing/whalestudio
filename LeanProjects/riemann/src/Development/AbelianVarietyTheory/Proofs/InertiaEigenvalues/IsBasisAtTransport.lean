import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.SignAtBasePlaceEqEmbedding
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TensorMapDescent
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SpanImageLeOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VectorValuedLiftFieldChange
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open Formalism.L2.Host (embLL0 CharFrame)
open GlobalTheory.TwInputs GlobalTheory.TwInputs.Move
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CoefLatIso

open MvPolynomial

theorem mem_localization_comap_iff {R R' W W' : Type} [CommRing R] [CommRing R'] [AddCommGroup W] [Module R W]
    [AddCommGroup W'] [Module R' W'] (φ : R ≃+* R') (f : W → W') (hf : ∀ (r : R) x, f (r • x) = φ r • f x)
    (p : Ideal R') [p.IsPrime] (L : Submodule R W) (L' : Submodule R' W') (hL : ∀ x, f x ∈ L' ↔ x ∈ L) (x : W) :
    x ∈ Formalism.HermitianLatticesTheory.localization₂ (p.comap (φ : R →+* R')) L ↔ f x ∈ Formalism.HermitianLatticesTheory.localization₂ p L' := by
  show (∃ s ∈ (p.comap (φ : R →+* R')).primeCompl, s • x ∈ L) ↔ ∃ s ∈ p.primeCompl, s • f x ∈ L'
  constructor
  · rintro ⟨s, hs, h⟩
    refine ⟨φ s, ?_, ?_⟩
    · rw [Ideal.mem_primeCompl_iff] at hs ⊢
      exact hs
    · rw [← hf]; exact (hL _).2 h
  · rintro ⟨s, hs, h⟩
    refine ⟨φ.symm s, ?_, ?_⟩
    · rw [Ideal.mem_primeCompl_iff] at hs ⊢
      rw [Ideal.mem_comap]
      simpa using hs
    · rw [← hL, hf, RingEquiv.apply_symm_apply]; exact h

section Fields

variable {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] (e : K' ≃+* K)

abbrev vmE (n : ℕ) : (Fin n → K') ≃+ (Fin n → K) := AddEquiv.piCongrRight fun _ : Fin n => e.toAddEquiv

theorem vmE_apply (n : ℕ) (x : Fin n → K') (a : Fin n) : vmE e n x a = e (x a) := rfl

theorem vmE_smul (n : ℕ) (r : 𝓞 K') (x : Fin n → K') :
    vmE e n (r • x) = RingOfIntegers.mapRingEquiv e r • vmE e n x :=
  funext fun i => GlobalTheory.IdealTransport.map_smul_int e r (x i)

theorem mem_span_vmE_iff {n : ℕ} (S : Set (Fin n → K')) (x : Fin n → K') :
    vmE e n x ∈ Submodule.span (𝓞 K) (vmE e n '' S) ↔ x ∈ Submodule.span (𝓞 K') S := by
  rw [← GlobalTheory.IdealTransport.span_image_span (RingOfIntegers.mapRingEquiv e) (vmE e n) (vmE_smul e n),
    GlobalTheory.IdealTransport.mem_span_image (RingOfIntegers.mapRingEquiv e) (vmE e n) (vmE_smul e n),
    AddEquiv.symm_apply_apply]

theorem mem_tauLat_iff {E : Type} [Field E] [NumberField E] {ι : Type} {n : ℕ} (emb : ι → E →+* K')
    (emb2 : ι → E →+* K) (h : ∀ τ, emb2 τ = e.toRingHom.comp (emb τ)) (τ : ι)
    (M : Submodule (𝓞 E) (Fin n → E)) (x : Fin n → K') :
    vmE e n x ∈ tauLat emb2 τ M ↔ x ∈ tauLat emb τ M := by
  have h2 : tauLat emb2 τ M =
      Submodule.span (𝓞 K) (vmE e n '' ((fun (y : Fin n → E) (a : Fin n) => emb τ (y a)) '' (M : Set (Fin n → E)))) := by
    rw [Set.image_image]
    unfold tauLat
    congr 1
    refine Set.image_congr fun y _ => funext fun a => ?_
    rw [h]; rfl
  rw [h2, mem_span_vmE_iff]
  rfl

theorem mem_dualFr' {F : Type} [Field F] [NumberField F] {n : ℕ} (L : Submodule (𝓞 F) (Fin n → F)) (y : Fin n → F) :
    y ∈ dualFr L ↔ ∀ x ∈ L, y ⬝ᵥ x ∈ (1 : Submodule (𝓞 F) F) := Iff.rfl

theorem map_mem_one_iff (a : K') : e a ∈ (1 : Submodule (𝓞 K) K) ↔ a ∈ (1 : Submodule (𝓞 K') K') := by
  simp only [Submodule.mem_one]
  constructor
  · rintro ⟨r, hr⟩
    refine ⟨(RingOfIntegers.mapRingEquiv e).symm r, e.injective ?_⟩
    rw [← hr]
    change e (e.symm (r : K)) = (r : K)
    exact e.apply_symm_apply _
  · rintro ⟨r, rfl⟩
    exact ⟨RingOfIntegers.mapRingEquiv e r, rfl⟩

theorem mem_dualFr_iff {n : ℕ} (L : Submodule (𝓞 K') (Fin n → K')) (L2 : Submodule (𝓞 K) (Fin n → K))
    (hL : ∀ x, vmE e n x ∈ L2 ↔ x ∈ L) (y : Fin n → K') : vmE e n y ∈ dualFr L2 ↔ y ∈ dualFr L := by
  have hd : ∀ x : Fin n → K', vmE e n y ⬝ᵥ vmE e n x = e (y ⬝ᵥ x) := fun x => by
    simp only [dotProduct, map_sum, map_mul, vmE_apply]
  rw [mem_dualFr', mem_dualFr']
  constructor
  · intro hy x hx
    rw [← map_mem_one_iff e, ← hd]
    exact hy _ ((hL x).2 hx)
  · intro hy x2 hx2
    obtain ⟨x, rfl⟩ := (vmE e n).surjective x2
    rw [hd, map_mem_one_iff]
    exact hy x ((hL x).1 hx2)

theorem mem_colLat_iff {n : ℕ} (B : GL (Fin n) K) (x : Fin n → K') :
    vmE e n x ∈ colLat B ↔ x ∈ colLat (Matrix.GeneralLinearGroup.map e.symm.toRingHom B) := by
  have h : colLat B = Submodule.span (𝓞 K) (vmE e n '' Set.range fun j : Fin n => fun a : Fin n =>
      ((Matrix.GeneralLinearGroup.map e.symm.toRingHom B : GL (Fin n) K') : Matrix (Fin n) (Fin n) K') a j) := by
    unfold colLat
    rw [← Set.range_comp]
    congr 1
    congr 1
    funext j a
    simp only [Function.comp_apply, vmE_apply]
    rw [Matrix.GeneralLinearGroup.map_apply]
    exact (e.apply_symm_apply _).symm
  rw [h, mem_span_vmE_iff]
  unfold colLat
  rfl

theorem isBasisAt_transport {n : ℕ} (w : HeightOneSpectrum (𝓞 K)) (M : Submodule (𝓞 K') (Fin n → K'))
    (M2 : Submodule (𝓞 K) (Fin n → K)) (hM : ∀ x, vmE e n x ∈ M2 ↔ x ∈ M) (B : GL (Fin n) K) (hB : IsBasisAt w M2 B) :
    IsBasisAt (w.comap (RingOfIntegers.mapRingEquiv e : 𝓞 K' →+* 𝓞 K) (RingOfIntegers.mapRingEquiv e).surjective) M
      (Matrix.GeneralLinearGroup.map e.symm.toRingHom B) := by
  unfold IsBasisAt at hB ⊢
  ext x
  have h1 := mem_localization_comap_iff (RingOfIntegers.mapRingEquiv e) (vmE e n) (vmE_smul e n) w.asIdeal M M2 hM x
  have h2 := mem_localization_comap_iff (RingOfIntegers.mapRingEquiv e) (vmE e n) (vmE_smul e n) w.asIdeal
    (colLat (Matrix.GeneralLinearGroup.map e.symm.toRingHom B)) (colLat B) (mem_colLat_iff e B) x
  refine h1.trans (Iff.trans ?_ h2.symm)
  rw [hB]

theorem map_smul_int' {σ : Type} (r : 𝓞 K') (P : MvPolynomial σ K') :
    map e.toRingHom (r • P) = RingOfIntegers.mapRingEquiv e r • map e.toRingHom P :=
  GlobalTheory.IoExtend.map_smul_alg e.toRingHom (RingOfIntegers.mapRingEquiv e : 𝓞 K' →+* 𝓞 K) (fun _ => rfl) r P

theorem map_symm_map {σ : Type} (P : MvPolynomial σ K') : map e.symm.toRingHom (map e.toRingHom P) = P := by
  rw [map_map]
  convert map_id P
  ext a
  simp

theorem mem_nabStd_iff {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (F : Pol K' ι n) :
    map e.toRingHom F ∈ nabStd K lam ↔ F ∈ nabStd K' lam := by
  constructor
  · intro h
    have := GlobalTheory.IoExtend.map_mem_nabStd e.symm.toRingHom lam h
    rwa [map_symm_map] at this
  · intro h
    exact GlobalTheory.IoExtend.map_mem_nabStd e.toRingHom lam h

theorem map_mem_nabP {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n)
    (M : ι → Submodule (𝓞 K') (Fin n → K')) (M2 : ι → Submodule (𝓞 K) (Fin n → K))
    (hM : ∀ τ x, vmE e n x ∈ M2 τ ↔ x ∈ M τ) {F : Pol K' ι n} (hF : F ∈ nabP lam M) :
    map e.toRingHom F ∈ nabP lam M2 := by
  unfold nabP transLat at hF ⊢
  simp only [Submodule.mem_iInf] at hF ⊢
  intro w B hB
  let B' : ι → GL (Fin n) K' := fun τ => Matrix.GeneralLinearGroup.map e.symm.toRingHom (B τ)
  have h1 := hF (w.comap (RingOfIntegers.mapRingEquiv e : 𝓞 K' →+* 𝓞 K) (RingOfIntegers.mapRingEquiv e).surjective) B'
    (fun τ => isBasisAt_transport e w (M τ) (M2 τ) (hM τ) (B τ) (hB τ))
  rw [Submodule.mem_comap] at h1 ⊢
  have hinv : ∀ t, ((B⁻¹ t : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((B'⁻¹ t : GL (Fin n) K') : Matrix (Fin n) (Fin n) K').map e.toRingHom := by
    intro t
    have : B'⁻¹ t = Matrix.GeneralLinearGroup.map e.symm.toRingHom ((B t)⁻¹) := by
      simp only [Pi.inv_apply, B', map_inv]
    rw [this]
    ext a b
    change _ = e (e.symm _)
    rw [e.apply_symm_apply]
    rfl
  have hact := GlobalTheory.IoExtend.polyAction_map e.toRingHom lam B'⁻¹ B⁻¹ hinv F
  have h2 := (mem_localization_comap_iff (RingOfIntegers.mapRingEquiv e) (map e.toRingHom) (map_smul_int' e) w.asIdeal
    (nabStd K' lam) (nabStd K lam) (mem_nabStd_iff e lam) _).1 h1
  change actP lam B⁻¹ (map e.toRingHom F) ∈ _
  rw [hact]
  exact h2

theorem map_mem_nabAtr {E : Type} [Field E] [NumberField E] {ι : Type} [Fintype ι] {n : ℕ} (emb : ι → E →+* K')
    (emb2 : ι → E →+* K) (h : ∀ τ, emb2 τ = e.toRingHom.comp (emb τ)) (lam : ι → DomWeight n)
    (M : Submodule (𝓞 E) (Fin n → E)) {F : VV K' lam} (hF : F ∈ nabAtr emb lam M) :
    (⟨map e.toRingHom F.1, GlobalTheory.Proof.TensorMapDescent.map_mem_VV _ lam _ F.2⟩ : VV K lam) ∈ nabAtr emb2 lam M := by
  unfold nabAtr nabK at hF ⊢
  rw [Submodule.mem_comap] at hF ⊢
  exact map_mem_nabP e lam _ _ (fun τ x => mem_dualFr_iff e _ _ (fun y => mem_tauLat_iff e emb emb2 h τ M y) x) hF

end Fields

theorem coefLatFn_ringEquiv (D : D7) (n : ℕ) (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K']
    (e : K' ≃+* K) (σ : K →+* ℂ) (emb : D.what₂.Tau → (D.host.E →+* K')) (O : Subring ℂ) (lam : D.what₂.Tau → DomWeight n)
    (M : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) :
    coefLatFn (σ.comp e.toRingHom) emb O lam M = coefLatFn σ (fun τ => e.toRingHom.comp (emb τ)) O lam M := by
  have hc : ∀ (P : Pol K' D.what₂.Tau n) (x : GLR D n),
      coefFn σ lam (map e.toRingHom P) x = coefFn (σ.comp e.toRingHom) lam P x := by
    intro P x
    unfold coefFn
    rw [MvPolynomial.eval₂Hom_map_hom]
  apply le_antisymm
  · rw [coefLatFn, Submodule.span_le]
    rintro _ ⟨F, hF, rfl⟩
    exact Submodule.subset_span ⟨_, map_mem_nabAtr e emb _ (fun _ => rfl) lam M hF, funext fun x => (hc F.1 x).symm⟩
  · rw [coefLatFn, Submodule.span_le]
    rintro _ ⟨G, hG, rfl⟩
    have hG' := map_mem_nabAtr e.symm (fun τ => e.toRingHom.comp (emb τ)) emb
      (fun τ => by ext a; simp) lam M hG
    refine Submodule.subset_span ⟨_, hG', funext fun x => ?_⟩
    refine Eq.trans ?_ (hc _ x)
    change coefFn σ lam G.1 x = coefFn σ lam (map e.toRingHom (map e.symm.toRingHom G.1)) x
    rw [map_map]
    congr 2
    convert (map_id G.1).symm
    ext a
    simp

end GlobalTheory.CoefLatIso
