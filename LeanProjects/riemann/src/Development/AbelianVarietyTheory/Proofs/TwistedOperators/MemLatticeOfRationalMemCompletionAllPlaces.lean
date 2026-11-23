import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt intAt latV latA)

noncomputable section
namespace GlobalTheory.RatLat

theorem dual_gens {A K W : Type} [CommRing A] [IsDomain A] [IsDedekindDomain A] [Field K] [Algebra A K]
    [IsFractionRing A K] [AddCommGroup W] [Module K W] [Module A W] [IsScalarTower A K W] (M : Submodule A W)
    (hfg : M.FG) (hden : ∀ v : W, ∃ d : A, d ≠ 0 ∧ d • v ∈ M) :
    ∃ (m : ℕ) (g : Fin m → W) (Φ : Fin m → W →ₗ[K] K), (∀ i, g i ∈ M) ∧
      (∀ i, ∀ x ∈ M, Φ i x ∈ (algebraMap A K).range) ∧ ∀ x, x = ∑ i, Φ i x • g i := by
  classical
  haveI hfin : Module.Finite A M := Module.Finite.iff_fg.2 hfg
  have hcancel : ∀ (d : A) (x : W), d ≠ 0 → d • x = 0 → x = 0 := by
    intro d x hd h
    rw [← IsScalarTower.algebraMap_smul K d x] at h
    exact (smul_eq_zero.1 h).resolve_left ((map_ne_zero_iff _ (IsFractionRing.injective A K)).2 hd)
  haveI hflat : Module.Flat A M := by
    rw [IsDedekindDomain.flat_iff_torsion_eq_bot, eq_bot_iff]
    rintro x ⟨d, hd⟩
    have : (d : A) • (x : W) = 0 := congrArg Subtype.val hd
    exact Subtype.ext (hcancel d x (nonZeroDivisors.coe_ne_zero d) this)
  haveI hfp : Module.FinitePresentation A M := Module.finitePresentation_of_finite _ _
  haveI hproj : Module.Projective A M := Module.Flat.projective_of_finitePresentation
  obtain ⟨m, π, hπ⟩ := Module.Finite.exists_fin' A M
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property π LinearMap.id hπ
  let g : Fin m → W := fun i => (π (Pi.single i 1) : W)
  have hg : ∀ i, g i ∈ M := fun i => (π (Pi.single i 1)).2
  have hexp : ∀ x : M, (x : W) = ∑ i, (algebraMap A K (σ x i)) • g i := by
    intro x
    have h1 : π (σ x) = x := LinearMap.congr_fun hσ x
    conv_lhs => rw [← h1, LinearMap.pi_apply_eq_sum_univ π (σ x)]
    rw [Submodule.coe_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Submodule.coe_smul, IsScalarTower.algebraMap_smul]
    congr 2
    congr 1
    funext j
    simp [Pi.single_apply, eq_comm]
  have hsp : Submodule.span K (M : Set W) = ⊤ := by
    rw [eq_top_iff]
    intro v _
    obtain ⟨d, hd, hv⟩ := hden v
    have hd' : algebraMap A K d ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective A K)).2 hd
    have : v = (algebraMap A K d)⁻¹ • (d • v) := by
      rw [← IsScalarTower.algebraMap_smul K d v, smul_smul, inv_mul_cancel₀ hd', one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hv)
  have hunitW : ∀ x : nonZeroDivisors A, IsUnit (algebraMap A (Module.End A W) x) :=
    (isLocalizedModule_id (nonZeroDivisors A) W K).map_units
  have hunitK : ∀ x : nonZeroDivisors A, IsUnit (algebraMap A (Module.End A K) x) :=
    (isLocalizedModule_id (nonZeroDivisors A) K K).map_units
  haveI hloc : IsLocalizedModule (nonZeroDivisors A) M.subtype := by
    refine ⟨hunitW, fun v => ?_, fun {x y} h => ⟨1, by simpa using Subtype.ext h⟩⟩
    obtain ⟨d, hd, hv⟩ := hden v
    exact ⟨(⟨d • v, hv⟩, ⟨d, mem_nonZeroDivisors_of_ne_zero hd⟩), rfl⟩
  let φ : Fin m → M →ₗ[A] K := fun i => (Algebra.linearMap A K) ∘ₗ (LinearMap.proj i) ∘ₗ σ
  let Φ0 : Fin m → W →ₗ[A] K := fun i => IsLocalizedModule.lift (nonZeroDivisors A) M.subtype (φ i) hunitK
  have hΦ0 : ∀ i (x : M), Φ0 i (x : W) = algebraMap A K (σ x i) := fun i x =>
    IsLocalizedModule.lift_apply _ M.subtype (φ i) hunitK x
  let Φ : Fin m → W →ₗ[K] K := fun i => (Φ0 i).extendScalarsOfIsLocalization (nonZeroDivisors A) K
  have hΦ : ∀ i (x : M), Φ i (x : W) = algebraMap A K (σ x i) := fun i x => hΦ0 i x
  refine ⟨m, g, Φ, hg, fun i x hx => ⟨σ ⟨x, hx⟩ i, (hΦ i ⟨x, hx⟩).symm⟩, fun x => ?_⟩
  have hL : (LinearMap.id : W →ₗ[K] W) = ∑ i, (LinearMap.smulRight (Φ i) (g i)) := by
    refine LinearMap.ext_on hsp fun y hy => ?_
    rw [LinearMap.id_apply, LinearMap.sum_apply]
    simp only [LinearMap.smulRight_apply]
    refine (hexp ⟨y, hy⟩).trans (Finset.sum_congr rfl fun i _ => ?_)
    exact congrArg (· • g i) (hΦ i ⟨y, hy⟩).symm
  have := LinearMap.congr_fun hL x
  simpa using this

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

theorem coe_mem_int_iff {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (f : F) :
    algebraMap F (Fv F v) f ∈ v.adicCompletionIntegers F ↔ v.valuation F f ≤ 1 := by
  rw [mem_adicCompletionIntegers]
  exact Iff.of_eq (congrArg (· ≤ 1) (valuedAdicCompletion_eq_valuation' v f))

theorem int_of_intAf {F : Type} [Field F] [NumberField F] (f : F) (h : algebraMap F (Af F) f ∈ intAf F) :
    f ∈ (algebraMap (𝓞 F) F).range := by
  refine mem_integers_of_valuation_le_one F f fun v => ?_
  have := h v
  rw [AlgHom.commutes] at this
  exact (coe_mem_int_iff v f).1 this

theorem smul_intAf {F : Type} [Field F] [NumberField F] (c : 𝓞 F) {α : Af F} (hα : α ∈ intAf F) :
    (algebraMap (𝓞 F) F c) • α ∈ intAf F := by
  intro v
  rw [map_smul, Algebra.smul_def]
  refine mul_mem ((coe_mem_int_iff v _).2 (valuation_le_one v c)) (hα v)

def extF {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (ψ : E →ₗ[F] F) : AF F ⊗[F] E →ₗ[F] AF F :=
  (TensorProduct.rid F (AF F)).toLinearMap ∘ₗ LinearMap.lTensor (AF F) ψ

theorem extF_tmul {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (ψ : E →ₗ[F] F) (a : AF F) (e : E) :
    extF ψ (a ⊗ₜ[F] e) = ψ e • a := by
  simp [extF]

def extV {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ} (Φ : (Fin n → E) →ₗ[F] F)
    (y : Fin n → AF F ⊗[F] E) : AF F :=
  ∑ j, extF (Φ ∘ₗ LinearMap.single F (fun _ : Fin n => E) j) (y j)

theorem extV_gen {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ} (Φ : (Fin n → E) →ₗ[F] F)
    (a : AF F) (x : Fin n → E) : extV Φ (fun i => a ⊗ₜ[F] x i) = Φ x • a := by
  classical
  simp only [extV, extF_tmul, LinearMap.comp_apply, ← Finset.sum_smul, ← map_sum]
  congr 2
  exact Finset.univ_sum_single x

theorem extV_add {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ} (Φ : (Fin n → E) →ₗ[F] F)
    (y y' : Fin n → AF F ⊗[F] E) : extV Φ (y + y') = extV Φ y + extV Φ y' := by
  simp [extV, map_add, Finset.sum_add_distrib]

theorem extV_neg {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ} (Φ : (Fin n → E) →ₗ[F] F)
    (y : Fin n → AF F ⊗[F] E) : extV Φ (-y) = -extV Φ y := by
  simp [extV, map_neg, Finset.sum_neg_distrib]

theorem extV_zero {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ} (Φ : (Fin n → E) →ₗ[F] F) :
    extV Φ (0 : Fin n → AF F ⊗[F] E) = 0 := by
  simp [extV]

theorem smul_pairA {F : Type} [Field F] [NumberField F] (f : F) (α : Af F) :
    f • pairA F 0 α = pairA F 0 (f • α) :=
  Prod.ext (smul_zero f) rfl

theorem coord_int {D : D7} {S : HSp D} (L : Lat S) (Φ : (Fin S.rank → D.host.E) →ₗ[D.host.F] D.host.F)
    (hΦ : ∀ x ∈ L, Φ x ∈ (algebraMap (𝓞 D.host.F) D.host.F).range) (z : Fin S.rank → D.host.E)
    (hz : (fun i => pairA D.host.F 0 1 ⊗ₜ[D.host.F] z i) ∈ latV S L (fun _ => True)) :
    Φ z ∈ (algebraMap (𝓞 D.host.F) D.host.F).range := by
  have key : ∀ y ∈ latV S L (fun _ => True), ∃ β ∈ intAf D.host.F, extV Φ y = pairA D.host.F 0 β := by
    intro y hy
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨α, hαi, -, a, ha, x, hx, rfl⟩ := hy
      rw [Set.mem_singleton_iff] at ha
      subst ha
      simp only [one_mul]
      obtain ⟨c, hc⟩ := hΦ x hx
      refine ⟨algebraMap (𝓞 D.host.F) D.host.F c • α, smul_intAf c hαi, ?_⟩
      rw [extV_gen, ← hc, smul_pairA]
    | zero => exact ⟨0, fun v => by rw [map_zero]; exact zero_mem _, by rw [extV_zero]; rfl⟩
    | add y y' _ _ hy hy' =>
      obtain ⟨β, hβ, e⟩ := hy
      obtain ⟨β', hβ', e'⟩ := hy'
      exact ⟨β + β', fun v => by rw [map_add]; exact add_mem (hβ v) (hβ' v),
        by rw [extV_add, e, e', GlobalTheory.FinPlLoc.pairA_add]⟩
    | neg y _ hy =>
      obtain ⟨β, hβ, e⟩ := hy
      exact ⟨-β, fun v => by rw [map_neg]; exact neg_mem (hβ v), by rw [extV_neg, e, GlobalTheory.FinPlLoc.pairA_neg]⟩
  obtain ⟨β, hβ, e⟩ := key _ hz
  rw [extV_gen, smul_pairA] at e
  have hb : Φ z • (1 : Af D.host.F) = β := congrArg Prod.snd e
  apply int_of_intAf
  rw [Algebra.algebraMap_eq_smul_one, hb]
  exact hβ

theorem mem_of_mem_latV : ∀ (D : D7) (S : HSp D) (L : Lat S), Submodule.IsLattice D.host.E L → ∀ z : Fin S.rank → D.host.E, (fun i => pairA D.host.F 0 1 ⊗ₜ[D.host.F] z i) ∈ latV S L (fun _ => True) → z ∈ L := by
  intro D S L hL z hz
  classical
  let M : Submodule (𝓞 D.host.F) (Fin S.rank → D.host.E) := L.restrictScalars (𝓞 D.host.F)
  obtain ⟨t, g0, hg0, hgen⟩ := GlobalTheory.FinPlLoc.exists_gens L hL.fg
  have hMfg : M.FG := by
    refine ⟨Finset.univ.image g0, ?_⟩
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      exact hg0 k
    · intro x hx
      obtain ⟨c, rfl⟩ := hgen x hx
      refine Submodule.sum_mem _ fun k _ => ?_
      rw [← Int.cast_smul_eq_zsmul (𝓞 D.host.F)]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  haveI hloc : IsLocalization (Algebra.algebraMapSubmonoid (𝓞 D.host.E) (nonZeroDivisors (𝓞 D.host.F)))
      D.host.E := IsIntegralClosure.isLocalization (𝓞 D.host.F) D.host.F D.host.E (𝓞 D.host.E)
  have hden : ∀ v : Fin S.rank → D.host.E, ∃ d : 𝓞 D.host.F, d ≠ 0 ∧ d • v ∈ M := by
    intro v
    have hv : v ∈ Submodule.span D.host.E (L : Set (Fin S.rank → D.host.E)) := by
      rw [hL.span_eq_top]; trivial
    obtain ⟨⟨_, a, ha, rfl⟩, hs⟩ := multiple_mem_span_of_mem_localization_span
      (Algebra.algebraMapSubmonoid (𝓞 D.host.E) (nonZeroDivisors (𝓞 D.host.F))) D.host.E _ v hv
    rw [Submodule.span_eq] at hs
    refine ⟨a, nonZeroDivisors.coe_ne_zero ⟨a, ha⟩, ?_⟩
    show a • v ∈ L
    rw [← IsScalarTower.algebraMap_smul (𝓞 D.host.E) a v]
    exact hs
  obtain ⟨m, g, Φ, hg, hΦ, hid⟩ := dual_gens (K := D.host.F) M hMfg hden
  rw [hid z]
  refine Submodule.sum_mem _ fun k _ => ?_
  obtain ⟨c, hc⟩ := coord_int L (Φ k) (hΦ k) z hz
  rw [← hc, IsScalarTower.algebraMap_smul D.host.F c (g k)]
  exact (M.smul_mem c (hg k) : c • g k ∈ M)

end GlobalTheory.RatLat
