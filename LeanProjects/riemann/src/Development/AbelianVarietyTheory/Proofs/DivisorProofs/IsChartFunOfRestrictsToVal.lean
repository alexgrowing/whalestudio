import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitObj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsDPModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDetGen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RTensorEqZeroOfRestrictAffineInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRuleUnitObjOfCovers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefSpecMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalSectionOfCoefficientSpec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatAffineOpenUnits
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvertibleOfFaithfullyFlatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeTensorModuleCompatStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RealMult.ChartFun

open GlobalTheory.RealMult.RuleDescend

variable {F : Type} [Field F] [NumberField F] {𝔠 : FracId F}

theorem eq_of_loc_away (R : Type) [CommRing R] (f : PrimeSpectrum R → R) (hf : ∀ p, f p ∉ p.asIdeal)
    (x y : R) (h : ∀ p, algebraMap R (Localization.Away (f p)) x = algebraMap R (Localization.Away (f p)) y) :
    x = y := by
  rw [← sub_eq_zero]
  let I : Ideal R := LinearMap.ker (LinearMap.toSpanSingleton R R (x - y))
  have hI : I = ⊤ := by
    by_contra hI
    obtain ⟨q, hq, hIq⟩ := Ideal.exists_le_maximal I hI
    let p : PrimeSpectrum R := ⟨q, hq.isPrime⟩
    have hp := h p
    rw [← sub_eq_zero, ← map_sub] at hp
    obtain ⟨⟨_, n, rfl⟩, hn⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers (f p)) _ _).1 hp
    have hmem : f p ^ n ∈ I := by
      simp only [I, LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, smul_eq_mul]
      exact hn
    exact hf p (hq.isPrime.mem_of_pow_mem n (hIq hmem))
  have h1 : (1 : R) ∈ I := hI ▸ Submodule.mem_top
  simpa [I] using h1

theorem isRapoport_of_range_subset {M : Scheme.{0}} (U : Obj F 𝔠 M) {A : Type} [CommRing A] (c : Sp A ⟶ M)
    (X : Obj F 𝔠 (Sp A)) (φ : X.A.left ⟶ U.A.left) (hX : X.IsPullBy U c φ) (hr : Set.range c ⊆ U.rapLocus) :
    X.IsRapoport := by
  rw [Obj.isRapoport_iff]
  refine Set.eq_univ_of_forall fun s ↦ ?_
  intro K _ t hs Y ψ hY
  obtain ⟨p, rfl⟩ := hs
  exact hr ⟨t p, rfl⟩ K (t ≫ c) ⟨p, rfl⟩ Y (ψ ≫ φ) (hY.comp hX)

theorem isRapoport_of_field_ext {K L : Type} [Field K] [Field L] (σ : K →+* L) {X : Obj F 𝔠 (Sp K)}
    {X' : Obj F 𝔠 (Sp L)} {φ : X'.A.left ⟶ X.A.left} (h : X'.IsPullBy X (spMap σ) φ) (hX' : X'.IsRapoport) :
    X.IsRapoport := by
  letI := σ.toAlgebra
  obtain ⟨e, -, he⟩ := Obj.exists_lieEquiv (R' := L) h
  letI := X.lieModule
  letI := X'.lieModule
  obtain ⟨_, hff, ⟨Φ⟩⟩ := GlobalTheory.T.base_change_tensor_module_compat K L (𝓞 F) X.Lie X'.Lie e he
  haveI : Module.Invertible (L ⊗[ℤ] 𝓞 F) X'.Lie := hX'
  haveI : IsNoetherianRing (K ⊗[ℤ] 𝓞 F) := Algebra.FiniteType.isNoetherianRing K _
  exact GlobalTheory.T.invertible_of_faithfully_flat (K ⊗[ℤ] 𝓞 F) (L ⊗[ℤ] 𝓞 F) X.Lie (Module.Invertible.congr Φ.symm)

theorem range_subset_rapLocus {M : Scheme.{0}} (U : Obj F 𝔠 M) {A : Type} [CommRing A] (c : Sp A ⟶ M)
    {X : Obj F 𝔠 (Sp A)} {φ : X.A.left ⟶ U.A.left} (h : X.IsPullBy U c φ) (hX : X.IsRapoport) :
    Set.range c ⊆ U.rapLocus := by
  rintro _ ⟨x, rfl⟩ K _ t ⟨y, hy⟩ Z χ hZ
  obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := t) (g := c) y x hy
  let L : Type := (pullback t c).residueField z
  let j : Sp L ⟶ pullback t c := (pullback t c).fromSpecResidueField z
  obtain ⟨σ, hσ⟩ : ∃ σ : K →+* L, spMap σ = j ≫ pullback.fst t c :=
    ⟨(Spec.preimage (j ≫ pullback.fst t c)).hom, Spec.map_preimage _⟩
  obtain ⟨τ, hτ⟩ : ∃ τ : A →+* L, spMap τ = j ≫ pullback.snd t c :=
    ⟨(Spec.preimage (j ≫ pullback.snd t c)).hom, Spec.map_preimage _⟩
  obtain ⟨Z', χ', hZ'⟩ := Z.exists_isPullBy (spMap σ)
  have h₁ := hZ'.comp hZ
  have e : spMap σ ≫ t = spMap τ ≫ c := by rw [hσ, hτ, Category.assoc, Category.assoc, pullback.condition]
  rw [e] at h₁
  obtain ⟨ψ, hψ, -⟩ := h₁.cancel h
  exact isRapoport_of_field_ext σ hZ' (hψ.isRapoport τ hX)

theorem val_eq_of_factor {R₀ : Type} [CommRing R₀] {k : ℕ} {Q : ObjClass 𝔠} (r : Rule Q R₀ k)
    {A S T : Type} [CommRing A] [CommRing S] [CommRing T] [Algebra R₀ S] [Algebra R₀ T]
    {Y : Obj F 𝔠 (Sp A)} {X : Obj F 𝔠 (Sp S)} {Z : Obj F 𝔠 (Sp T)} (κ : A →+* S) (ρ : S →ₐ[R₀] T) (ν : A →+* T)
    (hν : (ρ : S →+* T).comp κ = ν)
    {φ : X.A.left ⟶ Y.A.left} {χ : Z.A.left ⟶ Y.A.left} (hX : X.IsPullBy Y (spMap κ) φ)
    (hZ : Z.IsPullBy Y (spMap ν) χ) (qX : Q S X) (qZ : Q T Z)
    {δY : Y.DetGen} {δX : X.DetGen} {δZ : Z.DetGen} (dX : Obj.DetCorr κ φ δY.1 δX.1)
    (dZ : Obj.DetCorr ν χ δY.1 δZ.1) :
    r.val T Z qZ δZ = ρ (r.val S X qX δX) := by
  subst hν
  have hZ' := hZ
  rw [RuleDescend.spMap_comp] at hZ'
  obtain ⟨ψ, hψ, hψφ⟩ := hZ'.cancel hX
  obtain ⟨ε, e⟩ := (hψ.existsUnique_detGen (ρ : S →+* T) δX).exists
  have e' := detCorr_comp hX hψ dX e
  rw [hψφ] at e'
  obtain rfl : ε = δZ := (hZ.existsUnique_detGen _ δY).unique e' dZ
  exact r.baseChange S T ρ X qX Z qZ ψ δX ε hψ e

abbrev res (M : Scheme.{0}) {W W' : M.Opens} (hle : W' ≤ W) : Γ(M, W) →+* Γ(M, W') :=
  (M.presheaf.map (homOfLE hle).op).hom

def chartMap (M : Scheme.{0}) {W W' : M.Opens} (hle : W' ≤ W) (R₀ : Type) [CommRing R₀] :
    Γ(M, W) →+* R₀ ⊗[ℤ] Γ(M, W') :=
  (Algebra.TensorProduct.includeRight : Γ(M, W') →ₐ[ℤ] R₀ ⊗[ℤ] Γ(M, W')).toRingHom.comp (res M hle)

theorem chartMap_apply (M : Scheme.{0}) {W W' : M.Opens} (hle : W' ≤ W) (R₀ : Type) [CommRing R₀] (a : Γ(M, W)) :
    chartMap M hle R₀ a = 1 ⊗ₜ res M hle a := rfl

theorem spMap_chartMap_fromSpec (M : Scheme.{0}) {W W' : M.Opens} (hW : IsAffineOpen W) (hW' : IsAffineOpen W')
    (hle : W' ≤ W) (R₀ : Type) [CommRing R₀] :
    spMap (chartMap M hle R₀) ≫ hW.fromSpec = coefSpecMap hW' R₀ := by
  rw [chartMap, RuleDescend.spMap_comp, Category.assoc, coefSpecMap, ← hW.map_fromSpec hW' (homOfLE hle).op]
  rfl

theorem isRapoport_chart {M : Scheme.{0}} {U : Obj F 𝔠 M} {V : M.Opens} (hV : (V : Set M) = U.rapLocus)
    {W W' : M.Opens} (hW : IsAffineOpen W) (hW' : IsAffineOpen W') (hle : W' ≤ W ⊓ V) (R₀ : Type) [CommRing R₀]
    {Y : Obj F 𝔠 (Sp Γ(M, W))} {φY : Y.A.left ⟶ U.A.left} (hY : Y.IsPullBy U hW.fromSpec φY)
    {X' : Obj F 𝔠 (Sp (R₀ ⊗[ℤ] Γ(M, W')))} {φ' : X'.A.left ⟶ Y.A.left}
    (hX' : X'.IsPullBy Y (spMap (chartMap M (hle.trans inf_le_left) R₀)) φ') : X'.IsRapoport := by
  have h := hX'.comp hY
  rw [spMap_chartMap_fromSpec M hW hW'] at h
  refine isRapoport_of_range_subset U _ X' _ h ?_
  rintro _ ⟨y, rfl⟩
  rw [← hV]
  have : (coefSpecMap hW' R₀) y ∈ Set.range hW'.fromSpec := ⟨_, rfl⟩
  rw [hW'.range_fromSpec] at this
  exact (hle.trans inf_le_right) this

abbrev resL (M : Scheme.{0}) {W W' : M.Opens} (hle : W' ≤ W) : Γ(M, W) →ₗ[ℤ] Γ(M, W') :=
  (res M hle).toAddMonoidHom.toIntLinearMap

def RestrictsToVal {R₀ : Type} [CommRing R₀] {k : ℕ} (r₀ : Rule (rapObj 𝔠) R₀ k) {M : Scheme.{0}} (V : M.Opens)
    {W : M.Opens} (Y : Obj F 𝔠 (Sp Γ(M, W))) (δY : Y.DetGen) (h : R₀ ⊗[ℤ] Γ(M, W)) : Prop :=
  ∀ (W' : M.Opens), IsAffineOpen W' → ∀ (hle : W' ≤ W ⊓ V) (X' : Obj F 𝔠 (Sp (R₀ ⊗[ℤ] Γ(M, W'))))
    (φ' : X'.A.left ⟶ Y.A.left) (hX' : X'.IsRapoport) (δ' : X'.DetGen),
    X'.IsPullBy Y (spMap (chartMap M (hle.trans inf_le_left) R₀)) φ' →
    Obj.DetCorr (chartMap M (hle.trans inf_le_left) R₀) φ' δY.1 δ'.1 →
    r₀.val _ X' hX' δ' = LinearMap.lTensor R₀ (resL M (hle.trans inf_le_left)) h

theorem isChartFun_of_restrictsToVal {R₀ : Type} [CommRing R₀] {k : ℕ} (r₀ : Rule (rapObj 𝔠) R₀ k)
    {M : Scheme.{0}} {U : Obj F 𝔠 M} {V : M.Opens} (hV : (V : Set M) = U.rapLocus)
    {W : M.Opens} (hW : IsAffineOpen W) {Y : Obj F 𝔠 (Sp Γ(M, W))} {φY : Y.A.left ⟶ U.A.left}
    (hY : Y.IsPullBy U hW.fromSpec φY) (δY : Y.DetGen) (h : R₀ ⊗[ℤ] Γ(M, W)) (hh : RestrictsToVal r₀ V Y δY h) :
    IsChartFun r₀ Y δY h := by
  intro R _ _ ψ X φ hX δ hp hd
  have key : ∀ p : PrimeSpectrum R, ∃ f : R, f ∉ p.asIdeal ∧
      algebraMap R (Localization.Away f) (r₀.val R X hX δ) = algebraMap R (Localization.Away f) (tensorEval ψ h) := by
    intro p
    have hm : (spMap ψ ≫ hW.fromSpec) p ∈ W ⊓ V := by
      refine ⟨?_, ?_⟩
      · rw [← hW.range_fromSpec]; exact ⟨_, rfl⟩
      · rw [hV]; exact range_subset_rapLocus U _ (hp.comp hY) hX ⟨p, rfl⟩
    obtain ⟨W', hW', hmW', hle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 M.isBasis_affineOpens hm
    obtain ⟨f, hf, g, hg⟩ := GlobalTheory.exists_away_factor_coefSpecMap M R₀ R (spMap ψ ≫ hW.fromSpec) W' hW' p hmW'
    refine ⟨f, hf, ?_⟩
    have hτ : (g : R₀ ⊗[ℤ] Γ(M, W') →+* Localization.Away f).comp (chartMap M (hle.trans inf_le_left) R₀) =
        (algebraMap R (Localization.Away f)).comp ψ := by
      rw [← spMap_chartMap_fromSpec M hW hW' (hle.trans inf_le_left), ← Category.assoc, ← Category.assoc,
        cancel_mono, ← RuleDescend.spMap_comp, ← RuleDescend.spMap_comp] at hg
      exact congrArg CommRingCat.Hom.hom (Spec.map_injective hg)
    obtain ⟨X', φ', hX'⟩ := Y.exists_isPullBy (spMap (chartMap M (hle.trans inf_le_left) R₀))
    obtain ⟨δ', hδ'⟩ := (hX'.existsUnique_detGen _ δY).exists
    have hr' := isRapoport_chart hV hW hW' hle R₀ hY hX'
    obtain ⟨Z, χ, hZ⟩ := X.exists_isPullBy (spMap (algebraMap R (Localization.Away f)))
    obtain ⟨δZ, hδZ⟩ := (hZ.existsUnique_detGen _ δ).exists
    have hrZ := hZ.isRapoport _ hX
    have e₁ : r₀.val _ Z hrZ δZ = algebraMap R (Localization.Away f) (r₀.val R X hX δ) :=
      r₀.baseChange R _ (IsScalarTower.toAlgHom R₀ R (Localization.Away f)) X hX Z hrZ χ δ δZ hZ hδZ
    have e₂ := val_eq_of_factor r₀ _ g _ hτ hX' (isPullBy_comp hp hZ) hr' hrZ hδ' (detCorr_comp hp hZ hd hδZ)
    rw [← e₁, e₂, hh W' hW' hle X' φ' hr' δ' hX' hδ']
    clear e₁ e₂ hh
    induction h using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul r a =>
      have h1 : g (1 ⊗ₜ res M (hle.trans inf_le_left) a) = algebraMap R (Localization.Away f) (ψ a) :=
        RingHom.congr_fun hτ a
      have h2 : LinearMap.lTensor R₀ (resL M (hle.trans inf_le_left)) (r ⊗ₜ a) =
          r • ((1 : R₀) ⊗ₜ[ℤ] res M (hle.trans inf_le_left) a) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]; rfl
      rw [h2, map_smul, h1, tensorEval_tmul, map_mul, ← IsScalarTower.algebraMap_apply, Algebra.smul_def]
  choose f hf he using key
  exact eq_of_loc_away R f hf _ _ he

abbrev coefL (R₀ R₁ : Type) [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁] : R₀ →ₗ[ℤ] R₁ :=
  (algebraMap R₀ R₁).toAddMonoidHom.toIntLinearMap

theorem rTensor_val_eq {R₀ R₁ : Type} [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁] {k : ℕ}
    (r₀ : Rule (rapObj 𝔠) R₀ k) (r₁ : Rule (trivialObjectCondition 𝔠) R₁ k)
    (hr : ∀ (R : Type) [CommRing R] [Algebra R₁ R] (X : Obj F 𝔠 (Sp R)) (hX : X.IsRapoport) (δ : X.DetGen),
      r₁.val R X trivial δ = (r₀.extend R₁).val R X hX δ)
    {M : Scheme.{0}} {W W' : M.Opens} (hle : W' ≤ W) {Y : Obj F 𝔠 (Sp Γ(M, W))} (δY : Y.DetGen)
    {Y₁ : Obj F 𝔠 (Sp (R₁ ⊗[ℤ] Γ(M, W)))} {φ₁ : Y₁.A.left ⟶ Y.A.left} {δ₁ : Y₁.DetGen}
    (hY₁ : Y₁.IsPullBy Y (spMap (chartMap M le_rfl R₁)) φ₁) (hδ₁ : Obj.DetCorr (chartMap M le_rfl R₁) φ₁ δY.1 δ₁.1)
    {X' : Obj F 𝔠 (Sp (R₀ ⊗[ℤ] Γ(M, W')))} {φ' : X'.A.left ⟶ Y.A.left} (hr' : X'.IsRapoport) {δ' : X'.DetGen}
    (hX' : X'.IsPullBy Y (spMap (chartMap M hle R₀)) φ') (hδ' : Obj.DetCorr (chartMap M hle R₀) φ' δY.1 δ'.1) :
    LinearMap.rTensor Γ(M, W') (coefL R₀ R₁) (r₀.val _ X' hr' δ') =
      LinearMap.lTensor R₁ (resL M hle) (r₁.val _ Y₁ trivial δ₁) := by
  let ρ₁ : R₁ ⊗[ℤ] Γ(M, W) →ₐ[R₁] R₁ ⊗[ℤ] Γ(M, W') :=
    Algebra.TensorProduct.map (AlgHom.id R₁ R₁) (res M hle).toIntAlgHom
  let θ : R₀ ⊗[ℤ] Γ(M, W') →+* R₁ ⊗[ℤ] Γ(M, W') :=
    (Algebra.TensorProduct.map (algebraMap R₀ R₁).toIntAlgHom (AlgHom.id ℤ Γ(M, W'))).toRingHom
  obtain ⟨Z, χ, hZ⟩ := Y.exists_isPullBy (spMap (chartMap M hle R₁))
  obtain ⟨δZ, hδZ⟩ := (hZ.existsUnique_detGen _ δY).exists
  have h₁ : (ρ₁ : R₁ ⊗[ℤ] Γ(M, W) →+* R₁ ⊗[ℤ] Γ(M, W')).comp (chartMap M le_rfl R₁) = chartMap M hle R₁ := by
    ext a; simp [ρ₁, chartMap_apply]
  have h₀ : θ.comp (chartMap M hle R₀) = chartMap M hle R₁ := by
    ext a; simp [θ, chartMap_apply]
  have hrZ : Z.IsRapoport := by
    have hZ' := hZ
    rw [← h₀, RuleDescend.spMap_comp] at hZ'
    obtain ⟨ψ, hψ, -⟩ := hZ'.cancel hX'
    exact hψ.isRapoport _ hr'
  have e₁ := val_eq_of_factor r₁ _ ρ₁ _ h₁ hY₁ hZ trivial trivial hδ₁ hδZ
  have e₀ : (r₀.extend R₁).val _ Z hrZ δZ = θ (r₀.val _ X' hr' δ') := by
    letI : Algebra R₀ (R₁ ⊗[ℤ] Γ(M, W')) :=
      ((algebraMap R₁ (R₁ ⊗[ℤ] Γ(M, W'))).comp (algebraMap R₀ R₁)).toAlgebra
    let θ' : R₀ ⊗[ℤ] Γ(M, W') →ₐ[R₀] R₁ ⊗[ℤ] Γ(M, W') := { θ with commutes' := fun x ↦ rfl }
    exact val_eq_of_factor r₀ _ θ' _ h₀ hX' hZ hr' hrZ hδ' hδZ
  have l₁ : ∀ x, LinearMap.lTensor R₁ (resL M hle) x = ρ₁ x := fun x ↦ by
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul r a => rfl
  have l₀ : ∀ x, LinearMap.rTensor Γ(M, W') (coefL R₀ R₁) x = θ x := fun x ↦ by
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul r a => rfl
  rw [l₀, l₁, ← e₁, ← e₀, hr _ Z hrZ δZ]

theorem exists_isChartFun : ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (N : ℕ) (M : Scheme.{0})
  (s : M ⟶ Sp (Localization.Away (N : ℤ))) (U : Obj F 𝔠 M) (α : U.Level N) (V : M.Opens), IsDPModel N s U α V →
  ∀ (R₀ R₁ : Type) [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁], Function.Injective (algebraMap R₀ R₁) →
  ∀ (k : ℕ) (r₀ : Rule (rapObj 𝔠) R₀ k) (r₁ : Rule (trivialObjectCondition 𝔠) R₁ k),
  (∀ (R : Type) [CommRing R] [Algebra R₁ R] (X : Obj F 𝔠 (Sp R)) (hX : X.IsRapoport) (δ : X.DetGen),
    r₁.val R X trivial δ = (r₀.extend R₁).val R X hX δ) →
  ∀ (W : M.Opens) (hW : IsAffineOpen W) (Y : Obj F 𝔠 (Sp Γ(M, W))) (φY : Y.A.left ⟶ U.A.left),
    Y.IsPullBy U hW.fromSpec φY → ∀ δY : Y.DetGen, ∃ h : R₀ ⊗[ℤ] Γ(M, W), IsChartFun r₀ Y δY h := by
  intro F _ _ 𝔠 N M s U α V hDP R₀ R₁ _ _ _ hinj k r₀ r₁ hr W hW Y φY hY δY
  obtain ⟨-, -, hflat, hV, hnorm, hcod⟩ := hDP
  obtain ⟨Y₁, φ₁, hY₁⟩ := Y.exists_isPullBy (spMap (chartMap M (le_rfl : W ≤ W) R₁))
  obtain ⟨δ₁, hδ₁⟩ := (hY₁.existsUnique_detGen _ δY).exists
  let q := (LinearMap.range (coefL R₀ R₁)).mkQ
  have hex : Function.Exact (coefL R₀ R₁) q := LinearMap.exact_iff.2 (Submodule.ker_mkQ _)
  have hq : Function.Surjective q := Submodule.mkQ_surjective _
  have hzero : LinearMap.rTensor Γ(M, W) q (r₁.val _ Y₁ trivial δ₁) = 0 := by
    rw [← (TensorProduct.comm ℤ _ _).map_eq_zero_iff]
    refine rTensor_eq_zero_of_restrict_affine_inf N M s V hflat hnorm hcod W hW _ _ fun W' hW' hle ↦ ?_
    obtain ⟨X', φ', hX'⟩ := Y.exists_isPullBy (spMap (chartMap M (hle.trans inf_le_left) R₀))
    obtain ⟨δ', hδ'⟩ := (hX'.existsUnique_detGen _ δY).exists
    have e := rTensor_val_eq r₀ r₁ hr _ δY hY₁ hδ₁ (isRapoport_chart hV hW hW' hle R₀ hY hX') hX' hδ'
    have hc : ∀ x : R₁ ⊗[ℤ] Γ(M, W), LinearMap.rTensor _ (resL M (hle.trans inf_le_left))
        (TensorProduct.comm ℤ _ _ (LinearMap.rTensor Γ(M, W) q x)) = TensorProduct.comm ℤ _ _
          (LinearMap.rTensor Γ(M, W') q (LinearMap.lTensor R₁ (resL M (hle.trans inf_le_left)) x)) := fun x ↦ by
      induction x using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | add x y hx hy => simp only [map_add, hx, hy]
      | tmul r a => rfl
    refine (hc _).trans ?_
    rw [← e, (rTensor_exact Γ(M, W') hex hq).apply_apply_eq_zero, map_zero]
  obtain ⟨h, hh⟩ := (rTensor_exact Γ(M, W) hex hq _).1 hzero
  refine ⟨h, isChartFun_of_restrictsToVal r₀ hV hW hY δY h fun W' hW' hle X' φ' hr' δ' hX' hδ' ↦ ?_⟩
  haveI := (GlobalTheory.flat_and_isUnit_sections_of_flat_over_away N M s hflat W' hW').1
  refine Module.Flat.rTensor_preserves_injective_linearMap (M := Γ(M, W')) (coefL R₀ R₁) hinj ?_
  rw [rTensor_val_eq r₀ r₁ hr _ δY hY₁ hδ₁ hr' hX' hδ', ← hh, ← LinearMap.comp_apply, ← LinearMap.comp_apply,
    LinearMap.lTensor_comp_rTensor, LinearMap.rTensor_comp_lTensor]

end GlobalTheory.RealMult.ChartFun
