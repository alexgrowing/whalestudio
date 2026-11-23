import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitObj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDetGen

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RealMult.GlueTwo

theorem existsUnique_of_coprime {R W : Type} [CommRing R] [CommRing W] [Algebra R W] (a b : R) (hab : IsCoprime a b)
    [IsLocalization.Away (a * b) W] (f₁ : Localization.Away a →+* W) (f₂ : Localization.Away b →+* W)
    (hf₁ : f₁.comp (algebraMap R _) = algebraMap R W) (hf₂ : f₂.comp (algebraMap R _) = algebraMap R W)
    (x₁ : Localization.Away a) (x₂ : Localization.Away b) (h : f₁ x₁ = f₂ x₂) :
    ∃! x : R, algebraMap R (Localization.Away a) x = x₁ ∧ algebraMap R (Localization.Away b) x = x₂ := by
  refine existsUnique_of_exists_of_unique ?_ ?_
  · obtain ⟨n, c, hc⟩ := IsLocalization.Away.surj a x₁
    obtain ⟨m, d, hd⟩ := IsLocalization.Away.surj b x₂
    have e1 : f₁ x₁ * algebraMap R W a ^ n = algebraMap R W c := by
      have := congrArg f₁ hc
      rwa [map_mul, map_pow, ← RingHom.comp_apply f₁, ← RingHom.comp_apply f₁, hf₁] at this
    have e2 : f₂ x₂ * algebraMap R W b ^ m = algebraMap R W d := by
      have := congrArg f₂ hd
      rwa [map_mul, map_pow, ← RingHom.comp_apply f₂, ← RingHom.comp_apply f₂, hf₂] at this
    have key : algebraMap R W (c * b ^ m) = algebraMap R W (d * a ^ n) := by
      rw [map_mul, map_mul, ← e1, ← e2, h, map_pow, map_pow]
      ring
    obtain ⟨l, hl⟩ := IsLocalization.Away.exists_of_eq (a * b) key
    obtain ⟨u, v, huv⟩ := hab.pow (m := n + l) (n := m + l)
    have hl' : (c * a ^ l) * b ^ (m + l) = (d * b ^ l) * a ^ (n + l) := by
      linear_combination hl
    have hx₁ : (u * (c * a ^ l) + v * (d * b ^ l)) * a ^ (n + l) = c * a ^ l := by
      linear_combination (c * a ^ l) * huv - v * hl'
    have hx₂ : (u * (c * a ^ l) + v * (d * b ^ l)) * b ^ (m + l) = d * b ^ l := by
      linear_combination (d * b ^ l) * huv + u * hl'
    refine ⟨u * (c * a ^ l) + v * (d * b ^ l), ?_, ?_⟩
    · have hu : IsUnit (algebraMap R (Localization.Away a) (a ^ (n + l))) := by
        rw [map_pow]; exact (IsLocalization.Away.algebraMap_isUnit a).pow _
      rw [← hu.mul_left_inj, ← map_mul, hx₁, pow_add, map_mul, map_mul, map_pow, map_pow, ← _root_.mul_assoc, hc]
    · have hu : IsUnit (algebraMap R (Localization.Away b) (b ^ (m + l))) := by
        rw [map_pow]; exact (IsLocalization.Away.algebraMap_isUnit b).pow _
      rw [← hu.mul_left_inj, ← map_mul, hx₂, pow_add, map_mul, map_mul, map_pow, map_pow, ← _root_.mul_assoc, hd]
  · rintro x y ⟨hx₁, hx₂⟩ ⟨hy₁, hy₂⟩
    obtain ⟨n, hn⟩ := IsLocalization.Away.exists_of_eq a (hx₁.trans hy₁.symm)
    obtain ⟨m, hm⟩ := IsLocalization.Away.exists_of_eq b (hx₂.trans hy₂.symm)
    obtain ⟨u, v, huv⟩ := hab.pow (m := n) (n := m)
    linear_combination u * hn + v * hm - (x - y) * huv

theorem spMap_comp_two {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [← Spec.map_comp]; rfl

theorem spMap_id_two (A : Type) [CommRing A] : spMap (RingHom.id A) = 𝟙 (Sp A) := Spec.map_id _

theorem dualMapR_comp_two {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    Chart.dualMapR (g.comp f) = (Chart.dualMapR g).comp (Chart.dualMapR f) := by
  refine RingHom.ext fun x => TrivSqZeroExt.ext ?_ ?_ <;> simp [Chart.dualMapR]

end GlobalTheory.RealMult.GlueTwo

namespace GlobalTheory.RealMult.GlueTwo

variable {F : Type} [Field F] [NumberField F] {𝔠 : FracId F}

theorem isPullBy_comp_two {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (σ : R →+* R')
    (τ : R' →+* R'') (ρ : R →+* R'') (hρ : τ.comp σ = ρ) {X : Obj F 𝔠 (Sp R)} {X' : Obj F 𝔠 (Sp R')}
    {X'' : Obj F 𝔠 (Sp R'')} {φ : X'.A.left ⟶ X.A.left} {ψ : X''.A.left ⟶ X'.A.left}
    (h : X'.IsPullBy X (spMap σ) φ) (h' : X''.IsPullBy X' (spMap τ) ψ) : X''.IsPullBy X (spMap ρ) (ψ ≫ φ) := by
  subst hρ
  rw [spMap_comp_two]
  exact h'.comp h

theorem detCorr_comp_two {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (σ : R →+* R')
    (τ : R' →+* R'') (ρ : R →+* R'') (hρ : τ.comp σ = ρ) {X : Obj F 𝔠 (Sp R)} {X' : Obj F 𝔠 (Sp R')}
    {X'' : Obj F 𝔠 (Sp R'')} {φ : X'.A.left ⟶ X.A.left} {ψ : X''.A.left ⟶ X'.A.left}
    (h : X'.IsPullBy X (spMap σ) φ) (h' : X''.IsPullBy X' (spMap τ) ψ) {δ : X.DetOmega} {δ' : X'.DetOmega}
    {δ'' : X''.DetOmega} (hd : Obj.DetCorr σ φ δ δ') (hd' : Obj.DetCorr τ ψ δ' δ'') :
    Obj.DetCorr ρ (ψ ≫ φ) δ δ'' := by
  have hc := isPullBy_comp_two σ τ ρ hρ h h'
  subst hρ
  intro v v'' hv
  letI : Algebra R R' := σ.toAlgebra
  obtain ⟨e, he, -⟩ := Obj.exists_lieEquiv (R := R) (R' := R') h
  letI : Algebra R' R'' := τ.toAlgebra
  obtain ⟨e', he', -⟩ := Obj.exists_lieEquiv (R := R') (R' := R'') h'
  letI : Algebra R R'' := (τ.comp σ).toAlgebra
  obtain ⟨e'', he'', -⟩ := Obj.exists_lieEquiv (R := R) (R' := R'') hc
  have h1 : ∀ i, Obj.LieCorr σ φ (v i) (e (1 ⊗ₜ v i)) := fun i => (he _ _).2 rfl
  have h2 : ∀ i, Obj.LieCorr τ ψ (e (1 ⊗ₜ v i)) (e' (1 ⊗ₜ e (1 ⊗ₜ v i))) := fun i => (he' _ _).2 rfl
  have h3 : ∀ i, Obj.LieCorr (τ.comp σ) (ψ ≫ φ) (v i) (e' (1 ⊗ₜ e (1 ⊗ₜ v i))) := by
    intro i
    unfold Obj.LieCorr at h1 h2 ⊢
    rw [← Category.assoc, h2 i, Category.assoc, h1 i, dualMapR_comp_two, spMap_comp_two, Category.assoc]
  have h4 : v'' = fun i => e' (1 ⊗ₜ e (1 ⊗ₜ v i)) :=
    funext fun i => ((he'' _ _).1 (hv i)).trans ((he'' _ _).1 (h3 i)).symm
  rw [h4, hd' _ _ h2, hd v _ h1]
  rfl

theorem val_eq_of_isPullBy_two {Q : ObjClass 𝔠} {R₀ : Type} [CommRing R₀] {k : ℕ} (u : Rule Q R₀ k)
    {R R' : Type} [CommRing R] [CommRing R'] [Algebra R₀ R'] (ρ : R →+* R') {X : Obj F 𝔠 (Sp R)} {δ : X.DetGen}
    {Y₁ Y₂ : Obj F 𝔠 (Sp R')} (hQ₁ : Q R' Y₁) (hQ₂ : Q R' Y₂) {φ₁ : Y₁.A.left ⟶ X.A.left}
    {φ₂ : Y₂.A.left ⟶ X.A.left} (h₁ : Y₁.IsPullBy X (spMap ρ) φ₁) (h₂ : Y₂.IsPullBy X (spMap ρ) φ₂)
    {δ₁ : Y₁.DetGen} {δ₂ : Y₂.DetGen} (hd₁ : Obj.DetCorr ρ φ₁ δ.1 δ₁.1) (hd₂ : Obj.DetCorr ρ φ₂ δ.1 δ₂.1) :
    u.val R' Y₁ hQ₁ δ₁ = u.val R' Y₂ hQ₂ δ₂ := by
  have h₂' : Y₂.IsPullBy X (spMap (RingHom.id R') ≫ spMap ρ) φ₂ := by
    rwa [spMap_id_two, Category.id_comp]
  obtain ⟨ψ, hψ, hψφ⟩ := Obj.IsPullBy.cancel h₂' h₁
  obtain ⟨δ', hδ', -⟩ := hψ.existsUnique_detGen (RingHom.id R') δ₁
  have hc := detCorr_comp_two ρ (RingHom.id R') ρ (RingHom.id_comp ρ) h₁ hψ hd₁ hδ'
  rw [hψφ] at hc
  obtain rfl : δ' = δ₂ := (h₂.existsUnique_detGen ρ δ).unique hc hd₂
  exact (u.baseChange R' R' (AlgHom.id R₀ R') Y₁ hQ₁ Y₂ hQ₂ ψ δ₁ δ' hψ hδ').symm

theorem isUnit_natCast_away_two (R : Type) [CommRing R] (n : ℕ) :
    IsUnit ((n : ℕ) : Localization.Away ((n : ℕ) : R)) := by
  simpa using IsLocalization.Away.algebraMap_isUnit (S := Localization.Away ((n : ℕ) : R)) ((n : ℕ) : R)

theorem map_val_two {R₀ : Type} [CommRing R₀] {k n : ℕ} (u : Rule (unitObj 𝔠 n) R₀ k) {R W' : Type} [CommRing R]
    [Algebra R₀ R] [CommRing W'] [Algebra R₀ W'] (X : Obj F 𝔠 (Sp R)) (δ : X.DetGen)
    (Y₀ : Obj F 𝔠 (Sp (Localization.Away ((n : ℕ) : R)))) (φ₀ : Y₀.A.left ⟶ X.A.left)
    (h₀ : Y₀.IsPullBy X (spMap (algebraMap R _)) φ₀) (δ₀ : Y₀.DetGen)
    (hd₀ : Obj.DetCorr (algebraMap R _) φ₀ δ.1 δ₀.1) (g : Localization.Away ((n : ℕ) : R) →ₐ[R₀] W')
    (ρ : R →+* W') (hρ : (g : Localization.Away ((n : ℕ) : R) →+* W').comp (algebraMap R _) = ρ)
    (Z : Obj F 𝔠 (Sp W')) (ψ : Z.A.left ⟶ X.A.left) (hZ : Z.IsPullBy X (spMap ρ) ψ) (δZ : Z.DetGen)
    (hdZ : Obj.DetCorr ρ ψ δ.1 δZ.1) (hu : IsUnit ((n : ℕ) : W')) :
    g (u.val _ Y₀ (isUnit_natCast_away_two R n) δ₀) = u.val W' Z hu δZ := by
  obtain ⟨Z', χ, hZ'⟩ := Obj.exists_isPullBy Y₀ (spMap (g : Localization.Away ((n : ℕ) : R) →+* W'))
  obtain ⟨δZ', hdZ', -⟩ := hZ'.existsUnique_detGen _ δ₀
  rw [← u.baseChange _ W' g Y₀ (isUnit_natCast_away_two R n) Z' hu χ δ₀ δZ' hZ' hdZ']
  exact val_eq_of_isPullBy_two u ρ hu hu (isPullBy_comp_two _ _ ρ hρ h₀ hZ') hZ
    (detCorr_comp_two _ _ ρ hρ h₀ hZ' hd₀ hdZ') hdZ

end GlobalTheory.RealMult.GlueTwo

namespace GlobalTheory.RealMult.GlueTwo

variable {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {R₀ : Type} [CommRing R₀] {k : ℕ}

def GoodAt {n : ℕ} (u : Rule (unitObj 𝔠 n) R₀ k) {R : Type} [CommRing R] [Algebra R₀ R] (X : Obj F 𝔠 (Sp R))
    (δ : X.DetGen) (x : R) : Prop :=
  ∀ (Y : Obj F 𝔠 (Sp (Localization.Away ((n : ℕ) : R)))) (φ : Y.A.left ⟶ X.A.left),
    Y.IsPullBy X (spMap (algebraMap R _)) φ → ∀ δY : Y.DetGen, Obj.DetCorr (algebraMap R _) φ δ.1 δY.1 →
      algebraMap R _ x = u.val _ Y (isUnit_natCast_away_two R n) δY

theorem exists_pull_two {R S : Type} [CommRing R] [CommRing S] (ρ : R →+* S) (X : Obj F 𝔠 (Sp R)) (δ : X.DetGen) :
    ∃ (Y : Obj F 𝔠 (Sp S)) (φ : Y.A.left ⟶ X.A.left) (_ : Y.IsPullBy X (spMap ρ) φ) (δY : Y.DetGen),
      Obj.DetCorr ρ φ δ.1 δY.1 := by
  obtain ⟨Y, φ, h⟩ := Obj.exists_isPullBy X (spMap ρ)
  obtain ⟨δY, hd, -⟩ := h.existsUnique_detGen ρ δ
  exact ⟨Y, φ, h, δY, hd⟩

theorem goodAt_of_two {n : ℕ} (u : Rule (unitObj 𝔠 n) R₀ k) {R : Type} [CommRing R] [Algebra R₀ R]
    (X : Obj F 𝔠 (Sp R)) (δ : X.DetGen) (Y₀ : Obj F 𝔠 (Sp (Localization.Away ((n : ℕ) : R))))
    (φ₀ : Y₀.A.left ⟶ X.A.left) (h₀ : Y₀.IsPullBy X (spMap (algebraMap R _)) φ₀) (δ₀ : Y₀.DetGen)
    (hd₀ : Obj.DetCorr (algebraMap R _) φ₀ δ.1 δ₀.1) (x : R)
    (hx : algebraMap R _ x = u.val _ Y₀ (isUnit_natCast_away_two R n) δ₀) : GoodAt u X δ x := by
  intro Y φ h δY hd
  rw [hx]
  exact map_val_two u X δ Y₀ φ₀ h₀ δ₀ hd₀ (AlgHom.id R₀ _) (algebraMap R _) rfl Y φ h δY hd _

theorem algebraMap_eq_of_goodAt_two {n : ℕ} (u : Rule (unitObj 𝔠 n) R₀ k) {R : Type} [CommRing R] [Algebra R₀ R]
    (X : Obj F 𝔠 (Sp R)) (δ : X.DetGen) {x y : R} (hx : GoodAt u X δ x) (hy : GoodAt u X δ y) :
    algebraMap R (Localization.Away ((n : ℕ) : R)) x = algebraMap R _ y := by
  obtain ⟨Y, φ, h, δY, hd⟩ := exists_pull_two (algebraMap R (Localization.Away ((n : ℕ) : R))) X δ
  rw [hx Y φ h δY hd, hy Y φ h δY hd]

theorem isUnit_of_detGen_two {R : Type} [CommRing R] (X : Obj F 𝔠 (Sp R)) (δ δ' : X.DetGen) (c : R)
    (hc : δ'.1 = c • δ.1) : IsUnit c := by
  haveI := Obj.invertible_detOmega X
  have hmem : δ.1 ∈ Submodule.span R {δ'.1} := by rw [δ'.2]; trivial
  obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.1 hmem
  have hsurj : Function.Surjective (LinearMap.toSpanSingleton R X.DetOmega δ.1) := by
    intro m
    have hm : m ∈ Submodule.span R {δ.1} := by rw [δ.2]; trivial
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 hm
    exact ⟨a, ha⟩
  have hinj := (Module.Invertible.bijective_of_surjective hsurj).1
  have h1 : d * c = 1 := hinj (by
    simp only [LinearMap.toSpanSingleton_apply, mul_smul, ← hc, hd, one_smul])
  exact ⟨⟨c, d, by rw [mul_comm]; exact h1, h1⟩, rfl⟩

theorem goodAt_homog_two {n : ℕ} (u : Rule (unitObj 𝔠 n) R₀ k) {R : Type} [CommRing R] [Algebra R₀ R]
    (X : Obj F 𝔠 (Sp R)) (δ δ' : X.DetGen) (c : R) (hc : δ'.1 = c • δ.1) {x : R} (hx : GoodAt u X δ' x) :
    GoodAt u X δ (c ^ k * x) := by
  intro Y φ h δY hd
  have hcu := isUnit_of_detGen_two X δ δ' c hc
  obtain ⟨δY', hdY', -⟩ := h.existsUnique_detGen _ δ'
  have e : δY'.1 = algebraMap R (Localization.Away ((n : ℕ) : R)) c • δY.1 := by
    let g₁ : Y.DetGen := Subtype.mk (algebraMap R (Localization.Away ((n : ℕ) : R)) c • δY.1) (by
      rw [Submodule.span_singleton_smul_eq (hcu.map _)]; exact δY.2)
    have hγ : Obj.DetCorr (algebraMap R _) φ δ'.1 g₁.1 := by
      intro v v' hv
      simp [g₁, hd v v' hv, hc]
    exact congrArg Subtype.val ((h.existsUnique_detGen _ δ').unique hdY' hγ)
  rw [map_mul, map_pow, hx Y φ h δY' hdY']
  exact u.homog _ Y _ δY δY' _ e

end GlobalTheory.RealMult.GlueTwo

namespace GlobalTheory.RealMult.GlueTwo

variable {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {R₀ : Type} [CommRing R₀] {k : ℕ}

theorem goodAt_baseChange_two {n : ℕ} (u : Rule (unitObj 𝔠 n) R₀ k) {R R' : Type} [CommRing R] [Algebra R₀ R]
    [CommRing R'] [Algebra R₀ R'] (σ : R →ₐ[R₀] R') (X : Obj F 𝔠 (Sp R)) (X' : Obj F 𝔠 (Sp R'))
    (φ' : X'.A.left ⟶ X.A.left) (h' : X'.IsPullBy X (spMap (σ : R →+* R')) φ') (δ : X.DetGen) (δ' : X'.DetGen)
    (hd' : Obj.DetCorr (σ : R →+* R') φ' δ.1 δ'.1) {x : R} (hx : GoodAt u X δ x) : GoodAt u X' δ' (σ x) := by
  intro Y ψ h δY hd
  obtain ⟨Y₀, φ₀, h₀, δ₀, hd₀⟩ := exists_pull_two (algebraMap R (Localization.Away ((n : ℕ) : R))) X δ
  have hunit : IsUnit (((IsScalarTower.toAlgHom R₀ R' (Localization.Away ((n : ℕ) : R'))).comp σ) ((n : ℕ) : R)) := by
    simpa using isUnit_natCast_away_two R' n
  let g : Localization.Away ((n : ℕ) : R) →ₐ[R₀] Localization.Away ((n : ℕ) : R') :=
    IsLocalization.Away.liftAlgHom ((n : ℕ) : R) hunit
  have hg : (g : Localization.Away ((n : ℕ) : R) →+* Localization.Away ((n : ℕ) : R')).comp (algebraMap R _) =
      (algebraMap R' (Localization.Away ((n : ℕ) : R'))).comp (σ : R →+* R') :=
    RingHom.ext fun a => by simp [g]
  have key := map_val_two u X δ Y₀ φ₀ h₀ δ₀ hd₀ g _ hg Y (ψ ≫ φ')
    (isPullBy_comp_two _ _ _ rfl h' h) δY (detCorr_comp_two _ _ _ rfl h' h hd' hd) (isUnit_natCast_away_two R' n)
  rw [← key, ← hx Y₀ φ₀ h₀ δ₀ hd₀]
  simp [g]

theorem goodAt_rap_two {n : ℕ} (u : Rule (unitObj 𝔠 n) R₀ k) (r₀ : Rule (rapObj 𝔠) R₀ k)
    (H : ∀ (R : Type) [CommRing R] [Algebra R₀ R] (X : Obj F 𝔠 (Sp R)) (hn : IsUnit ((n : ℕ) : R))
      (hX : X.IsRapoport) (δ : X.DetGen), u.val R X hn δ = r₀.val R X hX δ)
    {R : Type} [CommRing R] [Algebra R₀ R] (X : Obj F 𝔠 (Sp R)) (hX : X.IsRapoport) (δ : X.DetGen) :
    GoodAt u X δ (r₀.val R X hX δ) := by
  intro Y φ h δY hd
  rw [H _ Y _ (h.isRapoport _ hX) δY]
  exact (r₀.baseChange R _ (IsScalarTower.toAlgHom R₀ R _) X hX Y _ φ δ δY h hd).symm

theorem isCoprime_three_two (R : Type) [CommRing R] : IsCoprime ((3 : ℕ) : R) ((2 : ℕ) : R) :=
  ⟨1, -1, by push_cast; ring⟩

theorem existsUnique_glued (s : Rule (unitObj 𝔠 3) R₀ k) (t : Rule (unitObj 𝔠 2) R₀ k)
    (H : ∀ (R : Type) [CommRing R] [Algebra R₀ R] (X : Obj F 𝔠 (Sp R)) (h₃ : IsUnit ((3 : ℕ) : R))
      (h₂ : IsUnit ((2 : ℕ) : R)) (δ : X.DetGen), s.val R X h₃ δ = t.val R X h₂ δ)
    (R : Type) [CommRing R] [Algebra R₀ R] (X : Obj F 𝔠 (Sp R)) (δ : X.DetGen) :
    ∃! x : R, GoodAt s X δ x ∧ GoodAt t X δ x := by
  refine existsUnique_of_exists_of_unique ?_ ?_
  · obtain ⟨Y₃, φ₃, h₃, δ₃, hd₃⟩ := exists_pull_two (algebraMap R (Localization.Away ((3 : ℕ) : R))) X δ
    obtain ⟨Y₂, φ₂, h₂, δ₂, hd₂⟩ := exists_pull_two (algebraMap R (Localization.Away ((2 : ℕ) : R))) X δ
    let W := Localization.Away (((3 : ℕ) : R) * ((2 : ℕ) : R))
    have u6 : IsUnit (algebraMap R W (((3 : ℕ) : R) * ((2 : ℕ) : R))) := IsLocalization.Away.algebraMap_isUnit _
    rw [map_mul] at u6
    have u3 : IsUnit ((IsScalarTower.toAlgHom R₀ R W) ((3 : ℕ) : R)) := isUnit_of_mul_isUnit_left u6
    have u2 : IsUnit ((IsScalarTower.toAlgHom R₀ R W) ((2 : ℕ) : R)) := isUnit_of_mul_isUnit_right u6
    let f₃ : Localization.Away ((3 : ℕ) : R) →ₐ[R₀] W := IsLocalization.Away.liftAlgHom ((3 : ℕ) : R) u3
    let f₂ : Localization.Away ((2 : ℕ) : R) →ₐ[R₀] W := IsLocalization.Away.liftAlgHom ((2 : ℕ) : R) u2
    have hf₃ : (f₃ : Localization.Away ((3 : ℕ) : R) →+* W).comp (algebraMap R _) = algebraMap R W :=
      RingHom.ext fun a => by simp [f₃]
    have hf₂ : (f₂ : Localization.Away ((2 : ℕ) : R) →+* W).comp (algebraMap R _) = algebraMap R W :=
      RingHom.ext fun a => by simp [f₂]
    obtain ⟨Z, ψ, hZ, δZ, hdZ⟩ := exists_pull_two (algebraMap R W) X δ
    have w3 : IsUnit ((3 : ℕ) : W) := by rw [← map_natCast (algebraMap R W) 3]; exact u3
    have w2 : IsUnit ((2 : ℕ) : W) := by rw [← map_natCast (algebraMap R W) 2]; exact u2
    have e3 := map_val_two s X δ Y₃ φ₃ h₃ δ₃ hd₃ f₃ _ hf₃ Z ψ hZ δZ hdZ w3
    have e2 := map_val_two t X δ Y₂ φ₂ h₂ δ₂ hd₂ f₂ _ hf₂ Z ψ hZ δZ hdZ w2
    obtain ⟨x, ⟨hx₃, hx₂⟩, -⟩ := existsUnique_of_coprime (W := W) _ _ (isCoprime_three_two R)
      (f₃ : Localization.Away ((3 : ℕ) : R) →+* W) (f₂ : Localization.Away ((2 : ℕ) : R) →+* W) hf₃ hf₂ _ _
      (show f₃ _ = f₂ _ from e3.trans ((H W Z w3 w2 δZ).trans e2.symm))
    exact ⟨x, goodAt_of_two s X δ Y₃ φ₃ h₃ δ₃ hd₃ x hx₃, goodAt_of_two t X δ Y₂ φ₂ h₂ δ₂ hd₂ x hx₂⟩
  · rintro x y ⟨hx₃, hx₂⟩ ⟨hy₃, hy₂⟩
    let W := Localization.Away (((3 : ℕ) : R) * ((2 : ℕ) : R))
    have u6 : IsUnit (algebraMap R W (((3 : ℕ) : R) * ((2 : ℕ) : R))) := IsLocalization.Away.algebraMap_isUnit _
    rw [map_mul] at u6
    let f₃ : Localization.Away ((3 : ℕ) : R) →+* W :=
      IsLocalization.Away.lift ((3 : ℕ) : R) (isUnit_of_mul_isUnit_left u6)
    let f₂ : Localization.Away ((2 : ℕ) : R) →+* W :=
      IsLocalization.Away.lift ((2 : ℕ) : R) (isUnit_of_mul_isUnit_right u6)
    obtain ⟨z, -, hz⟩ := existsUnique_of_coprime (W := W) _ _ (isCoprime_three_two R) f₃ f₂
      (IsLocalization.Away.lift_comp _ _) (IsLocalization.Away.lift_comp _ _)
      (algebraMap R _ x) (algebraMap R _ x) (by simp [f₃, f₂])
    exact (hz x ⟨rfl, rfl⟩).trans (hz y ⟨(algebraMap_eq_of_goodAt_two s X δ hx₃ hy₃).symm,
      (algebraMap_eq_of_goodAt_two t X δ hx₂ hy₂).symm⟩).symm

end GlobalTheory.RealMult.GlueTwo

namespace GlobalTheory.RealMult.GlueTwo

variable {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {R₀ : Type} [CommRing R₀] {k : ℕ}

def glueRule (s : Rule (unitObj 𝔠 3) R₀ k) (t : Rule (unitObj 𝔠 2) R₀ k)
    (H : ∀ (R : Type) [CommRing R] [Algebra R₀ R] (X : Obj F 𝔠 (Sp R)) (h₃ : IsUnit ((3 : ℕ) : R))
      (h₂ : IsUnit ((2 : ℕ) : R)) (δ : X.DetGen), s.val R X h₃ δ = t.val R X h₂ δ) :
    Rule (trivialObjectCondition 𝔠) R₀ k where
  val R _ _ X _ δ := (existsUnique_glued s t H R X δ).exists.choose
  homog R _ _ X _ δ δ' c hc := by
    have h' := (existsUnique_glued s t H R X δ').exists.choose_spec
    exact ((existsUnique_glued s t H R X δ).unique (existsUnique_glued s t H R X δ).exists.choose_spec
      ⟨goodAt_homog_two s X δ δ' c hc h'.1, goodAt_homog_two t X δ δ' c hc h'.2⟩).symm
  baseChange R R' _ _ _ _ σ X _ X' _ φ δ δ' h hd := by
    have h₀ := (existsUnique_glued s t H R X δ).exists.choose_spec
    exact (existsUnique_glued s t H R' X' δ').unique (existsUnique_glued s t H R' X' δ').exists.choose_spec
      ⟨goodAt_baseChange_two s σ X X' φ h δ δ' hd h₀.1, goodAt_baseChange_two t σ X X' φ h δ δ' hd h₀.2⟩

end GlobalTheory.RealMult.GlueTwo

namespace GlobalTheory.RealMult

theorem exists_rule_allObj_of_three_two :
    ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (R₀ : Type) [CommRing R₀] (k : ℕ)
      (r₀ : Rule (rapObj 𝔠) R₀ k) (s : Rule (unitObj 𝔠 3) R₀ k) (t : Rule (unitObj 𝔠 2) R₀ k),
      (∀ (R : Type) [CommRing R] [Algebra R₀ R] (X : Obj F 𝔠 (Sp R)) (h₃ : IsUnit ((3 : ℕ) : R)) (h₂ : IsUnit ((2 : ℕ) : R))
        (δ : X.DetGen), s.val R X h₃ δ = t.val R X h₂ δ) →
      (∀ (R : Type) [CommRing R] [Algebra R₀ R] (X : Obj F 𝔠 (Sp R)) (h₃ : IsUnit ((3 : ℕ) : R)) (hX : X.IsRapoport)
        (δ : X.DetGen), s.val R X h₃ δ = r₀.val R X hX δ) →
      (∀ (R : Type) [CommRing R] [Algebra R₀ R] (X : Obj F 𝔠 (Sp R)) (h₂ : IsUnit ((2 : ℕ) : R)) (hX : X.IsRapoport)
        (δ : X.DetGen), t.val R X h₂ δ = r₀.val R X hX δ) →
      ∃ r : Rule (trivialObjectCondition 𝔠) R₀ k, ∀ (R : Type) [CommRing R] [Algebra R₀ R] (X : Obj F 𝔠 (Sp R)) (hX : X.IsRapoport)
        (δ : X.DetGen), r.val R X trivial δ = r₀.val R X hX δ := by
  intro F _ _ 𝔠 R₀ _ k r₀ s t H H₃ H₂
  refine ⟨GlueTwo.glueRule s t H, fun R _ _ X hX δ => ?_⟩
  exact (GlueTwo.existsUnique_glued s t H R X δ).unique
    (GlueTwo.existsUnique_glued s t H R X δ).exists.choose_spec
    ⟨GlueTwo.goodAt_rap_two s r₀ H₃ X hX δ, GlueTwo.goodAt_rap_two t r₀ H₂ X hX δ⟩

end GlobalTheory.RealMult
