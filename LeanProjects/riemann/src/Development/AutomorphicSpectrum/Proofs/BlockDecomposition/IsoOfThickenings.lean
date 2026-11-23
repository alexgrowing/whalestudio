import Mathlib
import PositivityTheory.PublishedTheorems.TowerLemmas.FormalTowerLemmas.Imports
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.FormalAlgebraisation

import PositivityTheory.PublishedTheorems.UnitKilling.UnitAnnihilation.UnitAnnihilators.ExistsUnitKillsOfIdempotent
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out PositivityTheory.FormalThickening

namespace GlobalTheory.CompanionTheory.Formal.IsoThick

theorem exists_unit_kills {A B : Type} [CommRing A] [CommRing B] [IsNoetherianRing A] (φ : A →+* B)
    (hφ : φ.Finite) (J : Ideal A) (hsurj : ∀ b, ∃ a, b - φ a ∈ J.map φ)
    (hinj : ∀ a, φ a = 0 → ∀ n : ℕ, a ∈ J ^ n) :
    ∃ s : A, s - 1 ∈ J ∧ (∀ k, φ k = 0 → s * k = 0) ∧ ∀ b, ∃ a, φ s * b = φ a := by
  first | exact @KrullIntersectionUnits.KrullIntersectionLemmas.GlobalTheory.CompanionTheory.Formal.IsoThick.exists_unit_kills | exact KrullIntersectionUnits.KrullIntersectionLemmas.GlobalTheory.CompanionTheory.Formal.IsoThick.exists_unit_kills | (intros; apply KrullIntersectionUnits.KrullIntersectionLemmas.GlobalTheory.CompanionTheory.Formal.IsoThick.exists_unit_kills <;> assumption)

theorem bijective_of_away {A B A' B' : Type} [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    (φ : A →+* B) (ρA : A →+* A') (ρB : B →+* B') (ψ : A' →+* B')
    (hc : ∀ a, ψ (ρA a) = ρB (φ a)) (s : A)
    (hA : @IsLocalization.Away _ _ s A' _ ρA.toAlgebra)
    (hB : @IsLocalization.Away _ _ (φ s) B' _ ρB.toAlgebra)
    (hker : ∀ k, φ k = 0 → s * k = 0) (hcok : ∀ b, ∃ a, φ s * b = φ a) :
    Function.Bijective ψ := by
  letI := ρA.toAlgebra
  letI := ρB.toAlgebra
  have eA : ∀ a, algebraMap A A' a = ρA a := fun _ => rfl
  have eB : ∀ a, algebraMap B B' a = ρB a := fun _ => rfl
  have uA : IsUnit (ρA s) := IsLocalization.Away.algebraMap_isUnit (S := A') s
  have uB : IsUnit (ρB (φ s)) := IsLocalization.Away.algebraMap_isUnit (S := B') (φ s)
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨n, a, h⟩ := IsLocalization.Away.surj (S := A') s x
    rw [eA, eA] at h
    have h1 : ρB (φ a) = 0 := by
      rw [← hc, ← h, map_mul, hx, zero_mul]
    obtain ⟨⟨_, m, rfl⟩, hm⟩ :=
      (IsLocalization.map_eq_zero_iff (Submonoid.powers (φ s)) B' (φ a)).1 h1
    have h2 : φ (s ^ m * a) = 0 := by rw [map_mul, map_pow]; exact hm
    have h3 := hker _ h2
    have h4 : ρA s * (ρA s ^ m * ρA a) = 0 := by
      have := congrArg ρA h3
      simpa [map_mul, map_pow] using this
    have h5 : ρA a = 0 := by
      have := (uA.mul_right_eq_zero).1 h4
      exact ((uA.pow m).mul_right_eq_zero).1 this
    rw [h5] at h
    exact ((uA.pow n).mul_left_eq_zero).1 h
  · intro y
    obtain ⟨n, b, h⟩ := IsLocalization.Away.surj (S := B') (φ s) y
    rw [eB, eB] at h
    obtain ⟨a, ha⟩ := hcok b
    obtain ⟨x, hx⟩ : ∃ x, x * ρA s ^ (n + 1) = ρA a := by
      refine ⟨ρA a * ↑((uA.pow (n + 1)).unit⁻¹), ?_⟩
      rw [mul_assoc]
      have : (↑((uA.pow (n + 1)).unit⁻¹) : A') * ρA s ^ (n + 1) = 1 :=
        (uA.pow (n + 1)).val_inv_mul
      rw [this, mul_one]
    refine ⟨x, ?_⟩
    have h1 : ψ x * ρB (φ s) ^ (n + 1) = y * ρB (φ s) ^ (n + 1) := by
      have := congrArg ψ hx
      rw [map_mul, map_pow, hc, hc, ← ha, map_mul, ← h] at this
      rw [this]; ring
    exact (uB.pow (n + 1)).mul_right_cancel h1

open TensorProduct in
theorem tmul_one_eq_zero_iff {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (K : Ideal R)
    (m : M) : m ⊗ₜ[R] (1 : R ⧸ K) = 0 ↔ m ∈ (K • ⊤ : Submodule R M) := by
  have h : m ⊗ₜ[R] (1 : R ⧸ K) = 0 ↔ (TensorProduct.tensorQuotEquivQuotSMul M K).symm
      (Submodule.Quotient.mk m) = 0 := by rw [TensorProduct.tensorQuotEquivQuotSMul_symm_mk]
  rw [h, LinearEquiv.map_eq_zero_iff, Submodule.Quotient.mk_eq_zero]

open TensorProduct in
theorem exists_tmul_one {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (K : Ideal R)
    (y : M ⊗[R] (R ⧸ K)) : ∃ m : M, y = m ⊗ₜ[R] (1 : R ⧸ K) := by
  obtain ⟨m, hm⟩ := Submodule.Quotient.mk_surjective _ (TensorProduct.tensorQuotEquivQuotSMul M K y)
  refine ⟨m, ?_⟩
  rw [← TensorProduct.tensorQuotEquivQuotSMul_symm_mk, hm, LinearEquiv.symm_apply_apply]

open TensorProduct in
theorem facts_of_bijective {R A B : Type} [CommRing R] [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B] (φ : A →ₐ[R] B) (K : Ideal R)
    (h : Function.Bijective (Algebra.TensorProduct.map φ (AlgHom.id R (R ⧸ K)))) :
    (∀ a, φ a = 0 → a ∈ K.map (algebraMap R A)) ∧
      ∀ b, ∃ a, b - φ a ∈ K.map (algebraMap R B) := by
  constructor
  · intro a ha
    have h1 : a ⊗ₜ[R] (1 : R ⧸ K) = 0 := by
      apply h.1
      rw [map_zero]
      simp [ha]
    have h2 := (tmul_one_eq_zero_iff K a).1 h1
    rw [Ideal.smul_top_eq_map] at h2
    exact h2
  · intro b
    obtain ⟨y, hy⟩ := h.2 (b ⊗ₜ[R] (1 : R ⧸ K))
    obtain ⟨a, rfl⟩ := exists_tmul_one K y
    refine ⟨a, ?_⟩
    have h1 : (b - φ a) ⊗ₜ[R] (1 : R ⧸ K) = 0 := by
      rw [TensorProduct.sub_tmul, ← hy]
      simp
    have h2 := (tmul_one_eq_zero_iff K _).1 h1
    rw [Ideal.smul_top_eq_map] at h2
    exact h2

open TensorProduct in
theorem bijective_of_isIso_pullback {R A B T : Type} [CommRing R] [CommRing A] [CommRing B]
    [CommRing T] [Algebra R A] [Algebra R B] [Algebra R T] (φ : A →ₐ[R] B)
    (m : pullback (Spec.map (CommRingCat.ofHom (algebraMap R B)))
        (Spec.map (CommRingCat.ofHom (algebraMap R T))) ⟶
      pullback (Spec.map (CommRingCat.ofHom (algebraMap R A)))
        (Spec.map (CommRingCat.ofHom (algebraMap R T))))
    (hm1 : m ≫ pullback.fst _ _ = pullback.fst _ _ ≫ Spec.map (CommRingCat.ofHom φ.toRingHom))
    (hm2 : m ≫ pullback.snd _ _ = pullback.snd _ _) (h : IsIso m) :
    Function.Bijective (Algebra.TensorProduct.map φ (AlgHom.id R T)) := by
  have e1 : Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map φ (AlgHom.id R T)).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] T)) =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[R] T)) ≫
        Spec.map (CommRingCat.ofHom φ.toRingHom) := by
    simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
  have e2 : Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map φ (AlgHom.id R T)).toRingHom) ≫
      Spec.map (CommRingCat.ofHom ((Algebra.TensorProduct.includeRight : T →ₐ[R] A ⊗[R] T) :
        T →+* A ⊗[R] T)) =
      Spec.map (CommRingCat.ofHom ((Algebra.TensorProduct.includeRight : T →ₐ[R] B ⊗[R] T) :
        T →+* B ⊗[R] T)) := by
    simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext a
    simp
  have key : m = (pullbackSpecIso R B T).hom ≫
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map φ (AlgHom.id R T)).toRingHom) ≫
        (pullbackSpecIso R A T).inv := by
    apply pullback.hom_ext
    · rw [hm1, Category.assoc, Category.assoc, pullbackSpecIso_inv_fst, e1, ← Category.assoc,
        pullbackSpecIso_hom_fst]
    · rw [hm2, Category.assoc, Category.assoc, pullbackSpecIso_inv_snd, e2, pullbackSpecIso_hom_snd]
  have h2 : IsIso (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.map φ (AlgHom.id R T)).toRingHom)) := by
    have : Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.map φ (AlgHom.id R T)).toRingHom) =
        (pullbackSpecIso R B T).inv ≫ m ≫ (pullbackSpecIso R A T).hom := by
      rw [key]; simp
    rw [this]
    infer_instance
  rw [isIso_SpecMap_iff] at h2
  exact h2

theorem toSpecΓ_comp {R : Type} [CommRing R] {X : Scheme.{0}} (h : X ⟶ Spec (CommRingCat.of R)) :
    X.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ h.appTop) = h := by
  apply ext_of_isAffine
  rw [Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop, Scheme.ΓSpecIso_naturality, Iso.hom_inv_id_assoc]

theorem ring_case {R A B : Type} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    [IsNoetherianRing A] (φ : A →ₐ[R] B) (hφ : φ.toRingHom.Finite) (I : Ideal R)
    (hf : ∀ e : ℕ, Function.Bijective
      (Algebra.TensorProduct.map φ (AlgHom.id R (R ⧸ I ^ (e + 1))))) :
    ∃ s : A, s - 1 ∈ I.map (algebraMap R A) ∧ (∀ k, φ k = 0 → s * k = 0) ∧
      ∀ b, ∃ a, φ s * b = φ a := by
  refine exists_unit_kills φ.toRingHom hφ (I.map (algebraMap R A)) ?_ ?_
  · intro b
    obtain ⟨a, ha⟩ := (facts_of_bijective φ _ (hf 0)).2 b
    refine ⟨a, ?_⟩
    rw [Ideal.map_map]
    have : φ.toRingHom.comp (algebraMap R A) = algebraMap R B := φ.comp_algebraMap
    rw [this]
    simpa using ha
  · intro a ha n
    have h1 := (facts_of_bijective φ _ (hf n)).1 a ha
    rw [Ideal.map_pow] at h1
    exact Ideal.pow_le_pow_right (Nat.le_succ n) h1

theorem over_pullback_fst {S T : Scheme.{0}} (t : T ⟶ S) {P Q : Over S} (g : P ⟶ Q) :
    ((Over.pullback t).map g).left ≫ pullback.fst Q.hom t = pullback.fst P.hom t ≫ g.left := by
  simp
  exact pullback.lift_fst _ _ _

theorem over_pullback_snd {S T : Scheme.{0}} (t : T ⟶ S) {P Q : Over S} (g : P ⟶ Q) :
    ((Over.pullback t).map g).left ≫ pullback.snd Q.hom t = pullback.snd P.hom t := by
  simp
  exact pullback.lift_snd _ _ _

theorem isIso_pullback_conj {S T : Scheme.{0}} (t : T ⟶ S) {P Q P' Q' : Over S} (g : P ⟶ Q)
    (eP : P ≅ P') (eQ : Q ≅ Q') (h : IsIso ((Over.pullback t).map g).left) :
    IsIso ((Over.pullback t).map (eP.inv ≫ g ≫ eQ.hom)).left := by
  haveI : IsIso ((Over.forget _).map ((Over.pullback t).map g)) := h
  haveI : IsIso ((Over.pullback t).map g) := isIso_of_reflects_iso _ (Over.forget _)
  haveI : IsIso ((Over.pullback t).map (eP.inv ≫ g ≫ eQ.hom)) := by
    rw [Functor.map_comp, Functor.map_comp]
    infer_instance
  exact inferInstanceAs (IsIso ((Over.forget T).map ((Over.pullback t).map (eP.inv ≫ g ≫ eQ.hom))))

theorem affine_case {R : Type} [CommRing R] [IsNoetherianRing R] (I : Ideal R)
    (U V : Over (Spec (CommRingCat.of R))) (g : V ⟶ U) [IsAffine U.left] [IsAffine V.left]
    [IsProper g.left] [LocallyOfFiniteType U.hom]
    (h : ∀ e, IsIso ((Over.pullback (thick R I e)).map g).left) (x : U.left)
    (hx : I ≤ (U.hom x).asIdeal) :
    ∃ s : Γ(U.left, ⊤), x ∈ U.left.basicOpen s ∧ IsIso (g.left ∣_ U.left.basicOpen s) := by
  let aU : R →+* Γ(U.left, ⊤) := ((Scheme.ΓSpecIso (.of R)).inv ≫ U.hom.appTop).hom
  let aV : R →+* Γ(V.left, ⊤) := ((Scheme.ΓSpecIso (.of R)).inv ≫ V.hom.appTop).hom
  letI : Algebra R Γ(U.left, ⊤) := aU.toAlgebra
  letI : Algebra R Γ(V.left, ⊤) := aV.toAlgebra
  have hcomm : ((Scheme.ΓSpecIso (.of R)).inv ≫ U.hom.appTop) ≫ g.left.appTop =
      (Scheme.ΓSpecIso (.of R)).inv ≫ V.hom.appTop := by
    rw [← Over.w g, Scheme.Hom.comp_appTop, Category.assoc]
  let φ : Γ(U.left, ⊤) →ₐ[R] Γ(V.left, ⊤) :=
    { g.left.appTop.hom with
      commutes' := fun r => congrArg (fun f => f.hom r) hcomm }
  have wU : U.left.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (algebraMap R Γ(U.left, ⊤))) = U.hom :=
    toSpecΓ_comp U.hom
  have wV : V.left.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (algebraMap R Γ(V.left, ⊤))) = V.hom :=
    toSpecΓ_comp V.hom
  let eU : U ≅ Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R Γ(U.left, ⊤)))) :=
    Over.isoMk U.left.isoSpec (by simpa [Scheme.isoSpec_hom] using wU)
  let eV : V ≅ Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R Γ(V.left, ⊤)))) :=
    Over.isoMk V.left.isoSpec (by simpa [Scheme.isoSpec_hom] using wV)
  have hg' : (eV.inv ≫ g ≫ eU.hom).left = Spec.map (CommRingCat.ofHom φ.toRingHom) := by
    change V.left.isoSpec.inv ≫ g.left ≫ U.left.isoSpec.hom = _
    rw [Iso.inv_comp_eq, Scheme.isoSpec_hom, Scheme.isoSpec_hom, Scheme.toSpecΓ_naturality]
    rfl
  have hbij : ∀ e : ℕ, Function.Bijective
      (Algebra.TensorProduct.map φ (AlgHom.id R (R ⧸ I ^ (e + 1)))) := by
    intro e
    refine bijective_of_isIso_pullback (T := R ⧸ I ^ (e + 1)) φ
      ((Over.pullback (thick R I e)).map (eV.inv ≫ g ≫ eU.hom)).left ?_ ?_
      (isIso_pullback_conj _ g eV eU (h e))
    · rw [← hg']
      exact over_pullback_fst (thick R I e) (eV.inv ≫ g ≫ eU.hom)
    · exact over_pullback_snd (thick R I e) (eV.inv ≫ g ≫ eU.hom)
  haveI : IsFinite g.left := IsFinite.iff_isProper_and_isAffineHom.2 ⟨inferInstance, inferInstance⟩
  have hfin : φ.toRingHom.Finite := IsFinite.finite_app g.left ⊤ (isAffineOpen_top _)
  haveI : IsLocallyNoetherian U.left := LocallyOfFiniteType.isLocallyNoetherian U.hom
  haveI : IsNoetherianRing Γ(U.left, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩
  obtain ⟨s, hs1, hker, hcok⟩ := ring_case φ hfin I hbij
  refine ⟨s, ?_, ?_⟩
  · have hq : (U.hom x).asIdeal = (U.left.toSpecΓ x).asIdeal.comap aU := by
      conv_lhs => rw [← wU]
      rfl
    have hJ : I.map (algebraMap R Γ(U.left, ⊤)) ≤ (U.left.toSpecΓ x).asIdeal := by
      rw [Ideal.map_le_iff_le_comap]
      exact hx.trans hq.le
    have hs : s ∉ (U.left.toSpecΓ x).asIdeal := fun hs =>
      (U.left.toSpecΓ x).isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (by
        have := Ideal.sub_mem _ hs (hJ hs1)
        simpa using this))
    rw [← Scheme.toSpecΓ_preimage_basicOpen]
    exact hs
  · have hD : IsAffineOpen (U.left.basicOpen s) := (isAffineOpen_top _).basicOpen s
    rw [isIso_morphismRestrict_iff_isIso_app g.left hD, ConcreteCategory.isIso_iff_bijective]
    have e : g.left ⁻¹ᵁ U.left.basicOpen s = V.left.basicOpen (φ s) :=
      Scheme.preimage_basicOpen_top g.left s
    refine bijective_of_away g.left.appTop.hom
      (U.left.presheaf.map (homOfLE le_top).op).hom (V.left.presheaf.map (homOfLE le_top).op).hom
      _ ?_ s ?_ ?_ hker hcok
    · intro a
      have := g.left.naturality (homOfLE (le_top : U.left.basicOpen s ≤ ⊤)).op
      exact congrArg (fun f => f.hom a) this
    · exact (isAffineOpen_top _).isLocalization_of_eq_basicOpen s _ rfl
    · exact (isAffineOpen_top _).isLocalization_of_eq_basicOpen (φ s) _ e

theorem fibre_subsingleton {R : Type} [CommRing R] (I : Ideal R)
    (X C : Over (Spec (CommRingCat.of R))) (p : C ⟶ X)
    (hiso : IsIso ((Over.pullback (thick R I 0)).map p).left) (c₁ c₂ : C.left)
    (h12 : p.left c₁ = p.left c₂) (hI : I ≤ (X.hom (p.left c₁)).asIdeal) : c₁ = c₂ := by
  have hsurj : Function.Surjective (Ideal.Quotient.mk (I ^ (0 + 1))) := Ideal.Quotient.mk_surjective
  haveI : IsClosedImmersion (thick R I 0) := IsClosedImmersion.spec_of_surjective _ hsurj
  obtain ⟨y, hy⟩ : ∃ y, thick R I 0 y = X.hom (p.left c₁) := by
    have : X.hom (p.left c₁) ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk (I ^ (0 + 1)))) := by
      rw [_root_.range_comap_of_surjective _ _ hsurj, Ideal.mk_ker]
      exact (PrimeSpectrum.mem_zeroLocus _ _).2 (by simpa using hI)
    exact this
  have hC : ∀ c, C.hom c = X.hom (p.left c) := fun c => by
    rw [← Over.w p]; rfl
  obtain ⟨z₁, hz₁, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := C.hom) (g := thick R I 0)
    c₁ y (by rw [hC, hy])
  obtain ⟨z₂, hz₂, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := C.hom) (g := thick R I 0)
    c₂ y (by rw [hC, hy, h12])
  let P0 := ((Over.pullback (thick R I 0)).map p).left
  have hfst : ∀ z, pullback.fst X.hom (thick R I 0) (P0 z) =
      p.left (pullback.fst C.hom (thick R I 0) z) := fun z => by
    have := over_pullback_fst (thick R I 0) p
    exact congrArg (fun f => f z) this
  have hinj1 : Function.Injective (pullback.fst X.hom (thick R I 0)) :=
    (pullback.fst X.hom (thick R I 0)).isEmbedding.injective
  have hinj2 : Function.Injective P0 := P0.isEmbedding.injective
  have : z₁ = z₂ := hinj2 (hinj1 (by rw [hfst, hfst, hz₁, hz₂, h12]))
  rw [← hz₁, ← hz₂, this]

theorem isIso_restrict_thick {S T : Scheme.{0}} (t : T ⟶ S) (X C : Over S) (p : C ⟶ X)
    (W : X.left.Opens) (g : Over.mk ((p.left ⁻¹ᵁ W).ι ≫ C.hom) ⟶ Over.mk (W.ι ≫ X.hom))
    (hg : g.left = p.left ∣_ W) (h : IsIso ((Over.pullback t).map p).left) :
    IsIso ((Over.pullback t).map g).left := by
  let a : Over.mk ((p.left ⁻¹ᵁ W).ι ≫ C.hom) ⟶ C := Over.homMk (p.left ⁻¹ᵁ W).ι rfl
  let b : Over.mk (W.ι ≫ X.hom) ⟶ X := Over.homMk W.ι rfl
  have hcomm : a ≫ p = g ≫ b := by
    ext1
    change (p.left ⁻¹ᵁ W).ι ≫ p.left = g.left ≫ W.ι
    rw [hg, morphismRestrict_ι]
  have hsq : IsPullback a g p b :=
    IsPullback.of_map (Over.forget S) hcomm (by
      have h1 := (isPullback_morphismRestrict p.left W).flip
      rw [← hg] at h1
      exact h1)
  have hsq' := hsq.map (Over.pullback t)
  haveI : IsIso ((Over.forget T).map ((Over.pullback t).map p)) := h
  haveI : IsIso ((Over.pullback t).map p) := isIso_of_reflects_iso _ (Over.forget _)
  haveI : IsIso ((Over.pullback t).map g) := hsq'.isIso_snd_of_isIso
  exact inferInstanceAs (IsIso ((Over.forget T).map ((Over.pullback t).map g)))

theorem exists_nbhd {R : Type} [CommRing R] [IsNoetherianRing R] (I : Ideal R)
    (X C : Over (Spec (CommRingCat.of R))) (p : C ⟶ X) [IsProper X.hom] [IsProper p.left]
    (h : ∀ e, IsIso ((Over.pullback (thick R I e)).map p).left) (x : X.left)
    (hx : I ≤ (X.hom x).asIdeal) : ∃ W : X.left.Opens, x ∈ W ∧ IsIso (p.left ∣_ W) := by
  obtain ⟨V', hV', hsub⟩ : ∃ V' : C.left.Opens, IsAffineOpen V' ∧ ∀ c, p.left c = x → c ∈ V' := by
    by_cases hc : ∃ c, p.left c = x
    · obtain ⟨c, rfl⟩ := hc
      obtain ⟨V', hV', hcV, -⟩ := exists_isAffineOpen_mem_and_subset (X := C.left) (x := c) (U := ⊤) trivial
      refine ⟨V', hV', fun c' hc' => ?_⟩
      rwa [fibre_subsingleton I X C p (h 0) c' c hc' (by rw [hc']; exact hx)]
    · exact ⟨⊥, isAffineOpen_bot _, fun c hc' => (hc ⟨c, hc'⟩).elim⟩
  have hcl : IsClosed (p.left '' (V' : Set C.left)ᶜ) :=
    p.left.isClosedMap _ V'.isOpen.isClosed_compl
  have hxO : x ∈ (p.left '' (V' : Set C.left)ᶜ)ᶜ := by
    rintro ⟨c, hc, rfl⟩
    exact hc (hsub c rfl)
  let O : X.left.Opens := ⟨_, hcl.isOpen_compl⟩
  obtain ⟨W, hW, hxW, hWO⟩ := exists_isAffineOpen_mem_and_subset (X := X.left) (x := x) (U := O) hxO
  have hle : p.left ⁻¹ᵁ W ≤ V' := by
    intro c hc
    by_contra hcV
    exact hWO hc ⟨c, hcV, rfl⟩
  haveI : IsAffine V'.toScheme := hV'
  haveI : IsAffineHom ((V'.ι ≫ p.left) ≫ X.hom) := isAffineHom_of_isAffine _
  haveI : IsAffineHom (V'.ι ≫ p.left) := IsAffineHom.of_comp _ X.hom
  have hWa : IsAffineOpen (p.left ⁻¹ᵁ W) := by
    have h1 := (hW.preimage (V'.ι ≫ p.left)).image_of_isOpenImmersion V'.ι
    have h2 : V'.ι ''ᵁ ((V'.ι ≫ p.left) ⁻¹ᵁ W) = p.left ⁻¹ᵁ W := by
      change V'.ι ''ᵁ (V'.ι ⁻¹ᵁ (p.left ⁻¹ᵁ W)) = p.left ⁻¹ᵁ W
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
      exact inf_eq_right.2 hle
    rwa [h2] at h1
  haveI : IsAffine W.toScheme := hW
  haveI : IsAffine (p.left ⁻¹ᵁ W).toScheme := hWa
  let g : Over.mk ((p.left ⁻¹ᵁ W).ι ≫ C.hom) ⟶ Over.mk (W.ι ≫ X.hom) :=
    Over.homMk (p.left ∣_ W) (by
      change (p.left ∣_ W) ≫ W.ι ≫ X.hom = (p.left ⁻¹ᵁ W).ι ≫ C.hom
      rw [← Category.assoc, morphismRestrict_ι, Category.assoc, Over.w p])
  haveI : IsProper g.left := inferInstanceAs (IsProper (p.left ∣_ W))
  haveI : LocallyOfFiniteType (Over.mk (W.ι ≫ X.hom)).hom :=
    inferInstanceAs (LocallyOfFiniteType (W.ι ≫ X.hom))
  haveI : IsAffine (Over.mk (W.ι ≫ X.hom)).left := inferInstanceAs (IsAffine W.toScheme)
  haveI : IsAffine (Over.mk ((p.left ⁻¹ᵁ W).ι ≫ C.hom)).left :=
    inferInstanceAs (IsAffine (p.left ⁻¹ᵁ W).toScheme)
  obtain ⟨s, hs, hiso⟩ := affine_case I _ _ g
    (fun e => isIso_restrict_thick (thick R I e) X C p W g rfl (h e))
    (⟨x, hxW⟩ : W.toScheme) hx
  refine ⟨W.ι ''ᵁ (W.toScheme.basicOpen s), ⟨_, hs, rfl⟩, ?_⟩
  exact ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
    (morphismRestrictRestrict p.left W _)).1 hiso

theorem isoOfThick : IsoOfThick := by
  intro R _ _ I hI X C p hX hp hiso
  haveI := hI
  let Ω : X.left.Opens := ⨆ W : {W : X.left.Opens // IsIso (p.left ∣_ W)}, W.1
  have hΩ : Ω = ⊤ := by
    by_contra hne
    obtain ⟨x₀, hx₀⟩ : ∃ x, x ∉ Ω := by
      by_contra hall
      push_neg at hall
      exact hne (eq_top_iff.2 fun x _ => hall x)
    have hT : IsClosed (X.hom '' (Ω : Set X.left)ᶜ) :=
      X.hom.isClosedMap _ Ω.isOpen.isClosed_compl
    obtain ⟨m, hmT, hm⟩ : ∃ m : PrimeSpectrum R,
        m ∈ (X.hom '' (Ω : Set X.left)ᶜ : Set (PrimeSpectrum R)) ∧ m.asIdeal.IsMaximal := by
      obtain ⟨J, hJ⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal _).1 hT
      have hy : X.hom x₀ ∈ PrimeSpectrum.zeroLocus (J : Set R) := by
        rw [← hJ]; exact ⟨x₀, hx₀, rfl⟩
      have hJtop : J ≠ ⊤ := fun h => (X.hom x₀).isPrime.ne_top
        (top_le_iff.mp (h ▸ (PrimeSpectrum.mem_zeroLocus _ _).1 hy))
      obtain ⟨M, hM, hJM⟩ := Ideal.exists_le_maximal J hJtop
      refine ⟨⟨M, hM.isPrime⟩, ?_, hM⟩
      exact (Set.ext_iff.1 hJ _).2 hJM
    obtain ⟨x, hxZ, rfl⟩ := hmT
    have hIx : I ≤ (X.hom x).asIdeal :=
      (IsAdicComplete.le_jacobson_bot I).trans (sInf_le ⟨bot_le, hm⟩)
    obtain ⟨W, hxW, hW⟩ := exists_nbhd I X C p hiso x hIx
    exact hxZ (TopologicalSpace.Opens.mem_iSup.2 ⟨⟨W, hW⟩, hxW⟩)
  have hf : IsIso p.left :=
    IsZariskiLocalAtTarget.of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme)
      (fun W : {W : X.left.Opens // IsIso (p.left ∣_ W)} => W.1) hΩ (fun W => W.2)
  haveI : IsIso ((Over.forget _).map p) := hf
  exact isIso_of_reflects_iso p (Over.forget _)

end GlobalTheory.CompanionTheory.Formal.IsoThick
