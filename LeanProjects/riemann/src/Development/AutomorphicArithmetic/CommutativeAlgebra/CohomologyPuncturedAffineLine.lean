import Mathlib
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.GoodRoot
import Development.EtaleCohomology.EtaleSheaves.StandardChartsLineOne
import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsNearRootOfUnityProductDecomposition
import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsGoodRootOfHenselianSepClosedResidue
import Development.AutomorphicArithmetic.CommutativeAlgebra.IsAffineIsDomainPullbackStandardOpens
import Development.AutomorphicArithmetic.CommutativeAlgebra.ClosedFiberAffineSurjectiveKerMaximalIdeal
import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsFiberPullbackSquareOfOpenImmersions
import Development.AutomorphicArithmetic.CommutativeAlgebra.SchemeRootsOfUnityEqLocallyConstantPowers

noncomputable section
open CategoryTheory Limits AlgebraicGeometry IsLocalRing GlobalTheory.EtC UpperTheory.Et LateralTheory.E.t_E2Cut LateralTheory.E.LineOneCut LateralTheory.E.StandardEtaleChartsMultivariableHensel

private theorem appTop_comp_apply {X Y W : Scheme.{0}} (h : Y ⟶ X) (f : X ⟶ W) (s : Γ(W, ⊤)) :
    h.appTop.hom (f.appTop.hom s) = (h ≫ f).appTop.hom s := by
  rw [Scheme.Hom.comp_appTop]
  rfl

private abbrev st {A : Type} [CommRing A] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of A)) : A →+* Γ(X, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom

private theorem st_comp {A : Type} [CommRing A] {X Y : Scheme.{0}} (h : Y ⟶ X) (f : X ⟶ Spec (CommRingCat.of A)) (a : A) :
    h.appTop.hom (st f a) = st (h ≫ f) a := by
  exact appTop_comp_apply h f _

private theorem goodRoot_map_ringHom {S S₂ : Type} [CommRing S] [CommRing S₂] (φ : S →+* S₂) {q : ℕ} {ζ : S}
    (h : GoodRoot q ζ) : GoodRoot q (φ ζ) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨by rw [← map_pow, h1, map_one], fun a b hab => ?_, fun S' _ ψ x => ?_⟩
  · have := (h2 a b hab).map φ
    simpa only [map_sub, map_pow] using this
  · simpa using h3 S' (ψ.comp φ) x

private theorem notMem_basicOpen_pullback_iff_base_notMem_basicOpen {X Y : Scheme.{0}} (h : Y ⟶ X) (s : Γ(X, ⊤)) (y : Y) :
    y ∉ Y.basicOpen (h.appTop.hom s) ↔ h.base y ∉ X.basicOpen s := by
  rw [← Scheme.preimage_basicOpen_top]
  rfl

private theorem exists_preimage_map_eq_zero_of_mem_mm {A D E F : Type} [CommRing A] [IsLocalRing A] [CommRing D] [Algebra A D]
    [CommRing E] [CommRing F] (B : Subalgebra A D) (φ : E →+* D) (ψ : E →+* F) (σ : A →+* E)
    (hσ : ∀ a, algebraMap A D a = φ (σ a)) (hB : (B : Set D) = Set.range φ)
    (hψ : ∀ a ∈ maximalIdeal A, ψ (σ a) = 0) (y : D) (hy : y ∈ mm B) :
    ∃ y₀, φ y₀ = y ∧ ψ y₀ = 0 := by
  unfold mm at hy
  refine Submodule.smul_induction_on (p := fun y => ∃ y₀, φ y₀ = y ∧ ψ y₀ = 0) hy ?_ ?_
  · intro a ha b hb
    have hb' : b ∈ (B : Set D) := (Subalgebra.mem_toSubmodule B).1 hb
    rw [hB] at hb'
    obtain ⟨b₀, rfl⟩ := hb'
    exact ⟨σ a * b₀, by rw [map_mul, ← hσ, Algebra.smul_def], by rw [map_mul, hψ a ha, zero_mul]⟩
  · rintro x y ⟨x₀, rfl, hx0⟩ ⟨y₀, rfl, hy0⟩
    exact ⟨x₀ + y₀, map_add _ _ _, by rw [map_add, hx0, hy0, add_zero]⟩

private theorem pow_mod_eq_pow_of_pow_eq_one_commutative_algebra {S : Type} [CommRing S] {ζ : S} {q : ℕ} (h : ζ ^ q = 1) (n : ℕ) :
    ζ ^ (n % q) = ζ ^ n := by
  conv_rhs => rw [← Nat.mod_add_div n q, pow_add, pow_mul, h, one_pow, mul_one]

theorem UpperTheory.cohomology_punctured_affine_line : LateralTheory.E.StandardEtaleChartsMultivariableHensel.Heart := by
  unfold LateralTheory.E.StandardEtaleChartsMultivariableHensel.Heart
  intro q A _ _ hSH hq Z U V p hIL hZ ι₁ ι₂ h1 h2 hUa hVa hcov hs g
  obtain ⟨hHens, hsep⟩ := hSH
  letI := hHens
  haveI : NeZero q := ⟨fun h0 => by subst h0; simp at hq⟩
  obtain ⟨ζ, hζ⟩ := UpperTheory.exists_goodRoot_of_henselian_sepClosed_residue A q hq
  by_cases hW : Nonempty ↥(pullback (fibMap p ι₁) (fibMap p ι₂))
  swap
  · refine ⟨0, 0, ?_⟩
    ext x
    exact (hW ⟨x⟩).elim
  haveI := h1
  haveI := h2
  obtain ⟨r, c, hrc, hr1, hr2⟩ := UpperTheory.exists_fiber_pullback_square_of_open_immersions A p ι₁ ι₂
  obtain ⟨hPaff, hP⟩ := UpperTheory.isAffine_isDomain_pullback_standard_opens A p hZ ι₁ ι₂ hs
  haveI := hPaff
  obtain ⟨hWaff, hrsurj, hrker⟩ := UpperTheory.closed_fiber_affine_surjective_ker_maximalIdeal A (pullback.fst ι₁ ι₂ ≫ ι₁ ≫ p) r c hrc
  haveI := hWaff
  obtain ⟨hdom, hinj1, hinj2, T, hTint, hTB, hTC, hB, hC⟩ := hP ⟨r.base hW.some⟩
  obtain ⟨hFUaff, -, hFUker⟩ := UpperTheory.closed_fiber_affine_surjective_ker_maximalIdeal A (ι₁ ≫ p) (pullback.fst (ι₁ ≫ p) (cpt A))
    (pullback.snd _ _) (IsPullback.of_hasPullback _ _)
  obtain ⟨hFVaff, -, hFVker⟩ := UpperTheory.closed_fiber_affine_surjective_ker_maximalIdeal A (ι₂ ≫ p) (pullback.fst (ι₂ ≫ p) (cpt A))
    (pullback.snd _ _) (IsPullback.of_hasPullback _ _)
  haveI := hFUaff
  haveI := hFVaff
  obtain ⟨ζW, hζW⟩ : ∃ z, st (r ≫ pullback.fst ι₁ ι₂ ≫ ι₁ ≫ p) ζ = z := ⟨_, rfl⟩
  have hgW : GoodRoot q ζW := hζW ▸ goodRoot_map_ringHom _ hζ
  have eqU : (pullback.fst (fibMap p ι₁) (fibMap p ι₂)).appTop.hom
      (st (pullback.fst (ι₁ ≫ p) (cpt A) ≫ ι₁ ≫ p) ζ) = ζW := by
    rw [← hζW, st_comp, reassoc_of% hr1]
  have eqV : (pullback.snd (fibMap p ι₁) (fibMap p ι₂)).appTop.hom
      (st (pullback.fst (ι₂ ≫ p) (cpt A) ≫ ι₂ ≫ p) ζ) = ζW := by
    rw [← hζW, st_comp, ← reassoc_of% hr2, pullback.condition_assoc]
  obtain ⟨w, hwq, hw⟩ := (UpperTheory.scheme_roots_of_unity_eq_locallyConstant_powers _ q ζW hgW).1 g
  obtain ⟨w', rfl⟩ := hrsurj w
  letI : Algebra A Γ(pullback ι₁ ι₂, ⊤) := (st (pullback.fst ι₁ ι₂ ≫ ι₁ ≫ p)).toAlgebra
  haveI := hdom
  have toKer : ∀ y, y ∈ mm (⊤ : Subalgebra A Γ(pullback ι₁ ι₂, ⊤)) → r.appTop.hom y = 0 := by
    intro y hy
    unfold mm at hy
    rw [Algebra.top_toSubmodule, Ideal.smul_top_eq_map] at hy
    rw [← RingHom.mem_ker, hrker]
    exact hy
  have hmem : w' ^ q - 1 ∈ mm (⊤ : Subalgebra A Γ(pullback ι₁ ι₂, ⊤)) := by
    have hk : w' ^ q - 1 ∈ RingHom.ker r.appTop.hom := by
      rw [RingHom.mem_ker, map_sub, map_pow, hwq, map_one, sub_self]
    rw [hrker] at hk
    unfold mm
    rw [Algebra.top_toSubmodule, Ideal.smul_top_eq_map]
    exact hk
  obtain ⟨u, hu, v, hv, huq, hvq, hwuv⟩ := UpperTheory.exists_near_root_of_unity_product_decomposition A Γ(pullback ι₁ ι₂, ⊤) T hTint hTB hTC q hq w' hmem
  have hu' : u ∈ (T.B : Set _) := hu
  rw [hB] at hu'
  obtain ⟨u₀, rfl⟩ := hu'
  have hv' : v ∈ (T.C : Set _) := hv
  rw [hC] at hv'
  obtain ⟨v₀, rfl⟩ := hv'
  obtain ⟨e₁, he₁, he₁0⟩ := exists_preimage_map_eq_zero_of_mem_mm T.B (pullback.fst ι₁ ι₂).appTop.hom
    (pullback.fst (ι₁ ≫ p) (cpt A)).appTop.hom (st (ι₁ ≫ p)) (fun a => (st_comp _ _ a).symm) hB
    (fun a ha => by rw [← RingHom.mem_ker, hFUker]; exact Ideal.mem_map_of_mem _ ha) _ huq
  have hcomp2 : ∀ a, algebraMap A Γ(pullback ι₁ ι₂, ⊤) a = (pullback.snd ι₁ ι₂).appTop.hom (st (ι₂ ≫ p) a) := by
    intro a
    rw [st_comp]
    show st (pullback.fst ι₁ ι₂ ≫ ι₁ ≫ p) a = _
    rw [pullback.condition_assoc]
  obtain ⟨e₂, he₂, he₂0⟩ := exists_preimage_map_eq_zero_of_mem_mm T.C (pullback.snd ι₁ ι₂).appTop.hom
    (pullback.fst (ι₂ ≫ p) (cpt A)).appTop.hom (st (ι₂ ≫ p)) hcomp2 hC
    (fun a ha => by rw [← RingHom.mem_ker, hFVker]; exact Ideal.mem_map_of_mem _ ha) _ hvq
  have hu1 : ((pullback.fst (ι₁ ≫ p) (cpt A)).appTop.hom u₀) ^ q = 1 := by
    have : e₁ = u₀ ^ q - 1 := hinj1 (by rw [he₁, map_sub, map_pow, map_one])
    rw [this, map_sub, map_pow, map_one, sub_eq_zero] at he₁0
    exact he₁0
  have hv1 : ((pullback.fst (ι₂ ≫ p) (cpt A)).appTop.hom v₀) ^ q = 1 := by
    have : e₂ = v₀ ^ q - 1 := hinj2 (by rw [he₂, map_sub, map_pow, map_one])
    rw [this, map_sub, map_pow, map_one, sub_eq_zero] at he₂0
    exact he₂0
  obtain ⟨a', ha'⟩ := (UpperTheory.scheme_roots_of_unity_eq_locallyConstant_powers _ q _ (goodRoot_map_ringHom (st (pullback.fst (ι₁ ≫ p) (cpt A) ≫ ι₁ ≫ p)) hζ)).2.1 _ hu1
  obtain ⟨b', hb'⟩ := (UpperTheory.scheme_roots_of_unity_eq_locallyConstant_powers _ q _ (goodRoot_map_ringHom (st (pullback.fst (ι₂ ≫ p) (cpt A) ≫ ι₂ ≫ p)) hζ)).2.1 _ hv1
  refine ⟨a', -b', ?_⟩
  ext x
  have key : g x = a' ((pullback.fst (fibMap p ι₁) (fibMap p ι₂)).base x)
      + b' ((pullback.snd (fibMap p ι₁) (fibMap p ι₂)).base x) := by
    obtain ⟨Px, hPx⟩ := (UpperTheory.scheme_roots_of_unity_eq_locallyConstant_powers _ q ζW hgW).2.2.2 x
    have hx1 : Ideal.Quotient.mk Px (r.appTop.hom w') = Ideal.Quotient.mk Px (ζW ^ (g x).val) :=
      Ideal.Quotient.eq.2 ((hPx _).2 (hw x))
    have hx2 : r.appTop.hom w' = (pullback.fst (fibMap p ι₁) (fibMap p ι₂)).appTop.hom
        ((pullback.fst (ι₁ ≫ p) (cpt A)).appTop.hom u₀) *
        (pullback.snd (fibMap p ι₁) (fibMap p ι₂)).appTop.hom
        ((pullback.fst (ι₂ ≫ p) (cpt A)).appTop.hom v₀) := by
      have h0 := toKer _ hwuv
      rw [map_sub, sub_eq_zero, map_mul] at h0
      rw [h0]
      simp only [appTop_comp_apply, hr1, hr2]
    have hx3 : Ideal.Quotient.mk Px ((pullback.fst (fibMap p ι₁) (fibMap p ι₂)).appTop.hom
        ((pullback.fst (ι₁ ≫ p) (cpt A)).appTop.hom u₀)) =
        Ideal.Quotient.mk Px (ζW ^ (a' ((pullback.fst (fibMap p ι₁) (fibMap p ι₂)).base x)).val) := by
      refine Ideal.Quotient.eq.2 ((hPx _).2 ?_)
      rw [← eqU, ← map_pow, ← map_sub, notMem_basicOpen_pullback_iff_base_notMem_basicOpen]
      exact ha' _
    have hx4 : Ideal.Quotient.mk Px ((pullback.snd (fibMap p ι₁) (fibMap p ι₂)).appTop.hom
        ((pullback.fst (ι₂ ≫ p) (cpt A)).appTop.hom v₀)) =
        Ideal.Quotient.mk Px (ζW ^ (b' ((pullback.snd (fibMap p ι₁) (fibMap p ι₂)).base x)).val) := by
      refine Ideal.Quotient.eq.2 ((hPx _).2 ?_)
      rw [← eqV, ← map_pow, ← map_sub, notMem_basicOpen_pullback_iff_base_notMem_basicOpen]
      exact hb' _
    have hfin : Ideal.Quotient.mk Px (ζW ^ (g x).val) = Ideal.Quotient.mk Px (ζW ^ (a' ((pullback.fst (fibMap p ι₁) (fibMap p ι₂)).base x)
        + b' ((pullback.snd (fibMap p ι₁) (fibMap p ι₂)).base x)).val) := by
      rw [← hx1, hx2, map_mul, hx3, hx4, ← map_mul, ← pow_add, ZMod.val_add, pow_mod_eq_pow_of_pow_eq_one_commutative_algebra hgW.1]
    exact (UpperTheory.scheme_roots_of_unity_eq_locallyConstant_powers _ q ζW hgW).2.2.1 _ _ x ((hPx _).1 (Ideal.Quotient.eq.1 hfin))
  simp only [LocallyConstant.sub_apply, LocallyConstant.neg_apply, LocallyConstant.coe_comap,
    Function.comp_apply, key, sub_neg_eq_add]

end
