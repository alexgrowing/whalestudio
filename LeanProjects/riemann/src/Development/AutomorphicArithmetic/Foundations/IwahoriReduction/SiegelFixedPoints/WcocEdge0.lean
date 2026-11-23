import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.SiegelFixedPoints.IsThBIff
import Development.AbelianVarietyTheory.Definitions.Foundations.IsLamOfLSmulIff
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.SiegelFixedPoints.ConstInt

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.Glue GlobalTheory.KummerEisensteinGalois UpperTheory.Kd.L

section Gen
open GlobalTheory.KEdge GlobalTheory.NeedB GlobalTheory.K4.TopW

variable {F K Ω : Type*} [Field F] [Field K] [Field Ω] [Algebra F K] [Algebra F Ω] [Algebra K Ω] [IsScalarTower F K Ω]
  {N : ℕ} {ζ : Ω} {x y : (Ω ≃ₐ[F] Ω) →* Multiplicative (ZMod N)} {η : (Ω ≃ₐ[F] Ω) → ZMod N}

private theorem wcoc_conj {a h : Ω ≃ₐ[F] Ω} (ha : ∀ z : K, ∃ z' : K, a (algebraMap K Ω z) = algebraMap K Ω z')
    (hh : h ∈ geo F K Ω) : a⁻¹ * h * a⁻¹⁻¹ ∈ geo F K Ω := by
  rw [mem_geo] at hh ⊢
  intro z
  obtain ⟨z', hz'⟩ := ha z
  rw [inv_inv, AlgEquiv.mul_apply, AlgEquiv.mul_apply, hz', hh z', ← hz']
  exact AlgEquiv.symm_apply_apply a _

private theorem wcoc_edge0 (hC : CobOn (geo F K Ω) x y η) {g h : Ω ≃ₐ[F] Ω} (hg : g ∈ geo F K Ω) (hh : h ∈ geo F K Ω) :
    edge x y η g h = 0 := by
  have h1 := hC g hg h hh
  have h2 := hC (g * h) ((geo F K Ω).mul_mem hg hh) g⁻¹ ((geo F K Ω).inv_mem hg)
  have h3 := hC g hg g⁻¹ ((geo F K Ω).inv_mem hg)
  have h4 := hC 1 (geo F K Ω).one_mem 1 (geo F K Ω).one_mem
  simp only [map_mul, map_inv, toAdd_mul, toAdd_inv, map_one, toAdd_one, mul_inv_cancel, mul_one]
    at h1 h2 h3 h4
  unfold edge
  linear_combination h1 + h2 - h3 - h4

private theorem wcoc_gen [NeZero N] (hζ : IsPrimitiveRoot ζ N) (hC : CobOn (geo F K Ω) x y η) {a b c : Ω ≃ₐ[F] Ω}
    (ha : ∀ z : K, ∃ z' : K, a (algebraMap K Ω z) = algebraMap K Ω z')
    (hb : ∀ z : K, ∃ z' : K, b (algebraMap K Ω z) = algebraMap K Ω z') (haζ : a ζ = ζ)
    (hc : c⁻¹ * (a * b) ∈ geo F K Ω) {w v v' : K} (hw : IsTopW ζ x y η a⁻¹ w) (hv : IsTopW ζ x y η b⁻¹ v)
    (hv' : a (algebraMap K Ω v) = algebraMap K Ω v') : IsTopW ζ x y η c⁻¹ (w * v') := by
  obtain ⟨hw0, θw, hθw, hkw⟩ := hw
  obtain ⟨hv0, θv, hθv, hkv⟩ := hv
  have hab : ∀ z : K, ∃ z' : K, (a * b) (algebraMap K Ω z) = algebraMap K Ω z' := by
    intro z
    obtain ⟨z1, h1⟩ := hb z
    obtain ⟨z2, h2⟩ := ha z1
    exact ⟨z2, by rw [AlgEquiv.mul_apply, h1, h2]⟩
  have hθw0 : θw ≠ 0 := by
    rintro rfl
    rw [zero_pow (NeZero.ne N)] at hθw
    exact hw0 ((map_eq_zero _).1 hθw.symm)
  have hθv0 : θv ≠ 0 := by
    rintro rfl
    rw [zero_pow (NeZero.ne N)] at hθv
    exact hv0 ((map_eq_zero _).1 hθv.symm)
  have haθv0 : a θv ≠ 0 := fun h0 => hθv0 (a.injective (h0.trans (map_zero a).symm))
  have hv'0 : v' ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hv'
    apply hv0
    exact (map_eq_zero _).1 (a.injective (hv'.trans (map_zero a).symm))
  refine ⟨mul_ne_zero hw0 hv'0, θw * a θv, ?_, ?_⟩
  · rw [mul_pow, ← map_pow, hθw, hθv, hv', map_mul]
  · intro g hg
    have hg' := wcoc_conj ha hg
    have e1 := apply_eq_kum hζ hw0 hθw hg
    rw [hkw g hg] at e1
    have e2 := apply_eq_kum hζ hv0 hθv hg'
    rw [hkv _ hg'] at e2
    have e3 : g (a θv) = ζ ^ (edge x y η b⁻¹ (a⁻¹ * g * a⁻¹⁻¹)).val * a θv := by
      have h5 : g (a θv) = a ((a⁻¹ * g * a⁻¹⁻¹) θv) := by
        rw [inv_inv, AlgEquiv.mul_apply, AlgEquiv.mul_apply]
        exact (AlgEquiv.apply_symm_apply a _).symm
      rw [h5, e2, map_mul, map_pow, haζ]
    have hk : c⁻¹ = (c⁻¹ * (a * b)) * (b⁻¹ * a⁻¹) := by group
    have hmem : (b⁻¹ * a⁻¹) * g * (b⁻¹ * a⁻¹)⁻¹ ∈ geo F K Ω := by
      have h6 := wcoc_conj hab hg
      rwa [mul_inv_rev] at h6
    have key : edge x y η c⁻¹ g = edge x y η b⁻¹ (a⁻¹ * g * a⁻¹⁻¹) + edge x y η a⁻¹ g := by
      rw [hk, edge_mul_conj x y η (c⁻¹ * (a * b)) (b⁻¹ * a⁻¹) g, wcoc_edge0 hC hc hmem, zero_add,
        edge_mul_conj x y η b⁻¹ a⁻¹ g]
    apply kum_eq_of hζ (mul_ne_zero hθw0 haθv0)
    rw [map_mul, e1, e3, key, pow_val_add hζ]
    ring

end Gen

section Top
attribute [local instance] algMdl

private theorem wcoc_top {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) {M l n : ℕ}
    (hl : l ≠ 0) (hM0 : M ≠ 0) (hM : l ^ n ∣ M) {x y : topGal X M →* Multiplicative (ZMod (l ^ n))}
    {η : topGal X M → ZMod (l ^ n)} (hη : IsTopEta X M x y η)
    (hex : ∀ s : topGal X M, ∃ w : topL X M, IsTopW (K := topL X M) (topZeta X M l n) x y η s w)
    {σ τ : Ω ≃ₐ[ℚ] Ω} (hσ : σ ∈ fixMu Ω M) (hτ : τ ∈ fixMu Ω M) :
    ∃ u ∈ topL X M, u ≠ 0 ∧
      ((topW (K := topL X M) (topZeta X M l n) x y η (topLift X M (σ * τ))⁻¹ : topL X M) : X.K) =
        ((topW (K := topL X M) (topZeta X M l n) x y η (topLift X M σ)⁻¹ : topL X M) : X.K) *
          X.gal σ ((topW (K := topL X M) (topZeta X M l n) x y η (topLift X M τ)⁻¹ : topL X M) : X.K) * u ^ l ^ n := by
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero n hl⟩
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI : CharZero X.K := charZero_of_injective_algebraMap (algebraMap Ω X.K).injective
  haveI : CharZero (topL X M) := inferInstance
  have hζ := isPrimitiveRoot_topZeta X M hl n
  have hσL := isTopLift_topLift X hM0 hσ
  have hτL := isTopLift_topLift X hM0 hτ
  have hστL := isTopLift_topLift X hM0 ((fixMu Ω M).mul_mem hσ hτ)
  have hlift : ∀ {s : Ω ≃ₐ[ℚ] Ω} {φ : topGal X M}, IsTopLift X M s φ → ∀ z : topL X M,
      ∃ z' : topL X M, φ (algebraMap (topL X M) (topBar X M) z) = algebraMap (topL X M) (topBar X M) z' := by
    intro s φ h z
    obtain ⟨z', -, hz'⟩ := h z
    exact ⟨z', hz'⟩
  have hprod : IsTopLift X M (σ * τ) (topLift X M σ * topLift X M τ) := by
    intro f
    obtain ⟨f1, hf1, hb1⟩ := hτL f
    obtain ⟨f2, hf2, ha2⟩ := hσL f1
    refine ⟨f2, ?_, ?_⟩
    · rw [hf2, hf1, gal_mul_apply]
    · rw [AlgEquiv.mul_apply, hb1, ha2]
  have hc := IsTopLift.inv_mul_mem_geo hστL hprod
  obtain ⟨v', hv'1, hv'2⟩ := hσL (topW (K := topL X M) (topZeta X M l n) x y η (topLift X M τ)⁻¹)
  have hgen := wcoc_gen hζ hη.1 (hlift hσL) (hlift hτL) (topGal_topZeta X hl hM _) hc
    (TopW.isTopW_topW_of_exists (hex _)) (TopW.isTopW_topW_of_exists (hex _)) hv'2
  obtain ⟨e, he0, he⟩ := TopW.unique hζ (TopW.isTopW_topW_of_exists (hex (topLift X M (σ * τ))⁻¹)) hgen
  refine ⟨(e : X.K), e.2, by exact_mod_cast he0, ?_⟩
  rw [he, ← hv'1]
  push_cast
  ring

end Top

attribute [local instance] algMdl in
theorem UpperTheory.Kd.L.wcoc :
    ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] [CharZero Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (N : ℕ) [NeZero N] (c d : ℕ) (gm : (ZMod l)ˣ → SL(2, ℤ)), Par l N c d gm → ∀ (x : ZMod N) (m n : ℕ), 1 ≤ m → (∀ σ, wkMu X l n m N x c d σ ∈ topL X (topMu l n m N) ∧ wkMu X l n m N x c d σ ≠ 0) ∧ ∀ σ ∈ fixMu Ω (topMu l n m N), ∀ τ ∈ fixMu Ω (topMu l n m N), ∃ u ∈ topL X (topMu l n m N), u ≠ 0 ∧ wkMu X l n m N x c d (σ * τ) = wkMu X l n m N x c d σ * X.gal σ (wkMu X l n m N x c d τ) * u ^ l ^ n := by
  intro Ω _ _ _ _ ε X l _ N _ c d gm hP x m n hm
  obtain ⟨hη, hex⟩ := topex ε X l N c d gm hP x m n hm
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have hl0 : l ≠ 0 := (Fact.out : l.Prime).ne_zero
  have hN0 : N ≠ 0 := NeZero.ne N
  have hM0 : topMu l n m N ≠ 0 := by
    unfold topMu
    positivity
  have hMd : l ^ n ∣ topMu l n m N := by
    unfold topMu
    exact dvd_mul_of_dvd_left (pow_dvd_pow l (Nat.le_add_left n m)) _
  refine ⟨fun σ => ⟨?_, ?_⟩, fun σ hσ τ hτ => ?_⟩
  · simp only [wkMu]
    exact Subtype.mem _
  · simp only [wkMu]
    exact_mod_cast TopW.topW_ne_zero _
  · simp only [wkMu]
    exact wcoc_top X hl0 hM0 hMd hη hex hσ hτ
