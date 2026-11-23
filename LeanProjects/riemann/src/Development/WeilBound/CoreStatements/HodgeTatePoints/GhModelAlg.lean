import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LieModel

noncomputable section

namespace PositivityTheory.HtPt.Gh

open Module NumberField GlobalTheory.CompanionTheory.Ar

theorem mem_eig {R V O : Type} [CommRing R] [AddCommGroup V] [Module R V] [CommRing O]
    {ρ : O →+* Module.End R V} {χ : O →+* R} {x : V} :
    x ∈ GlobalTheory.CompanionTheory.Ar.eigSp ρ χ ↔ ∀ a, ρ a x = χ a • x := by
  simp [GlobalTheory.CompanionTheory.Ar.eigSp, Submodule.mem_iInf, sub_eq_zero]

theorem exists_lift {E : Type} [Field E] [NumberField E] {K : Type} [Field K] [CharZero K] (χ : 𝓞 E →+* K) :
    ∃ σ : E →+* K, ∀ a : 𝓞 E, σ (a : E) = χ a := by
  have hinj : Function.Injective χ := by
    rw [RingHom.injective_iff_ker_eq_bot]
    refine Ideal.eq_bot_of_comap_eq_bot (R := ℤ) ?_
    rw [eq_bot_iff]
    intro n hn
    have : (n : K) = 0 := by simpa using hn
    exact_mod_cast this
  exact ⟨IsFractionRing.lift hinj, fun a => IsFractionRing.lift_algebraMap hinj a⟩

theorem exists_int_proj (E : Type) [Field E] [NumberField E] :
    ∃ (m : ℤ) (a : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → 𝓞 E), m ≠ 0 ∧
      ∀ (K V : Type) [Field K] [CharZero K] [AddCommGroup V] [Module K V] (ρ : 𝓞 E →+* Module.End K V)
        (χ : 𝓞 E →+* K),
        (∀ x, ∑ k, χ (a k) • ρ (RingOfIntegers.basis E k) x ∈ GlobalTheory.CompanionTheory.Ar.eigSp ρ χ) ∧
        ∀ x ∈ GlobalTheory.CompanionTheory.Ar.eigSp ρ χ, ∑ k, χ (a k) • ρ (RingOfIntegers.basis E k) x = (m : K) • x := by
  obtain ⟨m, hm⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ)
    (fun q : Module.Free.ChooseBasisIndex ℤ (𝓞 E) × Module.Free.ChooseBasisIndex ℤ (𝓞 E) =>
      (integralBasis E).repr (HT.dualInt E q.1) q.2)
  choose n hn using hm
  have ha : ∀ k, ((∑ j, n (k, j) • RingOfIntegers.basis E j : 𝓞 E) : E) = ((m : ℤ) : E) * HT.dualInt E k := by
    intro k
    conv_rhs => rw [← (integralBasis E).sum_repr (HT.dualInt E k)]
    rw [RingOfIntegers.coe_eq_algebraMap, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have h := hn (k, j)
    simp only [eq_intCast, zsmul_eq_mul] at h
    rw [map_zsmul, ← integralBasis_apply, ← Int.cast_smul_eq_zsmul ℚ, h, mul_smul, Int.cast_smul_eq_zsmul,
      zsmul_eq_mul]
  refine ⟨m, fun k => ∑ j, n (k, j) • RingOfIntegers.basis E j, nonZeroDivisors.coe_ne_zero m, ?_⟩
  intro K V _ _ _ _ ρ χ
  obtain ⟨σ, hσ⟩ := exists_lift χ
  have he : ∀ x, x ∈ GlobalTheory.CompanionTheory.Ar.eigSp ρ χ ↔ x ∈ HT.eigSp ρ σ := fun x => by
    rw [mem_eig, HT.LatBasic.mem_eigSp]; simp only [hσ]
  have hT : ∀ x, ∑ k, χ (∑ j, n (k, j) • RingOfIntegers.basis E j) • ρ (RingOfIntegers.basis E k) x =
      ((m : ℤ) : K) • HT.eigProj ρ σ x := fun x => by
    simp only [HT.eigProj, LinearMap.sum_apply, LinearMap.smul_apply, Finset.smul_sum, smul_smul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← hσ, ha, map_mul, map_intCast]
  refine ⟨fun x => ?_, fun x hx => ?_⟩
  · rw [hT]
    exact Submodule.smul_mem _ _ ((he _).2 (HT.LatBasic.eigProj_mem ρ σ x))
  · rw [hT, HT.LatBasic.eigProj_of_mem ((he _).1 hx)]

theorem exists_predual {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] {r : ℕ}
    (b : Fin r → Module.Dual K V) (hli : LinearIndependent K b) (hsp : Submodule.span K (Set.range b) = ⊤) :
    ∃ f : Fin r → V, (∀ i j, b i (f j) = if i = j then 1 else 0) ∧ ∀ e, e = ∑ j, b j e • f j := by
  let B : Basis (Fin r) K (Module.Dual K V) := Basis.mk hli hsp.ge
  let F := B.dualBasis.map (Module.evalEquiv K V).symm
  refine ⟨F, fun i j => ?_, fun e => ?_⟩
  · have : b i = B i := by simp [B]
    rw [this]
    simp only [F, Basis.map_apply, Module.apply_evalEquiv_symm_apply, Basis.dualBasis_apply_self]
  · conv_lhs => rw [← F.sum_repr e]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    simp [F, B, Basis.dualBasis_repr]

theorem alg_main {E : Type} [Field E] [NumberField E] {Ω C R A A' : Type} [Field Ω] [Field C] [CharZero C]
    [CommRing R] [Algebra R C] [CommRing A] [CommRing A'] {Li EC : Type} [AddCommGroup Li] [Module Ω Li]
    [AddCommGroup EC] [Module C EC] [Module R EC] [IsScalarTower R C EC]
    (k : A →+* A') (g : A' →+* Ω) (hg : Function.Injective g) (ψ : A' →+* C) (φ : A →+* R)
    (hψ : ∀ a, ψ (k a) = algebraMap R C (φ a)) {n : ℕ} (β : Basis (Fin n) Ω Li) (γ : Basis (Fin n) C EC)
    (Val : Li → EC → Prop)
    (hVal : ∀ e x, Val e x ↔ ∃ c : Fin n → A', e = ∑ i, g (c i) • β i ∧ x = ∑ i, ψ (c i) • γ i)
    (ρ : 𝓞 E →+* Module.End Ω Li) (ρC : 𝓞 E →+* Module.End C EC) (χ : 𝓞 E →+* Ω) (σ : 𝓞 E →+* R)
    (hχ : ∀ a, ∃ s, g (k s) = χ a ∧ φ s = σ a) (hact : ∀ a e x, Val e x → Val (ρ a e) (ρC a x))
    (L W : Set Li) {r : ℕ} (w : Fin r → Module.Dual Ω Li) (f : Fin r → Li) (hβ : ∀ i, β i ∈ L)
    (hwL : ∀ j, ∀ e ∈ L, ∃ a, g (k a) = w j e) (hf : ∀ j, f j ∈ W)
    (hW : ∀ e ∈ W, e ∈ GlobalTheory.CompanionTheory.Ar.eigSp ρ χ ∧ ∀ j, ∃ a, g (k a) = w j e)
    (hexp : ∀ e ∈ GlobalTheory.CompanionTheory.Ar.eigSp ρ χ, e = ∑ j, w j e • f j) (hfv : ∀ j, ∃ x, Val (f j) x)
    (κ : Ω) (κz : R) (hκ : ∃ s, g (k s) = κ ∧ φ s = κz) (hκW : ∀ e ∈ W, κ • e ∈ L) :
    Submodule.span R {x | ∃ e ∈ L, Val e x} ⊓ (GlobalTheory.CompanionTheory.Ar.eigSp ρC ((algebraMap R C).comp σ)).restrictScalars R ≤
        Submodule.span R {x | ∃ e ∈ W, Val e x} ∧
      (∀ x ∈ Submodule.span R {x | ∃ e ∈ W, Val e x}, κz • x ∈ Submodule.span R {x | ∃ e ∈ L, Val e x} ⊓
        (GlobalTheory.CompanionTheory.Ar.eigSp ρC ((algebraMap R C).comp σ)).restrictScalars R) ∧
      (Submodule.span R {x | ∃ e ∈ W, Val e x}).FG := by
  classical
  haveI : CharZero A' := ψ.charZero
  haveI : CharZero Ω := charZero_of_injective_ringHom hg
  have vuniq : ∀ e x x', Val e x → Val e x' → x = x' := by
    intro e x x' h h'
    obtain ⟨c, h1, rfl⟩ := (hVal _ _).1 h
    obtain ⟨c', h2, rfl⟩ := (hVal _ _).1 h'
    have : c = c' := funext fun i => hg (by
      have := congrArg (fun y => β.repr y i) (h1.symm.trans h2)
      simpa [Finsupp.single_apply] using this)
    rw [this]
  have vzero : Val 0 0 := (hVal _ _).2 ⟨0, by simp, by simp⟩
  have vadd : ∀ e x e' x', Val e x → Val e' x' → Val (e + e') (x + x') := by
    intro e x e' x' h h'
    obtain ⟨c, rfl, rfl⟩ := (hVal _ _).1 h
    obtain ⟨c', rfl, rfl⟩ := (hVal _ _).1 h'
    exact (hVal _ _).2 ⟨c + c', by simp [add_smul, Finset.sum_add_distrib],
      by simp [add_smul, Finset.sum_add_distrib]⟩
  have vsmul : ∀ (a : A') e x, Val e x → Val (g a • e) (ψ a • x) := by
    intro a e x h
    obtain ⟨c, rfl, rfl⟩ := (hVal _ _).1 h
    exact (hVal _ _).2 ⟨fun i => a * c i, by simp [mul_smul, Finset.smul_sum], by simp [mul_smul, Finset.smul_sum]⟩
  have vsum : ∀ {I : Type} (s : Finset I) (e : I → Li) (x : I → EC), (∀ i, Val (e i) (x i)) →
      Val (∑ i ∈ s, e i) (∑ i ∈ s, x i) := by
    intro I s e x h
    induction s using Finset.induction_on with
    | empty => simpa using vzero
    | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi]; exact vadd _ _ _ _ (h i) ih
  have vbas : ∀ i, Val (β i) (γ i) := fun i => (hVal _ _).2 ⟨Pi.single i 1, by
    rw [Finset.sum_eq_single i] <;> simp +contextual, by rw [Finset.sum_eq_single i] <;> simp +contextual⟩
  have vchi : ∀ a e x, Val e x → Val (χ a • e) (((algebraMap R C).comp σ) a • x) := by
    intro a e x h
    obtain ⟨s, h1, h2⟩ := hχ a
    have := vsmul (k s) e x h
    rwa [h1, hψ, h2] at this
  have veig : ∀ e x, Val e x → e ∈ GlobalTheory.CompanionTheory.Ar.eigSp ρ χ →
      x ∈ GlobalTheory.CompanionTheory.Ar.eigSp ρC ((algebraMap R C).comp σ) := by
    intro e x h he
    refine mem_eig.2 fun a => vuniq _ _ _ (hact a e x h) ?_
    rw [mem_eig.1 he]
    exact vchi a e x h
  choose t ht using fun j i => hwL j (β i) (hβ i)
  choose xf hxf using hfv
  let wC : Fin r → Module.Dual C EC := fun j => γ.constr C fun i => ψ (k (t j i))
  have hwC : ∀ j e x, Val e x → ∃ c, g c = w j e ∧ ψ c = wC j x := by
    intro j e x h
    obtain ⟨c, rfl, rfl⟩ := (hVal _ _).1 h
    exact ⟨∑ i, c i * k (t j i), by simp [ht], by simp [wC]⟩
  have hwR : ∀ j e x, Val e x → (∃ a, g (k a) = w j e) → ∃ o, algebraMap R C o = wC j x := by
    rintro j e x h ⟨a, ha⟩
    obtain ⟨c, h1, h2⟩ := hwC j e x h
    exact ⟨φ a, by rw [← hψ, hg (ha.trans h1.symm), h2]⟩
  have hP : ∀ e x, Val e x → e ∈ GlobalTheory.CompanionTheory.Ar.eigSp ρ χ → x = ∑ j, wC j x • xf j := by
    intro e x h he
    choose c h1 h2 using fun j => hwC j e x h
    refine vuniq _ _ _ h ?_
    have := vsum Finset.univ _ _ fun j => vsmul (c j) _ _ (hxf j)
    simp only [h1, h2] at this
    rwa [← hexp e he] at this
  have hPC : ∀ x ∈ GlobalTheory.CompanionTheory.Ar.eigSp ρC ((algebraMap R C).comp σ), x = ∑ j, wC j x • xf j := by
    obtain ⟨m, a, hm, hT⟩ := exists_int_proj E
    let T : EC →ₗ[C] EC := ∑ q, ((algebraMap R C).comp σ) (a q) • ρC (RingOfIntegers.basis E q)
    have hTa : ∀ x, T x = ∑ q, ((algebraMap R C).comp σ) (a q) • ρC (RingOfIntegers.basis E q) x := fun x => by
      simp only [T, LinearMap.sum_apply, LinearMap.smul_apply]
    let P : EC →ₗ[C] EC := ∑ j, (wC j).smulRight (xf j)
    have hPa : ∀ x, P x = ∑ j, wC j x • xf j := fun x => by
      simp only [P, LinearMap.sum_apply, LinearMap.smulRight_apply]
    have hPT : P ∘ₗ T = T := γ.ext fun i => by
      rw [LinearMap.comp_apply, hPa]
      refine (hP _ _ ?_ ((hT Ω Li ρ χ).1 (β i))).symm
      rw [hTa]
      exact vsum _ _ _ fun q => vchi _ _ _ (hact _ _ _ (vbas i))
    intro x hx
    have h1 := LinearMap.congr_fun hPT x
    rw [LinearMap.comp_apply, hTa, (hT C EC ρC _).2 x hx, map_smul] at h1
    rw [← hPa]
    exact (smul_right_injective EC (Int.cast_ne_zero.2 hm) h1).symm
  have hcomb : ∀ x, x = ∑ j, wC j x • xf j → (∀ j, ∃ o, algebraMap R C o = wC j x) →
      x ∈ Submodule.span R (Set.range xf) := by
    intro x h1 h2
    choose o ho using h2
    rw [h1]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [← ho, algebraMap_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have hWz : Submodule.span R {x | ∃ e ∈ W, Val e x} = Submodule.span R (Set.range xf) := by
    refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono ?_)
    · rintro x ⟨e, he, h⟩
      exact hcomb x (hP e x h (hW e he).1) fun j => hwR j e x h ((hW e he).2 j)
    · rintro _ ⟨j, rfl⟩
      exact ⟨f j, hf j, hxf j⟩
  refine ⟨?_, ?_, ?_⟩
  · rintro x ⟨hx1, hx2⟩
    rw [hWz]
    refine hcomb x (hPC x hx2) fun j => ?_
    clear hx2
    induction hx1 using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨e, he, h⟩ := hx
      exact hwR j e x h (hwL j e he)
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨o, ho⟩ := hx
      obtain ⟨o', ho'⟩ := hy
      exact ⟨o + o', by rw [map_add, map_add, ho, ho']⟩
    | smul c x _ hx =>
      obtain ⟨o, ho⟩ := hx
      exact ⟨c * o, by rw [map_mul, ho, ← algebraMap_smul C c x, map_smul, smul_eq_mul]⟩
  · intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨e, he, h⟩ := hx
      obtain ⟨s, h1, h2⟩ := hκ
      have := vsmul (k s) e x h
      rw [h1, hψ, h2, algebraMap_smul] at this
      exact ⟨Submodule.subset_span ⟨_, hκW e he, this⟩,
        Submodule.smul_mem ((GlobalTheory.CompanionTheory.Ar.eigSp ρC ((algebraMap R C).comp σ)).restrictScalars R) κz
          (veig e x h (hW e he).1)⟩
    | zero => simp
    | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ c hx
  · rw [hWz]
    exact Submodule.fg_span (Set.finite_range _)

end PositivityTheory.HtPt.Gh
