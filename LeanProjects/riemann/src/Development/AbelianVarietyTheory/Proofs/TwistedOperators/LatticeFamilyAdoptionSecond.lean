import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.RealTB
import Formalism.LocalToGlobal.IndefiniteReal.RealPins
import Formalism.LocalToGlobal.IndefiniteReal.RealRec
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.NMjT
import Formalism.LocalRingCardinality.DataNChTie
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SemilinearExtensionBases
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FractionalBaseInclusion
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsBasisTensor
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FractionFieldEmbeddingCompat
import Formalism.LocalRingCardinality.DataIdx
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ImportsFurther

namespace GroupAverageFixedPoints
section

noncomputable section

open scoped TensorProduct
open Module

namespace GlobalTheory.CompanionTheory.LatSpan

section Rep

variable {F M Γ : Type} [Field F] [AddCommGroup M] [Module F M] [Group Γ] [Fintype Γ]

def avg (a : Γ →* Module.End F M) (P : Subgroup Γ) [Fintype P] (t : P →* Fˣ) : Module.End F M :=
  (Fintype.card P : F)⁻¹ • ∑ u : P, (((t u)⁻¹ : Fˣ) : F) • a (u : Γ)

def grp (a : Γ →* Module.End F M) (c : Γ → F) : Module.End F M := ∑ g, c g • a g

theorem avg_fix (a : Γ →* Module.End F M) (P : Subgroup Γ) [Fintype P] (t : P →* Fˣ)
    (hc : (Fintype.card P : F) ≠ 0) {x : M} (hx : ∀ u : P, a (u : Γ) x = ((t u : Fˣ) : F) • x) :
    avg a P t x = x := by
  have : ∀ u : P, ((((t u)⁻¹ : Fˣ) : F) • a (u : Γ)) x = x := fun u => by
    rw [LinearMap.smul_apply, hx u, smul_smul, Units.inv_mul, one_smul]
  simp only [avg, LinearMap.smul_apply, LinearMap.sum_apply, this, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul F, smul_smul, inv_mul_cancel₀ hc, one_smul]

theorem avg_type (a : Γ →* Module.End F M) (P : Subgroup Γ) [Fintype P] (t : P →* Fˣ) (v : P) (y : M) :
    a (v : Γ) (avg a P t y) = ((t v : Fˣ) : F) • avg a P t y := by
  simp only [avg, LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
  rw [smul_comm]
  congr 1
  rw [Finset.smul_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft v) _ _ fun u => ?_
  simp only [Equiv.coe_mulLeft, Subgroup.coe_mul, map_mul, Module.End.mul_apply, mul_inv_rev, Units.val_mul, smul_smul]
  congr 1
  rw [mul_left_comm, Units.mul_inv, mul_one]

variable (a : Γ →* Module.End F M) (P : Subgroup Γ) [Fintype P] (t : P →* Fˣ) (E : Module.End F M)

theorem mem_range_iff_type (hc : (Fintype.card P : F) ≠ 0) (hE : E * E = E)
    (hcom : ∀ u : P, a (u : Γ) * E = E * a (u : Γ)) (x : M) :
    x ∈ LinearMap.range (E * avg a P t) ↔
      (∀ u : P, a (u : Γ) x = ((t u : Fˣ) : F) • x) ∧ x ∈ LinearMap.range E := by
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨fun u => ?_, ⟨_, rfl⟩⟩
    have h := congrArg (fun A : Module.End F M => A (avg a P t y)) (hcom u)
    simp only [Module.End.mul_apply] at h ⊢
    rw [h, avg_type, map_smul]
  · rintro ⟨h, y, rfl⟩
    refine ⟨E y, ?_⟩
    have h2 : E (E y) = E y := congrArg (fun A : Module.End F M => A y) hE
    rw [Module.End.mul_apply, avg_fix a P t hc h, h2]

theorem mem_range_iff_image (hc : (Fintype.card P : F) ≠ 0) (x : M) :
    x ∈ LinearMap.range (E * avg a P t) ↔
      ∃ y, (∀ u : P, a (u : Γ) y = ((t u : Fˣ) : F) • y) ∧ E y = x := by
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨avg a P t y, fun u => avg_type a P t u y, rfl⟩
  · rintro ⟨y, h, rfl⟩
    exact ⟨y, by rw [Module.End.mul_apply, avg_fix a P t hc h]⟩

end Rep

section Ext

variable {O K K'' Fm : Type} [CommRing O] [Field K] [Algebra O K] [IsFractionRing O K]
  [Field K''] [Algebra O K''] [Algebra K K''] [IsScalarTower O K K'']
  [AddCommGroup Fm] [Module K Fm] [Module O Fm] [IsScalarTower O K Fm]

variable (O K'') in

def ext (A : Module.End K Fm) : Module.End K'' (K'' ⊗[O] Fm) :=
  LinearMap.baseChange K'' (A.restrictScalars O)

@[simp] theorem ext_tmul (A : Module.End K Fm) (x : K'') (m : Fm) :
    ext O K'' A (x ⊗ₜ[O] m) = x ⊗ₜ[O] A m := rfl

theorem tmul_smul_frac (c : K) (x : K'') (m : Fm) :
    x ⊗ₜ[O] (c • m) = (algebraMap K K'' c * x) ⊗ₜ[O] m := by
  have := IsLocalization.tensorProduct_compatibleSMul (nonZeroDivisors O) K K'' Fm
  rw [← TensorProduct.smul_tmul, Algebra.smul_def]

theorem ext_mul (A B : Module.End K Fm) : ext O K'' (A * B) = ext O K'' A * ext O K'' B := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro x m
  rfl

theorem ext_one : ext O K'' (1 : Module.End K Fm) = 1 := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro x m
  rfl

theorem ext_add (A B : Module.End K Fm) : ext O K'' (A + B) = ext O K'' A + ext O K'' B := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro x m
  simp [TensorProduct.tmul_add]

theorem ext_zero : ext O K'' (0 : Module.End K Fm) = 0 := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro x m
  simp

theorem ext_smul (c : K) (A : Module.End K Fm) :
    ext O K'' (c • A) = algebraMap K K'' c • ext O K'' A := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro x m
  simp [tmul_smul_frac, TensorProduct.smul_tmul', smul_eq_mul]
  rw [Algebra.smul_def]

theorem ext_sum {ι : Type} (s : Finset ι) (A : ι → Module.End K Fm) :
    ext O K'' (∑ i ∈ s, A i) = ∑ i ∈ s, ext O K'' (A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using ext_zero
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ext_add, ih]

theorem range_ext (A : Module.End K Fm) :
    LinearMap.range (ext O K'' A) =
      ((LinearMap.range A).restrictScalars O).baseChange K'' := by
  apply le_antisymm
  · rintro _ ⟨z, rfl⟩
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | tmul x m =>
      rw [ext_tmul]
      have : x ⊗ₜ[O] A m = x • ((1 : K'') ⊗ₜ[O] A m) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.tmul_mem_baseChange_of_mem _ ⟨m, rfl⟩)
  · rw [Submodule.baseChange_eq_span, Submodule.span_le]
    rintro _ ⟨_, ⟨m, rfl⟩, rfl⟩
    exact ⟨(1 : K'') ⊗ₜ[O] m, rfl⟩

end Ext

end GlobalTheory.CompanionTheory.LatSpan

noncomputable section

open scoped TensorProduct
open Module NumberField

namespace GlobalTheory.CompanionTheory.LatSpan

section Main

variable {LL O K K'' Fm WL Γ : Type} [Field LL] [CharZero LL] [AddCommGroup WL] [Module LL WL]
  [CommRing O] [Field K] [Algebra O K] [IsFractionRing O K]
  [Field K''] [Algebra O K''] [Algebra K K''] [IsScalarTower O K K'']
  [AddCommGroup Fm] [Module K Fm] [Module O Fm] [IsScalarTower O K Fm] [Group Γ] [Fintype Γ]

theorem span_image_good (σ : LL →+* K'') (f : WL →ₛₗ[σ] K'' ⊗[O] Fm) (hinj : Function.Injective f)
    (hspan : Submodule.span K'' (Set.range f) = ⊤)
    (aF : Γ →* Module.End K Fm) (aL : Γ → Module.End LL WL)
    (hc : ∀ g x, f (aL g x) = ext O K'' (aF g) (f x))
    (P : Subgroup Γ) [Fintype P] (tL : P →* LLˣ) (tF : P →* Kˣ)
    (ht : ∀ u, σ ((tL u : LLˣ) : LL) = algebraMap K K'' ((tF u : Kˣ) : K))
    (cL : Γ → LL) (cF : Γ → K) (hcf : ∀ g, σ (cL g) = algebraMap K K'' (cF g))
    (hE : grp aF cF * grp aF cF = grp aF cF) (hcom : ∀ u : P, aF (u : Γ) * grp aF cF = grp aF cF * aF (u : Γ))
    (V : Submodule K Fm)
    (hV : ∀ x, x ∈ V ↔ ∃ y, (∀ u : P, aF (u : Γ) y = ((tF u : Kˣ) : K) • y) ∧ grp aF cF y = x)
    (Wg : Submodule LL WL)
    (hW : ∀ x, x ∈ Wg ↔ (∀ u : P, aL (u : Γ) x = ((tL u : LLˣ) : LL) • x) ∧
      x ∈ LinearMap.range (∑ g, cL g • aL g)) :
    Submodule.span K'' (f '' (Wg : Set WL)) = (V.restrictScalars O).baseChange K'' := by
  have extmul : ∀ (A B : Module.End K Fm) (z : K'' ⊗[O] Fm),
      ext O K'' (A * B) z = ext O K'' A (ext O K'' B z) := fun A B z => by rw [ext_mul]; rfl
  let aLh : Γ →* Module.End LL WL :=
    { toFun := aL
      map_one' := by
        ext x
        apply hinj
        rw [hc, map_one, ext_one]; rfl
      map_mul' := fun g h => by
        ext x
        apply hinj
        rw [hc, map_mul, extmul, Module.End.mul_apply, hc, hc] }
  have hcL : (Fintype.card P : LL) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hcK : (Fintype.card P : K) ≠ 0 := fun h => hcL (σ.injective (by
    rw [map_natCast, map_zero]
    have := congrArg (algebraMap K K'') h
    rwa [map_natCast, map_zero] at this))
  have hfE : ∀ x, f (grp aLh cL x) = ext O K'' (grp aF cF) (f x) := fun x => by
    simp only [grp, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smulₛₗ, ext_sum, ext_smul]
    exact Finset.sum_congr rfl fun g _ => by rw [hcf]; congr 1; exact hc g x
  have hfA : ∀ x, f (avg aLh P tL x) = ext O K'' (avg aF P tF) (f x) := fun x => by
    simp only [avg, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smulₛₗ, ext_sum, ext_smul]
    rw [map_inv₀, map_inv₀, map_natCast, map_natCast]
    congr 1
    refine Finset.sum_congr rfl fun u _ => ?_
    have e1 : σ ((((tL u)⁻¹ : LLˣ)) : LL) = algebraMap K K'' ((((tF u)⁻¹ : Kˣ)) : K) := by
      rw [Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, map_inv₀, map_inv₀, ht]
    rw [e1]; congr 1; exact hc u x
  have hEL : grp aLh cL * grp aLh cL = grp aLh cL := by
    ext x
    apply hinj
    rw [Module.End.mul_apply, hfE, hfE, ← extmul, hE]
  have hcomL : ∀ u : P, aLh (u : Γ) * grp aLh cL = grp aLh cL * aLh (u : Γ) := fun u => by
    ext x
    apply hinj
    rw [Module.End.mul_apply, Module.End.mul_apply, hfE]
    change f (aL u _) = _
    rw [hc, hfE, ← extmul, hcom, extmul]
    change _ = ext O K'' (grp aF cF) (f (aL u x))
    rw [hc]
  have hWr : (Wg : Set WL) = LinearMap.range (grp aLh cL * avg aLh P tL) := by
    ext x
    rw [SetLike.mem_coe, hW, SetLike.mem_coe, mem_range_iff_type aLh P tL _ hcL hEL hcomL]
    rfl
  have hVr : V = LinearMap.range (grp aF cF * avg aF P tF) := by
    ext x
    rw [hV, mem_range_iff_image aF P tF _ hcK]
  have hr : LinearMap.range (ext O K'' (grp aF cF * avg aF P tF)) =
      Submodule.map (ext O K'' (grp aF cF * avg aF P tF)) (Submodule.span K'' (Set.range f)) := by
    rw [hspan, LinearMap.range_eq_map]
  rw [hWr, hVr, ← range_ext, hr, Submodule.map_span]
  congr 1
  ext z
  constructor
  · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
    refine ⟨f y, ⟨y, rfl⟩, ?_⟩
    rw [Module.End.mul_apply, hfE, hfA, extmul]
  · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
    refine ⟨_, ⟨y, rfl⟩, ?_⟩
    rw [Module.End.mul_apply, hfE, hfA, extmul]

end Main

section Lat

theorem integers_embed {LL Oe K'' : Type} [Field LL] [NumberField LL] [CommRing Oe] [IsDomain Oe]
    [IsIntegrallyClosed Oe] [Field K''] [Algebra Oe K''] [IsFractionRing Oe K''] (σ : LL →+* K'') (a : 𝓞 LL) :
    ∃ r : Oe, σ (a : LL) = algebraMap Oe K'' r := by
  have h : IsIntegral ℤ (σ (a : LL)) := (a.2 : IsIntegral ℤ (a : LL)).map σ.toIntAlgHom
  have h2 : IsIntegral Oe (σ (a : LL)) := h.tower_top
  obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.1 h2
  exact ⟨r, hr.symm⟩

variable {LL Oe K'' V T : Type} [Field LL] [NumberField LL] [AddCommGroup V] [Module LL V] [Module (𝓞 LL) V]
  [IsScalarTower (𝓞 LL) LL V] [CommRing Oe] [IsDomain Oe] [Field K''] [Algebra Oe K''] [IsFractionRing Oe K'']
  [AddCommGroup T] [Module K'' T] [Module Oe T] [IsScalarTower Oe K'' T]

theorem exists_smul_mem (M : Submodule Oe T) {x : T} (hx : x ∈ Submodule.span K'' (M : Set T)) :
    ∃ c : Oe, c ≠ 0 ∧ c • x ∈ M := by
  first
  | (rename_i h_3 h_4 h_5 h_6 h_7 h_8 h_9 h_10 h_11; revert Oe K'' T h_3 h_4 h_5 h_6 h_7 h_8 h_9 h_10 h_11 M x hx; exact @_root_.GlobalTheory.SmulMemOfMemSpanExists.exists_smul_mem_of_mem_span)
  | exact @_root_.GlobalTheory.SmulMemOfMemSpanExists.exists_smul_mem_of_mem_span
  | exact _root_.GlobalTheory.SmulMemOfMemSpanExists.exists_smul_mem_of_mem_span
  | (apply _root_.GlobalTheory.SmulMemOfMemSpanExists.exists_smul_mem_of_mem_span <;> assumption)
  | (intros; apply _root_.GlobalTheory.SmulMemOfMemSpanExists.exists_smul_mem_of_mem_span <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SmulMemOfMemSpanExists.exists_smul_mem_of_mem_span <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SmulMemOfMemSpanExists.exists_smul_mem_of_mem_span ..)

theorem isLatIn_span (σ : LL →+* K'') (hint : ∀ a : 𝓞 LL, ∃ r : Oe, σ (a : LL) = algebraMap Oe K'' r)
    (eM : V →ₛₗ[σ] T) (L : Submodule (𝓞 LL) V) (hFG : L.FG) (hsp : Submodule.span LL (L : Set V) = ⊤)
    (VV : Submodule K'' T) (hVV : Submodule.span K'' (Set.range eM) = VV) :
    Formalism.BasicNotions.NForms.IsLatIn (Submodule.span Oe (eM '' (L : Set V))) (VV.restrictScalars Oe) := by
  have hmem : ∀ x, eM x ∈ VV := fun x => hVV ▸ Submodule.subset_span ⟨x, rfl⟩
  refine ⟨?_, ?_, fun x hx => ?_⟩
  · obtain ⟨S, rfl⟩ := hFG
    classical
    refine ⟨S.image eM, le_antisymm ?_ ?_⟩
    · refine Submodule.span_le.2 ?_
      intro y hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
      exact Submodule.subset_span ⟨x, Submodule.subset_span hx, rfl⟩
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨x, hx, rfl⟩
      simp only [SetLike.mem_coe] at hx ⊢
      induction hx using Submodule.span_induction with
      | mem x h => exact Submodule.subset_span (by simpa using ⟨x, h, rfl⟩)
      | zero => simp
      | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
      | smul a x _ hx =>
        obtain ⟨r, hr⟩ := hint a
        have : eM (a • x) = r • eM x := by
          rw [← algebraMap_smul LL a x, map_smulₛₗ]
          change σ (a : LL) • eM x = _
          rw [hr, algebraMap_smul]
        rw [this]
        exact Submodule.smul_mem _ _ hx
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨x, _, rfl⟩
    exact hmem x
  · have hle : Set.range eM ⊆ (Submodule.span K'' ((Submodule.span Oe (eM '' (L : Set V)) : Submodule Oe T) : Set T) : Set T) := by
      rintro _ ⟨v, rfl⟩
      have hv : v ∈ Submodule.span LL (L : Set V) := hsp ▸ Submodule.mem_top
      simp only [SetLike.mem_coe]
      induction hv using Submodule.span_induction with
      | mem x h => exact Submodule.subset_span (Submodule.subset_span ⟨x, h, rfl⟩)
      | zero => simp
      | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
      | smul a x _ hx => rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ hx
    have hx' : x ∈ VV := hx
    rw [← hVV] at hx'
    exact exists_smul_mem _ (Submodule.span_le.2 hle hx')

end Lat

end GlobalTheory.CompanionTheory.LatSpan

end
end
end

section

noncomputable section

open scoped TensorProduct
open Module NumberField

namespace GlobalTheory.CompanionTheory.LatSpan

open GlobalTheory.IndefiniteRowSideFullHecke.SemilinearExtensionBases

section Form

variable {Ks LL WL : Type} [Field Ks] [Field LL] [Algebra Ks LL]
  [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL]
  {WK : Submodule Ks WL}
  {O K K'' : Type} [CommRing O] [IsDomain O] [Field K] [Algebra O K] [IsFractionRing O K] [Algebra Ks K]
  [Field K''] [Algebra O K''] [Algebra K K''] [IsScalarTower O K K'']
  {Fm : Type} [AddCommGroup Fm] [Module K Fm] [Module O Fm] [IsScalarTower O K Fm]

theorem inj_span_of_carries {emb : LL →+* K''} (e : WL →ₛₗ[emb] K'' ⊗[O] Fm) (h : CarriesBases O e) :
    Function.Injective e ∧ Submodule.span K'' (Set.range e) = ⊤ := by
  classical
  obtain ⟨b'', hb⟩ := h _ (Basis.ofVectorSpace LL WL)
  set b := Basis.ofVectorSpace LL WL with hbdef
  have hsum : ∀ x, e x = ∑ i ∈ (b.repr x).support, emb (b.repr x i) • b'' i := fun x => by
    conv_lhs => rw [← b.linearCombination_repr x]
    simp [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smulₛₗ, hb]
  constructor
  · refine (injective_iff_map_eq_zero e).2 fun x hx => ?_
    rw [hsum] at hx
    have h0 := linearIndependent_iff'.1 b''.linearIndependent _ _ hx
    have : b.repr x = 0 := by
      ext i
      by_contra hi
      have hm : i ∈ (b.repr x).support := Finsupp.mem_support_iff.2 hi
      exact hi ((map_eq_zero emb).1 (h0 i hm))
    simpa using this
  · rw [eq_top_iff, ← b''.span_eq]
    refine Submodule.span_mono ?_
    rintro _ ⟨i, rfl⟩
    exact ⟨b i, (hb i).symm⟩

theorem ext_intertwine (hF : IsForm LL WK) {emb : LL →+* K''} (eF : Fm ≃ₗ[K] K ⊗[Ks] WK)
    (e : WL →ₛₗ[emb] K'' ⊗[O] Fm) (he : IsExt O emb eF e)
    (rK : Module.End Ks WK) (rL : Module.End LL WL) (hr : ∀ f : WK, rL (f : WL) = (rK f : WK))
    (cL : LL) (cK : K) (hc : emb cL = algebraMap K K'' cK) (aF : Module.End K Fm)
    (ha : ∀ y, eF (aF y) = cK • LinearMap.baseChange K rK (eF y)) (x : WL) :
    e (cL • rL x) = ext O K'' aF (e x) := by
  obtain ⟨n, b, hbK, -, -, -, hsp⟩ := hF
  have hx : x ∈ Submodule.span LL (Set.range b) := hsp ▸ Submodule.mem_top
  obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun LL).1 hx
  let f : Fin n → WK := fun k => ⟨b k, hbK k⟩
  have e1 := he (Fin n) a f
  have e2 := he (Fin n) (fun k => cL * a k) (fun k => rK (f k))
  have e3 : cL • rL (∑ k, a k • b k) = ∑ k, (cL * a k) • ((rK (f k) : WK) : WL) := by
    rw [map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, ← hr (f k), mul_smul]
  have e4 : ∑ k, a k • b k = ∑ k, a k • ((f k : WK) : WL) := rfl
  rw [e3, e2, e4, e1, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [ext_tmul]
  have e5 : aF (eF.symm ((1 : K) ⊗ₜ[Ks] f k)) = cK • eF.symm ((1 : K) ⊗ₜ[Ks] rK (f k)) := by
    apply eF.injective
    rw [ha, LinearEquiv.apply_symm_apply, map_smul, LinearEquiv.apply_symm_apply, LinearMap.baseChange_tmul]
  rw [e5, tmul_smul_frac, map_mul, hc]

end Form

section Iso

open Formalism.IndefR.NX Formalism.IndefR.Arith

variable {LL Ks Ks' WL WL' G G' : Type} [Field LL] [NumberField LL] [Field Ks] [NumberField Ks] [Algebra Ks LL]
  [Field Ks'] [NumberField Ks'] [Algebra Ks' LL]
  [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL] [Module (𝓞 LL) WL] [IsScalarTower (𝓞 LL) LL WL]
  [Module (𝓞 Ks) WL] [IsScalarTower (𝓞 Ks) Ks WL]
  [AddCommGroup WL'] [Module LL WL'] [Module Ks' WL'] [IsScalarTower Ks' LL WL'] [Module (𝓞 LL) WL']
  [IsScalarTower (𝓞 LL) LL WL'] [Module (𝓞 Ks') WL'] [IsScalarTower (𝓞 Ks') Ks' WL']
  {W W' : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
  [∀ σ, NormedAddCommGroup (W' σ)] [∀ σ, InnerProductSpace ℂ (W' σ)] [Group G] [Group G']

theorem isKsForm_of_iso {A : FormsL LL Ks WL W G} {A' : FormsL LL Ks' WL' W' G'} (I : FormsIso A A')
    (h : A'.IsKsForm) : A.IsKsForm := by
  obtain ⟨n, b, hb, -, hs, hl, ht⟩ := h
  have hmem : ∀ z ∈ Submodule.span Ks' (Set.range b), I.e.symm z ∈ Submodule.span Ks (Set.range fun k => I.e.symm (b k)) := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z h =>
      obtain ⟨k, rfl⟩ := h
      exact Submodule.subset_span ⟨k, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx =>
      have h1 : c • x = algebraMap Ks LL (I.eK.symm c) • x := by
        rw [← I.eK_LL, RingEquiv.apply_symm_apply, algebraMap_smul]
      rw [h1, map_smul, algebraMap_smul]
      exact Submodule.smul_mem _ _ hx
  have hli : LinearIndependent LL fun k => I.e.symm (b k) := hl.map' I.e.symm.toLinearMap I.e.symm.ker
  refine ⟨n, fun k => I.e.symm (b k), fun k => ?_, ?_, le_antisymm ?_ ?_, hli, ?_⟩
  · rw [I.wk, LinearEquiv.apply_symm_apply]
    exact hs ▸ Submodule.subset_span ⟨k, rfl⟩
  · exact hli.restrict_scalars (fun a c h => (algebraMap Ks LL).injective (by simpa [Algebra.smul_def] using h))
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨k, rfl⟩
    rw [SetLike.mem_coe, I.wk, LinearEquiv.apply_symm_apply]
    exact hs ▸ Submodule.subset_span ⟨k, rfl⟩
  · intro x hx
    have := hmem (I.e x) (hs ▸ (I.wk x).1 hx)
    rwa [LinearEquiv.symm_apply_apply] at this
  · rw [eq_top_iff]
    intro x _
    have hx : I.e x ∈ Submodule.span LL (Set.range b) := ht ▸ Submodule.mem_top
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun LL).1 hx
    have : x = ∑ k, a k • I.e.symm (b k) := by
      apply I.e.injective
      rw [← ha, map_sum]
      simp
    rw [this]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

end Iso

end GlobalTheory.CompanionTheory.LatSpan

end
end

section

noncomputable section

open scoped TensorProduct
open Module NumberField

namespace GlobalTheory.CompanionTheory.LatSpan

open GlobalTheory.IndefiniteRowSideFullHecke.SemilinearExtensionBases GlobalTheory.IndefiniteRowSideFullHecke.FractionalBaseInclusion Formalism.BasicNotions Formalism.IndefR.NX

section PiLocalization₂

variable {D : D7} (c : NChoice D) (w : D.what₂.places.Pl)

@[reducible] def algKK : Algebra (FractionRing (D.ntw.O (c.twI w))) (FractionRing (c.Oe w)) :=
  (fracExt c w).toAlgebra

attribute [local instance] algKK

set_option synthInstance.maxHeartbeats 400000 in
instance towKK : IsScalarTower (D.ntw.O (c.twI w)) (FractionRing (D.ntw.O (c.twI w))) (FractionRing (c.Oe w)) :=
  IsScalarTower.of_algebraMap_eq fun y => by
    rw [IsScalarTower.algebraMap_apply (D.ntw.O (c.twI w)) (c.Oe w) (FractionRing (c.Oe w)), RingHom.algebraMap_toAlgebra]
    simp [fracExt, IsFractionRing.map]

variable {c w}

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem stage1 (ht : NChTie D c) (j : ℕ) (S : RatDat D.ntw) (hks : (S.A j).IsKsForm)
    (rho : RhoStab S j) (chi : ChiInLL0 S j)
    (eF : D.nexp.Fm (c.twI w) j (c.sd w) ≃ₗ[FractionRing (D.ntw.O (c.twI w))] Fm S (c.twI w) j (c.sd w))
    (hact : ∀ g x, eF (D.nexp.actG (c.twI w) j (c.sd w) g x) = actG S (c.twI w) j (c.sd w) rho chi g (eF x)) :
    ∃ e : S.WL j →ₛₗ[c.embW w] FractionRing (c.Oe w) ⊗[D.ntw.O (c.twI w)] D.nexp.Fm (c.twI w) j (c.sd w),
      Function.Injective e ∧ Submodule.span (FractionRing (c.Oe w)) (Set.range e) = ⊤ ∧
      (∀ (n : ℕ) (a : Fin n → D.what₂.LL) (f : Fin n → FmK S j),
        e (∑ k, a k • (show ↥(S.A j).WK from f k).1) =
          ∑ k, c.embW w (a k) ⊗ₜ[D.ntw.O (c.twI w)] eF.symm ((1 : KB S (c.twI w) (c.sd w)) ⊗ₜ[S.Ks] f k)) ∧
      (∀ (s : S.G) (x : S.WL j), e ((((S.A j).chi s)⁻¹ : D.what₂.LLˣ).val • (S.A j).ρ s x) =
        ext (D.ntw.O (c.twI w)) (FractionRing (c.Oe w))
          ((D.nexp.actG (c.twI w) j (c.sd w) (S.eG s)).toLinearMap) (e x)) := by
  letI algK : Algebra S.Ks (FractionRing (D.ntw.O (c.twI w))) := (ιK S (c.twI w) (c.sd w)).toAlgebra
  have hcomp : (c.embW w).comp (algebraMap S.Ks D.what₂.LL) =
      (algebraMap (FractionRing (D.ntw.O (c.twI w))) (FractionRing (c.Oe w))).comp
        (algebraMap S.Ks (FractionRing (D.ntw.O (c.twI w)))) :=
    GlobalTheory.Proof.FractionFieldEmbeddingCompat.embCompat D c ht S.Ks S.kKs S.kKs_spec w (ιK S (c.twI w) (c.sd w)) rfl
  let eF' : D.nexp.Fm (c.twI w) j (c.sd w) ≃ₗ[FractionRing (D.ntw.O (c.twI w))]
      FractionRing (D.ntw.O (c.twI w)) ⊗[S.Ks] (S.A j).WK := eF
  obtain ⟨⟨e, he, -⟩, hcar, -⟩ := GlobalTheory.SemilinearExt.semilinearExtension S.Ks D.what₂.LL (S.WL j) (S.A j).WK hks
    (D.ntw.O (c.twI w)) (FractionRing (D.ntw.O (c.twI w))) (FractionRing (c.Oe w)) (c.embW w) hcomp
    (D.nexp.Fm (c.twI w) j (c.sd w)) eF'
  obtain ⟨h1, h2⟩ := inj_span_of_carries e (hcar e he)
  refine ⟨e, h1, h2, fun n a f => he (Fin n) a f, fun s x => ?_⟩
  have hc : c.embW w ((((S.A j).chi s)⁻¹ : D.what₂.LLˣ).val) =
      algebraMap (FractionRing (D.ntw.O (c.twI w))) (FractionRing (c.Oe w))
        ((readLL0 S (c.twI w) (c.sd w) (chiL S j chi s))⁻¹) := by
    rw [Units.val_inv_eq_inv_val, map_inv₀]
    exact (congrArg Inv.inv (GlobalTheory.Proof.FractionFieldEmbeddingCompat.embW_eq_of_tie ht w (chiL S j chi s))).trans
      (map_inv₀ (algebraMap (FractionRing (D.ntw.O (c.twI w))) (FractionRing (c.Oe w))) _).symm
  refine ext_intertwine hks eF' e he (rhoKG S j rho s) ((S.A j).ρ s) (fun f => rfl) _ _ hc _ (fun y => ?_) x
  have h3 := hact (S.eG s) y
  refine h3.trans ?_
  have h4 : actG S (c.twI w) j (c.sd w) rho chi (S.eG s) (eF y) =
      actEnd S (c.twI w) j (c.sd w) rho chi (S.eG.symm (S.eG s)) (eF y) := rfl
  rw [h4, MulEquiv.symm_apply_apply]
  rfl

end PiLocalization₂

end GlobalTheory.CompanionTheory.LatSpan

noncomputable section
open scoped TensorProduct
open Module NumberField
namespace GlobalTheory.CompanionTheory.LatSpan

section Alg
variable {k A G : Type} [Field k] [Ring A] [Algebra k A] [Group G]

theorem lift_eq_sum [Fintype G] (F : G →* A) (x : MonoidAlgebra k G) :
    MonoidAlgebra.lift k A G F x = ∑ g, x.coeff g • F g := by
  rw [MonoidAlgebra.lift_apply]
  exact Finsupp.sum_fintype _ _ (fun _ => zero_smul _ _)

theorem lift_comm (F : G →* A) (x : MonoidAlgebra k G) (h : ∀ y, x * y = y * x) (g : G) :
    F g * MonoidAlgebra.lift k A G F x = MonoidAlgebra.lift k A G F x * F g := by
  have e : F g = MonoidAlgebra.lift k A G F (MonoidAlgebra.single g 1) := by
    rw [MonoidAlgebra.lift_single, one_smul]
  rw [e, ← map_mul, ← map_mul, h]

end Alg
end GlobalTheory.CompanionTheory.LatSpan

noncomputable section
open scoped TensorProduct
open Module NumberField
namespace GlobalTheory.CompanionTheory.LatSpan
open GlobalTheory.IndefiniteRowSideFullHecke.SemilinearExtensionBases GlobalTheory.IndefiniteRowSideFullHecke.FractionalBaseInclusion Formalism.BasicNotions Formalism.IndefR.NX Formalism.IndefR.Arith

section Stage2

variable {D : D7} {c : NChoice D} {w : D.what₂.places.Pl}

attribute [local instance] algKK

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 2000000 in
theorem stage2 (ht : NChTie D c) {Gp : Type} [Group Gp] [Fintype Gp] (I : Gp ≃* G0g D.nd)
    (S : RatDat D.ntw) (j : ℕ)
    {Ks' WL' : Type} [Field Ks'] [NumberField Ks'] [Algebra Ks' D.what₂.LL] [AddCommGroup WL'] [Module D.what₂.LL WL']
    [Module Ks' WL'] [IsScalarTower Ks' D.what₂.LL WL'] [Module (𝓞 D.what₂.LL) WL'] [IsScalarTower (𝓞 D.what₂.LL) D.what₂.LL WL']
    [Module (𝓞 Ks') WL'] [IsScalarTower (𝓞 Ks') Ks' WL']
    {W' : (D.what₂.LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W' σ)] [∀ σ, InnerProductSpace ℂ (W' σ)]
    (A' : FormsL D.what₂.LL Ks' WL' W' Gp) (fi : FormsIso (S.A j) A') (hks' : A'.IsKsForm)
    (hgeq : ∀ s, I (fi.eG s) = S.eG s)
    (rho : RhoStab S j) (chi : ChiInLL0 S j)
    (eF : D.nexp.Fm (c.twI w) j (c.sd w) ≃ₗ[FractionRing (D.ntw.O (c.twI w))] Fm S (c.twI w) j (c.sd w))
    (hact : ∀ g x, eF (D.nexp.actG (c.twI w) j (c.sd w) g x) = actG S (c.twI w) j (c.sd w) rho chi g (eF x))
    (eC : Gp → D.what₂.LL) (heC : ∀ h, eC h = (D.nexp.eLL0 (I h) : D.what₂.LL))
    (P0 : Subgroup Gp) (ψ : P0 →* D.what₂.LLˣ) (hlvl : ∀ g, g ∈ P0 ↔ I g ∈ D.nexp.U)
    (hpsi : ∀ (u : P0) (hu : I (u : Gp) ∈ D.nexp.U), ∃ x : D.LL0, (x : D.what₂.LL) = ((ψ u : D.what₂.LLˣ) : D.what₂.LL) ∧
      ((D.nexp.psiU (c.twI w) (c.sd w) ⟨I (u : Gp), hu⟩ : (FractionRing (D.ntw.O (c.twI w)))ˣ) : FractionRing (D.ntw.O (c.twI w))) =
        fracBase D (c.twI w) (embSide D (c.twI w) (c.sd w) x)) :
    ∃ e : S.WL j →ₛₗ[c.embW w] FractionRing (c.Oe w) ⊗[D.ntw.O (c.twI w)] D.nexp.Fm (c.twI w) j (c.sd w),
      (∀ (n : ℕ) (a : Fin n → D.what₂.LL) (f : Fin n → FmK S j),
        e (∑ k, a k • (show ↥(S.A j).WK from f k).1) =
          ∑ k, c.embW w (a k) ⊗ₜ[D.ntw.O (c.twI w)] eF.symm ((1 : KB S (c.twI w) (c.sd w)) ⊗ₜ[S.Ks] f k)) ∧
      Submodule.span (FractionRing (c.Oe w)) ((fun y => e (fi.e.symm y)) '' (A'.Wgood P0 ψ eC : Set WL')) =
        ((NForms.V0 D (c.twI w) j (c.sd w)).restrictScalars (D.ntw.O (c.twI w))).baseChange (FractionRing (c.Oe w)) := by
  classical
  obtain ⟨e, h1, h2, h3, h4⟩ := stage1 (w := w) ht j S (isKsForm_of_iso fi hks') rho chi eF hact
  refine ⟨e, h3, ?_⟩
  letI : Fintype P0 := Fintype.ofFinite _
  letI : Fintype (G0g D.nd) := Fintype.ofEquiv Gp I.toEquiv
  let Fh : G0g D.nd →* Module.End (FractionRing (D.ntw.O (c.twI w))) (D.nexp.Fm (c.twI w) j (c.sd w)) :=
    LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (D.nexp.actG (c.twI w) j (c.sd w))
  let aF : Gp →* Module.End (FractionRing (D.ntw.O (c.twI w))) (D.nexp.Fm (c.twI w) j (c.sd w)) :=
    Fh.comp I.toMonoidHom
  let aL : Gp → Module.End D.what₂.LL WL' := fun h => ((A'.chi h)⁻¹ : D.what₂.LLˣ).val • A'.ρ h
  let φ : P0 →* D.nexp.U :=
    { toFun := fun p => ⟨I p, (hlvl _).1 p.2⟩
      map_one' := Subtype.ext (map_one I)
      map_mul' := fun a b => Subtype.ext (map_mul I (a : Gp) (b : Gp)) }
  let tF : P0 →* (FractionRing (D.ntw.O (c.twI w)))ˣ := (D.nexp.psiU (c.twI w) (c.sd w)).comp φ
  let cF : Gp → FractionRing (D.ntw.O (c.twI w)) := fun h => (D.nexp.eAlg (c.twI w) (c.sd w)).coeff (I h)
  have hEq : grp aF cF = NForms.eG D (c.twI w) j (c.sd w) := by
    unfold NForms.eG
    rw [lift_eq_sum]
    exact Fintype.sum_equiv I.toEquiv _ _ fun h => rfl
  let f : WL' →ₛₗ[c.embW w] FractionRing (c.Oe w) ⊗[D.ntw.O (c.twI w)] D.nexp.Fm (c.twI w) j (c.sd w) :=
    e.comp fi.e.symm.toLinearMap
  have key := span_image_good (O := D.ntw.O (c.twI w)) (K := FractionRing (D.ntw.O (c.twI w)))
    (K'' := FractionRing (c.Oe w)) (c.embW w) f (h1.comp fi.e.symm.injective) ?_ aF aL ?_ P0 ψ tF ?_ eC cF ?_ ?_ ?_
    (NForms.V0 D (c.twI w) j (c.sd w)) ?_ (A'.Wgood P0 ψ eC) ?_
  · exact key
  · rw [eq_top_iff, ← h2]
    refine Submodule.span_mono ?_
    rintro _ ⟨x, rfl⟩
    exact ⟨fi.e x, by simp [f]⟩
  · intro h y
    have hs : fi.eG (fi.eG.symm h) = h := MulEquiv.apply_symm_apply _ _
    have k1 : fi.e.symm (aL h y) = ((((S.A j).chi (fi.eG.symm h))⁻¹ : D.what₂.LLˣ).val) •
        (S.A j).ρ (fi.eG.symm h) (fi.e.symm y) := by
      apply fi.e.injective
      rw [LinearEquiv.apply_symm_apply, map_smul, fi.rho, hs, LinearEquiv.apply_symm_apply, ← fi.chi, hs]
      rfl
    have k2 := h4 (fi.eG.symm h) (fi.e.symm y)
    rw [← hgeq, hs, ← k1] at k2
    exact k2
  · intro u
    obtain ⟨x, hx1, hx2⟩ := hpsi u ((hlvl _).1 u.2)
    rw [← hx1, GlobalTheory.Proof.FractionFieldEmbeddingCompat.embW_eq_of_tie ht w x, ← hx2]
    rfl
  · intro h
    rw [heC, GlobalTheory.Proof.FractionFieldEmbeddingCompat.embW_eq_of_tie ht w]
    change _ = fracExt c w ((D.nexp.eAlg (c.twI w) (c.sd w)).coeff (I h))
    rw [D.nexp.eAlg_def]
    rfl
  · rw [hEq]
    unfold NForms.eG
    rw [← map_mul, D.nexp.eAlg_idem]
  · intro u
    rw [hEq]
    exact lift_comm Fh _ (D.nexp.eAlg_central _ _) _
  · intro x
    rw [hEq]
    have hy : ∀ y, y ∈ NForms.Fm0 D (c.twI w) j (c.sd w) ↔
        ∀ u : P0, aF (u : Gp) y = ((tF u : (FractionRing (D.ntw.O (c.twI w)))ˣ) : FractionRing (D.ntw.O (c.twI w))) • y := by
      intro y
      rw [NForms.Fm0, Submodule.mem_iInf]
      simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
      constructor
      · intro h u
        exact h (φ u)
      · intro h u
        have hu : I.symm (u : G0g D.nd) ∈ P0 := (hlvl _).2 (by simp)
        have h5 := h ⟨_, hu⟩
        have e5 : φ ⟨_, hu⟩ = u := Subtype.ext (I.apply_symm_apply _)
        change D.nexp.actG (c.twI w) j (c.sd w) ((φ ⟨_, hu⟩ : D.nexp.U) : G0g D.nd) y =
          ((D.nexp.psiU (c.twI w) (c.sd w) (φ ⟨_, hu⟩) : (FractionRing (D.ntw.O (c.twI w)))ˣ) :
            FractionRing (D.ntw.O (c.twI w))) • y at h5
        rw [e5] at h5
        exact h5
    simp only [NForms.V0, Submodule.mem_map, hy]
  · intro x
    have hsum : (∑ g, eC g • aL g) = A'.eOp eC :=
      Finset.sum_congr rfl fun g _ => (mul_smul _ _ _).symm
    rw [hsum]
    change x ∈ A'.typeP P0 ψ ∧ x ∈ LinearMap.range (A'.eOp eC) ↔ _
    refine and_congr ?_ Iff.rfl
    rw [FormsL.mem_typeP]
    refine forall_congr' fun p => ?_
    constructor
    · intro h
      change ((A'.chi (p : Gp))⁻¹ : D.what₂.LLˣ).val • A'.ρ (p : Gp) x = _
      rw [h, smul_smul, ← Units.val_mul, inv_mul_cancel_left]
    · intro h
      have h' : ((A'.chi (p : Gp))⁻¹ : D.what₂.LLˣ).val • A'.ρ (p : Gp) x = ((ψ p : D.what₂.LLˣ) : D.what₂.LL) • x := h
      calc A'.ρ (p : Gp) x = (A'.chi (p : Gp)).val • (((A'.chi (p : Gp))⁻¹ : D.what₂.LLˣ).val • A'.ρ (p : Gp) x) := by
            rw [smul_smul, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_smul]
        _ = _ := by rw [h', smul_smul, Units.val_mul]

end Stage2
end GlobalTheory.CompanionTheory.LatSpan

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.IndefR.NX Formalism.L2.Pj
open Formalism.L2.Rows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.LatSpan

attribute [local instance] algKK

theorem heq_cast {R : Type} {n m : ℕ} (h : n = m) (z : Fin m → R) : HEq z (z ∘ Fin.cast h) := by
  subst h
  rfl

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 4000000 in

theorem lattice_of_lifts : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Y cX) (Rc : Formalism.L2.RecT ex) (P : RowSideFamily ex) (Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)) (Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)) (Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3) (S : Formalism.L2.SG.SpectralTiesReal.STiesR Rc) (B : RealTB Rc P Dcf Spf Zscf S) (_ : RealPins B.Q) (_ : RealRec B.Q) (jD : ∀ j, (Y.MjH j).V →ₗ[D.what₂.LL] B.Q.Sx.WL j) (eM : ∀ w j, (Y.MjH j).V →ₛₗ[ex.nch.embW w] FractionRing (ex.nch.Oe w) ⊗[D.ntw.O (ex.nch.twI w)] D.nexp.Fm (ex.nch.twI w) j (ex.nch.sd w)), NChTie D ex.nch → (∀ (i : Fin D.R.m) (x : (Y.MjH ((i : ℕ) + 1)).V) (y : Fin (Module.finrank D.what₂.LL (B.Q.Rl.toRealDat.WL B.Q.F.lv2 false i)) → D.what₂.LL), HEq ((P.JM.eW i).symm x) y → (B.Q.nexp.fi i).e (jD ((i : ℕ) + 1) x) = jDL B.Q.Rl B.Q.F.lv2 i y) → (∀ w j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (x : (Y.MjH j).V) (n : ℕ) (a : Fin n → D.what₂.LL) (f : Fin n → FmK B.Q.Sx j), jD j x = ∑ k, a k • (show ↥(B.Q.Sx.A j).WK from f k).1 → eM w j x = ∑ k, ex.nch.embW w (a k) ⊗ₜ[D.ntw.O (ex.nch.twI w)] (B.Q.nexp.eF (ex.nch.twI w) j (ex.nch.sd w) h1 h2).symm ((1 : KB B.Q.Sx (ex.nch.twI w) (ex.nch.sd w)) ⊗ₜ[B.Q.Sx.Ks] f k)) → ∀ w j, D.what₂.muAt w ≠ D.what₂.mu0 → 1 ≤ j → j ≤ D.R.m → NForms.IsLatIn (Submodule.span (ex.nch.Oe w) (eM w j '' ((Y.MjH j).L : Set (Y.MjH j).V))) ((((NForms.V0 D (ex.nch.twI w) j (ex.nch.sd w)).restrictScalars (D.ntw.O (ex.nch.twI w))).baseChange (FractionRing (ex.nch.Oe w))).restrictScalars (ex.nch.Oe w)) := by
  intro D L hT Gi Gl Kc Y cX ex Rc P Dcf Spf Zscf S B hPin hRec jD eM hN hjD hSum w j hne h1 h2
  obtain ⟨i, rfl⟩ : ∃ i : Fin D.R.m, j = (i : ℕ) + 1 := ⟨⟨j - 1, by omega⟩, by simp; omega⟩
  have hgrp := P.tied.div.grp
  have hIe : P.I.eG = B.Q.Rl.eG.trans B.Q.cG := hPin.eGtie
  have hC : ∀ h, (Formalism.L2.DIV.idemOf P.A3.A.X).coeff h = ((D.nexp.eLL0 (P.I.eG h) : D.LL0) : D.what₂.LL) := fun h =>
    D.what₂.embLL.injective ((hgrp.e0 h).trans (D.nStage_trivialCharacter_coeff_eq _).symm)
  obtain ⟨e, he1, he2⟩ := stage2 (w := w) hN P.I.eG B.Q.Sx ((i : ℕ) + 1) (B.Q.Rl.FW i) (B.Q.nexp.fi i) (B.fw.ks i)
    (fun s => by rw [hIe]; exact B.Q.nexp.geq i s) (B.Q.nexp.rho _ h1 h2) (B.Q.nexp.chi _ h1 h2)
    (B.Q.nexp.eF _ _ _ h1 h2) (B.Q.nexp.act _ _ _ h1 h2) (fun g => (Formalism.L2.DIV.idemOf P.A3.A.X).coeff g) hC P.P0 P.ψ0⁻¹
    hgrp.lvl0 (fun u hu => by
      obtain ⟨x, hx1, hx2⟩ := hgrp.psi0 u hu (ex.nch.twI w) (ex.nch.sd w)
      exact ⟨x, hx1, hx2⟩)
  have hd := Formalism.IndefR.dWL_eq B.Q i
  have hForm := isKsForm_of_iso (B.Q.nexp.fi i) (B.fw.ks i)
  have heM : ∀ x, eM w ((i : ℕ) + 1) x = e (jD ((i : ℕ) + 1) x) := by
    intro x
    obtain ⟨n, b, hbK, -, -, -, hsp⟩ := hForm
    have hx : jD ((i : ℕ) + 1) x ∈ Submodule.span D.what₂.LL (Set.range b) := hsp ▸ Submodule.mem_top
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun D.what₂.LL).1 hx
    let f : Fin n → FmK B.Q.Sx ((i : ℕ) + 1) := fun k => ⟨b k, hbK k⟩
    have h5 := hSum w ((i : ℕ) + 1) h1 h2 x n a f ha.symm
    rw [h5, ← ha]
    exact (he1 n a f).symm
  have hWg : (B.Q.Rl.FW i).Wgood P.P0 P.ψ0⁻¹ (fun g => (Formalism.L2.DIV.idemOf P.A3.A.X).coeff g) =
      B.Q.Rl.toRealDat.WL B.Q.F.lv2 false i := rfl
  have hrange : Set.range (eM w ((i : ℕ) + 1)) =
      (fun y => e ((B.Q.nexp.fi i).e.symm y)) ''
        ((B.Q.Rl.FW i).Wgood P.P0 P.ψ0⁻¹ (fun g => (Formalism.L2.DIV.idemOf P.A3.A.X).coeff g) : Set _) := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨(B.Q.nexp.fi i).e (jD ((i : ℕ) + 1) x), ?_, ?_⟩
      · rw [hjD i x _ (heq_cast hd ((P.JM.eW i).symm x))]
        rw [SetLike.mem_coe, hWg]
        simp only [Formalism.IndefR.NX.jDL, Fintype.linearCombination_apply]
        exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Module.finBasis D.what₂.LL _ k).2
      · simp only [LinearEquiv.symm_apply_apply, heM]
    · rintro ⟨y, hy, rfl⟩
      rw [SetLike.mem_coe, hWg] at hy
      let Bs := Module.finBasis D.what₂.LL (B.Q.Rl.toRealDat.WL B.Q.F.lv2 false i)
      let z : Fin (Module.finrank D.what₂.LL (B.Q.Rl.toRealDat.WL B.Q.F.lv2 false i)) → D.what₂.LL := Bs.equivFun ⟨y, hy⟩
      let x := P.JM.eW i (z ∘ Fin.cast hd.symm)
      have hH : HEq ((P.JM.eW i).symm x) z := by
        simp only [x, LinearEquiv.symm_apply_apply]
        exact (heq_cast hd.symm z).symm
      have h6 := hjD i x z hH
      have h7 : Formalism.IndefR.NX.jDL B.Q.Rl B.Q.F.lv2 i z = y := by
        simp only [Formalism.IndefR.NX.jDL, Fintype.linearCombination_apply]
        have h8 := Bs.sum_equivFun ⟨y, hy⟩
        have h9 : ((∑ k, Bs.equivFun ⟨y, hy⟩ k • Bs k : B.Q.Rl.toRealDat.WL B.Q.F.lv2 false i) : Fin (B.Q.Rl.nW i) → D.what₂.LL) = y :=
          congrArg Subtype.val h8
        rw [AddSubmonoidClass.coe_finset_sum] at h9
        exact h9
      refine ⟨x, ?_⟩
      rw [heM]
      change e _ = e ((B.Q.nexp.fi i).e.symm y)
      rw [← h7, ← h6, LinearEquiv.symm_apply_apply]
  refine isLatIn_span (ex.nch.embW w) (integers_embed _) (eM w ((i : ℕ) + 1)) (Y.MjH ((i : ℕ) + 1)).L
    (Y.MjH_good _).2.1 (Y.MjH_good _).2.2 _ ?_
  rw [hrange]
  exact he2

end GlobalTheory.CompanionTheory.LatSpan

end
end
end
end

end GroupAverageFixedPoints
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.IndefR.NX Formalism.L2.Pj
open Formalism.L2.Rows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem _root_.GlobalTheory.Adopt.lattice_family_adoption_second : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Y cX) (Rc : Formalism.L2.RecT ex) (P : RowSideFamily ex) (Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)) (Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)) (Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3) (S : Formalism.L2.SG.SpectralTiesReal.STiesR Rc) (B : RealTB Rc P Dcf Spf Zscf S) (_ : RealPins B.Q) (_ : RealRec B.Q) (jD : ∀ j, (Y.MjH j).V →ₗ[D.what₂.LL] B.Q.Sx.WL j) (eM : ∀ w j, (Y.MjH j).V →ₛₗ[ex.nch.embW w] FractionRing (ex.nch.Oe w) ⊗[D.ntw.O (ex.nch.twI w)] D.nexp.Fm (ex.nch.twI w) j (ex.nch.sd w)), NChTie D ex.nch → (∀ (i : Fin D.R.m) (x : (Y.MjH ((i : ℕ) + 1)).V) (y : Fin (Module.finrank D.what₂.LL (B.Q.Rl.toRealDat.WL B.Q.F.lv2 false i)) → D.what₂.LL), HEq ((P.JM.eW i).symm x) y → (B.Q.nexp.fi i).e (jD ((i : ℕ) + 1) x) = jDL B.Q.Rl B.Q.F.lv2 i y) → (∀ w j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (x : (Y.MjH j).V) (n : ℕ) (a : Fin n → D.what₂.LL) (f : Fin n → FmK B.Q.Sx j), jD j x = ∑ k, a k • (show ↥(B.Q.Sx.A j).WK from f k).1 → eM w j x = ∑ k, ex.nch.embW w (a k) ⊗ₜ[D.ntw.O (ex.nch.twI w)] (B.Q.nexp.eF (ex.nch.twI w) j (ex.nch.sd w) h1 h2).symm ((1 : KB B.Q.Sx (ex.nch.twI w) (ex.nch.sd w)) ⊗ₜ[B.Q.Sx.Ks] f k)) → ∀ w j, D.what₂.muAt w ≠ D.what₂.mu0 → 1 ≤ j → j ≤ D.R.m → NForms.IsLatIn (Submodule.span (ex.nch.Oe w) (eM w j '' ((Y.MjH j).L : Set (Y.MjH j).V))) ((((NForms.V0 D (ex.nch.twI w) j (ex.nch.sd w)).restrictScalars (D.ntw.O (ex.nch.twI w))).baseChange (FractionRing (ex.nch.Oe w))).restrictScalars (ex.nch.Oe w)) := by
  first | exact @GroupAverageFixedPoints.GlobalTheory.CompanionTheory.LatSpan.lattice_of_lifts | exact GroupAverageFixedPoints.GlobalTheory.CompanionTheory.LatSpan.lattice_of_lifts | (intros; apply GroupAverageFixedPoints.GlobalTheory.CompanionTheory.LatSpan.lattice_of_lifts <;> assumption)

end
