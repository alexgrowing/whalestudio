import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.DiagonalQuotientEigen
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompletionLines
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InjectiveOfSpan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffEqOfApply
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSubstInvariants
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvrComplete
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrimitiveRootCoeffRingOfGood
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemXSmulOfProjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBasisAddPiSmul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMatrixFrobenius

noncomputable section

namespace GlobalTheory.SenLines

open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.AdmLoc GlobalTheory.IndefiniteRowSideFullHecke.DiagonalQuotientEigen TensorProduct
open GlobalTheory.WachTie.MatF

section Algebra

theorem quot_equiv {O P : Type} [CommRing O] [AddCommGroup P] [Module O P] (P' : Submodule O P) {r : ℕ} (m : ℕ)
    (θ : (Fin r → O⟦X⟧) ≃ₗ[O] P) (h : ∀ c, θ c ∈ P' ↔ ∀ k, (X : O⟦X⟧) ^ m ∣ c k) :
    Nonempty ((P ⧸ P') ≃ₗ[O] (Fin m × Fin r → O)) := by
  let tr : (Fin r → O⟦X⟧) →ₗ[O] (Fin m × Fin r → O) :=
    LinearMap.pi fun x => (coeff (x.1 : ℕ)).comp (LinearMap.proj x.2)
  let f : P →ₗ[O] (Fin m × Fin r → O) := tr.comp θ.symm.toLinearMap
  have hs : Function.Surjective f := by
    intro y
    refine ⟨θ fun k => PowerSeries.mk fun a => if ha : a < m then y (⟨a, ha⟩, k) else 0, ?_⟩
    funext x
    simp [f, tr]
  have hk : P' = LinearMap.ker f := by
    ext x
    obtain ⟨c, rfl⟩ := θ.surjective x
    rw [h, LinearMap.mem_ker, funext_iff]
    simp only [X_pow_dvd_iff, f, tr, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
      LinearMap.pi_apply, LinearMap.proj_apply, Pi.zero_apply]
    exact ⟨fun H x => H x.2 x.1 x.1.2, fun H k a ha => H (⟨a, ha⟩, k)⟩
  exact ⟨(Submodule.quotEquivOfEq _ _ hk).trans (f.quotKerEquivOfSurjective hs)⟩

theorem charpoly_of_diagWith {F M : Type} [Field F] [AddCommGroup M] [Module F M] [Module.Finite F M]
    (f : M →ₗ[F] M) (S : Multiset F) (h : DiagWith f S) :
    f.charpoly = (S.map fun s => Polynomial.X - Polynomial.C s).prod := by
  obtain ⟨m, b, e, he, rfl⟩ := h
  have hm : LinearMap.toMatrix b b f = Matrix.diagonal e := by
    ext a c
    rw [LinearMap.toMatrix_apply, he, map_smul, b.repr_self, Matrix.diagonal_apply]
    by_cases hac : a = c
    · subst hac; simp
    · simp [hac, Finsupp.single_eq_of_ne hac]
  rw [← LinearMap.charpoly_toMatrix f b, hm, Matrix.charpoly_diagonal, Multiset.map_map]
  rfl

theorem eigWith_of_diagWith {O F k Q : Type} [CommRing O] [Field F] [Field k] [Algebra O F] [Algebra O k]
    [AddCommGroup Q] [Module O Q] [Module.Free O Q] [Module.Finite O Q]
    (hinj : Function.Injective (algebraMap O F)) (f : Q →ₗ[O] Q) (S : Multiset O)
    (h : DiagWith (f.baseChange F) (S.map (algebraMap O F))) :
    EigWith (f.baseChange k) (S.map (algebraMap O k)) := by
  have h1 := charpoly_of_diagWith _ _ h
  have key : ∀ (E : Type) [Field E] [Algebra O E],
      ((S.map (algebraMap O E)).map fun s => Polynomial.X - Polynomial.C s).prod =
        (S.map fun s => Polynomial.X - Polynomial.C s).prod.map (algebraMap O E) := by
    intro E _ _
    rw [Polynomial.map_multiset_prod, Multiset.map_map, Multiset.map_map]
    congr 2
    funext s
    simp
  rw [key, LinearMap.charpoly_baseChange] at h1
  refine ⟨inferInstance, ?_⟩
  rw [key, LinearMap.charpoly_baseChange, Polynomial.map_injective _ hinj h1]

theorem exists_cc {O F : Type} [CommRing O] [Field F] [CharZero F] [Algebra O F] (l : ℕ) (hl : l ≠ 0)
    (hu : IsUnit (1 + (l : O))) (a : ℤ) :
    ∃ c : O, algebraMap O F c = ((cc l a : ℚ) : F) ∧ (l : O) ∣ c + a := by
  have hl' : (l : F) ≠ 0 := Nat.cast_ne_zero.2 hl
  have h1 : (1 + (l : F)) ≠ 0 := by exact_mod_cast (by omega : 1 + l ≠ 0)
  obtain ⟨w, hw⟩ := hu.exists_right_inv
  have hw' : algebraMap O F w = (1 + (l : F))⁻¹ := by
    have := congrArg (algebraMap O F) hw
    rw [map_mul, map_add, map_one, map_natCast] at this
    exact (eq_inv_of_mul_eq_one_right this)
  induction a using Int.induction_on with
  | zero => exact ⟨0, by simp [cc], by simp⟩
  | succ a ih =>
    obtain ⟨c, hc, d, hd⟩ := ih
    refine ⟨(1 + l) * c - 1, ?_, d + c, ?_⟩
    · rw [map_sub, map_mul, hc]
      simp only [cc, map_add, map_one, map_natCast]
      push_cast
      rw [zpow_add_one₀ h1]
      field_simp
      ring
    · push_cast at hd ⊢
      linear_combination hd
  | pred a ih =>
    obtain ⟨c, hc, d, hd⟩ := ih
    refine ⟨(c + 1) * w, ?_, d - (c + 1) * w, ?_⟩
    · rw [map_mul, map_add, hc, hw']
      simp only [cc, map_one]
      push_cast
      rw [zpow_sub_one₀ h1]
      field_simp
      ring
    · push_cast at hd ⊢
      linear_combination hd + (c + 1) * hw

theorem exists_factor {O P D : Type} [CommRing O] [AddCommGroup P] [Module O P] [AddCommGroup D] [Module O D]
    (f g : P →ₗ[O] D) (hf : Function.Injective f) (h : ∀ x, ∃ y, f y = g x) :
    ∃ nb : P →ₗ[O] P, ∀ x, f (nb x) = g x := by
  refine ⟨(LinearEquiv.ofInjective f hf).symm.toLinearMap.comp (g.codRestrict (LinearMap.range f) h),
    fun x => ?_⟩
  have := (LinearEquiv.ofInjective f hf).apply_symm_apply (g.codRestrict (LinearMap.range f) h x)
  exact congrArg Subtype.val this

theorem dvd_zpow_sub_one {R : Type} [CommRing R] (x : R) (s : Rˣ) (h : x ∣ (s : R) - 1) (j : ℤ) :
    x ∣ ((s ^ j : Rˣ) : R) - 1 := by
  have key : ∀ t : Rˣ, x ∣ (t : R) - 1 ↔
      Units.map (Ideal.Quotient.mk (Ideal.span {x})).toMonoidHom t = 1 := fun t => by
    rw [Units.ext_iff, ← Ideal.mem_span_singleton, ← Ideal.Quotient.eq]
    simp
  rw [key] at h ⊢
  rw [map_zpow, h, one_zpow]

end Algebra

section Series

theorem exists_mu {F : Type} [Field F] (χ : F) (hχ : χ ≠ 0) (η m S A : (F⟦X⟧)ˣ) (j w : ℤ)
    (h1 : (η : F⟦X⟧) * S = C χ * rescale χ (η : F⟦X⟧))
    (h2 : (A : F⟦X⟧) * m = C (χ ^ (-w)) * rescale χ (m : F⟦X⟧)) :
    ∃ μ : (F⟦X⟧)ˣ, ((S ^ j : (F⟦X⟧)ˣ) : F⟦X⟧) * μ = C (χ ^ (j + w)) * A * rescale χ (μ : F⟦X⟧) := by
  let R : (F⟦X⟧)ˣ →* (F⟦X⟧)ˣ := Units.map (rescale χ).toMonoidHom
  let c : (F⟦X⟧)ˣ := Units.map (C : F →+* F⟦X⟧).toMonoidHom (Units.mk0 χ hχ)
  have hc : ∀ k : ℤ, ((c ^ k : (F⟦X⟧)ˣ) : F⟦X⟧) = C (χ ^ k) := fun k => by
    rw [← map_zpow]
    change C (((Units.mk0 χ hχ) ^ k : Fˣ) : F) = _
    rw [Units.val_zpow_eq_zpow_val, Units.val_mk0]
  have e1 : η * S = c * R η := Units.ext h1
  have e2 : A * m = c ^ (-w) * R m := Units.ext (by rw [Units.val_mul, Units.val_mul, hc]; exact h2)
  have e3 : S ^ j * (η ^ j * m⁻¹) = c ^ (j + w) * A * R (η ^ j * m⁻¹) := by
    rw [← mul_assoc, ← mul_zpow, mul_comm S, e1, eq_mul_inv_of_mul_eq e2, map_mul, map_zpow, map_inv,
      mul_zpow, zpow_add, zpow_neg]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  refine ⟨η ^ j * m⁻¹, ?_⟩
  have := congrArg Units.val e3
  rw [Units.val_mul, Units.val_mul (c ^ (j + w) * A), Units.val_mul (c ^ (j + w)), hc] at this
  exact this

theorem eigMs_eq {F : Type} [Field F] [CharZero F] (l : ℕ) {r : ℕ} (u : Fin r → ℤ) (w j j' : ℤ) :
    eigMs F l (Finset.univ.val.map u) w j j' =
      (Finset.univ : Finset (Fin r × Fin (j' - j).toNat)).val.map fun x =>
        ((1 + (l : F)) ^ (j + w - u x.1) * (1 + (l : F)) ^ (x.2 : ℕ) - 1) / (-(l : F)) := by
  have h1 : (1 + (l : F)) ≠ 0 := by exact_mod_cast (by omega : 1 + l ≠ 0)
  rw [← Finset.univ_product_univ, Finset.product_val, eigMs, Multiset.bind_map]
  rw [show ∀ (s : Multiset (Fin r)) (t : Multiset (Fin (j' - j).toNat)),
    s ×ˢ t = s.bind fun a => t.map (Prod.mk a) from fun _ _ => rfl, Multiset.map_bind]
  refine Multiset.bind_congr fun k _ => ?_
  rw [Int.Ico_eq_finset_map, ← Nat.Iio_eq_range, ← Fin.map_valEmbedding_univ]
  simp only [Finset.map_val, Multiset.map_map]
  refine Multiset.map_congr rfl fun x _ => ?_
  simp only [cc, Function.comp, Function.Embedding.trans_apply, Fin.valEmbedding_apply,
    Nat.castEmbedding_apply, addLeftEmbedding_apply]
  push_cast
  rw [← zpow_natCast, ← zpow_add₀ h1]
  congr 3
  ring

end Series

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)
    (J : O⟦X⟧ →ₐ[O] O⟦X⟧) {r : ℕ} (b : Module.Basis (Fin r) (LetA O n) ↥(W.N T)) (i : ZMod n)

def th : (Fin r → O⟦X⟧) →ₗ[O] W.DD T where
  toFun c := ∑ k, (Pi.single i (J (c k)) : LetA O n) • (b k : W.DD T)
  map_add' c d := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Pi.add_apply, map_add, Pi.single_add, add_smul]
  map_smul' c d := by
    rw [RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Pi.smul_apply, map_smul, Pi.single_smul, smul_assoc]

theorem th_apply (c : Fin r → O⟦X⟧) :
    th W T J b i c = ∑ k, (Pi.single i (J (c k)) : LetA O n) • (b k : W.DD T) := rfl

theorem mul_single (a : LetA O n) (x : O⟦X⟧) : a * Pi.single i x = Pi.single i (a i * x) := by
  funext m
  by_cases h : m = i
  · subst h; simp
  · simp [Pi.single_eq_of_ne h]

theorem smul_th_eq (a : LetA O n) (c : Fin r → O⟦X⟧) :
    a • th W T J b i c = ∑ k, (Pi.single i (a i * J (c k)) : LetA O n) • (b k : W.DD T) := by
  rw [th_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_smul, mul_single]

theorem smul_th {a : LetA O n} {e : O⟦X⟧} (h : a i = J e) (c : Fin r → O⟦X⟧) :
    a • th W T J b i c = th W T J b i (e • c) := by
  rw [smul_th_eq, th_apply]
  simp only [h, Pi.smul_apply, smul_eq_mul, map_mul]

theorem th_coord {c : Fin r → O⟦X⟧} {a : Fin r → LetA O n}
    (h : th W T J b i c = ∑ k, a k • (b k : W.DD T)) (k : Fin r) : J (c k) = a k i := by
  have := congrFun (congrFun (coord_unique W T b _ _ h) k) i
  simpa using this

theorem th_inj (hJ : Function.Injective J) : Function.Injective (th W T J b i) := by
  intro c d h
  funext k
  have := th_coord W T J b i (h.trans (th_apply W T J b i d)) k
  simpa using hJ (by simpa using this)

theorem th_mem_N (c : Fin r → O⟦X⟧) : th W T J b i c ∈ W.N T := by
  rw [th_apply]
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (b k).2

theorem γA_single (g : W.Gam) (x : O⟦X⟧) : W.γA g (Pi.single i x) = Pi.single i (W.γ₀ g x) := by
  funext m
  change W.γ₀ g ((Pi.single i x : LetA O n) m) = _
  by_cases h : m = i
  · subst h; simp
  · simp [Pi.single_eq_of_ne h]

theorem mem_NΔl_iff (hr : ∀ a, (∃ b, J b = a) ↔ ∀ δ ∈ W.DelF, W.γ₀ δ a = a)
    (hb : ∀ k, (b k : W.DD T) ∈ W.NΔ T) (x : W.DD T) : x ∈ NΔl W T i ↔ ∃ c, th W T J b i c = x := by
  constructor
  · rintro ⟨⟨hx, hΔ⟩, y, hy, hyx⟩
    obtain ⟨a, ha⟩ := exists_coord W T b y hy
    have hxa : x = ∑ k, (Pi.single i (a k i) : LetA O n) • (b k : W.DD T) := by
      rw [← hyx, ha]
      simp only [LinearMap.smul_apply, LinearMap.id_apply, Finset.smul_sum, smul_smul]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [mul_comm, letE, mul_single, mul_one]
    have hc : ∀ k, ∃ c, J c = a k i := fun k => (hr _).2 fun δ hδ => by
      have h1 := hΔ δ hδ
      rw [hxa, map_sum] at h1
      simp only [γD_smulA, γA_single, (hb _).2 δ hδ] at h1
      simpa using congrFun (congrFun (coord_unique W T b _ _ h1) k) i
    choose c hc using hc
    exact ⟨c, by rw [hxa, th_apply]; simp only [hc]⟩
  · rintro ⟨c, rfl⟩
    refine ⟨⟨th_mem_N W T J b i c, fun δ hδ => ?_⟩, th W T J b i c, th_mem_N W T J b i c, ?_⟩
    · rw [th_apply, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [γD_smulA, γA_single, (hb _).2 δ hδ, (hr _).1 ⟨_, rfl⟩ δ hδ]
    · change (letE i : LetA O n) • th W T J b i c = _
      rw [smul_th W T J b i (e := 1) (by simp [letE]), one_smul]

theorem γD_mem_NΔl (g : W.Gam) {x : W.DD T} (hx : x ∈ NΔl W T i) : W.γD T g x ∈ NΔl W T i := by
  obtain ⟨⟨hx, hΔ⟩, y, hy, hyx⟩ := hx
  refine ⟨⟨W.N_Γ T g x hx, fun δ hδ => by rw [← W.γD_mul, mul_comm, W.γD_mul, hΔ δ hδ]⟩,
    W.γD T g y, W.N_Γ T g y hy, ?_⟩
  rw [← hyx]
  change (letE i : LetA O n) • W.γD T g y = W.γD T g ((letE i : LetA O n) • y)
  rw [γD_smulA, letE, γA_single, map_one]

theorem γD_th {g : W.Gam} (hJ : QFrame W g J) (hb : ∀ k, (b k : W.DD T) ∈ W.NΔ T) (c : Fin r → O⟦X⟧) :
    ∃ c₁ : Fin r → O⟦X⟧, W.γD T g (th W T J b i c) =
      th W T J b i (c + (X - ((PD.p : ℕ) : O⟦X⟧)) • c₁) := by
  obtain ⟨-, hr, -, h0, -⟩ := hJ
  have hc := (mem_NΔl_iff W T J b i hr hb _).2 ⟨c, rfl⟩
  obtain ⟨c', hc'⟩ := (mem_NΔl_iff W T J b i hr hb _).1
    ((NΔl W T i).sub_mem (γD_mem_NΔl W T i g hc) hc)
  obtain ⟨y, hy, hy'⟩ := W.N_π T g _ (th_mem_N W T J b i c)
  obtain ⟨a, ha⟩ := exists_coord W T b y hy
  have h1 : th W T J b i c' = ∑ k, (letπ * a k) • (b k : W.DD T) := by
    rw [hc', hy', ha, Finset.smul_sum]
    simp only [smul_smul]
  have h2 : ∀ k, X - ((PD.p : ℕ) : O⟦X⟧) ∣ c' k := fun k => h0 _ (by
    rw [th_coord W T J b i h1 k]; simp [letπ])
  choose c₁ hc₁ using h2
  refine ⟨c₁, ?_⟩
  have : (X - ((PD.p : ℕ) : O⟦X⟧)) • c₁ = c' := funext fun k => (hc₁ k).symm
  rw [this, map_add, hc']
  abel

theorem mem_qN_iff (Qu : W.EEˣ) (hQ : (Qu : W.EE) = algebraMap (LetA O n) W.EE (qΔ W)) (j : ℤ) (x : W.DD T) :
    x ∈ qN W T i j ↔ ∃ y ∈ NΔl W T i, ((Qu ^ j : W.EEˣ) : W.EE) • y = x := by
  have hm : ∀ (k : ℕ) (z : W.DD T), mulD W T (qΔ W ^ k) z = (Qu ^ (k : ℤ)) • z := fun k z => by
    change (qΔ W ^ k) • z = ((Qu ^ (k : ℤ) : W.EEˣ) : W.EE) • z
    rw [zpow_natCast, Units.val_pow_eq_pow_val, hQ, ← map_pow, algebraMap_smul]
  simp only [qN, Submodule.mem_comap, Submodule.mem_map, hm]
  refine exists_congr fun y => and_congr_right fun _ => ?_
  change _ ↔ (Qu ^ j) • y = x
  rw [← inv_smul_eq_iff, smul_smul, ← zpow_neg, ← zpow_add]
  rw [show -((-j).toNat : ℤ) + (j.toNat : ℤ) = j by omega]

def cst : O⟦X⟧ →ₐ[O] LetA O n := AlgHom.pi fun _ => J

omit W T b in
theorem cst_apply (c : O⟦X⟧) : (cst J c : LetA O n) i = J c := rfl

def abelian₂ (ζ : LL) : O⟦X⟧ →ₐ[O] LL⟦X⟧ := (W.lev i ζ).comp (cst J)

theorem lev_eq (ζ : LL) {a : LetA O n} {e : O⟦X⟧} (h : a i = J e) : W.lev i ζ a = abelian₂ W J i ζ e := by
  have := W.lev_letter i ζ (a - cst J e) (by rw [Pi.sub_apply, h, cst_apply, sub_self])
  rw [map_sub, sub_eq_zero] at this
  exact this

theorem exists_matrix (ζ : LL) {r' : ℕ} (e : ↥(W.N T) →+ (Fin r' → LL⟦X⟧))
    (he : ∀ a x, e (a • x) = W.lev i ζ a • e x) :
    ∃ M : Matrix (Fin r') (Fin r) LL⟦X⟧,
      (Submodule.span LL⟦X⟧ (Set.range e) = ⊤ → Function.Surjective M.mulVec) ∧
      ∀ c, e ⟨th W T J b i c, th_mem_N W T J b i c⟩ = M.mulVec fun k => abelian₂ W J i ζ (c k) := by
  let M : Matrix (Fin r') (Fin r) LL⟦X⟧ := Matrix.of fun u k => e (b k) u
  have h1 : ∀ a : Fin r → LetA O n, e (∑ k, a k • b k) = M.mulVec fun k => W.lev i ζ (a k) := by
    intro a
    funext u
    simp [M, map_sum, he, Matrix.mulVec, dotProduct, mul_comm]
  refine ⟨M, fun hs => ?_, fun c => ?_⟩
  · have : Submodule.span LL⟦X⟧ (Set.range e) ≤ LinearMap.range M.mulVecLin := by
      rw [Submodule.span_le]
      rintro _ ⟨x, rfl⟩
      exact ⟨fun k => W.lev i ζ (b.repr x k), by rw [Matrix.mulVecLin_apply, ← h1, b.sum_repr]⟩
    intro y
    exact this (hs ▸ Submodule.mem_top)
  · have : (⟨th W T J b i c, th_mem_N W T J b i c⟩ : ↥(W.N T)) =
        ∑ k, (Pi.single i (J (c k)) : LetA O n) • b k := by
      apply Subtype.ext
      simp [th_apply]
    rw [this, h1]
    congr 1
    funext k
    exact lev_eq W J i ζ (by simp)

theorem exists_theta {g : W.Gam} (hJ : QFrame W g J) (hb : ∀ k, (b k : W.DD T) ∈ W.NΔ T)
    (Qu : W.EEˣ) (hQ : (Qu : W.EE) = algebraMap (LetA O n) W.EE (qΔ W)) (j : ℤ) :
    ∃ θ : (Fin r → O⟦X⟧) ≃ₗ[O] ↥(qN W T i j), ∀ c, (θ c : W.DD T) = (Qu ^ j) • th W T J b i c := by
  let f : (Fin r → O⟦X⟧) →ₗ[O] W.DD T :=
    (Algebra.lsmul O O (W.DD T) ((Qu ^ j : W.EEˣ) : W.EE)).comp (th W T J b i)
  have hf : ∀ c, f c = (Qu ^ j) • th W T J b i c := fun _ => rfl
  have hm : ∀ c, f c ∈ qN W T i j := fun c =>
    (mem_qN_iff W T i Qu hQ j _).2 ⟨_, (mem_NΔl_iff W T J b i hJ.2.1 hb _).2 ⟨c, rfl⟩, rfl⟩
  refine ⟨LinearEquiv.ofBijective (f.codRestrict _ hm) ⟨fun c d h => ?_, fun x => ?_⟩, fun _ => rfl⟩
  · have h1 : f c = f d := congrArg Subtype.val h
    rw [hf, hf] at h1
    exact th_inj W T J b i hJ.1 (MulAction.injective _ h1)
  · obtain ⟨y, hy, hx⟩ := (mem_qN_iff W T i Qu hQ j _).1 x.2
    obtain ⟨c, rfl⟩ := (mem_NΔl_iff W T J b i hJ.2.1 hb _).1 hy
    exact ⟨c, Subtype.ext hx⟩

theorem smul_unit_comm (a : LetA O n) (u : W.EEˣ) (x : W.DD T) : a • u • x = u • a • x := by
  rw [← algebraMap_smul W.EE a, ← algebraMap_smul W.EE a x, Units.smul_def, Units.smul_def, smul_comm]

theorem qΔ_eq {g : W.Gam} (hJ : QFrame W g J) : qΔ W = cst J X := funext fun _ => hJ.2.2.1.symm

theorem zpow_th {g : W.Gam} (hJ : QFrame W g J)
    (Qu : W.EEˣ) (hQ : (Qu : W.EE) = algebraMap (LetA O n) W.EE (qΔ W)) {j j' : ℤ} (hj : j ≤ j')
    (d : Fin r → O⟦X⟧) : (Qu ^ j') • th W T J b i d =
      (Qu ^ j) • th W T J b i ((X : O⟦X⟧) ^ (j' - j).toNat • d) := by
  rw [← smul_th W T J b i (a := qΔ W ^ (j' - j).toNat) (by rw [qΔ_eq W J hJ, ← map_pow, cst_apply]),
    ← algebraMap_smul W.EE, map_pow, ← hQ, ← Units.val_pow_eq_pow_val, ← Units.smul_def, smul_smul,
    ← zpow_natCast, ← zpow_add]
  rw [show j + ((j' - j).toNat : ℤ) = j' by omega]

theorem theta_mem {g : W.Gam} (hJ : QFrame W g J) (hb : ∀ k, (b k : W.DD T) ∈ W.NΔ T)
    (Qu : W.EEˣ) (hQ : (Qu : W.EE) = algebraMap (LetA O n) W.EE (qΔ W)) {j j' : ℤ} (hj : j ≤ j')
    (c : Fin r → O⟦X⟧) :
    (Qu ^ j) • th W T J b i c ∈ qN W T i j' ↔ ∀ k, (X : O⟦X⟧) ^ (j' - j).toNat ∣ c k := by
  have h1 := zpow_th W T J b i hJ Qu hQ hj
  rw [mem_qN_iff W T i Qu hQ]
  constructor
  · rintro ⟨y, hy, hx⟩ k
    obtain ⟨d, rfl⟩ := (mem_NΔl_iff W T J b i hJ.2.1 hb _).1 hy
    have h2 := th_inj W T J b i hJ.1 (MulAction.injective _ ((h1 d).symm.trans hx))
    exact ⟨d k, (congrFun h2 k).symm⟩
  · intro h
    choose d hd using h
    refine ⟨_, (mem_NΔl_iff W T J b i hJ.2.1 hb _).2 ⟨d, rfl⟩, (h1 d).trans ?_⟩
    congr 2
    exact funext fun k => (hd k).symm

theorem γD_zpow {g : W.Gam} (hJ : QFrame W g J) (s : (O⟦X⟧)ˣ) (hs : W.γ₀ g (J X) = J X * J s)
    (Qu : W.EEˣ) (hQ : (Qu : W.EE) = algebraMap (LetA O n) W.EE (qΔ W)) (j : ℤ) (x : W.DD T) :
    W.γD T g ((Qu ^ j) • x) = (Qu ^ j) • (cst J ((s ^ j : (O⟦X⟧)ˣ) : O⟦X⟧) : LetA O n) • W.γD T g x := by
  let φ : O⟦X⟧ →* W.EE := ((algebraMap (LetA O n) W.EE).comp (cst J).toRingHom).toMonoidHom
  let ψ : W.EE →* W.EE := (W.γE g).toRingHom.toMonoidHom
  have h1 : Units.map ψ Qu = Qu * Units.map φ s := by
    apply Units.ext
    change W.γE g Qu = Qu * algebraMap (LetA O n) W.EE (cst J s)
    rw [hQ, W.γE_ext, ← map_mul, qΔ_eq W J hJ]
    congr 1
    exact funext fun _ => hs
  have h2 : Units.map ψ (Qu ^ j) = Qu ^ j * Units.map φ (s ^ j) := by
    rw [map_zpow, map_zpow, h1, mul_zpow]
  have h3 : W.γE g ((Qu ^ j : W.EEˣ) : W.EE) = ((Qu ^ j : W.EEˣ) : W.EE) *
      algebraMap (LetA O n) W.EE (cst J ((s ^ j : (O⟦X⟧)ˣ) : O⟦X⟧)) := congrArg Units.val h2
  rw [Units.smul_def, W.γD_smul, h3, mul_smul, algebraMap_smul, Units.smul_def]

theorem nab_iff {g : W.Gam} (hJ : QFrame W g J) (s : (O⟦X⟧)ˣ) (hs : W.γ₀ g (J X) = J X * J s)
    (Qu : W.EEˣ) (hQ : (Qu : W.EE) = algebraMap (LetA O n) W.EE (qΔ W)) (j : ℤ)
    {a : LetA O n} {a₀ : O⟦X⟧} (ha : a i = J a₀) {c c' d : Fin r → O⟦X⟧}
    (hd : W.γD T g (th W T J b i c) = th W T J b i d) :
    (a * W.π₀) • (Qu ^ j) • th W T J b i c' =
        W.γD T g ((Qu ^ j) • th W T J b i c) - a • (Qu ^ j) • th W T J b i c ↔
      (a₀ * (X - ((PD.p : ℕ) : O⟦X⟧))) • c' = ((s ^ j : (O⟦X⟧)ˣ) : O⟦X⟧) • d - a₀ • c := by
  have h1 : (a * W.π₀) i = J (a₀ * (X - ((PD.p : ℕ) : O⟦X⟧))) := by
    rw [map_mul, map_sub, hJ.2.2.1, map_natCast, add_sub_cancel_right, Pi.mul_apply, ha]
    rfl
  rw [γD_zpow W T J hJ s hs Qu hQ, smul_unit_comm, smul_unit_comm, hd, smul_th W T J b i h1,
    smul_th W T J b i ha, smul_th W T J b i (cst_apply J i _), ← smul_sub, ← map_sub,
    (MulAction.injective _).eq_iff, (th_inj W T J b i hJ.1).eq_iff]

theorem exists_eta [CharZero LL] {g : W.Gam} (hJ : QFrame W g J) (ζ : LL) (hζ : IsPrimitiveRoot ζ PD.p) :
    ∃ η : (LL⟦X⟧)ˣ, abelian₂ W J i ζ X = X * (η : LL⟦X⟧) := by
  obtain ⟨E, hE0, hE1, hE⟩ := W.lev_π i ζ ⟨1, by rwa [pow_one]⟩
  obtain ⟨w, hw⟩ := hJ.2.2.2.2.2.1
  have hp := PD.hp
  obtain ⟨E', hE'⟩ : (X : LL⟦X⟧) ∣ E - 1 := by rw [X_dvd_iff]; simp [hE0]
  have hu1 : IsUnit E' := by
    have h1 := congrArg (coeff 0) hE1
    have h2 := congrArg (coeff 1) hE'
    rw [coeff_derivative, coeff_zero_eq_constantCoeff, hE0] at h1
    rw [coeff_succ_X_mul, coeff_zero_eq_constantCoeff, map_sub, coeff_one, if_neg one_ne_zero] at h2
    rw [isUnit_iff_constantCoeff, ← h2]
    simp only [Nat.cast_zero, zero_add, mul_one] at h1
    simp [h1]
  have hu2 : IsUnit (∑ k ∈ Finset.range PD.p, E ^ k) := by
    rw [isUnit_iff_constantCoeff]
    simp [hE0, hp.ne_zero]
  have hu3 : IsUnit (W.lev i ζ letπ) := by
    rw [eq_sub_of_add_eq' hE, isUnit_iff_constantCoeff]
    simpa [hE0, sub_eq_zero] using hζ.ne_one hp.one_lt
  have hu4 : IsUnit (W.lev i ζ fun _ => (w : O⟦X⟧)) := IsUnit.map _ (Pi.isUnit_iff.2 fun _ => w.isUnit)
  have h3 : (letπ : LetA O n) * (cst J X * fun _ => (w : O⟦X⟧)) = (1 + letπ) ^ PD.p - 1 :=
    funext fun _ => by
      change X * (J X * (w : O⟦X⟧)) = (1 + X) ^ PD.p - 1
      rw [hw, W.q₀_def]
  have h4 := congrArg (W.lev i ζ) h3
  rw [map_mul, map_mul, map_sub, map_pow, map_add, map_one, hE, mul_pow, ← map_pow, hζ.pow_eq_one, map_one,
    one_mul, ← mul_geom_sum, hE'] at h4
  refine ⟨(hu1.mul hu2).unit * ((hu3.mul hu4).unit)⁻¹, ?_⟩
  rw [Units.val_mul, ← mul_assoc, Units.eq_mul_inv_iff_mul_eq, IsUnit.unit_spec, IsUnit.unit_spec]
  change W.lev i ζ (cst J X) * _ = _
  linear_combination h4

theorem diagQuot [IsDomain O] [CharZero LL] (hinj : Function.Injective (algebraMap O LL))
    {g : W.Gam} (hJ : QFrame W g J) (b : Module.Basis (Fin (Module.finrank LL T.V)) (LetA O n) ↥(W.N T))
    (hb : ∀ k, (b k : W.DD T) ∈ W.NΔ T) (ζ : LL) (hζ : IsPrimitiveRoot ζ PD.p)
    (hρ : ∀ f, W.lev i ζ (W.γA g f) = rescale (1 + (PD.p : LL)) (W.lev i ζ f))
    (u : Fin (Module.finrank LL T.V) → ℤ) (e : ↥(W.N T) →+ (Fin (Module.finrank LL T.V) → LL⟦X⟧))
    (he : ∀ a x, e (a • x) = W.lev i ζ a • e x) (hsp : Submodule.span LL⟦X⟧ (Set.range e) = ⊤)
    (hγ : ∀ (x : ↥(W.N T)) hx k, e ⟨W.γD T g x, hx⟩ k =
      C ((1 + (PD.p : LL)) ^ (-u k)) * rescale (1 + (PD.p : LL)) (e x k))
    (a : LetA O n) (a₀ : (O⟦X⟧)ˣ) (ha : a i = J a₀) (ha₁ : X - ((PD.p : ℕ) : O⟦X⟧) ∣ (a₀ : O⟦X⟧) - 1)
    (w : ℤ) (m : (LL⟦X⟧)ˣ)
    (hm : W.lev i ζ a * m = C ((1 + (PD.p : LL)) ^ (-w)) * rescale (1 + (PD.p : LL)) (m : LL⟦X⟧))
    (j j' : ℤ) (hj : j < j') :
    DiagQuot W T g a i j j' (eigMs LL PD.p (Finset.univ.val.map u) w j j') := by
  obtain ⟨s, hs, hs₁⟩ := hJ.2.2.2.2.1
  obtain ⟨Qu, hQ⟩ : IsUnit (algebraMap (LetA O n) W.EE (qΔ W)) := hJ.2.2.2.2.2.2
  obtain ⟨θ, hθ⟩ := exists_theta W T J b i hJ hb Qu hQ j
  have hP : ∀ c, θ c ∈ (qN W T i j').submoduleOf (qN W T i j) ↔
      ∀ k, (X : O⟦X⟧) ^ (j' - j).toNat ∣ c k := fun c => by
    rw [← theta_mem W T J b i hJ hb Qu hQ hj.le, ← hθ]; rfl
  obtain ⟨eq⟩ := quot_equiv _ _ θ hP
  have hp := PD.hp
  have hχ : (1 + (PD.p : LL)) ≠ 0 := by exact_mod_cast (by omega : 1 + PD.p ≠ 0)
  have hX : X - ((PD.p : ℕ) : O⟦X⟧) ≠ 0 := fun h => by
    have := congrArg (coeff 1) h
    rw [← map_natCast (C : O →+* O⟦X⟧), map_sub, coeff_one_X, coeff_C, if_neg one_ne_zero, sub_zero,
      map_zero] at this
    exact one_ne_zero this
  refine ⟨fun x hx => ?_, Module.Free.of_equiv eq.symm, Module.Finite.equiv eq.symm, ?_, ?_, fun nb hnb => ?_⟩
  · obtain ⟨θ', hθ'⟩ := exists_theta W T J b i hJ hb Qu hQ j'
    obtain ⟨c, hc⟩ := θ'.surjective ⟨x, hx⟩
    have h1 : x = (Qu ^ j') • th W T J b i c := by rw [← hθ', hc]
    rw [h1, zpow_th W T J b i hJ Qu hQ hj.le, theta_mem W T J b i hJ hb Qu hQ le_rfl]
    simp
  · rw [eq.finrank_eq]; simp
  · refine exists_factor ((mulD W T (a * W.π₀)).comp (qN W T i j).subtype)
      ((W.γD T g - mulD W T a).comp (qN W T i j).subtype) ?_ fun x => ?_
    · rw [injective_iff_map_eq_zero]
      intro x hx
      obtain ⟨c, rfl⟩ := θ.surjective x
      have h1 := (nab_iff W T J b i hJ s hs Qu hQ j ha (c := 0) (c' := c) (d := 0) (by simp)).1
        (by rw [← hθ, map_zero, smul_zero, map_zero, smul_zero, sub_zero]; exact hx)
      rw [smul_zero, smul_zero, sub_zero, smul_eq_zero_iff_right (mul_ne_zero a₀.ne_zero hX)] at h1
      rw [h1, map_zero]
    · obtain ⟨c, rfl⟩ := θ.surjective x
      obtain ⟨c₁, hc₁⟩ := γD_th W T J b i hJ hb c
      obtain ⟨y, hy⟩ := dvd_zpow_sub_one _ s hs₁ j
      obtain ⟨z, hz⟩ := ha₁
      refine ⟨θ (((a₀⁻¹ : (O⟦X⟧)ˣ) : O⟦X⟧) • ((y - z) • c + ((s ^ j : (O⟦X⟧)ˣ) : O⟦X⟧) • c₁)), ?_⟩
      have := (nab_iff W T J b i hJ s hs Qu hQ j ha hc₁
        (c' := ((a₀⁻¹ : (O⟦X⟧)ˣ) : O⟦X⟧) • ((y - z) • c + ((s ^ j : (O⟦X⟧)ˣ) : O⟦X⟧) • c₁))).2 (by
          funext k
          simp only [Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul]
          have := a₀.mul_inv
          linear_combination (c k) * hz - (c k) * hy +
            (X - ((PD.p : ℕ) : O⟦X⟧)) * ((y - z) * c k + ((s ^ j : (O⟦X⟧)ˣ) : O⟦X⟧) * c₁ k) * this)
      rw [← hθ, ← hθ] at this
      exact this
  · obtain ⟨η, hη⟩ := exists_eta W J i hJ ζ hζ
    obtain ⟨M, hM, hMe⟩ := exists_matrix W T J b i ζ e he
    have hMu : IsUnit M.det :=
      (Matrix.isUnit_iff_isUnit_det M).1 (Matrix.mulVec_surjective_iff_isUnit.1 (hM hsp))
    let Λu : (O⟦X⟧)ˣ →* (LL⟦X⟧)ˣ := Units.map (abelian₂ W J i ζ).toRingHom.toMonoidHom
    obtain ⟨μ, hμ⟩ := exists_mu _ hχ η m (Λu s) (Λu a₀) j w (by
      have h1 := hρ (cst J X)
      rw [lev_eq W J i ζ (e := X * (s : O⟦X⟧)) (by rw [map_mul, ← hs]; rfl), map_mul] at h1
      change _ = rescale _ (abelian₂ W J i ζ X) at h1
      rw [hη, map_mul, rescale_X] at h1
      apply mul_left_cancel₀ (X_ne_zero (R := LL))
      change X * ((η : LL⟦X⟧) * abelian₂ W J i ζ s) = _
      linear_combination h1) (by rw [← hm, lev_eq W J i ζ ha]; rfl)
    rw [← map_zpow] at hμ
    change abelian₂ W J i ζ ((s ^ j : (O⟦X⟧)ˣ) : O⟦X⟧) * (μ : LL⟦X⟧) = C _ * abelian₂ W J i ζ a₀ * _ at hμ
    have hc : constantCoeff (X * (η : LL⟦X⟧) - ((PD.p : ℕ) : LL⟦X⟧)) = -(PD.p : LL) := by simp
    rw [eigMs_eq, ← hc]
    refine GlobalTheory.TruncDiag.diagWith_trunc _ _ _ θ (abelian₂ W J i ζ) η (X * (η : LL⟦X⟧) - ((PD.p : ℕ) : LL⟦X⟧))
      ((μ : LL⟦X⟧) • M) (1 + (PD.p : LL)) (fun k => (1 + (PD.p : LL)) ^ (j + w - u k)) nb hinj hP hη η.isUnit ?_ ?_ hχ ?_
      (fun k => zpow_ne_zero _ hχ) ?_
    · rw [Matrix.det_smul]
      exact (μ.isUnit.pow _).mul hMu
    · rw [hc, neg_ne_zero]
      exact Nat.cast_ne_zero.2 hp.ne_zero
    · intro k hk h
      have h1 : (1 + PD.p) ^ k = 1 := by exact_mod_cast h
      have := hp.pos
      rw [Nat.pow_eq_one] at h1
      omega
    · intro c c' hcc k
      obtain ⟨d, hd⟩ := γD_th W T J b i hJ hb c
      set d' := c + (X - ((PD.p : ℕ) : O⟦X⟧)) • d
      have h1 := hnb (θ c)
      rw [hcc, hθ, hθ, nab_iff W T J b i hJ s hs Qu hQ j ha hd] at h1
      have h2 : (abelian₂ W J i ζ a₀ * (X * (η : LL⟦X⟧) - ((PD.p : ℕ) : LL⟦X⟧))) • (fun k => abelian₂ W J i ζ (c' k)) =
          abelian₂ W J i ζ ((s ^ j : (O⟦X⟧)ˣ) : O⟦X⟧) • (fun k => abelian₂ W J i ζ (d' k)) -
            abelian₂ W J i ζ a₀ • (fun k => abelian₂ W J i ζ (c k)) := by
        funext k
        have := congrArg (abelian₂ W J i ζ) (congrFun h1 k)
        simpa [hη] using this
      have h3 := congrFun (congrArg M.mulVec h2) k
      rw [Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_smul] at h3
      have h4 := hγ ⟨_, th_mem_N W T J b i c⟩ (hd ▸ th_mem_N W T J b i d') k
      simp only [hd] at h4
      rw [hMe, hMe] at h4
      simp only [Matrix.smul_mulVec, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, map_mul] at h3 ⊢
      rw [h4] at h3
      apply mul_left_cancel₀ (Λu a₀).ne_zero
      change abelian₂ W J i ζ a₀ * _ = abelian₂ W J i ζ a₀ * _
      rw [sub_eq_add_neg (j + w), zpow_add₀ hχ, map_mul]
      linear_combination (μ : LL⟦X⟧) * h3 + C ((1 + (PD.p : LL)) ^ (-u k)) *
        rescale (1 + (PD.p : LL)) (M.mulVec (fun k => abelian₂ W J i ζ (c k)) k) * hμ

def HasCoords (g : W.Gam) (ζ : LL) (r : ℕ) (U : Multiset ℤ) : Prop :=
  ∃ (u : Fin r → ℤ) (e : ↥(W.N T) →+ (Fin r → LL⟦X⟧)), Finset.univ.val.map u = U ∧
    (∀ a x, e (a • x) = W.lev i ζ a • e x) ∧ Submodule.span LL⟦X⟧ (Set.range e) = ⊤ ∧
    ∀ (x : ↥(W.N T)) hx k, e ⟨W.γD T g x, hx⟩ k =
      C ((1 + (PD.p : LL)) ^ (-u k)) * rescale (1 + (PD.p : LL)) (e x k)

theorem coords_of_lines [CharZero LL] (g : W.Gam) (ζ : LL) (U : Multiset ℤ) (h : LinesAt W T i ζ U)
    (hγ : ∀ (x : ↥(W.N T)) hx (k : ℤ), W.levN T i ζ ⟨W.γD T g x, hx⟩ k =
      (1 + (PD.p : LL)) ^ k • W.levN T i ζ x k) : HasCoords W T i g ζ (Module.finrank LL T.V) U := by
  obtain ⟨u, d, hu, hd, hs⟩ := h
  obtain ⟨e, h1, h2, h3⟩ := GlobalTheory.SenLines.Coords.exists_coords (W.lev i ζ) (W.levN T i ζ) u d hd
    (fun a x => funext fun k => W.levN_smul T i ζ a x k) hs
  exact ⟨u, e, hu, h1, h2, fun x hx k => h3 _ x _
    (by exact_mod_cast (by omega : 1 + PD.p ≠ 0)) (hγ x hx) k⟩

theorem senPair [IsDomain O] [IsLocalRing O] [CharZero LL] (hinj : Function.Injective (algebraMap O LL))
    (hl : ¬ IsUnit ((PD.p : ℕ) : O))
    {g : W.Gam} (hJ : QFrame W g J) (b : Module.Basis (Fin (Module.finrank LL T.V)) (LetA O n) ↥(W.N T))
    (hb : ∀ k, (b k : W.DD T) ∈ W.NΔ T) (ζ : LL) (hζ : IsPrimitiveRoot ζ PD.p)
    (hρ : ∀ f, W.lev i ζ (W.γA g f) = rescale (1 + (PD.p : LL)) (W.lev i ζ f))
    (U : Multiset ℤ) (hC : HasCoords W T i g ζ (Module.finrank LL T.V) U)
    (a : LetA O n) (a₀ : (O⟦X⟧)ˣ) (ha : a i = J a₀) (ha₁ : X - ((PD.p : ℕ) : O⟦X⟧) ∣ (a₀ : O⟦X⟧) - 1)
    (w : ℤ) (m : (LL⟦X⟧)ˣ)
    (hm : W.lev i ζ a * m = C ((1 + (PD.p : LL)) ^ (-w)) * rescale (1 + (PD.p : LL)) (m : LL⟦X⟧)) :
    SenPair W T g a i U w := by
  obtain ⟨u, e, hu, he, hsp, hγ⟩ := hC
  have hD : ∀ j j' : ℤ, j < j' → DiagQuot W T g a i j j' (eigMs LL PD.p U w j j') := fun j j' hj =>
    hu ▸ diagQuot W T J i hinj hJ b hb ζ hζ hρ u e he hsp hγ a a₀ ha ha₁ w m hm j j' hj
  refine ⟨hD, fun k _ _ hk => ?_⟩
  obtain ⟨-, hfree, hfin, -, hex, hall⟩ := hD 0 1 zero_lt_one
  refine ⟨hex, fun nb hnb => ?_⟩
  obtain ⟨hs, hd⟩ := hall nb hnb
  refine ⟨hs, ?_⟩
  have hu1 : IsUnit (1 + ((PD.p : ℕ) : O)) := by
    rw [← sub_neg_eq_add]
    exact IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ (fun h => hl (by simpa using h))
  choose c hc hc' using exists_cc (O := O) (F := LL) PD.p PD.hp.ne_zero hu1
  have hk0 : algebraMap O k (PD.p : O) = 0 := by
    have := IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective (algebraMap O k) hk)
    rw [← RingHom.mem_ker, this]
    exact hl
  have e1 : eigMs LL PD.p U w 0 1 = (U.map fun x => c (0 - (x - w))).map (algebraMap O LL) := by
    rw [eigMs, show Finset.Ico (0 : ℤ) 1 = {0} from rfl, Multiset.map_map, ← Multiset.bind_singleton]
    refine Multiset.bind_congr fun x _ => ?_
    simp only [Finset.singleton_val, Multiset.map_singleton, Function.comp, hc]
  have e2 : (U.map fun x => ((x - w : ℤ) : k)) = (U.map fun x => c (0 - (x - w))).map (algebraMap O k) := by
    rw [Multiset.map_map]
    refine Multiset.map_congr rfl fun x _ => ?_
    obtain ⟨d, hd⟩ := hc' (0 - (x - w))
    have := congrArg (algebraMap O k) hd
    rw [map_mul, hk0, zero_mul, map_add, map_intCast] at this
    simp only [Function.comp]
    push_cast at this ⊢
    linear_combination -this
  rw [e2]
  rw [e1] at hd
  exact eigWith_of_diagWith hinj _ _ hd

theorem tie_γ {Zl Ai : Type} [CommRing Zl] [CommRing Ai] [Algebra Zl O] [Algebra Zl Ai]
    {RW : Type} [CommRing RW] [Algebra O RW]
    {inclR : (O ⊗[Zl] Ai) →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : O ⊗[Zl] Ai}
    {E : EtTie W (O ⊗[Zl] Ai) RW inclR φR gR πA} {ιdR : Ai →+* BdR} {p1 : Ai} {tS zS : BdR}
    (tie : CmpTie W E ιdR p1 tS zS) {g : W.Gam} (hχ : algebraMap O LL (W.χΓ g : O) = 1 + (PD.p : LL))
    {ζ : LL} (hζ : IsPrimitiveRoot ζ PD.p) :
    (∀ i f, W.lev i ζ (W.γA g f) = rescale (1 + (PD.p : LL)) (W.lev i ζ f)) ∧
      ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → ∀ i (x : ↥(W.N T)) hx (k : ℤ),
        W.levN T i ζ ⟨W.γD T g x, hx⟩ k = (1 + (PD.p : LL)) ^ k • W.levN T i ζ x k := by
  have hv : ((1 : ℕ) : WithTop ℚ) ≤ v (algebraMap O LL (W.χΓ g : O) - ((1 : ℕ) : LL)) := by
    rw [hχ, Nat.cast_one, Nat.cast_one, add_sub_cancel_left, W.v_l]
  refine ⟨fun i f => hχ ▸ tie.lev_Γ g i ζ ζ 1 1 (by rwa [pow_one]) hv (pow_one ζ).symm f,
    fun T hT i x hx k => ?_⟩
  rw [tie.levN_eq, tie.levN_eq, tie.levB_Γ T hT g i ζ ζ 1 1 (by rwa [pow_one]) hv (pow_one ζ).symm x hx k,
    map_smul, hχ]

end Generic

theorem finrank_lattice {G LL O V : Type} [Group G] [Field LL] [CommRing O] [IsDomain O] [Algebra O LL]
    [IsPrincipalIdealRing O]
    [IsFractionRing O LL] [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
    {ρ : Representation LL G V} (L : Lattice (O := O) ρ) : Module.finrank O ↥L.T = Module.finrank LL V := by
  have : L.T.IsLattice LL := ⟨L.fg, L.span⟩
  rw [Module.finrank, Module.finrank, Submodule.IsLattice.rank' LL]

end GlobalTheory.SenLines
