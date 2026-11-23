import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Definitions.HermitianLattices.TraceFormBilinSeparatingLeftIff
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsLocalizedModuleSubtype
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsCoeEqSpanDetOfIntVecLe
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsSmulMemOfMemSpanFraction

open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical nonZeroDivisors

namespace GlobalTheory.SW.TensLat

noncomputable section

variable {E : Type} [Field E] [NumberField E] {n r : ℕ}

theorem int_smul_mem {L : Lt E r} {a : E} (ha : IsIntegral ℤ a) {u : Fin r → E} (hu : u ∈ L) :
    a • u ∈ L := L.smul_mem (⟨a, ha⟩ : 𝓞 E) hu

theorem pure_mem {A : Lt E n} {B : Lt E r} {v : Fin n → E} {u : Fin r → E} (hv : v ∈ A)
    (hu : u ∈ B) : vecMulVec v u ∈ tens A B := AddSubgroup.subset_closure ⟨v, hv, u, hu, rfl⟩

theorem tens_le {A : Lt E n} {B : Lt E r} {H : AddSubgroup (Matrix (Fin n) (Fin r) E)}
    (h : ∀ v ∈ A, ∀ u ∈ B, vecMulVec v u ∈ H) : tens A B ≤ H := by
  refine (AddSubgroup.closure_le _).2 ?_
  rintro _ ⟨v, hv, u, hu, rfl⟩
  exact h v hv u hu

theorem tens_eq_comap (A : Lt E n) (B : Lt E r) :
    tens A B = (tens B A).comap (Matrix.transposeAddEquiv (Fin n) (Fin r) E).toAddMonoidHom := by
  have key : ∀ {n r : ℕ} (A : Lt E n) (B : Lt E r), tens A B ≤
      (tens B A).comap (Matrix.transposeAddEquiv (Fin n) (Fin r) E).toAddMonoidHom :=
    fun A B => tens_le fun v hv u hu => by
      change (vecMulVec v u)ᵀ ∈ tens B A
      rw [Matrix.transpose_vecMulVec]
      exact pure_mem hu hv
  exact le_antisymm (key A B) fun y hy => key B A hy

theorem isIntegral_mul_inv {c : FractionalIdeal (𝓞 E)⁰ E} (hc : c ≠ 0) {x b : E} (hx : x ∈ c)
    (hb : b ∈ c⁻¹) : IsIntegral ℤ (b * x) := by
  obtain ⟨a, ha⟩ := (FractionalIdeal.mem_one_iff _).1 ((FractionalIdeal.mem_inv_iff hc).1 hb x hx)
  exact ha ▸ a.isIntegral_coe

def fracMul (c : FractionalIdeal (𝓞 E)⁰ E) (B : Lt E r) : AddSubgroup (Fin r → E) where
  carrier := {u | ∀ b ∈ c⁻¹, b • u ∈ B}
  add_mem' := fun hu hv b hb => by rw [smul_add]; exact B.add_mem (hu b hb) (hv b hb)
  zero_mem' := fun b _ => by rw [smul_zero]; exact B.zero_mem
  neg_mem' := fun hu b hb => by rw [smul_neg]; exact B.neg_mem (hu b hb)

theorem relIndex_fracMul {c : FractionalIdeal (𝓞 E)⁰ E} (hc : c ≠ 0) {B B' : Lt E r} {N : 𝓞 E}
    (hN : N ≠ 0) (hB : ∀ u ∈ B, (N : E) • u ∈ B') :
    B'.toAddSubgroup.relIndex B.toAddSubgroup = (fracMul c B').relIndex (fracMul c B) := by
  have hNE : (N : E) ≠ 0 := by simpa using hN
  obtain ⟨x, hx⟩ := IsDedekindDomain.exists_add_spanSingleton_mul_eq
    (a := FractionalIdeal.spanSingleton (𝓞 E)⁰ (N : E)) (b := c⁻¹) (c := 1)
    (FractionalIdeal.spanSingleton_le_iff_mem.2 ((FractionalIdeal.mem_one_iff _).2 ⟨N, rfl⟩))
    (FractionalIdeal.spanSingleton_ne_zero_iff.2 hNE) (inv_ne_zero hc)
  have hxc : x ∈ c := by
    have h1 : FractionalIdeal.spanSingleton (𝓞 E)⁰ x * c⁻¹ ≤ 1 := hx ▸ le_sup_right
    have h2 : FractionalIdeal.spanSingleton (𝓞 E)⁰ x * c⁻¹ * c ≤ 1 * c := by gcongr
    rw [mul_assoc, inv_mul_cancel₀ hc, mul_one, one_mul] at h2
    exact FractionalIdeal.spanSingleton_le_iff_mem.1 h2
  obtain ⟨t, b, ht, hb, htb⟩ : ∃ t b : E, IsIntegral ℤ t ∧ b ∈ c⁻¹ ∧ t * N + x * b = 1 := by
    have h1 : (1 : E) ∈ FractionalIdeal.spanSingleton (𝓞 E)⁰ (N : E) +
        FractionalIdeal.spanSingleton (𝓞 E)⁰ x * c⁻¹ := hx ▸ FractionalIdeal.one_mem_one _
    obtain ⟨y, hy, z, hz, hyz⟩ := (FractionalIdeal.mem_add _ _ _).1 h1
    obtain ⟨t, rfl⟩ := (FractionalIdeal.mem_spanSingleton _).1 hy
    obtain ⟨b, hb, rfl⟩ := FractionalIdeal.mem_singleton_mul.1 hz
    exact ⟨t, b, t.isIntegral_coe, hb, hyz⟩
  refine TensorLat.relIndex_eq_of_hom (DistribSMul.toAddMonoidHom (Fin r → E) x) (fun v hv => ?_)
    (fun v hv => ?_) (fun u hu => ?_)
  · intro b' hb'
    rw [DistribSMul.toAddMonoidHom_apply, smul_smul]
    exact int_smul_mem (isIntegral_mul_inv hc hxc hb') hv
  · rw [DistribSMul.toAddMonoidHom_apply]
    refine ⟨fun h => ?_, fun h b' hb' => ?_⟩
    · have : v = t • (N : E) • v + b • x • v := by
        rw [smul_smul, smul_smul, ← add_smul, mul_comm b, htb, one_smul]
      rw [this]
      exact B'.add_mem (int_smul_mem ht (hB v hv)) (h b hb)
    · rw [smul_smul]
      exact int_smul_mem (isIntegral_mul_inv hc hxc hb') h
  · refine ⟨b • u, hu b hb, fun b' hb' => ?_⟩
    have h1 : u - DistribSMul.toAddMonoidHom (Fin r → E) x (b • u) = t • (N : E) • u := by
      rw [DistribSMul.toAddMonoidHom_apply, smul_smul, smul_smul, eq_sub_of_add_eq htb, sub_smul,
        one_smul]
    rw [h1, smul_comm b', smul_comm b']
    exact int_smul_mem ht (hB _ (hu b' hb'))

theorem exists_mul_le {B B' : Lt E r} (hfg : B.FG)
    (hsp : Submodule.span E (B' : Set (Fin r → E)) = ⊤) :
    ∃ N : 𝓞 E, N ≠ 0 ∧ ∀ u ∈ B, (N : E) • u ∈ B' := by
  obtain ⟨s, rfl⟩ := hfg
  choose d hd0 hd using fun v : Fin r → E =>
    exists_smul_mem_of_mem_span_fraction (K := E) B' v (hsp ▸ Submodule.mem_top)
  refine ⟨∏ v ∈ s, d v, Finset.prod_ne_zero_iff.2 fun v _ => hd0 v, fun u hu => ?_⟩
  change (∏ v ∈ s, d v) • u ∈ B'
  induction hu using Submodule.span_induction with
  | mem v hv =>
    rw [← Finset.prod_erase_mul _ _ hv, mul_smul]
    exact B'.smul_mem _ (hd v)
  | zero => simp
  | add a b _ _ ha hb => rw [smul_add]; exact B'.add_mem ha hb
  | smul α a _ ha => rw [smul_comm]; exact B'.smul_mem α ha

def colCoord (e : Module.Basis (Fin n) E (Fin n → E)) :
    Matrix (Fin n) (Fin r) E →+ (Fin n → Fin r → E) :=
  AddMonoidHom.mk' (fun y a j => e.repr (yᵀ j) a) fun y y' => by
    funext a j
    change e.repr (yᵀ j + y'ᵀ j) a = _
    simp

theorem tens_eq_of_pseudoBasis {A : Lt E n} (e : Module.Basis (Fin n) E (Fin n → E))
    (c : Fin n → FractionalIdeal (𝓞 E)⁰ E) (hc : ∀ a, c a ≠ 0)
    (hA : ∀ v, v ∈ A ↔ ∀ a, e.repr v a ∈ c a) (B : Lt E r) :
    tens A B = (AddSubgroup.pi Set.univ fun a => fracMul (c a) B).comap (colCoord e) := by
  refine le_antisymm (tens_le fun v hv u hu a _ b hb => ?_) fun y hy => ?_
  · have : colCoord e (vecMulVec v u) a = e.repr v a • u := by
      funext j
      have : (vecMulVec v u)ᵀ j = u j • v := by
        funext k; simp [vecMulVec_apply, mul_comm]
      change e.repr ((vecMulVec v u)ᵀ j) a = _
      rw [this]; simp [mul_comm]
    rw [this, smul_smul]
    exact int_smul_mem (isIntegral_mul_inv (hc a) ((hA v).1 hv a) hb) hu
  · have h1 : y = ∑ a, vecMulVec (e a) (colCoord e y a) := by
      ext k j
      have := congrFun (e.sum_repr (yᵀ j)) k
      rw [Matrix.transpose_apply] at this
      rw [← this, Matrix.sum_apply, Finset.sum_apply]
      exact Finset.sum_congr rfl fun a _ => mul_comm _ _
    rw [h1]
    refine AddSubgroup.sum_mem _ fun a _ => ?_
    have h2 : ∀ z ∈ c a * (c a)⁻¹, vecMulVec (e a) (z • colCoord e y a) ∈ tens A B := by
      intro z hz
      refine FractionalIdeal.mul_induction_on hz (fun t ht b hb => ?_) fun s t hs ht => ?_
      · rw [mul_smul, vecMulVec_smul, ← smul_vecMulVec]
        refine pure_mem ((hA _).2 fun a' => ?_) (hy a (Set.mem_univ _) b hb)
        by_cases h : a = a'
        · subst h; simpa using ht
        · simpa [h] using (c a').zero_mem
      · rw [add_smul, vecMulVec_add]
        exact add_mem hs ht
    simpa using h2 1 (by rw [mul_inv_cancel₀ (hc a)]; exact FractionalIdeal.one_mem_one _)

theorem relIndex_tens_right {A : Lt E n} (hA : A.FG)
    (hAs : Submodule.span E (A : Set (Fin n → E)) = ⊤) {B B' : Lt E r} (hfg : B.FG)
    (hsp : Submodule.span E (B' : Set (Fin r → E)) = ⊤) :
    (tens A B').relIndex (tens A B) = B'.toAddSubgroup.relIndex B.toAddSubgroup ^ n := by
  obtain ⟨-, e, c, hc, he, -⟩ := exists_pseudoBasis_adapted E n A ⊤ hA hAs
  obtain ⟨N, hN, hB⟩ := exists_mul_le hfg hsp
  have hs : Function.Surjective (colCoord (r := r) e) := fun z =>
    ⟨(Matrix.of fun j => e.equivFun.symm fun a => z a j)ᵀ, by
      funext a j
      exact congrFun (e.equivFun.apply_symm_apply fun a => z a j) a⟩
  rw [tens_eq_of_pseudoBasis e c hc he, tens_eq_of_pseudoBasis e c hc he,
    AddSubgroup.relIndex_comap, AddSubgroup.map_comap_eq_self_of_surjective hs,
    TensorLat.relIndex_pi_univ,
    Finset.prod_congr rfl fun a _ => (relIndex_fracMul (hc a) hN hB).symm]
  simp

theorem relIndex_tens_left {B : Lt E r} (hB : B.FG)
    (hBs : Submodule.span E (B : Set (Fin r → E)) = ⊤) {A A' : Lt E n} (hfg : A.FG)
    (hsp : Submodule.span E (A' : Set (Fin n → E)) = ⊤) :
    (tens A' B).relIndex (tens A B) = A'.toAddSubgroup.relIndex A.toAddSubgroup ^ r := by
  rw [tens_eq_comap A, tens_eq_comap A', AddSubgroup.relIndex_comap,
    AddSubgroup.map_comap_eq_self_of_surjective (AddEquiv.surjective _),
    relIndex_tens_right hB hBs hfg hsp]

variable [IsCMField E]

def ctr (y : Matrix (Fin n) (Fin r) E) (w : Fin n → E) : Fin r → E := ∑ k, cc (w k) • y k

theorem ctr_apply (y : Matrix (Fin n) (Fin r) E) (w : Fin n → E) (j : Fin r) :
    ctr y w j = herm 1 (yᵀ j) w := by
  simp [ctr, Base.herm_one, Finset.sum_apply, mul_comm]

theorem ctr_pure (v w : Fin n → E) (u : Fin r → E) : ctr (vecMulVec v u) w = herm 1 v w • u := by
  funext j
  simp only [ctr_apply, Base.herm_one, Pi.smul_apply, smul_eq_mul, Finset.sum_mul,
    Matrix.transpose_apply, vecMulVec_apply]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem eq_sum_ctr {m : ℕ} {v w : Fin m → Fin n → E}
    (h : ∀ u : Fin n → E, u = ∑ i, herm 1 u (w i) • v i) (y : Matrix (Fin n) (Fin r) E) :
    y = ∑ i, vecMulVec (v i) (ctr y (w i)) := by
  ext k j
  have := congrFun (h (yᵀ j)) k
  rw [Matrix.transpose_apply] at this
  rw [this, Matrix.sum_apply, Finset.sum_apply]
  exact Finset.sum_congr rfl fun a _ => by simp [vecMulVec_apply, ctr_apply, mul_comm]

theorem mem_tens_iff {M : ℕ} {Λ : Lt E n} (hΛ : Λ ∈ Vset E n M) (L : Lt E r)
    (y : Matrix (Fin n) (Fin r) E) : y ∈ tens Λ L ↔ ∀ w ∈ Λ, ctr y w ∈ L := by
  obtain ⟨-, m, v, w, hv, hw, h⟩ := exists_dual_family Λ hΛ.1 (fun x => (hΛ.2.1 x).1)
    fun x => (hΛ.2.1 x).2
  constructor
  · intro hy u hu
    let f : Matrix (Fin n) (Fin r) E →+ (Fin r → E) := AddMonoidHom.mk' (fun y => ctr y u)
      fun y y' => by
        have : ∀ i, (y + y') i = y i + y' i := fun _ => rfl
        simp only [ctr, this, smul_add, Finset.sum_add_distrib]
    refine tens_le (H := L.toAddSubgroup.comap f) (fun a ha b hb => ?_) hy
    change ctr _ u ∈ L
    rw [ctr_pure]
    exact int_smul_mem ((hΛ.2.1 a).1 ha u hu) hb
  · intro hy
    rw [eq_sum_ctr h y]
    exact AddSubgroup.sum_mem _ fun i _ => pure_mem (hv i) (hy _ (hw i))

theorem tens_fg {M : ℕ} {Λ : Lt E n} (hΛ : Λ ∈ Vset E n M) {L : Lt E r} (hL : L.FG) :
    (tens Λ L).FG := by
  obtain ⟨-, m, v, w, hv, hw, h⟩ := exists_dual_family Λ hΛ.1 (fun x => (hΛ.2.1 x).1)
    fun x => (hΛ.2.1 x).2
  let f : (Fin m → Fin r → E) →+ Matrix (Fin n) (Fin r) E :=
    AddMonoidHom.mk' (fun u => ∑ i, vecMulVec (v i) (u i))
      fun y y' => by simp [vecMulVec_add, Finset.sum_add_distrib]
  have h1 : (Submodule.pi Set.univ fun _ : Fin m => L.restrictScalars ℤ).FG :=
    Submodule.fg_pi fun _ => hL.restrictScalars
  have h2 : tens Λ L = ((Submodule.pi Set.univ fun _ : Fin m => L.restrictScalars ℤ).map
      f.toIntLinearMap).toAddSubgroup := by
    ext y
    constructor
    · intro hy
      exact ⟨fun i => ctr y (w i), fun i _ => (mem_tens_iff hΛ L y).1 hy _ (hw i),
        (eq_sum_ctr h y).symm⟩
    · rintro ⟨u, hu, rfl⟩
      change ∑ i, vecMulVec (v i) (u i) ∈ tens Λ L
      exact AddSubgroup.sum_mem _ fun i _ => pure_mem (hv i) (hu i (Set.mem_univ _))
  rw [h2]
  exact (Submodule.fg_iff_addSubgroup_fg _).1 (h1.map _)

variable (X : Data E r)

theorem EF_eq_bilin (u v : Fin r → E) : EF X u v = traceFormBilin (X.κ0 / 2) X.Gm u v :=
  (traceFormBilin_apply _ _ _ _).symm

theorem EF_smul (a : E) (u v : Fin r → E) : EF X (a • u) v = EF X u (cc a • v) :=
  EFf_smul_left _ _ _ _ _

theorem EF_swap (u v : Fin r → E) : EF X v u = -EF X u v := by
  refine EFf_swap ?_ X.Gm_herm u v
  have h := X.ξ0_im
  unfold cc at h ⊢
  rcases X.κ0_xi with k | k <;> simp [k, h, map_ofNat, neg_div]

theorem sum_EF_pure (y : Matrix (Fin n) (Fin r) E) (v : Fin n → E) (u : Fin r → E) :
    ∑ k, EF X (y k) (vecMulVec v u k) = EF X (ctr y v) u := by
  rw [ctr, EF_eq_bilin, map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← EF_eq_bilin, EF_smul]
  congr 1
  funext j
  simp [cc, vecMulVec_apply]

theorem span_of_selfD {L : Lt E r} (hL : SelfD X L) :
    Submodule.span E (L : Set (Fin r → E)) = ⊤ := by
  by_contra hne
  obtain ⟨f, hf0, hf⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
  obtain ⟨z, hz⟩ := DualFamily.exists_herm_eq f
  have hu : IsUnit X.Gm.det := isUnit_iff_ne_zero.2 X.Gm_det
  have h0 : z ᵥ* X.Gm⁻¹ = 0 := by
    refine DualFamily.eq_zero_of_line L hL.1 _ fun c => (hL.2 _).2 fun y hy => ⟨0, ?_⟩
    have h1 : herm 1 y z = 0 := by rw [← hz]; exact hf (Submodule.subset_span hy)
    have h2 : herm X.Gm (c • (z ᵥ* X.Gm⁻¹)) y = c * herm 1 z y := by
      rw [herm_eq_dotProduct, herm_eq_dotProduct, smul_dotProduct, dotProduct_mulVec,
        vecMul_vecMul, Matrix.nonsing_inv_mul _ hu, dotProduct_mulVec, smul_eq_mul]
    rw [EF_def, h2, DualFamily.herm_one_symm, h1]
    simp [cc]
  have h1 : z = 0 := by
    have := congrArg (· ᵥ* X.Gm) h0
    simpa [vecMul_vecMul, Matrix.nonsing_inv_mul _ hu] using this
  refine hf0 (LinearMap.ext fun u => ?_)
  rw [hz, h1]
  simp [Base.herm_one, cc]

variable {X}

theorem tens_selfDual {M : ℕ} {Λ : Lt E n} (hΛ : Λ ∈ Vset E n M) {L : Lt E r} (hL : SelfD X L)
    (y : Matrix (Fin n) (Fin r) E) :
    y ∈ tens Λ L ↔ ∀ y' ∈ tens Λ L, ∃ k : ℤ, ∑ i, EF X (y i) (y' i) = k := by
  constructor
  · intro hy y' hy'
    let f : Matrix (Fin n) (Fin r) E →+ ℚ := AddMonoidHom.mk' (fun y' => ∑ i, EF X (y i) (y' i))
      fun a b => by
        have : ∀ i, (a + b) i = a i + b i := fun _ => rfl
        simp only [EF_eq_bilin, this, map_add, Finset.sum_add_distrib]
    obtain ⟨k, hk⟩ := tens_le (H := (Int.castAddHom ℚ).range.comap f) (fun a ha b hb => by
      obtain ⟨k, hk⟩ := (hL.2 _).1 ((mem_tens_iff hΛ L y).1 hy a ha) b hb
      exact ⟨k, (hk.symm.trans (sum_EF_pure X y a b).symm :)⟩) hy'
    exact ⟨k, hk.symm⟩
  · intro h
    refine (mem_tens_iff hΛ L y).2 fun w hw => (hL.2 _).2 fun u hu => ?_
    rw [← sum_EF_pure]
    exact h _ (pure_mem hw hu)

theorem smul_mem_tens {M : ℕ} {Λ : Lt E n} (hΛ : Λ ∈ Vset E n M) {L : Lt E r} {w : E}
    (hw : IsIntegral ℤ w) {y : Matrix (Fin n) (Fin r) E} (hy : y ∈ tens Λ L) :
    w • y ∈ tens Λ L := by
  rw [mem_tens_iff hΛ] at hy ⊢
  intro v hv
  have : ctr (w • y) v = w • ctr y v := by
    funext j
    simp [ctr, Finset.sum_apply, Finset.mul_sum, mul_left_comm]
  rw [this]
  exact int_smul_mem hw (hy v hv)

theorem epsW_semichar {M : ℕ} {Λ : Lt E n} (hΛ : Λ ∈ Vset E n M) {L : Lt E r} (hL : SelfD X L)
    {w : E} (hw : IsIntegral ℤ w) (hw1 : w + cc w = 1) {y : Matrix (Fin n) (Fin r) E}
    (hy : y ∈ tens Λ L) : epsW X w y ^ 2 = 1 ∧ ∀ y' ∈ tens Λ L, epsW X w (y + y') =
      epsW X w y * epsW X w y' * cexp (-(π * I * ((∑ k, EF X (y k) (y' k) : ℚ) : ℂ))) := by
  have hint : ∀ y' ∈ tens Λ L, ∃ k : ℤ, ∑ i, EF X (y i) (w • y' i) = k := fun y' hy' =>
    (tens_selfDual hΛ hL y).1 hy _ (smul_mem_tens hΛ hw hy')
  constructor
  · obtain ⟨k, hk⟩ := hint y hy
    rw [epsW, hk, ← Complex.exp_nat_mul, ← Complex.exp_int_mul_two_pi_mul_I k]
    congr 1
    push_cast
    ring
  · intro y' hy'
    obtain ⟨k, hk⟩ := hint y' hy'
    have h1 : ∀ i, EF X ((y + y') i) (w • (y + y') i) = EF X (y i) (w • y i) +
        EF X (y' i) (w • y' i) - EF X (y i) (y' i) + 2 * EF X (y i) (w • y' i) := by
      intro i
      have e : (y + y') i = y i + y' i := rfl
      have h2 : EF X (y' i) (w • y i) = -EF X (y i) (cc w • y' i) := by rw [EF_swap, EF_smul]
      have h3 : EF X (y i) (w • y' i) + EF X (y i) (cc w • y' i) = EF X (y i) (y' i) := by
        rw [EF_eq_bilin, EF_eq_bilin, ← map_add, ← add_smul, hw1, one_smul, EF_eq_bilin]
      simp only [EF_eq_bilin] at h2 h3 ⊢
      simp only [e, smul_add, map_add, LinearMap.add_apply]
      linarith
    simp only [epsW, h1, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hk]
    rw [← Complex.exp_add, ← Complex.exp_add, ← mul_one (cexp (_ + _)),
      ← Complex.exp_int_mul_two_pi_mul_I k, ← Complex.exp_add]
    congr 1
    push_cast
    ring

theorem mem_tens_stdL (L : Lt E r) (y : Matrix (Fin n) (Fin r) E) :
    y ∈ tens (stdL E n) L ↔ ∀ k, y k ∈ L := by
  rw [mem_tens_iff (Base.stdL_mem_Vset n 1)]
  constructor
  · intro h k
    have := h (Pi.single k 1) (Submodule.subset_span ⟨k, rfl⟩)
    rw [ctr, Finset.sum_eq_single k] at this
    · simpa [cc] using this
    · intro j _ hj; simp [hj, cc]
    · simp
  · intro h w hw
    exact L.sum_mem fun k _ => int_smul_mem (Base.isIntegral_cc ((Base.mem_stdL w).1 hw k)) (h k)

end

theorem tens_selfDual_semichar_index : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ w : E, IsIntegral ℤ w → w + cc w = 1 → ∀ L, SelfD X L → ∀ (M : ℕ), ∀ Λ ∈ Vset E n M, (tens Λ L).FG ∧ (∀ y, y ∈ tens Λ L ↔ ∀ y' ∈ tens Λ L, ∃ k : ℤ, ∑ i, EF X (y i) (y' i) = k) ∧ (∀ y ∈ tens Λ L, epsW X w y ^ 2 = 1 ∧ ∀ y' ∈ tens Λ L, epsW X w (y + y') = epsW X w y * epsW X w y' * cexp (-(π * I * ((∑ k, EF X (y k) (y' k) : ℚ) : ℂ)))) ∧ (∀ y : Matrix (Fin n) (Fin r) E, y ∈ tens (stdL E n) L ↔ ∀ k, y k ∈ L) ∧ (∀ L', SelfD X L' → (tens Λ L').relIndex (tens Λ L) = L'.toAddSubgroup.relIndex L.toAddSubgroup ^ n ∧ tens Λ L ⊓ tens Λ L' = tens Λ (L ⊓ L')) ∧ ∀ Λ' ∈ Vset E n M, (tens Λ' L).relIndex (tens Λ L) = Λ'.toAddSubgroup.relIndex Λ.toAddSubgroup ^ r := by
  intro E _ _ _ r X g _ _ n _ _ w hw hw1 L hL M Λ hΛ
  have hsp : ∀ Λ ∈ Vset E n M, Submodule.span E (Λ : Set (Fin n → E)) = ⊤ := fun Λ hΛ =>
    DualFamily.span_eq_top Λ hΛ.1 fun x => (hΛ.2.1 x).2
  refine ⟨tens_fg hΛ hL.1, tens_selfDual hΛ hL, fun y hy => epsW_semichar hΛ hL hw hw1 hy,
    mem_tens_stdL L, fun L' hL' => ⟨relIndex_tens_right hΛ.1 (hsp Λ hΛ) hL.1 (span_of_selfD X hL'),
      ?_⟩, fun Λ' hΛ' => relIndex_tens_left hL.1 (span_of_selfD X hL) hΛ.1 (hsp Λ' hΛ')⟩
  ext y
  simp only [AddSubgroup.mem_inf, mem_tens_iff hΛ, Submodule.mem_inf]
  exact ⟨fun h v hv => ⟨h.1 v hv, h.2 v hv⟩, fun h => ⟨fun v hv => (h v hv).1, fun v hv => (h v hv).2⟩⟩

end GlobalTheory.SW.TensLat
