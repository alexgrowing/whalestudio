import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TorusAtData
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ModerateCoefficientPositivity
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.NormalisedThetaNormInvariant
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FirstMinimumPrincipalTorusAtOrthonormalFrame
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.PeriodTorusConstantEqBase
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UnimodularSymplecticCoordinatesAndLatticeRank
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.LatDen

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2

namespace GlobalTheory.ThetaHol

open Matrix Complex MeasureTheory
open scoped ComplexConjugate Real
open ReciprocityTheory.ChartRestriction.G
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (thetaChar omegaStd hermForm)
open GlobalTheory.ThFr GlobalTheory.CanTh

noncomputable section

section Char

variable {g : ℕ}

theorem canMult_add (a b : Fin g → ℝ) (m m' : Fin g ⊕ Fin g → ℤ) :
    canMult a b (fun i => (m + m') (.inl i)) (fun i => (m + m') (.inr i)) =
      canMult a b (fun i => m (.inl i)) (fun i => m (.inr i)) *
        canMult a b (fun i => m' (.inl i)) (fun i => m' (.inr i)) *
        cexp (π * I * (omegaStd m m' : ℤ)) := by
  rw [canMult, canMult, canMult, ← Complex.exp_add, ← Complex.exp_add,
    Complex.exp_eq_exp_iff_exists_int]
  refine ⟨∑ i, m (.inr i) * m' (.inl i), ?_⟩
  simp only [dotProduct, omegaStd, Pi.add_apply]
  push_cast
  simp only [mul_add, add_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    mul_comm (m' (.inl _) : ℂ) (m (.inr _) : ℂ)]
  ring

theorem exists_canMult_eq (ε : (Fin g ⊕ Fin g → ℤ) → ℤ) (h1 : ∀ m, ε m = 1 ∨ ε m = -1)
    (hadd : ∀ m m', (ε (m + m') : ℂ) = ε m * ε m' * cexp (π * I * (omegaStd m m' : ℤ))) :
    ∃ a b : Fin g → ℝ, ∀ m, canMult a b (fun i => m (.inl i)) (fun i => m (.inr i)) = ε m := by
  let t : Fin g ⊕ Fin g → ℝ := fun j => if ε (Pi.single j 1) = 1 then 0 else 1 / 2
  refine ⟨fun i => t (.inl i), fun i => t (.inr i), ?_⟩
  set C : (Fin g ⊕ Fin g → ℤ) → ℂ := fun m => canMult (fun i => t (.inl i)) (fun i => t (.inr i))
    (fun i => m (.inl i)) (fun i => m (.inr i)) with hC
  have hCadd : ∀ m m', C (m + m') = C m * C m' * cexp (π * I * (omegaStd m m' : ℤ)) :=
    canMult_add _ _
  have hne : ∀ m, (ε m : ℂ) ≠ 0 := fun m => by rcases h1 m with h | h <;> simp [h]
  have hC0 : C 0 = 1 := by simp [hC, canMult, dotProduct]
  have h0 : (ε 0 : ℂ) = 1 := by
    have := hadd 0 0
    simp only [add_zero, omegaStd, Pi.zero_apply, mul_zero, sub_zero, Finset.sum_const_zero,
      Int.cast_zero, Complex.exp_zero, mul_one] at this
    exact (mul_left_cancel₀ (hne 0) (this.symm.trans (mul_one _).symm))
  let S : AddSubgroup (Fin g ⊕ Fin g → ℤ) :=
    { carrier := {m | C m = ε m}
      add_mem' := fun {m m'} hm hm' => by
        rw [Set.mem_setOf_eq] at hm hm' ⊢
        rw [hCadd, hadd, hm, hm']
      zero_mem' := hC0.trans h0.symm
      neg_mem' := fun {m} hm => by
        rw [Set.mem_setOf_eq] at hm ⊢
        have e1 := hCadd m (-m)
        have e2 := hadd m (-m)
        rw [add_neg_cancel] at e1 e2
        rw [hC0, hm] at e1
        rw [h0] at e2
        exact mul_left_cancel₀ (hne m)
          (mul_right_cancel₀ (Complex.exp_ne_zero _) (e1.symm.trans e2)) }
  have hgen : ∀ j, Pi.single j 1 ∈ S := by
    intro j
    change C _ = _
    have e : C (Pi.single j 1) = cexp (2 * π * I * t j) ∨ C (Pi.single j 1) =
        cexp (-(2 * π * I * t j)) := by
      rcases j with j | j
      · left; simp [hC, canMult, dotProduct, Pi.single_apply]
      · right; simp [hC, canMult, dotProduct, Pi.single_apply]
    rcases h1 (Pi.single j 1) with h | h
    · have : t j = 0 := if_pos h
      rcases e with e | e <;> simp [e, this, h]
    · have : t j = 1 / 2 := if_neg (by rw [h]; decide)
      have e2 : 2 * π * I * (t j : ℂ) = π * I := by rw [this]; push_cast; ring
      rcases e with e | e <;> simp [e, e2, h, Complex.exp_neg]
  intro m
  have hm : m = ∑ j, m j • Pi.single j (1 : ℤ) := by
    funext j; simp [Pi.single_apply]
  have : m ∈ S := hm ▸ S.sum_mem fun j _ => S.zsmul_mem (hgen j) _
  exact this

end Char

section Conj

variable {E : Type} [Field E] [NumberField E] (T : PT E) {ι : Type} [Fintype ι]
  (e : ι ≃ Idx T.dim)

theorem Hf_self' (v : EuclideanSpace ℂ ι) : Hf v v = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
  rw [EuclideanSpace.norm_sq_eq, Hf]
  push_cast
  exact Finset.sum_congr rfl fun i _ => mul_conj' _

def cj : Vsp T.dim ≃ₗ[ℝ] EuclideanSpace ℂ ι where
  toFun y := WithLp.toLp 2 fun i => conj (y (e i))
  invFun z := WithLp.toLp 2 fun j => conj (z (e.symm j))
  map_add' y z := by ext i; simp
  map_smul' c y := by ext i; simp
  left_inv y := by ext j; simp
  right_inv z := by ext i; simp

theorem cj_apply (y : Vsp T.dim) (i : ι) : cj T e y i = conj (y (e i)) := rfl

theorem Hf_cj (v w : Vsp T.dim) : Hf (cj T e v) (cj T e w) = conj (Hf v w) := by
  simp only [Hf, cj_apply, map_sum, map_mul]
  exact e.sum_comp fun j => conj (v j) * conj (conj (w j))

variable (Y : GT ι) (F : EuclideanSpace ℂ ι → ℂ)

def cjFn (w : Fin 1 → Vsp T.dim) : ℂ := conj (F (cj T e (w 0)))

theorem pointwiseNorm_conjugateFunctionOnConjugateSpace (y : Vsp T.dim) :
    T.ptN2 1 (cjFn T e F) (fun _ => y) = Y.ptN2 1 F (cj T e y) := by
  have h := congrArg Complex.re (Hf_cj T e y y)
  rw [Hf_self', ofReal_re, conj_re] at h
  simp only [PT.ptN2, GT.ptN2, cjFn, HC, Fin.sum_univ_one, Complex.norm_conj, h]

variable {T e Y F} (hL : ∀ y, y ∈ T.L ↔ cj T e y ∈ lat Y.b)
  (hka : ∀ y ∈ T.L, Y.ka (cj T e y) = T.eps y) (hF : F ∈ Y.Sec 1)
include hL hka hF

theorem cjFn_mem_Sec : cjFn T e F ∈ T.Sec 1 1 := by
  refine ⟨fun w => ?_, fun γ hγ v => ?_⟩
  · have h1 : Differentiable ℂ fun z : ι → ℂ => F (WithLp.toLp 2 z) :=
      hF.1.comp (PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => ℂ)).symm.differentiable
    have h2 : Differentiable ℂ (star ∘ (fun z : ι → ℂ => F (WithLp.toLp 2 z)) ∘ star) := fun z => by
      simpa using (h1 (star z)).star_star
    have h3 : Differentiable ℂ fun w : Fin 1 → Vsp T.dim => fun i : ι => w 0 (e i) := by
      fun_prop
    exact (h2.comp h3) w
  · have h := hF.2 _ ((hL _).1 (hγ 0)) (cj T e (v 0))
    simp only [cjFn, Pi.add_apply, map_add, h, hka _ (hγ 0), Hf_cj, map_mul, ← Complex.exp_conj,
      HC, Fin.sum_univ_one, Fin.prod_univ_one, pow_one, map_div₀, conj_conj, map_intCast,
      map_natCast, conj_ofReal, map_ofNat]

theorem l2_cjFn_eq : T.l2 1 (cjFn T e F) = Y.l2 1 F := by
  have hG := cjFn_mem_Sec hL hka hF
  let f : Vsp T.dim ≃L[ℝ] EuclideanSpace ℂ ι := (cj T e).toContinuousLinearEquiv
  have hev : ∀ v, f v = cj T e v := fun _ => rfl
  let b' := Y.b.map f.symm.toLinearEquiv
  have hrepr : ∀ v i, b'.repr v i = Y.b.repr (cj T e v) i := fun v i => by
    simp only [b', Module.Basis.map_repr]
    rfl
  have hfd : f ⁻¹' ZSpan.fundamentalDomain Y.b = ZSpan.fundamentalDomain b' := by
    ext v
    simp only [Set.mem_preimage, ZSpan.mem_fundamentalDomain, hrepr, hev]
  have hle : Submodule.span ℤ (Set.range b') ≤ Submodule.span ℤ (Set.range T.b) := by
    intro v hv
    refine (hL v).2 ?_
    rw [Module.Basis.mem_span_iff_repr_mem] at hv ⊢
    simpa only [hrepr] using hv
  have h := average_fundamentalDomain_eq_real volume T.b b'
    (fun y => T.ptN2 1 (cjFn T e F) (fun _ => y))
    ((TiledBoundaries.continuous_pointNormSq_quotient T 1 hG.1.continuous).comp (continuous_pi fun _ => continuous_id))
    (fun γ hγ v => pointwiseNormSq_add_period T hG (γ := fun _ => γ) (fun _ => hγ) (fun _ => v)) hle 0
  rw [l2_norm_fundamental_domain, GT.l2, TensorLat.setAverage_comp_equiv volume volume f, hfd, ← h]
  simp only [hev, pointwiseNorm_conjugateFunctionOnConjugateSpace T e Y, add_zero]

theorem ratio_cj (hF0 : Y.l2 1 F ≠ 0) {s : (Fin 1 → Vsp T.dim) → ℂ} (hs : s ∈ T.Sec 1 1)
    (hs0 : s ≠ 0) (y : Vsp T.dim) :
    T.ptN2 1 s (fun _ => y) / T.l2 1 s = Y.ptN2 1 F (cj T e y) / Y.l2 1 F := by
  obtain ⟨c, hc⟩ := ThetaRho.exists_eq_smul T hs (cjFn_mem_Sec hL hka hF) hs0
  have hl := l2_cjFn_eq hL hka hF
  rw [hc, l2_smul] at hl
  have hc0 : ‖c‖ ^ 2 ≠ 0 := left_ne_zero_of_mul (hl ▸ hF0)
  have : T.ptN2 1 (c • s) (fun _ => y) = ‖c‖ ^ 2 * T.ptN2 1 s (fun _ => y) := by
    simp only [PT.ptN2, Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow, mul_assoc]
  rw [← pointwiseNorm_conjugateFunctionOnConjugateSpace, hc, this, ← hl, mul_div_mul_left _ _ hc0]

end Conj

section Lattice

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

open SemicharIndep in

theorem exists_sign (X : Data E r) : ∃ σ : ℤ, (σ = 1 ∨ σ = -1) ∧ ∀ u v, EF X u v = σ * B X u v := by
  rcases EF_eq_or X with h | h
  · exact ⟨-1, Or.inr rfl, fun u v => by rw [h, EFf_eq]; simp⟩
  · exact ⟨1, Or.inl rfl, fun u v => by rw [h, EFf_eq]; simp⟩

theorem finrank_lattice (X : Data E r) : Module.Free ℤ X.Λ ∧ Module.Finite ℤ X.Λ ∧
    Module.finrank ℤ X.Λ = 2 * (X.Ψ.card * r) := by
  obtain ⟨b, hb⟩ := CMLattice.exists_basis_lattice E r X
  obtain ⟨τ⟩ : Nonempty X.Ψ := by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    by_cases h : τ ∈ X.Ψ
    · exact ⟨⟨τ, h⟩⟩
    · exact ⟨⟨_, TorusCoord.conj_mem X h⟩⟩
  let f : X.Λ →+ Submodule.span ℤ (Set.range b) :=
    { toFun := fun v => ⟨fun τ => Data.emb τ.1 v, (hb _).2 ⟨v, v.2, rfl⟩⟩
      map_zero' := by ext τ a; simp [Data.emb]
      map_add' := fun u v => by ext τ a; simp [Data.emb] }
  have hf : Function.Bijective f := by
    constructor
    · intro u v h
      ext a
      exact τ.1.injective (congrFun (congrFun (congrArg Subtype.val h) τ) a)
    · rintro ⟨y, hy⟩
      obtain ⟨v, hv, rfl⟩ := (hb y).1 hy
      exact ⟨⟨v, hv⟩, rfl⟩
  let c := (b.restrictScalars ℤ).map (LinearEquiv.ofBijective f.toIntLinearMap hf).symm
  exact ⟨Module.Free.of_basis c, Module.Finite.of_basis c, by
    rw [Module.finrank_eq_card_basis c, Fintype.card_fin]⟩

open SemicharIndep in

theorem exists_isSympl (X : DataX E r) :
    ∃ bas : (Fin (X.Ψ.card * r) ⊕ Fin (X.Ψ.card * r) → ℤ) ≃ₗ[ℤ] X.Λ, IsSympl X.toData bas := by
  obtain ⟨h1, h2, h3⟩ := finrank_lattice X.toData
  obtain ⟨σ, hσ, hE⟩ := exists_sign X.toData
  have hσ2 : σ * σ = 1 := by rcases hσ with rfl | rfl <;> rfl
  choose k hk using fun u v : X.Λ => B_int X u.2 v.2
  have hl (u u' v) : k (u + u') v = k u v + k u' v := by
    have := B_add_left X.toData u u' v
    rw [← Submodule.coe_add, hk, hk, hk] at this
    exact_mod_cast this
  have hr (u v v') : k u (v + v') = k u v + k u v' := by
    have := B_add_right X.toData u v v'
    rw [← Submodule.coe_add, hk, hk, hk] at this
    exact_mod_cast this
  have hsk (u v) : k u v = -k v u := by
    have := B_skew X.toData u v
    rw [hk, hk] at this
    exact_mod_cast this
  let β : LinearMap.BilinForm ℤ X.Λ :=
    (AddMonoidHom.mk' (fun u => (AddMonoidHom.mk' (fun v => -σ * k u v) fun v v' => by
      rw [hr, mul_add]).toIntLinearMap) fun u u' => by
        ext v
        change -σ * k (u + u') v = -σ * k u v + -σ * k u' v
        rw [hl, mul_add]).toIntLinearMap
  have hβ (u v) : β u v = -σ * k u v := rfl
  have hsurj : Function.Surjective β := by
    intro φ
    obtain ⟨u, hu, h⟩ := X.EF_perf (σ • φ).toAddMonoidHom
    refine ⟨⟨u, hu⟩, LinearMap.ext fun v => ?_⟩
    have h' := h v
    rw [EFf_eq, hk ⟨u, hu⟩ v] at h'
    have h'' : σ * φ v = -k ⟨u, hu⟩ v := by exact_mod_cast h'
    rw [hβ]
    linear_combination (-σ) * h'' + φ v * hσ2
  have hinj : Function.Injective β := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    refine (Module.forall_dual_apply_eq_zero_iff ℤ x).1 fun φ => ?_
    obtain ⟨u, rfl⟩ := hsurj φ
    have := LinearMap.congr_fun hx u
    rw [hβ, LinearMap.zero_apply] at this
    rw [hβ, hsk]
    linear_combination -this
  obtain ⟨bas, hbas⟩ := unimodular_symplectic_coordinates_and_lattice_rank.1 X.Λ β _
    ⟨hinj, hsurj⟩ (fun x => by
      have := hsk x x
      rw [hβ, show k x x = 0 by omega, mul_zero]) h3
  refine ⟨bas, fun a b => ?_⟩
  rw [hE, hk, ← hbas, hβ]
  push_cast
  ring

variable {X : Data E r} {g : ℕ} {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ}
  (idx : Fin g ≃ X.Ψ × Fin r)

theorem exists_coord (hs : IsSympl X bas) (v : Fin r → E) : ∃ a b : Fin g → ℝ, ∀ x ∈ X.dom,
    hMat X bas idx x *ᵥ (per X x v ∘ idx) =
      (fun i => (b i : ℂ)) + tauMat X bas idx x *ᵥ fun i => (a i : ℂ) := by
  obtain ⟨n, hn, hv⟩ := (LatDen.latDen r X).1 v
  obtain ⟨m, hm⟩ := bas.surjective ⟨_, hv⟩
  refine ⟨fun i => m (.inr i) / n, fun i => m (.inl i) / n, fun x hx => ?_⟩
  have h := hMat_mulVec_per X bas idx (isUnit_det_perMat idx hs hx) m
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  have e : per X x v ∘ idx = (n : ℂ)⁻¹ • (per X x (bas m) ∘ idx) := by
    funext i
    rw [hm]
    simp [per_smul, hn']
  have e2 (s : Fin g → Fin g ⊕ Fin g) : (fun i => (((m (s i) : ℝ) / n : ℝ) : ℂ)) =
      (n : ℂ)⁻¹ • fun i => (m (s i) : ℂ) := by
    funext i
    simp [div_eq_inv_mul]
  rw [e, mulVec_smul, h, e2, e2, mulVec_smul, smul_add]

theorem pointwiseNorm_canonicalTheta_eq_sq_thetaConstant (hs : IsSympl X bas) {x : Frame X.Ψ r} (ho : X.IsOrtho x)
    (a b a' b' : Fin g → ℝ) (z : Fin g → ℂ) (hz : hMat X bas idx x *ᵥ z =
      (fun i => (b' i : ℂ)) + tauMat X bas idx x *ᵥ fun i => (a' i : ℂ)) :
    (frameTorus idx hs ho a b).ptN2 1 (canSec X bas idx a b x) (scaleUp X idx z) =
      ‖thetaChar (tauMat X bas idx x) (fun i => ((a + a') i : ℂ)) (fun i => ((b + b') i : ℂ)) 0‖ ^ 2 := by
  have hx := mem_dom_of_isOrtho ho
  have h := congrArg norm (canTh_translate (tauMat_isSymm idx hs hx) (tauMat_im_posDef idx hs hx)
    a b a' b' hz 0)
  have h1 := Hf_eq_normCoord idx hs ho (scaleUp X idx z) (scaleUp X idx z)
  rw [normCoord_scaleUp, Hf_self'] at h1
  rw [← h1, norm_mul, norm_mul, norm_translConst, one_mul, zero_add, Complex.norm_exp] at h
  have h2 : canTh (tauMat X bas idx x) (a + a') (b + b') 0 =
      thetaChar (tauMat X bas idx x) (fun i => ((a + a') i : ℂ)) (fun i => ((b + b') i : ℂ)) 0 := by
    simp [canTh]
  rw [← h2, ← h, GT.ptN2, canSec_scaleUp, canFn_eq_canTh, mul_pow, mul_comm, ← Real.exp_nat_mul]
  congr 2
  simp only [hermForm, zero_dotProduct, mul_zero, neg_zero, zero_sub, neg_re]
  rw [show (π : ℂ) / 2 = ((π / 2 : ℝ) : ℂ) by push_cast; ring, ← ofReal_mul, ofReal_re]
  push_cast
  ring

theorem norm_det_hMat (hs : IsSympl X bas) {x : Frame X.Ψ r} (ho : X.IsOrtho x) :
    √(2 ^ g * ((tauMat X bas idx x).map Complex.im).det) =
      √(2 ^ g / ∏ τ, X.c τ ^ r) * ‖(hMat X bas idx x).det‖ := by
  rw [det_im_tauMat idx hs (mem_dom_of_isOrtho ho), det_Hm_of_isOrtho idx hs ho, ofReal_re,
    mul_div_assoc', mul_div_right_comm, Real.sqrt_mul' _ (sq_nonneg _),
    Real.sqrt_sq (norm_nonneg _)]

theorem det_hMat_weight (x : Frame X.Ψ r) {u : Frame X.Ψ r} (hu : u ∈ Bor X.Ψ r) :
    (hMat X bas idx (rmul x u)).det =
      bchar (fun _ j => if X.p0 ≤ (j : ℕ) then 1 else -1) u * (hMat X bas idx x).det := by
  rw [det_hMat_rmul bas idx x hu, mul_comm, bchar, Fintype.prod_prod_type]
  congr 1
  refine Finset.prod_congr rfl fun τ _ => Finset.prod_congr rfl fun j _ => ?_
  by_cases h : X.p0 ≤ (j : ℕ)
  · simp [rowFac, h, not_lt.2 h]
  · simp [rowFac, h, not_le.1 h]

end Lattice

section Adapted

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}
  {x : Frame X.Ψ r} (A : TorusAt X x)

def adapted : Frame X.Ψ r := fun τ k a => A.e τ a k

theorem isOrtho_adapted : X.IsOrtho (adapted A) := fun τ => by
  ext a b
  rw [diagonal_apply]
  exact A.e_orth τ a b

theorem exists_adapted_eq : ∃ u ∈ Bor X.Ψ r, adapted A = rmul x u := by
  have key : ∀ (τ : X.Ψ) (a : Fin r), ∃ β : Fin r → ℂ, (∀ c, a < c → β c = 0) ∧
      A.e τ a = mat x τ *ᵥ β := by
    intro τ a
    have hm : A.e τ a ∈ Submodule.span ℂ
        (Set.range fun k : Fin (a + 1) => FD.col (mat x τ) (Fin.castLE a.2 k)) := by
      rw [← A.e_flag τ _ a.2]
      exact Submodule.subset_span ⟨Fin.last a, rfl⟩
    generalize A.e τ a = y at hm
    induction hm using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨k, rfl⟩ := hy
      refine ⟨Pi.single (Fin.castLE a.2 k) 1, fun c hc => Pi.single_eq_of_ne ?_ _, ?_⟩
      · rintro rfl
        have := k.2
        rw [Fin.lt_def] at hc
        simp only [Fin.val_castLE] at hc
        omega
      · ext j; simp [FD.col]
    | zero => exact ⟨0, fun _ _ => rfl, by simp⟩
    | add y z _ _ hy hz =>
      obtain ⟨β, h1, rfl⟩ := hy
      obtain ⟨γ, h2, rfl⟩ := hz
      exact ⟨β + γ, fun c hc => by simp [h1 c hc, h2 c hc], by rw [mulVec_add]⟩
    | smul t y _ hy =>
      obtain ⟨β, h1, rfl⟩ := hy
      exact ⟨t • β, fun c hc => by simp [h1 c hc], by rw [mulVec_smul]⟩
  choose β h0 hβ using key
  have h : adapted A = rmul x fun τ c a => β τ a c := by
    funext τ k a
    exact congrFun (hβ τ a) k
  refine ⟨fun τ c a => β τ a c, fun τ => ⟨fun hd => ?_, fun a c hc => h0 τ c a hc⟩, h⟩
  apply (mem_dom_of_isOrtho (isOrtho_adapted A) τ).1
  rw [h]
  change (mat x τ * mat (fun τ c a => β τ a c) τ).det = 0
  rw [det_mul, hd, mul_zero]

theorem exists_equiv : ∃ e : X.Ψ × Fin r ≃ Idx A.T.dim, ∀ v p,
    conj (A.φ v (e p)) = (√(X.c p.1) : ℂ) * per X (adapted A) v p := by
  let f : X.Ψ × Fin r → Idx A.T.dim := fun p =>
    if h : (p.2 : ℕ) < X.p0 then ⟨p.1.1, ⟨p.2, by rw [A.dim_pos]; exact h⟩⟩
    else ⟨ComplexEmbedding.conjugate p.1.1, ⟨p.2 - X.p0, by
      rw [A.dim_neg]; have := p.2.2; omega⟩⟩
  have hp := X.p0_le
  have hf : Function.Bijective f := by
    refine (Fintype.bijective_iff_surjective_and_card _).2 ⟨?_, ?_⟩
    · rintro ⟨σ, a⟩
      by_cases h : σ ∈ X.Ψ
      · have ha : (a : ℕ) < X.p0 := lt_of_lt_of_eq a.2 (A.dim_pos ⟨σ, h⟩)
        exact ⟨(⟨σ, h⟩, ⟨a, by omega⟩), dif_pos ha⟩
      · obtain ⟨τ, rfl⟩ : ∃ τ : X.Ψ, σ = ComplexEmbedding.conjugate τ.1 :=
          ⟨⟨_, TorusCoord.conj_mem X h⟩, (TorusAtDataPf.conj_conj_X σ).symm⟩
        have ha : (a : ℕ) < r - X.p0 := lt_of_lt_of_eq a.2 (A.dim_neg τ)
        refine ⟨(τ, ⟨X.p0 + a, by omega⟩), (dif_neg (by simp)).trans ?_⟩
        simp
    · rw [Fintype.card_sigma, TorusCoord.sum_emb_split X]
      simp [A.dim_pos, A.dim_neg, Nat.add_sub_cancel' hp]
  refine ⟨Equiv.ofBijective f hf, fun v ⟨τ, a⟩ => ?_⟩
  rw [Equiv.ofBijective_apply]
  by_cases h : (a : ℕ) < X.p0
  · rw [show f (τ, a) = _ from dif_pos h, A.coord_pos, map_mul, conj_ofReal, per_of_lt X _ _ _ h,
      hermC_conj τ.1 X.Gm_herm]
    rfl
  · rw [show f (τ, a) = _ from dif_neg h, A.coord_neg, map_mul, conj_ofReal, conj_conj,
      per_of_le X _ _ _ (not_lt.1 h)]
    congr 1
    have ha : (⟨X.p0 + (a - X.p0), by have := a.2; omega⟩ : Fin r) = a := Fin.ext (by
      simp only; omega)
    have hd := (mem_dom_of_isOrtho (isOrtho_adapted A) τ).1
    have hu : mat (adapted A) τ *ᵥ ((mat (adapted A) τ)⁻¹ *ᵥ Data.emb τ.1 v) = Data.emb τ.1 v := by
      rw [mulVec_mulVec, mul_nonsing_inv _ hd.isUnit, one_mulVec]
    have hcol : A.e τ a = mat (adapted A) τ *ᵥ Pi.single a 1 := by
      ext k; simp [mat, adapted]
    simp only [ha]
    conv_lhs => rw [hcol, ← hu]
    rw [UnitFrame.hermC_mulVec, isOrtho_adapted A]
    simp [dotProduct, mulVec_diagonal, FD.sgn, h, Pi.single_apply, apply_ite]

end Adapted

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : DataX E r} {g : ℕ}
  {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ}

theorem exists_char_at (hs : IsSympl X.toData bas) {x : Frame X.Ψ r} (A : TorusAt X.toData x) :
    ∃ a b : Fin g → ℝ, ∀ m, canMult a b (fun i => m (.inl i)) (fun i => m (.inr i)) =
      A.T.eps (A.φ (bas m)) := by
  have hm (m) : A.φ (bas m) ∈ A.T.L := (A.lat _).2 ⟨_, (bas m).2, rfl⟩
  refine exists_canMult_eq (fun m => A.T.eps (A.φ (bas m))) (fun m => A.T.eps_pm _ (hm m))
    fun m m' => ?_
  obtain ⟨σ, hσ, hE⟩ := exists_sign X.toData
  have h := A.T.eps_add _ (hm m) _ (hm m')
  have h1 := hE (bas m) (bas m')
  rw [hs] at h1
  have h2 : Real.cos (π * (Hf (A.φ (bas m)) (A.φ (bas m'))).im) =
      Real.cos ((omegaStd m m' : ℤ) * π) := by
    rw [A.im_eq _ (bas m).2 _ (bas m').2]
    change Real.cos (π * (A.sg * ((SemicharIndep.B X.toData (bas m) (bas m') : ℚ) : ℝ))) = _
    have h3 : ((omegaStd m m' : ℤ) : ℝ) =
        -(σ * ((SemicharIndep.B X.toData (bas m) (bas m') : ℚ) : ℝ)) := by
      rw [← neg_eq_iff_eq_neg]
      exact_mod_cast h1
    rw [h3]
    rcases hσ with rfl | rfl <;> rcases A.sg_pm with h4 | h4 <;> simp [h4, mul_comm]
  rw [h2, Real.cos_int_mul_pi] at h
  rw [map_add, Submodule.coe_add, map_add, mul_comm (π * I : ℂ), Complex.exp_int_mul,
    Complex.exp_pi_mul_I]
  have h5 := congrArg ((↑) : ℝ → ℂ) h
  push_cast at h5
  exact h5

theorem ratio_eq_theta (idx : Fin g ≃ X.Ψ × Fin r) (hs : IsSympl X.toData bas) {x : Frame X.Ψ r}
    (A : TorusAt X.toData x) {a b : Fin g → ℝ}
    (hab : ∀ m, canMult a b (fun i => m (.inl i)) (fun i => m (.inr i)) = A.T.eps (A.φ (bas m)))
    (v : Fin r → E) (a' b' : Fin g → ℝ)
    (hv : hMat X.toData bas idx (adapted A) *ᵥ (per X.toData (adapted A) v ∘ idx) =
      (fun i => (b' i : ℂ)) + tauMat X.toData bas idx (adapted A) *ᵥ fun i => (a' i : ℂ)) :
    A.T.ptN2 1 A.s (fun _ => A.φ v) / A.T.l2 1 A.s =
      √(2 ^ g / ∏ τ, X.c τ ^ r) * ‖thetaChar (tauMat X.toData bas idx (adapted A))
        (fun i => ((a + a') i : ℂ)) (fun i => ((b + b') i : ℂ)) 0‖ ^ 2 *
        ‖(hMat X.toData bas idx (adapted A)).det‖ := by
  have ho := isOrtho_adapted A
  obtain ⟨e, he⟩ := exists_equiv A
  have hcj (w) : cj A.T (idx.trans e) (A.φ w) =
      scaleUp X.toData idx (per X.toData (adapted A) w ∘ idx) := by
    ext i
    exact he w (idx i)
  have hL : ∀ y, y ∈ A.T.L ↔ cj A.T (idx.trans e) y ∈ lat (frameTorus idx hs ho a b).b := by
    intro y
    rw [A.lat, mem_lat_frameTorus]
    refine exists_congr fun w => and_congr_right fun _ => ?_
    rw [← hcj, (cj A.T (idx.trans e)).injective.eq_iff, eq_comm]
  have hka : ∀ y ∈ A.T.L, (frameTorus idx hs ho a b).ka (cj A.T (idx.trans e) y) = A.T.eps y := by
    intro y hy
    obtain ⟨w, hw, rfl⟩ := (A.lat y).1 hy
    obtain ⟨m, hm⟩ := bas.surjective ⟨w, hw⟩
    obtain rfl : w = bas m := by rw [hm]
    rw [hcj, ← hab, ← frameTorus_ka idx hs ho a b]
    congr 5
    exact congrArg bas (Sum.elim_comp_inl_inr m).symm
  rw [ratio_cj hL hka (canSec_mem_Sec idx hs ho a b) (l2_canSec_pos idx hs ho a b).ne'
    A.s_mem A.s_ne, hcj, pointwiseNorm_canonicalTheta_eq_sq_thetaConstant idx hs ho a b a' b' _ hv, l2_canSec_eq_inv_sqrt_two_pow_mul_det_im, div_inv_eq_mul,
    norm_det_hMat idx hs ho]
  ring

end Main

theorem normalised_theta_norm_holomorphic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : DataX E r), (∃ w0 : 𝓞 E, ∀ u ∈ X.Λ, ∀ v ∈ X.Λ, ∃ k : ℤ, Algebra.trace ℚ E (X.ξ0 * herm X.Gm u (((w0 : E) - cc (w0 : E)) • v)) - Algebra.trace ℚ E (X.ξ0 * herm X.Gm u v) = 2 * k) → ∃ (Θ : (Fin r → E) → Frame X.Ψ r → ℂ) (D : Frame X.Ψ r → ℂ) (κ : ℝ), 0 < κ ∧ (∀ v, DifferentiableOn ℂ (Θ v) X.dom) ∧ DifferentiableOn ℂ D X.dom ∧ (∀ x ∈ X.dom, D x ≠ 0) ∧ ∀ x ∈ X.dom, ∀ (A : TorusAt X.toData x) (v : Fin r → E), A.T.ptN2 1 A.s (fun _ => A.φ v) / A.T.l2 1 A.s = κ * ‖Θ v x‖ ^ 2 * ‖D x‖ * X.nfac (fun _ j => if X.p0 ≤ (j : ℕ) then 1 else -1) x := by
  intro E _ _ _ r X hw
  obtain ⟨bas, hs⟩ := exists_isSympl X
  let idx : Fin (X.Ψ.card * r) ≃ X.Ψ × Fin r := (Fintype.equivFinOfCardEq (by simp)).symm
  obtain ⟨a, b, hab⟩ : ∃ a b : Fin (X.Ψ.card * r) → ℝ, ∀ x (A : TorusAt X.toData x) m,
      canMult a b (fun i => m (.inl i)) (fun i => m (.inr i)) = A.T.eps (A.φ (bas m)) := by
    by_cases h : ∃ x, Nonempty (TorusAt X.toData x)
    · obtain ⟨x₀, ⟨A₀⟩⟩ := h
      obtain ⟨a, b, hab⟩ := exists_char_at hs A₀
      refine ⟨a, b, fun x A m => ?_⟩
      have h1 := torusAt_eps_indep E r X hw x₀ x A₀ A 1 ⟨by simp, by simp⟩ _ (bas m).2
      rw [Units.val_one, one_mulVec] at h1
      rw [hab, h1]
    · exact ⟨0, 0, fun x A => (h ⟨x, ⟨A⟩⟩).elim⟩
  choose a' b' hv using exists_coord idx hs
  refine ⟨fun v x => thetaChar (tauMat X.toData bas idx x) (fun i => ((a + a' v) i : ℂ))
      (fun i => ((b + b' v) i : ℂ)) 0, fun x => (hMat X.toData bas idx x).det,
    √(2 ^ (X.Ψ.card * r) / ∏ τ, X.c τ ^ r), Real.sqrt_pos.2 (div_pos (by positivity)
      (Finset.prod_pos fun τ _ => pow_pos (ThFr.c_pos _ τ) r)), fun v => ?_,
    differentiableOn_det_hMat idx hs, fun x hx => (isUnit_det_hMat idx hs hx).ne_zero,
    fun x hx A v => ?_⟩
  · exact differentiableOn_thetaChar (Z := fun _ => 0) (differentiableOn_tauMat idx hs)
      (differentiableOn_const _) (fun x hx => mem_thetaDomain (tauMat_im_posDef idx hs hx)) _ _
  · have ho := isOrtho_adapted A
    obtain ⟨u, hu, hA⟩ := exists_adapted_eq A
    have h1 := FrameDegreeData.pnorm_rmul X.toData _ (fun x => (hMat X.toData bas idx x).det)
      (fun y _ _ hb => det_hMat_weight idx y hb) x hx u hu
    rw [← hA, AR.Up.IC.pnorm_orth X.toData _ _ ho] at h1
    rw [ratio_eq_theta idx hs A (hab x A) v _ _ (hv v _ (mem_dom_of_isOrtho ho)), h1, hA,
      tauMat_rmul bas idx x hu, mul_assoc _ ‖_‖]
    rfl

end

end GlobalTheory.ThetaHol
