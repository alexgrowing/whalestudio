import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThetaL2OfAnalyticGenerator
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowEqOfBaseChange
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.NormalFormsEqOfKeyDataIsoComplex
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.AppellHumbertUnifTangentWeilPairing
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniqueLinearLiftOfHolomorphicAbelianVariet
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HermFormPullEqOfLbIsoPow
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries Matrix Topology
open MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory

namespace GlobalTheory.AbelianPartNorm

open GlobalTheory.KeyIsoNormal in

theorem exists_unif {P : Out.PolAV (Sp ℂ)} {rig : LB.Gen (P.L.pull (eSec P.A))} {th : P.L.Sec} {v : ℝ}
    (hv : Arch.IsThNormAt P rig th (RingHom.id ℂ) v) :
    ∃ (n : ℕ) (u : HolUnif P.A P.L n) (Hm : Matrix (Fin n) (Fin n) ℂ) (χ : u.Λ → ℂ)
      (θ : (Fin n → ℂ) → ℂ) (Fd : Set (Fin n → ℂ)),
      u.IsAH Hm χ ∧ u.IsRig rig ∧ u.IsFn th θ ∧ IsAddFundamentalDomain u.Λ Fd volume ∧
      v = (∫ z in Fd, ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (z ⬝ᵥ Hm.mulVec (star z)).re)) / (volume Fd).toReal := by
  obtain ⟨P', rig', th', φ, he, w, hc, hw, hr, hs, u', Hm, χ, θ, Fd, hAH, h₄, h₅, hFd, hv⟩ := hv
  have hid : spMap (RingHom.id ℂ) = 𝟙 (Sp ℂ) := Spec.map_id _
  have r := (maps_iff w _ (fun _ => eSec P.A) _ rig' rig (spMap (RingHom.id ℂ)) _
    (rigPull_le φ (spMap (RingHom.id ℂ)) he P.L) (fun _ => rfl)).1 hr
  rw [hid] at r he
  rw [Category.id_comp] at he
  have hc' := hc.congr hid rfl
  obtain ⟨u, hex, hΛ, hfr⟩ := exists_push P.isLB P'.isLB (Over.homMk φ (hc'.1.w.trans (Category.comp_id _))) hc' w
    ((isGen_iff w).1 hw) u'
  replace hex : ∀ z, (u.ex z).left = (u'.ex z).left ≫ φ := hex
  replace hfr : ∀ j k z, φ ((u'.ex z).left pt) ∈ P.L.U j → (u'.ex z).left pt ∈ P'.L.U k →
    u.fr j z = wv w (u'.ex z).left j k * u'.fr k z := hfr
  refine ⟨P'.g, u, Hm, fun l => χ ⟨l.1, hΛ ▸ l.2⟩, θ, Fd, ⟨hAH.1, hAH.2.1, fun l => hAH.2.2.1 _, fun l j z hz => ?_⟩,
    fun j hj => ?_, fun j z hz => ?_, hΛ ▸ hFd, hv⟩
  · rw [hex] at hz
    have hj : φ ((u'.ex z).left pt) ∈ P.L.U j := (top_le_preimage_iff_mem _ _).1 hz
    obtain ⟨k, hk⟩ := exists_chart P'.isLB ((u'.ex z).left pt)
    have hl : l.1 ∈ u'.Λ := hΛ ▸ l.2
    have hper : u'.ex (z + l) = u'.ex z := by rw [u'.ex_add, (u'.ker l).2 hl, _root_.mul_one]
    rw [hfr j k z hj hk, hfr j k (z + l) (hper ▸ hj) (hper ▸ hk), hper,
      hAH.2.2.2 ⟨l.1, hl⟩ k z ((top_le_preimage_iff_mem _ _).2 hk)]
    ring
  · have h0 : (u'.ex 0).left = eSec P'.A := by
      rw [(u'.ker 0).2 u'.Λ.zero_mem]
      change (toUnit _ ≫ η[P'.A]).left = η[P'.A].left
      rw [toUnit_unit, Category.id_comp]
    obtain ⟨k, hk⟩ := exists_chart P'.isLB (eSec P'.A pt)
    have hj' : φ (eSec P'.A pt) ∈ P.L.U (j PUnit.unit) := by
      have := mem_pull.1 (hj (Set.mem_univ pt))
      rw [← he] at this
      exact this
    have hk' : (𝟙 (Sp ℂ) : Sp ℂ ⟶ Sp ℂ) pt ∈ (P'.L.pull (eSec P'.A)).U (fun _ => k) := mem_pull.2 hk
    have e := congrArg Units.val (r _ (𝟙 (Sp ℂ)) pt j (fun _ => k) (fun _ => hj') (fun _ => hk))
    rw [Fintype.prod_unique, zpow_one, Category.id_comp, Category.id_comp, Units.val_mul] at e
    rw [hfr _ k 0 (h0 ▸ hj') (h0 ▸ hk), h0, h₄ (fun _ => k) ((top_le_preimage_iff_mem (𝟙 _) _).2 hk')]
    apply toStalk.injective
    rw [map_mul]
    exact (congrArg₂ (· * ·) (gw_eq_toStalk w _ hj' hk).symm (gm_eq_toStalk _ _ hk' _).symm).trans
      (e.symm.trans (gm_eq_toStalk _ _ (hj (Set.mem_univ pt)) _))
  · rw [hex] at hz ⊢
    have hj : φ ((u'.ex z).left pt) ∈ P.L.U j := (top_le_preimage_iff_mem _ _).1 hz
    obtain ⟨k, hk⟩ := exists_chart P'.isLB ((u'.ex z).left pt)
    have e := (KeyCancel.appLE_eq_iff_stalk w th th').1 hs _ (u'.ex z).left pt j k hj hk
    rw [gs_eq_toStalk _ _ hj, gs_eq_toStalk _ _ hk, gw_eq_toStalk w _ hj hk, ← map_mul] at e
    rw [toStalk.injective e, hfr j k z hj hk, h₅ k z ((top_le_preimage_iff_mem _ _).2 hk)]
    ring

theorem thetaCharOff_eq {g n : ℕ} (S : Finset (Fin g)) (e : Fin n ≃ {k // k ∉ S}) (τ : Matrix (Fin g) (Fin g) ℂ)
    (a b z : Fin g → ℂ) (ha : ∀ k ∈ S, a k = 0) :
    thetaCharOff S τ a b z = thetaChar (τ.submatrix (fun i => (e i).1) (fun i => (e i).1)) (fun i => a (e i).1)
      (fun i => b (e i).1) (fun i => z (e i).1) := by
  classical
  let ε : {m : Fin g → ℤ // ∀ k ∈ S, m k = 0} ≃ (Fin n → ℤ) :=
    { toFun := fun m i => m.1 (e i).1
      invFun := fun m => ⟨fun k => if h : k ∈ S then 0 else m (e.symm ⟨k, h⟩), fun k hk => dif_pos hk⟩
      left_inv := fun m => Subtype.ext (funext fun k => by
        by_cases h : k ∈ S
        · simp [h, m.2 k h]
        · simp [h])
      right_inv := fun m => funext fun i => by simp [(e i).2] }
  have hs : ∀ f : Fin g → ℂ, (∀ k ∈ S, f k = 0) → ∑ k, f k = ∑ i, f (e i).1 := fun f hf => by
    rw [e.sum_comp (fun k => f k.1), ← Finset.sum_subtype Sᶜ (by simp) f, ← Finset.sum_compl_add_sum S,
      Finset.sum_eq_zero hf, add_zero]
  unfold thetaCharOff thetaChar
  rw [← ε.tsum_eq]
  refine tsum_congr fun m => ?_
  have h0 : ∀ k ∈ S, ((fun i => (m.1 i : ℂ)) + a) k = 0 := fun k hk => by simp [m.2 k hk, ha k hk]
  have h1 : ((fun i => ((ε m i : ℤ) : ℂ)) + fun i => a (e i).1) = fun i => ((fun i => (m.1 i : ℂ)) + a) (e i).1 := rfl
  rw [h1]
  generalize ((fun i => (m.1 i : ℂ)) + a) = t at h0
  simp only [dotProduct, Matrix.mulVec]
  rw [hs _ (fun k hk => by rw [h0 k hk, zero_mul]), hs _ (fun k hk => by rw [h0 k hk, zero_mul])]
  simp only [Matrix.submatrix_apply, Pi.add_apply]
  congr 3
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hs _ (fun k hk => by rw [h0 k hk, mul_zero])]

open GlobalTheory.ThetaMean in
theorem exists_lattice {n : ℕ} {τ : Matrix (Fin n) (Fin n) ℂ} (hp : (τ.map Complex.im).PosDef) :
    ∃ Λ : Submodule ℤ (Fin n → ℂ), DiscreteTopology Λ ∧ Submodule.span ℝ (Λ : Set (Fin n → ℂ)) = ⊤ ∧
      ∀ x, x ∈ Λ ↔ ∃ a b : Fin n → ℤ, x = (fun i => (a i : ℂ)) + τ *ᵥ (fun i => (b i : ℂ)) := by
  let L : (Fin n ⊕ Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℂ) := LinearEquiv.ofBijective (periodMap τ) (periodMap_bijective hp)
  have hL (p : Fin n ⊕ Fin n → ℝ) : L p = periodMap τ p := rfl
  let b := (Pi.basisFun ℝ (Fin n ⊕ Fin n)).map L
  refine ⟨Submodule.span ℤ (Set.range b), inferInstance, ZSpan.span_top b, fun x => ?_⟩
  obtain ⟨p, rfl⟩ := L.surjective x
  rw [Module.Basis.mem_span_iff_repr_mem]
  have hr (i) : b.repr (L p) i = p i := by simp [b]
  simp only [hr]
  rw [hL]
  constructor
  · intro hz
    choose k hk using hz
    refine ⟨fun i => k (.inl i), fun i => k (.inr i), ?_⟩
    rw [periodMap_apply]
    simp [← hk]
  · rintro ⟨m, n, hmn⟩
    have : p = Sum.elim (fun i => (m i : ℝ)) (fun i => (n i : ℝ)) := by
      apply (periodMap_bijective hp).1
      rw [hmn, periodMap_apply]
      simp
    rintro (i | i)
    · exact ⟨m i, by simp [this]⟩
    · exact ⟨n i, by simp [this]⟩

theorem im_form_real {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ} (hs : τ.IsSymm) (hp : (τ.map Complex.im).PosDef)
    (m n m' n' : Fin g → ℝ) :
    (((fun i => (m i : ℂ)) + τ *ᵥ (fun i => (n i : ℂ))) ⬝ᵥ
      ((τ.map Complex.im)⁻¹).map (fun x : ℝ => (x : ℂ)) *ᵥ
        star ((fun i => (m' i : ℂ)) + τ *ᵥ (fun i => (n' i : ℂ)))).im =
      n ⬝ᵥ m' - m ⬝ᵥ n' := by
  set Y := τ.map Complex.im with hY
  set X := τ.map Complex.re with hX
  have hXs : X.IsSymm := hs.map _
  have hYs : Y.IsSymm := hs.map _
  have hu : IsUnit Y.det := (Matrix.isUnit_iff_isUnit_det _).1 hp.isUnit
  have gen : ∀ u v : Fin g → ℂ, (u ⬝ᵥ (Y⁻¹).map (fun x : ℝ => (x : ℂ)) *ᵥ star v).im =
      (fun i => (u i).im) ⬝ᵥ Y⁻¹ *ᵥ (fun i => (v i).re) - (fun i => (u i).re) ⬝ᵥ Y⁻¹ *ᵥ (fun i => (v i).im) := by
    intro u v
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Complex.im_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp
    ring
  have him : ∀ m n : Fin g → ℝ, (fun i => (((fun i => (m i : ℂ)) + τ *ᵥ (fun i => (n i : ℂ))) i).im) = Y *ᵥ n := by
    intro m n; funext i; simp [Matrix.mulVec, dotProduct, hY]
  have hre : ∀ m n : Fin g → ℝ, (fun i => (((fun i => (m i : ℂ)) + τ *ᵥ (fun i => (n i : ℂ))) i).re) =
      m + X *ᵥ n := by
    intro m n; funext i; simp [Matrix.mulVec, dotProduct, hX]
  have sd : ∀ {M : Matrix (Fin g) (Fin g) ℝ}, M.IsSymm → ∀ u v : Fin g → ℝ, u ⬝ᵥ M *ᵥ v = v ⬝ᵥ M *ᵥ u := by
    intro M hM u v
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hM.eq, dotProduct_comm]
  rw [gen, him, him, hre, hre, sd hYs.inv (Y *ᵥ _), Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec, Matrix.one_mulVec, add_dotProduct, add_dotProduct,
    dotProduct_comm (X *ᵥ _), dotProduct_comm (X *ᵥ _), sd hXs, dotProduct_comm m' n]
  ring

open GlobalTheory.ThetaMean in

theorem mem_of_integral {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ} (hs : τ.IsSymm) (hp : (τ.map Complex.im).PosDef)
    (x : Fin g → ℂ) (hx : ∀ a b : Fin g → ℤ, ∃ k : ℤ, (k : ℝ) = (x ⬝ᵥ
      ((τ.map Complex.im)⁻¹).map (fun x : ℝ => (x : ℂ)) *ᵥ
        star ((fun i => (a i : ℂ)) + τ *ᵥ (fun i => (b i : ℂ)))).im) :
    ∃ a b : Fin g → ℤ, x = (fun i => (a i : ℂ)) + τ *ᵥ (fun i => (b i : ℂ)) := by
  obtain ⟨p, rfl⟩ := (periodMap_bijective hp).2 x
  rw [periodMap_apply] at hx ⊢
  have h : ∀ a b : Fin g → ℤ, ∃ k : ℤ, (k : ℝ) = (fun i => p (.inr i)) ⬝ᵥ (fun i => (a i : ℝ)) -
      (fun i => p (.inl i)) ⬝ᵥ (fun i => (b i : ℝ)) := fun a b => by
    obtain ⟨k, hk⟩ := hx a b
    refine ⟨k, hk.trans ?_⟩
    rw [← im_form_real hs hp]
    simp
  have h1 : ∀ i, ∃ k : ℤ, p (.inl i) = k := fun i => by
    obtain ⟨k, hk⟩ := h 0 (Pi.single i 1)
    refine ⟨-k, ?_⟩
    simp [dotProduct, Pi.single_apply] at hk
    simp [hk]
  have h2 : ∀ i, ∃ k : ℤ, p (.inr i) = k := fun i => by
    obtain ⟨k, hk⟩ := h (Pi.single i 1) 0
    refine ⟨k, ?_⟩
    simp [dotProduct, Pi.single_apply] at hk
    simp [hk]
  choose a ha using h1
  choose b hb using h2
  exact ⟨a, b, by simp [ha, hb]⟩

theorem form_eq {n g : ℕ} {τ : Matrix (Fin n) (Fin n) ℂ} {c₁ c₂ : Fin n → ℂ} (hs : τ.IsSymm)
    (hp : (τ.map Complex.im).PosDef) (h₁ : ∀ i, c₁ i = 0 ∨ c₁ i = 1 / 2) (h₂ : ∀ i, c₂ i = 0 ∨ c₂ i = 1 / 2)
    {κ : ℂ} (hκ : κ ≠ 0) {Λ : Submodule ℤ (Fin g → ℂ)} {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian)
    {χ : Λ → ℂ} (hχ : ∀ l, ‖χ l‖ = 1) {θ : (Fin g → ℂ) → ℂ}
    (hθ : ∀ (l : Λ) z, θ (z + l) = χ l * Complex.exp (Real.pi * hermForm Hm z l + Real.pi / 2 * hermForm Hm l l) * θ z)
    (F : (Fin n → ℂ) →ₗ[ℂ] (Fin g → ℂ))
    (hF : ∀ a b : Fin n → ℤ, F ((fun i => (a i : ℂ)) + τ *ᵥ (fun i => (b i : ℂ))) ∈ Λ)
    {ρ : (Fin n → ℂ) → ℂ} (hρ : Differentiable ℂ ρ) (hρn : ∀ x, ρ x ≠ 0) (hρ0 : ρ 0 = 1)
    (e : ∀ x, κ * thetaChar τ c₁ c₂ x = θ (F x) * ρ x) :
    (∀ x y, hermForm Hm (F x) (F y) = x ⬝ᵥ ((τ.map Complex.im)⁻¹).map (fun x : ℝ => (x : ℂ)) *ᵥ star y) ∧
      ∀ x, ‖θ (F x)‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm (F x) (F x)).re) =
        ‖κ‖ ^ 2 * (‖thetaChar τ c₁ c₂ x‖ ^ 2 * Real.exp (-2 * Real.pi * ((fun i => (x i).im) ⬝ᵥ
          (((τ.map Complex.im)⁻¹) *ᵥ fun i => (x i).im)))) := by
  obtain ⟨Λ₀, d₀, s₀, m₀⟩ := exists_lattice hp
  obtain ⟨H₀, hH₀⟩ : ∃ H₀, H₀ = (1 : Matrix (Fin n) (Fin n) ℂ)ᵀ * ((τ.map Complex.im)⁻¹).map (fun x : ℝ => (x : ℂ)) *
    (1 : Matrix (Fin n) (Fin n) ℂ).map (starRingEnd ℂ) := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q : (Fin n → ℂ) → ℂ, q = fun z => Real.pi / 2 * (((1 : Matrix (Fin n) (Fin n) ℂ) *ᵥ z) ⬝ᵥ
    (((τ.map Complex.im)⁻¹).map (fun x : ℝ => (x : ℂ)) *ᵥ ((1 : Matrix (Fin n) (Fin n) ℂ) *ᵥ z))) := ⟨_, rfl⟩
  have hq0 : q 0 = 0 := by simp [hq]
  have hqd : Differentiable ℂ q := by
    rw [hq]
    simp only [dotProduct, Matrix.mulVec]
    fun_prop
  obtain ⟨an1, an2⟩ := GlobalTheory.ThetaAH.exp_mul_thetaChar_automorphy n τ 1 H₀ c₁ c₂ q hs hp h₁ h₂ hH₀ (fun z => by rw [hq])
  simp only [Matrix.one_mulVec] at an1 an2
  obtain ⟨θd, θne⟩ := (GlobalTheory.ThetaHalf.thetaChar_holomorphic_ne_zero n c₁ c₂ h₁ h₂).1 _ hs hp
  have hH₀h : H₀.IsHermitian := hH₀ ▸ (GlobalTheory.ThetaSquareIntegrable.posDef_form hp (by simp)).1
  have hc : ∀ l : Λ₀, ∃ x : ℂ, ‖x‖ = 1 ∧ ∀ z, Complex.exp (q (z + l)) * thetaChar τ c₁ c₂ (z + l) =
      x * Complex.exp (Real.pi * hermForm H₀ z l + Real.pi / 2 * hermForm H₀ l l) *
        (Complex.exp (q z) * thetaChar τ c₁ c₂ z) := fun l => by
    obtain ⟨a, b, h⟩ := (m₀ l).1 l.2
    exact an2 l a b h
  choose χ₀ hχ₀ hl₀ using hc
  have hΛ : ∀ l : Λ₀, F l ∈ Λ := fun l => by
    obtain ⟨a, b, h⟩ := (m₀ l).1 l.2
    rw [h]; exact hF a b
  set H₂ := (LinearMap.toMatrix' F).transpose * Hm * (LinearMap.toMatrix' F).transpose.conjTranspose with hH₂
  have hH₂h : H₂.IsHermitian := Matrix.isHermitian_mul_mul_conjTranspose _ hH
  have hsub : ∀ z w, hermForm (H₀ - H₂) z w = hermForm H₀ z w - hermForm Hm (F z) (F w) := fun z w => by
    have := PullHermitian.hermForm_sub_smul H₀ H₂ 1 1 z w
    rwa [one_smul, one_smul, _root_.one_mul, _root_.one_mul, hH₂, PullHermitian.hermForm_pull] at this
  have hrd : Differentiable ℂ fun x => Complex.exp (q x) * ρ x := hqd.cexp.mul hρ
  have key := appellHumbert_trivial_of_nowhere_vanishing n Λ₀ s₀ (H₀ - H₂) (fun l => χ₀ l / χ ⟨F l, hΛ l⟩)
    (fun x => Complex.exp (q x) * ρ x) (hH₀h.sub hH₂h) (fun l => by simp [hχ, hχ₀]) hrd
    (fun x => mul_ne_zero (Complex.exp_ne_zero _) (hρn x)) (fun l z => by
      rw [← sub_eq_zero]
      refine GlobalTheory.ThetaSquareIntegrable.eq_zero_of_entire_mul (D := fun z : Fin n → ℂ => Complex.exp (q (z + l)) * ρ (z + l) -
        χ₀ l / χ ⟨F l, hΛ l⟩ * Complex.exp (Real.pi * hermForm (H₀ - H₂) z l + Real.pi / 2 * hermForm (H₀ - H₂) l l) *
          (Complex.exp (q z) * ρ z)) θd θne ?_ (Filter.Eventually.of_forall fun x => ?_)
      · have c3 := hrd.continuous
        have c4 : Continuous fun z => hermForm (H₀ - H₂) z l := by
          simp only [hermForm, dotProduct]; fun_prop
        exact ((c3.comp (continuous_add_const _)).sub ((continuous_const.mul
          ((continuous_const.mul c4).add continuous_const).cexp).mul c3)).continuousAt
      · have e1 := e x
        have e2 := e (x + l)
        have e3 := hθ ⟨F l, hΛ l⟩ (F x)
        have e4 := hl₀ l x
        rw [map_add, e3] at e2
        have h4 : χ ⟨F l, hΛ l⟩ ≠ 0 := norm_ne_zero_iff.1 (by rw [hχ]; exact one_ne_zero)
        simp only [hsub]
        have e5 : ∀ a b a' b' : ℂ, Complex.exp (Real.pi * (a - a') + Real.pi / 2 * (b - b')) =
            Complex.exp (Real.pi * a + Real.pi / 2 * b) / Complex.exp (Real.pi * a' + Real.pi / 2 * b') := by
          intro a b a' b'
          rw [← Complex.exp_sub]
          congr 1
          ring
        rw [e5]
        have h7 := Complex.exp_ne_zero (Real.pi * hermForm Hm (F x) (F l) + Real.pi / 2 * hermForm Hm (F l) (F l))
        simp only at e2
        generalize Complex.exp (Real.pi * hermForm Hm (F x) (F l) + Real.pi / 2 * hermForm Hm (F l) (F l)) = s' at *
        generalize Complex.exp (Real.pi * hermForm H₀ x l + Real.pi / 2 * hermForm H₀ l l) = s at *
        generalize χ ⟨F l, hΛ l⟩ = c at *
        apply mul_left_cancel₀ (mul_ne_zero hκ (mul_ne_zero h4 h7))
        have k1 := mul_inv_cancel₀ h4
        have k2 := mul_inv_cancel₀ h7
        rw [div_eq_mul_inv (χ₀ l), div_eq_mul_inv s]
        linear_combination (c * s' * Complex.exp (q (x + l)) * ρ (x + l)) * e1 -
          (ρ x * Complex.exp (q (x + l))) * e2 + κ * ρ x * e4 -
          κ * thetaChar τ c₁ c₂ x * χ₀ l * s * Complex.exp (q x) * ρ x * (s' * s'⁻¹ * k1 + k2))
  have hf : ∀ x y, hermForm Hm (F x) (F y) = hermForm H₀ x y := fun x y => by
    have h := hsub x y
    rw [key.1] at h
    have h0 : hermForm (0 : Matrix (Fin n) (Fin n) ℂ) x y = 0 := by simp [hermForm]
    rw [h0] at h
    exact (sub_eq_zero.1 h.symm).symm
  refine ⟨fun x y => by rw [hf, hH₀]; simp [hermForm], fun x => ?_⟩
  have h1 := key.2.2 x
  simp only [hq0, hρ0, Complex.exp_zero, _root_.mul_one] at h1
  have h2 : θ (F x) = κ * Complex.exp (q x) * thetaChar τ c₁ c₂ x := by
    linear_combination -(θ (F x)) * h1 - Complex.exp (q x) * e x
  rw [hf, ← an1 x, h2, norm_mul, norm_mul]
  ring

theorem mean_eq {n g : ℕ} {τ : Matrix (Fin n) (Fin n) ℂ} {c₁ c₂ : Fin n → ℂ} (hs : τ.IsSymm)
    (hp : (τ.map Complex.im).PosDef) (h₁ : ∀ i, c₁ i = 0 ∨ c₁ i = 1 / 2) (h₂ : ∀ i, c₂ i = 0 ∨ c₂ i = 1 / 2)
    {κ : ℂ} (hκ : κ ≠ 0) {Λ : Submodule ℤ (Fin g → ℂ)} [DiscreteTopology Λ] {Hm : Matrix (Fin g) (Fin g) ℂ}
    (hH : Hm.IsHermitian) (hint : ∀ a b : Λ, ∃ k : ℤ, (k : ℝ) = (hermForm Hm a b).im)
    {χ : Λ → ℂ} (hχ : ∀ l, ‖χ l‖ = 1) {θ : (Fin g → ℂ) → ℂ}
    (hθ : ∀ (l : Λ) z, θ (z + l) = χ l * Complex.exp (Real.pi * hermForm Hm z l + Real.pi / 2 * hermForm Hm l l) * θ z)
    (F : (Fin n → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (hFs : Function.Surjective F)
    (hF : ∀ a b : Fin n → ℤ, F ((fun i => (a i : ℂ)) + τ *ᵥ (fun i => (b i : ℂ))) ∈ Λ)
    {ρ : (Fin n → ℂ) → ℂ} (hρ : Differentiable ℂ ρ) (hρn : ∀ x, ρ x ≠ 0) (hρ0 : ρ 0 = 1)
    (e : ∀ x, κ * thetaChar τ c₁ c₂ x = θ (F x) * ρ x) {Fd : Set (Fin g → ℂ)}
    (hFd : IsAddFundamentalDomain Λ Fd volume) :
    (∫ z in Fd, ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm z z).re)) / (volume Fd).toReal =
      ‖κ‖ ^ 2 * (Real.sqrt (2 ^ n * (τ.map Complex.im).det))⁻¹ := by
  obtain ⟨k1, k2⟩ := form_eq hs hp h₁ h₂ hκ hH hχ hθ F hF hρ hρn hρ0 e
  have hFi : Function.Injective F := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra h0
    have h1 := (GlobalTheory.ThetaSquareIntegrable.posDef_form (h := 1) hp (by simp)).2 x h0
    have h2 := k1 x x
    rw [hx] at h2
    simp [hermForm] at h1 h2
    rw [← h2] at h1
    simp at h1
  let Fe := LinearEquiv.ofBijective F ⟨hFi, hFs⟩
  obtain rfl : n = g := by simpa using Fe.finrank_eq
  obtain ⟨h, hh⟩ : ∃ h, h = LinearMap.toMatrix' Fe.symm.toLinearMap := ⟨_, rfl⟩
  have hm : ∀ x, h *ᵥ F x = x := fun x => by
    rw [hh, LinearMap.toMatrix'_mulVec]
    exact Fe.symm_apply_apply x
  have hu : IsUnit h.det := by
    rw [hh, LinearMap.det_toMatrix']
    exact Fe.symm.isUnit_det'
  have hΛ : ∀ lam, lam ∈ Λ.toAddSubgroup ↔ ∃ a b : Fin n → ℤ,
      h *ᵥ lam = (fun i => (a i : ℂ)) + τ *ᵥ (fun i => (b i : ℂ)) := fun lam => by
    obtain ⟨x, rfl⟩ := hFs lam
    rw [hm]
    constructor
    · intro hx
      refine mem_of_integral hs hp x fun a b => ?_
      rw [← k1]
      exact hint ⟨_, hx⟩ ⟨_, hF a b⟩
    · rintro ⟨a, b, rfl⟩
      exact hF a b
  obtain ⟨Fd', hFd', hI⟩ := GlobalTheory.ThetaMean.exists_fundamentalDomain_mean_norm_sq_thetaChar n τ h c₁ c₂ _ hs hp hu h₁ h₂ hΛ
  replace hFd : IsAddFundamentalDomain Λ.toAddSubgroup Fd volume := hFd
  have hcount : Countable Λ.toAddSubgroup := countable_of_Lindelof_of_discrete (X := Λ)
  have hinv : ∀ (l : Λ.toAddSubgroup) (z : Fin n → ℂ), ‖θ (l +ᵥ z)‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm (l +ᵥ z) (l +ᵥ z)).re) =
      ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm z z).re) := fun l z => by
    have : l +ᵥ z = z + (⟨l.1, l.2⟩ : Λ) := add_comm _ _
    rw [this, hθ, AppellHumbertTrivial.re_hermForm_add_self hH, norm_mul, norm_mul, hχ, Complex.norm_exp, _root_.one_mul, mul_pow, ← Real.exp_nat_mul,
      mul_comm (Real.exp _), _root_.mul_assoc, ← Real.exp_add]
    congr 2
    simp
    ring
  have hvol : (volume Fd).toReal = (volume Fd').toReal := by
    simpa [Measure.real] using hFd.setIntegral_eq hFd' (f := fun _ => (1 : ℝ)) fun _ _ => rfl
  rw [hFd.setIntegral_eq hFd' hinv, hvol, ← hI, ← mul_div_assoc, ← MeasureTheory.integral_const_mul]
  congr 2
  funext z
  obtain ⟨x, rfl⟩ := hFs z
  rw [k2, hm]

theorem exists_lift_frame (D₀ : Out.DegPre ℂ) {n g : ℕ} (u : HolUnif D₀.P.A D₀.P.L n) {Hm : Matrix (Fin n) (Fin n) ℂ}
    {χ : u.Λ → ℂ} (hAH : u.IsAH Hm χ) (hrig : u.IsRig D₀.rig) {th : D₀.P.L.Sec} {θ : (Fin n → ℂ) → ℂ}
    (hθ : u.IsFn th θ) (G : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ D₀.P.A)) (hadd : ∀ z w, G (z + w) = G z * G w)
    (hhol : IsHolTo Set.univ fun z => (G z).left) (hon : Function.Surjective G) {ψ : (Fin g → ℂ) → ℂ}
    (hψ : IsFnInRigFrame D₀ (fun z => (G z).left) th ψ) :
    ∃ (F : (Fin g → ℂ) →ₗ[ℂ] (Fin n → ℂ)) (ρ : (Fin g → ℂ) → ℂ), Function.Surjective F ∧
      (∀ z, G z = 1 → F z ∈ u.Λ) ∧ (∀ z, (∀ s : ℂ, G (s • z) = 1) → F z = 0) ∧
      Differentiable ℂ ρ ∧ (∀ z, ρ z ≠ 0) ∧ ρ 0 = 1 ∧ ∀ z, ψ z = θ (F z) * ρ z := by
  obtain ⟨-, -, -, -, t1, t2, -⟩ := GlobalTheory.AHWeil.tangent_and_weil_of_isAH GlobalTheory.thetaUnifAV_all D₀.P n u Hm χ hAH
  obtain ⟨F, hF, -⟩ := GlobalTheory.existsUnique_linear_lift_of_isHolTo D₀.P.A D₀.P.isAb D₀.P.L n g u t1 t2 G hadd hhol
  obtain ⟨fr, f1, f2, f3, f4, f5⟩ := hψ
  have hL := D₀.P.isLB
  have hd := u.discrete
  have hker : ∀ z, G z = 1 → F z ∈ u.Λ := fun z hz => by rw [← u.ker, hF, hz]
  have hFd : Differentiable ℂ F := (LinearMap.toContinuousLinearMap F).differentiable
  have tr : ∀ {U : D₀.P.A.left.Opens} {z}, ⊤ ≤ (G z).left ⁻¹ᵁ U → ⊤ ≤ (u.ex (F z)).left ⁻¹ᵁ U :=
    fun h => by rwa [hF]
  obtain ⟨r, hr, hrφ⟩ := PullHermitian.exists_glue
    (fun i : D₀.P.L.ι => {z | ⊤ ≤ (G z).left ⁻¹ᵁ D₀.P.L.U i})
    (fun i => by simpa using (hhol _ 0).1)
    (fun z => PullHermitian.exists_chart (G z).left hL)
    (fun i z => u.fr i (F z) / fr i z)
    (fun i => by
      have d2 := (u.fr_hol i).comp (s := {z | ⊤ ≤ (G z).left ⁻¹ᵁ D₀.P.L.U i})
        hFd.differentiableOn fun z hz => tr hz
      simp only [div_eq_mul_inv]
      exact d2.mul ((f1 i).inv fun z hz => f2 i z hz))
    (fun i j z hi hj => by
      have h1 := f3 i j z (PullHermitian.inf_of _ hi hj)
      have h2 := u.fr_compat i j (F z) (tr (PullHermitian.inf_of _ hi hj))
      rw [hF] at h2
      rw [div_eq_div_iff (f2 _ _ hi) (f2 _ _ hj), h1, h2]
      ring)
  refine ⟨F, r, ?_, hker, fun z hz => ?_, hr, fun z => ?_, ?_, fun z => ?_⟩
  · have hc : Countable u.Λ := countable_of_Lindelof_of_discrete
    have hs : Function.Surjective fun l : u.Λ => (LinearMap.range F).mkQ l := fun y => by
      obtain ⟨y, rfl⟩ := (LinearMap.range F).mkQ_surjective y
      obtain ⟨z, hz⟩ := hon (u.ex y)
      have h1 : y - F z ∈ u.Λ := by
        have h2 := u.ex_add (y - F z) (F z)
        rw [sub_add_cancel, hF, hz] at h2
        exact (u.ker _).1 (mul_eq_right.1 h2.symm)
      refine ⟨⟨_, h1⟩, ?_⟩
      simp
    have hq := hs.countable
    rw [← LinearMap.range_eq_top, ← Submodule.Quotient.subsingleton_iff]
    by_contra hn
    rw [not_subsingleton_iff_nontrivial] at hn
    obtain ⟨y, hy⟩ := exists_ne (0 : (Fin n → ℂ) ⧸ LinearMap.range F)
    have hC := (smul_left_injective ℂ hy).countable
    exact not_countable (Complex.ofReal_injective.countable)
  · have hm : ∀ t : ℂ, t • F z ∈ u.Λ := fun t => by
      rw [← map_smul]
      exact hker _ (hz t)
    have hc : Continuous fun t : ℂ => (⟨t • F z, hm t⟩ : u.Λ) :=
      Continuous.subtype_mk (continuous_id.smul continuous_const) _
    have h := PreconnectedSpace.constant (inferInstance : PreconnectedSpace ℂ) hc (x := 1) (y := 0)
    simpa using congrArg Subtype.val h
  · obtain ⟨i, hi⟩ := PullHermitian.exists_chart (G z).left hL
    rw [hrφ i z hi]
    exact div_ne_zero (u.fr_ne _ _ (tr hi)) (f2 _ _ hi)
  · obtain ⟨i, hi⟩ := PullHermitian.exists_chart (G 0).left hL
    have h0 : (G 0).left = eSec D₀.P.A := by
      rw [← hF, map_zero, (u.ker 0).2 u.Λ.zero_mem]
      change (toUnit _ ≫ η[D₀.P.A]).left = η[D₀.P.A].left
      rw [toUnit_unit, Category.id_comp]
    rw [hrφ i 0 hi, map_zero, div_eq_one_iff_eq (f2 _ _ hi), f4 i hi]
    exact hrig (fun _ => i) fun q hq => mem_pull.2 (by rw [← h0]; exact hi hq)
  · obtain ⟨i, hi⟩ := PullHermitian.exists_chart (G z).left hL
    have h1 := hθ i (F z) (tr hi)
    rw [hF, f5 i z hi] at h1
    rw [hrφ i z hi, ← mul_div_assoc, ← h1, mul_div_cancel_right₀ _ (f2 _ _ hi)]

theorem fn_automorphy {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} (hL : L.IsLB) {n : ℕ} (u : HolUnif A L n)
    {Hm : Matrix (Fin n) (Fin n) ℂ} {χ : u.Λ → ℂ} (hAH : u.IsAH Hm χ) {th : L.Sec} {θ : (Fin n → ℂ) → ℂ}
    (hθ : u.IsFn th θ) (l : u.Λ) (z : Fin n → ℂ) :
    θ (z + l) = χ l * Complex.exp (Real.pi * hermForm Hm z l + Real.pi / 2 * hermForm Hm l l) * θ z := by
  obtain ⟨i, hi⟩ := PullHermitian.exists_chart (u.ex z).left hL
  have hper : u.ex (z + l) = u.ex z := by rw [u.ex_add, (u.ker l).2 l.2, _root_.mul_one]
  have h1 := hθ i z hi
  have h2 := hθ i (z + l) (hper ▸ hi)
  rw [hper, h1, hAH.2.2.2 l i z hi] at h2
  apply mul_right_cancel₀ (u.fr_ne i (z + l) (hper ▸ hi))
  rw [← h2]
  simp only [hermForm]
  ring

theorem norm_eq : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (a : ArcIn Dw l β ℂ (σ.comp β)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y a χ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (Ha : HolArc Y σ a χ W Fu) (th : a.D₀.P.L.Sec) (Θ : ThetaDat Ha th) (w : ℂ) (v : ℝ), Ha.T < w.im → Arch.IsThNormAt a.D₀.P a.D₀.rig th (RingHom.id ℂ) v → v = ‖Θ.κ‖ ^ 2 * (Real.sqrt (2 ^ (g - Θ.S.card) * ((((Θ.τ w).map Complex.im).submatrix (fun k : {k // k ∉ Θ.S} => k.1) (fun k : {k // k ∉ Θ.S} => k.1)).det)))⁻¹ := by
  intro _ _ E _ _ _ H Dw l Xo c σ _ _ O _ β Y a χ W g ty Fu Ha th Θ w v hw hv
  classical
  obtain ⟨n, u, Hm, χl, θ, Fd, hAH, hrig, hfn, hFd, rfl⟩ := exists_unif hv
  have hj : (Out.TF (R := ℂ) ℂ).hom = 𝟙 (Sp ℂ) := by
    change Spec.map _ ≫ Spec.map _ = _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
    exact Spec.map_id _
  let j : 𝟙_ (Over (Sp ℂ)) ⟶ Out.TF (R := ℂ) ℂ := Over.homMk (𝟙 (Sp ℂ)) ((Category.id_comp _).trans hj)
  let G : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ a.D₀.P.A) := fun z =>
    Over.homMk (Ha.ex₀ z).b.left ((Over.w _).trans hj)
  have hG : ∀ z, G z = j ≫ (Ha.ex₀ z).b := fun z => Over.OverMorphism.ext (Category.id_comp _).symm
  have hG1 : ∀ z, (Ha.ex₀ z).b = Out.DegPre.zeroF a.D₀ ℂ → G z = 1 := fun z hz => by
    rw [hG, hz]
    exact MonObj.comp_one j
  obtain ⟨F, ρ, Fs, Fk, F0, ρd, ρn, ρ0, hρ⟩ := exists_lift_frame a.D₀ u hAH hrig hfn G
    (fun z z' => by
      rw [hG, hG, hG, (Ha.add z z').1]
      exact MonObj.comp_mul j _ _) Ha.hol_b
    (fun p => by
      obtain ⟨x, hx⟩ := GlobalTheory.TorusExt.exists_lift (D := a.D₀) (F := ℂ) (toUnit _ ≫ p)
      obtain ⟨z, rfl⟩ := Ha.onto x
      refine ⟨z, ?_⟩
      rw [hG, hx, ← Category.assoc, toUnit_unique (j ≫ toUnit _) (𝟙 _), Category.id_comp]) (Θ.onB w hw)
  obtain ⟨hs, hp⟩ := Θ.pos w hw
  have hm := GlobalTheory.ThetaSquareIntegrable.mulVec_period (Ha.Pw w) Θ.bas Θ.h (Θ.τ w) (Θ.per w)
  have hh : IsUnit Θ.h.det := by
    have : Θ.h * (Matrix.of fun i k => Ha.Pw w (Θ.bas (Pi.single (.inl k) 1)) i) = 1 := by
      ext i k
      have := congrFun (Θ.per w k).1 i
      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.one_apply, Pi.single_apply] using this
    exact Matrix.isUnit_det_of_right_inverse this
  have hi1 : ∀ z, Θ.h⁻¹ *ᵥ (Θ.h *ᵥ z) = z := fun z => by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hh, Matrix.one_mulVec]
  have hi2 : ∀ z, Θ.h *ᵥ (Θ.h⁻¹ *ᵥ z) = z := fun z => by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hh, Matrix.one_mulVec]
  have hP : ∀ t, F (Ha.Pw w t) = F (Ha.P₀ t) := fun t => by
    rw [Ha.Pw_eq, map_add, map_smul, F0 _ fun s => hG1 _ (Ha.shift s t).1, smul_zero, add_zero]
  have hS : ∀ k ∈ Θ.S, F (Θ.h⁻¹ *ᵥ Pi.single k 1) = 0 := fun k hk => by
    rw [← (Θ.per w k).1, hi1, hP]
    have h1 := (Ha.riemann _).1 ((Θ.orth (Pi.single (.inl k) 1)).2 ⟨fun k' => by simp, fun k' hk' => by
      have : k' ≠ k := fun e => hk' (e ▸ hk)
      simp [this]⟩)
    exact F0 _ fun s => hG1 _ (h1.2 s).choose_spec.1.1
  let e : Fin (g - Θ.S.card) ≃ {k // k ∉ Θ.S} := (Fintype.equivFinOfCardEq (by simp)).symm
  let ext : (Fin (g - Θ.S.card) → ℂ) →ₗ[ℂ] (Fin g → ℂ) :=
    { toFun := fun x k => if h : k ∈ Θ.S then 0 else x (e.symm ⟨k, h⟩)
      map_add' := fun x y => funext fun k => by by_cases h : k ∈ Θ.S <;> simp [h]
      map_smul' := fun s x => funext fun k => by by_cases h : k ∈ Θ.S <;> simp [h] }
  have hext : ∀ x i, ext x (e i).1 = x i := fun x i => by simp [ext, (e i).2]
  let L := Θ.h⁻¹.mulVecLin ∘ₗ ext
  let F' := F ∘ₗ L
  have hF' : ∀ y, F' (fun i => y (e i).1) = F (Θ.h⁻¹ *ᵥ y) := fun y => by
    have h1 : y = ext (fun i => y (e i).1) + ∑ k ∈ Θ.S, y k • Pi.single k 1 := by
      funext k
      by_cases h : k ∈ Θ.S <;> simp [ext, h, Finset.sum_apply, Pi.single_apply]
    conv_rhs => rw [h1]
    rw [Matrix.mulVec_add, map_add, Matrix.mulVec_sum, map_sum, Finset.sum_eq_zero fun k hk => by
      rw [Matrix.mulVec_smul, map_smul, hS k hk, smul_zero], add_zero]
    rfl
  have hinj : Function.Injective fun i => (e i).1 := Subtype.val_injective.comp e.injective
  obtain ⟨Ef, hEf, -⟩ := GlobalTheory.AHWeil.tangent_and_weil_of_isAH GlobalTheory.thetaUnifAV_all a.D₀.P n u Hm χl hAH
  have hd := u.discrete
  have key := mean_eq (τ := (Θ.τ w).submatrix (fun i => (e i).1) (fun i => (e i).1)) (c₁ := fun i => Θ.c₁ (e i).1)
    (c₂ := fun i => Θ.c₂ (e i).1) (hs.submatrix _) (hp.submatrix hinj) (fun i => Θ.half₁ _) (fun i => Θ.half₂ _)
    Θ.κ_ne hAH.1 (fun x y => ⟨Ef x y, hEf x y⟩) hAH.2.2.1 (fn_automorphy a.D₀.P.isLB u hAH hfn) F'
    (fun y => by
      obtain ⟨z, rfl⟩ := Fs y
      exact ⟨_, (hF' (Θ.h *ᵥ z)).trans (by rw [hi1])⟩)
    (fun p q => by
      let t : Fin g ⊕ Fin g → ℤ := Sum.elim (fun k => if h : k ∈ Θ.S then 0 else p (e.symm ⟨k, h⟩))
        (fun k => if h : k ∈ Θ.S then 0 else q (e.symm ⟨k, h⟩))
      have h1 : Ha.y (Θ.bas t) = 0 := (Θ.ker t).2 fun k hk => by simp [t, hk]
      have h2 := Fk _ (hG1 _ ((Ha.ker _).2 ⟨_, h1, rfl⟩).1)
      rw [← hP, ← hi1 (Ha.Pw w _), ← hF', hm] at h2
      convert h2 using 2
      funext i
      simp only [Pi.add_apply, Matrix.mulVec, dotProduct, Matrix.submatrix_apply]
      congr 1
      · simp [t, (e i).2]
      · rw [← Finset.sum_compl_add_sum Θ.S, Finset.sum_eq_zero (s := Θ.S) fun k hk => by simp [t, hk], add_zero,
          Finset.sum_subtype (p := fun k => k ∉ Θ.S) Θ.Sᶜ (by simp), ← e.sum_comp]
        exact Finset.sum_congr rfl fun k _ => by simp [t, (e k).2])
    (ρ := fun x => ρ (L x)) (ρd.comp L.toContinuousLinearMap.differentiable) (fun x => ρn _)
    (by simp only [map_zero, ρ0])
    (fun x => by
      have h1 := hρ (L x)
      have h2 : Θ.h *ᵥ L x = ext x := hi2 _
      simp only [h2] at h1
      rw [thetaCharOff_eq Θ.S e _ _ _ _ Θ.c₁_S] at h1
      simp only [hext] at h1
      exact h1) hFd
  refine key.trans ?_
  rw [← Matrix.det_submatrix_equiv_self e]
  rfl

end GlobalTheory.AbelianPartNorm
