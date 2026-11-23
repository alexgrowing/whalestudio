import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsUniqueSecIsFnAt
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.AppellHumbertTrivialOfNowhereVanishing

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out

namespace GlobalTheory.ThetaFn

open CubeValues SymmetricSemicharacter

theorem hermForm_pull {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ)
    (Φ : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (z w : Fin g → ℂ) :
    hermForm ((LinearMap.toMatrix' Φ).transpose * Hm *
      (LinearMap.toMatrix' Φ).transpose.conjTranspose) z w = hermForm Hm (Φ z) (Φ w) := by
  rw [← LinearMap.toMatrix'_mulVec Φ z, ← LinearMap.toMatrix'_mulVec Φ w]
  generalize LinearMap.toMatrix' Φ = M
  rw [hermForm, hermForm, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec z, Matrix.vecMul_transpose, ← Matrix.vecMul_transpose M w,
    Matrix.star_vecMul]

section Fibre

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
  {T : Over (Sp ℂ)} (p : 𝟙_ (Over (Sp ℂ)) ⟶ T)

def IsPullConst {m : T ⊗ A ⟶ A} (Φ : (Fin g → ℂ) → Fin g → ℂ) (a b : ℤ)
    (α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ![a, -b])) (c : ℂ) : Prop :=
  ∀ (j : Fin 2 → L.ι) z, ⊤ ≤ exAt u p z ⁻¹ᵁ LB.wchart L ![(snd T A).left, m.left] j →
    valAt' (exAt u p z) (LB.wchart L ![(snd T A).left, m.left] j) (α.s j).val *
      u.fr (j 1) (Φ z) ^ b = c * u.fr (j 0) z ^ a

variable {u p}

theorem exAt_mem_pairChart_iff {m : T ⊗ A ⟶ A} {z w : Fin g → ℂ}
    (h : exAt u p z ≫ m.left = (u.ex w).left) (j : Fin 2 → L.ι) :
    ⊤ ≤ exAt u p z ⁻¹ᵁ LB.wchart L ![(snd T A).left, m.left] j ↔
      ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U (j 0) ∧ ⊤ ≤ (u.ex w).left ⁻¹ᵁ L.U (j 1) := by
  refine (le_preimage_wchart (exAt u p z) L _ j).trans ?_
  rw [Fin.forall_fin_two, ← exAt_snd u p z, ← h]
  rfl

theorem map_mem_period {m : T ⊗ A ⟶ A} {Φ : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)}
    (hΦ : ∀ z, exAt u p z ≫ m.left = (u.ex (Φ z)).left) {l : Fin g → ℂ} (hl : l ∈ u.Λ) :
    Φ l ∈ u.Λ := by
  have h := hΦ (0 + l)
  rw [exAt_add_period u p 0 l hl, hΦ, map_zero, zero_add, ex_zero] at h
  exact (u.ker _).1 (Over.OverMorphism.ext h.symm)

theorem exists_fn_of_isGen (hL : L.IsLB) {m : T ⊗ A ⟶ A} {Φ : (Fin g → ℂ) → Fin g → ℂ}
    (hd : Differentiable ℂ Φ) (hΦ : ∀ z, exAt u p z ≫ m.left = (u.ex (Φ z)).left) {a b : ℤ}
    {α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ![a, -b])} (hα : α.IsGen) :
    ∃ r : (Fin g → ℂ) → ℂ, Differentiable ℂ r ∧ (∀ z, r z ≠ 0) ∧
      ∀ (j : Fin 2 → L.ι) z, ⊤ ≤ exAt u p z ⁻¹ᵁ LB.wchart L ![(snd T A).left, m.left] j →
        r z = valAt' (exAt u p z) (LB.wchart L ![(snd T A).left, m.left] j) (α.s j).val *
          u.fr (j 1) (Φ z) ^ b * u.fr (j 0) z ^ (-a) := by
  choose ch hch using exists_chart u valueRules hL
  let R : (Fin 2 → L.ι) → (Fin g → ℂ) → ℂ := fun j z =>
    valAt' (exAt u p z) (LB.wchart L ![(snd T A).left, m.left] j) (α.s j).val *
      u.fr (j 1) (Φ z) ^ b * u.fr (j 0) z ^ (-a)
  have hc : ∀ z, ⊤ ≤ exAt u p z ⁻¹ᵁ LB.wchart L ![(snd T A).left, m.left] ![ch z, ch (Φ z)] :=
    fun z => (exAt_mem_pairChart_iff (hΦ z) _).2 ⟨hch z, hch (Φ z)⟩
  have hRR : ∀ j j' z, ⊤ ≤ exAt u p z ⁻¹ᵁ LB.wchart L ![(snd T A).left, m.left] j →
      ⊤ ≤ exAt u p z ⁻¹ᵁ LB.wchart L ![(snd T A).left, m.left] j' → R j z = R j' z := by
    intro j j' z hj hj'
    obtain ⟨h0, h1⟩ := (exAt_mem_pairChart_iff (hΦ z) j).1 hj
    obtain ⟨h0', h1'⟩ := (exAt_mem_pairChart_iff (hΦ z) j').1 hj'
    have k0 := (le_preimage_inf _ _ _).2 ⟨h0, h0'⟩
    have k1 := (le_preimage_inf _ _ _).2 ⟨h1, h1'⟩
    have n0 := zpow_ne_zero a (val_unit_ne_zero _ valueRules k0 (L.g _ _))
    have n1 := zpow_ne_zero b (val_unit_ne_zero _ valueRules k1 (L.g _ _))
    have e1 := val_gen (exAt u p z) valueRules α hα j j' hj hj'
    have e2 := val_linComb (exAt u p z) valueRules L ![(snd T A).left, m.left] ![a, -b] j j' hj hj'
    rw [Fin.prod_univ_two] at e2
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, exAt_snd, hΦ] at e2
    replace e1 := e1.trans (congrArg (· * _) e2)
    simp only [R]
    rw [u.fr_compat _ _ _ k0, u.fr_compat _ _ _ k1]
    refine (congrArg (· * _ * _) e1).trans ?_
    simp only [mul_zpow, zpow_neg]
    field_simp
    exact congrArg (· / _) (_root_.mul_comm _ _)
  refine ⟨fun z => R ![ch z, ch (Φ z)] z, fun z => ?_, fun z => ?_, fun j z hj => hRR _ _ z (hc z) hj⟩
  · set j : Fin 2 → L.ι := ![ch z, ch (Φ z)]
    obtain ⟨ho, hv⟩ := exAt_hol u p _ (α.s j).val
    have hn := ho.mem_nhds (hc z)
    have d0 : DifferentiableAt ℂ (u.fr (j 0)) z :=
      (u.fr_hol _).differentiableAt ((u.hol _ 0).1.mem_nhds (hch z))
    have d1 : DifferentiableAt ℂ (fun w => u.fr (j 1) (Φ w)) z :=
      ((u.fr_hol (j 1)).differentiableAt ((u.hol _ 0).1.mem_nhds (hch (Φ z)))).comp z (hd z)
    have hq := ((hv.differentiableAt hn).mul (d1.zpow (m := b)
      (Or.inl (u.fr_ne _ _ (hch (Φ z)))))).mul (d0.zpow (m := -a) (Or.inl (u.fr_ne _ _ (hch z))))
    refine hq.congr_of_eventuallyEq ?_
    filter_upwards [hn] with w hw
    exact hRR _ j w (hc w) hw
  · exact mul_ne_zero (mul_ne_zero (val_unit_ne_zero _ valueRules (hc z) _)
      (zpow_ne_zero _ (u.fr_ne _ _ (hch _)))) (zpow_ne_zero _ (u.fr_ne _ _ (hch _)))

theorem exists_isPullConst (hL : L.IsLB) {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ}
    (hAH : u.IsAH Hm χ) {m : T ⊗ A ⟶ A} {Φ : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)}
    (hΦ : ∀ z, exAt u p z ≫ m.left = (u.ex (Φ z)).left) {a b : ℤ}
    {α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ![a, -b])} (hα : α.IsGen) :
    (∀ z w, (b : ℂ) * hermForm Hm (Φ z) (Φ w) = a * hermForm Hm z w) ∧
      (∀ l : u.Λ, χ ⟨Φ l, map_mem_period hΦ l.2⟩ ^ b = χ l ^ a) ∧
      ∃ c : ℂ, c ≠ 0 ∧ IsPullConst u p Φ a b α c := by
  obtain ⟨r, hr, hne, hrj⟩ := exists_fn_of_isGen hL Φ.toContinuousLinearMap.differentiable hΦ hα
  have hχ : ∀ l, χ l ≠ 0 := fun l h0 => by simpa [h0] using hAH.2.2.1 l
  set B : Matrix (Fin g) (Fin g) ℂ := (a : ℂ) • Hm - (b : ℂ) • ((LinearMap.toMatrix' Φ).transpose *
    Hm * (LinearMap.toMatrix' Φ).transpose.conjTranspose) with hB
  have hBf : ∀ z w, hermForm B z w = a * hermForm Hm z w - b * hermForm Hm (Φ z) (Φ w) := by
    intro z w
    rw [← hermForm_pull]
    simp only [hB, hermForm, Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub,
      dotProduct_smul, smul_eq_mul]
  have hBh : B.IsHermitian := by
    have h2 := Matrix.isHermitian_mul_mul_conjTranspose (LinearMap.toMatrix' Φ).transpose hAH.1
    rw [hB, Matrix.IsHermitian, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_smul, h2.eq, hAH.1.eq, star_intCast, star_intCast]
  haveI := u.discrete
  obtain ⟨k1, k2, k3⟩ := appellHumbert_trivial_of_nowhere_vanishing g u.Λ u.full B
    (fun l => χ l ^ a / χ ⟨Φ l, map_mem_period hΦ l.2⟩ ^ b) r hBh
    (fun l => by rw [norm_div, norm_zpow, norm_zpow, hAH.2.2.1, hAH.2.2.1]; simp) hr hne
    (fun l z => by
      obtain ⟨i, hi⟩ := exists_chart u valueRules hL z
      obtain ⟨i', hi'⟩ := exists_chart u valueRules hL (Φ z)
      have hj := (exAt_mem_pairChart_iff (hΦ z) ![i, i']).2 ⟨hi, hi'⟩
      have hj' := hj
      rw [← exAt_add_period u p z l l.2] at hj'
      rw [hrj _ _ hj', hrj _ _ hj, exAt_add_period u p z l l.2]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, ContinuousLinearMap.coe_coe,
        LinearMap.coe_toContinuousLinearMap']
      rw [hAH.2.2.2 l i z hi, hAH.2.2.2 ⟨Φ l, map_mem_period hΦ l.2⟩ i' (Φ z) hi', map_add,
        hBf, hBf]
      have n1 := zpow_ne_zero a (hχ l)
      have n2 := zpow_ne_zero b (hχ ⟨Φ l, map_mem_period hΦ l.2⟩)
      simp only [mul_zpow, zpow_neg, ← Complex.exp_int_mul, hermForm]
      set E0 := (Real.pi : ℂ) * (z ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) +
        Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) with hE0
      set E1 := (Real.pi : ℂ) * (Φ z ⬝ᵥ Hm.mulVec (star (Φ l))) +
        Real.pi / 2 * (Φ l ⬝ᵥ Hm.mulVec (star (Φ l))) with hE1
      have he : ∀ x : ℂ, x = a * E0 - b * E1 →
          Complex.exp x = Complex.exp (a * E0) / Complex.exp (b * E1) := fun x hx => by
        rw [hx, Complex.exp_sub]
      rw [he _ (by rw [hE0, hE1]; ring)]
      have n3 := Complex.exp_ne_zero (a * E0)
      have n4 := Complex.exp_ne_zero (b * E1)
      field_simp)
  refine ⟨fun z w => ?_, fun l => ?_, r 0, hne 0, fun j z hj => ?_⟩
  · have h := hBf z w
    rw [k1] at h
    simp only [hermForm, Matrix.zero_mulVec, dotProduct_zero] at h ⊢
    exact (sub_eq_zero.1 h.symm).symm
  · exact ((div_eq_one_iff_eq (zpow_ne_zero b (hχ _))).1 (k2 l)).symm
  · have n := zpow_ne_zero a (u.fr_ne _ _ ((exAt_mem_pairChart_iff (hΦ z) j).1 hj).1)
    rw [← k3 z, hrj j z hj, zpow_neg, inv_mul_cancel_right₀ n]
    rfl

theorem IsPullConst.fn_eq (hL : L.IsLB) {ψ : T ⊗ A ⟶ T ⊗ A} {m : T ⊗ A ⟶ A}
    {hm : ψ ≫ snd T A = m} {Φ : (Fin g → ℂ) → Fin g → ℂ}
    (hψ : ∀ z, exAt u p z ≫ ψ.left = exAt u p (Φ z)) {a b : ℤ}
    {α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ![a, -b])} {c : ℂ}
    (hc : IsPullConst u p Φ a b α c) {s : LB.Sec (LPow A L b T)} {s' : LB.Sec (LPow A L a T)}
    (ht : IsTwistPull A L ψ m hm a b α s s') {θ θ' : (Fin g → ℂ) → ℂ}
    (h : IsFnAt u p b s θ) (h' : IsFnAt u p a s' θ') (z : Fin g → ℂ) : θ' z = c * θ (Φ z) := by
  obtain ⟨i, hi⟩ := exists_chart u valueRules hL z
  obtain ⟨i', hi'⟩ := exists_chart u valueRules hL (Φ z)
  have hΦ : exAt u p z ≫ m.left = (u.ex (Φ z)).left := by
    rw [← hm, Over.comp_left, ← Category.assoc, hψ, exAt_snd]
  have hj := (exAt_mem_pairChart_iff hΦ ![i, i']).2 ⟨hi, hi'⟩
  have e := h.twistPull h' ht (hψ z) _ hj
  refine mul_right_cancel₀ (zpow_ne_zero a (u.fr_ne i z hi)) (e.trans ?_)
  rw [mul_left_comm, hc _ z hj]
  exact (mul_left_comm _ _ _).trans (_root_.mul_assoc _ _ _).symm

theorem IsPullConst.origin {rig : LB.Gen (L.pull (eSec A))} (hrig : u.IsRig rig) {m : T ⊗ A ⟶ A}
    {Φ : (Fin g → ℂ) → Fin g → ℂ} (h0 : Φ 0 = 0) (hΦ : exAt u p 0 ≫ m.left = (u.ex 0).left)
    {a b : ℤ} {α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ![a, -b])} {c : ℂ}
    (hc : IsPullConst u p Φ a b α c) (j : Fin 2 → L.ι)
    (hj : ⊤ ≤ exAt u p 0 ⁻¹ᵁ LB.wchart L ![(snd T A).left, m.left] j) :
    valAt' (exAt u p 0) (LB.wchart L ![(snd T A).left, m.left] j) (α.s j).val *
        valAt' (𝟙 (Sp ℂ)) ((L.pull (eSec A)).U fun _ => j 1) (rig.s fun _ => j 1).val ^ b =
      c * valAt' (𝟙 (Sp ℂ)) ((L.pull (eSec A)).U fun _ => j 0) (rig.s fun _ => j 0).val ^ a := by
  have key : ∀ i, ⊤ ≤ (u.ex 0).left ⁻¹ᵁ L.U i → u.fr i 0 =
      valAt' (𝟙 (Sp ℂ)) ((L.pull (eSec A)).U fun _ => i) (rig.s fun _ => i).val := fun i hi => by
    rw [ex_zero] at hi
    exact hrig (fun _ => i) fun _ hy => Set.mem_iInter.2 fun _ => hi hy
  obtain ⟨h1, h2⟩ := (exAt_mem_pairChart_iff hΦ j).1 hj
  rw [← key _ h1, ← key _ h2, ← hc j 0 hj, h0]

theorem IsPullConst.eq_one (hL : L.IsLB) {rig : LB.Gen (L.pull (eSec A))} (hrig : u.IsRig rig)
    {m : T ⊗ A ⟶ A} {Φ : (Fin g → ℂ) → Fin g → ℂ} (h0 : Φ 0 = 0)
    (hΦ : exAt u p 0 ≫ m.left = (u.ex 0).left) {a b : ℤ}
    {α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ![a, -b])} {c : ℂ}
    (hc : IsPullConst u p Φ a b α c)
    (hn : ∀ j : Fin 2 → L.ι, ⊤ ≤ exAt u p 0 ⁻¹ᵁ LB.wchart L ![(snd T A).left, m.left] j →
      valAt' (exAt u p 0) (LB.wchart L ![(snd T A).left, m.left] j) (α.s j).val *
          valAt' (𝟙 (Sp ℂ)) ((L.pull (eSec A)).U fun _ => j 1) (rig.s fun _ => j 1).val ^ b =
        valAt' (𝟙 (Sp ℂ)) ((L.pull (eSec A)).U fun _ => j 0) (rig.s fun _ => j 0).val ^ a) :
    c = 1 := by
  obtain ⟨i, hi⟩ := exists_chart u valueRules hL 0
  have hj := (exAt_mem_pairChart_iff hΦ fun _ => i).2 ⟨hi, hi⟩
  have e := (hc.origin hrig h0 hΦ _ hj).symm.trans (hn _ hj)
  refine (mul_eq_right₀ (zpow_ne_zero a (val_unit_ne_zero _ valueRules ?_ _))).1 e
  rw [ex_zero] at hi
  exact fun _ hy => Set.mem_iInter.2 fun _ => hi hy

theorem IsPullConst.unique (hL : L.IsLB) {m : T ⊗ A ⟶ A} {Φ : (Fin g → ℂ) → Fin g → ℂ}
    (hΦ : ∀ z, exAt u p z ≫ m.left = (u.ex (Φ z)).left) {a b : ℤ}
    {α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ![a, -b])} {c c' : ℂ}
    (hc : IsPullConst u p Φ a b α c) (hc' : IsPullConst u p Φ a b α c') : c = c' := by
  obtain ⟨i, hi⟩ := exists_chart u valueRules hL 0
  obtain ⟨i', hi'⟩ := exists_chart u valueRules hL (Φ 0)
  have hj := (exAt_mem_pairChart_iff (hΦ 0) ![i, i']).2 ⟨hi, hi'⟩
  exact mul_right_cancel₀ (zpow_ne_zero a (u.fr_ne i 0 hi)) ((hc _ 0 hj).symm.trans (hc' _ 0 hj))

variable (p) in

theorem exAt_snd_comp {f : A ⟶ A} {z w : Fin g → ℂ} (h : u.ex w = u.ex z ≫ f) :
    exAt u p z ≫ (snd T A ≫ f).left = (u.ex w).left := by
  rw [Over.comp_left, ← Category.assoc, exAt_snd, h, Over.comp_left]

variable (u) in

theorem ex_natCast_smul (k : ℕ) (z : Fin g → ℂ) : u.ex ((k : ℂ) • z) = u.ex z ^ k := by
  induction k with
  | zero => rw [Nat.cast_zero, zero_smul, ex_zero, pow_zero]
  | succ n ih => rw [Nat.cast_succ, add_smul, one_smul, u.ex_add, ih, pow_succ]

variable (u p) in

theorem exAt_mulT (k : ℕ) (z : Fin g → ℂ) :
    exAt u p z ≫ (mulT A T k).left = exAt u p ((k : ℂ) • z) :=
  (Over.comp_left _ _ _ _ _).symm.trans (congrArg CommaMorphism.left (by
    rw [mulT, comp_lift, lift_fst, MonObj.comp_pow, lift_snd, ex_natCast_smul]))

theorem pull_analytic_at (hL : L.IsLB) {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ}
    (hAH : u.IsAH Hm χ) {ψ : T ⊗ A ⟶ T ⊗ A} {m : T ⊗ A ⟶ A} (hm : ψ ≫ snd T A = m)
    {Φ : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)} (hψ : ∀ z, exAt u p z ≫ ψ.left = exAt u p (Φ z)) {a b : ℤ}
    {α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ![a, -b])} (hα : α.IsGen) :
    (∀ z w, (b : ℂ) * hermForm Hm (Φ z) (Φ w) = a * hermForm Hm z w) ∧
    ∃ c : ℂ, c ≠ 0 ∧ IsPullConst u p Φ a b α c ∧
      (∀ (s : LB.Sec (LPow A L b T)) (s' : LB.Sec (LPow A L a T)) (θ θ' : (Fin g → ℂ) → ℂ),
        IsTwistPull A L ψ m hm a b α s s' → IsFnAt u p b s θ → IsFnAt u p a s' θ' →
          ∀ z, θ' z = c * θ (Φ z)) ∧
      ∀ rig : LB.Gen (L.pull (eSec A)), u.IsRig rig →
        (∀ j : Fin 2 → L.ι, ⊤ ≤ exAt u p 0 ⁻¹ᵁ LB.wchart L ![(snd T A).left, m.left] j →
          valAt' (exAt u p 0) (LB.wchart L ![(snd T A).left, m.left] j) (α.s j).val *
              valAt' (𝟙 (Sp ℂ)) ((L.pull (eSec A)).U fun _ => j 1) (rig.s fun _ => j 1).val ^ b =
            c * valAt' (𝟙 (Sp ℂ)) ((L.pull (eSec A)).U fun _ => j 0) (rig.s fun _ => j 0).val ^ a) ∧
        ((∀ j : Fin 2 → L.ι, ⊤ ≤ exAt u p 0 ⁻¹ᵁ LB.wchart L ![(snd T A).left, m.left] j →
          valAt' (exAt u p 0) (LB.wchart L ![(snd T A).left, m.left] j) (α.s j).val *
              valAt' (𝟙 (Sp ℂ)) ((L.pull (eSec A)).U fun _ => j 1) (rig.s fun _ => j 1).val ^ b =
            valAt' (𝟙 (Sp ℂ)) ((L.pull (eSec A)).U fun _ => j 0) (rig.s fun _ => j 0).val ^ a) →
          c = 1) := by
  have hΦ : ∀ z, exAt u p z ≫ m.left = (u.ex (Φ z)).left := fun z => by
    rw [← hm, Over.comp_left, ← Category.assoc, hψ, exAt_snd]
  have hΦ0 : exAt u p 0 ≫ m.left = (u.ex 0).left := by rw [hΦ, map_zero]
  obtain ⟨h1, -, c, hc0, hc⟩ := exists_isPullConst hL hAH hΦ hα
  exact ⟨h1, c, hc0, hc, fun s s' θ θ' ht h h' => hc.fn_eq hL hψ ht h h', fun rig hrig =>
    ⟨hc.origin hrig (map_zero Φ) hΦ0, hc.eq_one hL hrig (map_zero Φ) hΦ0⟩⟩

end Fibre

end GlobalTheory.ThetaFn
