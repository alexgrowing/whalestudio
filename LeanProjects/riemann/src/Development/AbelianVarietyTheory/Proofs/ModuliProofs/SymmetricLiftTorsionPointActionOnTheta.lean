import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HasAnConstThetaGrpZeroIff
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExAtMemPairChartIff

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.SymLiftFrame

open ThetaFn CubeValues SymmetricSemicharacter AppellHumbertTrivial ReciprocityTheory.ChartRestriction.G.Out

section Values

variable {X Y Y' : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']

def cval {φ : K → (Y ⟶ X)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb L φ ε)) (r : Sp ℂ ⟶ Y)
    (J : (Sp ℂ ⟶ X) → L.ι) : ℂ :=
  valAt' r (LB.wchart L φ fun k => J (r ≫ φ k)) (t.s fun k => J (r ≫ φ k)).val

private theorem valAt'_presheaf_map_homOfLE {Z : Scheme.{0}} (x : Sp ℂ ⟶ Z) {U V : Z.Opens} (hVU : V ≤ U)
    (h : ⊤ ≤ x ⁻¹ᵁ V) (f : Γ(Z, U)) :
    valAt' x V (Z.presheaf.map (homOfLE hVU).op f) = valAt' x U f := by
  unfold valAt'
  rw [dif_pos h, dif_pos (h.trans fun p hp => hVU hp)]
  unfold valAt
  congr 1
  rw [← Scheme.Hom.map_appLE x h (homOfLE hVU).op]
  rfl

private theorem valAt'_mul_moduli {Z : Scheme.{0}} (x : Sp ℂ ⟶ Z) (U : Z.Opens) (f f' : Γ(Z, U)) :
    valAt' x U (f * f') = valAt' x U f * valAt' x U f' := by
  unfold valAt'
  split_ifs with h
  · unfold valAt
    rw [map_mul, map_mul]
  · rw [zero_mul]

private theorem valAt'_units_inv' {Z : Scheme.{0}} (x : Sp ℂ ⟶ Z) (U : Z.Opens) (f : Γ(Z, U)ˣ) :
    valAt' x U ↑f⁻¹ = (valAt' x U ↑f)⁻¹ := by
  unfold valAt'
  split_ifs with h
  · refine eq_inv_of_mul_eq_one_left ?_
    unfold valAt
    rw [← map_mul, ← map_mul, Units.inv_mul, map_one, map_one]
  · rw [inv_zero]

private theorem valAt'_app_eq_valAt'_comp' {Z Z' : Scheme.{0}} (x : Sp ℂ ⟶ Z') (q : Z' ⟶ Z) (U : Z.Opens)
    (h : ⊤ ≤ (x ≫ q) ⁻¹ᵁ U) (f : Γ(Z, U)) :
    valAt' x (q ⁻¹ᵁ U) (q.app U f) = valAt' (x ≫ q) U f := by
  unfold valAt'
  rw [dif_pos h, dif_pos (show ⊤ ≤ x ⁻¹ᵁ q ⁻¹ᵁ U from h)]
  unfold valAt
  congr 1

private theorem valAt'_one_moduli {Z : Scheme.{0}} (x : Sp ℂ ⟶ Z) (U : Z.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) :
    valAt' x U 1 = 1 := by
  unfold valAt'
  rw [dif_pos h]
  unfold valAt
  rw [map_one, map_one]

private theorem valAt'_finset_prod {Z : Scheme.{0}} {I : Type} (x : Sp ℂ ⟶ Z) (U : Z.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ U) (s : Finset I) (f : I → Γ(Z, U)) :
    valAt' x U (∏ i ∈ s, f i) = ∏ i ∈ s, valAt' x U (f i) := by
  unfold valAt'
  simp only [dif_pos h]
  unfold valAt
  rw [map_prod, map_prod]

theorem cval_of {φ : K → (Y ⟶ X)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb L φ ε)) (r : Sp ℂ ⟶ Y)
    (J : (Sp ℂ ⟶ X) → L.ι) (j : K → L.ι) (h : ∀ k, J (r ≫ φ k) = j k) :
    cval t r J = valAt' r (LB.wchart L φ j) (t.s j).val := by
  have e : (fun k => J (r ≫ φ k)) = j := funext h
  subst e
  rfl

variable {J : (Sp ℂ ⟶ X) → L.ι} (hJ : ∀ ψ : Sp ℂ ⟶ X, ⊤ ≤ ψ ⁻¹ᵁ L.U (J ψ))
  {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
include hJ

theorem mem_chart (φ : K → (Y ⟶ X)) (r : Sp ℂ ⟶ Y) :
    ⊤ ≤ r ⁻¹ᵁ LB.wchart L φ fun k => J (r ≫ φ k) := by
  intro p _
  refine Set.mem_iInter.2 fun k => ?_
  have hk := hJ (r ≫ φ k) (show p ∈ (⊤ : (Sp ℂ).Opens) from trivial)
  simpa using hk

theorem cval_ne_zero (t : LB.Gen (LB.LinComb L φ ε)) (r : Sp ℂ ⟶ Y) : cval t r J ≠ 0 := by
  intro h0
  have h1 := valAt'_mul_moduli r ((L.LinComb φ ε).U fun k => J (r ≫ φ k))
    ((t.s fun k => J (r ≫ φ k))⁻¹).val (t.s fun k => J (r ≫ φ k)).val
  rw [Units.inv_mul] at h1
  have h2 : valAt' r ((L.LinComb φ ε).U fun k => J (r ≫ φ k)) (t.s fun k => J (r ≫ φ k)).val = 0 := h0
  rw [h2, mul_zero] at h1
  exact one_ne_zero ((valAt'_one_moduli r _ (mem_chart hJ φ r)).symm.trans h1)

theorem cval_mul (t : LB.Gen (LB.LinComb L φ ε)) (t' : LB.Gen (LB.LinComb L φ' ε'))
    (r : Sp ℂ ⟶ Y) : cval (LB.mulGen L φ ε φ' ε' t t') r J = cval t r J * cval t' r J := by
  unfold cval LB.mulGen
  dsimp only
  unfold res
  rw [Units.val_mul, valAt'_mul_moduli, Units.coe_map, Units.coe_map]
  exact congrArg₂ (· * ·) (valAt'_presheaf_map_homOfLE _ _ (mem_chart hJ _ r) _) (valAt'_presheaf_map_homOfLE _ _ (mem_chart hJ _ r) _)

theorem cval_inv (t : LB.Gen (LB.LinComb L φ ε)) (r : Sp ℂ ⟶ Y) :
    cval (LB.invGen L φ ε t) r J = (cval t r J)⁻¹ := by
  unfold cval LB.invGen
  exact valAt'_units_inv' _ _ _

theorem cval_pull (t : LB.Gen (LB.LinComb L φ ε)) (h : Y' ⟶ Y) (r : Sp ℂ ⟶ Y') :
    cval (LB.pullGen L φ ε t h) r J = cval t (r ≫ h) J := by
  rw [cval_of t (r ≫ h) J (fun k => J (r ≫ h ≫ φ k)) (fun k => congrArg J (Category.assoc r h (φ k)))]
  unfold cval LB.pullGen pullU res
  dsimp only
  rw [Units.coe_map, Units.coe_map]
  exact (valAt'_presheaf_map_homOfLE _ _ (mem_chart hJ _ r) _).trans (valAt'_app_eq_valAt'_comp' r h _ (mem_chart hJ φ (r ≫ h)) _)

theorem cval_corr_one {t : LB.Gen (LB.LinComb L φ ε)}
    (h : LB.Gen.Corr L φ ε _ _ t (LB.oneGen L)) (r : Sp ℂ ⟶ Y) : cval t r J = 1 := by
  have e := h (fun k => J (r ≫ φ k)) PEmpty.elim (fun k₁ k₂ hk => by simp only [hk])
    (fun k _ _ => k.elim) (fun _ k' _ => k'.elim)
  unfold res LB.oneGen at e
  have h0 : ⊤ ≤ r ⁻¹ᵁ L.wchart (PEmpty.elim : PEmpty.{1} → (Y ⟶ X)) PEmpty.elim := by
    intro p _
    exact Set.mem_iInter.2 fun k => k.elim
  have hV : ⊤ ≤ r ⁻¹ᵁ ((L.wchart φ fun k => J (r ≫ φ k)) ⊓
      L.wchart (PEmpty.elim : PEmpty.{1} → (Y ⟶ X)) PEmpty.elim) := by
    intro p hp
    exact ⟨mem_chart hJ φ r hp, h0 hp⟩
  have e3 := congrArg (valAt' r _) (congrArg Units.val e)
  refine ((valAt'_presheaf_map_homOfLE r inf_le_left hV _).symm.trans e3).trans ?_
  refine (valAt'_presheaf_map_homOfLE r inf_le_right hV _).trans ?_
  exact valAt'_one_moduli r _ h0

end Values

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} {u : HolUnif A L g}
  {T : Over (Sp ℂ)} {p : 𝟙_ (Over (Sp ℂ)) ⟶ T} {J : (Sp ℂ ⟶ A.left) → L.ι}
  (hJ : ∀ ψ : Sp ℂ ⟶ A.left, ⊤ ≤ ψ ⁻¹ᵁ L.U (J ψ))

include hJ in

theorem cval_powGen {k : ℤ} (θ : ThetaGrp A L k T) (n : ℕ) (r : Sp ℂ ⟶ (T ⊗ A).left) :
    cval (powGen A L k θ n) r J =
      ∏ i ∈ Finset.range n, cval (L := L) θ.φ (r ≫ (translT A (θ.pt ^ i)).left) J := by
  rw [← Fin.prod_univ_eq_prod_range]
  unfold powGen
  conv_lhs => unfold cval
  dsimp only
  rw [Units.coe_prod]
  refine (valAt'_finset_prod r _ (mem_chart hJ _ r) _ _).trans (Finset.prod_congr rfl fun i _ => ?_)
  unfold res
  refine (valAt'_presheaf_map_homOfLE r _ (mem_chart hJ _ r) _).trans ?_
  exact cval_pull hJ θ.φ (translT A (θ.pt ^ (i : ℕ))).left r

include hJ in

theorem cval_symGen {k : ℤ} (θ : ThetaGrp A L k T) (nu : LB.Gen (negLB A L k T))
    (r : Sp ℂ ⟶ (T ⊗ A).left) :
    cval (symGen A L k θ nu) r J =
      cval (L := L) θ.φ (r ≫ (translT A θ.pt⁻¹).left) J * cval (L := L) nu r J *
        (cval (L := L) θ.φ (r ≫ (negT A T).left) J *
          (cval (L := L) nu (r ≫ (translT A θ.pt⁻¹).left) J)⁻¹) := by
  unfold symGen
  rw [cval_mul hJ, cval_mul hJ, cval_mul hJ _ nu, cval_pull hJ θ.φ, cval_pull hJ θ.φ, cval_inv hJ,
    cval_pull hJ nu]

theorem cval_two {m : T ⊗ A ⟶ A} {ε : Fin 2 → ℤ}
    (α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ε)) {z w : Fin g → ℂ}
    (h : exAt u p z ≫ m.left = (u.ex w).left) :
    cval α (exAt u p z) J = valAt' (exAt u p z) (LB.wchart L ![(snd T A).left, m.left]
      ![J (u.ex z).left, J (u.ex w).left]) (α.s ![J (u.ex z).left, J (u.ex w).left]).val := by
  refine cval_of α _ J _ fun i => ?_
  fin_cases i
  · show J ((lift p (u.ex z)).left ≫ (snd T A).left) = J (u.ex z).left
    rw [← Over.comp_left, lift_snd]
  · exact congrArg J h

variable {Hm : Matrix (Fin g) (Fin g) ℂ} {k : ℤ} {Θ : ThetaGrp A L k T} {x : Fin g → ℂ} {c : ℂ}

include hJ in
theorem cval_theta (hc : HasAnConst u p Hm Θ x c) (z : Fin g → ℂ) :
    cval (L := L) Θ.φ (exAt u p z) J * u.fr (J (u.ex (z + x)).left) (z + x) ^ k =
      c * fockFactor Hm k x z * u.fr (J (u.ex z).left) z ^ k := by
  rw [cval_of Θ.φ (exAt u p z) J ![J (u.ex z).left, J (u.ex (z + x)).left] (fun i => ?_)]
  · exact hc.2 _ z (hJ _) (hJ _)
  · fin_cases i
    · show J ((lift p (u.ex z)).left ≫ (snd T A).left) = J (u.ex z).left
      rw [← Over.comp_left, lift_snd]
    · exact congrArg J (exAt_translPt u hc.1 z)

theorem exists_choice (hL : L.IsLB) :
    ∃ J : (Sp ℂ ⟶ A.left) → L.ι, ∀ ψ : Sp ℂ ⟶ A.left, ⊤ ≤ ψ ⁻¹ᵁ L.U (J ψ) := by
  have hpt : ∀ a b : Sp ℂ, a = b := fun a b =>
    PrimeSpectrum.ext (((Ideal.eq_bot_or_top a.asIdeal).resolve_right a.isPrime.ne_top).trans
      ((Ideal.eq_bot_or_top b.asIdeal).resolve_right b.isPrime.ne_top).symm)
  have key : ∀ ψ : Sp ℂ ⟶ A.left, ∃ i, ⊤ ≤ ψ ⁻¹ᵁ L.U i := by
    intro ψ
    obtain ⟨p0⟩ : Nonempty (PrimeSpectrum ℂ) := inferInstance
    have h0 : ψ p0 ∈ (⨆ i, L.U i) := by
      rw [hL.cover]
      trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 h0
    exact ⟨i, fun p _ => by rw [hpt p p0]; exact hi⟩
  choose J hJ using key
  exact ⟨J, hJ⟩

theorem pow_mul_eq_one (hL : L.IsLB) {χ : u.Λ → ℂ} (hAH : u.IsAH Hm χ)
    (hc : HasAnConst u p Hm Θ x c) {n : ℕ} {l : u.Λ} (hl : (n : ℂ) • x = l)
    (h : LB.Gen.Corr L _ _ _ _ (powGen A L k Θ n) (LB.oneGen L)) : c ^ n * χ l ^ k = 1 := by
  obtain ⟨J, hJ⟩ := exists_choice hL
  have hex0 : u.ex 0 = 1 := (u.ker 0).2 (zero_mem _)
  have hpt : ∀ i : ℕ, p ≫ Θ.pt ^ i = u.ex ((i : ℂ) • x) := fun i => by
    rw [MonObj.comp_pow, hc.1, ex_natCast_smul]
  have key : ∀ m : ℕ, (∏ i ∈ Finset.range m, cval (L := L) Θ.φ (exAt u p ((i : ℂ) • x)) J) *
      u.fr (J (u.ex ((m : ℂ) • x)).left) ((m : ℂ) • x) ^ k =
      c ^ m * Complex.exp (-((k : ℂ) * (Real.pi : ℂ) * ((m : ℂ) ^ 2 / 2) * hermForm Hm x x)) *
        u.fr (J (u.ex 0).left) 0 ^ k := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have t := cval_theta hJ hc ((m : ℂ) • x)
      have hm1 : (m : ℂ) • x + x = ((m + 1 : ℕ) : ℂ) • x := by
        push_cast
        rw [add_smul, one_smul]
      rw [hm1] at t
      have hE : fockFactor Hm k x ((m : ℂ) • x) *
          Complex.exp (-((k : ℂ) * (Real.pi : ℂ) * ((m : ℂ) ^ 2 / 2) * hermForm Hm x x)) =
          Complex.exp (-((k : ℂ) * (Real.pi : ℂ) * (((m + 1 : ℕ) : ℂ) ^ 2 / 2) * hermForm Hm x x)) := by
        unfold fockFactor
        rw [← Complex.exp_add, hermForm_smul_left]
        congr 1
        push_cast
        ring
      rw [Finset.prod_range_succ]
      linear_combination (∏ i ∈ Finset.range m, cval (L := L) Θ.φ (exAt u p ((i : ℂ) • x)) J) * t +
        (c * fockFactor Hm k x ((m : ℂ) • x)) * ih +
        (c ^ (m + 1) * u.fr (J (u.ex 0).left) 0 ^ k) * hE
  have hprod : ∏ i ∈ Finset.range n, cval (L := L) Θ.φ (exAt u p ((i : ℂ) • x)) J = 1 := by
    have h1 := cval_corr_one hJ h (exAt u p 0)
    rw [cval_powGen hJ Θ n] at h1
    refine Eq.trans (Finset.prod_congr rfl fun i _ => ?_) h1
    rw [exAt_translT u (hpt i) 0, zero_add]
  have hl1 : u.ex (l : Fin g → ℂ) = u.ex 0 := by
    rw [hex0]
    exact (u.ker _).2 l.2
  have hk := key n
  rw [hprod, _root_.one_mul, hl, hl1] at hk
  have ha : u.fr (J (u.ex 0).left) 0 = χ l *
      Complex.exp ((Real.pi : ℂ) * hermForm Hm 0 l + (Real.pi : ℂ) / 2 * hermForm Hm l l) *
        u.fr (J (u.ex 0).left) (l : Fin g → ℂ) := by
    have := hAH.2.2.2 l (J (u.ex 0).left) 0 (hJ _)
    rw [zero_add] at this
    exact this
  have hak := congrArg (· ^ k) ha
  rw [mul_zpow, mul_zpow] at hak
  have h0 : hermForm Hm 0 (l : Fin g → ℂ) = 0 := zero_dotProduct _
  have hexp : Complex.exp ((Real.pi : ℂ) * hermForm Hm 0 l + (Real.pi : ℂ) / 2 * hermForm Hm l l) ^ k *
      Complex.exp (-((k : ℂ) * (Real.pi : ℂ) * ((n : ℂ) ^ 2 / 2) * hermForm Hm x x)) = 1 := by
    rw [← Complex.exp_int_mul, ← Complex.exp_add, h0, ← hl, hermForm_smul_left, hermForm_smul_right,
      star_natCast, ← Complex.exp_zero]
    congr 1
    ring
  have hfr0 : u.fr (J (u.ex 0).left) 0 ^ k ≠ 0 := zpow_ne_zero _ (u.fr_ne _ _ (hJ _))
  apply mul_right_cancel₀ hfr0
  linear_combination (-1 : ℂ) * hak -
    (χ l ^ k * Complex.exp ((Real.pi : ℂ) * hermForm Hm 0 l + (Real.pi : ℂ) / 2 * hermForm Hm l l) ^ k) * hk -
    (χ l ^ k * c ^ n * u.fr (J (u.ex 0).left) 0 ^ k) * hexp

theorem sq_eq_one (hL : L.IsLB) {χ : u.Λ → ℂ} (hAH : u.IsAH Hm χ)
    (hc : HasAnConst u p Hm Θ x c) {nu : LB.Gen (negLB A L k T)} (hnu : nu.IsGen)
    (h : LB.Gen.Corr L _ _ _ _ (symGen A L k Θ nu) (LB.oneGen L)) : c ^ 2 = 1 := by
  obtain ⟨J, hJ⟩ := exists_choice hL
  have hex0 : u.ex 0 = 1 := (u.ker 0).2 (zero_mem _)
  have hneg : ∀ z, u.ex (-z) = u.ex z ≫ ι := fun z => by
    rw [GrpObj.inv_eq_inv, GrpObj.comp_inv, Category.comp_id]
    refine (eq_inv_of_mul_eq_one_right ?_)
    rw [← u.ex_add, add_neg_cancel, hex0]
  have hxi : p ≫ Θ.pt⁻¹ = u.ex (-x) := by
    rw [GrpObj.comp_inv, hc.1, hneg, GrpObj.inv_eq_inv, GrpObj.comp_inv, Category.comp_id]
  have e2 : exAt u p 0 ≫ (negT A T).left = exAt u p 0 := by
    unfold negT exAt
    rw [← Over.comp_left, comp_lift, lift_fst, ← Category.assoc, lift_snd, ← hneg, neg_zero]
  have hΦ : ∀ z, exAt u p z ≫ (snd T A ≫ ι).left = (u.ex (-z)).left := fun z =>
    exAt_snd_comp p (hneg z)
  obtain ⟨-, -, cν, hcν0, hcν⟩ := exists_isPullConst hL hAH (Φ := -LinearMap.id)
    (fun z => by simpa only [LinearMap.neg_apply, LinearMap.id_apply] using hΦ z) (a := k) (b := k) hnu
  have hN : ∀ z, cval (L := L) nu (exAt u p z) J * u.fr (J (u.ex (-z)).left) (-z) ^ k =
      cν * u.fr (J (u.ex z).left) z ^ k := fun z => by
    rw [cval_of nu _ J ![J (u.ex z).left, J (u.ex (-z)).left] (fun i => ?_)]
    · exact hcν _ z ((exAt_mem_pairChart_iff (hΦ z) _).2 ⟨hJ _, hJ _⟩)
    · fin_cases i
      · show J ((lift p (u.ex z)).left ≫ (snd T A).left) = J (u.ex z).left
        rw [← Over.comp_left, lift_snd]
      · exact congrArg J (hΦ z)
  have hs := cval_corr_one hJ h (exAt u p 0)
  rw [cval_symGen hJ Θ nu, exAt_translT u hxi 0, zero_add, e2] at hs
  have t1 := cval_theta hJ hc (-x)
  have t2 := cval_theta hJ hc 0
  have p1 := hN 0
  have p2 := hN (-x)
  rw [neg_add_cancel] at t1
  rw [zero_add] at t2
  rw [neg_zero] at p1
  rw [neg_neg] at p2
  have hf : fockFactor Hm k x (-x) * fockFactor Hm k x 0 = 1 := by
    unfold fockFactor hermForm
    rw [← Complex.exp_add, neg_dotProduct, zero_dotProduct, ← Complex.exp_zero]
    congr 1
    ring
  have hF0 : u.fr (J (u.ex 0).left) 0 ^ k ≠ 0 := zpow_ne_zero _ (u.fr_ne _ _ (hJ _))
  have hFm : u.fr (J (u.ex (-x)).left) (-x) ^ k ≠ 0 := zpow_ne_zero _ (u.fr_ne _ _ (hJ _))
  have hn2 : cval (L := L) nu (exAt u p (-x)) J ≠ 0 := cval_ne_zero hJ nu _
  have hn1 : cval (L := L) nu (exAt u p 0) J = cν := mul_right_cancel₀ hF0 p1
  rw [hn1] at hs
  have e2' : cval (L := L) Θ.φ (exAt u p (-x)) J * cval (L := L) Θ.φ (exAt u p 0) J * cν =
      cval (L := L) nu (exAt u p (-x)) J := by
    have hi := mul_inv_cancel₀ hn2
    linear_combination (cval (L := L) nu (exAt u p (-x)) J) * hs -
      (cval (L := L) Θ.φ (exAt u p (-x)) J * cν * cval (L := L) Θ.φ (exAt u p 0) J) * hi
  apply mul_right_cancel₀ (mul_ne_zero (mul_ne_zero hFm hF0) hcν0)
  linear_combination (-cν) * ((cval (L := L) Θ.φ (exAt u p 0) J * u.fr (J (u.ex x).left) x ^ k) * t1 +
      (c * fockFactor Hm k x (-x) * u.fr (J (u.ex (-x)).left) (-x) ^ k) * t2 +
      (c ^ 2 * u.fr (J (u.ex (-x)).left) (-x) ^ k * u.fr (J (u.ex 0).left) 0 ^ k) * hf) +
    (u.fr (J (u.ex 0).left) 0 ^ k * u.fr (J (u.ex x).left) x ^ k) * e2' + u.fr (J (u.ex 0).left) 0 ^ k * p2

end GlobalTheory.SymLiftFrame

open GlobalTheory.SymLiftFrame GlobalTheory.ThetaFn GlobalTheory.AppellHumbertTrivial in

theorem GlobalTheory.symLift_act_in_frame : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (N : ℕ) (l : u.Λ) (f : (Fin P.g → ℂ) → ℂ) (T : Over (Sp ℂ)) [IsIso T.hom] (p : 𝟙_ (Over (Sp ℂ)) ⟶ T) (x : T ⟶ P.A) (U : Out.ThetaGrp P.A P.L ((N : ℤ) ^ 2) T) (s s' : LB.Sec (Out.LPow P.A P.L ((N : ℤ) ^ 2) T)), u.IsAH Hm χ → Odd N → p ≫ x = u.ex (((N : ℂ) ^ 2)⁻¹ • (l : Fin P.g → ℂ)) → Out.SymLift P.A P.L ((N : ℤ) ^ 2) (N ^ 2) x U → Out.IsActOf P.A P.L ((N : ℤ) ^ 2) U s s' → (∀ (j : Fin 1 → P.L.ι) z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U (j 0) → valAt' (lift p (u.ex z)).left ((Out.LPow P.A P.L ((N : ℤ) ^ 2) T).U j) (s.f j) = f z * u.fr (j 0) z ^ (((N : ℤ) ^ 2) : ℤ)) → (∀ (j : Fin 1 → P.L.ι) z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U (j 0) → valAt' (lift p (u.ex z)).left ((Out.LPow P.A P.L ((N : ℤ) ^ 2) T).U j) (s'.f j) = (χ l * Complex.exp (-(Real.pi / 2 / (N : ℂ) ^ 2) * hermForm Hm l l - Real.pi * hermForm Hm z l) * f (z + ((N : ℂ) ^ 2)⁻¹ • (l : Fin P.g → ℂ))) * u.fr (j 0) z ^ (((N : ℤ) ^ 2) : ℤ)) := by
  intro _ _ _ _ P u Hm χ N l f T _ p x U s s' hAH hN hx hS hAct hs j z hz
  obtain ⟨J, hJ⟩ := exists_choice P.isLB
  obtain ⟨hpteq, hpow, nu, hnu, hsym⟩ := hS
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.pos_of_ne_zero (by rintro rfl; exact absurd hN (by decide))).ne'
  set x0 : Fin P.g → ℂ := ((N : ℂ) ^ 2)⁻¹ • (l : Fin P.g → ℂ) with hx0
  have hpt0 : p ≫ U.pt = u.ex x0 := by rw [hpteq, hx]
  obtain ⟨c, hc⟩ := (exists_hasAnConst P.isLB hAH hpt0).2
  have hl' : ((N ^ 2 : ℕ) : ℂ) • x0 = l := by
    rw [hx0, smul_smul]
    push_cast
    rw [mul_inv_cancel₀ (pow_ne_zero 2 hN0), one_smul]
  have hpowc := pow_mul_eq_one P.isLB hAH hc hl' hpow
  have hsq := sq_eq_one P.isLB hAH hc hnu hsym
  have hχ := GlobalTheory.semicharacter_sq_eq_one_of_symmetric P u Hm χ hAH l
  obtain ⟨m, hm⟩ : Odd (N ^ 2) := hN.pow
  rw [show ((N : ℤ) ^ 2) = ((N ^ 2 : ℕ) : ℤ) by push_cast; ring, zpow_natCast, hm, pow_succ, pow_succ,
    pow_mul, pow_mul, hsq, hχ] at hpowc
  simp only [one_pow, _root_.one_mul] at hpowc
  have hcχ : c = χ l := by linear_combination (χ l) * hpowc - c * hχ
  obtain ⟨j0, rfl⟩ : ∃ j0, j = fun _ => j0 := ⟨j 0, funext fun i => by rw [Subsingleton.elim i 0]⟩
  have hsnd : ∀ w, exAt u p w ≫ (snd T P.A).left = (u.ex w).left := fun w => by
    show (lift p (u.ex w)).left ≫ (snd T P.A).left = _
    rw [← Over.comp_left, lift_snd]
  have hW : ∀ w, ⊤ ≤ exAt u p w ⁻¹ᵁ
      LB.wchart P.L (fun _ : Fin 1 => (snd T P.A).left) (fun _ => J (u.ex w).left) := fun w => by
    have h1 := mem_chart hJ (fun _ : Fin 1 => (snd T P.A).left) (exAt u p w)
    simp only [hsnd] at h1
    exact h1
  have htr : exAt u p z ≫ (Out.translPt P.A U.pt).left = (u.ex (z + x0)).left := exAt_translPt u hpt0 z
  have hV : ⊤ ≤ exAt u p z ⁻¹ᵁ LB.wchart P.L ![(snd T P.A).left, (Out.translPt P.A U.pt).left]
      ![j0, J (u.ex (z + x0)).left] :=
    (exAt_mem_pairChart_iff htr _).2 ⟨hz, hJ _⟩
  have e := congrArg (valAt' (exAt u p z) _) (hAct ![j0, J (u.ex (z + x0)).left])
  have e2 : valAt' (exAt u p z) ((Out.LPow P.A P.L ((N : ℤ) ^ 2) T).U fun _ => j0) (s'.f fun _ => j0) =
      valAt' (exAt u p z) (LB.wchart P.L ![(snd T P.A).left, (Out.translPt P.A U.pt).left]
        ![j0, J (u.ex (z + x0)).left]) (U.φ.s ![j0, J (u.ex (z + x0)).left]).val *
      valAt' (exAt u p (z + x0)) ((Out.LPow P.A P.L ((N : ℤ) ^ 2) T).U fun _ => J (u.ex (z + x0)).left)
        (s.f fun _ => J (u.ex (z + x0)).left) := by
    refine (valAt'_presheaf_map_homOfLE _ _ hV _).symm.trans (e.trans ((valAt'_mul_moduli _ _ _ _).trans ?_))
    refine congrArg₂ (· * ·) rfl ?_
    refine (valAt'_presheaf_map_homOfLE _ _ hV _).trans ?_
    refine (valAt'_app_eq_valAt'_comp' _ _ _ ?_ _).trans ?_
    · rw [exAt_translT u hpt0 z]
      exact hW _
    · rw [exAt_translT u hpt0 z]
      rfl
  have hs' : valAt' (exAt u p (z + x0)) ((Out.LPow P.A P.L ((N : ℤ) ^ 2) T).U fun _ => J (u.ex (z + x0)).left)
      (s.f fun _ => J (u.ex (z + x0)).left) = f (z + x0) * u.fr (J (u.ex (z + x0)).left) (z + x0) ^ ((N : ℤ) ^ 2) :=
    hs _ _ (hJ _)
  have hc2 : valAt' (exAt u p z) (LB.wchart P.L ![(snd T P.A).left, (Out.translPt P.A U.pt).left]
        ![j0, J (u.ex (z + x0)).left]) (U.φ.s ![j0, J (u.ex (z + x0)).left]).val *
      u.fr (J (u.ex (z + x0)).left) (z + x0) ^ ((N : ℤ) ^ 2) =
      c * fockFactor Hm ((N : ℤ) ^ 2) x0 z * u.fr j0 z ^ ((N : ℤ) ^ 2) := hc.2 _ z hz (hJ _)
  have hfock : fockFactor Hm ((N : ℤ) ^ 2) x0 z =
      Complex.exp (-((Real.pi : ℂ) / 2 / (N : ℂ) ^ 2) * hermForm Hm l l - (Real.pi : ℂ) * hermForm Hm z l) := by
    unfold fockFactor
    congr 1
    rw [hx0]
    simp only [hermForm_smul_left, hermForm_smul_right, star_inv₀, star_pow, star_natCast]
    push_cast
    field_simp
    ring
  refine e2.trans ?_
  rw [hs']
  show _ = χ l * _ * f (z + x0) * u.fr j0 z ^ ((N : ℤ) ^ 2)
  linear_combination f (z + x0) * hc2 + (fockFactor Hm ((N : ℤ) ^ 2) x0 z * f (z + x0) *
    u.fr j0 z ^ ((N : ℤ) ^ 2)) * hcχ + (χ l * f (z + x0) * u.fr j0 z ^ ((N : ℤ) ^ 2)) * hfock
