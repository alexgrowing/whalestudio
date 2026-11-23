import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.SameObj
import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
import Development.AbelianVarietyTheory.Definitions.KeyFormula.LevBasis
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.KeyFormulaPowOfKeyFormula
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.LineBundlePowSectionsEqThetaLevel
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstOfNormPeriodic

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyKa
open GlobalTheory.KeyEq

noncomputable section

namespace GlobalTheory.HalfTranslate

open Matrix Complex

section Theta

variable {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ}

theorem thetaChar_shift (hs : τ.IsSymm) (a b r s z : Fin g → ℂ) :
    thetaChar τ a b (z + (s + τ.mulVec r)) =
      cexp (-(Real.pi * I) * (r ⬝ᵥ τ.mulVec r + 2 * (r ⬝ᵥ (z + b + s)))) * thetaChar τ (a + r) (b + s) z := by
  unfold thetaChar
  rw [← tsum_mul_left]
  refine tsum_congr fun n => ?_
  rw [← Complex.exp_add, ← add_assoc _ a r]
  generalize ((fun i => (n i : ℂ)) + a) = t
  have h := ReciprocityTheory.PTheta.dot_mulVec_symm hs t r
  simp only [dotProduct_add, add_dotProduct, Matrix.mulVec_add]
  rw [h]
  congr 1
  ring

theorem thetaChar_int (a b z : Fin g → ℂ) (k l : Fin g → ℤ) :
    thetaChar τ (a + fun i => (k i : ℂ)) (b + fun i => (l i : ℂ)) z =
      cexp (2 * Real.pi * I * (a ⬝ᵥ fun i => (l i : ℂ))) * thetaChar τ a b z := by
  unfold thetaChar
  rw [← tsum_mul_left, ← (Equiv.addRight k).tsum_eq (fun n : Fin g → ℤ => cexp (2 * Real.pi * I * (a ⬝ᵥ fun i => (l i : ℂ))) * _)]
  refine tsum_congr fun n => ?_
  have e : ((fun i => ((n i : ℤ) : ℂ)) + (a + fun i => (k i : ℂ))) = (fun i => (((Equiv.addRight k n) i : ℤ) : ℂ)) + a := by
    funext i
    simp only [Pi.add_apply, Equiv.coe_addRight, Int.cast_add]
    ring
  rw [e, ← Complex.exp_add]
  generalize Equiv.addRight k n = n'
  refine Complex.exp_eq_exp_iff_exists_int.2 ⟨n' ⬝ᵥ l, ?_⟩
  have e2 : ((n' ⬝ᵥ l : ℤ) : ℂ) = (fun i => (n' i : ℂ)) ⬝ᵥ fun i => (l i : ℂ) := by
    simp [dotProduct]
  rw [e2]
  simp only [dotProduct_add, add_dotProduct]
  ring

theorem exists_int_dot {a : Fin g → ℂ} (ha : ∀ i, a i = 0 ∨ a i = 1 / 2) (m : Fin g → ℤ) :
    ∃ k : ℤ, a ⬝ᵥ (fun i => (m i : ℂ)) = k / 2 := by
  have : ∀ i, ∃ k : ℤ, a i * m i = k / 2 := fun i => by
    rcases ha i with h | h
    · exact ⟨0, by simp [h]⟩
    · exact ⟨m i, by rw [h]; ring⟩
  choose k hk using this
  exact ⟨∑ i, k i, by simp [dotProduct, hk, Finset.sum_div]⟩

theorem thetaChar_half (hs : τ.IsSymm) {a b a' b' : Fin g → ℂ} {m n : Fin g → ℤ} (hab : charHalf g a b)
    (hab' : charHalf g a' b') (ha : ∀ i, ∃ k : ℤ, a' i = a i + n i / 2 + k) (hb : ∀ i, ∃ k : ℤ, b' i = b i + m i / 2 + k) :
    ∃ d : ℂ, d ^ 8 = cexp (-(2 * Real.pi * I) * ((fun i => (n i : ℂ)) ⬝ᵥ τ.mulVec (fun i => (n i : ℂ)))) ∧
      ∀ z, cexp (Real.pi * I * ((fun i => (n i : ℂ)) ⬝ᵥ z)) * thetaChar τ a b (z + frac τ 2 m n) =
        d * thetaChar τ a' b' z := by
  choose k hk using ha
  choose l hl using hb
  have e0 : frac τ 2 m n = (2⁻¹ : ℂ) • (fun i => (m i : ℂ)) + τ.mulVec ((2⁻¹ : ℂ) • fun i => (n i : ℂ)) := by
    rw [frac, smul_add, Matrix.mulVec_smul]; norm_num
  have e1 : a + (2⁻¹ : ℂ) • (fun i => (n i : ℂ)) = a' + fun i => (((-k) i : ℤ) : ℂ) := by
    funext i; simp [hk]; ring
  have e2 : b + (2⁻¹ : ℂ) • (fun i => (m i : ℂ)) = b' + fun i => (((-l) i : ℤ) : ℂ) := by
    funext i; simp [hl]; ring
  obtain ⟨p, hp⟩ := exists_int_dot hab'.1 (-l)
  obtain ⟨q, hq⟩ := exists_int_dot hab.2 n
  have e3 : (fun i => (n i : ℂ)) ⬝ᵥ (fun i => (m i : ℂ)) = ((n ⬝ᵥ m : ℤ) : ℂ) := by simp [dotProduct]
  refine ⟨cexp (-(Real.pi * I) * (((fun i => (n i : ℂ)) ⬝ᵥ τ.mulVec (fun i => (n i : ℂ))) / 4 + q / 2 +
    ((n ⬝ᵥ m : ℤ) : ℂ) / 2 - p)), ?_, fun z => ?_⟩
  · rw [← Complex.exp_nat_mul]
    refine Complex.exp_eq_exp_iff_exists_int.2 ⟨4 * p - 2 * q - 2 * (n ⬝ᵥ m), ?_⟩
    generalize n ⬝ᵥ m = r
    push_cast
    ring
  · rw [e0, thetaChar_shift hs, e1, e2, thetaChar_int, hp, ← _root_.mul_assoc, ← _root_.mul_assoc, ← Complex.exp_add,
      ← Complex.exp_add]
    congr 2
    simp only [dotProduct_add, smul_dotProduct, dotProduct_smul, Matrix.mulVec_smul, smul_eq_mul, e3,
      dotProduct_comm _ b, hq]
    ring

end Theta

section Germs

abbrev pt : Sp ℂ := (default : PrimeSpectrum ℂ)

def toStalk : ℂ →+* (Sp ℂ).presheaf.stalk pt :=
  ((Sp ℂ).presheaf.germ ⊤ pt trivial).hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom

variable {X Y : Scheme.{0}}

theorem gs_eq_toStalk (x : Sp ℂ ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) :
    gs x pt U f = toStalk (valAt' x U f) := by
  rw [gs_eq x pt U (h trivial), valAt', dif_pos h, valAt, toStalk, RingHom.comp_apply]
  erw [(Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom_inv_id_apply]
  exact (TopCat.Presheaf.germ_res_apply (Sp ℂ).presheaf (homOfLE h) pt trivial _).symm

theorem gm_eq_toStalk (x : Sp ℂ ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)ˣ) :
    (gm x pt U f).val = toStalk (valAt' x U f.val) :=
  (gs_unit x pt U (h trivial) f).symm.trans (gs_eq_toStalk x U h _)

theorem stalkMap_gs {Z : Scheme.{0}} (r : Z ⟶ Y) (q : Y ⟶ X) (z : Z) (W : X.Opens) (h : q (r z) ∈ W)
    (a : Γ(X, W)) : (r.stalkMap z).hom (gs q (r z) W a) = gs (r ≫ q) z W a := by
  rw [gs_eq q (r z) W h, gs_eq (r ≫ q) z W h]
  exact Scheme.Hom.germ_stalkMap_apply r (q ⁻¹ᵁ W) z h _

theorem top_le_of_mem (x : Sp ℂ ⟶ X) {U : X.Opens} (h : x pt ∈ U) : ⊤ ≤ x ⁻¹ᵁ U := fun q _ => by
  obtain rfl : q = pt := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
  exact h

theorem valAt'_ne (x : Sp ℂ ⟶ X) {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)ˣ) : valAt' x U f.val ≠ 0 := fun h0 => by
  have := gm_eq_toStalk x U h f
  rw [h0, map_zero] at this
  exact Units.ne_zero _ this

theorem val_zpow_eq {W : ((Sp ℂ).presheaf.stalk pt)ˣ} {c : ℂ} (h : W.val = toStalk c) (k : ℤ) :
    (W ^ k).val = toStalk (c ^ k) := by
  have hc : c ≠ 0 := fun h0 => W.ne_zero (by rw [h, h0, map_zero])
  obtain rfl : W = Units.map toStalk.toMonoidHom (Units.mk0 c hc) := Units.ext h
  rw [← map_zpow, Units.coe_map, Units.val_zpow_eq_zpow_val]
  rfl

theorem gm_unitOn (ν : ℂˣ) : (gm (𝟙 (Sp ℂ)) pt ⊤ (unitOn ν)).val = toStalk ν := gm_val (𝟙 (Sp ℂ)) pt ⊤ trivial _

variable {L : LB X} {L' : LB Y} {F : Y ⟶ X}

def isoVal (w : LB.Iso L' (L.pull F)) (y : Sp ℂ ⟶ Y) (j : L.ι) (k : L'.ι) : ℂ :=
  valAt' y ((L.pull F).U (fun _ => j) ⊓ L'.U k) (w.s (fun _ => j, k)).val

theorem le_isoChart {y : Sp ℂ ⟶ Y} {j : L.ι} {k : L'.ι} (hj : ⊤ ≤ (y ≫ F) ⁻¹ᵁ L.U j) (hk : ⊤ ≤ y ⁻¹ᵁ L'.U k) :
    ⊤ ≤ y ⁻¹ᵁ ((L.pull F).U (fun _ => j) ⊓ L'.U k) := fun _ hq => ⟨mem_pull.2 (hj hq), hk hq⟩

theorem gw_eq_toStalk (w : LB.Iso L' (L.pull F)) {y : Sp ℂ ⟶ Y} {j : L.ι} {k : L'.ι} (hj : ⊤ ≤ (y ≫ F) ⁻¹ᵁ L.U j)
    (hk : ⊤ ≤ y ⁻¹ᵁ L'.U k) : (gw w y pt j k).val = toStalk (isoVal w y j k) :=
  gm_eq_toStalk y _ (le_isoChart hj hk) _

theorem isoVal_ne (w : LB.Iso L' (L.pull F)) {y : Sp ℂ ⟶ Y} {j : L.ι} {k : L'.ι} (hj : ⊤ ≤ (y ≫ F) ⁻¹ᵁ L.U j)
    (hk : ⊤ ≤ y ⁻¹ᵁ L'.U k) : isoVal w y j k ≠ 0 := valAt'_ne y (le_isoChart hj hk) _

theorem isoVal_trans {w : LB.Iso L' (L.pull F)} (hw : w.IsGen) {y : Sp ℂ ⟶ Y} {j j' : L.ι} {k k' : L'.ι}
    (hj : ⊤ ≤ (y ≫ F) ⁻¹ᵁ L.U j) (hj' : ⊤ ≤ (y ≫ F) ⁻¹ᵁ L.U j') (hk : ⊤ ≤ y ⁻¹ᵁ L'.U k) (hk' : ⊤ ≤ y ⁻¹ᵁ L'.U k') :
    valAt' y (L'.U k ⊓ L'.U k') (L'.g k k').val * isoVal w y j k =
      valAt' (y ≫ F) (L.U j ⊓ L.U j') (L.g j j').val * isoVal w y j' k' := by
  have h := (isGen_iff w).1 hw _ y pt j j' k k' (hj trivial) (hj' trivial) (hk trivial) (hk' trivial)
  apply toStalk.injective
  rw [map_mul, map_mul, ← gw_eq_toStalk w hj hk, ← gw_eq_toStalk w hj' hk',
    ← gm_eq_toStalk y (L'.U k ⊓ L'.U k') (fun _ hq => ⟨hk hq, hk' hq⟩), ← gm_eq_toStalk (y ≫ F) (L.U j ⊓ L.U j') (fun _ hq => ⟨hj hq, hj' hq⟩),
    ← Units.val_mul, ← Units.val_mul, h]
  congr 1
  rw [mul_comm (gm (y ≫ F) _ _ _), _root_.mul_assoc, mul_inv_cancel_left]

theorem val_of_germ (w : LB.Iso L' (L.pull F)) {y : Sp ℂ ⟶ Y} {j : L.ι} {k : L'.ι} (hj : ⊤ ≤ (y ≫ F) ⁻¹ᵁ L.U j)
    (hk : ⊤ ≤ y ⁻¹ᵁ L'.U k) {s : Γ(X, L.U j)} {s' : Γ(Y, L'.U k)}
    (h : gs F (y pt) (L.U j) s = (gw w (𝟙 _) (y pt) j k).val * gs (𝟙 _) (y pt) (L'.U k) s') :
    valAt' (y ≫ F) (L.U j) s = isoVal w y j k * valAt' y (L'.U k) s' := by
  have k3 := le_isoChart hj hk
  have st : ∀ (U : Y.Opens) (_ : ⊤ ≤ y ⁻¹ᵁ U) (f : Γ(Y, U)),
      (y.stalkMap pt).hom (gs (𝟙 Y) (y pt) U f) = toStalk (valAt' y U f) := fun U hU f => by
    rw [stalkMap_gs y (𝟙 Y) pt U (hU trivial), Category.comp_id, gs_eq_toStalk _ _ hU]
  have e : (y.stalkMap pt).hom (gw w (𝟙 _) (y pt) j k).val = toStalk (isoVal w y j k) :=
    (congrArg _ (gs_unit (𝟙 Y) (y pt) _ (k3 trivial) _).symm).trans (st _ k3 _)
  have h1 := congrArg (y.stalkMap pt).hom h
  rw [map_mul, e, st _ hk, stalkMap_gs y F pt (L.U j) (hj trivial), gs_eq_toStalk _ _ hj, ← map_mul] at h1
  exact toStalk.injective h1

theorem valAt'_self (hL : L.IsLB) (x : Sp ℂ ⟶ X) {j : L.ι} (hj : ⊤ ≤ x ⁻¹ᵁ L.U j) :
    valAt' x (L.U j ⊓ L.U j) (L.g j j).val = 1 := by
  apply toStalk.injective
  rw [← gm_eq_toStalk x (L.U j ⊓ L.U j) (fun _ hq => ⟨hj hq, hj hq⟩), gm_self hL x pt (hj trivial), map_one, Units.val_one]

theorem valAt'_app (x : Sp ℂ ⟶ Y) (φ : Y ⟶ X) (U : X.Opens) (f : Γ(X, U)) :
    valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) = valAt' (x ≫ φ) U f := by
  by_cases h : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ U
  · have h' : ⊤ ≤ x ⁻¹ᵁ (φ ⁻¹ᵁ U) := h
    apply toStalk.injective
    rw [← gs_eq_toStalk _ _ h, ← gs_eq_toStalk _ _ h']
    exact gs_pull x φ pt U (h trivial) f
  · have h' : ¬ ⊤ ≤ x ⁻¹ᵁ (φ ⁻¹ᵁ U) := h
    rw [valAt', valAt', dif_neg h, dif_neg h']

end Germs

section Frame

open FrameValue

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)

theorem frame_law {s : L.Sec} {θ e : (Fin g → ℂ) → ℂ} (hθ : Differentiable ℂ θ) (h0 : θ ≠ 0) (he : Continuous e)
    (hs : u.IsFn s θ) {l : Fin g → ℂ} (hl : l ∈ u.Λ) (h : ∀ z, θ (z + l) = e z * θ z) (i : L.ι) (z : Fin g → ℂ)
    (hz : ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i) : u.fr i z = e z * u.fr i (z + l) := by
  have hper : ∀ z, u.ex (z + l) = u.ex z := fun z => CubeValues.ex_add_period u z l hl
  have ho := (u.hol (L.U i) 0).1
  have hc := (u.fr_hol i).continuousOn
  refine Set.EqOn.of_subset_closure (s := {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i} ∩ {z | θ z ≠ 0})
    (t := {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i}) (f := u.fr i) (g := fun z => e z * u.fr i (z + l)) ?_ hc ?_
    Set.inter_subset_left ((ThetaTangent.dense_ne_zero hθ h0).open_subset_closure_inter ho) hz
  · rintro w ⟨hw, hw0⟩
    have h1 := hs i w hw
    have h2 := hs i (w + l) (by rw [hper]; exact hw)
    rw [hper, h1, h] at h2
    apply mul_left_cancel₀ hw0
    rw [h2]
    ring
  · exact he.continuousOn.mul (hc.comp (continuous_add_const l).continuousOn
      (fun w hw => by rw [Set.mem_setOf_eq, hper]; exact hw))

theorem isLift_double (z : Fin g → ℂ) :
    IsLift u (K := Fin 2) ![((𝟙 A) ^ 2).left, 𝟙 A.left] (u.ex z).left ![z + z, z] := fun k => by
  fin_cases k
  · show (u.ex z).left ≫ ((𝟙 A) ^ 2).left = (u.ex (z + z)).left
    rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id, sq, u.ex_add]
  · exact Category.comp_id _

theorem genVal_double (hL : L.IsLB) {mu : LB.Gen (LB.LinComb L (K := Fin 2) ![((𝟙 A) ^ 2).left, 𝟙 A.left] ![1, -4])}
    (hmu : mu.IsGen) (h : ∀ l ∈ u.Λ, ∀ z, ∃ e : ℂ, (∀ i, ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i → u.fr i z = e * u.fr i (z + l)) ∧
      ∀ i, ⊤ ≤ (u.ex (z + z)).left ⁻¹ᵁ L.U i → u.fr i (z + z) = e ^ 4 * u.fr i (z + l + (z + l))) (z : Fin g → ℂ) :
    genVal u hL mu (u.ex z).left ![z + z, z] = genVal u hL mu (u.ex 0).left ![0 + 0, 0] := by
  have hd := differentiable_genVal (u := u) hL hmu (𝟙 A.left) (q := fun z : Fin g → ℂ => z) differentiable_id
    (z := fun z => ![z + z, z]) (fun k => by fin_cases k <;> simp <;> fun_prop)
    (fun w => by rw [Category.comp_id]; exact isLift_double u w)
  simp only [Category.comp_id] at hd
  refine entire_apply_eq_of_periodic_of_span_real hd u.full (fun z l hl => ?_) z 0
  obtain ⟨e, h1, h2⟩ := h l hl z
  have hj := ((isLift_double u z).le_iff _).1 (le_wchart_chartAt hL _ (u.ex z).left)
  have h3 := h1 _ (hj 1)
  have h4 := h2 _ (hj 0)
  have he : e ≠ 0 := fun h0 => u.fr_ne _ _ (hj 1) (h3.trans (by rw [h0, zero_mul]))
  rw [CubeValues.ex_add_period u z l hl, genVal, genVal, genValIn, genValIn]
  congr 1
  simp only [frameProd, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at h3 h4 ⊢
  rw [h3, h4, mul_zpow, mul_zpow, zpow_one, zpow_one, _root_.mul_mul_mul_comm, ← zpow_natCast e, ← zpow_add₀ he]
  norm_num

def frAt (hL : L.IsLB) (z : Fin g → ℂ) : ℂ := u.fr (chartAt hL (u.ex z).left) z

theorem frAt_ne (hL : L.IsLB) (z : Fin g → ℂ) : frAt u hL z ≠ 0 := u.fr_ne _ _ (le_chartAt hL _)

theorem val_eq_toStalk (hL : L.IsLB) {Y : Scheme.{0}} {K : Type} [Fintype K] {φ : K → (Y ⟶ A.left)} {ε : K → ℤ}
    {t : LB.Gen (LB.LinComb L φ ε)} (ht : t.IsGen) {y : Sp ℂ ⟶ Y} {z : K → Fin g → ℂ} (hz : IsLift u φ y z) :
    (val t y pt (chartAt hL)).val = toStalk (genVal u hL t y z * ∏ k, frAt u hL (z k) ^ ε k) := by
  have h := le_wchart_chartAt hL φ y
  refine (gm_eq_toStalk y _ h _).trans (congrArg toStalk ((valAt'_gen hL ht hz h).trans ?_))
  simp only [frameProd, frAt, hz _]

theorem exists_transport {A' : Over (Sp ℂ)} [GrpObj A'] {L' : LB A'.left} (hL : L.IsLB) (hL' : L'.IsLB) (φ : A' ≅ A)
    [IsMonHom φ.hom] (z₀ : Fin g → ℂ) {F : A'.left ⟶ A.left}
    (hF : ∀ z, (u.ex z ≫ φ.inv).left ≫ F = (u.ex (z + z₀)).left) {w : LB.Iso L' (L.pull F)} (hw : w.IsGen)
    {e : (Fin g → ℂ) → ℂ} (he : Differentiable ℂ e) (he0 : ∀ z, e z ≠ 0) :
    ∃ u' : HolUnif A' L' g, (∀ z, u'.ex z = u.ex z ≫ φ.inv) ∧ u'.Λ = u.Λ ∧
      ∀ j k z, ⊤ ≤ (u.ex (z + z₀)).left ⁻¹ᵁ L.U j → ⊤ ≤ (u'.ex z).left ⁻¹ᵁ L'.U k →
        u'.fr k z * isoVal w (u'.ex z).left j k = e z * u.fr j (z + z₀) := by
  have hol : ∀ (U : A'.left.Opens) (f : Γ(A'.left, U)), IsOpen {z | ⊤ ≤ (u.ex z ≫ φ.inv).left ⁻¹ᵁ U} ∧
      DifferentiableOn ℂ (fun z => valAt' (u.ex z ≫ φ.inv).left U f) {z | ⊤ ≤ (u.ex z ≫ φ.inv).left ⁻¹ᵁ U} := fun U f => by
    have h := u.hol (φ.inv.left ⁻¹ᵁ U) ((φ.inv.left.app U).hom f)
    exact ⟨h.1, h.2.congr fun z _ => (valAt'_app (u.ex z).left φ.inv.left U f).symm⟩
  let c : (Fin g → ℂ) → L.ι := fun z => chartAt hL (u.ex (z + z₀)).left
  have hc : ∀ z, ⊤ ≤ (u.ex (z + z₀)).left ⁻¹ᵁ L.U (c z) := fun z => le_chartAt hL _
  have tr : ∀ {z j}, ⊤ ≤ (u.ex (z + z₀)).left ⁻¹ᵁ L.U j → ⊤ ≤ ((u.ex z ≫ φ.inv).left ≫ F) ⁻¹ᵁ L.U j :=
    fun h => by rwa [hF]
  let fr : L'.ι → (Fin g → ℂ) → ℂ := fun k z => e z * u.fr (c z) (z + z₀) / isoVal w (u.ex z ≫ φ.inv).left (c z) k
  have key : ∀ j k z, ⊤ ≤ (u.ex (z + z₀)).left ⁻¹ᵁ L.U j → ⊤ ≤ (u.ex z ≫ φ.inv).left ⁻¹ᵁ L'.U k →
      fr k z = e z * u.fr j (z + z₀) / isoVal w (u.ex z ≫ φ.inv).left j k := fun j k z hj hk => by
    have h1 := isoVal_trans hw (tr hj) (tr (hc z)) hk hk
    rw [valAt'_self hL' _ hk, _root_.one_mul, hF] at h1
    rw [div_eq_div_iff (isoVal_ne w (tr (hc z)) hk) (isoVal_ne w (tr hj) hk), h1,
      u.fr_compat j (c z) (z + z₀) fun _ hq => ⟨hj hq, hc z hq⟩]
    ring
  refine ⟨⟨fun z => u.ex z ≫ φ.inv, fun z z' => by rw [u.ex_add, MonObj.mul_comp], fun y => ?_, u.Λ, fun z => ?_,
    u.discrete, u.full, hol, fr, fun k z hz => ?_, fun k z hz => ?_, fun k k' z hz => ?_⟩, fun _ => rfl, rfl,
    fun j k z hj hk => ?_⟩
  · obtain ⟨z, hz⟩ := u.ex_onto (y ≫ φ.hom)
    exact ⟨z, by simp [hz]⟩
  · rw [← u.ker, Iso.comp_inv_eq, MonObj.one_comp]
  · have hs : Differentiable ℂ fun z : Fin g → ℂ => z + z₀ := by fun_prop
    have n1 := (u.hol (L.U (c z)) 0).1.mem_nhds (hc z)
    have n2 := (hol (L'.U k) 0).1.mem_nhds hz
    obtain ⟨o3, d3⟩ := hol _ (w.s (fun _ => c z, k)).val
    have d1 : DifferentiableAt ℂ (fun y => u.fr (c z) (y + z₀)) z :=
      ((u.fr_hol (c z)).differentiableAt n1).comp z (hs z)
    have d2 : DifferentiableAt ℂ (fun y => isoVal w (u.ex y ≫ φ.inv).left (c z) k) z :=
      d3.differentiableAt (o3.mem_nhds (le_isoChart (tr (hc z)) hz))
    refine (((he z).fun_mul d1).fun_mul (d2.fun_inv (isoVal_ne w (tr (hc z)) hz))).congr_of_eventuallyEq ?_
      |>.differentiableWithinAt
    filter_upwards [hs.continuous.continuousAt.preimage_mem_nhds n1, n2] with y h1 h2
    exact (key _ k y h1 h2).trans (div_eq_mul_inv _ _)
  · exact div_ne_zero (mul_ne_zero (he0 z) (u.fr_ne _ _ (hc z))) (isoVal_ne w (tr (hc z)) hz)
  · have hk : ⊤ ≤ (u.ex z ≫ φ.inv).left ⁻¹ᵁ L'.U k := fun _ hq => (hz hq).1
    have hk' : ⊤ ≤ (u.ex z ≫ φ.inv).left ⁻¹ᵁ L'.U k' := fun _ hq => (hz hq).2
    have h1 := isoVal_trans hw (tr (hc z)) (tr (hc z)) hk hk'
    rw [valAt'_self hL _ (tr (hc z)), _root_.one_mul] at h1
    show _ / _ = _ * (_ / _)
    rw [← mul_div_assoc, div_eq_div_iff (isoVal_ne w (tr (hc z)) hk) (isoVal_ne w (tr (hc z)) hk'), ← h1]
    ring
  · exact (congrArg (· * _) (key j k z hj hk)).trans (div_mul_cancel₀ _ (isoVal_ne w (tr hj) hk))

theorem isDiff_comp {A' : Over (Sp ℂ)} [GrpObj A'] {L' : LB A'.left} (u' : HolUnif A' L' g) (f : A ⟶ A')
    (hf : ∀ z, u'.ex z = u.ex z ≫ f) {w : Fin g → ℂ} {v : epsR ℂ ⟶ A} (h : u.IsDiff w v) : u'.IsDiff w (v ≫ f) := by
  intro U hU s
  have h1 := h (f.left ⁻¹ᵁ U) hU ((f.left.app U).hom s)
  simp only [valAt'_app] at h1
  simp only [hf, Over.comp_left]
  rw [← h1]
  simp only [Scheme.Hom.comp_appLE, CommRingCat.hom_comp, RingHom.comp_apply]

end Frame

open FrameValue in

theorem normalForm_translate : Out.Laws → ThetaUnifAV → ∀ (x x' : KeyIn ℂ) (g : ℕ) (h : x.P.g = g) (u : HolUnif x.P.A x.P.L g) (τ : Matrix (Fin g) (Fin g) ℂ) (a b a' b' : Fin g → ℂ) (m n : Fin g → ℤ) (ν : ℂˣ), charHalf g a b → charHalf g a' b' → Wit x h u τ a b → (∀ i, ∃ k : ℤ, a' i = a i + n i / 2 + k) → (∀ i, ∃ k : ℤ, b' i = b i + m i / 2 + k) → IsTrl x' x (u.ex (frac τ 2 m n)) ν → ∃ (h' : x'.P.g = g) (u' : HolUnif x'.P.A x'.P.L g) (φ : x'.P.A ≅ x.P.A) (c : ℂ), IsMonHom φ.hom ∧ (∀ z, u'.ex z ≫ φ.hom = u.ex z) ∧ c ^ 8 * (ν : ℂ) ^ 2 = 1 ∧ (∀ z, z ∈ u'.Λ ↔ z ∈ u.Λ) ∧ u'.IsRig x'.rig ∧ u'.IsFn x'.th (fun z => c * thetaChar τ a' b' z) ∧ ∀ i : Fin g, u'.IsDiff (Pi.single i (2 * Real.pi * Complex.I)⁻¹) (x'.v (i.cast h'.symm)) := by
  intro _ _ x x' g h u τ a b a' b' m n ν hab hab' ⟨hs, hp, hΛ, hrig, hth, hv⟩ ha hb hT
  have hL := x.P.isLB
  have hL' := x'.P.isLB
  haveI := x.P.isAb.comm
  obtain ⟨hθ, hθ0⟩ := LevelDict.isLevel_thetaChar hs hp hab
  obtain ⟨d, hd8, hd⟩ := thetaChar_half hs hab hab' ha hb
  generalize hz₀ : frac τ 2 m n = z₀ at hd hT
  obtain ⟨φ, hg, w, mu, rp, _, hφ, hw, hmu, hrp, c1, c2, c3, c4, c5⟩ := hT
  have law := fun (m n : Fin g → ℤ) => frame_law u hθ.1 hθ0 (by fun_prop) hth ((hΛ _).2 ⟨m, n, rfl⟩) (hθ.2 m n)
  have hG := genVal_double u hL hmu (fun l hl z => by
    obtain ⟨m, n, rfl⟩ := (hΛ l).1 hl
    refine ⟨_, fun i hi => law m n i z hi, fun i hi => (law (m + m) (n + n) i (z + z) hi).trans ?_⟩
    obtain ⟨p, hp⟩ := exists_int_dot hab.1 m
    obtain ⟨q, hq⟩ := exists_int_dot hab.2 n
    have e : ∀ k : Fin g → ℤ, (fun i => (((k + k) i : ℤ) : ℂ)) = (fun i => (k i : ℂ)) + fun i => (k i : ℂ) :=
      fun k => funext fun i => by simp
    rw [e, e]
    congr 1
    · rw [pow_one, pow_one, ← Complex.exp_nat_mul]
      refine Complex.exp_eq_exp_iff_exists_int.2 ⟨q - p, ?_⟩
      simp only [dotProduct_add, add_dotProduct, Matrix.mulVec_add, hp, hq]
      push_cast
      ring
    · rw [Matrix.mulVec_add]
      congr 1
      abel) z₀
  have h0 : (u.ex 0).left = eSec x.P.A := by rw [CubeValues.ex_zero, Hom.one_def]; simp [eSec]
  have hJ : Good x.P.L pt (chartAt hL) := fun ψ => le_chartAt hL ψ trivial
  have hJ' : Good x'.P.L pt (chartAt hL') := fun ψ => le_chartAt hL' ψ trivial
  have l0 : IsLift u (fun _ : PUnit => eSec x.P.A) (𝟙 (Sp ℂ)) (fun _ => 0) := fun _ => (Category.id_comp _).trans h0.symm
  have l1 : IsLift u (fun _ : PUnit => (u.ex z₀).left) (𝟙 (Sp ℂ)) (fun _ => z₀) := fun _ => Category.id_comp _
  have v0 := val_eq_toStalk u hL x.rig_gen l0
  have v1 := val_eq_toStalk u hL hrp l1
  have v2 := val_eq_toStalk u hL hmu (isLift_double u 0)
  have v3 := val_eq_toStalk u hL hmu (isLift_double u z₀)
  rw [genVal_rig hL hrig] at v0
  rw [hG] at v3
  have hlam := genVal_ne_zero hL rp l1
  generalize genVal u hL rp (𝟙 (Sp ℂ)) (fun _ => z₀) = lam at v1 hlam
  generalize genVal u hL mu (u.ex 0).left ![0 + 0, 0] = G at v2 v3
  simp only [Fintype.prod_unique, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, zpow_one, add_zero,
    _root_.one_mul] at v0 v1 v2 v3
  have n0 := frAt_ne u hL 0
  have n1 := frAt_ne u hL z₀
  have e4 : G = 1 := by
    have h1 := congrArg Units.val (c4 pt _ hJ)
    rw [h0] at v2
    have h2 := toStalk.injective (v2.symm.trans (h1.trans (val_zpow_eq v0 _)))
    field_simp at h2
    exact h2
  have e5 : frAt u hL (z₀ + z₀) * lam ^ 4 = ν * frAt u hL 0 := by
    have h1 := congrArg Units.val (c5 pt _ hJ)
    have h2 := toStalk.injective (v3.symm.trans (h1.trans ((congrArg₂ (· * ·) ((congrArg₂ (· * ·) (gm_unitOn ν) v0).trans
      (map_mul _ _ _).symm) (val_zpow_eq v1 _)).trans (map_mul _ _ _).symm)))
    rw [e4] at h2
    field_simp at h2
    exact h2
  have e6 : lam ^ 8 = (ν : ℂ) ^ 2 * d ^ 8 := by
    have h1 := law m n _ 0 (le_chartAt hL _)
    have h2 : z₀ + z₀ = 0 + ((fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ))) := by
      rw [← hz₀, frac, ← add_smul]; norm_num
    have h3 : u.ex (z₀ + z₀) = u.ex 0 := h2 ▸ CubeValues.ex_add_period u 0 _ ((hΛ _).2 ⟨m, n, rfl⟩)
    have n2 := frAt_ne u hL (z₀ + z₀)
    rw [frAt, h3] at e5 n2
    rw [← h2] at h1
    rw [frAt, h1, ← _root_.mul_assoc, mul_comm] at e5
    obtain ⟨p, hp⟩ := exists_int_dot hab.1 m
    obtain ⟨q, hq⟩ := exists_int_dot hab.2 n
    rw [show lam ^ 8 = (lam ^ 4) ^ 2 by ring, mul_right_cancel₀ n2 e5, hd8, mul_pow, pow_one, ← Complex.exp_nat_mul,
      hp, hq]
    congr 1
    refine Complex.exp_eq_exp_iff_exists_int.2 ⟨p - q, ?_⟩
    rw [dotProduct_zero]
    push_cast
    ring
  have hF : ∀ z, (u.ex z ≫ φ.inv).left ≫ (φ.hom ≫ trl x.P.A (u.ex z₀)).left = (u.ex (z + z₀)).left := fun z => by
    rw [← Over.comp_left, Category.assoc, Iso.inv_hom_id_assoc, trl, MonObj.comp_mul, Category.comp_id,
      ← Category.assoc, toUnit_unique (u.ex z ≫ toUnit _) (𝟙 _), Category.id_comp, add_comm, u.ex_add]
  obtain ⟨u', hex, hΛ', hfr⟩ := exists_transport u hL hL' φ z₀ hF hw
    (e := fun z => lam * cexp (-(Real.pi * I * ((fun i => (n i : ℂ)) ⬝ᵥ z)))) (by unfold dotProduct; fun_prop)
    (fun z => mul_ne_zero hlam (Complex.exp_ne_zero _))
  have hF' : ∀ z, (u'.ex z).left ≫ (φ.hom ≫ trl x.P.A (u.ex z₀)).left = (u.ex (z + z₀)).left := fun z => by
    rw [hex, hF]
  refine ⟨hg.trans h, u', φ, d / lam, hφ, fun z => by simp [hex], ?_, fun z => by rw [hΛ'], ?_, ?_, fun i => ?_⟩
  · rw [div_pow, e6]
    have : d ^ 8 ≠ 0 := hd8 ▸ Complex.exp_ne_zero _
    rw [div_mul_eq_mul_div, mul_comm, div_self (mul_ne_zero (pow_ne_zero _ ν.ne_zero) this)]
  · have h0' : (u'.ex 0).left = eSec x'.P.A := by rw [CubeValues.ex_zero, Hom.one_def]; simp [eSec]
    have l0' : IsLift u' (fun _ : PUnit => eSec x'.P.A) (𝟙 (Sp ℂ)) (fun _ => 0) :=
      fun _ => (Category.id_comp _).trans h0'.symm
    have v4 := val_eq_toStalk u' hL' x'.rig_gen l0'
    have k1 : ⊤ ≤ (u.ex (0 + z₀)).left ⁻¹ᵁ x.P.L.U (chartAt hL (u.ex z₀).left) := by
      rw [zero_add]; exact le_chartAt hL _
    have k2 := le_chartAt hL' (u'.ex 0).left
    have k3 := hfr _ _ 0 k1 k2
    have v5 := gw_eq_toStalk w (by rw [hF']; exact k1) k2
    have h1 := congrArg Units.val (c3 pt _ _ hJ hJ')
    simp only [Category.id_comp] at h1
    rw [h0'] at v5
    have h2 := toStalk.injective (v1.symm.trans (h1.trans ((congrArg₂ (· * ·) v5 v4).trans (map_mul _ _ _).symm)))
    have e7 : genVal u' hL' x'.rig (𝟙 (Sp ℂ)) (fun _ => 0) = 1 := by
      simp only [dotProduct_zero, mul_zero, neg_zero, Complex.exp_zero, _root_.mul_one, zero_add] at k3
      simp only [Fintype.prod_unique, zpow_one, frAt] at h2
      rw [← k3, h0'] at h2
      have n3 := isoVal_ne w (by rw [hF']; exact k1) k2
      have n4 := u'.fr_ne _ _ k2
      rw [h0'] at n3 n4
      refine mul_left_cancel₀ (mul_ne_zero n4 n3) ?_
      linear_combination -h2
    intro j hj
    have h3 := valAt'_gen hL' x'.rig_gen l0' (j := j) hj
    rw [e7, _root_.one_mul] at h3
    simp only [frameProd, Fintype.prod_unique, zpow_one] at h3
    exact h3.symm
  · intro k z hk
    have k1 := le_chartAt hL (u.ex (z + z₀)).left
    generalize chartAt hL (u.ex (z + z₀)).left = j at k1
    have k2 : ⊤ ≤ ((u'.ex z).left ≫ (φ.hom ≫ trl x.P.A (u.ex z₀)).left) ⁻¹ᵁ x.P.L.U j := by rw [hF']; exact k1
    have h2 := val_of_germ w k2 hk (c2 ((u'.ex z).left pt) j k (k2 trivial) (hk trivial))
    rw [hF', hth j _ k1] at h2
    have h3 := hfr j k z k1 hk
    have h4 := hd z
    rw [Complex.exp_neg] at h3
    have n3 := isoVal_ne w k2 hk
    have n4 := Complex.exp_ne_zero (Real.pi * I * ((fun i => (n i : ℂ)) ⬝ᵥ z))
    refine mul_left_cancel₀ n3 ?_
    rw [← h2]
    show _ = _ * (d / lam * thetaChar τ a' b' z * _)
    rw [mul_left_comm, mul_comm (isoVal _ _ _ _), h3, div_mul_eq_mul_div, ← h4]
    field_simp
  · have h1 := isDiff_comp u u' φ.inv hex (hv i)
    have h2 : x'.v (i.cast (hg.trans h).symm) = x.v (i.cast h.symm) ≫ φ.inv := by
      rw [Iso.eq_comp_inv, c1]; rfl
    rwa [h2]

end GlobalTheory.HalfTranslate
