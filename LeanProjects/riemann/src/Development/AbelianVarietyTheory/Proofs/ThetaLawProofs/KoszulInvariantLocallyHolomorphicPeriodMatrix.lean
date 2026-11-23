import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.LevBasis
import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
import Development.AbelianVarietyTheory.Definitions.KeyFormula.IsSquareDeterminantComparison
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KaRuleK
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SurjectiveOfComplexPointsLiftOfUniversallyClosed
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsIntegralOfIsAbelianSchemeField
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsLevBasisReal
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.DifferentiableOnCoordOfLinearIndependent
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SimpleZerosMoveHolomorphically
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.UnifValueJacZeros
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KosBlockMulKosD
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KaFormHomogeneous
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsDifferentiableOnTorsSq
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SubmatrixMulOfVanish
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SignInsert
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.LineBundlePowSectionsEqThetaLevelStatement
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsHolomorphicThetaOfLevelBasisStatement
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKoszulTorsionTransversalSplitZerosStatement
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsSquareDeterminantComparisonIsAlgClosedStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

noncomputable section
namespace GlobalTheory.KeyKa.KaHol

def LevB {g N : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (l : ℕ) (Th : Fin N → (Fin g → ℂ) → ℂ) : Prop :=
  (∀ k, IsLevel τ a b l (Th k)) ∧ ∀ F, IsLevel τ a b l F → ∃! c : Fin N → ℂ, ∀ z, F z = ∑ k, c k * Th k z

def SimpleZeros {g d : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (F : Fin g → (Fin g → ℂ) → ℂ) (z : Fin d → Fin g → ℂ) : Prop :=
  (∀ e i, F i (z e) = 0) ∧ (∀ e, (Matrix.of fun i k => fderiv ℂ (F i) (z e) (Pi.single k 1)).det ≠ 0) ∧
    (∀ e e' (m m' : Fin g → ℤ), z e = z e' + ((fun i => (m i : ℂ)) + τ.mulVec (fun i => (m' i : ℂ))) → e = e') ∧
    ∀ y, (∀ i, F i y = 0) → ∃ (e : Fin d) (m m' : Fin g → ℤ),
      y = z e + ((fun i => (m i : ℂ)) + τ.mulVec (fun i => (m' i : ℂ)))

def AnMul {g : ℕ} {N : ℕ → ℕ} (F : Fin g → (Fin g → ℂ) → ℂ) (Th : ∀ j, Fin (N j) → (Fin g → ℂ) → ℂ)
    (m : Fin g → ∀ j j', Matrix (Fin (N j)) (Fin (N j')) ℂ) : Prop :=
  ∀ i j, j < g → ∀ k z, F i z * Th (j + 1) k z = ∑ k', m i j (j + 1) k' k * Th j k' z

def evAn {g d : ℕ} {N : ℕ → ℕ} (Th : ∀ j, Fin (N j) → (Fin g → ℂ) → ℂ) (z : Fin d → Fin g → ℂ) (j : ℕ) :
    Matrix (Fin d) (Fin (N j)) ℂ := Matrix.of fun a k => Th j k (z a)

def jacAn {g d : ℕ} (F : Fin g → (Fin g → ℂ) → ℂ) (z : Fin d → Fin g → ℂ) : ℂ :=
  ∏ e, (Matrix.of fun i k : Fin g => (2 * Real.pi * Complex.I)⁻¹ * fderiv ℂ (F i) (z e) (Pi.single k 1)).det

theorem det_scale_ne_zero {g : ℕ} (M : Fin g → Fin g → ℂ) :
    (Matrix.of fun i k : Fin g => (2 * Real.pi * Complex.I)⁻¹ * M i k).det ≠ 0 ↔ (Matrix.of M).det ≠ 0 := by
  have : (Matrix.of fun i k : Fin g => (2 * Real.pi * Complex.I)⁻¹ * M i k) =
      (2 * Real.pi * Complex.I : ℂ)⁻¹ • Matrix.of M := by
    ext i k; simp
  rw [this, Matrix.det_smul, mul_ne_zero_iff, and_iff_right]
  exact pow_ne_zero _ (inv_ne_zero Complex.two_pi_I_ne_zero)

theorem IsLevel.mul {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ} {a b : Fin g → ℂ} {l₁ l₂ l : ℕ} {F G : (Fin g → ℂ) → ℂ}
    (hF : IsLevel τ a b l₁ F) (hG : IsLevel τ a b l₂ G) (h : l = l₁ + l₂) : IsLevel τ a b l (fun z => F z * G z) := by
  refine ⟨hF.1.mul hG.1, fun m n z => ?_⟩
  simp only [hF.2, hG.2, h, pow_add]
  ring

section Geo
variable {g : ℕ} (x : KeyIn ℂ) (u : HolUnif x.P.A x.P.L g)

theorem exists_chart (z : Fin g → ℂ) : ∃ c, ⊤ ≤ (u.ex z).left ⁻¹ᵁ x.P.L.U c := by
  obtain ⟨j, hj⟩ : ∃ j, (u.ex z).left (default : PrimeSpectrum ℂ) ∈ x.P.L.U j :=
    TopologicalSpace.Opens.mem_iSup.1 (by rw [x.P.isLB.cover]; trivial)
  exact ⟨j, (top_le_preimage_iff_mem _ _).2 hj⟩

theorem coords_iff {l N : ℕ} (b : Fin N → RR x l) (Th : Fin N → (Fin g → ℂ) → ℂ) (hb : ∀ k, FnPw x u (b k) (Th k))
    (f : ∀ i, Γ(x.P.A.left, x.P.L.U i)) (G : (Fin g → ℂ) → ℂ)
    (hf : ∀ i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ x.P.L.U i → valAt' (u.ex z).left (x.P.L.U i) (f i) = G z * u.fr i z ^ l)
    (c : Fin N → ℂ) : Coords x b c f ↔ ∀ z, G z = ∑ k, c k * Th k z := by
  have key : ∀ i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ x.P.L.U i → valAt' (u.ex z).left (x.P.L.U i)
      (∑ k, cst x.P.A.hom (x.P.L.U i) (c k) * (show Γ(x.P.A.left, x.P.L.U i) from (b k).f i)) =
      (∑ k, c k * Th k z) * u.fr i z ^ l := by
    intro i z hz
    rw [valAt'_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [valAt'_mul, _root_.mul_assoc, ← hb k i z hz]
    congr 1
    exact KoszulCx.valH_cst x (u.ex z) _ hz (c k)
  constructor
  · intro h z
    obtain ⟨i, hi⟩ := exists_chart x u z
    have e := key i z hi
    rw [← h i, hf i z hi] at e
    exact mul_right_cancel₀ (pow_ne_zero _ (u.fr_ne i z hi)) e
  · intro h i
    have := x.P.isAb.smooth
    have : IsIntegral x.P.A.left := polAV_isIntegral_of_isAlgClosed ℂ x.P
    refine ComplexPoints.eq_of_valAt'_eq x.P.A.hom _ _ _ fun q hq hi => ?_
    obtain ⟨z, hz⟩ := u.ex_onto (Over.homMk q hq)
    obtain rfl : (u.ex z).left = q := by rw [hz]; rfl
    rw [key i z hi, hf i z hi, h z]

theorem ex_eq_iff (z w : Fin g → ℂ) : u.ex z = u.ex w ↔ z - w ∈ u.Λ := by
  rw [← u.ker]
  have := u.ex_add (z - w) w
  rw [sub_add_cancel] at this
  rw [this]
  exact mul_eq_right

theorem pt_eq_of_apply_eq {q q' : Pt x} {p p' : Sp ℂ} (h : q.left p = q'.left p') : q = q' := by
  haveI := x.P.isAb.proper
  obtain rfl : p = IsLocalRing.closedPoint ℂ := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
  obtain rfl : p' = IsLocalRing.closedPoint ℂ := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
  exact Over.OverMorphism.ext (ext_of_apply_closedPoint_eq x.P.A.hom (Over.w q) (Over.w q') h)

theorem isBasis_of_levB (hT : ThetaUnifAV) (h : x.P.g = g) {τ : Matrix (Fin g) (Fin g) ℂ} {a b : Fin g → ℂ}
    (hab : charHalf g a b) (hW : Wit x h u τ a b) {l N : ℕ} {Th : Fin N → (Fin g → ℂ) → ℂ} (hTh : LevB τ a b l Th)
    (bs : Fin N → RR x l) (hb : ∀ k, FnPw x u (bs k) (Th k)) : IsBasis x bs := by
  intro s
  obtain ⟨F, ⟨hF, hs⟩, -⟩ := (GlobalTheory.T.lineBundlePow_sections_eq_theta_level hT g x h u τ a b l hab hW).1 s
  simpa only [coords_iff x u bs Th hb s.f F hs] using hTh.2 F hF

end Geo

section Zeros
variable (x : KeyIn ℂ) (u : HolUnif x.P.A x.P.L x.P.g) {τ : Matrix (Fin x.P.g) (Fin x.P.g) ℂ} {a b : Fin x.P.g → ℂ}
  {n d : ℕ} {s : Fin x.P.g → RR x n} {F : Fin x.P.g → (Fin x.P.g → ℂ) → ℂ} {z : Fin d → Fin x.P.g → ℂ}
  {ch : Fin d → x.P.L.ι}

theorem etZ_of_simpleZeros (hT : ThetaUnifAV) (hW : Wit x rfl u τ a b)
    (hF : ∀ i, Differentiable ℂ (F i) ∧ FnPw x u (s i) (F i)) (hz : SimpleZeros τ F z)
    (hc : ∀ e, ⊤ ≤ (u.ex (z e)).left ⁻¹ᵁ x.P.L.U (ch e)) : EtZ x s (fun e => u.ex (z e)) ch := by
  have H := fun e => unif_value_jac_zeros hT _ x rfl u τ a b n s F (z e) (ch e) hW hF (hc e)
  obtain ⟨h0, hd, hdist, hex⟩ := hz
  refine ⟨hc, fun e i => ?_, fun e => ?_, fun e e' hne p hp => ?_, ?_⟩
  · rw [(H e).1 i, h0, zero_mul]
  · rw [(H e).2.1 (h0 e), isUnit_iff_ne_zero]
    exact mul_ne_zero (pow_ne_zero _ (u.fr_ne _ _ (hc e))) ((det_scale_ne_zero _).2 (hd e))
  · obtain ⟨m, m', hm⟩ := (hW.2.2.1 _).1 ((ex_eq_iff x u _ _).1 (pt_eq_of_apply_eq x hp))
    exact hne (hdist e e' m m' (by rw [← hm, add_sub_cancel]))
  · obtain ⟨c, hc0⟩ := exists_chart x u 0
    refine (unif_value_jac_zeros hT _ x rfl u τ a b n s F 0 c hW hF hc0).2.2 d z fun y hy => ?_
    obtain ⟨e, m, m', he⟩ := hex y hy
    exact ⟨e, _, (hW.2.2.1 _).2 ⟨m, m', rfl⟩, he⟩

theorem simpleZeros_of_etZ (hT : ThetaUnifAV) (hW : Wit x rfl u τ a b)
    (hF : ∀ i, Differentiable ℂ (F i) ∧ FnPw x u (s i) (F i)) (hz : EtZ x s (fun e => u.ex (z e)) ch) :
    SimpleZeros τ F z := by
  obtain ⟨hc, h0, hd, hdist, hex⟩ := hz
  have H := fun e => unif_value_jac_zeros hT _ x rfl u τ a b n s F (z e) (ch e) hW hF (hc e)
  have hz0 : ∀ e i, F i (z e) = 0 := fun e i =>
    (mul_eq_zero.1 (((H e).1 i).symm.trans (h0 e i))).resolve_right (pow_ne_zero _ (u.fr_ne _ _ (hc e)))
  refine ⟨hz0, fun e => ?_, fun e e' m m' h => ?_, fun y hy => ?_⟩
  · have := (hd e).ne_zero
    rw [(H e).2.1 (hz0 e)] at this
    exact (det_scale_ne_zero _).1 (right_ne_zero_of_mul this)
  · by_contra hne
    refine hdist e e' hne (IsLocalRing.closedPoint ℂ) ?_
    have : u.ex (z e) = u.ex (z e') :=
      (ex_eq_iff x u _ _).2 ((hW.2.2.1 _).2 ⟨m, m', by rw [h, add_sub_cancel_left]⟩)
    simp only [this]
  · obtain ⟨e, p, hp⟩ := hex ((u.ex y).left (default : PrimeSpectrum ℂ)) fun i hi => by
      obtain ⟨c, hcy⟩ := TopologicalSpace.Opens.mem_iSup.1 hi
      have h1 := (top_le_preimage_iff_mem _ _).2 hcy
      have h2 := (top_le_preimage_basicOpen_iff (u.ex y).left (x.P.L.U c) ((s i).f c)).1 h1
      exact h2 (by rw [(hF i).2 c y (top_le_preimage_of_valAt'_ne_zero _ h2), hy, zero_mul])
    obtain ⟨m, m', hm⟩ := (hW.2.2.1 _).1 ((ex_eq_iff x u _ _).1 (pt_eq_of_apply_eq x hp).symm)
    exact ⟨e, m, m', by rw [← hm, add_sub_cancel]⟩

end Zeros

def formC (g n l l' : ℕ) (t t' : ℂ) (lam lam' : ℕ → ℂ) (J : ℂ) : ℂ :=
  (t ^ (4 * degProd g n l l' ^ (3 * g + 2)) * ∏ j ∈ Finset.range (g + 1),
      lam j ^ ((-1 : ℤ) ^ j * (g.choose j : ℤ) * ((degProd g n l l' / (l - j * n)) ^ (3 * g + 2) : ℕ))) ^
      ((g * n : ℤ) - 2 * l') *
    (t' ^ (4 * degProd g n l l' ^ (3 * g + 2)) * ∏ j ∈ Finset.range (g + 1),
      lam' j ^ ((-1 : ℤ) ^ j * (g.choose j : ℤ) * ((degProd g n l l' / (l' - j * n)) ^ (3 * g + 2) : ℕ))) ^
      ((2 * l : ℤ) - g * n) *
    J ^ (8 * (degProd g n l l' ^ (3 * g + 2) : ℕ) * ((l' : ℤ) - l))

theorem coe_kaForm (g n l l' : ℕ) (t t' J : ℂˣ) (la la' : ℕ → ℂˣ) (lam lam' : ℕ → ℂ)
    (h : ∀ j ≤ g, (la j : ℂ) = lam j) (h' : ∀ j ≤ g, (la' j : ℂ) = lam' j) :
    (kaForm g n l l' t t' la la' J : ℂ) = formC g n l l' t t' lam lam' J := by
  simp only [kaForm, tComb, formC, Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_pow_eq_pow_val,
    Units.coe_prod]
  congr 4
  · exact Finset.prod_congr rfl fun j hj => by rw [h j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))]
  · exact Finset.prod_congr rfl fun j hj => by rw [h' j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))]

theorem kaForm_frame {g n l l' : ℕ} (hl : g * n < l) (hl' : l < l') (t t' J U : ℂˣ) (la la' : ℕ → ℂˣ) :
    kaForm g n l l' (t * U ^ (2 * l)) (t' * U ^ (2 * l')) la la' (J * U ^ (g * n)) = kaForm g n l l' t t' la la' J := by
  have := kaForm_homogeneous ℂ g n l l' t t' J U⁻¹ 1 1 la la' (fun _ => 1) (fun _ => 1) hl hl'
  simp only [one_zpow, one_pow, Finset.prod_const_one, _root_.mul_one, neg_mul, inv_zpow', neg_neg] at this
  rw [← this]
  norm_cast

theorem sub_step {g n l j : ℕ} (h : g * n < l) (hj : j < g) : l - j * n = n + (l - (j + 1) * n) := by
  have : (j + 1) * n ≤ g * n := Nat.mul_le_mul_right _ hj
  have h2 : (j + 1) * n = j * n + n := Nat.succ_mul _ _
  omega

section Point
variable (x : KeyIn ℂ) (u : HolUnif x.P.A x.P.L x.P.g) {τ : Matrix (Fin x.P.g) (Fin x.P.g) ℂ} {a b : Fin x.P.g → ℂ}
  {n d : ℕ} {s : Fin x.P.g → RR x n} {F : Fin x.P.g → (Fin x.P.g → ℂ) → ℂ} {z : Fin d → Fin x.P.g → ℂ}
  {ch : Fin d → x.P.L.ι}

theorem exists_degree (laws : Out.Laws) (hT : ThetaUnifAV) (hab : charHalf x.P.g a b) (hW : Wit x rfl u τ a b)
    {l : ℕ} (hn : 1 ≤ n) (hl : x.P.g * n < l) (al : ℕ → Matrix (Fin 4) (Fin 4) ℤ)
    (hal : ∀ m, (al m).transpose * al m = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ))
    (hF : ∀ i, IsLevel τ a b n (F i) ∧ FnPw x u (s i) (F i)) (hE : EtZ x s (fun e => u.ex (z e)) ch)
    (Th : ∀ j, Fin ((l - j * n) ^ x.P.g) → (Fin x.P.g → ℂ) → ℂ) (hTh : ∀ j ≤ x.P.g, LevB τ a b (l - j * n) (Th j))
    (m) (hm : AnMul (N := fun j => (l - j * n) ^ x.P.g) F Th m) (lam : ℕ → ℂ)
    (hlam : ∀ j ≤ x.P.g, ∀ (bs : Fin ((l - j * n) ^ x.P.g) → RR x (l - j * n)) (la : ℂˣ),
      (∀ k, FnPw x u (bs k) (Th j k)) → IsSquareDeterminantComparison x (l - j * n) (al (l - j * n)) bs la → (la : ℂ) = lam j)
    (U : ℂˣ) (hU : (U : ℂ) = ∏ e, u.fr (ch e) (z e)) :
    ∃ (bs : ∀ j, Fin ((l - j * n) ^ x.P.g) → RR x (l - j * n)) (t : ℂˣ) (la : ℕ → ℂˣ),
      (∀ j ≤ x.P.g, IsBasis x (bs j) ∧ IsSquareDeterminantComparison x (l - j * n) (al (l - j * n)) (bs j) (la j)) ∧
      (∀ j ≤ x.P.g, (la j : ℂ) = lam j) ∧
      KosVal x l s (fun e => u.ex (z e)) ch bs (t * U ^ (2 * l) : ℂˣ) ∧
      TorsSq kdeg (kosD (N := fun j => (l - j * n) ^ x.P.g) m (evAn (N := fun j => (l - j * n) ^ x.P.g) Th z)) (t : ℂ) := by
  have h1 : ∀ j k, ∃ s : RR x (l - j * n), j ≤ x.P.g → FnPw x u s (Th j k) := by
    intro j k
    have hd := (GlobalTheory.T.lineBundlePow_sections_eq_theta_level hT _ x rfl u τ a b (l - j * n) hab hW).2
    by_cases hj : j ≤ x.P.g
    · obtain ⟨s, hs, -⟩ := hd _ ((hTh j hj).1 k)
      exact ⟨s, fun _ => hs⟩
    · obtain ⟨s, -⟩ := hd (fun _ => 0) ⟨differentiable_const _, fun _ _ _ => (mul_zero _).symm⟩
      exact ⟨s, fun h => absurd h hj⟩
  choose bs hbs using h1
  have hb : ∀ j ≤ x.P.g, IsBasis x (bs j) := fun j hj =>
    isBasis_of_levB x u hT rfl hab hW (hTh j hj) (bs j) fun k => hbs j k hj
  have h2 : ∀ j, ∃ la : ℂˣ, j ≤ x.P.g → IsSquareDeterminantComparison x (l - j * n) (al (l - j * n)) (bs j) la := by
    intro j
    by_cases hj : j ≤ x.P.g
    · have : j * n ≤ x.P.g * n := Nat.mul_le_mul_right _ hj
      obtain ⟨la, hla⟩ := GlobalTheory.T.exists_squareDeterminantComparison_isAlgClosed laws ℂ x (l - j * n) _ (bs j) (Nat.cast_ne_zero.2 (by omega)) (hal _) (hb j hj)
      exact ⟨la, fun _ => hla⟩
    · exact ⟨1, fun h => absurd h hj⟩
  choose la hla using h2
  obtain ⟨-, t₀, m₀, hm₀, ht₀⟩ := GlobalTheory.T.exists_koszulTorsion_transversal_split_zeros laws ℂ x n l d s bs _ ch hn hl hb hE
  have hcx := (KoszulCx.koszul_isCx ℂ x n l d s bs _ ch hl hb).2 m₀ hm₀ hE.1 hE.2.1
  have hfr : ∀ e, u.fr (ch e) (z e) ≠ 0 := fun e => u.fr_ne _ _ (hE.1 e)
  have hdet : (Matrix.diagonal fun e => u.fr (ch e) (z e) ^ l).det = (U : ℂ) ^ l := by
    rw [Matrix.det_diagonal, hU, Finset.prod_pow]
  obtain ⟨t, ht, htt⟩ := torsSq_kosD_conj ℂ x.P.g d (fun j => (l - j * n) ^ x.P.g) m₀ m _
    (evAn (N := fun j => (l - j * n) ^ x.P.g) Th z) (fun _ => 1)
    (Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal fun e => u.fr (ch e) (z e) ^ l)
      (hdet ▸ pow_ne_zero _ U.ne_zero)) t₀ (fun i j hj => by
      simp only [Units.val_one, Matrix.one_mul, Matrix.mul_one]
      ext k' k
      have hlev := IsLevel.mul (hF i).1 ((hTh (j + 1) hj).1 k) (sub_step hl hj)
      have e := (coords_iff x u (bs j) (Th j) (fun k => hbs j k hj.le) _ (fun z => F i z * Th (j + 1) k z)
        (fun c y hy => by
          rw [valAt'_mul]
          refine (congrArg₂ (· * ·) ((hF i).2 c y hy) (hbs (j + 1) k hj c y hy)).trans ?_
          rw [congrArg (u.fr c y ^ ·) (sub_step hl hj), pow_add]
          ring) _).1 (hm₀ i j hj k)
      exact congrFun (((hTh j hj.le).2 _ hlev).unique (hm i j hj k) e) k')
    (by
      ext e k
      simp only [Units.val_one, Matrix.mul_one]
      refine (Matrix.diagonal_mul _ _ _ _).trans ?_
      refine Eq.trans ?_ (hbs 0 k (Nat.zero_le _) (ch e) (z e) (hE.1 e)).symm
      simp [evAn, mul_comm]) hcx ht₀
  refine ⟨bs, t, la, fun j hj => ⟨hb j hj, hla j hj⟩,
    fun j hj => hlam j hj _ _ (fun k => hbs j k hj) (hla j hj), ⟨m₀, hm₀, ?_⟩, ht⟩
  have : t * U ^ (2 * l) = t₀ := by
    simp only [map_one, one_zpow, Finset.prod_const_one, _root_.mul_one] at htt
    rw [← htt, mul_comm 2 l, pow_mul]
    congr 2
    exact Units.ext hdet.symm
  rw [this]
  exact ht₀

end Point

theorem exists_kaVal (laws : Out.Laws) (hT : ThetaUnifAV) {g n l l' : ℕ} {al : ℕ → Matrix (Fin 4) (Fin 4) ℤ}
    {a b : Fin g → ℂ} (hab : charHalf g a b) (hadm : admitted g n l l' al) {τ : Matrix (Fin g) (Fin g) ℂ}
    (x : KeyIn ℂ) (h : x.P.g = g) (u : HolUnif x.P.A x.P.L g) (hW : Wit x h u τ a b)
    {F : Fin g → (Fin g → ℂ) → ℂ} (hF : ∀ i, IsLevel τ a b n (F i)) {z : Fin (g.factorial * n ^ g) → Fin g → ℂ}
    (hz : SimpleZeros τ F z)
    (Th : ∀ j, Fin ((l - j * n) ^ g) → (Fin g → ℂ) → ℂ) (hTh : ∀ j ≤ g, LevB τ a b (l - j * n) (Th j))
    (m) (hm : AnMul (N := fun j => (l - j * n) ^ g) F Th m) (lam : ℕ → ℂ)
    (hlam : ∀ j ≤ g, ∀ (bs : Fin ((l - j * n) ^ x.P.g) → RR x (l - j * n)) (la : ℂˣ),
      (∀ k, FnPw x u (bs k) (Th j (k.cast (by rw [h])))) → IsSquareDeterminantComparison x (l - j * n) (al (l - j * n)) bs la →
      (la : ℂ) = lam j)
    (Th' : ∀ j, Fin ((l' - j * n) ^ g) → (Fin g → ℂ) → ℂ) (hTh' : ∀ j ≤ g, LevB τ a b (l' - j * n) (Th' j))
    (m') (hm' : AnMul (N := fun j => (l' - j * n) ^ g) F Th' m') (lam' : ℕ → ℂ)
    (hlam' : ∀ j ≤ g, ∀ (bs : Fin ((l' - j * n) ^ x.P.g) → RR x (l' - j * n)) (la : ℂˣ),
      (∀ k, FnPw x u (bs k) (Th' j (k.cast (by rw [h])))) → IsSquareDeterminantComparison x (l' - j * n) (al (l' - j * n)) bs la →
      (la : ℂ) = lam' j) :
    ∃ (s : Fin x.P.g → RR x n) (κ : ℂˣ) (t t' : ℂ), KaVal x n l l' al s κ ∧
      TorsSq kdeg (kosD (N := fun j => (l - j * n) ^ g) m (evAn (N := fun j => (l - j * n) ^ g) Th z)) t ∧
      TorsSq kdeg (kosD (N := fun j => (l' - j * n) ^ g) m' (evAn (N := fun j => (l' - j * n) ^ g) Th' z)) t' ∧
      (∀ j ≤ g, lam j ≠ 0 ∧ lam' j ≠ 0) ∧ (κ : ℂ) = formC g n l l' t t' lam lam' (jacAn F z) := by
  subst h
  obtain ⟨hn, hl, hl', hal⟩ := hadm
  choose s hs using fun i => ((GlobalTheory.T.lineBundlePow_sections_eq_theta_level hT _ x rfl u τ a b n hab hW).2 _ (hF i)).exists
  choose ch hch using fun e => exists_chart x u (z e)
  have hE := etZ_of_simpleZeros x u hT hW (fun i => ⟨(hF i).1, hs i⟩) hz hch
  have hU : (∏ e, u.fr (ch e) (z e)) ≠ 0 := Finset.prod_ne_zero_iff.2 fun e _ => u.fr_ne _ _ (hch e)
  have hJ : jacAn F z ≠ 0 := Finset.prod_ne_zero_iff.2 fun e _ => (det_scale_ne_zero _).2 (hz.2.1 e)
  obtain ⟨bs, t, la, h1, h2, h3, h4⟩ := exists_degree x u laws hT hab hW (by omega) hl al hal
    (fun i => ⟨hF i, hs i⟩) hE Th hTh m hm lam hlam (Units.mk0 _ hU) rfl
  obtain ⟨bs', t', la', h1', h2', h3', h4'⟩ := exists_degree x u laws hT hab hW (by omega) (hl.trans hl') al hal
    (fun i => ⟨hF i, hs i⟩) hE Th' hTh' m' hm' lam' hlam' (Units.mk0 _ hU) rfl
  refine ⟨s, _, t, t', ⟨_, ch, bs, bs', _, _, Units.mk0 _ hJ * Units.mk0 _ hU ^ (x.P.g * n), la, la', hE, ?_, h1, h1',
    h3, h3', rfl⟩, h4, h4', fun j hj => ⟨h2 j hj ▸ (la j).ne_zero, h2' j hj ▸ (la' j).ne_zero⟩, ?_⟩
  · simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_mk0]
    rw [jacAn, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun e _ => ?_
    rw [(unif_value_jac_zeros hT _ x rfl u τ a b n s F (z e) (ch e) hW (fun i => ⟨(hF i).1, hs i⟩) (hch e)).2.1
      (hz.1 e), mul_comm]
    rfl
  · rw [kaForm_frame hl hl', coe_kaForm _ _ _ _ _ _ _ _ _ lam lam' h2 h2']
    rfl

theorem exists_simpleZeros (hT : ThetaUnifAV) {g n l l' : ℕ} {al : ℕ → Matrix (Fin 4) (Fin 4) ℤ}
    {a b : Fin g → ℂ} (hab : charHalf g a b) {τ : Matrix (Fin g) (Fin g) ℂ}
    (x : KeyIn ℂ) (h : x.P.g = g) (u : HolUnif x.P.A x.P.L g) (hW : Wit x h u τ a b)
    (s : Fin x.P.g → RR x n) (κ : ℂˣ) (hk : KaVal x n l l' al s κ) :
    ∃ (F : Fin g → (Fin g → ℂ) → ℂ) (z : Fin (g.factorial * n ^ g) → Fin g → ℂ),
      (∀ i, IsLevel τ a b n (F i)) ∧ SimpleZeros τ F z := by
  subst h
  obtain ⟨q, ch, -, -, -, -, -, -, -, hE, -⟩ := hk
  choose F hF hs using fun i => ((GlobalTheory.T.lineBundlePow_sections_eq_theta_level hT _ x rfl u τ a b n hab hW).1 (s i)).exists
  choose z hz using fun e => u.ex_onto (q e)
  obtain rfl : q = fun e => u.ex (z e) := funext fun e => (hz e).symm
  exact ⟨F, z, hF, simpleZeros_of_etZ x u hT hW (fun i => ⟨(hF i).1, hs i⟩) hE⟩

section An
variable {g : ℕ}

theorem differentiableOn_prod {E I : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {W : Set E} {s : Finset I}
    {f : I → E → ℂ} (h : ∀ i ∈ s, DifferentiableOn ℂ (f i) W) : DifferentiableOn ℂ (fun p => ∏ i ∈ s, f i p) W := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using differentiableOn_const (1 : ℂ)
  | insert i s hi ih =>
    simp only [Finset.prod_insert hi]
    exact (h i (Finset.mem_insert_self _ _)).mul (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem isLevel_sum {N l : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ} {a b : Fin g → ℂ} {Th : Fin N → (Fin g → ℂ) → ℂ}
    (h : ∀ k, IsLevel τ a b l (Th k)) (c : Fin N → ℂ) : IsLevel τ a b l (fun z => ∑ k, c k * Th k z) := by
  refine ⟨Differentiable.fun_sum fun k _ => (h k).1.const_mul _, fun m n z => ?_⟩
  simp only [(h _).2, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem LevB.coord_eq {N l : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ} {a b : Fin g → ℂ} {Th : Fin N → (Fin g → ℂ) → ℂ}
    (h : LevB τ a b l Th) {c c' : Fin N → ℂ} (e : ∀ z, ∑ k, c k * Th k z = ∑ k, c' k * Th k z) : c = c' :=
  (h.2 _ (isLevel_sum h.1 c)).unique (fun _ => rfl) e

theorem LevB.linearIndependent {N l : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ} {a b : Fin g → ℂ}
    {Th : Fin N → (Fin g → ℂ) → ℂ} (h : LevB τ a b l Th) : LinearIndependent ℂ Th := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  refine congrFun (h.coord_eq (c' := 0) fun z => ?_)
  simpa using congrFun hc z

theorem isCx_an {d : ℕ} {N lv : ℕ → ℕ} {τ : Matrix (Fin g) (Fin g) ℂ} {a b : Fin g → ℂ}
    {F : Fin g → (Fin g → ℂ) → ℂ} {Th : ∀ j, Fin (N j) → (Fin g → ℂ) → ℂ} (hTh : ∀ j ≤ g, LevB τ a b (lv j) (Th j))
    {m} (hm : AnMul F Th m) {z : Fin d → Fin g → ℂ} (hz : ∀ e i, F i (z e) = 0) :
    IsCx kdeg (kosD m (evAn Th z)) := by
  have key : ∀ i i' j, j + 2 ≤ g → ∀ k y, ∑ k', (m i j (j + 1) * m i' (j + 1) (j + 2)) k' k * Th j k' y =
      F i y * (F i' y * Th (j + 2) k y) := by
    intro i i' j hj k y
    rw [hm i' (j + 1) (by omega), Finset.mul_sum]
    simp only [Matrix.mul_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k₁ _ => ?_
    rw [mul_left_comm, hm i j (by omega), Finset.mul_sum]
    exact Finset.sum_congr rfl fun k₂ _ => by ring
  refine KoszulCx.isCx_kosD m _ (fun i i' j hj => ?_) fun i => ?_
  · ext k' k
    exact congrFun ((hTh j (by omega)).coord_eq (c := fun k' => (m i j (j + 1) * m i' (j + 1) (j + 2)) k' k)
      (c' := fun k' => (m i' j (j + 1) * m i (j + 1) (j + 2)) k' k) fun y => by
        rw [key i i' j hj, key i' i j hj, mul_left_comm]) k'
  · ext e k
    have := hm i 0 i.pos k (z e)
    rw [hz, zero_mul] at this
    rw [Matrix.mul_apply, Matrix.zero_apply, this]
    exact Finset.sum_congr rfl fun k' _ => mul_comm _ _

theorem differentiableOn_kosD {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {W : Set E} {d : ℕ} {N : ℕ → ℕ}
    (m : E → Fin g → ∀ j j', Matrix (Fin (N j)) (Fin (N j')) ℂ) (ev : E → ∀ j, Matrix (Fin d) (Fin (N j)) ℂ)
    (hm : ∀ i j, j < g → ∀ k' k, DifferentiableOn ℂ (fun p => m p i j (j + 1) k' k) W)
    (hev : ∀ e k, DifferentiableOn ℂ (fun p => ev p 0 e k) W) (r c : KIx g d N) :
    DifferentiableOn ℂ (fun p => kosD (m p) (ev p) r c) W := by
  have hm' : ∀ i j j', j' = j + 1 → j' ≤ g → ∀ k' k, DifferentiableOn ℂ (fun p => m p i j j' k' k) W := by
    rintro i j _ rfl h
    exact hm i j h
  have hev' : ∀ j, j = 0 → ∀ e k, DifferentiableOn ℂ (fun p => ev p j e k) W := by
    rintro _ rfl
    exact hev
  rcases r with r | r <;> rcases c with c | c <;> simp only [kosD]
  · refine DifferentiableOn.fun_sum fun i _ => ?_
    split_ifs with h
    · exact (hm' i _ _ (by rw [h.2, Finset.card_insert_of_notMem h.1])
        (by simpa using Finset.card_le_univ c.1) _ _).const_mul _
    · exact differentiableOn_const _
  · exact differentiableOn_const _
  · split_ifs with h
    · exact hev' _ (by simp [h]) _ _
    · exact differentiableOn_const _
  · exact differentiableOn_const _

theorem holFam_comp {F : (Fin g → Fin g → ℂ) → (Fin g → ℂ) → ℂ} (hF : HolFam (Key.phDom g) F)
    {W : Set (Fin g → Fin g → ℂ)} (hW : W ⊆ Key.phDom g) {z : (Fin g → Fin g → ℂ) → Fin g → ℂ}
    (hz : DifferentiableOn ℂ z W) : DifferentiableOn ℂ (fun p => F p (z p)) W :=
  DifferentiableOn.comp (f := fun p => (p, z p)) hF (differentiableOn_id.prodMk hz) fun _ hp => ⟨hW hp, trivial⟩

theorem holFam_fderiv {F : (Fin g → Fin g → ℂ) → (Fin g → ℂ) → ℂ} (hF : HolFam (Key.phDom g) F)
    {W : Set (Fin g → Fin g → ℂ)} (hW : W ⊆ Key.phDom g) {z : (Fin g → Fin g → ℂ) → Fin g → ℂ}
    (hz : DifferentiableOn ℂ z W) (v : Fin g → ℂ) : DifferentiableOn ℂ (fun p => fderiv ℂ (F p) (z p) v) W := by
  intro p hp
  have hc : ContDiffAt ℂ 2 (fun q : (Fin g → Fin g → ℂ) × (Fin g → ℂ) => F q.1 q.2) (p, z p) :=
    GlobalTheory.SCV.contDiffAt_of_differentiableOn hF
      (prod_mem_nhds ((GlobalTheory.isOpen_phDom g).mem_nhds (hW hp)) Filter.univ_mem) 2
  have h1 : ContDiffAt ℂ 1 (fun q : (Fin g → Fin g → ℂ) × (Fin g → ℂ) => fderiv ℂ (F q.1) q.2) (p, z p) := by
    refine ContDiffAt.fderiv (f := fun q : (Fin g → Fin g → ℂ) × (Fin g → ℂ) => F q.1) (n := 2) ?_ contDiffAt_snd
      (by norm_num)
    exact ContDiffAt.comp (g := fun q : (Fin g → Fin g → ℂ) × (Fin g → ℂ) => F q.1 q.2)
      (f := fun q : ((Fin g → Fin g → ℂ) × (Fin g → ℂ)) × (Fin g → ℂ) => (q.1.1, q.2)) ((p, z p), z p) hc
      (contDiffAt_fst.fst.prodMk contDiffAt_snd)
  exact (DifferentiableAt.comp_differentiableWithinAt (f := fun p => (p, z p)) p (h1.differentiableAt one_ne_zero)
    (differentiableWithinAt_id.prodMk (hz p hp))).clm_apply (differentiableWithinAt_const _)

theorem differentiableOn_jacAn {d : ℕ} {F : Fin g → (Fin g → Fin g → ℂ) → (Fin g → ℂ) → ℂ}
    (hF : ∀ i, HolFam (Key.phDom g) (F i)) {W : Set (Fin g → Fin g → ℂ)} (hW : W ⊆ Key.phDom g)
    {z : (Fin g → Fin g → ℂ) → Fin d → Fin g → ℂ} (hz : DifferentiableOn ℂ z W) :
    DifferentiableOn ℂ (fun p => jacAn (fun i => F i p) (z p)) W := by
  refine differentiableOn_prod fun e _ => ?_
  simp only [Matrix.det_apply', Matrix.of_apply]
  refine DifferentiableOn.fun_sum fun σ _ => DifferentiableOn.const_mul ?_ _
  exact differentiableOn_prod fun k _ =>
    (holFam_fderiv (hF _) hW (differentiableOn_pi.1 hz e) _).const_mul _

theorem differentiableOn_formC {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {W : Set E} (n l l' : ℕ)
    {t t' J : E → ℂ} {lam lam' : ℕ → E → ℂ} (ht : DifferentiableOn ℂ t W) (ht' : DifferentiableOn ℂ t' W)
    (hJ : DifferentiableOn ℂ J W) (hl : ∀ j ≤ g, DifferentiableOn ℂ (lam j) W)
    (hl' : ∀ j ≤ g, DifferentiableOn ℂ (lam' j) W)
    (h0 : ∀ p ∈ W, t p ≠ 0 ∧ t' p ≠ 0 ∧ J p ≠ 0 ∧ ∀ j ≤ g, lam j p ≠ 0 ∧ lam' j p ≠ 0) :
    DifferentiableOn ℂ (fun p => formC g n l l' (t p) (t' p) (fun j => lam j p) (fun j => lam' j p) (J p)) W := by
  have hj : ∀ {j}, j ∈ Finset.range (g + 1) → j ≤ g := fun h => Nat.lt_succ_iff.1 (Finset.mem_range.1 h)
  refine (DifferentiableOn.mul (DifferentiableOn.zpow ((ht.pow _).mul (differentiableOn_prod fun j h =>
    (hl j (hj h)).zpow (Or.inl fun p hp => ((h0 p hp).2.2.2 j (hj h)).1))) (Or.inl fun p hp => ?_))
    (DifferentiableOn.zpow ((ht'.pow _).mul (differentiableOn_prod fun j h =>
    (hl' j (hj h)).zpow (Or.inl fun p hp => ((h0 p hp).2.2.2 j (hj h)).2))) (Or.inl fun p hp => ?_))).mul
    (hJ.zpow (Or.inl fun p hp => (h0 p hp).2.2.1))
  · exact mul_ne_zero (pow_ne_zero _ (h0 p hp).1)
      (Finset.prod_ne_zero_iff.2 fun j h => zpow_ne_zero _ ((h0 p hp).2.2.2 j (hj h)).1)
  · exact mul_ne_zero (pow_ne_zero _ (h0 p hp).2.1)
      (Finset.prod_ne_zero_iff.2 fun j h => zpow_ne_zero _ ((h0 p hp).2.2.2 j (hj h)).2)

theorem exists_data (laws : Out.Laws) (hT : ThetaUnifAV) {n l d : ℕ} {a b : Fin g → ℂ} (hab : charHalf g a b)
    (hl : g * n < l) (al : ℕ → Matrix (Fin 4) (Fin 4) ℤ)
    (hal : ∀ m, (al m).transpose * al m = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ))
    {F : Fin g → (Fin g → Fin g → ℂ) → (Fin g → ℂ) → ℂ} (hF : ∀ i, HolFam (Key.phDom g) (F i))
    (hL : ∀ i, ∀ p ∈ Key.phDom g, IsLevel (per p) a b n (F i p))
    {W : Set (Fin g → Fin g → ℂ)} (hW : W ⊆ Key.phDom g)
    {z : (Fin g → Fin g → ℂ) → Fin d → Fin g → ℂ} (hz : DifferentiableOn ℂ z W)
    (hz0 : ∀ p ∈ W, ∀ e i, F i p (z p e) = 0) :
    ∃ (Th : ∀ j, Fin ((l - j * n) ^ g) → (Fin g → Fin g → ℂ) → (Fin g → ℂ) → ℂ)
      (m : (Fin g → Fin g → ℂ) → Fin g → ∀ j j', Matrix (Fin ((l - j * n) ^ g)) (Fin ((l - j' * n) ^ g)) ℂ)
      (lam : ℕ → (Fin g → Fin g → ℂ) → ℂ),
      (∀ p ∈ Key.phDom g, ∀ j ≤ g, LevB (per p) a b (l - j * n) (fun k => Th j k p)) ∧
      (∀ p ∈ Key.phDom g, AnMul (N := fun j => (l - j * n) ^ g) (fun i => F i p) (fun j k => Th j k p) (m p)) ∧
      (∀ j ≤ g, DifferentiableOn ℂ (lam j) (Key.phDom g)) ∧
      (∀ p ∈ Key.phDom g, ∀ (x : KeyIn ℂ) (h : x.P.g = g) (u : HolUnif x.P.A x.P.L g), Wit x h u (per p) a b →
        ∀ j ≤ g, ∀ (bs : Fin ((l - j * n) ^ x.P.g) → RR x (l - j * n)) (la : ℂˣ),
          (∀ k, FnPw x u (bs k) (Th j (k.cast (by rw [h])) p)) → IsSquareDeterminantComparison x (l - j * n) (al (l - j * n)) bs la →
          (la : ℂ) = lam j p) ∧
      (∀ r c, DifferentiableOn ℂ (fun p => kosD (N := fun j => (l - j * n) ^ g) (m p)
        (evAn (N := fun j => (l - j * n) ^ g) (fun j k => Th j k p) (z p)) r c) W) ∧
      ∀ p ∈ W, IsCx kdeg (kosD (N := fun j => (l - j * n) ^ g) (m p)
        (evAn (N := fun j => (l - j * n) ^ g) (fun j k => Th j k p) (z p))) := by
  have hpos : ∀ j ≤ g, 1 ≤ l - j * n := fun j hj => by
    have : j * n ≤ g * n := Nat.mul_le_mul_right _ hj
    omega
  have h1 : ∀ j, ∃ Th : Fin ((l - j * n) ^ g) → (Fin g → Fin g → ℂ) → (Fin g → ℂ) → ℂ,
      j ≤ g → LevBasis a b (l - j * n) Th := fun j => by
    by_cases hj : j ≤ g
    · obtain ⟨Th, h⟩ := LevelBasis.exists_levBasis g a b _ hab (hpos j hj)
      exact ⟨Th, fun _ => h⟩
    · exact ⟨0, fun h => absurd h hj⟩
  choose Th hTh using h1
  have hB : ∀ p ∈ Key.phDom g, ∀ j ≤ g, LevB (per p) a b (l - j * n) (fun k => Th j k p) :=
    fun p hp j hj => (hTh j hj).2 p hp
  have h2 : ∀ p i j (k : Fin ((l - (j + 1) * n) ^ g)), ∃ c : Fin ((l - j * n) ^ g) → ℂ,
      p ∈ Key.phDom g → j < g → ∀ y, F i p y * Th (j + 1) k p y = ∑ k', c k' * Th j k' p y := fun p i j k => by
    by_cases hp : p ∈ Key.phDom g ∧ j < g
    · obtain ⟨c, hc, -⟩ := (hB p hp.1 j hp.2.le).2 _
        (IsLevel.mul (hL i p hp.1) ((hB p hp.1 (j + 1) hp.2).1 k) (sub_step hl hp.2))
      exact ⟨c, fun _ _ => hc⟩
    · exact ⟨0, fun h h' => absurd ⟨h, h'⟩ hp⟩
  choose c hc using h2
  have h3 : ∀ j, ∃ lam : (Fin g → Fin g → ℂ) → ℂ, j ≤ g → DifferentiableOn ℂ lam (Key.phDom g) ∧
      ∀ p ∈ Key.phDom g, ∀ (x : KeyIn ℂ) (h : x.P.g = g) (u : HolUnif x.P.A x.P.L g)
        (bs : Fin ((l - j * n) ^ x.P.g) → RR x (l - j * n)) (la : ℂˣ), Wit x h u (per p) a b →
        (∀ k, FnPw x u (bs k) (Th j (k.cast (by rw [h])) p)) → IsSquareDeterminantComparison x (l - j * n) (al (l - j * n)) bs la →
        (la : ℂ) = lam p := fun j => by
    by_cases hj : j ≤ g
    · obtain ⟨lam, h⟩ := GlobalTheory.T.exists_holomorphic_theta_of_level_basis laws hT g _ a b _ (Th j) hab (hpos j hj) (hal _) (hTh j hj)
      exact ⟨lam, fun _ => h⟩
    · exact ⟨0, fun h => absurd h hj⟩
  choose lam hlam using h3
  let m : (Fin g → Fin g → ℂ) → Fin g → ∀ j j', Matrix (Fin ((l - j * n) ^ g)) (Fin ((l - j' * n) ^ g)) ℂ :=
    fun p i j j' => if h : j' = j + 1 then Matrix.of fun k' k => c p i j (h ▸ k) k' else 0
  have hmc : ∀ p i j k' k, m p i j (j + 1) k' k = c p i j k k' := fun p i j k' k => by
    simp only [m, dif_pos, Matrix.of_apply]
  have hm : ∀ p ∈ Key.phDom g,
      AnMul (N := fun j => (l - j * n) ^ g) (fun i => F i p) (fun j k => Th j k p) (m p) := by
    intro p hp i j hj k y
    simp only [hmc]
    exact hc p i j k hp hj y
  refine ⟨Th, m, lam, hB, hm, fun j hj => (hlam j hj).1,
    fun p hp x h u hx j hj bs la => (hlam j hj).2 p hp x h u bs la hx, ?_,
    fun p hp => isCx_an (N := fun j => (l - j * n) ^ g) (hB p (hW hp)) (hm p (hW hp)) (hz0 p hp)⟩
  refine differentiableOn_kosD (N := fun j => (l - j * n) ^ g) m _ (fun i j hj k' k => ?_) fun e k => ?_
  · simp only [hmc]
    refine (differentiableOn_coord_of_linearIndependent _ _ _ (Key.phDom g) (Th j)
      (fun p y => F i p y * Th (j + 1) k p y) (fun p => c p i j k) (GlobalTheory.isOpen_phDom g)
      (fun k y => holFam_comp ((hTh j hj.le).1 k) subset_rfl (differentiableOn_const y))
      (fun y => (holFam_comp (hF i) subset_rfl (differentiableOn_const y)).mul
        (holFam_comp ((hTh (j + 1) hj).1 k) subset_rfl (differentiableOn_const y)))
      (fun p hp => (hB p hp j hj.le).linearIndependent) (fun p hp => hc p i j k hp hj) k').mono hW
  · exact holFam_comp ((hTh 0 (Nat.zero_le _)).1 k) hW (differentiableOn_pi.1 hz e)

end An

theorem kaVal_locally_holomorphic : Out.Laws → ThetaUnifAV → ∀ (g : ℕ) (n l l' : ℕ) (al : ℕ → Matrix (Fin 4) (Fin 4) ℤ) (a b : Fin g → ℂ) (p₀ : (Fin g → Fin g → ℂ)) (x₀ : KeyIn ℂ) (h₀ : x₀.P.g = g) (u₀ : HolUnif x₀.P.A x₀.P.L g) (s₀ : Fin x₀.P.g → RR x₀ n) (κ₀ : ℂˣ), charHalf g a b → admitted g n l l' al → p₀ ∈ Key.phDom g → Wit x₀ h₀ u₀ (per p₀) a b → KaVal x₀ n l l' al s₀ κ₀ → ∃ (W : Set (Fin g → Fin g → ℂ)) (V : (Fin g → Fin g → ℂ) → ℂ), IsOpen W ∧ p₀ ∈ W ∧ W ⊆ Key.phDom g ∧ DifferentiableOn ℂ V W ∧ ∀ p ∈ W, ∀ (x : KeyIn ℂ) (h : x.P.g = g) (u : HolUnif x.P.A x.P.L g), Wit x h u (per p) a b → ∃ (s : Fin x.P.g → RR x n) (κ : ℂˣ), KaVal x n l l' al s κ ∧ (κ : ℂ) = V p := by
  intro laws hT g n l l' al a b p₀ x₀ h₀ u₀ s₀ κ₀ hab hadm hp₀ hW₀ hk₀
  obtain ⟨F₀, z₀, hF₀, hz₀⟩ := exists_simpleZeros hT hab x₀ h₀ u₀ hW₀ s₀ κ₀ hk₀
  obtain ⟨B, hB⟩ := LevelBasis.exists_levBasis g a b n hab (by have := hadm.1; omega)
  choose T hT₀ using fun i => ((hB.2 p₀ hp₀).2 _ (hF₀ i)).exists
  let F : Fin g → (Fin g → Fin g → ℂ) → (Fin g → ℂ) → ℂ := fun i p y => ∑ k, T i k * B k p y
  have hF : ∀ i, HolFam (Key.phDom g) (F i) := fun i =>
    DifferentiableOn.fun_sum fun k _ => DifferentiableOn.const_mul (hB.1 k) _
  have hL : ∀ i, ∀ p ∈ Key.phDom g, IsLevel (per p) a b n (F i p) := fun i p hp =>
    isLevel_sum (hB.2 p hp).1 _
  obtain rfl : F₀ = fun i => F i p₀ := funext fun i => funext (hT₀ i)
  obtain ⟨W₁, z, hW₁, hp₁, hd₁, hzp, hz, hG⟩ :=
    HolZeros.simple_zeros_move_holomorphically g n _ a b F p₀ z₀ hp₀ hF hL hz₀
  replace hG : ∀ p ∈ W₁, SimpleZeros (per p) (fun i => F i p) (z p) := hG
  obtain ⟨Th, m, lam, k1, k2, k3, k4, k5, k6⟩ := exists_data laws hT hab hadm.2.1 al hadm.2.2.2 hF hL hd₁ hz
    fun p hp => (hG p hp).1
  obtain ⟨Th', m', lam', k1', k2', k3', k4', k5', k6'⟩ := exists_data laws hT hab (hadm.2.1.trans hadm.2.2.1) al
    hadm.2.2.2 hF hL hd₁ hz fun p hp => (hG p hp).1
  have main := fun p (hp : p ∈ W₁) x h u hx => exists_kaVal laws hT hab hadm x h u hx (fun i => hL i p (hd₁ hp))
    (hG p hp) _ (k1 p (hd₁ hp)) _ (k2 p (hd₁ hp)) (fun j => lam j p) (k4 p (hd₁ hp) x h u hx)
    _ (k1' p (hd₁ hp)) _ (k2' p (hd₁ hp)) (fun j => lam' j p) (k4' p (hd₁ hp) x h u hx)
  obtain ⟨-, -, t₀, t₀', -, ht₀, ht₀', hl₀, -⟩ := main p₀ hp₁ x₀ h₀ u₀ hW₀
  obtain ⟨W₂, t, hW₂, hp₂, hd₂, ht, htt⟩ :=
    TorsionHolomorphic.exists_differentiableOn_torsSq _ _ kdeg _ W₁ p₀ t₀ hW₁ hp₁ k5 k6 ht₀
  obtain ⟨W₃, t', hW₃, hp₃, hd₃, ht', htt'⟩ :=
    TorsionHolomorphic.exists_differentiableOn_torsSq _ _ kdeg _ W₁ p₀ t₀' hW₁ hp₁ k5' k6' ht₀'
  have hn := (GlobalTheory.isOpen_phDom g).mem_nhds hp₀
  have hev : ∀ᶠ p in nhds p₀, p ∈ W₂ ∧ p ∈ W₃ ∧ ∀ j ∈ Set.Iic g, lam j p ≠ 0 ∧ lam' j p ≠ 0 := by
    refine Filter.Eventually.and (hW₂.mem_nhds hp₂) (Filter.Eventually.and (hW₃.mem_nhds hp₃) ?_)
    refine (Filter.eventually_all_finite (Set.finite_Iic g)).2 fun j hj => ?_
    exact (((k3 j hj).differentiableAt hn).continuousAt.eventually_ne (hl₀ j hj).1).and
      (((k3' j hj).differentiableAt hn).continuousAt.eventually_ne (hl₀ j hj).2)
  obtain ⟨W, hW, hWo, hpW⟩ := eventually_nhds_iff.1 hev
  have s₂ : W ⊆ W₂ := fun p hp => (hW p hp).1
  have s₃ : W ⊆ W₃ := fun p hp => (hW p hp).2.1
  have s₁ : W ⊆ W₁ := s₂.trans hd₂
  have s₀ : W ⊆ Key.phDom g := s₁.trans hd₁
  refine ⟨W, fun p => formC g n l l' (t p) (t' p) (fun j => lam j p) (fun j => lam' j p)
    (jacAn (fun i => F i p) (z p)), hWo, hpW, s₀, ?_, fun p hp x h u hx => ?_⟩
  · refine differentiableOn_formC n l l' (ht.mono s₂) (ht'.mono s₃) (differentiableOn_jacAn hF s₀ (hz.mono s₁))
      (fun j hj => (k3 j hj).mono s₀) (fun j hj => (k3' j hj).mono s₀) fun p hp => ⟨?_, ?_, ?_, (hW p hp).2.2⟩
    · exact (TorsionUnique.torsSq_unique _ _ _ _ _ _ (k6 p (s₁ hp)) (htt p (s₂ hp)) (htt p (s₂ hp))).2.ne_zero
    · exact (TorsionUnique.torsSq_unique _ _ _ _ _ _ (k6' p (s₁ hp)) (htt' p (s₃ hp)) (htt' p (s₃ hp))).2.ne_zero
    · exact Finset.prod_ne_zero_iff.2 fun e _ => (det_scale_ne_zero _).2 ((hG p (s₁ hp)).2.1 e)
  · obtain ⟨s, κ, r, r', hk, hr, hr', -, hκ⟩ := main p (s₁ hp) x h u hx
    refine ⟨s, κ, hk, ?_⟩
    rw [hκ, (TorsionUnique.torsSq_unique _ _ _ _ _ _ (k6 p (s₁ hp)) hr (htt p (s₂ hp))).1,
      (TorsionUnique.torsSq_unique _ _ _ _ _ _ (k6' p (s₁ hp)) hr' (htt' p (s₃ hp))).1]

end GlobalTheory.KeyKa.KaHol
end
