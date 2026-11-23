import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.LevelChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntAfIntCast
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntDvdOfEqNatMulIntegralAdeleAwayFromP

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private theorem herm_add_right {g : ℕ} (M : Matrix (Fin g) (Fin g) ℂ) (x a b : Fin g → ℂ) :
    hermForm M x (a + b) = hermForm M x a + hermForm M x b := by
  simp [hermForm, Matrix.mulVec_add, dotProduct_add]

private theorem herm_add_left {g : ℕ} (M : Matrix (Fin g) (Fin g) ℂ) (a b y : Fin g → ℂ) :
    hermForm M (a + b) y = hermForm M a y + hermForm M b y := by
  simp [hermForm, add_dotProduct]

private theorem herm_smul_right {g : ℕ} (M : Matrix (Fin g) (Fin g) ℂ) (c : ℂ) (x a : Fin g → ℂ) :
    hermForm M x (c • a) = star c * hermForm M x a := by
  simp [hermForm, star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

private theorem herm_smul_left {g : ℕ} (M : Matrix (Fin g) (Fin g) ℂ) (c : ℂ) (a y : Fin g → ℂ) :
    hermForm M (c • a) y = c * hermForm M a y := by
  simp only [hermForm, smul_dotProduct, smul_eq_mul]

private theorem herm_sub_smul {g : ℕ} (H₁ H₂ : Matrix (Fin g) (Fin g) ℂ) (t : ℂ) (x y : Fin g → ℂ) :
    hermForm (H₁ - t • H₂) x y = hermForm H₁ x y - t * hermForm H₂ x y := by
  simp [hermForm, Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub, dotProduct_smul]

private theorem real_smul_eq {g : ℕ} (c : ℝ) (a : Fin g → ℂ) : c • a = (c : ℂ) • a := by
  ext i; simp

private theorem herm_im_zero {g : ℕ} (M : Matrix (Fin g) (Fin g) ℂ) (s : Set (Fin g → ℂ))
    (hs : Submodule.span ℝ s = ⊤) (h : ∀ x ∈ s, ∀ y ∈ s, (hermForm M x y).im = 0) (z w : Fin g → ℂ) :
    (hermForm M z w).im = 0 := by
  have key : ∀ w ∈ s, ∀ z, (hermForm M z w).im = 0 := by
    intro w hw z
    have hz : z ∈ Submodule.span ℝ s := by rw [hs]; trivial
    induction hz using Submodule.span_induction with
    | mem x hx => exact h x hx w hw
    | zero => simp [hermForm]
    | add a b _ _ ha hb => rw [herm_add_left]; simp [ha, hb]
    | smul c a _ ha => rw [real_smul_eq, herm_smul_left]; simp [ha]
  have hw : w ∈ Submodule.span ℝ s := by rw [hs]; trivial
  induction hw using Submodule.span_induction with
  | mem y hy => exact key y hy z
  | zero => simp [hermForm]
  | add a b _ _ ha hb => rw [herm_add_right]; simp [ha, hb]
  | smul c a _ ha => rw [real_smul_eq, herm_smul_right]; simp [ha]

private theorem bil_dvd {M : Type} [AddCommGroup M] (Bf : LinearMap.BilinForm ℤ M) (n : ℕ) (x y e e' : M) :
    (n : ℤ) ∣ Bf (x + n • e) (y + n • e') - Bf x y := by
  refine ⟨Bf x e' + Bf e y + n * Bf e e', ?_⟩
  simp [map_add, map_nsmul, LinearMap.add_apply, nsmul_eq_mul]
  ring

private theorem form_step {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) (h : G.GAf) (n : ℕ)
    {a a' b b' : D.La} {w w' : AfP p ⊗[ℚ] VQ D} (hw : w ∈ LaHat D) (hw' : w' ∈ LaHat D)
    (e : L.actG h (inAf D a) = inAf D b + n • w) (e' : L.actG h (inAf D a') = inAf D b' + n • w') :
    ∃ i : AfP p, IsIntAf i ∧ ((D.EF b b' : ℤ) : AfP p) =
      ((uSimR (AfP p) h : (AfP p)ˣ) : AfP p) * ((D.EF a a' : ℤ) : AfP p) + (n : AfP p) * i := by
  have h1 := MultScale.EFA_actG L h (inAf D a) (inAf D a')
  rw [e, e', MultScale.EFA_inAf] at h1
  simp only [map_add, map_nsmul, LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul,
    MultScale.EFA_inAf] at h1
  have hn : IsIntAf (n : AfP p) := by
    have := MultScale.isIntAf_intCast (p := p) (n : ℤ)
    simpa using this
  refine ⟨-(MultScale.EFA D (inAf D b) w' + MultScale.EFA D w (inAf D b') +
    (n : AfP p) * MultScale.EFA D w w'), ?_, ?_⟩
  · exact MultScale.isIntAf_neg (MultScale.isIntAf_add (MultScale.isIntAf_add
      (MultScale.isIntAf_EFA D (MultScale.inAf_mem D b) hw')
      (MultScale.isIntAf_EFA D hw (MultScale.inAf_mem D b')))
      (MultScale.isIntAf_mul hn (MultScale.isIntAf_EFA D hw hw')))
  · linear_combination h1

private theorem cross_dvd {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) (h : G.GAf)
    {D' D'' : PLat D.O D.inv} (inc : D'.La →ₗ[D.O] D''.La) {f : ℕ → D.La →+ D'.La} {nu : ℕ → ℤ}
    {f'' : ℕ → D.La →+ D''.La} {nu'' : ℕ → ℤ} (hf : IsWit D' f nu) (hf'' : IsWit D'' f'' nu'')
    (hyp : ∀ n : ℕ, 0 < n → n.Coprime p → ∀ a b : D.La,
      (∃ u, inc (f n a) = f'' n b + n • u) ↔ ∃ w ∈ LaHat D, L.actG h (inAf D a) = inAf D b + n • w)
    (u₁ u₂ u₃ u₄ : D'.La) (n : ℕ) (hn : 0 < n) (hc : n.Coprime p) :
    (n : ℤ) ∣ D''.EF (inc u₁) (inc u₂) * D'.EF u₃ u₄ - D''.EF (inc u₃) (inc u₄) * D'.EF u₁ u₂ := by
  unfold IsWit at hf hf''
  have hX : ∀ x x' : D'.La, ∃ b b' a a' : D.La,
      (D''.EF (inc x) (inc x') ≡ nu'' n * (2 * D.EF b b') [ZMOD n]) ∧
      (D'.EF x x' ≡ nu n * (2 * D.EF a a') [ZMOD n]) ∧
      ∃ i : AfP p, IsIntAf i ∧ ((D.EF b b' : ℤ) : AfP p) =
        ((uSimR (AfP p) h : (AfP p)ˣ) : AfP p) * ((D.EF a a' : ℤ) : AfP p) + (n : AfP p) * i := by
    intro x x'
    obtain ⟨a, e, rfl⟩ := (hf.2 n hn hc).2.2.2.1 x
    obtain ⟨a', e', rfl⟩ := (hf.2 n hn hc).2.2.2.1 x'
    obtain ⟨b, E, hb⟩ := (hf''.2 n hn hc).2.2.2.1 (inc (f n a))
    obtain ⟨b', E', hb'⟩ := (hf''.2 n hn hc).2.2.2.1 (inc (f n a'))
    obtain ⟨w, hw, hwe⟩ := (hyp n hn hc a b).1 ⟨E, hb⟩
    obtain ⟨w', hw', hwe'⟩ := (hyp n hn hc a' b').1 ⟨E', hb'⟩
    refine ⟨b, b', a, a', ?_, ?_, form_step L h n hw hw' hwe hwe'⟩
    · have h1 : inc (f n a + n • e) = f'' n b + n • (E + inc e) := by
        rw [map_add, map_nsmul, hb, smul_add, add_assoc]
      have h2 : inc (f n a' + n • e') = f'' n b' + n • (E' + inc e') := by
        rw [map_add, map_nsmul, hb', smul_add, add_assoc]
      rw [h1, h2]
      exact (Int.modEq_iff_dvd.mpr (bil_dvd D''.EF n _ _ _ _)).symm.trans
        (Int.modEq_iff_dvd.mpr ((hf''.2 n hn hc).2.2.2.2 b b')).symm
    · exact (Int.modEq_iff_dvd.mpr (bil_dvd D'.EF n _ _ _ _)).symm.trans
        (Int.modEq_iff_dvd.mpr ((hf.2 n hn hc).2.2.2.2 a a')).symm
  obtain ⟨b1, b2, a1, a2, hX1, hY1, i12, hi12, he12⟩ := hX u₁ u₂
  obtain ⟨b3, b4, a3, a4, hX3, hY3, i34, hi34, he34⟩ := hX u₃ u₄
  have hZ : (n : ℤ) ∣ D.EF b1 b2 * D.EF a3 a4 - D.EF b3 b4 * D.EF a1 a2 := by
    apply IntDvd.int_dvd_of_eq_mul_isIntAf p n hn hc _
      (i12 * ((D.EF a3 a4 : ℤ) : AfP p) - i34 * ((D.EF a1 a2 : ℤ) : AfP p))
    · rw [sub_eq_add_neg]
      exact MultScale.isIntAf_add (MultScale.isIntAf_mul hi12 (MultScale.isIntAf_intCast _))
        (MultScale.isIntAf_neg (MultScale.isIntAf_mul hi34 (MultScale.isIntAf_intCast _)))
    · rw [map_intCast]
      push_cast
      linear_combination ((D.EF a3 a4 : ℤ) : AfP p) * he12 - ((D.EF a1 a2 : ℤ) : AfP p) * he34
  have h0 : nu'' n * (2 * D.EF b1 b2) * (nu n * (2 * D.EF a3 a4)) -
      nu'' n * (2 * D.EF b3 b4) * (nu n * (2 * D.EF a1 a2)) ≡ 0 [ZMOD n] := by
    apply Int.modEq_zero_iff_dvd.mpr
    obtain ⟨k, hk⟩ := hZ
    exact ⟨4 * nu'' n * nu n * k, by linear_combination (4 * nu'' n * nu n) * hk⟩
  exact Int.modEq_zero_iff_dvd.mp (((hX1.mul hY3).sub (hX3.mul hY1)).trans h0)

private theorem cross {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) (h : G.GAf)
    {D' D'' : PLat D.O D.inv} (inc : D'.La →ₗ[D.O] D''.La) {f : ℕ → D.La →+ D'.La} {nu : ℕ → ℤ}
    {f'' : ℕ → D.La →+ D''.La} {nu'' : ℕ → ℤ} (hf : IsWit D' f nu) (hf'' : IsWit D'' f'' nu'')
    (hyp : ∀ n : ℕ, 0 < n → n.Coprime p → ∀ a b : D.La,
      (∃ u, inc (f n a) = f'' n b + n • u) ↔ ∃ w ∈ LaHat D, L.actG h (inAf D a) = inAf D b + n • w)
    (u₁ u₂ u₃ u₄ : D'.La) :
    D''.EF (inc u₁) (inc u₂) * D'.EF u₃ u₄ = D''.EF (inc u₃) (inc u₄) * D'.EF u₁ u₂ := by
  set d := D''.EF (inc u₁) (inc u₂) * D'.EF u₃ u₄ - D''.EF (inc u₃) (inc u₄) * D'.EF u₁ u₂ with hd
  suffices hz : d = 0 by exact sub_eq_zero.mp hz
  have hn : 0 < p * d.natAbs + 1 := Nat.succ_pos _
  have hc : (p * d.natAbs + 1).Coprime p :=
    ((Nat.coprime_mul_left_add_right p 1 d.natAbs).mpr (Nat.coprime_one_right p)).symm
  have hdvd := cross_dvd L h inc hf hf'' hyp u₁ u₂ u₃ u₄ _ hn hc
  apply Int.eq_zero_of_abs_lt_dvd hdvd
  have hp : (2 : ℤ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).two_le
  rw [Int.abs_eq_natAbs]
  push_cast
  nlinarith [Int.natCast_nonneg d.natAbs]

theorem UpperTheory.Gal.W2.isogForm_of :
    UpperTheory.Gal.W2.RdForm → UpperTheory.Gal.W2.IsogForm := by
  intro _ p _ D G L h ρ D' D'' P P'' inc hP hP'' hPinc f nu f'' nu'' hf hf'' hyp
  by_cases hall : ∀ u u' : D'.La, D'.EF u u' = 0
  · refine ⟨1, one_pos, fun u u' => ?_⟩
    have h0 : ∀ x : D'.La, x = 0 := fun x => D'.nondeg x (hall x)
    rw [h0 u]
    simp
  push_neg at hall
  obtain ⟨u₃, u₄, hne⟩ := hall
  have hrel : ∀ u u' : D'.La, ((D''.EF (inc u) (inc u') : ℤ) : ℚ) =
      ((D''.EF (inc u₃) (inc u₄) : ℚ) / (D'.EF u₃ u₄ : ℚ)) * (D'.EF u u' : ℚ) := by
    intro u u'
    have hcq : ((D'.EF u₃ u₄ : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hne
    rw [div_mul_eq_mul_div, eq_div_iff hcq]
    exact_mod_cast cross L h inc hf hf'' hyp u u' u₃ u₄
  refine ⟨(D''.EF (inc u₃) (inc u₄) : ℚ) / (D'.EF u₃ u₄ : ℚ), ?_, hrel⟩
  unfold PELU.IsPeriod at hP hP''
  obtain ⟨-, hPinj, -, hspan, H1, -, hpos1, him1⟩ := hP
  obtain ⟨-, -, -, -, H2, -, hpos2, him2⟩ := hP''
  set q : ℚ := (D''.EF (inc u₃) (inc u₄) : ℚ) / (D'.EF u₃ u₄ : ℚ) with hq
  have hzero : ∀ z w, (hermForm (H2 - ((q : ℝ) : ℂ) • H1) z w).im = 0 := by
    apply herm_im_zero _ (Set.range P) hspan
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    rw [herm_sub_smul, Complex.sub_im, Complex.im_ofReal_mul, him1, ← hPinc x, ← hPinc y, him2]
    have hr : ((D''.EF (inc x) (inc y) : ℤ) : ℝ) = (q : ℝ) * ((D'.EF x y : ℤ) : ℝ) := by
      have := congrArg (fun t : ℚ => (t : ℝ)) (hrel x y)
      simpa [hq] using this
    rw [hr]
    ring
  have hM : ∀ z w, hermForm (H2 - ((q : ℝ) : ℂ) • H1) z w = 0 := by
    intro z w
    apply Complex.ext
    · have := hzero (Complex.I • z) w
      rw [herm_smul_left] at this
      simpa using this
    · simpa using hzero z w
  have hu3 : P u₃ ≠ 0 := by
    intro h0
    have hu : u₃ = 0 := hPinj (by rw [h0, map_zero])
    apply hne
    rw [hu]
    simp
  have e := hM (P u₃) (P u₃)
  rw [herm_sub_smul, sub_eq_zero] at e
  have p1 := hpos1 _ hu3
  have p2 := hpos2 _ hu3
  rw [e, Complex.re_ofReal_mul] at p2
  have hpos : (0 : ℝ) < (q : ℝ) := lt_of_not_ge (fun hle => by nlinarith)
  exact Rat.cast_pos.mp hpos
