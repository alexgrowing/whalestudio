import Mathlib
import Formalism.HermitianCurvature.StatementTBB
import Formalism.HermitianCurvature.StatementU
import Formalism.HermitianCurvature.LetterProductDoubleDegreeCount
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutBPEqDecay
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliEigenSumLinearCombinationStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PolynomialSmulCapelliEigenfunctionSum

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Finset

namespace GlobalTheory

open Finset in
private lemma CV_comp_clm_eq_clm_CV {k r : ℕ} {E E' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup E'] [NormedSpace ℂ E'] (Φ : E →L[ℂ] E') (Y : ℂ) {f : _root_.Formalism.FourierDecayAlt.B.Mat k r → E}
    (hf : _root_.Formalism.FourierDecayAlt.B.CkOn ⊤ (_root_.Formalism.FourierDecayAlt.B.GV k r) f) {g : _root_.Formalism.FourierDecayAlt.B.Mat k r} (hg : g ∈ _root_.Formalism.FourierDecayAlt.B.GV k r) :
    _root_.Formalism.FourierDecayAlt.Q.CV k r Y (fun h => Φ (f h)) g = Φ (_root_.Formalism.FourierDecayAlt.Q.CV k r Y f g) := by
  have hs : _root_.Formalism.FourierDecayAlt.Q.SmoothLev k r 0 Set.univ f := by
    intro g₀ hg₀
    obtain ⟨U, F, hU, hgU, hF, hEq⟩ := hf g₀ hg₀.1.1
    exact ⟨U, F, hU, hgU, hF, fun g hg hg' => hEq g hg hg'.1⟩
  have hg0 : g ∈ _root_.Formalism.FourierDecayAlt.Q.Glev k r 0 := ⟨hg, fun a ha => (Nat.not_lt_zero _ ha).elim⟩
  exact _root_.Formalism.FourierDecayAlt.Q.TPresMain.qminor_clm (i := 0) (D := Set.univ) isOpen_univ id id (_root_.Formalism.FourierDecayAlt.Q.uC k r 0 Y) Φ f hs g ⟨hg0, trivial⟩

open Finset in
private lemma entry_smul_eigenfunction_lemma_6 {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (lam : Fin (2 * r + k + 1) → ℝ) (d : ℕ) (A : ℝ) (ν : Fin (2 * r + k + 1) → ℤ) (i j : Fin (2 * r + k + 1))
    (f : _root_.Formalism.FourierDecayAlt.B.Mat k r → (Wq →L[ℂ] Wp))
    (hgap : ∀ s t, s ≠ t → 2 * (d : ℝ) < |lam s - lam t|) (hν : ∀ s, |ν s| ≤ (d : ℤ))
    (hck : _root_.Formalism.FourierDecayAlt.B.CkOn ⊤ (_root_.Formalism.FourierDecayAlt.B.GV k r) f) (hcc : ∀ m : ℕ, _root_.Formalism.FourierDecayAlt.B.InCC A m f)
    (heig : ∀ Y : ℝ, ∀ g ∈ _root_.Formalism.FourierDecayAlt.B.GV k r, _root_.Formalism.FourierDecayAlt.Q.CV k r (Y : ℂ) f g =
      ((∏ s, (Y + lam s + (ν s : ℝ)) : ℝ) : ℂ) • f g) :
    _root_.GlobalTheory.EigenSumPoly.IsEigenSum (Wp := Wp) (Wq := Wq) lam (d + 1) (A - 1) (fun g => g i j • f g) := by
  obtain ⟨V, W, _, _, _, _, E, E', ι, ev, mul, hGl, hGl', hι, hW, hCk, hinj, hInCC, hrep, hE, hCV, hmul⟩ :=
    _root_.GlobalTheory.capelli_module_model k r Wp Wq (fun s => lam s + ν s) A
  obtain ⟨w, hw⟩ := hrep f ⟨hck, hcc⟩ (fun Y g hg => by rw [heig Y g hg]; simp [add_assoc])
  have hsm : ∀ a : Fin (2 * r + k + 1), _root_.Formalism.FourierDecayAlt.B.CkOn ⊤ (_root_.Formalism.FourierDecayAlt.B.GV k r) (fun g : _root_.Formalism.FourierDecayAlt.B.Mat k r => g i a) :=
    fun a => _root_.PI.UnitaryCorollaryDerivatives.ckOn_of_contDiff (_root_.Formalism.FourierDecayAlt.P.JCx1.contDiff_entry i a)
  have hEH : ∀ (a b c : Fin (2 * r + k + 1)) (g : _root_.Formalism.FourierDecayAlt.B.Mat k r),
      _root_.Formalism.FourierDecayAlt.Q.EH k r a b (fun g : _root_.Formalism.FourierDecayAlt.B.Mat k r => g i c) g = if b = c then g i a else 0 := by
    intro a b c g
    have h := _root_.Formalism.FourierDecayAlt.P.Qx5.eh_linear (Matrix.entryLinearMap ℂ ℂ i c) g a b
    simp only [Matrix.entryLinearMap_apply] at h
    rw [h]
    erw [Matrix.mul_apply]
    by_cases hbc : b = c <;> simp [hbc, Matrix.single_apply]
  set x : Fin (2 * r + k + 1) → Module.End ℂ V := fun a => mul (fun g => g i a) with hx
  have hcomm : ∀ a b c, E a b * x c = x c * E a b + if b = c then x a else 0 := by
    intro a b c
    apply LinearMap.ext
    intro v
    apply hinj
    intro g hg
    have h1 := (hmul _ (hsm c)).2 a b v g hg
    have h2 := (hmul _ (hsm c)).1 ((E a b) v) g hg
    rw [Module.End.mul_apply, LinearMap.add_apply, Module.End.mul_apply, map_add, Pi.add_apply, h1, h2, hEH]
    split_ifs with hbc
    · subst hbc
      have h3 := (hmul _ (hsm a)).1 v g hg
      try simp only at h3
      rw [h3]
    · simp
  set μ : Fin (2 * r + k + 1) → ℂ := fun s => ((lam s + ν s : ℝ) : ℂ) - (((2 * r + k + 1 : ℕ) : ℂ) - 1) / 2 with hμ
  have hinjμ : Function.Injective μ := by
    intro s t hst
    by_contra hne
    have h1 : ((lam s + ν s : ℝ) : ℂ) = ((lam t + ν t : ℝ) : ℂ) := by simpa [hμ] using hst
    have h2 : lam s + ν s = lam t + ν t := by exact_mod_cast h1
    have hs' : |(ν s : ℝ)| ≤ d := by exact_mod_cast hν s
    have ht' : |(ν t : ℝ)| ≤ d := by exact_mod_cast hν t
    have h3 : |lam s - lam t| ≤ 2 * d := by
      rw [abs_le] at hs' ht' ⊢
      constructor <;> linarith
    linarith [hgap s t hne]
  obtain ⟨v, hv, hveig⟩ := _root_.GlobalTheory.qdet_vector_multiplier_shift_plus V W (2 * r + k + 1) E E' ι x μ hGl hGl' hι
    hinjμ (fun u w => by simpa [hμ] using hW u w) hcomm j w
  refine ⟨2 * r + k + 1, fun s => ev (∑ a, x a (ι (v s a))), fun s t => ν t + if t = s then 1 else 0,
    ?_, ?_, ?_, ?_⟩
  · intro s t
    have := hν t
    show |ν t + (if t = s then 1 else 0)| ≤ ((d + 1 : ℕ) : ℤ)
    rw [abs_le] at this ⊢
    split_ifs <;> push_cast <;> constructor <;> omega
  · intro s
    refine ⟨hCk _, fun m => ?_⟩
    have hcong : ∀ g ∈ _root_.Formalism.FourierDecayAlt.B.GV k r, (fun g : _root_.Formalism.FourierDecayAlt.B.Mat k r => ∑ a, g i a • ev (ι (v s a)) g) g =
        ev (∑ a, x a (ι (v s a))) g := by
      intro g hg
      rw [map_sum, Finset.sum_apply]
      refine Finset.sum_congr rfl fun a _ => ?_
      have h3 := (hmul _ (hsm a)).1 (ι (v s a)) g hg
      try simp only at h3
      rw [hx, h3]
    refine (_root_.GlobalTheory.ckOn_inCC_congr_on_group k r _ (A - 1) _ _ hcong).2 m ?_
    have hl := _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.InCC_opsum (A := A - 1) (m := m) (List.finRange (2 * r + k + 1))
      (fun a (g : _root_.Formalism.FourierDecayAlt.B.Mat k r) => g i a • ev (ι (v s a)) g) (fun a _ => by
        have hpd : ∀ (A' : ℝ) (m' : ℕ), ∃ K : ℝ, 0 ≤ K ∧ ∀ (F : _root_.Formalism.FourierDecayAlt.B.Mat k r → Wq →L[ℂ] Wp) (b : ℝ),
            _root_.Formalism.FourierDecayAlt.B.CCle (A' + ((1 : ℕ) : ℝ)) m' F b → _root_.Formalism.FourierDecayAlt.B.CCle A' m' (fun g => g i a • F g) (K * b) :=
          @And.right (∀ F : _root_.Formalism.FourierDecayAlt.B.Mat k r → Wq →L[ℂ] Wp, _root_.Formalism.FourierDecayAlt.B.CkOn ⊤ (_root_.Formalism.FourierDecayAlt.B.GV k r) F →
            _root_.Formalism.FourierDecayAlt.B.CkOn ⊤ (_root_.Formalism.FourierDecayAlt.B.GV k r) fun g => g i a • F g) _
            (_root_.Formalism.FourierDecayAlt.P.CutBP.pd_good_of_poly (Wp := Wp) (Wq := Wq) (k := k) (r := r) (c := fun g => g i a) (_root_.Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra.pd_entry i a))
        obtain ⟨K, -, hK⟩ := hpd (A - 1) m
        obtain ⟨b, hb⟩ := hInCC (v s a) m
        refine ⟨K * b, hK _ b ?_⟩
        rw [show A - 1 + ((1 : ℕ) : ℝ) = A by push_cast; ring]
        exact hb)
    convert hl using 1
    funext g
    exact Fin.sum_univ_def _
  · intro s Y g hg
    rw [← hCV (Y : ℂ) _ g hg, hveig s, map_smul, Pi.smul_apply]
    congr 1
    push_cast
    refine Finset.prod_congr rfl fun t _ => ?_
    simp only [hμ]
    split_ifs <;> push_cast <;> ring
  · intro g hg
    have h3 := (hmul _ (hsm j)).1 (ι w) g hg
    try simp only at h3
    show g i j • f g = _
    rw [← hw g hg, ← h3]
    show ev (x j (ι w)) g = _
    rw [hv, map_sum, Finset.sum_apply]

open Finset in
private lemma isEigenSum_entry_smul {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (lam : Fin (2 * r + k + 1) → ℝ) (d : ℕ) (A : ℝ) (i j : Fin (2 * r + k + 1))
    (F : _root_.Formalism.FourierDecayAlt.B.Mat k r → (Wq →L[ℂ] Wp)) (hgap : ∀ s t, s ≠ t → 2 * (d : ℝ) < |lam s - lam t|)
    (hF : _root_.GlobalTheory.EigenSumPoly.IsEigenSum lam d A F) : _root_.GlobalTheory.EigenSumPoly.IsEigenSum lam (d + 1) (A - 1) (fun g => g i j • F g) := by
  obtain ⟨N₀, Fi, ν, hν, hreg, heig, hsum⟩ := hF
  exact _root_.GlobalTheory.capelli_eigenSum_linearCombination k r Wp Wq lam (d + 1) (A - 1) (Fin N₀) Finset.univ (fun _ => 1)
    (fun l g => g i j • Fi l g) _
    (fun l _ => ⟨d + 1, A - 1, le_rfl, le_rfl, entry_smul_eigenfunction_lemma_6 lam d A (ν l) i j (Fi l) hgap (hν l)
      (hreg l).1 (hreg l).2 (heig l)⟩)
    (fun g hg => by simp [hsum g hg, Finset.smul_sum])

open Finset in
private lemma isEigenSum_star_entry_smul {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (lam : Fin (2 * r + k + 1) → ℝ) (d : ℕ) (A : ℝ) (i j : Fin (2 * r + k + 1))
    (F : _root_.Formalism.FourierDecayAlt.B.Mat k r → (Wq →L[ℂ] Wp)) (hgap : ∀ s t, s ≠ t → 2 * (d : ℝ) < |lam s - lam t|)
    (hF : _root_.GlobalTheory.EigenSumPoly.IsEigenSum lam d A F) : _root_.GlobalTheory.EigenSumPoly.IsEigenSum lam (d + 1) (A - 1) (fun g => star (g i j) • F g) :=
  _root_.GlobalTheory.conj_entry_smul_eigenSum k r Wp Wq lam d A i j F hgap hF

open Finset in
private lemma monomial_smul_eigenSum_lemma_3 {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (lam : Fin (2 * r + k + 1) → ℝ)
    (s : Multiset ((Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) ⊕ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1)))) :
    ∀ (d : ℕ) (A : ℝ) (F : _root_.Formalism.FourierDecayAlt.B.Mat k r → (Wq →L[ℂ] Wp)),
      (∀ s' t, s' ≠ t → 2 * ((d + Multiset.card s : ℕ) : ℝ) < |lam s' - lam t|) → _root_.GlobalTheory.EigenSumPoly.IsEigenSum lam d A F →
      _root_.GlobalTheory.EigenSumPoly.IsEigenSum lam (d + Multiset.card s) (A - Multiset.card s)
        (fun g => (s.map (_root_.GlobalTheory.EigenSumPoly.entryVar g)).prod • F g) := by
  induction s using Multiset.induction_on with
  | empty =>
    intro d A F _ hF
    simpa using hF
  | cons a s ih =>
    intro d A F hgap hF
    have hgap' : ∀ s' t, s' ≠ t → 2 * ((d + Multiset.card s : ℕ) : ℝ) < |lam s' - lam t| := by
      intro s' t hst
      refine lt_of_le_of_lt ?_ (hgap s' t hst)
      simp only [Multiset.card_cons]
      push_cast
      linarith
    have h1 := ih d A F hgap' hF
    have h2 : _root_.GlobalTheory.EigenSumPoly.IsEigenSum lam (d + Multiset.card s + 1) (A - Multiset.card s - 1)
        (fun g => _root_.GlobalTheory.EigenSumPoly.entryVar g a • (s.map (_root_.GlobalTheory.EigenSumPoly.entryVar g)).prod • F g) := by
      rcases a with ⟨i, j⟩ | ⟨i, j⟩
      · exact isEigenSum_entry_smul lam _ _ i j _ hgap' h1
      · exact isEigenSum_star_entry_smul lam _ _ i j _ hgap' h1
    have e1 : d + Multiset.card (a ::ₘ s) = d + Multiset.card s + 1 := by
      simp [Multiset.card_cons, add_assoc]
    have e2 : A - ((Multiset.card (a ::ₘ s) : ℕ) : ℝ) = A - Multiset.card s - 1 := by
      simp only [Multiset.card_cons]
      push_cast
      ring
    rw [e1, e2]
    convert h2 using 2 with g
    rw [Multiset.map_cons, Multiset.prod_cons, mul_smul]

open Finset in
private lemma isEigenSum_poly_smul {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (lam : Fin (2 * r + k + 1) → ℝ) (d e : ℕ) (A : ℝ) (c : _root_.Formalism.FourierDecayAlt.B.Mat k r → ℂ) (hc : _root_.Formalism.FourierDecayAlt.U.IsPolyDeg e c)
    (F : _root_.Formalism.FourierDecayAlt.B.Mat k r → (Wq →L[ℂ] Wp)) (hgap : ∀ s t, s ≠ t → 2 * ((d + e : ℕ) : ℝ) < |lam s - lam t|)
    (hF : _root_.GlobalTheory.EigenSumPoly.IsEigenSum lam d A F) : _root_.GlobalTheory.EigenSumPoly.IsEigenSum lam (d + e) (A - e) (fun g => c g • F g) := by
  classical
  obtain ⟨q, hq, hcq⟩ := hc
  refine _root_.GlobalTheory.capelli_eigenSum_linearCombination k r Wp Wq lam (d + e) (A - e) _ q.support q.coeff
    (fun m g => (m.toMultiset.map (_root_.GlobalTheory.EigenSumPoly.entryVar g)).prod • F g) _ (fun m hm => ?_) (fun g _ => ?_)
  · have hcard : Multiset.card m.toMultiset ≤ e := by
      rw [Finsupp.card_toMultiset]
      exact (MvPolynomial.le_totalDegree hm).trans hq
    refine ⟨d + Multiset.card m.toMultiset, A - Multiset.card m.toMultiset, by omega, ?_,
      monomial_smul_eigenSum_lemma_3 lam m.toMultiset d A F (fun s t hst => lt_of_le_of_lt ?_ (hgap s t hst)) hF⟩
    · have : (Multiset.card m.toMultiset : ℝ) ≤ e := by exact_mod_cast hcard
      linarith
    · have : ((d + Multiset.card m.toMultiset : ℕ) : ℝ) ≤ ((d + e : ℕ) : ℝ) := by
        exact_mod_cast (by omega : d + Multiset.card m.toMultiset ≤ d + e)
      linarith
  · show c g • F g = _
    rw [hcq g, MvPolynomial.eval_eq, Finset.sum_smul]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [mul_smul, Finsupp.toMultiset_map, Finsupp.prod_toMultiset,
      Finsupp.prod_mapDomain_index (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
    rfl

open Finset in

theorem _root_.GlobalTheory.gfPow_smul_comp_polyOp_eigenSum :
    ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Wq' : Type) [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq'] [FiniteDimensional ℂ Wq'] (z z' : Fin (2 * r + k + 1) → ℂ) (lam : Fin (2 * r + k + 1) → ℝ) (A₀ : ℝ) (p₀ dA : ℕ) (f : _root_.Formalism.FourierDecayAlt.B.Mat k r → (Wq →L[ℂ] Wp)) (Aop : _root_.Formalism.FourierDecayAlt.B.Mat k r → (Wq' →L[ℂ] Wq)), (∀ s t, s ≠ t → 2 * (((2 * r + 2) * p₀ + dA : ℕ) : ℝ) < |lam s - lam t|) → (_root_.Formalism.FourierDecayAlt.B.CkOn ⊤ (_root_.Formalism.FourierDecayAlt.B.GV k r) (f) ∧ ∀ m : ℕ, _root_.Formalism.FourierDecayAlt.B.InCC (A₀) m (f)) → (∀ Y : ℝ, ∀ g ∈ _root_.Formalism.FourierDecayAlt.B.GV k r, _root_.Formalism.FourierDecayAlt.Q.CV k r (Y : ℂ) (f) g = ((∏ s, (Y + lam s) : ℝ) : ℂ) • (f) g) → (∃ (n₁ : ℕ) (c : Fin n₁ → _root_.Formalism.FourierDecayAlt.B.Mat k r → ℂ) (L : Fin n₁ → (Wq' →L[ℂ] Wq)), (∀ i, _root_.Formalism.FourierDecayAlt.U.IsPolyDeg dA (c i)) ∧ ∀ g, Aop g = ∑ i, c i g • L i) → (∃ (N₀ : ℕ) (Fi : Fin N₀ → _root_.Formalism.FourierDecayAlt.B.Mat k r → (Wq' →L[ℂ] Wp)) (ν : Fin N₀ → Fin (2 * r + k + 1) → ℤ), (∀ i s, |ν i s| ≤ (((2 * r + 2) * p₀ + dA : ℕ) : ℤ)) ∧ (∀ i, (_root_.Formalism.FourierDecayAlt.B.CkOn ⊤ (_root_.Formalism.FourierDecayAlt.B.GV k r) (Fi i) ∧ ∀ m : ℕ, _root_.Formalism.FourierDecayAlt.B.InCC (A₀ - (((2 * r + 2) * p₀ + dA : ℕ) : ℝ)) m (Fi i))) ∧ (∀ i, (∀ Y : ℝ, ∀ g ∈ _root_.Formalism.FourierDecayAlt.B.GV k r, _root_.Formalism.FourierDecayAlt.Q.CV k r (Y : ℂ) (Fi i) g = ((∏ s, (Y + lam s + (ν i s : ℝ)) : ℝ) : ℂ) • (Fi i) g)) ∧ ∀ g ∈ _root_.Formalism.FourierDecayAlt.B.GV k r, (fun g => ((_root_.Formalism.QuantumDeterminants.Gf k r z z' g ^ p₀ : ℝ) : ℂ) • (f g).comp (Aop g)) g = ∑ i, Fi i g) := by
  intro k r Wp Wq _ _ _ _ _ _ Wq' _ _ _ z z' lam A₀ p₀ dA f Aop hgap hf heig hA
  obtain ⟨hck, hcc⟩ := hf
  obtain ⟨n₁, c, L, hc, hAop⟩ := hA
  set e := (2 * r + 2) * p₀ + dA with he
  have hpiece : ∀ i, _root_.GlobalTheory.EigenSumPoly.IsEigenSum (Wp := Wp) (Wq := Wq') lam e (A₀ - e)
      (fun g => (((_root_.Formalism.QuantumDeterminants.Gf k r z z' g ^ p₀ : ℝ) : ℂ) * c i g) • (f g).comp (L i)) := by
    intro i
    let Φ : (Wq →L[ℂ] Wp) →L[ℂ] (Wq' →L[ℂ] Wp) := (ContinuousLinearMap.compL ℂ Wq' Wq Wp).flip (L i)
    have hΦ : ∀ h, Φ h = h.comp (L i) := fun h => rfl
    have h0 : _root_.GlobalTheory.EigenSumPoly.IsEigenSum (Wp := Wp) (Wq := Wq') lam 0 A₀ (fun g => (f g).comp (L i)) := by
      refine ⟨1, fun _ g => (f g).comp (L i), fun _ _ => 0, fun _ _ => by simp, fun _ => ⟨?_, fun m => ?_⟩,
        fun _ Y g hg => ?_, fun g _ => by simp⟩
      · exact _root_.Formalism.FourierDecayAlt.P.CutBPEq.ckOn_clm Φ hck
      · obtain ⟨b, hb⟩ := hcc m
        exact ⟨_, _root_.Formalism.FourierDecayAlt.P.CutBPEq.ccle_clm Φ hb⟩
      · have h1 := CV_comp_clm_eq_clm_CV Φ (Y : ℂ) hck hg
        simp only [hΦ] at h1
        rw [h1, heig Y g hg]
        simp
    have hG := _root_.Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra.pd_prod (Finset.range p₀) (P := fun _ (g : _root_.Formalism.FourierDecayAlt.B.Mat k r) => ((_root_.Formalism.QuantumDeterminants.Gf k r z z' g : ℝ) : ℂ))
      (fun _ _ => _root_.Formalism.FourierDecayAlt.P.AdmissibleLieWords.gf_pd k r z z')
    have hfun : (fun g : _root_.Formalism.FourierDecayAlt.B.Mat k r => ((_root_.Formalism.QuantumDeterminants.Gf k r z z' g ^ p₀ : ℝ) : ℂ) * c i g) =
        fun g => (∏ _ ∈ Finset.range p₀, ((_root_.Formalism.QuantumDeterminants.Gf k r z z' g : ℝ) : ℂ)) * c i g := by
      funext g
      simp
    have hpoly : _root_.Formalism.FourierDecayAlt.U.IsPolyDeg e (fun g : _root_.Formalism.FourierDecayAlt.B.Mat k r => ((_root_.Formalism.QuantumDeterminants.Gf k r z z' g ^ p₀ : ℝ) : ℂ) * c i g) := by
      rw [hfun, show e = (Finset.range p₀).card * (2 * r + 2) + dA by rw [he, Finset.card_range]; ring]
      exact _root_.Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra.pd_mul hG (hc i)
    have h2 := isEigenSum_poly_smul lam 0 e A₀ _ hpoly _ (fun s t h => by rw [zero_add]; exact hgap s t h) h0
    rw [zero_add] at h2
    exact h2
  exact _root_.GlobalTheory.capelli_eigenSum_linearCombination k r Wp Wq' lam e (A₀ - e) (Fin n₁) Finset.univ (fun _ => 1)
    (fun i g => (((_root_.Formalism.QuantumDeterminants.Gf k r z z' g ^ p₀ : ℝ) : ℂ) * c i g) • (f g).comp (L i)) _
    (fun i _ => ⟨e, A₀ - e, le_rfl, le_rfl, hpiece i⟩)
    (fun g _ => by
      simp [hAop, ContinuousLinearMap.comp_finset_sum, ContinuousLinearMap.comp_smul, Finset.smul_sum, smul_smul])

end GlobalTheory
