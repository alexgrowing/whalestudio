import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowMinor
import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StandardBaseFlagComplementIntegralLatticeStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DefiniteLatticeDiscriminantModuleCardDetSqStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameTermCountSublatticeBoundStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsGramRepresentativeSizeLeHHSqStatement
open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LoopC.TermsOver

private theorem upperTriangular_mul_and_diag {R : Type} [CommRing R] {n : ℕ} (B B' : Matrix (Fin n) (Fin n) R)
    (h0 : ∀ a b, b < a → B a b = 0) (h0' : ∀ a b, b < a → B' a b = 0) :
    (∀ a b, b < a → (B * B') a b = 0) ∧ ∀ a, (B * B') a a = B a a * B' a a := by
  refine ⟨fun a b hab => ?_, fun a => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    rcases lt_or_ge k a with hk | hk
    · rw [h0 a k hk, zero_mul]
    · rw [h0' k b (lt_of_lt_of_le hab hk), mul_zero]
  · rw [Matrix.mul_apply, Finset.sum_eq_single a]
    · intro k _ hka
      rcases lt_or_gt_of_ne hka with hk | hk
      · rw [h0 a k hk, zero_mul]
      · rw [h0' k a hk, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ a) h

theorem upper_inv {R : Type} [CommRing R] {n : ℕ} (B : Matrix (Fin n) (Fin n) R)
    (h0 : ∀ a b, b < a → B a b = 0) (h1 : ∀ a, B a a = 1) :
    ∃ B' : Matrix (Fin n) (Fin n) R, (∀ a b, b < a → B' a b = 0) ∧ (∀ a, B' a a = 1) ∧ B * B' = 1 := by
  have hBT : B.BlockTriangular id := fun a b hab => h0 a b hab
  have hdet : B.det = 1 := by
    rw [Matrix.det_of_isUpperTriangular hBT]
    simp [h1]
  have hu : IsUnit B.det := by
    rw [hdet]
    exact isUnit_one
  have := Matrix.invertibleOfIsUnitDet B hu
  have hinv : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv B hu
  have hT' : (B⁻¹).BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular hBT
  have h0' : ∀ a b, b < a → B⁻¹ a b = 0 := fun a b hab => hT' hab
  refine ⟨B⁻¹, h0', fun a => ?_, hinv⟩
  have := (upperTriangular_mul_and_diag B B⁻¹ h0 h0').2 a
  rw [hinv, h1, one_mul, Matrix.one_apply_eq] at this
  exact this.symm

theorem upper_mul {R : Type} [CommRing R] {n : ℕ} (B B' : Matrix (Fin n) (Fin n) R)
    (h0 : ∀ a b, b < a → B a b = 0) (h1 : ∀ a, B a a = 1)
    (h0' : ∀ a b, b < a → B' a b = 0) (h1' : ∀ a, B' a a = 1) :
    (∀ a b, b < a → (B * B') a b = 0) ∧ (∀ a, (B * B') a a = 1) := by
  obtain ⟨hz, hd⟩ := upperTriangular_mul_and_diag B B' h0 h0'
  exact ⟨hz, fun a => by rw [hd, h1, h1', one_mul]⟩

section ZE
variable {E : Type} [Field E] {n : ℕ}

theorem map_mul' (A B : Matrix (Fin n) (Fin n) (𝓞 E)) :
    (A * B).map (fun x => (x : E)) = A.map (fun x => (x : E)) * B.map (fun x => (x : E)) := by
  exact Matrix.map_mul (f := algebraMap (𝓞 E) E)

theorem map_one' : (1 : Matrix (Fin n) (Fin n) (𝓞 E)).map (fun x => (x : E)) = 1 := by
  exact Matrix.map_one _ (by simp) (by simp)

theorem zequiv_trans {Z Z₁ Z₂ : Matrix (Fin n) (Fin n) E} (h : ZEquiv Z Z₁) (h' : ZEquiv Z₁ Z₂) :
    ZEquiv Z Z₂ := by
  obtain ⟨A, B, hA0, hA1, hB0, hB1, rfl⟩ := h
  obtain ⟨A', B', hA0', hA1', hB0', hB1', rfl⟩ := h'

  have hlow := upper_mul Aᵀ A'ᵀ (fun a b hab => hA0 b a hab) (fun a => hA1 a)
    (fun a b hab => hA0' b a hab) (fun a => hA1' a)
  rw [← Matrix.transpose_mul] at hlow
  obtain ⟨hup0, hup1⟩ := upper_mul B B' hB0 hB1 hB0' hB1'
  refine ⟨A' * A, B * B', fun a b hab => hlow.1 b a hab, fun a => hlow.2 a, hup0, hup1, ?_⟩
  rw [TermsOver.map_mul', TermsOver.map_mul']
  simp only [Matrix.mul_assoc]

theorem zequiv_symm {Z Z₁ : Matrix (Fin n) (Fin n) E} (h : ZEquiv Z Z₁) : ZEquiv Z₁ Z := by
  obtain ⟨A, B, hA0, hA1, hB0, hB1, rfl⟩ := h
  obtain ⟨B', hB0', hB1', hBB'⟩ := upper_inv B hB0 hB1
  obtain ⟨C, hC0, hC1, hAC⟩ := upper_inv Aᵀ (fun a b hab => hA0 b a hab) (fun a => hA1 a)
  have hCA : Cᵀ * A = 1 := by
    rw [← Matrix.transpose_transpose A, ← Matrix.transpose_mul, hAC, Matrix.transpose_one]
  have e1 : Cᵀ.map (fun x : 𝓞 E => (x : E)) * A.map (fun x => (x : E)) = 1 := by
    rw [← TermsOver.map_mul', hCA, TermsOver.map_one']
  have e2 : B.map (fun x : 𝓞 E => (x : E)) * B'.map (fun x => (x : E)) = 1 := by
    rw [← TermsOver.map_mul', hBB', TermsOver.map_one']
  refine ⟨Cᵀ, B', fun a b hab => hC0 b a hab, fun a => hC1 a, hB0', hB1', ?_⟩
  calc Z = (Cᵀ.map (fun x : 𝓞 E => (x : E)) * A.map (fun x => (x : E))) * Z *
        (B.map (fun x : 𝓞 E => (x : E)) * B'.map (fun x => (x : E))) := by
        rw [e1, e2, Matrix.one_mul, Matrix.mul_one]
    _ = _ := by simp only [Matrix.mul_assoc]

end ZE

theorem frSet_congr (D : D7) (Λ : LatV D) {T : D.host.E} (F : Fg D T) (T' : D.host.E) {Z Z₁ : GramM D}
    (h : ZEquiv Z Z₁) (P : LatW D) : FrSet D Λ F T' Z P = FrSet D Λ F T' Z₁ P := by
  ext F'
  simp only [FrSet, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, zequiv_trans h2 h, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, zequiv_trans h2 (zequiv_symm h), h3⟩

theorem one_le_b (s : Scale) : 1 ≤ s.b := by
  show 1 ≤ Real.exp (s.x ^ s.eps)
  exact Real.one_le_exp (Real.rpow_nonneg (le_of_lt (lt_trans zero_lt_one s.one_lt_alt)) _)

theorem one_le_sizeZ (D : D7) (b C : ℝ) (Z : GramM D) : 1 ≤ sizeZ D b C Z := by
  unfold sizeZ
  exact Finset.prod_induction _ (fun x => 1 ≤ x) (fun a b ha hb => one_le_mul_of_one_le_of_one_le ha hb) le_rfl
    (fun τ _ => Finset.prod_induction _ (fun x => 1 ≤ x)
      (fun a b ha hb => one_le_mul_of_one_le_of_one_le ha hb) le_rfl (fun l _ => le_max_left _ _))

theorem NT_sq_le (D : D7) (u : D.what₂.Word) (b C CT : ℝ) (hb : 1 ≤ b) (hC1 : 1 ≤ C) (hC : 2 * |CT| ≤ C)
    (hT : Tr D u ≤ b ^ (CT * D.R.m)) (Z : GramM D) : NT D u ^ 2 ≤ HHZ D b C Z := by
  have hb0 : (0 : ℝ) ≤ b := le_trans zero_le_one hb
  have hT0 : (0 : ℝ) ≤ Tr D u := by
    show (0 : ℝ) ≤ ((D.mem u).A.T : ℝ)
    positivity
  have hC0 : (0 : ℝ) ≤ C := le_trans zero_le_one hC1
  have hm0 : (0 : ℝ) ≤ (D.R.m : ℝ) := Nat.cast_nonneg _
  have hf0 : (0 : ℝ) ≤ (D.R.f : ℝ) := Nat.cast_nonneg _
  have hm3 : (D.R.m : ℝ) ≤ (D.R.m : ℝ) ^ 3 := by
    rcases Nat.eq_zero_or_pos D.R.m with h | h
    · simp [h]
    · have h1 : (1 : ℝ) ≤ D.R.m := by exact_mod_cast h
      calc (D.R.m : ℝ) = D.R.m * 1 := by ring
        _ ≤ D.R.m * (D.R.m : ℝ) ^ 2 := mul_le_mul_of_nonneg_left (one_le_pow₀ h1) hm0
        _ = (D.R.m : ℝ) ^ 3 := by ring

  have hexp : CT * D.R.m * D.R.f * 2 ≤ C * (D.R.m : ℝ) ^ 2 * D.R.f * (C * D.R.m) := by
    have hCT : 2 * CT ≤ C := le_trans (by linarith [le_abs_self CT]) hC
    have hmf : (0 : ℝ) ≤ D.R.m * D.R.f := mul_nonneg hm0 hf0
    calc CT * D.R.m * D.R.f * 2 = (2 * CT) * (D.R.m * D.R.f) := by ring
      _ ≤ C * (D.R.m * D.R.f) := mul_le_mul_of_nonneg_right hCT hmf
      _ ≤ (C * C) * ((D.R.m : ℝ) ^ 3 * D.R.f) :=
          mul_le_mul (le_mul_of_one_le_right hC0 hC1) (mul_le_mul_of_nonneg_right hm3 hf0) hmf
            (mul_nonneg hC0 hC0)
      _ = C * (D.R.m : ℝ) ^ 2 * D.R.f * (C * D.R.m) := by ring
  have hNT : NT D u ^ 2 ≤ ((b ^ (CT * D.R.m)) ^ D.R.f) ^ 2 :=
    pow_le_pow_left₀ (by show (0 : ℝ) ≤ ((D.mem u).A.T : ℝ) ^ D.R.f; positivity)
      (pow_le_pow_left₀ hT0 hT _) 2
  have hpow : ((b ^ (CT * D.R.m)) ^ D.R.f) ^ 2 = b ^ (CT * D.R.m * D.R.f * 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hb0, ← Real.rpow_mul hb0]
    norm_num
  have hsz : 1 ≤ sizeZ D b C Z ^ 4 := one_le_pow₀ (one_le_sizeZ D b C Z)
  calc NT D u ^ 2 ≤ b ^ (CT * D.R.m * D.R.f * 2) := hpow ▸ hNT
    _ ≤ b ^ (C * (D.R.m : ℝ) ^ 2 * D.R.f * (C * D.R.m)) := Real.rpow_le_rpow_of_exponent_le hb hexp
    _ = (b ^ (C * (D.R.m : ℝ) ^ 2 * D.R.f)) ^ (C * (D.R.m : ℝ)) := Real.rpow_mul hb0 _ _
    _ ≤ HHZ D b C Z := le_mul_of_one_le_right (Real.rpow_nonneg (Real.rpow_nonneg hb0 _) _) hsz

theorem subOK_of (D : D7) (L P : LatW D) (hL : L.FG) (hpos : IsPosDef (D.sp.X 0).hT)
    (hint : Formalism.HermitianLatticesTheory.IsIntegralLat (D.sp.X 0).hT L) (hP : P ≤ L) (s : ℕ) (hr : rkW D P = D.R.k - s)
    (De : ℝ) (hd : detW D P ≤ De) : SubOK D L P s De := by
  have hsatL : sat D L P ≤ L := inf_le_left
  have hPsat : P ≤ sat D L P := le_inf hP (fun x hx => Submodule.subset_span hx)

  have hfg : (sat D L P).FG := by
    have := isNoetherian_of_fg_of_noetherian L hL
    have h1 : ((sat D L P).comap L.subtype).FG := IsNoetherian.noetherian _
    have h2 := h1.map L.subtype
    rwa [Submodule.map_comap_subtype, inf_eq_right.2 hsatL] at h2
  have hspan : Submodule.span D.host.E (sat D L P : Set (D.sp.X 0).V) =
      Submodule.span D.host.E (P : Set (D.sp.X 0).V) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      intro x hx
      exact hx.2
    · exact Submodule.span_mono hPsat
  have hrk : rkW D P = rkW D (sat D L P) := by
    unfold rkW
    rw [hspan]
  have hintS : Formalism.HermitianLatticesTheory.IsIntegralLat (D.sp.X 0).hT (sat D L P) :=
    fun x hx y hy => hint x (hsatL hx) y (hsatL hy)
  obtain ⟨hd1, hd2, hsub⟩ := GlobalTheory.T.definiteLattice_discriminantModule_card_det_sq D (sat D L P) hfg hpos hintS
  obtain ⟨hi1, hdet⟩ := hsub P hPsat hrk
  have hdS0 : 0 ≤ detW D (sat D L P) := Real.sqrt_nonneg _
  have hdS1 : 1 ≤ detW D (sat D L P) := by
    have : (1 : ℝ) ≤ detW D (sat D L P) ^ 2 := by
      rw [← hd2]
      exact_mod_cast hd1
    nlinarith
  refine ⟨hP, hr, hi1, ?_, hd⟩
  calc (idxW D (sat D L P) P : ℝ) ≤ detW D (sat D L P) * idxW D (sat D L P) P :=
        le_mul_of_one_le_left (Nat.cast_nonneg _) hdS1
    _ = detW D P := hdet.symm
    _ ≤ De := hd

theorem frB_le (D : D7) (s : ℕ) (N De Q Hh : ℝ) (hN0 : 0 ≤ N) (hDe : 1 ≤ De) (hQ0 : 0 ≤ Q) (hH : 1 ≤ Hh)
    (hN : N ^ 2 ≤ Hh) (hD : De ≤ Hh ^ 3) (hQ : Q ≤ Hh ^ 2) :
    frB D s N De Q ≤ N ^ (2 * D.R.rS) * De ^ D.R.rS * 9 ^ (s * D.R.f) *
      Hh ^ (9 * s + 9 * s * D.R.rS + 16 * D.R.rS ^ 2) := by
  have hH0 : 0 ≤ Hh := le_trans zero_le_one hH
  have hDe0 : 0 ≤ De := le_trans zero_le_one hDe

  have h9 : De ^ 2 * N ^ 2 * Q ≤ Hh ^ 9 := by
    have hD2 : De ^ 2 ≤ Hh ^ 6 := by
      calc De ^ 2 ≤ (Hh ^ 3) ^ 2 := pow_le_pow_left₀ hDe0 hD 2
        _ = Hh ^ 6 := by ring
    calc De ^ 2 * N ^ 2 * Q ≤ Hh ^ 6 * Hh * Hh ^ 2 :=
          mul_le_mul (mul_le_mul hD2 hN (by positivity) (by positivity)) hQ hQ0 (by positivity)
      _ = Hh ^ 9 := by ring
  have hA : (De ^ 2 * N ^ 2 * Q) ^ (s + s * D.R.rS) ≤ (Hh ^ 9) ^ (s + s * D.R.rS) :=
    pow_le_pow_left₀ (by positivity) h9 _
  have hB : Q ^ (2 * D.R.rS ^ 2) ≤ Hh ^ (16 * D.R.rS ^ 2) :=
    calc Q ^ (2 * D.R.rS ^ 2) ≤ (Hh ^ 2) ^ (2 * D.R.rS ^ 2) := pow_le_pow_left₀ hQ0 hQ _
      _ = Hh ^ (4 * D.R.rS ^ 2) := by rw [← pow_mul]; ring_nf
      _ ≤ Hh ^ (16 * D.R.rS ^ 2) := pow_le_pow_right₀ hH (by omega)
  have hsplit : Hh ^ (9 * s + 9 * s * D.R.rS + 16 * D.R.rS ^ 2) =
      (Hh ^ 9) ^ (s + s * D.R.rS) * Hh ^ (16 * D.R.rS ^ 2) := by
    rw [← pow_mul, ← pow_add]
    ring_nf
  unfold frB fixB
  rw [hsplit]
  have hpos : 0 ≤ N ^ (2 * D.R.rS) * De ^ D.R.rS * 9 ^ (s * D.R.f) := by positivity
  calc N ^ (2 * D.R.rS) * De ^ D.R.rS *
        (9 ^ (s * D.R.f) * (De ^ 2 * N ^ 2 * Q) ^ (s + s * D.R.rS) * Q ^ (2 * D.R.rS ^ 2))
      = N ^ (2 * D.R.rS) * De ^ D.R.rS * 9 ^ (s * D.R.f) *
        ((De ^ 2 * N ^ 2 * Q) ^ (s + s * D.R.rS) * Q ^ (2 * D.R.rS ^ 2)) := by ring
    _ ≤ N ^ (2 * D.R.rS) * De ^ D.R.rS * 9 ^ (s * D.R.f) *
        ((Hh ^ 9) ^ (s + s * D.R.rS) * Hh ^ (16 * D.R.rS ^ 2)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hA hB (by positivity) (by positivity)) hpos

theorem main : ∀ Cg cb Cu cT CT C0 A : ℝ, ∃ C₀ : ℝ, ∀ C ≥ C₀, ∀ (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl : ℝ), 1 ≤ Cl → Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A → ∀ F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u → ∀ Λ : LatV D, IsRowLat D F0 Λ → ∀ Z : GramM D, RelZ D Z → ∀ s : ℕ, 1 ≤ s → s ≤ D.R.k → ∀ P : LatW D, P ≤ L0X D Λ (lf D F0) → rkW D P = D.R.k - s → ∀ De Hh : ℝ, 1 ≤ De → detW D P ≤ De → HHZ D large₂.sc.b C Z ≤ Hh → De ≤ Hh ^ 3 → (cntCl (FrSet D Λ (lf D F0) ((Tu D u' : ℕ) : D.host.E) Z P) (TEqv D Λ (lf D F0)) : ℝ≥0∞) ≤ ENNReal.ofReal (NT D u ^ (2 * D.R.rS) * De ^ D.R.rS * 9 ^ (s * D.R.f) * Hh ^ (9 * s + 9 * s * D.R.rS + 16 * D.R.rS ^ 2)) := by
  intro Cg cb Cu cT CT C0 A
  obtain ⟨C₁, hC₁⟩ := GlobalTheory.T.exists_gram_representative_size_le_HH_sq Cg cb Cu cT CT C0 A
  refine ⟨max C₁ (max 1 (2 * |CT|)), ?_⟩
  intro C hC D large₂ u u' C' Cl hCl hH F0 hF0e hF0z Λ hΛ Z hZ s hs1 hsk P hP hr De Hh hDe hd hHZ hDH
  have hbase : IsBase D u F0 := ⟨hF0e, hF0z⟩
  have hstand : Stand D u u' := hH.2.1
  have hS0 : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT := hH.1.1
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hTr, -, -⟩ := hS0
  have hC1 : 1 ≤ C := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hC
  have hCT : 2 * |CT| ≤ C := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hC
  have hCC₁ : C ≥ C₁ := le_trans (le_max_left _ _) hC
  obtain ⟨-, -, hpos, hlat, hint, -, -⟩ := GlobalTheory.T.standardBaseFlag_complement_integralLattice D u u' F0 Λ hstand hbase hΛ
  have hsub : SubOK D (L0X D Λ (lf D F0)) P s De := subOK_of D _ P hlat.fg hpos hint hP s hr De hd
  have hNTZ : NT D u ^ 2 ≤ HHZ D large₂.sc.b C Z :=
    NT_sq_le D u large₂.sc.b C CT (one_le_b _) hC1 hCT (hTr u).2 Z
  have hN : NT D u ^ 2 ≤ Hh := hNTZ.trans hHZ
  have hHZ0 : 0 ≤ HHZ D large₂.sc.b C Z := le_trans (sq_nonneg _) hNTZ
  have hHh0 : 0 ≤ Hh := hHZ0.trans hHZ
  have hHh1 : 1 ≤ Hh := by
    by_contra hlt'
    have hlt := lt_of_not_ge hlt'
    have : Hh ^ 3 < 1 := by nlinarith [mul_nonneg hHh0 hHh0]
    linarith
  have hNT0 : 0 ≤ NT D u := by
    show (0 : ℝ) ≤ ((D.mem u).A.T : ℝ) ^ D.R.f
    positivity
  have hbound := frB_le D s (NT D u) De (HHZ D large₂.sc.b C Z ^ 2) Hh hNT0 hDe (sq_nonneg _) hHh1 hN hDH
    (pow_le_pow_left₀ hHZ0 hHZ 2)
  by_cases hne : (FrSet D Λ (lf D F0) ((Tu D u' : ℕ) : D.host.E) Z P).Nonempty
  · obtain ⟨F', hF'⟩ := hne
    obtain ⟨Z₁, hZZ₁, hQ⟩ := hC₁ C hCC₁ D large₂ u u' C' Cl hCl hH F0 Λ hbase hΛ Z F' hZ hF'.1 hF'.2.1
    rw [frSet_congr D Λ (lf D F0) _ hZZ₁ P]
    exact (GlobalTheory.T.frameTermCount_sublattice_bound D u u' F0 Λ hstand hbase hΛ P Z₁ s De _ hs1 hsk hsub hQ).trans
      (ENNReal.ofReal_le_ofReal hbound)
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne]
    simp [cntCl]

end GlobalTheory.LoopC.TermsOver
