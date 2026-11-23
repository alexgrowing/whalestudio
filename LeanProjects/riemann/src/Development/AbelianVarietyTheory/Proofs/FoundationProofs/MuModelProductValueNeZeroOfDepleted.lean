import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ChapterMu
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.CuspidalUnitaryTwistsClaim
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EisensteinProductSeriesEqDepletedEisensteinProduStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AtkinLehnerEisStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ZsEqMulDepEis
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EisensteinPeriodicWeightsIsModularFormStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsModularFormCoeffSeqHeckeUAndDepletionStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoeffEisensteinSeriesTwistedHeckeUHeckeV
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoeffHeckeUVCauchyProductIdentities
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFormCoeffSeqMulAndQExpansion
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlashIntMatrixPosDetProperties
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFormCoeffSeqLinearStructure
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFormCoeffSeqEqOfPosCoeffEq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.QExpansionFunctionInjectiveOfPolynomialGrowth
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DirichletCharFiniteFourierTransformProperties
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.ZMVal

lemma ch_per {M : ℕ} (φ : DirichletCharacter ℂ M) (m : ℕ) (hm : M ∣ m) (d : ℤ) : ch φ (d + (m : ℤ)) = ch φ d := by
  obtain ⟨r, rfl⟩ := hm
  simp [ch]

lemma ch_mul' {M : ℕ} (φ : DirichletCharacter ℂ M) (x y : ℤ) : ch φ (x * y) = ch φ x * ch φ y := by
  simp [ch]

lemma ch_zero_of_dvd {l : ℕ} (φ : DirichletCharacter ℂ l) (hl : l.Prime) (x : ℤ) (hx : (l : ℤ) ∣ x) : ch φ x = 0 := by
  haveI : Fact l.Prime := ⟨hl⟩
  have : ((x : ZMod l)) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd x l).2 hx
  simp only [ch]; rw [this]; exact MulChar.map_zero φ

lemma isUnit_of_coprime {M : ℕ} (d : ℤ) (h : IsCoprime d M) : IsUnit (d : ZMod M) := by
  obtain ⟨u, v, huv⟩ := h
  refine isUnit_iff_exists_inv.2 ⟨(u : ZMod M), ?_⟩
  have := congrArg (fun z : ℤ => (z : ZMod M)) huv
  simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, mul_zero, add_zero, Int.cast_one] at this
  rw [mul_comm]; exact this

lemma ch_mul_inv {M : ℕ} (φ : DirichletCharacter ℂ M) (d : ℤ) (h : IsCoprime d M) : ch φ d * ch φ⁻¹ d = 1 := by
  have hu := isUnit_of_coprime d h
  simp only [ch]
  rw [← MulChar.mul_apply, mul_inv_cancel, ← hu.unit_spec]
  exact MulChar.one_apply_coe _

lemma ch_ne_zero {M : ℕ} (φ : DirichletCharacter ℂ M) (d : ℤ) (h : IsCoprime d M) : ch φ d ≠ 0 :=
  left_ne_zero_of_mul_eq_one (ch_mul_inv φ d h)

lemma sq_neg_one {M : ℕ} (φ : DirichletCharacter ℂ M) : φ (-1) * φ (-1) = 1 := by
  rw [← map_mul]; simp

lemma dc_inv_neg_one {M : ℕ} (φ : DirichletCharacter ℂ M) : φ⁻¹ (-1) = φ (-1) := by
  rw [MulChar.inv_apply_eq_inv']
  have h := sq_neg_one φ
  exact inv_eq_of_mul_eq_one_right h

lemma coprime_left {a b : ℕ} (d : ℤ) (h : IsCoprime d ((a * b : ℕ) : ℤ)) : IsCoprime d (a : ℤ) := by
  push_cast at h; exact h.of_mul_right_left

lemma coprime_right {a b : ℕ} (d : ℤ) (h : IsCoprime d ((a * b : ℕ) : ℤ)) : IsCoprime d (b : ℤ) := by
  push_cast at h; exact h.of_mul_right_right

lemma chi_neg_one {k N : ℕ} (hk : Odd k) (χ : DirichletCharacter ℂ N) (g : ℕ → ℂ) (h : Prim k N χ⁻¹ g) :
    χ (-1) = -1 := by
  have hsq := sq_neg_one χ
  by_contra hne
  have h1 : χ (-1) = 1 := by
    have : (χ (-1) - 1) * (χ (-1) + 1) = 0 := by linear_combination hsq
    rcases mul_eq_zero.1 this with h | h
    · linear_combination h
    · exact absurd (by linear_combination h) hne
  have hinv : χ⁻¹ (-1) = 1 := by rw [dc_inv_neg_one, h1]
  have hq : ∀ τ : ℍ, qs g τ = 0 := by
    intro τ
    have := h.cf.1.2 (-1) (by simp) τ
    have hs : ((-1 : SL(2, ℤ)) • τ) = τ := by
      rw [show (-1 : SL(2, ℤ)) = -(1 : SL(2, ℤ)) from rfl, ModularGroup.SL_neg_smul, one_smul]
    rw [hs] at this
    simp [ch, hinv, hk.neg_one_pow] at this
    linear_combination this / 2
  have hpb0 : PolyB (0 : ℕ → ℂ) := ⟨0, 0, by simp⟩
  have : g = 0 := GlobalTheory.EisM.qs_injective g 0 h.cf.1.1 hpb0 (by funext τ; rw [hq τ]; simp [qs])
  have := h.one
  simp_all

lemma slz_smul' (j : ℕ) (δ : M2) (c : ℂ) (f : ℍ → ℂ) : slz j δ (c • f) = c • slz j δ f := by
  funext τ; simp only [slz, Pi.smul_apply, smul_eq_mul]; ring

lemma slz_mul' (j j' : ℕ) (hj : 1 ≤ j) (hj' : 1 ≤ j') (δ : M2) (f g : ℍ → ℂ) :
    slz (j + j') δ (fun τ => f τ * g τ) = fun τ => ((δ.det : ℤ) : ℂ) * (slz j δ f τ * slz j' δ g τ) := by
  funext τ
  obtain ⟨a, rfl⟩ : ∃ a, j = a + 1 := ⟨j - 1, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, j' = b + 1 := ⟨j' - 1, by omega⟩
  simp only [slz]
  rw [show a + 1 + (b + 1) - 1 = a + b + 1 by omega, show a + 1 - 1 = a by omega, show b + 1 - 1 = b by omega]
  have hx : ∀ x : ℂ, (x ^ (a + 1 + (b + 1)))⁻¹ = (x ^ (a + 1))⁻¹ * (x ^ (b + 1))⁻¹ := fun x => by rw [pow_add, mul_inv]
  rw [hx]; ring

lemma lam_sub_smul (B : ℕ) (c a b : ℕ → ℂ) (t : ℂ) : lam B c (a - t • b) = lam B c a - t * lam B c b := by
  simp only [lam, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
  congr 1; refine Finset.sum_congr rfl fun n _ => by ring

lemma lam_smul (B : ℕ) (c a : ℕ → ℂ) (t : ℂ) : lam B c (t • a) = t * lam B c a := by
  simp only [lam, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => by ring

lemma mul_smul_smul (a b : ℕ → ℂ) (s t : ℂ) : mul (s • a) (t • b) = (s * t) • mul a b := by
  funext n; simp only [mul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => by ring

end GlobalTheory.ZMVal

namespace GlobalTheory.ZMVal

lemma U_eis_eq {j L l : ℕ} (ε : ℤ → ℂ) (c t : ℂ) (a b : ℤ → ℂ) (hj : 1 ≤ j) (hL : 0 < L) (hl : l.Prime)
    (hlL : l ∣ L) (hper : ∀ d, ε (d + L) = ε d) (hMF : MF j L ε (eis j c a b))
    (ha : ∀ x : ℤ, (l : ℤ) ∣ x → a x = 0) (hb : ∀ y, b (l * y) = t * b y) :
    Uo l (eis j c a b) = t • eis j c a b := by
  have h1 := (GlobalTheory.T.isModularFormCoeffSeq_heckeU_and_depletion j L l ε _ hj hl hlL hper hMF).1
  have h2 := ((GlobalTheory.EisM.mf_linear j L ε).2.2.1 t _ hMF).1
  refine GlobalTheory.EisM.eq_of_coeff_pos_eq j L ε _ _ hj hL h1 h2 (fun n hn => ?_)
  simp only [Uo, Pi.smul_apply, smul_eq_mul]
  exact (GlobalTheory.eis_U_V j l c t a b hl).1 ha hb n hn

lemma slashIntMatrixPosDet_atkinLehner_twice (j N l : ℕ) (a₀ b₀ c₀ d₀ : ℤ) (hdet : N * a₀ * d₀ - l * b₀ * c₀ = 1) (hj : 1 ≤ j) (hN : 0 < N)
    (ε : ℤ → ℂ) (f : ℍ → ℂ) (hf : Inv j (N * l) ε f) :
    ∃ d : ℤ, IsCoprime d ((N * l : ℕ) : ℤ) ∧
      slz j !![(N : ℤ) * a₀, b₀; N * l * c₀, N * d₀] (slz j !![(N : ℤ) * a₀, b₀; N * l * c₀, N * d₀] f) =
        ((N : ℂ) ^ j / (N : ℂ) ^ 2 * ε d) • f := by
  set W : M2 := !![(N : ℤ) * a₀, b₀; N * l * c₀, N * d₀] with hW
  set γm : M2 := !![(N : ℤ) * a₀ ^ 2 + l * b₀ * c₀, (a₀ + d₀) * b₀; N * l * c₀ * (a₀ + d₀), l * b₀ * c₀ + N * d₀ ^ 2]
    with hγm
  have hγdet : γm.det = 1 := by
    rw [hγm, Matrix.det_fin_two_of]; linear_combination ((N : ℤ) * a₀ * d₀ - l * b₀ * c₀ + 1) * hdet
  let γ : SL(2, ℤ) := ⟨γm, hγdet⟩
  set D : M2 := !![(N : ℤ), 0; 0, (N : ℤ)] with hD
  have hWW : W * W = D * γm := by
    rw [hW, hD, hγm]
    ext i k; fin_cases i <;> fin_cases k <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  have hWdet : 0 < W.det := by
    have : W.det = N := by rw [hW, Matrix.det_fin_two_of]; linear_combination (N : ℤ) * hdet
    rw [this]; exact_mod_cast hN
  have hDdet : 0 < D.det := by rw [hD, Matrix.det_fin_two_of]; simp; positivity
  have hprops := GlobalTheory.EisM.slz_props j f hj
  refine ⟨l * b₀ * c₀ + N * d₀ ^ 2, ⟨(N : ℤ) * a₀ ^ 2 + l * b₀ * c₀, -((a₀ + d₀) * b₀ * c₀ * (a₀ + d₀)), ?_⟩, ?_⟩
  · push_cast; linear_combination ((N : ℤ) * a₀ * d₀ - l * b₀ * c₀ + 1) * hdet
  rw [← hprops.1 W W hWdet hWdet, hWW, hprops.1 D γm hDdet (by rw [hγdet]; norm_num)]
  have hDf : slz j D f = ((N : ℂ) ^ j / (N : ℂ) ^ 2) • f := by
    funext τ; rw [hD, hprops.2.2.2.2 N τ hN]; rfl
  rw [hDf, slz_smul']
  have hγ : slz j (γ : M2) f = fun τ => ε (γ 1 1) * f τ :=
    ((hprops.2.2.1 (N * l) ε).1 hf) γ (by
      show ((N * l : ℕ) : ℤ) ∣ γm 1 0
      rw [hγm]; simp; exact ⟨c₀ * (a₀ + d₀), by ring⟩)
  have hγ' : slz j γm f = fun τ => ε (l * b₀ * c₀ + N * d₀ ^ 2) * f τ := by
    rw [show γm = (γ : M2) from rfl, hγ]; rfl
  rw [hγ']
  funext τ; simp only [Pi.smul_apply, smul_eq_mul]; ring

end GlobalTheory.ZMVal

namespace GlobalTheory.ZMVal

lemma coprime_of_dvd {d : ℤ} {m M : ℕ} (h : IsCoprime d ((M : ℕ) : ℤ)) (hm : m ∣ M) : IsCoprime d (m : ℤ) :=
  h.of_isCoprime_of_dvd_right (Int.natCast_dvd_natCast.2 hm)

end GlobalTheory.ZMVal

open GlobalTheory.ZMVal in

theorem _root_.GlobalTheory.zm_val_ne_zero : ∀ (e N l : ℕ) (χ θ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ l) (g : ℕ → ℂ) (α β : ℂ) (a₀ b₀ c₀ d₀ : ℤ), N * a₀ * d₀ - l * b₀ * c₀ = 1 → 1 ≤ e → 0 < N → l.Prime → ¬ l ∣ N → Prim (2 * e + 1) N χ⁻¹ (fun n => conj (g n)) → α + β = χ l * conj (g l) → α * β = χ l * (l : ℂ) ^ (2 * e) → α ≠ 0 → θ (-1) = (-1) ^ e * ψ (-1) → θ * χ⁻¹ ≠ 1 → ∀ (B : ℕ) (c : ℕ → ℂ), EigF (2 * e + 1) N l χ (fun q => χ q * conj (g q)) α B c → val B c l α 1 (Zs (2 * e + 1) l (ch θ) (hat ⇑(θ * χ⁻¹)) (fun x y => ψ x * ψ⁻¹ y * ((y : ℂ) / x) ^ e)) ≠ 0 → ∀ (B' : ℕ) (c' : ℕ → ℂ), (∀ a a', MF (2 * e + 1) (N * l) (ch χ⁻¹) a → MF (2 * e + 1) (N * l) (ch χ) a' → qs a' = slz (2 * e + 1) !![(N : ℤ) * a₀, b₀; N * l * c₀, N * d₀] (qs a) → lam B' c' a = lam B c a') → (∀ a, MF (2 * e + 1) (N * l) (ch χ⁻¹) a → lam B' c' (Uo l a) = χ⁻¹ l * α * lam B' c' a) → val B' c' l (χ⁻¹ l * α) 1 (Zm (2 * e + 1) l (hat θ) (ch (θ * χ⁻¹)) (fun A d => ψ A * ψ⁻¹ d * ((d : ℂ) / A) ^ e)) ≠ 0 := by
  intro e N l χ θ ψ g α β a₀ b₀ c₀ d₀ hdet he hN hl hlN hprim hsum hprod hα0 hpar hθχ B c hEig hval B' c' hAL hU'
  haveI : Fact l.Prime := ⟨hl⟩
  have hl0 : 0 < l := hl.pos
  have hNl : 0 < N * l := Nat.mul_pos hN hl0
  have hlNl : l ∣ N * l := dvd_mul_left l N
  have hNNl : N ∣ N * l := dvd_mul_right N l
  have hχm : χ (-1) = -1 := chi_neg_one (k := 2 * e + 1) ⟨e, rfl⟩ χ _ hprim
  have hψsq := sq_neg_one ψ
  set θ' := θ * χ⁻¹ with hθ'
  have chm : ∀ {M : ℕ} (φ : DirichletCharacter ℂ M), ch φ (-1) = φ (-1) := fun φ => by simp [ch]
  have hper : ∀ {M : ℕ} (φ : DirichletCharacter ℂ M), M ∣ N * l → ∀ d : ℤ, ch φ (d + ((N * l : ℕ) : ℤ)) = ch φ d :=
    fun φ h d => ch_per φ _ h d
  have hatch := (GlobalTheory.EisM.hat_char_props).1
  have hatper : ∀ (φ : DirichletCharacter ℂ N) (x : ℤ), hat φ (x + ((N * l : ℕ) : ℤ)) = hat φ x := by
    intro φ x
    have hp : Function.Periodic (hat φ) (N : ℤ) := fun x => (hatch N φ hN).1 x
    have := hp.nat_mul l x
    rw [show ((N * l : ℕ) : ℤ) = (l : ℤ) * (N : ℤ) by push_cast; ring]
    simpa using this
  have hθ'inv : ∀ d, ch θ'⁻¹ d = ch θ⁻¹ d * ch χ d := fun d => by
    simp only [ch, hθ', mul_inv, inv_inv, MulChar.mul_apply]
  have hθ'v : ∀ d, ch θ' d = ch θ d * ch χ⁻¹ d := fun d => by simp only [ch, hθ', MulChar.mul_apply]
  have hθ'm : θ' (-1) = -((-1 : ℂ) ^ e * ψ (-1)) := by
    rw [hθ', MulChar.mul_apply, dc_inv_neg_one, hχm, hpar]; ring

  obtain ⟨c1, hE1⟩ := GlobalTheory.T.eisenstein_periodic_weights_isModularForm e l N (ch ψ) (ch θ) (ch ψ) (ch θ) he hl0 hN
    (ch_zero_of_dvd ψ hl 0 (dvd_zero _))
    (fun x => ch_per ψ l dvd_rfl x) (fun x => ch_per θ N dvd_rfl x)
    (fun d _ => ⟨fun x => by rw [ch_mul', mul_comm], fun x => by rw [ch_mul', mul_comm]⟩)
    (by rw [chm, chm, hpar]; linear_combination ((-1 : ℂ) ^ e) * hψsq)
  rw [mul_comm l N] at hE1
  obtain ⟨c2, hE2⟩ := GlobalTheory.T.eisenstein_periodic_weights_isModularForm (e + 1) (N * l) 1 (fun y => ch ψ⁻¹ y * hat θ' y) (fun _ => 1)
    (fun d => ch ψ⁻¹ d * ch θ'⁻¹ d) (fun _ => 1) (by omega) hNl one_pos
    (by rw [ch_zero_of_dvd ψ⁻¹ hl 0 (dvd_zero _), zero_mul])
    (fun x => by rw [hper ψ⁻¹ hlNl, hatper]) (fun x => rfl)
    (fun d hd => ⟨fun x => by
        rw [ch_mul', (hatch N θ' hN).2.1 d x (coprime_of_dvd hd (dvd_mul_of_dvd_left hNNl 1))]; ring,
      fun x => by simp⟩)
    (by simp only [chm, dc_inv_neg_one, hθ'm]; linear_combination (-(-1 : ℂ) ^ e) * hψsq)
  simp only [mul_one] at hE2
  obtain ⟨c3, hF1⟩ := GlobalTheory.T.eisenstein_periodic_weights_isModularForm e (N * l) 1 (fun y => ch ψ y * hat θ y) (fun _ => 1)
    (fun d => ch ψ d * ch θ⁻¹ d) (fun _ => 1) he hNl one_pos
    (by rw [ch_zero_of_dvd ψ hl 0 (dvd_zero _), zero_mul])
    (fun x => by rw [hper ψ hlNl, hatper]) (fun x => rfl)
    (fun d hd => ⟨fun x => by
        rw [ch_mul', (hatch N θ hN).2.1 d x (coprime_of_dvd hd (dvd_mul_of_dvd_left hNNl 1))]; ring,
      fun x => by simp⟩)
    (by simp only [chm, dc_inv_neg_one, hpar]; linear_combination ((-1 : ℂ) ^ e) * hψsq)
  simp only [mul_one] at hF1
  obtain ⟨c4, hF2⟩ := GlobalTheory.T.eisenstein_periodic_weights_isModularForm (e + 1) l N (ch ψ⁻¹) (ch θ') (ch ψ⁻¹) (ch θ') (by omega) hl0 hN
    (ch_zero_of_dvd ψ⁻¹ hl 0 (dvd_zero _))
    (fun x => ch_per ψ⁻¹ l dvd_rfl x) (fun x => ch_per θ' N dvd_rfl x)
    (fun d _ => ⟨fun x => by rw [ch_mul', mul_comm], fun x => by rw [ch_mul', mul_comm]⟩)
    (by rw [chm, chm, dc_inv_neg_one, hθ'm]; linear_combination (-(-1 : ℂ) ^ e) * hψsq)
  rw [mul_comm l N] at hF2

  obtain ⟨κ1, hκ1, hW1⟩ := GlobalTheory.T.exists_ne_zero_slz_qs_eis_eq_smul e N l ψ θ c1 c3 a₀ b₀ c₀ d₀ hdet he hN hl hlN hE1 hF1
  obtain ⟨κ2, hκ2, hW2⟩ := GlobalTheory.T.exists_ne_zero_slz_qs_eis_eq_smul (e + 1) N l ψ⁻¹ θ' c4 c2 a₀ b₀ c₀ d₀ hdet (by omega) hN hl hlN hF2 hE2
  set W : M2 := !![(N : ℤ) * a₀, b₀; N * l * c₀, N * d₀] with hW
  have hWd : W.det = N := by rw [hW, Matrix.det_fin_two_of]; linear_combination (N : ℤ) * hdet
  obtain ⟨d, hd, hWW⟩ := slashIntMatrixPosDet_atkinLehner_twice e N l a₀ b₀ c₀ d₀ hdet he hN _ _ hE1.2
  set E1 := eis e c1 (ch ψ) (ch θ) with hE1d
  set E2 := eis (e + 1) c2 (fun y => ch ψ⁻¹ y * hat θ' y) (fun _ => 1) with hE2d
  set F1 := eis e c3 (fun y => ch ψ y * hat θ y) (fun _ => 1) with hF1d
  set F2 := eis (e + 1) c4 (ch ψ⁻¹) (ch θ') with hF2d
  set K0 : ℂ := (N : ℂ) ^ e / (N : ℂ) ^ 2 * (ch ψ d * ch θ d) with hK0
  have hF1W : slz e W (qs F1) = (κ1⁻¹ * K0) • qs E1 := by
    have h : qs F1 = κ1⁻¹ • slz e W (qs E1) := by rw [hW1, smul_smul, inv_mul_cancel₀ hκ1, one_smul]
    rw [h, slz_smul', hWW, smul_smul]

  have hmul := (GlobalTheory.EisM.mul_main).1
  have hmf := GlobalTheory.EisM.mul_main.2
  set X := mul E1 E2 with hXd
  set Xm := mul F1 F2 with hXmd
  have hk : 2 * e + 1 = e + (e + 1) := by ring
  have hX : MF (2 * e + 1) (N * l) (ch χ) X := by
    rw [hk]
    refine (GlobalTheory.EisM.mf_linear _ _ _).2.2.2.1 _ _ (fun x hx => ?_) (hmf e (e + 1) (N * l) _ _ E1 E2 hE1 hE2)
    have h1 := ch_mul_inv ψ x (coprime_right (a := N) x hx)
    have h2 := ch_mul_inv θ x (coprime_left (b := l) x hx)
    rw [hθ'inv]; linear_combination (ch θ x * ch θ⁻¹ x * ch χ x) * h1 + ch χ x * h2
  have hXm : MF (2 * e + 1) (N * l) (ch χ⁻¹) Xm := by
    rw [hk]
    refine (GlobalTheory.EisM.mf_linear _ _ _).2.2.2.1 _ _ (fun x hx => ?_) (hmf e (e + 1) (N * l) _ _ F1 F2 hF1 hF2)
    have h1 := ch_mul_inv ψ x (coprime_right (a := N) x hx)
    have h2 := ch_mul_inv θ x (coprime_left (b := l) x hx)
    rw [hθ'v]; linear_combination (ch θ x * ch θ⁻¹ x * ch χ⁻¹ x) * h1 + ch χ⁻¹ x * h2
  set K : ℂ := ((N : ℤ) : ℂ) * (κ1⁻¹ * K0) * κ2 with hK
  have ha' : MF (2 * e + 1) (N * l) (ch χ) (K • X) := ((GlobalTheory.EisM.mf_linear _ _ _).2.2.1 K X hX).1
  have hqs : qs (K • X) = slz (2 * e + 1) W (qs Xm) := by
    rw [((GlobalTheory.EisM.mf_linear _ _ _).2.2.1 K X hX).2, hXd, hXmd, (hmul E1 E2 hE1.1 hE2.1).2,
      (hmul F1 F2 hF1.1 hF2.1).2, hk, slz_mul' e (e + 1) he (by omega) W (qs F1) (qs F2), hF1W, hW2, hWd]
    funext τ; simp only [Pi.smul_apply, smul_eq_mul]; ring
  have hAL' := hAL Xm (K • X) hXm ha' hqs

  have hpE1 : ∀ x, (fun d => ch ψ d * ch θ d) (x + ((N * l : ℕ) : ℤ)) = (fun d => ch ψ d * ch θ d) x := fun x => by
    simp only; rw [hper ψ hlNl, hper θ hNNl]

  have UE1 : Uo l E1 = (ch θ l) • E1 := U_eis_eq _ c1 (ch θ l) (ch ψ) (ch θ) he hNl hl hlNl hpE1 hE1
      (fun x hx => ch_zero_of_dvd ψ hl x hx) (fun y => ch_mul' θ l y)
  have UnitaryRankTwoFlags : Uo l E2 = (1 : ℂ) • E2 := U_eis_eq (fun d => ch ψ⁻¹ d * ch θ'⁻¹ d) c2 1 (fun y => ch ψ⁻¹ y * hat θ' y) (fun _ => 1) (by omega) hNl hl hlNl
      (fun x => by simp only [hper ψ⁻¹ hlNl, hper θ'⁻¹ hNNl]) hE2
      (fun x hx => by simp only [ch_zero_of_dvd ψ⁻¹ hl x hx, zero_mul]) (fun y => by simp)
  have UF1 : Uo l F1 = (1 : ℂ) • F1 := U_eis_eq (fun d => ch ψ d * ch θ⁻¹ d) c3 1 (fun y => ch ψ y * hat θ y) (fun _ => 1) he hNl hl hlNl
      (fun x => by simp only [hper ψ hlNl, hper θ⁻¹ hNNl]) hF1
      (fun x hx => by simp only [ch_zero_of_dvd ψ hl x hx, zero_mul]) (fun y => by simp)
  have UF2 : Uo l F2 = (ch θ' l) • F2 := U_eis_eq (fun d => ch ψ⁻¹ d * ch θ' d) c4 (ch θ' l) (ch ψ⁻¹) (ch θ') (by omega) hNl hl hlNl
      (fun x => by simp only [hper ψ⁻¹ hlNl, hper θ' hNNl]) hF2
      (fun x hx => ch_zero_of_dvd ψ⁻¹ hl x hx) (fun y => ch_mul' θ' l y)
  have hfor := GlobalTheory.EisM.formal_identities ℂ l hl0
  have hFF : (fun x y : ℕ => ψ x * ψ⁻¹ y * ((y : ℂ) / x) ^ e) =
      fun x y : ℕ => ch ψ x * ch ψ⁻¹ y * ((y : ℂ) / x) ^ e := by
    funext x y; simp [ch]

  have hZs : Zs (2 * e + 1) l (ch θ) (hat θ') (fun x y => ψ x * ψ⁻¹ y * ((y : ℂ) / x) ^ e) =
      mul (dep l E1) (dep l E2) := by
    have := GlobalTheory.zs_eq_mul_dep_eis (2 * e + 1) l e (ch θ) (hat θ') (ch ψ) (ch ψ⁻¹) c1 c2 (by omega)
    rw [show 2 * e + 1 - 1 - e = e by omega] at this
    rw [hFF, this]
  simp only [val, pow_one, Function.iterate_one] at hval
  rw [hZs, (hfor.2.1 E1 E2), UE1, UnitaryRankTwoFlags, mul_smul_smul, lam_sub_smul, hEig.U _ hX] at hval

  have hZm : Zm (2 * e + 1) l (hat θ) (ch θ') (fun A d => ψ A * ψ⁻¹ d * ((d : ℂ) / A) ^ e) =
      mul (dep l F1) (dep l F2) := by
    have := GlobalTheory.T.eisensteinProductSeries_eq_depleted_eisenstein_product (2 * e + 1) l e (hat θ) (ch θ') (ch ψ) (ch ψ⁻¹) c3 c4 (by omega)
    rw [show 2 * e + 1 - 1 - e = e by omega,
      show (fun x => hat θ x * ch ψ x) = fun x => ch ψ x * hat θ x from funext fun x => mul_comm _ _] at this
    rw [hFF, this]
  simp only [val, pow_one, Function.iterate_one]
  rw [hZm, (hfor.2.1 F1 F2), UF1, UF2, mul_smul_smul, lam_sub_smul, hU' _ hXm, hAL', lam_smul]

  have hcl : χ⁻¹ (l : ZMod N) = ch χ⁻¹ l := by simp [ch]
  have hlc : IsCoprime (l : ℤ) (N : ℤ) := Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd hl).2 hlN)
  have hχl : ch χ⁻¹ l ≠ 0 := ch_ne_zero _ _ hlc
  have hKne : K ≠ 0 := by
    have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
    have h1 := ch_ne_zero ψ d (coprime_right (a := N) d hd)
    have h2 := ch_ne_zero θ d (coprime_left (b := l) d hd)
    rw [hK, hK0]; push_cast
    exact mul_ne_zero (mul_ne_zero hN0 (mul_ne_zero (inv_ne_zero hκ1)
      (mul_ne_zero (div_ne_zero (pow_ne_zero _ hN0) (pow_ne_zero _ hN0)) (mul_ne_zero h1 h2)))) hκ2
  have hv : (α - ch θ l) * lam B c X ≠ 0 := by
    intro h; apply hval; linear_combination α⁻¹ * h
  rw [hcl, hθ'v]
  have : (ch χ⁻¹ l * α)⁻¹ * (ch χ⁻¹ l * α * (K * lam B c X) - 1 * (ch θ l * ch χ⁻¹ l) * (K * lam B c X)) =
      (ch χ⁻¹ l * α)⁻¹ * (ch χ⁻¹ l * K * ((α - ch θ l) * lam B c X)) := by ring
  rw [this]
  exact mul_ne_zero (inv_ne_zero (mul_ne_zero hχl hα0)) (mul_ne_zero (mul_ne_zero hχl hKne) hv)
