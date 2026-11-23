import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.Chapter
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoeffHeckeVOperatorRaisesLevelStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFormCoeffSeqEqOfPosCoeffEqStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsModularFormCoeffSeqHeckeUAndDepletionStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EisensteinPeriodicWeightsIsModularFormStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoeffEisensteinSeriesTwistedHeckeUHeckeVStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoeffHeckeUVCauchyProductIdentitiesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DirichletCharFiniteFourierTransformPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFormCoeffSeqLinearStructureStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFormCoeffSeqMulAndQExpansionStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ZsEqMulDepEisStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.DepletedValue

lemma isUnit_of_isCoprime {n : ℕ} {d : ℤ} (h : IsCoprime d (n : ℤ)) : IsUnit (d : ZMod n) := by
  obtain ⟨u, v, huv⟩ := h
  have h1 := congrArg (Int.cast : ℤ → ZMod n) huv
  push_cast at h1
  simp only [ZMod.natCast_self, mul_zero, add_zero] at h1
  exact isUnit_iff_exists_inv.mpr ⟨_, by rw [mul_comm]; exact h1⟩

lemma ch_ne_zero {n : ℕ} (χ : DirichletCharacter ℂ n) {d : ℤ} (h : IsCoprime d (n : ℤ)) : ch χ d ≠ 0 :=
  ((isUnit_of_isCoprime h).map χ).ne_zero

lemma ch_inv {n : ℕ} (χ : DirichletCharacter ℂ n) (d : ℤ) : ch χ⁻¹ d = (ch χ d)⁻¹ :=
  MulChar.inv_apply_eq_inv' _ _

lemma ch_mul {n : ℕ} (θ χ : DirichletCharacter ℂ n) (d : ℤ) : ch (θ * χ) d = ch θ d * ch χ d := by
  simp [ch]

lemma ch_one {n : ℕ} {d : ℤ} (h : IsCoprime d (n : ℤ)) : ch (1 : DirichletCharacter ℂ n) d = 1 :=
  MulChar.one_apply (isUnit_of_isCoprime h)

lemma ch_dvd {l : ℕ} (hl : l.Prime) (ψ : DirichletCharacter ℂ l) {d : ℤ} (h : (l : ℤ) ∣ d) : ch ψ d = 0 := by
  haveI : Fact l.Prime := ⟨hl⟩
  have : (d : ZMod l) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd d l).2 h
  simp only [ch, this]; exact MulChar.map_zero ψ

lemma coprime_left {d : ℤ} {N l : ℕ} (h : IsCoprime d ((N * l : ℕ) : ℤ)) : IsCoprime d (N : ℤ) := by
  push_cast at h; exact h.of_mul_right_left

lemma coprime_right {d : ℤ} {N l : ℕ} (h : IsCoprime d ((N * l : ℕ) : ℤ)) : IsCoprime d (l : ℤ) := by
  push_cast at h; exact h.of_mul_right_right

lemma mul_smul_right (a b : ℕ → ℂ) (s : ℂ) : mul a (s • b) = s • mul a b := by
  funext n; simp [mul, Finset.mul_sum]; exact Finset.sum_congr rfl (fun _ _ => by ring)

lemma mul_smul_left (a b : ℕ → ℂ) (s : ℂ) : mul (s • a) b = s • mul a b := by
  funext n; simp [mul, Finset.mul_sum]; exact Finset.sum_congr rfl (fun _ _ => by ring)

lemma mul_add_right (a b b' : ℕ → ℂ) : mul a (b + b') = mul a b + mul a b' := by
  funext n; simp [mul, mul_add, Finset.sum_add_distrib]

lemma lam_add (B : ℕ) (c a b : ℕ → ℂ) : lam B c (a + b) = lam B c a + lam B c b := by
  simp [lam, mul_add, Finset.sum_add_distrib]

lemma lam_smul (B : ℕ) (c a : ℕ → ℂ) (s : ℂ) : lam B c (s • a) = s * lam B c a := by
  simp [lam, Finset.mul_sum]; exact Finset.sum_congr rfl (fun _ _ => by ring)

lemma lam_sub (B : ℕ) (c a b : ℕ → ℂ) : lam B c (a - b) = lam B c a - lam B c b := by
  simp [lam, mul_sub, Finset.sum_sub_distrib]

lemma mul_zero_right (a : ℕ → ℂ) : mul a 0 = 0 := by
  funext n; simp [mul]

lemma lam_zero (B : ℕ) (c : ℕ → ℂ) : lam B c 0 = 0 := by simp [lam]

lemma core {l : ℕ} (hl : 0 < l) (B : ℕ) (c : ℕ → ℂ) (α t₀ : ℂ) (F E : ℕ → ℂ) (hF : Uo l F = t₀ • F) (hE : Uo l E = E)
    (hU : lam B c (Uo l (mul F E)) = α * lam B c (mul F E)) (h0 : lam B c (mul F E) ≠ 0) (hα : α ≠ t₀) (hα0 : α ≠ 0) :
    val B c l α 1 (mul (dep l F) (dep l E)) ≠ 0 := by
  simp only [val, Function.iterate_one, pow_one]
  rw [(GlobalTheory.T.coeffHecke_UV_cauchyProduct_identities ℂ l hl).2.1, hF, hE, mul_smul_left, lam_sub, lam_smul, hU, ← sub_mul]
  exact mul_ne_zero (inv_ne_zero hα0) (mul_ne_zero (sub_ne_zero.mpr hα) h0)

end GlobalTheory.DepletedValue

namespace GlobalTheory.DepletedValue

lemma zs_eq (e l : ℕ) (he : 1 ≤ e) {N : ℕ} (θ χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ l) (c₀ c' : ℂ) :
    Zs (2 * e + 1) l (ch θ) (hat ⇑(θ * χ)) (fun x y => ψ x * ψ⁻¹ y * ((y : ℂ) / x) ^ e) =
      mul (dep l (eis e c₀ (ch ψ) (ch θ))) (dep l (eis (e + 1) c' (fun y => ch ψ⁻¹ y * hat ⇑(θ * χ) y) fun _ => 1)) := by
  have h := GlobalTheory.T.zs_monomial_ratio_eq_mul_dep_eis (2 * e + 1) l e (ch θ) (hat ⇑(θ * χ)) (ch ψ) (ch ψ⁻¹) c₀ c' (by omega)
  have hk : 2 * e + 1 - 1 - e = e := by omega
  rw [hk] at h
  rw [← h]
  congr 1
  funext x y
  simp [ch]

lemma U_FF (e N l : ℕ) (he : 1 ≤ e) (hN : 0 < N) (hl : l.Prime) (θ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ l) (c₀ : ℂ)
    (hF : MF e (N * l) (fun d => ch ψ d * ch θ d) (eis e c₀ (ch ψ) (ch θ))) :
    Uo l (eis e c₀ (ch ψ) (ch θ)) = θ l • eis e c₀ (ch ψ) (ch θ) := by
  have hper : ∀ d : ℤ, (fun d => ch ψ d * ch θ d) (d + ((N * l : ℕ) : ℤ)) = (fun d => ch ψ d * ch θ d) d := by
    intro d; simp [ch]
  have h1 := (GlobalTheory.T.isModularFormCoeffSeq_heckeU_and_depletion e (N * l) l _ _ he hl (dvd_mul_left l N) hper hF).1
  have h2 := ((GlobalTheory.T.modularFormCoeffSeq_linear_structure e (N * l) _).2.2.1 (θ l) _ hF).1
  refine GlobalTheory.T.modularFormCoeffSeq_eq_of_pos_coeff_eq e (N * l) _ _ _ he (Nat.mul_pos hN hl.pos) h1 h2 (fun n hn => ?_)
  have h3 := (GlobalTheory.T.coeffEisensteinSeriesTwisted_heckeU_heckeV e l c₀ (θ l) (ch ψ) (ch θ) hl).1 (fun x hx => ch_dvd hl ψ hx) (fun y => by simp [ch]) n hn
  simpa [Uo] using h3

lemma U_EE (e N l : ℕ) (hl : l.Prime) (θ' : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ l) (c' : ℂ) :
    Uo l (eis (e + 1) c' (fun y => ch ψ⁻¹ y * hat ⇑θ' y) fun _ => 1) = eis (e + 1) c' (fun y => ch ψ⁻¹ y * hat ⇑θ' y) fun _ => 1 := by
  funext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp [Uo]
  have h3 := (GlobalTheory.T.coeffEisensteinSeriesTwisted_heckeU_heckeV (e + 1) l c' 1 (fun y => ch ψ⁻¹ y * hat ⇑θ' y) (fun _ => 1) hl).1
    (fun x hx => by simp [ch_dvd hl ψ⁻¹ hx]) (fun y => by simp) n hn
  simpa [Uo] using h3

lemma char_eq {N l : ℕ} (χ θ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ l) (φ : DirichletCharacter ℂ (N * l))
    (hφ : ∀ d : ℤ, ch φ d = ch (θ * χ) d * ch ψ d) (d : ℤ) (hd : IsCoprime d ((N * l : ℕ) : ℤ)) :
    ch ψ d * ch θ d * ch φ⁻¹ d = ch χ⁻¹ d := by
  have h1 := ch_ne_zero ψ (coprime_right hd)
  have h2 := ch_ne_zero θ (coprime_left hd)
  have h3 := ch_ne_zero χ (coprime_left hd)
  rw [ch_inv, ch_inv, hφ, ch_mul]
  field_simp

end GlobalTheory.DepletedValue

namespace GlobalTheory.DepletedValue

lemma good_ne (e N l : ℕ) (χ θ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ l) (φ : DirichletCharacter ℂ (N * l))
    (c₀ c₁ : ℂ) (B : ℕ) (c : ℕ → ℂ) (he : 1 ≤ e) (hN : 0 < N) (hl : l.Prime) (hlN : ¬ l ∣ N) (hψ : ψ ≠ 1)
    (hφ : ∀ d : ℤ, ch φ d = ch (θ * χ) d * ch ψ d)
    (hF : MF e (N * l) (fun d => ch ψ d * ch θ d) (eis e c₀ (ch ψ) (ch θ)))
    (hE : MF (e + 1) (N * l) (ch φ⁻¹) (eis (e + 1) c₁ (hat φ) fun _ => 1))
    (hlam : lam B c (mul (eis e c₀ (ch ψ) (ch θ)) (eis (e + 1) c₁ (hat φ) fun _ => 1)) ≠ 0) :
    ∃ c' : ℂ, MF (2 * e + 1) (N * l) (ch χ⁻¹) (mul (eis e c₀ (ch ψ) (ch θ)) (eis (e + 1) c' (fun y => ch ψ⁻¹ y * hat ⇑(θ * χ) y) fun _ => 1)) ∧
      lam B c (mul (eis e c₀ (ch ψ) (ch θ)) (eis (e + 1) c' (fun y => ch ψ⁻¹ y * hat ⇑(θ * χ) y) fun _ => 1)) ≠ 0 := by
  have hcop : N.Coprime l := (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hl).2 hlN))
  set κ : ℂ := ch (θ * χ) l * ch ψ N * hat ψ 1 with hκ
  have hhat : ∀ x, hat φ x = κ * (ch ψ⁻¹ x * hat ⇑(θ * χ) x) := by
    intro x
    rw [(GlobalTheory.T.dirichletCharFiniteFourierTransform_properties).2.1 N l (θ * χ) ψ φ hN hl.pos hcop hφ x, ((GlobalTheory.T.dirichletCharFiniteFourierTransform_properties).2.2 l ψ hl).1 hψ |>.2 x, hκ]
    ring
  have hEn : ∀ c' : ℂ, ∀ n, n ≠ 0 → (eis (e + 1) c₁ (hat φ) fun _ => 1) n = κ * (eis (e + 1) c' (fun y => ch ψ⁻¹ y * hat ⇑(θ * χ) y) fun _ => 1) n := by
    intro c' n hn
    simp only [eis, if_neg hn, Finset.mul_sum, hhat]
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  have hκ0 : κ ≠ 0 := by
    intro h0
    have hz : (eis (e + 1) c₁ (hat φ) fun _ => 1) = 0 :=
      GlobalTheory.T.modularFormCoeffSeq_eq_of_pos_coeff_eq (e + 1) (N * l) _ _ _ (by omega) (Nat.mul_pos hN hl.pos) hE (GlobalTheory.T.modularFormCoeffSeq_linear_structure (e + 1) (N * l) _).1
        (fun n hn => by rw [hEn 0 n hn, h0, zero_mul]; rfl)
    rw [hz, mul_zero_right, lam_zero] at hlam
    exact hlam rfl
  refine ⟨c₁ / κ, ?_, ?_⟩ <;>
  have hEE : (eis (e + 1) (c₁ / κ) (fun y => ch ψ⁻¹ y * hat ⇑(θ * χ) y) fun _ => 1) = κ⁻¹ • (eis (e + 1) c₁ (hat φ) fun _ => 1) := by
    funext n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [eis, div_eq_inv_mul]
    · rw [Pi.smul_apply, hEn (c₁ / κ) n hn, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hκ0, one_mul]
  · rw [hEE]
    have h1 := ((GlobalTheory.T.modularFormCoeffSeq_linear_structure (e + 1) (N * l) _).2.2.1 κ⁻¹ _ hE).1
    have h2 := GlobalTheory.T.modularFormCoeffSeq_mul_and_qExpansion.2 _ _ _ _ _ _ _ hF h1
    have hw : e + (e + 1) = 2 * e + 1 := by ring
    rw [hw] at h2
    exact (GlobalTheory.T.modularFormCoeffSeq_linear_structure (2 * e + 1) (N * l) _).2.2.2.1 _ _ (fun d hd => char_eq χ θ ψ φ hφ d hd) h2
  · rw [hEE, mul_smul_right, lam_smul]
    exact mul_ne_zero (inv_ne_zero hκ0) hlam

end GlobalTheory.DepletedValue

namespace GlobalTheory.DepletedValue

lemma ch_one_of_not_dvd {l : ℕ} (hl : l.Prime) {d : ℤ} (h : ¬ (l : ℤ) ∣ d) : ch (1 : DirichletCharacter ℂ l) d = 1 := by
  haveI : Fact l.Prime := ⟨hl⟩
  have h' : (d : ZMod l) ≠ 0 := fun h0 => h ((ZMod.intCast_zmod_eq_zero_iff_dvd d l).1 h0)
  exact MulChar.one_apply h'.isUnit

lemma good_one (e N l : ℕ) (χ θ : DirichletCharacter ℂ N) (φ : DirichletCharacter ℂ (N * l))
    (α c₀ c₁ : ℂ) (B : ℕ) (c : ℕ → ℂ) (he : 1 ≤ e) (hN : 0 < N) (hl : l.Prime) (hlN : ¬ l ∣ N) (hα0 : α ≠ 0)
    (hU : ∀ a, MF (2 * e + 1) (N * l) (ch χ⁻¹) a → lam B c (Uo l a) = α * lam B c a)
    (hθ : θ (-1) = (-1) ^ e * (1 : DirichletCharacter ℂ l) (-1)) (hχ : χ (-1) = -1) (hθχ : θ * χ ≠ 1)
    (hφ : ∀ d : ℤ, ch φ d = ch (θ * χ) d * ch (1 : DirichletCharacter ℂ l) d)
    (hF : MF e (N * l) (fun d => ch (1 : DirichletCharacter ℂ l) d * ch θ d) (eis e c₀ (ch (1 : DirichletCharacter ℂ l)) (ch θ)))
    (hE : MF (e + 1) (N * l) (ch φ⁻¹) (eis (e + 1) c₁ (hat φ) fun _ => 1))
    (hlam : lam B c (mul (eis e c₀ (ch (1 : DirichletCharacter ℂ l)) (ch θ)) (eis (e + 1) c₁ (hat φ) fun _ => 1)) ≠ 0)
    (hαχ : α ≠ (l : ℂ) ^ e * χ⁻¹ l) :
    ∃ c' : ℂ, MF (2 * e + 1) (N * l) (ch χ⁻¹) (mul (eis e c₀ (ch (1 : DirichletCharacter ℂ l)) (ch θ))
        (eis (e + 1) c' (fun y => ch (1 : DirichletCharacter ℂ l)⁻¹ y * hat ⇑(θ * χ) y) fun _ => 1)) ∧
      lam B c (mul (eis e c₀ (ch (1 : DirichletCharacter ℂ l)) (ch θ))
        (eis (e + 1) c' (fun y => ch (1 : DirichletCharacter ℂ l)⁻¹ y * hat ⇑(θ * χ) y) fun _ => 1)) ≠ 0 := by
  haveI : Fact l.Prime := ⟨hl⟩
  have hcop : N.Coprime l := (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hl).2 hlN))
  have hlZ : IsCoprime (l : ℤ) (N : ℤ) := Nat.isCoprime_iff_coprime.mpr hcop.symm
  have hNZ : IsCoprime (N : ℤ) (l : ℤ) := Nat.isCoprime_iff_coprime.mpr hcop
  set θ' := θ * χ with hθ'
  set FF := eis e c₀ (ch (1 : DirichletCharacter ℂ l)) (ch θ) with hFF
  obtain ⟨hper, htw, hz⟩ := (GlobalTheory.T.dirichletCharFiniteFourierTransform_properties).1 N θ' hN

  obtain ⟨c'', hBs⟩ := GlobalTheory.T.eisenstein_periodic_weights_isModularForm (e + 1) N 1 (hat ⇑θ') (fun _ => 1) (ch θ'⁻¹) (fun _ => 1) (by omega) hN one_pos
    (hz hθχ) hper (fun _ => rfl) (fun d hd => ⟨fun x => htw d x (by simpa using hd), fun x => by simp⟩) (by
      have h1 : ch θ (-1) = θ (-1) := by simp [ch]
      have h2 : ch χ (-1) = χ (-1) := by simp [ch]
      have h3 : (1 : DirichletCharacter ℂ l) (-1) = 1 := MulChar.one_apply isUnit_one.neg
      rw [ch_inv, ch_mul, h1, h2, hθ, hχ, h3, pow_succ]
      simp
      rw [← inv_pow, inv_neg, inv_one])
  rw [Nat.mul_one] at hBs
  set Bs := eis (e + 1) c'' (hat ⇑θ') fun _ => 1 with hBsdef
  have hBsL : MF (e + 1) (N * l) (fun d => ch θ'⁻¹ d * 1) Bs := (GlobalTheory.T.modularFormCoeffSeq_linear_structure (e + 1) N _).2.2.2.2.1 _ _ (dvd_mul_right N l) hBs
  have hVBs : MF (e + 1) (N * l) (fun d => ch θ'⁻¹ d * 1) (Vo l Bs) := (GlobalTheory.T.coeffHeckeVOperator_raises_level (e + 1) N l _ Bs hl.pos).1 hBs
  set et := ch θ'⁻¹ (l : ℤ) with het
  have hVpart : ∀ n, n ≠ 0 → eis (e + 1) c'' (fun x => if (l : ℤ) ∣ x then hat ⇑θ' x else 0) (fun _ => 1) n = et * (l : ℂ) ^ e * Vo l Bs n := by
    intro n hn
    have := (GlobalTheory.T.coeffEisensteinSeriesTwisted_heckeU_heckeV (e + 1) l c'' et (hat ⇑θ') (fun _ => 1) hl).2 (by omega) (fun x => by rw [mul_comm]; exact htw l x hlZ) n hn
    simpa using this

  have hinv : (1 : DirichletCharacter ℂ l)⁻¹ = 1 := inv_one
  have hEE : (eis (e + 1) (c'' + (-(et * (l : ℂ) ^ e)) * c'') (fun y => ch (1 : DirichletCharacter ℂ l)⁻¹ y * hat ⇑θ' y) fun _ => 1) =
      Bs + (-(et * (l : ℂ) ^ e)) • Vo l Bs := by
    funext n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [hBsdef, eis, Vo]
    · rw [Pi.add_apply, Pi.smul_apply, smul_eq_mul, neg_mul (et * (l : ℂ) ^ e) (Vo l Bs n), ← hVpart n hn, hBsdef]
      simp only [eis, if_neg hn, hinv]
      rw [← sub_eq_add_neg, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun p _ => ?_)
      by_cases h : (l : ℤ) ∣ (p.1 : ℤ)
      · simp [h, ch_dvd hl 1 h]
      · simp [h, ch_one_of_not_dvd hl h]

  have hEEmf : MF (e + 1) (N * l) (fun d => ch θ'⁻¹ d * 1) (Bs + (-(et * (l : ℂ) ^ e)) • Vo l Bs) :=
    ((GlobalTheory.T.modularFormCoeffSeq_linear_structure (e + 1) (N * l) _).2.1 _ _ hBsL ((GlobalTheory.T.modularFormCoeffSeq_linear_structure (e + 1) (N * l) _).2.2.1 _ _ hVBs).1).1

  have hprod : ∀ G, MF (e + 1) (N * l) (fun d => ch θ'⁻¹ d * 1) G → MF (2 * e + 1) (N * l) (ch χ⁻¹) (mul FF G) := by
    intro G hG
    have h2 := GlobalTheory.T.modularFormCoeffSeq_mul_and_qExpansion.2 _ _ _ _ _ _ _ hF hG
    have hw : e + (e + 1) = 2 * e + 1 := by ring
    rw [hw] at h2
    refine (GlobalTheory.T.modularFormCoeffSeq_linear_structure (2 * e + 1) (N * l) _).2.2.2.1 _ _ (fun d hd => ?_) h2
    have h1 := ch_ne_zero θ (coprime_left hd)
    have h3 := ch_ne_zero χ (coprime_left hd)
    simp only [ch_one (coprime_right hd), ch_inv, hθ', ch_mul]
    field_simp

  have hhatE : ∀ x, hat φ x = ch θ' l * (hat ⇑θ' x * ((if (l : ℤ) ∣ x then (l : ℂ) else 0) - 1)) := by
    intro x
    rw [(GlobalTheory.T.dirichletCharFiniteFourierTransform_properties).2.1 N l θ' 1 φ hN hl.pos hcop hφ x, ((GlobalTheory.T.dirichletCharFiniteFourierTransform_properties).2.2 l 1 hl).2 rfl x, ch_one hNZ, mul_one]
  have hEn : ∀ n, n ≠ 0 → (eis (e + 1) c₁ (hat φ) fun _ => 1) n =
      ((ch θ' l * (et * (l : ℂ) ^ (e + 1))) • Vo l Bs + (-ch θ' l) • Bs) n := by
    intro n hn
    have hV := hVpart n hn
    have hsplit : ((ch θ' l * (et * (l : ℂ) ^ (e + 1))) • Vo l Bs + (-ch θ' l) • Bs) n =
        ch θ' l * (l : ℂ) * eis (e + 1) c'' (fun x => if (l : ℤ) ∣ x then hat ⇑θ' x else 0) (fun _ => 1) n - ch θ' l * Bs n := by
      rw [hV, Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, pow_succ]; ring
    rw [hsplit, hBsdef]
    simp only [eis, if_neg hn, Finset.mul_sum, ← Finset.sum_sub_distrib, hhatE]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    split_ifs <;> ring
  have hRmf : MF (e + 1) (N * l) (ch φ⁻¹) ((ch θ' l * (et * (l : ℂ) ^ (e + 1))) • Vo l Bs + (-ch θ' l) • Bs) := by
    have h1 := ((GlobalTheory.T.modularFormCoeffSeq_linear_structure (e + 1) (N * l) _).2.1 _ _ ((GlobalTheory.T.modularFormCoeffSeq_linear_structure (e + 1) (N * l) _).2.2.1 (ch θ' l * (et * (l : ℂ) ^ (e + 1))) _ hVBs).1
      ((GlobalTheory.T.modularFormCoeffSeq_linear_structure (e + 1) (N * l) _).2.2.1 (-ch θ' l) _ hBsL).1).1
    refine (GlobalTheory.T.modularFormCoeffSeq_linear_structure (e + 1) (N * l) _).2.2.2.1 _ _ (fun d hd => ?_) h1
    simp only [ch_inv, hφ, ch_one (coprime_right hd), mul_one]
  have hEeq := GlobalTheory.T.modularFormCoeffSeq_eq_of_pos_coeff_eq (e + 1) (N * l) _ _ _ (by omega) (Nat.mul_pos hN hl.pos) hE hRmf hEn

  have hUFF := U_FF e N l he hN hl θ 1 c₀ hF
  have hUV : α * lam B c (mul FF (Vo l Bs)) = θ l * lam B c (mul FF Bs) := by
    rw [← hU _ (hprod _ hVBs), (GlobalTheory.T.coeffHecke_UV_cauchyProduct_identities ℂ l hl.pos).1, hUFF, mul_smul_left, lam_smul]
  have hlamE : lam B c (mul FF (eis (e + 1) c₁ (hat φ) fun _ => 1)) =
      ch θ' l * (et * (l : ℂ) ^ (e + 1)) * lam B c (mul FF (Vo l Bs)) + (-ch θ' l) * lam B c (mul FF Bs) := by
    rw [hEeq, mul_add_right, mul_smul_right, mul_smul_right, lam_add, lam_smul, lam_smul]
  have hB0 : lam B c (mul FF Bs) ≠ 0 := by
    intro h0
    have hV0 : lam B c (mul FF (Vo l Bs)) = 0 := by
      have := hUV; rw [h0, mul_zero] at this
      exact (mul_eq_zero.mp this).resolve_left hα0
    exact hlam (by rw [hlamE, hV0, h0]; ring)
  have hetθ : et * θ l = χ⁻¹ l := by
    have h1 : ch θ (l : ℤ) ≠ 0 := ch_ne_zero θ hlZ
    have h3 : ch χ (l : ℤ) ≠ 0 := ch_ne_zero χ hlZ
    have e1 : θ l = ch θ (l : ℤ) := by simp [ch]
    have e2 : χ⁻¹ l = ch χ⁻¹ (l : ℤ) := by simp [ch]
    rw [e1, e2, het, ch_inv, ch_inv, hθ', ch_mul]
    field_simp
  refine ⟨c'' + (-(et * (l : ℂ) ^ e)) * c'', ?_, ?_⟩
  · rw [hEE]; exact hprod _ hEEmf
  · rw [hEE, mul_add_right, mul_smul_right, lam_add, lam_smul]
    intro h0
    have : (α - (l : ℂ) ^ e * χ⁻¹ l) * lam B c (mul FF Bs) = 0 := by
      rw [← hetθ]
      linear_combination α * h0 + et * (l : ℂ) ^ e * hUV
    rcases mul_eq_zero.mp this with h | h
    · exact hαχ (sub_eq_zero.mp h)
    · exact hB0 h

end GlobalTheory.DepletedValue

namespace GlobalTheory.EisM

theorem val_depleted_ne_zero : ∀ (e N l : ℕ) (χ θ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ l) (φ : DirichletCharacter ℂ (N * l)) (t : ℕ → ℂ) (α c₀ c₁ : ℂ) (B : ℕ) (c : ℕ → ℂ), 1 ≤ e → 0 < N → l.Prime → ¬ l ∣ N → α ≠ 0 → EigF (2 * e + 1) N l χ⁻¹ t α B c → θ (-1) = (-1) ^ e * ψ (-1) → χ (-1) = -1 → θ * χ ≠ 1 → (∀ d : ℤ, ch φ d = ch (θ * χ) d * ch ψ d) → MF e (N * l) (fun d => ch ψ d * ch θ d) (eis e c₀ (ch ψ) (ch θ)) → MF (e + 1) (N * l) (ch φ⁻¹) (eis (e + 1) c₁ (hat φ) fun _ => 1) → lam B c (mul (eis e c₀ (ch ψ) (ch θ)) (eis (e + 1) c₁ (hat φ) fun _ => 1)) ≠ 0 → α ≠ θ l → α ≠ (l : ℂ) ^ e * χ⁻¹ l → val B c l α 1 (Zs (2 * e + 1) l (ch θ) (hat ⇑(θ * χ)) (fun x y => ψ x * ψ⁻¹ y * ((y : ℂ) / x) ^ e)) ≠ 0 := by
  intro e N l χ θ ψ φ t α c₀ c₁ B c he hN hl hlN hα0 hEig hθ hχ hθχ hφ hF hE hlam hαθ hαχ
  obtain ⟨c', hmf, hne⟩ : ∃ c' : ℂ, MF (2 * e + 1) (N * l) (ch χ⁻¹) (mul (eis e c₀ (ch ψ) (ch θ)) (eis (e + 1) c' (fun y => ch ψ⁻¹ y * hat ⇑(θ * χ) y) fun _ => 1)) ∧
      lam B c (mul (eis e c₀ (ch ψ) (ch θ)) (eis (e + 1) c' (fun y => ch ψ⁻¹ y * hat ⇑(θ * χ) y) fun _ => 1)) ≠ 0 := by
    rcases eq_or_ne ψ 1 with rfl | hψ
    · exact GlobalTheory.DepletedValue.good_one e N l χ θ φ α c₀ c₁ B c he hN hl hlN hα0 hEig.U hθ hχ hθχ hφ hF hE hlam hαχ
    · exact GlobalTheory.DepletedValue.good_ne e N l χ θ ψ φ c₀ c₁ B c he hN hl hlN hψ hφ hF hE hlam
  rw [GlobalTheory.DepletedValue.zs_eq e l he θ χ ψ c₀ c']
  exact GlobalTheory.DepletedValue.core hl.pos B c α (θ l) _ _ (GlobalTheory.DepletedValue.U_FF e N l he hN hl θ ψ c₀ hF) (GlobalTheory.DepletedValue.U_EE e N l hl (θ * χ) ψ c')
    (hEig.U _ hmf) hne hαθ hα0

end GlobalTheory.EisM
