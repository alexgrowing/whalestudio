import Development.WeilBound.ThetaLifts.SmallCones.ThetaUniq
import Development.WeilBound.ThetaLifts.SmallCones.ConeLaw
import Development.WeilBound.ThetaLifts.SmallCones.ExpAlg

set_option linter.unusedSectionVars false

noncomputable section

namespace PositivityTheory.ThKCT

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKEst PositivityTheory.ThKG PositivityTheory.ThKG.Tow
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem cA_cA (hσ : IsCMExt F E σ) (x : AE F E) : cA σ (cA σ x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a y => simp [cA, cm_conj_conj hσ]
  | add a b ha hb => simp [ha, hb]

theorem chi_conj (hσ : IsCMExt F E σ) {χ : Chr F E} {k : ℕ}
    (h : ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ k) (t : (AE F E)ˣ) :
    χ (GlobalTheory.Doubling.conjUnit σ t) = (χ t)⁻¹ := by
  have h1 := h (Units.map (Algebra.norm (AF F) : AE F E →* AF F) t)
  rw [if_pos (Subgroup.mem_sup_right (MonoidHom.mem_range.mpr ⟨t, rfl⟩)), Circle.coe_eq_one,
    show Units.map (algebraMap (AF F) (AE F E) : AF F →* AE F E) (Units.map (Algebra.norm (AF F) : AE F E →* AF F) t) =
      t * GlobalTheory.Doubling.conjUnit σ t from Units.ext (GlobalTheory.Doubling.algebraMap_norm_eq hσ (R := AF F) t.1), map_mul] at h1
  exact eq_inv_of_mul_eq_one_right h1

theorem conjUnit_val (t : (AE F E)ˣ) : (GlobalTheory.Doubling.conjUnit σ t : (AE F E)ˣ).1 = cA σ t.1 := rfl

section

variable {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁} {B : Base F E} {M : Model σ X W}
  {om : Rep σ X W} {om₀ : Rep σ X₁ W₁} {H : Plane E n n₁} {H' : Plane E d d₁} {e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁} {χX χW : Chr F E}
  {r s r' s' : ℕ} {rX rW : ℝ}

theorem isLevi_inv' {t h₁ p} (h : IsLevi (σ := σ) (W := W) (W₁ := W₁) H' t h₁ p) :
    mat p⁻¹ *ᵥ incV F H'.x = (t⁻¹ : (AE F E)ˣ).1 • incV F H'.x :=
  mat_inv_mulVec p (by rw [Matrix.mulVec_smul, h.1, smul_smul, Units.inv_mul, one_smul])

theorem levi_inv_y {t h₁ p} (h : IsLevi (σ := σ) (W := W) (W₁ := W₁) H' t h₁ p) :
    mat p⁻¹ *ᵥ incV F H'.y = cA σ t.1 • incV F H'.y :=
  mat_inv_mulVec p (by rw [Matrix.mulVec_smul, h.2.1, smul_smul, ← map_mul, Units.mul_inv, map_one, one_smul])

theorem Mix2.levi (h : Mix2 H H' χX χW rX rW om om₀ e) {t g₁ p t' h₁ p'} (h1 : IsLevi H t g₁ p) (h2 : IsLevi H' t' h₁ p') {Φ}
    (hΦ : Φ ∈ schA F (Fin n × Fin d)) : e (om (p, p') Φ) = ((χW t : ℂ) * (((absE F E t : ℝ) ^ rX : ℝ) : ℂ) *
      ((χX t' : ℂ) * (((absE F E t' : ℝ) ^ rW : ℝ) : ℂ))) • om₀ (g₁, h₁) (e Φ) := by
  simpa using h t g₁ p h1 1 (one_mem _) t' h₁ p' h2 1 (one_mem _) Φ hΦ

theorem Mix2.uni (h : Mix2 H H' χX χW rX rW om om₀ e) {m} (hm : m ∈ unip σ X H) {Φ} (hΦ : Φ ∈ schA F (Fin n × Fin d)) :
    e (om (m, 1) Φ) = e Φ := by
  simpa [← Prod.one_eq_mk] using h 1 1 1 (levi_one H) m hm 1 1 1 (levi_one H') 1 (one_mem _) Φ hΦ

theorem rpow_c {a : ℝ} (ha : 0 < a) (x y : ℝ) : ((a ^ x : ℝ) : ℂ) * ((a ^ y : ℝ) : ℂ) = ((a ^ (x + y) : ℝ) : ℂ) := by
  rw [Real.rpow_add ha, Complex.ofReal_mul]

theorem lawsTA (hp : IsPair B M χX χW om r s r' s') (hM : Mix2 H H' χX χW ((d₁ : ℝ) / 2) ((n : ℝ) / 2) om om₀ e)
    (hx : ∀ m ∈ unip σ X H, mat m *ᵥ incV F H.x = incV F H.x) :
    LawsT B M om om₀ H H' e (shiftA H H') (fun l => (χW⁻¹ l : ℂ) * (((absE F E l : ℝ) ^ ((n : ℝ) - 1 - d₁ / 2) : ℝ) : ℂ))
      fun l => l⁻¹ := by
  have hs := fun w Ψ h => rho_mem M hp.base.std w (Φ := Ψ) h
  refine ⟨inv_one, by simp, fun m hm Ψ hΨ => ?_, fun l g₁ p h₁ p' h1 h2 Ψ hΨ => ?_⟩
  · unfold shiftA
    rw [rho_om hp _ _ _ _ _ hΨ, hM.uni hm (hs _ _ hΨ), mat_inv_mulVec m (hx m hm), inv_one, mat_one', Matrix.one_mulVec]
  · unfold shiftA
    rw [rho_om hp _ _ _ _ _ hΨ, hM.levi h1 h2 (hs _ _ hΨ), isLevi_inv' h1, levi_inv_y h2, smul_smul]
    simp only [inv_inv, Units.val_one, map_one, one_smul, Matrix.smul_vecMulVec, NNReal.coe_one, Real.one_rpow, Circle.coe_one,
      Complex.ofReal_one, mul_one, map_inv, MonoidHom.inv_apply]
    congr 1
    have ha := absE_pos (F := F) l
    rw [mul_left_comm, NNReal.coe_inv, rpow_c (inv_pos.2 ha), Real.inv_rpow ha.le, ← Real.rpow_neg ha.le]
    congr 3
    ring

theorem lawsA (hp : IsPair B M χX χW om r s r' s') (hM : Mix2 H H' χX χW ((d₁ : ℝ) / 2) ((n : ℝ) / 2) om om₀ e) {z : ℕ}
    (hz : 2 * n = d + 2 * z) (hd : d = d₁ + 2) (hx : ∀ m ∈ unip σ X H, mat m *ᵥ incV F H.x = incV F H.x) :
    Laws B M om om₀ H H' e (shiftA H H') χW⁻¹ (χX / χW) z fun l => l⁻¹ := by
  have hs := fun w Ψ h => rho_mem M hp.base.std w (Φ := Ψ) h
  have hd' : (d : ℝ) = d₁ + 2 := by exact_mod_cast hd
  have hz' : (2 * n : ℝ) = d + 2 * z := by exact_mod_cast hz
  refine ⟨?_, fun t h₁ p' h2 => ⟨GlobalTheory.Doubling.conjUnit σ t, fun l Ψ hΨ => ?_⟩⟩
  · convert lawsTA hp hM hx using 3 with l
    rw [← Complex.ofReal_pow, ← Real.rpow_natCast]
    congr 2
    linarith
  · unfold shiftA
    rw [rho_om hp _ _ _ _ _ hΨ, hM.levi (levi_one H) h2 (hs _ _ hΨ), levi_inv_y h2, inv_one, mat_one', Matrix.one_mulVec,
      Matrix.vecMulVec_smul, smul_smul, Units.val_mul, conjUnit_val]
    congr 1
    have ha := absE_pos (F := F) t
    simp only [map_one, NNReal.coe_one, Real.one_rpow, Circle.coe_one, Complex.ofReal_one, mul_one, one_mul, MonoidHom.inv_apply,
      chi_conj hp.base.cm hp.resW, inv_inv, GlobalTheory.Doubling.absE_conjUnit, MonoidHom.div_apply, Circle.coe_div]
    rw [← Complex.ofReal_pow, ← Real.rpow_natCast, show (n : ℝ) / 2 = (d - n) / 2 + z by linarith, ← rpow_c ha]
    field_simp

theorem sy_iso (hx : form σ W.J H'.x H'.x = 0) (a b : Fin n → AE F E) :
    sy σ X W (Matrix.vecMulVec a (incV F H'.x)) (Matrix.vecMulVec b (incV F H'.x)) = 0 := by
  have h0 : ∑ j, ∑ l, incV F H'.x j * incM F W.J j l * cA σ (incV F H'.x l) = 0 := by
    have := congrArg (inclR (F := F) (AF F)) hx
    simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, Finset.mul_sum, map_zero] at this
    simpa [incV, incM, cA, inclR, mul_assoc] using this
  have : hTens (cA σ) (incM F X.J) (incM F W.J) (Matrix.vecMulVec a (incV F H'.x)) (Matrix.vecMulVec b (incV F H'.x)) = 0 := by
    calc _ = ∑ i, ∑ k, a i * incM F X.J i k * cA σ (b k) * ∑ j, ∑ l, incV F H'.x j * incM F W.J j l * cA σ (incV F H'.x l) := by
          simp only [hTens, Matrix.vecMulVec_apply, map_mul, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by ring
      _ = 0 := by simp [h0]
  simp only [sy, symp, this, mul_zero, map_zero]

theorem lawsB {M₀ : Model σ X₁ W₁} (hp : IsPair B M χX χW om r s r' s') (he : IsEv B M M₀ H.ι H'.ι (isoB H H') e)
    (hM : Mix2 H H' χX χW ((d : ℝ) / 2) ((n₁ : ℝ) / 2) om om₀ e) {z : ℕ}
    (hz : d + 2 = 2 * n + 2 * z) (hn : n = n₁ + 2) (hxx : form σ W.J H'.x H'.x = 0)
    (hy : ∀ m ∈ unip σ X H, ∃ (y : Fin n₁ → AE F E) (c : AE F E),
      mat m *ᵥ incV F H.y = incV F H.y + incM F H.ι *ᵥ y + c • incV F H.x) :
    Laws B M om om₀ H H' e (shiftB σ H H') χW (χX / χW) z id := by
  have hs := fun w Ψ h => rho_mem M hp.base.std w (Φ := Ψ) h
  have hz' : (d : ℝ) + 2 = 2 * n + 2 * z := by exact_mod_cast hz
  have hn' : (n : ℝ) = n₁ + 2 := by exact_mod_cast hn
  refine ⟨⟨rfl, by simp, fun m hm Ψ hΨ => ?_, fun l g₁ p h₁ p' h1 h2 Ψ hΨ => ?_⟩,
    fun t h₁ p' h2 => ⟨(GlobalTheory.Doubling.conjUnit σ t)⁻¹, fun l Ψ hΨ => ?_⟩⟩
  · unfold shiftB
    obtain ⟨y, c, hy'⟩ := hy m⁻¹ (inv_mem hm)
    rw [rho_om hp _ _ _ _ _ hΨ, hM.uni hm (hs _ _ hΨ), hy', inv_one, mat_one', Matrix.one_mulVec, Units.val_one, map_one, one_smul,
      one_smul, Matrix.add_vecMulVec, Matrix.add_vecMulVec, add_comm, ← rho_rho_of M.co B.ψ _ _ (by
        rw [← Matrix.add_vecMulVec]; exact sy_iso hxx _ _), he.inv _ (Or.inl ⟨c • incV F H'.x, by
        rw [Matrix.smul_vecMulVec, Matrix.vecMulVec_smul]⟩) _ (hs _ _ hΨ), add_comm, ← rho_rho_of M.co B.ψ _ _ (sy_iso hxx _ _),
      he.inv _ (Or.inr ⟨y, rfl⟩) _ (hs _ _ hΨ)]
  · unfold shiftB
    rw [rho_om hp _ _ _ _ _ hΨ, hM.levi h1 h2 (hs _ _ hΨ), levi_inv_y h1, isLevi_inv' h2, smul_smul]
    simp only [id, inv_one, Units.val_one, map_one, one_smul, Matrix.smul_vecMulVec, NNReal.coe_one, Real.one_rpow, Circle.coe_one,
      Complex.ofReal_one, mul_one]
    congr 1
    have ha := absE_pos (F := F) l
    rw [mul_left_comm, rpow_c ha, ← Complex.ofReal_pow, ← Real.rpow_natCast]
    congr 3
    linarith
  · unfold shiftB
    have hc : cA σ (l * (GlobalTheory.Doubling.conjUnit σ t)⁻¹ : (AE F E)ˣ).1 = cA σ l.1 * (t⁻¹ : (AE F E)ˣ).1 := by
      rw [Units.val_mul, map_mul, ← map_inv, conjUnit_val, cA_cA hp.base.cm]
    rw [rho_om hp _ _ _ _ _ hΨ, hM.levi (levi_one H) h2 (hs _ _ hΨ), isLevi_inv' h2, inv_one, mat_one', Matrix.one_mulVec,
      Matrix.vecMulVec_smul, smul_smul, hc]
    congr 1
    have ha := absE_pos (F := F) t
    simp only [map_one, NNReal.coe_one, Real.one_rpow, Circle.coe_one, Complex.ofReal_one, mul_one, one_mul, map_inv,
      chi_conj hp.base.cm hp.resW, inv_inv, GlobalTheory.Doubling.absE_conjUnit, MonoidHom.div_apply, Circle.coe_div, NNReal.coe_inv]
    rw [← Complex.ofReal_pow, ← Real.rpow_natCast, Real.inv_rpow ha.le, ← Real.rpow_neg ha.le,
      show (n₁ : ℝ) / 2 = (d - n) / 2 + -z by linarith, ← rpow_c ha]
    field_simp

end

end PositivityTheory.ThKCT

end
