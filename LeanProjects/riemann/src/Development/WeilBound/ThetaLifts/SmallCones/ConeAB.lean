import Development.WeilBound.ThetaLifts.SmallCones.ThetaUniq
import Development.WeilBound.ThetaLifts.SmallCones.ConeCore
import Development.WeilBound.ThetaLifts.SmallCones.ConeLawAB

set_option linter.unusedSectionVars false

noncomputable section

namespace PositivityTheory.ThKCT

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKEst PositivityTheory.ThKG PositivityTheory.ThKG.Tow
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem domSo (hS : SoSemi) (hV : FinVolU) (hE : EpsOf) {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {B : Base F E} {M : Model σ X W}
    {χX χW om r s r' s'} (hp : IsPair B M χX χW om r s r' s') : Dom M om (soFin B M) := by
  intro φ hφ
  obtain ⟨p, k, hc, h⟩ := hS F E σ B n d X W M χX χW om r s r' s' hp φ hφ 0
  refine ⟨p, k, fun _ => 1, hc, measurable_const, ?_, fun f g y => ?_⟩
  · rw [setLIntegral_one]
    exact hV F E σ hp.base.cm n X.J (hE F E σ B hp.base n X r s (Or.inl hp.herm)).1 M.μ M.dom hp.good.haar hp.good.dom
  · rw [mul_one, ← ofReal_norm_eq_enorm]
    exact ENNReal.ofReal_le_ofReal (by simpa using h f g y)

theorem incM_vecMulVec {n d : ℕ} (x : Fin n → E) (y : Fin d → E) :
    incM F (Matrix.vecMulVec x y) = Matrix.vecMulVec (incV F x) (incV F y) := by
  ext i j
  simp [incM, incV, Matrix.vecMulVec_apply]

theorem hTens_vec {n d : ℕ} (J : Matrix (Fin n) (Fin n) E) (J' : Matrix (Fin d) (Fin d) E) (x x' : Fin n → E) (y y' : Fin d → E) :
    hTens (cA σ) (incM F J) (incM F J') (incM F (Matrix.vecMulVec x y)) (incM F (Matrix.vecMulVec x' y')) =
      inclR (F := F) (AF F) (form σ J x x' * form σ J' y y') := by
  have hc : ∀ a : E, cA σ (inclR (F := F) (AF F) a) = inclR (F := F) (AF F) (σ a) := fun a => by simp [cA, inclR]
  simp only [hTens, incM, Matrix.map_apply, Matrix.vecMulVec_apply, hc, ← map_mul, ← map_sum, form, dotProduct, Matrix.mulVec]
  congr 1
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm, Finset.mul_sum _ _ (x i), Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by rw [map_mul]; ring

theorem form_swap (hσ : IsCMExt F E σ) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {ε : E} (h : ∀ i j, σ (J j i) = ε * J i j)
    (x y : Fin n → E) : σ (form σ J x y) = ε * form σ J y x := by
  simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, cm_conj_conj hσ, Finset.mul_sum, h]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem coneA_of (hUn : Unfold) (hU : UnipEx) (hD : StabDec) (hTB : ThetaBasic) (hG : GrpTop) (hE : EpsOf) (hA : EvAdm)
    (hM : MixAB) (hL : LineInt) (hW : DomWeil) : ConeA := by
  intro F E _ _ _ _ _ σ B n d n₁ d₁ X W X₁ W₁ H H' j₀ j₁ i₀ i₁ r s r' s' M M₀ hH hH' e he z hz K μK μ hI hμK hμ
  obtain ⟨κ, hκ, h⟩ := cone_core hUn hU hD hTB hG hE hA (r := r + 1) (s := s + 1) (r' := r' + 1) (s' := s' + 1) (r₀ := r) (s₀ := s)
    (r₀' := r') (s₀' := s') hH hH' he hI hμK hμ (shiftA H H') z _ (Or.inr rfl)
  refine ⟨κ, hκ, fun χX χW om om₀ hp hp₀ Φ hΦ hK => ?_⟩
  have hν : Continuous (χW⁻¹ : Chr F E) := hp.hW.1.inv
  have hyx : form σ X.J H.y H.x = 1 := by
    have := form_swap hp.base.cm (J := X.J) (ε := 1) (fun i j => by rw [one_mul, hp.herm.herm]) H.x H.y
    rw [hH.xy, map_one, one_mul] at this
    exact this.symm
  have key := fun Ψ hΨ => hL F E σ B n d n₁ d₁ X W X₁ W₁ M M₀ hp.base hp.good hp₀.good _ _ _ e he
    (Matrix.vecMulVec H.x H'.y) (Matrix.vecMulVec H.y H'.x)
    (fun a => Or.inl ⟨a • incV F H.y, by rw [incM_vecMulVec, Matrix.smul_vecMulVec]⟩)
    (by rw [hTens_vec, hyx, hH'.xy, mul_one, map_one]; exact isUnit_one) (AlgHom.id _ _) (Or.inl rfl) μ hμ z χW⁻¹ (by omega) hν Ψ hΨ
  simp only [incM_vecMulVec, AlgHom.id_apply] at key
  have h1 := hH.rank
  have h2 := hH'.rank
  exact h χX χW om om₀ hp hp₀ χW⁻¹ (χX / χW) (schA F _) hν
    (lawsA hp ((hM F E σ B n d n₁ d₁ X W X₁ W₁ H H' j₀ j₁ i₀ i₁ r s r' s' M M₀ hH hH' χX χW om om₀ hp hp₀).1 e he) hz.1 h2
      fun m hm => ((hU F E σ B n n₁ X X₁ H j₀ j₁ _ _ hp.base (Or.inl hp.herm) hH).2.2.2.2.2.1 m hm).1)
    (fun _ h => h) (fun x Ψ h => pair_pres hp x h)
    (fun Ψ hΨ h₁ => (key Ψ hΨ).1 om₀ (fun x Φ h => pair_pres hp₀ x h)
      (Or.inl (hW F E σ B _ _ X₁ W₁ M₀ χX χW om₀ r s r' s' hp₀ (Or.inl (by omega)))) h₁)
    (fun Ψ hΨ => (key Ψ hΨ).2) Φ hΦ hK

theorem coneB_of (hUn : Unfold) (hU : UnipEx) (hD : StabDec) (hTB : ThetaBasic) (hG : GrpTop) (hE : EpsOf) (hA : EvAdm)
    (hM : MixAB) (hL : LineInt) (hS : SoSemi) (hV : FinVolU) (hSF : SoFin) (hSt : SoStab) (hSe : SoEv) : ConeB := by
  intro F E _ _ _ _ _ σ B n d n₁ d₁ X W X₁ W₁ H H' j₀ j₁ i₀ i₁ r s r' s' M M₀ hH hH' e he z hz K μK μ hI hμK hμ
  obtain ⟨κ, hκ, h⟩ := cone_core hUn hU hD hTB hG hE hA (r := r + 1) (s := s + 1) (r' := r' + 1) (s' := s' + 1) (r₀ := r) (s₀ := s)
    (r₀' := r') (s₀' := s') hH hH' he hI hμK hμ (shiftB σ H H') z _ (Or.inl rfl)
  refine ⟨κ, hκ, fun χX χW om om₀ hp hp₀ Φ hΦ hK => ?_⟩
  have hyx : form σ W.J H'.y H'.x = -1 := by
    have := form_swap hp.base.cm (J := W.J) (ε := -1) (fun i j => by rw [neg_one_mul, hp.skew.skew]) H'.x H'.y
    rw [hH'.xy, map_one, neg_one_mul] at this
    rw [this, neg_neg]
  have key := fun Ψ hΨ => hL F E σ B n d n₁ d₁ X W X₁ W₁ M M₀ hp.base hp.good hp₀.good _ _ _ e he
    (Matrix.vecMulVec H.y H'.x) (Matrix.vecMulVec H.x H'.y)
    (fun a => Or.inl ⟨a • incV F H'.y, by rw [incM_vecMulVec, Matrix.vecMulVec_smul]⟩)
    (by rw [hTens_vec, hyx, hH.xy, one_mul, map_neg, map_one]; exact isUnit_one.neg) (cA σ) (Or.inr rfl) μ hμ z χW hz.2 hp.hW.1 Ψ hΨ
  have hle := (hSF F E σ B n d X W M χX χW om _ _ _ _ hp).2.2.1
  have hso := fun Ψ hΨ => (hSe F E σ B n d n₁ d₁ X W X₁ W₁ H H' j₀ j₁ i₀ i₁ _ _ _ _ M M₀ hH hH' hp.base hp.herm hp.skew hp.good
    hp₀.good e he Ψ hΨ).2
  simp only [incM_vecMulVec] at key hso
  exact h χX χW om om₀ hp hp₀ χW (χX / χW) (M.So B.ψ B.τ₁) hp.hW.1
    (lawsB hp he ((hM F E σ B n d n₁ d₁ X W X₁ W₁ H H' j₀ j₁ i₀ i₁ r s r' s' M M₀ hH hH' χX χW om om₀ hp hp₀).2 e he) hz.1 hH.rank
      hH'.xx fun m hm => ((hU F E σ B n n₁ X X₁ H j₀ j₁ _ _ hp.base (Or.inl hp.herm) hH).2.2.2.2.2.1 m hm).2)
    hle (hSt F E σ B n d X W M χX χW om _ _ _ _ hp)
    (fun Ψ hΨ h₁ => (key Ψ (hle Ψ hΨ)).1 om₀ (fun x Φ h => pair_pres hp₀ x h) (Or.inr ⟨domSo hS hV hE hp₀, hso Ψ hΨ⟩) h₁)
    (fun Ψ hΨ => (key Ψ hΨ).2) Φ hΦ hK

end PositivityTheory.ThKCT

end
