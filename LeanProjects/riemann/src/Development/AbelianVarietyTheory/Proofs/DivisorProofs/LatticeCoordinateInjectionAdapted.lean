import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped GlobalTheory.VacAny

namespace GlobalTheory.VacResNonvan

theorem hTens_vecMulVec_gen {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E)
    {α β : Type} [Fintype α] [Fintype β] (JA : Matrix α α E) (JB : Matrix β β E) (x x' : α → E) (y y' : β → E) :
    GlobalTheory.WeilM.hTens c JA JB (Matrix.vecMulVec x y) (Matrix.vecMulVec x' y') =
      (∑ i : α, ∑ k : α, x i * JA i k * c (x' k)) * (∑ j : β, ∑ l : β, y j * JB j l * c (y' l)) := by
  unfold GlobalTheory.WeilM.hTens
  simp_rw [Finset.sum_mul_sum]
  simp only [Matrix.vecMulVec_apply, map_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem symp_vecMulVec_self_eq_zero (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E]
    (σ : E →ₐ[F] E) {n d : ℕ} (J : Matrix (Fin n) (Fin n) E) (JW : Matrix (Fin d) (Fin d) E) (ξ : AE F E)
    (x : Fin n → E) (hx : form σ J x x = 0) (a b : Fin d → AE F E) :
    symp (R := AF F) (cA σ) ξ (incM F J) (incM F JW) (Matrix.vecMulVec (incV F x) a)
      (Matrix.vecMulVec (incV F x) b) = 0 := by
  have hc : ∀ e : E, cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := fun e => rfl
  have h0 : (∑ i, ∑ k, incV F x i * incM F J i k * cA σ (incV F x k)) = 0 := by
    have e : (∑ i, ∑ k, incV F x i * incM F J i k * cA σ (incV F x k)) =
        inclR (F := F) (AF F) (form σ J x x) := by
      simp only [form, dotProduct, Matrix.mulVec, incV, incM, Matrix.map_apply, hc, map_sum, map_mul,
        Finset.mul_sum, mul_assoc]
    rw [e, hx, map_zero]
  rw [GlobalTheory.WeilM.symp, hTens_vecMulVec_gen, h0, zero_mul, mul_zero, map_zero]

end GlobalTheory.VacResNonvan

open GlobalTheory.VacResNonvan in

theorem GlobalTheory.VacResNonvan.nonvan : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d n₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ) (M₁ : Model σ X₁ W),
    H.IsAdapted σ B X X₁ j₀ j₁ →
    ∀ (j : Fin n₁ × Fin d → Fin n × Fin d) (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J)) (Fin n × Fin d)),
      Function.Injective j →
      (∀ z, co.e (incM F H.ι * z) = (Function.extend j (M₁.co.e z).1 0, Function.extend j (M₁.co.e z).2 0)) →
      (∀ z, (co.e (Matrix.vecMulVec (incV F H.x) z)).1 = 0 ∧ ∀ k, (co.e (Matrix.vecMulVec (incV F H.x) z)).2 (j k) = 0) →
      (∀ z, (co.e (Matrix.vecMulVec (incV F H.y) z)).2 = 0 ∧ ∀ k, (co.e (Matrix.vecMulVec (incV F H.y) z)).1 (j k) = 0) →
      ∀ (v : Pl F),
      (∀ γ ∈ latAtV X W v, ∃ (a b : Fin d → AE F E) (z : Matrix (Fin n₁) (Fin d) (AE F E)), z ∈ latAtV X₁ W v ∧
        Matrix.vecMulVec (incV F H.x) a ∈ latAtV X W v ∧ Matrix.vecMulVec (incV F H.y) b ∈ latAtV X W v ∧
        γ = Matrix.vecMulVec (incV F H.x) a + incM F H.ι * z + Matrix.vecMulVec (incV F H.y) b) →
      (∀ w : (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v),
        (∀ γ ∈ latAtV X W v, GlobalTheory.LatVac.psiAt B.ψ v ((GlobalTheory.LatVac.locCo co v γ).1 ⬝ᵥ w.2 - w.1 ⬝ᵥ (GlobalTheory.LatVac.locCo co v γ).2) = 1) →
        w ∈ (latAtV X W v).map (GlobalTheory.LatVac.locCo co v)) →
      ∀ (φ : (Fin n × Fin d → Fv F v) → ℂ) (θ : 𝓞 E),
        (∀ γ ∈ latAtV X W v, schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo co v γ) φ =
          B.ψ (⅟(2 : AF F) * symp (R := AF F) (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F X.J) (incM F W.J) γ γ) • φ) →
        ∀ x, φ x ≠ 0 → φ (Function.extend j (x ∘ j) 0) ≠ 0 := by
  intro F E _ _ _ _ _ σ B n d n₁ X W X₁ H j₀ j₁ M₁ hAd j co hj hι hx hy v hdec hdual φ θ heig x hx0
  have hlc : ∀ γ, GlobalTheory.LatVac.locCo co v γ =
      (fun k => evFin F v ((co.e γ).1 k), fun k => evFin F v ((co.e γ).2 k)) := fun γ => rfl
  have htw : ∀ γ ∈ latAtV X W v, symp (R := AF F) (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F X.J)
      (incM F W.J) γ γ = 0 → schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo co v γ) φ = φ := by
    intro γ hγ h0
    rw [heig γ hγ, h0, mul_zero, AddChar.map_zero_eq_one, one_smul]
  set x' : Fin n × Fin d → Fv F v := Function.extend j (x ∘ j) 0 with hx'
  set t := x - x' with ht
  have hx'j : ∀ k, x' (j k) = x (j k) := fun k => by rw [hx', hj.extend_apply]; rfl
  have hx'o : ∀ k, (¬ ∃ k', j k' = k) → x' k = 0 := fun k hk => by
    rw [hx', Function.extend_apply' _ _ _ hk]; rfl
  have htj : ∀ k, t (j k) = 0 := fun k => by rw [ht, Pi.sub_apply, hx'j, sub_self]
  have hA : ∀ a, Matrix.vecMulVec (incV F H.x) a ∈ latAtV X W v →
      GlobalTheory.LatVac.psiAt B.ψ v (x ⬝ᵥ (GlobalTheory.LatVac.locCo co v (Matrix.vecMulVec (incV F H.x) a)).2) = 1 := by
    intro a ha
    have e := congrFun (htw _ ha (symp_vecMulVec_self_eq_zero F E σ X.J W.J _ H.x hAd.xx a a)) x
    have h1 : (GlobalTheory.LatVac.locCo co v (Matrix.vecMulVec (incV F H.x) a)).1 = 0 := by
      funext k; rw [hlc]; simp [(hx a).1]
    simp only [schr, h1, zero_dotProduct, mul_zero, add_zero] at e
    exact (mul_eq_right₀ hx0).1 e
  have hw : (t, (0 : Fin n × Fin d → Fv F v)) ∈ (latAtV X W v).map (GlobalTheory.LatVac.locCo co v) := by
    apply hdual
    intro γ hγ
    obtain ⟨a, b, z, hz, ha, hb, rfl⟩ := hdec γ hγ
    have e1 : t ⬝ᵥ (GlobalTheory.LatVac.locCo co v (Matrix.vecMulVec (incV F H.y) b)).2 = 0 := by
      rw [hlc]; simp [(hy b).1]
    have e2 : t ⬝ᵥ (GlobalTheory.LatVac.locCo co v (incM F H.ι * z)).2 = 0 := by
      rw [hlc, hι z]
      simp only [dotProduct]
      apply Finset.sum_eq_zero
      intro k _
      by_cases hk : ∃ k', j k' = k
      · obtain ⟨k', rfl⟩ := hk; rw [htj, zero_mul]
      · simp [Function.extend_apply' _ _ _ hk]
    have e3 : t ⬝ᵥ (GlobalTheory.LatVac.locCo co v (Matrix.vecMulVec (incV F H.x) a)).2 =
        x ⬝ᵥ (GlobalTheory.LatVac.locCo co v (Matrix.vecMulVec (incV F H.x) a)).2 := by
      rw [ht, sub_dotProduct, sub_eq_self]
      simp only [dotProduct]
      apply Finset.sum_eq_zero
      intro k _
      by_cases hk : ∃ k', j k' = k
      · obtain ⟨k', rfl⟩ := hk; rw [hlc]; simp [(hx a).2 k']
      · rw [hx'o k hk, zero_mul]
    rw [map_add, map_add, Prod.snd_add, Prod.snd_add, dotProduct_add, dotProduct_add, e1, e2, e3,
      add_zero, add_zero, dotProduct_zero, zero_sub]
    have h1 := hA a ha
    have h2 := AddChar.map_add_eq_mul (GlobalTheory.LatVac.psiAt B.ψ v)
      (-(x ⬝ᵥ (GlobalTheory.LatVac.locCo co v (Matrix.vecMulVec (incV F H.x) a)).2))
      (x ⬝ᵥ (GlobalTheory.LatVac.locCo co v (Matrix.vecMulVec (incV F H.x) a)).2)
    rw [neg_add_cancel, AddChar.map_zero_eq_one, h1, mul_one] at h2
    exact h2.symm
  obtain ⟨γ₀, hγ₀, hγ₀e⟩ := AddSubgroup.mem_map.1 hw
  obtain ⟨a, b, z, hz, ha, hb, rfl⟩ := hdec γ₀ hγ₀
  have hC : GlobalTheory.LatVac.locCo co v (Matrix.vecMulVec (incV F H.y) b) = (t, 0) := by
    refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
    · have e := congrFun (congrArg Prod.fst hγ₀e) k
      rw [map_add, map_add] at e
      simp only [Prod.fst_add, Pi.add_apply] at e
      by_cases hk : ∃ k', j k' = k
      · obtain ⟨k', rfl⟩ := hk
        change _ = t (j k')
        rw [htj, hlc]; simp [(hy b).2 k']
      · change _ = t k
        rw [← e, hlc, hlc, hlc, hι z]
        simp [(hx a).1, Function.extend_apply' _ _ _ hk]
    · rw [hlc]; simp [(hy b).1]
  have e := congrFun (htw _ hb (symp_vecMulVec_self_eq_zero F E σ X.J W.J _ H.y hAd.yy b b)) x'
  rw [hC] at e
  simp only [schr, dotProduct_zero, mul_zero, add_zero, AddChar.map_zero_eq_one, one_mul] at e
  have hxt : x' + t = x := by rw [ht]; abel
  rw [hxt] at e
  rw [← e]
  exact hx0
