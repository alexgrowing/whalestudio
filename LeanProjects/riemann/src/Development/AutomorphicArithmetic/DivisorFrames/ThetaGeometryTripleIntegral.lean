import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingConfigurationLeviIntegralImports
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorusUOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAStabilizerThetaFinite
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.ConeSmallUnf

section SlopeTestRemainingChoices

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

private theorem eventually_rho_om_eq_pair {B : Base F E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (hB : B.IsGood σ)
    {C : Set (UA σ X.J × UA σ W.J)} (hCc : IsCompact C) (M : Model σ X W) {χ χ' : Chr F E}
    {om : Rep σ X W} (hom : M.IsWeil B.ψ χ χ' om) {Φ : Fn F n d} (hΦ : Φ ∈ schA F _) :
    ∀ᶠ u in 𝓝 (0 : Matrix (Fin n) (Fin d) (AE F E)), GlobalTheory.XTermFinParts.infOne F • u = 0 →
      ∀ p ∈ C, M.co.rho B.ψ u (om p Φ) = om p Φ := by
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) (AE F E)
  haveI : IsModuleTopology (AF F) (Matrix (Fin n) (Fin d) (AE F E)) :=
    inferInstanceAs (IsModuleTopology (AF F) (Fin n → Fin d → AE F E))
  have he : Continuous (M.co.e : Matrix (Fin n) (Fin d) (AE F E) → _) :=
    IsModuleTopology.continuous_of_linearMap M.co.e.toLinearMap
  have hm1 : Continuous fun g : UA σ X.J => mat g⁻¹ :=
    (Units.continuous_val.comp continuous_subtype_val).comp continuous_inv
  have hm2 : Continuous fun g : UA σ W.J => mat g⁻¹ :=
    (Units.continuous_val.comp continuous_subtype_val).comp continuous_inv
  have hm : Continuous fun p : UA σ X.J × UA σ W.J => (mat p.1⁻¹, mat p.2⁻¹) :=
    (hm1.comp continuous_fst).prodMk (hm2.comp continuous_snd)
  have h1 : ∀ᶠ u in 𝓝 (0 : Matrix (Fin n) (Fin d) (AE F E)),
      ∀ m ∈ (fun p : UA σ X.J × UA σ W.J => (mat p.1⁻¹, mat p.2⁻¹)) '' C,
        GlobalTheory.XTermFinParts.infOne F • M.co.e (m.1 * u * (m.2)ᵀ) = 0 → schr B.ψ (M.co.e (m.1 * u * (m.2)ᵀ)) Φ = Φ := by
    refine (hCc.image hm).eventually_forall_of_forall_eventually fun m _ => ?_
    have c : Continuous fun p : Matrix (Fin n) (Fin d) (AE F E) ×
        (Matrix (Fin n) (Fin n) (AE F E) × Matrix (Fin d) (Fin d) (AE F E)) =>
        M.co.e (p.2.1 * p.1 * (p.2.2)ᵀ) :=
      he.comp ((continuous_snd.fst.matrix_mul continuous_fst).matrix_mul continuous_snd.snd.matrix_transpose)
    exact (c.tendsto' (0, m) 0 (by simp)).eventually (GlobalTheory.XTermFinParts.eventually_schr_eq hB.std hΦ)
  filter_upwards [h1] with u hu h0 p hp
  obtain ⟨k, h⟩ := p
  have h2 := hu (mat k⁻¹, mat h⁻¹) ⟨(k, h), hp, rfl⟩ (by
    rw [← map_smul, ← Matrix.smul_mul, ← Matrix.mul_smul, h0, Matrix.mul_zero, Matrix.zero_mul, map_zero])
  have h3 := (IsUWeilPair.isUSplitting hom).impl (k, h) (mat k⁻¹ * u * (mat h⁻¹)ᵀ) Φ hΦ
  have h4 : actAB (cA σ) (k, h) (mat k⁻¹ * u * (mat h⁻¹)ᵀ) = u := by
    show mat k * (mat k⁻¹ * u * (mat h⁻¹)ᵀ) * (mat h)ᵀ = u
    have a1 : mat k * mat k⁻¹ = 1 := by
      show mat (k * k⁻¹) = 1
      rw [mul_inv_cancel]; rfl
    have a2 : mat h * mat h⁻¹ = 1 := by
      show mat (h * h⁻¹) = 1
      rw [mul_inv_cancel]; rfl
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, a1, Matrix.one_mul, Matrix.mul_assoc, ← Matrix.transpose_mul, a2,
      Matrix.transpose_one, Matrix.mul_one]
  rw [h4] at h3
  rw [← h3]
  exact congrArg _ h2

private theorem symp_eq_zero_y {B : Base F E} {n n₁ d : ℕ} {X : Spc F E n} {X₁ : Spc F E n₁} {H : Plane E n n₁} {i₀ i₁ : ℕ}
    (hH : H.IsAdapted σ B X X₁ i₀ i₁) (JB : Matrix (Fin d) (Fin d) (AE F E)) (z : Matrix (Fin n₁) (Fin d) (AE F E))
    (l : AE F E) (y : Fin d → AE F E) :
    symp (R := AF F) (cA σ) (-1) (incM F X.J) JB (incM F H.ι * z) (l • Matrix.vecMulVec (incV F H.y) y) = 0 := by
  have h0 : ∀ a, ∑ i, ∑ k, incM F H.ι i a * incM F X.J i k * cA σ (incV F H.y k) = 0 := fun a => by
    have h := congrArg (inclR (F := F) (AF F)) (hH.orth (Pi.single a 1)).2
    rw [map_zero, Matrix.mulVec_single_one] at h
    rw [← h]
    simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, Finset.mul_sum, mul_assoc]
    rfl
  have h1 : hTens (cA σ) (incM F X.J) JB (incM F H.ι * z) (l • Matrix.vecMulVec (incV F H.y) y) =
      ∑ a, ∑ j, ∑ m, (∑ i, ∑ k, incM F H.ι i a * incM F X.J i k * cA σ (incV F H.y k)) *
        (z a j * JB j m * cA σ l * cA σ (y m)) := by
    simp only [hTens, Matrix.mul_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul, map_mul, Finset.sum_mul]
    simp only [← Finset.sum_product', Finset.univ_product_univ]
    refine Fintype.sum_equiv ⟨fun p => (p.2.2.2.2, p.2.1, p.2.2.2.1, p.1, p.2.2.1),
      fun p => (p.2.2.2.1, p.2.1, p.2.2.2.2, p.2.2.1, p.1), fun _ => rfl, fun _ => rfl⟩ _ _ fun p => ?_
    simp only [Equiv.coe_fn_mk]
    ring
  rw [symp, h1]
  simp [h0]

end SlopeTestRemainingChoices

theorem UpperTheory.theta_geometry_triple_integral :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ)
        (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
        ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' →
        ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
        ∀ Ψ ∈ schA F (Fin (b + 2) × Fin (a + (b + 2))), ∀ C : Set (UA σ G.V'.J × UA σ G.W.J), IsCompact C →
        ∃ (m : ℕ) (c : Fin m → Fin b × Fin (a + b) → Af F) (φ : Fin m → (Fin b × Fin (a + b) → Af F) → ℂ),
          (∀ j, φ j ∈ SB _) ∧ ∀ p ∈ C, ∀ (l : (AE F E)ˣ) (x : Fin b × Fin (a + b) → AF F),
            e' (G.M'.co.rho B.ψ (shiftB σ H H' l) (om' p Ψ)) x = ∑ j, e' (G.M'.co.rho B.ψ (shiftB σ H H' l) (om' p Ψ)) (fun q => ((x q).1, c j q)) * φ j (fun q => (x q).2) := by
  intro F E _ _ _ _ _ σ B a b G G₁ H H' hC e he X om om' om₁ om₁' hT _ Ψ hΨ C hCc
  have hψ := hT.base.std
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) (AE F E)
  have hs : Continuous (G₁.M'.co.e.symm : _ → Matrix (Fin b) (Fin (a + b)) (AE F E)) :=
    IsModuleTopology.continuous_of_linearMap G₁.M'.co.e.symm.toLinearMap
  have c : Continuous fun w => incM F H.ι * G₁.M'.co.e.symm w * (incM F H'.ι)ᵀ :=
    (continuous_const.matrix_mul hs).matrix_mul continuous_const
  have hN := (c.tendsto' 0 0 (by simp)).eventually (eventually_rho_om_eq_pair hT.base hCc G.M' hT.weil' hΨ)
  obtain ⟨m, c, φ, hφ, hD⟩ := GlobalTheory.XTermFinParts.exists_parts hψ hN
  refine ⟨m, c, φ, hφ, fun p hp l => hD _ fun w hw h0 => ?_⟩
  have hΨ' : om' p Ψ ∈ schA F _ := (IsUWeilPair.isUSplitting hT.weil').pres p Ψ hΨ
  have h1 := hw (by
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, ← map_smul, h0, map_zero, Matrix.mul_zero, Matrix.zero_mul]) p hp
  have h2 := he.Heisenberg₂ (G₁.M'.co.e.symm w) _ (GlobalTheory.HeisSchA.rho_mem_schA G.M' B.ψ hψ (shiftB σ H H' l) _ hΨ')
  rw [GlobalTheory.XTermFinParts.rho_comm G.M'.co B.ψ (by rw [Matrix.mul_assoc]; exact symp_eq_zero_y hC.hH _ _ _ _),
    h1, show G₁.M'.co.rho B.ψ (G₁.M'.co.e.symm w) = schr B.ψ w from
      congrArg (schr B.ψ) (G₁.M'.co.e.apply_symm_apply w)] at h2
  exact h2.symm
