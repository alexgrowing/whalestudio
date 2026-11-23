import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodicityLevelHeightBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerPreservesAdelicSchwartz
import Development.AbelianVarietyTheory.PublishedTheorems.AdelicLattices₂.ExistsIntMulIsIntegralOfTrace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteSchwartzSetIntegralShift

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.FinPartHeis

theorem finPart_right : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (x : Fin n → E),
    B.IsGood σ → M.IsGood B.ψ → ∀ Ψ ∈ schA F (Fin n × Fin d), ∀ N : ℕ, 1 ≤ N →
    ∃ S : Set (Fn F n d), S.Finite ∧ S ⊆ schA F (Fin n × Fin d) ∧ ∀ w : Fin d → E, (∀ i, ∃ o : 𝓞 E, (N : E) * w i = o) →
      ∃ Φ ∈ S, M.co.rho B.ψ (Matrix.vecMulVec (incV F x) (incV F w)) Ψ =
        M.co.rho B.ψ (realAd F 1 • Matrix.vecMulVec (incV F x) (incV F w)) Φ := by
  intro F E _ _ _ _ _ σ B n d X W M x hB hM Ψ hΨ N hN
  have hψ : IsStd B.ψ := hB.std
  obtain ⟨m₀, hm₀, hfix⟩ := GlobalTheory.ThetaLevel.heis_fix B.ψ hψ.1 Ψ hΨ
  obtain ⟨m₃, hm₃, htriv⟩ := GlobalTheory.PsiTriv.exists_nat_trivial B.ψ hψ.1
  have hIZ : ∀ z : ℤ, IsIntegral ℤ (z : F) := fun z => by
    simpa using (isIntegral_algebraMap : IsIntegral ℤ (algebraMap ℤ F z))
  have hIN : ∀ z : ℕ, IsIntegral ℤ (z : F) := fun z => by exact_mod_cast hIZ z

  have hr : realAd F 1 = ((1 : InfiniteAdeleRing F), (0 : FiniteAdeleRing (𝓞 F) F)) := realAd_one_eq F
  set ef : AF F := 1 - realAd F 1 with hef_def
  have hrr : realAd F 1 * realAd F 1 = realAd F 1 := by
    have := GlobalTheory.ThetaDecay.realAd_mul (F := F) 1 1
    rwa [mul_one] at this
  have hr1 : (realAd F 1).1 = 1 := by rw [hr]
  have hef1 : ef.1 = 0 := by
    show (1 : AF F).1 - (realAd F 1).1 = 0
    rw [hr1]; exact sub_self _
  have hefv : ∀ v, evFin F v ef = 1 := fun v => by
    rw [hef_def, map_sub, map_one, sub_eq_self]
    show (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) ((sndA F) (realAd F 1)) = 0
    rw [show (sndA F) (realAd F 1) = 0 by rw [hr]; rfl, map_zero]
  have hff : ef * ef = ef := by rw [hef_def]; linear_combination hrr

  let emb : (Fin n × Fin d → F) → (Fin n × Fin d → AF F) := fun a i => ef * algebraMap F (AF F) (a i)
  have hnorm : ∀ v (m : ℕ) (o : F), IsIntegral ℤ o → ‖evFin F v (ef * algebraMap F (AF F) ((m : F) * o))‖ ≤ ‖(m : Fv F v)‖ := by
    intro v m o ho
    rw [map_mul, hefv, one_mul, AlgHom.commutes, map_mul, map_natCast, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (norm_algebraMap_le_one v ho)
  have hemb_int : ∀ (m : ℕ) (a : Fin n × Fin d → F), (∀ i, ∃ o : F, IsIntegral ℤ o ∧ a i = m * o) →
      GlobalTheory.ThetaDenom.IsMulInt F m (emb a) := by
    intro m a ha
    refine ⟨fun i => ?_, fun v i => ?_⟩
    · show ef.1 * _ = 0
      rw [hef1, zero_mul]
    · obtain ⟨o, ho, hao⟩ := ha i
      show ‖evFin F v (ef * algebraMap F (AF F) (a i))‖ ≤ _
      rw [hao]
      exact hnorm v m o ho
  have hemb_triv : ∀ o : F, IsIntegral ℤ o → B.ψ (ef * algebraMap F (AF F) ((m₃ : F) * o)) = 1 := by
    intro o ho
    exact htriv _ (by show ef.1 * _ = 0; rw [hef1, zero_mul]) fun v => hnorm v m₃ o ho
  have hdot : ∀ c c' : Fin n × Fin d → F, emb c ⬝ᵥ emb c' = ef * algebraMap F (AF F) (c ⬝ᵥ c') := by
    intro c c'
    simp only [dotProduct, emb, map_sum, Finset.mul_sum, map_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    linear_combination (algebraMap F (AF F) (c i) * algebraMap F (AF F) (c' i)) * hff

  have hincV0 : incV F (0 : Fin d → E) = 0 := funext fun i => by simp [incV]
  have hincVadd : ∀ ξ ξ' : Fin d → E, incV F (ξ + ξ') = incV F ξ + incV F ξ' := fun ξ ξ' =>
    funext fun i => by simp [incV]
  let T : (Fin d → E) →+ (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F) :=
    { toFun := fun ξ => ef • M.co.e (Matrix.vecMulVec (incV F x) (incV F ξ))
      map_zero' := by
        rw [hincV0, show Matrix.vecMulVec (incV F x) (0 : Fin d → AE F E) = 0 from by ext i j; simp [Matrix.vecMulVec_apply], map_zero, smul_zero]
      map_add' := fun ξ ξ' => by simp only [hincVadd, Matrix.vecMulVec_add, map_add, smul_add] }

  have hdec : ∀ ξ : Fin d → E, M.co.rho B.ψ (Matrix.vecMulVec (incV F x) (incV F ξ)) Ψ =
      M.co.rho B.ψ (realAd F 1 • Matrix.vecMulVec (incV F x) (incV F ξ)) (schr B.ψ (T ξ) Ψ) := by
    intro ξ
    show schr B.ψ (M.co.e _) Ψ = schr B.ψ (M.co.e (realAd F 1 • _)) (schr B.ψ (ef • M.co.e _) Ψ)
    rw [LinearEquiv.map_smul]
    generalize M.co.e (Matrix.vecMulVec (incV F x) (incV F ξ)) = p
    have hsplit : p = realAd F 1 • p + ef • p := by rw [← add_smul, hef_def, add_sub_cancel, one_smul]
    funext x
    conv_lhs => rw [hsplit]
    rw [schr_add]
    have h0 : ⅟(2 : AF F) * ((ef • p).1 ⬝ᵥ (realAd F 1 • p).2 - (realAd F 1 • p).1 ⬝ᵥ (ef • p).2) = 0 := by
      simp only [Prod.smul_fst, Prod.smul_snd, smul_dotProduct, dotProduct_smul, smul_eq_mul]
      ring
    rw [h0, AddChar.map_zero_eq_one, one_mul]

  have hN0 : (N : E) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  let L : Submodule ℤ (Fin d → E) :=
    { carrier := {ξ | ∀ i, ∃ o : 𝓞 E, (N : E) * ξ i = o}
      add_mem' := fun {a b} ha hb i => by
        obtain ⟨o, ho⟩ := ha i
        obtain ⟨o', ho'⟩ := hb i
        exact ⟨o + o', by rw [Pi.add_apply, mul_add, ho, ho']; push_cast; ring⟩
      zero_mem' := fun i => ⟨0, by simp⟩
      smul_mem' := fun k {a} ha i => by
        obtain ⟨o, ho⟩ := ha i
        refine ⟨k * o, ?_⟩
        show (N : E) * (k • a) i = ((k * o : 𝓞 E) : E)
        rw [Pi.smul_apply, zsmul_eq_mul, mul_left_comm, ho]
        simp }
  have hLfg : L.FG := by
    let f : (Fin d → 𝓞 E) →ₗ[ℤ] (Fin d → E) :=
      { toFun := fun o i => (N : E)⁻¹ * (o i : E)
        map_add' := fun a b => by funext i; simp [mul_add]
        map_smul' := fun k a => by funext i; simp [mul_left_comm] }
    have hL : L = Submodule.map f ⊤ := by
      ext ξ
      simp only [Submodule.map_top, LinearMap.mem_range]
      constructor
      · intro h
        choose o ho using h
        exact ⟨o, funext fun i => by
          show (N : E)⁻¹ * (o i : E) = ξ i
          rw [← ho i, ← mul_assoc, inv_mul_cancel₀ hN0, one_mul]⟩
      · rintro ⟨o, rfl⟩ i
        exact ⟨o i, by
          show (N : E) * ((N : E)⁻¹ * (o i : E)) = o i
          rw [← mul_assoc, mul_inv_cancel₀ hN0, one_mul]⟩
    rw [hL]
    exact Submodule.FG.map f Module.Finite.fg_top

  choose A Bv hAB using fun ξ : Fin d → E => hM.rat (Matrix.vecMulVec x ξ)
  have hinc : ∀ ξ : Fin d → E, incM F (Matrix.vecMulVec x ξ) = Matrix.vecMulVec (incV F x) (incV F ξ) := by
    intro ξ; ext i j; simp [incM, incV, Matrix.vecMulVec_apply, map_mul]
  obtain ⟨G, hG⟩ := id hLfg
  obtain ⟨D, hD0, hD⟩ := GlobalTheory.HermClass.exists_int_mul_isIntegral F
    (S := ⋃ g ∈ (G : Set (Fin d → E)), (Set.range (A g) ∪ Set.range (Bv g)))
    (Set.Finite.biUnion G.finite_toSet fun g _ => (Set.finite_range _).union (Set.finite_range _))
  have hden : ∀ ξ ∈ L, ∃ a b : Fin n × Fin d → F, (∀ i, IsIntegral ℤ ((D : F) * a i)) ∧
      (∀ i, IsIntegral ℤ ((D : F) * b i)) ∧ T ξ = (emb a, emb b) := by
    intro ξ hξ
    rw [← hG] at hξ
    induction hξ using Submodule.span_induction with
    | mem g hg =>
      refine ⟨A g, Bv g, fun i => hD _ ?_, fun i => hD _ ?_, ?_⟩
      · exact Set.mem_biUnion hg (Or.inl ⟨i, rfl⟩)
      · exact Set.mem_biUnion hg (Or.inr ⟨i, rfl⟩)
      · show ef • M.co.e _ = _
        rw [← hinc, hAB]
        rfl
    | zero =>
      refine ⟨0, 0, fun i => ?_, fun i => ?_, ?_⟩
      · rw [Pi.zero_apply, mul_zero]; exact isIntegral_zero
      · rw [Pi.zero_apply, mul_zero]; exact isIntegral_zero
      rw [map_zero]
      ext i <;> simp [emb]
    | add ξ ξ' _ _ h h' =>
      obtain ⟨a, b, ha, hb, he⟩ := h
      obtain ⟨a', b', ha', hb', he'⟩ := h'
      refine ⟨a + a', b + b', fun i => ?_, fun i => ?_, ?_⟩
      · simpa [mul_add] using (ha i).add (ha' i)
      · simpa [mul_add] using (hb i).add (hb' i)
      · rw [map_add, he, he']
        ext i <;> simp [emb, mul_add]
    | smul k ξ _ h =>
      obtain ⟨a, b, ha, hb, he⟩ := h
      refine ⟨(k : F) • a, (k : F) • b, fun i => ?_, fun i => ?_, ?_⟩
      · have := (hIZ k).mul (ha i)
        simpa [mul_left_comm] using this
      · have := (hIZ k).mul (hb i)
        simpa [mul_left_comm] using this
      · rw [map_zsmul, he]
        ext i <;> simp [emb, zsmul_eq_mul, map_mul, map_intCast] <;> ring

  set K : ℤ := 2 * m₀ * m₃ * D * D with hK_def
  have hK0 : K ≠ 0 := by
    have : (m₀ : ℤ) ≠ 0 := by exact_mod_cast hm₀.ne'
    have : (m₃ : ℤ) ≠ 0 := by exact_mod_cast hm₃.ne'
    simp only [hK_def]
    positivity
  obtain ⟨R, hRfin, hRL, hres⟩ := GlobalTheory.HermClass.exists_finite_residues L hLfg hK0
  refine ⟨(fun ρ => schr B.ψ (T ρ) Ψ) '' R, hRfin.image _, ?_, fun ξ hξ => ?_⟩
  · rintro _ ⟨ρ, -, rfl⟩
    exact GlobalTheory.SchrKeepsSchA.schr_mem_schA F B.ψ hψ _ _ Ψ hΨ
  · obtain ⟨ρ, hρR, η, hη, rfl⟩ := hres ξ hξ
    refine ⟨_, ⟨ρ, hρR, rfl⟩, ?_⟩
    rw [hdec]
    congr 1
    obtain ⟨a, b, ha, hb, he⟩ := hden η hη
    obtain ⟨a', b', ha', hb', he'⟩ := hden ρ (hRL ρ hρR)
    have hK1 : K • ((emb a, emb b) : (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F)) =
        (emb ((K : F) • a), emb ((K : F) • b)) := by
      ext i <;> simp [emb, zsmul_eq_mul, map_mul, map_intCast] <;> ring
    have hKint : ∀ (c : Fin n × Fin d → F), (∀ i, IsIntegral ℤ ((D : F) * c i)) →
        ∀ i, ∃ o : F, IsIntegral ℤ o ∧ ((K : F) • c) i = m₀ * o := by
      intro c hc i
      refine ⟨((2 * m₃ * D : ℤ) : F) * ((D : F) * c i), (hIZ _).mul (hc i), ?_⟩
      simp only [Pi.smul_apply, smul_eq_mul, hK_def]
      push_cast
      ring
    show schr B.ψ (T (ρ + K • η)) Ψ = schr B.ψ (T ρ) Ψ
    rw [map_add, map_zsmul, he, he', hK1]
    funext x
    rw [schr_add, hfix _ _ (hemb_int m₀ _ (hKint a ha)) (hemb_int m₀ _ (hKint b hb))]

    have hZ : IsIntegral ℤ ((D : F) * D * (a ⬝ᵥ b' - a' ⬝ᵥ b)) := by
      rw [mul_sub, dotProduct, dotProduct, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine IsIntegral.sum _ fun i _ => ?_
      have := ((ha i).mul (hb' i)).sub ((ha' i).mul (hb i))
      convert this using 1
      ring
    have hph : ⅟(2 : AF F) * ((emb ((K : F) • a)) ⬝ᵥ (emb b') - (emb a') ⬝ᵥ (emb ((K : F) • b))) =
        ef * algebraMap F (AF F) ((m₃ : F) * (m₀ * ((D : F) * D * (a ⬝ᵥ b' - a' ⬝ᵥ b)))) := by
      rw [hdot, hdot, ← mul_sub, ← map_sub, smul_dotProduct, dotProduct_smul]
      have hXY : (K : F) • (a ⬝ᵥ b') - (K : F) • (a' ⬝ᵥ b) =
          2 * ((m₃ : F) * (m₀ * ((D : F) * D * (a ⬝ᵥ b' - a' ⬝ᵥ b)))) := by
        simp only [smul_eq_mul, hK_def]
        push_cast
        ring
      rw [hXY, map_mul, map_ofNat]
      linear_combination (ef * algebraMap F (AF F) ((m₃ : F) * (m₀ * ((D : F) * D * (a ⬝ᵥ b' - a' ⬝ᵥ b))))) *
        (invOf_mul_self (2 : AF F))
    rw [hph, hemb_triv _ ((hIN m₀).mul hZ), one_mul]

end GlobalTheory.FinPartHeis
