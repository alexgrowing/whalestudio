import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogAbsEEqZero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationOfMemNotMemSq
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section
namespace GlobalTheory.LeviLoc
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem smul_locIdele_sub_one {v : Pl F} {w : HeightOneSpectrum (𝓞 E)} (hw : w.under (𝓞 F) = v)
    (y : (w.adicCompletion E)ˣ) (u : AF F) (hu : evFin F v u = 0) :
    u • ((locIdele F w y : AE F E) - 1) = 0 := by
  subst hw
  rw [Algebra.smul_def]
  refine EulerTie.comp_finComp.ext' ?_ fun Q => ?_
  · rw [map_mul, map_sub, map_one, (EulerTie.parts_locIdele w y).1, sub_self, mul_zero, map_zero]
  · rw [GlobalTheory.CMPrimeIdele.ev_mul, map_zero]
    by_cases hQ : Q = w
    · subst hQ
      rw [EulerTie.comp_finComp.2.2.2.2]
      have : u.2 (Q.under (𝓞 F)) = 0 := hu
      rw [this, map_zero, zero_mul]; rfl
    · rw [map_sub, map_one]
      change _ * (EulerTie.finComp F E (locIdele F w y : AE F E) Q - 1) = _
      rw [EulerTie.finComp_locIdele_ne hQ, sub_self, mul_zero]; rfl

theorem smul_sub_eq_zero {n : ℕ} {c : AF F} {t : AE F E} (ht : c • (t - 1) = 0) (z : Fin n → AE F E) :
    c • (t • z - z) = 0 := by
  have : t • z - z = (t - 1) • z := by rw [sub_smul, one_smul]
  rw [this, ← smul_assoc, ht, zero_smul]

theorem incV_decomp {n n₁ : ℕ} (x y : Fin n → E) (ι : Matrix (Fin n) (Fin n₁) E) (s t : E) (u : Fin n₁ → E) :
    incV F (s • x + ι *ᵥ u + t • y) =
      inclR (F := F) (AF F) s • incV F x + incM F ι *ᵥ incV F u + inclR (F := F) (AF F) t • incV F y := by
  funext i
  simp [incV, incM, Matrix.mulVec, dotProduct, map_sum, map_mul]

theorem levi_locIdele_mem_UAt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E (a + a') d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B G.W W₁ i₀ i₁ → ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), w.under (𝓞 F) = v → ∀ (x : (w.adicCompletion E)ˣ) (m : UA σ G.W.J), IsLevi (W₁ := W₁) H' (locIdele F w x) 1 m → m ∈ UAt σ G.W (evFin F v) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT d₁ W₁ H' i₀ i₁ hA v w hw x m hL
  have hspan : ∀ z : Fin (a + a') → E, ∃ (s t : E) (u : Fin d₁ → E), z = s • H'.x + H'.ι *ᵥ u + t • H'.y := by
    let S : Submodule E (Fin (a + a') → E) :=
      { carrier := {z | ∃ (s t : E) (u : Fin d₁ → E), z = s • H'.x + H'.ι *ᵥ u + t • H'.y}
        add_mem' := by
          rintro _ _ ⟨s, t, u, rfl⟩ ⟨s', t', u', rfl⟩
          exact ⟨s + s', t + t', u + u', by rw [add_smul, add_smul, Matrix.mulVec_add]; abel⟩
        zero_mem' := ⟨0, 0, 0, by simp⟩
        smul_mem' := by
          rintro c _ ⟨s, t, u, rfl⟩
          exact ⟨c * s, c * t, c • u, by rw [Matrix.mulVec_smul, smul_add, smul_add, mul_smul, mul_smul]⟩ }
    have hsub : (G.W.L : Set (Fin (a + a') → E)) ⊆ S := fun z hz => by
      obtain ⟨s, t, u, -, -, -, e⟩ := hA.split z hz
      exact ⟨s, t, u, e⟩
    intro z
    have hz : z ∈ Submodule.span E (G.W.L : Set (Fin (a + a') → E)) := by
      rw [hT.geo.hW.lat.span_eq_top]; trivial
    exact Submodule.span_le.2 hsub hz
  show ∀ c : AF F, evFin F v c = 0 → c • (mat m - 1) = 0
  intro c hc
  have h1 : c • ((locIdele F w x : AE F E) - 1) = 0 := smul_locIdele_sub_one hw x c hc
  have h2 : c • (cA σ ((locIdele F w x)⁻¹ : (AE F E)ˣ).1 - 1) = 0 := by
    rw [← map_inv, ← map_one (cA σ), ← map_sub, ← map_smul, smul_locIdele_sub_one hw x⁻¹ c hc, map_zero]
  have hx : (c • (mat m - 1)) *ᵥ incV F H'.x = 0 := by
    rw [Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, hL.1]
    exact smul_sub_eq_zero h1 _
  have hy : (c • (mat m - 1)) *ᵥ incV F H'.y = 0 := by
    rw [Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, hL.2.1]
    exact smul_sub_eq_zero h2 _
  have hι : (c • (mat m - 1)) * incM F H'.ι = 0 := by
    rw [Matrix.smul_mul, Matrix.sub_mul, Matrix.one_mul, hL.2.2]
    have : mat (1 : UA σ W₁.J) = 1 := rfl
    rw [this, Matrix.mul_one, sub_self, smul_zero]
  ext i j
  obtain ⟨s, t, u, e⟩ := hspan (Pi.single j 1)
  have hcol : (c • (mat m - 1)) *ᵥ incV F (Pi.single j (1 : E)) = 0 := by
    rw [e, incV_decomp, Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
      Matrix.mulVec_mulVec, hx, hy, hι, Matrix.zero_mulVec, smul_zero, smul_zero, add_zero, add_zero]
  have hsingle : incV F (Pi.single j (1 : E)) = Pi.single j 1 := by
    funext k
    by_cases hk : k = j
    · subst hk; simp [incV]
    · simp [incV, Pi.single_apply, hk]
  rw [hsingle, Matrix.mulVec_single_one] at hcol
  have := congrFun hcol i
  simpa [Matrix.col] using this

end GlobalTheory.LeviLoc
