import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeEvFun
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsPowApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabAtPair
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalStabilizerLocallyCompactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviEmbeddingLocalMeasurableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemidirectHaarMeasureProductStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalSpacesBorelPolishStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarVectorScalingIdeleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarSkewScalingIdeleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigALocalMeasurePreserving

noncomputable section

namespace GlobalTheory.ThK.LemF.QuotInv

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)

theorem modulus_levi : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ)
    (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' → ∀ (v : Pl F),
    ∀ m₀ : idelesAt E (evFin F v) →* UAtSub σ G.V (evFin F v), (∀ t, IsLevi H t.1 (1 : UA σ G₁.V.J) (m₀ t).1) →
    ∀ hn : (∀ t, ∀ q ∈ stabAt σ G.V (evFin F v) H.x, (m₀ t)⁻¹ * q * m₀ t ∈ stabAt σ G.V (evFin F v) H.x),
    ∀ μ : Measure (stabAt σ G.V (evFin F v) H.x), μ.IsHaarMeasure → ∀ t,
      μ.map (fun q : stabAt σ G.V (evFin F v) H.x => (⟨(m₀ t)⁻¹ * q * m₀ t, hn t q q.2⟩ : stabAt σ G.V (evFin F v) H.x)) = absPow E (evFin F v) (b + 1) t • μ := by
  intro F E _ _ _ _ _ σ B b a' G G₁ H H' hC X om om' om₁ om₁' hT hT₁ v m₀ hL hn μ hμ t
  have hσ : ∀ e, σ (σ e) = e := by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    intro e
    apply τ.injective
    rw [hT.base.cm.2.2.2, hT.base.cm.2.2.2, star_star]
  obtain ⟨Φ, hR, hM⟩ := GlobalTheory.T.config_a_local_measure_preserving F E σ B b a' G G₁ H H' hC X om om' om₁ om₁' hT hT₁ hσ v
  obtain ⟨⟨i1, i2, i3, i4⟩, ⟨j1, j2, j3, j4⟩⟩ := GlobalTheory.T.local_spaces_borel_polish F E σ b v
  obtain ⟨k1, k2, k3, -⟩ := GlobalTheory.T.local_stabilizer_locally_compact F E σ B b a' G G₁ H H' hC X om om' om₁ om₁' hT hT₁ v
  have hcl := (GlobalTheory.T.levi_embedding_local_measurable F E σ B b a' G G₁ H H' hC X om om' om₁ om₁' hT hT₁ v m₀ hL).1
  haveI : BorelSpace (UA σ G.V.J) := ⟨rfl⟩
  haveI : LocallyCompactSpace (stabAt σ G.V (evFin F v) H.x) := hcl.locallyCompactSpace
  have hLcl : IsClosed ((stabAtPair σ G.V (evFin F v) H.x H.y : Subgroup _) : Set (stabAt σ G.V (evFin F v) H.x)) := by
    have hm : Continuous fun q : stabAt σ G.V (evFin F v) H.x => mat q.1.1 :=
      Units.continuous_val.comp (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_subtype_val))
    exact isClosed_eq (hm.matrix_mulVec continuous_const) continuous_const
  haveI := hLcl.locallyCompactSpace
  let α : stabAt σ G.V (evFin F v) H.x →* stabAt σ G.V (evFin F v) H.x :=
    { toFun := fun q => ⟨(m₀ t)⁻¹ * q * m₀ t, hn t q q.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun p q => Subtype.ext (by simp [mul_assoc]) }
  have hαc : Continuous α :=
    ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _
  have hsA : Continuous (vecAtSmul (ev := evFin F v) (m := b) (cA σ (t.1⁻¹ : (AE F E)ˣ).1)) :=
    ((continuous_const_smul _).comp continuous_subtype_val).subtype_mk _
  have hsC : Continuous (normSmul (ev := evFin F v) hσ (t.1⁻¹ : (AE F E)ˣ).1) :=
    (continuous_const.mul continuous_subtype_val).subtype_mk _
  have hconj : ∀ l a c, α (Φ (l, (a, c))) = Φ (l, (vecAtSmul (cA σ (t.1⁻¹ : (AE F E)ˣ).1) a,
      normSmul hσ (t.1⁻¹ : (AE F E)ˣ).1 c)) := fun l a c =>
    Subtype.ext (Subtype.ext (hM t.1 (m₀ t).1 (hL t) l a c).symm)
  have key := GlobalTheory.T.semidirect_haar_measure_product _ _ _ _ Φ hR α _ _ (absE F E t.1 ^ b) (absE F E t.1) hαc hsA hsC hconj
    (GlobalTheory.T.haar_vector_scaling_idele F E σ b v t.1 t.2) (GlobalTheory.T.haar_skew_scaling_idele F E σ hT.base.cm hσ v t.1 t.2) μ hμ
  rw [absPow_apply, pow_succ]
  exact key

end GlobalTheory.ThK.LemF.QuotInv

end
