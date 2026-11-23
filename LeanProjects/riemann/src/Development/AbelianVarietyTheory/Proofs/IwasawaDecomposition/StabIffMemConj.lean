import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NeZeroTop
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPointOfRationalUnitaryAdelicMul
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.TopCh

theorem stab_iff_mem_conj : ∀ (F E K : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] [Field K] (hc : CMData F E) (n : ℕ) [NeZero n] (ST SG Q : Finset (HeightOneSpectrum (𝓞 E))) (Λ : LevFam E K n SG) (Θ : LevQFam E K n Q) (U : Subgroup (GL (Fin n) (AfE F E))) (k' y : GL (Fin n) (AfE F E)) (p : DecoF E n ST SG Q), (∀ (g x : GL (Fin n) (AfE F E)) (p p' : DecoF E n ST SG Q), IsPtOf hc (g * k') p → IsPtOf hc (g * x * k') p' → (x ∈ U ↔ ∃ (h : Λ.grp) (θ : Θ.grp), ((1, h.1, θ.1) : UF E n × GLG E n SG × GLQ E n Q) • p = p')) → IsPtOf hc (y * k') p → ∀ γ : UF E n, (∃ (h : Λ.grp) (θ : Θ.grp), ((γ, h.1, θ.1) : UF E n × GLG E n SG × GLQ E n Q) • p = p) ↔ ratAd F γ ∈ U.map (MulAut.conj y).toMonoidHom := by
  intro F E K _ _ _ _ _ _ _ hc n _ ST SG Q Λ Θ U k' y p hlev hp γ
  have hγ : IsPtOf hc (ratAd F γ * (y * k')) (((γ, 1, 1) : UF E n × GLG E n SG × GLQ E n Q) • p) := by
    first | exact GlobalTheory.Mem.Col2.RatMove.isPtOf_ratAd F E hc n ST SG Q γ (y * k') p hp | exact GlobalTheory.Mem.Col2.RatMove.isPtOf_ratAd (hc := hc) γ hp | (apply GlobalTheory.Mem.Col2.RatMove.isPtOf_ratAd <;> assumption)
  have hx : IsPtOf hc (y * (y⁻¹ * ratAd F γ * y) * k') (((γ, 1, 1) : UF E n × GLG E n SG × GLQ E n Q) • p) := by
    have : y * (y⁻¹ * ratAd F γ * y) * k' = ratAd F γ * (y * k') := by group
    rw [this]; exact hγ
  have key := hlev y (y⁻¹ * ratAd F γ * y) p _ hp hx
  have hmem : ratAd F γ ∈ U.map (MulAut.conj y).toMonoidHom ↔ y⁻¹ * ratAd F γ * y ∈ U := by
    constructor
    · rintro ⟨u, hu, he⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at he
      rw [← he]; simpa [mul_assoc] using hu
    · intro hu
      refine ⟨_, hu, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
  rw [hmem, key]
  constructor
  · rintro ⟨h, θ, he⟩
    refine ⟨h⁻¹, θ⁻¹, ?_⟩
    have e1 : ((γ, 1, 1) : UF E n × GLG E n SG × GLQ E n Q) = ((1, (h⁻¹).1, (θ⁻¹).1) : UF E n × GLG E n SG × GLQ E n Q) * (γ, h.1, θ.1) := by
      ext <;> simp
    rw [e1, mul_smul, he]
  · rintro ⟨h, θ, he⟩
    refine ⟨h⁻¹, θ⁻¹, ?_⟩
    have : ((γ, (h⁻¹).1, (θ⁻¹).1) : UF E n × GLG E n SG × GLQ E n Q) = ((1, (h⁻¹).1, (θ⁻¹).1) : UF E n × GLG E n SG × GLQ E n Q) * (γ, 1, 1) := by
      ext <;> simp
    rw [this, mul_smul, ← he, ← mul_smul]
    have : ((1, (h⁻¹).1, (θ⁻¹).1) : UF E n × GLG E n SG × GLQ E n Q) * (1, h.1, θ.1) = 1 := by
      ext <;> simp
    rw [this, one_smul]

end GlobalTheory.Mem.Col2.TopCh
