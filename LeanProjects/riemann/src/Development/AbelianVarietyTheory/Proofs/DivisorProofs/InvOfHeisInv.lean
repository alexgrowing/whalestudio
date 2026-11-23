import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLagrAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationLocalityUnitaryGroupVStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunctionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergInvariantFormCompLocalWeilOperatorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergInvariantFormVanishesLagrangianTestStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceTransformingCharacterEqOneStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.InertVacLag

theorem inv_of_heisInv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ (m : ℕ) (C : Matrix (Fin (a + a')) (Fin m) (AE F E)), GlobalTheory.InertVacLag.IsLagrAt σ G.W v C →
    ∀ l : ((Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] ℂ, GlobalTheory.InertVacLag.HeisInv G.M' B.ψ v C l →
    ∀ g ∈ UAt σ G.V' (evFin F v), ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
      Acts (evFin F v) (om' (g, 1)) φ φ₁ → l φ₁ = l φ := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v w hin hv m C hC l hl g hg φ hφ φ₁ hφ₁ hA
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.T.exists_complementary_adelicSchwartz_restFunction (F := F) (Fin a' × Fin (a + a')) v
  have htadd : ∀ f f' : (Fin a' × Fin (a + a') → Fv F v) → ℂ,
      tens (evFin F v) (f + f') R = tens (evFin F v) f R + tens (evFin F v) f' R := fun f f' => by
    funext x; simp [tens, add_mul]
  have htsmul : ∀ (c : ℂ) (f : (Fin a' × Fin (a + a') → Fv F v) → ℂ),
      tens (evFin F v) (c • f) R = c • tens (evFin F v) f R := fun c f => by
    funext x; simp [tens, mul_assoc]
  let Sop : UA σ G.V'.J → (((Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] ((Fin a' × Fin (a + a') → Fv F v) → ℂ)) :=
    fun g =>
    { toFun := fun f t => (R 0)⁻¹ * om' (g, 1) (tens (evFin F v) f R) (fun i => GlobalTheory.LatVac.liftV v (t i))
      map_add' := fun f f' => by
        funext t; simp only [htadd, map_add, Pi.add_apply]; ring
      map_smul' := fun c f => by
        funext t; simp only [htsmul, map_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
  have hSop : ∀ g f t, Sop g f t = (R 0)⁻¹ * om' (g, 1) (tens (evFin F v) f R) (fun i => GlobalTheory.LatVac.liftV v (t i)) :=
    fun _ _ _ => rfl
  have huniq : ∀ (T : ((Fin a' × Fin (a + a') → AF F) → ℂ) → (Fin a' × Fin (a + a') → AF F) → ℂ)
      (f f₁ : (Fin a' × Fin (a + a') → Fv F v) → ℂ), f ∈ SB _ → Acts (evFin F v) T f f₁ →
      ∀ t, f₁ t = (R 0)⁻¹ * T (tens (evFin F v) f R) (fun i => GlobalTheory.LatVac.liftV v (t i)) := by
    intro T f f₁ hf hA t
    rw [hA R (hR f hf)]
    have hat : At (evFin F v) (fun i => GlobalTheory.LatVac.liftV v (t i)) := by
      intro u hu; funext i; exact GlobalTheory.LatVac.at_liftV v _ u hu
    have h1 : R (fun i => GlobalTheory.LatVac.liftV v (t i)) = R 0 := by
      simpa using (hR f hf).1 0 _ hat
    simp only [tens, h1, GlobalTheory.LatVac.evFin_liftV]
    field_simp
  have hS : ∀ g ∈ UAt σ G.V' (evFin F v), ∀ f ∈ SB (Fin a' × Fin (a + a') → Fv F v),
      Sop g f ∈ SB (Fin a' × Fin (a + a') → Fv F v) ∧ Acts (evFin F v) (om' (g, 1)) f (Sop g f) := by
    intro g hg f hf
    obtain ⟨S₀, hS₀⟩ := GlobalTheory.T.weilRepresentationLocality_unitaryGroupV' B G X om om' hT v g hg
    have e : S₀ f = Sop g f := funext fun t => (huniq _ f _ hf (hS₀ f hf).2 t).trans (hSop g f t).symm
    rw [← e]; exact hS₀ f hf
  obtain ⟨φ₀, hφ₀, hline⟩ := GlobalTheory.T.heisenberg_invariant_form_vanishes_lagrangian_test F E σ a' (a + a') G.V' G.W G.M' B.ψ v (hT.base.inert v w hin).2.2 m C hC
  by_cases hz : ∀ f ∈ SB (Fin a' × Fin (a + a') → Fv F v), l f = 0
  · rw [hz φ₁ hφ₁, hz φ hφ]
  push_neg at hz
  have hl0 : l φ₀ ≠ 0 := fun h => by
    obtain ⟨f, hf, hne⟩ := hz; exact hne (hline l hl h f hf)
  let c : UA σ G.V'.J → ℂ := fun g => l (Sop g φ₀) / l φ₀
  have hlaw : ∀ g ∈ UAt σ G.V' (evFin F v), ∀ f ∈ SB (Fin a' × Fin (a + a') → Fv F v),
      ∀ f₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v), Acts (evFin F v) (om' (g, 1)) f f₁ → l f₁ = c g * l f := by
    intro g hg f hf f₁ hf₁ hA
    have hf₁eq : f₁ = Sop g f := funext fun t => (huniq _ f f₁ hf hA t).trans (hSop g f t).symm
    have hE := GlobalTheory.T.heisenbergInvariantForm_comp_localWeilOperator F E σ B a a' G X om om' hT v m C l hl g hg (Sop g) (hS g hg)
    have hl' : GlobalTheory.InertVacLag.HeisInv G.M' B.ψ v C (l ∘ₗ Sop g - c g • l) := by
      intro u hu f hf f₁ hf₁ hA'
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
      rw [hE u hu f hf f₁ hf₁ hA', hl u hu f hf f₁ hf₁ hA']
    have h0 : (l ∘ₗ Sop g - c g • l) φ₀ = 0 := by
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, LinearMap.comp_apply, c]
      field_simp
      ring
    have h1 := hline _ hl' h0 f hf
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, LinearMap.comp_apply] at h1
    rw [hf₁eq]
    linear_combination h1
  have hc := GlobalTheory.T.inert_place_transforming_character_eq_one F E σ B a a' G X om om' hT v w hin hv m C hC l hl hz c hlaw g hg
  rw [hlaw g hg φ hφ φ₁ hφ₁ hA, hc, one_mul]

end GlobalTheory.InertVacLag
end
