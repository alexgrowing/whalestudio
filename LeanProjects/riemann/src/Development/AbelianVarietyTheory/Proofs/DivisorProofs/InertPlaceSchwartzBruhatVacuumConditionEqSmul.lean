import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLocalImageLatticeSupportedAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorLatticeLocalDarbouxCoordsBounded
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianTensorSkewHermitianLatticeOpenCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceTensorLatticeSelfDualSymplecticStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSecondCoordinateOfOrthogonalSelfDualStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix GlobalTheory.VacAny

noncomputable section
namespace GlobalTheory.VacUniqInert

theorem eq_smul_of_eigen {K κ : Type} [Field K] [Fintype κ] [Invertible (2 : K)] (ψ₀ : AddChar K ℂ) {ι : Type}
    (L : ι → (κ → K) × (κ → K)) (c : ι → ℂ)
    (hD : ∀ u : κ → K, (∀ i, (L i).1 = 0 → ψ₀ (u ⬝ᵥ (L i).2) = 1) → ∃ i, (L i).1 = u)
    (f η : (κ → K) → ℂ) (hf : ∀ i, schr ψ₀ (L i) f = c i • f) (hη : ∀ i, schr ψ₀ (L i) η = c i • η)
    (hη0 : η ≠ 0) : ∃ c' : ℂ, f = c' • η := by
  obtain ⟨X₀, hX₀⟩ : ∃ X₀, η X₀ ≠ 0 := by
    by_contra h
    push_neg at h
    exact hη0 (funext h)
  have hne : ∀ t, ψ₀ t ≠ 0 := fun t h => by
    have e := AddChar.map_add_eq_mul ψ₀ t (-t)
    rw [add_neg_cancel, AddChar.map_zero_eq_one, h, zero_mul] at e
    exact one_ne_zero e
  refine ⟨f X₀ / η X₀, funext fun X => ?_⟩
  simp only [Pi.smul_apply, smul_eq_mul]
  by_cases hu : ∀ i, (L i).1 = 0 → ψ₀ ((X - X₀) ⬝ᵥ (L i).2) = 1
  · obtain ⟨i, hi⟩ := hD _ hu
    have hX : X₀ + (L i).1 = X := by rw [hi]; abel
    have e1 := congrFun (hf i) X₀
    have e2 := congrFun (hη i) X₀
    simp only [schr, Pi.smul_apply, smul_eq_mul, hX] at e1 e2
    have hA := hne (X₀ ⬝ᵥ (L i).2 + ⅟(2 : K) * ((L i).1 ⬝ᵥ (L i).2))
    field_simp
    refine mul_left_cancel₀ hA ?_
    linear_combination η X₀ * e1 - f X₀ * e2
  · push_neg at hu
    obtain ⟨i, hi0, hne1⟩ := hu
    have key : ∀ g : (κ → K) → ℂ, schr ψ₀ (L i) g = c i • g → ∀ Y, ψ₀ (Y ⬝ᵥ (L i).2) * g Y = c i * g Y := by
      intro g hg Y
      have e := congrFun hg Y
      simpa [schr, hi0] using e
    have hc : ψ₀ (X₀ ⬝ᵥ (L i).2) = c i := mul_right_cancel₀ hX₀ (key η (hη i) X₀)
    have hz : ∀ g : (κ → K) → ℂ, schr ψ₀ (L i) g = c i • g → g X = 0 := by
      intro g hg
      by_contra hgX
      have h1 : ψ₀ (X ⬝ᵥ (L i).2) = ψ₀ (X₀ ⬝ᵥ (L i).2) := by
        rw [hc]; exact mul_right_cancel₀ hgX (key g hg X)
      apply hne1
      have e : X ⬝ᵥ (L i).2 = (X - X₀) ⬝ᵥ (L i).2 + X₀ ⬝ᵥ (L i).2 := by rw [sub_dotProduct]; ring
      rw [e, AddChar.map_add_eq_mul] at h1
      exact mul_right_cancel₀ (hne _) (h1.trans (one_mul _).symm)
    rw [hz f (hf i), hz η (hη i), mul_zero]

theorem vac_unique : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → ∀ (θ : 𝓞 E), (θ : E) + σ θ = 1 →
      (∀ γ ∈ latAtV G.V' G.W v, Acts (evFin F v) (G.M'.co.rho B.ψ γ) (G.M'.vac v)
          (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V'.J) (incM F G.W.J) γ γ) • (G.M'.vac v))) →
      ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), (∀ γ ∈ latAtV G.V' G.W v, Acts (evFin F v) (G.M'.co.rho B.ψ γ) φ
          (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V'.J) (incM F G.W.J) γ γ) • φ)) → ∃ c : ℂ, φ = c • G.M'.vac v := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hTr v w hin θ _ hvac φ hφ hfix
  classical
  have hat : ∀ γ ∈ latAtV G.V' G.W v, At (evFin F v) γ := (GlobalTheory.LatVac.latAtV_at_stable G.V' G.W v).1
  let cf : latAtV G.V' G.W v → ℂ := fun γ =>
    B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V'.J) (incM F G.W.J) γ γ)
  have hloc : ∀ f ∈ SB (Fin a' × Fin (a + a') → Fv F v), (∀ γ ∈ latAtV G.V' G.W v,
      Acts (evFin F v) (G.M'.co.rho B.ψ γ) f
        (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V'.J) (incM F G.W.J) γ γ) • f)) →
      ∀ γ : latAtV G.V' G.W v, schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M'.co v γ) f = cf γ • f := by
    intro f hf h γ
    exact GlobalTheory.TensUniq.eq_of_tens_eq v f _ _ hf fun r hr =>
      (GlobalTheory.VacBridge.rho_acts_locCo G.M'.co B.ψ v γ (hat γ γ.2) f r hr).symm.trans (h γ γ.2 r hr)
  have hsd : ∀ z, z ∈ (latAtV G.V' G.W v).map (GlobalTheory.LatVac.locCo G.M'.co v) ↔
      ∀ l ∈ (latAtV G.V' G.W v).map (GlobalTheory.LatVac.locCo G.M'.co v), GlobalTheory.LatVac.psiAt B.ψ v (z.1 ⬝ᵥ l.2 - l.1 ⬝ᵥ z.2) = 1 :=
    GlobalTheory.LatVac.DualLoc.map_selfDual v G.M'.co B.ψ (latAtV G.V' G.W v) hat
      (fun z hz => GlobalTheory.T.inertPlace_tensorLattice_selfDual_symplectic F E σ B hTr.base G.V' G.W _ _ _ _ hTr.geo.hV' hTr.geo.hW v w hin z hz)
  have hst : ∀ t ∈ v.adicCompletionIntegers F, ∀ l ∈ (latAtV G.V' G.W v).map (GlobalTheory.LatVac.locCo G.M'.co v),
      t • l ∈ (latAtV G.V' G.W v).map (GlobalTheory.LatVac.locCo G.M'.co v) := by
    rintro t ht _ ⟨γ, hγ, rfl⟩
    refine ⟨GlobalTheory.LatVac.liftV v t • γ, (GlobalTheory.LatVac.latAtV_at_stable G.V' G.W v).2 t ht γ hγ, ?_⟩
    rw [GlobalTheory.LatOpenCpt.locCo_smul, GlobalTheory.LatVac.evFin_liftV]
  have hbd : ∃ c : Fv F v, c ≠ 0 ∧ ∀ l ∈ (latAtV G.V' G.W v).map (GlobalTheory.LatVac.locCo G.M'.co v), ∀ i,
      c * l.1 i ∈ v.adicCompletionIntegers F := by
    obtain ⟨c, hc0, hc⟩ := GlobalTheory.LatBound.locCo_latAtV_bounded G.V' G.W v G.M'.co hTr.geo.hV'.lat hTr.geo.hW.lat
    exact ⟨c, hc0, by rintro _ ⟨γ, hγ, rfl⟩ i; exact (hc γ hγ i).1⟩
  have hD := GlobalTheory.T.exists_second_coordinate_of_orthogonal_selfDual v (GlobalTheory.LatVac.psiAt B.ψ v) _ hsd hst hbd
  refine eq_smul_of_eigen (GlobalTheory.LatVac.psiAt B.ψ v) (fun γ : latAtV G.V' G.W v => GlobalTheory.LatVac.locCo G.M'.co v γ) cf
    (fun u hu => ?_) φ (G.M'.vac v) (hloc φ hφ hfix) (hloc _ (hTr.geo.hM'.vac v).1 hvac) (hTr.geo.hM'.vac v).2.1
  obtain ⟨y', γ, hγ, he⟩ := hD u (by
    rintro y ⟨γ, hγ, he⟩
    have h1 := hu ⟨γ, hγ⟩ (congrArg Prod.fst he)
    have h2 : (GlobalTheory.LatVac.locCo G.M'.co v γ).2 = y := congrArg Prod.snd he
    simp only at h1
    rw [h2] at h1
    exact h1)
  exact ⟨⟨γ, hγ⟩, congrArg Prod.fst he⟩

end GlobalTheory.VacUniqInert
