import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledUnitaryCharacterTrivialOfSiegelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryDoubledBlockDiagOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductFunctionOnSumCoordsMemAdelicSchwartzSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianSelfDualLatticeSpaceFormHermitianNondeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlanePairRestrictionFirstStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlanePairRestrictionSecondStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlanePairRestrictionThirdStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section
namespace GlobalTheory.MixXUWChar

theorem boxFun_smul_left {F : Type} [Field F] [NumberField F] {κ κ' : Type} (a : ℂ) (f : (κ → AF F) → ℂ) (g : (κ' → AF F) → ℂ) :
    boxFun (a • f) g = a • boxFun f g := by
  funext x; simp [boxFun, mul_assoc]

theorem boxFun_ne_zero {F : Type} [Field F] [NumberField F] {κ κ' : Type} {f : (κ → AF F) → ℂ} {g : (κ' → AF F) → ℂ} (hf : f ≠ 0) (hg : g ≠ 0) :
    boxFun f g ≠ 0 := by
  obtain ⟨x₁, hx₁⟩ := Function.ne_iff.mp hf
  obtain ⟨x₂, hx₂⟩ := Function.ne_iff.mp hg
  intro h0
  have h := congrFun h0 (Sum.elim x₁ x₂)
  simp only [boxFun, Pi.zero_apply] at h
  exact mul_ne_zero hx₁ hx₂ (by simpa [Function.comp_def] using h)

theorem apply_ne_zero {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : G →* Module.End ℂ V) (g : G)
    {v : V} (hv : v ≠ 0) : ρ g v ≠ 0 := by
  intro h0
  apply hv
  have := congrArg (ρ g⁻¹) h0
  rwa [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply, map_zero] at this

theorem char_eq_one : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ) (M₁ : Model σ X₁ W) (om₁ : Rep σ X₁ W) (r₁ s₁ : ℕ),
      H.IsAdapted σ B X X₁ j₀ j₁ → IsPair B M₁ χX χW om₁ r₁ s₁ r' s' →
      ∀ e, IsEv B M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e →
      (∃ Φ ∈ schA F (Fin n × Fin d), e Φ ≠ 0) →
      ∀ c : UA σ W.J →* ℂˣ, (∀ h, ∀ Φ ∈ schA F (Fin n × Fin d), e (om (1, h) Φ) = (c h : ℂ) • om₁ (1, h) (e Φ)) → c = 1 := by
  intro hPr F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hH hp₁ e he hne c hc
  obtain ⟨⟨hspl, dd, omd, hdd, hws, hbox⟩, -, -⟩ := hp.weil
  obtain ⟨⟨-, dd₁, omd₁, hdd₁, hws₁, hbox₁⟩, -, -⟩ := hp₁.weil
  obtain ⟨ed, e₂, hmaps, hheis, hinv, hwc, hbx, he₂, φ₂, hφ₂, hφ₂ne⟩ :=
    GlobalTheory.T.adapted_plane_pair_restriction_first hPr F E σ B n d X W M χX χW om r s r' s' hp n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hH hp₁ e he hne dd dd₁ hdd hdd₁
  obtain ⟨Φ₀, hΦ₀, hΦ₀ne⟩ := hne
  have hboxs : boxFun Φ₀ φ₂ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d) :=
    GlobalTheory.SchwartzBox.boxFun_mem_schA F _ _ Φ₀ hΦ₀ φ₂ hφ₂
  have hedne : ed (boxFun Φ₀ φ₂) ≠ 0 := by
    rw [hbx Φ₀ hΦ₀ φ₂ hφ₂]; exact boxFun_ne_zero hΦ₀ne hφ₂ne
  obtain ⟨cd, hcd, hlaw⟩ := GlobalTheory.T.adapted_plane_pair_restriction_second hPr F E σ B n d X W M χX χW om r s r' s' hp n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hH hp₁ e he
    ⟨Φ₀, hΦ₀, hΦ₀ne⟩ dd dd₁ hdd hdd₁ omd omd₁ hws.2.1 hws₁.2.1 ed hmaps hheis hinv hwc ⟨_, hboxs, hedne⟩
  have hdet : W.J.det ≠ 0 := by
    obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
    have h := GlobalTheory.WeilSchrodingerHerm.det_ne_zero_of_hasSig (hp.skew.sig w)
    intro h0
    apply h
    have hm : (W.J.map (B.emb w).1).det = (B.emb w).1 W.J.det := (RingHom.map_det _ _).symm
    rw [Matrix.det_smul, hm, h0, map_zero, mul_zero]
  have hcd1 : cd = 1 := GlobalTheory.T.doubledUnitary_character_trivial_of_siegel F E σ hp.base.cm d W.J (-1) (fun i j => by simp [hp.skew.skew i j]) hdet cd hcd
    (fun p t hpt => Units.ext (by
      simpa using GlobalTheory.T.adapted_plane_pair_restriction_third hPr F E σ B n d X W M χX χW om r s r' s' hp n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hH hp₁ e he
        ⟨Φ₀, hΦ₀, hΦ₀ne⟩ dd dd₁ hdd hdd₁ omd omd₁ hws hws₁ ed hmaps hheis hinv hwc ⟨_, hboxs, hedne⟩ p t hpt
        (cd p) (hlaw p)))
  refine MonoidHom.ext fun h => Units.ext ?_
  obtain ⟨gd, hgd⟩ := GlobalTheory.unitary_diag_one_mem_dbl (AF F) (AE F E) (cA σ) (Fin d) (incM F W.J) h
  have h2 := hlaw gd (boxFun Φ₀ φ₂) hboxs
  rw [hcd1, hbox h gd hgd Φ₀ hΦ₀ φ₂ hφ₂, MonoidHom.one_apply, Units.val_one, one_smul, MonoidHom.comp_apply,
    MonoidHom.inr_apply, hbx _ (show om (1, h) Φ₀ ∈ schA F (Fin n × Fin d) from hspl.pres h Φ₀ hΦ₀) φ₂ hφ₂, hc h Φ₀ hΦ₀, hbx Φ₀ hΦ₀ φ₂ hφ₂,
    hbox₁ h gd hgd (e Φ₀) (he.maps Φ₀ hΦ₀) (e₂ φ₂) (he₂ φ₂ hφ₂), MonoidHom.comp_apply, MonoidHom.inr_apply,
    boxFun_smul_left] at h2
  have hv : boxFun (om₁ (1, h) (e Φ₀)) (e₂ φ₂) ≠ 0 := boxFun_ne_zero (apply_ne_zero om₁ _ hΦ₀ne) hφ₂ne
  have := smul_left_injective ℂ hv (h2.trans (one_smul ℂ _).symm)
  simpa using this

end GlobalTheory.MixXUWChar
