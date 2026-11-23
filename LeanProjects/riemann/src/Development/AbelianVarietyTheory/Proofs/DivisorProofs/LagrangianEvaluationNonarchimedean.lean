import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ConjugateOrderData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPlaceRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SzPeriodsOfTangent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyOfForall
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLinearOfIsMonHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EllipticCurveGoodReductionModelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentPullbackEllipticModelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralLatticeLAdicReductionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyGoodReductionExtensionStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)

attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.LatModel.exists_isogModel : GlobalTheory.Published.SerreTateGoodReductionSt → GlobalTheory.Published.AbelianDualCrystal →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (I : Type) [Fintype I] (d : ℕ)
    (φ : I → E →+* ℂ), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData d φ → ∀ (𝔣 : Ideal (OF E)) (Λ : PeriodPair), IsBaseCond 𝔣 →
    GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsIntLattice d Λ →
    ∀ (l : ℕ) [Fact l.Prime] (Q : Finset (HeightOneSpectrum (OF E))), IsFinSetSplitPlacesCoprimeConductor 𝔣 Q → (∀ q ∈ Q, (l : OF E) ∉ q.asIdeal) →
    ∀ y : (Af E)ˣ, OneOver l y → ∀ (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (Ω : ℂ), Ω ^ 12 = latDisc Λ →
    ∀ (𝔠 : FracId (FR E)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (U : Unif φ (lattice (condQ 𝔣 Q) y) 0 X),
    ∃ (k₀ : IntermediateField ℚ ℂ) (R₀ : Subring ℂ), FiniteDimensional ℚ k₀ ∧ IsPlaceOver l lam k₀ R₀ ∧
      (∀ x ∈ R₀, x ∈ k₀) ∧
      ∃ (G₀ : Over (Sp R₀)) (_ : GrpObj G₀) (p₀ : X.A.left ⟶ G₀.left) (P₀ : Out.PolAV (Sp R₀)) (Ψ₀ : P₀.A ⟶ G₀),
        IsAbelianScheme G₀ ∧ IsGrpPullback X.A G₀ (spMap R₀.subtype) p₀ ∧ IsMonHom Ψ₀ ∧ IsFinite Ψ₀.left ∧
        Flat Ψ₀.left ∧ Surjective Ψ₀.left ∧
        ∀ i : I, ∃ (v₀ : epsR R₀ ⟶ G₀) (v' : X.Lie) (W : Fin (Module.finrank ℚ (FR E)) → ℂ),
          IsTangent v₀ ∧ v'.hom.left ≫ p₀ = spMap (Chart.dualMapR R₀.subtype) ≫ v₀.left ∧ U.u.IsDiff W v'.hom ∧
          W (U.e.symm i) ≠ 0 ∧ Sz l lam (a0 𝔣 l) ((W (U.e.symm i) * Ω)⁻¹) := by
  intro hST hAD E _ _ _ _ I _ d φ hF 𝔣 Λ h𝔣 hΛ l _ Q hQ hQl y hy lam Ω hΩ 𝔠 X U
  have hf : 0 < Module.finrank ℚ (FR E) := Module.finrank_pos
  let j₀ : Fin (Module.finrank ℚ (FR E)) := ⟨0, hf⟩
  obtain ⟨k₁, R₁, hk₁, hR₁, hR₁k, P₁, A₁, _, φ₁, L₁, u₁, v₁, v₁', t, hA₁, hdim₁, hpb₁, hΛ₁, hv₁, hv₁', hvv₁, hd₁, ht, hsz⟩ :=
    GlobalTheory.T.elliptic_curve_good_reduction_model hST d Λ hF.1 hΛ l lam Ω hΩ
  obtain ⟨P, A', _, φ', L', u, v, v', hA', hdim, hpb, hΛu, hv, hv', hvv, hd⟩ :=
    GlobalTheory.T.tangent_pullback_elliptic_model R₁ R₁.subtype P₁ A₁ φ₁ L₁ u₁ v₁ v₁' t Λ.lattice hA₁ hdim₁ hpb₁ hΛ₁ hv₁ hv₁' hvv₁ hd₁
      (Module.finrank ℚ (FR E)) j₀
  obtain ⟨α, M, n, N, hα, hfin, hflat, hsurj, hN, hker, hM, hMj, hn, hszn⟩ :=
    GlobalTheory.T.integral_lattice_l_adic_reduction E I d φ hF 𝔣 Λ h𝔣 hΛ l Q hQ hQl y hy lam 𝔠 X U A' L' u hA' hdim hΛu j₀
  obtain ⟨k₀, R₀, hk₀, hR₀, hR₀k, G₀, _, p₀, P₀, Ψ₀, hG₀, hp₀, hΨ, hΨf, hΨfl, hΨs, htan⟩ :=
    GlobalTheory.T.isogeny_good_reduction_extension l lam k₁ R₁ hk₁ hR₁ hR₁k P A' φ' hpb X.A α N X.ab hα hfin hflat hsurj hN hker
  refine ⟨k₀, R₀, hk₀, hR₀, hR₀k, G₀, inferInstance, p₀, P₀, Ψ₀, hG₀, hp₀, hΨ, hΨf, hΨfl, hΨs, fun i ↦ ?_⟩
  obtain ⟨v₀, hv₀, hc⟩ := htan v v' hv hvv
  have hαt : IsTangent (v' ≫ α) := GlobalTheory.HomLinear.isTangent_comp α hv'
  have hW : M (Pi.single j₀ t) = fun _ ↦ t * (n : ℂ) := by
    have : (Pi.single j₀ t : Fin (Module.finrank ℚ (FR E)) → ℂ) = t • Pi.single j₀ 1 := by
      rw [← Pi.single_smul, smul_eq_mul, _root_.mul_one]
    rw [this, map_smul, hMj]
    rfl
  refine ⟨v₀, GlobalTheory.Serre.Lie.mk X.rm (v' ≫ α) hαt, M (Pi.single j₀ t), hv₀, ?_, ?_, ?_, ?_⟩
  · simpa using hc
  · simpa using GlobalTheory.HomLinear.isDiff_comp u U.u α M hM hv' hd
  · rw [hW]
    exact mul_ne_zero ht (by exact_mod_cast hn.ne')
  · rw [hW]
    have e : (t * (n : ℂ) * Ω)⁻¹ = (n : ℂ)⁻¹ * (t * Ω)⁻¹ := by
      rw [show t * (n : ℂ) * Ω = (n : ℂ) * (t * Ω) by ring, _root_.mul_inv]
    rw [e]
    simpa using GlobalTheory.LatValRam.sz_mul hszn hsz
