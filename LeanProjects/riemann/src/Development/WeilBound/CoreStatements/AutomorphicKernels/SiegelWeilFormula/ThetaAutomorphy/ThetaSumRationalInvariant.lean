import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AuxiliaryPrimeFunction
import Development.WeilBound.ThetaLifts.LeviDeterminants.WeilRepRationalDarbouxFixesThetaDistribution
import Development.WeilBound.ThetaLifts.LeviDeterminants.EqZeroOfTheta
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.ThetaSumTensorProduct
import Development.WeilBound.ThetaLifts.LatticeBasics.RatEquiv
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.CompFinFinOne

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Tauto

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

open PositivityTheory.ThKF0.Resc in
set_option maxHeartbeats 1000000 in

theorem split_core {m n : ℕ} {κ : Type} [Fintype κ] {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) {δ : E}
    (hq : IsQuad σ δ) (JA : Matrix (Fin m) (Fin m) E) (JB : Matrix (Fin n) (Fin n) E) (hA : IsHerm σ JA)
    (hB : IsHerm σ JB)
    (d' : Darboux (symp (R := AF F) (cA σ) (inclR (F := F) (AF F) δ) (incM F JA) (incM F (dbl JB))) κ)
    (d₀ : Matrix (Fin m) (Fin n ⊕ Fin n) E ≃ₗ[F] (κ → F) × (κ → F))
    (hd : ∀ x, d'.e (incM F x) = (fun i => algebraMap F (AF F) ((d₀ x).1 i), fun i => algebraMap F (AF F) ((d₀ x).2 i)))
    (χ : Chr F E) (hχ : IsHecke F E χ)
    (om' : UG (cA σ) (incM F (dbl JB)) →* Module.End ℂ ((κ → AF F) → ℂ))
    (hS : IsSplitting (adeleClass F) ψ d' (actB (cA σ)) om')
    (hR : SiegelRule (cA σ) (adeleClass F) ψ (inclR (F := F) (AF F) δ) (incM F JA) (incM F (dbl JB)) d' χ
      (diagCols (Fin n)) om')
    (g : UG (cA σ) (incM F (dbl JB)))
    (hg : ∃ γ₀ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) E,
      ((g : GL (Fin n ⊕ Fin n) (AE F E)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) = incM F γ₀) :
    ∀ Ψ ∈ schA F κ, thetaSum F (om' g Ψ) = thetaSum F Ψ := by
  haveI : Invertible (2 : F) := invertibleOfNonzero two_ne_zero
  have hL : IsLagr σ (dbl JB) (diagCols (Fin n)) := isLagr_diagCols (R := F) σ JB
  have hC : (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) E).map
      (fun z => ((1 : AF F) ⊗ₜ[F] z : AE F E)) = diagCols (Fin n) := by
    have e1 : (1 : Matrix (Fin n) (Fin n) E).map (fun z => ((1 : AF F) ⊗ₜ[F] z : AE F E)) = 1 :=
      Matrix.map_one _ (map_zero (inclR (F := F) (AF F))) (map_one (inclR (F := F) (AF F)))
    simp only [diagCols, Matrix.fromRows_map, e1]
  have hχ' : ∀ (z : E) (u : (AE F E)ˣ), (u : AE F E) = (1 : AF F) ⊗ₜ[F] z → χ u = 1 := fun z u hu => by
    have : Nontrivial (AF F) := (AdeleRing.algebraMap_injective (𝓞 F) F).nontrivial
    have : Nontrivial (AF F ⊗[F] E) := (Algebra.TensorProduct.includeRight_injective (A := AF F) (B := E)
      (algebraMap F (AF F)).injective).nontrivial
    have hz : z ≠ 0 := by
      rintro rfl
      exact u.ne_zero (by rw [hu, TensorProduct.tmul_zero])
    rw [show u = Units.map (inclR (F := F) (AF F)).toMonoidHom (Units.mk0 z hz) from Units.ext hu]
    exact hχ.2 _
  exact GlobalTheory.CompanionTheory.ThetaMember.split_of_eq F E σ δ (Fin m) (Fin n ⊕ Fin n) κ JA (dbl JB)
    ψ hψ.1 (PositivityTheory.ThKF0.isStd_ne_one hψ) hψ.2.1 hq hA (GlobalTheory.CompanionTheory.ThetaMember.isHerm_dbl hB)
    (incM F (dbl JB)) rfl d' d₀ hd χ (Fin n) (diagCols (Fin n)) (diagCols (Fin n)) hC om' hχ' hL hS hR g hg

omit [NumberField F] [NumberField E] in

theorem split_resc {R K : Type} [CommRing R] [CommRing K] [Algebra R K] [Invertible (2 : R)] {c : K →ₐ[R] K}
    {α β ν κ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype ν] [DecidableEq ν] [Fintype κ]
    {ξ ξ' u v : K} (h : ξ = ξ' * u * v) (hv : IsUnit v) {JA JA' : Matrix α α K} {JB JB' : Matrix β β K}
    (hA : JA' = u • JA) (hB : JB' = v • JB) {C : TestClass R} {ψ : AddChar R ℂ} {d : Darboux (symp c ξ JA JB) κ}
    {χ : Kˣ →* Circle} {Cy : Matrix β ν K} {om : UG c JB →* Module.End ℂ ((κ → R) → ℂ)}
    (hS : IsSplitting C ψ d (actB c) om) (hR : SiegelRule c C ψ ξ JA JB d χ Cy om) :
    ∃ (d' : Darboux (symp c ξ' JA' JB') κ) (om' : UG c JB' →* Module.End ℂ ((κ → R) → ℂ)), d'.e = d.e ∧
      IsSplitting C ψ d' (actB c) om' ∧ SiegelRule c C ψ ξ' JA' JB' d' χ Cy om' ∧
      ∀ g : UG c JB, ∃ g' : UG c JB', g'.1 = g.1 ∧ om' g' = om g := by
  subst hA hB
  have hU : UG c (v • JB) = UG c JB := PositivityTheory.ThKF0.Resc.ug_smul hv JB
  refine ⟨⟨d.e, fun w w' => (PositivityTheory.ThKF0.Resc.symp_smul h JA JB w w').trans (d.form w w')⟩,
    om.comp (Subgroup.inclusion hU.le), rfl,
    ⟨fun g => hS.pres _, fun g => hS.impl (Subgroup.inclusion hU.le g), fun g => hS.adm _⟩,
    fun l hl hinv p t hp => hR l hl hinv (Subgroup.inclusion hU.le p) t hp,
    fun g => ⟨Subgroup.inclusion hU.ge g, rfl, rfl⟩⟩

open PositivityTheory.ThKF0.Resc in
set_option maxHeartbeats 1000000 in

theorem theta_sum_rational_invariant (d : SD σ) (γ : d.G) (hγ : γ ∈ rat2 σ d.Y) (Ψ : d.Fn) (hΨ : Ψ ∈ d.sch) :
    thetaSum F (d.om γ Ψ) = thetaSum F Ψ := by
  have hσ : IsCMExt F E σ := d.cm
  have hψ : IsStd d.B.ψ := d.std
  have h2 : Module.finrank F E = 2 := hσ.2.2.1
  haveI : Invertible (2 : F) := invertibleOfNonzero two_ne_zero
  obtain ⟨δ, hq⟩ := exists_isQuad hσ
  have h0 : δ ≠ 0 := hq.unit.ne_zero
  obtain ⟨-, hS, hR⟩ := d.ok.dbl.weil

  have hYd : d.Y.J.det ≠ 0 := by
    obtain ⟨⟨ε, hε⟩, -⟩ := d.ok.frame
    intro hz
    have hee : ((ε : ℤ) : E) * ((ε : ℤ) : E) = 1 := by
      rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
    have hM : (Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E) *
        Matrix.fromBlocks 0 (((ε : ℤ) : E) • 1) 1 0 = 1 := by
      rw [Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]
      simp [smul_smul, hee]
    have h1 := congrArg Matrix.det hM
    rw [Matrix.det_mul, ← hε, Matrix.det_mul, Matrix.det_mul, dbl, Matrix.det_fromBlocks_zero₂₁, hz] at h1
    simp at h1

  have hκ : Fintype.card d.κ = Fintype.card (Fin d.m) * Fintype.card (Fin d.n ⊕ Fin d.n) := by
    have : Nontrivial (AF F) := (AdeleRing.algebraMap_injective (𝓞 F) F).nontrivial
    let bE : Module.Basis (Fin 2) F E := Module.finBasisOfFinrankEq F E h2
    let bA := Algebra.TensorProduct.basis (AF F) bE
    haveI : Module.Free (AF F) (AE F E) := Module.Free.of_basis bA
    haveI : Module.Finite (AF F) (AE F E) := Module.Finite.of_basis bA
    have e := d.dd.e.finrank_eq
    rw [Module.finrank_matrix, Module.finrank_eq_card_basis bA, Module.finrank_prod,
      Module.finrank_fintype_fun_eq_card] at e
    simp only [Fintype.card_fin, Fintype.card_sum] at e ⊢
    omega
  obtain ⟨d₀, hd₀⟩ := exists_ratCoord h2 hκ d.dd.e d.ok.dbl.rat

  obtain ⟨a, b, hab, hA, hB⟩ : ∃ a b : E, -1 = δ * a * b ∧ IsHerm σ (a • d.A.J) ∧ IsHerm σ (b • d.Y.J) := by
    rcases d.ok.sign with ⟨hA, hY⟩ | ⟨hA, hY⟩
    · refine ⟨1, -δ⁻¹, by field_simp, ?_, ?_⟩
      · rw [one_smul]; exact ⟨hA.herm, (herm_det hA).isUnit⟩
      · refine ⟨fun i j => by simp [hY i j, hq.anti], Ne.isUnit ?_⟩
        rw [Matrix.det_smul]
        exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 (inv_ne_zero h0))) hYd
    · refine ⟨-δ⁻¹, 1, by field_simp, ?_, ?_⟩
      · refine ⟨fun i j => by simp [hA.skew i j, hq.anti], Ne.isUnit ?_⟩
        rw [Matrix.det_smul]
        exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 (inv_ne_zero h0))) (skew_det hA)
      · rw [one_smul]; exact ⟨hY, hYd.isUnit⟩
  have hb : b ≠ 0 := by
    rintro rfl
    simp at hab
  have hξ : (-1 : AE F E) = inclR (F := F) (AF F) δ * inclR (F := F) (AF F) a * inclR (F := F) (AF F) b := by
    rw [← map_mul, ← map_mul, ← hab, map_neg, map_one]
  have hJA : incM F (a • d.A.J) = inclR (F := F) (AF F) a • incM F d.A.J := by
    ext i j; simp [incM]
  have hJB : incM F (dbl (b • d.Y.J)) = inclR (F := F) (AF F) b • dbl (incM F d.Y.J) := by
    ext (i | i) (j | j) <;> simp [incM, dbl]
  obtain ⟨d', om', he, hS', hR', hgg⟩ := split_resc (c := cA σ) (C := adeleClass F) (ψ := d.B.ψ) (κ := d.κ) hξ
    (hb.isUnit.map (inclR (F := F) (AF F))) hJA hJB hS.toIsSplitting hR
  have hd' : ∀ x, d'.e (incM F x) = (fun i => algebraMap F (AF F) ((d₀ x).1 i), fun i => algebraMap F (AF F) ((d₀ x).2 i)) :=
    fun x => by rw [he]; exact hd₀ x
  obtain ⟨g', hg'1, hg'2⟩ := hgg γ
  have hg : ∃ γ₀ : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E,
      ((g' : GL (Fin d.n ⊕ Fin d.n) (AE F E)) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) = incM F γ₀ := by
    obtain ⟨g₀, hg₀⟩ := Subgroup.mem_subgroupOf.mp hγ
    refine ⟨g₀, ?_⟩
    rw [hg'1, ← hg₀]
    rfl
  rw [← hg'2]
  exact split_core hψ hq (a • d.A.J) (b • d.Y.J) hA hB d' d₀ hd' d.χ d.ok.hecke om' hS' hR' g' hg Ψ hΨ

end PositivityTheory.SiegelWeilFormula.Tauto

end
