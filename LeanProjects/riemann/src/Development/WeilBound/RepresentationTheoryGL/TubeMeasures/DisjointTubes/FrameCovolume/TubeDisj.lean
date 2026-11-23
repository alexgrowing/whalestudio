import Development.WeilBound.RepresentationTheoryGL.TubeMeasures.DisjointTubes.TubeSt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquivalenceGeneratedTorusRel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticGroupConjRationalPrincipalCongruence
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalCongruenceConjMemArithmeticGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetEqOneUnitaryPrincipalCongruenceLevelThreeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsInvertibleUnitaryAdelicMatrixOfRationalUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndefiniteFrameRealSpecialUnitary
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.MuCardLeTwo
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

namespace MainStatements.Tam.T2

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem tube_disj (D : D7) (V : HSp D) (θ : InfFam D) (A : Frames V) (rp : GA D V →* (∀ ρ, Upq V ρ))
    (Ψ : Finset (D.host.E →+* ℂ)) (Gm : Matrix (Fin V.rank) (Fin V.rank) D.host.E) (σ : D.what₂.Tau ≃ Ψ)
    (π : (∀ ρ, Upq V ρ) → realSU Ψ Gm) (M : ℕ) (ι : Type) (X : ι → Data D.host.E V.rank) (g : ι → GA D V)
    (F : ι → Set (realSU Ψ Gm))
    (hM : 3 ≤ M) (hGm : Gm = -(V.gram)ᵀ) (hθ : IsInfFam θ) (hrp : IsRealPart V θ A rp)
    (hσ : ∀ ρ, (σ ρ).1 = tauE D ρ)
    (heq : ∀ (s' : realSU Ψ Gm) (b₀ : ∀ ρ, Upq V ρ), (∀ ρ, UpqT.mat (b₀ ρ) * A ρ =
      A ρ * ((s'.1 (σ ρ) : GL (Fin V.rank) ℂ) : Matrix (Fin V.rank) (Fin V.rank) ℂ)) → ∀ b, π (b₀ * b) = s' * π b)
    (hF : ∀ k, ∀ γ ∈ inReal Ψ Gm (X k).Γ, ∀ y ∈ F k, γ * y ∈ F k → γ = 1)
    (hdist : ∀ k k', UEquiv (IsCMField.complexConj D.host.E) (-(V.gram)ᵀ)
      (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) M
      ((finHom V (g k)).1 : Matrix (Fin V.rank) (Fin V.rank) (RA (maximalRealSubfield D.host.E) D.host.E)) ((finHom V (g k')).1 : Matrix (Fin V.rank) (Fin V.rank) (RA (maximalRealSubfield D.host.E) D.host.E)) → k = k')
    (hXG : ∀ k, (X k).Gm = -(V.gram)ᵀ)
    (hXΛ : ∀ k, ((X k).Λ : Set (Fin V.rank → D.host.E)) = latOf (maximalRealSubfield D.host.E)
      ((finHom V (g k)).1 : Matrix (Fin V.rank) (Fin V.rank) (RA (maximalRealSubfield D.host.E) D.host.E)) (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)))
    (hXΓ : ∀ k γ, γ ∈ (X k).Γ ↔ IsUStab (X k).Gm (X k).Λ γ ∧ ∀ x ∈ (X k).Λ, ∃ y ∈ (X k).Λ,
      (γ : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ x - x = M • y) :
    ∀ δ ∈ GQ V, ∀ (k k' : ι) (y : GA D V), ((g k)⁻¹ * y ∈ KM V M ∧ π (rp y) ∈ F k) →
      ((g k')⁻¹ * (δ * y) ∈ KM V M ∧ π (rp (δ * y)) ∈ F k') → δ = 1 ∧ k = k' := by
  intro δ hg k k' y hy hgy
  classical
  obtain ⟨δ0, hδU, hδeq⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hg)
  have hmat : matHom V δ = Formalism.UG.bc (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F)) δ0 := hδeq.symm
  have h1 : (matHom V δ).1 = (δ0 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map
      (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F)) := by rw [hmat]; rfl
  have hinf : ∀ ρ, infMat D.sp.cm.sig V.gram (θ ρ) δ = (δ0 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (tauE D ρ) := by
    intro ρ
    have hinc : ((δ0 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Ainf D.host.F))).map (θ ρ) =
        (δ0 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (tauE D ρ) := by
      ext a b
      exact (hθ ρ).1 _
    rw [← hinc, ← GlobalTheory.UnitaryGlue.map_map_inclR (fstA D.host.F), ← h1]; rfl
  have hfin : (finHom V δ).1 = (δ0 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (inclR (Af D.host.F)) := by
    rw [← GlobalTheory.UnitaryGlue.map_map_inclR (sndA D.host.F), ← h1]; rfl
  have hfinv : (finHom V δ⁻¹).1 = ((δ0⁻¹ : GL (Fin V.rank) D.host.E) : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map
      (inclR (Af D.host.F)) := by
    rw [map_inv]
    apply Units.inv_eq_of_mul_eq_one_left
    rw [hfin, ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    exact Matrix.map_one _ (map_zero _) (map_one _)

  have hU : ((δ0 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map cc)ᵀ * V.gram * δ0.1 = V.gram := by
    change Formalism.UG.cT _ δ0.1 * V.gram * δ0.1 = V.gram at hδU
    convert hδU using 3
    ext a b
    simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply]
    congr 1
  have hmatG : δ0.1ᵀ * -(V.gram)ᵀ * δ0.1.map cc = -(V.gram)ᵀ := by
    have := congrArg (fun A => -Aᵀ) hU
    simpa [Matrix.transpose_mul, Matrix.mul_assoc, Matrix.neg_mul, Matrix.mul_neg] using this
  have hherm := GlobalTheory.MsRepsFwd.herm_mulVec _ _ hmatG

  have hmulKM : ∀ a b, a ∈ KM V M → b ∈ KM V M → a * b ∈ KM V M := fun a b ha hb => by
    show IsKM _ _ _ _ ((finHom V (a * b)).1 : Matrix (Fin V.rank) (Fin V.rank) (RA (maximalRealSubfield D.host.E) D.host.E))
    rw [map_mul, Units.val_mul]
    exact GlobalTheory.UCls.isKM_mul ha hb
  have hinvKM : ∀ a, a ∈ KM V M → a⁻¹ ∈ KM V M := fun a ha => by
    show IsKM _ _ _ _ ((finHom V a⁻¹).1 : Matrix (Fin V.rank) (Fin V.rank) (RA (maximalRealSubfield D.host.E) D.host.E))
    rw [map_inv, Matrix.coe_units_inv]
    exact GlobalTheory.UCls.isKM_inv ha
  have hκ : (g k')⁻¹ * δ * g k ∈ KM V M := by
    have e : (g k')⁻¹ * δ * g k = ((g k')⁻¹ * (δ * y)) * ((g k)⁻¹ * y)⁻¹ := by group
    rw [e]; exact hmulKM _ _ hgy.1 (hinvKM _ hy.1)
  have hκ' : (g k)⁻¹ * δ⁻¹ * g k' ∈ KM V M := by
    have e : (g k)⁻¹ * δ⁻¹ * g k' = ((g k)⁻¹ * y) * ((g k')⁻¹ * (δ * y))⁻¹ := by group
    rw [e]; exact hmulKM _ _ hy.1 (hinvKM _ hgy.1)
  have hUA : IsUA (IsCMField.complexConj D.host.E) (-(V.gram)ᵀ) (ratM (maximalRealSubfield D.host.E) δ0.1) :=
    GlobalTheory.T.isInvertibleUnitaryAdelicMatrix_of_rational_unitary D.host.E V.rank _ δ0.1 (Matrix.isUnits_det_units δ0).ne_zero hherm
  have hratM : ratM (maximalRealSubfield D.host.E) δ0.1 = δ0.1.map (inclR (Af D.host.F)) := rfl
  have hkk : k = k' := hdist k k' ⟨δ0.1, hUA, (finHom V ((g k)⁻¹ * δ⁻¹ * g k')).1, hκ', by
    rw [hratM, ← hfin, ← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul]
    congr 2
    group⟩
  cases hkk

  haveI : Nontrivial (Af D.host.F) := by
    obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 D.host.F)
    exact (Formalism.UG.evalV D.host.F ⟨P, hP.isPrime,
      Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField D.host.F)⟩).toRingHom.domain_nontrivial
  haveI : Nontrivial (Af D.host.F ⊗[D.host.F] D.host.E) :=
    (Algebra.TensorProduct.includeLeft_injective (R := D.host.F) (S := D.host.F) (A := Af D.host.F) (B := D.host.E)
      (algebraMap D.host.F D.host.E).injective).nontrivial
  have hinj : Function.Injective (inclR (F := D.host.F) (E := D.host.E) (Af D.host.F)) :=
    (inclR (F := D.host.F) (E := D.host.E) (Af D.host.F)).injective
  have he1 : δ0.1.map (inclR (F := D.host.F) (Af D.host.F)) * (finHom V (g k)).1 =
      (finHom V (g k)).1 * (finHom V ((g k)⁻¹ * δ * g k)).1 := by
    rw [← hfin, ← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul]
    congr 2
    group
  have he2 : (δ0⁻¹ : GL (Fin V.rank) D.host.E).1.map (inclR (F := D.host.F) (Af D.host.F)) * (finHom V (g k)).1 =
      (finHom V (g k)).1 * (finHom V ((g k)⁻¹ * δ⁻¹ * g k)).1 := by
    rw [← hfinv, ← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul]
    congr 2
    group
  have C1 := GlobalTheory.MsRepsFwd.latOf_congr D.host.F D.host.E V.rank M (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E))
    (finHom V (g k)).1 (finHom V ((g k)⁻¹ * δ * g k)).1 δ0.1 hinj hκ.2.1 he1
  have C2 := GlobalTheory.MsRepsFwd.latOf_congr D.host.F D.host.E V.rank M (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E))
    (finHom V (g k)).1 (finHom V ((g k)⁻¹ * δ⁻¹ * g k)).1 (δ0⁻¹ : GL (Fin V.rank) D.host.E).1 hinj hκ'.2.1 he2
  have hmem : ∀ x, x ∈ (X k).Λ ↔ x ∈ GlobalTheory.AdLat.latOf D.host.F (finHom V (g k)).1
      (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) := by
    intro x
    rw [← SetLike.mem_coe, hXΛ k]
  have hcong : ∀ x ∈ (X k).Λ, ∃ y ∈ (X k).Λ, δ0.1 *ᵥ x - x = M • y := by
    intro x hx
    obtain ⟨y, hy, e⟩ := C1 x ((hmem x).1 hx)
    exact ⟨y, (hmem y).2 hy, e⟩
  have hcong' : ∀ x ∈ (X k).Λ, ∃ y ∈ (X k).Λ, (δ0⁻¹ : GL (Fin V.rank) D.host.E).1 *ᵥ x - x = M • y := by
    intro x hx
    obtain ⟨y, hy, e⟩ := C2 x ((hmem x).1 hx)
    exact ⟨y, (hmem y).2 hy, e⟩
  have hstab : ∀ x, x ∈ (X k).Λ ↔ δ0.1 *ᵥ x ∈ (X k).Λ := by
    intro x
    constructor
    · intro hx
      obtain ⟨y, hy, e⟩ := hcong x hx
      rw [show δ0.1 *ᵥ x = x + M • y by rw [← e]; abel]
      exact (X k).Λ.add_mem hx (nsmul_mem hy M)
    · intro hx
      obtain ⟨y, hy, e⟩ := hcong' _ hx
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec] at e
      rw [show x = δ0.1 *ᵥ x + M • y by rw [← e]; abel]
      exact (X k).Λ.add_mem hx (nsmul_mem hy M)
  have hΓ : δ0 ∈ (X k).Γ := (hXΓ k δ0).2 ⟨⟨by rw [hXG k]; exact hherm, hstab⟩, hcong⟩
  have hd1 : (δ0 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).det = 1 :=
    GlobalTheory.T.det_eq_one_unitary_principal_congruence_level_three D.host.E V.rank M (X k) hM (hXΓ k) δ0 hΓ

  have hmemSU : embGL Ψ V.rank δ0 ∈ realSU Ψ Gm := embGL_mem_realSU Ψ Gm δ0 hd1 (by rw [hGm]; exact hherm)
  have hin : (⟨embGL Ψ V.rank δ0, hmemSU⟩ : realSU Ψ Gm) ∈ inReal Ψ Gm (X k).Γ :=
    Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨δ0, hΓ, rfl⟩)
  have heqv := heq ⟨embGL Ψ V.rank δ0, hmemSU⟩ (rp δ) (fun ρ => by
    rw [hrp δ ρ, hinf ρ]
    show _ = A ρ * (δ0 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (σ ρ).1
    rw [hσ ρ]) (rp y)
  have hs1 := hF k _ hin (π (rp y)) hy.2 (by rw [← heqv, ← map_mul]; exact hgy.2)
  have hf : 1 ≤ D.R.f := by unfold Ranks.f Ranks.n; have := And.intro (Nat.one_le_two_pow (n := D.R.e)) (show 0 < D.R.ord by positivity); omega
  obtain ⟨ρ₀⟩ : Nonempty D.what₂.Tau := by
    rw [← Fintype.card_pos_iff, D.what₂.card_Tau]; omega
  have hδ1 : δ0 = 1 := by
    have h5 := congrArg (fun s : realSU Ψ Gm => ((s.1 (σ ρ₀) : GL (Fin V.rank) ℂ) : Matrix (Fin V.rank) (Fin V.rank) ℂ)) hs1
    have h6 : (δ0 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (σ ρ₀).1 =
        (1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (σ ρ₀).1 := by
      rw [Matrix.map_one _ (map_zero _) (map_one _)]
      exact h5
    exact Units.ext (Matrix.map_injective (σ ρ₀).1.injective h6)
  refine ⟨Subtype.ext ?_, rfl⟩
  rw [hδ1, map_one] at hmat
  exact hmat

end MainStatements.Tam.T2
