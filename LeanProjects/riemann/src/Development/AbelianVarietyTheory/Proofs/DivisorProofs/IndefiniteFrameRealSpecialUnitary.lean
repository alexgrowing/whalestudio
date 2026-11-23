import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PermMMulTranspose
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianHaarIndependentOfOrthonormalFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalCongruenceConjMemArithmeticGroup
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpqLocallyCompactGroup
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocallyCompactSecondCountableBorelCountable
import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.Sector
import Development.AutomorphicArithmetic.CyclotomicBounds.RootsOfUnity.HostTorsionOrderLe
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryExistsWithPrescribedParts

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory.TubePack

theorem det_eq_of_intertwine {ι : Type} [Fintype ι] [DecidableEq ι] {r : ℕ} (e : ι ≃ Fin r)
    (U : Matrix ι ι ℂ) (A : Matrix ι (Fin r) ℂ) (B : Matrix (Fin r) ι ℂ) (M : Matrix (Fin r) (Fin r) ℂ)
    (hAB : A * B = 1) (h : U * A = A * M) : U.det = M.det := by
  have hBA : B * A = 1 := (Matrix.mul_eq_one_comm_of_equiv e).1 hAB
  have hM : M = B * U * A := by
    rw [Matrix.mul_assoc, h, ← Matrix.mul_assoc, hBA, Matrix.one_mul]
  have h1 : B * U * A = (B.submatrix id e.symm * U.submatrix e.symm e.symm) * A.submatrix e.symm id := by
    rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id]
  have h2 : A.submatrix e.symm id * B.submatrix id e.symm = 1 := by
    have h0 := Matrix.submatrix_mul_equiv A B (⇑e.symm) (Equiv.refl (Fin r)) (⇑e.symm)
    rw [hAB, Matrix.submatrix_one_equiv] at h0
    exact h0
  have h3 : (A.submatrix e.symm id).det * (B.submatrix id e.symm).det = 1 := by
    rw [← Matrix.det_mul, h2, Matrix.det_one]
  rw [hM, h1, Matrix.det_mul, Matrix.det_mul, Matrix.det_submatrix_equiv_self]
  linear_combination (-U.det) * h3

theorem herm_neg {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (G : Matrix (Fin r) (Fin r) E)
    (x y : Fin r → E) : herm (-G) x y = -herm G x y := by
  simp only [herm, Matrix.neg_apply, mul_neg, neg_mul, Finset.sum_neg_distrib]

theorem tube_disjoint : ∀ (D : D7) (V : HSp D) (θ : InfFam D) (A : Frames V) (rp : GA D V →* (∀ ρ, Upq V ρ)) (Ψ : Finset (D.host.E →+* ℂ)) (Gm : Matrix (Fin V.rank) (Fin V.rank) D.host.E) (x₀ : Frame Ψ V.rank) (σ : D.what₂.Tau ≃ Ψ) (e : ∀ ρ : D.what₂.Tau, Fin (V.sig (tauE D ρ)).1 ⊕ Fin (V.sig (tauE D ρ)).2 ≃ Fin V.rank) (π : (∀ ρ, Upq V ρ) → realSU Ψ Gm) (K : Subgroup (GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D))) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (J : Type) (s : J → Matrix (Fin V.rank) (Fin V.rank) (RA (maximalRealSubfield D.host.E) D.host.E)) (h : J → GA D V) (F : J → Set (realSU Ψ Gm)) (ρ₀ : D.what₂.Tau), Gm = -(V.gram)ᵀ → IsInfFam θ → IsRealPart V θ A rp → IsIdent (fun ρ => (V.sig (tauE D ρ)).1) (fun ρ => (V.sig (tauE D ρ)).2) Ψ Gm x₀ σ A e → (∀ ρ, (σ ρ).1 = tauE D ρ) → (∀ (s' : realSU Ψ Gm) (b₀ : ∀ ρ, Upq V ρ), (∀ ρ, UpqT.mat (b₀ ρ) * A ρ = A ρ * ((s'.1 (σ ρ) : GL (Fin V.rank) ℂ) : Matrix (Fin V.rank) (Fin V.rank) ℂ)) → ∀ b, π (b₀ * b) = s' * π b) → (∀ j, ∀ γ ∈ inReal Ψ Gm (ratStab (V.gram)ᵀ (Λ : Set (Fin V.rank → D.host.E)) (s j)), ∀ y ∈ F j, γ * y ∈ F j → γ = 1) → (∀ (j j' : J) (g : GA D V) (γ : GL (Fin V.rank) D.host.E), g ∈ GQ V → matHom V g = Formalism.UG.bc (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F)) γ → finE V ((h j')⁻¹ * g * h j) ∈ K → IsIntegral ℤ (γ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).det ∧ ((γ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).det = 1 → j = j')) → (∀ (j : J) (g : GA D V) (γ : GL (Fin V.rank) D.host.E), g ∈ GQ V → matHom V g = Formalism.UG.bc (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F)) γ → (γ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).det = 1 → finE V ((h j)⁻¹ * g * h j) ∈ K → γ ∈ ratStab (V.gram)ᵀ (Λ : Set (Fin V.rank → D.host.E)) (s j)) → ∀ g ∈ GQ V, ∀ (j j' : J) (y : GA D V), (finE V ((h j)⁻¹ * y) ∈ K ∧ π (rp y) ∈ F j ∧ 0 < (UpqT.mat (rp y ρ₀)).det.im) → (finE V ((h j')⁻¹ * (g * y)) ∈ K ∧ π (rp (g * y)) ∈ F j' ∧ 0 < (UpqT.mat (rp (g * y) ρ₀)).det.im) → UpperTheory.Ram.Sector.sec (NumberField.Units.torsionOrder D.host.E) (UpqT.mat (rp y ρ₀)).det = UpperTheory.Ram.Sector.sec (NumberField.Units.torsionOrder D.host.E) (UpqT.mat (rp (g * y) ρ₀)).det → g = 1 ∧ j = j' := by
  intro D V θ A rp Ψ Gm x₀ σ e π K Λ J s h F ρ₀ hGm hθ hrp hid hσ heq hF hlink1 hlink2 g hg j j' y hy hgy hsec
  obtain ⟨δ, hδU, hδeq⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hg)
  have hmat : matHom V g = Formalism.UG.bc (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F)) δ := hδeq.symm
  have h1 : (matHom V g).1 = (δ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F)) := by rw [hmat]; rfl
  have hinf : ∀ ρ, infMat D.sp.cm.sig V.gram (θ ρ) g = (δ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (tauE D ρ) := by
    intro ρ
    have hinc : ((δ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Ainf D.host.F))).map (θ ρ) = (δ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (tauE D ρ) := by
      ext a b
      exact (hθ ρ).1 _
    rw [← hinc, ← GlobalTheory.UnitaryGlue.map_map_inclR (fstA D.host.F), ← h1]; rfl
  have hK : finE V ((h j')⁻¹ * g * h j) ∈ K := by
    have := K.mul_mem hgy.1 (K.inv_mem hy.1)
    rw [← map_inv, ← map_mul] at this
    convert this using 2
    group
  obtain ⟨hint, hdj⟩ := hlink1 j j' g δ hg hmat hK
  have hconj : ∀ (τ : D.host.E →+* ℂ) (x : D.host.E), τ ((D.sp.cm.sig : D.host.E →+* D.host.E) x) = starRingEnd ℂ (τ x) := fun τ x => IsCMField.complexEmbedding_complexConj D.host.E τ x
  have hU' : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (δ : Matrix (Fin V.rank) (Fin V.rank) D.host.E) * V.gram * (δ : Matrix (Fin V.rank) (Fin V.rank) D.host.E) = V.gram := hδU
  have hdd : (D.sp.cm.sig : D.host.E →+* D.host.E) (δ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).det * (δ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).det = 1 := by
    have h2 := congrArg Matrix.det hU'
    rw [Matrix.det_mul, Matrix.det_mul, Formalism.UG.cT, Matrix.det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at h2
    have hg0 := GlobalTheory.UnitaryGlue.gram_det_ne_zero V
    apply mul_right_cancel₀ hg0
    linear_combination h2
  have hnorm : ∀ φ : D.host.E →+* ℂ, ‖φ (δ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).det‖ = 1 := by
    intro φ
    have h2 := congrArg φ hdd
    rw [map_mul, hconj, map_one, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq] at h2
    have h3 : ‖φ (δ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).det‖ ^ 2 = 1 := by exact_mod_cast h2
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h3
  obtain ⟨n, hn, hpow⟩ := NumberField.Embeddings.pow_eq_one_of_norm_eq_one D.host.E ℂ hint hnorm
  have hpm := UpperTheory.Ram.Sector.pow_torsionOrder ⟨n, hn, hpow⟩
  have hdetρ : ∀ ρ, (UpqT.mat (rp g ρ)).det = tauE D ρ (δ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).det := by
    intro ρ
    rw [RingHom.map_det, RingHom.mapMatrix_apply]
    refine det_eq_of_intertwine (e ρ) _ (A ρ) (mat x₀ (σ ρ) * (permM (e ρ))ᵀ) _ ?_ ?_
    · rw [← Matrix.mul_assoc, (hid ρ).2, permM_mul_transpose]
    · rw [hrp g ρ, hinf ρ]
  have hmul : (UpqT.mat (rp (g * y) ρ₀)).det = tauE D ρ₀ (δ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).det * (UpqT.mat (rp y ρ₀)).det := by
    rw [← hdetρ ρ₀, ← Matrix.det_mul, map_mul]
    rfl
  have hd1 : (δ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).det = 1 := by
    have h4 := hgy.2.2
    rw [hmul] at h4 hsec
    have h5 := UpperTheory.Ram.Sector.eq_one_of_sec_eq (NumberField.Units.torsionOrder_pos D.host.E)
      (by rw [← map_pow, hpm, map_one]) hy.2.2 h4 hsec
    exact (tauE D ρ₀).injective (by rw [h5, map_one])
  have hjj := hdj hd1
  subst hjj
  have hstab := hlink2 j g δ hg hmat hd1 hK
  have hmemSU : embGL Ψ V.rank δ ∈ realSU Ψ Gm := by
    refine embGL_mem_realSU Ψ Gm δ hd1 fun x y' => ?_
    rw [hGm, herm_neg, herm_neg, hstab.2.1]
  have hin : (⟨embGL Ψ V.rank δ, hmemSU⟩ : realSU Ψ Gm) ∈ inReal Ψ Gm (ratStab (V.gram)ᵀ (Λ : Set (Fin V.rank → D.host.E)) (s j)) :=
    Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨δ, hstab, rfl⟩)
  have heqv := heq ⟨embGL Ψ V.rank δ, hmemSU⟩ (rp g) (fun ρ => by
    rw [hrp g ρ, hinf ρ]
    show _ = A ρ * (δ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (σ ρ).1
    rw [hσ ρ]) (rp y)
  have hs1 := hF j _ hin (π (rp y)) hy.2.1 (by rw [← heqv, ← map_mul]; exact hgy.2.1)
  have hδ1 : δ = 1 := by
    have h5 := congrArg (fun s : realSU Ψ Gm => ((s.1 (σ ρ₀) : GL (Fin V.rank) ℂ) : Matrix (Fin V.rank) (Fin V.rank) ℂ)) hs1
    have h6 : (δ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (σ ρ₀).1 = (1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (σ ρ₀).1 := by
      rw [Matrix.map_one _ (map_zero _) (map_one _)]
      exact h5
    exact Units.ext (Matrix.map_injective (σ ρ₀).1.injective h6)
  refine ⟨Subtype.ext ?_, rfl⟩
  rw [hδ1, map_one] at hmat
  exact hmat

end GlobalTheory.TubePack
