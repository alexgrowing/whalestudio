import Formalism.LocalToGlobal.InertKernelTheory.StatementJets
import Formalism.LocalToGlobal.InertKernelTheory.DefsMM
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntTens
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntPull
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntEasy

noncomputable section

namespace Formalism.L2.KerInert.OrthonormalJets

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem smulLat_star {N : ℕ} (γ : Matrix (Fin N) (Fin N) D.host.E) (h : star γ * γ = 1)
    (M : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) :
    SDLat.smulLat (star γ) (SDLat.smulLat γ M) = M := by
  ext x
  rw [PullbackComparison.mem_smulLat]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨z, hz, rfl⟩ := (PullbackComparison.mem_smulLat γ M y).1 hy
    rw [Matrix.mulVec_mulVec, h, Matrix.one_mulVec]
    exact hz
  · intro hx
    refine ⟨γ.mulVec x, (PullbackComparison.mem_smulLat γ M _).2 ⟨x, hx, rfl⟩, ?_⟩
    rw [Matrix.mulVec_mulVec, h, Matrix.one_mulVec]

theorem locBasis_push {N N' r : ℕ} (p : ℕ) (γ : Matrix (Fin N) (Fin N) D.host.E)
    (γ' : Matrix (Fin N') (Fin N') D.host.E) (h1 : γ * star γ = 1) (h2 : star γ * γ = 1)
    (h3 : γ' * star γ' = 1) (h4 : star γ' * γ' = 1) (M : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (M' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E)
    (hb : LocBasis D p (YYl D M M') b) :
    LocBasis D p (YYl D (SDLat.smulLat γ M) (SDLat.smulLat γ' M')) (fun i => γ' * b i * star γ) := by
  have hb' : LocBasis D p (YYl D (SDLat.smulLat (star γ) (SDLat.smulLat γ M))
      (SDLat.smulLat (star γ') (SDLat.smulLat γ' M'))) b := by
    rw [smulLat_star γ h2, smulLat_star γ' h4]
    exact hb
  have := PullbackComparison.locBasis_pull p (star γ) (star γ') (by rw [star_star]; exact h2) (by rw [star_star]; exact h1)
    (by rw [star_star]; exact h4) (by rw [star_star]; exact h3) (SDLat.smulLat γ M) (SDLat.smulLat γ' M') b hb'
  simpa only [star_star] using this

theorem ortho_push {N N' r : ℕ} (γ : Matrix (Fin N) (Fin N) D.host.E)
    (γ' : Matrix (Fin N') (Fin N') D.host.E) (h2 : star γ * γ = 1) (h4 : star γ' * γ' = 1)
    (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (hb : Orthonormal D b) :
    Orthonormal D (fun i => γ' * b i * star γ) := by
  have := PullbackComparison.ortho_pull (star γ) (star γ') (by rw [star_star]; exact h2) (by rw [star_star]; exact h4) b hb
  simpa only [star_star] using this

end Formalism.L2.KerInert.OrthonormalJets

namespace Formalism.L2.KerInert

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker OrthonormalJets

theorem orthBasisExists_of (hG : GlobONB) (hW : WeakApprox) : OrthBasisExists := by
  intro D p _ hp5 hin N N' L L' hA
  obtain ⟨n, rfl⟩ := hA.1
  obtain ⟨n', rfl⟩ := hA.2.1
  have hQ : Algebra.IsAlgebraic ℚ Formalism.MainNotions.TaylorLogMetric.Qbar := algebraicClosure.isAlgebraic ℚ ℂ
  let lam : Formalism.MainNotions.TaylorLogMetric.Qbar →+* ℂ_[p] :=
    (IsAlgClosed.lift (R := ℚ) (S := Formalism.MainNotions.TaylorLogMetric.Qbar) (M := ℂ_[p])).toRingHom
  obtain ⟨r, b, hloc, hon, -⟩ := hG D p hp5 hin lam
  have hlocN := IntTens.locBasis_bB (IntTens.eTwo n') (IntTens.eTwo n) p b hloc
  have honN := IntTens.orth_bB (IntTens.eTwo n') (IntTens.eTwo n) b hon
  obtain ⟨γ, γ', M, M', -, hM, hM', rfl, rfl⟩ := hW D p hp5 hin _ _ L L' hA
  have hlocM := (pairing_fact D ⊥ 0 p _ _ _ M _ M' hM hM').1 _ _ hlocN
  letI := D.host.cmStar
  have h1 : (γ : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E) * star (γ : Matrix _ _ D.host.E) = 1 :=
    Matrix.mem_unitaryGroup_iff.1 γ.2
  have h2 : star (γ : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E) * (γ : Matrix _ _ D.host.E) = 1 :=
    Matrix.mem_unitaryGroup_iff'.1 γ.2
  have h3 : (γ' : Matrix (Fin (n' + n')) (Fin (n' + n')) D.host.E) * star (γ' : Matrix _ _ D.host.E) = 1 :=
    Matrix.mem_unitaryGroup_iff.1 γ'.2
  have h4 : star (γ' : Matrix (Fin (n' + n')) (Fin (n' + n')) D.host.E) * (γ' : Matrix _ _ D.host.E) = 1 :=
    Matrix.mem_unitaryGroup_iff'.1 γ'.2
  exact ⟨_, _, locBasis_push p _ _ h1 h2 h3 h4 M M' _ hlocM, ortho_push _ _ h2 h4 _ honN⟩

end Formalism.L2.KerInert
