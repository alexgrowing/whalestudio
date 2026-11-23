import Mathlib
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.LeibnizOrd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenFixedOfSubgroup
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirProjEqOneOfMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviIntegralFacts
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib

noncomputable section

namespace GlobalTheory.CompanionTheory.LeibGP

section SlopeTestRemainingChoices

variable (k : Type) [Field k]

theorem blockIndex_false (m j : ℕ) (a : Fin m) :
    eGP m j ⟨false, a⟩ = Fin.castSucc (two (stdSum (rfl : m + j = m + j)) ⟨false, a⟩) := by
  first
    | rfl
    | exact Fin.ext rfl
    | (apply Fin.ext
       simp [GlobalTheory.BZMir.Leib.eGP, GlobalTheory.SmGL.two, GlobalTheory.SmGL.stdSum])

theorem blockIndex_true_castSucc (m j : ℕ) (b : Fin j) :
    eGP m j ⟨true, Fin.castSucc b⟩ = Fin.castSucc (two (stdSum (rfl : m + j = m + j)) ⟨true, b⟩) := by
  first
    | rfl
    | exact Fin.ext rfl
    | (apply Fin.ext
       simp [GlobalTheory.BZMir.Leib.eGP, GlobalTheory.SmGL.two, GlobalTheory.SmGL.stdSum])

theorem glEmbMat_castSucc (n : ℕ) (A : Matrix (Fin n) (Fin n) k) (a b : Fin n) :
    glEmbMat k n A (Fin.castSucc a) (Fin.castSucc b) = A a b := by
  simp [GlobalTheory.BZMir.glEmbMat]

theorem glEmbMat_last_castSucc (n : ℕ) (A : Matrix (Fin n) (Fin n) k) (b : Fin n) :
    glEmbMat k n A (Fin.last n) (Fin.castSucc b) = 0 := by
  simp [GlobalTheory.BZMir.glEmbMat]

theorem glEmbMat_castSucc_last (n : ℕ) (A : Matrix (Fin n) (Fin n) k) (a : Fin n) :
    glEmbMat k n A (Fin.castSucc a) (Fin.last n) = 0 := by
  simp [GlobalTheory.BZMir.glEmbMat]

theorem glEmbMat_last_last (n : ℕ) (A : Matrix (Fin n) (Fin n) k) :
    glEmbMat k n A (Fin.last n) (Fin.last n) = 1 := by
  simp [GlobalTheory.BZMir.glEmbMat]

end SlopeTestRemainingChoices

theorem gpProj_levi : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m j : ℕ) (p : GL (Fin (m + j)) k) (hp : p ∈ parab k (two (stdSum (rfl : m + j = m + j)))) (hp' : levi k (m + j) p ∈ MirabolicParabolic k m j), gpProj k m j ⟨levi k (m + j) p, hp'⟩ = (leviProj k (two (stdSum (rfl : m + j = m + j))) ⟨p, hp⟩ false, levi k j (leviProj k (two (stdSum (rfl : m + j = m + j))) ⟨p, hp⟩ true)) := by
  intro k _ _ _ _ m j p hp hp'
  refine Prod.ext ?_ ?_
  · apply Units.ext
    ext a b
    simp only [GlobalTheory.BZMir.Leib.gpProj, GlobalTheory.BZMir.Leib.hgpIncl, MonoidHom.prod_apply,
      MonoidHom.comp_apply, MonoidHom.codRestrict_apply, Pi.evalMonoidHom_apply, MonoidHom.coe_mk, OneHom.coe_mk]
    (try erw [GlobalTheory.SmGL.leviProj_apply])
    (try erw [GlobalTheory.SmGL.leviProj_apply])
    simp [GlobalTheory.SmGL.leviProj_apply, GlobalTheory.BZMir.levi, GlobalTheory.BZMir.glEmb, GlobalTheory.BZMir.glEmbHom,
        GlobalTheory.CompanionTheory.LeibGP.blockIndex_false, GlobalTheory.CompanionTheory.LeibGP.blockIndex_true_castSucc, GlobalTheory.BZMir.Leib.blockIndex_true_last,
        GlobalTheory.CompanionTheory.LeibGP.glEmbMat_castSucc, GlobalTheory.CompanionTheory.LeibGP.glEmbMat_last_castSucc,
        GlobalTheory.CompanionTheory.LeibGP.glEmbMat_castSucc_last, GlobalTheory.CompanionTheory.LeibGP.glEmbMat_last_last,
        MonoidHom.codRestrict_apply, Units.coe_map, MonoidHom.coe_mk, OneHom.coe_mk]
  · apply Subtype.ext
    apply Units.ext
    ext a b
    simp only [GlobalTheory.BZMir.Leib.gpProj, GlobalTheory.BZMir.Leib.hgpIncl, MonoidHom.prod_apply,
      MonoidHom.comp_apply, MonoidHom.codRestrict_apply, Pi.evalMonoidHom_apply, MonoidHom.coe_mk, OneHom.coe_mk]
    (try erw [GlobalTheory.SmGL.leviProj_apply])
    induction a using Fin.lastCases <;> induction b using Fin.lastCases <;>
      simp [GlobalTheory.SmGL.leviProj_apply, GlobalTheory.BZMir.levi, GlobalTheory.BZMir.glEmb, GlobalTheory.BZMir.glEmbHom,
        GlobalTheory.CompanionTheory.LeibGP.blockIndex_false, GlobalTheory.CompanionTheory.LeibGP.blockIndex_true_castSucc, GlobalTheory.BZMir.Leib.blockIndex_true_last,
        GlobalTheory.CompanionTheory.LeibGP.glEmbMat_castSucc, GlobalTheory.CompanionTheory.LeibGP.glEmbMat_last_castSucc,
        GlobalTheory.CompanionTheory.LeibGP.glEmbMat_castSucc_last, GlobalTheory.CompanionTheory.LeibGP.glEmbMat_last_last,
        MonoidHom.codRestrict_apply, Units.coe_map, MonoidHom.coe_mk, OneHom.coe_mk]

end GlobalTheory.CompanionTheory.LeibGP

end
