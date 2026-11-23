import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HMatMulVecPerCrd
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeVacuaExistUnique
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaKernelOrthonormalFrameInDomainPeriodLinearStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AdelicZakThetaExistsUniqueStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaKernelTestFunctionMapLinearInjectiveEquivarStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsTestFunctionOfFockVacuumThetaFunctionStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.IsLatticeVacuumIffSignedRationalFixedStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Ker

theorem epsW_neg_rows {E : Type} [Field E] [NumberField E] [IsCMField E] {r n : ℕ} (X : Data E r) (w : E)
    (y : Matrix (Fin n) (Fin r) E) : SW.epsW X w (-y) = SW.epsW X w y := by
  have key : ∀ k, EF X ((-y) k) (w • (-y) k) = EF X (y k) (w • y k) := by
    intro k
    change (SW.EFBil X) (-(y k)) (w • -(y k)) = (SW.EFBil X) (y k) (w • y k)
    rw [smul_neg]
    simp only [map_neg, LinearMap.neg_apply, neg_neg]
  unfold SW.epsW
  rw [Finset.sum_congr rfl (fun k _ => key k)]

theorem latVac_th_iff (D : D7) (S T : HSp D) (C : Ctx S T) (w : D.host.E) (hw : IsIntegral ℤ w)
    (h1 : w + cc w = 1) (h2 : IdemTwo w) (M : ℕ) (Λ : Lt D.host.E S.rank) (hΛ : Λ ∈ Vset D.host.E S.rank M)
    (L : Lt D.host.E T.rank) (hL : SelfD C.X L) (x : Frame C.X.Ψ T.rank) (hx : x ∈ C.X.dom)
    (φ : TF S.rank C.g) (hφ : SW.IsSB φ) :
    IsLatVac (heisO C.ψ S T) (hatA S T (tens Λ L)) (C.Th x φ) ↔
      ∀ y ∈ tens Λ L, SW.epsW C.X w y • heisG C.X C.bas y φ = φ := by
  have hth : C.IsTh (C.Th x φ) := (GlobalTheory.T.adelicZakTheta_exists_unique D S T C x hx φ hφ).1.1
  rw [GlobalTheory.T.isLatticeVacuum_iff_signedRational_fixed D S T C w hw h1 h2 M Λ hΛ L hL _ hth]
  have hsb : ∀ y, SW.IsSB (heisG C.X C.bas y φ) := fun y =>
    ((GlobalTheory.SW.heisG_laws D.host.E T.rank C.X C.g C.bas C.idx S.rank C.sympl C.even).2.2.2 y φ hφ).1
  have hrho := (GlobalTheory.T.thetaKernel_testFunction_map_linear_injective_equivariant D S T C x hx φ hφ).2.2.1
  constructor
  · intro h y hy
    have h' := h (-y) (neg_mem hy)
    rw [hrho, neg_neg, epsW_neg_rows] at h'
    have hsb' : SW.IsSB (SW.epsW C.X w y • heisG C.X C.bas y φ) :=
      GlobalTheory.SW.TensVac.rho_sb (idx := C.idx) (hs := C.sympl) (hn := C.even) y hφ
    rw [← (GlobalTheory.T.thetaKernel_testFunction_map_linear_injective_equivariant D S T C x hx _ (hsb y)).2.1] at h'
    exact ((GlobalTheory.T.thetaKernel_testFunction_map_linear_injective_equivariant D S T C x hx _ hsb').1 φ hφ).2 h'
  · intro h y hy
    have h' := h (-y) (neg_mem hy)
    rw [epsW_neg_rows] at h'
    rw [hrho, ← (GlobalTheory.T.thetaKernel_testFunction_map_linear_injective_equivariant D S T C x hx _ (hsb (-y))).2.1, h']

theorem latVac_th_line : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ w : D.host.E, IsIntegral ℤ w → w + cc w = 1 → IdemTwo w → ∀ (M : ℕ), ∀ Λ ∈ Vset D.host.E S.rank M, ∀ L : Lt D.host.E T.rank, SelfD C.X L → (∀ x ∈ C.X.dom, ∀ φ : TF S.rank C.g, SW.IsSB φ → (IsLatVac (heisO C.ψ S T) (hatA S T (tens Λ L)) (C.Th x φ) ↔ ∀ y ∈ tens Λ L, SW.epsW C.X w y • heisG C.X C.bas y φ = φ)) ∧ ∀ B, C.IsB B → ∀ v, IsVac C.X C.bas w (tens Λ L) v → ∀ f, C.IsTh f → C.IsFock B f → IsLatVac (heisO C.ψ S T) (hatA S T (tens Λ L)) f → ∃ t : ℂ, f = t • (C.Th (C.xB B) v) := by
  intro D S T C w hw h1 h2 M Λ hΛ L hL
  refine ⟨fun x hx φ hφ => latVac_th_iff D S T C w hw h1 h2 M Λ hΛ L hL x hx φ hφ, ?_⟩
  intro B hB v hv f hf hF hlat
  obtain ⟨φ, hφ, rfl⟩ := GlobalTheory.T.exists_testFunction_of_fockVacuum_thetaFunction D S T C B hB f hf hF
  have hx : C.xB B ∈ C.X.dom := ((GlobalTheory.T.thetaKernel_orthonormalFrame_inDomain_periodLinear D S T C).2 B hB).2.1
  have hfix := (latVac_th_iff D S T C w hw h1 h2 M Λ hΛ L hL (C.xB B) hx φ hφ).1 hlat
  have hline := (GlobalTheory.SW.TensVac.vacua D.host.E T.rank C.X C.g C.bas C.idx S.rank C.sympl C.even
    w hw h1 L hL M Λ hΛ).2.1 v φ hv hφ hfix
  refine ⟨SW.ip φ v, ?_⟩
  calc C.Th (C.xB B) φ = C.Th (C.xB B) (SW.ip φ v • v) := by rw [← hline]
    _ = SW.ip φ v • C.Th (C.xB B) v := (GlobalTheory.T.thetaKernel_testFunction_map_linear_injective_equivariant D S T C _ hx v hv.1).2.1 _

end GlobalTheory.Ker
