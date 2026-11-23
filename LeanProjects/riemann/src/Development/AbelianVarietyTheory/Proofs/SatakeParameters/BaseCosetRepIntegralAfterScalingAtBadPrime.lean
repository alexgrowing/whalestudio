import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemLatBack
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepDatumInvariantCBHomTwistPrimes
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU
open scoped TensorProduct
open Classical

noncomputable section

namespace GlobalTheory.TwU.BaseCosetInt

theorem baseCosetRep_integral_after_scaling_at_bad_prime : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC)
    (ex : Extra D L hT Gi Gl Kc Y cX) (t : Formalism.L2.Ker.KerEntTied ex) (u : D.what₂.Word) (μ : D.what₂.Tup) (St : ChainCharts D u μ) (A : AdData t u μ St)
    (dtU : (letI := D.host.cmStar; Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm) →* D.Dt) (a : 𝓞 D.host.E), AdPins A dtU → AdTie A dtU a → ∀ (β : (St (t.m2 + 1) (cpl_lt t μ).le).Ch) (P : SB t μ) (l : Fin (D.R.N (t.m2 + 1))),
    IntAt P.1 ((qOf P.1 : t.X.E) ^ (if P.1 ∈ t.Pr.vGs then 1 else (t.cst μ).M) * A.y0 β P l) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a _hP hA β P l
  obtain ⟨⟨c, hc⟩, -⟩ := ((St (t.m2 + 1) (cpl_lt t μ).le).K β).y_bij.2 (Quotient.mk'' 1)
  have hY := hA.chain.2.1 c
  have h3 := GlobalTheory.TopInv.repY_mem t.sel (t.tup μ) (t.cst μ) _ _ hY P
  rw [← (frsF t.sel (t.tup μ) (A.pt _ (cpl_lt t μ).le c) P).apply_symm_apply (_ • _)] at h3
  replace h3 := (GlobalTheory.TopStep.frsF_mem _ P _).1 h3
  rw [map_smul] at h3
  have hint := (mem_localization_standardLattice _ _).1 h3 l
  have hmem : repY (A.yb c) ∈ A.yb c := by
    obtain ⟨y, -, hYe⟩ := hY
    exact Classical.epsilon_spec (p := fun z => z ∈ A.yb c) ⟨y, by rw [hYe]; simp⟩
  have hco := hA.coset c _ hmem P l
  rw [hc] at hco
  generalize (frsF t.sel (t.tup μ) (A.pt (t.m2 + 1) (cpl_lt t μ).le c) P).symm (repY (A.yb c)) = v at hint hco
  have hq0 : (qOf P.1 : t.X.E) ≠ 0 := GlobalTheory.TopInv.qOf_ne P.1
  have hqi : ∀ n : ℕ, IntAt P.1 ((qOf P.1 : t.X.E) ^ n) := fun n => by
    simpa using IntAt.coe P.1 ((qOf P.1 : 𝓞 t.X.E) ^ n)
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply] at hint hco
  generalize (if P.1 ∈ t.Pr.vGs then 1 else (t.cst μ).M) = e at hint ⊢
  generalize (if P.1 ∈ t.Pr.vGs then 0 else (t.cst μ).M) = e0 at hco
  have key : (qOf P.1 : t.X.E) ^ e * v l = (qOf P.1 : t.X.E) ^ e * A.y0 β P l +
      (qOf P.1 : t.X.E) ^ (e + e0) * (((qOf P.1 : t.X.E) ^ e0)⁻¹ * (v l - A.y0 β P l)) := by
    rw [pow_add]
    field_simp
    ring
  rw [key] at hint
  exact (GlobalTheory.TopInv.intAt_add_iff ((hqi _).mul hco)).1 hint

end GlobalTheory.TwU.BaseCosetInt
