import Mathlib
import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PeriodLatticeFinitelyGenerated
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralAwayFromMovedLocalDatumStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.DIV Classical

namespace GlobalTheory

theorem intOff_finset_prod {S : Finset ℕ} {κ : Type} (s : Finset κ) (f : κ → ℂ) (h : ∀ k ∈ s, IntOff S (f k)) :
    IntOff S (∏ k ∈ s, f k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (IntOff.one : IntOff S 1)
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).mul (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

theorem xiCpl1_intOff : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), (∀ j, ∃ e, Formalism.L2.Col.IsMu0 t.Ch t.seam.σ₀ e j (t.glob.mu0 j)) → (∀ (j : Fin D.R.m) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 t.X.E)), (∀ i, ((t.Pr.g i : ℕ) : 𝓞 t.X.E) ∉ v.asIdeal) → t.seam.σ₀ (t.Ch.muVal j v : t.X.K) = (((t.glob.mu0 j).val v : ℂˣ) : ℂ)) → ∀ u μ, (∀ k, D.host.g k ∉ Y.Qp μ) → ∀ al p₀ p Yb x, IntOff (t.O u μ).S (t.seam.σ₀ (XiCpl1 (u := t.word u) t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) t.m2 al p₀ p Yb x)) := by
  intro D L hT Gi Gl K Y cX ex t h1 h2 u μ hQ al p₀ p Yb x
  have hm : t.m2 < D.R.m := by have := (t.idx_ok μ).hm; omega
  unfold XiCpl1
  rw [map_mul, map_prod]
  refine IntOff.mul ?_ (intOff_finset_prod _ _ fun P _ => ?_)
  · unfold phiT
    split_ifs
    · rw [map_one]; exact IntOff.one
    · rw [map_zero]; exact IntOff.zero
  · unfold PsiAt
    first
    | exact GlobalTheory.T.integralAwayFrom_moved_localDatum D L hT Gi Gl K Y cX ex t h1 h2 u μ hQ t.m2 hm P _ 1
        (fun hP => ⟨(t.idx_ok μ).stabG t.m2 al P hP, one_mem _⟩) _
    | exact GlobalTheory.T.integralAwayFrom_moved_localDatum D L hT Gi Gl K Y cX ex t h1 h2 u μ t.m2 hm P _ 1
        (fun hP => ⟨(t.idx_ok μ).stabG t.m2 al P hP, one_mem _⟩) _

end GlobalTheory
