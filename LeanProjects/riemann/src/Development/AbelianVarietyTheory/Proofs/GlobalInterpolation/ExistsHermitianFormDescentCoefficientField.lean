import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
import Formalism.LocalToGlobal.Columns.TiedValLatG
import Formalism.LocalToGlobal.Columns.CoefModB
import Formalism.LocalToGlobal.KernelLattices.InterlaceAll
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.InvTrKEmbGLApply

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2 Matrix

noncomputable section

namespace GlobalTheory.Glob.FormDescent

theorem desc : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] (emb : ι → E →+* K) (σ : K →+* ℂ) {n : ℕ} (S : GStep E K n) (lam : ι → DomWeight n) (h : (S.fam emb lam).Ok) (z : S.Cl → GlobalTheory.Mem.Col2.Fr emb σ n → ℂ), z ∈ S.Fi emb σ lam → ∀ v : S.Cl → Formalism.L2.DIV.VV K lam, (∀ c, z c = evV emb (1 : Matrix (Fin n) (Fin n) E) lam σ (v c)) → ∃ y : S.FormsK emb lam h, (∀ c, y.1 c = v c) ∧ S.embF emb σ lam h y = z := by
  intro E K ι _ _ _ _ _ _ _ emb σ n S lam h z hz v hv
  have hinj : Function.Injective (evV emb (1 : Matrix (Fin n) (Fin n) E) lam σ) := by
    intro a b hab
    have h1 := congrArg (polOf (Gr emb σ n) (shiftOf lam) (fr0 emb σ n)) hab
    rw [GlobalTheory.LvT.BuiltChain.polOf_evV, GlobalTheory.LvT.BuiltChain.polOf_evV] at h1
    exact Subtype.ext (MvPolynomial.map_injective σ σ.injective h1)
  refine ⟨⟨v, fun c g => ?_⟩, fun c => rfl, ?_⟩
  · apply hinj
    show evV emb (1 : Matrix (Fin n) (Fin n) E) lam σ (S.rho emb lam c.1 g.1 (v c)) = _
    rw [GlobalTheory.LvT.BuiltChain.evV_rho, ← hv c]
    exact (hz c).2 ⟨g.1, g.2⟩
  · funext c
    exact (hv c).symm

end GlobalTheory.Glob.FormDescent
