import Formalism.LocalToGlobal.Columns.RecChainUnfOne
import Formalism.LocalToGlobal.Columns.DetChrOf

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions

namespace Formalism.L2.Col

namespace DetChrOf

section Pull

variable {F E K : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [Field K]

def chiPull (σ : E →ₐ[F] E) (c : Formalism.L2.DIV.Chr F E K) : Formalism.L2.DIV.Chr F E K := c.comp (Formalism.L2.DIV.h90 σ)

end Pull

section Comparison₂

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs)

theorem chiDetTie_of_pt (σ₀ : X.K →+* ℂ) (Dc : DetChr X R.m) (hc : Formalism.BasicNotions.CMData X.F X.E) (Am : Formalism.L2.Ker.Amb X)
    (u : Pr.Word) (f : ∀ a : ℕ, Submodule (𝓞 X.E) (Sp X.E a) → ℂ)
    (hF : ∀ a b N N', Am.chiF a b N N' = f a N ^ (((b / 2 : ℕ) : ℤ)) * f b N' ^ (-((a / 2 : ℕ) : ℤ)))
    (hpt : ∀ j (cl : StCl W Λ u j), σ₀ ((Formalism.L2.DIV.detTw hc.sig Dc.chi (repPt W Λ hc u j cl) : X.Kˣ) : X.K) =
      f (R.N j) (repN W Λ u j cl)) :
    ChiDetTie W Λ σ₀ Dc hc Am u := by
  intro i _ c c'
  rw [Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, map_zpow₀, hpt, hpt, hF]
  have ha : f (R.N i) (repN W Λ u i c) ≠ 0 := by
    rw [← hpt]; exact (map_ne_zero σ₀).mpr (Units.ne_zero _)
  have hb : f (R.N (i + 1)) (repN W Λ u (i + 1) c') ≠ 0 := by
    rw [← hpt]; exact (map_ne_zero σ₀).mpr (Units.ne_zero _)
  rw [zpow_neg, zpow_neg]
  field_simp

end Comparison₂

section Amb

open Formalism.L2.Ker

variable {D : D7} {X : Fields} (s : Seam D X)

end Amb

end DetChrOf

end Formalism.L2.Col
