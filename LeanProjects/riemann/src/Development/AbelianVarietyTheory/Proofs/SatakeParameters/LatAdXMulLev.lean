import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemLatBack
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemStabGLAdeleIff
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.TwU

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem hatStab_of_lev {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
    (S : StepLevel F E σ J T f bad) (κ : S.U) : HatStab S.Lb κ.1 := by
  have h := (S.U_eq κ.1).1 κ.2
  have hk : κ.1 ∈ levelAfL σ J S.Lb :=
    (GlobalTheory.LatticeStabLocal.mem_levelAfL_iff F E σ n J S.Lb S.Lb_fin κ.1).2 ⟨h.1, fun v => S.Uloc_lev v (h.2 v)⟩
  exact fun z => ((inv_mem hk).2 z).symm

theorem latAdX_mul_lev {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC}
    {ex : Extra D L hT Gi Gl Kc Y cX} {t : Formalism.L2.Ker.KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup} {St : ChainCharts D u μ} (A : AdData t u μ St) (a : 𝓞 D.host.E) (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch)
    (x : GL (Fin (D.R.N i)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (κ : ((St i hi).K β).lev.U) :
    latAdX A a i hi β (x * κ.1) = latAdX A a i hi β x := by
  unfold latAdX latCo
  rw [latAd_stab x κ.1 _ (hatStab_of_lev _ κ)]

end GlobalTheory.TwU
