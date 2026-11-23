import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar

noncomputable section

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

namespace GlobalTheory.PlaceValues

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)
  {K' : Type} [Field K'] (jL : D.what₂.LL →+* K') (σ' : K' →+* ℂ)

theorem exists_ratMat (V : HSp D) (γ : GQ V) : ∃ γE, Bridge.IsRatMat V γ γE := by
  obtain ⟨γE, -, hE⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 γ.2)
  exact ⟨γE, hE.symm⟩

set_option maxHeartbeats 2000000 in
theorem ext_val (V : HSp D) (C : Bridge.CoefDat D V) {S : CSD D.what₂.LL} {J : Subgroup (Bridge.Gf V)} {χ : J →* ℂˣ}
    (P : Bridge.ClassPres (Bridge.ratF V) S D.what₂.embLL C.ρ J χ) {lam : D.what₂.Tau → DomWeight V.rank}
    {c0 : VV D.what₂.LL lam →ₛₗ[D.what₂.embLL] C.W} {rho : GL (Fin V.rank) D.host.E →* Module.End D.what₂.LL (VV D.what₂.LL lam)}
    (hm : Bridge.CoefMapTie V C c0 rho) {pair nab del} (hc : Bridge.CoefTie V C P lam c0 pair nab del)
    (f : S.Cl → S.V) (g : Bridge.Gf V) : ∃ k v, P.ext f g = ((χ k : ℂˣ) : ℂ) • c0 v := by
  obtain ⟨e, -, hcoef, -⟩ := hc
  obtain ⟨γE, hγE⟩ := exists_ratMat V (P.decG g)
  refine ⟨P.decK g, rho γE (e (f (P.decC g))), ?_⟩
  rw [hm.1 _ _ hγE, ← hcoef]
  rfl

end GlobalTheory.PlaceValues
