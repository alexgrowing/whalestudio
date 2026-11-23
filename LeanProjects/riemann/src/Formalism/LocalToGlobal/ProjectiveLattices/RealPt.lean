import Formalism.LocalToGlobal.ProjectiveLattices.SecPtRed

noncomputable section

namespace Formalism.L2.Pj

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Gaps.EtaleWeightGaps NumberField IsDedekindDomain

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {E : PtExt X} {hM : IntAtExt X E}
  {ka wL wF : WeightFamilies.Wt D j}

def RealPtSt (G : GlobalFamilyData (xplus X E hM) ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO))
    (h : IsUnif (OsK (xplus X E hM) la G.w) (unifO (xplus X E hM) la G.N)) [∀ ζ : PtsG G la, IsDVRAt ζ] : Prop :=
  ∀ ζ : PtsG G la, ∃ (y : E.Pt' la) (T : CDVR) (ι : Loc ζ →+* T.V) (_ : IsLocalHom ι)
    (hunr : ∃ ϖ : Loc ζ, Irreducible ϖ ∧ Irreducible (ι ϖ)) (ev : Rp (xplus X E hM) la G.N →+* T.Fr)
    (hu : IsUnit (ev (sec (xplus X E hM) la G.w 0))),
    (∀ (w : WeightFamilies.Wt D j) (F : B.Cusp j w), E.vAt' la y (X.inc w F) =
      nval T.V (ep (unifO (xplus X E hM) la G.N) ζ) (ev (emb (xplus X E hM) la G.N (X.inc w F)))) ∧
    ∀ x : ↥(Frac0 (xplus X E hM) la G.w),
      IsLocalization.Away.lift (sec (xplus X E hM) la G.w 0) hu (x : Lw (xplus X E hM) la G.w) =
        phiAt ζ T.Fr ι h (addVal_map_of_unr ι hunr) (toOsK (xplus X E hM) la G.w x)

end Formalism.L2.Pj
