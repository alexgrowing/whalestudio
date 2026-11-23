import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsNormalisedPolarisation
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LbIsoCubeLBMulRightOf
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfLocalOnBase

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

noncomputable section

namespace GlobalTheory.LamF

theorem exists_pat_of_polAV : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsNoetherianRing R] (P : Out.PolAV (Sp R)) (act : OAct (𝓞 E) P.A), (∀ a, LamEq P.L (act.act a) (𝟙 P.A) P.L (𝟙 P.A) (act.act (H.bar a))) → ∃ (T : PAT H (Sp R)) (e : T.t.G ≅ P.A), T.g = P.g ∧ Serre.IsLinearHom T.t.act act e.hom ∧ LamEq P.L e.hom e.hom T.t.PP.L (𝟙 T.t.G) (𝟙 T.t.G) := by
  intro laws E _ _ _ H R _ _ P act hadj
  have : IsCommMonObj P.A := P.isAb.comm
  obtain ⟨L', hL', ⟨rig, hrig⟩, hsym, hamp, hk, hlam, prim⟩ :=
    exists_normalised_polarisation laws R P (act.act H.w0) (act.act (H.bar H.w0)) (act.hom _) (act.hom _)
      (by rw [← act.add, GlobalTheory.HostModel.cmHost_bar_halfIntegerGenerator, add_sub_cancel, act.one]) (hadj H.w0)
  let PP : RigLB P.A := ⟨L', rig, hL', hrig⟩
  let P' : Out.PolAV (Sp R) :=
    { A := P.A, isAb := P.isAb, g := P.g, smoothDim := P.smoothDim, L := L', isLB := hL', rigid := ⟨rig, hrig⟩,
      sym := hsym, ample := hamp, ktriv := hk }
  obtain ⟨cub⟩ := (laws.cube _ P' PP rfl).1
  have sym : PP.IsSymmetric :=
    GlobalTheory.PrimNorm.isSymmetric_of_hasGen PP (exists_gen_neg_of_sym laws.globalFns P.isAb hL' hsym)
  have lb : ∀ {T : Over (Sp R)} (x : Fin 2 → (T ⟶ P.A)) {L : LB P.A.left}, L.IsLB → (cubeLB P.A x L).IsLB :=
    fun x L hL => DVR.linComb_isLB _ hL _ _
  have pts := ((GlobalTheory.LamCalc.lamEq_calculus _ P.A P.A P.A P.A P.A L' P.L P.L hL' P.isLB P.isLB
    (𝟙 _) (𝟙 _) (𝟙 _) (𝟙 _) (𝟙 _) (𝟙 _) (𝟙 _) (𝟙 _) (𝟙 _) (𝟙 _)).2.1 hlam).2.2.2.2
  simp only [Category.comp_id] at pts
  have adj : ∀ a, LBIso (cubeLB P.A ![fst P.A P.A ≫ act.act a, snd P.A P.A] L')
      (cubeLB P.A ![fst P.A P.A, snd P.A P.A ≫ act.act (H.bar a)] L') := fun a =>
    LBIso.trans (lb _ hL') (lb _ P.isLB) (lb _ hL') (pts _ _ _)
      (LBIso.trans (lb _ P.isLB) (lb _ P.isLB) (lb _ hL')
        (by simpa only [LamEq, Category.comp_id] using hadj a) (pts _ _ _).symm)
  exact ⟨{ t := { G := P.A, semi := GlobalTheory.isSemiAbelian_of_isAbelianScheme _ P.isAb, act := act, PP := PP, cub := cub,
                  sym := sym, adj := adj, prim := prim },
           ab := P.isAb, g := P.g, dim := P.smoothDim, sym := hsym, ample := hamp, ktriv := hk },
    Iso.refl _, rfl, Serre.IsLinearHom.id act, LBIso.symm hlam⟩

end GlobalTheory.LamF
