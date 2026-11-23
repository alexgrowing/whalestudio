import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTriSelf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsoOfSubbundleSameRankStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSubbundleCompIsIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppInjectiveOfFrames

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.Vert GlobalTheory.TriFrame GlobalTheory.FlagCell
open GlobalTheory.Twist (resM)
open Formalism.MainNotions.DIV.Cons (intO SCF)

namespace GlobalTheory.FlagPairOfHom

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {B : Vert.Model O}
  {E E' : B.X.Modules} (ψ : E' ⟶ E) [IsIso (B.genRes.map ψ)] {r : ℕ} {fl : Vert.Flag E r}
  {fl' : Vert.Flag E' r} (a : ∀ i, fl'.F i ⟶ fl.F i) (ha : ∀ i, a i ≫ fl.ι i = fl'.ι i ≫ ψ)

include ha in

theorem isIso_genRes_map (i : Fin (r + 1)) : IsIso (B.genRes.map (a i)) := by
  haveI : Nonempty B.gen := ⟨⟨_, B.genericPoint_mem_gen⟩⟩
  haveI : IsIntegral B.gen.toScheme := isIntegral_of_isOpenImmersion B.gen.ι
  refine GlobalTheory.T.iso_of_subbundle_same_rank B.gen.toScheme _ _ _ i (B.genRes.map (fl.ι i)) _
    ((fl.isVB i).pullback _) ((fl'.isVB i).pullback _) inferInstance ?_
  rw [← Functor.map_comp, ha, Functor.map_comp]
  exact GrBundle.isSubbundle_comp_isIso
    (SubPull.isSubbundle_pullback _ _ B.gen.ι _ _ (fl'.ι i) i (fl'.isVB i) (fl'.isSubbundle i)) _

include ha in

theorem step_comm (i : Fin r) : fl'.step i ≫ a i.succ = a i.castSucc ≫ fl.step i := by
  rw [← cancel_mono (fl.ι i.succ), Category.assoc, Category.assoc, Vert.Flag.step_ι, ha, ha,
    Vert.Flag.step_ι_assoc]

def pair : Vert.Model.FlagPair (Vert.Model.GenIso.ofHom ψ) r where
  fl := fl
  fl' := fl'
  gen i :=
    haveI := isIso_genRes_map ψ a ha i
    Vert.Model.GenIso.ofHom (a i)
  gen_ι i := by
    rw [← Iso.eq_inv_comp, ← Category.assoc, ← Iso.comp_inv_eq]
    change B.genRes.map (fl'.ι i) ≫ B.genRes.map ψ = B.genRes.map (a i) ≫ B.genRes.map (fl.ι i)
    rw [← Functor.map_comp, ← Functor.map_comp, ha]

def grMap (i : Fin r) : fl'.gr i ⟶ fl.gr i :=
  cokernel.map (fl'.step i) (fl.step i) (a i.castSucc) (a i.succ) (step_comm ψ a ha i)

theorem π_grMap (i : Fin r) : fl'.π i ≫ grMap ψ a ha i = a i.succ ≫ fl.π i :=
  cokernel.π_desc _ _ _

theorem grIso_inv (i : Fin r) : ((pair ψ a ha).grIso i).inv = B.genRes.map (grMap ψ a ha i) := by
  have h := (pair ψ a ha).π_grIso_hom i
  rw [← Iso.inv_comp_eq, ← Category.assoc, ← Iso.eq_comp_inv] at h
  rw [← cancel_epi (B.genRes.map (fl'.π i)), ← Functor.map_comp, π_grMap, Functor.map_comp]
  exact h.symm

theorem exists_flagPair : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (B : Vert.Model O) (E E' : B.X.Modules) (ψ : E' ⟶ E) [IsIso (B.genRes.map ψ)] (r : ℕ) (fl : Vert.Flag E r) (fl' : Vert.Flag E' r) (a : ∀ i, fl'.F i ⟶ fl.F i), (∀ i, a i ≫ fl.ι i = fl'.ι i ≫ ψ) → ∃ P : Vert.Model.FlagPair (Vert.Model.GenIso.ofHom ψ) r, ∃ (_ : P.fl = fl) (_ : P.fl' = fl'), ∀ i, ∃ (φ : B.GenIso (fl.gr i) (fl'.gr i)) (b : fl'.gr i ⟶ fl.gr i), φ.inv = B.genRes.map b ∧ fl'.π i ≫ b = a i.succ ≫ fl.π i ∧ P.div i = φ.div (fl.isVB_gr i) (fl'.isVB_gr i) :=
  fun _ _ _ _ _ _ _ ψ _ _ _ _ a ha => ⟨pair ψ a ha, rfl, rfl, fun i =>
    ⟨(pair ψ a ha).grIso i, grMap ψ a ha i, grIso_inv ψ a ha i, π_grMap ψ a ha i, rfl⟩⟩

end GlobalTheory.FlagPairOfHom
