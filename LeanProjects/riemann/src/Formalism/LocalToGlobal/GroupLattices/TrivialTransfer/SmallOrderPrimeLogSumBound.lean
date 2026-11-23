import Formalism.LocalToGlobal.GroupLattices.TrivialTransfer.GramTotallyDefinite
import Formalism.LocalToGlobal.GroupLattices.TrivialTransfer.ProGTransfer
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
import Formalism.SharpRestriction.GlobalSchurBounds.FlipTwoThree
import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts

noncomputable section

namespace Formalism.L2.G.Triv

open Formalism.BasicNotions Formalism.MainNotions Formalism.UG NumberField IsDedekindDomain Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem inf_eq_bot (D : D7) (Lv : LevelData D) (u : D.what₂.Word) (c : (D.mem u).C.cls 0) :
    ratPts D.sp.cm.sig D.sp.gram0 (FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊓
      (Lv u).U.map (MulAut.conj ((Lv u).y c : GL (Fin D.R.k) _)).toMonoidHom = ⊥ := by
  rw [eq_bot_iff]
  rintro z ⟨⟨γ, hγ, rfl⟩, hz⟩
  have h1 := (Cmp.mem_map_conj (Lv u).U _ _).1 hz
  have h2 : (⟨γ, hγ⟩ : UJ (D.sp.cm.sig : D.host.E →+* D.host.E) D.sp.gram0) = 1 :=
    trivStabU (Lv u) D.host.g_prime D.host.g_ne ((Lv u).y c) ⟨γ, hγ⟩ (Subgroup.mem_subgroupOf.2 h1)
  have h3 : γ = 1 := congrArg Subtype.val h2
  rw [Subgroup.mem_bot, h3, map_one]

theorem adm17 (D : D7) (Lv : LevelData D) : StandardLattice.adm17 D Lv := fun _ u _ c => inf_eq_bot D Lv u c

theorem SmallOrderPrimeLogSumBound (D : D7) (Lv : LevelData D) : StandardLattice.SmallOrderPrimeLogSumBound D Lv := fun _ u => stabZero_rec D Lv u

theorem adm3 (D : D7) (Lv : LevelData D) : flipTwoThree.adm3 D := fun u c => stabZero_rec D Lv u c

theorem admS (D : D7) (Lv : LevelData D) (u : D.what₂.Word) : product_first_zeroth_parts.admS D u := stabZero_rec D Lv u

theorem proper_of_split_completion (h1 : IwProG) (h2 : ProGTransfer) (D : D7) (Lv : LevelData D)
    (halg : ∀ (u : D.what₂.Word) (i : Fin 2) (v : HeightOneSpectrum (𝓞 D.host.F)) (h : (D.host.g i : 𝓞 D.host.F) ∈ v.asIdeal)
      (a : v.adicCompletion D.host.F), (Lv u).splitG i v h ((1 : D.host.E) ⊗ₜ[D.host.F] a) = (a, a)) : StandardLattice.Conclusion4p D Lv :=
  fun u => proG_of h1 h2 (Lv u) D.host.g_prime (isUnit_det_gram0 D.sp) (halg u)

end Formalism.L2.G.Triv

end
