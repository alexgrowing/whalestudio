import Formalism.LocalToGlobal.Divisibility.RecBridge

open Module NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.L2.DIV Formalism.L2.Indef Formalism.HermitianLatticesTheory

noncomputable section

namespace Formalism.L2.DIV.Cons

variable {D : D7}

theorem sgRec_eq_sgFl (L : SizeData₂ D) (u : D.what₂.Word) : sgRec L u = Formalism.L2.G.ServJoint.sgFl L u := rfl

def nuOf (L : SizeData₂ D) (u : D.what₂.Word) {d : ℕ} (e : (Fin d → D.what₂.LL) ≃ₗ[D.what₂.LL] (D.div.Nu u).V) :
    Submodule (𝓞 D.what₂.LL) (Fin d → D.what₂.LL) :=
  (L.NuLat u).comap ((e : (Fin d → D.what₂.LL) →ₗ[D.what₂.LL] (D.div.Nu u).V).restrictScalars (𝓞 D.what₂.LL))

theorem map_nuOf (L : SizeData₂ D) (u : D.what₂.Word) {d : ℕ} (e : (Fin d → D.what₂.LL) ≃ₗ[D.what₂.LL] (D.div.Nu u).V) :
    (nuOf L u e).map ((e : (Fin d → D.what₂.LL) →ₗ[D.what₂.LL] (D.div.Nu u).V).restrictScalars (𝓞 D.what₂.LL)) =
      L.NuLat u := by
  unfold nuOf
  exact Submodule.map_comap_eq_of_surjective (fun y => ⟨e.symm y, by simp⟩) _

private theorem sg_eq_zero_of_not_mem_supp (L : SizeData₂ D) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hw : w ∉ L.supp) :
    L.sg u w = 0 := by
  unfold Formalism.BasicNotions.SizeData₂.sg
  refine Finset.sum_eq_zero fun j _ => ?_
  simp [Formalism.BasicNotions.SizeData₂.gainD, L.gain_supp j w hw, L.F_supp j w hw, L.E_supp u j w hw]

private theorem shiftIdeal_shiftZ_sgRec_eq_Iu (L : SizeData₂ D) (u : D.what₂.Word) :
    Formalism.DivisionValues.shiftIdeal (shiftZ (sgRec L u)) = Formalism.BasicNotions.DV.Iu D L u := by
  have hfun : ∀ i, shiftZ (sgRec L u) (D.plEq i) = ⌊Formalism.BasicNotions.DV.ur D i (L.sg u i)⌋ := by
    intro i
    simp [shiftZ, sgRec]
  calc Formalism.DivisionValues.shiftIdeal (shiftZ (sgRec L u))
      = ∏ᶠ i, ((D.plEq i).asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 D.what₂.LL)) D.what₂.LL) ^
          (-(shiftZ (sgRec L u) (D.plEq i))) := by
        rw [Formalism.DivisionValues.shiftIdeal]
        exact (finprod_comp_equiv D.plEq).symm
    _ = ∏ᶠ i, ((D.plEq i).asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 D.what₂.LL)) D.what₂.LL) ^
          (-⌊Formalism.BasicNotions.DV.ur D i (L.sg u i)⌋) := by
        simp only [hfun]
    _ = Formalism.BasicNotions.DV.Iu D L u := by
        unfold Formalism.BasicNotions.DV.Iu
        refine finprod_eq_prod_of_mulSupport_subset _ ?_
        intro i hi
        rw [Function.mem_mulSupport] at hi
        by_contra hs
        have hs' : i ∉ L.supp := fun h => hs (Finset.mem_coe.2 h)
        apply hi
        simp [sg_eq_zero_of_not_mem_supp L u i hs', Formalism.BasicNotions.DV.ur]

theorem shift_nuOf (L : SizeData₂ D) (hN : NprimeDef D L) (u : D.what₂.Word) {d : ℕ}
    (e : (Fin d → D.what₂.LL) ≃ₗ[D.what₂.LL] (D.div.Nu u).V) (NuC : Submodule (𝓞 D.what₂.LL) (Fin d → D.what₂.LL))
    (hlat : (D.div.Nu u).L =
      NuC.map ((e : (Fin d → D.what₂.LL) →ₗ[D.what₂.LL] (D.div.Nu u).V).restrictScalars (𝓞 D.what₂.LL))) :
    NuC = shiftLat (nuOf L u e) (sgRec L u) := by
  have finj : Function.Injective
      ((e : (Fin d → D.what₂.LL) →ₗ[D.what₂.LL] (D.div.Nu u).V).restrictScalars (𝓞 D.what₂.LL)) :=
    fun x y h => e.injective h
  apply Submodule.map_injective_of_injective finj
  rw [← hlat, hN u]
  unfold shiftLat Formalism.HermitianLatticesTheory.idealSmul nuOf
  rw [Submodule.map_span, shiftIdeal_shiftZ_sgRec_eq_Iu]
  congr 1
  ext z
  constructor
  · rintro ⟨a, ha, y, hy, rfl⟩
    refine ⟨a • e.symm y, ⟨a, ?_, e.symm y, ?_, rfl⟩, ?_⟩
    · simpa using ha
    · show e (e.symm y) ∈ L.NuLat u
      simpa using hy
    · show e (a • e.symm y) = a • y
      simp
  · rintro ⟨z', ⟨a, ha, x, hx, rfl⟩, rfl⟩
    refine ⟨a, ?_, e x, hx, ?_⟩
    · simpa using ha
    · show e (a • x) = a • e x
      exact map_smul e a x

theorem shift_of_colTie (L : SizeData₂ D) (hN : NprimeDef D L) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ}
    {A : FamIn D.what₂.LL G Pl0 T m} {Ps : Subgroup G} {ψs : Ps →* D.what₂.LLˣ} {Zs : DefSub A.fam.amb}
    {S1 : IndefData (A.side Ps ψs Zs)} {Dc : DefCols (A.side Ps ψs Zs)} {Sp : SPer Dc} {C : ColData Dc Sp S1}
    {NuC : ∀ w, Submodule (𝓞 D.what₂.LL) (Fin (Dc.a w) → D.what₂.LL)} {wU : D.what₂.Word → Dc.Mem}
    {eNu : ∀ u, (Fin (Dc.a (wU u)) → D.what₂.LL) ≃ₗ[D.what₂.LL] (D.div.Nu u).V}
    {eRR : (Fin S1.D → D.what₂.LL) ≃ₗ[D.what₂.LL] D.div.RR.V} (h : ColTie D A C NuC wU eNu eRR) (u : D.what₂.Word) :
    NuC (wU u) = shiftLat (nuOf L u (eNu u)) (sgRec L u) :=
  shift_nuOf L hN u (eNu u) (NuC (wU u)) (h.Nu u).lat

theorem sgRec_fin (L : SizeData₂ D) (u : D.what₂.Word) : (Function.support (shiftZ (sgRec L u))).Finite := by
  refine (L.supp.finite_toSet.image D.plEq).subset ?_
  intro w hw
  rw [Function.mem_support] at hw
  refine ⟨D.plEq.symm w, ?_, D.plEq.apply_symm_apply w⟩
  by_contra hs
  have hs' : D.plEq.symm w ∉ L.supp := fun h => hs (Finset.mem_coe.2 h)
  apply hw
  simp [shiftZ, sgRec, sg_eq_zero_of_not_mem_supp L u _ hs', Formalism.BasicNotions.DV.ur]

end Formalism.L2.DIV.Cons

end
