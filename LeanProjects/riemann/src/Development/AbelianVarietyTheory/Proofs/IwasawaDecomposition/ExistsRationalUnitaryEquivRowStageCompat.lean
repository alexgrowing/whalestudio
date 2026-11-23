import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BrgStdR
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsDeco
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryFiniteAdelicPointAsMatrixMemFlagIwahori
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryGroupsEquivUnitFormGramOne
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section

namespace GlobalTheory.Mem.R3.RowStdRat

open GlobalTheory.Mem.R3.RowAd GlobalTheory.Mem.R3.LiftBrg.StdGroups

theorem ptE_eq (X : Stages) (h : Bridge.Gf X.toD7.sp.X') :
    ptE X h = LiftBrg.castGL (rank_X' X) (Formalism.UG.bc (swapAE X.toD7) h.1) := rfl

def psiX (X : Stages) (hg : X.toD7.sp.X'.gram = 1) :
    Formalism.L2.Col.URat X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) →* GQ X.toD7.sp.X' where
  toFun γ :=
    have hm : LiftBrg.castGL (rank_X' X).symm (γ : GL (Fin (X.B.R.N X.B.R.m - 1)) X.toD7.host.E) ∈
        Formalism.UG.UJ (X.toD7.sp.cm.sig : X.toD7.host.E →+* X.toD7.host.E) X.toD7.sp.X'.gram := by
      rw [hg]
      exact castGL_mem_UJ_one _ _ _ γ.2
    ⟨(show GA X.toD7 X.toD7.sp.X' from
        (⟨Formalism.UG.bc (inclR (F := X.toD7.host.F) (AF X.toD7.host.F))
            (LiftBrg.castGL (rank_X' X).symm (γ : GL (Fin (X.B.R.N X.B.R.m - 1)) X.toD7.host.E)),
          bc_inclR_mem_HR _ _ _ _ hm⟩ : HR (AF X.toD7.host.F) X.toD7.sp.cm.sig X.toD7.sp.X'.gram)),
      Subgroup.mem_subgroupOf.2 ⟨_, hm, rfl⟩⟩
  map_one' := Subtype.ext (Subtype.ext (by first | rfl | (simp only [map_one]; rfl) | (simp <;> rfl)))
  map_mul' a b := Subtype.ext (Subtype.ext (by first | rfl | (simp only [map_mul]; rfl) | (simp <;> rfl)))

theorem psiX_mat (X : Stages) (hg : X.toD7.sp.X'.gram = 1) (γ : Formalism.L2.Col.URat X.toD7.sp.cm (X.B.R.N X.B.R.m - 1)) :
    matHom X.toD7.sp.X' (psiX X hg γ : GA X.toD7 X.toD7.sp.X') =
      Formalism.UG.bc (incA X.toD7) (LiftBrg.castGL (rank_X' X).symm (γ : GL (Fin (X.B.R.N X.B.R.m - 1)) X.toD7.host.E)) := rfl

theorem ptE_ratF_psiX (X : Stages) (hg : X.toD7.sp.X'.gram = 1) (γ : Formalism.L2.Col.URat X.toD7.sp.cm (X.B.R.N X.B.R.m - 1)) :
    ptE X (Bridge.ratF X.toD7.sp.X' (psiX X hg γ)) = (Formalism.L2.Col.ratIn X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) γ).1 := by
  rw [ptE_eq, Formalism.L2.Col.ratIn_val]
  have e1 : ((Bridge.ratF X.toD7.sp.X' (psiX X hg γ)) : GL (Fin X.toD7.sp.X'.rank) _) =
      Formalism.UG.bc (inclR (F := X.toD7.host.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af X.toD7.host.F))
        (LiftBrg.castGL (rank_X' X).symm (γ : GL (Fin (X.B.R.N X.B.R.m - 1)) X.toD7.host.E)) := by
    change finHom X.toD7.sp.X' _ = _
    rw [finHom, MonoidHom.comp_apply, Subgroup.coe_subtype, psiX_mat]
    exact GlobalTheory.HLatMove.bc_map_bc_inclR _ _
  rw [e1]
  have e2 : Formalism.UG.bc (swapAE X.toD7) (Formalism.UG.bc (inclR (F := X.toD7.host.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af X.toD7.host.F))
      (LiftBrg.castGL (rank_X' X).symm (γ : GL (Fin (X.B.R.N X.B.R.m - 1)) X.toD7.host.E))) =
      Formalism.UG.bc (Formalism.L2.Col.iA X.toD7.host.F X.toD7.host.E)
        (LiftBrg.castGL (rank_X' X).symm (γ : GL (Fin (X.B.R.N X.B.R.m - 1)) X.toD7.host.E)) := by
    ext a b
    simp [Formalism.UG.bc, swapAE, inclR, Formalism.UG.inclE]
  rw [e2, ← castGL_bc, castGL_symm_castGL']

end GlobalTheory.Mem.R3.RowStdRat

namespace GlobalTheory.Mem.R3.RowStdRat

open GlobalTheory.Mem.R3.RowAd GlobalTheory.Mem.R3.LiftBrg.StdGroups

theorem psiX_injective (X : Stages) (hg : X.toD7.sp.X'.gram = 1) : Function.Injective (psiX X hg) := by
  intro a b hab
  have h2 : (Formalism.L2.Col.ratIn X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) a).1 = (Formalism.L2.Col.ratIn X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) b).1 := by
    rw [← ptE_ratF_psiX X hg a, ← ptE_ratF_psiX X hg b, hab]
  simp only [Formalism.L2.Col.ratIn_val] at h2
  exact Subtype.ext (Formalism.L2.DIV.incl_inj _ _ _ h2)

theorem psiX_surjective (X : Stages) (hg : X.toD7.sp.X'.gram = 1) : Function.Surjective (psiX X hg) := by
  intro δ
  obtain ⟨γE, hγE, e⟩ := Subgroup.mem_subgroupOf.1 δ.2
  have hγ : LiftBrg.castGL (rank_X' X) γE ∈ Formalism.L2.Col.URat X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) := by
    rw [hg] at hγE
    exact castGL_mem_UJ_one _ _ _ hγE
  refine ⟨⟨_, hγ⟩, Subtype.ext (Subtype.ext ?_)⟩
  change Formalism.UG.bc (inclR (F := X.toD7.host.F) (AF X.toD7.host.F))
    (LiftBrg.castGL (rank_X' X).symm (LiftBrg.castGL (rank_X' X) γE)) = _
  rw [castGL_symm_castGL' (rank_X' X) γE]
  exact e

theorem matEq_castGL {A : Type} [CommRing A] {m n : ℕ} (h : m = n) (x : GL (Fin m) A) : MatEq (LiftBrg.castGL h x) x := by
  subst h
  refine ⟨rfl, fun i j i' j' hi hj => ?_⟩
  have hi' : i = i' := Fin.ext hi
  have hj' : j = j' := Fin.ext hj
  subst hi' hj'
  simp [LiftBrg.castGL, Matrix.reindexAlgEquiv_apply]

theorem stdRat_equiv : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px), I.Ok →
    ∀ (e : Formalism.L2.Col.UAd X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ≃* Bridge.Gf X.toD7.sp.X'),
    (∀ x, RowAd.ptE X (e x) = x.1) →
    ∃ eΓ : Formalism.L2.Col.URat X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ≃* GQ X.toD7.sp.X',
      (∀ γ, Bridge.ratF X.toD7.sp.X' (eΓ γ) = e (Formalism.L2.Col.ratIn X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) γ)) ∧
      ∀ γ, ∃ γE : GL (Fin X.toD7.sp.X'.rank) X.toD7.host.E, Bridge.IsRatMat X.toD7.sp.X' (eΓ γ) γE ∧
        MatEq γE γ.1 := by
  intro X px I hI e he
  have hg := RowDeco.gram_X'_eq_one X I hI
  have hinj : Function.Injective (ptE X) := by
    intro h h' hh
    obtain ⟨x, rfl⟩ := e.surjective h
    obtain ⟨x', rfl⟩ := e.surjective h'
    rw [he, he] at hh
    rw [Subtype.ext hh]
  refine ⟨MulEquiv.ofBijective (psiX X hg) ⟨psiX_injective X hg, psiX_surjective X hg⟩, fun γ => ?_, fun γ => ?_⟩
  · apply hinj
    rw [he]
    exact ptE_ratF_psiX X hg γ
  · exact ⟨LiftBrg.castGL (rank_X' X).symm (γ : GL (Fin (X.B.R.N X.B.R.m - 1)) X.toD7.host.E), psiX_mat X hg γ,
      matEq_castGL _ _⟩

end GlobalTheory.Mem.R3.RowStdRat
