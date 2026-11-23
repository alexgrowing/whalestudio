import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldValuesMemFixedField
import Formalism.LocalToGlobal.Columns.RecLevelSym
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.R3.LevelsFace

theorem level_ext'₂ {E : Type} [Field E] [NumberField E] {Pg : Finset (Pl E)} {r : ℕ} {L L' : LevelP Pg r ℂ}
    (h : ∀ g, g ∈ L.H ↔ g ∈ L'.H) (h' : ∀ g hg hg', L.chi ⟨g, hg⟩ = L'.chi ⟨g, hg'⟩) : L = L' := by
  obtain ⟨H, c⟩ := L
  obtain ⟨H', c'⟩ := L'
  obtain rfl : H = H' := Subgroup.ext h
  obtain rfl : c = c' := MonoidHom.ext fun g => h' g.1 g.2 g.2
  rfl

theorem chi_ofLocal_map' {E : Type} [Field E] [NumberField E] {Pg : Finset (Pl E)} {r : ℕ} {K : Type} [Field K] (σ : K →+* ℂ)
    (Hl : ∀ PP : Pg, Subgroup (GL (Fin r) (kP PP.1))) (f : ∀ PP : Pg, Hl PP →* Multiplicative (kP PP.1))
    (ψ : ∀ PP : Pl E, AddChar (kP PP) K) (g g' : G0 Pg r) (e : g = g') (hg : g ∈ Subgroup.pi Set.univ Hl)
    (hg' : g' ∈ Subgroup.pi Set.univ Hl) :
    Units.map σ.toMonoidHom ((LevelP.ofLocal Hl fun PP => addCharHom (ψ PP.1) (f PP)).chi ⟨g, hg⟩) =
      (LevelP.ofLocal Hl fun PP => addCharHom (σ.toMonoidHom.compAddChar (ψ PP.1)) (f PP)).chi ⟨g', hg'⟩ := by
  subst e
  refine ((congrArg (Units.map σ.toMonoidHom) (MonoidHom.finsetProd_apply _ _ _)).trans (map_prod _ _ _)).trans
    (Eq.trans ?_ (MonoidHom.finsetProd_apply _ _ _).symm)
  exact Finset.prod_congr rfl fun PP _ => Units.ext rfl

variable (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px)

theorem levels_of_eq (hI : I.Ok) {Pg : Finset (Pl X.toD7.host.E)} (hPg : Pg = (X.B.primes px).vGs)
    (eG : Gc X.B px ≃* G0 Pg X.toD7.R.r) (hId : IsPlacewiseIdentity X (px := px) eG) :
    ∃ ψ0 : ∀ PP : Pl X.toD7.host.E, AddChar (kP PP) ℂ, IsGenericPsi Pg ψ0 ∧
      levPOf eG X.toD7.what₂.embLL (lev0 I) (chr0 I) = P0 Pg X.toD7.R.r ψ0 ∧
      ∃ π : Equiv.Perm (Fin X.toD7.R.r), IsSymOrd X.toD7.R.rS X.toD7.R.k π ∧
        (∀ g, g ∈ (levPOf eG X.toD7.what₂.embLL (lev1 I) (chr1 I)).H ↔
          reord π g ∈ (PsharpSym Pg X.toD7.R.r X.toD7.R.rS X.toD7.R.k ψ0).H) ∧
        ∀ g hg hg', (levPOf eG X.toD7.what₂.embLL (lev1 I) (chr1 I)).chi ⟨g, hg⟩ =
          (PsharpSym Pg X.toD7.R.r X.toD7.R.rS X.toD7.R.k ψ0).chi ⟨reord π g, hg'⟩ := by
  subst hPg
  have hs : ∀ g, eG.symm g = g := fun g =>
    funext fun w => (hId (eG.symm g) w.1 w.2 w.2).symm.trans (congrFun (eG.apply_symm_apply g) w)
  have hle : X.toD7.R.k + X.toD7.R.rS ≤ X.toD7.R.r := by
    have := Formalism.L2.Col.r_eq_sym X.toD7.R
    omega
  refine ⟨fun PP => X.B.embLL.toMonoidHom.compAddChar (psiC I PP), fun PP hP h => ?_, level_ext'₂ (fun g => ?_)
    fun g hg hg' => ?_, (Formalism.L2.Col.symPerm X.toD7.R.r X.toD7.R.k X.toD7.R.rS).symm, fun a => ?_, fun g => ?_, fun g hg hg' => ?_⟩
  · have h1 : psiC I PP = 1 :=
      by
        ext x
        exact X.B.embLL.injective ((DFunLike.congr_fun h x).trans (map_one _).symm)
    rw [psiC_of_mem I hP] at h1
    exact hI.ch_ok.psi_zero_nontrivial_character _ h1
  · show eG.symm g ∈ lev0 I ↔ _
    rw [hs]
    exact Iff.rfl
  · exact chi_ofLocal_map' X.B.embLL _ _ (psiC I) _ _ (hs g) hg hg'
  · rw [Formalism.L2.Col.symPerm_symm_val hle]
    unfold Formalism.L2.Col.symIdxInv
    split_ifs <;> omega
  · show eG.symm g ∈ (Formalism.L2.Col.rPsymF I.Ch).grp ↔ _
    rw [hs]
    show g ∈ Subgroup.pi Set.univ _ ↔ reord _ g ∈ Subgroup.pi Set.univ _
    simp only [Subgroup.mem_pi]
    refine forall_congr' fun w => imp_congr_right fun _ => ?_
    show g w ∈ Formalism.L2.Col.HPsymF _ _ _ _ ↔ _
    rw [Formalism.L2.Col.HPsymF_eq_comap_unipSym, Subgroup.mem_comap]
    exact Iff.rfl
  · apply Units.ext
    have key : ∀ (w : (X.B.primes px).vGs) (M M' : GL (Fin X.toD7.R.r) (kP w.1)) (e : M' = Formalism.L2.Col.toSymOrd (kP w.1) X.toD7.R.r X.toD7.R.k X.toD7.R.rS M)
        (hM : M ∈ Formalism.L2.Col.HPsymF (kP w.1) X.toD7.R.r X.toD7.R.k X.toD7.R.rS)
        (hM' : M' ∈ unipSym (kP w.1) X.toD7.R.r X.toD7.R.rS X.toD7.R.k),
        X.B.embLL ((Formalism.L2.Col.chiSymF (I.Ch.psi0 w) X.toD7.R.r X.toD7.R.k X.toD7.R.rS ⟨M, hM⟩ : X.B.LLˣ) : X.B.LL) =
          X.B.embLL (psiC I w.1 (Multiplicative.toAdd (symHom (kP w.1) X.toD7.R.r X.toD7.R.rS X.toD7.R.k ⟨M', hM'⟩))) := by
      intro w M M' e hM hM'
      subst e
      rw [Formalism.L2.Col.chiSymF_apply, Formalism.L2.Col.chiSym_eq_symHom _ _ _ _ _ hM', psiC_of_mem I w.2]
      rfl
    show X.B.embLL (((Formalism.L2.Col.rPsymF I.Ch).chr ⟨eG.symm g, hg⟩ : X.B.LLˣ) : X.B.LL) = _
    rw [Formalism.L2.Col.LevFam.chr_apply, Units.coe_prod, map_prod]
    erw [MonoidHom.finsetProd_apply, Units.coe_prod]
    refine Finset.prod_congr rfl fun w _ => ?_
    exact key w _ _ (congrArg (fun h : G0 (X.B.primes px).vGs X.toD7.R.r =>
      Formalism.L2.Col.toSymOrd (kP w.1) X.toD7.R.r X.toD7.R.k X.toD7.R.rS (h w)) (hs g)).symm _ _

theorem levelsL_face0 : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → Formalism.IndefR.Seed.LevelsL (famR X I hX U Xg tr) L eG (face0 X I hX U Xg tr).lv2 := by
  intro X px I hX U Xg tr L eG hI hL hId
  exact levels_of_eq X I hI hL.Pg eG hId

end GlobalTheory.Mem.R3.LevelsFace
