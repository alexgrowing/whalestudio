import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ArBirational
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StalkStepMono
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchubertCellOpenImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPointInSomeCell
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvMulApplyEqZeroOfMinor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEqFlagPtOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenImmersionCellFlAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagStalkColumnSpan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellFlagStalkSpan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellColumnsFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellFlagPointStalk
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.FlagZ

set_option autoImplicit false

noncomputable section

open GlobalTheory.QCoh (freeModule)
open GlobalTheory.Twist (resM)

namespace GlobalTheory.FlagZ.TautCell

variable {ι : Type} [Fintype ι] {N : ℕ}

theorem isFrame_colU (w : ι → Equiv.Perm (Fin N)) (τ : ι) : VB.IsFrame (colU w τ) :=
  Univ.isFrame_cellCol ι N w τ

theorem stalkStep_eq_span (w : ι → Equiv.Perm (Fin N)) (τ : ι) (l : ℕ) (y : Fl ι N) (hy : y ∈ cellU w) :
    Univ.stalkStep ι N τ l y = Submodule.span _ {v | ∃ j : Fin N, (j : ℕ) < l ∧
      v = (freeModule (Fl ι N) (Fin N)).presheaf.germ (cellU w) y hy (colU w τ j)} :=
  (Univ.stalkStep_eq_colSpan ι N τ l y _ (Univ.flagPt_germ_cellGL_eq_fromSpecStalk ι N w y hy)).trans
    (Univ.colSpan_germ_cellGL ι N w τ l y hy)

theorem colU_mem_sub (w : ι → Equiv.Perm (Fin N)) (τ : ι) (l : ℕ) (j : Fin N) (hj : (j : ℕ) < l) :
    colU w τ j ∈ (Univ.sub ι N τ l).sec (cellU w) := fun y hy => by
  rw [stalkStep_eq_span w τ l y hy]
  exact Submodule.subset_span ⟨j, hj, rfl⟩

end GlobalTheory.FlagZ.TautCell

namespace GlobalTheory.FlagZ.TautCell

variable {ι : Type} [Fintype ι] {N : ℕ}

theorem coord_eq_zero_of_mem (w : ι → Equiv.Perm (Fin N)) (τ : ι) (l : ℕ) {V : (Fl ι N).Opens} (h : V ≤ cellU w)
    (c : Fin N → Γ(Fl ι N, V))
    (hc : Fintype.linearCombination Γ(Fl ι N, V) (fun k => resM _ h (colU w τ k)) c ∈ (Univ.sub ι N τ l).sec V)
    (k : Fin N) (hk : l ≤ (k : ℕ)) : c k = 0 := by
  refine TopCat.Presheaf.section_ext (Fl ι N).sheaf V _ _ fun y hyV => ?_
  have hy : y ∈ cellU w := h hyV
  let B := (isFrame_colU w τ).stalkBasis y hy
  have hmem := hc y hyV
  rw [stalkStep_eq_span w τ l y hy] at hmem
  have hsum : (freeModule (Fl ι N) (Fin N)).presheaf.germ V y hyV
      (Fintype.linearCombination Γ(Fl ι N, V) (fun k => resM _ h (colU w τ k)) c) =
        ∑ i, (Fl ι N).presheaf.germ V y hyV (c i) • B i := by
    simp only [Fintype.linearCombination_apply, map_sum, GlobalTheory.QCoh.germ_smul, GlobalTheory.Twist.germ_resM, B,
      VB.IsFrame.stalkBasis_apply]
  rw [hsum] at hmem
  have hle : Submodule.span ((Fl ι N).presheaf.stalk y) {v | ∃ j : Fin N, (j : ℕ) < l ∧
      v = (freeModule (Fl ι N) (Fin N)).presheaf.germ (cellU w) y hy (colU w τ j)} ≤
        LinearMap.ker (B.coord k) := by
    refine Submodule.span_le.2 ?_
    rintro v ⟨j, hj, rfl⟩
    have hjk : j ≠ k := fun e => by subst e; omega
    change B.coord k _ = 0
    have hB : B j = (freeModule (Fl ι N) (Fin N)).presheaf.germ (cellU w) y hy (colU w τ j) :=
      VB.IsFrame.stalkBasis_apply _ _ _ _
    rw [← hB, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply, if_neg hjk]
  have h0 := hle hmem
  rw [LinearMap.mem_ker, ← Module.Basis.equivFun_symm_apply, Module.Basis.coord_apply,
    ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply] at h0
  change (Fl ι N).presheaf.germ V y hyV (c k) = (Fl ι N).presheaf.germ V y hyV 0
  rw [h0, map_zero]

end GlobalTheory.FlagZ.TautCell

namespace GlobalTheory.FlagZ.TautCell

variable {ι : Type} [Fintype ι] {N : ℕ}

theorem exists_frame_cell (w : ι → Equiv.Perm (Fin N)) (τ : ι) (l : Fin (N + 1)) :
    ∃ e : Fin l → Γ(Univ.F ι N τ l, cellU w), VB.IsFrame e ∧
      ∀ j, (Univ.sub ι N τ l).incl.app (cellU w) (e j) = colU w τ (Fin.castLE l.is_le j) := by
  classical
  let e : Fin l → Γ(Univ.F ι N τ l, cellU w) := fun j =>
    (Univ.sub ι N τ l).mkSec (colU w τ (Fin.castLE l.is_le j)) (colU_mem_sub w τ l _ j.2)
  refine ⟨e, fun V h => ?_, fun j => rfl⟩
  let ext : (Fin l → Γ(Fl ι N, V)) → Fin N → Γ(Fl ι N, V) := fun a => Function.extend (Fin.castLE l.is_le) a 0
  have hinj : Function.Injective (Fin.castLE l.is_le) := Fin.castLE_injective _
  have hcomb (a : Fin l → Γ(Fl ι N, V)) :
      (Univ.sub ι N τ l).incl.app V (Fintype.linearCombination Γ(Fl ι N, V) (fun j => resM (Univ.sub ι N τ l).toMod h (e j)) a) =
        Fintype.linearCombination Γ(Fl ι N, V) (fun k => resM _ h (colU w τ k)) (ext a) := by
    rw [Fintype.linearCombination_apply, Fintype.linearCombination_apply, map_sum]
    refine Fintype.sum_of_injective _ hinj _ _ (fun k hk => ?_) fun j => ?_
    · rw [show ext a k = 0 from Function.extend_apply' _ _ _ (fun ⟨j, hj⟩ => hk ⟨j, hj⟩), zero_smul]
    · rw [Scheme.Modules.Hom.app_smul, show ext a (Fin.castLE l.is_le j) = a j from hinj.extend_apply _ _ _]
      rfl
  have hF := isFrame_colU w τ V h
  refine ⟨fun a b hab => ?_, fun s => ?_⟩
  · have hab' := hF.1 ((hcomb a).symm.trans ((congrArg _ hab).trans (hcomb b)))
    funext j
    have := congrFun hab' (Fin.castLE l.is_le j)
    simpa only [ext, hinj.extend_apply] using this
  · obtain ⟨c, hc⟩ := hF.2 ((Univ.sub ι N τ l).incl.app V s)
    have hz := coord_eq_zero_of_mem w τ l h c (hc ▸ (Univ.sub ι N τ l).incl_app_mem s)
    refine ⟨fun j => c (Fin.castLE l.is_le j), (Univ.sub ι N τ l).incl_app_injective V ?_⟩
    refine Eq.trans (hcomb (fun j => c (Fin.castLE l.is_le j))) ?_
    rw [← hc]
    congr 1
    funext k
    by_cases hk : ∃ j, Fin.castLE l.is_le j = k
    · obtain ⟨j, rfl⟩ := hk
      exact hinj.extend_apply _ _ _
    · change Function.extend (Fin.castLE l.is_le) (fun j => c (Fin.castLE l.is_le j)) 0 k = c k
      rw [Function.extend_apply' _ _ _ hk]
      refine (hz k ?_).symm
      by_contra hlt
      exact hk ⟨⟨k, by omega⟩, rfl⟩

theorem exists_isFrame_step_cell : ∀ (ι : Type) [Fintype ι] (N : ℕ) (w : ι → Equiv.Perm (Fin N)) (τ : ι)
    (l : Fin (N + 1)), ∃ e : Fin l → Γ(GlobalTheory.FlagZ.Univ.F ι N τ l, GlobalTheory.FlagZ.TautCell.cellU w), GlobalTheory.VB.IsFrame e ∧
      ∀ j, (GlobalTheory.FlagZ.Univ.sub ι N τ l).incl.app (GlobalTheory.FlagZ.TautCell.cellU w) (e j) =
        GlobalTheory.FlagZ.TautCell.colU w τ (Fin.castLE l.is_le j) :=
  fun _ _ _ w τ l => exists_frame_cell w τ l

end GlobalTheory.FlagZ.TautCell
