import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ArBirational
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColSecOn

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.VB GlobalTheory.FlagZ GlobalTheory
open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM)

namespace GlobalTheory.FlagZ.Loc

variable {N : ℕ} {T : Scheme.{0}}

theorem isQuasicoherent_stdE_ovl : (Taut.stdE N).IsQuasicoherent :=
  (isVB_freeModule_fin (Sp ℤ) N).isQuasicoherent

theorem isFrame_stdSec_ovl (g : T ⟶ Sp ℤ) (U : T.Opens) (hU : U ≤ g ⁻¹ᵁ ⊤) :
    IsFrame fun i : Fin N =>
      GlobalTheory.QCoh.pullbackSections g (Taut.stdE N) hU (freeFrame (Sp ℤ) (Fin N) i) := by
  haveI := isQuasicoherent_stdE_ovl (N := N)
  have h := ((isFrame_freeFrame (Sp ℤ) (Fin N)).pullback g).res hU
  have e : (fun i : Fin N =>
      GlobalTheory.QCoh.pullbackSections g (Taut.stdE N) hU (freeFrame (Sp ℤ) (Fin N) i)) = fun i =>
      resM _ hU (GlobalTheory.QCoh.pullbackSections g (Taut.stdE N) (le_refl (g ⁻¹ᵁ ⊤)) (freeFrame (Sp ℤ) (Fin N) i)) :=
    funext fun i => (QCoh.res_pullbackSections g _ _ _ _).symm
  rw [e]
  exact h

theorem resM_colSecOn_ovl (g : T ⟶ Sp ℤ) {U V : T.Opens} (h : U ≤ V) (M : Matrix (Fin N) (Fin N) Γ(T, V))
    (j : Fin N) :
    resM _ h (colSecOn g V M j) = colSecOn g U (M.map (resG T h)) j := by
  simp only [colSecOn, map_sum, resM_smul, Matrix.map_apply]
  refine Finset.sum_congr rfl fun i _ => congrArg _ ?_
  exact QCoh.res_pullbackSections g _ _ _ _

theorem Adapted.restr {ι : Type} {g : T ⟶ Sp ℤ}
    {fl' : ∀ _ : ι, Vert.Flag ((Scheme.Modules.pullback g).obj (Taut.stdE N)) N} {U V : T.Opens}
    {G : ι → GL (Fin N) Γ(T, V)} (hG : Adapted g fl' V G) (h : U ≤ V) :
    Adapted g fl' U fun a => Matrix.GeneralLinearGroup.map (resG T h) (G a) := by
  intro a l
  obtain ⟨s, hs, hsι⟩ := hG a l
  refine ⟨fun j => resM _ h (s j), hs.res h, fun j => ?_⟩
  rw [app_resM, hsι j, resM_colSecOn_ovl]
  rfl

theorem exists_col_comb_ovl {ι : Type} {g : T ⟶ Sp ℤ}
    {fl' : ∀ _ : ι, Vert.Flag ((Scheme.Modules.pullback g).obj (Taut.stdE N)) N} {U : T.Opens}
    {G H : ι → GL (Fin N) Γ(T, U)} (hG : Adapted g fl' U G) (hH : Adapted g fl' U H) (a : ι) (j : Fin N) :
    ∃ c : Fin (j.succ : ℕ) → Γ(T, U),
      ∀ i, (H a).1 i j = ∑ k, (G a).1 i (Fin.castLE j.succ.is_le k) * c k := by
  obtain ⟨s, hs, hsι⟩ := hG a j.succ
  obtain ⟨t, -, htι⟩ := hH a j.succ
  obtain ⟨c, hc⟩ := (hs U le_rfl).2 (t (Fin.last j))
  simp only [resM_self, Fintype.linearCombination_apply] at hc
  have e1 := congrArg (((fl' a).ι j.succ).app U) hc
  simp only [map_sum, Scheme.Modules.Hom.app_smul, hsι, htι] at e1
  have hj : Fin.castLE j.succ.is_le (Fin.last j) = j := Fin.ext rfl
  rw [hj] at e1
  simp only [colSecOn, Finset.smul_sum, smul_smul] at e1
  rw [Finset.sum_comm] at e1
  simp only [← Finset.sum_smul] at e1
  have hE := (isFrame_stdSec_ovl (N := N) g U (fun _ _ => trivial) U le_rfl).1
  simp only [resM_self] at hE
  refine ⟨c, fun i => ?_⟩
  have := congrFun (hE (a₁ := fun i => (∑ k, c k * (G a).1 i (Fin.castLE j.succ.is_le k)))
    (a₂ := fun i => (H a).1 i j) (by simp only [Fintype.linearCombination_apply]; exact e1)) i
  rw [← this]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

theorem blockTriangular_inv_mul_ovl {ι : Type} {g : T ⟶ Sp ℤ}
    {fl' : ∀ _ : ι, Vert.Flag ((Scheme.Modules.pullback g).obj (Taut.stdE N)) N} {U : T.Opens}
    {G H : ι → GL (Fin N) Γ(T, U)} (hG : Adapted g fl' U G) (hH : Adapted g fl' U H) (a : ι) :
    ((G a)⁻¹ * H a).1.BlockTriangular id := by
  intro k j hjk
  obtain ⟨c, hc⟩ := exists_col_comb_ovl hG hH a j
  rw [Units.val_mul, Matrix.mul_apply]
  simp only [hc, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun m _ => ?_
  simp only [← mul_assoc, ← Finset.sum_mul]
  rw [← Matrix.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_apply_ne, zero_mul]
  intro h
  have h1 := congrArg Fin.val h
  have h2 := m.isLt
  simp only [Fin.coe_castLE, Fin.val_succ] at h1 h2
  have h3 : (j : ℕ) < k := hjk
  omega

theorem flagPt_eq_of_adapted_ovl {ι : Type} [Fintype ι] {g : T ⟶ Sp ℤ}
    {fl' : ∀ _ : ι, Vert.Flag ((Scheme.Modules.pullback g).obj (Taut.stdE N)) N} {U : T.Opens}
    {G H : ι → GL (Fin N) Γ(T, U)} (hG : Adapted g fl' U G) (hH : Adapted g fl' U H) :
    flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd G = flagPt Prod.fst Prod.snd H :=
  (flagPt_mul_upper G (G⁻¹ * H) fun a => blockTriangular_inv_mul_ovl hG hH a).symm.trans
    (congrArg _ (mul_inv_cancel_left G H))

theorem flagPt_inf_eq : ∀ {ι : Type} [Fintype ι] {N : ℕ} {T : Scheme.{0}} (g : T ⟶ Sp ℤ)
    (fl' : ∀ _ : ι, Vert.Flag ((Scheme.Modules.pullback g).obj (Taut.stdE N)) N) (V W : T.Opens)
    (hV : IsAffineOpen V) (hW : IsAffineOpen W) (G : ι → GL (Fin N) Γ(T, V)) (H : ι → GL (Fin N) Γ(T, W)),
    Loc.Adapted g fl' V G → Loc.Adapted g fl' W H →
    T.homOfLE (inf_le_left : V ⊓ W ≤ V) ≫ hV.isoSpec.hom ≫ flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd G =
      T.homOfLE (inf_le_right : V ⊓ W ≤ W) ≫ hW.isoSpec.hom ≫ flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd H := by
  intro ι _ N T g fl' V W hV hW G H hG hH
  rw [hV.isoSpec_hom, hW.isoSpec_hom, ← Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_assoc,
    ← Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_assoc]
  refine congrArg ((V ⊓ W).toSpecΓ ≫ ·) ?_
  change spMap (resG T _) ≫ _ = spMap (resG T _) ≫ _
  rw [spMap_flagPt, spMap_flagPt]
  exact flagPt_eq_of_adapted_ovl (hG.restr inf_le_left) (hH.restr inf_le_right)

end GlobalTheory.FlagZ.Loc
