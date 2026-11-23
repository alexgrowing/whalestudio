import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZeroSectionBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDualOfIsPerfectOfAdditive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianDeRhamPoincareDualityOfCubeDual
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsProdPolAV
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceSpecOfIsLocalRing
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.ZarhinStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Hypotheses₂

namespace Zarhin

variable {S : Scheme.{0}}

def IsPolarisation (A B : Over S) [GrpObj A] [GrpObj B] (P : LB (A ⊗ B).left) (l : A ⟶ B) : Prop :=
  IsMonHom l ∧ ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (s : Sp Ω ⟶ S),
    ∃ L : LB ((Over.pullback s).obj A).left, L.IsLB ∧ Out.RelAmple ((Over.pullback s).obj A) L ∧
      LBIso ((ev P (fst A A) (snd A A ≫ l)).pull (sqToBase A s)) (abelian₂ ((Over.pullback s).obj A) L)

end Zarhin

def ZarhinScheme : Prop :=
  ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] (P : LB (A ⊗ B).left) (l : A ⟶ B),
    IsAbelianScheme A → IsAbelianScheme B → IsDual A B P → Zarhin.IsPolarisation A B P l →
      ∃ c : Pic (G4 (A ⊗ B) ⊗ G4 (A ⊗ B)).left, IsPrincipalPol (G4 (A ⊗ B)) c

namespace Zarhin

def SymmetricBundleSt : Prop :=
  ∀ (C : Type) [Field C] [IsAlgClosed C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C],
    v.Integers R → ∀ (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A →
      ∀ c : Pic (A ⊗ A).left, IsPrincipalPol A c →
        ∃ (L : LB A.left) (hL : L.IsLB), Out.Rigidified A L ∧ Out.Sym A L ∧ Out.RelAmple A L ∧ Out.KTriv A L ∧
          c = lam (cls L hL) (fst A A) (snd A A)

variable {S : Scheme.{0}}

theorem isPolarisation_of_relAmple {A B : Over S} [GrpObj A] [GrpObj B] {P : LB (A ⊗ B).left} (hP : P.IsLB)
    {l : A ⟶ B} (hl : IsMonHom l) {L : LB A.left} (hL : L.IsLB) (ha : Out.RelAmple A L)
    (e : LBIso (abelian₂ A L) (ev P (fst A A) (snd A A ≫ l))) : IsPolarisation A B P l := by
  refine ⟨hl, fun Ω _ _ s => ?_⟩
  have h := isGrpPullback_pullback A s
  have hL' := pull_isLB hL (pullback.fst A.hom s)
  obtain ⟨w, hw⟩ := (cls_eq_iff hL' hL').1 rfl
  obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_mem_and_subset (X := S)
    (x := s (IsLocalRing.closedPoint Ω)) (U := ⊤) trivial
  have hE : (ev P (fst A A) (snd A A ≫ l)).IsLB := pull_isLB hP _
  have hΛ : (abelian₂ A L).IsLB := LB.isLB_linComb hL _ _
  have hΛ' : (abelian₂ ((Over.pullback s).obj A) (L.pull (pullback.fst A.hom s))).IsLB := LB.isLB_linComb hL' _ _
  refine ⟨_, hL', relAmple_pull h.1 hL hL' ((isGen_iff w).1 hw) U hU
    (fun y => by rwa [Subsingleton.elim y (IsLocalRing.closedPoint Ω)]) ha,
    (cls_eq_iff (pull_isLB hE _) hΛ').1 ?_⟩
  rw [cls_pull hE, ← (cls_eq_iff hΛ hE).2 e,
    show cls _ hΛ = lam (cls L hL) (fst A A) (snd A A) from cls_cube_two hL _ _ hΛ,
    show cls _ hΛ' = lam (cls _ hL') (fst _ _) (snd _ _) from cls_cube_two hL' _ _ hΛ',
    sqToBase, pull_lam, lift_fst, lift_snd, cls_pull hL, lam_pull_of_isGrpPullback h]
  rfl

theorem isPolarisation_id (Q : Out.PolAV S) : IsPolarisation Q.A Q.A (abelian₂ Q.A Q.L) (𝟙 _) := by
  have hΛ : (abelian₂ Q.A Q.L).IsLB := LB.isLB_linComb Q.isLB _ _
  refine isPolarisation_of_relAmple hΛ inferInstance Q.isLB Q.ample ((cls_eq_iff hΛ (pull_isLB hΛ _)).1 ?_)
  rw [cls_ev hΛ, evc, Category.comp_id, lift_fst_snd, Over.id_left, pull_id]

theorem hyp_zero (S : Scheme.{0}) : IsAbelianScheme (𝟙_ (Over S)) ∧
    IsDual (𝟙_ (Over S)) (𝟙_ (Over S)) (LB.triv _) ∧
    IsPolarisation (𝟙_ (Over S)) (𝟙_ (Over S)) (LB.triv _) (𝟙 _) := by
  let Q := Out.Inh.zeroPolAV S
  have hΛ : (abelian₂ Q.A Q.L).IsLB := LB.isLB_linComb Q.isLB _ _
  refine ⟨Q.isAb, isDual_unit, isPolarisation_of_relAmple (LB.isLB_triv _) inferInstance Q.isLB Q.ample
    ((cls_eq_iff hΛ (pull_isLB (LB.isLB_triv _) _)).1 ?_)⟩
  rw [show cls _ hΛ = lam (cls Q.L Q.isLB) (fst _ _) (snd _ _) from cls_cube_two Q.isLB _ _ hΛ,
    show fst Q.A Q.A = 1 from toUnit_unique _ _, lam_one_left]
  exact (map_zero (pull _)).symm

theorem hyp_elliptic (hD : GlobalTheory.Published.DualAbelianScheme) {R : Type} [CommRing R] [IsNoetherianRing R]
    (W : WeierstrassCurve R) [W.IsElliptic] :
    let E := GlobalTheory.WeierstrassCurve.ellPolAV W
    E.g = 1 ∧ IsAbelianScheme E.A ∧ IsDual E.A E.A (abelian₂ E.A E.L) ∧ IsPolarisation E.A E.A (abelian₂ E.A E.L) (𝟙 _) := by
  intro E
  exact ⟨rfl, E.isAb, GlobalTheory.PerfectDual.isDual_of_isPerfect hD _ _ E.isAb E.isAb E.smoothDim E.smoothDim
    (isPerfect_ell W), isPolarisation_id E⟩

theorem exists_prod {R : Type} [CommRing R] (P P' : Out.PolAV (Sp R)) :
    ∃ M : LB (P.A ⊗ P'.A).left, M.IsLB ∧ Out.Rigidified _ M ∧ Out.Sym _ M ∧ Out.RelAmple _ M ∧ Out.KTriv _ M := by
  have hB : IsAbelianScheme (P.A ⊗ P'.A) := AbelianSchemeGerms.isAbelianScheme_tensor _ _ P.isAb P'.isAb
  let p := fst P.A P'.A
  let q := snd P.A P'.A
  obtain ⟨M, hM, eM⟩ := cls_surj (pull p.left (cls P.L P.isLB) + pull q.left (cls P'.L P'.isLB))
  have hd := LB.isLB_div hM (pull_isLB P.isLB p.left)
  have last : LBIso (M.div (P.L.pull p.left)) (P'.L.pull q.left) := by
    refine (cls_eq_iff hd (pull_isLB P'.isLB _)).1 ?_
    rw [cls_div hM (pull_isLB P.isLB p.left), eM, cls_pull P.isLB, cls_pull P'.isLB, add_sub_cancel_left]
  haveI := P.isAb.proper
  haveI := P'.isAb.proper
  haveI := hB.proper
  refine ⟨M, hM, ?_, ?_, ?_, GlobalTheory.TripleProd.kTriv_prod hM P.isLB P'.isLB eM P.ktriv P'.ktriv⟩
  · rw [PolProd.rigidified_iff _ hM, eM, map_add, ← pull_comp, ← pull_comp, PolProd.eSec_comp p,
      PolProd.eSec_comp q, (PolProd.rigidified_iff _ P.isLB).1 P.rigid,
      (PolProd.rigidified_iff _ P'.isLB).1 P'.rigid, add_zero]
  · have h₁ := ((PolProd.sym_iff _ P.isLB).1 P.sym).pull_over (π' := (P.A ⊗ P'.A).hom) p.left (Over.w p)
    have h₂ := ((PolProd.sym_iff _ P'.isLB).1 P'.sym).pull_over (π' := (P.A ⊗ P'.A).hom) q.left (Over.w q)
    rw [PolProd.sym_iff _ hM, eM]
    convert PolProd.locZero_add h₁ h₂ using 1
    rw [map_add, map_sub, map_sub, ← pull_comp, ← pull_comp, ← pull_comp, ← pull_comp, PolProd.inv_comp_left p,
      PolProd.inv_comp_left q]
    abel
  · exact (relAmple_iff_isAmpleLB_of_isAffine _ hM).2 (IsAmpleLB.box
      ((relAmple_iff_isAmpleLB_of_isAffine _ P.isLB).1 P.ample)
      ((relAmple_iff_isAmpleLB_of_isAffine _ P'.isLB).1 P'.ample)
      hM (p := p.left) (q := q.left) (f := P.A.hom) (g := P'.A.hom) (IsPullback.of_hasPullback _ _) last.symm)

def prodPol {R : Type} [CommRing R] (P P' : Out.PolAV (Sp R)) : Out.PolAV (Sp R) where
  A := P.A ⊗ P'.A
  isAb := AbelianSchemeGerms.isAbelianScheme_tensor _ _ P.isAb P'.isAb
  g := P'.g + P.g
  smoothDim := smooth_prod P.smoothDim P'.smoothDim
  L := (exists_prod P P').choose
  isLB := (exists_prod P P').choose_spec.1
  rigid := (exists_prod P P').choose_spec.2.1
  sym := (exists_prod P P').choose_spec.2.2.1
  ample := (exists_prod P P').choose_spec.2.2.2.1
  ktriv := (exists_prod P P').choose_spec.2.2.2.2

theorem conclusion_of_polAV {R : Type} [CommRing R] (E : Out.PolAV (Sp R)) :
    ∃ c : Pic (G4 (E.A ⊗ E.A) ⊗ G4 (E.A ⊗ E.A)).left, IsPrincipalPol (G4 (E.A ⊗ E.A)) c :=
  let D := prodPol E E
  ⟨_, GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase.isPrincipalPol_of_polAV (prodPol D (prodPol D (prodPol D D)))⟩

theorem exists_elliptic (R : Type) [CommRing R] [IsLocalRing R] : ∃ W : WeierstrassCurve R, W.IsElliptic := by
  have e : IsUnit ((-8 : R) * 37 + (-11) * (-27)) := by
    rw [show (-8 : R) * 37 + (-11) * (-27) = 1 by norm_num]; exact isUnit_one
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add e with u | u
  · refine ⟨⟨0, 0, 1, -1, 0⟩, ⟨?_⟩⟩
    convert isUnit_of_mul_isUnit_right u using 1
    norm_num [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  · refine ⟨⟨0, 0, 1, 0, 0⟩, ⟨?_⟩⟩
    convert isUnit_of_mul_isUnit_right u using 1
    norm_num [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

theorem isLocalRing_integers {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R] [Algebra R C]
    (hv : v.Integers R) : IsLocalRing R :=
  haveI : IsDomain R := Function.Injective.isDomain (algebraMap R C) hv.hom_inj
  haveI := ValuationRing.of_integers v hv
  inferInstance

theorem symmetricBundle_elliptic {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R]
    [Algebra R C] (hv : v.Integers R) :
    ∃ (A : Over (Sp R)) (_ : GrpObj A) (c : Pic (A ⊗ A).left), IsAbelianScheme A ∧
      SmoothOfRelativeDimension 1 A.hom ∧ IsPrincipalPol A c ∧
      ∃ (L : LB A.left) (hL : L.IsLB), Out.Rigidified A L ∧ Out.Sym A L ∧ Out.RelAmple A L ∧ Out.KTriv A L ∧
        c = lam (cls L hL) (fst A A) (snd A A) := by
  have := isLocalRing_integers hv
  obtain ⟨W, _⟩ := exists_elliptic R
  let E := GlobalTheory.WeierstrassCurve.ellPolAV W
  exact ⟨E.A, E.grp, _, E.isAb, E.smoothDim, GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase.isPrincipalPol_of_polAV E, E.L, E.isLB, E.rigid, E.sym,
    E.ample, E.ktriv, rfl⟩

theorem setting_padic (p : ℕ) [Fact p.Prime] : IsAlgClosed ℂ_[p] ∧
    (Valued.v : Valuation ℂ_[p] NNReal).Integers (Valued.v : Valuation ℂ_[p] NNReal).integer :=
  ⟨inferInstance, Valuation.integer.integers _⟩

theorem zarhinStatement_of (hD : GlobalTheory.Published.DualAbelianScheme) (hC : GlobalTheory.Published.CubeTheorem) (hZ : ZarhinScheme)
    (hS : SymmetricBundleSt) : GlobalTheory.CompanionTheory.Ar.GR.ZarhinStatement := by
  intro C _ _ v R _ _ hv A _ L hA hL ha
  have := isLocalRing_integers hv
  have hΛ : (abelian₂ A L).IsLB := LB.isLB_linComb hL _ _
  obtain ⟨a₁, a₂⟩ := GlobalTheory.CubeDual.isAdditive_lam hC hA hL hΛ
  obtain ⟨B, _, P, hB, -, h₁, h₂⟩ := hD _ A hA
  obtain ⟨x, hx, -⟩ := h₁.univ A (abelian₂ A L) hΛ a₁
  have hm := isMonHom_of_classifying _ A A B (abelian₂ A L) P h₁ h₂.additive hΛ a₂ x hx
  obtain ⟨c, hc⟩ := hZ _ A B P x hA hB h₁ (isPolarisation_of_relAmple h₁.isLB hm hL ha hx)
  have hAB := AbelianSchemeGerms.isAbelianScheme_tensor A B hA hB
  have h4 : IsAbelianScheme (G4 (A ⊗ B)) := AbelianSchemeGerms.isAbelianScheme_tensor _ _ hAB
    (AbelianSchemeGerms.isAbelianScheme_tensor _ _ hAB (AbelianSchemeGerms.isAbelianScheme_tensor _ _ hAB hAB))
  obtain ⟨M, hM, m₁, m₂, m₃, m₄, -⟩ := hS C v R hv _ h4 c hc
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim R _ h4
  haveI := hA.comm
  haveI := hB.comm
  refine ⟨⟨G4 (A ⊗ B), h4, g, hg, M, hM, m₁, m₂, m₃, m₄⟩, lift (lift (𝟙 A) 1) 1, fst _ _ ≫ fst _ _,
    inferInstance, inferInstance, by simp⟩

end Zarhin

end GlobalTheory.CompanionTheory.Hypotheses₂
