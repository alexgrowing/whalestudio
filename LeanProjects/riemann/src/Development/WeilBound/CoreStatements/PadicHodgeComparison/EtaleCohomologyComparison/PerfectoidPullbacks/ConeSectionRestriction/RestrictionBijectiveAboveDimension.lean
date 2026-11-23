import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.RSubOneMem
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GrCechFin
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalProjectiveModel

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb

theorem isProper_of_isO1 {R : Type} [CommRing R] {X : Scheme.{0}} {p : X ⟶ ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R}
    {D : E.LineData X} (hD : IsTautologicalLine p D) : IsProper p := by
  obtain ⟨N, i, hi, hip, -⟩ := hD
  exact GlobalTheory.CommonModel.isProper_of_isProjOver ⟨N, i, hi, hip⟩

theorem cls_congr {R : Type} [CommRing R] (K : Cx.{1} R) {n : ℕ} {a b : K.X n} (h : a = b) (ha : K.d n a = 0)
    (hb : K.d n b = 0) : K.cls a ha = K.cls b hb := by
  subst h; rfl

variable {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))

omit [CharZero K] in
theorem ks_mono (𝒱 : Set X.Opens) {s S : ℕ} (h : s ≤ S) : KS q s 𝒱 ≤ KS q S 𝒱 := fun T hT =>
  ⟨⟨show pdP T.δ S = ⊥ from eq_bot_iff.2 ((dividedPowerFiltration_anti T.δ h).trans (le_of_eq hT.1.1)), hT.1.2⟩, hT.2⟩

omit [CharZero K] in
theorem ks_pd (𝒱 : Set X.Opens) (s : ℕ) (c : (KS q s 𝒱).FullSubcategory) : ((KS q s 𝒱).ι.obj c).pdPow s = ⊥ :=
  c.property.1.1

omit [CharZero K] in
theorem ks_sec (D : E.LineData X) (s : ℕ) (c : (KS q s (𝒱D D)).FullSubcategory) :
    ∃ (V : X.Opens) (σ : (V : Scheme.{0}) ⟶ D.Y), σ ≫ D.f = V.ι ∧ InU V ((KS q s (𝒱D D)).ι.obj c) := by
  obtain ⟨-, V, ⟨σ, hσ⟩, hV⟩ := c.property
  exact ⟨V, σ, hσ, hV⟩

def clsK (D : E.LineData X) (s : ℕ) (Λ : CLiftK (KS q s (𝒱D D)).ι D) :
    CH.H ((KS q s (𝒱D D)).ι ⋙ O (smFun X q)) 2 :=
  (CH.cx ((KS q s (𝒱D D)).ι ⋙ O (smFun X q))).cls (zK Λ s) (zK_cocycle Λ s (ks_pd q _ s))

theorem pull_cls_zK {C C' : Type 1} [Category.{0} C] [Category.{0} C'] {g : C ⥤ Thick (smFun X q)} {D : E.LineData X}
    (Λ : CLiftK g D) (h : C' ⥤ C) (s : ℕ) (hz : CH.d _ 2 (zK Λ s) = 0) (hz' : CH.d _ 2 (zK (Λ.precomp h) s) = 0) :
    (CH.Mor.restrict (g ⋙ O (smFun X q)) h).pull 2 ((CH.cx (g ⋙ O (smFun X q))).cls (zK Λ s) hz) =
      (CH.cx ((h ⋙ g) ⋙ O (smFun X q))).cls (zK (Λ.precomp h) s) hz' := by
  refine (CrystallineSemistableComparison.P.mapH_cls (CH.Mor.restrict (g ⋙ O (smFun X q)) h).hom 2 (zK Λ s) hz ?_).trans ?_
  · change CH.d _ 2 ((CH.Mor.restrict (g ⋙ O (smFun X q)) h).pullC 2 (zK Λ s)) = 0
    rw [CH.Mor.d_pullC, hz, map_zero]
  · exact cls_congr _ (zK_precomp Λ h s).symm _ _

theorem clsK_res (D : E.LineData X) {s S : ℕ} (h : s ≤ S) (Λ : CLiftK (KS q s (𝒱D D)).ι D)
    (ΛS : CLiftK (KS q S (𝒱D D)).ι D) :
    (CH.Mor.restrict ((KS q S (𝒱D D)).ι ⋙ O (smFun X q)) (ObjectProperty.ιOfLE (ks_mono q _ h))).pull 2
      (clsK q D S ΛS) = clsK q D s Λ := by
  have hz1 : CH.d _ 2 (zK (ΛS.precomp (ObjectProperty.ιOfLE (ks_mono q (𝒱D D) h))) S) = 0 :=
    zK_cocycle (ΛS.precomp (ObjectProperty.ιOfLE (ks_mono q (𝒱D D) h))) S
      (fun c => (ks_mono q (𝒱D D) h _ c.property).1.1)
  have hz2 : CH.d _ 2 (zK (ΛS.precomp (ObjectProperty.ιOfLE (ks_mono q (𝒱D D) h))) s) = 0 :=
    zK_cocycle (ΛS.precomp (ObjectProperty.ιOfLE (ks_mono q (𝒱D D) h))) s (ks_pd q _ s)
  refine (pull_cls_zK q ΛS _ S _ hz1).trans ((cls_congr _ ?_ hz1 hz2).trans ?_)
  · funext σ
    exact (plogK_congr _ h (ks_pd q _ s _) (r_sub_one_mem _ σ)).symm
  · exact zK_cls_eq _ Λ s (ks_pd q _ s) hz2 _

theorem pull_restrict_comp {R : Type} [CommRing R] {C C' C'' : Type 1} [Category.{0} C] [Category.{0} C']
    [Category.{0} C''] (F : C ⥤ ModuleCat.{0} R) (G : C' ⥤ C) (G' : C'' ⥤ C') (n : ℕ) (x : CH.H F n) :
    (CH.Mor.restrict F (G' ⋙ G)).pull n x = (CH.Mor.restrict (G ⋙ F) G').pull n ((CH.Mor.restrict F G).pull n x) :=
  (CrystallineSemistableComparison.P.pull_comp (CH.Mor.restrict F G) (CH.Mor.restrict (G ⋙ F) G') n x).1

theorem resK_res (𝒱 : Set X.Opens) {s S : ℕ} (h : s ≤ S) (x : HdR q 2) :
    resK q (KS q s 𝒱) 2 x = (CH.Mor.restrict ((KS q S 𝒱).ι ⋙ O (smFun X q)) (ObjectProperty.ιOfLE (ks_mono q 𝒱 h))).pull 2
      (resK q (KS q S 𝒱) 2 x) :=
  pull_restrict_comp (O (smFun X q)) (KS q S 𝒱).ι (ObjectProperty.ιOfLE (ks_mono q 𝒱 h)) 2 x

theorem restriction_bijective_above_dimension (d : ℕ) [SmoothOfRelativeDimension d q] (D : E.LineData X) (hD : IsTautologicalLine q D) :
    ∀ S, d < S → Function.Bijective (resK q (KS q S (𝒱D D)) 2) := by
  have hP : IsProper q := isProper_of_isO1 hD
  obtain ⟨U, hU⟩ := (cov_ex q).2 d inferInstance
  have hcov : sSup (𝒱D D) = ⊤ := by
    obtain ⟨N, i, -, -, hi⟩ := hD
    exact sSup_𝒱D D N i hi
  intro S hS
  exact (k_iso q U S (fun α => by rw [hU]; exact hS) (𝒱D D) hcov 2).1

theorem test_factor (D : E.LineData X) (S : ℕ) (x : HdR q 2)
    (hA : ∀ ΛS : CLiftK (KS q S (𝒱D D)).ι D, resK q (KS q S (𝒱D D)) 2 x = clsK q D S ΛS)
    {C : Type 1} [Category.{0} C] (g' : C ⥤ (KS q S (𝒱D D)).FullSubcategory) {s : ℕ} (hsS : s ≤ S)
    (hs : ∀ c, ((g' ⋙ (KS q S (𝒱D D)).ι).obj c).pdPow s = ⊥) (Λ : CLiftK (g' ⋙ (KS q S (𝒱D D)).ι) D)
    (hz : CH.d _ 2 (zK Λ s) = 0) :
    (CH.cx ((g' ⋙ (KS q S (𝒱D D)).ι) ⋙ O (smFun X q))).cls (zK Λ s) hz =
      (CH.Mor.restrict (O (smFun X q)) (g' ⋙ (KS q S (𝒱D D)).ι)).pull 2 x := by
  let ΛS := (lift_exists q D S).some
  have hz1 : CH.d _ 2 (zK (ΛS.precomp g') S) = 0 :=
    zK_cocycle (ΛS.precomp g') S (fun c => (g'.obj c).property.1.1)
  have hz2 : CH.d _ 2 (zK (ΛS.precomp g') s) = 0 := zK_cocycle (ΛS.precomp g') s hs
  rw [pull_restrict_comp (O (smFun X q)) (KS q S (𝒱D D)).ι g' 2 x]
  change _ = (CH.Mor.restrict ((KS q S (𝒱D D)).ι ⋙ O (smFun X q)) g').pull 2 (resK q (KS q S (𝒱D D)) 2 x)
  rw [hA ΛS]
  refine (zK_cls_eq Λ (ΛS.precomp g') s hs hz hz2).trans ?_
  refine (cls_congr _ (funext fun σ => plogK_congr _ hsS (hs _) (r_sub_one_mem _ σ)) hz2 hz1).trans ?_
  exact (pull_cls_zK q ΛS g' S _ hz1).symm

theorem isFirstChernDeRham_unique_of (d : ℕ) [SmoothOfRelativeDimension d q] (D : E.LineData X) (hD : IsTautologicalLine q D) (c c' : HdR q 2)
    (hc : IsFirstChernDeRham q D c) (hc' : IsFirstChernDeRham q D c') : c = c' := by
  have hk := restriction_bijective_above_dimension q d D hD
  let Λ₀ := (lift_exists q D (d + 1)).some
  obtain ⟨z, hz, hzf, hzc⟩ := hc (d + 1) _ (KS q (d + 1) (𝒱D D)).ι (ks_pd q _ _) (ks_sec q D _) Λ₀
  obtain ⟨z', hz', hzf', hzc'⟩ := hc' (d + 1) _ (KS q (d + 1) (𝒱D D)).ι (ks_pd q _ _) (ks_sec q D _) Λ₀
  have e : z = z' := funext fun σ => (hzf σ).trans (hzf' σ).symm
  subst e
  exact (hk (d + 1) (by omega)).1 (hzc.symm.trans hzc')

theorem isFirstChernDeRham_exists_of (d : ℕ) [SmoothOfRelativeDimension d q] (D : E.LineData X) (hD : IsTautologicalLine q D) :
    ∃ c : HdR q 2, IsFirstChernDeRham q D c := by
  have hk := restriction_bijective_above_dimension q d D hD
  let Λ₀ := (lift_exists q D (d + 1)).some
  let x := Function.surjInv (hk (d + 1) (by omega)).2 (clsK q D (d + 1) Λ₀)
  have hx : resK q (KS q (d + 1) (𝒱D D)) 2 x = clsK q D (d + 1) Λ₀ := Function.surjInv_eq _ _
  have hA : ∀ S, d + 1 ≤ S → ∀ ΛS : CLiftK (KS q S (𝒱D D)).ι D,
      resK q (KS q S (𝒱D D)) 2 x = clsK q D S ΛS := by
    intro S hS ΛS
    obtain ⟨x', hx'⟩ := (hk S (by omega)).2 (clsK q D S ΛS)
    have e : resK q (KS q (d + 1) (𝒱D D)) 2 x' = resK q (KS q (d + 1) (𝒱D D)) 2 x := by
      rw [resK_res q (𝒱D D) hS x', hx', clsK_res q D hS Λ₀ ΛS, hx]
    rw [← (hk (d + 1) (by omega)).1 e, hx']
  refine ⟨x, fun s C _ g hs hV Λ => ⟨zK Λ s, zK_cocycle Λ s hs, fun σ => rfl, ?_⟩⟩
  let S := max s (d + 1)
  let g' : C ⥤ (KS q S (𝒱D D)).FullSubcategory := ObjectProperty.lift _ g fun c =>
    ⟨⟨show pdP _ S = ⊥ from eq_bot_iff.2 ((dividedPowerFiltration_anti _ (le_max_left _ _)).trans (le_of_eq (hs c))),
      fun r y hy => by simpa using hy⟩, by
      obtain ⟨V, σ, hσ, hV⟩ := hV c
      exact ⟨V, ⟨σ, hσ⟩, hV⟩⟩
  exact test_factor q D S x (hA S (le_max_right _ _)) g' (le_max_left _ _) hs Λ (zK_cocycle Λ s hs)

end CrystallineSemistableComparison.Pb
