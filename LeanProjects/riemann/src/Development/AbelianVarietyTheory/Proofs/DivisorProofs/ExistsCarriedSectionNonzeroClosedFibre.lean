import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecCarried
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppEqZeroOfSval
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionNonzeroOfExpansionModMaximalIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExpandsAtOfAdmissibleBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionUniformisationOfTraitUnif
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GmMulEqOfResMulEq
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpandsGTransport
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IntegralSectionsCorrespond
import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.NotIsThetaOfNonunit
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaArc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsoUniqueOfRig
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.InvTheta

open GlobalTheory.FamFieldPull

section General

variable {X X' Y Y' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K : Type} [Fintype K]

theorem isUnit_gs_iff {Z : Scheme.{0}} (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U) (a : Γ(X, U)) :
    IsUnit (gs r z U a) ↔ r z ∈ X.basicOpen a := by
  rw [gs_stalkMap r z U h, isUnit_map_iff (r.stalkMap z).hom, gs_eq (𝟙 X) (r z) U h]
  exact (X.mem_basicOpen a _ h).symm

theorem gs_zero {Z : Scheme.{0}} (r : Z ⟶ X) (z : Z) (U : X.Opens) : gs r z U 0 = 0 := by
  unfold gs
  split_ifs
  · rw [map_zero, map_zero]
  · rfl

theorem mem_basicOpen_app {Z : Scheme.{0}} (r : Z ⟶ X) (z : Z) (U : X.Opens) (a : Γ(X, U)) :
    z ∈ Z.basicOpen ((r.app U).hom a) ↔ r z ∈ X.basicOpen a :=
  (congrArg (z ∈ ·) (Scheme.preimage_basicOpen r a)).symm.to_iff

theorem gw_comp_of_rig {S S' S'' : Scheme.{0}} {A : Over S} {A' : Over S'} {A'' : Over S''} [GrpObj A]
    [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A'] [GrpObj A''] [IsCommMonObj A''] (hA : IsAbelianScheme A'')
    {M : LB A.left} {M' : LB A'.left} {M'' : LB A''.left} (hM : M.IsLB) (hM' : M'.IsLB) (hM'' : M''.IsLB)
    {b : A'.left ⟶ A.left} {c : A''.left ⟶ A'.left} {d : A''.left ⟶ A.left} (hd : c ≫ b = d)
    {e : (𝟙_ (Over S')).left ⟶ (𝟙_ (Over S)).left} {e' : (𝟙_ (Over S'')).left ⟶ (𝟙_ (Over S')).left}
    {e'' : (𝟙_ (Over S'')).left ⟶ (𝟙_ (Over S)).left} (hee : e' ≫ e = e'')
    (he : eSec A' ≫ b = e ≫ eSec A) (he' : eSec A'' ≫ c = e' ≫ eSec A') (he'' : eSec A'' ≫ d = e'' ≫ eSec A)
    {w : LB.Iso M' (M.pull b)} {w' : LB.Iso M'' (M'.pull c)} {w'' : LB.Iso M'' (M.pull d)}
    (g : w.IsGen) (g' : w'.IsGen) (g'' : w''.IsGen)
    {t : LB.Gen (M.pull (eSec A))} {t' : LB.Gen (M'.pull (eSec A'))} {t'' : LB.Gen (M''.pull (eSec A''))}
    (m : LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec A') (fun _ => 1)) t' (rigPullOf b e he M t))
    (m' : LB.Gen.Maps (LB.linCombIso w' (K := PUnit) (fun _ => eSec A'') (fun _ => 1)) t'' (rigPullOf c e' he' M' t'))
    (m'' : LB.Gen.Maps (LB.linCombIso w'' (K := PUnit) (fun _ => eSec A'') (fun _ => 1)) t'' (rigPullOf d e'' he'' M t))
    (Z : Scheme.{0}) (r : Z ⟶ A''.left) (z : Z) (j : M.ι) (i : M'.ι) (k : M''.ι) (hj : d (r z) ∈ M.U j)
    (hi : c (r z) ∈ M'.U i) (hk : r z ∈ M''.U k) : gw w'' r z j k = gw w (r ≫ c) z j i * gw w' r z i k := by
  subst hd hee
  have pg := (isGen_iff _).1 g
  have pg' := (isGen_iff _).1 g'
  obtain ⟨v, T⟩ := exists_comp hM' w w' pg pg' hM hM''
  have p := (maps_iff w _ (fun _ => eSec A) _ t' t e _ (rigPull_le b e he M) (fun _ => rfl)).1 m
  have p' := (maps_iff w' _ (fun _ => eSec A') _ t'' t' e' _ (rigPull_le c e' he' M') (fun _ => rfl)).1 m'
  have q := T.pmaps_comp hM' (fun _ => he') p p'
  have mv := (maps_iff v _ (fun _ => eSec A) _ t'' t (e' ≫ e) (rigPullOf (c ≫ b) (e' ≫ e) he'' M t)
    (rigPull_le (c ≫ b) (e' ≫ e) he'' M) (fun _ => rfl)).2 q
  obtain rfl : v = w'' := iso_unique_of_rig GlobalTheory.abelianSchemeLaws_all.1.globalFns A'' hA hM'' hM
    ((isGen_iff _).2 (T.pgen_comp hM' pg pg')) g'' mv m''
  exact T Z r z j i k hj hi hk

theorem isSecPull_self (hL : L.IsLB) {F' : X' ⟶ X'} (hF : F' ≫ F = F) {w : LB.Iso L' (L.pull F)}
    {w' : LB.Iso L' (L'.pull F')}
    (T : ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) (j : L.ι) (i k : L'.ι), F (r z) ∈ L.U j → F' (r z) ∈ L'.U i →
      r z ∈ L'.U k → gw w r z j k = gw w (r ≫ F') z j i * gw w' r z i k)
    {φ' : K → (Y' ⟶ X')} {φ : K → (Y ⟶ X)} {ε : K → ℤ} {b : Y' ⟶ Y} {c : Y' ⟶ Y'} (hc : c ≫ b = b)
    (hφ : ∀ κ, φ' κ ≫ F' = c ≫ φ' κ) {a : LB.Sec (LB.LinComb L' φ' ε)} {s : LB.Sec (LB.LinComb L φ ε)}
    (H : IsSecPull w φ' φ ε b a s) : IsSecPull w' φ' φ' ε c a a := by
  intro Z r z p q hp hq
  choose j hj using fun κ => exists_chart hL (F (φ' κ (r z)))
  have e₁ : ∀ κ, φ' κ ((r ≫ c) z) = F' (φ' κ (r z)) := fun κ => congrArg (fun g => g (r z)) (hφ κ).symm
  have e₂ : ∀ x, F (F' x) = F x := fun x => congrArg (fun g => g x) hF
  have h₁ := H Z r z j q hj hq
  have h₂ := H Z (r ≫ c) z j p (fun κ => by rw [e₁, e₂]; exact hj κ) (fun κ => by rw [e₁]; exact hp κ)
  rw [Category.assoc, hc, h₁] at h₂
  have h₃ : ∏ κ, gw w (r ≫ φ' κ) z (j κ) (q κ) ^ ε κ =
      (∏ κ, gw w ((r ≫ c) ≫ φ' κ) z (j κ) (p κ) ^ ε κ) * ∏ κ, gw w' (r ≫ φ' κ) z (p κ) (q κ) ^ ε κ := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun κ _ => ?_
    rw [← mul_zpow, T Z (r ≫ φ' κ) z (j κ) (p κ) (q κ) (hj κ) (hp κ) (hq κ), Category.assoc, Category.assoc, hφ]
  rw [h₃, Units.val_mul, _root_.mul_assoc] at h₂
  exact ((Units.mul_right_inj _).1 h₂).symm

theorem app_eq_zero_of_isSecPull (hL : L.IsLB) {w : LB.Iso L' (L.pull F)}
    {φ' : K → (Y' ⟶ X')} {φ : K → (Y ⟶ X)} {ε : K → ℤ} {b : Y' ⟶ Y} (hφ : ∀ κ, φ' κ ≫ F = b ≫ φ κ)
    {a : LB.Sec (LB.LinComb L' φ' ε)} {s : LB.Sec (LB.LinComb L φ ε)} (H : IsSecPull w φ' φ ε b a s)
    {Z T : Scheme.{0}} {r : Z ⟶ Y'} {t : Z ⟶ T} {u : T ⟶ Y} (hr : r ≫ b = t ≫ u)
    (h0 : ∀ j, (u.app _).hom (s.f j) = 0) (q : K → L'.ι) : (r.app _).hom (a.f q) = 0 := by
  refine fn_ext fun z hz => ?_
  have hz' : r z ∈ LB.wchart L' φ' q := hz
  choose j hj using fun κ => exists_chart hL (F (φ' κ (r z)))
  have h₁ := H Z r z j q hj (fun κ => Set.mem_iInter.1 hz' κ)
  have hm : u (t z) ∈ LB.wchart L φ j := by
    have e : u (t z) = b (r z) := congrArg (fun g => g z) hr.symm
    rw [e]
    exact GlobalTheory.SecPull.mem_wchart_comp hφ (Set.mem_iInter.2 hj)
  have h₃ : gs (r ≫ b) z (LB.wchart L φ j) (s.f j) = 0 := by
    rw [hr]
    refine (gs_pull t u z _ hm _).symm.trans ((congrArg (gs t z _) (h0 j)).trans ?_)
    exact gs_zero t z _
  have h₂ := (Units.mul_right_eq_zero _).1 (h₁.symm.trans h₃)
  refine (gs_pull (𝟙 Z) r z _ hz' _).trans ?_
  rw [Category.id_comp]
  exact h₂.trans (gs_zero _ _ _).symm

theorem mem_basicOpen_of_isSecPull (hL' : L'.IsLB) {w : LB.Iso L' (L.pull F)}
    {φ' : K → (Y' ⟶ X')} {φ : K → (Y ⟶ X)} {ε : K → ℤ} {b : Y' ⟶ Y} (hφ : ∀ κ, φ' κ ≫ F = b ≫ φ κ)
    {a : LB.Sec (LB.LinComb L' φ' ε)} {s : LB.Sec (LB.LinComb L φ ε)} (H : IsSecPull w φ' φ ε b a s)
    {y : Y'} {p : K → L.ι} (hy : b y ∈ Y.basicOpen (s.f p)) : ∃ q, y ∈ Y'.basicOpen (a.f q) := by
  choose q hq using fun κ => exists_chart hL' (φ' κ y)
  have hp : b y ∈ LB.wchart L φ p := Y.basicOpen_le _ hy
  have h₁ := H Y' (𝟙 _) y p q (fun κ => by
    have e : F (φ' κ y) = φ κ (b y) := congrArg (fun g => g y) (hφ κ)
    exact e ▸ Set.mem_iInter.1 hp κ) hq
  have hu : IsUnit (gs (𝟙 Y' ≫ b) y (LB.wchart L φ p) (s.f p)) :=
    (isUnit_gs_iff (𝟙 Y' ≫ b) y _ hp _).2 hy
  rw [h₁] at hu
  exact ⟨q, (isUnit_gs_iff (𝟙 Y') y _ (Set.mem_iInter.2 hq) _).1 (isUnit_of_mul_isUnit_right hu)⟩

end General

theorem thick_zero_apply {R : Type} [CommRing R] [IsLocalRing R]
    (p : Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (0 + 1)))) : thick R (maximalIdeal R) 0 p = closedPoint R := by
  apply PrimeSpectrum.ext
  refine ((maximalIdeal.isMaximal R).eq_of_le (thick R (maximalIdeal R) 0 p).isPrime.ne_top fun x hx => ?_).symm
  change Ideal.Quotient.mk (maximalIdeal R ^ (0 + 1)) x ∈ p.asIdeal
  rw [Ideal.Quotient.eq_zero_iff_mem.2 (by rwa [zero_add, pow_one])]
  exact zero_mem _

theorem eq_of_expandsAt {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (U : Unif I D A G) {k : ℕ}
    (hk : 1 ≤ k) (Φ : Fam D.toPre (FractionRing R) k) {f : ∀ α, D.toPre.SecB k α}
    (hf : ∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) α) (DegPre.famε k) (Φ.s α)
      (D.toPre.famφB α) (DegPre.famε k) (f α) (DegPre.prB D.toPre (FractionRing R)).left 1)
    {σ τ : H0 U.LG.L k} (hσ : ∀ e, U.ExpandsAt e k σ f) (hτ : ∀ e, U.ExpandsAt e k τ f) : σ = τ := by
  have := U.smooth
  have h1 : ∀ {Y : Scheme.{0}} (p : Y ⟶ Sp R), scal p (1 : R) = 1 := fun p => by rw [scal, map_one, map_one]
  obtain ⟨s, hs⟩ := GlobalTheory.RigidSections.exists_restrict U.toUnifPre k σ
  obtain ⟨t, ht⟩ := GlobalTheory.RigidSections.exists_restrict U.toUnifPre k τ
  obtain rfl : s = t := ((U.expand k hk).2 Φ).unique
    ⟨1, one_ne_zero, σ, f, by rw [h1]; exact hs, fun α => by rw [h1]; exact hf α, hσ⟩
    ⟨1, one_ne_zero, τ, f, by rw [h1]; exact ht, fun α => by rw [h1]; exact hf α, hτ⟩
  have h := GlobalTheory.IntegralExpansion.secIsMul_of_secScal U.LG.isLB G.hom (a := 1)
    (GlobalTheory.ExpInt.generic_app_injective G) ht (by rw [h1]; exact hs)
  refine DVR.SecOps.sec_ext fun j => (h j).trans ?_
  rw [h1, resTop, map_one, _root_.one_mul]

theorem exists_nonzero {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {R' : Type} [CommRing R'] [IsDomain R']
    [IsLocalRing R'] {ρ : R →+* R'} [IsLocalHom ρ] {D : DegData R (maximalIdeal R)} {D' : DegData R' (maximalIdeal R')}
    (hD : IsPullDeg ρ D.toPre D'.toPre) {A' : PolAV (Sp (FractionRing R'))} {G' : Over (Sp R')} [GrpObj G']
    [IsCommMonObj G'] (U' : UnifPre (maximalIdeal R') D' A' G') {f : ∀ α, D.toPre.SecB 1 α}
    {f' : ∀ α, D'.toPre.SecB 1 α}
    (hf : ∀ x, IsSecPull hD.w (D'.toPre.famφB x) (D.toPre.famφB (hD.xe x)) (DegPre.famε 1) (prA hD) (f' x) (f (hD.xe x)))
    (hvan : ∀ α, α ≠ 0 → ∀ j, ((D.toPre.prBe (maximalIdeal R) 0).left.app _).hom ((f α).f j) = 0)
    {x : D.toPre.P.A.left} (hx : D.toPre.P.A.hom x = closedPoint R) (hn : x ∈ nonzeroLocus (f 0))
    {σ : H0 U'.LG.L 1} (hσ : U'.ExpandsAt 0 1 σ f') :
    ∃ g' : G'.left, G'.hom g' = closedPoint R' ∧ g' ∈ secNz (DVR.secOfH0 σ) := by
  have hover : prA hD ≫ D.toPre.P.A.hom = D'.toPre.P.A.hom ≫ specOf ρ := by
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    exact congrArg (· ≫ _) (Over.w hD.e.hom)
  have hle : maximalIdeal R ^ (0 + 1) ≤ (maximalIdeal R' ^ (0 + 1)).comap ρ := by
    rw [zero_add, pow_one, pow_one]
    exact fun a ha => map_nonunit ρ a ha
  have hsq : thick R' (maximalIdeal R') 0 ≫ specOf ρ =
      spMap (Ideal.quotientMap _ ρ hle) ≫ thick R (maximalIdeal R) 0 := by
    rw [← Spec.map_comp, ← Spec.map_comp]; rfl
  have hpG : (U'.gt 0).pG.left ≫ D'.toPre.P.A.hom =
      (thickObj R' (maximalIdeal R') 0 G').hom ≫ thick R' (maximalIdeal R') 0 := Over.w (U'.gt 0).pG
  let t : (thickObj R' (maximalIdeal R') 0 G').left ⟶ pullback D.toPre.P.A.hom (thick R (maximalIdeal R) 0) :=
    pullback.lift ((U'.gt 0).pG.left ≫ prA hD)
      ((thickObj R' (maximalIdeal R') 0 G').hom ≫ spMap (Ideal.quotientMap _ ρ hle)) (by
        rw [Category.assoc, hover, ← Category.assoc]
        erw [hpG]
        rw [Category.assoc, hsq, Category.assoc])
  have hvan' : ∀ α, α ≠ 0 → ∀ j, ((U'.gt 0).pG.left.app _).hom ((f' α).f j) = 0 := fun α hα j =>
    app_eq_zero_of_isSecPull D.toPre.P.isLB (GlobalTheory.ExpGTrans.famφB_pull hD α) (hf α)
      (t := t) (u := (D.toPre.prBe (maximalIdeal R) 0).left) (pullback.lift_fst _ _ _).symm
      (hvan _ (fun h => hα (hD.xe.map_eq_zero_iff.1 h))) j
  obtain ⟨x₁, hx₁, hx₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := D.toPre.P.A.hom) (g := specOf ρ) x
    (closedPoint R') (hx.trans (comap_closedPoint ρ).symm)
  have hnt : Nontrivial (R' ⧸ maximalIdeal R' ^ (0 + 1)) := Ideal.Quotient.nontrivial_iff.2 (by
    rw [zero_add, pow_one]; exact (maximalIdeal.isMaximal R').ne_top)
  obtain ⟨p⟩ : Nonempty (Spec (CommRingCat.of (R' ⧸ maximalIdeal R' ^ (0 + 1)))) := inferInstance
  have hx₃ : D'.toPre.P.A.hom (hD.e.inv.left x₁) = closedPoint R' :=
    (congrArg (fun g => g x₁) (Over.w hD.e.inv)).trans hx₂
  have hx₄ : prA hD (hD.e.inv.left x₁) = x := by
    have e : hD.e.inv.left ≫ prA hD = pullback.fst _ _ := by
      rw [← Category.assoc, ← Over.comp_left, Iso.inv_hom_id, Over.id_left, Category.id_comp]
    exact (congrArg (fun g => g x₁) e).trans hx₁
  obtain ⟨x₂, hx₅, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := D'.toPre.P.A.hom)
    (g := thick R' (maximalIdeal R') 0) (hD.e.inv.left x₁) p (hx₃.trans (thick_zero_apply p).symm)
  have := (U'.gt 0).q_surj
  obtain ⟨y, hy⟩ := (U'.gt 0).q.left.surjective x₂
  have hy' : (U'.gt 0).pG.left y = hD.e.inv.left x₁ := by
    rw [← hx₅, ← hy]; rfl
  have hn' : ∀ α, α = 0 → ∃ j, x ∈ D.toPre.P.A.left.basicOpen ((f α).f j) := by
    rintro _ rfl
    exact TopologicalSpace.Opens.mem_iSup.1 hn
  obtain ⟨j, hj⟩ := hn' (hD.xe 0) (map_zero _)
  obtain ⟨q, hq⟩ := mem_basicOpen_of_isSecPull D'.toPre.P.isLB (GlobalTheory.ExpGTrans.famφB_pull hD 0) (hf 0)
    (y := hD.e.inv.left x₁) (p := j) (by rw [hx₄]; exact hj)
  obtain ⟨i, hi⟩ := ExpandNonzero.nonzero_of_expandsAt_zero R' D' A' G' U' 1 σ f' hσ hvan' y
    ⟨q, (mem_basicOpen_app (U'.gt 0).pG.left y _ _).2 (hy' ▸ hq)⟩
  refine ⟨(fstG (maximalIdeal R') 0 G').left y, ?_, TopologicalSpace.Opens.mem_iSup.2 ⟨i 0, ?_⟩⟩
  · exact (congrArg (fun g => g y) (Over.w (fstG (maximalIdeal R') 0 G'))).trans (thick_zero_apply _)
  · obtain ⟨i₀, rfl⟩ : ∃ i₀, i = fun _ => i₀ := ⟨i 0, funext fun a => by rw [Subsingleton.elim a 0]⟩
    have hi' : (fstG (maximalIdeal R') 0 G').left y ∈ G'.left.basicOpen (σ.f fun _ => i₀) :=
      (mem_basicOpen_app (fstG (maximalIdeal R') 0 G').left y _ _).1 hi
    change _ ∈ G'.left.basicOpen ((G'.left.presheaf.map (homOfLE (DVR.chart_le_weighted_chart_single i₀)).op).hom (σ.f fun _ => i₀))
    exact (Scheme.basicOpen_res _ (σ.f fun _ => i₀) (homOfLE (DVR.chart_le_weighted_chart_single i₀)).op).ge
      ⟨DVR.h0_le _ (G'.left.basicOpen_le _ hi'), hi'⟩

theorem secCarried_of_isSecPull {X : Scheme.{0}} {L : LB X} {f : X ⟶ X} {w : LB.Iso L (L.pull f)} {σ : H0 L 1}
    (H : IsSecPull w (fun _ : Fin 1 => 𝟙 X) (fun _ : Fin 1 => 𝟙 X) (fun _ => ((1 : ℕ) : ℤ)) f σ σ) :
    SecCarried L (DVR.secOfH0 σ) f w := by
  intro z j k hk hj
  have h := H X (𝟙 X) z (fun _ => j) (fun _ => k) (fun _ => hj) (fun _ => hk)
  rw [Fin.prod_univ_one, Category.id_comp, Category.id_comp, zpow_natCast, pow_one] at h
  have h₁ := gs_res f z (DVR.chart_le_weighted_chart_single j) hj (σ.f fun _ => j)
  have h₂ := gs_res (𝟙 X) z (DVR.chart_le_weighted_chart_single k) hk (σ.f fun _ => k)
  exact (gs_eq _ _ _ hj _).symm.trans (h₁.trans (h.trans (congrArg (_ * ·) (h₂.symm.trans (gs_eq _ _ _ hk _)))))

set_option maxHeartbeats 1000000 in
set_option linter.unusedVariables false in

theorem exists_carried_nonzero : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hB : Base R) (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R') (hF : FinExt ρ) (hG : IsGal ρ) (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'] (hS' : IsSemiAbelian G') (U' : Unif (maximalIdeal R') D' A' G') (a : GalAct ρ hD U') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left) (hS : IsSemiAbelian G) (hβ : IsGrpPullback G' G (spMap ρ) β) (hact : ∀ σ, a.act σ ≫ β = β), ∃ θ : U'.LG.L.Sec, (∀ (σ : Gal ρ) (h : IsPullDeg (Gal.hom σ) D'.toPre D'.toPre) (bc : G' ≅ (Over.pullback (specOf (Gal.hom σ))).obj G'), bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ)) = a.act σ → ∀ hP : IsPullUnif (Gal.hom σ) h bc U' U', PullOver hD h → SecCarried U'.LG.L θ _ (Classical.choose hP.lg)) ∧ ∃ g' : G'.left, G'.hom g' = closedPoint R' ∧ g' ∈ secNz θ := by
  intro R _ _ _ hB R' _ _ _ ρ hF hG D D' hD A' G' _ _ hS' U' a G _ _ β hS hβ hact
  have : IsNoetherianRing R := hB.1.1
  have := Ident.finExt_isLocalHom hF
  have hgf : GlobalFnsSt := GlobalTheory.abelianSchemeLaws_all.1.globalFns
  have h1 : ∀ {T : Type} [CommRing T] {Y : Scheme.{0}} (p : Y ⟶ Sp T), scal p (1 : T) = 1 := fun p => by
    rw [scal, map_one, map_one]
  obtain ⟨b, x, hx, hn⟩ :=
    GlobalTheory.ThetaSectionTest.exists_nonzero_closed GlobalTheory.abelianSchemeLaws_all.1.secBaseChange D.toPre
  obtain ⟨Φ, f, hΦ, rfl, hvan⟩ := GlobalTheory.FamWtZero.exists_family R hB.1 D 1 le_rfl b
  choose f' hf' using fun y : D'.toPre.X => (GlobalTheory.SecPull.existsUnique_secPull _ _ _ _ _ _ _ D.toPre.P.isLB
    D'.toPre.P.isLB hD.w hD.w_gen _ _ _ (DegPre.famε 1) _ (GlobalTheory.ExpGTrans.famφB_pull hD y) (f (hD.xe y))).exists
  obtain ⟨Φ', hΦ'⟩ := GlobalTheory.exists_fam_of_isPullDeg hgf R R' ρ D.toPre D'.toPre hD 1 Φ f f'
    (fun α => h1 (T := R) _ ▸ hΦ α) hf'
  obtain ⟨s, hs⟩ := IntFam.exists_expandsAt_of_admissibleBase R' hF.1 D' A' G' hS' U' 1 le_rfl Φ' f'
    (fun α => by rw [h1]; exact hΦ' α)
  refine ⟨DVR.secOfH0 s, fun σ h bc hbc hP hO => ?_, exists_nonzero hD U'.toUnifPre hf' hvan hx hn (hs 0)⟩
  obtain ⟨hw, -, -, hlev⟩ := Classical.choose_spec hP.lg
  generalize Classical.choose hP.lg = wL at hw hlev
  have hc : prA h ≫ prA hD = prA hD := hO.2 _ _ rfl rfl
  have hee : specOf (Gal.hom σ) ≫ specOf ρ = specOf ρ := by
    rw [← Spec.map_comp]
    congr 1
    ext r
    exact σ.2 r
  have T := gw_comp_of_rig D'.toPre.P.isAb D.toPre.P.isLB D'.toPre.P.isLB D'.toPre.P.isLB hc hee hD.he h.he hD.he
    hD.w_gen h.w_gen hD.w_gen hD.w_rig h.w_rig hD.w_rig
  have hself : ∀ y y', y' = y → (∀ κ, D'.toPre.famφB y κ ≫ prA h = prA h ≫ D'.toPre.famφB y' κ) →
      IsSecPull h.w (D'.toPre.famφB y) (D'.toPre.famφB y') (DegPre.famε 1) (prA h) (f' y) (f' y') := by
    rintro y _ rfl hφ
    exact isSecPull_self D.toPre.P.isLB hc T hc hφ (hf' _)
  obtain ⟨τ, hτ⟩ := (GlobalTheory.SecPull.existsUnique_secPull _ _ _ _ _ _ _ U'.LG.isLB U'.LG.isLB wL hw _
    (fun _ : Fin 1 => 𝟙 G'.left) (fun _ : Fin 1 => 𝟙 G'.left) (fun _ => ((1 : ℕ) : ℤ)) _
    (fun _ => (Category.id_comp _).trans (Category.comp_id _).symm) s).exists
  have hτe : ∀ e, U'.ExpandsAt e 1 τ f' := fun e => by
    obtain ⟨l, hl, hp, ht, hsq⟩ := hlev e
    refine GlobalTheory.expandsAt_transport R' R' _ _ D' D' A' A' G' G' U'.toUnifPre U'.toUnifPre _ h.w h.xe _ wL
      h.w_gen hw (GlobalTheory.ExpGTrans.famφB_pull h) e e 1 l
      ⟨hl, ⟨hp, fun y => ?_⟩, (GlobalTheory.square_res_iff_gw hl hp h.w wL (U'.w e) (U'.w e)).1 hsq⟩ s τ f' f' hτ
      (fun y => hself y _ (hO.1 y) (GlobalTheory.ExpGTrans.famφB_pull h y)) (hs e)
    obtain ⟨hψ, hm⟩ := ht y
    exact ⟨hψ, (maps_iff h.w _ _ _ _ _ l _ (GeneratorPullback.pullAlong_le _ _ _ _ _ hψ) (fun _ => rfl)).1 hm⟩
  obtain rfl : τ = s := eq_of_expandsAt U' le_rfl Φ' hΦ' hτe hs
  exact secCarried_of_isSecPull hτ

end GlobalTheory.Mum.InvTheta
