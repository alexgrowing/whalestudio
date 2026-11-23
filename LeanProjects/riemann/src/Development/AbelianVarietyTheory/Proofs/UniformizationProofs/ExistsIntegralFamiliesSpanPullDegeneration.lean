import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.SectionScalarValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.GenCalc
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsRepresentativesModNsmul
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBasisOfEq
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.FamEqOnClassOfEq
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueSecPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsTwistBasisOffPrime
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFamOfIsPullDegStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IntegralFamilyPrescribedTermUnitAtPrimeStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FamSpan

section Gen

variable {X X' Y Y' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K : Type} [Fintype K]

theorem exists_up_sec {w : LB.Iso L' (L.pull F)} (hw : PGen w) (hL : L.IsLB) (hL' : L'.IsLB)
    (φ' : K → (Y ⟶ X')) (ε : K → ℤ) (s : LB.Sec (LB.LinComb L' φ' ε)) :
    ∃ a : LB.Sec (LB.LinComb L (fun k => φ' k ≫ F) ε),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (p : K → L.ι) (q : K → L'.ι),
        r z ∈ LB.wchart L (fun k => φ' k ≫ F) p → r z ∈ LB.wchart L' φ' q →
        gs r z (LB.wchart L (fun k => φ' k ≫ F) p) (a.f p) =
          (pw w φ' ε r z p q).val * gs r z (LB.wchart L' φ' q) (s.f q) := by
  choose u hu using fun p q => exists_pw w φ' ε p q
  have glue : ∀ p : K → L.ι, ∃ a : Γ(Y, LB.wchart L (fun k => φ' k ≫ F) p),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) q,
      r z ∈ LB.wchart L (fun k => φ' k ≫ F) p → r z ∈ LB.wchart L' φ' q →
      gs r z _ a = (pw w φ' ε r z p q).val * gs r z (LB.wchart L' φ' q) (s.f q) := by
    intro p
    let W : (K → L'.ι) → Y.Opens := fun q => LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q
    obtain ⟨v, hv⟩ : ∃ v : ∀ q, Γ(Y, W q), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) q, r z ∈ W q →
        gs r z (W q) (v q) = (pw w φ' ε r z p q).val * gs r z (LB.wchart L' φ' q) (s.f q) :=
      ⟨fun q => (u p q).val * (Y.presheaf.map (homOfLE (inf_le_right : W q ≤ LB.wchart L' φ' q)).op).hom (s.f q),
        fun Z r z q hz => (gs_mul r z _ hz _ _).trans (congrArg₂ (· * ·)
          ((gs_unit r z _ hz _).trans (congrArg Units.val (hu p q Z r z hz)))
          (gs_res r z _ hz _))⟩
    obtain ⟨a, ha, -⟩ := Y.sheaf.existsUnique_gluing' W (LB.wchart L (fun k => φ' k ≫ F) p)
      (fun q => homOfLE inf_le_left) (fun y hy => by
        choose q hq using fun k => exists_chart hL' (φ' k y)
        exact Opens.mem_iSup.2 ⟨q, hy, Set.mem_iInter.2 hq⟩) v
      (fun q q' => fn_ext (V := W q ⊓ W q') fun y hy => by
        refine (gs_res (𝟙 Y) y inf_le_left hy _).trans (Eq.trans ?_ (gs_res (𝟙 Y) y inf_le_right hy _).symm)
        rw [hv _ _ y q hy.1, hv _ _ y q' hy.2, sec_trans s (𝟙 Y) y hy.1.2 hy.2.2,
          pw_trans hw φ' ε (𝟙 Y) y hy.1.1 hy.1.1 hy.1.2 hy.2.2, trF_self hL _ ε (𝟙 Y) y hy.1.1, _root_.one_mul,
          ← _root_.mul_assoc, ← Units.val_mul, mul_right_comm, inv_mul_cancel, _root_.one_mul])
    refine ⟨a, fun Z r z q h₁ h₂ => ?_⟩
    have hz : r z ∈ W q := ⟨h₁, h₂⟩
    exact (gs_res r z inf_le_left hz a).symm.trans ((congrArg (gs r z (W q)) (ha q)).trans (hv Z r z q hz))
  choose a ha using glue
  refine ⟨⟨a, fun j j' => fn_ext fun y hy => ?_⟩, fun Z r z p q => ha p Z r z q⟩
  choose q hq using fun k => exists_chart hL' (φ' k y)
  have m : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L' φ' q := Set.mem_iInter.2 hq
  refine (gs_res (𝟙 Y) y _ hy _).trans (Eq.trans ?_ ((gs_mul (𝟙 Y) y _ hy _ _).trans (congrArg₂ (· * ·)
    ((gs_unit (𝟙 Y) y _ hy _).trans (congrArg Units.val (gm_linComb L _ ε (𝟙 Y) y j j' hy.1 hy.2)))
    (gs_res (𝟙 Y) y _ hy _))).symm)
  refine (ha j _ (𝟙 Y) y q hy.1 m).trans (Eq.trans ?_ (congrArg _ (ha j' _ (𝟙 Y) y q hy.2 m)).symm)
  rw [pw_trans hw φ' ε (𝟙 Y) y hy.1 hy.2 m m, trF_self hL' _ ε (𝟙 Y) y m, inv_one, _root_.mul_one, Units.val_mul,
    _root_.mul_assoc]
  rfl

def fac (w : LB.Iso L' (L.pull F)) (φ' : K → (Y ⟶ X')) (ε : K → ℤ) {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z)
    (J : (Z ⟶ X) → L.ι) (J' : (Z ⟶ X') → L'.ι) : (Z.presheaf.stalk z)ˣ :=
  ∏ k, gw w (r ≫ φ' k) z (J ((r ≫ φ' k) ≫ F)) (J' (r ≫ φ' k)) ^ ε k

theorem fac_congr (w : LB.Iso L' (L.pull F)) {φ' : K → (Y ⟶ X')} {ψ' : K → (Y' ⟶ X')} (ε : K → ℤ) {Z : Scheme.{0}}
    {r : Z ⟶ Y} {r' : Z ⟶ Y'} (h : ∀ k, r ≫ φ' k = r' ≫ ψ' k) (z : Z)
    (J : (Z ⟶ X) → L.ι) (J' : (Z ⟶ X') → L'.ι) : fac w φ' ε r z J J' = fac w ψ' ε r' z J J' := by
  simp only [fac, h]

theorem exists_up_val {w : LB.Iso L' (L.pull F)} (hw : PGen w) (hL : L.IsLB) (hL' : L'.IsLB)
    (φ' : K → (Y' ⟶ X')) (ε : K → ℤ) (s : LB.Sec (LB.LinComb L' φ' ε)) (θ : Y ⟶ Y') (φ : K → (Y ⟶ X))
    (hφ : φ = fun k => (θ ≫ φ' k) ≫ F) :
    ∃ a : LB.Sec (LB.LinComb L φ ε), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) J J', Good L z J → Good L' z J' →
      sval a r z J = (fac w φ' ε (r ≫ θ) z J J').val * sval s (r ≫ θ) z J' := by
  subst hφ
  obtain ⟨a, ha⟩ := exists_up_sec hw hL hL' (fun k => θ ≫ φ' k) ε (DVR.pullSec L' φ' ε s θ)
  refine ⟨a, fun Z r z J J' hJ hJ' => ?_⟩
  rw [← sval_pullSec φ' ε s θ r z hJ']
  refine (ha Z r z _ _ (hJ.mem _ r) (hJ'.mem _ r)).trans (congrArg₂ (· * ·) (congrArg Units.val ?_) rfl)
  simp only [pw, fac, Category.assoc]

theorem val_of_rel {w : LB.Iso L' (L.pull F)} {φ' : K → (X' ⟶ X')} {φ : K → (X ⟶ X)} {ε : K → ℤ}
    (hc : ∀ κ, φ' κ ≫ F = F ≫ φ κ) {s : LB.Sec (LB.LinComb L φ ε)} {a : LB.Sec (LB.LinComb L' φ' ε)}
    (H : ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) (p : K → L.ι) (q : K → L'.ι),
      (∀ κ, F (φ' κ (r z)) ∈ L.U (p κ)) → (∀ κ, φ' κ (r z) ∈ L'.U (q κ)) →
      gs (r ≫ F) z (LB.wchart L φ p) (s.f p) =
        (∏ κ, gw w (r ≫ φ' κ) z (p κ) (q κ) ^ ε κ).val * gs r z (LB.wchart L' φ' q) (a.f q))
    {Z : Scheme.{0}} (r : Z ⟶ X') (z : Z) {J J'} (hJ : Good L z J) (hJ' : Good L' z J') :
    sval s (r ≫ F) z J = (fac w φ' ε r z J J').val * sval a r z J' := by
  rw [sval_of s (r ≫ F) z J (fun k => J ((r ≫ φ' k) ≫ F)) (fun k => by rw [Category.assoc, Category.assoc, hc])]
  exact H Z r z _ _ (fun k => hJ ((r ≫ φ' k) ≫ F)) (fun k => hJ' (r ≫ φ' k))

theorem exists_good' (hL : L.IsLB) {Z : Scheme.{0}} (z : Z) : ∃ J, Good L z J := by
  choose I hI using fun ψ : Z ⟶ X => exists_chart hL (ψ z)
  exact ⟨I, hI⟩

end Gen

section Span

variable {X X' Y Y' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K : Type} [Fintype K]

theorem span_sec {w : LB.Iso L' (L.pull F)} (hw : PGen w) (hL : L.IsLB) (hL' : L'.IsLB)
    {φ' : K → (X' ⟶ X')} {φ : K → (X ⟶ X)} {ε : K → ℤ} (hc : ∀ κ, φ' κ ≫ F = F ≫ φ κ)
    (π : Y ⟶ X) (π' : Y' ⟶ X') (θ : Y ⟶ Y') (θ' : Y' ⟶ Y) (hθ : θ' ≫ θ = 𝟙 _) (hπ : θ ≫ π' ≫ F = π)
    {ψ' : K → (Y' ⟶ X')} (hψ : ∀ k, ψ' k = π' ≫ φ' k) {m : ℕ} (b g : Fin m → LB.Sec (LB.LinComb L φ ε))
    {C : Type} (κc : C → Γ(Y, ⊤))
    (hb : ∀ s : LB.Sec (LB.LinComb L (fun i => π ≫ φ i) ε), ∃ c : Fin m → C, ∀ j,
      s.f j = ∑ i, resTop (LB.wchart L (fun i => π ≫ φ i) j) (κc (c i)) *
        (show Γ(Y, LB.wchart L (fun i => π ≫ φ i) j) from (DVR.pullSec L φ ε (b i) π).f j))
    (ρ : Fin m → Γ(X, ⊤)) (hg : ∀ i j, (g i).f j = resTop _ (ρ i) * (b i).f j)
    (g' : Fin m → LB.Sec (LB.LinComb L' φ' ε))
    (hg' : ∀ i (y : Y') J J', Good L y J → Good L' y J' →
      sval (g i) ((𝟙 Y' ≫ π') ≫ F) y J = (fac w φ' ε (𝟙 Y' ≫ π') y J J').val * sval (g' i) (𝟙 Y' ≫ π') y J')
    (G : Fin m → LB.Sec (LB.LinComb L' ψ' ε)) (hG : ∀ i, GeneratorPullback.SecScal L' ψ' ε (G i) φ' ε (g' i) π' 1)
    (u : Fin m → Γ(Y', ⊤)) (hu : ∀ i, u i * (π' ≫ F).appTop.hom (ρ i) = 1)
    (s : LB.Sec (LB.LinComb L' ψ' ε)) :
    ∃ c : Fin m → C, ∀ j, s.f j = ∑ i, resTop (LB.wchart L' ψ' j) (θ'.appTop.hom (κc (c i)) * u i) *
      (show Γ(Y', LB.wchart L' ψ' j) from (G i).f j) := by
  obtain ⟨a, ha⟩ := exists_up_val hw hL hL' ψ' ε s θ (fun i => π ≫ φ i) (funext fun k => by
    rw [hψ, Category.assoc, Category.assoc, hc, ← hπ, Category.assoc, Category.assoc])
  obtain ⟨c, hc'⟩ := hb a
  refine ⟨c, IntegralCoord.lin_of_sval hL' _ G fun y J' hJ' => ?_⟩
  obtain ⟨J, hJ⟩ := exists_good' hL y
  have e₁ := ha _ θ' y J J' hJ hJ'
  rw [hθ, sval_lin (fun i => κc (c i)) _ hc' θ' y hJ] at e₁
  have hπ' : θ' ≫ π = (𝟙 Y' ≫ π') ≫ F := by rw [← hπ, ← Category.assoc, hθ, Category.assoc]
  have fc : fac w φ' ε (𝟙 Y' ≫ π') y J J' = fac w ψ' ε (𝟙 Y') y J J' :=
    fac_congr w ε (fun k => by rw [hψ, Category.assoc]) y J J'
  refine (Units.mul_right_inj (fac w ψ' ε (𝟙 Y') y J J')).1 (e₁.symm.trans ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have e₂ := hg' i y J J' hJ hJ'
  rw [secScal_sval (hG i) (𝟙 Y') y hJ', fc] at e₂
  have e₃ : sval (g i) ((𝟙 Y' ≫ π') ≫ F) y J =
      gs ((𝟙 Y' ≫ π') ≫ F) y ⊤ (ρ i) * sval (b i) ((𝟙 Y' ≫ π') ≫ F) y J := by
    have hm := hJ.mem φ ((𝟙 Y' ≫ π') ≫ F)
    exact (congrArg (gs _ y _) (hg i _)).trans ((gs_mul _ y _ hm _ _).trans
      (congrArg₂ (· * ·) (gs_res _ y le_top hm _) rfl))
  have e₄ : gs (𝟙 Y') y ⊤ (u i) * gs ((𝟙 Y' ≫ π') ≫ F) y ⊤ (ρ i) = 1 := by
    rw [Category.assoc, ← IntegralCoord.gs_appTop, ← gs_mul _ y ⊤ (by trivial), hu, gs_eq _ y ⊤ (by trivial), map_one,
      map_one]
  rw [sval_pullSec _ _ _ _ _ y hJ, hπ', gs_mul _ y ⊤ (by trivial), IntegralCoord.gs_appTop, Category.id_comp θ',
    mul_left_comm, ← e₂, e₃, _root_.mul_assoc, ← _root_.mul_assoc (gs (𝟙 Y') y ⊤ (u i)), e₄, _root_.one_mul]

theorem zero_sec {w : LB.Iso L' (L.pull F)} (hL : L.IsLB) (hL' : L'.IsLB)
    {φ' : K → (X' ⟶ X')} {φ : K → (X ⟶ X)} {ε : K → ℤ} (π' : Y' ⟶ X')
    {ψ' : K → (Y' ⟶ X')} (g : LB.Sec (LB.LinComb L φ ε)) (hg : ∀ j, g.f j = 0) (g' : LB.Sec (LB.LinComb L' φ' ε))
    (hg' : ∀ (y : Y') J J', Good L y J → Good L' y J' →
      sval g ((𝟙 Y' ≫ π') ≫ F) y J = (fac w φ' ε (𝟙 Y' ≫ π') y J J').val * sval g' (𝟙 Y' ≫ π') y J')
    (G : LB.Sec (LB.LinComb L' ψ' ε)) (hG : GeneratorPullback.SecScal L' ψ' ε G φ' ε g' π' 1) (j) : G.f j = 0 := by
  refine sec_ext_val hL' (s' := DVR.SecOps.secZero) (fun y J' hJ' => ?_) j
  obtain ⟨J, hJ⟩ := exists_good' hL y
  have e := hg' y J J' hJ hJ'
  have z₁ : sval g ((𝟙 Y' ≫ π') ≫ F) y J = 0 := by
    refine (congrArg (gs _ y _) (hg _)).trans ((gs_eq _ y _ (hJ.mem φ _) _).trans ?_)
    exact (congrArg _ (map_zero _)).trans (map_zero _)
  have z₂ : sval (DVR.SecOps.secZero : LB.Sec (LB.LinComb L' ψ' ε)) (𝟙 Y') y J' = 0 := by
    refine (gs_eq _ y _ (hJ'.mem ψ' _) _).trans ?_
    exact (congrArg _ (map_zero _)).trans (map_zero _)
  rw [z₁, secScal_sval hG (𝟙 Y') y hJ'] at e
  rw [z₂]
  exact (Units.mul_right_eq_zero _).1 e.symm

end Span

section Pull

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R}
  {D' : DegPre R'}

theorem famφB_comm (hD : IsPullDeg φ D D') (x : D'.X) (κ : Fin 4) :
    D'.famφB x κ ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) =
      (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) ≫ D.famφB (hD.xe x) κ := by
  have gp := pull_grp hD
  let U := pushPt gp.1.w (𝟙 D'.P.A)
  have hU : U.left = hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ) := Category.id_comp _
  have hw : (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) ≫ D.P.A.hom = D'.P.A.hom ≫ specOf φ := gp.1.w
  have h2 : (toUnit D'.P.A ≫ D'.c x).left ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) =
      (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) ≫ (toUnit D.P.A ≫ D.c (hD.xe x)).left := by
    show (D'.P.A.hom ≫ (D'.c x).left) ≫ _ = _ ≫ D.P.A.hom ≫ (D.c (hD.xe x)).left
    rw [Category.assoc, hD.c_pr, ← Category.assoc, ← hw, Category.assoc]
  fin_cases κ
  · exact (Category.id_comp _).trans (Category.comp_id _).symm
  · have e := gp.2 D'.P.A (𝟙 _) (toUnit _ ≫ D'.c x) (U ≫ 𝟙 _) (U ≫ toUnit _ ≫ D.c (hD.xe x))
      (by rw [Category.comp_id]; rfl) (by rw [Over.comp_left, hU]; exact h2.symm)
    rw [← MonObj.comp_mul, Over.comp_left, hU] at e
    exact e.symm
  · exact h2
  · show (D'.P.A.hom ≫ eSec D'.P.A) ≫ _ = _ ≫ D.P.A.hom ≫ eSec D.P.A
    rw [Category.assoc, hD.he, ← Category.assoc, ← hw, Category.assoc]

end Pull

section Concrete

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R}
  {D' : DegPre R'}

theorem base_eq (φ : R →+* R') : (jFK (R := R') (FractionRing R') ≫ jK R') ≫ specOf φ =
    Spec.map (CommRingCat.ofHom ((algebraMap R' (FractionRing R')).comp φ)) := by
  show (Spec.map (CommRingCat.ofHom (algebraMap (FractionRing R') (FractionRing R'))) ≫
    Spec.map (CommRingCat.ofHom (algebraMap R' (FractionRing R')))) ≫ Spec.map (CommRingCat.ofHom φ) = _
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]

theorem exists_iso (hD : IsPullDeg φ D D') (T : Over (Spec (CommRingCat.of R)))
    (a : (TF (R := R') (FractionRing R')).left ≅ T.left)
    (ha : a.hom ≫ T.hom = (TF (R := R') (FractionRing R')).hom ≫ specOf φ) :
    ∃ e : (DegPre.BF D' (FractionRing R')).left ≅ (T ⊗ D.P.A).left,
      e.hom ≫ (fst T D.P.A).left = (fst (TF (R := R') (FractionRing R')) D'.P.A).left ≫ a.hom ∧
      e.hom ≫ (snd T D.P.A).left = (DegPre.prB D' (FractionRing R')).left ≫
        (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) := by
  have P₁ : IsPullback (fst (TF (R := R') (FractionRing R')) D'.P.A).left (DegPre.prB D' (FractionRing R')).left
      (TF (R := R') (FractionRing R')).hom D'.P.A.hom := IsPullback.of_hasPullback _ _
  have P₂ : IsPullback (fst T D.P.A).left (snd T D.P.A).left T.hom D.P.A.hom := IsPullback.of_hasPullback _ _
  have P₃ := P₁.paste_vert (pull_grp hD).1.flip
  have P₄ : IsPullback ((fst (TF (R := R') (FractionRing R')) D'.P.A).left ≫ a.hom)
      ((DegPre.prB D' (FractionRing R')).left ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ))) T.hom D.P.A.hom :=
    P₃.of_iso (Iso.refl _) a (Iso.refl _) (Iso.refl _) (by simp) (by simp) (by simpa using ha.symm) (by simp)
  exact ⟨P₄.isoIsPullback _ _ P₂, P₄.isoIsPullback_hom_fst _ _ P₂, P₄.isoIsPullback_hom_snd _ _ P₂⟩

theorem span_term (hD : IsPullDeg φ D D') (k : ℕ) (x : D'.X) {m : ℕ} (b g : Fin m → D.SecB k (hD.xe x))
    (hb : IsSecBasis (T := Over.mk (Spec.map (CommRingCat.ofHom ((algebraMap R' (FractionRing R')).comp φ))))
      (A := D.P.A) _ (fun i => DVR.pullSec D.P.L (D.famφB (hD.xe x)) (DegPre.famε k) (b i)
        (snd (Over.mk (Spec.map (CommRingCat.ofHom ((algebraMap R' (FractionRing R')).comp φ)))) D.P.A).left))
    (r : Fin m → R) (hr : ∀ i, algebraMap R' (FractionRing R') (φ (r i)) ≠ 0)
    (hg : ∀ i j, (g i).f j = resTop _ (scal D.P.A.hom (r i)) * (b i).f j) (g' : Fin m → D'.SecB k x)
    (hg' : ∀ i (y : (DegPre.BF D' (FractionRing R')).left) J J', Good D.P.L y J → Good D'.P.L y J' →
      sval (g i) ((𝟙 _ ≫ (DegPre.prB D' (FractionRing R')).left) ≫
        (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ))) y J =
      (fac hD.w (D'.famφB x) (DegPre.famε k) (𝟙 _ ≫ (DegPre.prB D' (FractionRing R')).left) y J J').val *
        sval (g' i) (𝟙 _ ≫ (DegPre.prB D' (FractionRing R')).left) y J')
    (G : Fin m → LB.Sec (LB.LinComb D'.P.L (DegPre.famφ D' (FractionRing R') x) (DegPre.famε k)))
    (hG : ∀ i, GeneratorPullback.SecScal D'.P.L (DegPre.famφ D' (FractionRing R') x) (DegPre.famε k) (G i) (D'.famφB x)
      (DegPre.famε k) (g' i) (DegPre.prB D' (FractionRing R')).left 1)
    (s : LB.Sec (LB.LinComb D'.P.L (DegPre.famφ D' (FractionRing R') x) (DegPre.famε k))) :
    ∃ c : Fin m → FractionRing R', ∀ j, s.f j = ∑ i, resTop _ (DVR.gF D' (FractionRing R') (c i)) * (G i).f j := by
  obtain ⟨e, e₁, e₂⟩ := exists_iso hD
    (Over.mk (Spec.map (CommRingCat.ofHom ((algebraMap R' (FractionRing R')).comp φ)))) (Iso.refl _)
    ((Category.id_comp _).trans (base_eq φ).symm)
  replace e₁ := e₁.trans (Category.comp_id _)
  obtain ⟨c, hc⟩ := span_sec ((isGen_iff hD.w).1 hD.w_gen) D.P.isLB D'.P.isLB (famφB_comm hD x) _
    (DegPre.prB D' (FractionRing R')).left e.inv e.hom e.hom_inv_id (by rw [← e₂, e.inv_hom_id_assoc])
    (DVR.GC.famφ_eq D' (FractionRing R') x) b g
    (fun c => (fst (Over.mk (Spec.map (CommRingCat.ofHom ((algebraMap R' (FractionRing R')).comp φ)))) D.P.A).left.appTop.hom c)
    (fun s => (hb s).exists) (fun i => scal D.P.A.hom (r i)) hg g' hg' G hG
    (fun i => DVR.gF D' (FractionRing R') (algebraMap R' (FractionRing R') (φ (r i)))⁻¹) (fun i => by
      have q : (DegPre.prB D' (FractionRing R')).left ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) ≫ D.P.A.hom =
          (fst (TF (R := R') (FractionRing R')) D'.P.A).left ≫
            Spec.map (CommRingCat.ofHom ((algebraMap R' (FractionRing R')).comp φ)) := by
        rw [← Category.assoc, ← e₂, ← e₁, Category.assoc, Category.assoc, Over.w]
        exact congrArg _ (Over.w _).symm
      have q' : ((DegPre.prB D' (FractionRing R')).left ≫
          (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ))).appTop.hom (scal D.P.A.hom (r i)) =
          DVR.gF D' (FractionRing R') (algebraMap R' (FractionRing R') (φ (r i))) := by
        have := congrArg (fun t => t.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (r i))) q
        refine Eq.trans this ?_
        refine congrArg (fst (TF (R := R') (FractionRing R')) D'.P.A).left.appTop.hom ?_
        refine (IntegralCoord.specMap_appTop _ _).trans (congrArg _ (congrArg _ ?_))
        exact Iso.inv_hom_id_apply (Scheme.ΓSpecIso (CommRingCat.of R)) (r i)
      rw [q', ← map_mul, inv_mul_cancel₀ (hr i), map_one]) s
  refine ⟨fun i => (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R'))).hom.hom (c i) *
    (algebraMap R' (FractionRing R') (φ (r i)))⁻¹, fun j => (hc j).trans (Finset.sum_congr rfl fun i _ => ?_)⟩
  refine congrArg₂ (· * ·) (congrArg _ ?_) rfl
  rw [map_mul]
  refine congrArg₂ (· * ·) ?_ rfl
  have := congrArg (fun t => t.appTop.hom (c i)) e₁
  refine Eq.trans this ?_
  exact congrArg (fst (TF (R := R') (FractionRing R')) D'.P.A).left.appTop.hom
    (Iso.hom_inv_id_apply (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R'))) (c i)).symm

theorem sum_f {F : Type} [Field F] [Algebra (FractionRing R) F] {k : ℕ} {N : Type} (S : Finset N)
    (t : N → Fam D F k) (α : D.X) (j) : ((∑ i ∈ S, t i).s α).f j = ∑ i ∈ S, ((t i).s α).f j :=
  map_sum (AddMonoidHom.mk' (fun s : Fam D F k => (s.s α).f j) (fun _ _ => rfl)) t S

end Concrete

open DVR in

theorem exists_span : PolBaseChangeSt → GlobalFnsSt → DVR.TwistBaseChangeStatement → ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (I : Ideal R), AdmBase R I → ∀ (φ : R →+* R') (D : DegData R I) (D' : DegPre R') (hD : IsPullDeg φ D.toPre D') (k : ℕ), 1 ≤ k → ∃ (n : ℕ) (F : Fin n → Fam D.toPre (FractionRing R) k) (f : Fin n → ∀ α, D.toPre.SecB k α) (F' : Fin n → Fam D' (FractionRing R') k) (f' : Fin n → ∀ α, D'.SecB k α), (∀ i, (∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) α) (DegPre.famε k) ((F i).s α) (D.toPre.famφB α) (DegPre.famε k) (f i α) (DegPre.prB D.toPre (FractionRing R)).left 1) ∧ (∀ α, GeneratorPullback.SecScal D'.P.L (DegPre.famφ D' (FractionRing R') α) (DegPre.famε k) ((F' i).s α) (D'.famφB α) (DegPre.famε k) (f' i α) (DegPre.prB D' (FractionRing R')).left 1) ∧ (∀ x : D'.X, (∀ (Z : Scheme.{0}) (r : Z ⟶ D'.P.A.left) (z : Z) (p : Fin 4 → D.toPre.P.L.ι) (q : Fin 4 → D'.P.L.ι), (∀ κ, ((hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ))) ((D'.famφB x) κ (r z)) ∈ D.toPre.P.L.U (p κ)) → (∀ κ, (D'.famφB x) κ (r z) ∈ D'.P.L.U (q κ)) → Geo.Tor.gs (r ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ))) z (LB.wchart D.toPre.P.L (D.toPre.famφB (hD.xe x)) p) ((f i (hD.xe x)).f p) = (∏ κ, Geo.Tor.gw hD.w (r ≫ (D'.famφB x) κ) z (p κ) (q κ) ^ (DegPre.famε k) κ).val * Geo.Tor.gs r z (LB.wchart D'.P.L (D'.famφB x) q) ((f' i x).f q)))) ∧ Submodule.span (FractionRing R') (Set.range F') = ⊤ := by
  intro hP hG hT R R' _ _ _ _ I hA φ D D' hD k hk
  classical
  have : IsNoetherianRing R := hA.1
  let pt : (TK R').left := genericPoint (Spec (CommRingCat.of (FractionRing R')))
  let P : Spec (CommRingCat.of R) := (jK R' ≫ specOf φ) pt
  have hPW : P ∈ hD.W := by
    show (jK R' ≫ specOf φ) pt ∈ hD.W
    rw [← hD.g_comm]
    exact (hD.g pt).2
  have hne : ∀ r : R, r ∉ P.asIdeal → algebraMap R' (FractionRing R') (φ r) ≠ 0 := fun r hr h => hr (by
    show algebraMap R' (FractionRing R') (φ r) ∈ PrimeSpectrum.asIdeal pt
    rw [h]; exact Ideal.zero_mem _)
  have hgen : genericPoint (Spec (CommRingCat.of R)) ∈ hD.W :=
    (genericPoint_specializes P).mem_open hD.W.isOpen hPW
  have := P.isPrime
  obtain ⟨-, e, he⟩ := exists_representatives_mod_nsmul D'.X k hk
  choose b hb using fun α => GlobalTheory.TwistLoc.exists_basis_off_prime hP hG hT R D.toPre ⟨hD.W, hgen, ⟨hD.psiW⟩⟩ P.asIdeal k hk α
  choose r hr F f hF hfρ hf0 using fun q : Fin (k ^ Module.finrank ℤ D'.X) × Fin (k ^ D.toPre.P.g) =>
    GlobalTheory.T.integralFamily_prescribedTerm_unit_at_prime hG R I hA D hD.W ⟨hD.psiW⟩ P hPW k hk (hD.xe (e q.1)) (b (hD.xe (e q.1)) q.2)
  choose f' hf' using fun q x => (SecPull.existsUnique_secPull _ _ _ _ D.toPre.P.L D'.P.L _ D.toPre.P.isLB D'.P.isLB
    hD.w hD.w_gen (Fin 4) (D'.famφB x) (D.toPre.famφB (hD.xe x)) (DegPre.famε k) _ (famφB_comm hD x)
    (f q (hD.xe x))).exists
  choose F' hF' using fun q => GlobalTheory.T.exists_fam_of_isPullDeg_alt hG R R' φ D.toPre D' hD k (F q) (f q) (f' q) (hF q) (hf' q)
  let en := (finProdFinEquiv (m := k ^ Module.finrank ℤ D'.X) (n := k ^ D.toPre.P.g)).symm
  refine ⟨_, fun i => F (en i), fun i => f (en i), fun i => F' (en i), fun i => f' (en i),
    fun i => ⟨hF _, hF' _, hf' _⟩, ?_⟩
  have hrange : Set.range (fun i => F' (en i)) = Set.range F' := en.surjective.range_comp F'
  rw [hrange, eq_top_iff]
  rintro s -
  choose c hc using fun i => span_term hD k (e i) (b (hD.xe (e i))) (fun l => f (i, l) (hD.xe (e i)))
    (hb _ _ _ (fun t ht => (hne t ht).isUnit) _ (fun _ _ => rfl)) (fun l => r (i, l)) (fun l => hne _ (hr (i, l)))
    (fun l => hfρ (i, l)) (fun l => f' (i, l) (e i))
    (fun l y J J' hJ hJ' => val_of_rel (famφB_comm hD (e i)) (hf' (i, l) (e i)) _ y hJ hJ')
    (fun l => (F' (i, l)).s (e i)) (fun l => hF' (i, l) (e i)) (s.s (e i))
  have hs : s = ∑ q : Fin (k ^ Module.finrank ℤ D'.X) × Fin (k ^ D.toPre.P.g), c q.1 q.2 • F' q := by
    refine fam_ext fun χ j => ?_
    obtain ⟨i, ⟨m, rfl⟩, -⟩ := he χ
    refine fam_eq_on_class_of_eq hG R' D' _ k s _ (e i) (fun j => ?_) m j
    rw [sum_f, Fintype.sum_prod_type, Finset.sum_eq_single i, hc i j]
    · rfl
    · intro i' _ hi
      refine Finset.sum_eq_zero fun l _ => ?_
      have h0 := zero_sec D.toPre.P.isLB D'.P.isLB (DegPre.prB D' (FractionRing R')).left (f (i', l) (hD.xe (e i)))
        (hf0 (i', l) _ fun mu hmu => hi ((he (e i)).unique ⟨hD.xe.symm mu, hD.xe.injective (by
          rw [map_add, map_nsmul, AddEquiv.apply_symm_apply]; exact hmu.symm)⟩ ⟨0, by rw [smul_zero, add_zero]⟩))
        (f' (i', l) (e i)) (fun y J J' hJ hJ' => val_of_rel (famφB_comm hD (e i)) (hf' (i', l) (e i)) _ y hJ hJ')
        ((F' (i', l)).s (e i)) (hF' (i', l) (e i)) j
      rw [smul_f, h0, mul_zero]
    · intro h; exact absurd (Finset.mem_univ i) h
  rw [hs]
  exact Submodule.sum_mem _ fun q _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨q, rfl⟩)

end GlobalTheory.FamSpan
