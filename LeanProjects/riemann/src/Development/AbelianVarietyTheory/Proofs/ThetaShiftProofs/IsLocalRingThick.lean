import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ToStkAInjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueSecPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpandsAtTransport
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ModelChartLiftCoordsGeneratorIndep
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueThetaOfStatement

set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.ArcQ.FrAgree

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR hiding gw
open Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ
open scoped CategoryTheory.Obj

section Local

variable {X Y Z : Scheme.{0}}

theorem exists_local (Z : Scheme.{0}) (z : Z) : ∃ (A : Type) (_ : CommRing A) (_ : IsLocalRing A) (i : Sp A ⟶ Z),
    i (cpt A) = z ∧ Function.Injective (i.stalkMap (cpt A)).hom := by
  refine ⟨Z.presheaf.stalk z, inferInstance, inferInstance, Z.fromSpecStalk z, Scheme.fromSpecStalk_closedPoint, ?_⟩
  have e := Scheme.stalkClosedPointTo_fromSpecStalk (X := Z) z
  have i : Function.Injective (Scheme.stalkClosedPointTo (Z.fromSpecStalk z)).hom := by
    rw [e]
    exact (Iso.commRingCatIsoToRingEquiv _).injective
  exact Function.Injective.of_comp (f := (stalkClosedPointIso (Z.presheaf.stalk z)).hom.hom) i

def stU (r : Z ⟶ Y) (z : Z) : (Y.presheaf.stalk (r z))ˣ →* (Z.presheaf.stalk z)ˣ :=
  Units.map (r.stalkMap z).hom.toMonoidHom

theorem stU_injective (r : Z ⟶ Y) (z : Z) (h : Function.Injective (r.stalkMap z).hom) :
    Function.Injective (stU r z) := Units.map_injective h

theorem gm_comp (r : Z ⟶ Y) (g : Y ⟶ X) (z : Z) (U : X.Opens) (a : Γ(X, U)ˣ) :
    stU r z (gm g (r z) U a) = gm (r ≫ g) z U a := by
  symm
  by_cases h : g (r z) ∈ U
  · refine Units.ext ((gs_unit (r ≫ g) z U h a).symm.trans (Eq.trans ?_
      (congrArg (r.stalkMap z).hom (gs_unit g (r z) U h a))))
    rw [← gs_pull r g z U h, gs_stalkMap r z _ h, gs_pull (𝟙 Y) g (r z) U h, Category.id_comp]
  · have h' : (r ≫ g) z ∉ U := h
    rw [gm, dif_neg h', gm, dif_neg h]
    exact (map_one _).symm

end Local

section Gen

variable {B B' B₀ Y Y' : Scheme.{0}} {M : LB B} {M' : LB B'} {M₀ : LB B₀} {K : Type} [Fintype K] {ε : K → ℤ}
  {Φ : B ⟶ B'} {φ' : B' ⟶ B₀} {w' : LB.Iso M' (M₀.pull φ')} {w₁ : LB.Iso M (M'.pull Φ)}
  {w : LB.Iso M (M₀.pull (Φ ≫ φ'))}

theorem pmaps_of_genRelR (T : Tri w' w₁ w) (hw : PGen w) (hM : M.IsLB) (hM₀ : M₀.IsLB) {ψ : K → (Y ⟶ B)}
    {ψ' : K → (Y' ⟶ B')} (h : Y ⟶ Y') (hc : ∀ k, ψ k ≫ Φ = h ≫ ψ' k) (t : LB.Gen (LB.LinComb M ψ ε)) (ht : t.IsGen)
    (t' : LB.Gen (LB.LinComb M' ψ' ε))
    (H : ∀ (A : Type) [CommRing A] [IsLocalRing A] (v : Sp A ⟶ Y) (pt₀ : K → (Sp A ⟶ B₀))
      (t₀ : LB.Gen (LB.LinComb M₀ pt₀ ε)), t₀.IsGen → GenRelR w (LB.pullGen _ _ _ t v) t₀ →
      GenRelR w' (LB.pullGen _ _ _ t' (v ≫ h)) t₀) : PMaps w₁ ψ ψ' ε t t' h := by
  intro Z r z p q hp hq
  obtain ⟨A, _, _, i, rfl, inj⟩ := exists_local Z z
  apply stU_injective i _ inj
  refine (gm_comp i _ _ _ _).trans (Eq.trans ?_ ((map_mul _ _ _).trans (congrArg₂ (· * ·) ((map_prod _ _ _).trans
    (Finset.prod_congr rfl fun k _ => (map_zpow _ _ _).trans (congrArg (· ^ ε k) (gm_comp i _ _ _ _))))
    (gm_comp i _ _ _ _))).symm)
  obtain ⟨t₀, g₀, hv⟩ := exists_up hw hM₀ hM (LB.pullGen _ _ _ t (i ≫ r)) (pullGen_isGen _ _ _ _ ht _)
  have G := (genRelR_iff _ _ _).1 (H A (i ≫ r) _ t₀ g₀ ((genRelR_iff _ _ _).2 ⟨fun _ => rfl, fun j j₀ h₀ h₁ => by
    have := hv _ (𝟙 _) (cpt A) j₀ j (Set.mem_iInter.2 h₀) (Set.mem_iInter.2 h₁)
    simp only [pw, Category.id_comp] at this
    exact congrArg Units.val this.symm⟩))
  choose j₀ hj₀ using fun k => exists_chart hM₀ (φ' (Φ (ψ k (r (i (cpt A))))))
  have pe := fun k => pt_eq hc k (r (i (cpt A)))
  have a := Units.ext (G.2 p j₀ (fun k => (congrArg (fun y => φ' y ∈ M₀.U (j₀ k)) (pe k)).mpr (hj₀ k))
    (fun k => (congrArg (fun y => y ∈ M'.U (p k)) (pe k)).mpr (hp k)))
  have b := hv _ (𝟙 _) (cpt A) j₀ q (Set.mem_iInter.2 hj₀) (Set.mem_iInter.2 hq)
  have c := T.prod (ε := ε) hc _ (i ≫ r) (cpt A) j₀ p q hj₀ hp hq
  rw [b, gm_pullGen', gm_pullGen'] at a
  simp only [pw, Category.id_comp] at a
  rw [c, _root_.mul_assoc] at a
  have := mul_left_cancel a
  simpa only [gw, Category.assoc] using this

end Gen

section Fam

variable {R R₀ : Type} [CommRing R] [IsDomain R] [CommRing R₀] [IsDomain R₀]

theorem famφB_push {D : DegPre R₀} {D' : DegPre R} {f : Sp R ⟶ Sp R₀} {Φ : D'.P.A.left ⟶ D.P.A.left}
    (gp : IsGrpPullback D'.P.A D.P.A f Φ) {x : D'.X} {x₀ : D.X} (hc : (D'.c x).left ≫ Φ = f ≫ (D.c x₀).left)
    (κ : Fin 4) : D'.famφB x κ ≫ Φ = Φ ≫ D.famφB x₀ κ := by
  let P := pushHom gp D'.P.A
  have h1 : (P (𝟙 _)).left = Φ := Category.id_comp _
  have h2 : P (cP D' _ x) = cP D _ x₀ := Over.OverMorphism.ext (by
    show (D'.P.A.hom ≫ (D'.c x).left) ≫ Φ = (D'.P.A.hom ≫ f) ≫ (D.c x₀).left
    rw [Category.assoc, Category.assoc]
    exact congrArg _ hc)
  have key : ∀ (a : D'.P.A ⟶ D'.P.A) (b : D.P.A ⟶ D.P.A), P a = P (𝟙 _) ≫ b → a.left ≫ Φ = Φ ≫ b.left :=
    fun a b e => (congrArg (fun q => q.left) e).trans (congrArg (· ≫ b.left) h1)
  fin_cases κ
  · exact (Category.id_comp _).trans (Category.comp_id _).symm
  · refine key (𝟙 _ * cP D' _ x) (𝟙 _ * cP D _ x₀) ?_
    rw [map_mul, MonObj.comp_mul, Category.comp_id, comp_cP, h2]
  · refine key (cP D' _ x) (cP D _ x₀) ?_
    rw [comp_cP, h2]
  · refine key 1 1 ?_
    rw [map_one, MonObj.comp_one]

theorem famφB_hom (D : DegPre R) (x : D.X) (κ : Fin 4) : D.famφB x κ ≫ D.P.A.hom = D.P.A.hom := by
  fin_cases κ
  exacts [Category.id_comp _, Over.w (𝟙 _ * cP D _ x), Over.w (cP D _ x), Over.w (1 : D.P.A ⟶ D.P.A)]

theorem Oφ_eq (D : DegPre R) {T : Over (Sp R)} (p : T ⟶ D.P.A) (x : D.X) (κ : Fin 4) :
    D.Oφ p x κ = p.left ≫ D.famφB x (![1, 2, 0, 3] κ) := by
  fin_cases κ
  · exact congrArg (fun z => z.left) ((MonObj.comp_mul p (𝟙 _) (cP D _ x)).trans
      (congrArg₂ (· * ·) (Category.comp_id _) (comp_cP D _ x))).symm
  · exact congrArg (fun z => z.left) (comp_cP D p x).symm
  · exact (Category.comp_id _).symm
  · exact congrArg (fun z : _ ⟶ D.P.A => z.left) (MonObj.comp_one (M := D.P.A) p).symm

end Fam

section Zero

variable {R : Type} [CommRing R] [IsDomain R] {B₀ : Scheme.{0}} {M₀ : LB B₀}

def ZeroTerm (D : DegPre R) {φ : D.P.A.left ⟶ B₀} (w : LB.Iso D.P.L (M₀.pull φ)) (th : M₀.Sec) (α : D.X)
    (s : D.SecB 1 α) : Prop :=
  ∀ (j : Fin 4 → D.P.L.ι) (j₀ : M₀.ι) (V : D.P.A.left.Opens) (h₁ : V ≤ LB.wchart D.P.L (D.famφB α) j)
    (h₂ : V ≤ (LB.div (M₀.pull φ) D.P.L).U (fun _ => j₀, j 1)) (h₃ : V ≤ φ ⁻¹ᵁ M₀.U j₀),
    LB.Coh D.P.L (D.famφB α) j →
    (φ.appLE _ _ h₃).hom (th.f j₀) = resG _ h₂ (w.s (fun _ => j₀, j 1)).val * resG _ h₁ (s.f j)

theorem zeroTerm_iff (D : DegPre R) {φ : D.P.A.left ⟶ B₀} (w : LB.Iso D.P.L (M₀.pull φ)) (th : M₀.Sec) (α : D.X)
    (s : D.SecB 1 α) : ZeroTerm D w th α s ↔ ∀ (Z : Scheme.{0}) (r : Z ⟶ D.P.A.left) (z : Z) (j : Fin 4 → D.P.L.ι)
      (j₀ : M₀.ι), LB.Coh D.P.L (D.famφB α) j → r z ∈ LB.wchart D.P.L (D.famφB α) j → φ (r z) ∈ M₀.U j₀ →
      r z ∈ D.P.L.U (j 1) → gs (r ≫ φ) z _ (th.f j₀) =
        (gw w r z j₀ (j 1)).val * gs r z (LB.wchart D.P.L (D.famφB α) j) (s.f j) := by
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ D.P.A.left) (z : Z) (j : Fin 4 → D.P.L.ι) (j₀ : M₀.ι)
      (V : D.P.A.left.Opens) (h₁ : V ≤ LB.wchart D.P.L (D.famφB α) j)
      (h₂ : V ≤ (LB.div (M₀.pull φ) D.P.L).U (fun _ => j₀, j 1)), r z ∈ V →
      gs r z V (resG _ h₂ (w.s (fun _ => j₀, j 1)).val * resG _ h₁ (s.f j)) =
        (gw w r z j₀ (j 1)).val * gs r z (LB.wchart D.P.L (D.famφB α) j) (s.f j) :=
    fun Z r z j j₀ V h₁ h₂ hz => (gs_mul r z V hz _ _).trans (congrArg₂ (· * ·)
      ((gs_res r z h₂ hz _).trans (gs_unit r z _ (h₂ hz) _)) (gs_res r z h₁ hz _))
  constructor
  · intro H Z r z j j₀ hc h₁ h₃ h₂
    have hz : r z ∈ LB.wchart D.P.L (D.famφB α) j ⊓ (LB.div (M₀.pull φ) D.P.L).U (fun _ => j₀, j 1) ⊓
        φ ⁻¹ᵁ M₀.U j₀ := ⟨⟨h₁, mem_pull.2 h₃, h₂⟩, h₃⟩
    exact (gs_appLE φ _ _ inf_le_right r z hz _).symm.trans ((congrArg (gs r z _) (H j j₀ _
      (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right) inf_le_right hc)).trans (key Z r z j j₀ _ _ _ hz))
  · intro H j j₀ V h₁ h₂ h₃ hc
    exact fn_ext fun y hy => (gs_appLE φ _ _ h₃ (𝟙 _) y hy _).trans
      ((H _ (𝟙 _) y j j₀ hc (h₁ hy) (h₃ hy) (h₂ hy).2).trans (key _ (𝟙 _) y j j₀ V h₁ h₂ hy).symm)

theorem famφB_one (D : DegPre R) {α : D.X} (h : α = 0) : D.famφB α 1 = 𝟙 _ := by
  subst h
  exact congrArg (fun z : D.P.A ⟶ D.P.A => z.left) (show 𝟙 _ * cP D _ 0 = 𝟙 _ by rw [cPoint_zero, _root_.mul_one])

theorem famφB_two (D : DegPre R) {α : D.X} (h : α = 0) : D.famφB α 2 = D.famφB α 3 := by
  subst h
  exact congrArg (fun z : D.P.A ⟶ D.P.A => z.left) (cPoint_zero _)

theorem zeroTerm_move {D D' : DegPre R} {Φ : D.P.A.left ⟶ D'.P.A.left} {φ' : D'.P.A.left ⟶ B₀}
    {w' : LB.Iso D'.P.L (M₀.pull φ')} {w₁ : LB.Iso D.P.L (D'.P.L.pull Φ)} {w : LB.Iso D.P.L (M₀.pull (Φ ≫ φ'))}
    (T : Tri w' w₁ w) (th : M₀.Sec) {α' : D'.X} (h0 : α' = 0) (hφ : ∀ κ, D.famφB 0 κ ≫ Φ = Φ ≫ D'.famφB α' κ)
    (s : D.SecB 1 0) (s' : D'.SecB 1 α')
    (hs : ∀ (Z : Scheme.{0}) (r : Z ⟶ D.P.A.left) (z : Z) (p : Fin 4 → D'.P.L.ι) (q : Fin 4 → D.P.L.ι),
      (∀ κ, Φ (D.famφB 0 κ (r z)) ∈ D'.P.L.U (p κ)) → (∀ κ, D.famφB 0 κ (r z) ∈ D.P.L.U (q κ)) →
      gs (r ≫ Φ) z (LB.wchart D'.P.L (D'.famφB α') p) (s'.f p) =
        (∏ κ, gw w₁ (r ≫ D.famφB 0 κ) z (p κ) (q κ) ^ DegPre.famε 1 κ).val *
          gs r z (LB.wchart D.P.L (D.famφB 0) q) (s.f q))
    (H : ZeroTerm D' w' th α' s') : ZeroTerm D w th 0 s := by
  refine (zeroTerm_iff D w th 0 s).2 fun Z r z j j₀ hc h₁ h₃ h₂ => ?_
  choose J hJ using fun ψ : D'.P.A.left ⟶ D'.P.A.left => exists_chart D'.P.isLB (ψ (Φ (r z)))
  have m₁ : Φ (r z) ∈ D'.P.L.U (J (D'.famφB α' 1)) := by
    rw [famφB_one D' h0]; exact hJ (𝟙 _)
  have a := (zeroTerm_iff D' w' th α' s').1 H Z (r ≫ Φ) z (fun κ => J (D'.famφB α' κ)) j₀
    (fun a b e => congrArg J e) (Set.mem_iInter.2 fun κ => hJ _) h₃ m₁
  have b := hs Z r z (fun κ => J (D'.famφB α' κ)) j (fun κ =>
    (congrArg (fun q => q (r z) ∈ D'.P.L.U (J (D'.famφB α' κ))) (hφ κ)).mpr (hJ _)) (Set.mem_iInter.1 h₁)
  have c : ∏ κ, gw w₁ (r ≫ D.famφB 0 κ) z (J (D'.famφB α' κ)) (j κ) ^ DegPre.famε 1 κ =
      gw w₁ r z (J (D'.famφB α' 1)) (j 1) := by
    rw [Fin.prod_univ_four, famφB_one D rfl, Category.comp_id, hc 2 3 (famφB_two D rfl), famφB_two D rfl,
      famφB_two D' h0]
    show _ ^ (((1 : ℕ) : ℤ) - 1) * _ ^ (1 : ℤ) * _ ^ (-1 : ℤ) * _ ^ (1 : ℤ) = _
    simp
  rw [← Category.assoc, a, b, c, T Z r z j₀ _ _ h₃ m₁ h₂, Units.val_mul, _root_.mul_assoc]

end Zero

section Move

variable {R R₀ : Type} [CommRing R] [IsDomain R] [CommRing R₀] [IsDomain R₀] {I : Ideal R} {D D' : DegData R I}
  {A A' : PolAV (Sp (FractionRing R))} {G G' : Over (Sp R)} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']

set_option maxHeartbeats 1600000 in

theorem theta_move (U : UnifPre I D A G) (U' : UnifPre I D' A' G') {D₀ : DegPre R₀} {f : Sp R ⟶ Sp R₀}
    {φ : D.toPre.P.A.left ⟶ D₀.P.A.left} {φ' : D'.toPre.P.A.left ⟶ D₀.P.A.left}
    (gp : IsGrpPullback D.toPre.P.A D₀.P.A f φ) (gp' : IsGrpPullback D'.toPre.P.A D₀.P.A f φ')
    (w : LB.Iso D.toPre.P.L (D₀.P.L.pull φ)) (w' : LB.Iso D'.toPre.P.L (D₀.P.L.pull φ')) (hw : w.IsGen) (hw' : w'.IsGen)
    (e : D₀.X ≃+ D.toPre.X) (e' : D₀.X ≃+ D'.toPre.X)
    (hc : ∀ y, (D.toPre.c (e y)).left ≫ φ = f ≫ (D₀.c y).left)
    (hc' : ∀ y, (D'.toPre.c (e' y)).left ≫ φ' = f ≫ (D₀.c y).left) (ψ : G ⟶ G')
    (wL : LB.Iso U.LG.L (U'.LG.L.pull ψ.left)) (hwL : wL.IsGen)
    (hlev : ∀ (n : ℕ) (ψn : (thickObj R I n G).left ⟶ (thickObj R I n G').left),
      ψn = ((Over.pullback (thick R I n)).map ψ).left →
      ((U.gt n).pG.left ≫ φ = ψn ≫ (U'.gt n).pG.left ≫ φ') ∧
      ∀ (A : Type) [CommRing A] [IsLocalRing A] (v : Sp A ⟶ (thickObj R I n G).left),
        (∀ (x : D₀.X) (pt₀ : Fin 4 → (Sp A ⟶ D₀.P.A.left)) (t₀ : LB.Gen (LB.LinComb D₀.P.L pt₀ Oinvε)),
          t₀.IsGen → GenRelR w (LB.pullGen _ _ _ ((U.gt n).t (e x)) v) t₀ →
          GenRelR w' (LB.pullGen _ _ _ ((U'.gt n).t (e' x)) (v ≫ ψn)) t₀) ∧
        ∀ (j₀ : D₀.P.L.ι) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι),
          ⊤ ≤ (v ≫ (U.gt n).pG.left) ⁻¹ᵁ (LB.div (D₀.P.L.pull φ) D.toPre.P.L).U (fun _ => j₀, jM) →
          ⊤ ≤ (v ≫ ψn ≫ (U'.gt n).pG.left) ⁻¹ᵁ (LB.div (D₀.P.L.pull φ') D'.toPre.P.L).U (fun _ => j₀, jM') →
          ⊤ ≤ (v ≫ (fstG I n G).left) ⁻¹ᵁ (LB.div (U'.LG.L.pull ψ.left) U.LG.L).U (fun _ => jL', jL) →
          valR (v ≫ (U.gt n).pG.left) _ (w.s (fun _ => j₀, jM)).val *
              valR v _ ((U.w n).s (fun _ => jM, fun _ => jL)).val =
            valR (v ≫ ψn ≫ (U'.gt n).pG.left) _ (w'.s (fun _ => j₀, jM')).val *
              valR (v ≫ ψn) _ ((U'.w n).s (fun _ => jM', fun _ => jL')).val *
              valR (v ≫ (fstG I n G).left) _ (wL.s (fun _ => jL', jL)).val)
    (th : D₀.P.L.Sec) (σ' : H0 U'.LG.L 1) (fam' : ∀ x, D'.toPre.SecB 1 x) (θ' : LB.Sec U'.LG.L)
    (hE : ∀ n, U'.ExpandsAt n 1 σ' fam') (h0 : ZeroTerm D'.toPre w' th 0 (fam' 0)) (hσ : SectionOfLineBundleOne σ' θ') :
    ∃ (σ : H0 U.LG.L 1) (fam : ∀ x, D.toPre.SecB 1 x) (θ : LB.Sec U.LG.L), (∀ n, U.ExpandsAt n 1 σ fam) ∧
      ZeroTerm D.toPre w th 0 (fam 0) ∧ SectionOfLineBundleOne σ θ ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) j k, ψ.left (r z) ∈ U'.LG.L.U j → r z ∈ U.LG.L.U k →
        gs (r ≫ ψ.left) z _ (θ'.f j) = (gw wL r z j k).val * gs r z _ (θ.f k) := by
  have hM := D.toPre.P.isLB
  have hM' := D'.toPre.P.isLB
  have hM₀ := D₀.P.isLB
  obtain ⟨Φ, rfl, hΦ⟩ : ∃ Φ : D.toPre.P.A.left ⟶ D'.toPre.P.A.left, Φ ≫ φ' = φ ∧
      Φ ≫ D'.toPre.P.A.hom = D.toPre.P.A.hom := ⟨gp'.1.lift _ _ gp.1.w, gp'.1.lift_fst _ _ _, gp'.1.lift_snd _ _ _⟩
  have pw := (isGen_iff w).1 hw
  have pw' := (isGen_iff w').1 hw'
  obtain ⟨w₁, T⟩ := exists_cancel hM₀ w' w pw' pw hM' hM
  have hw₁ := (isGen_iff w₁).2 (T.pgen_cancel hM₀ pw' pw)
  let xe : D.toPre.X ≃+ D'.toPre.X := e.symm.trans e'
  have hφ : ∀ x κ, D.toPre.famφB x κ ≫ Φ = Φ ≫ D'.toPre.famφB (xe x) κ := fun x κ => by
    obtain ⟨x₀, rfl⟩ := e.surjective x
    have ex : xe (e x₀) = e' x₀ := congrArg e' (e.symm_apply_apply x₀)
    rw [ex]
    apply gp'.1.hom_ext
    · rw [Category.assoc, Category.assoc, famφB_push gp (hc x₀), famφB_push gp' (hc' x₀), Category.assoc]
    · rw [Category.assoc, Category.assoc, famφB_hom, hΦ, famφB_hom]
  obtain ⟨σ, hσ₁, -⟩ := SecPull.existsUnique_secPull _ _ _ _ _ _ _ U'.LG.isLB U.LG.isLB wL hwL (Fin 1)
    (fun _ => 𝟙 G.left) (fun _ => 𝟙 G'.left) (fun _ => ((1 : ℕ) : ℤ)) ψ.left
    (fun _ => (Category.id_comp _).trans (Category.comp_id _).symm) σ'
  choose fam hfam using fun x => (SecPull.existsUnique_secPull _ _ _ _ _ _ _ hM' hM w₁ hw₁ (Fin 4)
    (D.toPre.famφB x) (D'.toPre.famφB (xe x)) (DegPre.famε 1) Φ (hφ x) (fam' (xe x))).exists
  obtain ⟨θ, hθ⟩ := sec_pull_down ((isGen_iff wL).1 hwL) U'.LG.isLB U.LG.isLB θ'
  refine ⟨σ, fam, θ, fun n => ?_, ?_, fun j hj => fn_ext fun y hy => ?_, hθ⟩
  · obtain ⟨h, hh⟩ : ∃ h : (thickObj R I n G).left ⟶ (thickObj R I n G').left,
        h = ((Over.pullback (thick R I n)).map ψ).left := ⟨_, rfl⟩
    obtain ⟨l₁, l₂⟩ := hlev n h hh
    have hG : h ≫ (fstG I n G').left = (fstG I n G).left ≫ ψ.left := by
      rw [hh]; exact pullback.lift_fst _ _ _
    have hq : (U.gt n).pG.left ≫ Φ = h ≫ (U'.gt n).pG.left := by
      apply gp'.1.hom_ext
      · rw [Category.assoc, Category.assoc]; exact l₁
      · rw [Category.assoc, Category.assoc, hΦ, Over.w (U.gt n).pG, Over.w (U'.gt n).pG, ← Over.w (fstG I n G'),
          ← Over.w (fstG I n G), ← Over.w ψ, ← Category.assoc, ← hG, Category.assoc]
    have hO : ∀ x κ, D.toPre.Oφ (U.gt n).pG x κ ≫ Φ = h ≫ D'.toPre.Oφ (U'.gt n).pG (xe x) κ := fun x κ => by
      rw [Oφ_eq, Oφ_eq, Category.assoc, hφ, ← Category.assoc, hq, Category.assoc]
    refine expandsAt_transport R R I I D' D A' A G' G U' U Φ w₁ xe ψ.left wL hw₁ hwL hφ n n 1 h
      ⟨hG, ⟨hq, fun x => ⟨hO x, ?_⟩⟩, ?_⟩ σ' σ fam' fam hσ₁ hfam (hE n)
    · refine pmaps_of_genRelR T pw hM hM₀ h (hO x) _ ((U.gt n).t_gen x) _ fun A _ _ v pt₀ t₀ g₀ => ?_
      obtain ⟨x₀, rfl⟩ := e.surjective x
      have ex : xe (e x₀) = e' x₀ := congrArg e' (e.symm_apply_apply x₀)
      rw [ex]
      exact (l₂ A v).1 x₀ pt₀ t₀ g₀
    · intro Z r z jM' jM jL' jL m₁ m₂ m₃ m₄
      obtain ⟨A, _, _, i, rfl, inj⟩ := exists_local Z z
      apply stU_injective i _ inj
      refine ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_comp i _ _ _ _) (gm_comp i _ _ _ _))).trans (Eq.trans ?_
        ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_comp i _ _ _ _) (gm_comp i _ _ _ _))).symm)
      obtain ⟨j₀, m₀⟩ := exists_chart hM₀ (φ' (Φ ((U.gt n).pG.left (r (i (cpt A))))))
      have eq : (U'.gt n).pG.left (h (r (i (cpt A)))) = Φ ((U.gt n).pG.left (r (i (cpt A)))) :=
        congrArg (fun q => q (r (i (cpt A)))) hq.symm
      have eG : (fstG I n G').left (h (r (i (cpt A)))) = ψ.left ((fstG I n G).left (r (i (cpt A)))) :=
        congrArg (fun q => q (r (i (cpt A)))) hG
      have m₁' := eq ▸ m₁
      have m₀' := eq ▸ m₀
      have m₃' := eG ▸ m₃
      have H1 := (top_le_iff_cpt ((i ≫ r) ≫ (U.gt n).pG.left)
        ((LB.div (D₀.P.L.pull (Φ ≫ φ')) D.toPre.P.L).U (fun _ => j₀, jM))).2 ⟨mem_pull₂.2 m₀, m₂⟩
      have H2 := (top_le_iff_cpt ((i ≫ r) ≫ h ≫ (U'.gt n).pG.left)
        ((LB.div (D₀.P.L.pull φ') D'.toPre.P.L).U (fun _ => j₀, jM'))).2 ⟨mem_pull.2 m₀', m₁'⟩
      have H3 := (top_le_iff_cpt ((i ≫ r) ≫ (fstG I n G).left)
        ((LB.div (U'.LG.L.pull ψ.left) U.LG.L).U (fun _ => jL', jL))).2 ⟨mem_pull.2 m₃, m₄⟩
      have H4 := (top_le_iff_cpt (i ≫ r) ((LB.div (D.toPre.P.L.pull (U.gt n).pG.left)
        (U.LG.L.pull (fstG I n G).left)).U (fun _ => jM, fun _ => jL))).2 ⟨mem_pull.2 m₂, mem_pull.2 m₄⟩
      have H5 := (top_le_iff_cpt ((i ≫ r) ≫ h) ((LB.div (D'.toPre.P.L.pull (U'.gt n).pG.left)
        (U'.LG.L.pull (fstG I n G').left)).U (fun _ => jM', fun _ => jL'))).2 ⟨mem_pull.2 m₁', mem_pull.2 m₃'⟩
      have a := congrArg (toStkA (cpt A)) ((l₂ A (i ≫ r)).2 j₀ jM jM' jL jL' H1 H2 H3)
      rw [map_mul, map_mul, map_mul, toStkA_valR _ _ _ H1, toStkA_valR _ _ _ H2, toStkA_valR _ _ _ H3,
        toStkA_valR _ _ _ H4, toStkA_valR _ _ _ H5, ← Units.val_mul, ← Units.val_mul, ← Units.val_mul] at a
      have b := T _ ((i ≫ r) ≫ (U.gt n).pG.left) (cpt A) j₀ jM' jM m₀ m₁ m₂
      rw [Category.assoc (i ≫ r), hq] at b
      have c := (congrArg (· * _) b).symm.trans (Units.ext a)
      rw [_root_.mul_assoc, _root_.mul_assoc] at c
      have d := mul_left_cancel c
      simp only [Category.assoc] at d
      exact d
  · exact zeroTerm_move T th (map_zero xe) (hφ 0) _ _ (hfam 0)
      ((show ∀ α, α = 0 → ZeroTerm D'.toPre w' th α (fam' α) by rintro _ rfl; exact h0) _ (map_zero xe))
  · obtain ⟨p, hp⟩ := exists_chart U'.LG.isLB (ψ.left y)
    have le : LB.wchart U'.LG.L (fun _ : Fin 1 => 𝟙 G'.left) (fun _ => p) ≤ U'.LG.L.U p := LB.wchart_le _ _ _ 0
    have a := hσ₁ _ (𝟙 _) y (fun _ => p) j (fun _ => hp) (Set.mem_iInter.1 hy)
    rw [hσ _ le, gs_res (𝟙 _ ≫ ψ.left) y le (Set.mem_iInter.2 fun _ => hp), hθ _ (𝟙 _) y p (j 0) hp (hj hy), Fin.prod_univ_one,
      Category.comp_id, zpow_natCast, pow_one] at a
    exact ((Units.mul_right_inj _).1 a).symm.trans (gs_res (𝟙 _) y hj hy _).symm

end Move

theorem cast_rig {S : Scheme.{0}} {G G' : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
    {L₁ L₂ : RigLB G} (h : L₁ = L₂) {L₁' L₂' : RigLB G'} (h' : L₁' = L₂') {F : G.left ⟶ G'.left}
    (he : eSec G ≫ F = 𝟙 _ ≫ eSec G') (w : LB.Iso L₁.L (L₁'.L.pull F)) (g : w.IsGen)
    (m : LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec G) (fun _ => 1)) L₁.rig
      (rigPullOf F (𝟙 _) he L₁'.L L₁'.rig)) (θ₁ : LB.Sec L₁.L) {θ₁' : LB.Sec L₁'.L} {θ₂' : LB.Sec L₂'.L}
    (hθ : HEq θ₂' θ₁')
    (H : ∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) j k, F (r z) ∈ L₁'.L.U j → r z ∈ L₁.L.U k →
      gs (r ≫ F) z _ (θ₁'.f j) = (gw w r z j k).val * gs r z _ (θ₁.f k)) :
    ∃ (w₂ : LB.Iso L₂.L (L₂'.L.pull F)) (θ₂ : LB.Sec L₂.L), w₂.IsGen ∧
      LB.Gen.Maps (LB.linCombIso w₂ (K := PUnit) (fun _ => eSec G) (fun _ => 1)) L₂.rig
        (rigPullOf F (𝟙 _) he L₂'.L L₂'.rig) ∧ HEq θ₂ θ₁ ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) j k, F (r z) ∈ L₂'.L.U j → r z ∈ L₂.L.U k →
        gs (r ≫ F) z _ (θ₂'.f j) = (gw w₂ r z j k).val * gs r z _ (θ₂.f k) := by
  subst h h'
  cases hθ
  exact ⟨w, θ₁, g, m, HEq.rfl, H⟩

theorem isoMaps_iff {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} (w : LB.Iso L' (L.pull F))
    (σ : LB.Sec L') (s : LB.Sec (L.pull F)) :
    IsoMaps w σ s ↔ ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) (j : L.ι) (k : L'.ι), F (r z) ∈ L.U j → r z ∈ L'.U k →
      gs r z _ (s.f (fun _ => j)) = (gw w r z j k).val * gs r z _ (σ.f k) := by
  constructor
  · intro h Z r z j k hj hk
    have hz : r z ∈ (L.pull F).U (fun _ => j) ⊓ L'.U k := ⟨mem_pull.2 hj, hk⟩
    have a := congrArg (gs r z _) (h (fun _ => j) k)
    exact (gs_res _ z _ hz _).symm.trans (a.trans ((gs_mul _ z _ hz _ _).trans
        (congrArg₂ (· * ·) (gs_unit _ z _ hz _) (gs_res _ z _ hz _))))
  · intro h (i : PUnit → L.ι) k
    exact fn_ext fun p hp =>
      (gs_res _ p _ hp _).trans ((h _ (𝟙 _) p (i PUnit.unit) k (mem_pull.1 hp.1) hp.2).trans
        (Eq.symm ((gs_mul _ p _ hp _ _).trans (congrArg₂ (· * ·) (gs_unit (𝟙 _) p _ hp _) (gs_res _ p _ hp _)))))

theorem isLocalRing_dual (R : Type) [CommRing R] [IsLocalRing R] : IsLocalRing (DualNumber R) :=
  have : Nontrivial (DualNumber R) := (TrivSqZeroExt.inl_injective (R := R) (M := R)).nontrivial
  IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => by
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.isUnit_iff_isUnit_fst]
    simpa using IsLocalRing.isUnit_or_isUnit_one_sub_self x.fst

theorem isLocalRing_thick (k : Type) [Field k] (n : ℕ) :
    IsLocalRing (DualNumber (PowerSeries k ⧸ Ideal.span {(PowerSeries.X : PowerSeries k)} ^ (n + 1))) := by
  have : Nontrivial (PowerSeries k ⧸ Ideal.span {(PowerSeries.X : PowerSeries k)} ^ (n + 1)) :=
    Ideal.Quotient.nontrivial_iff.2 fun e => by
      rw [Ideal.pow_eq_top_iff, Ideal.span_singleton_eq_top] at e
      exact e.elim PowerSeries.X_prime.not_unit (Nat.succ_ne_zero n)
  have : IsLocalRing (PowerSeries k ⧸ Ideal.span {(PowerSeries.X : PowerSeries k)} ^ (n + 1)) :=
    IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
  exact isLocalRing_dual _

theorem exists_factor {k S : Type} [Field k] [CommRing S] (io : PowerSeries k →+* S) (h : IsUnit (io PowerSeries.X)) :
    ∃ io' : FractionRing (PowerSeries k) →+* S, spMap io = spMap io' ≫ jK (PowerSeries k) := by
  have hu : ∀ y : nonZeroDivisors (PowerSeries k), IsUnit (io y) := fun y => by
    have hy : (y : PowerSeries k) ≠ 0 := nonZeroDivisors.ne_zero y.2
    rw [← PowerSeries.X_pow_order_mul_divXPowOrder (f := (y : PowerSeries k)), map_mul, map_pow]
    exact (h.pow _).mul ((PowerSeries.isUnit_divided_by_X_pow_order hy).map io)
  refine ⟨IsLocalization.lift hu, ?_⟩
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, IsLocalization.lift_comp]

section ThetaShiftProofs

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {k : Type} [Field k] {bF : c.F →+* k} {a : ArcIn Dw l (RingHom.id c.F) k bF}
  {O O' : Type} [CommRing O] [CommRing O'] {β : O →+* c.F} {β' : O' →+* c.F} {Y : Model Xo c β} {Y' : Model Xo c β'}
  {χ : Sp (PowerSeries k) ⟶ Y.X} {χ' : Sp (PowerSeries k) ⟶ Y'.X} {W : Wit Y (a.restrict β) χ}
  {W' : Wit Y' (a.restrict β') χ'} {ψ : W.t.G ≅ W'.t.G}

theorem lieImg_move (hA : W.Agree W' ψ) (ν : GtPt a.D₀ (epsR k)) (v : epsR (PowerSeries k) ⟶ W.t.G)
    (h : LieImg W ν v) : LieImg W' ν (v ≫ ψ.hom) := by
  obtain ⟨-, -, -, he, wL, -, -, hlev⟩ := hA
  intro n ρ κ vn h₁ h₂ h₃ h₄ hb hf x
  have := isLocalRing_thick k n
  let ψn := (Over.pullback (thick (PowerSeries k) (Ideal.span {PowerSeries.X}) n)).mapIso ψ
  have e₁ : (vn ≫ ψn.inv.left) ≫ ψn.hom.left = vn := by
    rw [Category.assoc, ← Over.comp_left, Iso.inv_hom_id, Over.id_left, Category.comp_id]
  have e₂ : ψn.inv.left ≫ (fstG (Ideal.span {PowerSeries.X}) n W.t.G).left =
      (fstG (Ideal.span {PowerSeries.X}) n W'.t.G).left ≫ ψ.inv.left := pullback.lift_fst _ _ _
  have a := h n ρ κ (vn ≫ ψn.inv.left) h₁ h₂ h₃ h₄ (by rw [Category.assoc, Over.w ψn.inv]; exact hb) (by
    rw [Category.assoc, e₂, ← Category.assoc, hf, Category.assoc, ← Over.comp_left, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]) x
  have b := ((hlev n ψn.hom.left rfl).2 _ (vn ≫ ψn.inv.left)).1 x _ (LB.pullGen _ _ _ (ν.s x) (spMap κ))
    (pullGen_isGen _ _ _ _ (ν.isGen x) _) a
  rw [e₁] at b
  exact b

theorem thetaOf_move (hA : W.Agree W' ψ) (th : a.D₀.P.L.Sec) (θ' : LB.Sec W'.t.PP.L) (h : ThetaOf W' th θ') :
    ∃ (he : eSec W.t.G ≫ ψ.hom.left = 𝟙 _ ≫ eSec W'.t.G) (w : LB.Iso W.t.PP.L (W'.t.PP.L.pull ψ.hom.left))
      (θ : LB.Sec W.t.PP.L), w.IsGen ∧
      LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec W.t.G) (fun _ => 1)) W.t.PP.rig
        (rigPullOf ψ.hom.left (𝟙 _) he W'.t.PP.L W'.t.PP.rig) ∧ ThetaOf W th θ ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ W.t.G.left) (z : Z) j k, ψ.hom.left (r z) ∈ W'.t.PP.L.U j → r z ∈ W.t.PP.L.U k →
        gs (r ≫ ψ.hom.left) z _ (θ'.f j) = (gw w r z j k).val * gs r z _ (θ.f k) := by
  obtain ⟨-, -, -, he, wL, g, m, hlev⟩ := hA
  obtain ⟨σ', fam', θ₁', hE, h0, hσ, hθ⟩ := h
  obtain ⟨σ, fam, θ₁, hE₁, h0₁, hσ₁, H⟩ := theta_move W.P.U.toUnifPre W'.P.U.toUnifPre W.spec.1 W'.spec.1 W.w W'.w
    W.spec.2.1 W'.spec.2.1 W.e.toAddEquiv W'.e.toAddEquiv W.spec.2.2.2.2.1 W'.spec.2.2.2.2.1 ψ.hom wL g hlev th σ' fam'
    θ₁' hE h0 hσ
  obtain ⟨w, θ, g₂, m₂, hθ₂, H₂⟩ := cast_rig W.P.bundle W'.P.bundle he wL g m θ₁ hθ H
  exact ⟨he, w, θ, g₂, m₂, ⟨σ, fam, θ₁, hE₁, h0₁, hσ₁, hθ₂⟩, H₂⟩

theorem isArcFr_move (hA : W.Agree W' ψ) (y₀ : Sp (FractionRing (PowerSeries k)) ⟶ Xo.XF c)
    (hy : y₀ ≫ Y.j = jK (PowerSeries k) ≫ χ) (hy' : y₀ ≫ Y'.j = jK (PowerSeries k) ≫ χ') (hj : Mono Y.j)
    (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → GtPt a.D₀ (epsR k)) (th : a.D₀.P.L.Sec)
    (hu : ∀ θ₁ θ₂, ThetaOf W th θ₁ → ThetaOf W th θ₂ → θ₁ = θ₂) (θ' : LB.Sec W'.t.PP.L) (hθ' : ThetaOf W' th θ')
    {S : Type} [CommRing S] [Algebra c.F S] (io : PowerSeries k →+* S) (y : FrPt Xo c S)
    (hio : IsUnit (io PowerSeries.X)) (h : IsArcFr W e th io y) : IsArcFr W' e th io y := by
  obtain ⟨z, t', m1, m2, φ, zj, zx, φb, φ1, φ2, hv, θ, w1, w2, σ, s1, θ2, hth, r1, r2, i1, i2, p2, hg⟩ := h
  obtain ⟨he, w, θ₁, g, m, hθ₁, Hθ⟩ := thetaOf_move hA th θ' hθ'
  obtain rfl : θ = θ₁ := hu _ _ hth hθ₁
  have hmon := hA.1
  obtain ⟨io', hio'⟩ := exists_factor io hio
  have zj' : z ≫ Y'.j = spMap io ≫ χ' := by
    have : z = spMap io' ≫ y₀ := by
      rw [← cancel_mono Y.j, zj, hio', Category.assoc, Category.assoc, hy]
    rw [this, hio', Category.assoc, Category.assoc, hy']
  obtain ⟨n₁, e₁⟩ : ∃ n₁ : SABMap t' Y'.oF.t z, m1.φ = n₁.φ ≫ Y'.m0.toSABMap.φ := by
    refine (show ∀ (x : Sp S ⟶ Xo.X) (m : SABMap t' Xo.univ.t x), z ≫ pullback.fst _ _ = x →
      ∃ n₁ : SABMap t' Y'.oF.t z, m.φ = n₁.φ ≫ Y'.m0.toSABMap.φ from ?_) _ m1 zx
    rintro _ m rfl
    exact sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ Y'.m0.toSABMap m
  obtain ⟨n₂, e₂⟩ : ∃ n₂ : SABMap t' Y'.t (spMap io ≫ χ'), n₂.φ = n₁.φ ≫ Y'.m.φ := by
    rw [← zj']
    exact sabComp pullCubComp E H _ _ _ _ _ _ _ _ Y'.m n₁
  obtain ⟨m2', e₃⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ W'.m n₂
  have e₄ : m2'.φ = m2.φ ≫ ψ.hom.left := by
    apply W'.m.cart.1.hom_ext
    · rw [Category.assoc]
      exact e₃.symm.trans (e₂.trans (hA.2.2.1 _ m2.φ φ n₁.φ φ2.symm (φ1.trans e₁)
        (φb.trans n₁.cart.1.w.symm)).symm)
    · rw [Category.assoc, Over.w ψ.hom]
      exact m2'.cart.1.w.trans m2.cart.1.w.symm
  obtain ⟨w2', r2', T⟩ := GlobalTheory.Reg.LiftUnique.cube_rig_comp (CubeMap.ofHom ψ.hom) m2.cm m2'.cm e₄
    (by rw [m2'.base, m2.base]; exact (Category.comp_id _).symm) _ _ _ w w2 ⟨g, m⟩ r2
  refine ⟨z, t', m1, m2', n₁.φ, zj', zx, n₁.cart.1.w, e₁.symm, e₂.symm.trans e₃, fun τ i => ?_,
    θ', w1, w2', σ, s1, thfPull _ m2'.φ θ', hθ', r1, r2', i1, ?_, fun _ _ => rfl, hg⟩
  · obtain ⟨v, u', a₁, a₂, a₃, a₄⟩ := hv τ i
    refine ⟨v ≫ ψ.hom, u', lieImg_move hA _ v a₁, a₂, ?_, a₄⟩
    rw [e₄, ← Category.assoc, a₃, Category.assoc, Over.comp_left]
  · refine (isoMaps_iff w2' σ _).2 fun Z r z j i hj hi =>
      (gs_appLE m2'.φ _ _ _ r z (mem_pull.2 hj) _).trans ?_
    obtain ⟨q, hq⟩ := exists_chart W.t.PP.isLB (m2.φ (r z))
    have le : (W.t.PP.L.pull m2.φ).U (fun _ => q) ≤ m2.φ ⁻¹ᵁ W.t.PP.L.U q := fun _ hx => mem_pull.1 hx
    have b := (isoMaps_iff w2 σ θ2).1 i2 Z r z q i hq hi
    rw [p2 (fun _ => q) le] at b
    have b' := (gs_appLE m2.φ _ _ le r z (mem_pull.2 hq) _).symm.trans b
    have hm : ψ.hom.left ((r ≫ m2.φ) z) ∈ W'.t.PP.L.U j :=
      (congrArg (fun f => f (r z) ∈ W'.t.PP.L.U j) e₄).mp hj
    have eg : r ≫ m2'.φ = (r ≫ m2.φ) ≫ ψ.hom.left := by rw [e₄, Category.assoc]
    refine (congrArg (fun f => gs f z _ (θ'.f j)) eg).trans ?_
    rw [Hθ Z (r ≫ m2.φ) z j q hm hq, b', T Z r z j q i hj hq hi, Units.val_mul, _root_.mul_assoc]
    rfl

end ThetaShiftProofs

end GlobalTheory.ArcQ.FrAgree

namespace GlobalTheory.ArcQ

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

theorem isArcFr_of_agree : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (k : Type) [Field k] (bF : c.F →+* k) (a : ArcIn Dw l (RingHom.id c.F) k bF) (O O' : Type) [CommRing O] [CommRing O'] (β : O →+* c.F) (β' : O' →+* c.F) (Y : Model Xo c β) (Y' : Model Xo c β') (χ : Sp (PowerSeries k) ⟶ Y.X) (χ' : Sp (PowerSeries k) ⟶ Y'.X) (W : Wit Y (a.restrict β) χ) (W' : Wit Y' (a.restrict β') χ') (ψ : W.t.G ≅ W'.t.G), W.Agree W' ψ → ∀ y₀ : Sp (FractionRing (PowerSeries k)) ⟶ Xo.XF c, y₀ ≫ Y.j = Out.jK (PowerSeries k) ≫ χ → y₀ ≫ Y'.j = Out.jK (PowerSeries k) ≫ χ' → Mono Y.j → ∀ (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR k)) (th : a.D₀.P.L.Sec), ThNZ th → ∀ (S : Type) [CommRing S] [Algebra c.F S] (ι : PowerSeries k →+* S) (y : FrPt Xo c S), IsUnit (ι PowerSeries.X) → IsArcFr W e th ι y → IsArcFr W' e th ι y := by
  intro hL hL2 E _ _ _ H Dw l Xo c k _ bF a O O' _ _ β β' Y Y' χ χ' W W' ψ hA y₀ hy hy' hj e th hth S _ _ ι y hι h
  obtain ⟨θ', hθ', -⟩ := (GlobalTheory.T.existsUnique_thetaOf_alt hL hL2 E H Dw l Xo c O' β' Y' k _ (a.restrict β') χ' W' th hth).1
  exact FrAgree.isArcFr_move hA y₀ hy hy' hj e th
    (fun _ _ => (GlobalTheory.T.existsUnique_thetaOf_alt hL hL2 E H Dw l Xo c O β Y k _ (a.restrict β) χ W th hth).1.unique) θ' hθ' ι y hι h

end GlobalTheory.ArcQ
