import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.WeightedChartPullback.CancelSecAct
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.WeightedChartPullback.TorusInj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocal
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueSamePt
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SecEqZeroAndHomEqOfThickenings

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section

namespace GlobalTheory.ExpUniq

section Values
variable {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}

def diffSec {M : LB Y} (s s' : LB.Sec M) : LB.Sec M where
  f j := s.f j - s'.f j
  compat i j := by rw [map_sub, map_sub, s.compat, s'.compat, mul_sub]

theorem sval_diffSec (s s' : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y) {z : Z} {J} (hJ : Good L z J) :
    sval (diffSec s s') r z J = sval s r z J - sval s' r z J := by
  have k : ∀ (U : Y.Opens) (_ : r z ∈ U) (a b : Γ(Y, U)), gs r z U (a - b) = gs r z U a - gs r z U b :=
    fun U h a b => by simp only [gs_eq r z U h, map_sub]
  exact k _ (hJ.mem φ r) _ _

theorem eq_of_diffSec {M : LB Y} {s s' : LB.Sec M} (h : ∀ j, (diffSec s s').f j = 0) : s = s' := by
  obtain ⟨f, hf⟩ := s
  obtain ⟨f', hf'⟩ := s'
  obtain rfl : f = f' := funext fun j => sub_eq_zero.1 (h j)
  rfl

theorem gs_comp (r : Z ⟶ Y) (g : Y ⟶ X) (z : Z) (U : X.Opens) (h : g (r z) ∈ U)
    (a : Γ(X, U)) : gs (r ≫ g) z U a = (r.stalkMap z).hom (gs g (r z) U a) := by
  rw [← gs_pull r g z U h, gs_stalkMap r z _ h]
  exact congrArg _ ((gs_pull (𝟙 Y) g (r z) U h a).trans (by rw [Category.id_comp]))

theorem gs_eq_zero_of_sval (hL : L.IsLB) (s : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z)
    (h : ∀ J, Good L z J → sval s r z J = 0) (j : K → L.ι) (hj : r z ∈ LB.wchart L φ j) :
    gs r z _ (s.f j) = 0 := by
  obtain ⟨J, hJ⟩ := exists_good_pt hL z
  exact (sec_trans s r z hj (hJ.mem φ r)).trans ((congrArg _ (h J hJ)).trans (mul_zero _))

theorem sval_eq_zero_of_flat (hL : L.IsLB) (s : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y) {Z' : Scheme.{0}}
    (p : Z' ⟶ Z) [Flat p] [Surjective p] (h : ∀ z J, Good L z J → sval s (p ≫ r) z J = 0) (z : Z) (J)
    (hJ : Good L z J) : sval s r z J = 0 := by
  obtain ⟨y, rfl⟩ := p.surjective z
  have hm := hJ.mem φ r
  have e := (gs_comp p r y _ hm _).symm.trans (gs_eq_zero_of_sval hL s (p ≫ r) y (h y) _ hm)
  exact zero_dvd_iff.1 (dvd_descend p y (by rw [map_zero]; exact zero_dvd_iff.2 e))

end Values

theorem sval_eq_zero_of_sum {S B : Scheme.{0}} (X : Type) [AddCommGroup X] (Y : Over S) {L : LB B} (hL : L.IsLB)
    {K : Type} [Fintype K] (φ : X → K → (Y.left ⟶ B)) (ε : K → ℤ) (s : ∀ χ, LB.Sec (LB.LinComb L (φ χ) ε))
    (F : Finset X) (H : ∀ (w : (splitTorus S X ⊗ Y).left) J, Good L w J →
      ∑ χ ∈ F, gs (𝟙 _) w ⊤ (TorusInj.chiP X Y χ) * sval (s χ) (snd (splitTorus S X) Y).left w J = 0)
    (α : X) (hα : α ∈ F) (y : Y.left) (J) (hJ : Good L y J) : sval (s α) (𝟙 _) y J = 0 := by
  classical
  let j : X → K → L.ι := fun β k => J (𝟙 _ ≫ φ β k)
  let V : Y.left.Opens := F.inf fun β => LB.wchart L (φ β) (j β)
  have hV : ∀ β ∈ F, V ≤ LB.wchart L (φ β) (j β) := fun β hβ => Finset.inf_le hβ
  have hy : y ∈ V := by
    have : ∀ (F' : Finset X), y ∈ F'.inf fun β => LB.wchart L (φ β) (j β) := fun F' => by
      induction F' using Finset.induction_on with
      | empty => trivial
      | insert a F' _ ih => rw [Finset.inf_insert]; exact ⟨hJ.mem (φ a) (𝟙 _), ih⟩
    exact this F
  have ex : ∀ β ∈ F, ∃ c : Γ(Y.left, V), ∀ (Z : Scheme.{0}) (ρ : Z ⟶ Y.left) (z : Z),
      ρ z ∈ V → gs ρ z V c = gs ρ z (LB.wchart L (φ β) (j β)) ((s β).f (j β)) := fun β hβ =>
    ⟨_, fun Z ρ z hz => gs_res ρ z (hV β hβ) hz _⟩
  choose! c hc using ex
  let σ : Y ⟶ splitTorus S X ⊗ Y := lift 1 (𝟙 _)
  have hσ : σ.left ≫ (snd (splitTorus S X) Y).left = 𝟙 _ := by
    rw [← Over.comp_left, lift_snd, Over.id_left]
  have h0 := TorusInj.eq_zero_of_sum X Y F c (fn_ext fun w hw => by
    obtain ⟨J', hJ', e⟩ := exists_good L hL w (K := F × K)
      (fun a => (snd (splitTorus S X) Y).left ≫ φ a.1.1 a.2) (fun a => j a.1.1 a.2)
      (fun a b e => by
        have := congrArg (σ.left ≫ ·) e
        simp only [← Category.assoc, hσ] at this
        exact congrArg J this)
      (fun a => Set.mem_iInter.1 (hV _ a.1.2 hw) a.2)
    have E := H w J' hJ'
    have hw' : (𝟙 (splitTorus S X ⊗ Y).left : _ ⟶ _) w ∈ (snd (splitTorus S X) Y).left ⁻¹ᵁ V := hw
    rw [gs_eq _ w _ hw', gs_eq _ w _ hw', map_zero, map_zero, map_sum, map_sum, ← E]
    refine Finset.sum_congr rfl fun β hβ => ?_
    rw [← gs_eq _ w _ hw', gs_mul _ w _ hw', gs_res _ w _ hw', gs_pull (𝟙 _) (snd (splitTorus S X) Y).left w V hw, Category.id_comp,
      hc β hβ _ _ w hw, sval_of (s β) _ w J' (j β) (fun k => e (⟨β, hβ⟩, k))]) α hα
  have := hc α hα _ (𝟙 _) y hy
  rw [h0, gs_eq _ y V hy, map_zero, map_zero] at this
  exact this.symm

theorem sec_eq_zero {R : Type} [CommRing R] (I : Ideal R) (W : Type) [CommRing W] [IsNoetherianRing W] [Algebra R W]
    (hI : I.map (algebraMap R W) ≤ Ideal.jacobson ⊥) (H : Over (Spec (CommRingCat.of R))) [GrpObj H] [Smooth H.hom]
    [GeometricallyConnected H.hom] (N : LB (TA R W ⊗ H).left) (hN : N.IsLB) (s : LB.Sec N)
    (hs : ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (TA R W ⊗ H).left) (a : Z ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))),
      (r ≫ (snd (TA R W) H).left) ≫ H.hom = a ≫ thick R I e → ∀ (z : Z) j, r z ∈ N.U j → gs r z _ (s.f j) = 0) (j : N.ι) :
    s.f j = 0 := by
  let φ := algebraMap R W
  let H₀ : Over (Spec (CommRingCat.of W)) := Over.mk (pullback.fst (TA R W).hom H.hom)
  have := grpObj_geometricallyIntegral_of_smooth _ H
  have : Smooth H₀.hom := inferInstanceAs (Smooth (pullback.fst (TA R W).hom H.hom))
  have : GeometricallyIntegral H₀.hom :=
    inferInstanceAs (GeometricallyIntegral (pullback.fst (TA R W).hom H.hom))
  refine ThickeningDetermines.eq_zero_of_secIdeal_eq_bot hN s ?_ j
  have key := isIso_of_isClosedImmersion_of_thickenings W _ hI H₀
    (Over.homMk (pullback.lift (𝟙 _) ((TA R W).hom ≫ η[H].left) (by
      rw [Category.assoc, Over.w η[H]]; simp)) (pullback.lift_fst _ _ _)) (fun p ↦ inferInstance)
    _ (ThickeningDetermines.secIdeal hN s).subschemeι fun n ↦ by
      have : IsClosedImmersion (thick _ (I.map φ) n) :=
        IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
      have : QuasiCompact (fstG (I.map φ) n H₀).left :=
        inferInstanceAs (QuasiCompact (pullback.fst H₀.hom (thick _ (I.map φ) n)))
      let r : (thickObj _ (I.map φ) n H₀).left ⟶ (TA R W ⊗ H).left := (fstG (I.map φ) n H₀).left
      have : QuasiCompact r := this
      have h0 : ∀ j, (r.app _).hom (s.f j) = 0 := fun j ↦ fn_ext fun z hz => by
        have hz' : (𝟙 (thickObj _ (I.map φ) n H₀).left : _ ⟶ _) z ∈ r ⁻¹ᵁ N.U j := hz
        rw [gs_pull _ r z _ hz', Category.id_comp, gs_eq _ z _ hz', map_zero, map_zero]
        refine hs n _ r (pullback.snd H₀.hom (thick _ (I.map φ) n) ≫
            Spec.map (CommRingCat.ofHom (Ideal.quotientMap ((I.map φ) ^ (n + 1)) φ
            (by rw [← Ideal.map_pow]; exact Ideal.le_comap_map)))) ?_ z j hz
        have e₁ : (snd (TA R W) H).left ≫ H.hom = H₀.hom ≫ (TA R W).hom := pullback.condition.symm
        have e₂ : r ≫ H₀.hom = pullback.snd H₀.hom (thick _ (I.map φ) n) ≫ thick _ (I.map φ) n := pullback.condition
        rw [Category.assoc, e₁, ← Category.assoc, e₂, Category.assoc, Category.assoc, ← Spec.map_comp]
        exact congrArg _ (Spec.map_comp _ _).symm
      exact ⟨IsClosedImmersion.lift _ r (by
        rw [Scheme.IdealSheafData.ker_subschemeι]
        exact ThickeningDetermines.secIdeal_le_ker hN s _ h0), IsClosedImmersion.lift_fac _ _ _⟩
  rw [← Scheme.IdealSheafData.ker_subschemeι (ThickeningDetermines.secIdeal hN s)]
  exact IsClosedImmersion.isIso_iff_ker_eq_bot.1 key

section Level
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (c : GtCoord I D e G)
  {Y : Scheme.{0}} (p : Y ⟶ D.P.A.left) {K : Type} [Fintype K] {ε : K → ℤ}

theorem sval_eq_zero_of_group {φ : K → (Y ⟶ D.P.A.left)} (s : LB.Sec (LB.LinComb D.P.L φ ε))
    (H : ∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R I e G).left) (r : Z ⟶ Y), r ≫ p = x ≫ c.pG.left →
      ∀ z J, Good D.P.L z J → sval s r z J = 0)
    {Z : Scheme.{0}} (r : Z ⟶ Y) (a : Z ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))
    (ha : (r ≫ p) ≫ D.P.A.hom = a ≫ thick R I e) (z : Z) (J) (hJ : Good D.P.L z J) : sval s r z J = 0 := by
  let b : Z ⟶ (thickObj R I e D.P.A).left := pullback.lift (r ≫ p) a ha
  have hb : b ≫ pullback.fst D.P.A.hom (thick R I e) = r ≫ p := pullback.lift_fst _ _ _
  have := c.q_flat
  have := c.q_surj
  refine sval_eq_zero_of_flat D.P.isLB s r (pullback.fst b c.q.left)
    (H _ (pullback.snd b c.q.left) _ ?_) z J hJ
  rw [Category.assoc, ← hb, ← Category.assoc, pullback.condition, Category.assoc]
  rfl

theorem sval_eq_zero_of_weight_sum {φ : D.X → K → (Y ⟶ D.P.A.left)} (s : ∀ χ, LB.Sec (LB.LinComb D.P.L (φ χ) ε))
    (F : Finset D.X)
    (H : ∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R I e G).left) (r : Z ⟶ Y), r ≫ p = x ≫ c.pG.left →
      ∀ z J, Good D.P.L z J → ∑ χ ∈ F, sval (s χ) r z J * (val (c.t χ) x z J).val = 0)
    (α : D.X) (hα : α ∈ F) (Z : Scheme.{0}) (x : Z ⟶ (thickObj R I e G).left) (r : Z ⟶ Y)
    (hr : r ≫ p = x ≫ c.pG.left) (z : Z) (J) (hJ : Good D.P.L z J) : sval (s α) r z J = 0 := by
  let Z' : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) := Over.mk (x ≫ (thickObj R I e G).hom)
  let y : Z' ⟶ thickObj R I e G := Over.homMk x rfl
  let m : WeightPf.Te D I e ⊗ Z' ⟶ WeightPf.Te D I e ⊗ thickObj R I e G := WeightPf.Te D I e ◁ y
  let π : (WeightPf.Te D I e ⊗ Z').left ⟶ Z := (snd (WeightPf.Te D I e) Z').left
  have m₁ : m.left ≫ (fst _ _ : _ ⟶ WeightPf.Te D I e).left = (fst (WeightPf.Te D I e) Z').left := by
    rw [← Over.comp_left, whiskerLeft_fst]
  have m₂ : m.left ≫ (snd (WeightPf.Te D I e) (thickObj R I e G)).left = π ≫ x := by
    rw [← Over.comp_left, whiskerLeft_snd]; rfl
  have E := sval_eq_zero_of_sum D.X Z' D.P.isLB _ _
    (fun χ => pullMulSec (s χ) r (LB.pullGen D.P.L _ _ (c.t χ) x) (DVR.pullGen_isGen _ _ _ _ (c.t_gen χ) _)) F
    (fun w J hJ => by
      refine Eq.trans (Finset.sum_congr rfl fun χ _ => ?_)
        (H _ (m.left ≫ (WeightPf.act c).left) (π ≫ r) (by
          rw [Category.assoc, hr, Category.assoc, WeightPf.act_left_pG, ← Category.assoc, ← m₂, Category.assoc])
          w J hJ)
      have h := val_corr hJ (c.t_weight χ) m.left
      have h' : val (c.t χ) (m.left ≫ (WeightPf.act c).left) w J =
          gm (fst (WeightPf.Te D I e) Z').left w ⊤ (charUnit _ D.X χ) * val (c.t χ) (π ≫ x) w J := by
        rw [← m₁, ← m₂]
        refine (val_pull hJ _ _ _).symm.trans (h.trans ((val_mul hJ _ _ _).trans
          (congrArg₂ (· * ·) ?_ (val_pull hJ _ _ _))))
        exact (gm_res _ w _ (hJ.mem (PEmpty.elim : PEmpty → (_ ⟶ D.P.A.left)) _) _).trans
          (gm_pull _ _ w ⊤ trivial _)
      have h₀ : gs (𝟙 _) w ⊤ (TorusInj.chiP D.X Z' χ) =
          (gm (fst (WeightPf.Te D I e) Z').left w ⊤ (charUnit _ D.X χ)).val :=
        ((gs_pull (𝟙 _) (fst (WeightPf.Te D I e) Z').left w ⊤ trivial _).trans
          (by rw [Category.id_comp])).trans (gs_unit _ w ⊤ trivial _)
      rw [h', h₀, Units.val_mul, mul_left_comm]
      exact congrArg _ ((sval_pullMulSec _ _ _ _ π w hJ).trans
        (congrArg (fun u => _ * Units.val u) (val_pull hJ _ _ _)))) α hα z J hJ
  have E' := (sval_pullMulSec (s α) r _ _ (𝟙 Z) z hJ).symm.trans E
  rw [Category.id_comp] at E'
  exact (Units.mul_left_eq_zero _).1 E'

end Level

section Expansion
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
  {U : PreU I D A G} {T : Over (Spec (CommRingCat.of R))} {k : ℕ} {σ σ' : U.SecGT T k} {f f' : ∀ α, SecBT D T k α}

theorem expT_diff (h : U.ExpT T k σ f) (h' : U.ExpT T k σ' f') :
    U.ExpT T k (diffSec σ σ') (fun α => diffSec (f α) (f' α)) := fun e => by
  classical
  obtain ⟨s, hs⟩ := h e
  obtain ⟨s', hs'⟩ := h' e
  refine ⟨s ∪ s', fun Z x rG rB h₁ h₂ h₃ z JG J hJG hJ => ?_⟩
  obtain ⟨a, b⟩ := hs Z x rG rB h₁ h₂ h₃ z JG J hJG hJ
  obtain ⟨a', b'⟩ := hs' Z x rG rB h₁ h₂ h₃ z JG J hJG hJ
  refine ⟨fun α hα => ?_, ?_⟩
  · rw [Finset.mem_union, not_or] at hα
    rw [sval_diffSec _ _ _ hJ, a α hα.1, a' α hα.2, sub_zero]
  · rw [sval_diffSec _ _ _ hJG, mul_sub, b, b',
      Finset.sum_subset (Finset.subset_union_left (s₂ := s')) (fun α _ hα => by rw [a α hα, zero_mul]),
      Finset.sum_subset (s₁ := s') (Finset.subset_union_right (s₁ := s)) (fun α _ hα => by rw [a' α hα, zero_mul]),
      ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun α _ => by rw [sval_diffSec _ _ _ hJ, sub_mul]

theorem sval_sec_eq_zero (h : U.ExpT T k σ f)
    (hf : ∀ α (Z : Scheme.{0}) (r : Z ⟶ _) z J, Good D.P.L z J → sval (f α) r z J = 0) (e : ℕ) {Z : Scheme.{0}}
    (r : Z ⟶ (T ⊗ G).left) (a : Z ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))
    (ha : (r ≫ (snd T G).left) ≫ G.hom = a ≫ thick R I e) (z : Z) (JG) (hJG : Good U.P.L.L z JG) :
    sval σ r z JG = 0 := by
  obtain ⟨s, hs⟩ := h e
  let x : Z ⟶ (thickObj R I e G).left := pullback.lift _ a ha
  have hx : x ≫ (fstG I e G).left = r ≫ (snd T G).left := pullback.lift_fst _ _ _
  have hb : (U.gt e).pG.left ≫ D.P.A.hom = (fstG I e G).left ≫ G.hom :=
    (Over.w (U.gt e).pG).trans (Over.w (fstG I e G)).symm
  have w : (r ≫ (fst T G).left) ≫ T.hom = (x ≫ (U.gt e).pG.left) ≫ D.P.A.hom := by
    rw [Category.assoc, Category.assoc, hb, ← Category.assoc, ← Category.assoc, hx, Category.assoc, Category.assoc,
      Over.w, Over.w]
  obtain ⟨J, hJ⟩ := exists_good_pt D.P.isLB z
  have E := (hs Z x r (pullback.lift _ _ w) hx.symm (pullback.lift_snd _ _ _) (pullback.lift_fst _ _ _)
    z JG J hJG hJ).2
  rw [Finset.sum_eq_zero (fun α _ => by rw [hf α _ _ z J hJ, zero_mul]), ← Units.val_pow_eq_pow_val] at E
  exact (Units.mul_right_eq_zero _).1 E

theorem sval_term_eq_zero (h : U.ExpT T k σ f)
    (hσ : ∀ (Z : Scheme.{0}) (r : Z ⟶ _) z J, Good U.P.L.L z J → sval σ r z J = 0) (α : D.X) (e : ℕ) {Z : Scheme.{0}}
    (r : Z ⟶ (T ⊗ D.P.A).left) (a : Z ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))
    (ha : (r ≫ (snd T D.P.A).left) ≫ D.P.A.hom = a ≫ thick R I e) (z : Z) (J) (hJ : Good D.P.L z J) :
    sval (f α) r z J = 0 := by
  obtain ⟨s, hs⟩ := h e
  have hb : (U.gt e).pG.left ≫ D.P.A.hom = (fstG I e G).left ≫ G.hom :=
    (Over.w (U.gt e).pG).trans (Over.w (fstG I e G)).symm
  have H : ∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R I e G).left) (r : Z ⟶ (T ⊗ D.P.A).left),
      r ≫ (snd T D.P.A).left = x ≫ (U.gt e).pG.left → ∀ z J, Good D.P.L z J →
      (∀ α ∉ s, sval (f α) r z J = 0) ∧ ∑ χ ∈ s, sval (f χ) r z J * (val ((U.gt e).t χ) x z J).val = 0 := by
    intro Z x r hr z J hJ
    have w : (r ≫ (fst T D.P.A).left) ≫ T.hom = (x ≫ (fstG I e G).left) ≫ G.hom := by
      rw [Category.assoc, Category.assoc, ← hb, ← Category.assoc, ← Category.assoc, ← hr, Category.assoc,
        Category.assoc, Over.w, Over.w]
    obtain ⟨JG, hJG⟩ := exists_good_pt U.P.L.isLB z
    obtain ⟨E₁, E₂⟩ := hs Z x (pullback.lift _ _ w) r (pullback.lift_snd _ _ _) hr (pullback.lift_fst _ _ _).symm
      z JG J hJG hJ
    exact ⟨E₁, E₂.symm.trans ((congrArg _ (hσ _ _ z JG hJG)).trans (mul_zero _))⟩
  refine sval_eq_zero_of_group (U.gt e) (snd T D.P.A).left (f α) (fun Z x r hr z J hJ => ?_) r a ha z J hJ
  by_cases hα : α ∈ s
  · exact sval_eq_zero_of_weight_sum (U.gt e) (snd T D.P.A).left f s
      (fun Z x r hr z J hJ => (H Z x r hr z J hJ).2) α hα Z x r hr z J hJ
  · exact (H Z x r hr z J hJ).1 α hα

end Expansion

end GlobalTheory.ExpUniq

namespace GlobalTheory

open ExpUniq in

theorem expT_eq_iff : (AllPre fun {V} _ _ _ {_} {_} {_} _ _ U => ∀ (W : Type) [CommRing W] [IsLocalRing W] [Algebra V W], FinExt V W → ∀ k σ σ' f f', U.ExpT (TA V W) k σ f → U.ExpT (TA V W) k σ' f' → (σ = σ' ↔ f = f')) := by
  intro V _ _ _ hV D A G _ _ U W _ _ _ hW k σ σ' f f' h h'
  have := hV.1
  have := hW.1
  have : IsNoetherianRing W := IsNoetherianRing.of_finite V W
  have hI : (IsLocalRing.maximalIdeal V).map (algebraMap V W) ≤ Ideal.jacobson ⊥ :=
    have := hW.2.2.2.2
    IsAdicComplete.le_jacobson_bot _
  have hd := expT_diff h h'
  constructor
  · rintro rfl
    have := D.P.isAb.smooth
    have := D.P.isAb.geomConnected
    refine funext fun α => eq_of_diffSec (sec_eq_zero _ W hI D.P.A _ (DVR.linComb_isLB _ D.P.isLB _ _) _
      fun e Z r a ha z j hj => gs_eq_zero_of_sval D.P.isLB _ r z (fun J hJ => ?_) j hj)
    exact sval_term_eq_zero hd (fun Z r z J hJ => by rw [sval_diffSec _ _ _ hJ, sub_self]) α e r a ha z J hJ
  · rintro rfl
    have := U.semi.smooth
    have := U.semi.geomConnected
    refine eq_of_diffSec (sec_eq_zero _ W hI G _ (DVR.linComb_isLB _ U.P.L.isLB _ _) _
      fun e Z r a ha z j hj => gs_eq_zero_of_sval U.P.L.isLB _ r z (fun J hJ => ?_) j hj)
    exact sval_sec_eq_zero hd (fun α Z r z J hJ => by rw [sval_diffSec _ _ _ hJ, sub_self]) e r a ha z J hJ

end GlobalTheory
