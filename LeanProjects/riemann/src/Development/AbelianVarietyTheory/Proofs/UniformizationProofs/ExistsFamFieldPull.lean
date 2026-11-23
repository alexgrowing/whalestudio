import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueSecPull
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBoxPullGen

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FamFieldPull

open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor

section General

variable {X X' Y Y' Z : Scheme.{0}} {L : LB X} {L' : LB X'} {Φ : X' ⟶ X} {K : Type} [Fintype K]

def wGerm (w : LB.Iso L' (L.pull Φ)) (y : Z) (J : (Z ⟶ X) → L.ι) (J' : (Z ⟶ X') → L'.ι) (ψ : Z ⟶ X') :
    (Z.presheaf.stalk y)ˣ := gw w ψ y (J (ψ ≫ Φ)) (J' ψ)

def IsSecPull (w : LB.Iso L' (L.pull Φ)) (φ' : K → (Y' ⟶ X')) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (h : Y' ⟶ Y)
    (a : LB.Sec (LB.LinComb L' φ' ε)) (s : LB.Sec (LB.LinComb L φ ε)) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (p : K → L.ι) (q : K → L'.ι),
    (∀ κ, Φ (φ' κ (r z)) ∈ L.U (p κ)) → (∀ κ, φ' κ (r z) ∈ L'.U (q κ)) →
    gs (r ≫ h) z (LB.wchart L φ p) (s.f p) =
      (∏ κ, gw w (r ≫ φ' κ) z (p κ) (q κ) ^ ε κ).val * gs r z (LB.wchart L' φ' q) (a.f q)

theorem IsSecPull.val {w : LB.Iso L' (L.pull Φ)} {φ' : K → (Y' ⟶ X')} {φ : K → (Y ⟶ X)} {ε : K → ℤ} {h : Y' ⟶ Y}
    {a : LB.Sec (LB.LinComb L' φ' ε)} {s : LB.Sec (LB.LinComb L φ ε)} (H : IsSecPull w φ' φ ε h a s)
    (hc : ∀ κ, φ' κ ≫ Φ = h ≫ φ κ) (r : Z ⟶ Y') (z : Z) {J J'} (hJ : Good L z J) (hJ' : Good L' z J') :
    sval s (r ≫ h) z J = (∏ κ, wGerm w z J J' (r ≫ φ' κ) ^ ε κ).val * sval a r z J' := by
  rw [sval_of s (r ≫ h) z J (fun κ => J ((r ≫ φ' κ) ≫ Φ)) (fun κ => by rw [Category.assoc, ← hc, Category.assoc])]
  exact H Z r z _ (fun κ => J' (r ≫ φ' κ)) (fun κ => hJ ((r ≫ φ' κ) ≫ Φ)) (fun κ => hJ' (r ≫ φ' κ))

theorem pmaps_val {w : LB.Iso L' (L.pull Φ)} {φ' : K → (Y' ⟶ X')} {φ : K → (Y ⟶ X)} {ε : K → ℤ} {h : Y' ⟶ Y}
    {a : LB.Gen (LB.LinComb L' φ' ε)} {t : LB.Gen (LB.LinComb L φ ε)} (H : PMaps w φ' φ ε a t h)
    (hc : ∀ κ, φ' κ ≫ Φ = h ≫ φ κ) (r : Z ⟶ Y') (z : Z) {J J'} (hJ : Good L z J) (hJ' : Good L' z J') :
    val t (r ≫ h) z J = (∏ κ, wGerm w z J J' (r ≫ φ' κ) ^ ε κ) * val a r z J' := by
  rw [val_of t (r ≫ h) z J (fun κ => J ((r ≫ φ' κ) ≫ Φ)) (fun κ => by rw [Category.assoc, ← hc, Category.assoc])]
  exact H Z r z _ (fun κ => J' (r ≫ φ' κ)) (fun κ => hJ ((r ≫ φ' κ) ≫ Φ)) (fun κ => hJ' (r ≫ φ' κ))

theorem exists_genPull (w : LB.Iso L' (L.pull Φ)) (hw : w.IsGen) (hL : L.IsLB) (hL' : L'.IsLB)
    (φ' : K → (Y' ⟶ X')) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (h : Y' ⟶ Y) (hc : ∀ κ, φ' κ ≫ Φ = h ≫ φ κ)
    (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) :
    ∃ t' : LB.Gen (LB.LinComb L' φ' ε), t'.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (J J'),
      Good L z J → Good L' z J' →
      val t (r ≫ h) z J = (∏ κ, wGerm w z J J' (r ≫ φ' κ) ^ ε κ) * val t' r z J' := by
  obtain ⟨s, hs, -⟩ := SecPull.existsUnique_secPull X X' Y Y' L L' Φ hL hL' w hw K φ' φ ε h hc (Geo.Tor.genSec t ht)
  have hv : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (J J'), Good L z J → Good L' z J' →
      (val t (r ≫ h) z J).val = (∏ κ, wGerm w z J J' (r ≫ φ' κ) ^ ε κ).val * sval s r z J' :=
    fun Z r z J J' hJ hJ' => (sval_genSec t ht _ z hJ).symm.trans (IsSecPull.val hs hc r z hJ hJ')
  have hu : ∀ c, IsUnit (s.f c) := fun c => Y'.toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy => by
    obtain ⟨J', hJ', e⟩ := sval_trans hL' s y c hy
    obtain ⟨J, hJ⟩ := BoxFamily.exists_good_at hL y
    have h₁ : IsUnit (sval s (𝟙 Y') y J') :=
      isUnit_of_mul_isUnit_right ((hv _ (𝟙 Y') y J J' hJ hJ') ▸ Units.isUnit _)
    exact (congrArg IsUnit ((gs_eq (𝟙 Y') y (LB.wchart L' φ' c) hy _).symm.trans e)).mpr
      ((Units.isUnit _).mul h₁)
  refine ⟨⟨fun c => (hu c).unit⟩, fun a b => Units.ext (s.compat a b), fun Z r z J J' hJ hJ' => Units.ext ?_⟩
  refine (hv Z r z J J' hJ hJ').trans ?_
  rw [Units.val_mul]
  exact congrArg₂ (· * ·) rfl (gs_unit r z _ (hJ'.mem φ' r) (hu _).unit)

end General

section Deg

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R}
  {D' : DegPre R'} (hD : IsPullDeg φ D D') (F : Type) [Field F] [Algebra (FractionRing R) F]
  [Algebra (FractionRing R') F]

abbrev prA : D'.P.A.left ⟶ D.P.A.left := hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)

theorem cPoint_left_pr {T' : Over (Spec (CommRingCat.of R'))} {T : Over (Spec (CommRingCat.of R))} (h : T'.left ⟶ T.left)
    (hh : h ≫ T.hom = T'.hom ≫ specOf φ) (x : D'.X) :
    (cP D' T' x).left ≫ prA hD = h ≫ (cP D T (hD.xe x)).left := by
  show (T'.hom ≫ (D'.c x).left) ≫ prA hD = h ≫ T.hom ≫ (D.c (hD.xe x)).left
  rw [Category.assoc, hD.c_pr, ← Category.assoc, ← hh, Category.assoc]

theorem one_left_pr {T' : Over (Spec (CommRingCat.of R'))} {T : Over (Spec (CommRingCat.of R))} (h : T'.left ⟶ T.left)
    (hh : h ≫ T.hom = T'.hom ≫ specOf φ) :
    (1 : T' ⟶ D'.P.A).left ≫ prA hD = h ≫ (1 : T ⟶ D.P.A).left := by
  show (T'.hom ≫ eSec D'.P.A) ≫ prA hD = h ≫ T.hom ≫ eSec D.P.A
  rw [Category.assoc, hD.he, ← Category.assoc, ← hh, Category.assoc]

theorem mul_left_pr {T' : Over (Spec (CommRingCat.of R'))} {T : Over (Spec (CommRingCat.of R))} (h : T'.left ⟶ T.left)
    (hh : h ≫ T.hom = T'.hom ≫ specOf φ) {a' b' : T' ⟶ D'.P.A} {a b : T ⟶ D.P.A}
    (ha : a'.left ≫ prA hD = h ≫ a.left) (hb : b'.left ≫ prA hD = h ≫ b.left) :
    (a' * b').left ≫ prA hD = h ≫ (a * b).left := by
  let θ : Over.mk (T'.hom ≫ spMap φ) ⟶ T := Over.homMk h hh
  exact ((pull_grp hD).2 T' a' b' (θ ≫ a) (θ ≫ b) ha.symm hb.symm).symm.trans
    (congrArg (fun q => q.left) (MonObj.comp_mul θ a b).symm)

variable (hT : (TF (R := R') F).hom ≫ specOf φ = (TF (R := R) F).hom)
  {Θ : (DegPre.BF D' F).left ⟶ (DegPre.BF D F).left}
  (h₁ : Θ ≫ (fst (TF (R := R) F) D.P.A).left = (fst (TF (R := R') F) D'.P.A).left)
  (h₂ : Θ ≫ (DegPre.prB D F).left = (DegPre.prB D' F).left ≫ prA hD)

include hT h₁ in
theorem theta_over : Θ ≫ (DegPre.BF D F).hom = (DegPre.BF D' F).hom ≫ specOf φ := by
  rw [← Over.w (fst (TF (R := R) F) D.P.A), ← Over.w (fst (TF (R := R') F) D'.P.A), ← Category.assoc, h₁,
    Category.assoc, hT]

include hT h₁ h₂

theorem shift_pr (x : D'.X) : (DegPre.prB D' F * cP D' _ x).left ≫ prA hD =
    Θ ≫ (DegPre.prB D F * cP D _ (hD.xe x)).left :=
  mul_left_pr hD Θ (theta_over F hT h₁) h₂.symm (cPoint_left_pr hD Θ (theta_over F hT h₁) x)

theorem famφ_pr (x : D'.X) (a : Fin 4) :
    DegPre.famφ D' F x a ≫ prA hD = Θ ≫ DegPre.famφ D F (hD.xe x) a := by
  fin_cases a
  · exact h₂.symm
  · exact shift_pr hD F hT h₁ h₂ x
  · exact cPoint_left_pr hD Θ (theta_over F hT h₁) x
  · exact one_left_pr hD Θ (theta_over F hT h₁)

theorem trF_pr (mu : D'.X) : (DegPre.trF D' F mu).left ≫ Θ = Θ ≫ (DegPre.trF D F (hD.xe mu)).left := by
  have a₁ : (DegPre.trF D' F mu).left ≫ (fst (TF (R := R') F) D'.P.A).left = (fst (TF (R := R') F) D'.P.A).left :=
    congrArg (fun q => q.left) (lift_fst _ _ : DegPre.trF D' F mu ≫ _ = _)
  have a₂ : (DegPre.trF D F (hD.xe mu)).left ≫ (fst (TF (R := R) F) D.P.A).left = (fst (TF (R := R) F) D.P.A).left :=
    congrArg (fun q => q.left) (lift_fst _ _ : DegPre.trF D F (hD.xe mu) ≫ _ = _)
  have b₁ : (DegPre.trF D' F mu).left ≫ (DegPre.prB D' F).left = (DegPre.prB D' F * cP D' _ mu).left :=
    congrArg (fun q => q.left) (lift_snd _ _ : DegPre.trF D' F mu ≫ _ = _)
  have b₂ : (DegPre.trF D F (hD.xe mu)).left ≫ (DegPre.prB D F).left = (DegPre.prB D F * cP D _ (hD.xe mu)).left :=
    congrArg (fun q => q.left) (lift_snd _ _ : DegPre.trF D F (hD.xe mu) ≫ _ = _)
  apply pullback.hom_ext
  · show (_ ≫ Θ) ≫ (fst (TF (R := R) F) D.P.A).left = (Θ ≫ _) ≫ (fst (TF (R := R) F) D.P.A).left
    rw [Category.assoc, Category.assoc, h₁, a₁, a₂, h₁]
  · show (_ ≫ Θ) ≫ (DegPre.prB D F).left = (Θ ≫ _) ≫ (DegPre.prB D F).left
    rw [Category.assoc, Category.assoc, h₂, b₂, ← Category.assoc, b₁]
    exact shift_pr hD F hT h₁ h₂ mu

theorem zF_pr : (DegPre.zF D' F).left ≫ Θ = (DegPre.zF D F).left := by
  have a₁ : (DegPre.zF D' F).left ≫ (fst (TF (R := R') F) D'.P.A).left = 𝟙 _ :=
    congrArg (fun q => q.left) (lift_fst _ _ : DegPre.zF D' F ≫ _ = _)
  have a₂ : (DegPre.zF D F).left ≫ (fst (TF (R := R) F) D.P.A).left = 𝟙 _ :=
    congrArg (fun q => q.left) (lift_fst _ _ : DegPre.zF D F ≫ _ = _)
  have b₁ : (DegPre.zF D' F).left ≫ (DegPre.prB D' F).left = (1 : TF (R := R') F ⟶ D'.P.A).left :=
    congrArg (fun q => q.left) (lift_snd _ _ : DegPre.zF D' F ≫ _ = _)
  have b₂ : (DegPre.zF D F).left ≫ (DegPre.prB D F).left = (1 : TF (R := R) F ⟶ D.P.A).left :=
    congrArg (fun q => q.left) (lift_snd _ _ : DegPre.zF D F ≫ _ = _)
  apply pullback.hom_ext
  · show (_ ≫ Θ) ≫ (fst (TF (R := R) F) D.P.A).left = _ ≫ (fst (TF (R := R) F) D.P.A).left
    rw [Category.assoc, h₁, a₁, a₂]; rfl
  · show (_ ≫ Θ) ≫ (DegPre.prB D F).left = _ ≫ (DegPre.prB D F).left
    rw [Category.assoc, h₂, b₂, ← Category.assoc, b₁]
    exact (one_left_pr hD (T' := TF (R := R') F) (T := TF (R := R) F) (𝟙 _)
      ((Category.id_comp _).trans hT.symm)).trans (Category.id_comp _)

theorem deltaφ_pr (k : ℕ) (α mu : D'.X) (a : Fin 4 ⊕ Fin 4) :
    DegPre.deltaφ D' F k α mu a ≫ prA hD = Θ ≫ DegPre.deltaφ D F k (hD.xe α) (hD.xe mu) a := by
  rcases a with a | a
  · refine (famφ_pr hD F hT h₁ h₂ (α + k • mu) a).trans ?_
    rw [map_add, map_nsmul]; rfl
  · show ((DegPre.trF D' F mu).left ≫ DegPre.famφ D' F α a) ≫ _ =
      Θ ≫ (DegPre.trF D F (hD.xe mu)).left ≫ DegPre.famφ D F (hD.xe α) a
    rw [Category.assoc, famφ_pr hD F hT h₁ h₂, ← Category.assoc, trF_pr hD F hT h₁ h₂, Category.assoc]

omit h₁ h₂ in
theorem famMult_pr (k : ℕ) (α mu : D'.X) (y : Sp F) {J J'} (hJ : Good D.P.L y J) (hJ' : Good D'.P.L y J') :
    val (Z := Sp F) (DegPre.famMult D F k (hD.xe mu) (hD.xe α)) (𝟙 _) y J =
      (∏ a, wGerm hD.w y J J' ((DegPre.zF D' F).left ≫ DegPre.deltaφ D' F k α mu a) ^ DegPre.deltaε k a) *
        val (Z := Sp F) (DegPre.famMult D' F k mu α) (𝟙 _) y J' := by
  have hj : jFK (R := R') F ≫ jK R' ≫ spMap φ = jFK (R := R) F ≫ jK R := (Category.assoc _ _ _).symm.trans hT
  have hh : (𝟙 (Sp F) : (TF (R := R') F).left ⟶ (TF (R := R) F).left) ≫ (TF (R := R) F).hom =
    (TF (R := R') F).hom ≫ specOf φ := (Category.id_comp _).trans hT.symm
  have vψ : ∀ χ, vK (D.psi (hD.xe χ)) y J =
      (wGerm hD.w y J J' (cP D' (TF (R := R') F) χ).left)⁻¹ * vK (D'.psi χ) y J' := fun χ => by
    have a₁ : 𝟙 _ ≫ jFK (R := R') F ≫ D'.xK χ = (cP D' (TF (R := R') F) χ).left :=
      (Category.id_comp _).trans (Category.assoc _ _ _).symm
    have e := pmaps_val (pmaps_psi hD F hj χ) (fun _ => by
      have := cPoint_left_pr hD (T' := TF (R := R') F) (T := TF (R := R) F) (𝟙 (Sp F)) hh χ
      exact (congrArg (· ≫ prA hD) (Category.assoc _ _ _).symm).trans
        (this.trans (congrArg (𝟙 (Sp F) ≫ ·) (Category.assoc _ _ _)))) (𝟙 _) y hJ hJ'
    rw [Fintype.prod_unique, zpow_neg_one, a₁, val_pull hJ, val_pull hJ', Category.comp_id] at e
    exact e
  have vρ : vK D.rigK y J = wGerm hD.w y J J' (1 : TF (R := R') F ⟶ D'.P.A).left * vK D'.rigK y J' := by
    have pm := (maps_iff hD.w _ (fun _ => eSec D.P.A) _ D'.rig D.rig (specOf φ) _
      (rigPull_le (prA hD) (specOf φ) hD.he D.P.L) (fun _ => rfl)).1 hD.w_rig
    have e := pmaps_val pm (fun _ => hD.he) (TF (R := R') F).hom y hJ hJ'
    rw [Fintype.prod_unique, zpow_one, hT] at e
    have b₁ : (𝟙 _ ≫ jFK (R := R) F) ≫ (toUnit (TK R)).left = (TF (R := R) F).hom := by rw [Category.id_comp]; rfl
    have b₂ : (𝟙 _ ≫ jFK (R := R') F) ≫ (toUnit (TK R')).left = (TF (R := R') F).hom := by rw [Category.id_comp]; rfl
    refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (congrArg₂ (· * ·) rfl (val_pull hJ' _ _ _).symm))
    rw [b₁, b₂]
    exact e
  have m : val (Z := Sp F) (DegPre.famMult D F k (hD.xe mu) (hD.xe α)) (𝟙 _) y J = vK (D.psi (hD.xe mu)) y J ^ k *
      (vK (D.psi (hD.xe mu + hD.xe α)) y J * (vK (D.psi (hD.xe mu)) y J)⁻¹ * (vK (D.psi (hD.xe α)) y J)⁻¹ *
        (vK D.rigK y J)⁻¹) * vK D.rigK y J ^ k := BoxFamily.famMult_val F hJ k _ _ _
  have m' : val (Z := Sp F) (DegPre.famMult D' F k mu α) (𝟙 _) y J' = vK (D'.psi mu) y J' ^ k *
      (vK (D'.psi (mu + α)) y J' * (vK (D'.psi mu) y J')⁻¹ * (vK (D'.psi α) y J')⁻¹ *
        (vK D'.rigK y J')⁻¹) * vK D'.rigK y J' ^ k := BoxFamily.famMult_val F hJ' k _ _ _
  have p := BoxFamily.prod_delta_zero F D' k α mu (wGerm (Z := Sp F) hD.w y J J')
  refine m.trans (Eq.trans ?_ (congrArg₂ (· * ·) p m').symm)
  rw [← map_add, vψ, vψ, vψ, vρ]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_pow]
  module

theorem gen_pr (hG : GlobalFnsSt) (k : ℕ) (α mu : D'.X)
    (u' : LB.Gen (LB.LinComb D'.P.L (DegPre.deltaφ D' F k α mu) (DegPre.deltaε k))) (hu' : u'.IsGen)
    (hc' : LB.Gen.Corr D'.P.L _ _ _ _ (LB.pullGen D'.P.L _ _ u' (DegPre.zF D' F).left) (DegPre.famMult D' F k mu α))
    (u : LB.Gen (LB.LinComb D.P.L (DegPre.deltaφ D F k (hD.xe α) (hD.xe mu)) (DegPre.deltaε k)))
    (hu : u.IsGen)
    (hc : LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (DegPre.zF D F).left)
      (DegPre.famMult D F k (hD.xe mu) (hD.xe α)))
    {Z : Scheme.{0}} (q : Z ⟶ (DegPre.BF D' F).left) (y : Z) {J J'} (hJ : Good D.P.L y J) (hJ' : Good D'.P.L y J') :
    val u (q ≫ Θ) y J =
      (∏ a, wGerm hD.w y J J' (q ≫ DegPre.deltaφ D' F k α mu a) ^ DegPre.deltaε k a) * val u' q y J' := by
  obtain ⟨t, ht, hv⟩ := exists_genPull hD.w hD.w_gen D.P.isLB D'.P.isLB _ _ _ Θ (deltaφ_pr hD F hT h₁ h₂ k α mu) u hu
  have z₁ : DegPre.zF D' F ≫ fst _ _ = 𝟙 _ := lift_fst _ _
  have key := gen_unique D'.P.isLB (fst (TF (R := R') F) D'.P.A).left (DegPre.zF D' F).left
    (congrArg (fun q => q.left) z₁) (surj_appTop D' F hG) hu' ht (fun y J' hJ' => by
      obtain ⟨J, hJ⟩ := BoxFamily.exists_good_at D.P.isLB y
      have e₁ := hv _ (DegPre.zF D' F).left y J J' hJ hJ'
      have e₂ := famMult_pr hD F hT k α mu y hJ hJ'
      have e₃ := val_corr hJ' hc' (𝟙 _)
      rw [val_pull hJ', Category.id_comp] at e₃
      have e₄ := (val_pull hJ _ _ _).symm.trans (val_corr hJ hc (𝟙 (Sp F)))
      erw [Category.id_comp] at e₄
      rw [zF_pr hD F hT h₁ h₂] at e₁
      exact e₃.trans (mul_left_cancel (e₂.symm.trans (e₄.symm.trans e₁))))
    Z q y J' hJ'
  rw [key]
  exact hv Z q y J J' hJ hJ'

theorem pull_fe (hG : GlobalFnsSt) (k : ℕ) (s : Fam D F k)
    (s' : ∀ x : D'.X, LB.Sec (LB.LinComb D'.P.L (DegPre.famφ D' F x) (DegPre.famε k)))
    (hs : ∀ x, IsSecPull hD.w (DegPre.famφ D' F x) (DegPre.famφ D F (hD.xe x)) (DegPre.famε k) Θ (s' x)
      (s.s (hD.xe x))) : DegPre.FamFE D' F k s' := by
  intro mu α u' hu' hc'
  obtain ⟨u, hu, hc⟩ := (gen_fe (D := D) (F := F) hG k (hD.xe mu) (hD.xe α)).1
  refine (secRel_iff D'.P.isLB _ _ _ _ _ _ _ _ _ u').2 fun y J' hJ' => ?_
  obtain ⟨J, hJ⟩ := BoxFamily.exists_good_at D.P.isLB y
  have e₁ := (hs (α + k • mu)).val (famφ_pr hD F hT h₁ h₂ _) (𝟙 _) y hJ hJ'
  have e₂ := (hs α).val (famφ_pr hD F hT h₁ h₂ _) (𝟙 _ ≫ (DegPre.trF D' F mu).left) y hJ hJ'
  have e₃ := gen_pr hD F hT h₁ h₂ hG k α mu u' hu' hc' u hu hc (𝟙 _) y hJ hJ'
  have e₄ : sval (s.s (hD.xe (α + k • mu))) (𝟙 _ ≫ Θ) y J =
      sval (s.s (hD.xe α)) ((𝟙 _ ≫ (DegPre.trF D' F mu).left) ≫ Θ) y J * (val u (𝟙 _ ≫ Θ) y J).val := by
    have := (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u).1 (s.fe _ _ u hu hc) _ (𝟙 _ ≫ Θ) y J hJ
    rw [map_add, map_nsmul, this, Category.assoc, Category.assoc, trF_pr hD F hT h₁ h₂]
  have e₅ : (∏ a, wGerm hD.w y J J' (𝟙 _ ≫ DegPre.deltaφ D' F k α mu a) ^ DegPre.deltaε k a) =
      (∏ a, wGerm hD.w y J J' (𝟙 _ ≫ DegPre.famφ D' F (α + k • mu) a) ^ DegPre.famε k a) *
      (∏ a, wGerm hD.w y J J' ((𝟙 _ ≫ (DegPre.trF D' F mu).left) ≫ DegPre.famφ D' F α a) ^ DegPre.famε k a)⁻¹ := by
    simp only [Category.assoc]
    exact prod_sum₂ (K := Fin 4) (K' := Fin 4) _ rfl (prod_neg _ _ rfl)
  refine (∏ a, wGerm hD.w y J J' (𝟙 _ ≫ DegPre.famφ D' F (α + k • mu) a) ^ DegPre.famε k a).mul_right_inj.1 ?_
  refine e₁.symm.trans (e₄.trans ?_)
  rw [e₃, e₅]
  refine (congrArg₂ (· * ·) e₂ rfl).trans ?_
  exact BoxFamily.unit_shuffle _ _ _ _

end Deg

end GlobalTheory.FamFieldPull

namespace GlobalTheory

theorem exists_fam_field_pull : GlobalFnsSt → ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (φ : R →+* R') (D : DegPre R) (D' : DegPre R') (hD : IsPullDeg φ D D') (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing R') F], (∀ r : R, algebraMap (FractionRing R) F (algebraMap R (FractionRing R) r) = algebraMap (FractionRing R') F (algebraMap R' (FractionRing R') (φ r))) → ∀ (Θ : (DegPre.BF D' F).left ⟶ (DegPre.BF D F).left), Θ ≫ (fst (TF (R := R) F) D.P.A).left = (fst (TF (R := R') F) D'.P.A).left → Θ ≫ (DegPre.prB D F).left = (DegPre.prB D' F).left ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) → ∀ (k : ℕ) (s : Fam D F k), ∃ s' : Fam D' F k, (∀ x : D'.X, (∀ (Z : Scheme.{0}) (r : Z ⟶ (DegPre.BF D' F).left) (z : Z) (p : Fin 4 → D.P.L.ι) (q : Fin 4 → D'.P.L.ι), (∀ κ, ((hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ))) ((DegPre.famφ D' F x) κ (r z)) ∈ D.P.L.U (p κ)) → (∀ κ, (DegPre.famφ D' F x) κ (r z) ∈ D'.P.L.U (q κ)) → Geo.Tor.gs (r ≫ Θ) z (LB.wchart D.P.L (DegPre.famφ D F (hD.xe x)) p) ((s.s (hD.xe x)).f p) = (∏ κ, Geo.Tor.gw hD.w (r ≫ (DegPre.famφ D' F x) κ) z (p κ) (q κ) ^ (DegPre.famε k) κ).val * Geo.Tor.gs r z (LB.wchart D'.P.L (DegPre.famφ D' F x) q) ((s'.s x).f q))) := by
  intro hG R R' _ _ _ _ φ D D' hD F _ _ _ hF Θ h₁ h₂ k s
  have hT : (TF (R := R') F).hom ≫ specOf φ = (TF (R := R) F).hom :=
    (Category.assoc _ _ _).trans
      (((congrArg (jFK (R := R') F ≫ ·) (Geo.Tor.spMap_comp φ _).symm).trans (Geo.Tor.spMap_comp _ _).symm).trans
        ((congrArg Geo.Tor.spMap (RingHom.ext fun r => (hF r).symm)).trans (Geo.Tor.spMap_comp _ _)))
  choose s' hs using fun x : D'.X => (SecPull.existsUnique_secPull _ _ _ _ D.P.L D'.P.L _ D.P.isLB D'.P.isLB hD.w
    hD.w_gen _ (DegPre.famφ D' F x) (DegPre.famφ D F (hD.xe x)) (DegPre.famε k) Θ
    (FamFieldPull.famφ_pr hD F hT h₁ h₂ x) (s.s (hD.xe x))).exists
  exact ⟨⟨s', FamFieldPull.pull_fe hD F hT h₁ h₂ hG k s s' hs⟩, hs⟩

end GlobalTheory
