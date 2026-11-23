import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegUnif
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import Development.AbelianVarietyTheory.BlockTheory.UniformisationCharts.CanonicalRigidImages
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.InvariantFunctionsDescend
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAffineOpenAndBijectiveOfWeightUnits
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsRatioPoints
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsMemCommonChart
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorusStableAffineOpenFunctionsWeightGraded
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LocallyTrivialTorusQuotientFlatSurjectiveCosets

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GtCoordCompare

section Refine

variable {X Y Y' : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']

def Refines (M : LB Y) (L : LB X) (φ : K → (Y ⟶ X)) (ε : K → ℤ) : Prop :=
  ∃ σ : M.ι → K → L.ι, (∀ i, M.U i ≤ LB.wchart L φ (σ i)) ∧
    ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (i j : M.ι), r z ∈ M.U i → r z ∈ M.U j →
      gm r z (M.U i ⊓ M.U j) (M.g i j) = trF φ ε r z (σ i) (σ j)

theorem refines_self (φ : K → (Y ⟶ X)) (ε : K → ℤ) : Refines (LB.LinComb L φ ε) L φ ε :=
  ⟨id, fun _ => le_rfl, fun _ r z i j hi hj => gm_linComb L φ ε r z i j hi hj⟩

theorem Refines.div {M M' : LB Y} {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    (h : Refines M L φ ε) (h' : Refines M' L φ' ε') :
    Refines (LB.div M M') L (Sum.elim φ φ') (Sum.elim ε fun k => - ε' k) := by
  obtain ⟨σ, le, hg⟩ := h
  obtain ⟨σ', le', hg'⟩ := h'
  refine ⟨fun p => Sum.elim (σ p.1) (σ' p.2), fun p y hy => Set.mem_iInter.2 ?_, fun Z r z p q hp hq => ?_⟩
  · rintro (k | k)
    exacts [Set.mem_iInter.1 (le _ hy.1) k, Set.mem_iInter.1 (le' _ hy.2) k]
  · refine (gm_div M' M r z p q ⟨hp, hq⟩).trans ?_
    rw [hg Z r z _ _ hp.1 hq.1, hg' Z r z _ _ hp.2 hq.2, trF, trF, trF, Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
    rfl

theorem Refines.linComb {M : LB Y} {φ : K → (Y ⟶ X)} {ε : K → ℤ} (h : Refines M L φ ε)
    (ψ : K' → (Y' ⟶ Y)) (δ : K' → ℤ) :
    Refines (LB.LinComb M ψ δ) L (fun p : K' × K => ψ p.1 ≫ φ p.2) (fun p => ε p.2 * δ p.1) := by
  obtain ⟨σ, le, hg⟩ := h
  refine ⟨fun j p => σ (j p.1) p.2, fun j y hy => Set.mem_iInter.2 fun p => ?_, fun Z r z i j hi hj => ?_⟩
  · exact Set.mem_iInter.1 (le _ (Set.mem_iInter.1 hy p.1)) p.2
  · refine (gm_linComb M ψ δ r z i j hi hj).trans ?_
    rw [trF, Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [hg Z (r ≫ ψ a) z _ _ (Set.mem_iInter.1 hi a) (Set.mem_iInter.1 hj a), trF, ← Finset.prod_zpow]
    simp only [zpow_mul, Category.assoc]

theorem Refines.exists_gen (hL : L.IsLB) {M : LB Y} {φ : K → (Y ⟶ X)} {ε : K → ℤ} (h : Refines M L φ ε)
    {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ} (hF : FormEq φ' ε' φ ε) (t : LB.Gen (LB.LinComb L φ' ε')) (ht : t.IsGen) :
    ∃ s : LB.Gen M, s.IsGen := by
  obtain ⟨u, hu, -⟩ := Geo.Tor.exists_gen hL hF t ht
  obtain ⟨σ, le, hg⟩ := h
  refine ⟨⟨fun i => res (le i) (u.s (σ i))⟩, fun i j => unit_ext fun y hy => ?_⟩
  refine ((gm_res _ y _ hy _).trans ((gm_res _ y _ hy.1 _).trans (gen_trans hu (𝟙 Y) y (le i hy.1) (le j hy.2)))).trans
    (Eq.symm ?_)
  exact (map_mul _ _ _).trans (congrArg₂ (· * ·) (hg _ _ y i j hy.1 hy.2)
    ((gm_res _ y _ hy _).trans (gm_res _ y _ hy.2 _)))

theorem isGen_one : (LB.oneGen L (Y := Y)).IsGen :=
  fun _ _ => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm

theorem gm_appLE {Z : Scheme.{0}} (f : Z ⟶ Y) (U : Y.Opens) (h : ⊤ ≤ f ⁻¹ᵁ U) (a : Γ(Y, U)ˣ) (z : Z) :
    gm (𝟙 Z) z ⊤ (Units.map (f.appLE U ⊤ h).hom.toMonoidHom a) = gm f z U a := by
  have e : Units.map (f.appLE U ⊤ h).hom.toMonoidHom a = res h (pullU f U a) := Units.ext rfl
  rw [e, gm_res _ z h trivial, gm_pull _ f z U (h trivial), Category.id_comp]

end Refine

section Present

variable {S : Scheme.{0}}

theorem bijective_of_basis {X : Type} [AddCommGroup X] {κ : Type} (b : Module.Basis κ ℤ X) {G B : Over S}
    [GrpObj G] [GrpObj B] (q : G ⟶ B) (i : splitTorus S X ⟶ G) (hq : IsMonHom q) (hi : IsMonHom i)
    (hf : Flat q.left) (hs : Surjective q.left) (ha : IsAffineHom q.left)
    (hk : IsPullback i (toUnit _) q (η[B])) (V : B.left.Opens) (hV : IsAffineOpen V)
    (u : κ → Γ(G.left, q.left ⁻¹ᵁ V)ˣ)
    (hu : ∀ (k : κ) (Z : Over S) (t : Z ⟶ splitTorus S X) (g : Z ⟶ G) (z : Z.left), q.left (g.left z) ∈ V →
      gm ((t ≫ i) * g).left z _ (u k) = gm t.left z ⊤ (charUnit S X (b k)) * gm g.left z _ (u k)) :
    Function.Bijective (AddMonoidAlgebra.liftNCRingHom (q.left.app V).hom
      ((Units.coeHom _).comp (AddMonoidHom.toMultiplicativeLeft
        (b.constr ℤ (fun k => Additive.ofMul (u k))).toAddMonoidHom)) (fun _ _ => Commute.all _ _)) := by
  refine (isAffineOpen_and_bijective_of_weight_units S X G B q i hq hi hf hs inferInstance hk V hV _ ?_).2
  intro χ Z t g h₁ h₂
  let v : Multiplicative X →* Γ(G.left, q.left ⁻¹ᵁ V)ˣ := AddMonoidHom.toMultiplicativeLeft
    (b.constr ℤ (fun k => Additive.ofMul (u k))).toAddMonoidHom
  have hv : ∀ k, v (Multiplicative.ofAdd (b k)) = u k := fun k =>
    congrArg Additive.toMul (b.constr_basis ℤ (fun k => Additive.ofMul (u k)) k)
  let F₁ : Multiplicative X →* Γ(Z.left, ⊤)ˣ :=
    (Units.map (((t ≫ i) * g).left.appLE _ ⊤ h₁).hom.toMonoidHom).comp v
  let F₂ : Multiplicative X →* Γ(Z.left, ⊤)ˣ := splitTorusPointsEquiv S X Z t *
    (Units.map (g.left.appLE _ ⊤ h₂).hom.toMonoidHom).comp v
  have e : (MonoidHom.toAdditiveRight F₁).toIntLinearMap = (MonoidHom.toAdditiveRight F₂).toIntLinearMap := by
    refine b.ext fun k => congrArg Additive.ofMul (unit_ext fun z _ => ?_)
    change gm _ z ⊤ (Units.map _ (v (Multiplicative.ofAdd (b k)))) =
      gm _ z ⊤ (splitTorusPointsEquiv S X Z t (Multiplicative.ofAdd (b k)) * Units.map _ (v (Multiplicative.ofAdd (b k))))
    have a : splitTorusPointsEquiv S X Z t (Multiplicative.ofAdd (b k)) = pullU t.left ⊤ (charUnit S X (b k)) :=
      Units.ext (splitTorusPointsEquiv_val _ _ _ t _)
    rw [map_mul, hv, gm_appLE, gm_appLE, hu k Z t g z (h₂ trivial), a]
    congr 1
    exact ((gm_pull (𝟙 _) t.left z ⊤ trivial _).trans (by rw [Category.id_comp])).symm
  have e' : F₁ (Multiplicative.ofAdd χ) = F₂ (Multiplicative.ofAdd χ) :=
    congrArg Additive.toMul (LinearMap.congr_fun e χ)
  rw [← splitTorusPointsEquiv_val]
  exact congrArg Units.val e'

attribute [local instance] SplitExt.free SplitExt.finite in

theorem isGt_of_units (E : SplitExt S) {G : Over S} [GrpObj G] (q : G ⟶ E.B) (i : splitTorus S E.X ⟶ G)
    (hq : IsMonHom q) (hi : IsMonHom i) (hf : Flat q.left) (hs : Surjective q.left) (ha : IsAffineHom q.left)
    (hk : IsPullback i (toUnit _) q (η[E.B]))
    (s : ∀ (χ : E.X) (a : (E.O χ).L.ι), Γ(G.left, q.left ⁻¹ᵁ (E.O χ).L.U a)ˣ)
    (h₁ : ∀ (χ : E.X) (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (a a' : (E.O χ).L.ι), q.left (r z) ∈ (E.O χ).L.U a →
      q.left (r z) ∈ (E.O χ).L.U a' →
      gm r z _ (s χ a') = gm (r ≫ q.left) z _ ((E.O χ).L.g a a') * gm r z _ (s χ a))
    (h₂ : ∀ (χ : E.X) (a : (E.O χ).L.ι) (Z : Over S) (t : Z ⟶ splitTorus S E.X) (g : Z ⟶ G) (z : Z.left),
      q.left (g.left z) ∈ (E.O χ).L.U a →
      gm ((t ≫ i) * g).left z _ (s χ a) = gm t.left z ⊤ (charUnit S E.X χ) * gm g.left z _ (s χ a))
    (h₃ : ∀ (χ : E.X) (a : (E.O χ).L.ι) (y : (𝟙_ (Over S)).left), q.left (eSec G y) ∈ (E.O χ).L.U a →
      gm (eSec G) y _ (s χ a) * gm (𝟙 _) y _ ((E.O χ).rig.s fun _ => a) = 1) : E.IsGt G := by
  have hact : ∀ {Z : Over S} (t : Z ⟶ splitTorus S E.X) (g : Z ⟶ G) (z : Z.left),
      q.left (((t ≫ i) * g).left z) = q.left (g.left z) := by
    intro Z t g z
    have e : ((t ≫ i) * g) ≫ q = g ≫ q := by
      rw [MonObj.mul_comp, Category.assoc, hk.w, ← Category.assoc, comp_toUnit, ← Hom.one_def, _root_.one_mul]
    exact congrArg (fun f => f.left z) e
  let u : ∀ (j : E.ChartIdx) (_k : Module.Free.ChooseBasisIndex ℤ E.X), Γ(G.left, q.left ⁻¹ᵁ E.chart j)ˣ :=
    fun j k => res (Scheme.Hom.preimage_mono q.left (E.chart_le j k)) (s _ (j k))
  have hu : ∀ (j : E.ChartIdx) k {Z : Scheme.{0}} (r : Z ⟶ G.left) (z : Z), q.left (r z) ∈ E.chart j →
      gm r z (q.left ⁻¹ᵁ E.chart j) (u j k) = gm r z _ (s _ (j k)) := fun j k Z r z hz => gm_res r z _ hz _
  refine ⟨{
    q := q, i := i, q_hom := hq, i_hom := hi, q_flat := hf, q_surjective := hs, q_affine := ha, isKernel := hk
    u := u
    coord := fun j V hV h => ?_
    trans := fun j j' k => unit_ext fun y hy => ?_
    act_le := fun j y hy => (congrArg (· ∈ E.chart j) (hact (fst _ _) (snd _ _) y)).mpr hy
    equiv := fun j k => unit_ext fun y hy => ?_
    unit_norm := fun j k => unit_ext fun y hy => ?_ }⟩
  · refine bijective_of_basis E.basis q i hq hi hf hs ha hk V hV _ fun k Z t g z hz => ?_
    have hz' : q.left (((t ≫ i) * g).left z) ∈ V := by rw [hact]; exact hz
    rw [gm_res _ z (V := q.left ⁻¹ᵁ V) _ hz', gm_res _ z (V := q.left ⁻¹ᵁ V) _ hz, hu j k _ z (h hz'), hu j k _ z (h hz)]
    exact h₂ _ _ Z t g z (E.chart_le j k (h hz))
  · refine ((gm_res _ y _ hy _).trans ((hu j' k _ y hy.2).trans
      (h₁ _ _ (𝟙 _) y (j k) (j' k) (E.chart_le j k hy.1) (E.chart_le j' k hy.2)))).trans (Eq.symm ?_)
    exact (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_pull (𝟙 _) q.left y (E.chart j ⊓ E.chart j') hy _).trans
      (gm_res _ y (V := E.chart j ⊓ E.chart j') _ hy _)) ((gm_res _ y _ hy _).trans (hu j k _ y hy.1)))
  · have hy' : q.left (((fst (splitTorus S E.X) G ≫ i) * snd (splitTorus S E.X) G).left y) ∈ E.chart j :=
      (congrArg (· ∈ E.chart j) (hact (fst _ _) (snd _ _) y)).mpr hy
    have e := h₂ _ (j k) _ (fst _ _) (snd _ _) y (E.chart_le j k hy)
    rw [← hu j k _ y hy, ← hu j k _ y hy'] at e
    refine ((gm_res _ y _ hy _).trans ((gm_pull (𝟙 _) ((fst (splitTorus S E.X) G ≫ i) * snd (splitTorus S E.X) G).left y
      (q.left ⁻¹ᵁ E.chart j) hy' _).trans ?_)).trans
      ((map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_res (𝟙 _) y _ hy _).trans
        (gm_pull (𝟙 _) (fst (splitTorus S E.X) G).left y ⊤ trivial _))
        (gm_pull (𝟙 _) (snd (splitTorus S E.X) G).left y (q.left ⁻¹ᵁ E.chart j) hy _))).symm
    rw [Category.id_comp, Category.id_comp, Category.id_comp]
    exact e
  · refine Eq.trans ?_ ((h₃ _ (j k) y (E.chart_le j k hy.1)).trans (map_one _).symm)
    refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_res _ y _ hy _).trans
      ((gm_pull (𝟙 _) (eSec G) y (q.left ⁻¹ᵁ E.chart j) hy.1 _).trans ?_)) (gm_res _ y _ hy _))
    rw [Category.id_comp]
    exact hu j k _ y hy.1

end Present

section Data

variable {R : Type} [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (e : ℕ)

theorem c_add (T : Over (Spec (CommRingCat.of R))) (χ χ' : D.X) :
    toUnit T ≫ D.c (χ + χ') = (toUnit T ≫ D.c χ) * (toUnit T ≫ D.c χ') := by
  rw [D.c_add]
  exact MonObj.comp_mul _ _ _

abbrev bundle (χ : D.X) : LB (thickObj R I e D.P.A).left :=
  LB.LinComb D.P.L (Y := (thickObj R I e D.P.A).left) (D.Oφ (D.prBe I e) χ) Oε

end Data

abbrev GermFn (Y : Scheme.{0}) := ∀ (Z : Scheme.{0}) (_ : Z ⟶ Y) (z : Z), (Z.presheaf.stalk z)ˣ

section

variable {P G B : Scheme.{0}} (q : G ⟶ B) (a p : P ⟶ G)

def HasGen (N : LB B) (c : GermFn P) : Prop :=
  ∃ s : ∀ j, Γ(G, q ⁻¹ᵁ N.U j)ˣ,
    (∀ (Z : Scheme.{0}) (r : Z ⟶ G) (z : Z) (j j' : N.ι), q (r z) ∈ N.U j → q (r z) ∈ N.U j' →
      gm r z _ (s j') = gm (r ≫ q) z _ (N.g j j') * gm r z _ (s j)) ∧
    ∀ (Z : Scheme.{0}) (r : Z ⟶ P) (z : Z) (j : N.ι), q (p (r z)) ∈ N.U j →
      gm (r ≫ a) z _ (s j) = c Z r z * gm (r ≫ p) z _ (s j)

variable {q a p}

theorem pt_eq (h : a ≫ q = p ≫ q) (x : P) : q (a x) = q (p x) := congrArg (fun g => g x) h

theorem HasGen.of_local (h : a ≫ q = p ≫ q) {N : LB B} {c : GermFn P} {A : Type} (W : A → B.Opens)
    (hW : ∀ x, ∃ α, x ∈ W α) (F : N.ι → A → GermFn G)
    (rep : ∀ j α, ∃ y : Γ(G, q ⁻¹ᵁ N.U j ⊓ q ⁻¹ᵁ W α)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ G) (z : Z),
      q (r z) ∈ N.U j → q (r z) ∈ W α → gm r z _ y = F j α Z r z)
    (tr : ∀ (Z : Scheme.{0}) (r : Z ⟶ G) (z : Z) (j j' : N.ι) (α α' : A), q (r z) ∈ N.U j →
      q (r z) ∈ N.U j' → q (r z) ∈ W α → q (r z) ∈ W α' →
      F j' α' Z r z = gm (r ≫ q) z _ (N.g j j') * F j α Z r z)
    (wt : ∀ (Z : Scheme.{0}) (r : Z ⟶ P) (z : Z) (j : N.ι) (α : A), q (p (r z)) ∈ N.U j →
      q (p (r z)) ∈ W α → F j α Z (r ≫ a) z = c Z r z * F j α Z (r ≫ p) z) :
    HasGen q a p N c := by
  choose y hy using rep
  have glue : ∀ j, ∃ s : Γ(G, q ⁻¹ᵁ N.U j)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ G) (z : Z) (α : A),
      q (r z) ∈ N.U j → q (r z) ∈ W α → gm r z _ s = F j α Z r z := by
    intro j
    obtain ⟨s, hs⟩ := glue_unit (q ⁻¹ᵁ N.U j) (fun α => q ⁻¹ᵁ N.U j ⊓ q ⁻¹ᵁ W α)
      (fun _ => inf_le_left) (fun x hx => by
        obtain ⟨α, hα⟩ := hW (q x)
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨α, hx, hα⟩) (y j) (fun α α' x hx => by
        have e₁ := tr _ (𝟙 G) x j j α α' hx.1.1 hx.1.1 hx.1.2 hx.2.2
        have e₂ := tr _ (𝟙 G) x j j α α hx.1.1 hx.1.1 hx.1.2 hx.1.2
        exact (hy j α _ (𝟙 G) x hx.1.1 hx.1.2).trans ((e₂.trans e₁.symm).trans
          (hy j α' _ (𝟙 G) x hx.1.1 hx.2.2).symm))
    refine ⟨s, fun Z r z α h₁ h₂ => ?_⟩
    have hm : r z ∈ q ⁻¹ᵁ N.U j ⊓ q ⁻¹ᵁ W α := ⟨h₁, h₂⟩
    exact (gm_res r z inf_le_left hm s).symm.trans ((congrArg (gm r z _) (hs α)).trans
      (hy j α Z r z h₁ h₂))
  choose s hs using glue
  refine ⟨s, fun Z r z j j' h₁ h₂ => ?_, fun Z r z j h₁ => ?_⟩
  · obtain ⟨α, hα⟩ := hW (q (r z))
    rw [hs j Z r z α h₁ hα, hs j' Z r z α h₂ hα]
    exact tr Z r z j j' α α h₁ h₂ hα hα
  · obtain ⟨α, hα⟩ := hW (q (p (r z)))
    rw [hs j Z (r ≫ p) z α h₁ hα, hs j Z (r ≫ a) z α ((pt_eq h (r z)).symm ▸ h₁ : q (a (r z)) ∈ _)
      ((pt_eq h (r z)).symm ▸ hα : q (a (r z)) ∈ _)]
    exact wt Z r z j α h₁ hα

theorem gm_gen {N : LB B} {t : LB.Gen N} (ht : t.IsGen) {Z : Scheme.{0}} (r : Z ⟶ B) (z : Z)
    {j j' : N.ι} (h : r z ∈ N.U j) (h' : r z ∈ N.U j') :
    gm r z _ (t.s j) = gm r z _ (N.g j j') * gm r z _ (t.s j') := by
  have hm : r z ∈ N.U j ⊓ N.U j' := ⟨h, h'⟩
  exact (gm_res r z _ hm _).symm.trans ((congrArg (gm r z _) (ht j j')).trans ((map_mul _ _ _).trans
    (congrArg _ (gm_res r z _ hm _))))

theorem gm_iso {L M : LB B} {w : LB.Iso L M} (hw : w.IsGen) {Z : Scheme.{0}} (r : Z ⟶ B) (z : Z)
    {j j' : M.ι} {k k' : L.ι} (hj : r z ∈ M.U j) (hj' : r z ∈ M.U j') (hk : r z ∈ L.U k)
    (hk' : r z ∈ L.U k') :
    gm r z (M.U j ⊓ L.U k) (w.s (j, k)) = gm r z _ (M.g j j') * (gm r z _ (L.g k k'))⁻¹ *
      gm r z (M.U j' ⊓ L.U k') (w.s (j', k')) := by
  have := gm_gen hw r z (j := (j, k)) (j' := (j', k')) ⟨hj, hk⟩ ⟨hj', hk'⟩
  exact this.trans (congrArg (· * _) (gm_div L M r z (j, k) (j', k') ⟨⟨hj, hk⟩, hj', hk'⟩))

theorem HasGen.div (h : a ≫ q = p ≫ q) {L M : LB B} {c c' : GermFn P} (hM : HasGen q a p M c)
    (hL : HasGen q a p L c') :
    HasGen q a p (LB.div M L) (fun Z r z => c Z r z * (c' Z r z)⁻¹) := by
  obtain ⟨s, s₁, s₂⟩ := hM
  obtain ⟨t, t₁, t₂⟩ := hL
  obtain ⟨u, hu⟩ : ∃ u : ∀ j : M.ι × L.ι, Γ(G, q ⁻¹ᵁ (M.U j.1 ⊓ L.U j.2))ˣ,
      ∀ (Z : Scheme.{0}) (r : Z ⟶ G) (z : Z) j, q (r z) ∈ M.U j.1 ⊓ L.U j.2 →
        gm r z _ (u j) = gm r z _ (s j.1) * (gm r z _ (t j.2))⁻¹ :=
    ⟨fun j => res (q.preimage_mono inf_le_left) (s j.1) * (res (q.preimage_mono inf_le_right) (t j.2))⁻¹,
      fun Z r z j hj => (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res r z _ hj _)
        ((map_inv _ _).trans (congrArg (·⁻¹) (gm_res r z _ hj _))))⟩
  refine ⟨u, fun Z r z j j' h₁ h₂ => ?_, fun Z r z j h₁ => ?_⟩
  · refine (hu Z r z j' h₂).trans (Eq.trans ?_ (congrArg₂ (· * ·)
      (gm_div L M (r ≫ q) z j j' ⟨h₁, h₂⟩) (hu Z r z j h₁)).symm)
    rw [s₁ Z r z _ _ h₁.1 h₂.1, t₁ Z r z _ _ h₁.2 h₂.2, mul_inv, _root_.mul_mul_mul_comm]
  · refine (hu Z (r ≫ a) z j ((pt_eq h (r z)).symm ▸ h₁ : q (a (r z)) ∈ _)).trans
      (Eq.trans ?_ (congrArg _ (hu Z (r ≫ p) z j h₁)).symm)
    rw [s₂ Z r z _ h₁.1, t₂ Z r z _ h₁.2, mul_inv, _root_.mul_mul_mul_comm]

theorem HasGen.iso (h : a ≫ q = p ≫ q) {L M : LB B} {c : GermFn P} (hL : HasGen q a p L c)
    (cov : ∀ x, ∃ k, x ∈ L.U k) (w : LB.Iso L M) (hw : w.IsGen) : HasGen q a p M c := by
  obtain ⟨s, s₁, s₂⟩ := hL
  refine HasGen.of_local h L.U cov
    (fun j k Z r z => gm r z _ (s k) * (gm (r ≫ q) z (M.U j ⊓ L.U k) (w.s (j, k)))⁻¹)
    (fun j k => ⟨res (V := q ⁻¹ᵁ M.U j ⊓ q ⁻¹ᵁ L.U k) inf_le_right (s k) *
      (res (U := q ⁻¹ᵁ (M.U j ⊓ L.U k)) (le_inf inf_le_left inf_le_right)
        (pullU q (M.U j ⊓ L.U k) (w.s (j, k))))⁻¹, fun Z r z h₁ h₂ => ?_⟩)
    (fun Z r z j j' k k' h₁ h₂ h₃ h₄ => ?_) (fun Z r z j k h₁ h₂ => ?_)
  · have hm : r z ∈ q ⁻¹ᵁ M.U j ⊓ q ⁻¹ᵁ L.U k := ⟨h₁, h₂⟩
    exact (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res r z _ hm _)
      ((map_inv _ _).trans (congrArg (·⁻¹)
        ((gm_res r z _ hm _).trans (gm_pull r q z (M.U j ⊓ L.U k) hm _)))))
  · rw [gm_iso hw (r ≫ q) z h₁ h₂ h₃ h₄, s₁ Z r z k k' h₃ h₄]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  · rw [s₂ Z r z k h₂, Category.assoc, Category.assoc, h, _root_.mul_assoc]

theorem HasGen.exists_gen {X : Scheme.{0}} {L : LB X} {K : Type} [Fintype K]
    {φ : K → (B ⟶ X)} {ε : K → ℤ} {c : GermFn P} (h : a ≫ q = p ≫ q)
    (H : HasGen q a p (LB.LinComb L φ ε) c) (φ' : K → (G ⟶ X)) (ε' : K → ℤ)
    (hφ : ∀ k, φ' k = q ≫ φ k) (hε : ∀ k, ε' k = -ε k) (hL : L.IsLB) :
    ∃ t : LB.Gen (LB.LinComb L φ' ε'), t.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ P) (z : Z) (J),
      Good L z J → val t (r ≫ a) z J = c Z r z * val t (r ≫ p) z J := by
  obtain rfl : φ' = fun k => q ≫ φ k := funext hφ
  obtain rfl : ε' = fun k => -ε k := funext hε
  obtain ⟨s, s₁, s₂⟩ := H
  have le : ∀ j : K → L.ι, LB.wchart L (fun k => q ≫ φ k) j ≤ q ⁻¹ᵁ LB.wchart L φ j :=
    fun _ _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
  refine ⟨⟨fun j => res (le j) (s j)⟩, fun j j' => unit_ext fun y hy => ?_, fun Z r z J hJ => ?_⟩
  · refine ((gm_res _ y _ hy _).trans (gm_res (𝟙 G) y (le j) hy.1 _)).trans (Eq.trans ?_ ((map_mul _ _ _).trans
      (congrArg₂ (· * ·) (gm_linComb L _ _ (𝟙 G) y j j' hy.1 hy.2)
        ((gm_res _ y _ hy _).trans (gm_res (𝟙 G) y (le j') hy.2 _)))).symm)
    have e := (s₁ _ (𝟙 G) y j j' (le j hy.1) (le j' hy.2)).trans (congrArg (· * _)
      (gm_linComb L φ ε (𝟙 G ≫ q) y j j' (le j hy.1) (le j' hy.2)))
    refine (inv_mul_cancel_left _ _).symm.trans (congrArg₂ (· * ·) ?_ e.symm)
    refine (DVR.prod_neg _ _ ?_).symm
    simp only [Category.assoc]
  · have m := hJ.mem (fun k => q ≫ φ k) (r ≫ p)
    have m' := hJ.mem (fun k => q ≫ φ k) (r ≫ a)
    have e : ∀ k, J ((r ≫ a) ≫ q ≫ φ k) = J ((r ≫ p) ≫ q ≫ φ k) := fun k => by
      rw [Category.assoc, Category.assoc, reassoc_of% h]
    rw [funext e] at m'
    rw [val_of _ (r ≫ a) z J _ e]
    exact (gm_res _ z (le _) m' _).trans ((s₂ Z r z _ (le _ m)).trans
      (congrArg _ (gm_res _ z (le _) m _).symm))

end

theorem gm_res_pull_top {X Y Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (f : Y ⟶ X) {V : Y.Opens}
    (hz : r z ∈ V) (h : V ≤ f ⁻¹ᵁ ⊤) (c : Γ(X, ⊤)ˣ) :
    gm r z V (res h (pullU f ⊤ c)) = gm (r ≫ f) z ⊤ c :=
  (gm_res r z h hz _).trans (gm_pull r f z ⊤ trivial c)

section Datum

variable {S : Scheme.{0}}

noncomputable def wt (X : Type) [AddCommGroup X] (G : Over S) (χ : X) :
    GermFn (splitTorus S X ⊗ G).left :=
  fun _ r z => gm (r ≫ (fst (splitTorus S X) G).left) z ⊤ (charUnit S X χ)

variable {E : SplitExt S} {G : Over S} [GrpObj G] (d : E.GtDatum G)

noncomputable abbrev act : splitTorus S E.X ⊗ G ⟶ G :=
  lift (fst (splitTorus S E.X) G ≫ d.i) (snd (splitTorus S E.X) G) ≫ μ[G]

attribute [local instance] SplitExt.free SplitExt.finite

end Datum

end GlobalTheory.GtCoordCompare
