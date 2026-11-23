import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Degenerations.MorAlgSt
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.WCompat
import Development.AbelianVarietyTheory.Definitions.Degenerations.ToATotal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsCPMapCompCancel
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.EvenCubicUnitEqOne
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceOfSection
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueAlgEquivOfCompatibleQuotient
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGtCoordOfTorusQuotient
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NonemptyFormalUniformisationTowerStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NonemptyAlgebraisationFormalTowerAmpleStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAdditiveWeightPointsOfTorusTowerStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.CubicalBundleRelAmpleOfAmpleFibresStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.KTrivOfClosedFibreLocalRingStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorusCoordinatesCompatOfTorusCompatStatement

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN

noncomputable section
namespace GlobalTheory.PreUnifLocal

section Quot
variable {Y A B : Scheme.{0}} {N : LB Y} {L : LB A} {M : LB B} {F : Y ⟶ A} {p : Y ⟶ B}

def IsQuotIso (u : LB.Iso N (L.pull F)) (v : LB.Iso N (M.pull p)) (w : LB.Iso (L.pull F) (M.pull p)) : Prop :=
  ∀ (Z : Scheme.{0}) (x : Z ⟶ Y) (z : Z) (j : M.ι) (k : L.ι) (m : N.ι), p (x z) ∈ M.U j → F (x z) ∈ L.U k →
    x z ∈ N.U m → gw v x z j m = gw w x z j (fun _ => k) * gw u x z k m

theorem exists_isQuotIso (hN : N.IsLB) (hL : L.IsLB) (hM : M.IsLB) {u : LB.Iso N (L.pull F)}
    {v : LB.Iso N (M.pull p)} (hu : PGen u) (hv : PGen v) : ∃ w, IsQuotIso u v w := by
  have glue : ∀ (j : M.ι) (k : L.ι), ∃ s : Γ(Y, (M.pull p).U (fun _ => j) ⊓ (L.pull F).U (fun _ => k))ˣ,
      ∀ (Z : Scheme.{0}) (x : Z ⟶ Y) (z : Z) (m : N.ι), p (x z) ∈ M.U j → F (x z) ∈ L.U k → x z ∈ N.U m →
        gm x z _ s = gw v x z j m * (gw u x z k m)⁻¹ := by
    intro j k
    obtain ⟨W, hW⟩ : ∃ W : N.ι → Y.Opens, ∀ m y, y ∈ W m ↔ p y ∈ M.U j ∧ F y ∈ L.U k ∧ y ∈ N.U m :=
      ⟨fun m => p ⁻¹ᵁ M.U j ⊓ (F ⁻¹ᵁ L.U k ⊓ N.U m), fun _ _ => Iff.rfl⟩
    have l₀ : ∀ m, W m ≤ (M.pull p).U (fun _ => j) ⊓ (L.pull F).U (fun _ => k) := fun m y hy =>
      ⟨mem_pull.2 ((hW m y).1 hy).1, mem_pull.2 ((hW m y).1 hy).2.1⟩
    have l₁ : ∀ m, W m ≤ (M.pull p).U (fun _ => j) ⊓ N.U m := fun m y hy =>
      ⟨mem_pull.2 ((hW m y).1 hy).1, ((hW m y).1 hy).2.2⟩
    have l₂ : ∀ m, W m ≤ (L.pull F).U (fun _ => k) ⊓ N.U m := fun m y hy =>
      ⟨mem_pull.2 ((hW m y).1 hy).2.1, ((hW m y).1 hy).2.2⟩
    obtain ⟨a, ha⟩ : ∃ a : ∀ m, Γ(Y, W m)ˣ, ∀ (Z : Scheme.{0}) (x : Z ⟶ Y) (z : Z) (m : N.ι), x z ∈ W m →
        gm x z (W m) (a m) = gw v x z j m * (gw u x z k m)⁻¹ :=
      ⟨fun m => res (l₁ m) (v.s (fun _ => j, m)) * (res (l₂ m) (u.s (fun _ => k, m)))⁻¹, fun Z x z m hy =>
        (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res x z (l₁ m) hy _)
          ((map_inv _ _).trans (congrArg (·⁻¹) (gm_res x z (l₂ m) hy _))))⟩
    obtain ⟨s, hs⟩ := glue_unit _ W l₀ (fun y hy => by
        obtain ⟨m, hm⟩ := exists_chart hN y
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨m, (hW m y).2 ⟨mem_pull.1 hy.1, mem_pull.1 hy.2, hm⟩⟩) a
      (fun m m' y hy => by
        have h₁ := (hW m y).1 hy.1
        have h₂ := (hW m' y).1 hy.2
        rw [ha _ (𝟙 Y) y m hy.1, ha _ (𝟙 Y) y m' hy.2, hv _ (𝟙 Y) y j j m m' h₁.1 h₁.1 h₁.2.2 h₂.2.2,
          hu _ (𝟙 Y) y k k m m' h₁.2.1 h₁.2.1 h₁.2.2 h₂.2.2, gm_self hM (𝟙 Y ≫ p) y h₁.1,
          gm_self hL (𝟙 Y ≫ F) y h₁.2.1]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv, ofMul_one]
        abel)
    refine ⟨s, fun Z x z m hj hk hm => ?_⟩
    have hy := (hW m (x z)).2 ⟨hj, hk, hm⟩
    exact (gm_res x z (l₀ m) hy s).symm.trans ((congrArg (gm x z (W m)) (hs m)).trans (ha Z x z m hy))
  choose s hs using glue
  refine ⟨⟨fun c => s (c.1 PUnit.unit) (c.2 PUnit.unit)⟩, fun Z x z j k m hj hk hm => ?_⟩
  exact (inv_mul_cancel_right _ _).symm.trans (congrArg (· * gw u x z k m) (hs j k Z x z m hj hk hm).symm)

theorem IsQuotIso.isGen (hN : N.IsLB) {u : LB.Iso N (L.pull F)} {v : LB.Iso N (M.pull p)} (hu : PGen u)
    (hv : PGen v) {w : LB.Iso (L.pull F) (M.pull p)} (h : IsQuotIso u v w) : w.IsGen := by
  refine (isGen_iff _).2 fun Z x z j j' k k' hj hj' hk hk' => ?_
  obtain ⟨m, hm⟩ := exists_chart hN (x z)
  have a := hv _ x z j j' m m hj hj' hm hm
  rw [h _ x z j (k PUnit.unit) m hj (mem_pull.1 hk) hm, h _ x z j' (k' PUnit.unit) m hj' (mem_pull.1 hk') hm,
    hu _ x z (k PUnit.unit) (k' PUnit.unit) m m (mem_pull.1 hk) (mem_pull.1 hk') hm hm] at a
  rw [gm_pull_g L F x z k k' hk hk']
  change gw w x z j (fun _ => k PUnit.unit) = _ * gw w x z j' (fun _ => k' PUnit.unit)
  apply Additive.ofMul.injective
  have a' := congrArg Additive.ofMul a
  simp only [ofMul_mul, ofMul_inv] at a' ⊢
  linear_combination (norm := abel) a'

theorem exists_ratio (hN : N.IsLB) (hM : M.IsLB) {v v' : LB.Iso N (M.pull p)} (hv : PGen v) (hv' : PGen v') :
    ∃ a : Γ(Y, ⊤)ˣ, ∀ (Z : Scheme.{0}) (x : Z ⟶ Y) (z : Z) (j : M.ι) (m : N.ι), p (x z) ∈ M.U j → x z ∈ N.U m →
      gw v' x z j m = gm x z ⊤ a * gw v x z j m := by
  let W : M.ι × N.ι → Y.Opens := fun c => (M.pull p).U (fun _ => c.1) ⊓ N.U c.2
  let b : ∀ c, Γ(Y, W c)ˣ := fun c => v'.s (fun _ => c.1, c.2) * (v.s (fun _ => c.1, c.2))⁻¹
  have hb : ∀ (Z : Scheme.{0}) (x : Z ⟶ Y) (z : Z) c,
      gm x z (W c) (b c) = gw v' x z c.1 c.2 * (gw v x z c.1 c.2)⁻¹ := fun Z x z c =>
    (map_mul _ _ _).trans (congrArg (gw v' x z c.1 c.2 * ·) (map_inv _ _))
  obtain ⟨a, ha⟩ := glue_unit ⊤ W (fun _ => le_top) (fun y _ => by
      obtain ⟨j, hj⟩ := exists_chart hM (p y)
      obtain ⟨m, hm⟩ := exists_chart hN y
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨(j, m), mem_pull.2 hj, hm⟩) b (fun c c' y hy => by
      rw [hb, hb, hv _ (𝟙 Y) y c.1 c'.1 c.2 c'.2 (mem_pull.1 hy.1.1) (mem_pull.1 hy.2.1) hy.1.2 hy.2.2,
        hv' _ (𝟙 Y) y c.1 c'.1 c.2 c'.2 (mem_pull.1 hy.1.1) (mem_pull.1 hy.2.1) hy.1.2 hy.2.2]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel)
  refine ⟨a, fun Z x z j m hj hm => ?_⟩
  have := (gm_res x z le_top (show x z ∈ W (j, m) from ⟨mem_pull.2 hj, hm⟩) a).symm.trans
    ((congrArg (gm x z (W (j, m))) (ha (j, m))).trans (hb Z x z (j, m)))
  rw [this, inv_mul_cancel_right]

end Quot

section Unique
variable {S S' : Scheme.{0}} {G : Over S'} {B : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj B] [IsCommMonObj B]

theorem gw_eq_of_isCPMap (hG : GlobalFnsSt) [ConnectedSpace S'] [ConnectedSpace G.left] {X : Type} [AddCommGroup X]
    [Module.Free ℤ X] (Q : TQ G X) {P : CP G} {M : CP B} {f : S' ⟶ S} {p : G.left ⟶ B.left} {hp} {v v'}
    (h : IsCPMap P M f p hp v) (h' : IsCPMap P M f p hp v') (Z : Scheme.{0}) (x : Z ⟶ G.left) (z : Z) (j m)
    (hj : p (x z) ∈ M.L.L.U j) (hm : x z ∈ P.L.L.U m) : gw v' x z j m = gw v x z j m := by
  obtain ⟨a, ha⟩ := exists_ratio P.L.isLB M.L.isLB ((isGen_iff _).1 h.gen) ((isGen_iff _).1 h'.gen)
  have key : ∀ (T : Over S') (z : T.left), gm (1 : T ⟶ G).left z ⊤ a = 1 ∧
      (∀ x : T ⟶ G, gm (x⁻¹).left z ⊤ a = gm x.left z ⊤ a) ∧ ∀ x y u : T ⟶ G,
        gm (x * y * u).left z ⊤ a * gm x.left z ⊤ a * gm y.left z ⊤ a * gm u.left z ⊤ a =
          gm (x * y).left z ⊤ a * gm (x * u).left z ⊤ a * gm (y * u).left z ⊤ a := by
    intro T z
    obtain ⟨J', hJ'⟩ := exists_good_pt P.L.isLB z
    obtain ⟨J, hJ⟩ := exists_good_pt M.L.isLB z
    obtain ⟨W, hW⟩ : ∃ W : (T ⟶ G) → (T.left.presheaf.stalk z)ˣ,
      ∀ x, W x = gw v x.left z (J (x.left ≫ p)) (J' x.left) := ⟨_, fun _ => rfl⟩
    obtain ⟨U, hU⟩ : ∃ U : (T ⟶ G) → (T.left.presheaf.stalk z)ˣ, ∀ x, gm x.left z ⊤ a = U x := ⟨_, fun _ => rfl⟩
    obtain ⟨a₁, a₂, a₃⟩ := h.vals T z J' J hJ' hJ W hW
    obtain ⟨b₁, b₂, b₃⟩ := h'.vals T z J' J hJ' hJ (fun x => U x * W x) (fun x => by
      rw [hW, ← hU]; exact (ha _ x.left z _ _ (hJ (x.left ≫ p)) (hJ' x.left)).symm)
    simp only [hU]
    have o : U 1 = 1 := by
      have := mul_right_cancel (b₁.symm.trans a₁)
      exact mul_eq_right.1 this
    refine ⟨o, fun x => ?_, fun x y u => ?_⟩
    · have a := congrArg Additive.ofMul (a₂ x)
      have b := congrArg Additive.ofMul (b₂ x)
      apply Additive.ofMul.injective
      simp only [ofMul_mul] at a b ⊢
      linear_combination (norm := abel) a - b
    · have a := a₃ x y u
      have b := b₃ x y u
      rw [o] at b
      generalize @id (T.left.presheaf.stalk z)ˣ (cubV M.c (T := Over.mk (T.hom ≫ f)) z J (toBase hp x)
        (toBase hp y) (toBase hp u)) = C at a b
      have a' := congrArg Additive.ofMul a
      have b' := congrArg Additive.ofMul b
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_one] at a' b' ⊢
      linear_combination (norm := abel) a' - b'
  have one : a = 1 := by
    refine GlobalTheory.even_cubic_unit_eq_one hG S' X G Q a fun T U hU => ?_
    let E : (T ⟶ G) → Γ(T.left, ⊤)ˣ := fun x => Units.map x.left.appTop.hom.toMonoidHom a
    have hE : ∀ x, U x = (E x).val := hU
    have e : ∀ (x : T ⟶ G) z, gm (𝟙 T.left) z ⊤ (E x) = gm x.left z ⊤ a := fun x z => (gm_top _ _ _).symm
    simp only [hE, ← Units.val_mul]
    refine ⟨congrArg Units.val (show E 1 = 1 from unit_ext fun z _ => ?_),
      fun x => congrArg Units.val (unit_ext fun z _ => ?_), fun x y u => congrArg Units.val (unit_ext fun z _ => ?_)⟩
    · rw [e, map_one]; exact (key T z).1
    · rw [e, e]; exact (key T z).2.1 x
    · simp only [map_mul, e]; exact (key T z).2.2 x y u
  rw [ha Z x z j m hj hm, one, map_one, _root_.one_mul]

theorem gw_compat (hG : GlobalFnsSt) [ConnectedSpace S'] [ConnectedSpace G.left] {X : Type} [AddCommGroup X]
    [Module.Free ℤ X] (Q : TQ G X) {S₁ : Scheme.{0}} {G₁ : Over S₁} {H : Over S} [GrpObj G₁] [IsCommMonObj G₁]
    [GrpObj H] [IsCommMonObj H] {P₀ : CP G} {P₁ : CP G₁} {P : CP H} {M : CP B} {t : S' ⟶ S₁} {f₁ : S₁ ⟶ S}
    {f₀ : S' ⟶ S} {m : G.left ⟶ G₁.left} {F₁ : G₁.left ⟶ H.left} {F₀ : G.left ⟶ H.left} {p₁ : G₁.left ⟶ B.left}
    {p₀ : G.left ⟶ B.left} (ef : t ≫ f₁ = f₀) (eF : m ≫ F₁ = F₀) (ep : m ≫ p₁ = p₀)
    (hm : IsGrpPullback G G₁ t m) {hF₀ hF₁ hp₀ hp₁ u₀ u₁ v₀ v₁} (U₀ : IsCPMap P₀ P f₀ F₀ hF₀ u₀)
    (U₁ : IsCPMap P₁ P f₁ F₁ hF₁ u₁) (V₀ : IsCPMap P₀ M f₀ p₀ hp₀ v₀) (V₁ : IsCPMap P₁ M f₁ p₁ hp₁ v₁) {w₀ w₁}
    (W₀ : IsQuotIso u₀ v₀ w₀) (W₁ : IsQuotIso u₁ v₁ w₁) (Z : Scheme.{0}) (x : Z ⟶ G.left) (z : Z) (j k)
    (hj : p₀ (x z) ∈ M.L.L.U j) (hk : F₀ (x z) ∈ P.L.L.U k) :
    gw w₁ (x ≫ m) z j (fun _ => k) = gw w₀ x z j (fun _ => k) := by
  subst ef eF ep
  obtain ⟨r, R, Tr⟩ := (isCPMap_comp_cancel _ _ _ f₁ t H G₁ G P P₁ P₀ F₁ hF₁ u₁ m hm.1.w hF₀ U₁).2
    (fun T x y => Over.OverMorphism.ext (hm.2 T x y _ _ rfl rfl).symm) u₀ U₀
  obtain ⟨v', Tv, V'⟩ := V₁.exists_comp R hp₀
  obtain ⟨c, hc⟩ := exists_chart P₀.L.isLB (x z)
  obtain ⟨d, hd⟩ := exists_chart P₁.L.isLB (m (x z))
  have e₀ := W₀ Z x z j k c hj hk hc
  have e₁ := W₁ Z (x ≫ m) z j k d hj hk hd
  rw [gw_eq_of_isCPMap hG Q V' V₀ Z x z j c hj hc, Tv Z x z j d c hj hd hc, Tr Z x z k d c hk hd hc, e₁,
    _root_.mul_assoc] at e₀
  exact mul_right_cancel e₀

end Unique

section Vals
variable {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S'} {H B : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj H]
  [IsCommMonObj H] [GrpObj B] [IsCommMonObj B]

omit [GrpObj G] [IsCommMonObj G] [IsCommMonObj H] in

theorem cubV_toBase {L : RigLB H} (c : CubicalStr H L) (F : (Over.map f).obj G ⟶ H)
    (hF : (show G.left ⟶ H.left from F.left) ≫ H.hom = G.hom ≫ f) {T : Over S'} (z : T.left) (J)
    (x y u : T ⟶ G) :
    @id (T.left.presheaf.stalk z)ˣ (cubV c (T := Over.mk (T.hom ≫ f)) z J (toBase hF x)
      (toBase hF y) (toBase hF u)) =
    @id (T.left.presheaf.stalk z)ˣ (cubV c (T := (Over.map f).obj T) z J ((Over.map f).map x ≫ F)
      ((Over.map f).map y ≫ F) ((Over.map f).map u ≫ F)) := by
  have e : ∀ x : T ⟶ G, toBase hF x = (Over.map f).map x ≫ F := fun x => Over.OverMorphism.ext rfl
  rw [e, e, e]

theorem IsQuotIso.vals {P₀ : CP G} {P : CP H} {M : CP B} (F : (Over.map f).obj G ⟶ H) (p : (Over.map f).obj G ⟶ B)
    {hF hp u v} (hu : IsCPMap P₀ P f F.left hF u) (hv : IsCPMap P₀ M f p.left hp v) {w} (hw : IsQuotIso u v w)
    (Z : Over S') (z : Z.left) (JG : (Z.left ⟶ H.left) → P.L.L.ι) (J : (Z.left ⟶ B.left) → M.L.L.ι)
    (hJG : Good P.L.L z JG) (hJ : Good M.L.L z J) (W : (Z ⟶ G) → (Z.left.presheaf.stalk z)ˣ)
    (hW : ∀ x, W x = gw w x.left z (J (x.left ≫ p.left)) (fun _ => JG (x.left ≫ F.left))) :
    (val (L := M.L.L) (φ := fun _ : PUnit => eSec B) (ε := fun _ => 1) M.L.rig (Z.hom ≫ f) z J =
        W 1 * val (L := P.L.L) (φ := fun _ : PUnit => eSec H) (ε := fun _ => 1) P.L.rig (Z.hom ≫ f) z JG) ∧
      (∀ x : Z ⟶ G, val M.sym (x.left ≫ p.left) z J * W x = W x⁻¹ * val P.sym (x.left ≫ F.left) z JG) ∧
      ∀ x y u : Z ⟶ G,
        @id (Z.left.presheaf.stalk z)ˣ (cubV M.c (T := (Over.map f).obj Z) z J
            ((Over.map f).map x ≫ p) ((Over.map f).map y ≫ p) ((Over.map f).map u ≫ p)) *
            W (x * y) * W (x * u) * W (y * u) * W 1 =
        W (x * y * u) * W x * W y * W u *
          @id (Z.left.presheaf.stalk z)ˣ (cubV P.c (T := (Over.map f).obj Z) z JG
            ((Over.map f).map x ≫ F) ((Over.map f).map y ≫ F) ((Over.map f).map u ≫ F)) := by
  obtain ⟨J', hJ'⟩ := exists_good_pt P₀.L.isLB z
  obtain ⟨U, hU⟩ : ∃ U : (Z ⟶ G) → (Z.left.presheaf.stalk z)ˣ,
    ∀ x, U x = gw u x.left z (JG (x.left ≫ F.left)) (J' x.left) := ⟨_, fun _ => rfl⟩
  obtain ⟨a₁, a₂, a₃⟩ := hu.vals Z z J' JG hJ' hJG U hU
  obtain ⟨b₁, b₂, b₃⟩ := hv.vals Z z J' J hJ' hJ (fun x => W x * U x) (fun x => by
    rw [hW, hU]
    exact (hw _ x.left z _ _ _ (hJ (x.left ≫ p.left)) (hJG (x.left ≫ F.left)) (hJ' x.left)).symm)
  refine ⟨b₁.trans ((_root_.mul_assoc _ _ _).trans (congrArg (W 1 * ·) a₁.symm)), fun x => ?_, fun x y t => ?_⟩
  · have a := congrArg Additive.ofMul (a₂ x)
    have b := congrArg Additive.ofMul (b₂ x)
    apply Additive.ofMul.injective
    simp only [ofMul_mul] at a b ⊢
    linear_combination (norm := abel) b - a
  · have a := a₃ x y t
    have b := b₃ x y t
    rw [cubV_toBase P.c F hF] at a
    rw [cubV_toBase M.c p hp] at b
    generalize @id (Z.left.presheaf.stalk z)ˣ (cubV M.c (T := (Over.map f).obj Z) z J
            ((Over.map f).map x ≫ p) ((Over.map f).map y ≫ p) ((Over.map f).map t ≫ p)) = C at b ⊢
    generalize @id (Z.left.presheaf.stalk z)ˣ (cubV P.c (T := (Over.map f).obj Z) z JG
            ((Over.map f).map x ≫ F) ((Over.map f).map y ≫ F) ((Over.map f).map t ≫ F)) = C' at a ⊢
    have a' := congrArg Additive.ofMul a
    have b' := congrArg Additive.ofMul b
    apply Additive.ofMul.injective
    simp only [ofMul_mul] at a' b' ⊢
    linear_combination (norm := abel) b' - a'

end Vals

section Assemble
variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {I : Ideal R}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] {P : CP G} {X : Type} [AddCommGroup X]

theorem sym_of_cp {S : Scheme.{0}} {B : Over S} [GrpObj B] [IsCommMonObj B] (M : CP B) : Sym B M.L.L := fun _ =>
  ⟨⊤, trivial, gen_chartPull (chartPullSame M.L.L _ _ _ (B.hom ⁻¹ᵁ ⊤).ι fun k => by
    fin_cases k
    exacts [rfl, (Category.comp_id _).symm]) M.sym M.sym_gen⟩

omit [IsDomain R] in

theorem isLocalRing_quot (hI : I ≠ ⊤) (e : ℕ) : IsLocalRing (R ⧸ I ^ (e + 1)) := by
  have : Nontrivial (R ⧸ I ^ (e + 1)) := Ideal.Quotient.nontrivial_iff.2 fun h =>
    hI (top_le_iff.1 (h ▸ Ideal.pow_le_self (Nat.succ_ne_zero e)))
  exact IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective

omit [IsDomain R] [IsLocalRing R] [IsCommMonObj G] in

theorem isGrpPullback_thickMap (e : ℕ) :
    IsGrpPullback (thickObj R I e G) (thickObj R I (e + 1) G) (thickTrans R I e) (thickMap R I e G) :=
  (isGrpPullback_pullback G (thick R I (e + 1))).cancel
    ((isGrpPullback_pullback G (thick R I e)).congr (thickTrans_comp R I e).symm
      ((pullback.lift_fst _ _ _).trans (Category.comp_id _)).symm) (pullback.lift_snd _ _ _)

theorem exists_preU (hG : GlobalFnsSt)
    (hc : ∀ (D : DegPre R) (e : ℕ) (g : GtCoord I D e G) (g' : GtCoord I D (e + 1) G),
      thickMap R I e G ≫ g'.pG.left = g.pG.left → TorusCompat (thickTrans R I e) (thickMap R I e G) g.i g'.i →
      ∀ χ, LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ (g'.t χ) (thickMap R I e G)) (g.t χ))
    (hI : I ≠ ⊤) (hs : IsSemiAbelian G) [Module.Free ℤ X] [Module.Finite ℤ X] (T : TowerR I P X) (a : T.Alg)
    (hK : KTriv a.B a.M.L.L) (c : X → (𝟙_ _ ⟶ a.B)) (hadd : ∀ χ χ', c (χ + χ') = c χ * c χ')
    (hw : ∀ χ e, a.RepWt (c χ) χ e) (A : PolAV (Sp (FractionRing R))) (gen : (Over.pullback (jK R)).obj G ≅ A.A)
    (hgen : IsMonHom gen.hom) (hA : LBIso (A.L.pull gen.hom.left) (P.L.L.pull (pullback.fst G.hom (jK R)))) :
    ∃ (D : DegPre R) (U : PreU I D A G), U.P = P ∧ U.gen = gen := by
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim R a.B a.isAb
  obtain ⟨wA, hwA⟩ := hA
  choose psi hpsi using fun χ : X => DVR.exists_gen_of_local (V := FractionRing R) a.M.L.L a.M.L.isLB (K := PUnit)
    (fun _ => ptK (c χ)) (fun _ => -1)
  let B : PolAV (Spec (CommRingCat.of R)) :=
    { A := a.B, isAb := a.isAb, g := g, smoothDim := hg, L := a.M.L.L, isLB := a.M.L.isLB,
      rigid := ⟨a.M.L.rig, a.M.L.rigGen⟩, sym := sym_of_cp a.M, ample := a.ample, ktriv := hK }
  let D : DegPre R :=
    { P := B, rig := a.M.L.rig, rig_gen := a.M.L.rigGen, cub := a.M.c, sym := a.M.sym, sym_gen := a.M.sym_gen,
      sym_rig := a.M.sym_rig, X := X, c := c, c_add := hadd, psi := psi, psi_gen := hpsi }
  choose gt hi hp using fun e => GlobalTheory.exists_gtCoord_of_torusQuotient hG R I D e G (T.l e).Q (a.b e)
    (a.b_pb e).1 (fun χ => hw χ e)
  have hq : ∀ e, thickMap R I e G ≫ (gt (e + 1)).pG.left = (gt e).pG.left := fun e => by
    rw [hp, hp, ← Category.assoc, ← T.β_q, Category.assoc, a.b_β]
  choose u hu using fun e => (T.l e).lev
  have hv : ∀ e, ∃ v, IsCPMap (T.l e).Pe a.M (thick R I e) (gt e).pG.left (Over.w (gt e).pG) v := fun e => by
    obtain ⟨h, v, hv⟩ := a.b_pb e
    have : ∀ f p (_ : f = 𝟙 _ ≫ thick R I e) (_ : p = (T.l e).Q.q.left ≫ a.b e) hw,
        ∃ v, IsCPMap (T.l e).Pe a.M f p hw v := by
      rintro _ _ rfl rfl hw
      obtain ⟨v', -, h'⟩ := hv.exists_comp (T.l e).D.map hw
      exact ⟨v', h'⟩
    exact this _ _ (Category.id_comp _).symm (hp e) _
  choose v hv using hv
  choose w hw using fun e => exists_isQuotIso (T.l e).Pe.L.isLB P.L.isLB a.M.L.isLB ((isGen_iff _).1 (hu e).gen)
    ((isGen_iff _).1 (hv e).gen)
  refine ⟨D,
    { semi := hs, gen := gen, gen_hom := hgen, P := P, wA := wA, wA_gen := hwA, gt := gt, gt_q := hq
      gt_t := fun e => hc D e _ _ (hq e) (by rw [hi, hi]; exact T.tor e)
      w := w
      w_gen := fun e => (hw e).isGen (T.l e).Pe.L.isLB ((isGen_iff _).1 (hu e).gen) ((isGen_iff _).1 (hv e).gen)
      w_vals := fun e Z z JG J hJG hJ W hW => ?_
      w_compat := fun e Z x z j k hj hk => ?_ }, rfl, rfl⟩
  · exact IsQuotIso.vals (fstG I e G) (gt e).pG (hu e) (hv e) (hw e) Z z JG J hJG hJ W hW
  · have := isLocalRing_quot hI e
    have := GlobalTheory.AbelianDim.connectedSpace_spec_of_isLocalRing (R ⧸ I ^ (e + 1))
    have hs' := Geo.Tor.IsSemiAbelian.pullback (thick R I e) G hs
    have := hs'.smooth
    have := hs'.geomConnected
    have : ConnectedSpace (thickObj R I e G).left := (GlobalTheory.GroupConn.connectedSpace_group _ (thickObj R I e G)).1
    exact gw_compat hG (T.l e).Q (thickTrans_comp R I e) ((pullback.lift_fst _ _ _).trans (Category.comp_id _)) (hq e)
      (isGrpPullback_thickMap e) (hu e) (hu (e + 1)) (hv e) (hv (e + 1)) (hw e) (hw (e + 1)) Z x z j k hj hk

end Assemble

section Principal
variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {I : Ideal R}

omit [IsDomain R] in

theorem isAdicComplete_quot [IsNoetherianRing R] (h : IsAdicComplete (IsLocalRing.maximalIdeal R) R) (J : Ideal R)
    [IsLocalRing (R ⧸ J)] : IsAdicComplete (IsLocalRing.maximalIdeal (R ⧸ J)) (R ⧸ J) := by
  have := GlobalTheory.isAdicComplete_map_of_finite (IsLocalRing.maximalIdeal R) (R ⧸ J)
  rwa [show algebraMap R (R ⧸ J) = Ideal.Quotient.mk J from rfl,
    IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective] at this

omit [IsDomain R] in

theorem kTriv_closedFibre {J : Ideal R} (hJ : J ≠ ⊤) {B : Over (Sp R)} [GrpObj B] {B₀ : Over (Sp (R ⧸ J))} [GrpObj B₀]
    {b : B₀.left ⟶ B.left} (hb : IsGrpPullback B₀ B (spMap (Ideal.Quotient.mk J)) b) {M : LB B.left} {M₀ : LB B₀.left}
    (hM : M.IsLB) (hM₀ : M₀.IsLB) {v : LB.Iso M₀ (M.pull b)} (hv : v.IsGen) (hK : KTriv B₀ M₀) :
    KTriv ((Over.pullback (spMap (IsLocalRing.residue R))).obj B)
      (M.pull (pullback.fst B.hom (spMap (IsLocalRing.residue R)))) := by
  let x : Sp (IsLocalRing.ResidueField R) ⟶ Sp (R ⧸ J) :=
    spMap (Ideal.Quotient.lift J (IsLocalRing.residue R) fun r hr =>
      (IsLocalRing.residue_eq_zero_iff r).2 (IsLocalRing.le_maximalIdeal hJ hr))
  have hx : x ≫ spMap (Ideal.Quotient.mk J) = spMap (IsLocalRing.residue R) := by
    rw [← Spec.map_comp]; rfl
  have sq : pullback.fst B.hom (spMap (IsLocalRing.residue R)) ≫ B.hom =
      (pullback.snd B.hom (spMap (IsLocalRing.residue R)) ≫ x) ≫ spMap (Ideal.Quotient.mk J) := by
    rw [Category.assoc, hx, pullback.condition]
  have hφ := hb.1.lift_fst _ _ sq
  have h := hb.cancel ((isGrpPullback_pullback B (spMap (IsLocalRing.residue R))).congr hx.symm hφ.symm)
    (hb.1.lift_snd _ _ sq)
  have hL' : (M.pull (pullback.fst B.hom (spMap (IsLocalRing.residue R)))).IsLB := LB.isLB_pull hM _
  obtain ⟨r, hr⟩ : LBIso (M.pull (pullback.fst B.hom (spMap (IsLocalRing.residue R))))
      (M.pull (hb.1.lift _ _ sq ≫ b)) := by
    rw [hφ]; exact GlobalTheory.lbIso_refl hL'
  obtain ⟨w, Tw⟩ := Geo.Tor.exists_cancel hM v r ((isGen_iff _).1 hv) ((isGen_iff _).1 hr) hM₀ hL'
  exact kTriv_pull h hM₀ hL' (Tw.pgen_cancel hM ((isGen_iff _).1 hv) ((isGen_iff _).1 hr)) hK

end Principal

theorem exists_preU_of_fibres (hF : Laws → Laws2 → Laws3 → USt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), admitted R I → ∀ (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (P : CP G), IsSemiAbelian G → HypW G P.L.L → ∀ (A : PolAV (Sp (FractionRing R))) (gen : (Over.pullback (jK R)).obj G ≅ A.A), IsMonHom gen.hom → LBIso (A.L.pull gen.hom.left) (P.L.L.pull (pullback.fst G.hom (jK R))) → ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (T : TowerR I P X) (k : Type) [Field k] (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (R ⧸ I ^ (0 + 1)))), RelAmple ((Over.pullback x).obj (T.l 0).Q.B) ((T.l 0).D.M.L.L.pull (pullback.fst _ x)) ∧ KTriv ((Over.pullback x).obj (T.l 0).Q.B) ((T.l 0).D.M.L.L.pull (pullback.fst _ x))) :
    Laws → Laws2 → Laws3 → Ega → USt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), admitted R I → IsPrincipalIdealRing (R ⧸ I) → ∀ (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (P : CP G), IsSemiAbelian G → HypW G P.L.L → SplitOver G I → ∀ (A : PolAV (Sp (FractionRing R))) (gen : (Over.pullback (jK R)).obj G ≅ A.A), IsMonHom gen.hom → LBIso (A.L.pull gen.hom.left) (P.L.L.pull (pullback.fst G.hom (jK R))) → ∃ (D : DegPre R) (U : PreU I D A G), U.P = P ∧ U.gen = gen := by
  intro hL hL2 hL3 hE hU R _ _ _ I hR hP G _ _ P hs hW hS A gen hgen hA
  have hI : I ≠ ⊤ := hR.2.2.2.1.ne_top
  have := hR.1.1
  have hpr : IsProper (pullback.snd G.hom (jK R)) := by
    have := A.isAb.proper
    have e : pullback.snd G.hom (jK R) = gen.hom.left ≫ A.A.hom := (Over.w gen.hom).symm
    have : IsIso gen.hom.left := inferInstanceAs (IsIso ((Over.forget _).map gen.hom))
    rw [e]; infer_instance
  obtain ⟨X, _, _, _, ⟨T⟩⟩ := GlobalTheory.T.nonempty_formalUniformisationTower hL hL2 R I hR G P hs hW hpr hS
  have hf := hF hL hL2 hL3 hU R I hR G P hs hW A gen hgen hA X T
  have := isLocalRing_quot hI 0
  have e : I ^ (0 + 1) = I := pow_one I
  have : (I ^ (0 + 1)).IsPrime := e.symm ▸ hR.2.2.2.1
  have : IsPrincipalIdealRing (R ⧸ I ^ (0 + 1)) := e.symm ▸ hP
  have amp : RelAmple (T.l 0).Q.B (T.l 0).D.M.L.L :=
    GlobalTheory.T.cubical_bundle_relAmple_of_ample_fibres hL hL2 (R ⧸ I ^ (0 + 1)) (isAdicComplete_quot hR.2.1 _) _ (T.l 0).Q.isAb (T.l 0).D.M
      fun k _ x => (hf k x).1
  obtain ⟨a⟩ := GlobalTheory.T.nonempty_algebraisation_formal_tower_ample hL hL2 hE R I hR G P X T amp
  have k₀ : KTriv (T.l 0).Q.B (T.l 0).D.M.L.L :=
    GlobalTheory.T.kTriv_of_closed_fibre_localRing hL hL2 (R ⧸ I ^ (0 + 1)) _ (T.l 0).Q.isAb _ (T.l 0).D.M.L.isLB amp (hf _ _).2
  obtain ⟨hb, v, hv⟩ := a.b_pb 0
  have hK : KTriv a.B a.M.L.L := GlobalTheory.T.kTriv_of_closed_fibre_localRing hL hL2 R _ a.isAb _ a.M.L.isLB a.ample
    (kTriv_closedFibre (e.symm ▸ hI) hb a.M.L.isLB (T.l 0).D.M.L.isLB hv.gen k₀)
  obtain ⟨c, hadd, hw⟩ := GlobalTheory.T.exists_additive_weightPoints_of_torusTower hL hL2 hE R I hR G P X T a hK
  exact exists_preU hL.globalFns (fun D e => GlobalTheory.T.torusCoordinates_compat_of_torus_compat hL.globalFns R I D e G) hI hs T a hK c hadd hw A gen hgen hA

end GlobalTheory.PreUnifLocal
end
