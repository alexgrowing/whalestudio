import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidTorsionOfDataRigid
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAffineOpenAndBijectiveOfWeightUnits
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThickenedPointToTorusExtensionGenerator

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace CoordToExt

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

theorem exists_iso (hL : L.IsLB) {φ φ' : K → (Y ⟶ X)} (h : φ = φ') (ε : K → ℤ) :
    ∃ w : LB.Iso (LB.LinComb L φ ε) (LB.LinComb L φ' ε), w.IsGen := by
  subst h
  refine ((refines_self φ ε).div (refines_self φ ε)).exists_gen hL (fun U _ f => ?_) _ isGen_one
  refine (Fintype.prod_empty _).trans (Eq.symm ((Fintype.prod_sum_type _).trans ?_))
  simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, mul_inv_cancel]

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

theorem exists_rig {G B T : Scheme.{0}} (q : G ⟶ B) (eG : T ⟶ G) (eB : T ⟶ B) (e : eG ≫ q = eB) (M : LB B)
    (s : ∀ a : M.ι, Γ(G, q ⁻¹ᵁ M.U a)ˣ)
    (hs : ∀ (Z : Scheme.{0}) (r : Z ⟶ G) (z : Z) (a a' : M.ι), q (r z) ∈ M.U a → q (r z) ∈ M.U a' →
      gm r z _ (s a') = gm (r ≫ q) z _ (M.g a a') * gm r z _ (s a)) :
    ∃ ρ : LB.Gen (M.pull eB), ρ.IsGen ∧ ∀ (a : M.ι) (y : T), q (eG y) ∈ M.U a →
      gm eG y _ (s a) * gm (𝟙 _) y _ (ρ.s fun _ => a) = 1 := by
  subst e
  have le : ∀ J : PUnit → M.ι, (M.pull (eG ≫ q)).U J ≤ eG ⁻¹ᵁ (q ⁻¹ᵁ M.U (J PUnit.unit)) :=
    fun J y hy => mem_pull₂.1 hy
  have v : ∀ (J : PUnit → M.ι) y, y ∈ (M.pull (eG ≫ q)).U J →
      gm (𝟙 T) y ((M.pull (eG ≫ q)).U J) (res (le J) (pullU eG _ (s (J PUnit.unit))))⁻¹ =
        (gm eG y _ (s (J PUnit.unit)))⁻¹ :=
    fun J y hy => (map_inv _ _).trans (congrArg (·⁻¹) ((gm_res _ y (le J) hy _).trans
      ((gm_pull _ eG y (q ⁻¹ᵁ M.U (J PUnit.unit)) (le J hy) _).trans (by rw [Category.id_comp]))))
  refine ⟨⟨fun J => (res (le J) (pullU eG _ (s (J PUnit.unit))))⁻¹⟩, fun J J' => unit_ext fun y hy => ?_,
    fun a y hy => ?_⟩
  · refine ((gm_res _ y _ hy _).trans (v J y hy.1)).trans (Eq.symm ?_)
    refine ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_pull_g M (eG ≫ q) (𝟙 _) y J J' hy.1 hy.2)
      ((gm_res _ y _ hy _).trans (v J' y hy.2)))).trans ?_
    rw [hs _ eG y _ _ (le J hy.1) (le J' hy.2), Category.id_comp, mul_inv, mul_inv_cancel_left]
  · exact (congrArg (_ * ·) (v (fun _ => a) y (mem_pull₂.2 hy))).trans (mul_inv_cancel _)

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

theorem prod_square {S : Scheme.{0}} {B T : Over S} [GrpObj B] (x : Fin 2 → (T ⟶ B)) {U : Type} [CommGroup U]
    (F : (T ⟶ B) → U) :
    ∏ J : ULift.{0} (Finset (Fin 2)), F (psum B x J.down) ^ ((-1 : ℤ) ^ (2 - J.down.card)) =
      F 1 * (F (x 0))⁻¹ * (F (x 1))⁻¹ * F (x 0 * x 1) := by
  refine (Fintype.prod_equiv Equiv.ulift _ (fun J => F (psum B x J) ^ ((-1 : ℤ) ^ (2 - J.card))) (fun _ => rfl)).trans ?_
  rw [show (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} by decide,
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_singleton]
  have p₀ : psum B x ∅ = 1 := rfl
  have p₁ : psum B x {0} = x 0 := _root_.mul_one (x 0)
  have p₂ : psum B x {1} = x 1 := _root_.mul_one (x 1)
  have p₃ : psum B x {0, 1} = x 0 * x 1 := congrArg (x 0 * ·) (_root_.mul_one (x 1))
  have q₀ : (-1 : ℤ) ^ (2 - (∅ : Finset (Fin 2)).card) = 1 := by decide
  have q₁ : ∀ i : Fin 2, (-1 : ℤ) ^ (2 - ({i} : Finset (Fin 2)).card) = -1 := by decide
  have q₃ : (-1 : ℤ) ^ (2 - ({0, 1} : Finset (Fin 2)).card) = 1 := by decide
  rw [p₀, p₁, p₂, p₃, q₀, q₁, q₁, q₃]
  simp only [zpow_neg, zpow_one, _root_.mul_assoc]

section Data

variable {R : Type} [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (e : ℕ)

theorem prod_O {T : Over (Spec (CommRingCat.of R))} (p : T ⟶ D.P.A) (χ : D.X) {U : Type} [CommGroup U]
    (h : (T.left ⟶ D.P.A.left) → U) :
    ∏ k, h (D.Oφ p χ k) ^ Oε k = h ((toUnit T ≫ D.c χ) * p).left * (h (toUnit T ≫ D.c χ).left)⁻¹ * (h p.left)⁻¹ *
      h (1 : T ⟶ D.P.A).left := by
  rw [Fin.prod_univ_four, _root_.mul_comm (toUnit T ≫ D.c χ) p]
  change h (p * (toUnit T ≫ D.c χ)).left ^ (1 : ℤ) * h (toUnit T ≫ D.c χ).left ^ (-1 : ℤ) * h p.left ^ (-1 : ℤ) *
    h (1 : T ⟶ D.P.A).left ^ (1 : ℤ) = _
  simp only [zpow_neg, zpow_one]

theorem c_add (T : Over (Spec (CommRingCat.of R))) (χ χ' : D.X) :
    toUnit T ≫ D.c (χ + χ') = (toUnit T ≫ D.c χ) * (toUnit T ≫ D.c χ') := by
  rw [D.c_add]
  exact MonObj.comp_mul _ _ _

theorem c_zero (T : Over (Spec (CommRingCat.of R))) : toUnit T ≫ D.c 0 = 1 := by
  have h := c_add D T 0 0
  rw [add_zero] at h
  exact mul_eq_left.1 h.symm

abbrev bundle (χ : D.X) : LB (thickObj R I e D.P.A).left :=
  LB.LinComb D.P.L (Y := (thickObj R I e D.P.A).left) (D.Oφ (D.prBe I e) χ) Oε

theorem bundle_add (χ χ' : D.X) :
    ∃ t : LB.Iso (bundle I D e χ') (LB.div (bundle I D e (χ + χ')) (bundle I D e χ)), t.IsGen := by
  refine (((refines_self _ _).div (refines_self _ _)).div (refines_self _ _)).exists_gen D.P.isLB (fun U _ h => ?_)
    _ (DVR.pullGen_isGen _ _ _ _ D.cub.isGen (lift (toUnit _ ≫ D.c χ) (lift (toUnit _ ≫ D.c χ') (D.prBe I e))).left)
  refine (prod_cub (toUnit _ ≫ D.c χ) (toUnit _ ≫ D.c χ') (D.prBe I e) h).trans (Eq.symm ?_)
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
  refine (congrArg₂ (· * ·) (congrArg₂ (· * ·) (prod_O D (D.prBe I e) _ h) (congrArg (·⁻¹) (prod_O D (D.prBe I e) _ h)))
    (congrArg (·⁻¹) (prod_O D (D.prBe I e) _ h))).trans ?_
  rw [c_add]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem bundle_zero : ∃ t : LB.Gen (bundle I D e 0), t.IsGen := by
  refine (refines_self _ _).exists_gen D.P.isLB (fun U _ h => ?_) _ isGen_one
  refine (Fintype.prod_empty _).trans (Eq.symm ((prod_O D (D.prBe I e) _ h).trans ?_))
  rw [c_zero, _root_.one_mul]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_one]
  abel

theorem bundle_primitive (χ : D.X) : ∃ t : LB.Gen (abelian₂ (thickObj R I e D.P.A) (bundle I D e χ)), t.IsGen := by
  let ρ := pushHom (isGrpPullback_pullback D.P.A (thick R I e)) (G2 (thickObj R I e D.P.A))
  have hρ : ∀ (x : G2 (thickObj R I e D.P.A) ⟶ thickObj R I e D.P.A) k,
      x.left ≫ D.Oφ (D.prBe I e) χ k = D.Oφ (ρ x) χ k := fun x k =>
    WeightPf.Oφ_comp (T' := Over.mk ((G2 (thickObj R I e D.P.A)).hom ≫ thick R I e))
      ((Over.map (thick R I e)).map x) (D.prBe I e) χ k
  refine ((refines_self _ _).linComb _ _).exists_gen D.P.isLB (fun U _ h => ?_)
    _ (DVR.pullGen_isGen _ _ _ _ D.cub.isGen (lift (toUnit _ ≫ D.c χ) (lift (ρ (x2 _ 0)) (ρ (x2 _ 1)))).left)
  refine (prod_cub (toUnit _ ≫ D.c χ) (ρ (x2 _ 0)) (ρ (x2 _ 1)) h).trans (Eq.symm ?_)
  rw [Fintype.prod_prod_type]
  simp only [zpow_mul, Finset.prod_zpow, hρ]
  refine (prod_square (x2 (thickObj R I e D.P.A)) (fun x => ∏ k, h (D.Oφ (ρ x) χ k) ^ Oε k)).trans ?_
  refine (congrArg₂ (· * ·) (congrArg₂ (· * ·) (congrArg₂ (· * ·) (prod_O D (ρ _) _ h) (congrArg (·⁻¹) (prod_O D (ρ _) _ h)))
    (congrArg (·⁻¹) (prod_O D (ρ _) _ h))) (prod_O D (ρ _) _ h)).trans ?_
  rw [map_one, map_mul, _root_.mul_one, ← _root_.mul_assoc (toUnit _ ≫ D.c χ)]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem isAbelianScheme_thick : IsAbelianScheme (thickObj R I e D.P.A) :=
  { comm := inferInstance
    smooth := by have := D.P.isAb.smooth; show Smooth (pullback.snd _ _); infer_instance
    proper := by have := D.P.isAb.proper; show IsProper (pullback.snd _ _); infer_instance
    geomConnected := by
      have := D.P.isAb.geomConnected; show GeometricallyConnected (pullback.snd _ _); infer_instance }

variable {I D e} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G)

theorem q_Oφ (χ : D.X) (k : Fin 4) : g.q.left ≫ D.Oφ (D.prBe I e) χ k = D.Oφ g.pG χ k :=
  WeightPf.Oφ_comp ((Over.map (thick R I e)).map g.q) (D.prBe I e) χ k

theorem mem_chart (χ : D.X) (a : Fin 4 → D.P.L.ι) (y : (thickObj R I e G).left)
    (hy : g.q.left y ∈ (bundle I D e χ).U a) : y ∈ LB.wchart D.P.L (D.Oφ g.pG χ) a :=
  Set.mem_iInter.2 fun k => (congrArg (fun f => f y ∈ D.P.L.U (a k)) (q_Oφ g χ k)).mp (Set.mem_iInter.1 hy k)

def coordUnit (χ : D.X) (a : (bundle I D e χ).ι) : Γ((thickObj R I e G).left, g.q.left ⁻¹ᵁ (bundle I D e χ).U a)ˣ :=
  res (fun y hy => mem_chart g χ a y hy) ((g.t χ).s a)

theorem gm_coordUnit (χ : D.X) (a : (bundle I D e χ).ι) {Z : Scheme.{0}} (r : Z ⟶ (thickObj R I e G).left) (z : Z)
    (h : g.q.left (r z) ∈ (bundle I D e χ).U a) :
    gm r z _ (coordUnit g χ a) = gm r z (LB.wchart D.P.L (D.Oφ g.pG χ) a) ((g.t χ).s a) :=
  gm_res r z (V := g.q.left ⁻¹ᵁ (bundle I D e χ).U a) _ h _

theorem coordUnit_trans (χ : D.X) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z)
    (a a' : (bundle I D e χ).ι) (h : g.q.left (r z) ∈ (bundle I D e χ).U a)
    (h' : g.q.left (r z) ∈ (bundle I D e χ).U a') :
    gm r z _ (coordUnit g χ a') = gm (r ≫ g.q.left) z _ ((bundle I D e χ).g a a') * gm r z _ (coordUnit g χ a) := by
  have e₁ := gen_trans (g.t_gen χ) r z (mem_chart g χ a _ h) (mem_chart g χ a' _ h')
  have e₂ := gm_linComb D.P.L (Y := (thickObj R I e D.P.A).left) (D.Oφ (D.prBe I e) χ) Oε (r ≫ g.q.left) z a a' h h'
  have e₃ : (∏ k, gm ((r ≫ g.q.left) ≫ D.Oφ (D.prBe I e) χ k) z (D.P.L.U (a k) ⊓ D.P.L.U (a' k))
      (D.P.L.g (a k) (a' k)) ^ Oε k) * trF (D.Oφ g.pG χ) Oinvε r z a a' = 1 := by
    refine Finset.prod_mul_distrib.symm.trans (Finset.prod_eq_one fun k _ => ?_)
    have hk : Oinvε k = - Oε k := by revert k; decide
    have hq : (r ≫ g.q.left) ≫ D.Oφ (D.prBe I e) χ k = r ≫ D.Oφ g.pG χ k :=
      (Category.assoc _ _ _).trans (congrArg (r ≫ ·) (q_Oφ g χ k))
    rw [hk, zpow_neg]
    exact (congrArg (fun f => gm f z (D.P.L.U (a k) ⊓ D.P.L.U (a' k)) (D.P.L.g (a k) (a' k)) ^ Oε k * _) hq).trans
      (mul_inv_cancel _)
  refine (gm_coordUnit g χ a' r z h').trans (Eq.symm ((congrArg₂ (· * ·) e₂ ((gm_coordUnit g χ a r z h).trans e₁)).trans ?_))
  exact (_root_.mul_assoc _ _ _).symm.trans ((congrArg (· * _) e₃).trans (_root_.one_mul _))

theorem coordUnit_weight (χ : D.X) (a : (bundle I D e χ).ι) (Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))
    (t : Z ⟶ splitTorus _ D.X) (y : Z ⟶ thickObj R I e G) (z : Z.left)
    (h : g.q.left (y.left z) ∈ (bundle I D e χ).U a) :
    gm ((t ≫ g.i) * y).left z _ (coordUnit g χ a) =
      gm t.left z ⊤ (charUnit _ D.X χ) * gm y.left z _ (coordUnit g χ a) := by
  have := g.q_hom
  have e₀ : ((t ≫ g.i) * y) ≫ g.q = y ≫ g.q := by
    rw [MonObj.mul_comp, Category.assoc, g.isKernel.w, ← Category.assoc, comp_toUnit, ← Hom.one_def, _root_.one_mul]
  have e₁ : ((t ≫ g.i) * y).left ≫ g.q.left = y.left ≫ g.q.left := congrArg (fun f => f.left) e₀
  have h' : g.q.left (((t ≫ g.i) * y).left z) ∈ (bundle I D e χ).U a :=
    (congrArg (fun f => f z ∈ (bundle I D e χ).U a) e₁).mpr h
  have e₂ : ∀ k, ((t ≫ g.i) * y).left ≫ D.Oφ g.pG χ k = y.left ≫ D.Oφ g.pG χ k := fun k => by
    rw [← q_Oφ]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) e₁).trans (Category.assoc _ _ _))
  obtain ⟨J, hJ⟩ := TorusCoord.exists_good' D.P.isLB z
  have v := TorusCoord.val_t_act g t y χ (𝟙 _) z J hJ
  have c : splitTorusPointsEquiv _ D.X Z t (Multiplicative.ofAdd χ) = pullU t.left ⊤ (charUnit _ D.X χ) :=
    Units.ext (splitTorusPointsEquiv_val _ _ _ t χ)
  have c' := gm_pull (𝟙 _) t.left z ⊤ trivial (charUnit _ D.X χ)
  rw [Category.id_comp] at c'
  rw [Category.id_comp, Category.id_comp, c] at v
  have v' := v.trans (congrArg (· * _) c')
  have t₁ := gen_trans (g.t_gen χ) _ z (mem_chart g χ a _ h') (hJ.mem _ ((t ≫ g.i) * y).left)
  have t₂ := gen_trans (g.t_gen χ) _ z (mem_chart g χ a _ h) (hJ.mem _ y.left)
  have t₃ : trF (D.Oφ g.pG χ) Oinvε ((t ≫ g.i) * y).left z a (fun k => J (((t ≫ g.i) * y).left ≫ D.Oφ g.pG χ k)) =
      trF (D.Oφ g.pG χ) Oinvε y.left z a (fun k => J (y.left ≫ D.Oφ g.pG χ k)) :=
    Finset.prod_congr rfl fun k _ => congrArg
      (fun f => gm f z (D.P.L.U (a k) ⊓ D.P.L.U (J f)) (D.P.L.g (a k) (J f)) ^ Oinvε k) (e₂ k)
  refine ((gm_coordUnit g χ a _ z h').trans (t₁.trans (congrArg₂ (· * ·) t₃ v'))).trans (Eq.symm ?_)
  exact (congrArg (_ * ·) ((gm_coordUnit g χ a _ z h).trans t₂)).trans (mul_left_comm _ _ _)

end Data

end CoordToExt

open CoordToExt in

theorem gtCoord_isGt : Geo.Tor.GtCoordToGtSt := by
  rintro R _ _ I D e G _ _ ⟨g⟩
  have := g.q_hom
  have he : eSec (thickObj R I e G) ≫ g.q.left = eSec (thickObj R I e D.P.A) :=
    congrArg (fun f => f.left) (IsMonHom.one_hom g.q)
  choose ρ hρ hρ' using fun χ => exists_rig g.q.left _ _ he (bundle I D e χ) (coordUnit g χ) (coordUnit_trans g χ)
  let E : SplitExt (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) :=
    { B := thickObj R I e D.P.A
      isAbelian := isAbelianScheme_thick I D e
      X := D.X
      O := fun χ => ⟨bundle I D e χ, ρ χ, DVR.linComb_isLB _ D.P.isLB _ _, hρ χ⟩
      addIso := bundle_add I D e
      zeroTriv := bundle_zero I D e
      primitive := bundle_primitive I D e }
  refine ⟨E, Iso.refl _, AddEquiv.refl _, inferInstanceAs (IsMonHom (𝟙 (thickObj R I e D.P.A))), fun χ => ?_, ?_⟩
  · refine exists_iso D.P.isLB (funext fun k => ?_) Oε
    refine Eq.trans ?_ (WeightPf.Oφ_comp ((Over.map (thick R I e)).map (𝟙 (thickObj R I e D.P.A)) ≫ D.prBe I e) (𝟙 _) χ k).symm
    rw [Category.comp_id]
    exact congrArg (D.Oφ · χ k) (((congrArg (· ≫ _) ((Over.map (thick R I e)).map_id _)).trans (Category.id_comp _)).symm)
  · exact isGt_of_units E g.q g.i g.q_hom g.i_hom g.q_flat g.q_surj g.q_affine g.isKernel (coordUnit g)
      (coordUnit_trans g) (coordUnit_weight g) hρ'

end GlobalTheory
