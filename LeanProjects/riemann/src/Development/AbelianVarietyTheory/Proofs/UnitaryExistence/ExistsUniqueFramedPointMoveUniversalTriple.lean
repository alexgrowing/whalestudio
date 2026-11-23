import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.NormsFree
import Formalism.LocalToGlobal.ProjectiveLattices.RegPFree
import Formalism.LocalToGlobal.ProjectiveLattices.RegQFree
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.ProjectiveLattices.LiftLaSpec
import Formalism.LocalToGlobal.ProjectiveLattices.IsGenFrGenFr
import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import Formalism.LocalToGlobal.ProjectiveLattices.IsLevMove
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsoEqOfMapsAlongSection
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelMapFibreSimplyTransitive
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.CubeMapTripleProductUnique
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.CarriedGeneratorUnique

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FrameMove

section Bundle

variable {X X' Y Y' : Scheme.{0}} {L : LB X} {L' : LB X'}

abbrev pullOne (L : LB X) (p : Y ⟶ X) : LB Y := LB.LinComb L (K := Fin 1) (fun _ => p) (fun _ => 1)

theorem mem_pullOne {p : Y ⟶ X} {y : Y} {j : L.ι} : y ∈ (pullOne L p).U (fun _ => j) ↔ p y ∈ L.U j :=
  ⟨fun h => Set.mem_iInter.1 h 0, fun h => Set.mem_iInter.2 fun _ => h⟩

theorem idx_eq (J : Fin 1 → L.ι) : J = fun _ => J 0 := funext fun k => congrArg J (Subsingleton.elim _ _)

theorem sec_trans_one {Z : Scheme.{0}} {p : Y ⟶ X} (s : LB.Sec (pullOne L p)) (r : Z ⟶ Y) (z : Z) {j j' : L.ι}
    (hj : p (r z) ∈ L.U j) (hj' : p (r z) ∈ L.U j') :
    gs r z ((pullOne L p).U (fun _ => j)) (s.f (fun _ => j)) =
      (gm (r ≫ p) z _ (L.g j j')).val * gs r z ((pullOne L p).U (fun _ => j')) (s.f (fun _ => j')) := by
  have := sec_trans s r z (j := fun _ => j) (j' := fun _ => j') (mem_pullOne.2 hj) (mem_pullOne.2 hj')
  rw [trF, Fin.prod_univ_one, zpow_one] at this
  exact this

theorem exists_carry (hL : L.IsLB) (hL' : L'.IsLB) (p : Y ⟶ X) (p' : Y' ⟶ X') (q : Y ⟶ Y')
    (U : ∀ j i, Γ(Y, p ⁻¹ᵁ L.U j ⊓ q ⁻¹ᵁ p' ⁻¹ᵁ L'.U i)ˣ)
    (hU : ∀ (y : Y) j j' i i', p y ∈ L.U j → p y ∈ L.U j' → p' (q y) ∈ L'.U i → p' (q y) ∈ L'.U i' →
      gm (𝟙 Y) y _ (U j i) = gm p y _ (L.g j j') * (gm (q ≫ p') y _ (L'.g i i'))⁻¹ * gm (𝟙 Y) y _ (U j' i'))
    (s' : LB.Sec (pullOne L' p')) :
    ∃ s : LB.Sec (pullOne L p), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) j i, p (r z) ∈ L.U j → p' (q (r z)) ∈ L'.U i →
      gs r z ((pullOne L p).U (fun _ => j)) (s.f (fun _ => j)) =
        (gm r z _ (U j i)).val * gs (r ≫ q) z ((pullOne L' p').U (fun _ => i)) (s'.f (fun _ => i)) := by
  have glue : ∀ j : L.ι, ∃ a : Γ(Y, (pullOne L p).U (fun _ => j)), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) i,
      p (r z) ∈ L.U j → p' (q (r z)) ∈ L'.U i → gs r z _ a =
        (gm r z _ (U j i)).val * gs (r ≫ q) z ((pullOne L' p').U (fun _ => i)) (s'.f (fun _ => i)) := by
    intro j
    have le : ∀ i, p ⁻¹ᵁ L.U j ⊓ q ⁻¹ᵁ p' ⁻¹ᵁ L'.U i ≤ q ⁻¹ᵁ (pullOne L' p').U (fun _ => i) :=
      fun i y hy => mem_pullOne.2 hy.2
    have le' : ∀ i, p ⁻¹ᵁ L.U j ⊓ q ⁻¹ᵁ p' ⁻¹ᵁ L'.U i ≤ (pullOne L p).U (fun _ => j) :=
      fun i y hy => mem_pullOne.2 hy.1
    obtain ⟨u, hu⟩ : ∃ u : ∀ i, Γ(Y, p ⁻¹ᵁ L.U j ⊓ q ⁻¹ᵁ p' ⁻¹ᵁ L'.U i), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) i,
        r z ∈ p ⁻¹ᵁ L.U j ⊓ q ⁻¹ᵁ p' ⁻¹ᵁ L'.U i → gs r z _ (u i) =
          (gm r z _ (U j i)).val * gs (r ≫ q) z ((pullOne L' p').U (fun _ => i)) (s'.f (fun _ => i)) :=
      ⟨fun i => (U j i).val * (q.appLE _ _ (le i)).hom (s'.f (fun _ => i)), fun Z r z i hz =>
        (gs_mul r z _ hz _ _).trans (congrArg₂ (· * ·) (gs_unit r z _ hz _) (gs_appLE q _ _ (le i) r z hz _))⟩
    obtain ⟨a, ha, -⟩ := Y.sheaf.existsUnique_gluing' (fun i => p ⁻¹ᵁ L.U j ⊓ q ⁻¹ᵁ p' ⁻¹ᵁ L'.U i)
      ((pullOne L p).U (fun _ => j)) (fun i => homOfLE (le' i)) (fun y hy => by
        obtain ⟨k, hk⟩ := exists_chart hL' (p' (q y))
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, mem_pullOne.1 hy, hk⟩) u
      (fun k k' => fn_ext (V := (p ⁻¹ᵁ L.U j ⊓ q ⁻¹ᵁ p' ⁻¹ᵁ L'.U k) ⊓ (p ⁻¹ᵁ L.U j ⊓ q ⁻¹ᵁ p' ⁻¹ᵁ L'.U k'))
        fun y hy => by
        refine (gs_res (𝟙 Y) y inf_le_left hy _).trans (Eq.trans ?_ (gs_res (𝟙 Y) y inf_le_right hy _).symm)
        have hj : p y ∈ L.U j := hy.1.1
        rw [hu _ _ y k hy.1, hu _ _ y k' hy.2, Category.id_comp, sec_trans_one s' q y hy.1.2 hy.2.2,
          hU y j j k k' hj hj hy.1.2 hy.2.2, gm_self hL p y hj,
          _root_.one_mul, Units.val_mul, _root_.mul_assoc, mul_left_comm (gm (𝟙 Y) y _ (U j k')).val,
          Units.inv_mul_cancel_left])
    refine ⟨a, fun Z r z k h₁ h₂ => ?_⟩
    have hz : r z ∈ p ⁻¹ᵁ L.U j ⊓ q ⁻¹ᵁ p' ⁻¹ᵁ L'.U k := ⟨h₁, h₂⟩
    exact (gs_res r z (le' k) hz a).symm.trans ((congrArg (gs r z _) (ha k)).trans (hu Z r z k hz))
  choose a ha using glue
  obtain ⟨b, hb⟩ : ∃ b : ∀ J : Fin 1 → L.ι, Γ(Y, (pullOne L p).U J), ∀ j, b (fun _ => j) = a j :=
    ⟨fun J => (Y.presheaf.map (eqToHom (congrArg (pullOne L p).U (idx_eq J))).op).hom (a (J 0)), fun j => by simp⟩
  refine ⟨⟨b, fun (J J' : Fin 1 → L.ι) => ?_⟩, fun Z r z j i h₁ h₂ => (congrArg _ (hb j)).trans (ha j Z r z i h₁ h₂)⟩
  rw [idx_eq J, idx_eq J']
  generalize J 0 = j
  generalize J' 0 = j'
  refine fn_ext fun y hy => ?_
  obtain ⟨k, hk⟩ := exists_chart hL' (p' (q y))
  have hj : p y ∈ L.U j := mem_pullOne.1 hy.1
  have hj' : p y ∈ L.U j' := mem_pullOne.1 hy.2
  have g : gm (𝟙 Y) y _ ((pullOne L p).g (fun _ => j) (fun _ => j')) = gm p y _ (L.g j j') :=
    (gm_linComb L _ _ (𝟙 Y) y _ _ hy.1 hy.2).trans (by rw [Fin.prod_univ_one, zpow_one, Category.id_comp])
  rw [gs_res _ y _ hy, gs_mul _ y _ hy, gs_res _ y _ hy, gs_unit _ y _ hy, g, hb, hb,
    ha j _ (𝟙 Y) y k hj hk, ha j' _ (𝟙 Y) y k hj' hk, hU y j j' k k hj hj' hk hk, gm_self hL' (q ≫ p') y hk,
    inv_one, _root_.mul_one, Units.val_mul, _root_.mul_assoc]

variable {F : X' ⟶ X} {p : Y ⟶ X} {p' : Y' ⟶ X'} {pm : Y' ⟶ Y}

def Carried (w : LB.Iso L' (L.pull F)) (pm : Y' ⟶ Y) (t : LB.Sec (pullOne L' p')) (σ : LB.Sec (pullOne L p)) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (j : L.ι) (i : L'.ι), F (p' (r z)) ∈ L.U j → p' (r z) ∈ L'.U i →
    gs (r ≫ pm) z ((pullOne L p).U (fun _ => j)) (σ.f (fun _ => j)) =
      (gw w (r ≫ p') z j i).val * gs r z ((pullOne L' p').U (fun _ => i)) (t.f (fun _ => i))

theorem exists_carried_back (hL : L.IsLB) (hL' : L'.IsLB) {w : LB.Iso L' (L.pull F)} (hw : PGen w)
    (h : pm ≫ p = p' ≫ F) (σ : LB.Sec (pullOne L p)) : ∃ t : LB.Sec (pullOne L' p'), Carried w pm t σ := by
  have e : ∀ y, p (pm y) = F (p' y) := fun y => congrArg (fun g => g y) h
  have le : ∀ i j, p' ⁻¹ᵁ L'.U i ⊓ pm ⁻¹ᵁ p ⁻¹ᵁ L.U j ≤ p' ⁻¹ᵁ ((L.pull F).U (fun _ => j) ⊓ L'.U i) :=
    fun i j y hy => ⟨mem_pull.2 (e y ▸ hy.2), hy.1⟩
  have k : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) i j, p' (r z) ∈ L'.U i → p (pm (r z)) ∈ L.U j →
      gm r z _ (res (le i j) (pullU p' _ (w.s (fun _ => j, i))))⁻¹ = (gw w (r ≫ p') z j i)⁻¹ :=
    fun Z r z i j hi hj => (map_inv _ _).trans (congrArg (·⁻¹)
      ((gm_res r z (le i j) ⟨hi, hj⟩ _).trans (gm_pull r p' z _ (le i j ⟨hi, hj⟩) _)))
  obtain ⟨t, ht⟩ := exists_carry hL' hL p' p pm (fun i j => (res (le i j) (pullU p' _ (w.s (fun _ => j, i))))⁻¹)
    (fun y i i' j j' hi hi' hj hj' => by
      rw [k _ _ y i j hi hj, k _ _ y i' j' hi' hj', Category.id_comp, h,
        hw _ p' y j j' i i' (e y ▸ hj) (e y ▸ hj') hi hi', mul_inv, mul_inv, inv_inv, _root_.mul_comm (_ : (Y'.presheaf.stalk y)ˣ)⁻¹]) σ
  refine ⟨t, fun Z r z j i hj hi => ?_⟩
  rw [ht Z r z i j hi ((e _).symm ▸ hj), k Z r z i j hi ((e _).symm ▸ hj), Units.mul_inv_cancel_left]

theorem exists_carried_forth (hL : L.IsLB) (hL' : L'.IsLB) {w : LB.Iso L' (L.pull F)} (hw : PGen w) [hi : IsIso pm]
    (h : pm ≫ p = p' ≫ F) (t : LB.Sec (pullOne L' p')) : ∃ σ : LB.Sec (pullOne L p), Carried w pm t σ := by
  obtain ⟨q, q₁, q₂⟩ := hi.out
  have h' : p = (q ≫ p') ≫ F := by rw [Category.assoc, ← h, ← Category.assoc, q₂, Category.id_comp]
  have e : ∀ y, p y = F (p' (q y)) := fun y => congrArg (fun g => g y) h'
  have le : ∀ j i, p ⁻¹ᵁ L.U j ⊓ q ⁻¹ᵁ p' ⁻¹ᵁ L'.U i ≤ (q ≫ p') ⁻¹ᵁ ((L.pull F).U (fun _ => j) ⊓ L'.U i) :=
    fun j i y hy => ⟨mem_pull.2 (show F (p' (q y)) ∈ _ from e y ▸ hy.1), hy.2⟩
  have k : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) j i, p (r z) ∈ L.U j → p' (q (r z)) ∈ L'.U i →
      gm r z _ (res (le j i) (pullU (q ≫ p') _ (w.s (fun _ => j, i)))) = gw w (r ≫ q ≫ p') z j i :=
    fun Z r z j i hj hi => by
      have m : r z ∈ p ⁻¹ᵁ L.U j ⊓ q ⁻¹ᵁ p' ⁻¹ᵁ L'.U i := ⟨hj, hi⟩
      exact (gm_res r z (le j i) m _).trans (gm_pull r (q ≫ p') z _ (le j i m) _)
  obtain ⟨σ, hσ⟩ := exists_carry hL hL' p p' q
    (fun j i => res (le j i) (pullU (q ≫ p') _ (w.s (fun _ => j, i))))
    (fun y j j' i i' hj hj' hi hi' => by
      rw [k _ _ y j i hj hi, k _ _ y j' i' hj' hi', Category.id_comp,
        hw _ (q ≫ p') y j j' i i' (show F (p' (q y)) ∈ _ from e y ▸ hj)
          (show F (p' (q y)) ∈ _ from e y ▸ hj') hi hi', ← h']) t
  refine ⟨σ, fun Z r z j i hj hi => ?_⟩
  have e₁ : q (pm (r z)) = r z := congrArg (fun g => g (r z)) q₁
  have hj' : p ((r ≫ pm) z) ∈ L.U j := by
    show p (pm (r z)) ∈ _
    rw [e, e₁]; exact hj
  have hi' : p' (q ((r ≫ pm) z)) ∈ L'.U i := by
    show p' (q (pm (r z))) ∈ _
    rw [e₁]; exact hi
  have e₂ : (r ≫ pm) ≫ q = r := by rw [Category.assoc, q₁, Category.comp_id]
  rw [hσ Z (r ≫ pm) z j i hj' hi', k Z (r ≫ pm) z j i hj' hi', ← Category.assoc, e₂]

theorem Carried.mul_iff (hL : L.IsLB) (hL' : L'.IsLB) {w : LB.Iso L' (L.pull F)} [IsIso pm]
    (h : pm ≫ p = p' ≫ F) {t t₀ : LB.Sec (pullOne L' p')} {σ σ₀ : LB.Sec (pullOne L p)}
    (c : Carried w pm t σ) (c₀ : Carried w pm t₀ σ₀) {B : Scheme.{0}} {π : Y ⟶ B} {π' : Y' ⟶ B} (hπ : pm ≫ π = π')
    (a : Γ(B, ⊤)) :
    (∀ J, σ.f J = (Y.presheaf.map (homOfLE le_top).op).hom (π.appTop.hom a) * σ₀.f J) ↔
      ∀ I, t.f I = (Y'.presheaf.map (homOfLE le_top).op).hom (π'.appTop.hom a) * t₀.f I := by
  have k : ∀ {Y₁ : Scheme.{0}} (π₁ : Y₁ ⟶ B) (V : Y₁.Opens) (f : Γ(Y₁, V)) (Z : Scheme.{0}) (r : Z ⟶ Y₁) (z : Z),
      r z ∈ V → gs r z V ((Y₁.presheaf.map (homOfLE le_top).op).hom (π₁.appTop.hom a) * f) =
        gs (r ≫ π₁) z ⊤ a * gs r z V f := fun π₁ V f Z r z hz =>
    (gs_mul r z V hz _ _).trans (congrArg (· * _) ((gs_res r z le_top hz _).trans (gs_pull r π₁ z ⊤ trivial a)))
  have e : ∀ y, p (pm y) = F (p' y) := fun y => congrArg (fun g => g y) h
  constructor
  · intro H I
    rw [idx_eq I]
    generalize I 0 = i
    refine fn_ext fun y hy => ?_
    obtain ⟨j, hj⟩ := exists_chart hL (F (p' y))
    have hi := mem_pullOne.1 hy
    have m : (𝟙 Y' ≫ pm) y ∈ (pullOne L p).U (fun _ => j) := mem_pullOne.2 (show p (pm y) ∈ _ from (e y).symm ▸ hj)
    have a₁ := c _ (𝟙 Y') y j i hj hi
    rw [H (fun _ => j), k π _ _ _ _ y m, c₀ _ (𝟙 Y') y j i hj hi, mul_left_comm, Category.assoc, hπ] at a₁
    rw [k π' _ _ _ _ y hy]
    exact ((Units.mul_right_inj _).1 a₁).symm
  · intro H J
    rw [idx_eq J]
    generalize J 0 = j
    refine fn_ext fun y hy => ?_
    obtain ⟨i, hi⟩ := exists_chart hL' (p' (inv pm y))
    have e₁ : pm (inv pm y) = y := congrArg (fun g => g y) (IsIso.inv_hom_id pm)
    have hj : F (p' (inv pm y)) ∈ L.U j := by rw [← e, e₁]; exact mem_pullOne.1 hy
    have a₁ := c _ (inv pm) y j i hj hi
    have a₀ := c₀ _ (inv pm) y j i hj hi
    rw [IsIso.inv_hom_id] at a₁ a₀
    rw [k π _ _ _ _ y hy, a₁, a₀, H (fun _ => i), k π' _ _ _ _ y (mem_pullOne.2 hi), mul_left_comm, ← hπ,
      IsIso.inv_hom_id_assoc, Category.id_comp]

end Bundle

section Tangent

theorem eps_alg {S : Type} [CommRing S] (a : S) :
    spMap (epsMul a) ≫ spMap (algebraMap S (DualNumber S)) = spMap (algebraMap S (DualNumber S)) := by
  rw [← Geo.Tor.spMap_comp]
  congr 1
  exact RingHom.ext fun x => by ext <;> simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl]

theorem fst_alg {S : Type} [CommRing S] :
    spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ spMap (algebraMap S (DualNumber S)) = 𝟙 (Sp S) := by
  rw [← Geo.Tor.spMap_comp, ← LevelFibre.spMap_id']
  exact congrArg spMap (RingHom.ext fun x => by simp [TrivSqZeroExt.algebraMap_eq_inl])

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {ρ : Xo.X ⟶ Xo.X} (ν : SABMap Xo.univ.t Xo.univ.t ρ)
  {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X}

theorem one_left_comp : (1 : Over.mk x ⟶ Xo.univ.t.G).left ≫ ν.φ = (1 : Over.mk (x ≫ ρ) ⟶ Xo.univ.t.G).left := by
  obtain ⟨e, he⟩ := LevelFibre.exists_ptEquiv ν.cart x (x ≫ ρ) rfl
  rw [← map_one e]
  exact (he 1).symm

theorem isTanAt_push {v : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (h : IsTanAt x v) : IsTanAt (x ≫ ρ) (v ≫ ν.φ) :=
  ⟨by rw [Category.assoc, ν.cart.1.w, ← Category.assoc, h.1, Category.assoc],
    by rw [← Category.assoc, h.2]; exact one_left_comp ν⟩

theorem exists_isTanAt {w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (h : IsTanAt (x ≫ ρ) w) :
    ∃ v, IsTanAt x v ∧ w = v ≫ ν.φ := by
  have hw : w ≫ Xo.univ.t.G.hom = (spMap (algebraMap S (DualNumber S)) ≫ x) ≫ ρ := h.1.trans (Category.assoc _ _ _).symm
  refine ⟨ν.cart.1.lift _ _ hw, ⟨ν.cart.1.lift_snd _ _ _, ν.cart.1.hom_ext ?_ ?_⟩, (ν.cart.1.lift_fst _ _ _).symm⟩
  · rw [Category.assoc, ν.cart.1.lift_fst, h.2]
    exact (one_left_comp ν).symm
  · rw [Category.assoc, ν.cart.1.lift_snd, ← Category.assoc, fst_alg, Category.id_comp]
    exact (Over.w (1 : Over.mk x ⟶ Xo.univ.t.G)).symm

theorem isEigAt_iff [Algebra c.F S] (τ : E →+* ℂ) {v : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (h : IsTanAt x v) :
    IsEigAt c τ (v ≫ ν.φ) ↔ IsEigAt c τ v := by
  refine forall_congr' fun a => ⟨fun k => ν.cart.1.hom_ext ?_ ?_, fun k => ?_⟩
  · rw [Category.assoc, ν.act, ← Category.assoc, Category.assoc _ v]
    exact k
  · rw [Category.assoc, Over.w, Category.assoc, h.1, ← Category.assoc, eps_alg]
  · rw [Category.assoc, ← ν.act, ← Category.assoc, k, Category.assoc]

theorem isCombAt_iff {m : ℕ} {v : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)} (hv : ∀ i, IsTanAt x (v i))
    (a : Fin m → S) {w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (hw : IsTanAt x w) :
    IsCombAt (x ≫ ρ) (fun i => v i ≫ ν.φ) a (w ≫ ν.φ) ↔ IsCombAt x v a w := by
  obtain ⟨e, he⟩ := LevelFibre.exists_ptEquiv ν.cart (spMap (algebraMap S (DualNumber S)) ≫ x)
    (spMap (algebraMap S (DualNumber S)) ≫ x ≫ ρ) (Category.assoc _ _ _)
  have hp : ∀ u : Fin m → (tEps x ⟶ Xo.univ.t.G),
      (List.ofFn fun i => e (u i)).prod.left = (List.ofFn u).prod.left ≫ ν.φ := fun u => by
    refine Eq.trans ?_ (he _)
    rw [map_list_prod, List.map_ofFn]
    rfl
  constructor
  · rintro ⟨u', h₁, h₂⟩
    obtain ⟨u, rfl⟩ : ∃ u : Fin m → (tEps x ⟶ Xo.univ.t.G), u' = fun i => e (u i) :=
      ⟨fun i => e.symm (u' i), funext fun i => (e.apply_symm_apply _).symm⟩
    refine ⟨u, fun i => ν.cart.1.hom_ext ?_ ?_, ν.cart.1.hom_ext ((hp u).symm.trans h₂) ?_⟩
    · exact (he _).symm.trans ((h₁ i).trans (Category.assoc _ _ _).symm)
    · refine (Over.w (u i)).trans ?_
      rw [Category.assoc, (hv i).1, ← Category.assoc, eps_alg]
      rfl
    · exact (Over.w _).trans hw.1.symm
  · rintro ⟨u, h₁, h₂⟩
    refine ⟨fun i => e (u i), fun i => (he _).trans ?_, (hp u).trans (by rw [h₂])⟩
    rw [h₁, Category.assoc]

end Tangent

end GlobalTheory.FrameMove

namespace GlobalTheory

open FrameMove in

theorem exists_unique_frMove : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ), ρ ≫ Xo.s = Xo.s → ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S), (∃ y' : FrPt Xo c S, FrMove ρ ν y y') ∧ ∀ y' y'' : FrPt Xo c S, ∀ ν' : SABMap Xo.univ.t Xo.univ.t ρ, ν'.φ = ν.φ → FrMove ρ ν y y' → FrMove ρ ν' y y'' → y' = y'' := by
  intro E _ _ _ H Dw l Xo c ρ ν hρ S _ _ y
  have hL := Xo.univ.t.PP.isLB
  refine ⟨?_, fun y' y'' ν' hν h' h'' => ?_⟩
  · obtain ⟨w, gw₁, rw₁, cw₁⟩ := ν.lin
    have cond : (fst (Over.mk y.x) Xo.univ.t.G).left ≫ y.x =
        (snd (Over.mk y.x) Xo.univ.t.G).left ≫ Xo.univ.t.G.hom := pullback.condition
    obtain ⟨q, q₁, q₂⟩ : ∃ q : Gx y.x ⟶ Gx (y.x ≫ ρ),
        q ≫ (fst (Over.mk (y.x ≫ ρ)) Xo.univ.t.G).left = (fst (Over.mk y.x) Xo.univ.t.G).left ∧
        q ≫ (snd (Over.mk (y.x ≫ ρ)) Xo.univ.t.G).left = (snd (Over.mk y.x) Xo.univ.t.G).left ≫ ν.φ :=
      ⟨pullback.lift (fst (Over.mk y.x) Xo.univ.t.G).left ((snd (Over.mk y.x) Xo.univ.t.G).left ≫ ν.φ) (by
        show _ ≫ y.x ≫ ρ = _
        rw [← Category.assoc, cond, Category.assoc, Category.assoc, ν.cart.1.w]),
        pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
    haveI := LevelMoveTest.pinned_isIso ν y.x q q₁ q₂
    have hw := (isGen_iff w).1 gw₁
    obtain ⟨σ, hσ⟩ := exists_carried_forth hL hL hw q₂ y.s
    refine ⟨⟨y.x ≫ ρ, by rw [Category.assoc, hρ, y.x_over], fun τ i => y.u τ i ≫ ν.φ,
      fun τ i => isTanAt_push ν (y.tan τ i), fun τ i => (isEigAt_iff ν τ (y.tan τ i)).2 (y.eig τ i),
      fun τ v' hv' he' => ?_, σ, fun s' => ?_⟩, rfl, fun _ _ => rfl, q, w, q₁, q₂, ⟨gw₁, rw₁, cw₁⟩,
      fun i' i W _ h₀ h₁ h₂ => fn_ext fun z hz => ?_⟩
    · obtain ⟨v, hv, rfl⟩ := exists_isTanAt ν hv'
      exact (existsUnique_congr fun a => isCombAt_iff ν (y.tan τ) a hv).2
        (y.basis τ v hv ((isEigAt_iff ν τ hv).1 he'))
    · obtain ⟨t, ht⟩ := exists_carried_back hL hL hw q₂ s'
      exact (existsUnique_congr fun a => ht.mul_iff hL hL q₂ hσ q₁ (toΓ S a)).2 (y.gen t)
    · have hi' : ν.φ ((snd (Over.mk y.x) Xo.univ.t.G).left z) ∈ Xo.univ.t.PP.L.U i' := mem_pull.1 (h₀ hz).1
      have hi : (snd (Over.mk y.x) Xo.univ.t.G).left z ∈ Xo.univ.t.PP.L.U i := (h₀ hz).2
      refine (gs_appLE q _ W h₁ (𝟙 _) z hz _).trans (Eq.trans ?_ (gs_mul _ z W hz _ _).symm)
      refine (hσ _ (𝟙 _) z i' i hi' hi).trans (congrArg₂ (· * ·) ?_ (gs_res _ z h₂ hz _).symm)
      refine Eq.trans ?_ (gs_appLE _ _ W h₀ (𝟙 _) z hz _).symm
      exact (gs_unit (𝟙 _ ≫ (snd (Over.mk y.x) Xo.univ.t.G).left) z _ (h₀ hz) _).symm
  · obtain rfl := SemiAbelianTripleChecks.sabMap_ext ν' ν hν
    refine LevelMoveTest.frMove_unique ν' (fun w w' hw hw' => ?_) y y' y'' h' h''
    exact iso_eq_of_maps_along_section (S := Xo.X) (exists_chart hL)
      (fun p => (exists_chart hL (ν'.φ p)).elim fun j hj => ⟨fun _ => j, mem_pull.2 hj⟩)
      Xo.univ.t.G.hom (eSec Xo.univ.t.G) (Over.w η[Xo.univ.t.G])
      (firstFiveLaws.1.globalFns _ _ (ObjDim.isAbelianScheme Xo.univ)).2 hw.1 hw'.1 hw.2.1 hw'.2.1

end GlobalTheory
