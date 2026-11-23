import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsIsFibreIso
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFamFieldPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PhiRelTransport
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.QkPullEquiv

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ArcPull GlobalTheory.TorusExt

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R}
  {D' : DegPre R'} (hD : IsPullDeg φ D D') {F : Type} [Field F] [Algebra (FractionRing R) F]
  [Algebra (FractionRing R') F]

theorem weilQkIs_of_pull (hG : GlobalFnsSt) (hF : Compat φ F) {k : ℕ} {p q : QkPt D F k} {p' q' : QkPt D' F k}
    (hp : p'.y = hD.xe.symm p.y) (hpg : IsPullGtF φ hD F p.g p'.g) (hq : q'.y = hD.xe.symm q.y)
    (hqg : IsPullGtF φ hD F q.g q'.g) {ζ : F} (H : WeilQkIs D' F k p' q' ζ) : WeilQkIs D F k p q ζ := by
  intro w v hw hv s s₁ s₂ s₃ s₄ r₁ r₂ r₃ r₄ β
  obtain ⟨α, rfl⟩ := hD.xe.surjective β
  obtain ⟨κ, κ', hκ⟩ := exists_isFibreIso hD hF
  obtain ⟨w', hw', tw⟩ := phiRel_transport hG R R' φ D D' hD F hF κ hκ.fst hκ.snd.symm k p p' hp hpg w hw
  obtain ⟨v', hv', tv⟩ := phiRel_transport hG R R' φ D D' hD F hF κ hκ.fst hκ.snd.symm k q q' hq hqg v hv
  choose dn hdn using exists_fam_field_pull hG R R' φ D D' hD F hF κ hκ.fst hκ.snd.symm k
  have e := (isSmul_iff _ _ _).1 (H w' v' hw' hv' _ _ _ _ _ (tv _ _ _ _ (hdn s) (hdn s₁) r₁)
    (tw _ _ _ _ (hdn s₁) (hdn s₂) r₂) (tw _ _ _ _ (hdn s) (hdn s₃) r₃) (tv _ _ _ _ (hdn s₃) (hdn s₄) r₄))
  refine sec_ext_val D.P.isLB (s := s₂.s (hD.xe α)) (s' := (ζ • s₄).s (hD.xe α)) fun y J hJ => ?_
  obtain ⟨J', hJ'⟩ := DegPull.exists_good' D'.P.isLB y
  have a := FamFieldPull.IsSecPull.val (hdn s₂ α) (hκ.fam α) κ' y hJ hJ'
  have b := FamFieldPull.IsSecPull.val (hdn s₄ α) (hκ.fam α) κ' y hJ hJ'
  have c : κ' ≫ (fst (TF (R := R') F) D'.P.A).left = 𝟙 _ ≫ (fst (TF (R := R) F) D.P.A).left := by
    rw [← hκ.fst, ← Category.assoc, hκ.inv_hom]
  rw [hκ.inv_hom] at a b
  rw [e, sval_smul _ _ _ _ y hJ', c, mul_left_comm, ← b] at a
  rw [sval_smul _ _ _ _ y hJ]
  exact a

variable (hG : GlobalFnsSt) (hF : Compat φ F) (hB : D.TauBimult) (hB' : D'.TauBimult) {k : ℕ}

theorem pullQk_injective : Function.Injective (pullQk hD hG hF hB hB' (k := k)) := fun _ _ h =>
  qk_ext (hD.xe.symm.injective (congrArg QkPt.y h)) (pullGt_injective hD hG hF (congrArg QkPt.g h))

theorem qkAdd_pullQk_iff (p q r : QkPt D F k) : QkAdd p q r ↔
    QkAdd (pullQk hD hG hF hB hB' p) (pullQk hD hG hF hB hB' q) (pullQk hD hG hF hB hB' r) :=
  ⟨qkAdd_pullQk hD hG hF hB hB', fun h => (qkAdd_iff hB _ _ _).2 ((equiv_pullQk hD hG hF hB hB' _ _).1
    ((qkAdd_iff_of_equiv hB' (qk_equiv_refl hB' _) (qk_equiv_refl hB' _)
      (qkAdd_pullQk hD hG hF hB hB' (qkAdd_qkAdd hB p q))).1 h))⟩

theorem weilQkIs_pullQk_iff (p q : QkPt D F k) (z : F) : WeilQkIs D F k p q z ↔
    WeilQkIs D' F k (pullQk hD hG hF hB hB' p) (pullQk hD hG hF hB hB' q) z := by
  obtain ⟨a₁, a₂⟩ := (eq_pullQk_iff hD hG hF hB hB' p _).1 rfl
  obtain ⟨b₁, b₂⟩ := (eq_pullQk_iff hD hG hF hB hB' q _).1 rfl
  exact ⟨weilQkIs_pull hD hF a₁ a₂ b₁ b₂, weilQkIs_of_pull hD hG hF a₁ a₂ b₁ b₂⟩

theorem comm_proj {f' : D'.P.A ⟶ D'.P.A} {f : D.P.A ⟶ D.P.A}
    (h : f' ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf φ)).map f) :
    f'.left ≫ PsiEvenPull.proj hD = PsiEvenPull.proj hD ≫ f.left := by
  have e : f'.left ≫ hD.e.hom.left = hD.e.hom.left ≫ ((Over.pullback (specOf φ)).map f).left :=
    congrArg (fun q => q.left) h
  have g : ((Over.pullback (specOf φ)).map f).left ≫ pullback.fst D.P.A.hom (specOf φ) =
      pullback.fst D.P.A.hom (specOf φ) ≫ f.left := pullback.lift_fst _ _ _
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) e).trans ((Category.assoc _ _ _).trans
    ((congrArg (_ ≫ ·) g).trans (Category.assoc _ _ _).symm)))

theorem qkAct_pullQk_iff {O : Type} [CommRing O] [StarRing O] [Module O D.X] [Module O D'.X] {o : D.OAct O}
    {o' : D'.OAct O} (hx : ∀ (a : O) y, hD.xe (a • y) = a • hD.xe y)
    (ho : ∀ a, (o'.onB.act a).left ≫ PsiEvenPull.proj hD = PsiEvenPull.proj hD ≫ (o.onB.act a).left) (a : O)
    (p q : QkPt D F k) : QkAct o a p q ↔ QkAct o' a (pullQk hD hG hF hB hB' p) (pullQk hD hG hF hB hB' q) :=
  ⟨qkAct_pullQk hD hG hF hB hB' hx ho, fun h => (qkAct_iff hB hG o _ _ _).2
    ((equiv_pullQk hD hG hF hB hB' _ _).1 ((qkAct_iff_of_equiv hB' hG o' (qk_equiv_refl hB' _)
      (qkAct_pullQk hD hG hF hB hB' hx ho (qkAct_qkSmul hB hG o a p))).1 h))⟩

theorem exists_equiv_pullQk : ∃ τ : QkPt D F k ≃ QkPt D' F k, ⇑τ = pullQk hD hG hF hB hB' :=
  ⟨Equiv.ofBijective _ ⟨pullQk_injective hD hG hF hB hB', pullQk_surjective hD hG hF hB hB'⟩, rfl⟩

end GlobalTheory.QkPullEquiv

namespace GlobalTheory

open GlobalTheory.ArcPull GlobalTheory.TorusExt GlobalTheory.QkPullEquiv in

theorem exists_qk_pull_equiv : Laws → Laws2 → ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (φ : R →+* R') (D : DegPre R) (D' : DegPre R') (hD : IsPullDeg φ D D'), D.TauBimult → D'.TauBimult → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing R') F], (∀ r : R, algebraMap (FractionRing R) F (algebraMap R (FractionRing R) r) = algebraMap (FractionRing R') F (algebraMap R' (FractionRing R') (φ r))) → ∀ k : ℕ, ∃ τ : QkPt D F k ≃ QkPt D' F k, (∀ p p', τ p = p' ↔ p'.y = hD.xe.symm p.y ∧ IsPullGtF φ hD F p.g p'.g) ∧ (∀ p q, QkPt.Equiv D F p q ↔ QkPt.Equiv D' F (τ p) (τ q)) ∧ (∀ p q r, QkAdd p q r ↔ QkAdd (τ p) (τ q) (τ r)) ∧ (∀ p q z, WeilQkIs D F k p q z ↔ WeilQkIs D' F k (τ p) (τ q) z) ∧ ∀ (O : Type) [CommRing O] [StarRing O] [Module O D.X] [Module O D'.X] (o : D.OAct O) (o' : D'.OAct O), (∀ (a : O) y, hD.xe (a • y) = a • hD.xe y) → (∀ a, o'.onB.act a ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf φ)).map (o.onB.act a)) → ∀ a p q, QkAct o a p q ↔ QkAct o' a (τ p) (τ q) := by
  intro hL _ R R' _ _ _ _ φ D D' hD hB hB' F _ _ _ hF k
  have hG := hL.globalFns
  obtain ⟨τ, hτ⟩ := exists_equiv_pullQk hD hG hF hB hB' (k := k)
  refine ⟨τ, ?_⟩
  rw [hτ]
  exact ⟨fun p p' => eq_comm.trans (eq_pullQk_iff hD hG hF hB hB' p p'),
    fun p q => (equiv_pullQk hD hG hF hB hB' p q).symm, qkAdd_pullQk_iff hD hG hF hB hB',
    weilQkIs_pullQk_iff hD hG hF hB hB',
    fun O _ _ _ _ o o' hx ho => qkAct_pullQk_iff hD hG hF hB hB' hx fun a => comm_proj hD (ho a)⟩

end GlobalTheory
