import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.MulSubMulTo
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.EtDefs
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AtlasGroupActions.TowerSmulZero
import BuildAid.D2

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris DividedPowers GroundTheory.PAdicHodge Formalism.Per6

namespace CrystallineSemistableComparison.HT

open PAlg

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem lin_add {R : Type} [CommRing R] {A B C : Type 1} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [Module R A] [Module R B]
    [Module R C] (f : A →ₗ[R] C) (g : B →ₗ[R] C) {x x' : A} {y y' y'' : B} (h : f x = g y) (h' : f x' = g y') (e : y'' = y + y') :
    f (x + x') = g y'' := by rw [e, map_add, map_add, h, h']

theorem lin_smul {R : Type} [CommRing R] {A B C : Type 1} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [Module R A] [Module R B]
    [Module R C] (f : A →ₗ[R] C) (g : B →ₗ[R] C) (c : R) {x : A} {y y' : B} (h : f x = g y) (e : y' = c • y) :
    f (c • x) = g y' := by rw [e, map_smul, map_smul, h]

theorem kill_val (A : PAlg l) (n : ℕ) (x : A.Acr n) : A.cris n ((l : Acris l) ^ n) * x = 0 := by
  rw [map_pow, map_natCast, A.pow_l_acr n, zero_mul]

theorem kill_MH (P : PAlg l ⥤ Type) (n j : ℕ) (x : MH P n j) : ((l : Acris l) ^ n) • x = 0 :=
  GlueE.H_smul_eq_zero _ _ (fun T y => kill_val T.1.obj n y) j x

theorem e_smul (e : E.EtFam l K) (M : Model l K) (j n : ℕ) (z : ℤ_[l]) (v : M.T j) :
    e M n j ((z • v).lev n) = zA l z • e M n j (v.lev n) :=
  ((congrArg (e M n j) (GlobalTheory.EtC.HtL.smul_eq l n n le_rfl M.spc j 0 z (v.1 n))).trans (map_nsmul (e M n j) _ _)).trans
    (GlueE.padic_smul (zA l) n _ (kill_MH M.P n j _) z).symm

theorem zA_chi (σ : K.fixingSubgroup) (r : ℕ) :
    zA l ((DeRhamTwist.Twist.chi0 l σ.1 ^ r : ℤ_[l]ˣ) : ℤ_[l]) = χA (IntermediateField.fixingSubgroupEquiv K σ) ^ r := by
  rw [Units.val_pow_eq_pow_val, map_pow]
  rfl

variable (ht : TFil l) {e : E.EtFam l K} (he : EtP e)
include he

theorem h1_lift_add : ∀ {M : Model l K} {r j : ℕ} {v v' : M.T j} {x x' : Fam M r j},
    IsLift ht e r v x → IsLift ht e r v' x' → IsLift ht e r (v + v') (x + x') :=
  fun {M r j v v' x x'} h h' => ⟨comp_add h.1 h'.1, fun n =>
    lin_add ((βMorF (B.schFn M.p) (okToOC l K) r n).pull j) ((tMor ht ((B.schFn M.p).pt (okToOC l K)) r n).pull j) (h.2 n) (h'.2 n)
      (map_add (e M n j) (v.lev n) (v'.lev n))⟩

theorem h1_lift_smul : ∀ {M : Model l K} {r j : ℕ} {v : M.T j} {x : Fam M r j} (z : ℤ_[l]),
    IsLift ht e r v x → IsLift ht e r (z • v) (zA l z • x) :=
  fun {M r j v x} z h => ⟨comp_smul _ h.1, fun n =>
    lin_smul ((βMorF (B.schFn M.p) (okToOC l K) r n).pull j) ((tMor ht ((B.schFn M.p).pt (okToOC l K)) r n).pull j) (zA l z) (h.2 n)
      (e_smul e M j n z v)⟩

theorem h1_lift_shift : ∀ {M : Model l K} {r r' j : ℕ} {v : M.T j} {x : Fam M r j} (k : ℕ) (h : r + k = r'),
    IsLift ht e r v x → IsLift ht e r' v (shS ht k h x) :=
  fun {M r r' j v x} k h hx => ⟨comp_sh ht k h hx.1, fun n =>
    (β_sh (B.schFn M.p) (okToOC l K) ht k h n j (x n)).trans
      ((congrArg ((shT ht ((B.schFn M.p).pt (okToOC l K)) k h n).pull j) (hx.2 n)).trans (shT_tMor ht _ k h n j _))⟩

theorem h1_lift_galois : ∀ {M : Model l K} {r j : ℕ} {v : M.T j} {x : Fam M r j} (σ : K.fixingSubgroup), IsLift ht e r v x →
    IsLift ht e r (DeRhamTwist.Twist.chi0 l σ.1 ^ r • M.actT j σ v) (galS σ x) :=
  fun {M r j v x} σ hx => ⟨comp_gal σ hx.1, fun n =>
    (β_galF (B.schFn M.p) (okToOC l K) (IntermediateField.fixingSubgroupEquiv K σ) (galOC_okToOC _) r n j (x n)).trans
      ((congrArg ((galT (IntermediateField.fixingSubgroupEquiv K σ) (B.ptTw (B.schFn M.p) (okToOC l K)
          (IntermediateField.fixingSubgroupEquiv K σ) (galOC_okToOC _)) r n).pull j) (hx.2 n)).trans
        ((galT_tMor ht _ _ r n j _).trans
          ((map_smul ((tMor ht ((B.schFn M.p).pt (okToOC l K)) r n).pull j) _ _).symm.trans
            (congrArg ((tMor ht ((B.schFn M.p).pt (okToOC l K)) r n).pull j)
              ((e_smul e M j n ((DeRhamTwist.Twist.chi0 l σ.1 ^ r : ℤ_[l]ˣ) : ℤ_[l]) (M.actT j σ v)).trans
                (congrArg₂ (· • ·) (zA_chi σ r)
                  (he.good.equi M n j (IntermediateField.fixingSubgroupEquiv K σ) (v.lev n)))).symm))))⟩

theorem h1_lift_naturality : ∀ {M N : Model l K} (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) {r j : ℕ} {v : N.T j} {x : Fam N r j},
    IsLift ht e r v x → IsLift ht e r (Model.pullT u hu j v) (pullS u hu x) :=
  fun {M N} u hu {r j v x} hx => ⟨comp_pull u hu hx.1, fun n =>
    (β_pullF (okToOC l K) (B.schMap u hu) r n j (x n)).trans
      ((congrArg ((pullT' ((B.schMap u hu).pt (okToOC l K)) r n).pull j) (hx.2 n)).trans
        ((pullT_tMor ht _ r n j _).trans
          (congrArg ((tMor ht ((B.schFn M.p).pt (okToOC l K)) r n).pull j) (he.good.nat M N u hu n j (v.lev n)).symm)))⟩

end CrystallineSemistableComparison.HT
