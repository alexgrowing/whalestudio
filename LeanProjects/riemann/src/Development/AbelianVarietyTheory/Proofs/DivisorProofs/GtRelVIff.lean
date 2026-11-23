import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensFacts
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.WithISelf
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

noncomputable section

namespace GlobalTheory.Mum.TensRos

section Values

variable {F : Type} [Field F] {N N' : NumD F} {r : ℕ}

def PV (W : Matrix (Fin r) (Fin r) ℤ) (e : N'.X → Fin r → N.X) (χ' : N'.X) (vs : Fin r → N.Gt) : F :=
  ((∏ i, ∏ j, ((vs j).s (e χ' i) * (vs i).s (e χ' j) /
      (N.θ (N.c (e χ' j)) (vs j).b (N.c (e χ' i)) * N.θ (N.c (e χ' j)) (vs j).b (vs i).b *
        N.θ (N.c (e χ' i)) (vs i).b (N.c (e χ' j) * (vs j).b))) ^ W i j : Fˣ) : F)

theorem gtRelV_iff (W : Matrix (Fin r) (Fin r) ℤ) (φ : N'.A → Fin r → N.A) (e : N'.X → Fin r → N.X) (wv : N'.A → F)
    (v' : N'.Gt) (vs : Fin r → N.Gt) :
    GtRelV W φ e wv v' vs ↔ (∀ j, φ v'.b j = (vs j).b) ∧ ∀ χ' : N'.X,
      (v'.s χ' : F) * wv (N'.c χ') * wv v'.b = PV W e χ' vs * wv (N'.c χ' * v'.b) * wv 1 := Iff.rfl

end Values

variable {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}
  {F : Type} [Field F] [Algebra (FractionRing R) F] {N N' : NumD F}

def tensJ (T : Tens D D' W) (ν : NumOf D F N) (y : Sp F ⟶ D'.P.A.left) :
    (LB.LinComb D.P.L (tensφ T.pr) (tensε W)).ι :=
  fun k => ν.J (y ≫ tensφ T.pr k)

def RosVT (T : Tens D D' W) (ν : NumOf D F N) (ν' : NumOf D' F N') (f g : D'.P.A ⟶ D'.P.A) (ρ : N'.A → N'.A → F) :
    Prop :=
  ∃ u : LB.Gen (LB.LinComb (LB.LinComb D.P.L (tensφ T.pr) (tensε W)) (rosatiφ D'.P.A f g) rosatiε), u.IsGen ∧
    LB.Gen.Corr (LB.LinComb D.P.L (tensφ T.pr) (tensε W)) _ _ _ _
      (LB.pullGen (LB.LinComb D.P.L (tensφ T.pr) (tensε W)) _ _ u (zero2 D'.P.A))
      (LB.oneGen (LB.LinComb D.P.L (tensφ T.pr) (tensε W))) ∧
    ∀ b b', ρ b b' = vF u (lift (ν'.eA b) (ν'.eA b')).left (tensJ T ν)

theorem cmp_actV {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}
    (T : Tens D D' W) {F : Type} [Field F] [Algebra (FractionRing R) F] {N N' : NumD F} (ν : NumOf D F N)
    (ν' : NumOf D' F N') {O : Type} [CommRing O] [StarRing O] [Module O D'.X] (o : D'.OAct O)
    (ρ : O →+* Matrix (Fin r) (Fin r) ℤ) (hact : T.IsAct o ρ) (x : O) (b : N'.A) (j : Fin r) :
    GlobalTheory.Mum.TensTor.cmp T ν ν' (GlobalTheory.Relabel.actV ν' o.onB x b) j = ∏ k, GlobalTheory.Mum.TensTor.cmp T ν ν' b k ^ ρ x j k := by
  letI := D.P.isAb.comm
  let P : (D'.P.A ⟶ D.P.A) →* (TF (R := R) F ⟶ D.P.A) :=
    { toFun := fun f => ν'.eA b ≫ f
      map_one' := MonObj.comp_one _
      map_mul' := fun f g => MonObj.comp_mul _ _ _ }
  have e : ν'.eA (GlobalTheory.Relabel.actV ν' o.onB x b) ≫ T.pr j = P (∏ k, T.pr k ^ ρ x j k) := by
    rw [GlobalTheory.Relabel.actV, MulEquiv.apply_symm_apply, Category.assoc, hact.2 x j]; rfl
  rw [GlobalTheory.Mum.TensTor.cmp, e, map_prod, map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [map_zpow, map_zpow]
  rfl

theorem c_actV {R : Type} [CommRing R] [IsDomain R] {D' : DegPre R} {F : Type} [Field F]
    [Algebra (FractionRing R) F] {N' : NumD F} (ν' : NumOf D' F N') {O : Type} [CommRing O] [StarRing O]
    [Module O D'.X] (o : D'.OAct O) (a : O) (χ : N'.X) :
    GlobalTheory.Relabel.actV ν' o.onB a (N'.c χ) = N'.c (ν'.eX.symm (a • ν'.eX χ)) := by
  apply ν'.eA.injective
  rw [GlobalTheory.Relabel.actV, MulEquiv.apply_symm_apply, ν'.c_eq, ν'.c_eq, AddEquiv.apply_symm_apply]
  show (toUnit _ ≫ D'.c _) ≫ _ = toUnit _ ≫ D'.c _
  rw [o.c_lin, Category.assoc]

end GlobalTheory.Mum.TensRos
end
