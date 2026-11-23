import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCochFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeG
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsLieBasisIffIsUnitDet
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsLiftOfIsNilpotent

open AlgebraicGeometry CategoryTheory Limits NumberField MonoidalCategory CartesianMonoidalCategory MonObj Matrix Topology
open Formalism.BasicNotions ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CubeFib GlobalTheory.LieMet GlobalTheory.LieHt GlobalTheory.LocM.Frm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh GlobalTheory.Toroidal GlobalTheory.HeightParts GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.BdFib
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AbMapLie

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  {t : SAB H X} {k : Type} [Field k] {x : Sp k ⟶ X} {φ : Fib k} {m : CubeMap φ.G t.G}
  (hm : IsGrpPullback φ.G t.G x m.F)

def up (w : TanM x t.G) : epsR k ⟶ φ.G := (ReciprocityTheory.ChartRestriction.G.PullbackSections.push_surj hm (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv w)).choose

theorem push_up (w : TanM x t.G) : pushHom hm (epsR k) (up hm w) = ReciprocityTheory.ChartRestriction.G.PullbackSections.tv w :=
  (ReciprocityTheory.ChartRestriction.G.PullbackSections.push_surj hm (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv w)).choose_spec

theorem up_left (w : TanM x t.G) : (up hm w).left ≫ m.F = (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv w).left :=
  congrArg (fun z => z.left) (push_up hm w)

theorem up_add (w₁ w₂ : TanM x t.G) : up hm (w₁ + w₂) = up hm w₁ * up hm w₂ :=
  ReciprocityTheory.ChartRestriction.G.PullbackSections.push_inj hm (by rw [map_mul, push_up, push_up, push_up, ReciprocityTheory.ChartRestriction.G.PullbackSections.tv_add])

theorem up_smul (a : k) (w : TanM x t.G) : up hm (a • w) = ReciprocityTheory.ChartRestriction.G.PullbackSections.scK a (up hm w) :=
  ReciprocityTheory.ChartRestriction.G.PullbackSections.push_inj hm (by
    rw [ReciprocityTheory.ChartRestriction.G.PullbackSections.push_scK, push_up, push_up, ReciprocityTheory.ChartRestriction.G.PullbackSections.tv_smul])

theorem isTangent_up (w : TanM x t.G) : IsTangent (up hm w) :=
  (ReciprocityTheory.ChartRestriction.G.PullbackSections.isTangent_iff hm _).2 (by rw [push_up]; exact ReciprocityTheory.ChartRestriction.G.PullbackSections.tv_mem w)

theorem isTangent_comp {G B : Over (Sp k)} [GrpObj G] [GrpObj B] (f : G ⟶ B) [IsMonHom f] {p : epsR k ⟶ G}
    (hp : IsTangent p) : IsTangent (p ≫ f) := by
  unfold IsTangent at *
  rw [Over.comp_left, ← Category.assoc, hp, ← Over.comp_left, IsMonHom.one_hom]

variable {n : ℕ} {v : Fin n → (epsR k ⟶ φ.P.A)} (hv : IsLieBasis v)

def coord (w : TanM x t.G) : Fin n → k :=
  (hv.2 _ (isTangent_comp φ.q (isTangent_up hm w))).exists.choose

theorem coord_spec (w : TanM x t.G) : IsLieComb (coord hm hv w) v (up hm w ≫ φ.q) :=
  (hv.2 _ (isTangent_comp φ.q (isTangent_up hm w))).exists.choose_spec

theorem coord_eq {w : TanM x t.G} {c : Fin n → k} (h : IsLieComb c v (up hm w ≫ φ.q)) : coord hm hv w = c :=
  (hv.2 _ (isTangent_comp φ.q (isTangent_up hm w))).unique (coord_spec hm hv w) h

include hv in
theorem tanExp_add [IsCommMonObj φ.P.A] (c₁ c₂ : Fin n → k) :
    GlobalTheory.SqZero.tanExp v (c₁ + c₂) = GlobalTheory.SqZero.tanExp v c₁ * GlobalTheory.SqZero.tanExp v c₂ := by
  exact congrArg Additive.toMul ((GlobalTheory.LieComb.combHom hv.1).map_add c₁ c₂)

def coordL : TanM x t.G →ₗ[k] (Fin n → k) where
  toFun := coord hm hv
  map_add' w₁ w₂ := by
    haveI : IsCommMonObj φ.P.A := φ.P.isAb.comm
    refine coord_eq hm hv ?_
    rw [GlobalTheory.LieComb.isLieComb_iff_tanExp, up_add, MonObj.mul_comp, tanExp_add hv,
      ← (GlobalTheory.LieComb.isLieComb_iff_tanExp _ _).1 (coord_spec hm hv w₁),
      ← (GlobalTheory.LieComb.isLieComb_iff_tanExp _ _).1 (coord_spec hm hv w₂)]
  map_smul' a w := by
    haveI : IsCommMonObj φ.P.A := φ.P.isAb.comm
    refine coord_eq hm hv ?_
    have h1 : IsLieComb ![a] ![up hm w ≫ φ.q] (up hm (a • w) ≫ φ.q) :=
      ⟨![ReciprocityTheory.ChartRestriction.G.PullbackSections.scK a (up hm w ≫ φ.q)], fun i => by fin_cases i; rfl, by
        rw [up_smul]
        simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, _root_.mul_one, Matrix.cons_val_zero]
        exact Over.OverMorphism.ext (Category.assoc _ _ _)⟩
    have h2 := (GlobalTheory.LieComb.lieComb_algebra k φ.P.A n v hv.1).2.2.1 1 ![coord hm hv w] ![up hm w ≫ φ.q] ![a] _
      (fun i => by fin_cases i; exact coord_spec hm hv w) h1
    simpa using h2

theorem ker_fst_isNilpotent :
    IsNilpotent (RingHom.ker (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom).hom) := by
  refine ⟨2, ?_⟩
  rw [pow_two, Ideal.zero_eq_bot, eq_bot_iff]
  refine Ideal.mul_le.2 fun a ha b hb => ?_
  rw [RingHom.mem_ker] at ha hb
  change a.fst = 0 at ha
  change b.fst = 0 at hb
  rw [Ideal.mem_bot]
  ext
  · simp [ha]
  · simp [ha, hb]

theorem exists_tangent_lift {b : epsR k ⟶ φ.P.A} (hb : IsTangent b) :
    ∃ w' : epsR k ⟶ φ.G, IsTangent w' ∧ w' ≫ φ.q = b := by
  haveI := GlobalTheory.TangentLift.smooth_q φ
  have h0 : η[φ.G].left ≫ φ.q.left =
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom) ≫ b.left := by
    rw [← Over.comp_left, IsMonHom.one_hom]
    exact hb.symm
  obtain ⟨y, hy1, hy2⟩ := GlobalTheory.TangentLift.exists_lift_of_isNilpotent φ.q.left
    (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom) (fun a => ⟨TrivSqZeroExt.inl a, rfl⟩)
    ker_fst_isNilpotent b.left η[φ.G].left h0 (η[φ.G].left (IsLocalRing.closedPoint k))
    (fun p => congrArg η[φ.G].left (Subsingleton.elim (α := PrimeSpectrum k) _ _))
  refine ⟨Over.homMk y (by rw [← Over.w φ.q, ← Category.assoc, hy2, Over.w b]), hy1, ?_⟩
  exact Over.OverMorphism.ext hy2

theorem coordL_surjective : Function.Surjective (coordL hm hv) := by
  haveI : IsCommMonObj φ.P.A := φ.P.isAb.comm
  intro c
  obtain ⟨b, hb, -⟩ := (GlobalTheory.LieComb.lieComb_algebra k φ.P.A n v hv.1).1 c
  have hbt := (GlobalTheory.LieComb.lieComb_algebra k φ.P.A n v hv.1).2.1 c b hb
  obtain ⟨w', hw't, hw'q⟩ := exists_tangent_lift hbt
  let w : TanM x t.G := ReciprocityTheory.ChartRestriction.G.PullbackSections.mkT (pushHom hm (epsR k) w')
    ((ReciprocityTheory.ChartRestriction.G.PullbackSections.isTangent_iff hm w').1 hw't)
  have hw : up hm w = w' := ReciprocityTheory.ChartRestriction.G.PullbackSections.push_inj hm (by rw [push_up]; rfl)
  refine ⟨w, coord_eq hm hv ?_⟩
  rw [hw, hw'q]
  exact hb

theorem isAbMap_coordL : IsAbMap φ m v (coordL hm hv) := fun w =>
  ⟨up hm w, up_left hm w, coord_spec hm hv w⟩

theorem exists_abMap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (k : Type) [Field k] [CharZero k] (x : Sp k ⟶ X) (φ : Fib k) (m : CubeMap φ.G t.G), FibAt t x φ m → ∀ (n : ℕ) (v : Fin n → (epsR k ⟶ φ.P.A)), IsLieBasis v → ∃ q : TanM x t.G →ₗ[k] (Fin n → k), Function.Surjective q ∧ IsAbMap φ m v q := by
  intro E _ _ _ H X t k _ _ x φ m hφ n v hv
  exact ⟨coordL hφ.1 hv, coordL_surjective hφ.1 hv, isAbMap_coordL hφ.1 hv⟩

end GlobalTheory.AbMapLie

end
