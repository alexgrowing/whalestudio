import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowEqOfBaseChange
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ZH.LabelMap

theorem exists_lift_points {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S') {Γ : Type} [AddCommGroup Γ]
    (pt : Γ → (baseOver S ⟶ G)) (hadd : ∀ a b, pt (a + b) = pt a * pt b) :
    ∃ xx : Multiplicative Γ →* (T ⟶ G'),
      (∀ a x, x.left ≫ φ = (T.hom ≫ f) ≫ (pt a).left ↔ x = xx (Multiplicative.ofAdd a)) ∧
      ∀ (k : ℕ), (∀ z : Over.mk (T.hom ≫ f) ⟶ G, z ^ k = 1 → ∃ a, (T.hom ≫ f) ≫ (pt a).left = z.left) →
        ∀ x : T ⟶ G', x ^ k = 1 → ∃ a, xx (Multiplicative.ofAdd a) = x := by
  let Φ : (T ⟶ G') →* (Over.mk (T.hom ≫ f) ⟶ G) :=
    MonoidHom.mk' (fun x => toBase h.1.w x) fun x y => Over.OverMorphism.ext (h.2 T x y _ _ rfl rfl).symm
  have hΦ : ∀ x, (Φ x).left = x.left ≫ φ := fun _ => rfl
  have inj : Function.Injective Φ := fun x y e => Over.OverMorphism.ext (h.1.hom_ext
    ((hΦ x).symm.trans ((congrArg (fun z => z.left) e).trans (hΦ y))) ((Over.w x).trans (Over.w y).symm))
  have surj : Function.Surjective Φ := fun z =>
    ⟨Over.homMk (h.1.lift z.left T.hom (Over.w z)) (h.1.lift_snd _ _ _), Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩
  let e := MulEquiv.ofBijective Φ ⟨inj, surj⟩
  let U : Over.mk (T.hom ≫ f) ⟶ baseOver S := Over.homMk (T.hom ≫ f) (Category.comp_id _)
  let q : Multiplicative Γ →* (Over.mk (T.hom ≫ f) ⟶ G) :=
    MonoidHom.mk' (fun a => U ≫ pt a.toAdd) fun a b =>
      (congrArg (U ≫ ·) (hadd a.toAdd b.toAdd)).trans (MonObj.comp_mul U _ _)
  have key : ∀ a x, x.left ≫ φ = (T.hom ≫ f) ≫ (pt a).left ↔ x = e.symm (q (Multiplicative.ofAdd a)) := fun a x =>
    ⟨fun H => e.eq_symm_apply.2 (Over.OverMorphism.ext H),
      fun H => congrArg (fun z => z.left) (e.eq_symm_apply.1 H)⟩
  refine ⟨e.symm.toMonoidHom.comp q, key, fun k hk x hx => ?_⟩
  obtain ⟨a, ha⟩ := hk (Φ x) (by rw [← map_pow, hx, map_one])
  exact ⟨a, ((key a x).1 ha.symm).symm⟩

attribute [local instance] TorusExt.gtGroup in

theorem pow_eq_one_of_qkAdd {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F]
    [Algebra (FractionRing R) F] (hB : D.TauBimult) {k : ℕ} {M : Type} [Group M] (f : QkPt D F k → M)
    (heq : ∀ q q', QkPt.Equiv D F q q' → f q = f q') (hadd : ∀ q q' q'', QkAdd q q' q'' → f q'' = f q * f q')
    (q : QkPt D F k) : f q ^ k = 1 := by
  have fz : f (TorusExt.qkZero hB F k) = 1 := by
    have e := hadd _ _ _ (TorusExt.qkAdd_qkAdd hB (TorusExt.qkZero hB F k) (TorusExt.qkZero hB F k))
    rw [show TorusExt.qkAdd hB (TorusExt.qkZero hB F k) (TorusExt.qkZero hB F k) = TorusExt.qkZero hB F k from
      TorusExt.qk_ext (add_zero _) (add_zero _)] at e
    exact mul_eq_left.1 e.symm
  let m : ℕ → QkPt D F k := fun n => TorusExt.qkMk hB (n • q.y) (n • q.g) (by
    rw [smul_comm, TorusExt.qk_nsmul hB, map_nsmul])
  have hm : ∀ n, f (m n) = f q ^ n := fun n => by
    induction n with
    | zero => exact (congrArg f (TorusExt.qk_ext (zero_nsmul _) (zero_nsmul _))).trans (fz.trans (pow_zero _).symm)
    | succ n ih =>
      rw [pow_succ, ← ih, ← hadd _ _ _ (TorusExt.qkAdd_qkAdd hB _ _)]
      exact congrArg f (TorusExt.qk_ext (succ_nsmul _ _) (succ_nsmul _ _))
  rw [← hm, ← fz]
  exact (heq _ _ ((TorusExt.equiv_iff hB _ _).2
    ⟨q.y, (zero_add _).symm, (TorusExt.qk_nsmul hB q).trans (zero_add _).symm⟩)).symm

theorem exists_labelMap : Laws → Laws2 → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀), ∃ yy : S.Gam →+ u.D.toPre.X ⧸ (nsmulAddMonoidHom (S.r * S.N) : u.D.toPre.X →+ u.D.toPre.X).range, Function.Surjective yy ∧ (∀ (a : S.Gam) (pk : QkPt u.D.toPre (PadicAlgCl p) (S.r * S.N)) (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A), QkToAkU u.U.toUnifPre (PadicAlgCl p) (S.r * S.N) pk x → x.left ≫ u.φ = spMap y₀ ≫ (ρ.pt a).left → yy a = QuotientAddGroup.mk pk.y) := by
  intro L _ hU o Ω _ _ _ _ S ρ p _ y₀ u
  haveI : CharZero u.V := ((algebraMap (FractionRing u.V) (PadicAlgCl p)).comp (algebraMap u.V _)).charZero
  have hk : 1 ≤ S.r * S.N := Nat.mul_pos S.r_pos (by have := S.N_ge; omega)
  obtain ⟨f, hrel, honto, heq, hadd, -⟩ := hU u.V u.complete u.A u.G u.D u.U (PadicAlgCl p) (S.r * S.N) hk
  obtain ⟨xx, hxx, hsurj⟩ := exists_lift_points u.cart (TFK (R := u.V) (PadicAlgCl p)) ρ.pt ρ.pt_add
  have hy : (TFK (R := u.V) (PadicAlgCl p)).hom ≫ spMap u.yK = spMap y₀ := by
    exact (Spec.map_comp (CommRingCat.ofHom u.yK) (CommRingCat.ofHom (algebraMap _ _))).symm.trans
      (congrArg spMap u.fac)
  have hsurj' := hsurj (S.r * S.N) fun z hz =>
    (ρ.pt_bij (PadicAlgCl p) _ z hz).exists.imp fun a ha => congrArg (fun w => w.left) ha
  have htors : ∀ a : S.Gam, xx (Multiplicative.ofAdd a) ^ (S.r * S.N) = 1 := fun a => by
    have : (S.r * S.N) • a = 0 := funext fun i => by
      rw [Pi.smul_apply, nsmul_eq_mul, ZMod.natCast_self, zero_mul]; rfl
    rw [← map_pow, ← ofAdd_nsmul, this, ofAdd_zero, map_one]
  choose P hP using fun a => honto _ (htors a)
  have hB := u.D.tau_bimult
  have wd : ∀ q q' : QkPt u.D.toPre (PadicAlgCl p) (S.r * S.N), f q = f q' →
      (QuotientAddGroup.mk q.y : u.D.toPre.X ⧸ (nsmulAddMonoidHom (S.r * S.N) : u.D.toPre.X →+ u.D.toPre.X).range) =
        QuotientAddGroup.mk q'.y := fun q q' e => by
    obtain ⟨z, hz, -⟩ := (heq q q').1 e
    exact QuotientAddGroup.eq.2 ⟨z, by rw [hz, neg_add_cancel_left]; rfl⟩
  have ftors : ∀ q, f q ^ (S.r * S.N) = 1 := pow_eq_one_of_qkAdd hB f (fun q q' e => (heq q q').2 e) hadd
  refine ⟨AddMonoidHom.mk' (fun a => QuotientAddGroup.mk (P a).y) fun a b => ?_, fun c => ?_, fun a pk x hx hφ => ?_⟩
  · exact wd _ (TorusExt.qkAdd hB (P a) (P b)) (by
      rw [hadd _ _ _ (TorusExt.qkAdd_qkAdd hB _ _), hP, hP, hP, ofAdd_add, map_mul])
  · obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective c
    obtain ⟨q, rfl⟩ := TorusExt.exists_qkPt (F := PadicAlgCl p) L.mulN (Or.inr L.polBaseChange) hB (Nat.pos_iff_ne_zero.1 hk) y
    obtain ⟨a, ha⟩ := hsurj' _ (ftors q)
    exact ⟨a, wd _ _ ((hP a).trans ha)⟩
  · exact wd _ _ ((hP a).trans (((hxx a x).1 (hφ.trans (by rw [hy]))).symm.trans ((hrel pk x).1 hx)))

end GlobalTheory.ZH.LabelMap
end
