import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptyObjMapOfFiniteEtaleCoverStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteEtaleDeeperLevelCoverStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NsmulMemSmulTop
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelMapFiniteEtaleSurjective
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.OverHomEqIffForallIsAlgClosedAlgebra
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM GlobalTheory.LevelCover

noncomputable section

namespace GlobalTheory.LevelQuotRep

attribute [local instance] MvPolynomial.gradedAlgebra in
theorem isSeparated_of_qproj {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Sp R} (h : IsQProjOver f) :
    IsSeparated f := by
  obtain ⟨N, i, hi, -, rfl⟩ := h
  unfold PSpace.str
  infer_instance

theorem exists_lift_geom {W Z : Scheme.{0}} (q : W ⟶ Z) [LocallyOfFiniteType q] [Surjective q] {K : Type} [Field K]
    [IsAlgClosed K] (x : Sp K ⟶ Z) : ∃ h : Sp K ⟶ W, h ≫ q = x := by
  obtain ⟨y, -⟩ := (pullback.snd q x).surjective (IsLocalRing.closedPoint K)
  have : JacobsonSpace ↥(pullback q x) := LocallyOfFiniteType.jacobsonSpace (pullback.snd q x)
  obtain ⟨y', -, hy'⟩ := nonempty_inter_closedPoints (Z := (Set.univ : Set ↥(pullback q x)))
    ⟨y, trivial⟩ isOpen_univ.isLocallyClosed
  have hc : IsClosed {y'} := hy'
  refine ⟨pointOfClosedPoint (pullback.snd q x) y' hc ≫ pullback.fst q x, ?_⟩
  rw [Category.assoc, pullback.condition, pointOfClosedPoint_comp_assoc]

theorem finite_etale_onto_spMap {K L : Type} [Field K] [Field L] [CharZero K] [CharZero L] [FiniteDimensional ℚ L]
    (k : K →+* L) : IsFinite (spMap k) ∧ Etale (spMap k) ∧ Surjective (spMap k) := by
  algebraize [k]
  have : IsScalarTower ℚ K L := IsScalarTower.of_algebraMap_eq fun x => by simp
  have hf : Module.Finite K L := Module.Finite.of_restrictScalars_finite ℚ K L
  refine ⟨?_, ?_, ⟨fun y => ⟨default, Subsingleton.elim _ _⟩⟩⟩
  · rw [IsFinite.SpecMap_iff]
    exact hf
  · rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    have : Algebra.FormallyEtale K L := Algebra.FormallyEtale.of_isSeparable K L
    have : Algebra.FinitePresentation K L := Algebra.FinitePresentation.of_finiteType.mp inferInstance
    exact (⟨inferInstance, inferInstance⟩ : Algebra.Etale K L)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l l₂ : Level H}

theorem finiteDimensional_KA (l : Level H) : FiniteDimensional ℚ (KA l) := by
  refine IntermediateField.finiteDimensional_adjoin fun x hx => ?_
  rcases hx with rfl | rfl
  · refine IsIntegral.of_pow two_pos ?_
    rw [H.sqrt_neg_disc_sq]
    exact (isIntegral_algebraMap (x := (H.d : ℚ))).neg
  · refine IsIntegral.of_pow l.A_pos ?_
    rw [show zeta l.A ^ l.A = 1 from (Complex.isPrimitiveRoot_exp l.A l.A_pos.ne').pow_eq_one]
    exact isIntegral_one

section Obj

variable {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B''] {b : Base l B} {b' : Base l B'} {b'' : Base l B''}
  {S S' S'' : Scheme.{0}} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B'} {s'' : S'' ⟶ Sp B''}
  {o : Obj D l b s} {o' : Obj D l b' s'} {o'' : Obj D l b'' s''}

theorem obj_comp {f : S' ⟶ S} {f' : S'' ⟶ S'} (m' : ObjMap o'' o' f') (m : ObjMap o' o f) :
    Nonempty (ObjMap o'' o (f' ≫ f)) :=
  ⟨(((ObjMaps.id_comp_cancel E H D l _ _ _ _ _ _ _ _ _ _ _ _ o o' o'').2 f f' m).1 m').choose⟩

theorem obj_cancel {f : S' ⟶ S} {e : S'' ⟶ S} (m : ObjMap o' o f) (n : ObjMap o'' o e) (g : S'' ⟶ S')
    (he : g ≫ f = e) : Nonempty (ObjMap o'' o' g) := by
  subst he
  exact ⟨(((ObjMaps.id_comp_cancel E H D l _ _ _ _ _ _ _ _ _ _ _ _ o o' o'').2 f g m).2 n).choose⟩

theorem obj_pull_same (o : Obj D l b s) (f : S' ⟶ S) : ∃ o' : Obj D l b (f ≫ s), Nonempty (ObjMap o' o f) :=
  obj_pull E H D l _ _ b b (RingHom.id _) _ _ s _ f rfl rfl (by rw [spMap_id', Category.comp_id]) o

end Obj

variable {Xo₂ : Moduli D l₂} (Q : LevelQuot l Xo₂)

theorem exists_lowers {B : Type} [CommRing B] {b : Base l B} {T : Scheme.{0}} {t : T ⟶ Sp B} {o : Obj D l b t}
    {z : T ⟶ Q.X} (n : ObjMap o Q.univ z) (y : T ⟶ Xo₂.X) (hy : y ≫ Q.π = z) :
    ∃ mu : SABMap o.t Xo₂.univ.t y, Lowers l Xo₂.univ o.eta o.etaA y mu.φ := by
  obtain ⟨mu, hmu⟩ := sab_cancel Q.m n.toSABMap y hy
  refine ⟨mu, fun a => sec_cancel mu Q.m _ _ ?_, fun a => sec_cancel mu Q.m _ _ ?_⟩
  · rw [hmu, Q.eta, ← Category.assoc, hy]; exact n.eta a
  · rw [hmu, Q.etaA, ← Category.assoc, hy]; exact n.etaA a

theorem hom_unique {B : Type} [CommRing B] {b : Base l B} {T : Scheme.{0}} [IsReduced T] {t : T ⟶ Sp B}
    {o : Obj D l b t} {f f' : T ⟶ Q.X} (h : f ≫ Q.s = f' ≫ Q.s) (m : ObjMap o Q.univ f) (m' : ObjMap o Q.univ f') :
    f = f' := by
  have := isSeparated_of_qproj Q.qproj
  have := Q.fin
  have := Q.onto
  refine (hom_eq_iff_forall_isAlgClosed Q.s h).mpr fun K _ _ x => ?_
  obtain ⟨ox, ⟨n⟩⟩ := obj_pull_same o x
  obtain ⟨u⟩ := obj_comp n m
  obtain ⟨u'⟩ := obj_comp n m'
  obtain ⟨y, hy⟩ := exists_lift_geom Q.π (x ≫ f)
  obtain ⟨y', hy'⟩ := exists_lift_geom Q.π (x ≫ f')
  obtain ⟨mu, hmu⟩ := exists_lowers Q u y hy
  obtain ⟨mu', hmu'⟩ := exists_lowers Q u' y' hy'
  rw [← hy, ← hy']
  refine Q.fibre K y y' ox.t mu mu' ox.eta ox.etaA ?_ hmu hmu'
  rw [← Q.overK, ← Category.assoc, ← Category.assoc, hy, hy', Category.assoc, Category.assoc, h]

def baseUp : Base l (KA l₂) where
  unit := (baseKA l₂).unit
  ρ := Q.jK (baseKA l).ρ
  ρ_sq := by rw [← map_pow, (baseKA l).ρ_sq, map_neg, map_natCast]
  ζ := Q.jK (baseKA l).ζ
  ζ_prim := (baseKA l).ζ_prim.map_of_injective Q.jK.injective

theorem baseKA_rho_coe (l : Level H) : (((baseKA l).ρ : KA l) : ℂ) = H.rt0 := rfl

theorem baseUp_rho_coe : (((baseUp Q).ρ : KA l₂) : ℂ) = (((baseKA l).ρ : KA l) : ℂ) := Q.jK_val (baseKA l).ρ

theorem baseUp_rho : (baseUp Q).ρ = (baseKA l₂).ρ :=
  Subtype.ext ((baseUp_rho_coe Q).trans ((baseKA_rho_coe l).trans (baseKA_rho_coe l₂).symm))

theorem baseUp_zeta (hd : l.A ∣ l₂.A) : (baseUp Q).ζ = (baseKA l₂).ζ ^ (l₂.A / l.A) := Subtype.ext (by
  rw [IntermediateField.coe_pow]
  exact (Q.jK_val _).trans (zeta_dvd l₂.A_pos hd))

theorem exists_cover (hL : Out.Laws) (hpq : 1 ≤ D.p + D.q) (hd : l.Dvd l₂) {S : Scheme.{0}} [IsReduced S]
    {s' : S ⟶ Sp (KA l)} (ob : Obj D l (baseKA l) s') :
    ∃ (S₂ : Scheme.{0}) (q : S₂ ⟶ S) (g : S₂ ⟶ Q.X) (s₂ : S₂ ⟶ Sp (KA l₂)) (o : Obj D l (baseUp Q) s₂),
      IsFinite q ∧ Etale q ∧ Surjective q ∧ g ≫ Q.s = q ≫ s' ∧ Nonempty (ObjMap o ob q) ∧
        Nonempty (ObjMap o Q.univ g) := by
  have := finiteDimensional_KA l₂
  obtain ⟨k1, k2, k3⟩ := finite_etale_onto_spMap Q.jK
  obtain ⟨o₁, ⟨n₁⟩⟩ := obj_pull E H D l _ _ (baseKA l) (baseUp Q) Q.jK _ _ s' (pullback.snd s' (spMap Q.jK))
    (pullback.fst _ _) rfl rfl pullback.condition ob
  obtain ⟨S₂, p, o₂, m, hf, he, hs, ⟨hm₁, hm₂⟩, -⟩ := GlobalTheory.T.exists_finiteEtale_deeper_level_cover hL E H D l l₂ _ (baseUp Q) (baseKA l₂) _ _ o₁ hpq hd
    (baseUp_rho Q) (baseUp_zeta Q hd.2.2)
  have hr : IsReduced S₂ := isReduced_of_smooth_of_isReduced (p ≫ pullback.fst s' (spMap Q.jK))
  obtain ⟨f₂, ⟨hf₂, ⟨u⟩⟩, -⟩ := Xo₂.rep S₂ _ hr o₂
  let o := ObjLower.lower o₂ hd (baseUp_rho Q) (baseUp_zeta Q hd.2.2)
  let mo : ObjMap o o₁ p := ⟨m, hm₁, hm₂⟩
  obtain ⟨z, hz⟩ := sab_comp u.toSABMap Q.m rfl
  refine ⟨S₂, p ≫ pullback.fst _ _, f₂ ≫ Q.π, _, o, inferInstance, inferInstance, inferInstance, ?_,
    obj_comp mo n₁, ⟨⟨z, fun a => ?_, fun a => ?_⟩⟩⟩
  · rw [Category.assoc, Q.overK, ← Category.assoc, hf₂, Category.assoc, Category.assoc, pullback.condition]
  · show (o₂.eta a ^ (l₂.M / l.M)).left ≫ z.φ = _
    rw [hz, ← Category.assoc, sec_pow u.toSABMap _ _ (u.eta a), Category.assoc, Q.eta, Category.assoc]
  · show (o₂.etaA a ^ (l₂.A / l.A)).left ≫ z.φ = _
    rw [hz, ← Category.assoc, sec_pow u.toSABMap _ _ (u.etaA a), Category.assoc, Q.etaA, Category.assoc]

end GlobalTheory.LevelQuotRep

namespace GlobalTheory

open LevelQuotRep in

theorem levelQuot_represents : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H) (Xo₂ : Moduli D l₂) (Q : LevelQuot l Xo₂), 1 ≤ D.p + D.q → l.Dvd l₂ → ∀ (S : Scheme.{0}) (s' : S ⟶ Sp (KA l)), IsReduced S → ∀ ob : Obj D l (baseKA l) s', ∃! f : S ⟶ Q.X, f ≫ Q.s = s' ∧ Nonempty (ObjMap ob Q.univ f) := by
  intro hL hL2 E _ _ _ H D l l₂ Xo₂ Q hpq hd S s' hS ob
  refine existsUnique_of_exists_of_unique ?_
    fun f f' ⟨h, ⟨m⟩⟩ ⟨h', ⟨m'⟩⟩ => hom_unique Q (h.trans h'.symm) m m'
  obtain ⟨S₂, q, g, s₂, o, hf, he, hs, hg, ⟨mq⟩, ⟨mg⟩⟩ := exists_cover Q hL hpq hd ob
  have key : pullback.fst q q ≫ g = pullback.snd q q ≫ g := by
    have : IsReduced (pullback q q) := isReduced_of_smooth_of_isReduced (pullback.fst q q ≫ q)
    obtain ⟨oR, ⟨n⟩⟩ := obj_pull_same o (pullback.fst q q)
    obtain ⟨n₁⟩ := obj_comp n mq
    obtain ⟨n'⟩ := obj_cancel mq n₁ (pullback.snd q q) pullback.condition.symm
    obtain ⟨u⟩ := obj_comp n mg
    obtain ⟨u'⟩ := obj_comp n' mg
    exact hom_unique Q (by rw [Category.assoc, Category.assoc, hg, pullback.condition_assoc]) u u'
  have hcoeq : ∀ {Z : Scheme.{0}} (g₁ g₂ : Z ⟶ S₂), g₁ ≫ q = g₂ ≫ q → g₁ ≫ g = g₂ ≫ g := fun g₁ g₂ h => by
    have := pullback.lift g₁ g₂ h ≫= key
    rwa [pullback.lift_fst_assoc, pullback.lift_snd_assoc] at this
  have hfac : q ≫ EffectiveEpi.desc q g hcoeq = g := EffectiveEpi.fac q g hcoeq
  refine ⟨EffectiveEpi.desc q g hcoeq, ?_, ?_⟩
  · rw [← cancel_epi q, ← Category.assoc, hfac, hg]
  · exact GlobalTheory.T.nonempty_objMap_of_finite_etale_surjective_cover hL hL2 E H D l _ _ _ _ _ _ _ _ _ _ _ _ Q.univ ob o q _ (Or.inl hS) hf he hs ⟨mq⟩
      (hfac.symm ▸ ⟨mg⟩)

end GlobalTheory
