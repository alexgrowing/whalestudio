import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPeriodGens
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelPointLiftZeroFirstCoordinateStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsNumberFieldQkPointsComplexDegeneration
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DivTorsRat

open GlobalTheory.TorusExt

attribute [local instance] gtGroup

theorem exists_char_descend {X K F : Type} [Group X] [Field K] [Field F] (f : K →+* F) {k : ℕ} (hk : k ≠ 0) {ζ : K}
    (hζ : IsPrimitiveRoot ζ k) (t : X →* Fˣ) (ht : t ^ k = 1) :
    ∃ t₀ : X →* Kˣ, (Units.map f.toMonoidHom).comp t₀ = t := by
  have hinj : Function.Injective (Units.map f.toMonoidHom) := Units.map_injective f.injective
  have : NeZero k := ⟨hk⟩
  have hr : ∀ x, t x ∈ (Units.map f.toMonoidHom).range := fun x => by
    have h1 : ((t x : Fˣ) : F) ^ k = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← MonoidHom.pow_apply, ht]; rfl
    obtain ⟨i, -, hi⟩ := (hζ.map_of_injective f.injective).eq_pow_of_pow_eq_one h1
    exact ⟨(hζ.isUnit hk).unit ^ i, Units.ext (by simpa using hi)⟩
  refine ⟨(MonoidHom.ofInjective hinj).symm.toMonoidHom.comp (t.codRestrict _ hr), MonoidHom.ext fun x => ?_⟩
  exact MonoidHom.apply_ofInjective_symm hinj _

theorem exists_qkExt_of_b {V : Type} [CommRing V] [IsDomain V] {Q : DegPre V} (hB : Q.TauBimult) {K F : Type} [Field K]
    [Field F] [Algebra (FractionRing V) K] [Algebra (FractionRing V) F] (f : K →+* F)
    (hf : f.comp (algebraMap (FractionRing V) K) = algebraMap (FractionRing V) F) {k : ℕ} (hk : k ≠ 0) {ζ : K}
    (hζ : IsPrimitiveRoot ζ k) (p : QkPt Q F k) (hp : p.y = 0) (q : QkPt Q K k) (hq : q.y = 0)
    (hb : p.g.b.left = spMap f ≫ q.g.b.left) : ∃ p₀ : QkPt Q K k, QkExt f p₀ p := by
  have hb' : p.g.b = (gtExt Q f hf q.g).b := (Over.OverMorphism.ext hb).trans (gtExt_b f hf _).symm
  have np : k • p.g = 0 := by rw [qk_nsmul hB, hp, map_zero]
  have nq : k • q.g = 0 := by rw [qk_nsmul hB, hq, map_zero]
  obtain ⟨t, ht⟩ := exists_torusPt_eq (g := p.g + -(gtExt Q f hf q.g)) (by rw [add_b, neg_b, hb', mul_inv_cancel])
  have tk : t ^ k = 1 := by
    have : torusPt Q F (Additive.ofMul (t ^ k)) = torusPt Q F (Additive.ofMul 1) := by
      rw [ofMul_pow, map_nsmul, ← ht, nsmul_add, smul_neg, ← map_nsmul, np, nq, ofMul_one, map_zero, map_zero, neg_zero,
        add_zero]
    exact torusPt_injective this
  obtain ⟨t₀, rfl⟩ := exists_char_descend f hk hζ t tk
  have t0 : t₀ ^ k = 1 := MonoidHom.ext fun x => Units.map_injective (f := f.toMonoidHom) f.injective (by
    have := DFunLike.congr_fun tk x
    rw [MonoidHom.pow_apply, map_pow, MonoidHom.one_apply, map_one]
    exact this)
  refine ⟨qkMk hB 0 (q.g + torusPt Q K (Additive.ofMul t₀)) ?_, (qkExt_iff hB f hf _ _).2 (qk_ext hp ?_)⟩
  · rw [nsmul_add, nq, ← map_nsmul, ← ofMul_pow, t0, ofMul_one, map_zero, map_zero, add_zero]
  · show p.g = gtExt Q f hf (q.g + torusPt Q K (Additive.ofMul t₀))
    rw [map_add, GlobalTheory.QkNumberField.gtExt_torusPt, ← ht]
    abel

theorem exists_ptEquiv {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {F : G'.left ⟶ G.left} (gp : IsGrpPullback G' G f F) (T : Over S') (b : T.left ⟶ S) (hb : b = T.hom ≫ f) :
    ∃ ρ : (T ⟶ G') ≃* (Over.mk b ⟶ G), ∀ x, (ρ x).left = x.left ≫ F := by
  subst hb
  refine ⟨MulEquiv.ofBijective (pushHom gp T) ⟨fun x y e => ?_, fun y => ?_⟩, fun _ => rfl⟩
  · exact Over.OverMorphism.ext (gp.1.hom_ext (congrArg (fun q => q.left) e) ((Over.w x).trans (Over.w y).symm))
  · exact ⟨Over.homMk (gp.1.lift y.left T.hom (Over.w y)) (gp.1.lift_snd _ _ _),
      Over.OverMorphism.ext (gp.1.lift_fst _ _ _)⟩

theorem exists_etaA {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}
    {B W : Type} [CommRing B] [CommRing W] {b : Geo.Tor.Base l B} {σ : B →+* W} (o : Obj D l b (spMap σ)) {F : Type} [Field F]
    [IsAlgClosed F] (j : W →+* F) (x : Over.mk (spMap j) ⟶ o.t.G) (hx : x ^ l.A = 1) :
    ∃ a, x.left = spMap j ≫ (o.etaA a).left := by
  obtain ⟨-, I, -, h, -⟩ := o.geom F (spMap j) (j.comp σ) (by
    rw [spMap, spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp])
  obtain ⟨a, ha⟩ := (I.onto l.A l.A_pos x).1 hx
  refine ⟨a, ?_⟩
  rw [← ha, ← h]
  simp

theorem exists_qkExt_of_divFrom : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (iw : L.W →+* R) {I : Type} [Fintype I] (s : I → R) (ε : I → LinearMap.BilinForm ℤ L.D.X) (e : P.D.toPre.X ≃ₗ[𝓞 E] L.D.X), (∀ k, ε k ∈ balForms H.bar L.D.X) → (∀ k, s k ≠ 0) → DivFrom L P.D.toPre P.oD iw s ε e → ∀ p : QkPt P.D.toPre (AlgebraicClosure (FractionRing R)) l.M', p.y = 0 → ∃ p₀ : QkPt P.D.toPre (FractionRing R) l.M', QkExt (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R))) p₀ p := by
  intro E _ _ _ H D' l c L R _ _ _ _ t P iw I _ s ε e hε hs ⟨g, hD, hdiv⟩ p hp
  have hB := P.D.tau_bimult
  have hM : 0 < l.M' := (LowDat.lowLevel l).A_pos
  let K := FractionRing R
  let F := AlgebraicClosure K
  let j : L.W →+* F := (algebraMap K F).comp ((algebraMap R K).comp iw)
  have hj : spMap j = (TF (R := R) F).hom ≫ spMap iw := by
    show _ = (jFK (R := R) F ≫ jK R) ≫ spMap iw
    simp only [j, jFK, jK, spMap, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
  have gp : IsGrpPullback P.D.toPre.P.A L.D.P.A (spMap iw) (hD.e.hom.left ≫ pullback.fst L.D.P.A.hom (specOf iw)) :=
    pull_grp hD
  obtain ⟨ρ₁, h₁⟩ := exists_ptEquiv gp (TF (R := R) F) (spMap j) hj
  obtain ⟨ρ₂, h₂⟩ := exists_ptEquiv L.ab.1 (Over.mk (spMap j)) (spMap j) (Category.comp_id _).symm
  have hbk : p.g.b ^ l.M' = 1 := by rw [← nsmul_b, qk_nsmul hB, hp, map_zero, zero_b]
  obtain ⟨a, ha⟩ := exists_etaA L.o j (ρ₂.symm (ρ₁ p.g.b)) (by
    show _ ^ l.M' = 1
    rw [← map_pow, ← map_pow, hbk, map_one, map_one])
  obtain ⟨q, hq, hqb⟩ := GlobalTheory.T.exists_levelPoint_lift_zero_first_coordinate L P.D.toPre P.oD iw s ε e g hD hε hs hdiv a
  have hζ : IsPrimitiveRoot (⟨zeta l.M', c.zeta_mem⟩ : c.F) l.M' :=
    IsPrimitiveRoot.of_map_of_injective (f := c.F.val.toRingHom) (Complex.isPrimitiveRoot_exp l.M' hM.ne')
      Subtype.val_injective
  refine exists_qkExt_of_b hB (algebraMap K F) (RingHom.comp_id _) hM.ne'
    (hζ.map_of_injective ((algebraMap R K).comp (iw.comp L.b)).injective) p hp q hq ?_
  have e₂ := h₂ (ρ₂.symm (ρ₁ p.g.b))
  rw [ρ₂.apply_symm_apply, ha, h₁] at e₂
  refine gp.1.hom_ext (e₂.trans (Eq.symm ((Category.assoc _ _ _).trans
    ((congrArg (spMap (algebraMap K F) ≫ ·) hqb).trans ?_)))) ?_
  · rw [hj]
    show _ = (((spMap (algebraMap K F) ≫ jK R) ≫ _) ≫ _) ≫ _
    simp only [Category.assoc]
  · exact (Over.w p.g.b).trans ((Over.w (extMap (R := R) (algebraMap K F) (RingHom.comp_id _) ≫ q.g.b)).symm)

end GlobalTheory.DivTorsRat
