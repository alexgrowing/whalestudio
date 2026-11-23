import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHTFormOver
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeInnerProductPullbackIffStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace PositivityTheory.UnitarySelfGeneration

theorem gr_one {S S' T : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (a : T ⟶ S') (b : T ⟶ S) (e : a ≫ f = b) :
    (1 : Over.mk a ⟶ G').left ≫ φ = (1 : Over.mk b ⟶ G).left := by
  subst e
  exact congrArg (fun z => z.left) (map_one (pushHom h (Over.mk a)))

theorem gr_dual {R R' : Type} [CommRing R] [CommRing R'] (s : R →+* R') :
    spMap (dualMap s) ≫ spMap (algebraMap R (DualNumber R)) = spMap (algebraMap R' (DualNumber R')) ≫ spMap s := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem gr_core {X : Scheme.{0}} {Ω R : Type} [Field Ω] [CommRing R] {x : Sp R ⟶ X} (hx : Mono x)
    (z : Sp ℂ ⟶ X) (s : R →+* ℂ) (k : R →+* Ω) (hz : spMap s ≫ x = z)
    {G G' : Over X} [GrpObj G] [GrpObj G'] {Gp : Over (Sp R)} [GrpObj Gp]
    {φ : Gp.left ⟶ G.left} {φ' : Gp.left ⟶ G'.left} (h : IsGrpPullback Gp G x φ) (h' : IsGrpPullback Gp G' x φ')
    (m : Sp (DualNumber Ω) ⟶ G.left) (m' : Sp (DualNumber Ω) ⟶ G'.left) (u : Sp (DualNumber Ω) ⟶ Gp.left)
    (hu : u ≫ φ = m) (hu' : u ≫ φ' = m') (v : epsAt z ⟶ G) (a : epsAt x ⟶ G) (ha1 : IsTanAt G x a)
    (ha2 : m = spMap (dualMap k) ≫ a.left) (ha3 : v.left = spMap (dualMap s) ≫ a.left) :
    ∃ (v₀ : epsAt (spMap s) ⟶ Gp) (v' : epsAt z ⟶ G') (a' : epsAt x ⟶ G'),
      v₀.left ≫ φ = v.left ∧ v₀.left ≫ φ' = v'.left ∧ IsTanAt G' x a' ∧ m' = spMap (dualMap k) ≫ a'.left ∧
        v'.left = spMap (dualMap s) ≫ a'.left := by
  have : Mono φ := (MorphismProperty.monomorphisms _).of_isPullback h.1.flip
    (MorphismProperty.monomorphisms.infer_property _)
  obtain ⟨l, hl1, hl2⟩ : ∃ l : Sp (DualNumber R) ⟶ Gp.left, l ≫ φ = a.left ∧
      l ≫ Gp.hom = spMap (algebraMap R (DualNumber R)) :=
    ⟨h.1.lift a.left _ (Over.w a), h.1.lift_fst _ _ _, h.1.lift_snd _ _ _⟩
  have w0 : (spMap (dualMap s) ≫ l) ≫ Gp.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap s := by
    rw [Category.assoc, hl2]
    exact gr_dual _
  have w1 : (l ≫ φ') ≫ G'.hom = spMap (algebraMap R (DualNumber R)) ≫ x := by
    rw [Category.assoc, h'.1.w, ← Category.assoc, hl2]
  have w2 : ((spMap (dualMap s) ≫ l) ≫ φ') ≫ G'.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ z := by
    rw [Category.assoc, h'.1.w, ← Category.assoc, w0, Category.assoc, hz]
  refine ⟨Over.homMk _ w0, Over.homMk _ w2, Over.homMk _ w1, ?_, rfl, ?_, ?_, Category.assoc _ _ _⟩
  · exact (Category.assoc _ _ _).trans ((congrArg _ hl1).trans ha3.symm)
  · have e : spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ l = (1 : Over.mk (𝟙 (Sp R)) ⟶ Gp).left := by
      rw [← cancel_mono φ]
      exact (Category.assoc _ _ _).trans ((congrArg _ hl1).trans
        (Eq.trans ha1 (gr_one h _ _ (Category.id_comp _)).symm))
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ φ') e).trans (gr_one h' _ _ (Category.id_comp _)))
  · have e : u = spMap (dualMap k) ≫ l := by
      rw [← cancel_mono φ, hu, Category.assoc, hl1]
      exact ha2
    exact hu'.symm.trans ((congrArg (· ≫ φ') e).trans (Category.assoc _ _ _))

theorem gr_half {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} (z : Sp ℂ ⟶ X)
    {G G' : Over X} [GrpObj G] [GrpObj G'] {Gp : Over (Spec (X.presheaf.stalk (centre z)))} [iG : GrpObj Gp]
    {φ : Gp.left ⟶ G.left} {φ' : Gp.left ⟶ G'.left} (h : IsGrpPullback Gp G (X.fromSpecStalk _) φ)
    (h' : IsGrpPullback Gp G' (X.fromSpecStalk _) φ') {L : LB G.left} {L' : LB G'.left}
    {V : Type} [AddCommGroup V] [Module Ω V] (M : LieModel G ξ V) (M' : LieModel G' ξ V)
    (tie : ∀ e, ∃ v : Sp (DualNumber Ω) ⟶ Gp.left, v ≫ φ = (M.pt e).left ∧ v ≫ φ' = (M'.pt e).left)
    (ip : ∀ (v₀ w₀ : epsAt (R := ℂ) (Spec.map (Scheme.stalkClosedPointTo z)) ⟶ Gp) (v w : epsAt z ⟶ G)
      (v' w' : epsAt z ⟶ G') (c : ℂ), v₀.left ≫ φ = v.left → w₀.left ≫ φ = w.left → v₀.left ≫ φ' = v'.left →
      w₀.left ≫ φ' = w'.left → HodgeIP G L z v w c → HodgeIP G' L' z v' w' c)
    {r : ℕ} (b : Fin r → V) (Γ : Matrix (Fin r) (Fin r) ℂ) (hG : M.GramAt L z b Γ) : M'.GramAt L' z b Γ := by
  obtain ⟨v, hv, hΓ⟩ := hG
  have hz : Spec.map (Scheme.stalkClosedPointTo z) ≫ X.fromSpecStalk (centre z) = z :=
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk z
  have key : ∀ i, ∃ (v₀ : epsAt (R := ℂ) (Spec.map (Scheme.stalkClosedPointTo z)) ⟶ Gp) (v' : epsAt z ⟶ G'),
      v₀.left ≫ φ = (v i).left ∧ v₀.left ≫ φ' = v'.left ∧ M'.ValAt z (b i) v' := by
    intro i
    obtain ⟨hs, a, ⟨ha1, ha2⟩, ha3⟩ := hv i
    obtain ⟨u, hu, hu'⟩ := tie (b i)
    obtain ⟨v₀, v', a', k1, k2, k3, k4, k5⟩ := @gr_core X Ω (X.presheaf.stalk (centre z)) _ _
      (X.fromSpecStalk (centre z)) (inferInstanceAs (Mono (X.fromSpecStalk (centre z)))) z
      (Scheme.stalkClosedPointTo z).hom (genMap ξ ⟨centre z, hs⟩) hz G G' _ _ Gp iG φ φ' h h'
      _ _ u hu hu' (v i) a ha1 ha2 ha3
    exact ⟨v₀, v', k1, k2, hs, a', ⟨k3, k4⟩, k5⟩
  choose v₀ v' k1 k2 k3 using key
  exact ⟨v', k3, fun p q => ip (v₀ p) (v₀ q) _ _ _ _ _ (k1 p) (k1 q) (k2 p) (k2 q) (hΓ p q)⟩

theorem gr_ip {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S' : Scheme.{0}} {t : SAB H S}
    {t' : SAB H S'} {f : S' ⟶ S} (m : SABMap t' t f) (z' : Sp ℂ ⟶ S') (z : Sp ℂ ⟶ S) (e : z' ≫ f = z)
    (v' w' : epsAt z' ⟶ t'.G) (v w : epsAt z ⟶ t.G) (c : ℂ) (hv : v'.left ≫ m.φ = v.left)
    (hw : w'.left ≫ m.φ = w.left) : HodgeIP t'.G t'.PP.L z' v' w' c ↔ HodgeIP t.G t.PP.L z v w c := by
  subst e
  exact GlobalTheory.T.hodge_inner_product_pullback_iff E H S S' t t' f m z' v' w' v w c hv hw

theorem gram_matrix_twisted_lie_models : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (g : HostAut H) (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (p : Cpt ξ) (t t' : SAB H X) (tp : SAB H (Spec (X.presheaf.stalk p.1))) (m : SABMap tp t (X.fromSpecStalk p.1)) (m' : SABMap (twistSAB tp g) t' (X.fromSpecStalk p.1)) (V : Type) [AddCommGroup V] [Module Ω V] (M : LieModel t.G ξ V) (M' : LieModel t'.G ξ V), (∀ e, ∃ v : Sp (DualNumber Ω) ⟶ tp.G.left, v ≫ m.φ = (M.pt e).left ∧ v ≫ m'.φ = (M'.pt e).left) → ∀ (z : Sp ℂ ⟶ X), centre z = p.1 → ∀ (r : ℕ) (b : Fin r → V) (Γ : Matrix (Fin r) (Fin r) ℂ), M.GramAt t.PP.L z b Γ ↔ M'.GramAt t'.PP.L z b Γ := by
  rintro E _ _ _ H g X Ω _ ξ ⟨q, hq⟩ t t' tp m m' V _ _ M M' tie z (rfl : centre z = q) r b Γ
  have hz : Spec.map (Scheme.stalkClosedPointTo z) ≫ X.fromSpecStalk (centre z) = z :=
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk z
  constructor
  · refine gr_half z m.cart m'.cart M M' tie (fun v₀ w₀ v w v' w' c a1 a2 a3 a4 hh => ?_) b Γ
    exact (gr_ip m' _ z hz v₀ w₀ v' w' c a3 a4).1 ((gr_ip m _ z hz v₀ w₀ v w c a1 a2).2 hh)
  · refine gr_half z m'.cart m.cart M' M (fun e => (tie e).imp fun _ h => h.symm)
      (fun v₀ w₀ v w v' w' c a1 a2 a3 a4 hh => ?_) b Γ
    exact (gr_ip m _ z hz v₀ w₀ v' w' c a3 a4).1 ((gr_ip m' _ z hz v₀ w₀ v w c a1 a2).2 hh)

end PositivityTheory.UnitarySelfGeneration
