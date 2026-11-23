import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN

namespace GlobalTheory.LN.GenericPoint

theorem exists_extend {F K : Type} [Field F] [CharZero F] [Algebra.IsAlgebraic ℚ F] [Field K] [CharZero K]
    (V : ValuationSubring F) (g : V →+* K) : ∃ g' : F →+* K, g'.comp V.subtype = g := by
  have hinj : Function.Injective g := by
    rw [RingHom.injective_iff_ker_eq_bot, eq_bot_iff]
    intro a ha
    by_contra h0
    have hF : IsAlgebraic ℤ (a : F) :=
      (IsFractionRing.isAlgebraic_iff ℤ ℚ F).2 (Algebra.IsAlgebraic.isAlgebraic _)
    have hV : IsAlgebraic ℤ a :=
      (isAlgebraic_algHom_iff (V.subtype.toIntAlgHom) Subtype.val_injective).1 hF
    refine Ideal.comap_ne_bot_of_algebraic_mem h0 ha hV (eq_bot_iff.2 fun n hn => ?_)
    have e : (n : K) = 0 := by simpa using hn
    exact_mod_cast e
  exact ⟨IsFractionRing.lift hinj, RingHom.ext fun a => IsFractionRing.lift_algebraMap hinj a⟩

theorem jK_mem {R : Type} [CommRing R] [IsDomain R] {U : Set (Sp R)} (hU : IsOpen U) (h : U.Nonempty)
    (q : Sp (FractionRing R)) : jK R q ∈ U := by
  obtain ⟨x, hx⟩ := h
  refine Specializes.mem_open (x := jK R q) (y := x) ?_ hU hx
  refine (PrimeSpectrum.le_iff_specializes (R := R) _ _).1 fun a ha => ?_
  have hq : q.asIdeal = ⊥ := (Ideal.eq_bot_or_top q.asIdeal).resolve_right q.isPrime.ne_top
  have h1 : algebraMap R (FractionRing R) a ∈ q.asIdeal := ha
  rw [hq, Ideal.mem_bot, map_eq_zero_iff _ (IsFractionRing.injective R (FractionRing R))] at h1
  rw [h1]; exact Ideal.zero_mem _

theorem lbIso_pull {W X Y : Scheme.{0}} {L : LB X} {M : LB Y} {a : Y ⟶ X} (h : LBIso M (L.pull a)) (j : W ⟶ Y)
    {a' : W ⟶ X} (ha : a' = j ≫ a) : LBIso (M.pull j) (L.pull a') :=
  LBIso.chartPull (Geo.Tor.chartPullPull M j j rfl) (chartPullSame L _ _ _ j fun _ => ha) h

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem lbIso_of_sabMap {S S' : Scheme.{0}} {t' : SAB H S'} {t : SAB H S} {f : S' ⟶ S} (m : SABMap t' t f) :
    LBIso t'.PP.L (t.PP.L.pull m.φ) := by
  obtain ⟨w, hw, -⟩ := m.lin
  exact ⟨w, hw⟩

theorem polAt_of_lift {X S Z : Scheme.{0}} {T : SAB H X} {t : SAB H S} {t' : SAB H Z} {ξ : S ⟶ X} {j : Z ⟶ X}
    (m : SABMap t T ξ) (m' : SABMap t' T j) (hp : IsProper t'.G.hom) (hA : RelAmple t'.G t'.PP.L)
    (hK : KTriv t'.G t'.PP.L) {K : Type} [Field K] (x : Sp K ⟶ S) (y : Sp K ⟶ Z) (h : y ≫ j = x ≫ ξ) : PolAt t x := by
  have g₁ : IsGrpPullback ((Over.pullback x).obj t.G) T.G (x ≫ ξ) (pullback.fst t.G.hom x ≫ m.φ) :=
    (isGrpPullback_pullback t.G x).comp m.cart
  have w : (pullback.fst t.G.hom x ≫ m.φ) ≫ T.G.hom = (pullback.snd t.G.hom x ≫ y) ≫ j :=
    g₁.1.w.trans (by rw [Category.assoc, h]; rfl)
  obtain ⟨ψ, h₁, h₂⟩ : ∃ ψ : pullback t.G.hom x ⟶ t'.G.left,
      ψ ≫ m'.φ = pullback.fst t.G.hom x ≫ m.φ ∧ ψ ≫ t'.G.hom = pullback.snd t.G.hom x ≫ y :=
    ⟨_, m'.cart.1.lift_fst _ _ w, m'.cart.1.lift_snd _ _ w⟩
  have g₂ : IsGrpPullback ((Over.pullback x).obj t.G) t'.G y ψ :=
    m'.cart.cancel (g₁.congr h.symm h₁.symm) h₂
  have e : LBIso (t.PP.L.pull (pullback.fst t.G.hom x)) (t'.PP.L.pull ψ) :=
    LBIso.trans (pull_isLB t.PP.isLB _) (pull_isLB T.PP.isLB _) (pull_isLB t'.PP.isLB _)
      (lbIso_pull (lbIso_of_sabMap m) _ rfl) (lbIso_pull (lbIso_of_sabMap m') _ h₁.symm).symm
  have hp' : IsProper (pullback.snd t.G.hom x) := MorphismProperty.of_isPullback (P := @IsProper) g₂.1 hp
  have hq := amplePt Z K y t'.G ((Over.pullback x).obj t.G) ψ g₂ t'.PP.L (t.PP.L.pull (pullback.fst t.G.hom x))
    t'.PP.isLB (pull_isLB t.PP.isLB (pullback.fst t.G.hom x)) e hA hK
  exact ⟨hp', hq.1, hq.2⟩

end GlobalTheory.LN.GenericPoint

open GlobalTheory.LN.GenericPoint in

theorem GlobalTheory.LN.generic_point_of_meets_abLocus : Laws → Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (W₀ : ValuationSubring ℂ) (Y : Model Xo c (c.V W₀).subtype) (p : ℕ), Y.LevelStructureConditions p → ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (ξ : Sp R ⟶ Y.X) (t : SAB H (Sp R)) (_ : SABMap t Y.t ξ), (ξ ⁻¹' abLocus Y.t.G).Nonempty → (∃ y : Sp (FractionRing R) ⟶ Xo.XF c, y ≫ Y.j = jK R ≫ ξ) ∧ PolAt t (jK R) ∧ ξ ⁻¹' abLocus Y.t.G = abLocus t.G := by
  intro _ _ E _ _ _ H D l Xo c W₀ Y p ⟨_, _, _, ⟨U, hU, _⟩, _⟩ R _ _ _ ξ t m hne
  have hop : IsOpen (ξ ⁻¹' abLocus Y.t.G) := by
    rw [← hU]; exact U.isOpen.preimage ξ.continuous
  have := c.fin
  obtain ⟨g, hg⟩ := exists_extend (K := FractionRing R) (c.V W₀) (Spec.preimage ((jK R ≫ ξ) ≫ Y.s)).hom
  have sq : (jK R ≫ ξ) ≫ Y.s = spMap g ≫ spMap (c.V W₀).subtype := by
    rw [← Geo.Tor.spMap_comp, hg]
    exact (Spec.map_preimage _).symm
  have := Y.jQ_open
  have hr : Set.range (pullback.lift _ _ sq) ⊆ Set.range Y.jQ := by
    rintro _ ⟨q, rfl⟩
    rw [← Y.ab_gen, Set.mem_preimage, ← Scheme.Hom.comp_apply, pullback.lift_fst, Scheme.Hom.comp_apply]
    exact jK_mem hop hne q
  have hy : IsOpenImmersion.lift Y.jQ _ hr ≫ Y.j = jK R ≫ ξ := by
    rw [Model.j, ← Category.assoc, IsOpenImmersion.lift_fac, pullback.lift_fst]
  exact ⟨⟨_, hy⟩, polAt_of_lift m Y.m Y.oF.proper Y.oF.ample Y.oF.ktriv _ _ hy,
    Set.ext fun x => abLocus_pullback abLocusOne Y.t.semi m.cart.1 x⟩
