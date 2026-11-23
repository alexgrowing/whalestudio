import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifPowOf3
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigIsoCongr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsGenRosati
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ProperRelAmpleKTrivOfFieldExtension

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GenericPol

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem exists_lift {K : Type} [Field K] {X Z : Scheme.{0}} (x : Spec (CommRingCat.of K) ⟶ X) (j : Z ⟶ X)
    (h : Set.range x ⊆ Set.range j) :
    ∃ (K' : Type) (_ : Field K') (i : K →+* K') (z : Spec (CommRingCat.of K') ⟶ Z), specOf i ≫ x = z ≫ j := by
  obtain ⟨z, hz⟩ := h ⟨(default : PrimeSpectrum K), rfl⟩
  obtain ⟨p, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := x) (g := j) _ z hz.symm
  let u := (pullback x j).fromSpecResidueField p
  refine ⟨(pullback x j).residueField p, inferInstance, (Spec.preimage (u ≫ pullback.fst x j)).hom,
    u ≫ pullback.snd x j, ?_⟩
  have e : specOf (Spec.preimage (u ≫ pullback.fst x j)).hom = u ≫ pullback.fst x j :=
    Spec.map_preimage _
  rw [e]
  exact (Category.assoc _ _ _).trans ((congrArg (u ≫ ·) pullback.condition).trans (Category.assoc _ _ _).symm)

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] {H : Host E}

theorem proper_ample_kTriv {X Z : Scheme.{0}} {T : SAB H X} {T' : SAB H Z} {j : Z ⟶ X} (mj : SABMap T' T j)
    (hp : IsProper T'.G.hom) (hA : RelAmple T'.G T'.PP.L) (hK : KTriv T'.G T'.PP.L) {K : Type} [Field K]
    {x : Spec (CommRingCat.of K) ⟶ X} {t : SAB H (Spec (CommRingCat.of K))} (m : SABMap t T x)
    (h : Set.range x ⊆ Set.range j) : IsProper t.G.hom ∧ RelAmple t.G t.PP.L ∧ KTriv t.G t.PP.L := by
  obtain ⟨K', _, i, z, e⟩ := exists_lift x j h
  obtain ⟨PP', cub, sym, adj, prim, m₁, -⟩ := sabPull CubePf.cubePull (specOf i) t
  generalize (⟨(Over.pullback (specOf i)).obj t.G, IsSemiAbelian.pullback _ t.G t.semi,
    Geo.Tor.OAct.pullback _ t.G t.act, PP', cub, sym, adj, prim⟩ : SAB H _) = t' at m₁
  obtain ⟨n, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m m₁
  obtain ⟨m', -⟩ := sabCancel pullCubCancel E H _ _ _ T T' t' j z mj (e ▸ n)
  obtain ⟨w, g, -⟩ := m'.lin
  obtain ⟨w₁, g₁, -⟩ := m₁.lin
  obtain ⟨U, hU, hc, -⟩ := exists_isAffineOpen_mem_and_subset (X := Z) (U := ⊤)
    (x := z (IsLocalRing.closedPoint K')) trivial
  have hy : ∀ y, z y ∈ U := fun y =>
    (congrArg (fun V => y ∈ V) (Scheme.preimage_eq_top_of_closedPoint_mem z hc)).mpr trivial
  have := t.semi.smooth
  have := t.semi.separated
  have := t.semi.quasiCompact
  exact GlobalTheory.AmpleDescent.proper_relAmple_kTriv_of_fieldExtension K K' i t.G t'.G m₁.φ m₁.cart t.PP.L t'.PP.L t.PP.isLB t'.PP.isLB ⟨w₁, g₁⟩
    (MorphismProperty.of_isPullback (P := @IsProper) m'.cart.1 hp)
    (relAmple_pull m'.cart.1 T'.PP.isLB t'.PP.isLB ((isGen_iff w).1 g) U hU hy hA)
    (kTriv_pull m'.cart T'.PP.isLB t'.PP.isLB ((isGen_iff w).1 g) hK)

def toPolAV {S : Scheme.{0}} (t : SAB H S) (g : ℕ) (hg : SmoothOfRelativeDimension g t.G.hom) (hp : IsProper t.G.hom)
    (hA : RelAmple t.G t.PP.L) (hK : KTriv t.G t.PP.L) : PolAV S where
  A := t.G
  isAb := ⟨t.semi.comm, t.semi.smooth, hp, t.semi.geomConnected⟩
  g := g
  smoothDim := hg
  L := t.PP.L
  isLB := t.PP.isLB
  rigid := ⟨t.PP.rig, t.PP.rigGen⟩
  sym := by
    obtain ⟨-, w, hw, -⟩ := t.sym
    exact fun _ => ⟨⊤, trivial, gen_of_iso ((isGen_iff w).1 hw) _⟩
  ample := hA
  ktriv := hK

theorem rosatiAdj {S : Scheme.{0}} (t : SAB H S) (a : NumberField.RingOfIntegers E) :
    RosatiAdj t.G t.PP.L (t.act.act a) (t.act.act (H.bar a)) := by
  obtain ⟨u, hu⟩ := GlobalTheory.NormRos.exists_gen_rosati t.PP.isLB _ _ (t.adj a)
  exact fun _ => ⟨⊤, trivial, LB.pullGen _ _ _ u _, DVR.pullGen_isGen _ _ _ _ hu _⟩

end GlobalTheory.GenericPol

open GlobalTheory.GenericPol ReciprocityTheory.ChartRestriction.G.Geo.Tor in

theorem GlobalTheory.exists_polAV_genericFibre : ∀ (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (H : Geo.Tor.Host E) (Dm : Geo.Tor.Datum H) (l : Geo.Tor.Level H) (Xo : Geo.Tor.Moduli Dm l) (c : Geo.Tor.Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Geo.Tor.Model Xo c β) (R : Type) [CommRing R] [IsDomain R] (χ : Geo.Tor.Sp R ⟶ Y.X) (t : Geo.Tor.SAB H (Geo.Tor.Sp R)) (_ : Geo.Tor.SABMap t Y.t χ), Set.range (jK R ≫ χ) ⊆ Set.range Y.j → ∀ g : ℕ, SmoothOfRelativeDimension g t.G.hom → ∃ (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (eA : (Over.pullback (jK R)).obj t.G ≅ A.A) (oA : letI := H.starRing; A.OAct (NumberField.RingOfIntegers E)), A.g = g ∧ IsMonHom eA.hom ∧ Geo.Tor.LBIso (A.L.pull eA.hom.left) (t.PP.L.pull (pullback.fst t.G.hom (jK R))) ∧ (letI := H.starRing; ∀ a, (Over.pullback (jK R)).map (t.act.act a) ≫ eA.hom = eA.hom ≫ oA.act a) := by
  intro E _ _ _ H Dm l Xo c O _ β Y R _ _ χ t m h g hg
  let := H.starRing
  obtain ⟨PP', cub, sym, adj, prim, m₁, hm₁⟩ := sabPull CubePf.cubePull (jK R) t
  let t' : SAB H (Spec (CommRingCat.of (FractionRing R))) :=
    ⟨(Over.pullback (jK R)).obj t.G, IsSemiAbelian.pullback _ t.G t.semi,
      Geo.Tor.OAct.pullback _ t.G t.act, PP', cub, sym, adj, prim⟩
  let m₀ : SABMap t' t (jK R) := m₁
  have hm₀ : m₀.cm.F = pullback.fst t.G.hom (jK R) := hm₁
  obtain ⟨n, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m m₀
  obtain ⟨hp, hA, hK⟩ := proper_ample_kTriv Y.m Y.oF.proper Y.oF.ample Y.oF.ktriv n h
  have hg' : SmoothOfRelativeDimension g t'.G.hom := by
    show SmoothOfRelativeDimension g (pullback.snd t.G.hom (jK R))
    exact (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _) hg
  obtain ⟨w, hw, -⟩ := m₀.lin
  have hL : LBIso t'.PP.L (t.PP.L.pull (pullback.fst t.G.hom (jK R))) := hm₀ ▸ ⟨w, hw⟩
  refine ⟨toPolAV t' g hg' hp hA hK, Iso.refl _, ⟨t'.act.toRingAct, rosatiAdj t'⟩, rfl, ?_, ?_, fun a => ?_⟩
  · exact inferInstanceAs (IsMonHom (𝟙 t'.G))
  · exact LBIso.chartPull (Geo.Tor.chartPullPull t'.PP.L (𝟙 _) (𝟙 _) rfl) (Geo.Tor.chartPullId _) hL
  · exact (Category.comp_id _).trans (Category.id_comp _).symm
