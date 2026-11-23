import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.ArcFramePointTruncation

noncomputable section

namespace GlobalTheory.QkPullDirect

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.TorusExt GlobalTheory.ArcPull GlobalTheory.IndefiniteRowSideFullHecke.SectionsThroughEpsilonPoints
open scoped CategoryTheory.Obj

section Charts

variable {X X' Y Y' Y'' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K : Type} [Fintype K]

theorem gm_of_corr (hL : L.IsLB) {φ : K → (Y ⟶ X)} {φ' : K → (Y' ⟶ X)} {ε : K → ℤ} {h : Y' ⟶ Y}
    (hφ : ∀ k, φ' k = h ≫ φ k) {t : LB.Gen (LB.LinComb L φ ε)} {t' : LB.Gen (LB.LinComb L φ' ε)} (ht : t.IsGen)
    (ht' : t'.IsGen) (H : LB.Gen.Corr L φ' ε (fun k => h ≫ φ k) ε t' (LB.pullGen L φ ε t h)) {Z : Scheme.{0}}
    (r : Z ⟶ Y') (z : Z) (p : K → L.ι) (hp : ∀ k, φ' k (r z) ∈ L.U (p k)) :
    gm r z (LB.wchart L φ' p) (t'.s p) = gm (r ≫ h) z (LB.wchart L φ p) (t.s p) := by
  obtain rfl : φ' = fun k => h ≫ φ k := funext hφ
  obtain ⟨J, hJ, -⟩ := exists_good L hL z (K := PEmpty) PEmpty.elim PEmpty.elim (fun a => a.elim) (fun a => a.elim)
  have e := (val_corr hJ H r).trans (val_pull hJ t h r)
  rw [val_of t (r ≫ h) z J (fun k => J (r ≫ h ≫ φ k)) (fun k => by rw [Category.assoc])] at e
  have m₀ := hJ.mem (fun k => h ≫ φ k) r
  have m₁ : r z ∈ LB.wchart L (fun k => h ≫ φ k) p := Set.mem_iInter.2 hp
  have a := gen_trans ht' r z m₁ m₀
  have b := gen_trans ht (r ≫ h) z (j := p) (j' := fun k => J (r ≫ h ≫ φ k)) (Set.mem_iInter.2 hp)
    (Set.mem_iInter.2 fun k => Set.mem_iInter.1 m₀ k)
  refine a.trans (Eq.trans (congrArg₂ (· * ·) ?_ e) b.symm)
  simp only [trF, Category.assoc]

theorem genThrough_iff (hL : L.IsLB) (w : LB.Iso L' (L.pull F)) {φ : K → (Y ⟶ X)} {φ' : K → (Y' ⟶ X)}
    {ψ : K → (Y' ⟶ X')} {ε : K → ℤ} {h : Y' ⟶ Y}
    (hφ : ∀ k, φ' k = h ≫ φ k) {t : LB.Gen (LB.LinComb L φ ε)} {t' : LB.Gen (LB.LinComb L φ' ε)} (ht : t.IsGen)
    (ht' : t'.IsGen) (H : LB.Gen.Corr L φ' ε (fun k => h ≫ φ k) ε t' (LB.pullGen L φ ε t h))
    (a : LB.Gen (LB.LinComb L' ψ ε)) : GenThrough w ε a t' (𝟙 Y') ↔ GenThrough w ε a t h := by
  unfold GenThrough
  refine (and_congr_left' (forall_congr' fun k => by rw [Category.id_comp, hφ])).trans (and_congr_right fun hc => ?_)
  refine forall₅_congr fun Z r z p q => forall_congr' fun hp => forall_congr' fun _ => ?_
  rw [Category.comp_id, gm_of_corr hL hφ ht ht' H r z p fun k => ?_]
  have e : φ' k (r z) = F (ψ k (r z)) := congrArg (fun g => g (r z)) ((hφ k).trans (hc k).symm)
  rw [e]
  exact hp k

end Charts

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R}
  {D' : DegPre R'}

theorem isPullGtF_iff_genThrough (hD : IsPullDeg φ D D') {F : Type} [Field F] [Algebra (FractionRing R) F]
    [Algebra (FractionRing R') F] (g : GtPtF D F) (g' : GtPtF D' F) :
    IsPullGtF φ hD F g g' ↔ g'.b.left ≫ prOf hD = g.b.left ∧
      ∀ x, GenThrough hD.w DegPre.gtε (g'.s x) (g.s (hD.xe x)) (𝟙 _) :=
  and_congr Iff.rfl (forall_congr' fun x =>
    ⟨fun ⟨hψ, hm⟩ => ⟨hψ, (maps_iff hD.w _ _ _ (g'.s x) (g.s (hD.xe x)) (𝟙 _) _
        (GeneratorPullback.pullAlong_le _ _ _ _ _ hψ) (fun _ => rfl)).1 hm⟩,
      fun ⟨hψ, hm⟩ => ⟨hψ, (maps_iff hD.w _ _ _ (g'.s x) (g.s (hD.xe x)) (𝟙 _) _
        (GeneratorPullback.pullAlong_le _ _ _ _ _ hψ) (fun _ => rfl)).2 hm⟩⟩)

theorem gtφ_of_qkExt {F F' : Type} [Field F] [Algebra (FractionRing R) F] [Field F'] [Algebra (FractionRing R) F']
    {f : F →+* F'} (hf : f.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F') {k : ℕ}
    {p : QkPt D F k} {q : QkPt D F' k} (h : QkExt f p q) (χ : D.X) (i : Fin 4) :
    D.gtφ F' q.g.b χ i = spMap f ≫ D.gtφ F p.g.b χ i := by
  have b : q.g.b = extMap f hf ≫ p.g.b := Over.OverMorphism.ext h.2.1
  have a₁ : (cP D _ χ * q.g.b).left = spMap f ≫ (cP D _ χ * p.g.b).left := by
    rw [b, ← comp_cP D (extMap f hf), ← MonObj.comp_mul]; rfl
  have a₂ : (cP D (TF (R := R) F') χ).left = spMap f ≫ (cP D (TF (R := R) F) χ).left := by
    rw [← comp_cP D (extMap f hf)]; rfl
  have a₃ : (1 : TF (R := R) F' ⟶ D.P.A).left = spMap f ≫ (1 : TF (R := R) F ⟶ D.P.A).left := by
    rw [← MonObj.comp_one (extMap f hf)]; rfl
  fin_cases i
  exacts [a₁, a₂, h.2.1, a₃]

theorem direct_iff (hD : IsPullDeg φ D D') [Algebra (FractionRing R) (FractionRing R')] {k : ℕ}
    {p : QkPt D (FractionRing R) k} {q₀ : QkPt D (FractionRing R') k}
    (h : QkExt (algebraMap (FractionRing R) (FractionRing R')) p q₀) (q : QkPt D' (FractionRing R') k) :
    (q.y = hD.xe.symm q₀.y ∧ IsPullGtF φ hD (FractionRing R') q₀.g q.g) ↔ (hD.xe q.y = p.y ∧
      q.g.b.left ≫ prOf hD = spMap (algebraMap (FractionRing R) (FractionRing R')) ≫ p.g.b.left ∧
      ∀ x, GenThrough hD.w DegPre.gtε (q.g.s x) (p.g.s (hD.xe x))
        (spMap (algebraMap (FractionRing R) (FractionRing R')))) := by
  rw [isPullGtF_iff_genThrough, hD.xe.eq_symm_apply, h.1, h.2.1]
  exact and_congr Iff.rfl (and_congr Iff.rfl (forall_congr' fun x =>
    genThrough_iff D.P.isLB hD.w (gtφ_of_qkExt (RingHom.comp_id _) h _) (p.g.isGen _) (q₀.g.isGen _) (h.2.2 _) _))

theorem isPullQk_iff (A A' : Type) [CommRing A] [IsDomain A] [CommRing A'] [IsDomain A'] (g : A →+* A')
    (D₀ : Out.DegPre A) (D₁ : Out.DegPre A') (pd : Out.IsPullDeg g D₀ D₁) (hB : D₀.TauBimult) (k : ℕ)
    (p : Out.QkPt D₀ (FractionRing A) k) (q : Out.QkPt D₁ (FractionRing A') k) :
    GlobalTheory.ArcPull.IsPullQk pd p q ↔ ∃ hg : Function.Injective g, pd.xe q.y = p.y ∧
      q.g.b.left ≫ GlobalTheory.IndefiniteRowSideFullHecke.SectionsThroughEpsilonPoints.prOf pd = spMap (GlobalTheory.IndefiniteRowSideFullHecke.SectionsThroughEpsilonPoints.fracMap g hg) ≫ p.g.b.left ∧
      ∀ x, GlobalTheory.IndefiniteRowSideFullHecke.SectionsThroughEpsilonPoints.GenThrough pd.w Out.DegPre.gtε (q.g.s x) (p.g.s (pd.xe x))
        (spMap (GlobalTheory.IndefiniteRowSideFullHecke.SectionsThroughEpsilonPoints.fracMap g hg)) := by
  constructor
  · rintro ⟨_, hK, q₀, e₀, h⟩
    have hg : Function.Injective g := fun a b e => IsFractionRing.injective A (FractionRing A)
      ((algebraMap (FractionRing A) (FractionRing A')).injective (by rw [hK, hK, e]))
    have hf : GlobalTheory.IndefiniteRowSideFullHecke.SectionsThroughEpsilonPoints.fracMap g hg = algebraMap (FractionRing A) (FractionRing A') :=
      IsLocalization.ringHom_ext (nonZeroDivisors A) (RingHom.ext fun r =>
        (GlobalTheory.IndefiniteRowSideFullHecke.SectionsThroughEpsilonPoints.fracMap_algebraMap hg r).trans (hK r).symm)
    refine ⟨hg, ?_⟩
    rw [hf]
    exact (direct_iff pd e₀ q).1 h
  · rintro ⟨hg, h⟩
    letI : Algebra (FractionRing A) (FractionRing A') := (GlobalTheory.IndefiniteRowSideFullHecke.SectionsThroughEpsilonPoints.fracMap g hg).toAlgebra
    obtain ⟨q₀, e₀, -⟩ := existsUnique_qkExt (F' := FractionRing A') hB
      (algebraMap (FractionRing A) (FractionRing A')) (RingHom.comp_id _) p
    exact ⟨_, GlobalTheory.IndefiniteRowSideFullHecke.SectionsThroughEpsilonPoints.fracMap_algebraMap hg, q₀, e₀, (direct_iff pd e₀ q).2 h⟩

end GlobalTheory.QkPullDirect
