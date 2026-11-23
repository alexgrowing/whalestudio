import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsPullbackPow
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueIota
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FormallyUnramifiedMulInvertibleInteger

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.FlatTors GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator
open scoped TensorProduct

namespace GlobalTheory.PairScheme

open GlobalTheory.TorusModel GlobalTheory.TorsionFormCompare

theorem formallyUnramified_fibre {S S' N W : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] (k : ℕ)
    (j : S' ⟶ S) (hk : IsUnit (k : Γ(S', ⊤))) (w : W ⟶ S) [IsOpenImmersion w] {s : W ⟶ G.left} (hs : s ≫ G.hom = w)
    {n : N ⟶ G.left} {q : N ⟶ W} (H : IsPullback n q ((𝟙 G) ^ k : G ⟶ G).left s) :
    FormallyUnramified (pullback.snd (q ≫ w) j) := by
  have hm : ((𝟙 G) ^ k : G ⟶ G).left ≫ G.hom = G.hom := Over.w _
  have hn : n ≫ G.hom = q ≫ w := by rw [← hm, ← Category.assoc, H.w, Category.assoc, hs]
  have e : (Over.pullback j).map ((𝟙 G) ^ k : G ⟶ G) = mulA ((Over.pullback j).obj G) k :=
    (map_pow (Over.pullback j).homMonoidHom (𝟙 G) k).trans
      (congrArg (· ^ k) (CategoryTheory.Functor.map_id (Over.pullback j) G))
  let m' : pullback G.hom j ⟶ pullback G.hom j := ((Over.pullback j).map ((𝟙 G) ^ k : G ⟶ G)).left
  have hu : FormallyUnramified m' := by
    have := formallyUnramified_mulA S' ((Over.pullback j).obj G) k hk
    rw [← e] at this
    exact this
  have m1 : m' ≫ pullback.fst G.hom j = pullback.fst G.hom j ≫ ((𝟙 G) ^ k : G ⟶ G).left := pullback.lift_fst _ _ _
  have m2 : m' ≫ pullback.snd G.hom j = pullback.snd G.hom j := pullback.lift_snd _ _ _
  have PR : IsPullback (pullback.fst G.hom j) m' ((𝟙 G) ^ k : G ⟶ G).left (pullback.fst G.hom j) :=
    IsPullback.of_bot (by rw [m2, hm]; exact IsPullback.of_hasPullback _ _) m1.symm (IsPullback.of_hasPullback _ _)
  let q' : pullback (q ≫ w) j ⟶ pullback w j :=
    pullback.lift (pullback.fst _ _ ≫ q) (pullback.snd _ _) (by rw [Category.assoc, pullback.condition])
  have q1 : q' ≫ pullback.fst w j = pullback.fst _ _ ≫ q := pullback.lift_fst _ _ _
  have q2 : q' ≫ pullback.snd w j = pullback.snd _ _ := pullback.lift_snd _ _ _
  have PQ : IsPullback (pullback.fst (q ≫ w) j) q' q (pullback.fst w j) :=
    IsPullback.of_bot (by rw [q2]; exact IsPullback.of_hasPullback _ _) q1.symm (IsPullback.of_hasPullback _ _)
  let n' : pullback (q ≫ w) j ⟶ pullback G.hom j :=
    pullback.lift (pullback.fst _ _ ≫ n) (pullback.snd _ _) (by rw [Category.assoc, hn, pullback.condition])
  have n1 : n' ≫ pullback.fst G.hom j = pullback.fst _ _ ≫ n := pullback.lift_fst _ _ _
  have n2 : n' ≫ pullback.snd G.hom j = pullback.snd _ _ := pullback.lift_snd _ _ _
  let s' : pullback w j ⟶ pullback G.hom j :=
    pullback.lift (pullback.fst _ _ ≫ s) (pullback.snd _ _) (by rw [Category.assoc, hs, pullback.condition])
  have s1 : s' ≫ pullback.fst G.hom j = pullback.fst _ _ ≫ s := pullback.lift_fst _ _ _
  have s2 : s' ≫ pullback.snd G.hom j = pullback.snd _ _ := pullback.lift_snd _ _ _
  have PL : IsPullback n' q' m' s' := by
    refine IsPullback.of_right (by rw [n1, s1]; exact PQ.paste_horiz H) ?_ PR
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, m1, s1, reassoc_of% n1, reassoc_of% q1, H.w]
    · rw [Category.assoc, Category.assoc, m2, s2, n2, q2]
  have : FormallyUnramified q' := MorphismProperty.of_isPullback (P := @FormallyUnramified) PL hu
  rw [← q2]
  exact MorphismProperty.comp_mem (@FormallyUnramified) _ _ this inferInstance

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {Gt : Over (Sp R)} [GrpObj Gt]
  {Φ : ∀ T, (T ⟶ Gt) ≃ GtPt D T}

theorem isNsmul_iff (hΦ : Represents Φ) (k : ℕ) {T : Over (Sp R)} (x z : T ⟶ Gt) :
    GtPt.IsNsmul k (Φ T x) (Φ T z) ↔ x ^ k = z := by
  constructor
  · rintro ⟨u, u0, us, hz⟩
    have : ∀ i : Fin (k + 1), u i = Φ T (x ^ (i : ℕ)) := fun i => by
      induction i using Fin.induction with
      | zero => exact isZero_unique u0 (by simpa using isZero_one hΦ T)
      | succ i ih =>
        have h := us i
        rw [ih] at h
        rw [Fin.val_succ, pow_succ]
        exact isAdd_unique h (hΦ.2 T _ _)
    exact (Φ T).injective ((this (Fin.last k)).symm.trans hz)
  · rintro rfl
    refine ⟨fun i => Φ T (x ^ (i : ℕ)), by simpa using isZero_one hΦ T, fun i => ?_, rfl⟩
    simp only [Fin.val_succ, Fin.val_castSucc, pow_succ]
    exact hΦ.2 T _ _

theorem isIotaW_pull {W : (Sp R).Opens} {ψW : PsiOn D W} {T T' : Over W.toScheme} (h : T' ⟶ T) {y : D.X}
    {g : GtPt D (overW W T)} {g' : GtPt D (overW W T')} (H : GtPt.IsPull h.left g g') (hg : GtPt.IsIotaW ψW y g) :
    GtPt.IsIotaW ψW y g' := by
  refine ⟨Over.OverMorphism.ext (H.1.trans ?_), fun χ => corr_of_val D.P.isLB fun z J hJ => ?_⟩
  · rw [hg.1]
    exact congrArg (·.left) (comp_toUnit_assoc ((Over.map W.ι).map h) (D.c y))
  · refine (val_corr hJ (H.2 χ) _).trans ((val_pull hJ _ _ _).trans ((val_corr hJ (hg.2 χ) _).trans
      ((val_pull hJ _ _ _).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm))))
    rw [Category.assoc, Over.w h]

theorem exists_pairRep [CharZero R] [IsCommMonObj Gt] (hΦ : Represents Φ) {W : (Sp R).Opens} (ψW : PsiOn D W) {k : ℕ}
    (hk : 1 ≤ k) [IsFinite ((𝟙 Gt) ^ k : Gt ⟶ Gt).left] [Flat ((𝟙 Gt) ^ k : Gt ⟶ Gt).left]
    [Surjective ((𝟙 Gt) ^ k : Gt ⟶ Gt).left] (y : D.X)
    (hι : ∀ T : Over W.toScheme, ∃! g : GtPt D (overW W T), GtPt.IsIotaW ψW y g) :
    ∃ (N : Over W.toScheme) (p₀ : QkPtW D W ψW k N), PairRep ψW k y N p₀ := by
  obtain ⟨g₀, hg₀, -⟩ := hι (Over.mk (𝟙 _))
  obtain ⟨s, rfl⟩ := (Φ _).surjective g₀
  let s₀ : W.toScheme ⟶ Gt.left := s.left
  have hs : s₀ ≫ Gt.hom = W.ι := (Over.w s).trans (Category.id_comp _)
  let m : Gt.left ⟶ Gt.left := ((𝟙 Gt) ^ k : Gt ⟶ Gt).left
  have hm : m ≫ Gt.hom = Gt.hom := Over.w _
  let τ : ∀ T : Over W.toScheme, T ⟶ Over.mk (𝟙 _) := fun T => Over.homMk T.hom (Category.comp_id _)
  have io : ∀ T, GtPt.IsIotaW ψW y (Φ _ ((Over.map W.ι).map (τ T) ≫ s)) := fun T =>
    isIotaW_pull (τ T) (hΦ.1 _ _ ((Over.map W.ι).map (τ T)) s) hg₀
  have key : ∀ (T : Over W.toScheme) (x : overW W T ⟶ Gt),
      (∃ h, GtPt.IsNsmul k (Φ _ x) h ∧ GtPt.IsIotaW ψW y h) ↔ x.left ≫ m = T.hom ≫ s₀ := fun T x => by
    have e : x.left ≫ m = (x ^ k).left := by
      rw [← Category.comp_id x, ← MonObj.comp_pow, Category.comp_id]; rfl
    rw [e]
    constructor
    · rintro ⟨h, h₁, h₂⟩
      rw [(hι T).unique h₂ (io T), isNsmul_iff hΦ] at h₁
      exact congrArg (·.left) h₁
    · exact fun h => ⟨_, (isNsmul_iff hΦ _ _ _).2 (Over.OverMorphism.ext h), io T⟩
  let N : Over W.toScheme := Over.mk (pullback.snd m s₀)
  let n : overW W N ⟶ Gt := Over.homMk (pullback.fst m s₀) (by
    rw [← hm, ← Category.assoc, pullback.condition, Category.assoc, hs]; rfl)
  have hf : IsFinite N.hom := inferInstanceAs (IsFinite (pullback.snd m s₀))
  have hl : Flat N.hom := inferInstanceAs (Flat (pullback.snd m s₀))
  refine ⟨N, ⟨y, Φ _ n, (key N n).2 pullback.condition⟩, ⟨hf, hl, ?_⟩,
    inferInstanceAs (Surjective (pullback.snd m s₀)), rfl, ?_⟩
  · change Etale (pullback.snd (N.hom ≫ W.ι) (jK R))
    have : FormallyUnramified (pullback.snd (N.hom ≫ W.ι) (jK R)) := by
      refine formallyUnramified_fibre Gt k (jK R) ?_ W.ι hs (IsPullback.of_hasPullback m s₀)
      have : IsUnit (k : FractionRing R) := by
        have : CharZero (FractionRing R) := IsFractionRing.charZero_of_isFractionRing R
        exact (Nat.cast_ne_zero.2 (by omega) : (k : FractionRing R) ≠ 0).isUnit
      simpa using this.map (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom
    exact Etale.of_formallyUnramified_of_flat _
  · rintro T ⟨y', g, hg⟩ rfl
    obtain ⟨x, rfl⟩ := (Φ _).surjective g
    have hx := (key T x).1 hg
    refine ⟨Over.homMk (pullback.lift x.left T.hom hx) (pullback.lift_snd _ _ _), ⟨rfl, ?_⟩, fun h hh => ?_⟩
    · exact (isPull_iff_comp hΦ ((Over.map W.ι).map (Over.homMk (pullback.lift x.left T.hom hx)
        (pullback.lift_snd _ _ _) : T ⟶ N)) n x).2 (Over.OverMorphism.ext (pullback.lift_fst _ _ _))
    · have e := (isPull_iff_comp hΦ ((Over.map W.ι).map h) n x).1 hh.2
      refine Over.OverMorphism.ext (pullback.hom_ext ?_ ?_)
      · exact (congrArg (·.left) e).trans (pullback.lift_fst x.left T.hom hx).symm
      · exact (Over.w h).trans (pullback.lift_snd x.left T.hom hx).symm

theorem pairRep_exists : AllFlat fun {E} _ _ _ {H} {R} _ _ _ {t} P {W} ψW k => ∀ y : P.D.toPre.X,
    ∃ (N : Over W.toScheme) (p₀ : QkPtW P.D.toPre W ψW k N), PairRep ψW k y N p₀ := by
  intro E _ _ _ H R _ _ _ _ hR t P W hW hp ψW k hk y
  have := hR.1
  obtain ⟨Gt, _, _, Φ, hΦ, -, -, h⟩ := GlobalTheory.ExtensionMul.exists_represents_pow R P.D.toPre
  obtain ⟨_, _, _⟩ := h k hk
  exact exists_pairRep hΦ ψW hk y fun T => GlobalTheory.IotaExists.iota_existsUnique E H R hR t P W hW hp ψW k hk T y

end GlobalTheory.PairScheme
