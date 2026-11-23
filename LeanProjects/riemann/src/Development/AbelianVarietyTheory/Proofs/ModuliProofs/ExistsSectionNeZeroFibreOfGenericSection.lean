import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.NonemptyPerfectSectionsComplexOfSmoothProjStatement
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.VeryAmpleByOfRelAmple
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SecBaseChangeOfPerf
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsMaximalMinorNeZeroOfLinearIndependent

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

noncomputable section
namespace GlobalTheory.GenericSection
open GlobalTheory.AbLaw GlobalTheory.AbLaw.SecBC

theorem exists_ker_ne_zero {R K K' : Type} [CommRing R] [Field K] [Field K'] (g : R →+* K) (g' : R →+* K')
    (hg : Function.Injective g) {a b : ℕ} (D : Matrix (Fin b) (Fin a) R) (v : Fin a → K) (hv : v ≠ 0)
    (h : (D.map g).mulVec v = 0) : ∃ v' : Fin a → K', v' ≠ 0 ∧ (D.map g').mulVec v' = 0 := by
  by_contra hno
  push Not at hno
  have hind : LinearIndependent K' (fun j : Fin a => fun i : Fin b => (D.map g') i j) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    by_contra hc0
    push Not at hc0
    have hc' : c ≠ 0 := fun h0 => by
      obtain ⟨j, hj⟩ := hc0
      exact hj (by rw [h0]; rfl)
    apply hno c hc'
    funext i
    have := congrFun hc i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
    rw [Pi.zero_apply] at this
    rw [← this]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  obtain ⟨e, -, he⟩ := GlobalTheory.exists_maximal_minor_ne_zero_of_linearIndependent K' b (Fin a) _ hind
  have hdet : (D.submatrix e id).det ≠ 0 := by
    intro h0
    apply he
    have : (Matrix.of fun k j => (D.map g') (e k) j) = (D.submatrix e id).map g' := by
      ext k j
      rfl
    have hm := RingHom.map_det g' (D.submatrix e id)
    rw [RingHom.mapMatrix_apply] at hm
    rw [this, ← hm, h0, map_zero]
  have hdetK : ((D.map g).submatrix e id).det ≠ 0 := by
    have : (D.map g).submatrix e id = (D.submatrix e id).map g := rfl
    have hm := RingHom.map_det g (D.submatrix e id)
    rw [RingHom.mapMatrix_apply] at hm
    rw [this, ← hm]
    exact fun h0 => hdet (hg (by rw [h0, map_zero]))
  apply hv
  apply Matrix.eq_zero_of_mulVec_eq_zero hdetK
  funext k
  have := congrFun h (e k)
  simpa [Matrix.mulVec, dotProduct, Matrix.submatrix] using this

def zeroSec {X : Scheme.{0}} (M : LB X) : LB.Sec M where
  f := fun _ => 0
  compat := fun _ _ => by rw [map_zero, map_zero, mul_zero]

theorem exists_sec_iff {X X' Y : Scheme.{0}} {L : LB Y} {p : X ⟶ Y} {R R' : Type} [CommRing R] [CommRing R']
    {f : X ⟶ Spec (CommRingCat.of R)} (F : Perf f (L.pull p)) (g : R →+* R') {π : X' ⟶ X}
    {f' : X' ⟶ Spec (CommRingCat.of R')} (H : IsPullback π f' f (Spec.map (CommRingCat.ofHom g)))
    {q : X' ⟶ Y} (e : q = π ≫ p) :
    (∃ (s : (L.pull q).Sec) (j : _), s.f j ≠ 0) ↔ ∃ v : Fin F.a → R', v ≠ 0 ∧ (F.D₀.map g).mulVec v = 0 := by
  subst e
  unfold LB.pull at F ⊢
  let c : R' →+* Γ(X', ⊤) := f'.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom
  obtain ⟨h1, h2, h3⟩ := SecBC.rep_main (F := F) (ψ := fun _ => π ≫ p) (fun _ => rfl) g f' H c (fun _ => rfl)
  have h0 : SecBC.Rep π (fun _ => π ≫ p) F c 0 (zeroSec (L.LinComb (fun _ : PUnit.{1} => π ≫ p) (fun _ => 1))).f := by
    have hs := SecBC.Rep.sum (F := F) (ψ := fun _ => π ≫ p) (c := c) (fun _ => rfl) (I := Empty)
      (w := Empty.elim) (b := Empty.elim) (fun l => l.elim) Empty.elim
    simp only [Finset.univ_eq_empty, Finset.sum_empty] at hs
    exact hs
  constructor
  · rintro ⟨s, j, hs⟩
    obtain ⟨v, hv, hrep⟩ := h2 s
    refine ⟨v, fun hv0 => hs ?_, hv⟩
    subst hv0
    rw [SecBC.Rep.sec_eq (fun _ => rfl) hrep h0]
    rfl
  · rintro ⟨v, hv0, hv⟩
    obtain ⟨s, hs⟩ := h1 v hv
    by_contra hno
    push Not at hno
    apply hv0
    have hz : s = zeroSec _ := SecBC.sec_ext (fun j => hno s j)
    rw [hz] at hs
    exact h3 v 0 (zeroSec (L.LinComb (fun _ : PUnit.{1} => π ≫ p) (fun _ => 1))) hv (Matrix.mulVec_zero _) hs h0

theorem exists_ringHom {S : Scheme.{0}} {R K : Type} [CommRing R] [Field K] (t : Sp R ⟶ S) [IsOpenImmersion t]
    (x : Sp K ⟶ S) (h : Set.range x ⊆ Set.range t) :
    ∃ g : R →+* K, Spec.map (CommRingCat.ofHom g) ≫ t = x := by
  refine ⟨(Spec.preimage (IsOpenImmersion.lift t x h)).hom, ?_⟩
  rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  exact IsOpenImmersion.lift_fac t x h

theorem exists_isPullback {A S T T' : Scheme.{0}} (a : A ⟶ S) (t : T ⟶ S) (u : T' ⟶ T) (x : T' ⟶ S)
    (h : u ≫ t = x) : ∃ π : pullback a x ⟶ pullback a t,
      IsPullback π (pullback.snd a x) (pullback.snd a t) u ∧ pullback.fst a x = π ≫ pullback.fst a t := by
  subst h
  have hc : pullback.fst a (u ≫ t) ≫ a = (pullback.snd a (u ≫ t) ≫ u) ≫ t := by
    rw [pullback.condition, Category.assoc]
  refine ⟨pullback.lift _ _ hc, ?_, (pullback.lift_fst _ _ hc).symm⟩
  refine IsPullback.of_right ?_ (pullback.lift_snd _ _ hc) (IsPullback.of_hasPullback a t)
  rw [pullback.lift_fst]
  exact IsPullback.of_hasPullback a (u ≫ t)

theorem exists_sec_ne_zero_of_generic : Out.Laws → ∀ (S : Scheme.{0}) [IsIntegral S] (P : Out.PolAV S) (N : LB P.A.left) (K K' : Type) [Field K] [Field K'] (x : Sp K ⟶ S) (y : Sp K' ⟶ S) (s : (N.pull (pullback.fst P.A.hom x)).Sec), N.IsLB → Set.range x = {genericPoint S} → (∃ j, s.f j ≠ 0) → ∃ (s' : (N.pull (pullback.fst P.A.hom y)).Sec) (j : _), s'.f j ≠ 0 := by
  intro hLaws S _ P N K K' _ _ x y s hN hx hs
  obtain ⟨W, hW, hyW, -⟩ := exists_isAffineOpen_mem_and_subset
    (show y (IsLocalRing.closedPoint K') ∈ (⊤ : S.Opens) from trivial)
  let t : Sp Γ(S, W) ⟶ S := hW.fromSpec
  have hrange : Set.range t = W := hW.range_fromSpec
  have hgen : genericPoint S ∈ (W : Set S) := by
    rw [(genericPoint_spec S).mem_open_set_iff W.isOpen]
    exact ⟨_, trivial, hyW⟩
  have : Nonempty W := ⟨⟨_, hyW⟩⟩
  have hxr : Set.range x ⊆ Set.range t := by
    rw [hx, hrange]
    simpa using hgen
  have hyr : Set.range y ⊆ Set.range t := by
    rintro _ ⟨z, rfl⟩
    rw [hrange, Subsingleton.elim z (IsLocalRing.closedPoint K')]
    exact hyW
  obtain ⟨gx, hgx⟩ := exists_ringHom t x hxr
  obtain ⟨gy, hgy⟩ := exists_ringHom t y hyr
  have hinj : Function.Injective gx := by
    rw [injective_iff_map_eq_zero]
    intro r hr
    by_contra hr0
    have hne : (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum Γ(S, W))).Nonempty :=
      ⟨⟨⊥, Ideal.isPrime_bot⟩, by simpa [PrimeSpectrum.mem_basicOpen] using hr0⟩
    have hop : IsOpen (t '' (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum Γ(S, W)))) :=
      t.isOpenEmbedding.isOpenMap _ (PrimeSpectrum.basicOpen r).isOpen
    have hg2 : genericPoint S ∈ t '' (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum Γ(S, W))) := by
      rw [(genericPoint_spec S).mem_open_set_iff hop]
      obtain ⟨q, hq⟩ := hne
      exact ⟨_, trivial, q, hq, rfl⟩
    obtain ⟨q, hq, hqe⟩ := hg2
    have hxpt : x (IsLocalRing.closedPoint K) = genericPoint S := by
      have hm : x (IsLocalRing.closedPoint K) ∈ Set.range x := ⟨_, rfl⟩
      rw [hx] at hm
      exact hm
    have hq2 : q = Spec.map (CommRingCat.ofHom gx) (IsLocalRing.closedPoint K) := by
      apply t.isOpenEmbedding.injective
      rw [hqe, ← hxpt, ← hgx]
      rfl
    rw [hq2] at hq
    apply (PrimeSpectrum.mem_basicOpen _ _).1 hq
    show r ∈ (PrimeSpectrum.comap gx (IsLocalRing.closedPoint K)).asIdeal
    rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, hr]
    exact zero_mem _
  have H0 : IsPullback (pullback.fst P.A.hom t) (pullback.snd P.A.hom t) P.A.hom t :=
    IsPullback.of_hasPullback _ _
  obtain ⟨n, -, m, σ, hlb, hva⟩ := polAV_veryAmpleBy hLaws.polBaseChange S P Γ(S, W) t _ _ _ H0
  have : Smooth P.A.hom := by
    have := P.smoothDim
    exact SmoothOfRelativeDimension.smooth P.g P.A.hom
  have hproj : IsProjBy (pullback.snd P.A.hom t) := ⟨_, hlb, m, σ, hva⟩
  obtain ⟨F⟩ := GlobalTheory.T.nonempty_perfectSectionsComplex_of_smooth_proj Γ(S, W) _ (pullback.snd P.A.hom t) inferInstance hproj
    (N.pull (pullback.fst P.A.hom t)) (LB.isLB_pull hN _)
  obtain ⟨πx, hπx, hex⟩ := exists_isPullback P.A.hom t (Spec.map (CommRingCat.ofHom gx)) x hgx
  obtain ⟨πy, hπy, hey⟩ := exists_isPullback P.A.hom t (Spec.map (CommRingCat.ofHom gy)) y hgy
  obtain ⟨v, hv, hker⟩ := (exists_sec_iff F gx hπx hex).1 ⟨s, hs⟩
  obtain ⟨v', hv', hker'⟩ := exists_ker_ne_zero gx gy hinj F.D₀ v hv hker
  exact (exists_sec_iff F gy hπy hey).2 ⟨v', hv', hker'⟩

end GlobalTheory.GenericSection
