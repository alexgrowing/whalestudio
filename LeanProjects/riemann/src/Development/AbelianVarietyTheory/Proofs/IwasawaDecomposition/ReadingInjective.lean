import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeSameMap
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RootsOfUnityRingLeWittIntegers
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ExistsIsHeckeSetting
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardLatticesDiagonal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyDefiniteSpacesStandardAndLarge
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFamilyIffRationalHecke
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.StepSplittingCharactersTameLevelResidue

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwInputs.Move
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open Formalism.L2.Host (embLL0 CharFrame)
open GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2 (NExpTied)
open Formalism.AUTREP (GAf)
open GlobalTheory.HeightCounting GlobalTheory.HeightCounting.SideCopy GlobalTheory.TwInputs.Move.Forms

namespace GlobalTheory.HeightCounting.SerCarry

variable {D D' : D7} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0}

def HkAd (X : RealSide D) (Sb : Finset (PlE D.host))
    (hL : ∀ j : ℕ, ℕ → PlE D.host → Module.End D.what₂.LL (Fin (X.R.nW (NX.idxOf D j)) → D.what₂.LL)) : Prop :=
  ∀ j k P α Rr, 1 ≤ j → j ≤ D.R.m → HkDat X.R Sb (NX.idxOf D j) k P α Rr → ∀ x,
    evidence X (NX.idxOf D j) (hL j k P x) =
      hkNorm X.R (NX.idxOf D j) k P • Mult.heckeOn (model X (NX.idxOf D j)) Rr (evidence X (NX.idxOf D j) x)

def HkLaw (D : D7) (S : NX.RatDat D.ntw)
    (eF : ∀ i j b, 1 ≤ j → j ≤ D.R.m → D.nexp.Fm i j b ≃ₗ[FractionRing (D.ntw.O i)] NX.Fm S i j b)
    (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j))
    (hs : ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ k P (x : S.WL j), x ∈ (S.A j).WK → hL j k P x ∈ (S.A j).WK)
    (c : ∀ (i : D.ntw.Tw) (_b : Bool) (_P : PlE D.host), (D.ntw.O i)ˣ) : Prop :=
  ∀ i j b (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (k : ℕ) (P : PlE D.host) (x : D.nexp.Fm i j b), P ∉ D.ntw.S0 i →
    IsSplitPl D.host P → k ≤ D.R.r → eF i j b h1 h2 (D.nexp.hkF i j b k P x) =
      algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) (c i b P) ^ k • hkF D S i j b (hL j) (hs j h1 h2) k P (eF i j b h1 h2 x)

def LowIn (D : D7) : Prop := ∀ i, ∀ p ∈ lowAll D, placesOver D.host.E p ⊆ ↑(D.ntw.S0 i)

theorem HkAd.at {X : RealSide D} {Sb hL} (H : HkAd X Sb hL) (j : Fin D.R.m)
    (f : (Fin (X.R.nW (NX.idxOf D ((j : ℕ) + 1))) → D.what₂.LL) → Fin (X.R.nW j) → D.what₂.LL) (hf : ∀ x, HEq (f x) x)
    {k P α Rr} (hd : HkDat X.R Sb j k P α Rr) (x) :
    evidence X j (f (hL ((j : ℕ) + 1) k P x)) = hkNorm X.R j k P • Mult.heckeOn (model X j) Rr (evidence X j (f x)) := by
  have key : ∀ (a : Fin D.R.m), a = j → ∀ (u : (Fin (X.R.nW a) → D.what₂.LL) → Fin (X.R.nW a) → D.what₂.LL)
      (f : (Fin (X.R.nW a) → D.what₂.LL) → Fin (X.R.nW j) → D.what₂.LL), (∀ x, HEq (f x) x) →
      (∀ α Rr, HkDat X.R Sb a k P α Rr → ∀ x, evidence X a (u x) = hkNorm X.R a k P • Mult.heckeOn (model X a) Rr (evidence X a x)) →
      ∀ x, evidence X j (f (u x)) = hkNorm X.R j k P • Mult.heckeOn (model X j) Rr (evidence X j (f x)) := by
    intro a haj
    subst haj
    intro u f hf hu x
    rw [eq_of_heq (hf _), eq_of_heq (hf _)]
    exact hu α Rr hd x
  exact key _ (NX.idxOf_succ D j) _ f hf (fun α Rr hd => H _ k P α Rr (Nat.le_add_left _ _) j.2 hd) x

theorem reading_injective (X : RealSide D) (j : Fin D.R.m) : Function.Injective (evidence X j) := by
  refine (X.char.models.HW j _).1.comp ((injective_iff_map_eq_zero _).2 fun x hx => by_contra fun h0 => ?_)
  exact ((X.unif j (sg0 D X.A3.A)).1 1 (fun _ => x) (linearIndependent_unique_iff.2 h0)).ne_zero 0 hx

theorem fiOfEq_heq (X : RealSide D) {a b : Fin D.R.m} (hab : a = b) (x) : HEq ((fiOfEq X hab).e x) x := by
  subst hab; rfl

theorem exists_hkDat (X : RealSide D) (hl : LowIn D) {Sb} (hSb : OverSet D Sb (lowAll D)) {i : D.ntw.Tw} {v : PlE D.host}
    (hv : v ∉ D.ntw.S0 i) (hsp : IsSplitPl D.host v) : v ∉ Sb ∧ ((2 : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal ∧
      ∀ (j : Fin D.R.m) (k : ℕ), k ≤ D.R.r → ∃ α Rr, HkDat X.R Sb j k v α Rr := by
  have hlow : ∀ p ∈ lowAll D, ((p : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal := fun p hp hm => hv (hl i p hp hm)
  have hgP : ∀ kk : Fin 2, ((D.host.g kk : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal := fun kk =>
    hlow _ (by fin_cases kk <;> simp [lowAll])
  have hso : Bridge.SplitOff v (X.R.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) := by
    have hAll : X.R.Sb = X.R.Pg := X.char.allPl
    have hPg := X.char.lev.Pg
    refine ⟨(GlobalTheory.HeckeTieCompare.isSplitPl_iff v).1 hsp, fun h => ?_, fun Q hQ h => ?_⟩
    · rw [Finset.mem_coe, hAll] at h
      obtain ⟨kk, hkk⟩ := (hPg v).1 h
      exact hgP kk (GlobalTheory.StepLaw.typePrime_mem_of_div hkk)
    · rw [Finset.mem_coe, hAll] at hQ
      obtain ⟨kk, hkk⟩ := (hPg Q).1 hQ
      have hm := GlobalTheory.StepLaw.typePrime_mem_of_div hkk
      rw [h, Formalism.L2.Col.conjIdeal_asIdeal, Formalism.L2.Col.mem_conjP, map_natCast] at hm
      exact hgP kk hm
  have h1 : v ∉ Sb := fun hh => hv (hSb.subset (hl i) hh)
  have h2 := hlow 2 (by simp [lowAll, Formalism.L2.lowPr])
  refine ⟨h1, h2, fun j k hk => ?_⟩
  obtain ⟨α, Rc, ha, hR⟩ := GlobalTheory.HeckeSupSt.exists_heckeElt X.char.lev X.char.fam j hso hk
  exact ⟨α, Rc, hsp, h1, h2, hk, ha, hR⟩

theorem units_cast {A B : Type} [iA : CommRing A] [iB : CommRing B] (h : A = B) (hi : HEq iA iB) {u : Aˣ} {v : Bˣ} (hu : HEq v u) :
    ringCast h hi (u : A) = v := by
  subst h; cases hi; cases hu; rfl

section Law

variable (h : CopyTw D D' ι e) {X : RealSide D} {X' : RealSide D'} (m : RealMove X X' ι) {kKs hk}
  (YS : NX.NExpRealS X.R X.cG (NX.ratDatR X.R X.cG kKs hk)) (hfi : ∀ i x, HEq ((YS.fi i).e x) x)
  (hl : LowIn D) (hl' : LowIn D') {Sb Sb'} (hSb : OverSet D Sb (lowAll D)) (hSb' : OverSet D' Sb' (lowAll D'))
  {hL hL'} (H : HkAd X Sb hL) (H' : HkAd X' Sb' hL')

include hfi hl hl' hSb hSb' H H' in

theorem hk_intertwine {i : D.ntw.Tw} {i' : D'.ntw.Tw} (j : Fin D.R.m) (k : ℕ) {P : PlE D.host} {P' : PlE D'.host} (hP : HEq P P')
    (p0 : P ∉ D.ntw.S0 i) (p1 : P' ∉ D'.ntw.S0 i') (p2 : IsSplitPl D'.host P') (p3 : k ≤ D'.R.r)
    (y : ((NX.ratDatR X.R X.cG kKs hk).A ((j : ℕ) + 1)).WK) (hy) :
    ((ks h m YS j).φ ⟨hL ((j : ℕ) + 1) k P y.1, hy⟩).1 = hL' ((j : ℕ) + 1) k P' ((ks h m YS j).φ y).1 := by
  obtain ⟨q1, q2, q3⟩ := (place_geo h.gal.R h.gal.host).2 P P' hP
  obtain ⟨α', R', hd'⟩ := (exists_hkDat X' hl' hSb' p1 p2).2.2 (h.cm j) k p3
  obtain ⟨r1, r2, -⟩ := exists_hkDat X hl hSb p0 (q1.2 p2)
  obtain ⟨α, R, ha0, hR0, hF⟩ := (hecke_geo h.gal.R h.gal.host h.sp j (h.cm j) rfl).2.2 _ _ (m.βW j (h.cm j) rfl) _ _ m.Pg P P' hP
    k α' R' hd'.elt hd'.reps
  have e0 := H.at j (YS.fi j).e (hfi j) ⟨q1.2 p2, r1, r2, by rw [h.gal.R]; exact p3, ha0, hR0⟩ y.1
  have e0' := H'.at (h.cm j) (fiOfEq X' (NX.idxOf_succ D' (h.cm j))).e (fiOfEq_heq X' _) hd' ((ks h m YS j).φ y).1
  have hnV : D.R.nV = D'.R.nV := by rw [h.gal.R]
  have e1 : hkNorm X.R j k P = hkNorm X'.R (h.cm j) k P' := by
    unfold hkNorm
    rw [q3 _ _ (m.Cmu0 j (h.cm j) rfl), q2, hnV]
  have e2 := hecke_sameMap h m j hF (read_move h m YS j ⟨_, hy⟩) (read_move h m YS j y) (e0.trans (congrArg (· • _) e1))
  exact (fiOfEq X' (NX.idxOf_succ D' (h.cm j))).e.injective (reading_injective X' _ (e2.trans e0'.symm))

include hfi hl hl' hSb hSb' H H' in

theorem hkLaw_move (hsup) {hs c} (hs') {c'} (hc : SameUnits c c') (L : HkLaw D _ YS.eF hL hs c) :
    HkLaw D' (dat h m YS) (tie h m YS hsup).eF hL' hs' c' := by
  intro i' j b h1 h2 k P' x p1 p2 p3
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' h1
  have hi := back_heq h i'
  have hP : HEq (cast (place_geo h.gal.R h.gal.host).1.symm P') P' := cast_heq _ _
  generalize cast (place_geo h.gal.R h.gal.host).1.symm P' = P at hP ⊢
  obtain ⟨x, rfl⟩ := (h.fmCast hi _ b).surjective x
  obtain ⟨r1, -, r3⟩ := record_heq h.gal h.set h.frm h.Bsup h.delta hi
  have e1 : D'.nexp.hkF i' (n + 1) b k P' (h.fmCast hi _ b x) = h.fmCast hi _ b (D.nexp.hkF _ (n + 1) b k P x) :=
    eq_of_heq (((r1 _ b _ _ (h.fmCast_heq hi _ b x).symm).2.2 k _ _ hP).symm.trans (h.fmCast_heq hi _ b _).symm)
  have p0 : P ∉ D.ntw.S0 (back h i') := fun hh => p1 ((r3 P P' hP).1.1 hh)
  change eFm h m YS i' (n + 1) b h1 h2 _ = _ • hkF D' (dat h m YS) i' (n + 1) b (hL' (n + 1)) (hs' (n + 1) h1 h2) k P'
    (eFm h m YS i' (n + 1) b h1 h2 _)
  rw [e1, eFm_cast h m YS hi ⟨n, lt_m h h2⟩ b h1 h2, eFm_cast h m YS hi ⟨n, lt_m h h2⟩ b h1 h2,
    L _ _ b _ _ k P x p0 (((place_geo h.gal.R h.gal.host).2 P P' hP).1.2 p2) (by rw [h.gal.R]; exact p3), fmOf_smul]
  refine congrArg₂ (· • ·) ?_ (fmOf_restrict (S' := dat h m YS) (h.scal hi b) (ks h m YS ⟨n, lt_m h h2⟩) _ _ _ (hs' (n + 1) h1 h2 k P')
    (fun y => hk_intertwine h m YS hfi hl hl' hSb hSb' H H' ⟨n, lt_m h h2⟩ k hP p0 p1 p2 p3 y _) _)
  rw [map_pow, IsFractionRing.ringEquivOfRingEquiv_algebraMap]
  exact congrArg (fun z => algebraMap _ _ z ^ k) (units_cast _ _ (hc _ _ b _ _ hi hP))

end Law

end GlobalTheory.HeightCounting.SerCarry

end
