import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.GaloisCupProducts.HomPullGoodRHof
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.FaceMapCompSuccAboveCastSucc
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.CrSEqOne

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

noncomputable section

set_option maxHeartbeats 1000000

open CategoryTheory AlgebraicGeometry Limits GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb.Kap

namespace LevelPullbackIdentities

theorem qid {B : Type} [CommRing B] (J : Ideal B) (h : J ≤ J.comap (RingHom.id B)) (w : B ⧸ J) :
    Ideal.quotientMap J (RingHom.id B) h w = w := by
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective w
  rfl

theorem spec_qid {B : Type} [CommRing B] (J : Ideal B) (h : J ≤ J.comap (RingHom.id B)) {Y : Scheme.{0}}
    (y : Spec (CommRingCat.of (B ⧸ J)) ⟶ Y) :
    Spec.map (CommRingCat.ofHom (Ideal.quotientMap J (RingHom.id B) h)) ≫ y = y := by
  have e : Ideal.quotientMap J (RingHom.id B) h = RingHom.id _ := RingHom.ext (qid J h)
  rw [e]
  simp

theorem s_one {b : Base} {L : b.Fun} (hι : IsEmpty L.ι) (ht : b.t = 1) (T : Thick L) : T.s = 1 := by
  have h := T.hs
  rw [Finset.prod_of_isEmpty, ht, map_one, mul_one] at h
  exact Units.ext h.symm

def thHom {b : Base} {L : b.Fun} (hι : IsEmpty L.ι) (ht : b.t = 1) {T T' : Thick L} (φ : T.B →+* T'.B)
    (comm : ∀ r, φ (T.i r) = T'.i r) (dp : IsDPMorphism T.δ T'.δ φ) (hle : T.J ≤ T'.J.comap φ)
    (pt : L.Pt.map (CommRingCat.ofHom (Ideal.quotientMap T'.J φ hle)) T.y = T'.y) : T ⟶ T' where
  φ := φ
  u j := isEmptyElim j
  comm := comm
  dp := dp
  hle := hle
  pt := pt
  hx j := isEmptyElim j
  hs := by rw [s_one hι ht T', s_one hι ht T, map_one, Finset.prod_of_isEmpty, one_mul]
  hv j := isEmptyElim j

end LevelPullbackIdentities

theorem pullR_id' : ∀ {K : Type} [CommRing K] {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of K)) (n : ℕ) (x : HdR p n),
    pullR n (𝟙 X) (Category.id_comp p) x = x := by
  intro K _ X p n x
  let m' : CH.Mor (O (smFun X p)) (O (smFun X p)) (RingHom.id K) :=
    ⟨(smMor (𝟙 X) (Category.id_comp p)).functor,
      fun _ => { toFun := fun z => z, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }, fun _ _ => rfl⟩
  let η : (CH.Mor.id (O (smFun X p))).G ⟶ m'.G :=
    { app := fun T => LevelPullbackIdentities.thHom (L := smFun X p) ⟨fun j => Empty.elim j⟩ rfl (RingHom.id T.B) (fun r => rfl)
        (DPMorphism.id T.δ).isDPMorphism (fun _ h => h)
        (Subtype.ext (Prod.ext (Ideal.Quotient.ringHom_ext (RingHom.ext fun a => LevelPullbackIdentities.qid _ (fun _ h => h) _))
          ((LevelPullbackIdentities.spec_qid _ (fun _ h => h) _).trans (Category.comp_id _).symm)))
      naturality := fun _ _ f => Thick.Hom.ext (RingHom.ext fun _ => rfl) (funext fun j => Empty.elim j) }
  have h1 : (CH.Mor.id (O (smFun X p))).pull n x = x := (CrystallineSemistableComparison.P.pull_comp (CH.Mor.id _) (CH.Mor.id _) n x).2
  have h2 := CrystallineSemistableComparison.P.prism (CH.Mor.id (O (smFun X p))) m' η (fun T x => rfl) n x
  exact h2.symm.trans h1

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

section
variable (S : LevSys (per l K)) (hS : S.Good) (m : ℕ) (M : Model l K)

namespace LevelPullbackIdentities

def etaLev (s : ℕ)
    (hQ₁ : ∀ T, QB (S.L (m + 1)) M s T → QA (S.L (m + 1)) M s (((nmB M (hS.lev (m + 1))).mor 0).obj T))
    (hQ₀ : ∀ T, QB (S.L m) M s T → QA (S.L m) M s (((nmB M (hS.lev m)).mor 0).obj T)) :
    (nmS (nmLevB S hS m M) 1 s).o.G ⋙ (smB M s (hS.lev (m + 1)) hQ₁).o.G ⟶
      (smB M s (hS.lev m) hQ₀).o.G ⋙ (nmS (nmLevA S hS m M) l s).o.G where
  app T := ObjectProperty.homMk (mkH (RingHom.id T.obj.B) (fun r => congrArg T.obj.i (hS.dι m r))
    (DPMorphism.id T.obj.δ).isDPMorphism (fun _ h => h)
    (Subtype.ext (Prod.ext (Ideal.Quotient.ringHom_ext (RingHom.ext fun a =>
      (qid _ (fun _ h => h) _).trans (congrArg (fun b => T.obj.y.1.1 (Ideal.Quotient.mk _ b)) (hS.dι m a))))
      ((spec_qid _ (fun _ h => h) _).trans (by
        show ((T.obj.y.1.2 ≫ 𝟙 M.gen) ≫ pullback.fst _ _ : _ ⟶ M.X) = (T.obj.y.1.2 ≫ pullback.fst _ _) ≫ 𝟙 M.X
        simp)))))
  naturality _ _ f := ObjectProperty.hom_ext _ (CrystallineSemistableComparison.Pb.hom_ext rfl)

end LevelPullbackIdentities

theorem nmHO_nmLevB_bMap (s : ℕ)
    (hQ₁ : ∀ T, QB (S.L (m + 1)) M s T → QA (S.L (m + 1)) M s (((nmB M (hS.lev (m + 1))).mor 0).obj T))
    (hQ₀ : ∀ T, QB (S.L m) M s T → QA (S.L m) M s (((nmB M (hS.lev m)).mor 0).obj T)) (j : ℕ) (z : HO (QA (S.L (m + 1)) M s) j) :
    nmHO (nmLevB S hS m M) 1 s j (bMap M s (hS.lev (m + 1)) hQ₁ j z) =
      bMap M s (hS.lev m) hQ₀ j (nmHO (nmLevA S hS m M) l s j z) := by
  have i1 : RingHomCompTriple (S.L (m + 1)).ι (S.dB m) ((S.dB m).comp (S.L (m + 1)).ι) := ⟨rfl⟩
  have i2 : RingHomCompTriple (S.dA m) (S.L m).ι ((S.dB m).comp (S.L (m + 1)).ι) :=
    ⟨RingHom.ext fun a => (hS.dι m a).symm⟩
  have e₁ := CrystallineSemistableComparison.pull_pull ((S.dB m).comp (S.L (m + 1)).ι) (smB M s (hS.lev (m + 1)) hQ₁).o
    (nmS (nmLevB S hS m M) 1 s).o j z
  have e₂ := CrystallineSemistableComparison.pull_pull ((S.dB m).comp (S.L (m + 1)).ι) (nmS (nmLevA S hS m M) l s).o
    (smB M s (hS.lev m) hQ₀).o j z
  exact e₁.trans ((CrystallineSemistableComparison.P.prism ((smB M s (hS.lev (m + 1)) hQ₁).o.comp (σ'' := (S.dB m).comp (S.L (m + 1)).ι) (nmS (nmLevB S hS m M) 1 s).o)
    ((nmS (nmLevA S hS m M) l s).o.comp (σ'' := (S.dB m).comp (S.L (m + 1)).ι) (smB M s (hS.lev m) hQ₀).o)
    (LevelPullbackIdentities.etaLev S hS m M s hQ₁ hQ₀) (fun T x => rfl) j z).trans e₂.symm)

end

section
variable {m : ℕ} {L : Lev (per l K) m} (hL : L.Good) {M N : Model l K} (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) (s : ℕ)
  (hQN : ∀ T, QB L N s T → QA L N s (((nmB N hL).mor 0).obj T))
  (hQM : ∀ T, QB L M s T → QA L M s (((nmB M hL).mor 0).obj T))

namespace LevelPullbackIdentities

def etaPull : (nmS (nmPullB L u hu) 1 s).o.G ⋙ (smB N s hL hQN).o.G ⟶
      (smB M s hL hQM).o.G ⋙ (nmS (nmPullA L u hu) l s).o.G where
  app T := ObjectProperty.homMk (mkH (RingHom.id T.obj.B) (fun r => rfl)
    (DPMorphism.id T.obj.δ).isDPMorphism (fun _ h => h)
    (Subtype.ext (Prod.ext (Ideal.Quotient.ringHom_ext (RingHom.ext fun a => qid _ (fun _ h => h) _))
      ((spec_qid _ (fun _ h => h) _).trans (by
        show ((T.obj.y.1.2 ≫ Model.genMap u hu) ≫ pullback.fst _ _ : _ ⟶ N.X) = (T.obj.y.1.2 ≫ pullback.fst _ _) ≫ u
        simp only [Category.assoc, Model.genMap, pullback.lift_fst])))))
  naturality _ _ f := ObjectProperty.hom_ext _ (CrystallineSemistableComparison.Pb.hom_ext rfl)

end LevelPullbackIdentities

theorem nmHO_nmPullB_bMap (j : ℕ) (z : HO (QA L N s) j) :
    nmHO (nmPullB L u hu) 1 s j (bMap N s hL hQN j z) = bMap M s hL hQM j (nmHO (nmPullA L u hu) l s j z) := by
  have i1 : RingHomCompTriple L.ι (RingHom.id L.B) L.ι := ⟨RingHom.ext fun _ => rfl⟩
  have i2 : RingHomCompTriple (RingHom.id L.A) L.ι L.ι := ⟨RingHom.ext fun _ => rfl⟩
  have e₁ := CrystallineSemistableComparison.pull_pull L.ι (smB N s hL hQN).o (nmS (nmPullB L u hu) 1 s).o j z
  have e₂ := CrystallineSemistableComparison.pull_pull L.ι (nmS (nmPullA L u hu) l s).o (smB M s hL hQM).o j z
  exact e₁.trans ((CrystallineSemistableComparison.P.prism ((smB N s hL hQN).o.comp (σ'' := L.ι) (nmS (nmPullB L u hu) 1 s).o)
    ((nmS (nmPullA L u hu) l s).o.comp (σ'' := L.ι) (smB M s hL hQM).o)
    (LevelPullbackIdentities.etaPull hL u hu s hQN hQM) (fun T x => rfl) j z).trans e₂.symm)

end

end CrystallineSemistableComparison.Pb.Kap
