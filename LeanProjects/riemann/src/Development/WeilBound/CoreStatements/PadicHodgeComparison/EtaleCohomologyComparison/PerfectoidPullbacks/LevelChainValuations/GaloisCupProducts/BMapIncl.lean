import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.NmK
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DividedPowerReduction.CoefficientReductionFirstChernClassTateTwist
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DividedPowerReduction.ReductionChangeLevel
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.FaceMapCompSuccAboveCastSucc
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.CrSEqOne

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

noncomputable section

set_option maxHeartbeats 1000000

open CategoryTheory AlgebraicGeometry Limits GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb.Kap

namespace LevelChangeComparison

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

end LevelChangeComparison

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

section
variable (S : LevSys (per l K)) (hS : S.Good) (m : ℕ) (M : Model l K)

def nmLevA : NMor (S.L (m + 1)).γ M.p (κA (OK l K) (S.L (m + 1)).I) (S.L m).γ M.p (κA (OK l K) (S.L m).I) (S.dA m) :=
  nmK (S.L (m + 1)).γ (S.L m).γ M.p M.p (S.dA m) (hS.ddp m) (hS.dO m) (𝟙 M.X) (Category.id_comp _)

def nmLevB : NMor (S.L (m + 1)).γB M.q (κA K (S.L (m + 1)).IB) (S.L m).γB M.q (κA K (S.L m).IB) (S.dB m) :=
  nmK (S.L (m + 1)).γB (S.L m).γB M.q M.q (S.dB m) (hS.ddpB m) (hS.dK m) (𝟙 M.gen) (Category.id_comp _)

namespace LevelChangeComparison

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

end LevelChangeComparison

end

theorem bMap_incl {m : ℕ} {L : Lev (per l K) m} (hL : L.Good) (M : Model l K) {s s' : ℕ} (h : s ≤ s')
    (hQ : ∀ T, QB L M s T → QA L M s (((nmB M hL).mor 0).obj T))
    (hQ' : ∀ T, QB L M s' T → QA L M s' (((nmB M hL).mor 0).obj T)) (j : ℕ) (z : HO (QA L M s') j) :
    (incl (ts_le L.γB M.q 1 h {⊤})).o.pull j (bMap M s' hL hQ' j z) =
      bMap M s hL hQ j ((incl (ts_le L.γ M.p l h {⊤})).o.pull j z) := by
  have e₁ := CrystallineSemistableComparison.pull_pull L.ι (smB M s' hL hQ').o (incl (ts_le L.γB M.q 1 h {⊤})).o j z
  have e₂ := CrystallineSemistableComparison.pull_pull L.ι (incl (ts_le L.γ M.p l h {⊤})).o (smB M s hL hQ).o j z
  exact e₁.trans (Eq.trans rfl e₂.symm)

end CrystallineSemistableComparison.Pb.Kap
