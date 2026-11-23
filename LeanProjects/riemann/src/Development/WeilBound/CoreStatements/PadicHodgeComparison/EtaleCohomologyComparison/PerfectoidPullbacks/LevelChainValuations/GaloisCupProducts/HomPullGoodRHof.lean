import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.RHof
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.GaloisCupProducts.BMapIncl

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

noncomputable section

set_option maxHeartbeats 1000000

open CategoryTheory AlgebraicGeometry Limits GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb.Kap

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

section
variable {R : Per l K} {m : ℕ} (L : Lev R m) {M N : Model l K} (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p)

def nmPullA : NMor L.γ N.p (κA (OK l K) L.I) L.γ M.p (κA (OK l K) L.I) (RingHom.id L.A) :=
  nmK L.γ L.γ N.p M.p (RingHom.id L.A) (DPMorphism.id L.γ).isDPMorphism (fun _ => rfl) u hu

def nmPullB : NMor L.γB N.q (κA K L.IB) L.γB M.q (κA K L.IB) (RingHom.id L.B) :=
  nmK L.γB L.γB N.q M.q (RingHom.id L.B) (DPMorphism.id L.γB).isDPMorphism (fun _ => rfl) (Model.genMap u hu)
    (Model.genMap_q u hu)

end

section
variable {m : ℕ} {L : Lev (per l K) m} (hL : L.Good) {M N : Model l K} (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) (s : ℕ)
  (hQN : ∀ T, QB L N s T → QA L N s (((nmB N hL).mor 0).obj T))
  (hQM : ∀ T, QB L M s T → QA L M s (((nmB M hL).mor 0).obj T))
  (rHN : ∀ n j, N.Hc false n j →ₛₗ[L.lam] HM (QA L N s) none ((l : L.A) ^ n) j)
  (rHM : ∀ n j, M.Hc false n j →ₛₗ[L.lam] HM (QA L M s) none ((l : L.A) ^ n) j)

def homPull : Hom (chainOf hL N s hQN rHN) (chainOf hL M s hQM rHM) where
  sΛ := RingHom.id _
  sA := RingHom.id _
  sB := RingHom.id _
  fS n j := B.pullHc (okToOC l K) (B.schMap u hu) false n j
  fZn n j := nmHM (nmPullA L u hu) l s none n j
  fZ j := nmHO (nmPullA L u hu) l s j
  fW j := nmHO (nmPullB L u hu) 1 s j
  fV j := pullR j (Model.genMap u hu) (Model.genMap_q u hu)

namespace PullbackComparison

def etaPull : (nmS (nmPullB L u hu) 1 s).o.G ⋙ (smB N s hL hQN).o.G ⟶
      (smB M s hL hQM).o.G ⋙ (nmS (nmPullA L u hu) l s).o.G where
  app T := ObjectProperty.homMk (mkH (RingHom.id T.obj.B) (fun r => rfl)
    (DPMorphism.id T.obj.δ).isDPMorphism (fun _ h => h)
    (Subtype.ext (Prod.ext (Ideal.Quotient.ringHom_ext (RingHom.ext fun a => LevelChangeComparison.qid _ (fun _ h => h) _))
      ((LevelChangeComparison.spec_qid _ (fun _ h => h) _).trans (by
        show ((T.obj.y.1.2 ≫ Model.genMap u hu) ≫ pullback.fst _ _ : _ ⟶ N.X) = (T.obj.y.1.2 ≫ pullback.fst _ _) ≫ u
        simp only [Category.assoc, Model.genMap, pullback.lift_fst])))))
  naturality _ _ f := ObjectProperty.hom_ext _ (CrystallineSemistableComparison.Pb.hom_ext rfl)

end PullbackComparison

end

section
variable {m : ℕ} {L : Lev (per l K) m}
  (d : ∀ n, RedIn (B.DD false (PAlg.base l) n) (B.κb (okToOC l K) false n) L.γ l n)
  (hc : ∀ n (c : Acris l), (d n).ρ ((PAlg.base l).cris n c) = Ideal.Quotient.mk _ (L.lam c))
  {M N : Model l K} (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) (s : ℕ)

theorem lnMap_id {B : Type} [CommRing B] (k n : ℕ) (y : B ⧸ Ideal.span {(k : B) ^ n}) :
    lnMap (RingHom.id B) k (le_refl n) y = y := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
  rfl

theorem rHof_pull (n j : ℕ) (x : N.Hc false n j) :
    nmHM (nmPullA L u hu) l s none n j (rHof d hc N s n j x) =
      rHof d hc M s n j (B.pullHc (okToOC l K) (B.schMap u hu) false n j x) :=
  (red_nm (d n) (d n) s (nmPullA L u hu) _ _ _ _ _ (hc n) (hc n) _ _ (fun _ _ => rfl) (fun _ => (lnMap_id l n _).symm)
    none j x).symm

end

end CrystallineSemistableComparison.Pb.Kap
