import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.ChainOf
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.RHof
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.NmK
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DividedPowerReduction.IsFirstChernThickening
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DividedPowerReduction.CoefficientReductionFirstChernClassTateTwist
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DividedPowerReduction.ReductionChangeLevel
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.TwistAcrisZeroPreservesFiltration

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

noncomputable section

set_option maxHeartbeats 1000000

open CategoryTheory AlgebraicGeometry Limits GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb.Kap

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

def galS (M : Model l K) (g : K.fixingSubgroup) (n j : ℕ) : M.Hc false n j →ₛₗ[(per l K).σA g] M.Hc false n j :=
  B.galHc (B.schFn M.p) (okToOC l K) (IntermediateField.fixingSubgroupEquiv K g) (galOC_okToOC _) false n j

theorem galQidApply {B : Type} [CommRing B] (J : Ideal B) (h : J ≤ J.comap (RingHom.id B)) (x : B ⧸ J) :
    Ideal.quotientMap J (RingHom.id B) h x = x := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

theorem galSpecQid {B : Type} [CommRing B] (J : Ideal B) (h : J ≤ J.comap (RingHom.id B)) :
    Spec.map (CommRingCat.ofHom (Ideal.quotientMap J (RingHom.id B) h)) = 𝟙 _ := by
  have e : Ideal.quotientMap J (RingHom.id B) h = RingHom.id _ := by
    ext x
    rfl
  rw [e, CommRingCat.ofHom_id, Spec.map_id]

section
variable {m : ℕ} {L : Lev (per l K) m} (hL : L.Good) (g : K.fixingSubgroup) (M : Model l K)

def nmGA : NMor L.γ M.p (κA (OK l K) L.I) L.γ M.p (κA (OK l K) L.I) (L.σA g) :=
  nmK L.γ L.γ M.p M.p (L.σA g) (hL.σ_dp g) (hL.σ_O g) (𝟙 _) (Category.id_comp _)

def nmGB : NMor L.γB M.q (κA K L.IB) L.γB M.q (κA K L.IB) (L.σB g) :=
  nmK L.γB L.γB M.q M.q (L.σB g) (hL.σB_dp g) (hL.σB_K g) (𝟙 _) (Category.id_comp _)

def galEta (T : Thick (nlFun L.γB 0 M.gen M.q (κA K L.IB))) :
    ((nmB M hL).mor 0).obj (((nmGB hL g M).mor 0).obj T) ⟶ ((nmGA hL g M).mor 0).obj (((nmB M hL).mor 0).obj T) :=
  mkH (RingHom.id _) (fun r => congrArg T.i (hL.σ_ι g r).symm) (DPMorphism.id T.δ).isDPMorphism (fun _ hx => hx) (by
    refine Subtype.ext (Prod.ext ?_ ?_)
    · refine Ideal.Quotient.ringHom_ext (RingHom.ext fun r => ?_)
      change Ideal.quotientMap T.J (RingHom.id T.B) (fun _ hx => hx) (T.y.1.1 (Ideal.Quotient.mk _ (L.σB g (L.ι r)))) =
        T.y.1.1 (Ideal.Quotient.mk _ (L.ι (L.σA g r)))
      rw [hL.σ_ι g r]; exact galQidApply _ _ _
    · change Spec.map (CommRingCat.ofHom (Ideal.quotientMap T.J (RingHom.id T.B) _)) ≫ ((T.y.1.2 ≫ 𝟙 M.gen) ≫ _) =
        (T.y.1.2 ≫ _) ≫ 𝟙 M.X
      rw [galSpecQid, Category.id_comp, Category.comp_id, Category.comp_id])

def galEtaO (T : Thick (nlFun L.γB 0 M.gen M.q (κA K L.IB))) :
    ((nmO L.γB M.q).mor 0).obj (((nmGB hL g M).mor 0).obj T) ⟶ ((nmO L.γB M.q).mor 0).obj T :=
  mkH (RingHom.id _) (fun r => congrArg T.i (hL.σB_K g r)) (DPMorphism.id T.δ).isDPMorphism (fun _ hx => hx) (by
    refine Subtype.ext (Prod.ext ?_ ?_)
    · refine Ideal.Quotient.ringHom_ext (RingHom.ext fun r => ?_)
      change Ideal.quotientMap T.J (RingHom.id T.B) (fun _ hx => hx) (T.y.1.1 (Ideal.Quotient.mk _ (L.σB g (algebraMap K L.B r)))) =
        T.y.1.1 (Ideal.Quotient.mk _ (algebraMap K L.B r))
      rw [hL.σB_K g r]; exact galQidApply _ _ _
    · change Spec.map (CommRingCat.ofHom (Ideal.quotientMap T.J (RingHom.id T.B) _)) ≫ ((T.y.1.2 ≫ 𝟙 M.gen) ≫ 𝟙 M.gen) =
        T.y.1.2 ≫ 𝟙 M.gen
      rw [galSpecQid, Category.id_comp, Category.comp_id])

variable (s : ℕ) (hQ : ∀ T, QB L M s T → QA L M s (((nmB M hL).mor 0).obj T))
  (rH : ∀ n j, M.Hc false n j →ₛₗ[L.lam] HM (QA L M s) none ((l : L.A) ^ n) j)

def homGal : Hom (chainOf hL M s hQ rH) (chainOf hL M s hQ rH) where
  sΛ := (per l K).σA g
  sA := L.σA g
  sB := L.σB g
  fS n j := galS M g n j
  fZn n j := nmHM (nmGA hL g M) l s none n j
  fZ j := nmHO (nmGA hL g M) l s j
  fW j := nmHO (nmGB hL g M) 1 s j
  fV _ := LinearMap.id

def GalRed : Prop :=
  ∀ n j (x : M.Hc false n j), nmHM (nmGA hL g M) l s none n j (rH n j x) = rH n j (galS M g n j x)

end

section
variable {m : ℕ} {L : Lev (per l K) m}
  (d : ∀ n, RedIn (B.DD false (PAlg.base l) n) (B.κb (okToOC l K) false n) L.γ l n)
  (hc : ∀ n (c : Acris l), (d n).ρ ((PAlg.base l).cris n c) = Ideal.Quotient.mk _ (L.lam c))

end

end CrystallineSemistableComparison.Pb.Kap
