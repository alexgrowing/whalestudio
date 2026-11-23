import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonal

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta

variable (D : D7) (hF : OFull D) (hz : OZeta D) (hN : N1ab) (l : Level (hostOfRecord D))
  (hl : l.M = D.host.g 0 * D.host.g 1 ∧ l.A = 1)

def parAt : Par D where
  H := hostOfRecord D
  l := l
  c :=
    { F := FO D
      fin := inferInstance
      conj := fun τ a => conj_mem_FO D τ a
      zeta_mem := by
        have h := (coeffFieldOfRecord D (hU := unramBridge D.host.E (cmUnram_conj D)) hz).zeta_mem
        have h1 : (levelG D (hU := unramBridge D.host.E (cmUnram_conj D))).M' = l.M' := by
          simp [Level.M', levelG, levelOfPs, hl.1, hl.2]
        rw [h1] at h
        exact h
      le := by
        have h := (coeffFieldOfRecord D (hU := unramBridge D.host.E (cmUnram_conj D)) hz).le
        have h1 : KA l = KA (levelG D (hU := unramBridge D.host.E (cmUnram_conj D))) := by
          unfold KA
          rw [hl.2]
          rfl
        rw [h1]
        exact h }
  Dw := datumAtLift D _ (datHolds D)
  Xo := fun j => Classical.choice (hN D.host.E _ (datumAtLift D _ (datHolds D) j) l (datumAtLift_pq_pos D _ (datHolds D) j))
  eO := eOf D hF

theorem parAt_pins : (parAt D hF hz hN l hl).Pins := by
  refine ⟨⟨rfl, rfl, rfl, tauEmb_sqrt D⟩, hl, eOf_spec D hF, fun j hj => ?_⟩
  show IsDatW D j (datumAtLift D _ (datHolds D) j)
  unfold datumAtLift
  rw [dif_pos hj]
  exact isDatW_datumOf D _ j _ _

theorem parAt_pq (j : ℕ) : 1 ≤ ((parAt D hF hz hN l hl).Dw j).p + ((parAt D hF hz hN l hl).Dw j).q :=
  datumAtLift_pq_pos D _ (datHolds D) j

def LevelPb (pb : Fin 2 → HeightOneSpectrum (𝓞 D.host.K)) : Prop :=
  ∃ l : Level (hostOfRecord D), (l.M = D.host.g 0 * D.host.g 1 ∧ l.A = 1) ∧
    l.Mb = ∏ k, (pb k).asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E))

theorem coreJExists_at (hN1c : N1c) (pb : Fin 2 → HeightOneSpectrum (𝓞 D.host.K))
    (hg : ∀ k, ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ (pb k).asIdeal)
    (hb : l.Mb = ∏ k, (pb k).asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)))
    (chiW : ℕ → ((parAt D hF hz hN l hl).c.F →+* ℂ) → (AE D)ˣ →* Circle)
    (L : LawsJRest hN1c (parAt D hF hz hN l hl) (parAt_pq D hF hz hN l hl) chiW) :
    ∃ T : CoreJ D, LawsJ T ∧ T.pb = pb ∧ T.Q = parAt D hF hz hN l hl ∧ HEq T.chiW chiW := by
  have h := lawsJ_coreJOf L (parAt_pins D hF hz hN l hl)
  exact ⟨{ coreJOf L with toCore := { (coreJOf L).toCore with pb := pb } },
    { h with toLawsM := { h.toLawsM with half := ⟨hg, hb⟩ } }, rfl, rfl, HEq.rfl⟩

end Formalism.L2.Pj
