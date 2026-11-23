import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LevGap
import Formalism.SharpRestriction.InertJacobiLevels.WeightedTrivialDatumMetricLatticeTrivial

noncomputable section

namespace Formalism.MainNotions.Gaps.LG

open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.FrobeniusOrbits Formalism.MainNotions.Inhab
open scoped TensorProduct

section HostC

variable {R : Ranks} (H : Host R) (T0 : ℕ) [hT0 : Fact T0.Prime] (pz0 : 𝓞 H.E)
  (hpz0 : (pz0 : H.E) * H.conj (pz0 : H.E) = (T0 : H.E))

theorem parOf_eq_base (T : ℕ) (pz : 𝓞 H.E) (piG : Fin 2 → 𝓞 H.E) :
    (letI := H.cmStar; parOf (hostSpacesOfNorm H T0 pz0 hpz0) H.g T pz (fun i => H.conj (piG i : H.E))) = hostPar H T pz piG := by
  let _ := H.cmStar
  simp only [parOf, hostPar, Par.mk.injEq, and_true]
  exact ⟨signature_eq_conjugation H T0 pz0 hpz0, gram_matrix_zero_eq_one H T0 pz0 hpz0⟩

def latOfBase (T : ℕ) (pz : 𝓞 H.E) (a : Fin 2 → H.E)
    (S : (letI := H.cmStar; parOf (hostSpacesOfNorm H T0 pz0 hpz0) H.g T pz a).Splits)
    [Finite ((letI := H.cmStar; parOf (hostSpacesOfNorm H T0 pz0 hpz0) H.g T pz a).Cls S)] (d : ℕ) (hd : 0 < d) :
    letI := H.cmStar
    ∀ i, (clsPkg ((parOf (hostSpacesOfNorm H T0 pz0 hpz0) H.g T pz a).Cls S) d hd).cls i →
      Submodule (𝓞 H.E) ((hostSpacesOfNorm H T0 pz0 hpz0).X i).V :=
  letI := H.cmStar
  fun i => match i with
  | 0 => fun c => latBack (hostSpacesOfNorm H T0 pz0 hpz0)
      (CS.globLat ((Quotient.out c : (parOf (hostSpacesOfNorm H T0 pz0 hpz0) H.g T pz a).GA) :
        GL (Fin R.k) (H.E ⊗[H.F] FiniteAdeleRing (𝓞 H.F) H.F)) (parOf (hostSpacesOfNorm H T0 pz0 hpz0) H.g T pz a).Lb)
  | _ + 1 => fun c => Empty.elim c

end HostC

set_option maxHeartbeats 800000 in

theorem levGap5_of (h1 : FactSplitG) (h2 : FactLb) (h3 : FactFMCard) (h4 : FactIwLe) (h5 : FactUCompact)
    (h6 : FactUOpen) (h7 : FactClsFinite) (h8 : FactStabTriv) (h9 : FactTNeG) (h10 : FactPlacesT)
    (h11 : FactTau) : Formalism.MainNotions.Inhab.LevelGap := by
  intro R H W _ u0 T hT hlev hpde pz hK hpz hcong hpi
  letI := H.cmStar
  choose piG hpiK hpiN using hpi
  have hd : 0 < minkM (2 * R.f * R.N R.m) := asm_minkM_pos _
  by_cases hg : ∀ k, (placesOver H.E (H.g k)).ncard = Module.finrank ℚ H.E
  · have hyp : ∀ u, LevHyp H (T u) (pz u) piG := fun u => ⟨(hT u).out, hK u, hpz u, hcong u, hpiK, hpiN, hg⟩
    have ok : ∀ u, (parOf (hostSpacesOfNorm H (T u0) (pz u0) (hpz u0)) H.g (T u) (pz u)
        (fun i => H.conj (piG i : H.E))).AllOK (2 * R.f) := by
      intro u
      rw [parOf_eq_base]
      exact ⟨⟨fun i v h => Classical.choice (h1 H (T u) (pz u) piG (hyp u) i v h)⟩, h2 H (T u) (pz u) piG (hyp u),
        h3 H (T u) (pz u) piG (hyp u), h4 H (T u) (pz u) piG (hyp u), h5 H (T u) (pz u) piG (hyp u),
        h6 H (T u) (pz u) piG (hyp u), h7 H (T u) (pz u) piG (hyp u), h8 H (T u) (pz u) piG (hyp u)⟩
    have hS : ∀ u, Nonempty (parOf (hostSpacesOfNorm H (T u0) (pz u0) (hpz u0)) H.g (T u) (pz u)
        (fun i => H.conj (piG i : H.E))).Splits := fun u => (ok u).splits
    let S := fun u => Classical.choice (hS u)
    haveI : ∀ u, Finite ((parOf (hostSpacesOfNorm H (T u0) (pz u0) (hpz u0)) H.g (T u) (pz u)
        (fun i => H.conj (piG i : H.E))).Cls (S u)) := fun u => (ok u).fin (S u)
    have heT : ∀ u, Nonempty (Fin R.f ≃ PlT H (T u)) := fun u => h10 H (T u) (pz u) piG (hyp u)
    let eT := fun u => Classical.choice (heT u)
    have hTg : ∀ u i, Nat.Coprime (T u) (H.g i) := fun u i =>
      (Nat.coprime_primes (hT u).out (H.g_prime i)).2 (h9 H (T u) (pz u) piG (hyp u) i)
    have htau0 : ∀ u (w : HeightOneSpectrum (𝓞 H.E)), ∃ e : Fin R.f ≃ ↥(R.Psi), PlacesToy.resCharW w = T u →
        ∀ (v : Fin R.f) (x : 𝓞 H.F), x ∈ (eT u v).1.asIdeal ↔
          (0 : WithTop ℤ) < PlacesToy.valW w (H.sigmaOf (e v : R.GG) (algebraMap H.F H.E (x : H.F))) := by
      intro u w
      by_cases h : PlacesToy.resCharW w = T u
      · obtain ⟨e, he⟩ := h11 H (T u) (pz u) piG (hyp u) w (h ▸ PlacesToy.resCharW_mem w)
        exact ⟨(eT u).trans e, fun _ v x => (he (eT u v) x).trans (valW_pos_iff _ _).symm⟩
      · exact ⟨Fintype.equivOfCardEq (by rw [Fintype.card_fin, card_realPlaces_eq_degree]), fun hh => absurd hh h⟩
    choose tauF htau using htau0
    refine ⟨fun u => clsPkg ((parOf (hostSpacesOfNorm H (T u0) (pz u0) (hpz u0)) H.g (T u) (pz u)
        (fun i => H.conj (piG i : H.E))).Cls (S u)) (minkM (2 * R.f * R.N R.m)) hd,
      fun _ _ => ⟨fun c => Empty.elim c⟩, fun _ => rfl,
      fun u => latOfBase H (T u0) (pz u0) (hpz u0) (T u) (pz u) _ (S u) (minkM (2 * R.f * R.N R.m)) hd, ?_, ?_⟩
    · intro u i c
      match i, c with
      | 0, c =>
        exact latBack_isLattice _ _
          (Formalism.UG.P.global_lattice_isLattice_holds H.F H.E (Fin R.k) _ (ok u).lb.fin (ok u).lb.span _)
      | _ + 1, c => exact Empty.elim c
    · intro hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol Dst hD du hdu Gam hG hwin
        hg' ht G kb ks tw htw
      refine levGapD_gen _ pz piG ?_ ?_ ?_ ?_ ?_ ?_ S (fun _ => Equiv.refl _) ?_ ?_ ?_
        eT tauF ?_
      · exact hK
      · exact hpz
      · exact hcong
      · exact hpiK
      · exact hpiN
      · exact ok
      · exact fun _ _ => inferInstanceAs (Subsingleton Unit)
      · exact fun _ c => crdLat0_latBack _ _
      · exact hTg
      · exact fun u w hw v x => htau u w hw v x
  · refine ⟨fun _ => clsPkg Empty (minkM (2 * R.f * R.N R.m)) hd, fun _ _ => ⟨fun c => Empty.elim c⟩, fun _ => rfl,
      fun _ i => match i with
        | 0 => fun c => Empty.elim c
        | _ + 1 => fun c => Empty.elim c, ?_, ?_⟩
    · intro _ i c
      match i, c with
      | 0, c => exact Empty.elim c
      | _ + 1, c => exact Empty.elim c
    · intro hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol Dst hD du hdu Gam hG hwin
        hg' ht G kb ks tw htw
      exact absurd hg' hg

theorem levGap5 : Formalism.MainNotions.Inhab.LevelGap :=
  levGap5_of factSplitG Formalism.MainNotions.Gaps.LevGap.factLb factFMCard factIwLe Formalism.MainNotions.Gaps.LevGap.factUCompact
    Formalism.MainNotions.Gaps.LevGap.factUOpen factClsFinite factStabTriv Formalism.MainNotions.Gaps.LevGap.factTNeG
    Formalism.MainNotions.Gaps.LevGap.factPlacesT Formalism.MainNotions.Gaps.LevGap.factTau

end Formalism.MainNotions.Gaps.LG

end
