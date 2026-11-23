import Formalism.LocalToGlobal.UnitaryNorms.UnramT
import Formalism.LocalToGlobal.GlobalTheory.GL6.PBwLocInd

noncomputable section

open NumberField Ideal

namespace PI.UnitaryGroupMassFormula.IAT

open Formalism.BasicNotions Formalism.L2.Forms Formalism.L2.Host Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

variable {D : D7} {u : D.what₂.Word}

theorem seen_pos (A : AtTTied u) (w : D.what₂.places.Pl) (hw : Formalism.MainNotions.product_first_zeroth_parts.OverT D u w) (hseen : (D.fm u).seenP w = true)
    (v : (D.mem u).A.vT) (y : 𝓞 D.host.E) (hy : y ∈ A.Pv v) :
    0 < D.what₂.places.val w (D.embE (D.host.sigmaOf (D.eTau ((D.fm u).tauOf w v) : D.R.GG) (y : D.host.E))) := by
  have hw' : D.what₂.places.resChar w = (D.mem u).A.T := hw
  let σ : D.host.E ≃ₐ[ℚ] D.host.E :=
    D.host.sigmaOf (D.eTau ((D.fm u).tauOf w v) : D.R.GG)
  let ν : AddValuation D.host.E (WithTop ℤ) :=
    (D.what₂.places.val w).comap (D.embE.comp (σ : D.host.E →+* D.host.E))
  change 0 < ν (y : D.host.E)
  let cO : 𝓞 D.host.E ≃+* 𝓞 D.host.E := RingOfIntegers.mapRingEquiv D.host.conj.toRingEquiv
  have hcO : ∀ y : 𝓞 D.host.E, ((cO y : 𝓞 D.host.E) : D.host.E) = D.host.conj (y : D.host.E) := fun y => rfl
  have hinv := conj_conj D.host
  have mkF : ∀ z : 𝓞 D.host.E, D.host.conj (z : D.host.E) = z →
      ∃ zF : 𝓞 D.host.F, algebraMap (𝓞 D.host.F) (𝓞 D.host.E) zF = z := by
    intro z hz
    have hF : (z : D.host.E) ∈ D.host.F := (D.host.conjE_mem_hostF_iff _).2 hz
    refine ⟨⟨⟨z, hF⟩, ?_⟩, ?_⟩
    · exact (isIntegral_algHom_iff (D.host.F.subtype.toIntAlgHom) Subtype.val_injective).mp
        (RingOfIntegers.isIntegral_coe z)
    · rfl
  have hcoe : ∀ zF : 𝓞 D.host.F, algebraMap (𝓞 D.host.F) D.host.E zF =
      ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) zF : 𝓞 D.host.E) : D.host.E) := fun _ => rfl
  have hTau : ∀ zF : 𝓞 D.host.F, zF ∈ (A.eV v).1.asIdeal ↔
      0 < ν ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) zF : 𝓞 D.host.E) : D.host.E) := by
    intro zF
    rw [A.tauOf w hw' v zF, hcoe]
    exact Iff.rfl
  have hπ : 0 < ν (A.piU : D.host.E) := by
    have := A.seenP w hw' ((D.fm u).tauOf w v)
    rw [if_pos hseen] at this
    exact this
  have hpb : A.res v (cO A.piU) ≠ 0 := A.res_conj v (cO A.piU) rfl
  have hπb : ν ((cO A.piU : 𝓞 D.host.E) : D.host.E) = 0 := by
    obtain ⟨zF, hzF⟩ := mkF (A.piU + cO A.piU) (by
      push_cast; simp only [hcO, map_add, hinv]; ring)
    have hnot : zF ∉ (A.eV v).1.asIdeal := by
      rw [A.res_v, hzF, map_add, A.res_pi, zero_add]; exact hpb
    rw [hTau, hzF] at hnot
    refine le_antisymm (not_lt.mp fun h => hnot ?_) (addVal_nonneg ν _)
    push_cast
    exact lt_of_lt_of_le (lt_min hπ h) (ν.map_add _ _)
  have hy' : A.res v y = 0 := hy
  obtain ⟨zF, hzF⟩ := mkF (y * cO A.piU + cO y * A.piU) (by
    push_cast; simp only [hcO, map_add, map_mul, hinv]; ring)
  have hin : zF ∈ (A.eV v).1.asIdeal := by
    rw [A.res_v, hzF, map_add, map_mul, map_mul, hy', A.res_pi]; simp
  rw [hTau, hzF] at hin
  push_cast at hin
  have h2 : 0 < ν (((cO y : 𝓞 D.host.E) : D.host.E) * A.piU) := by
    rw [ν.map_mul]; exact lt_of_lt_of_le hπ (le_add_of_nonneg_left (addVal_nonneg ν _))
  have h3 : 0 < ν ((y : D.host.E) * (cO A.piU : 𝓞 D.host.E)) := by
    have : (y : D.host.E) * (cO A.piU : 𝓞 D.host.E) =
        ((y : D.host.E) * (cO A.piU : 𝓞 D.host.E) + ((cO y : 𝓞 D.host.E) : D.host.E) * A.piU) -
          ((cO y : 𝓞 D.host.E) : D.host.E) * A.piU := by ring
    rw [this]
    exact lt_of_lt_of_le (lt_min hin h2) (ν.map_sub _ _)
  rwa [ν.map_mul, hπb, add_zero] at h3

theorem seen_zero (A : AtTTied u) (w : D.what₂.places.Pl) (hw : Formalism.MainNotions.product_first_zeroth_parts.OverT D u w) (hseen : (D.fm u).seenP w = true)
    (v : (D.mem u).A.vT) (s : 𝓞 D.host.E) (hs : s ∉ A.Pv v) :
    D.what₂.places.val w (D.embE (D.host.sigmaOf (D.eTau ((D.fm u).tauOf w v) : D.R.GG) (s : D.host.E))) = 0 := by
  let σ : D.host.E ≃ₐ[ℚ] D.host.E :=
    D.host.sigmaOf (D.eTau ((D.fm u).tauOf w v) : D.R.GG)
  let ν : AddValuation D.host.E (WithTop ℤ) :=
    (D.what₂.places.val w).comap (D.embE.comp (σ : D.host.E →+* D.host.E))
  have hPmax : (A.Pv v).IsMaximal := RingHom.ker_isMaximal_of_surjective (A.res v) (A.res_surj v)
  exact addVal_eq_zero_of_not_mem ν (A.Pv v) hPmax (fun y hy => seen_pos A w hw hseen v y hy) s hs

theorem seen_mem (A : AtTTied u) (w : D.what₂.places.Pl) (hw : Formalism.MainNotions.product_first_zeroth_parts.OverT D u w) (hseen : (D.fm u).seenP w = true)
    (v : (D.mem u).A.vT) (e : D.host.E) (s : 𝓞 D.host.E) (hs : s ∉ A.Pv v)
    (he : (s : D.host.E) * e ∈ (algebraMap (𝓞 D.host.E) D.host.E).range) :
    embT D ((D.fm u).tauOf w v) e ∈ bwA_Ow D w := by
  obtain ⟨a, ha⟩ := he
  let σ : D.host.E ≃ₐ[ℚ] D.host.E :=
    D.host.sigmaOf (D.eTau ((D.fm u).tauOf w v) : D.R.GG)
  let ν : AddValuation D.host.E (WithTop ℤ) :=
    (D.what₂.places.val w).comap (D.embE.comp (σ : D.host.E →+* D.host.E))
  have hν : ∀ y, ν y = D.what₂.places.val w (D.embE (σ y)) := fun y => rfl
  have hs0 : ν (s : D.host.E) = 0 := seen_zero A w hw hseen v s hs
  have ha0 : 0 ≤ ν (a : D.host.E) := addVal_nonneg ν a
  have he0 : 0 ≤ ν e := by
    have h1 : ν ((s : D.host.E) * e) = ν (a : D.host.E) := by rw [← ha]
    rw [ν.map_mul, hs0, zero_add] at h1
    rw [h1]; exact ha0
  rw [bwA_embT_eq]
  exact ⟨_, he0, rfl⟩

end PI.UnitaryGroupMassFormula.IAT

end
