import Mathlib
import Formalism.SharpRestriction.GrowthBounds.WeilJacquetShalikaLaw
import Formalism.SharpRestriction.ParConsts
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsPlaceCofactorValuationLowerBound
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.LocalLevelIsKOneAtT

noncomputable section

namespace GlobalTheory.TwU

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits Classical Formalism.L2.KerInert.Loc

theorem resV_subst_two {ι κ σ τ R : Type} [CommRing R] [Finite ι] [Finite σ]
    {f : κ → ι} (hf : Function.Injective f) {g : τ → σ} (hg : Function.Injective g)
    {a : σ → MvPowerSeries ι R} (ha : MvPowerSeries.HasSubst a)
    {a' : τ → MvPowerSeries κ R} (ha' : MvPowerSeries.HasSubst a')
    (h1 : ∀ k, resV f (a (g k)) = a' k) (h0 : ∀ i, (∀ k, g k ≠ i) → resV f (a i) = 0)
    (T : MvPowerSeries σ R) :
    resV f (MvPowerSeries.subst a T) = MvPowerSeries.subst a' (resV g T) := by
  rw [resV_subst hf ha, resV_eq_subst hg T, MvPowerSeries.subst_comp_subst_apply (hasSubst_resFam g) ha']
  congr 1
  funext i
  by_cases h : ∃ k, g k = i
  · obtain ⟨k, rfl⟩ := h
    rw [h1, resFam_apply hg, MvPowerSeries.subst_X ha']
  · push_neg at h
    rw [h0 i h, resFam_off g i h, ← MvPowerSeries.coe_substAlgHom ha', map_zero]

theorem resV_CX {ι κ R : Type} [CommRing R] [Finite ι] {f : κ → ι} (hf : Function.Injective f) (c : R) (k : κ) :
    resV f (MvPowerSeries.C c * MvPowerSeries.X (f k) : MvPowerSeries ι R) = MvPowerSeries.C c * MvPowerSeries.X k := by
  rw [resV_mul hf, resV_X hf]
  congr 1
  ext n
  rw [resV_coeff, MvPowerSeries.coeff_C, MvPowerSeries.coeff_C]
  by_cases hn : n = 0
  · subst hn; simp
  · rw [if_neg hn, if_neg]
    intro h0
    apply hn
    have := congrArg Finsupp.degree h0
    rw [degree_mapDomain] at this
    exact (Finsupp.degree_eq_zero_iff n).1 (by simpa using this)

theorem resV_CX_off {ι κ R : Type} [CommRing R] [Finite ι] {f : κ → ι} (hf : Function.Injective f) (c : R) (i : ι)
    (hi : ∀ k, f k ≠ i) :
    resV f (MvPowerSeries.C c * MvPowerSeries.X i : MvPowerSeries ι R) = 0 := by
  rw [resV_mul hf, resV_X_off hf i hi, mul_zero]

theorem inj_at {p : ℕ} [Fact p.Prime] (X : Sys p) (j : ℕ) (v : X.Pl) :
    Function.Injective (fun z : Zidx (X.G.P.n' v) (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1)) => (⟨v, z⟩ : X.ZA j)) :=
  fun a b h => eq_of_heq (Sigma.mk.inj_iff.1 h).2

theorem inE_inj {p : ℕ} [Fact p.Prime] (X : Sys p) (j : ℕ) (v : X.Pl) : Function.Injective (inE X j v) := by
  have hg : Function.Injective (fun e : Eidx (X.G.P.n' v) (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1)) => (⟨v, e⟩ : X.EA j)) :=
    fun a b h => eq_of_heq (Sigma.mk.inj_iff.1 h).2
  exact hg.sumMap hg

end GlobalTheory.TwU

namespace GlobalTheory.TwU

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits Classical Formalism.L2.KerInert.Loc

theorem hasSubst_coordZA {p : ℕ} [Fact p.Prime] (X : Sys p) (j : ℕ) :
    MvPowerSeries.HasSubst (X.coordZA (K0 p) j) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (by
    rintro (⟨w, r, a, b⟩ | ⟨w, r, a, b⟩) <;> simp [Sys.coordZA])

theorem hasSubst_coordZ {p : ℕ} [Fact p.Prime] {n' r0 r1 : ℕ} (B : OmBasis p n') :
    MvPowerSeries.HasSubst (coordZ (r0 := r0) (r1 := r1) B (K0 p) 1) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (by
    rintro (⟨r, a, b⟩ | ⟨r, a, b⟩) <;> simp [coordZ])

theorem resV_ThZA {p : ℕ} [Fact p.Prime] (X : Sys p) (j : ℕ) (v : X.Pl) (T : MvPowerSeries (X.EA j ⊕ X.EA j) (K0 p)) :
    resV (fun z : Zidx (X.G.P.n' v) (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1)) => (⟨v, z⟩ : X.ZA j)) (X.ThZA (K0 p) j T) =
      ThZ (X.om v) (K0 p) 1 (resV (inE X j v) T) := by
  have hE := inE_inj X j v
  have hZ := inj_at X j v
  unfold Sys.ThZA ThZ
  refine resV_subst_two hZ hE (hasSubst_coordZA X j) (hasSubst_coordZ _) ?_ ?_ T
  · rintro (⟨r, a, b⟩ | ⟨r, a, b⟩)
    · show resV _ (X.coordZA (K0 p) j (Sum.inl ⟨v, (r, a, b)⟩)) = _
      simp only [Sys.coordZA, coordZ]
      rw [resV_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [one_mul, Algebra.algebraMap_self, RingHom.id_apply]
      exact resV_CX hZ _ (s, a, b)
    · show resV _ (X.coordZA (K0 p) j (Sum.inr ⟨v, (r, a, b)⟩)) = _
      simp only [Sys.coordZA, coordZ]
      rw [resV_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [one_mul, Algebra.algebraMap_self, RingHom.id_apply]
      exact resV_CX hZ _ (s, a, b)
  · rintro (⟨w, r, a, b⟩ | ⟨w, r, a, b⟩) hi
    · have hw : w ≠ v := by
        rintro rfl
        exact hi (Sum.inl (r, a, b)) rfl
      simp only [Sys.coordZA]
      rw [resV_sum]
      refine Finset.sum_eq_zero fun s _ => ?_
      exact resV_CX_off hZ _ _ (fun z h => hw (congrArg Sigma.fst h).symm)
    · have hw : w ≠ v := by
        rintro rfl
        exact hi (Sum.inr (r, a, b)) rfl
      simp only [Sys.coordZA]
      rw [resV_sum]
      refine Finset.sum_eq_zero fun s _ => ?_
      exact resV_CX_off hZ _ _ (fun z h => hw (congrArg Sigma.fst h).symm)

theorem resV_phAt {p : ℕ} [Fact p.Prime] (X : Sys p) (be : MvPowerSeries (Fin 2) (K0 p)) (j : ℕ) (v : X.Pl) :
    resV (inE X j v) (phAt X be j v) =
      ∑ e : Eidx (X.G.P.n' v) (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1)),
        sub2 p be (MvPowerSeries.X (Sum.inl e)) (MvPowerSeries.X (Sum.inr e)) := by
  have hE := inE_inj X j v
  unfold phAt
  rw [resV_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [restrict_formalSum hE be (by simp) (by simp)]
  exact congrArg₂ (sub2 p be) (resV_X hE (Sum.inl e)) (resV_X hE (Sum.inr e))

theorem restr_onePlace : ∀ (p : ℕ) [Fact p.Prime] (X : Sys p) (be : MvPowerSeries (Fin 2) (K0 p)) (j : ℕ) (v : X.Pl)
    (U : MvPowerSeries (X.EA j ⊕ X.EA j) (K0 p)), MvPowerSeries.constantCoeff be = 0 → IntS p (inParam p U) →
    IntS p (inParam p (resV (inE X j v) U)) ∧
      resV (fun z : Zidx (X.G.P.n' v) (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1)) => (⟨v, z⟩ : X.ZA j))
        (X.ThZA (K0 p) j (expS p (-phAt X be j v) * U)) = thOne (X.om v) be (resV (inE X j v) U) := by
  intro p _ X be j v U _ hU
  have hE := inE_inj X j v
  refine ⟨?_, ?_⟩
  · obtain ⟨g, hg⟩ := hU
    exact ⟨resV (inE X j v) g, by rw [← resV_inParam hE, hg, resV_map]⟩
  · rw [resV_ThZA, resV_mul hE, resV_expS hE, resV_neg, resV_phAt]
    rfl

end GlobalTheory.TwU

end
