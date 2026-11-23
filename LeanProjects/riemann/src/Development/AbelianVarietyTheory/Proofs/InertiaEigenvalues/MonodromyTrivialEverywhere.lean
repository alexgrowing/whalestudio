import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAttachedHodge
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjPlMemPlacesOver
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeneralAdmissibleOfIrreducibilityStmt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPadicAlgClRingEquivComplexCompEqOfCountabl
import ReciprocityTheory.GaloisValuations.ArithOfA
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NoMonodromyOfInertiaSeparableCharpoly

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial Formalism.L2.Host GlobalTheory.Pst GlobalTheory.GalOfCusp GlobalTheory.TripleLocal GlobalTheory.TypeLeaf

noncomputable section

namespace GlobalTheory.GoodRowMono

theorem separable_prod_teich {g : ℕ} [Fact g.Prime] (t : Formalism.CyclotomicNorms.Fbar g →* ℂ)
    (ht : ∀ x y, x ≠ 0 → y ≠ 0 → t x = t y → x = y) {f : (ZMod g)[X]} (hf : Squarefree f) :
    (((Formalism.CyclotomicNorms.rootsBar f).map fun x => X - C (t x)).prod).Separable := by
  have hnd : ((Formalism.CyclotomicNorms.rootsBar f).map t).Nodup :=
    (nodup_roots ((separable_map _).2 (PerfectField.separable_iff_squarefree.2 hf))).map (GlobalTheory.TameLabels.teich_injective t ht)
  have e : ((Formalism.CyclotomicNorms.rootsBar f).map fun x => X - C (t x)) =
      ((Formalism.CyclotomicNorms.rootsBar f).map t).map (fun a => X - C a) := by
    rw [Multiset.map_map]; rfl
  rw [e]
  have hs : ((((Formalism.CyclotomicNorms.rootsBar f).map t).map fun a => X - C a).prod).Splits :=
    Splits.multisetProd fun x hx => by
      obtain ⟨y, -, rfl⟩ := Multiset.mem_map.1 hx
      exact Splits.X_sub_C _
  refine (nodup_roots_iff_of_splits (monic_multiset_prod_of_monic _ _ fun a _ => monic_X_sub_C a).ne_zero hs).1 ?_
  rw [roots_multiset_prod_X_sub_C]
  exact hnd

variable (D : D7)

theorem mono0_of_separable (T : GlobalTheory.RowTie.WDTie D.nd D.naut) {w : PlE D.host} (L : D.naut.LP w) {s : G D.host.E D.nd.Om}
    (hs : s ∈ Ine (F := D.host.E) (D.nd.plOm.1 w)) (h : (D.naut.inePol L s).Separable) : D.naut.mono0 L := by
  rw [T.mono0]
  rw [T.inePol w L s hs] at h
  exact GlobalTheory.WeilDeligne.WD.noMonodromy_of_inertia_separable_charpoly D.host.E D.nd.Om _ w (D.nd.plOm.2 w) (T.e w L) s hs h

variable {D}

theorem separable_fixed {σ : D.what₂.FT} {π : D.naut.CG D.R.r} (hg : D.nd.goodRow σ)
    (hlab : ∀ k v, D.nd.lab k σ v = D.naut.items₂ k (D.naut.plGw k v) (D.naut.locG π (D.naut.plGw k v)))
    (k : Fin 2) (v : D.nd.PlG k) :
    (D.naut.inePol (D.naut.locG π (D.naut.plGw k v)) (D.ntypes.tg k v)).Separable := by
  have : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  have hfull : (D.naut.items₂ k (D.naut.plGw k v) (D.naut.locG π (D.naut.plGw k v))).natDegree =
      D.naut.lpDim (D.naut.locG π (D.naut.plGw k v)) := by
    rw [← hlab, (D.nd.lab_monic k σ v).2, D.naut.locG_dim]
  rw [D.ntypes.inertiaCharpoly_type k v _ hfull, ← hlab]
  exact separable_prod_teich _ (D.ntypes.teichC_inj k) ((hg k).1.2.1 v)

theorem separable_conj (T : GlobalTheory.RowTie.WDTie D.nd D.naut) (hD : FrobDense D) (hG : GalHodge D T)
    {σ : D.what₂.FT} {π : D.naut.CG D.R.r} (hg : D.nd.goodRow σ) (hc : D.naut.csd π) (hra : D.naut.ralg π)
    (hlab : ∀ k v, D.nd.lab k σ v = D.naut.items₂ k (D.naut.plGw k v) (D.naut.locG π (D.naut.plGw k v)))
    (k : Fin 2) (v : D.nd.PlG k) {w : PlE D.host} (hv : IsConjPl D.host (D.naut.plGw k v) w) :
    ∃ s ∈ Ine (F := D.host.E) (D.nd.plOm.1 w), (D.naut.inePol (D.naut.locG π w) s).Separable := by
  obtain ⟨l, hl1, hl2⟩ := Nat.exists_infinite_primes (D.host.g k + 1)
  have : Fact l.Prime := ⟨hl2⟩
  have hne : l ≠ D.host.g k := by omega
  obtain ⟨ι⟩ : Nonempty (Qbar l ≃+* ℂ) := GlobalTheory.nonempty_padicAlgCl_ringEquiv_complex l
  obtain ⟨r, hr⟩ := hG l ι π 0 hc ((regAlgShift_zero D.naut π).2 hra)
  have hR := hr.toIsAttachedAway.isGaloisRepOf
  set t := D.ntypes.tg k v with htdef
  have ht : t ∈ Ine (F := D.host.E) (D.nd.plOm.1 (D.naut.plGw k v)) := D.ntypes.tg_mem k v
  have hw0 : D.naut.plGw k v ∉ placesOver D.host.E l := GlobalTheory.TameLabels.not_mem_of_ne hl2 hne
  have hwl : w ∉ placesOver D.host.E l := fun h =>
    hw0 (GlobalTheory.TwistDet.mem_placesOver_conj (GlobalTheory.TwistDet.isConjPl_symm hv) h)
  have hti : t⁻¹ ∈ Ine (F := D.host.E) (D.nd.plOm.1 (D.naut.plGw k v)) := Subgroup.inv_mem _ ht
  have e1 := GlobalTheory.TripleResidual.charpoly_cConj D.ntw hD hc hR t⁻¹
  rw [cyc_eq_one_of_mem_Ine hw0 (D.nd.plOm.2 _) hti, Units.val_one, one_zpow, one_smul, inv_inv] at e1
  have hB := GlobalTheory.TwistDet.isPlaceOver_moveVal_cc D.ntw hv (D.nd.plOm.2 (D.naut.plGw k v))
  have hcI := GlobalTheory.TwistDet.cConj_mem_ine D.ntw hti
  obtain ⟨γ, hγ⟩ := exists_smul_eq_of_isPlaceOver (F := D.host.E) hB (D.nd.plOm.2 w)
  have hs : γ * GlobalTheory.TwistDet.cConj D.ntw t⁻¹ * γ⁻¹ ∈ Ine (F := D.host.E) (D.nd.plOm.1 w) :=
    hγ ▸ conj_mem_Ine_smul hcI
  refine ⟨_, hs, ?_⟩
  have e2 := (hR.2.2 w hwl).1 _ hs
  have e3 := (hR.2.2 _ hw0).1 t ht
  rw [GlobalTheory.TripleResidual.charpoly_conj_GL, e1, e3, D.naut.inePol_tw _ _ _ ht] at e2
  rw [← D.naut.inePol_tw _ ((1 - (D.R.r : ℝ)) / 2) _ hs, ← e2]
  exact separable_fixed hg hlab k v

theorem mono0_all : ∀ (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut), FrobDense D → GalHodge D T →
    ∀ (σ : D.what₂.FT) (π : D.naut.CG D.R.r), D.nd.goodRow σ → D.naut.csd π → D.naut.ralg π →
    (∀ w, (∀ k, w ∉ placesOver D.host.E (D.host.g k)) → D.naut.unr (D.naut.locG π w)) →
    (∀ k v, D.nd.lab k σ v = D.naut.items₂ k (D.naut.plGw k v) (D.naut.locG π (D.naut.plGw k v))) →
    ∀ w, D.naut.mono0 (D.naut.locG π w) := by
  intro D T hD hG σ π hg hc hra hunr hlab w
  by_cases hw : ∀ k, w ∉ placesOver D.host.E (D.host.g k)
  · exact D.naut.unr_mono0 _ (hunr w hw)
  push Not at hw
  obtain ⟨k, hk⟩ := hw
  obtain ⟨v, rfl | hv⟩ := GlobalTheory.TypePlaceCover.place_cover D k w hk
  · exact mono0_of_separable D T _ (D.ntypes.tg_mem k v) (separable_fixed hg hlab k v)
  · obtain ⟨s, hs, hsp⟩ := separable_conj T hD hG hg hc hra hlab k v hv
    exact mono0_of_separable D T _ hs hsp

end GlobalTheory.GoodRowMono
