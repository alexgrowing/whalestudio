import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.DatumEmbeddingMemHlam
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.InfChar
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SigLamEquivData
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.StdGap
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.SigLamKTypeBounds
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.InfChar
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.SigLamEquivData
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.PropsKfin

noncomputable section

open Finset Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS.G2

variable {n : ℕ} {ε : Fin n → Bool} {lam : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)}
  {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {v₀ : T.V}

theorem sigLam_kfin (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0) (S : Submodule ℂ (Hlam ε Ψ v₀)) (hSf : FiniteDimensional ℂ S)
    (hSK : Formalism.MainNotions.S.IsKStableOn ε (sigLam ε Ψ v₀) S) : S ≤ kfinLam ε Ψ v₀ := by
  have hinj : Function.Injective (Hlam ε Ψ v₀).subtype := Subtype.val_injective
  have hint := subtype_sigLam hgap hP hv₀
  have := hSf
  have hf : FiniteDimensional ℂ (S.map (Hlam ε Ψ v₀).subtype) :=
    (Submodule.equivMapOfInjective _ hinj S).finiteDimensional
  have hK : ∀ k ∈ Kset ε, ∀ x ∈ S.map (Hlam ε Ψ v₀).subtype, rreg ε k x ∈ S.map (Hlam ε Ψ v₀).subtype := by
    intro k hk x hx
    rw [← mir_Kset_eq] at hk
    exact (kStableOn_map_iff _ hinj hint S).1 hSK k hk x hx
  have h := data_kfin_le hgap (rreg_isURepOn ε) (isDerivedOn_smE (rreg_isURepOn ε))
    (datumV_isKIrrHW hP hv₀) (datumV_casimir hP v₀) (datumV_kStable hP v₀) _ (map_subtype_le_closGen S) hf hK
  intro x hx
  exact h ⟨x, hx, rfl⟩

theorem hasGelfandChar_sigLam (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0)
    (hG : ∀ (k : ℕ) (g : Matrix (Fin n) (Fin n) ℂ), inUJ ε g →
      S7.opGelfand (S7.rightE ε) k Ψ g = gval (icShift lam) k • Ψ g ∧
        S7.opGelfand (S7.rightEanti ε) k Ψ g = gval (icShift (-lam)) k • Ψ g) :
    HasGelfandChar (smE ε (rreg ε)) lam (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)) := by
  have hE : IsGlRep (smE ε (rreg ε)) := (isDerivedOn_smE (rreg_isURepOn ε)).glRep
  intro k x hx
  have hdat : ∀ y ∈ datumV ε Ψ v₀, gelfand (smE ε (rreg ε)) k y = gval (icShift lam) k • y ∧
      gelfand (antiE (smE ε (rreg ε))) k y = gval (icShift (-lam)) k • y := by
    intro y hy
    obtain ⟨v, hv⟩ := (mem_datumV_iff hP v₀ y).1 hy
    have hg := icx_good_datum hP hv
    exact ⟨icx_val (icxGood_gelfand (smE ε (rreg ε)) (S7.rightE ε) (fun a b _ _ h => icxGood_eab h a b) hg k)
        hv _ fun g hg' => (hG k g hg').1,
      icx_val (icxGood_gelfand (antiE (smE ε (rreg ε))) (S7.rightEanti ε) (fun a b _ _ h => icxGood_anti h a b) hg k)
        hv _ fun g hg' => (hG k g hg').2⟩
  exact ⟨icx_genSub_eigen _ _ _ _ (fun a b => (gelfand_comm hE k a b).symm) (fun y hy => (hdat y hy).1) x hx,
    icx_genSub_eigen _ _ _ _ (fun a b => icx_anti_comm hE k a b) (fun y hy => (hdat y hy).2) x hx⟩

theorem puniq_exists_h {lam' : Fin n → ℝ} (hgap : StdGap ε lam) (hgap' : StdGap ε lam') :
    ∃ h : ℝ, GapAtLeast ε lam h ∧ GapAtLeast ε lam' h ∧ 2 * (n : ℝ) < h ∧ (n : ℝ) - 1 < h := by
  obtain ⟨-, h1, hg1, hh1⟩ := hgap
  obtain ⟨-, h2, hg2, hh2⟩ := hgap'
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  refine ⟨min h1 h2, fun a b hab => le_trans (min_le_left _ _) (hg1 a b hab),
    fun a b hab => le_trans (min_le_right _ _) (hg2 a b hab), lt_min hh1 hh2, ?_⟩
  exact lt_min (by linarith) (by linarith)

theorem sigLam_inj (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0) {lam' : Fin n → ℝ} {T' : S7.KType ε (lowK ε lam')}
    {Ψ' : Matrix (Fin n) (Fin n) ℂ → (T'.V →L[ℂ] T'.V)} {v₀' : T'.V} (hgap' : StdGap ε lam')
    (hP' : IsPsiFor ε lam' T' Ψ') (hv₀' : v₀' ≠ 0) (U : Hlam ε Ψ v₀ ≃ₗᵢ[ℂ] Hlam ε Ψ' v₀')
    (hU : ∀ g ∈ UJset ε, ∀ x : Hlam ε Ψ v₀, U (sigLam ε Ψ v₀ g x) = sigLam ε Ψ' v₀' g (U x)) :
    lam = lam' := by
  obtain ⟨h, hg, hg', hb, hn⟩ := puniq_exists_h hgap hgap'
  have hU' : ∀ g ∈ UJset ε, ∀ y : Hlam ε Ψ' v₀', U.symm (sigLam ε Ψ' v₀' g y) = sigLam ε Ψ v₀ g (U.symm y) := by
    intro g hgU y
    have := hU g hgU (U.symm y)
    rw [LinearIsometryEquiv.apply_symm_apply] at this
    rw [← this, LinearIsometryEquiv.symm_apply_apply]
  have hK1 := puniq_isKTypeOf_map U (fun g hgK x => hU g (puniq_kset hgK) x) (sigLam_lowK hgap hP hv₀).1
  have hK2 := puniq_isKTypeOf_map U.symm (fun g hgK y => hU' g (puniq_kset hgK) y)
    (sigLam_lowK hgap' hP' hv₀').1
  have b1 := (sigLam_kType_bounds hgap' hP' hv₀' _ hK1).2 h hg' hb
  have b2 := (sigLam_kType_bounds hgap hP hv₀ _ hK2).2 h hg hb
  rw [mir_lowK_eq] at b1 b2
  by_contra hne
  have hne' : lowK ε lam ≠ lowK ε lam' := by
    intro heq
    apply hne
    funext a
    have := congrFun heq a
    simp only [lowK, Pi.add_apply, Pi.sub_apply] at this
    linarith
  have c1 := b1 hne'
  have c2 := b2 (Ne.symm hne')
  linarith

end ReciprocityTheory.ChartRestriction.DS.G2
