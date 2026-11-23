import Development.WeilBound.ThetaLifts.SphericalLattices.ChartSt
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GlobalUnitScalingHaarProductFormula
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OrdLEqNegLog

noncomputable section

namespace PositivityTheory.Sph.M2

open scoped Matrix TensorProduct
open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LFun.InertChart GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  PositivityTheory.ThK PositivityTheory.ThKH.Iwas MeasureTheory GlobalTheory.Doubling

theorem relIndex_transport {G H : Type} [Group G] [Group H] (U : Subgroup G) (Φ : G →* H)
    (hinj : ∀ g ∈ U, ∀ g' ∈ U, Φ g = Φ g' → g = g') {A B : Subgroup G} (hA : A ≤ U) (hB : B ≤ U) :
    (A.map Φ).relIndex (B.map Φ) = A.relIndex B := by
  have hφ : Function.Injective (Φ.comp U.subtype) := fun x y e => Subtype.ext (hinj _ x.2 _ y.2 e)
  have e : ∀ C : Subgroup G, C ≤ U → (C.subgroupOf U).map (Φ.comp U.subtype) = C.map Φ := fun C hC => by
    rw [← Subgroup.map_map, Subgroup.subgroupOf_map_subtype, inf_of_le_left hC]
  rw [← e A hA, ← e B hB, Subgroup.relIndex_map_map_of_injective _ _ hφ, Subgroup.relIndex_subgroupOf hB]

theorem map_conj_map {G H : Type} [Group G] [Group H] (Φ : G →* H) (g : G) (A : Subgroup G) :
    (A.map (MulAut.conj g).toMonoidHom).map Φ = (A.map Φ).map (MulAut.conj (Φ g)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [map_mul, map_inv]

theorem modSt_of (hC : ChartSt) (hL : LocModSt) : PositivityTheory.Sph.ModSt := by
  intro F E _ _ _ _ _ σ d B W r s hB hW v w hw _ m Cy hLag hAd p hp t ht u hu
  obtain rfl : d = m + m := hLag.rank.trans (two_mul m)
  have hσ := hB.cm
  have h : w.under (𝓞 F) = v := (under_eq_iff hw w).2 rfl
  obtain ⟨c, hc, -⟩ := existsUnique_isConjAt σ hw h
  obtain ⟨ϖ, hU⟩ := exists_isUnramInv hσ hw hc
  obtain ⟨Φ, hG, hinj, hsurj, hK, hP, hdet⟩ := hC F E σ B r s m W hB hW v w hw h c hc Cy hLag
  set KP := PositivityTheory.Sph.PSub σ W v Cy ⊓ KSub σ W v with hKP
  have hKPU : KP ≤ USub σ W v := fun g hg => (hg.2 : g ∈ KAt σ W v).1
  have hpU : p ∈ USub σ W v := (hp.1 : p ∈ PAt σ W v Cy).1
  have himg : KP.map Φ = KPW (w.adicCompletion E) c m := by
    ext M
    constructor
    · rintro ⟨g, hg, rfl⟩
      have hgU := hKPU hg
      exact ⟨(hP g hgU).1 hg.1, hG g, (hK g hgU).1 hg.2⟩
    · rintro ⟨hM1, hM2, hM3⟩
      obtain ⟨g, hgU, rfl⟩ := hsurj _ hM2
      exact ⟨g, ⟨(hP g hgU).2 hM1, (hK g hgU).2 hM3⟩, rfl⟩
  have hconj : ∀ g ∈ USub σ W v, KP.map (MulAut.conj g).toMonoidHom ≤ USub σ W v := fun g hg => by
    rintro _ ⟨k, hk, rfl⟩
    exact (USub σ W v).mul_mem ((USub σ W v).mul_mem hg (hKPU hk)) ((USub σ W v).inv_mem hg)
  have tr : ∀ g ∈ USub σ W v, (KP.map (MulAut.conj g).toMonoidHom).relIndex KP =
      ((KPW (w.adicCompletion E) c m).map (MulAut.conj (Φ g)).toMonoidHom).relIndex (KPW (w.adicCompletion E) c m) :=
    fun g hg => by
      rw [← relIndex_transport (USub σ W v) Φ hinj (hconj g hg) hKPU, map_conj_map, himg]
  have hPW : Φ p ∈ PW (w.adicCompletion E) c m := (hP p hpU).1 hp
  have key := hL (w.adicCompletion E) ϖ c (Formalism.UG.qV F v) hU m (Φ p) hPW
  rw [← map_inv, ← tr p⁻¹ ((USub σ W v).inv_mem hpU), ← tr p hpU, hdet p hp t ht] at key
  rw [key]
  congr 1
  have h21 : (Φ p : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (w.adicCompletion E)).toBlocks₂₁ = 0 :=
    GlobalTheory.LGrp.mem_blockQ_two.1 hPW.2
  have hdetΦ : (Φ p : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (w.adicCompletion E)).det =
      (Φ p : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (w.adicCompletion E)).toBlocks₁₁.det *
        (Φ p : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (w.adicCompletion E)).toBlocks₂₂.det := by
    conv_lhs => rw [← Matrix.fromBlocks_toBlocks (Φ p : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (w.adicCompletion E)), h21]
    exact Matrix.det_fromBlocks_zero₂₁ _ _ _
  have hne : piE h t.det ≠ 0 := by
    rw [← hdet p hp t ht]
    intro h0
    have hu' := (Matrix.isUnit_iff_isUnit_det _).1 (Φ p).isUnit
    rw [hdetΦ, h0, zero_mul] at hu'
    exact not_isUnit_zero hu'
  let x : (Fv F v ⊗[F] E)ˣ := Units.map (complEquiv hw h).symm.toMonoidHom (Units.mk0 _ hne)
  have hx1 : x.1 = (t.map (compFin F E v)).det := by
    change (complEquiv hw h).symm ((complEquiv hw h) (compFin F E v t.det)) = _
    rw [RingEquiv.symm_apply_apply]
    exact RingHom.map_det _ _
  have habs := GlobalTheory.AbsInert.absEv_inert F E σ hσ v w h hw x
  have hm : (((sbClass (Fv F v)).modu u : NNReal) : ℝ) = (absEv F E v x : ℝ) := by
    have e1 := GlobalTheory.CompanionTheory.SW.ProdFormula.distribHaarChar_eq_nnnorm v (u : Fv F v) u.ne_zero
    rw [Units.mk0_val] at e1
    change ((distribHaarChar (Fv F v) u : NNReal) : ℝ) = _
    rw [e1, absEv_apply, hx1, ← hu]
  have hx : piE h t.det = toCompl h x.1 := by
    rw [hx1]
    change toCompl h (compFin F E v t.det) = toCompl h (t.map (compFin F E v)).det
    rw [RingHom.map_det]
    rfl
  rw [hm, habs, hx, ← zpow_natCast, ← zpow_mul]
  congr 1
  ring

end PositivityTheory.Sph.M2

end
