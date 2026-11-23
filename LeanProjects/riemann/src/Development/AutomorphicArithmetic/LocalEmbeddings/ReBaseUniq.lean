import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealmapsIsomorphism
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedFiniteMapsRestriction

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.ReBase

section Real

open scoped Matrix
open GlobalTheory.RealActs GlobalTheory.ThK.RealUniq

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {B : Base F E}

theorem howe_sup_pr (hKP : GlobalTheory.FunPr.Hypotheses₂) {n d r s r' s' : ℕ} {Y : Spc F E n} {W : Spc F E d} {M : Model σ Y W} {χY χW : Chr F E}
    {o : Rep σ Y W} (h : IsPair B M χY χW o r s r' s') :
    ∀ N N', GlobalTheory.Published.ThetaSubInf M B.ψ B.emb o N → GlobalTheory.Published.ThetaSubInf M B.ψ B.emb o N' → N ≠ M.Pol B.ψ B.emb →
      N' ≠ M.Pol B.ψ B.emb → N ⊔ N' ≠ M.Pol B.ψ B.emb := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hY : Y.J.det ≠ 0 := fun h0 => det_ne_zero_of_sig (h.herm.sig w) (by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero])
  have hW : W.J.det ≠ 0 := fun h0 => det_ne_zero_of_sig (h.skew.sig w) (by
    rw [Matrix.det_smul, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero, mul_zero])
  exact (hKP.howeDualityReal F E σ h.base.cm n d Y W M B.ψ χY χW o h.base.std h.herm.herm hY h.skew.skew hW h.resX h.resW
    h.hX h.hW h.weil B.emb h.herm.cartan h.skew.cartan).2

theorem realMaps_unique : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a a') (Rf : FinMaps F a a'), IsMatched B G X om om' R Rf →
    ∀ R₃ : RealMaps F a a', IsRealMaps B G om om' R₃ → ∃ (ψ : R.Pi ≃ₗ[ℂ] R₃.Pi) (l : ℂ), l ≠ 0 ∧
      (∀ f ∈ G.M.Pol B.ψ B.emb, R₃.p f = ψ (R.p f)) ∧ ∀ f ∈ G.M'.Pol B.ψ B.emb, R₃.p' f = l • ψ (R.p' f) := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' R Rf hM R₃ hR₃
  have hR := hM.real
  have hPV := isPair_V hM.triple
  have hPV' := isPair_V' hM.triple
  have actV := GlobalTheory.T.polynomial_datum_action_of_pair hKP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hPV
  have actV' := GlobalTheory.T.polynomial_datum_action_of_pair hKP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hPV'
  have ks_p : ∀ R' : RealMaps F a a', IsRealMaps B G om om' R' → KerStab B G.M om R'.p := fun R' h =>
    ⟨fun γ hγ f hf f₁ h1 h0 => by
      have := h.lie γ hγ f hf 0 (zero_mem _) f₁ 0 h1 (actsD_zero _) (by rw [h0, map_zero])
      rwa [map_zero] at this,
     fun k hk f hf f₁ h1 h0 => by
      have := h.cpt k hk f hf 0 (zero_mem _) f₁ 0 h1 (acts_zero _) (by rw [h0, map_zero])
      rwa [map_zero] at this⟩
  have ks_p' : ∀ R' : RealMaps F a a', IsRealMaps B G om om' R' → KerStab B G.M' om' R'.p' := fun R' h =>
    ⟨fun γ hγ f hf f₁ h1 h0 => by
      have := h.lie γ hγ 0 (zero_mem _) f hf 0 f₁ (actsD_zero _) h1 (by rw [h0, map_zero])
      rw [map_zero] at this; exact this.symm,
     fun k hk f hf f₁ h1 h0 => by
      have := h.cpt k hk 0 (zero_mem _) f hf 0 f₁ (acts_zero _) h1 (by rw [h0, map_zero])
      rw [map_zero] at this; exact this.symm⟩
  have onto' : ∀ R' : RealMaps F a a', IsRealMaps B G om om' R' → ∀ y, ∃ f' ∈ G.M'.Pol B.ψ B.emb, R'.p' f' = y :=
    fun R' h y => by
      have : y ∈ (G.M'.Pol B.ψ B.emb).map R'.p' := h.quot'.onto ▸ Submodule.mem_top
      exact Submodule.mem_map.1 this
  have onto : ∀ R' : RealMaps F a a', IsRealMaps B G om om' R' → ∀ y, ∃ f ∈ G.M.Pol B.ψ B.emb, R'.p f = y :=
    fun R' h y => by
      have : y ∈ (G.M.Pol B.ψ B.emb).map R'.p := h.quot.onto ▸ Submodule.mem_top
      exact Submodule.mem_map.1 this
  have irr_p' : ∀ R' : RealMaps F a a', IsRealMaps B G om om' R' → Irred B G.M' om' R'.p' := fun R' h N h1 h2 => by
    apply h.irred N
    · intro γ hγ f hf f₁ hf₁ hN
      obtain ⟨f', hf', e⟩ := onto' R' h (R'.p f)
      obtain ⟨D, -, hDi⟩ := actV'.2.2.1 γ hγ
      have h1' := (hDi f' hf' (D f')).2 rfl
      rw [h.lie γ hγ f hf f' hf' f₁ (D f') hf₁ h1' e.symm]
      exact h1 γ hγ f' hf' (D f') h1' (e ▸ hN)
    · intro k hk f hf f₁ hf₁ hN
      obtain ⟨f', hf', e⟩ := onto' R' h (R'.p f)
      obtain ⟨D, -, hDi⟩ := actV'.2.2.2 k hk
      have h1' := (hDi f' hf' (D f')).2 rfl
      rw [h.cpt k hk f hf f' hf' f₁ (D f') hf₁ h1' e.symm]
      exact h2 k hk f' hf' (D f') h1' (e ▸ hN)
  obtain ⟨ψ, hψ⟩ := GlobalTheory.T.exists_equiv_howeDuality_realPlaces F E σ B _ _ _ _ G.M om _ _ R.p R₃.p actV (howe_sup_pr hKP hPV) hR.quot hR₃.quot hR.nontriv
    hR₃.nontriv (ks_p R hR) (ks_p R₃ hR₃) hR.irred hR₃.irred
  obtain ⟨ψ₁, hψ₁⟩ := GlobalTheory.T.exists_equiv_howeDuality_realPlaces F E σ B _ _ _ _ G.M' om' _ _ R.p' R₃.p' actV' (howe_sup_pr hKP hPV') hR.quot' hR₃.quot'
    hR.nontriv hR₃.nontriv (ks_p' R hR) (ks_p' R₃ hR₃) (irr_p' R hR) (irr_p' R₃ hR₃)
  choose DL hDLm hDLi using actV.2.2.1
  choose DK hDKm hDKi using actV.2.2.2
  choose DL' hDLm' hDLi' using actV'.2.2.1
  choose DK' hDKm' hDKi' using actV'.2.2.2
  let ι : Type := {γ // γ ∈ Lines σ G.W} ⊕ {k // k ∈ KInf σ G.W B.emb}
  let D : ι → SInf F (Fin a × Fin (a + a')) →ₗ[ℂ] SInf F (Fin a × Fin (a + a')) :=
    Sum.elim (fun γ => DL γ.1 γ.2) (fun k => DK k.1 k.2)
  let D' : ι → SInf F (Fin a' × Fin (a + a')) →ₗ[ℂ] SInf F (Fin a' × Fin (a + a')) :=
    Sum.elim (fun γ => DL' γ.1 γ.2) (fun k => DK' k.1 k.2)
  have Dm : ∀ i, ∀ f ∈ G.M.Pol B.ψ B.emb, D i f ∈ G.M.Pol B.ψ B.emb := by
    rintro (γ | k) f hf
    exacts [hDLm _ _ f hf, hDKm _ _ f hf]
  have Dm' : ∀ i, ∀ f ∈ G.M'.Pol B.ψ B.emb, D' i f ∈ G.M'.Pol B.ψ B.emb := by
    rintro (γ | k) f hf
    exacts [hDLm' _ _ f hf, hDKm' _ _ f hf]
  have joint : ∀ R' : RealMaps F a a', IsRealMaps B G om om' R' → ∀ i, ∀ f ∈ G.M.Pol B.ψ B.emb,
      ∀ f' ∈ G.M'.Pol B.ψ B.emb, R'.p f = R'.p' f' → R'.p (D i f) = R'.p' (D' i f') := by
    rintro R' h (γ | k) f hf f' hf' e
    · exact h.lie γ.1 γ.2 f hf f' hf' _ _ ((hDLi _ _ f hf _).2 rfl) ((hDLi' _ _ f' hf' _).2 rfl) e
    · exact h.cpt k.1 k.2 f hf f' hf' _ _ ((hDKi _ _ f hf _).2 rfl) ((hDKi' _ _ f' hf' _).2 rfl) e
  have ker0 : ∀ i, ∀ f ∈ G.M.Pol B.ψ B.emb, R.p f = 0 → R.p (D i f) = 0 := by
    rintro (γ | k) f hf h0
    · exact (ks_p R hR).1 γ.1 γ.2 f hf _ ((hDLi _ _ f hf _).2 rfl) h0
    · exact (ks_p R hR).2 k.1 k.2 f hf _ ((hDKi _ _ f hf _).2 rfl) h0
  let π : G.M.Pol B.ψ B.emb →ₗ[ℂ] R.Pi := R.p ∘ₗ (G.M.Pol B.ψ B.emb).subtype
  have hπ : Function.Surjective π := fun y => by
    obtain ⟨f, hf, e⟩ := onto R hR y
    exact ⟨⟨f, hf⟩, e⟩
  let ρ : ι → Module.End ℂ R.Pi := fun i =>
    induced π hπ ((D i).restrict (Dm i)) (fun u hu => ker0 i u.1 u.2 hu)
  have hρ : ∀ i, ∀ f (hf : f ∈ G.M.Pol B.ψ B.emb), ρ i (R.p f) = R.p (D i f) := fun i f hf =>
    induced_apply π hπ _ _ ⟨f, hf⟩
  have irrρ : ∀ N : Submodule ℂ R.Pi, (∀ i, ∀ x ∈ N, ρ i x ∈ N) → N = ⊥ ∨ N = ⊤ := fun N hN => by
    apply hR.irred N
    · intro γ hγ f hf f₁ h1 hx
      rw [(hDLi γ hγ f hf f₁).1 h1]
      have := hN (Sum.inl ⟨γ, hγ⟩) _ hx
      rwa [hρ _ f hf] at this
    · intro k hk f hf f₁ h1 hx
      rw [(hDKi k hk f hf f₁).1 h1]
      have := hN (Sum.inr ⟨k, hk⟩) _ hx
      rwa [hρ _ f hf] at this
  let T : Module.End ℂ R.Pi := ψ.symm.toLinearMap ∘ₗ ψ₁.toLinearMap
  have comm : ∀ i, T * ρ i = ρ i * T := fun i => by
    refine LinearMap.ext fun x => ?_
    obtain ⟨f', hf', rfl⟩ := onto' R hR x
    obtain ⟨f, hf, e⟩ := onto R hR (R.p' f')
    obtain ⟨g, hg, eg⟩ := onto R₃ hR₃ (R₃.p' f')
    have j1 := joint R hR i f hf f' hf' e
    have j3 := joint R₃ hR₃ i g hg f' hf' eg
    have lhs : T (ρ i (R.p' f')) = R.p (D i g) := by
      calc T (ρ i (R.p' f')) = ψ.symm (ψ₁ (R.p' (D' i f'))) := by rw [← e, hρ i f hf, j1]; rfl
      _ = ψ.symm (R₃.p' (D' i f')) := by rw [← hψ₁ _ (Dm' i f' hf')]
      _ = R.p (D i g) := by rw [← j3, hψ _ (Dm i g hg), LinearEquiv.symm_apply_apply]
    have rhs : ρ i (T (R.p' f')) = R.p (D i g) := by
      calc ρ i (T (R.p' f')) = ρ i (ψ.symm (R₃.p' f')) := by
            show ρ i (ψ.symm (ψ₁ (R.p' f'))) = _
            rw [← hψ₁ f' hf']
      _ = ρ i (R.p g) := by rw [← eg, hψ g hg, LinearEquiv.symm_apply_apply]
      _ = R.p (D i g) := hρ i g hg
    rw [Module.End.mul_apply, Module.End.mul_apply, lhs, rhs]
  have hrank : Module.rank ℂ R.Pi ≤ Cardinal.aleph0 :=
    (LinearMap.rank_le_of_surjective π hπ).trans (GlobalTheory.T.polynomial_data_countable_rank hKP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hPV)
  obtain ⟨c, hc⟩ := GlobalTheory.T.eq_smul_one_of_commute_irreducible_of_countable_rank R.Pi ι ρ T hR.nontriv hrank irrρ comm
  have hT : ∀ x, T x = c • x := fun x => by rw [hc]; rfl
  refine ⟨ψ, c, ?_, hψ, fun f hf => ?_⟩
  · rintro rfl
    haveI := hR.nontriv
    obtain ⟨x, hx⟩ := exists_ne (0 : R.Pi)
    have h0 : ψ.symm (ψ₁ x) = 0 := by rw [← zero_smul ℂ x, ← hT x]; rfl
    exact hx (ψ₁.injective (ψ.symm.injective (h0.trans (map_zero _).symm) |>.trans (map_zero _).symm))
  · rw [hψ₁ f hf]
    calc ψ₁ (R.p' f) = ψ (T (R.p' f)) := by
          show _ = ψ (ψ.symm (ψ₁ (R.p' f)))
          rw [LinearEquiv.apply_symm_apply]
    _ = c • ψ (R.p' f) := by rw [hT, map_smul]

end Real

section Fin

open GlobalTheory.FinUniq

theorem finMaps_unique : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a a') (Rf : FinMaps F a a'), IsMatched B G X om om' R Rf →
    ∀ (V : Spc F E a) (V' : Spc F E a') (W : Spc F E (a + a')) (Rf₃ : FinMaps F a a'), IsFinMaps B (reG G V V' W) X om om' Rf₃ →
    ∀ v : Pl F, ∃ (ψ : Rf.Pi v ≃ₗ[ℂ] Rf₃.Pi v) (l : ℂ), l ≠ 0 ∧ (∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), Rf₃.p v φ = ψ (Rf.p v φ)) ∧
      (∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), Rf₃.p' v φ = l • ψ (Rf.p' v φ)) ∧ (v ∉ X.T → l = 1) := by
  intro hK F E _ _ _ _ _ σ B a a' G X om om' R Rf hM V V' W Rf₃ h₃ v
  have hT := hM.triple
  have hf := hM.fin
  have hP := GlobalTheory.ThK.Inhab.pairV hT
  have hP' := GlobalTheory.ThK.Inhab.pairV' hT
  have hAE := GlobalTheory.ThK.LocalOps.actsEx hK
  have h1V : (1 : UA σ G.V.J) ∈ UAt σ G.V (evFin F v) := fun u _ => by
    show u • ((1 : UA σ G.V.J).1.1 - 1) = 0
    rw [show (1 : UA σ G.V.J).1.1 = 1 from rfl, sub_self, smul_zero]
  have h1V' : (1 : UA σ G.V'.J) ∈ UAt σ G.V' (evFin F v) := fun u _ => by
    show u • ((1 : UA σ G.V'.J).1.1 - 1) = 0
    rw [show (1 : UA σ G.V'.J).1.1 = 1 from rfl, sub_self, smul_zero]
  have exV : ∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      ∃ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (1, h)) φ φ₁ := fun h hh φ hφ => by
    obtain ⟨φ₁, ⟨h1, h2⟩, -⟩ := (hAE F E σ B _ _ _ _ _ _ _ om _ _ _ _ hP v).1 1 h1V h hh φ hφ
    exact ⟨φ₁, h1, h2⟩
  have exV' : ∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
      ∃ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v), Acts (evFin F v) (om' (1, h)) φ φ₁ := fun h hh φ hφ => by
    obtain ⟨φ₁, ⟨h1, h2⟩, -⟩ := (hAE F E σ B _ _ _ _ _ _ _ om' _ _ _ _ hP' v).1 1 h1V' h hh φ hφ
    exact ⟨φ₁, h1, h2⟩

  have props : ∀ Q : FinMaps F a a',
      (SB (Fin a' × Fin (a + a') → Fv F v)).map (Q.p' v) = ⊤ →
      (∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ' ∈ SB (Fin a' × Fin (a + a') → Fv F v),
        ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁' ∈ SB (Fin a' × Fin (a + a') → Fv F v),
        Acts (evFin F v) (om (1, h)) φ φ₁ → Acts (evFin F v) (om' (1, h)) φ' φ₁' → Q.p v φ = Q.p' v φ' →
          Q.p v φ₁ = Q.p' v φ₁') →
      (∀ N : Submodule ℂ (Q.Pi v), (∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
        Acts (evFin F v) (om (1, h)) φ φ₁ → Q.p v φ ∈ N → Q.p v φ₁ ∈ N) → N = ⊥ ∨ N = ⊤) →
      (∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
        Acts (evFin F v) (om (1, h)) φ φ₁ → Q.p v φ = 0 → Q.p v φ₁ = 0) ∧
      (∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
        Acts (evFin F v) (om' (1, h)) φ φ₁ → Q.p' v φ = 0 → Q.p' v φ₁ = 0) ∧
      (∀ N : Submodule ℂ (Q.Pi v), (∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
        Acts (evFin F v) (om' (1, h)) φ φ₁ → Q.p' v φ ∈ N → Q.p' v φ₁ ∈ N) → N = ⊥ ∨ N = ⊤) := by
    intro Q onto' eqv irr
    refine ⟨fun h hh φ hφ φ₁ hφ₁ hact e => ?_, fun h hh φ hφ φ₁ hφ₁ hact e => ?_, fun N hN => irr N ?_⟩
    · rw [eqv h hh φ hφ 0 (zero_mem _) φ₁ hφ₁ 0 (zero_mem _) hact (acts_zero_zero v _) (by rw [e, map_zero]), map_zero]
    · rw [← eqv h hh 0 (zero_mem _) φ hφ 0 (zero_mem _) φ₁ hφ₁ (acts_zero_zero v _) hact (by rw [e, map_zero]), map_zero]
    · intro h hh φ hφ φ₁ hφ₁ hact hmem
      obtain ⟨φ', hφ', e⟩ : ∃ φ' ∈ SB (Fin a' × Fin (a + a') → Fv F v), Q.p' v φ' = Q.p v φ := by
        have : Q.p v φ ∈ (SB (Fin a' × Fin (a + a') → Fv F v)).map (Q.p' v) := by rw [onto']; trivial
        exact this
      obtain ⟨φ₁', hφ₁', hact'⟩ := exV' h hh φ' hφ'
      rw [eqv h hh φ hφ φ' hφ' φ₁ hφ₁ φ₁' hφ₁' hact hact' e.symm]
      exact hN h hh φ' hφ' φ₁' hφ₁' hact' (e ▸ hmem)
  obtain ⟨sV, sV', iV'⟩ := props Rf (hf.onto' v) (hf.equiv v) (hf.irred v)
  obtain ⟨tV, tV', jV'⟩ := props Rf₃ (h₃.onto' v) (h₃.equiv v) (h₃.irred v)
  haveI := hf.nontriv v
  haveI := h₃.nontriv v
  have mV := ker_maximal om v (Rf.p v) (hf.onto v) (hf.inv v) sV (hf.irred v)
  have mV₃ := ker_maximal (Y := G.V) (Z := G.W) om v (Rf₃.p v) (h₃.onto v) (h₃.inv v) tV (h₃.irred v)
  have mV' := ker_maximal om' v (Rf.p' v) (hf.onto' v) (hf.inv' v) sV' iV'
  have mV₃' := ker_maximal (Y := G.V') (Z := G.W) om' v (Rf₃.p' v) (h₃.onto' v) (h₃.inv' v) tV' jV'
  have howe := GlobalTheory.T.weil_representation_cm_extension hK hK.howeDualityUnitary hK.minguezThetaGL F E σ hT.base.cm
  have eV := howe a (a + a') G.V G.W G.M B.ψ X.β (X.β / X.α) om hT.base.std hP.herm.herm (det_ne_zero_herm hP.herm)
    hP.skew.skew (det_ne_zero_skew hP.skew) hP.resX hP.resW hP.hX hP.hW hP.weil v _ _ mV mV₃
  have eV' := howe a' (a + a') G.V' G.W G.M' B.ψ X.α (X.α / X.β) om' hT.base.std hP'.herm.herm (det_ne_zero_herm hP'.herm)
    hP'.skew.skew (det_ne_zero_skew hP'.skew) hP'.resX hP'.resW hP'.hX hP'.hW hP'.weil v _ _ mV' mV₃'
  obtain ⟨ψ, hψ⟩ := equiv_of_ker_eq' (Rf.p v) (Rf₃.p v) (hf.onto v) (h₃.onto v) eV
  obtain ⟨ψ', hψ'⟩ := equiv_of_ker_eq' (Rf.p' v) (Rf₃.p' v) (hf.onto' v) (h₃.onto' v) eV'
  set T : Module.End ℂ (Rf.Pi v) := ψ.symm.toLinearMap ∘ₗ ψ'.toLinearMap with hTdef
  have hTapp : ∀ x, T x = ψ.symm (ψ' x) := fun x => rfl
  have comm : ∀ h ∈ UAt σ G.W (evFin F v), ∀ χ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ χ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      Acts (evFin F v) (om (1, h)) χ χ₁ → ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      Acts (evFin F v) (om (1, h)) φ φ₁ → Rf.p v φ = T (Rf.p v χ) → Rf.p v φ₁ = T (Rf.p v χ₁) := by
    intro h hh χ hχ χ₁ hχ₁ hc φ hφ φ₁ hφ₁ ha e
    obtain ⟨χ', hχ', e1⟩ : ∃ χ' ∈ SB (Fin a' × Fin (a + a') → Fv F v), Rf.p' v χ' = Rf.p v χ := by
      have : Rf.p v χ ∈ (SB (Fin a' × Fin (a + a') → Fv F v)).map (Rf.p' v) := by rw [hf.onto' v]; trivial
      exact this
    obtain ⟨χ₁', hχ₁', hc'⟩ := exV' h hh χ' hχ'
    have e2 : Rf.p v χ₁ = Rf.p' v χ₁' := hf.equiv v h hh χ hχ χ' hχ' χ₁ hχ₁ χ₁' hχ₁' hc hc' e1.symm
    have e3 : Rf₃.p v φ = Rf₃.p' v χ' := by
      rw [hψ φ hφ, e, hTapp, ← e1, LinearEquiv.apply_symm_apply, ← hψ' χ' hχ']
    have e4 : Rf₃.p v φ₁ = Rf₃.p' v χ₁' := h₃.equiv v h hh φ hφ χ' hχ' φ₁ hφ₁ χ₁' hχ₁' ha hc' e3
    rw [hTapp, e2, ← hψ' χ₁' hχ₁', ← e4, hψ φ₁ hφ₁, LinearEquiv.symm_apply_apply]
  have hrank : Module.rank ℂ (Rf.Pi v) ≤ Cardinal.aleph0 := by
    haveI := sc_Fv v
    have sp : Function.Surjective ((Rf.p v).comp (SB (Fin a × Fin (a + a') → Fv F v)).subtype) := fun y => by
      have : y ∈ (SB (Fin a × Fin (a + a') → Fv F v)).map (Rf.p v) := by rw [hf.onto v]; trivial
      obtain ⟨x, hx, rfl⟩ := this
      exact ⟨⟨x, hx⟩, rfl⟩
    exact (LinearMap.rank_le_of_surjective _ sp).trans (rank_SB_le _)
  have hker : ∀ c : ℂ, ∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      Acts (evFin F v) (om (1, h)) φ φ₁ → Rf.p v φ ∈ LinearMap.ker (T - c • 1) →
        Rf.p v φ₁ ∈ LinearMap.ker (T - c • 1) := by
    intro c h hh φ hφ φ₁ hφ₁ hact hmem
    rw [LinearMap.mem_ker] at hmem ⊢
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero] at hmem ⊢
    have hsc := GlobalTheory.ThK.LocalOps.acts_lin v (om (1, h)) (exV h hh) hφ hφ hact hact c 0
    rw [zero_smul, zero_smul, add_zero, add_zero] at hsc
    have e : Rf.p v (c • φ) = T (Rf.p v φ) := by rw [map_smul, hmem]
    have := comm h hh φ hφ φ₁ hφ₁ hact (c • φ) ((SB (Fin a × Fin (a + a') → Fv F v)).smul_mem c hφ) (c • φ₁)
      ((SB (Fin a × Fin (a + a') → Fv F v)).smul_mem c hφ₁) hsc e
    rw [← this, map_smul]
  have hran : ∀ c : ℂ, ∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      Acts (evFin F v) (om (1, h)) φ φ₁ → Rf.p v φ ∈ LinearMap.range (T - c • 1) →
        Rf.p v φ₁ ∈ LinearMap.range (T - c • 1) := by
    intro c h hh φ hφ φ₁ hφ₁ hact hmem
    obtain ⟨y, hy⟩ := hmem
    obtain ⟨χ, hχ, rfl⟩ : ∃ χ ∈ SB (Fin a × Fin (a + a') → Fv F v), Rf.p v χ = y := by
      have : y ∈ (SB (Fin a × Fin (a + a') → Fv F v)).map (Rf.p v) := by rw [hf.onto v]; trivial
      exact this
    obtain ⟨χ₁, hχ₁, hc⟩ := exV h hh χ hχ
    have hsum := GlobalTheory.ThK.LocalOps.acts_lin v (om (1, h)) (exV h hh) hφ hχ hact hc 1 c
    rw [one_smul, one_smul] at hsum
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply] at hy
    have e : Rf.p v (φ + c • χ) = T (Rf.p v χ) := by
      rw [map_add, map_smul, ← hy]; abel
    have := comm h hh χ hχ χ₁ hχ₁ hc (φ + c • χ) (add_mem hφ ((SB (Fin a × Fin (a + a') → Fv F v)).smul_mem c hχ)) (φ₁ + c • χ₁)
      (add_mem hφ₁ ((SB (Fin a × Fin (a + a') → Fv F v)).smul_mem c hχ₁)) hsum e
    refine ⟨Rf.p v χ₁, ?_⟩
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
    rw [← this, map_add, map_smul]; abel
  obtain ⟨l, hl⟩ := scalar_of_irred (fun N => ∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (1, h)) φ φ₁ → Rf.p v φ ∈ N → Rf.p v φ₁ ∈ N)
    hrank (hf.irred v) T hker hran
  have hTl : ∀ x, ψ' x = l • ψ x := fun x => by
    have := congrArg (fun f : Module.End ℂ (Rf.Pi v) => f x) hl
    simp only [hTapp, LinearMap.smul_apply, Module.End.one_apply] at this
    rw [← map_smul, ← this, LinearEquiv.apply_symm_apply]
  have hl0 : l ≠ 0 := by
    rintro rfl
    obtain ⟨x, hx⟩ := exists_ne (0 : Rf.Pi v)
    have := hTl x
    rw [zero_smul, LinearEquiv.map_eq_zero_iff] at this
    exact hx this
  refine ⟨ψ, l, hl0, hψ, fun φ hφ => by rw [hψ' φ hφ, hTl], fun hv => ?_⟩
  obtain ⟨s1, s2⟩ := hf.sph v hv
  obtain ⟨s3, -⟩ := h₃.sph v hv
  have hvac := (hT.geo.hM.vac v).1
  have hvac' := (hT.geo.hM'.vac v).1
  change Rf₃.p v (G.M.vac v) = Rf₃.p' v (G.M'.vac v) at s3
  have e1 : Rf₃.p' v (G.M'.vac v) = l • Rf₃.p v (G.M.vac v) := by
    rw [hψ' _ hvac', hTl, ← s1, ← hψ _ hvac]
  have hne : Rf₃.p v (G.M.vac v) ≠ 0 := by
    rw [hψ _ hvac]; exact (LinearEquiv.map_ne_zero_iff ψ).2 s2
  rw [← s3] at e1
  have : (l - 1) • Rf₃.p v (G.M.vac v) = 0 := by rw [sub_smul, one_smul, ← e1, sub_self]
  rcases smul_eq_zero.1 this with h | h
  · exact sub_eq_zero.1 h
  · exact absurd h hne

end Fin

end GlobalTheory.ReBase

end
