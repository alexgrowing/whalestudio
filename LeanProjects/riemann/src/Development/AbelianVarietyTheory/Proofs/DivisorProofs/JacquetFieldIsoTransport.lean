import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMidJacAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRankSB
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSplitChartSplitChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSubquotientTransport
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThK.MidJac GlobalTheory.CuspBlock

noncomputable section

namespace GlobalTheory.MidJacTransport

open GlobalTheory.FieldTransportInd GlobalTheory.ThK.DetProd

section Gen

variable {G G' W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G'] [AddCommGroup W] [Module ℂ W]

theorem exists_transport_symm_surjective (Φ : G ≃* G') (hΦ : Continuous Φ) (hΦs : Continuous Φ.symm)
    {H : Subgroup G} {H' : Subgroup G'} (hH : ∀ g, Φ g ∈ H' ↔ g ∈ H) {σ : Representation ℂ H W}
    {σ' : Representation ℂ H' W} (hσ : ∀ h : H, σ' ⟨Φ h, (hH h).2 h.2⟩ = σ h) :
    ∃ S : (smInd H' σ').IntertwiningMap ((smInd H σ).comp Φ.symm.toMonoidHom), Function.Surjective S := by
  have hH' : ∀ g', Φ.symm g' ∈ H ↔ g' ∈ H' := fun g' => by
    rw [← hH, MulEquiv.apply_symm_apply]
  have hσ' : ∀ h' : H', σ ⟨Φ.symm h', (hH' h').2 h'.2⟩ = σ' h' := by
    intro h'
    rw [← hσ]
    congr 1
    exact Subtype.ext (MulEquiv.apply_symm_apply _ _)
  refine ⟨transport Φ.symm (by simpa using hΦ) hH' hσ', fun f => ⟨transportFun Φ hΦs hH hσ f, ?_⟩⟩
  refine Subtype.ext (Subtype.ext (funext fun y => ?_))
  show f.1.1 (Φ.symm (Φ.symm.symm y)) = f.1.1 y
  simp

end Gen

variable {K L : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]

theorem continuous_glEquiv (ψ : K ≃+* L) (hψ : Continuous ψ) {N : ℕ} :
    Continuous (GlobalTheory.LFun.SplitTie.glEquiv N ψ) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · show Continuous fun g : GL (Fin N) K => (g : Matrix (Fin N) (Fin N) K).map ψ
    exact Units.continuous_val.matrix_map hψ
  · show Continuous fun g : GL (Fin N) K => ((g⁻¹ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K).map ψ
    exact Units.continuous_coe_inv.matrix_map hψ

variable {α : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
  [∀ a, DecidableEq (m a)] {N : ℕ}

theorem glEquiv_mem_unipRad (ψ : K ≃+* L) (e : (Σ a, m a) ≃ Fin N) (g : GL (Fin N) K) :
    GlobalTheory.LFun.SplitTie.glEquiv N ψ g ∈ unipRad L e ↔ g ∈ unipRad K e := by
  rw [mem_unipRad, mem_unipRad, glEquiv_mem_parab]
  refine and_congr_right fun _ => forall_congr' fun a => forall₂_congr fun i j => ?_
  show ψ ((g : Matrix (Fin N) (Fin N) K) _ _) = _ ↔ _
  by_cases hij : i = j
  · subst hij
    simp only [Matrix.one_apply_eq]
    exact map_eq_one_iff ψ ψ.injective
  · simp only [Matrix.one_apply_ne hij]
    exact map_eq_zero_iff ψ ψ.injective

theorem glEquiv_leviEmb (ψ : K ≃+* L) (e : (Σ a, m a) ≃ Fin N) (g : Levi K m) :
    GlobalTheory.LFun.SplitTie.glEquiv N ψ (leviEmb K e g) = leviEmb L e (levMap ψ g) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  obtain ⟨⟨a, x⟩, rfl⟩ := e.surjective i
  obtain ⟨⟨b, y⟩, rfl⟩ := e.surjective j
  show ψ ((leviEmb K e g : Matrix (Fin N) (Fin N) K) _ _) = _
  by_cases hab : a = b
  · subst hab
    rw [leviEmb_apply_same, leviEmb_apply_same, levMap_apply]
    rfl
  · rw [leviEmb_apply_ne K e g hab, leviEmb_apply_ne L e _ hab, map_zero]

theorem levMap_midHom (ψ : K ≃+* L) (l n N : ℕ) (g : GL (Fin n) K) :
    levMap ψ (midHom K l n N g) = midHom L l n N (GlobalTheory.LFun.SplitTie.glEquiv n ψ g) := by
  funext j
  rw [levMap_apply]
  by_cases hj : j = 1
  · subst hj
    simp only [midHom, MonoidHom.mulSingle_apply, Pi.mulSingle_eq_same]
    rfl
  · show glMap ψ _ (Pi.mulSingle (M := fun j : Fin 3 => GL (Fin (tripSizes l n N j)) K) 1 g j) =
      Pi.mulSingle (M := fun j : Fin 3 => GL (Fin (tripSizes l n N j)) L) 1 (GlobalTheory.LFun.SplitTie.glEquiv n ψ g) j
    erw [Pi.mulSingle_eq_of_ne hj, Pi.mulSingle_eq_of_ne hj, map_one]

theorem isSubquotient_midJacU_transport : ∀ (k k' : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] (e : k ≃+* k'),
    Continuous e → Continuous e.symm → ∀ (a a' l n : ℕ) (h : l + n ≤ a + a') (α₀ β₀ : kˣ →* ℂˣ) (α β : k'ˣ →* ℂˣ),
    (∀ y, α₀ y = α (Units.map e.toRingHom.toMonoidHom y)) → (∀ y, β₀ y = β (Units.map e.toRingHom.toMonoidHom y)) →
    ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (Q : Representation ℂ (GL (Fin n) k) W),
      IsSubquotient Q ((jacU (tripPlace h) (detInd a a' α₀ β₀)).comp (midHom k l n (a + a'))) →
      IsSubquotient (Q.comp (GlobalTheory.LFun.SplitTie.glEquiv n e).symm.toMonoidHom)
        ((jacU (tripPlace h) (detInd a a' α β)).comp (midHom k' l n (a + a'))) := by
  intro k k' _ _ _ _ _ _ _ _ e he hes a a' l n h α₀ β₀ α β hα hβ W _ _ Q hQ
  have hρ : ∀ g, ofChar (twoDet a a' α β) (levMap e g) = ofChar (twoDet a a' α₀ β₀) g := by
    intro g
    have h2 : twoDet a a' α β (levMap e g) = twoDet a a' α₀ β₀ g := by
      show α (Matrix.GeneralLinearGroup.det (levMap e g 0)) * β (Matrix.GeneralLinearGroup.det (levMap e g 1)) =
        α₀ (Matrix.GeneralLinearGroup.det (g 0)) * β₀ (Matrix.GeneralLinearGroup.det (g 1))
      rw [levMap_apply, levMap_apply, det_glMap, det_glMap, hα, hβ]
    exact LinearMap.ext fun x => by simp [ofChar_apply, h2]
  have hσ : ∀ p : parab k (e2 a a'),
      ((twist (ofChar (twoDet a a' α β)) (deltaHalf k' _)).comp (leviProj k' (e2 a a')))
        ⟨GlobalTheory.LFun.SplitTie.glEquiv (a + a') e p, (glEquiv_mem_parab e (e2 a a') p).2 p.2⟩ =
      ((twist (ofChar (twoDet a a' α₀ β₀)) (deltaHalf k _)).comp (leviProj k (e2 a a'))) p := by
    intro p
    refine LinearMap.ext fun w => ?_
    show (deltaHalf k' _ (leviProj k' (e2 a a') _) : ℂ) • ofChar (twoDet a a' α β) (leviProj k' (e2 a a') _) w =
      (deltaHalf k _ (leviProj k (e2 a a') p) : ℂ) • ofChar (twoDet a a' α₀ β₀) (leviProj k (e2 a a') p) w
    rw [leviProj_glEquiv, deltaHalf_levMap e he, hρ]
  obtain ⟨S, hS⟩ : ∃ S : (detInd a a' α β).IntertwiningMap
      ((detInd a a' α₀ β₀).comp (GlobalTheory.LFun.SplitTie.glEquiv (a + a') e).symm.toMonoidHom), Function.Surjective S :=
    exists_transport_symm_surjective _ (continuous_glEquiv e he) (continuous_glEquiv_symm e he)
      (glEquiv_mem_parab e (e2 a a')) hσ
  have hSi : ∀ g v, S (detInd a a' α β g v) =
      detInd a a' α₀ β₀ ((GlobalTheory.LFun.SplitTie.glEquiv (a + a') e).symm g) (S v) :=
    fun g v => LinearMap.congr_fun (S.isIntertwining' g) v
  have hU : ∀ u ∈ unipRad k' (tripPlace h),
      (GlobalTheory.LFun.SplitTie.glEquiv (a + a') e).symm u ∈ unipRad k (tripPlace h) := fun u hu => by
    rw [← glEquiv_mem_unipRad e, MulEquiv.apply_symm_apply]
    exact hu
  have hle : twKer (detInd a a' α β) (unipRad k' (tripPlace h)) 1 ≤
      (twKer (detInd a a' α₀ β₀) (unipRad k (tripPlace h)) 1).comap S.toLinearMap := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨u, v, rfl⟩
    refine Submodule.subset_span ⟨⟨_, hU u u.2⟩, S v, ?_⟩
    simp only [MonoidHom.one_apply, Units.val_one, one_smul, map_sub]
    rw [← hSi]
    rfl
  have key : ∀ g : GL (Fin n) k', (GlobalTheory.LFun.SplitTie.glEquiv (a + a') e).symm
      (leviEmb k' (tripPlace h) (midHom k' l n (a + a') g)) =
      leviEmb k (tripPlace h) (midHom k l n (a + a') ((GlobalTheory.LFun.SplitTie.glEquiv n e).symm g)) := by
    intro g
    rw [MulEquiv.symm_apply_eq, glEquiv_leviEmb, levMap_midHom, MulEquiv.apply_symm_apply]
  let J : Representation.IntertwiningMap ((jacU (tripPlace h) (detInd a a' α β)).comp (midHom k' l n (a + a')))
      (((jacU (tripPlace h) (detInd a a' α₀ β₀)).comp (midHom k l n (a + a'))).comp
        (GlobalTheory.LFun.SplitTie.glEquiv n e).symm.toMonoidHom) :=
    ⟨(twKer _ _ 1).mapQ (twKer _ _ 1) S.toLinearMap hle, fun g => by
      refine Submodule.linearMap_qext _ (LinearMap.ext fun v => ?_)
      show Submodule.Quotient.mk (S (detInd a a' α β (leviEmb k' (tripPlace h) (midHom k' l n (a + a') g)) v)) =
        (Submodule.Quotient.mk (detInd a a' α₀ β₀ (leviEmb k (tripPlace h)
          (midHom k l n (a + a') ((GlobalTheory.LFun.SplitTie.glEquiv n e).symm g))) (S v)) :
            Jacquet (detInd a a' α₀ β₀) (unipRad k (tripPlace h)))
      rw [hSi, key]⟩
  have hJ : Function.Surjective J := by
    have hm : Function.Surjective ((twKer (detInd a a' α β) (unipRad k' (tripPlace h)) 1).mapQ
        (twKer (detInd a a' α₀ β₀) (unipRad k (tripPlace h)) 1) S.toLinearMap hle) := by
      have h1 := Submodule.mapQ_mkQ (twKer (detInd a a' α β) (unipRad k' (tripPlace h)) 1)
        (twKer (detInd a a' α₀ β₀) (unipRad k (tripPlace h)) 1) S.toLinearMap (h := hle)
      have h2 : Function.Surjective (((twKer (detInd a a' α₀ β₀) (unipRad k (tripPlace h)) 1).mkQ).comp S.toLinearMap) :=
        (Submodule.mkQ_surjective _).comp hS
      rw [← h1] at h2
      rw [LinearMap.coe_comp] at h2
      exact Function.Surjective.of_comp h2
    exact hm
  exact (isSubquotient_comp hQ _).trans (IsSubquotient.of_surjective J hJ)

end GlobalTheory.MidJacTransport
