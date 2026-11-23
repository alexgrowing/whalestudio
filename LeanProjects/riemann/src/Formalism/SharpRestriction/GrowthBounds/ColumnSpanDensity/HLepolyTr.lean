import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.InvariantSectionsRingChange

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.GradedWeylDivisibility MvPolynomial

section

variable {p n' : ℕ} {R₁ R₂ : RS p n'} (I : RSIso R₁ R₂) {m : ℕ} (lam0 : Fin n' → Fin (m + 1) → ℤ)

theorem pm_symm (P : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) R₁.Kf) :
    I.symm.JO.pm (I.JO.pm P) = P := by
  show MvPolynomial.map (I.φK.symm : R₂.Kf →+* R₁.Kf) (MvPolynomial.map (I.φK : R₁.Kf →+* R₂.Kf) P) = P
  have h : (I.φK.symm : R₂.Kf →+* R₁.Kf).comp (I.φK : R₁.Kf →+* R₂.Kf) = RingHom.id _ := by
    ext x; simp
  rw [MvPolynomial.map_map, h, MvPolynomial.map_id]

theorem pm_symm' (P : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) R₂.Kf) :
    I.JO.pm (I.symm.JO.pm P) = P := by
  show MvPolynomial.map (I.φK : R₁.Kf →+* R₂.Kf) (MvPolynomial.map (I.φK.symm : R₂.Kf →+* R₁.Kf) P) = P
  have h : (I.φK : R₁.Kf →+* R₂.Kf).comp (I.φK.symm : R₂.Kf →+* R₁.Kf) = RingHom.id _ := by
    ext x; simp
  rw [MvPolynomial.map_map, h, MvPolynomial.map_id]

def PsiV : Vsp R₁.Kf lam0 ≃+ Vsp R₂.Kf lam0 where
  toFun x := ⟨I.JO.pm x.1, Vsp_tr I lam0 x.1 x.2⟩
  invFun y := ⟨I.symm.JO.pm y.1, Vsp_tr I.symm lam0 y.1 y.2⟩
  left_inv x := Subtype.ext (pm_symm I x.1)
  right_inv y := Subtype.ext (pm_symm' I y.1)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

theorem HLpoly_tr (L : Submodule R₁.W (Fin (m + 1) → R₁.Qq))
    (P : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) R₁.Kf)
    (hP : P ∈ Hten R₁.O lam0 (fun s => extO R₁.O R₁.ι R₁.σ s.val L)) :
    I.JO.pm P ∈ Hten R₂.O lam0 (fun s => extO R₂.O R₂.ι R₂.σ s.val (mapSub I.JW L)) := by
  have h := Hten_tr (I := I) (lam0 := lam0) (Λ := fun s => extO R₁.O R₁.ι R₁.σ s.val L) (P := P) hP
  simp only [extO_tr] at h
  exact h

theorem HLepoly_tr (e : Edge R₁.W R₁.Qq (m + 1))
    (P : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) R₁.Kf)
    (hP : P ∈ Hten R₁.O lam0 (fun s => LeAt p R₁.ι R₁.σ R₁.w s.val e)) :
    I.JO.pm P ∈ Hten R₂.O lam0
      (fun s => LeAt p R₂.ι R₂.σ R₂.w s.val ⟨mapSub I.JW e.src, mapSub I.JW e.tgt⟩) := by
  have h := Hten_tr (I := I) (lam0 := lam0) (Λ := fun s => LeAt p R₁.ι R₁.σ R₁.w s.val e) (P := P) hP
  simp only [LeAt_tr] at h
  exact h

end

theorem restHLTransport : RestHLTransport := by
  intro p n' R₁ R₂ I m lam0
  have hΨ : ∀ (c : R₁.Kf) (v : Vsp R₁.Kf lam0), PsiV I lam0 (c • v) = I.φK c • PsiV I lam0 v := by
    intro c v
    exact Subtype.ext (map_smul' _ c v.1)
  refine ⟨mapSubEquiv I.JW, PsiV I lam0, hΨ, fun L => isLattice_mapSub_iff I.JW L, fun r e => ?_, fun L x => ?_,
    fun e x => ?_, ?_⟩
  · constructor
    · exact isEdge_mapSub I.JW p n' r
    · intro h
      have h2 := isEdge_mapSub I.JW.symm p n' r h
      simp only at h2
      have h3 : mapSub I.JW.symm (mapSub I.JW e.src) = e.src := mapSub_symm _ _
      have h4 : mapSub I.JW.symm (mapSub I.JW e.tgt) = e.tgt := mapSub_symm _ _
      have h5 : (⟨mapSub I.JW.symm (mapSub I.JW e.src), mapSub I.JW.symm (mapSub I.JW e.tgt)⟩ :
          Edge R₁.W R₁.Qq (m + 1)) = e := by rw [h3, h4]
      have h6 : IsEdge p n' r (⟨mapSub I.JW.symm (mapSub I.JW e.src), mapSub I.JW.symm (mapSub I.JW e.tgt)⟩ :
          Edge R₁.W R₁.Qq (m + 1)) := h2
      rwa [h5] at h6
  · constructor
    · intro hx
      exact HLpoly_tr I lam0 L x.1 hx
    · intro hx
      have h2 := HLpoly_tr I.symm lam0 (mapSub I.JW L) (PsiV I lam0 x).1 hx
      have h3 : mapSub I.symm.JW (mapSub I.JW L) = L := mapSub_symm I.JW L
      rw [h3] at h2
      have h4 : I.symm.JO.pm ((PsiV I lam0 x : Vsp R₂.Kf lam0) : MvPolynomial _ R₂.Kf) = x.1 := pm_symm I x.1
      rw [h4] at h2
      exact h2
  · constructor
    · intro hx
      exact HLepoly_tr I lam0 e x.1 hx
    · intro hx
      have h2 := HLepoly_tr I.symm lam0 ⟨mapSub I.JW e.src, mapSub I.JW e.tgt⟩ (PsiV I lam0 x).1 hx
      have h3 : mapSub I.symm.JW (mapSub I.JW e.src) = e.src := mapSub_symm I.JW _
      have h3' : mapSub I.symm.JW (mapSub I.JW e.tgt) = e.tgt := mapSub_symm I.JW _
      simp only [h3, h3'] at h2
      have h4 : I.symm.JO.pm ((PsiV I lam0 x : Vsp R₂.Kf lam0) : MvPolynomial _ R₂.Kf) = x.1 := pm_symm I x.1
      rw [h4] at h2
      exact h2
  · unfold dimV Module.finrank
    rw [rank_eq_of_equiv_equiv I.φK (PsiV I lam0) I.φK.bijective hΨ]

theorem lpRingIndep_of' (h : RestRSIso) : LPRingIndep := lpRingIndep_of h restHLTransport

end Formalism.MainNotions.flipOneThree.Pf

end
