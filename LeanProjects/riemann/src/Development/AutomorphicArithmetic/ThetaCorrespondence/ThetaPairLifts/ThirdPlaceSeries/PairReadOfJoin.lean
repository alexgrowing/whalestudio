import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PairReadingOfJoin
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section
namespace GlobalTheory.PairReadPf
end GlobalTheory.PairReadPf
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.PairReadPf in
attribute [local instance] GlobalTheory.NPin.ThetaMod.acg GlobalTheory.NPin.ThetaMod.mod in
theorem GlobalTheory.NPin.pairRead_of_join_alt : GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), _root_.GlobalTheory.NPin.CharacterChoiceJoin P → ∀ S : Reading P.T, _root_.GlobalTheory.NPin.IsFaithfulReading P S → RowUnit S → PairRead S := by
  intro hBZ hL D P J S hT hRU i w hw σ Q hPairs
  obtain ⟨s, rfl⟩ := exists_splitPlace_w D w hw
  obtain ⟨j, hj⟩ : ∃ j : Fin D.R.m, j.1 + 1 = D.nd.j i :=
    ⟨⟨D.nd.j i - 1, by have := D.nd.j_range i; omega⟩, by have := D.nd.j_range i; simp only; omega⟩
  obtain ⟨f, hf, F, hF, hne⟩ := hPairs
  have hFmem : (P.M.loc i).real F ∈ NG.AFall D.host.E D.R.nV (P.M.loc i).wt.ρ := by
    have : (P.M.loc i).real F ∈ LinearMap.range (P.M.loc i).real := LinearMap.mem_range_self _ _
    rw [(P.M.loc i).real_range] at this
    exact this.1
  let X := J.rowM i
  let Θ := J.th i j hj
  let Fp : ↥(NG.AFall D.host.E D.R.nV (P.M.loc i).wt.ρ) := ⟨_, hFmem⟩
  let yp : ↥X.C := ⟨X.φ f, X.φ_mem f⟩
  have h0 : Θ.Λ Θ.φ₀ Fp yp ≠ 0 := by
    rw [← Θ.read F f Fp rfl]
    intro h
    apply hne
    show inner ℂ F (LinearMap.adjoint (D.what₂.thetaP (D.nd.mu i) (D.nd.j i)) f) = 0
    rw [LinearMap.adjoint_inner_right, ← inner_conj_symm, h, map_zero]
  have hμc := hT.mu i s.w hw j hj
  have hηc := hT.eta i s.w hw
  have hloc := Θ.loc s _ _ hμc hηc
  let ℓ0 : Θ.Ω →+ ℂ := AddMonoidHom.mk' (fun φ => Θ.Λ φ Fp yp) (by intro a b; simp)
  obtain ⟨ι, φ1, hφ1, hℓ1⟩ := exists_ne_of_mem_iSup _ ℓ0 hloc h0
  obtain ⟨hLin, φ2, ⟨Φ0, rfl⟩, hℓ2⟩ := exists_ne_of_mem_iSup _ ℓ0 hφ1 hℓ1
  obtain ⟨c, hc, hci, hιeq⟩ := hLin
  have hFiso : (Fp : GAf D.host.E D.R.nV → (P.M.loc i).wt.W) ∈
      NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i Q) := by
    have := hF
    rw [P.H.av.typeV] at this
    exact this
  have hspan := GlobalTheory.T.isotypicPart_spanned_by_splitPlace_localComponent D.host.E D.R.nV (P.M.loc i).wt (P.H.av.S i Q) (P.H.av.irr i Q) s _
    (hT.rep i s hw Q) c hc hci
  let ℓF : ↥(NG.AFall D.host.E D.R.nV (P.M.loc i).wt.ρ) →+ ℂ :=
    AddMonoidHom.mk' (fun F' => Θ.Λ (ι Φ0) F' yp) (by intro a b; simp)
  obtain ⟨T1, F1, hF1, hℓF1⟩ := exists_ne_of_mem_iSup_sub _ _
    (fun T => iSup_le fun hT1 => by rintro _ ⟨v, rfl⟩; exact hT1.1 v) ℓF Fp (hspan hFiso) hℓ2
  obtain ⟨hT1, F2, ⟨a0, ha0⟩, hℓF2⟩ := exists_ne_of_mem_iSup_sub _ _
    (fun hT1 => by rintro _ ⟨v, rfl⟩; exact hT1.1 v) ℓF F1 hF1 hℓF1
  have hσne : D.what₂.isot (D.nd.j i) σ ≠ ⊥ := by
    intro hb
    rw [hb, Submodule.mem_bot] at hf
    subst hf
    exact hne (by simp)
  have hyI : (yp : X.A) ∈ Formalism.IndefR.principalLevelFrame.isotIn (D := D) X.ρ X.C (P.rep σ) := (X.isot σ f).1 hf
  unfold Formalism.IndefR.principalLevelFrame.isotIn at hyI
  let ℓy : ↥X.C →+ ℂ := (Θ.Λ (ι Φ0) F2).toAddMonoidHom
  obtain ⟨Φe, y1, hy1, hℓy1⟩ := exists_ne_of_mem_iSup_sub X.C _
    (fun Φe => iSup_le fun h => h.2) ℓy yp hyI hℓF2
  obtain ⟨hΦe, y2, ⟨f2, hf2⟩, hℓy2⟩ := exists_ne_of_mem_iSup_sub X.C _
    (fun h => h.2) ℓy y1 hy1 hℓy1
  have hΦC : ∀ g : ↥(P.rep σ).S, Φe g ∈ X.C := fun g => hΦe.2 (LinearMap.mem_range_self _ _)
  have hspan2 := GlobalTheory.T.finiteType_spanned_by_splitPlace_localComponent D.host.E D.R.r (P.rep σ) s _ (hT.row i s hw σ hσne) c hc hci
  let ℓ2 : ↥(P.rep σ).S →+ ℂ :=
    AddMonoidHom.mk' (fun g => Θ.Λ (ι Φ0) F2 ⟨Φe g, hΦC g⟩) (by
      intro a b
      have e : (⟨Φe (a + b), hΦC (a + b)⟩ : ↥X.C) = ⟨Φe a, hΦC a⟩ + ⟨Φe b, hΦC b⟩ := by
        apply Subtype.ext; simp
      show Θ.Λ (ι Φ0) F2 ⟨Φe (a + b), hΦC (a + b)⟩ = Θ.Λ (ι Φ0) F2 ⟨Φe a, hΦC a⟩ + Θ.Λ (ι Φ0) F2 ⟨Φe b, hΦC b⟩
      rw [e, map_add])
  have hℓ2f2 : ℓ2 f2 ≠ 0 := by
    have e : (⟨Φe f2, hΦC f2⟩ : ↥X.C) = y2 := Subtype.ext hf2
    show Θ.Λ (ι Φ0) F2 ⟨Φe f2, hΦC f2⟩ ≠ 0
    rw [e]; exact hℓy2
  obtain ⟨T2, g1, hg1, hℓg1⟩ := exists_ne_of_mem_iSup_sub _ _
    (fun T => iSup_le fun hT2 => by rintro _ ⟨v, rfl⟩; exact hT2.1 v) ℓ2 f2 (hspan2 f2.2) hℓ2f2
  obtain ⟨hT2, g2, ⟨c0, hc0⟩, hℓg2⟩ := exists_ne_of_mem_iSup_sub _ _
    (fun hT2 => by rintro _ ⟨v, rfl⟩; exact hT2.1 v) ℓ2 g1 hg1 hℓg1
  let T' : ((S i s.w hw).rep Q).V →ₗ[ℂ] ↥(NG.AFall D.host.E D.R.nV (P.M.loc i).wt.ρ) :=
    T1.codRestrict _ hT1.1
  let T'' : ((S i s.w hw).row σ).V →ₗ[ℂ] ↥X.C :=
    (Φe ∘ₗ T2.codRestrict _ hT2.1).codRestrict X.C (fun v => hΦC _)
  have hT'eq : ∀ x : GAf D.host.E D.R.nV, TrivOutside {s.v} x → ∀ a,
      ((T' (((S i s.w hw).rep Q).π (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x)) a) :
        ↥(NG.AFall D.host.E D.R.nV (P.M.loc i).wt.ρ)) : GAf D.host.E D.R.nV → (P.M.loc i).wt.W) =
        NG.rt D.host.E D.R.nV x (T' a : GAf D.host.E D.R.nV → (P.M.loc i).wt.W) :=
    fun x hx a => hT1.2 x hx a
  have hT''eq : ∀ x : GAf D.host.E D.R.r, TrivOutside {s.v} x → ∀ a,
      ((T'' (((S i s.w hw).row σ).π (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.r x)) a) : ↥X.C) : X.A) =
        X.ρ x (T'' a) := by
    intro x hx a
    have e : (⟨T2 (((S i s.w hw).row σ).π (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.r x)) a),
        hT2.1 _⟩ : ↥(P.rep σ).S) =
        ⟨NG.rt D.host.E D.R.r x (T2 a), (P.rep σ).stable x _ (hT2.1 a)⟩ := Subtype.ext (hT2.2 x hx a)
    show Φe ⟨_, _⟩ = X.ρ x (Φe ⟨T2 a, hT2.1 a⟩)
    rw [e]
    exact hΦe.1 x ⟨T2 a, hT2.1 a⟩
  let b := ((Θ.Λ ∘ₗ ι).compl₂ T').compr₂ (precompₛ T'')
  have hb0 : b Φ0 a0 c0 ≠ 0 := by
    have e1 : T' a0 = F2 := Subtype.ext ha0
    have e2 : T'' c0 = ⟨Φe g2, hΦC g2⟩ := by
      apply Subtype.ext
      show Φe ⟨T2 c0, hT2.1 c0⟩ = Φe g2
      congr 1
      exact Subtype.ext hc0
    show Θ.Λ (ι Φ0) (T' a0) (T'' c0) ≠ 0
    rw [e1, e2]
    exact hℓg2
  refine GlobalTheory.T.thetaPairing_of_invariant_trilinear_form _ D.R.r (D.R.r + D.R.t) _ _ (S i s.w hw).mu ((S i s.w hw).row σ).π
    (twist ((S i s.w hw).rep Q).π (detChar (Fin (D.R.r + D.R.t)) (S i s.w hw).eta))
    ((hBZ _).1 (Fin D.R.r) _ _ ((S i s.w hw).row σ).smooth ((S i s.w hw).row σ).irr)
    (hRU i s.w hw σ hσne) (S i s.w hw).mu_ok.1 b (fun h => hb0 (by rw [h]; rfl)) ?_
  intro g h Φ Φ' hΦ a c'
  exact GlobalTheory.T.thetaTrilinearForm_localGroup_invariant D P.M i P.rep X _ _ Θ s (S i s.w hw).mu (S i s.w hw).eta ι c hιeq _ _
    ((S i s.w hw).rep Q).π ((S i s.w hw).row σ).π T' hT'eq T'' hT''eq g h Φ Φ' hΦ a c'
end
end
