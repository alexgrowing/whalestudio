import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SideEigenConductor
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ForcedByAutomorphicSemisimpleData

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty
namespace GlobalTheory.ExtTheta
variable {D : D7}
theorem transport_alt (U : _root_.GlobalTheory.HeightCounting.AUSideAlt D) (M : MtFam D) {μ₀ μ₁ : D.what₂.Tup} {j₀ j₁ : ℕ} (hμ : μ₀ = μ₁) (hj : j₀ = j₁)
    (a₀ : 1 ≤ j₀) (b₀ : j₀ ≤ D.R.m) (a₁ : 1 ≤ j₁) (b₁ : j₁ ≤ D.R.m) {ι : Type}
    (S₀ : ι → Submodule ℂ (GAf D.host.E D.R.nV → (M μ₀ j₀ a₀ b₀).wt.W))
    (irr₀ : ∀ P, NG.IsIrrRep (M μ₀ j₀ a₀ b₀).wt.ρ (S₀ P))
    (surj : ∀ S', NG.IsIrrRep (M μ₀ j₀ a₀ b₀).wt.ρ S' →
      (NG.isoTyp (M μ₀ j₀ a₀ b₀).wt.ρ S').comap (M μ₀ j₀ a₀ b₀).real ≠ ⊥ → ∃ P, NG.IsoRep (S₀ P) S')
    (S₁ : Submodule ℂ (GAf D.host.E D.R.nV → (M μ₁ j₁ a₁ b₁).wt.W))
    (irr₁ : NG.IsIrrRep (M μ₁ j₁ a₁ b₁).wt.ρ S₁)
    (ne : (NG.isoTyp (M μ₁ j₁ a₁ b₁).wt.ρ S₁).comap (M μ₁ j₁ a₁ b₁).real ≠ ⊥) :
    ∃ P, (∀ (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)) (k : ℕ) (c : ℂ),
      (∀ y ∈ (NG.isoTyp (M μ₁ j₁ a₁ b₁).wt.ρ S₁).comap (M μ₁ j₁ a₁ b₁).real,
        NG.tN (M μ₁ j₁ a₁ b₁).J s ϖ k ((M μ₁ j₁ a₁ b₁).real y) = c • (M μ₁ j₁ a₁ b₁).real y) →
      ∀ y ∈ (NG.isoTyp (M μ₀ j₀ a₀ b₀).wt.ρ (S₀ P)).comap (M μ₀ j₀ a₀ b₀).real,
        NG.tN (M μ₀ j₀ a₀ b₀).J s ϖ k ((M μ₀ j₀ a₀ b₀).real y) = c • (M μ₀ j₀ a₀ b₀).real y) ∧
      (∀ w, D.nbc.locAU j₀ (U.cls j₀ a₀ b₀ { (M μ₀ j₀ a₀ b₀).wt with S := S₀ P, irrS := irr₀ P }) w =
        D.nbc.locAU j₁ (U.cls j₁ a₁ b₁ { (M μ₁ j₁ a₁ b₁).wt with S := S₁, irrS := irr₁ }) w) ∧
      (∀ w, D.nbc.satAU j₀ (U.cls j₀ a₀ b₀ { (M μ₀ j₀ a₀ b₀).wt with S := S₀ P, irrS := irr₀ P }) w =
        D.nbc.satAU j₁ (U.cls j₁ a₁ b₁ { (M μ₁ j₁ a₁ b₁).wt with S := S₁, irrS := irr₁ }) w) ∧
      D.nbc.infW j₀ (D.nbc.wtAU j₀ (U.cls j₀ a₀ b₀ { (M μ₀ j₀ a₀ b₀).wt with S := S₀ P, irrS := irr₀ P })) =
        D.nbc.infW j₁ (D.nbc.wtAU j₁ (U.cls j₁ a₁ b₁ { (M μ₁ j₁ a₁ b₁).wt with S := S₁, irrS := irr₁ })) := by
  subst hμ; subst hj
  obtain ⟨P, hP⟩ := surj S₁ irr₁ ne
  have e := isoTyp_congr (M μ₀ j₀ a₀ b₀).wt.ρ (irr₀ P).1.stable hP
  have hc : U.cls j₀ a₀ b₀ { (M μ₀ j₀ a₀ b₀).wt with S := S₀ P, irrS := irr₀ P } =
      U.cls j₀ a₀ b₀ { (M μ₀ j₀ a₀ b₀).wt with S := S₁, irrS := irr₁ } :=
    (U.iso j₀ a₀ b₀ _ _).2 ⟨NG.AlgWt.Iso.refl _, hP⟩
  refine ⟨P, fun s ϖ k c h => ?_, fun w => ?_, fun w => ?_, ?_⟩
  · rw [e]; exact h
  · rw [hc]
  · rw [hc]
  · rw [hc]
variable {cf : CharFrame D} {jE : D.host.E →+* Qb} {A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE} {M : MtFam D} {C : NChoice D}
  {tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E}
theorem split_out_of_w_eq {big₀ big₁ : D.what₂.places.Pl → Finset ℂ} {X₀ X₁ : LocNd (lay0 D)} {T₀ : LocTw X₀} {T₁ : LocTw X₁}
    (Sp₀ : NdSpec A.pl M C big₀ X₀ T₀) (Sp₁ : NdSpec A.pl M C big₁ X₁ T₁) (i₀ : X₀.nd.Loc) (i₁ : X₁.nd.Loc)
    (hw : X₀.nd.w i₀ = X₁.nd.w i₁) (v : PlE D.host) (h : SplitOut X₀.nd i₀ v) : SplitOut X₁.nd i₁ v := by
  have hl : X₀.nd.l i₀ = X₁.nd.l i₁ := by rw [← X₀.nd.w_l, ← X₁.nd.w_l, hw]
  have q₀ : X₀.nd.Q i₀ = C.Q (X₀.nd.w i₀) :=
    (Sp₀.Q_eq _ _ i₀ ((X₀.nd.locs_mem _ _ _).2 ⟨rfl, rfl⟩)).trans (Sp₀.Qc_eq _ _)
  have q₁ : X₁.nd.Q i₁ = C.Q (X₁.nd.w i₁) :=
    (Sp₁.Q_eq _ _ i₁ ((X₁.nd.locs_mem _ _ _).2 ⟨rfl, rfl⟩)).trans (Sp₁.Qc_eq _ _)
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, hl ▸ h2, fun hs => h3 ?_, ?_⟩
  · have := (X₁.S_def i₁ v).1 hs
    refine (X₀.S_def i₀ v).2 ?_
    have hl' : X₀.l i₀ = X₁.l i₁ := hl
    rw [hl']; exact this
  · rw [q₁, ← hw, ← q₀]; exact h4
theorem mu_c_eq_of_mu_eq_of_j_eq {X₀ X₁ : LocNd (lay0 D)} {iq₀ : ∀ i : X₀.nd.Loc, FractionRing (X₀.nd.O i) →+* Qbar (X₀.nd.l i)}
    {iq₁ : ∀ i : X₁.nd.Loc, FractionRing (X₁.nd.O i) →+* Qbar (X₁.nd.l i)} {Y₀ : LocAut X₀} {Y₁ : LocAut X₁}
    {C₀ : LocBC Y₀} {C₁ : LocBC Y₁} (U₀ : _root_.GlobalTheory.HeightCounting.AutomorphicSpecialisation A M tup iq₀ Y₀ C₀) (U₁ : _root_.GlobalTheory.HeightCounting.AutomorphicSpecialisation A M tup iq₁ Y₁ C₁)
    (i₀ : X₀.nd.Loc) (i₁ : X₁.nd.Loc) (hμ : X₀.nd.mu i₀ = X₁.nd.mu i₁) (hj : X₀.nd.j i₀ = X₁.nd.j i₁) :
    (Y₀.muC i₀ : D.naut.CG 1) = Y₁.muC i₁ := by
  have hr := X₀.nd.j_range i₀
  let j : Fin D.R.m := ⟨X₀.nd.j i₀ - 1, by omega⟩
  have e₀ : j.1 + 1 = X₀.nd.j i₀ := by simp only [j]; omega
  have h₀ := U₀.muC i₀ j e₀
  have h₁ := U₁.muC i₁ j (e₀.trans hj)
  apply A.chr.e1.injective
  apply Subtype.ext
  rw [h₀, h₁, hμ]
set_option maxHeartbeats 1000000 in
theorem zn_of_alt {X₀ X₁ : LocNd (lay0 D)} {iq₀ : ∀ i : X₀.nd.Loc, FractionRing (X₀.nd.O i) →+* Qbar (X₀.nd.l i)}
    {iq₁ : ∀ i : X₁.nd.Loc, FractionRing (X₁.nd.O i) →+* Qbar (X₁.nd.l i)} {Y₀ : LocAut X₀} {Y₁ : LocAut X₁}
    {C₀ : LocBC Y₀} {C₁ : LocBC Y₁} (U₀ : _root_.GlobalTheory.HeightCounting.AutomorphicSpecialisation A M tup iq₀ Y₀ C₀) (U₁ : _root_.GlobalTheory.HeightCounting.AutomorphicSpecialisation A M tup iq₁ Y₁ C₁)
    (i₀ : X₀.nd.Loc) (i₁ : X₁.nd.Loc) (hw : X₀.nd.w i₀ = X₁.nd.w i₁) (hj : X₀.nd.j i₀ = X₁.nd.j i₁)
    (hs : ∀ v, SplitOut X₀.nd i₀ v → SplitOut X₁.nd i₁ v) (x₀ : X₀.nd.X i₀) (x₁ : X₁.nd.X i₁)
    (he : ∀ v k, SplitOut X₀.nd i₀ v → 1 ≤ k → k ≤ D.R.nV →
      iotaO X₁.nd Y₁.naut i₁ ((X₁.nd.hT i₁ v k : X₁.nd.X i₁ → X₁.nd.O i₁) x₁) =
        iotaO X₀.nd Y₀.naut i₀ ((X₀.nd.hT i₀ v k : X₀.nd.X i₀ → X₀.nd.O i₀) x₀))
    (h : x₁ ∈ ZN X₁.nd Y₁.naut i₁) : x₀ ∈ ZN X₀.nd Y₀.naut i₀ := by
  have hμ : X₀.nd.mu i₀ = X₁.nd.mu i₁ := by rw [X₀.nd.mu_w, X₁.nd.mu_w, hw]
  have hm := _root_.GlobalTheory.ExtTheta.mu_c_eq_of_mu_eq_of_j_eq U₀ U₁ i₀ i₁ hμ hj
  obtain ⟨P₁, hP₁, Pa, ⟨c1, c2, c3, c4, c5, c6⟩, hmem⟩ := h
  have ne := Y₁.naut.typeV_ne i₁ P₁
  rw [U₁.typeV] at ne
  obtain ⟨P₀, t1, t2, t3, t4⟩ := _root_.GlobalTheory.ExtTheta.transport_alt A.au M hμ hj (X₀.nd.j_range i₀).1 (X₀.nd.j_range i₀).2 (X₁.nd.j_range i₁).1
    (X₁.nd.j_range i₁).2 (U₀.S i₀) (U₀.irr i₀) (U₀.surj i₀) (U₁.S i₁ P₁) (U₁.irr i₁ P₁) ne
  have l1 : ∀ w, (Y₀.naut.locV i₀ P₀ w : D.naut.LP w) = Y₁.naut.locV i₁ P₁ w := fun w => by
    rw [C₀.embAV_loc, C₁.embAV_loc, U₀.emb, U₁.emb]; exact t2 w
  have l2 : ∀ w, Y₀.naut.satV i₀ P₀ w = Y₁.naut.satV i₁ P₁ w := fun w => by
    rw [C₀.embAV_sat, C₁.embAV_sat, U₀.emb, U₁.emb]; exact t3 w
  have l3 : Y₀.naut.infWt i₀ = Y₁.naut.infWt i₁ := by
    rw [C₀.embAV_inf i₀ P₀, C₁.embAV_inf i₁ P₁, U₀.emb, U₁.emb]; exact t4
  refine ⟨P₀, (U₀.ptV i₀ P₀ x₀).2 fun w k s ϖ h1 h2 h3 h4 h5 => ?_, Pa, ⟨c1, c2, c3, fun w hw => ?_, fun w hw => ?_, fun τ => ?_⟩, ?_⟩
  · have h6 := (U₁.ptV i₁ P₁ x₁).1 hP₁ w k s ϖ (hs w h1) h2 h3 h4 h5
    rw [U₁.typeV, he w k h1 h4 h5] at h6
    rw [U₀.typeV]
    exact t1 s ϖ k _ h6
  · exact (c4 w hw).trans (l1 w).symm
  · rw [l2]; exact c5 w hw
  · rw [l3]; exact c6 τ
  · have : (Y₀.naut.muC i₀ : D.naut.CG 1) = Y₁.naut.muC i₁ := hm
    rw [this]; exact hmem
set_option maxHeartbeats 1000000 in
theorem theta_loci_alt : HeckeStdPlain → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → ∀ (big₀ big₁ : D.what₂.places.Pl → Finset ℂ) (L₀ L₁ : LocAll (lay0 D)), _root_.GlobalTheory.CoefDuty.BuiltAlt A M C tp.tup big₀ L₀ → _root_.GlobalTheory.CoefDuty.BuiltAlt A M C tp.tup big₁ L₁ → ∀ (i₀ : L₀.lay.fixZ.nd.Loc) (i₁ : L₁.lay.fixZ.nd.Loc), L₀.lay.fixZ.nd.w i₀ = L₁.lay.fixZ.nd.w i₁ → L₀.lay.fixZ.nd.j i₀ = L₁.lay.fixZ.nd.j i₁ → ∀ e : L₁.lay.fixZ.nd.X i₁ ≃ L₀.lay.fixZ.nd.X i₀, (∀ (v : PlE D.host) (k : ℕ) (x : L₁.lay.fixZ.nd.X i₁), SplitOut L₁.lay.fixZ.nd i₁ v → 1 ≤ k → k ≤ D.R.nV → iotaO L₁.lay.fixZ.nd L₁.lay.fixZ.naut i₁ ((L₁.lay.fixZ.nd.hT i₁ v k : L₁.lay.fixZ.nd.X i₁ → L₁.lay.fixZ.nd.O i₁) x) = iotaO L₀.lay.fixZ.nd L₀.lay.fixZ.naut i₀ ((L₀.lay.fixZ.nd.hT i₀ v k : L₀.lay.fixZ.nd.X i₀ → L₀.lay.fixZ.nd.O i₀) (e x))) → ∀ x, x ∈ L₁.lay.fixZ.nd.Z i₁ ↔ e x ∈ L₀.lay.fixZ.nd.Z i₀ := by
  intro _ D cf jE A low Pq S hL eig θ Bs M C tp _ _ _ _ _ _ big₀ big₁ L₀ L₁ ⟨Sp₀, ⟨U₀⟩, _⟩ ⟨Sp₁, ⟨U₁⟩, _⟩ i₀ i₁ hw hj e he x
  have s01 := _root_.GlobalTheory.ExtTheta.split_out_of_w_eq Sp₀ Sp₁ i₀ i₁ hw
  have s10 := _root_.GlobalTheory.ExtTheta.split_out_of_w_eq Sp₁ Sp₀ i₁ i₀ hw.symm
  refine (L₁.lay.zOk_fixZ.1 i₁ x).trans (Iff.trans ⟨fun h => ?_, fun h => ?_⟩ (L₀.lay.zOk_fixZ.1 i₀ (e x)).symm)
  · exact _root_.GlobalTheory.ExtTheta.zn_of_alt U₀ U₁ i₀ i₁ hw hj s01 (e x) x (fun v k h1 h2 h3 => he v k x (s01 v h1) h2 h3) h
  · exact _root_.GlobalTheory.ExtTheta.zn_of_alt U₁ U₀ i₁ i₀ hw.symm hj.symm s10 x (e x) (fun v k h1 h2 h3 => (he v k x h1 h2 h3).symm) h
end GlobalTheory.ExtTheta
end
end
