import Development.WeilBound.CoreStatements.PadicHodgeComparison.GoodCoverEigenspaces.JumpStepOf

noncomputable section

open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalV GlobalTheory.HTLink GlobalTheory.HodgeCoh GlobalTheory.EtC GlobalTheory.Pst
open UpperTheory.Gal.Int.Geo GlobalTheory.WeilDeligne GlobalTheory.HeckeGal

namespace PositivityTheory.AutomorphicGaloisHodgeTate.G8

theorem occ_low (hS : CrystallineSemistableComparison.HTSpecB.HTSpecGood) (h5 : LocalMat) (h6 : CoverLow) (h8 : BCTower) (h9 : LocE)
    {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    {H : HTower E} {θ : H.Γ → Qbar l} {w : HeightOneSpectrum (𝓞 E)} {C : Cover H θ (Ow w)} (D : LowData C) (hN : Nice (low D))
    (θ₁ : (low D).Γ → Qbar l) {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : LocBridge l E Ω Gw O) (τK : E →+* ↥Bw.Kw.1) (hτ : ∀ x, (τK x : Qbar l) = Bw.j (algebraMap E Ω x))
    (hi : ∀ x : Ow w, ‖(τK (x : E) : Qbar l)‖ ≤ 1) (b : ℕ)
    (hb : HOcc (bcAlong (low D) ((ι.toRingHom.comp (algebraMap ↥Bw.Kw.1 (Qbar l))).comp τK)) (fun g => ι (θ₁ g)) b)
    {d : ℕ} (ρ : (Ω ≃ₐ[E] Ω) →* GL (Fin d) (Qbar l)) (hρ : IsMat l (low D) Ω (Qbar l) θ₁ ρ) :
    HTOcc (K := Bw.Kw) (fun σ => (ρ (Bw.e.symm σ : Gw)).val) b := by
  obtain ⟨hops, hloc⟩ := h5 E Ω l (low D) θ₁ hN Gw O Bw τK hτ
  obtain ⟨hNK, ⟨bc⟩⟩ := h8 E _ ℂ τK (ι.toRingHom.comp (algebraMap ↥Bw.Kw.1 (Qbar l))) (low D) hN
  have hocc := h9 l Bw.Kw ι (bcAlong (low D) τK)
    (bcAlong (low D) ((ι.toRingHom.comp (algebraMap ↥Bw.Kw.1 (Qbar l))).comp τK)) (fun g => g) bc θ₁ (fun g => ι (θ₁ g)) b (fun _ => rfl) hNK hops
    (h6 hS E l H θ w C D Bw.Kw τK hi) hb d _ (hloc d ρ hρ)
  have e : ∀ σ : ↥(GK Bw.Kw), (IntermediateField.fixingSubgroupEquiv Bw.Kw.1).symm
      (IntermediateField.fixingSubgroupEquiv Bw.Kw.1 σ) = σ := fun σ => MulEquiv.symm_apply_apply _ σ
  obtain ⟨S, z, hz, h⟩ := hocc
  refine ⟨S, z, hz, fun σ hσ => ?_⟩
  have := h σ hσ
  beta_reduce at this
  rw [e σ] at this
  exact this

theorem jumpCore_of (hS : CrystallineSemistableComparison.HTSpecB.HTSpecGood) (h1 : LowNice) (h2 : LowHodge) (h3 : LowPiece) (h4 : MatEx) (h5 : LocalMat)
    (h6 : CoverLow) (h7 : BridgeInt) (h8 : BCTower) (h9 : LocE) (h10 : OccMove) (h11 : JumpsEx) (h12 : ConjBridge)
    (h13 : JumpOfHT2) : JumpCore := by
  intro E Ω _ _ _ _ _ l _ ι H θ hN dd ρ₀ ρ hM hG w hw P AI hT A hA O _ _ _ Bw hj hcr τ LL' τ' hτ
  obtain ⟨J, hJ⟩ := h11 E Ω l P AI hT _ O Bw dd _ hcr τ LL' τ' hτ
  refine ⟨J, hJ, fun b hb => ?_⟩
  obtain ⟨γ, O', _, _, _, Bw', hc, hτ'⟩ := h12 E Ω l _ O Bw τ LL' τ' hτ
  obtain ⟨C, hO, hGood⟩ := hw
  obtain ⟨D⟩ := lowData_ex C hGood
  have hN' := h1 _ _ H θ _ C D
  obtain ⟨τK, hτK⟩ : ∃ τK : E →+* ↥Bw'.Kw.1, ∀ x, (τK x : Qbar l) = Bw'.j (algebraMap E Ω x) :=
    ⟨(Bw'.j.comp (algebraMap E Ω)).codRestrict Bw'.Kw.1 Bw'.j_E, fun _ => rfl⟩
  obtain ⟨d₁, ρ₁, hρ₁⟩ := h4 E Ω l (low D) (fun g => θ g / D.m g) hN'
  have e : ι.toRingHom.comp τ = (ι.toRingHom.comp (algebraMap ↥Bw'.Kw.1 (Qbar l))).comp τK :=
    RingHom.ext fun x => congrArg ι ((DFunLike.congr_fun hτ' x).symm.trans (hτK x).symm)
  have hb' := h2 E _ ℂ _ ι.toRingHom H θ _ C D hN hO b hb
  rw [e] at hb'
  have hocc := occ_low hS h5 h6 h8 h9 ι D hN' (fun g => θ g / D.m g) Bw' τK hτK
    (fun x => by rw [hτK, hc.1]; exact h7 E Ω l w A hA O Bw hj γ x) b hb' ρ₁ hρ₁
  obtain ⟨M, hMi, hMρ⟩ := h3 E Ω l H θ _ C D hN hO d₁ dd ρ₁ ρ₀ hρ₁ hM
  obtain ⟨c, hcg⟩ := hG
  refine h13 E Ω l P AI hT _ O O' Bw Bw' γ hc dd _ b J ?_ (by rw [hτ']; exact hJ)
  exact (h10 l Bw'.Kw b).2 dd (fun σ => (ρ₀ (Bw'.e.symm σ : Dec (F := E) A)).val) _ c (fun σ => hcg _)
    ((h10 l Bw'.Kw b).1 d₁ dd _ _ M hMi (fun σ => hMρ _) hocc)

end PositivityTheory.AutomorphicGaloisHodgeTate.G8

end
