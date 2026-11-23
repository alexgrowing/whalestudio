import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PlainTorsionPairs.CRealAv
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PointTheoremBaseObject
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PrDesc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PrLinkedEnd
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PlainTorsionPairs.IrrArithPointsAutomorphicAway
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ArithmeticPointClassicality

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr
open private ap_norm ap_field ap_coef ap_local ap_adic ap_det ap_locAlg apExt ap_lift ap_psi from Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.AutPtOf
def UpperTheory.Gal.projectedFormsSystemPart.AutPtOAlt {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
    {η : G ℚ Ω →* ℤˣ} {Ψ : G ℚ Ω →* c.Oˣ} {σ g₁ : G ℚ Ω} {B : ValuationSubring Ω} {M : ℕ}
    {L : Type} [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] {Φ : Fr.Frame l (ResidueField c.O)} (u : W.Plc (W.Lp L))
    (k : GalLink η Ψ σ g₁ B M L Φ) (n : ℕ) (ι : Qbar l ≃+* ℂ) (ka : G L Ω →* (Qbar l)ˣ) : Prop :=
  ∀ (A : Subalgebra c.O (PadicAlgCl l)) [IsDiscreteValuationRing A] [Module.Finite c.O A] [IsLocalHom (algebraMap c.O A)]
    (ρ : Fr.NRep Φ n A), IsLiftA c.O ρ →
    (∀ v i, ∀ g ∈ Φ.Iv v, (ρ.ψ v i g).val = algebraMap c.O A (Ψ (k.j v g) ^ Fr.w n i).val) →
    ∀ r : G L Ω →* GL (Fin n) (Qbar l), (∀ s, (r s).val = (ρ.r (k.p0 s)).map A.val) → IsIrr r →
      _root_.UpperTheory.Gal.projectedFormsSystemPart.AutOffN u ι (tw r ka)
theorem UpperTheory.Gal.projectedFormsSystemPart.autPtO_alt :
    GlobalTheory.Published.GlobalArtinReciprocity →
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (c : Coef l)
    [CharP (ResidueField c.O) l] (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N)
    (η : G ℚ Ω →* ℤˣ) (σ g₁ : G ℚ Ω) (B : ValuationSubring Ω) (M : ℕ), LinkHyp c N e η σ B M →
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] (Φ : Fr.Frame l (ResidueField c.O))
    (k : GalLink η (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) σ g₁ B M L Φ)
    (c₁ : Coef l) [Fr.IsCoef l c₁.O] (f : ResidueField c.O →+* ResidueField c₁.O) (n : ℕ)
    (ka : G L Ω →* (Qbar l)ˣ) (R : CReal k c₁ f n ka), IsKa σ M ι n ka → ∀ J, R.T.GoodPt J → R.B₀.arithmeticPointClassicalityDense ι J →
      _root_.UpperTheory.Gal.projectedFormsSystemPart.AutPtOAlt R.s.v0 k n ι ka := by
  intro hG Ω _ _ _ l _ ι c _ N _ e ψ η σ g₁ B M H L _ _ _ _ _ Φ k c₁ _ f n ka R hka J hJ hE A _ _ _ ρ hρ hψ r hr hirr
  obtain ⟨c₂, h₁, h₂⟩ := ap_coef c c₁ A
  letI : Algebra c₁.O c₂.O := (Subalgebra.inclusion h₁).toRingHom.toAlgebra
  let φ : A →+* c₂.O := A.val.toRingHom.codRestrict c₂.O fun x => h₂ x.1 x.2
  haveI : IsLocalHom φ := ap_local c₂ φ (fun a => rfl) fun a b h => Subtype.ext (congrArg (fun t : c₂.O => t.1) h)
  haveI hl : IsLocalHom (algebraMap c₁.O c₂.O) := ap_local c₂ _ (fun a => rfl) (Subalgebra.inclusion_injective h₁)
  obtain ⟨hc, hf, -⟩ := UpperTheory.V.abelian₂.dvr_finite l c₂.O
  haveI : IsCD c₁.O c₂.O := { complete := hc, isLocalHom := hl, fin := hf }
  let j : c₂.O →ₐ[c₁.O] Qbar l := { c₂.O.val.toRingHom with commutes' := fun _ => rfl }
  let ρ₂ : Fr.NRep (Φ.ext f) n c₂.O := apExt f (ρ.map φ)
  have hlift : IsLiftA c₁.O ρ₂ := ap_lift f φ (fun a => by
    rw [R.hf a ⟨a.1, R.le a.2⟩ rfl, ResidueField.map_residue]; rfl) ρ hρ
  obtain ⟨F, hF, hD, hP⟩ := hJ c₂.O ρ₂ hlift (Qbar l) j Subtype.val_injective fun U hU =>
    hirr.2.2 U le_top fun s v hv => by rw [hr]; exact hU (k.p0 s) trivial v hv
  have hw : ∀ v : W.Vl l L, ((l : ℕ) : 𝓞 L) ∈ (R.s.w v).asIdeal := fun v => by
    have h1 := (R.s.hA v (l : ℕ)).2 v.2
    refine (R.s.hw v (l : ℕ)).1 ?_
    simpa using h1
  choose wt hwt using fun v : W.Vl l L => ap_locAlg hG ι ka hka.alg (R.s.hw v) (hw v)
  refine _root_.UpperTheory.Gal.projectedFormsSystemPart.end2oN R.v0 hE (j.comp F) (fun v i τ => wt v τ - (e : ℤ) * Fr.w n i) _ (fun x hx => ?_) ⟨fun v τ a b hab => ?_, fun v i => ?_⟩ ?_
    ((UpperTheory.isIrr_twist_and_repIso_of_twist_repIso _ _ n ka).1 r hirr)
  · have h1 : F x = 0 := hF hx
    change j (F x) = 0
    rw [h1, map_zero]
  · have h1 : Fr.w n b < Fr.w n a := by
      have h2 : (a : ℕ) < b := hab
      unfold Fr.w
      split_ifs <;> omega
    have h3 : (0 : ℤ) < e := by exact_mod_cast H.e_pos
    exact sub_lt_sub_left (mul_lt_mul_of_pos_left h1 h3) _
  · obtain ⟨χ, hχ, h1⟩ := ap_psi c e ψ L (Ω := Ω) (Fr.w n i)
    refine hwt v _ χ hχ _ fun g hg => Units.ext ?_
    have h2 : F (R.B₀.u.ψ v i g).val = (R.K.twψ ρ₂ v i g).val := congrArg (fun t => (t g).val) (hP v i)
    have h3 := hψ (R.K.e v) i (R.K.lam v g) ((R.K.lam_I v g).2 hg)
    rw [R.lam_j] at h3
    rw [Units.val_mul, ← h1, ← R.κ_pr]
    change j (F (R.B₀.u.ψ v i g).val) = _
    rw [h2]
    exact congrArg (fun t : A => t.1 * (R.K.κ (R.V.pr g)).val.1) h3
  · have h1 : W.UniversalOrdinaryDeterminantRing.Pt.D (j.comp F) = (W.GDet.ofRep (R.K.tw ρ₂)).map (j : c₂.O →+* Qbar l) :=
      congrArg (fun D => D.map (j : c₂.O →+* Qbar l)) hD
    refine (congrArg (fun D => D.comap R.V.pr) h1).trans (ap_det _ _ _ _ fun g => ?_)
    change (tw r ka g).val = _
    rw [tw_val, hr, ← R.κ_pr, ← R.π_pr]
    rfl
theorem UpperTheory.Gal.projectedFormsSystemPart.twoRuns_alt (hA : GlobalTheory.Published.GlobalArtinReciprocity) (hMod : _root_.UpperTheory.V.W.ModUAlt) (hLam : W.LamEx)
    {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {c : Coef l}
    [CharP (ResidueField c.O) l] {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N}
    {η : G ℚ Ω →* ℤˣ} {σ g₁ : G ℚ Ω} {B : ValuationSubring Ω} {M : ℕ} (H : LinkHyp c N e η σ B M)
    {L : Type} [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] {Φ : Fr.Frame l (ResidueField c.O)}
    {k : GalLink η (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) σ g₁ B M L Φ} (v : Φ.V)
    {c₁ : Coef l} [Fr.IsCoef l c₁.O] {f : ResidueField c.O →+* ResidueField c₁.O}
    {ka kb : G L Ω →* (Qbar l)ˣ} (hL : W.Large L c₁) (ha : IsKa σ M ι 2 ka) (hb : IsKa σ M ι 3 kb)
    (e₂ : ∀ p₀ : ℕ, p₀ ≠ 0 → ∃ R : CReal k c₁ f 2 ka, ¬ R.s.p ∣ p₀)
    (e₃ : ∀ p₀ : ℕ, p₀ ≠ 0 → ∃ R : CReal k c₁ f 3 kb, ¬ R.s.p ∣ p₀)
    (s₂ : ∀ (R : CReal k c₁ f 2 ka) J, R.B₀.PointTheoremBaseObject ι J → R.T.IdealSpecializationPoint J)
    (s₃ : ∀ (R : CReal k c₁ f 3 kb) J, R.B₀.PointTheoremBaseObject ι J → R.T.IdealSpecializationPoint J) :
    FinPt c₁.O (Φ.ext f) 3 ∧ _root_.UpperTheory.V.Pr.AutPtAlt k 3 ι kb ∧ _root_.UpperTheory.V.Pr.AutPtAlt k 2 ι ka := by
  have one : ∀ (R₂ : CReal k c₁ f 2 ka) (R₃ : CReal k c₁ f 3 kb), FinPt c₁.O (Φ.ext f) 3 ∧
      _root_.UpperTheory.Gal.projectedFormsSystemPart.AutPtOAlt R₃.s.v0 k 3 ι kb ∧ _root_.UpperTheory.Gal.projectedFormsSystemPart.AutPtOAlt R₂.s.v0 k 2 ι ka := fun R₂ R₃ => by
    obtain ⟨J₂, h₂, d₂⟩ := _root_.UpperTheory.V.Pr.modularity_linked_ends hMod hLam ι H v R₂ hL (s₂ R₂)
    obtain ⟨J₃, h₃, d₃⟩ := _root_.UpperTheory.V.Pr.modularity_linked_ends hMod hLam ι H v R₃ hL (s₃ R₃)
    obtain ⟨g₂, g₃, hfin⟩ := UpperTheory.V.Pr.absMain l c₁.O _ R₂.T R₃.T J₂ J₃ h₂ h₃
    exact ⟨hfin, _root_.UpperTheory.Gal.projectedFormsSystemPart.autPtO_alt hA Ω l ι c N e ψ η σ g₁ B M H L Φ k c₁ f 3 _ R₃ hb J₃ g₃ d₃,
      _root_.UpperTheory.Gal.projectedFormsSystemPart.autPtO_alt hA Ω l ι c N e ψ η σ g₁ B M H L Φ k c₁ f 2 ka R₂ ha J₂ g₂ d₂⟩
  obtain ⟨R₂, -⟩ := e₂ 1 one_ne_zero
  obtain ⟨R₃, -⟩ := e₃ 1 one_ne_zero
  obtain ⟨R₂', n₂⟩ := e₂ R₂.s.p R₂.s.p_prime.ne_zero
  obtain ⟨R₃', n₃⟩ := e₃ R₃.s.p R₃.s.p_prime.ne_zero
  obtain ⟨hfin, a₃, a₂⟩ := one R₂ R₃
  obtain ⟨-, b₃, b₂⟩ := one R₂' R₃'
  exact ⟨hfin, fun A _ _ _ ρ h1 h2 r h3 h4 => _root_.UpperTheory.Gal.projectedFormsSystemPart.glueN (by norm_num) (UpperTheory.Gal.projectedFormsSystemPart.v0_ne n₃)
      (a₃ A ρ h1 h2 r h3 h4) (b₃ A ρ h1 h2 r h3 h4),
    fun A _ _ _ ρ h1 h2 r h3 h4 => _root_.UpperTheory.Gal.projectedFormsSystemPart.glueN (by norm_num) (UpperTheory.Gal.projectedFormsSystemPart.v0_ne n₂)
      (a₂ A ρ h1 h2 r h3 h4) (b₂ A ρ h1 h2 r h3 h4)⟩
end
