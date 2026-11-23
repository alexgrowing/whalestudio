import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PlainTorsionPairs.OffSelf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicPointGalois
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.BFixOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TNiceSmall
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.IsAutCsdA
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PlainTorsionPairs.IrrArithPointsAutomorphicAway
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ArithmeticPointClassicality

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr UpperTheory.V.Alg UpperTheory.V.J UpperTheory.V.Th
open private det_comap tw_flag unramified_at_base_place irr_of_mat pt_flag w_ne from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.NiceAt
namespace UpperTheory.Gal.projectedFormsSystemPart
private theorem la_move {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
    {A A' : ValuationSubring Ω} {w w' : W.Plc F} (h : IsPlaceOver A w) (h' : IsPlaceOver A' w') (e : A = A')
    (ψ : Fin n → Dec (F := F) A →* (Qbar l)ˣ) (ψ' : Fin n → Dec (F := F) A' →* (Qbar l)ˣ)
    (hψ : ∀ j (g : Dec (F := F) A) (g' : Dec (F := F) A'), (g : G F Ω) = (g' : G F Ω) → ψ j g = ψ' j g') (wt : Fin n → W.Emb l w → ℤ)
    (hm : ∀ τ, StrictMono fun j => wt j τ) (hl : ∀ j, W.IsLocAlg h (ψ j) (wt j)) :
    ∃ wt' : Fin n → W.Emb l w' → ℤ, (∀ τ, StrictMono fun j => wt' j τ) ∧ ∀ j, W.IsLocAlg h' (ψ' j) (wt' j) := by
  subst e
  obtain rfl : w = w' := IsDedekindDomain.HeightOneSpectrum.ext (Ideal.ext fun x => (h x).symm.trans (h' x))
  obtain rfl : ψ = ψ' := funext fun j => MonoidHom.ext fun g => hψ j g g rfl
  exact ⟨wt, hm, hl⟩
section
variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
  {η : G ℚ Ω →* ℤˣ} {Ψ : G ℚ Ω →* c.Oˣ} {σ g₁ : G ℚ Ω} {B : ValuationSubring Ω} {M : ℕ}
  {L : Type} [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] {Φ : Fr.Frame l (ResidueField c.O)}
  {k : GalLink η Ψ σ g₁ B M L Φ} {c₁ : Coef l} [Fr.IsCoef l c₁.O] {f : ResidueField c.O →+* ResidueField c₁.O}
  {ka : G L Ω →* (Qbar l)ˣ}
def EndPtAlt (R : CReal k c₁ f 3 ka) (ι : Qbar l ≃+* ℂ) (φ : R.B₀.B →ₐ[c₁.O] R.S.B) : Prop :=
  ∀ (h : R.s.Wt 3) (ξ : R.S.A →ₐ[c₁.O] Qbar l), VPt R.S ξ → R.S.u.TI (RingHom.ker ξ) →
    ∀ x : R.B₀.Pt, x = (ξ.comp R.S.inc).comp φ → x.Arith h → _root_.UpperTheory.V.Z.Win.IsAutCsdA ι ((R.K.tw (ptRep R.S ξ)).toHomUnits.comp R.V.pr)
private theorem psi_eq (R : CReal k c₁ f 3 ka) {φ : R.B₀.B →ₐ[c₁.O] R.S.B} (hφ : R.T.IsPhi φ) (ξ : R.S.A →ₐ[c₁.O] Qbar l) (v) :
    W.UniversalOrdinaryDeterminantRing.Pt.psi (B := R.B₀) ((ξ.comp R.S.inc).comp φ) v = R.K.twψ (ptRep R.S ξ) v :=
  funext fun i => (TwLink.IsPhi.maps R.K hφ ξ).2 v i
private theorem off_self (R : CReal k c₁ f 3 ka) {ι : Qbar l ≃+* ℂ} {φ : R.B₀.B →ₐ[c₁.O] R.S.B} (hφ : R.T.IsPhi φ)
    {J : Ideal R.B₀.B} (hg : AllGood R.S (J.map φ)) (hE : R.B₀.arithmeticPointClassicalityDense ι J) (h : R.s.Wt 3) (ξ : R.S.A →ₐ[c₁.O] Qbar l)
    (hV : VPt R.S ξ) (hTI : R.S.u.TI (RingHom.ker ξ)) (ha : W.UniversalOrdinaryDeterminantRing.Pt.Arith (B := R.B₀) ((ξ.comp R.S.inc).comp φ) h) :
    _root_.UpperTheory.Gal.projectedFormsSystemPart.AutOffN R.s.v0 ι ((R.K.tw (ptRep R.S ξ)).toHomUnits.comp R.V.pr) := by
  have hD : W.UniversalOrdinaryDeterminantRing.Pt.D (B := R.B₀) ((ξ.comp R.S.inc).comp φ) = W.GDet.ofRep (R.K.tw (ptRep R.S ξ)) :=
    (TwLink.IsPhi.maps R.K hφ ξ).1
  have hrep : W.UniversalOrdinaryDeterminantRing.Pt.IsRep (B := R.B₀) ((ξ.comp R.S.inc).comp φ) ((R.K.tw (ptRep R.S ξ)).toHomUnits.comp R.V.pr) := by
    refine (congrArg (fun D : W.GDet 3 (Qbar l) R.V.frame.G₀ => D.comap R.V.pr) hD).trans
      (det_comap (R.K.tw (ptRep R.S ξ)) R.V.pr (W.mat ((R.K.tw (ptRep R.S ξ)).toHomUnits.comp R.V.pr)) fun g => rfl)
  exact _root_.UpperTheory.Gal.projectedFormsSystemPart.end2oN R.v0 hE ((ξ.comp R.S.inc).comp φ) h _
    (fun b hb => hg _ (RingHom.ker_isPrime _) hTI (Ideal.mem_map_of_mem φ hb)) ha hrep
    (irr_of_mat _ R.V.pr (Pr.pr_surj R.V) (R.K.tw_irr _ (irrTI l c₁ _ R.C₀ 3 R.ok (Or.inr rfl) R.S ξ hV.1 hTI)))
private theorem kap (R : CReal k c₁ f 3 ka) (g : G L Ω) : R.K.κA (Qbar l) (R.V.pr g) = ka g := Units.ext (R.κ_pr g)
private theorem psi_j (ρ : Fr.NRep (Φ.ext f) 3 (Qbar l)) {u u' : Φ.V} (e : u = u') (j : Fin 3) (a : Φ.Gv u) (a' : Φ.Gv u')
    (h : (k.j u a).1 = (k.j u' a').1) : ρ.ψ u j a = ρ.ψ u' j a' := by
  subst e
  rw [k.j_inj u (Subtype.ext h)]
theorem endPt_of_allGood_of_arithmeticPointClassicality (R R₀ : CReal k c₁ f 3 ka) (hp : ¬ R₀.s.p ∣ R.s.p) {ι : Qbar l ≃+* ℂ} {φ : R.B₀.B →ₐ[c₁.O] R.S.B}
    (hφ : R.T.IsPhi φ) {J : Ideal R.B₀.B} (hg : AllGood R.S (J.map φ)) (hE : R.B₀.arithmeticPointClassicalityDense ι J)
    {φ' : R₀.B₀.B →ₐ[c₁.O] R.S.B} (hφ' : (setS R₀ R.S).T.IsPhi φ') {J' : Ideal R₀.B₀.B} (hg' : AllGood R.S (J'.map φ'))
    (hE' : R₀.B₀.arithmeticPointClassicalityDense ι J') : _root_.UpperTheory.Gal.projectedFormsSystemPart.EndPtAlt R ι φ := by
  rintro h ξ hV hTI _ rfl ha
  have key : ∀ v' : W.Vl l L, ∃ wt' : Fin 3 → W.Emb l (R₀.s.w v') → ℤ, (∀ τ, StrictMono fun j => wt' j τ) ∧
      ∀ j, W.IsLocAlg (R₀.s.hw v') (W.UniversalOrdinaryDeterminantRing.Pt.psi (B := R₀.B₀) ((ξ.comp R.S.inc).comp φ') v' j) (wt' j) := fun v' => by
    obtain ⟨v, hv⟩ : ∃ v : W.Vl l L, R.K.e v = R₀.K.e v' := R.K.e.surjective (R₀.K.e v')
    refine la_move (R.s.hw v) (R₀.s.hw v') ((R.A_pl v).trans ((congrArg k.pl hv).trans (R₀.A_pl v').symm)) _ _
      (fun j g g' e => ?_) (h v) (ha.1 v) (ha.2 v)
    rw [psi_eq R hφ ξ v, psi_eq (setS R₀ R.S) hφ' ξ v']
    change (ptRep R.S ξ).ψ (R.K.e v) j (R.K.lam v g) * R.K.κA (Qbar l) (R.V.pr g) =
      (ptRep R.S ξ).ψ (R₀.K.e v') j (R₀.K.lam v' g') * R₀.K.κA (Qbar l) (R₀.V.pr g')
    rw [kap, kap, e]
    exact congrArg (· * ka g') (psi_j (k := k) (ptRep R.S ξ) hv j (R.K.lam v g) (R₀.K.lam v' g')
      ((R.lam_j v g).trans ((congrArg (galEmb ℚ L Ω) e).trans (R₀.lam_j v' g').symm)))
  choose wt' h1 h2 using key
  have a := off_self R hφ hg hE h ξ hV hTI ha
  have b := off_self (setS R₀ R.S) hφ' hg' hE' wt' ξ hV hTI ⟨h1, h2⟩
  have e : ((setS R₀ R.S).K.tw (ptRep R.S ξ)).toHomUnits.comp (setS R₀ R.S).V.pr =
      (R.K.tw (ptRep R.S ξ)).toHomUnits.comp R.V.pr := MonoidHom.ext fun g => Units.ext (by
    change ((R₀.K.κA (Qbar l) (R₀.V.pr g) : (Qbar l)ˣ) : Qbar l) • (ptRep R.S ξ).r (R₀.K.π (R₀.V.pr g)) =
      ((R.K.κA (Qbar l) (R.V.pr g) : (Qbar l)ˣ) : Qbar l) • (ptRep R.S ξ).r (R.K.π (R.V.pr g))
    rw [kap, kap, R.π_pr, R₀.π_pr])
  exact _root_.UpperTheory.Gal.projectedFormsSystemPart.glueN (by norm_num) (v0_ne hp) a (e ▸ b)
end
theorem niceAt2_alt :
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (c : Coef l)
    [CharP (ResidueField c.O) l] (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N)
    (η : G ℚ Ω →* ℤˣ) (σ g₁ : G ℚ Ω) (B : ValuationSubring Ω) (M : ℕ), LinkHyp c N e η σ B M →
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] (Φ : Fr.Frame l (ResidueField c.O))
    (k : GalLink η (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) σ g₁ B M L Φ)
    (c₁ : Coef l) [Fr.IsCoef l c₁.O] (f : ResidueField c.O →+* ResidueField c₁.O)
    (ka : G L Ω →* (Qbar l)ˣ) (R : CReal k c₁ f 3 ka), W.Large L c₁ → IsKa σ M ι 3 ka →
    ∀ φ, R.T.IsPhi φ → _root_.UpperTheory.Gal.projectedFormsSystemPart.EndPtAlt R ι φ → ∀ (h : R.s.Wt 3) (ξ : R.S.A →ₐ[c₁.O] Qbar l), VPt R.S ξ →
      R.S.u.TI (RingHom.ker ξ) → ∀ x : R.B₀.Pt, x = (ξ.comp R.S.inc).comp φ → x.Good h →
      (Th.Free R.V.frame fun v => x.psi v) →
      _root_.UpperTheory.V.Th.AutomorphicPointLocallyGeneric ι x (R.K.tw (ptRep R.S ξ)).toHomUnits ∧ ∀ v, x.psi v = R.K.twψ (ptRep R.S ξ) v := by
  intro Ω _ _ _ l _ ι c _ N _ e ψ η σ g₁ B M H L _ _ _ _ _ Φ k c₁ _ f ka R _ _ φ hφ hJ h ξ hV hTI x hx hGood hFree
  have hn : (3 : ℕ) = 2 ∨ (3 : ℕ) = 3 := Or.inr rfl
  let ρQ : Fr.NRep (Φ.ext f) 3 (Qbar l) := ptRep R.S ξ
  let ρ0 : R.V.frame.G₀ →* GL (Fin 3) (Qbar l) := (R.K.tw ρQ).toHomUnits
  have hm : R.B₀.u.Maps ((ξ.comp (R.S.inc.comp φ) : R.B₀.B →ₐ[c₁.O] Qbar l) : R.B₀.B →+* Qbar l)
      (W.GDet.ofRep (R.K.tw ρQ)) (R.K.twψ ρQ) := TwLink.IsPhi.maps R.K hφ ξ
  have hxe : x = ξ.comp (R.S.inc.comp φ) := hx
  have hψ : ∀ v, x.psi v = R.K.twψ ρQ v := fun v => funext fun i => by
    rw [hxe]
    exact hm.2 v i
  have hD : W.UniversalOrdinaryDeterminantRing.Pt.D x = W.GDet.ofRep (R.K.tw ρQ) := by
    rw [hxe]
    exact hm.1
  have hcont : Continuous ρ0 := by
    have h1 : Continuous (R.K.tw ρQ) := by
      refine continuous_matrix fun a b => ?_
      have h2 := continuous_subtype_val.comp (((X.So.adicCont l c₁).2 _ _).1 R.K.κ_cont)
      have h3 := ((derRep l c₁ _ R.C₀ 3 R.ok hn R.S ξ hV.1 0 (Submodule.zero_mem _)).1 a b).comp R.K.π_cont
      exact h2.mul h3
    exact Units.continuous_iff.2 ⟨h1, h1.comp continuous_inv⟩
  have hirr : MatIrr ⊤ (W.mat ρ0) := R.K.tw_irr ρQ (irrTI l c₁ _ R.C₀ 3 R.ok hn R.S ξ hV.1 hTI)
  have hrep : W.UniversalOrdinaryDeterminantRing.Pt.IsRep x (ρ0.comp R.V.pr) := by
    refine (congrArg (fun D => D.comap R.V.pr) hD).trans (det_comap (R.K.tw ρQ) R.V.pr (W.mat (ρ0.comp R.V.pr)) fun g => rfl)
  have harith : W.UniversalOrdinaryDeterminantRing.Pt.Arith x h := ⟨hGood.1, fun v j => by
    obtain ⟨ph, hph, -⟩ := hGood.2 v
    exact ⟨ph j, hph j⟩⟩
  have hA : _root_.UpperTheory.V.Th.AutomorphicPointGalois ι x ρ0 := by
    refine ⟨hcont, hrep, ⟨h, harith⟩, hJ h ξ hV hTI x hx harith, ?_, fun v => ?_⟩
    · rintro _ ⟨g, hg, rfl⟩
      have h1 : R.K.π (R.V.pr g) = 1 := by
        rw [R.π_pr]
        exact unramified_at_base_place e ψ H.dvd k _ R.v0M g hg
      have h2 : R.K.κ (R.V.pr g) = 1 := R.K.ramκ _ ⟨g, hg, rfl⟩
      refine Units.ext ?_
      change ((R.K.κA (Qbar l) (R.V.pr g) : (Qbar l)ˣ) : Qbar l) • ρQ.r (R.K.π (R.V.pr g)) = 1
      have h3 : ((R.K.κA (Qbar l) (R.V.pr g) : (Qbar l)ˣ) : Qbar l) = 1 := by
        change algebraMap c₁.O (Qbar l) ((R.K.κ (R.V.pr g) : (↥c₁.O)ˣ) : c₁.O) = 1
        rw [h2, Units.val_one, map_one]
      rw [h1, map_one, h3, one_smul]
    · rw [hψ v]
      obtain ⟨g₀, hg⟩ := R.ok.f3 (R.K.e v)
      exact tw_flag R.K ρQ v (pt_flag R.S ξ hV hn _ g₀ hg)
  have hVne : Nonempty Φ.V := by
    by_contra hV'
    rw [not_nonempty_iff] at hV'
    have h' : _ < Φ.d := R.big.1
    simp [Fr.Frame.d] at h'
  obtain ⟨v'⟩ := hVne
  refine ⟨_root_.UpperTheory.V.Th.nice_zero_of_rank_two_or_three_irreducible_free ι x ρ0 hn hA hirr hFree ?_, hψ⟩
  obtain ⟨v, hv⟩ := R.K.e.surjective v'
  obtain ⟨s, hs⟩ := R.ok.f3 (R.K.e v)
  obtain ⟨g, rfl⟩ := (R.K.lam v).surjective s
  refine ⟨v, 0, 1, g, fun h' => w_ne hn _ hs 0 1 (by decide) ?_⟩
  rw [R.K.psib, R.K.psib, R.K.chib, R.K.chib, ← R.K.lam_loc] at h'
  exact mul_right_cancel h'
def Red2Alt : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (c : Coef l)
    [CharP (ResidueField c.O) l] (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N)
    (η : G ℚ Ω →* ℤˣ) (σ g₁ : G ℚ Ω) (B : ValuationSubring Ω) (M : ℕ), LinkHyp c N e η σ B M →
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] (Φ : Fr.Frame l (ResidueField c.O))
    (k : GalLink η (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) σ g₁ B M L Φ)
    (c₁ : Coef l) [Fr.IsCoef l c₁.O] (f : ResidueField c.O →+* ResidueField c₁.O)
    (ka : G L Ω →* (Qbar l)ˣ) (R : CReal k c₁ f 3 ka), W.Large L c₁ → IsKa σ M ι 3 ka →
    ∀ φ, R.T.IsPhi φ → Function.Surjective φ → ∀ J, AllGood R.S (J.map φ) → R.T.DimT J → R.B₀.Dense J →
      _root_.UpperTheory.Gal.projectedFormsSystemPart.EndPtAlt R ι φ → ∀ ξ : R.S.A →ₐ[c₁.O] Qbar l, IntPt R.S ξ → R.S.u.TI (RingHom.ker ξ) →
      ∀ a ∈ J, ∃ s : R.S.A, ξ s ≠ 0 ∧ s * R.S.inc (φ a) = 0
theorem red2_alt :
    GlobalTheory.Published.GlobalArtinReciprocity → _root_.UpperTheory.V.Th.DenseThresholdMainCase → _root_.UpperTheory.Gal.projectedFormsSystemPart.Red2Alt := by
  intro hG hC Ω _ _ _ l _ ι c _ N _ e ψ η σ g₁ B M hL L _ _ _ _ _ Φ k c₁ _ f ka R hW hK φ hPhi hSurj J hAll hDim hDense hEnd ξ hξ hTI a ha
  obtain ⟨h, hInc, hFree⟩ := wtEx hG Ω l ι c N e ψ η σ g₁ B M hL L Φ k c₁ f ka R hW hK
  have hNice := _root_.UpperTheory.Gal.projectedFormsSystemPart.niceAt2_alt Ω l ι c N e ψ η σ g₁ B M hL L Φ k c₁ f ka R hW hK φ hPhi hEnd h
  have hFix := _root_.UpperTheory.V.J.fixOf_alt hC Ω l ι c N e ψ η σ g₁ B M hL L Φ k c₁ f ka R hW hK
  have hN : IsNoetherianRing R.B₀.B := IsCO.toIsNoetherian (O := c₁.O)
  have hD : DenseB R.S (J.map φ) (fun y => W.UniversalOrdinaryDeterminantRing.Pt.Good (y.comp φ) h) :=
    @denseOf l _ c₁ R.B₀.B R.S.B _ hN _ _ _ φ J (1 + 3 * (Φ.ext f).d) (fun x => W.UniversalOrdinaryDeterminantRing.Pt.Good x h) hSurj hDim (hDense h hInc)
  refine redAbs l c₁ (Φ.ext f) R.C₀ 3 R.ok (Or.inr rfl) R.S (J.map φ) (fun y => W.UniversalOrdinaryDeterminantRing.Pt.Good (y.comp φ) h) hAll hD ?_ ξ hξ hTI (φ a) (Ideal.mem_map_of_mem _ ha)
  intro ζ hV hT _ hGd
  obtain ⟨h1, h2⟩ := hNice ζ hV hT _ rfl hGd (hFree _ hGd)
  exact fixLe l c₁ (Φ.ext f) R.C₀ 3 R.ok (Or.inr rfl) R.S ζ hV.1 hT (hFix ζ _ hV.1 h1 h2)
end UpperTheory.Gal.projectedFormsSystemPart
end
