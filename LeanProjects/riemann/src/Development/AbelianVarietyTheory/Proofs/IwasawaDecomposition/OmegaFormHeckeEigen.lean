import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.FWTie
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FibExtMarked
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AnalyticFibreDescriptionLevelMoveMarkingComp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AnalyticFibreMatching
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EtaCharacterUnramified
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaFormIntegrality
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SymplecticBasesMatched
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrthonormalNegFirstFamilyFrameCartanMove
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeMarkingAdmissible
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaMultiplierUnitary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFinUnitIsDetRoot
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilVacuumFiniteSelfDualLatticeSplittingStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaFormNonvanishing
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaFormGaloisEquivariance
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelActionMemCuspFormsOfActionLaws
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RealPeriodMapHomeomorphRiemannFormDensity
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts

namespace GlobalTheory.OneMapRef.Equivar

open CategoryTheory MonObj in

theorem marked_congr {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} [Algebra c.F ℂ] {r g : ℕ} {X : Data E r}
    {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} {idx : Fin g ≃ X.Ψ × Fin r} {e : Fin g ≃ Lt1 Dw} {x : Frame X.Ψ r}
    {L : Lt E r} {y : FrPt Xo c ℂ} (A : AnFib X bas idx e x L y) {mk mk' : Dw.La →ₗ[𝓞 E] (Fin r → E)}
    (h : A.Marked mk) (hc : ∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La), ∃ u ∈ L, mk' a = mk a + l.M • u) :
    A.Marked mk' := by
  intro a ha
  obtain ⟨u, hu, e'⟩ := hc a ha
  have hM : (l.M : E) ≠ 0 := by have := l.three_le; exact_mod_cast (by omega : l.M ≠ 0)
  have hadd : ∀ u v, pv X idx x (u + v) = pv X idx x u + pv X idx x v := fun u v => by
    unfold pv; rw [per_add]; rfl
  rw [h a ha, e', smul_add, ← Nat.cast_smul_eq_nsmul E, inv_smul_smul₀ hM, hadd, A.ex_add,
    (A.ex_ker _).2 ⟨u, hu, rfl⟩, _root_.mul_one]

variable {D : D7} {S T : HSp D} {r g g' : ℕ}

theorem latW_injective (hr : T.rank = r) : Function.Injective (latW (D := D) (T := T) hr) := by
  subst hr
  intro L L' h
  ext v
  exact SetLike.ext_iff.1 h v

theorem sameSp_of_isSet {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {hr : T.rank = r} {X X' : Data D.host.E r}
    {eT : D.what₂.Tau ≃ X.Ψ} {eT' : D.what₂.Tau ≃ X'.Ψ} {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ}
    {bas' : (Fin g' ⊕ Fin g' → ℤ) ≃ₗ[ℤ] X'.Λ} (h : IsSet ψ θ S T hr X eT bas) (h' : IsSet ψ θ S T hr X' eT' bas')
    (hp : X'.p0 = X.p0) : SameSp X' X := by
  obtain ⟨-, -, -, -, hm, hk, he, -⟩ := h
  obtain ⟨-, -, -, -, hm', hk', he', -⟩ := h'
  refine ⟨?_, hm'.1.trans hm.1.symm, hp, hm'.2.trans hm.2.symm, hk'.trans hk.symm⟩
  ext τ
  constructor
  · intro hτ
    obtain ⟨ρ, hρ⟩ := eT'.surjective ⟨τ, hτ⟩
    have : τ = (eT ρ).1 := by rw [he, ← he', hρ]
    exact this ▸ (eT ρ).2
  · intro hτ
    obtain ⟨ρ, hρ⟩ := eT.surjective ⟨τ, hτ⟩
    have : τ = (eT' ρ).1 := by rw [he', ← he, hρ]
    exact this ▸ (eT' ρ).2

theorem symm_eq_of_isSet {X X' : Data D.host.E r} {eT : D.what₂.Tau ≃ X.Ψ} {eT' : D.what₂.Tau ≃ X'.Ψ}
    (he : ∀ ρ, (eT ρ).1 = tauE D ρ) (he' : ∀ ρ, (eT' ρ).1 = tauE D ρ) (τ : D.host.E →+* ℂ) (h : τ ∈ X.Ψ)
    (h' : τ ∈ X'.Ψ) : eT'.symm ⟨τ, h'⟩ = eT.symm ⟨τ, h⟩ := by
  rw [Equiv.symm_apply_eq]
  refine Subtype.ext ?_
  rw [he', ← he, Equiv.apply_symm_apply]

theorem exists_real_ne_zero {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {hr : T.rank = r} {X : Data D.host.E r}
    {eT : D.what₂.Tau ≃ X.Ψ} {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} (h : IsSet ψ θ S T hr X eT bas)
    (idx : Fin g ≃ X.Ψ × Fin r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) {L : Lt D.host.E r} {th : (Fin g → ℂ) → ℂ}
    (hm : MeanOne X bas idx x L th) : ∃ w : WO S T, Ker.IsRealPt w ∧
      Ker.gaussR X bas idx x (Ker.zR X idx x (rePt θ hr eT w)) * ∏ b, th (Ker.zR X idx x (rePt θ hr eT w) b) ≠ 0 := by
  obtain ⟨-, hθ, -, hev, -, -, -, hs⟩ := h
  obtain ⟨z, hz⟩ : ∃ z, th z ≠ 0 := by
    by_contra hc
    push Not at hc
    obtain ⟨_, _, -, -, h3⟩ := hm
    simp [hc] at h3
  have hq : X.p0 + (r - X.p0) = r := by have := X.p0_le; omega
  obtain ⟨⟨Lz, hL⟩, -⟩ := GlobalTheory.Ker.zR_laws _ r X g _ hq bas idx S.rank hs hev x hx
  obtain ⟨v, hv⟩ := Lz.surjective fun _ => z
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  have hw : rePt θ hr eT (Matrix.of fun a k => σ fun ρ => v (eT ρ) k (Fin.cast hr a) : WO S T) = v := by
    funext τ k a
    have := hσ.comp (fun ρ => v (eT ρ) k (Fin.cast hr (Fin.cast hr.symm a))) (eT.symm τ)
    refine this.trans ?_
    rw [Equiv.apply_symm_apply]
    rfl
  refine ⟨Matrix.of fun a k => σ fun ρ => v (eT ρ) k (Fin.cast hr a), Matrix.ext fun a k => hσ.fin _, ?_⟩
  rw [hw, ← hL, hv]
  exact mul_ne_zero (Complex.exp_ne_zero _) (Finset.prod_ne_zero_iff.2 fun _ _ => hz)

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem compare {σ : c.F →+* ℂ} (hA : l.A = 1) {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {hr : T.rank = r}
    {ι : Dw.La →ₗ[𝓞 D.host.E] (Fin T.rank → D.host.E)} (hι : LatEmb T ι) {X X' : Data D.host.E r}
    {eT : D.what₂.Tau ≃ X.Ψ} {eT' : D.what₂.Tau ≃ X'.Ψ} {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ}
    {bas' : (Fin g' ⊕ Fin g' → ℤ) ≃ₗ[ℤ] X'.Λ} {idx : Fin g ≃ X.Ψ × Fin r} {idx' : Fin g' ≃ X'.Ψ × Fin r}
    {e : Fin g ≃ Lt1 Dw} {e' : Fin g' ≃ Lt1 Dw} (hS : IsSet ψ θ S T hr X eT bas) (hS' : IsSet ψ θ S T hr X' eT' bas')
    (hM : Matched c σ X idx e) (hM' : Matched c σ X' idx' e') (hp : X'.p0 = X.p0) (hD : SelfD X X.Λ)
    (hD' : SelfD X' X'.Λ) {δ a' : GA D T} (hδ : δ ∈ GQ T) (hL : latW hr X.Λ = latG T (δ * a'))
    (hL' : latW hr X'.Λ = latG T a') {Z : Fam T} (hZ : IsONeg T X.p0 Z) {x : Frame X.Ψ r} {x' : Frame X'.Ψ r}
    (hx : x ∈ X.dom) (hx' : x' ∈ X'.dom) (ex : x = frOf hr eT (mvZ θ (δ * a') Z)) (ex' : x' = frOf hr eT' (mvZ θ a' Z)) :
    letI : Algebra c.F ℂ := σ.toAlgebra
    ∀ (y y' : FrPt Xo c ℂ) (A : AnFib X bas idx e x X.Λ y) (A' : AnFib X' bas' idx' e' x' X'.Λ y')
      (th : (Fin g → ℂ) → ℂ) (th' : (Fin g' → ℂ) → ℂ), A.Reads 1 y.s th → A'.Reads 1 y'.s th' →
      ∀ mk mk' : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E), (∀ a, mk a ∈ X.Λ) → (∀ a, mk' a ∈ X'.Λ) →
      MarkAd hr l ι (δ * a') mk → MarkAd hr l ι a' mk' → A.Marked mk → A'.Marked mk' →
      ∃ lam : ℂ, (∀ a n, ∀ f ∈ sec Xo c a n, evR Xo c f y' = lam ^ n * evR Xo c f y) ∧
        ∀ w : WO S T, Ker.IsRealPt w → ∃ w' : WO S T, Ker.IsRealPt w' ∧
          Ker.gaussR X' bas' idx' x' (Ker.zR X' idx' x' (rePt θ hr eT' w')) *
              ∏ b, th' (Ker.zR X' idx' x' (rePt θ hr eT' w') b) =
            lam ^ S.rank * (Ker.gaussR X bas idx x (Ker.zR X idx x (rePt θ hr eT w)) *
              ∏ b, th (Ker.zR X idx x (rePt θ hr eT w) b)) ∧
          ∀ (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)),
            IsWeilDatumO ψ S T χS χT om → ∀ f, IsThetaFunO ψ S T f → om (1, δ * a') f w = om (1, a') f w' := by
  letI : Algebra c.F ℂ := σ.toAlgebra
  intro y y' A A' th th' hth hth' mk mk' hmk hmk' hm hm' hAm hAm'
  have hX : SameSp X' X := sameSp_of_isSet hS hS' hp
  have hsy := symm_eq_of_isSet hS.2.2.2.2.2.2.1 hS'.2.2.2.2.2.2.1
  obtain ⟨ga, g1, g2, g3, g4, g5⟩ := GlobalTheory.OneMapRef.RatPt.rational_points D S T r g hr ψ θ X eT bas idx hS δ hδ
  obtain ⟨k1, k2⟩ := ((GlobalTheory.OneMapRef.markAd_laws D H Dw T r hr ι hι a' X'.Λ hL' l).2 mk' hmk' hm').2.2.2 δ ga g1
  have eL : mapL ga X'.Λ = X.Λ := latW_injective hr (k1.trans hL.symm)
  have eX : lact ga (castFr hX.psi x') = x := by
    have : castFr hX.psi x' = frOf hr eT (mvZ θ a' Z) := by
      rw [ex']
      funext τ a b
      simp only [castFr, frOf]
      rw [hsy τ.1 τ.2]
    rw [this, g3, ex, ((GlobalTheory.OneMapRef.oneg_frames D S T r g hr ψ θ X eT bas idx hS Z hZ).2.2.2.2 a').2.2.1 δ]
  have key := GlobalTheory.OneMapRef.anFib_move_renum D H Dw l Xo c σ r g g' X' X hX bas' idx' e' bas idx e hS'.2.2.2.2.2.2.2
    hS.2.2.2.2.2.2.2 hM' hM x' hx' X'.Λ hD' ga g2 y' A' th' hth'
  rw [eL, eX] at key
  obtain ⟨A₁, th₁, r1, r2, r3⟩ := key
  have hmem : ∀ a, mvMap ga mk' a ∈ X.Λ := fun a => eL ▸ ⟨mk' a, hmk' a, rfl⟩
  obtain ⟨m1, -, m3, -⟩ := (GlobalTheory.OneMapRef.markAd_laws D H Dw T r hr ι hι _ X.Λ hL l).2 _ hmem k2
  obtain ⟨lam, -, l2, l3⟩ := GlobalTheory.OneMapRef.exists_scalar_of_marked _ H Dw l Xo c r g X bas idx e x X.Λ hS.2.2.2.2.2.2.2 hx hD
    hA y y' A A₁ mk ((GlobalTheory.OneMapRef.markAd_laws D H Dw T r hr ι hι _ X.Λ hL l).2 _ hmk hm).1 hAm
    (marked_congr A₁ (r2 mk' hAm') (m3 l dvd_rfl le_rfl mk hmk hm)) th th₁ hth r1
  refine ⟨lam, l3, fun w hw => ?_⟩
  obtain ⟨w', hw', rfl⟩ := (g4 w).1 hw
  refine ⟨w', hw', ?_, fun χS χT om ho f hf => ?_⟩
  · rw [← r3 S.rank (rePt θ hr eT' w') (rePt θ hr eT (actO S T 1 δ w')), l2]
    · simp only [Pi.smul_apply, smul_eq_mul, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      ring
    · intro τ k
      rw [(g4 w').2]
      congr 1
      funext a
      simp only [rePt]
      rw [hsy τ.1 (hX.psi ▸ τ.2) τ.2]
  · have : ((1, δ * a') : GA D S × GA D T) = (1, δ) * (1, a') := by rw [Prod.mk_mul_mk, one_mul]
    rw [this, map_mul, Module.End.mul_apply]
    exact g5 χS χT om ho _ (ho.om_pres _ _ hf) w'

theorem rdU_eq {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (f : Rul Xo c) (k : U.Comp) {x : Frame (U.X k).Ψ r}
    (hx : x ∈ (U.X k).dom) : rdU U f k x = @evR _ _ _ _ _ _ _ Xo c f ℂ _ σ.toAlgebra (ptC U k ⟨x, hx⟩) :=
  dif_pos hx

end GlobalTheory.OneMapRef.Equivar
