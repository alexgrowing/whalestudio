import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsDualDualRep
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LocalGaloisRepInvariantsFromFractionRing
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousAlgebraMapPadicInt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsJumpMultiset

namespace GlobalTheory.BKCup

section Bridge

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.BKDimNoInv
open ReciprocityTheory.Gal (cycZ)

variable {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] [IsAlgClosed Ω]
  {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  (Bw : LocBridge l E Ω Gw O) (P : LocPrime l)

theorem cycLL_eq (g : ↥(GK Bw.Kw)) :
    ((cycLL (P.PD Bw.Kw) ↥Bw.LL.1 g : (↥Bw.LL.1)ˣ) : ↥Bw.LL.1) =
      Bw.toLL (algebraMap ℤ_[l] O ((cycZ E Ω l (Bw.e.symm g : ↥Gw) : ℤ_[l]ˣ) : ℤ_[l])) := by
  change algebraMap ℚ_[l] ↥Bw.LL.1 (((P.PD Bw.Kw).χ g : ℚ_[l]ˣ) : ℚ_[l]) = _
  rw [P.PD_χ, ← GlobalTheory.BlockJumps.cycZ_eq_chi Bw P g]
  exact (congrArg Subtype.val (Bw.eO_alg _)).symm

theorem dot_dual {O L : Type} [CommRing O] [CommRing L] (φ : O →+* L) {m : ℕ} (A : GL (Fin m) O) (ε : O)
    (x y : Fin m → L) :
    ((A : Matrix (Fin m) (Fin m) O).map φ).mulVec x ⬝ᵥ
      ((ε • (A : Matrix (Fin m) (Fin m) O)⁻¹.transpose).map φ).mulVec y = φ ε * (x ⬝ᵥ y) := by
  have h1 : (ε • (A : Matrix (Fin m) (Fin m) O)⁻¹.transpose).map φ =
      φ ε • (((A : Matrix (Fin m) (Fin m) O)⁻¹).map φ).transpose := by
    ext a b
    simp
  have h2 : ((A : Matrix (Fin m) (Fin m) O)⁻¹).map φ * (A : Matrix (Fin m) (Fin m) O).map φ = 1 := by
    rw [← Matrix.map_mul, ← Matrix.coe_units_inv, Units.inv_mul, Matrix.map_one _ φ.map_zero φ.map_one]
  rw [h1, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose,
    Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]

set_option maxHeartbeats 1000000 in
theorem cup_cob {m : ℕ} (r r' : ↥Gw →* GL (Fin m) O)
    (hr : Continuous fun g => ((r g : GL (Fin m) O) : Matrix (Fin m) (Fin m) O))
    (hr' : Continuous fun g => ((r' g : GL (Fin m) O) : Matrix (Fin m) (Fin m) O))
    (hd : ∀ g, ((r' g : GL (Fin m) O) : Matrix (Fin m) (Fin m) O) =
      algebraMap ℤ_[l] O ((cycZ E Ω l (g : Ω ≃ₐ[E] Ω) : ℤ_[l]ˣ) : ℤ_[l]) •
        ((r g : GL (Fin m) O) : Matrix (Fin m) (Fin m) O)⁻¹.transpose)
    (hBK : bkACore (P.PD Bw.Kw)) (hdR : Bw.IsdRW P r)
    (c c' : ↥(GK Bw.Kw) → Fin m → ↥Bw.LL.1) (y y' : ↥Gw → Fin m → O)
    (hc : c ∈ finiteCocycles (P.PD Bw.Kw) (Bw.rep r)) (hc' : c' ∈ finiteCocycles (P.PD Bw.Kw) (Bw.rep r'))
    (hy : ∀ g a, c (Bw.e g) a = Bw.toLL (y g a)) (hy' : ∀ g a, c' (Bw.e g) a = Bw.toLL (y' g a)) :
    ∃ f : ↥Gw → ↥Bw.LL.1, Continuous f ∧ ∀ g h : ↥Gw,
      Bw.toLL (y g ⬝ᵥ ((r' g : GL (Fin m) O) : Matrix (Fin m) (Fin m) O).mulVec (y' h)) =
        Bw.toLL (algebraMap ℤ_[l] O ((cycZ E Ω l (g : Ω ≃ₐ[E] Ω) : ℤ_[l]ˣ) : ℤ_[l])) * f h - f (g * h) + f g := by
  have hG := (GlobalTheory.LocalIntegers.good_integers l Bw.LL).1
  let A := grepOf Bw r hr
  let A' := grepOf Bw r' hr'
  have hA : IsDR (P.PD Bw.Kw) A.ρ := by
    change Module.finrank ↥Bw.LL.1 ↥(DdR (P.PD Bw.Kw) (Bw.rep r)) =
      Module.finrank ℚ_[l] ↥Bw.Kw.1 * Module.finrank ↥Bw.LL.1 (Fin m → ↥Bw.LL.1)
    rw [Module.finrank_fin_fun]
    exact hdR
  let Q : (Fin m → ↥Bw.LL.1) →ₗ[↥Bw.LL.1] (Fin m → ↥Bw.LL.1) →ₗ[↥Bw.LL.1] ↥Bw.LL.1 :=
    dotProductBilin ↥Bw.LL.1 ↥Bw.LL.1
  have hD : IsDual1 (P.PD Bw.Kw) (Bw.rep r) (Bw.rep r') Q := by
    refine ⟨fun g x z => ?_, fun x hx => ?_, fun z hz => ?_, rfl⟩
    · change Bw.rep r g x ⬝ᵥ Bw.rep r' g z = _ * (x ⬝ᵥ z)
      rw [rep_apply, rep_apply, hd, dot_dual, cycLL_eq]
    · exact dotProduct_eq_zero x hx
    · exact dotProduct_eq_zero z fun x => (dotProduct_comm _ _).trans (hz x)
  obtain ⟨f, hf, hf'⟩ := (((hBK _ _ hG A A' Q hA hD).1 c hc.1).1 hc) c' hc'
  refine ⟨f ∘ Bw.e, hf.comp Bw.e_cont, fun g h => ?_⟩
  have h1 : ((cycLL (P.PD Bw.Kw) ↥Bw.LL.1 (Bw.e g) : (↥Bw.LL.1)ˣ) : ↥Bw.LL.1) * f (Bw.e h) - f (Bw.e g * Bw.e h) +
      f (Bw.e g) = c (Bw.e g) ⬝ᵥ Bw.rep r' (Bw.e g) (c' (Bw.e h)) := congrFun hf' (Bw.e g, Bw.e h)
  rw [cycLL_eq, rep_apply, MulEquiv.symm_apply_apply, ← map_mul] at h1
  refine Eq.trans ?_ h1.symm
  simp only [dotProduct, Matrix.mulVec, map_sum, map_mul, Matrix.map_apply, hy, hy']

end Bridge

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.Published.PoitouTate GlobalTheory.ResSel

theorem cup_coboundary : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), GalHyp bkP i s → ∀ ρ, IsDual i s ρ → ∀ (v : PlE D.host) (hv : v ∈ placesOver D.host.E (X.l i)) (c c' : ↥(Loc.GK (bkP.br i v hv).Kw) → Fin D.R.r → ↥(bkP.br i v hv).LL.1) (y y' : ↥(DecV N v) → Fin D.R.r → X.O0 i), c ∈ Formalism.WeaklyAdmissibleFiltrations.finiteCocycles (PDv bkP i v hv) (repV bkP i v hv (Tgl i s)) → c' ∈ Formalism.WeaklyAdmissibleFiltrations.finiteCocycles (PDv bkP i v hv) (repV bkP i v hv ρ) → (∀ g a, c ((bkP.br i v hv).e g) a = (bkP.br i v hv).toLL (y g a)) → (∀ g a, c' ((bkP.br i v hv).e g) a = (bkP.br i v hv).toLL (y' g a)) → ∃ f : ↥(DecV N v) → ↥(bkP.br i v hv).LL.1, Continuous f ∧ ∀ g h : ↥(DecV N v), (bkP.br i v hv).toLL (y g ⬝ᵥ ((ρ g : GL (Fin D.R.r) (X.O0 i)) : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)).mulVec (y' h)) = (bkP.br i v hv).toLL (algebraMap ℤ_[X.l i] (X.O0 i) ((cycZ D.host.E N.Om (X.l i) g : ℤ_[X.l i]ˣ) : ℤ_[X.l i])) * f h - f (g * h) + f g := by
  intro D N X bkP i s h ρ hρ v hv c c' y y' hc hc' hy hy'
  haveI : IsAlgClosed N.Om := IsAlgClosure.isAlgClosed D.host.E
  refine cup_cob (bkP.br i v hv) (D.loc (X.l i)) ((Tgl i s).comp (DecV N v).subtype) (ρ.comp (DecV N v).subtype)
    ?_ ?_ (fun g => ?_) (h.2.2.2.2.2.1 _ _).1 (h.1.2.1 v hv (Tgl i s) (Or.inr rfl)).1 c c' y y' hc hc' hy hy'
  · exact ((GlobalTheory.PrimeToInertia.continuous_Tmat i s).comp continuous_subtype_val).congr fun g => (Tgl_coe i s g).symm
  · exact ((GlobalTheory.PrimeToInertia.continuous_Tdual i s).comp continuous_subtype_val).congr fun g => (hρ g).symm
  · refine (hρ g).trans ?_
    rw [Tdual, ← Tgl_coe]
    rfl

end GlobalTheory.BKCup
