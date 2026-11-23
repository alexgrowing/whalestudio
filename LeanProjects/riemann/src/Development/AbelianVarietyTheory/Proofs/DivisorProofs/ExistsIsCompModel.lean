import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueLiesUnder
import Development.AbelianVarietyTheory.Definitions.Divisors.EqOfSpecializesOfFinite
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBaseChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JGenSpecializes

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad

namespace GlobalTheory.Mean4O.CompModel

theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) :=
  (Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)).symm

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β} {F : Type} [Field F] {e : F ≃+* c.F}

theorem stalkPt_genStr (C : FlagCpt Z e) (z : C.Y.X) (φ : c.F →+* C.Y.X.presheaf.stalk z)
    (hφ : constF e C.Y = (algebraMap (C.Y.X.presheaf.stalk z) C.Y.X.functionField).comp φ) :
    stalkPt C.Y z ≫ C.π ≫ genStr Z = spMap φ := by
  let ρ : c.F →+* C.Y.X.presheaf.stalk z := (Spec.preimage (stalkPt C.Y z ≫ C.π ≫ genStr Z)).hom
  have h0 : spMap ρ = stalkPt C.Y z ≫ C.π ≫ genStr Z := Spec.map_preimage _
  let j := algebraMap (C.Y.X.presheaf.stalk z) C.Y.X.functionField
  letI := (constF e C.Y).toAlgebra
  have hgen : spMap j ≫ stalkPt C.Y z = genericPt C.Y :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk ((genericPoint_spec C.Y.X).specializes trivial)
  have h1 : spMap (j.comp ρ) = spMap (constF e C.Y) := by
    rw [← sp_comp, h0, ← Category.assoc, ← Category.assoc, hgen]
    exact (congrArg (· ≫ genStr Z) C.y0_x.symm).trans ((Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) Z.jQ_over).trans (pullback.lift_snd _ _ _)))
  have h2 : j.comp ρ = constF e C.Y := congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
  have h3 : ρ = φ := RingHom.ext fun r => IsFractionRing.injective (C.Y.X.presheaf.stalk z) C.Y.X.functionField
      ((RingHom.congr_fun h2 r).trans (RingHom.congr_fun hφ r))
  rw [← h0, h3]

theorem exists_flagPt (C : FlagCpt Z e) {K : Type} [Field K] (p : Sp K ⟶ C.Y.X) :
    ∃ y : FlagPt Z K, p ≫ C.π = y.y ∧ C.Carries p y.frame := by
  obtain ⟨φ, f, t, hT, -⟩ := C.gr_spec (below p)
  let ψ : C.Y.X.presheaf.stalk (below p) →+* K := (Scheme.stalkClosedPointTo p).hom
  have hp : p = spMap ψ ≫ stalkPt C.Y (below p) := (Scheme.Spec_stalkClosedPointTo_fromSpecStalk p).symm
  have hx : spMap ψ ≫ stalkPt C.Y (below p) ≫ C.π ≫ genι Z = (p ≫ C.π) ≫ genι Z := by
    rw [← Category.assoc, ← hp, Category.assoc]
  obtain ⟨g, hg⟩ : ∃ g : EigFrame Z (ψ.comp φ) ((p ≫ C.π) ≫ genι Z), ∀ τ i, g.v τ i = spMap (dualMap ψ) ≫ f.v τ i := by
    rw [← hx]
    exact EigFrame.exists_baseChange E H Dw l Xo c O β Z _ _ φ _ f ψ
  have ho : (p ≫ C.π) ≫ genStr Z = spMap (ψ.comp φ) := by
    rw [← sp_comp, ← stalkPt_genStr C _ φ hT.2.1, ← Category.assoc (spMap ψ), ← hp, Category.assoc]
  refine ⟨⟨ψ.comp φ, p ≫ C.π, ho, g.v, g.tan, g.eig, g.basis⟩, rfl, below p, ψ, φ, f, t, 1, hp, hT, hx.symm, rfl,
    fun τ i => ⟨Pi.single i 1, by simp, fun k hk => Pi.single_eq_of_ne hk.ne' _, ?_⟩⟩
  have := isCombAtG_single Z.t _ (g.tan τ) i
  rw [show (fun k => spMap (dualMap ψ) ≫ f.v τ k) = g.v τ from funext fun k => (hg τ k).symm]
  exact this

end Free

section Model

variable {F : Type} [Field F] [NumberField F] {Y : Var F} (M : TrueGeo.Model Y)

theorem dense_image_j (S : Set Y.X) : Dense (M.j '' S) ↔ Dense S := by
  have := M.ar.isIntegral
  have := SmallSec.isPreimmersion_j M
  have hd : DenseRange M.j := fun x =>
    (genericPoint_specializes x).mem_closed isClosed_closure
      (subset_closure (SmallSec.mem_range_j M (SmallSec.asIdeal_p_gen M)))
  exact (IsDenseInducing.mk M.j.isEmbedding.isInducing hd).dense_image

theorem irreducible_fibre {K : Type} [Field K] (σ : F →+* K) :
    IrreducibleSpace ↥(pullback M.p (spMap (σ.comp (algebraMap (𝓞 F) F)))) := by
  have h := ((IsPullback.of_hasPullback Y.str (spMap σ)).paste_horiz M.pb)
  rw [sp_comp] at h
  have : IsIntegral (pullback Y.str (spMap σ)) :=
    GeometricallyIntegral.geometrically_isIntegral (f := Y.str) _ _ _ (IsPullback.of_hasPullback Y.str (spMap σ))
  exact h.isoPullback.hom.homeomorph.irreducibleSpace_iff.1 inferInstance

theorem isAlgPt_iff {K : Type} [Field K] (ε : K ≃+* AlgebraicClosure ℚ) (x : M.X) :
    IsAlgPt x ↔ ∃ p : Sp K ⟶ Y.X, M.j (below p) = x := by
  have hb {K K' : Type} [Field K] [Field K'] (a : K →+* K') (p : Sp K ⟶ Y.X) : below (spMap a ≫ p) = below p :=
    congrArg p (Subsingleton.elim (α := PrimeSpectrum K) _ _)
  constructor
  · intro hx
    let σ : F →+* AlgebraicClosure ℚ := (IsAlgClosed.lift (R := ℚ) (S := F) (M := AlgebraicClosure ℚ)).toRingHom
    obtain ⟨z, rfl⟩ := exists_geomPt M.ar (σ.comp (algebraMap (𝓞 F) F)) hx
    have hz : z.1 ≫ M.p = spMap σ ≫ spMap (algebraMap (𝓞 F) F) := by rw [sp_comp]; exact z.2
    refine ⟨spMap ε.symm.toRingHom ≫ M.pb.lift z.1 (spMap σ) hz, ?_⟩
    rw [hb]
    exact congrArg (fun q : Sp (AlgebraicClosure ℚ) ⟶ M.X => q (IsLocalRing.closedPoint _)) (M.pb.lift_fst z.1 (spMap σ) hz)
  · rintro ⟨p, rfl⟩
    rw [← hb ε.toRingHom p]
    let q := spMap ε.toRingHom ≫ p
    exact GeomPt.isAlgPt (ι := (Spec.preimage ((q ≫ M.j) ≫ M.p)).hom) M.ar ⟨q ≫ M.j, (Spec.map_preimage _).symm⟩

end Model

theorem exists_isCompModel : ∀ (D : D7) (O : Setup D) (A : SlopeTestRemainingChoices O.Y), O.IsFlagHeightData A → ∀ (c : O.s.Comp) (M : TrueGeo.Model (O.var c)) (hM : IsArithVar M.p (Formalism.MainNotions.WeightThresholdDefs.dimY O.Y)), ∃ b : O.Y.Pt → M.X, (∀ y : ShFam.Pad.Pt O.s, ShFam.Pad.compPt O.s y = c → b y = M.j (baseOn O.Φ c y)) ∧ IsCompModel A c (@ArMod.mk _ (𝓞 D.what₂.LL) _ M.X hM.isIntegral M.p hM) b := by
  intro D O A hA c M hM
  have : IsAlgClosure ℚ Qb := algebraicClosure.isAlgClosure ℚ ℂ
  have : IsAlgClosure ℚ (AlgebraicClosure ℚ) := ⟨inferInstance, AlgebraicClosure.isAlgebraic ℚ⟩
  let ε : Qb ≃+* AlgebraicClosure ℚ := (IsAlgClosure.equiv ℚ Qb (AlgebraicClosure ℚ)).toRingEquiv
  refine ⟨fun y : ShFam.Pad.Pt O.s => M.j (baseOn O.Φ c y), fun _ _ => rfl, ⟨_, irreducible_fibre M
    (IsAlgClosed.lift (R := ℚ) (S := D.what₂.LL) (M := AlgebraicClosure ℚ)).toRingHom⟩, ?_, fun Z => ?_⟩
  · refine Set.ext fun x : M.X => Iff.trans ?_ (isAlgPt_iff M ε x).symm
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain rfl : compPt O.s y = c := hy
      obtain ⟨p, -, -, hp⟩ := liesUnder_basePt O.Φ y
      exact ⟨p, congrArg M.j hp⟩
    · rintro ⟨p, rfl⟩
      obtain ⟨y, h₁, h₂⟩ := exists_flagPt (O.Φ.C c) p
      have h : LiesUnder O.Φ c y (below p) := ⟨p, h₁, h₂, rfl⟩
      obtain rfl : compPt O.s y = c := h.compPt_eq
      exact ⟨y, rfl, congrArg M.j ((existsUnique_liesUnder O.Φ y).unique (liesUnder_basePt O.Φ y) h)⟩
  · refine (hA.dense c Z).trans (and_congr Iff.rfl ?_)
    exact (dense_image_j M _).symm.trans (iff_of_eq (congrArg Dense (Set.image_image _ _ (Z : Set (ShFam.Pad.Pt O.s)))))

end GlobalTheory.Mean4O.CompModel
