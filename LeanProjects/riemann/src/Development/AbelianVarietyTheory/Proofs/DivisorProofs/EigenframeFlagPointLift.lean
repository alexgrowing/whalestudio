import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LnStepFalse
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedPointRelationFieldExt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DualGramInterpGram
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj
open GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.Toroidal GlobalTheory.LocM.Frm GlobalTheory.HeightParts
open GlobalTheory.GradedNorm GlobalTheory.LieHt
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LieSmooth

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagPtDescent

theorem exists_factor_of_fixed {K : Type} [Field K] (io : K →+* Qb) {R : Type} [CommRing R] (ψ : R →+* Qb)
    (h : ∀ γ : Qb ≃+* Qb, (γ : Qb →+* Qb).comp io = io → (γ : Qb →+* Qb).comp ψ = ψ) :
    ∃ ψK : R →+* K, io.comp ψK = ψ := by
  letI := io.toAlgebra
  haveI hcl : IsAlgClosure ℚ Qb := algebraicClosure.isAlgClosure ℚ ℂ
  haveI : IsAlgClosed Qb := hcl.isAlgClosed
  haveI : CharZero K := RingHom.charZero io
  haveI : Algebra.IsAlgebraic ℚ Qb := hcl.isAlgebraic
  haveI : Algebra.IsAlgebraic K Qb := Algebra.IsAlgebraic.tower_top (K := ℚ) K
  haveI : IsAlgClosure K Qb := ⟨inferInstance, inferInstance⟩
  haveI : IsGalois K Qb := IsAlgClosure.isGalois K Qb
  have hmem : ∀ r, ψ r ∈ io.range := fun r => by
    have h1 : ψ r ∈ (⊥ : IntermediateField K Qb) := (InfiniteGalois.mem_bot_iff_fixed (ψ r)).2 fun γ =>
      RingHom.congr_fun (h γ.toRingEquiv (RingHom.ext fun a => γ.commutes a)) r
    obtain ⟨a, ha⟩ := IntermediateField.mem_bot.1 h1
    exact ⟨a, ha⟩
  let e : K ≃+* io.range := RingEquiv.ofBijective io.rangeRestrict
    ⟨fun a b hab => io.injective (congrArg Subtype.val hab), io.rangeRestrict_surjective⟩
  refine ⟨e.symm.toRingHom.comp (ψ.codRestrict io.range hmem), RingHom.ext fun r => ?_⟩
  have := congrArg Subtype.val (e.apply_symm_apply (ψ.codRestrict io.range hmem r))
  exact this

end GlobalTheory.FlagPtDescent

namespace GlobalTheory.FlagPtDescent

open GlobalTheory.ShFam

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}

theorem tri_descent {R K L : Type} [CommRing R] [Field K] [Field L] {φ₁ : c.F →+* R} {x₁ : Sp R ⟶ Z.X}
    (f : EigFrame Z φ₁ x₁) (ψK : R →+* K) (io : K →+* L) {fK : c.F →+* K} {xK : Sp K ⟶ Z.X} (g : EigFrame Z fK xK)
    {φL : c.F →+* L} {xL : Sp L ⟶ Z.X} {gL : EigFrame Z φL xL} {t' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Lˣ}
    (hg : g.IsMap io gL) (hT : f.Tri (io.comp ψK) gL t') (hφ : fK = ψK.comp φ₁) (hx : xK = spMap ψK ≫ x₁) :
    ∃ t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Kˣ, f.Tri ψK g t := by
  obtain ⟨f', hf'⟩ := f.exists_isMap ψK hφ hx
  have hφL : φL = io.comp fK := by rw [hT.2.1, hφ]; rfl
  have hxL : xL = spMap io ≫ xK := by
    rw [hT.1, hx, ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap_comp, Category.assoc]
  obtain ⟨f'', hf''⟩ := f'.exists_isMap io hφL hxL
  have hff : f.IsMap (io.comp ψK) f'' := fun τ i => by
    rw [hf'' τ i, hf' τ i, GlobalTheory.GradedPieces.dual_comp]
  have key := fun τ => hT.co τ hff
  have hm := fun τ => EigFrame.IsMap.co τ hf'' hg hxL
  have hz : ∀ τ a i, i < a → f'.co g τ a i = 0 := fun τ a i h => io.injective (by
    rw [map_zero, ← Matrix.map_apply (f := io), ← hm τ]; exact (key τ).1 a i h)
  have hd : ∀ τ i, f'.co g τ i i ≠ 0 := fun τ i h0 => (t' τ i).ne_zero (by
    rw [← (key τ).2 i, hm τ, Matrix.map_apply, h0, map_zero])
  refine ⟨fun τ i => Units.mk0 _ (hd τ i), hx, hφ, fun τ i => ⟨fun a => f'.co g τ a i, rfl, fun k hk => hz τ k i hk, ?_⟩⟩
  rw [← funext (hf' τ)]
  exact f'.co_spec g τ i

end GlobalTheory.FlagPtDescent

namespace GlobalTheory.LieSmooth

open GlobalTheory.FlagPtDescent

theorem basePt_definedOver : ∀ {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {s : FinalTheorems S κ} (Φ : s.Flag) (y : Pt s) {K : Type} [Field K] [NumberField K] (io : K →+* Qb) (fK : κ.c.F →+* K) (yK : Sp K ⟶ gen s.T.Z), spMap io ≫ yK = y.y → yK ≫ genStr s.T.Z = spMap fK → ∀ g : EigFrame s.T.Z fK (yK ≫ genι s.T.Z), g.IsMap io y.frame → ∃ p : Sp K ⟶ (Φ.C (compPt s y)).Y.X, p ≫ (Φ.C (compPt s y)).π = yK ∧ (Φ.C (compPt s y)).Carries p g ∧ below p = basePt Φ y := by
  intro D A N j S κ s Φ y K _ _ io fK yK hy hstr g hg
  haveI : IsAlgClosed Qb := (algebraicClosure.isAlgClosure ℚ ℂ).isAlgClosed
  obtain ⟨p₀, hp₀π, hp₀c, hp₀b⟩ := liesUnder_basePt Φ y
  have hfK : y.fK = io.comp fK := EigLoc.spMap_inj (by
    rw [← y.y_over, ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap_comp, ← hstr, ← hy, Category.assoc])
  have hfix : ∀ γ : Qb ≃+* Qb, (γ : Qb →+* Qb).comp io = io → spMap (γ : Qb →+* Qb) ≫ p₀ = p₀ := by
    intro γ hγ
    have hyγ : y.y = spMap (γ : Qb →+* Qb) ≫ y.y := by
      rw [← hy, ← Category.assoc, ← ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap_comp, hγ]
    have hfr : y.frame.IsMap (γ : Qb →+* Qb) y.frame := fun τ i => by
      rw [hg τ i, GlobalTheory.GradedPieces.dual_comp, hγ]
    have hc := GlobalTheory.GalCarryBC.carries_map _ (γ : Qb →+* Qb) hp₀c hfr
      (by rw [hfK, ← RingHom.comp_assoc, hγ]) (by rw [← Category.assoc, ← hyγ])
    obtain ⟨_, _, hu⟩ := Φ.lifts Qb y.fK y.y y.y_over y.frame
    have h1 := hu ⟨compPt s y, spMap (γ : Qb →+* Qb) ≫ p₀⟩
      ⟨by rw [Category.assoc, hp₀π, ← hyγ], hc⟩
    have h2 := hu ⟨compPt s y, p₀⟩ ⟨hp₀π, hp₀c⟩
    exact eq_of_heq (Sigma.mk.inj (h1.trans h2.symm)).2
  obtain ⟨y₁, ψ, φ₁, f, t, t', hp₀, hf0, hfy⟩ := hp₀c
  have hψ : ∀ γ : Qb ≃+* Qb, (γ : Qb →+* Qb).comp io = io → (γ : Qb →+* Qb).comp ψ = ψ := by
    intro γ hγ
    apply EigLoc.spMap_inj
    haveI : Mono (stalkPt (Φ.C (compPt s y)).Y y₁) := inferInstanceAs (Mono (Scheme.fromSpecStalk _ y₁))
    apply (cancel_mono (stalkPt (Φ.C (compPt s y)).Y y₁)).1
    rw [ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap_comp, Category.assoc, ← hp₀, hfix γ hγ]
  obtain ⟨ψK, hψK⟩ := exists_factor_of_fixed io ψ hψ
  have hp₀' : p₀ = spMap io ≫ spMap ψK ≫ stalkPt (Φ.C (compPt s y)).Y y₁ := by
    rw [hp₀, ← hψK, ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap_comp, Category.assoc]
  haveI : Epi (spMap io) := Flat.epi_of_flat_of_surjective _
  have hπ : (spMap ψK ≫ stalkPt (Φ.C (compPt s y)).Y y₁) ≫ (Φ.C (compPt s y)).π = yK := by
    apply (cancel_epi (spMap io)).1
    rw [hy, ← hp₀π, hp₀']
    simp only [Category.assoc]
  refine ⟨spMap ψK ≫ stalkPt (Φ.C (compPt s y)).Y y₁, hπ, ?_, ?_⟩
  · have hφ : fK = ψK.comp φ₁ := by
      apply RingHom.ext
      intro a
      apply io.injective
      have := RingHom.congr_fun hfy.2.1 a
      rw [hfK, ← hψK] at this
      exact this
    have hx : yK ≫ genι s.T.Z = spMap ψK ≫ stalkPt (Φ.C (compPt s y)).Y y₁ ≫ (Φ.C (compPt s y)).π ≫ genι s.T.Z := by
      rw [← hπ]; simp only [Category.assoc]
    rw [← hψK] at hfy
    obtain ⟨t'', ht''⟩ := tri_descent f ψK io g hg hfy hφ hx
    exact ⟨y₁, ψK, φ₁, f, t, t'', rfl, hf0, ht''⟩
  · rw [← hp₀b, hp₀']
    show (spMap ψK ≫ stalkPt _ y₁) (IsLocalRing.closedPoint K) =
      (spMap io ≫ spMap ψK ≫ stalkPt _ y₁) (IsLocalRing.closedPoint Qb)
    show _ = (spMap ψK ≫ stalkPt _ y₁) ((spMap io) (IsLocalRing.closedPoint Qb))
    congr 1
    exact Subsingleton.elim _ _

end GlobalTheory.LieSmooth

end
