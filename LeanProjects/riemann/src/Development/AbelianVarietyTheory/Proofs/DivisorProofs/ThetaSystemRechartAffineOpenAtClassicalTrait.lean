import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaSystemMovedToAffineOpenStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Points

namespace GlobalTheory.Poinc

theorem rechart_at_classical_trait : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (c : CTrait X₁ p z₁), ∃ (c₀ : X₁.Ω₁) (hc : c₀ ≠ 0) (R' : Subalgebra X₁.o₁ X₁.Ω₁) (fg : R'.FG) (frac : ∀ x : X₁.Ω₁, ∃ a ∈ R', ∃ b ∈ R', x = a / b) (hth : ∀ x, c₀ * X₁.S.th x ∈ R') (hev : ∀ x k, c₀ * X₁.S.ev x k ∈ R') (ρ' : (X₁.S.rechart c₀ hc R' fg frac hth hev).Real) (ε' : Matrix (Fin 8) (Fin 8) ℤ → (ρ'.P.A ⟶ ρ'.P.A)) (u' : Sp R' ⟶ F.X), Same X₁.ρ ε₁ ρ' ε' (fun x => x) (RingHom.id _) ∧ ρ'.i₀ = X₁.ρ.i₀ ∧ R' ≤ X₁.M.O ((gPt p ≫ c.y) (closedPoint (PadicAlgCl p))) ∧ IsDiagEnd F W ρ'.P u' ε' ∧ ∃ y₀ : R' →+* PadicAlgCl p, (∀ a : R', y₀ a = X₁.M.val (gPt p ≫ c.y) a) ∧ spMap y₀ ≫ u' = spMap c.ι ≫ c.T.y ∧ ∀ a : X₁.o₁, ‖y₀ (algebraMap X₁.o₁ R' a)‖ ≤ 1 := by
  intro g n F W Z i X₁ hg hn hodd himm he8 hth hproj ε₁ hdiag p _ z₁ c
  have h1 : X₁.π ((gPt p ≫ c.y) (closedPoint (PadicAlgCl p))) ∈ Set.range i := by
    have e1 := congrArg (fun f : Sp (PadicAlgCl p) ⟶ Z => f (closedPoint (PadicAlgCl p))) c.comm
    simp only [Scheme.Hom.comp_apply] at e1
    exact ⟨_, by simp only [Scheme.Hom.comp_apply]; exact e1.symm⟩
  obtain ⟨U, c₀, hc, fg, frac, hth', hev, ρ', ε', u', hU, hwU, -, hSame, hi₀, hdiag', hpt⟩ :=
    GlobalTheory.T.exists_thetaSystem_moved_to_affineOpen g n F W Z i X₁ hg hn hodd himm he8 hth hproj ε₁ hdiag _ h1
  set w := (gPt p ≫ c.y) (closedPoint (PadicAlgCl p)) with hw
  have hne : (U : Set X₁.M.Z).Nonempty := ⟨w, hwU⟩
  have hle : X₁.M.ringOn U ≤ X₁.M.O w := RatModel.ringOn_le_O hwU
  have hsp : ∀ w', (gPt p ≫ c.y) w' ⤳ w := fun w' => by
    rw [Subsingleton.elim w' (closedPoint (PadicAlgCl p))]
  let y₀ : X₁.M.ringOn U →+* PadicAlgCl p :=
    (RatModel.valHomOf (gPt p ≫ c.y) w hsp).comp (Subalgebra.inclusion hle).toRingHom
  have hy₀ : ∀ a : X₁.M.ringOn U, y₀ a = X₁.M.val (gPt p ≫ c.y) a := fun a => rfl

  let e : Sp (X₁.M.ringOn U) ⟶ X₁.M.Z :=
    Spec.map (CommRingCat.ofHom (X₁.M.sectionsEquiv U hne).toRingHom) ≫ hU.fromSpec
  have he : ∀ {K : Type} [CommRing K] (φ : X₁.M.ringOn U →+* K), ⊤ ≤ (spMap φ ≫ e) ⁻¹ᵁ U ∧
      ∀ f, valR (spMap φ ≫ e) U f = φ (X₁.M.sectionsEquiv U hne f) := by
    intro K _ φ
    have e2 : spMap φ ≫ e = Spec.map (CommRingCat.ofHom (φ.comp (X₁.M.sectionsEquiv U hne).toRingHom)) ≫
        hU.fromSpec := by
      rw [← Category.assoc, ← Spec.map_comp]; rfl
    rw [e2]
    have hx := le_preimage_specMap_fromSpec hU (CommRingCat.ofHom (φ.comp (X₁.M.sectionsEquiv U hne).toRingHom))
    refine ⟨hx, fun f => ?_⟩
    rw [valR_eq _ U hx, valMap_specMap_fromSpec]
    rfl
  have hyU : ⊤ ≤ (gPt p ≫ c.y) ⁻¹ᵁ U := (le_preimage_iff _ U).2 hwU
  have ha : spMap y₀ ≫ e = gPt p ≫ c.y := by
    refine ext_of_valR hU (he y₀).1 hyU fun f => ?_
    rw [(he y₀).2, hy₀, RatModel.coe_sectionsEquiv, RatModel.val_valF ((top_le_preimage_iff _ _).1 hyU)]
    rfl
  have hgen : spMap (X₁.M.ringOn U).val.toRingHom ≫ e = X₁.M.pt := by
    refine ext_of_valR hU (he _).1 (X₁.M.top_le_preimage_pt hne) fun f => ?_
    rw [(he _).2]
    exact (RatModel.coe_sectionsEquiv U hne f).trans (valF_eq_valR _ _ _)
  have hdom : IsDominant (spMap (X₁.M.ringOn U).val.toRingHom) :=
    ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2 (by
      rw [(RingHom.injective_iff_ker_eq_bot _).1 Subtype.val_injective]; exact bot_le)⟩
  haveI : IsSeparated X₁.z := X₁.isProper_compactificationMap.toIsSeparated
  have hgen2 : spMap (X₁.M.ringOn U).val.toRingHom ≫ (e ≫ X₁.π) =
      spMap (X₁.M.ringOn U).val.toRingHom ≫ (u' ≫ i) := by
    rw [← Category.assoc, hgen, X₁.comp, ← Category.assoc _ u' i, hpt, Category.assoc]
  have hb : e ≫ X₁.π = u' ≫ i :=
    ext_of_isDominant_of_isSeparated X₁.z
      (ext_of_isDominant (spMap (X₁.M.ringOn U).val.toRingHom) (by
        simp only [← Category.assoc] at hgen2 ⊢; rw [hgen2]))
      (spMap (X₁.M.ringOn U).val.toRingHom) hgen2
  haveI := himm
  have hpt' : spMap y₀ ≫ u' = spMap c.ι ≫ c.T.y := by
    rw [← cancel_mono i, Category.assoc, ← hb, ← Category.assoc, ha, Category.assoc, c.comm, Category.assoc]

  let τ := Spec.preimage (c.y ≫ X₁.M.s)
  have hσ : (gPt p ≫ c.y) ≫ X₁.M.s = spMap ((OO p).subtype.comp τ.hom) := by
    rw [Category.assoc, ← Spec.map_preimage (c.y ≫ X₁.M.s), ← Spec.map_comp]; rfl
  refine ⟨c₀, hc, X₁.M.ringOn U, fg, frac, hth', hev, ρ', ε', u', hSame, hi₀, hle, hdiag', y₀, hy₀, hpt',
    fun a => ?_⟩
  rw [hy₀]
  show ‖X₁.M.val (gPt p ≫ c.y) (algebraMap X₁.o₁ X₁.Ω₁ a)‖ ≤ 1
  rw [RatModel.val_algebraMap hσ a]
  exact (mem_OO_iff _).1 (τ.hom a).2

end GlobalTheory.Poinc
