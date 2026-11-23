import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBaseFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLieCombIffIsCombAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalRingPointDualNumberSndLinearDerivation
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

namespace GlobalTheory.LogPole

theorem spMap_comp_spMap' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]; rfl

theorem sp_ext_ev {R S : Type} [CommRing R] [CommRing S] {z z' : Sp S ⟶ Sp R} (h : ⊤ ≤ z ⁻¹ᵁ ⊤)
    (h' : ⊤ ≤ z' ⁻¹ᵁ ⊤) (e : ∀ a, ev z ⊤ h a = ev z' ⊤ h' a) : z = z' := by
  rw [← FlagMod.spMap_ev z (isAffineOpen_top _) h, ← FlagMod.spMap_ev z' (isAffineOpen_top _) h']
  congr 2
  exact RingHom.ext e

theorem ev_spMap_top {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (h : ⊤ ≤ (spMap f) ⁻¹ᵁ ⊤)
    (h₀ : ⊤ ≤ (𝟙 (Sp R)) ⁻¹ᵁ ⊤) (a : Γ(Sp R, ⊤)) : ev (spMap f) ⊤ h a = f (ev (𝟙 (Sp R)) ⊤ h₀ a) := by
  have e := FlagMod.ev_spMap f (𝟙 (Sp R)) ⊤ h₀ (by simpa using h)
  rw [FlagMod.ev_congr (Category.comp_id (spMap f)).symm ⊤ h (by simpa using h), e]
  rfl

end GlobalTheory.LogPole

open GlobalTheory.LogPole in

theorem GlobalTheory.LogPole.exists_tanPt_of_logDer : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (TF : TorFlag Xo c) (U : TF.Y.X.affineOpens) (D : LogKS.logDer TF.Y.s (Scheme.IdealSheafData.vanishingIdeal (LogKS.interior TF.Y).compl) U) (K : Type) [Field K] [Algebra c.F K] (P₀ : FrPt Xo c K) (hU : ⊤ ≤ (frX P₀ ≫ TF.Y.j) ⁻¹ᵁ U.1), ∃ (y' : Sp (DualNumber K) ⟶ Xo.XF c) (hU' : ⊤ ≤ (y' ≫ TF.Y.j) ⁻¹ᵁ U.1), y' ≫ pullback.snd _ _ = spMap (algebraMap c.F (DualNumber K)) ∧ spMap (FlagTan.red c K).toRingHom ≫ y' = frX P₀ ∧ ∀ r, ev (y' ≫ TF.Y.j) U.1 hU' r = TrivSqZeroExt.inl (ev (frX P₀ ≫ TF.Y.j) U.1 hU r) + TrivSqZeroExt.inr (ev (frX P₀ ≫ TF.Y.j) U.1 hU (D.1 r)) := by
  intro E _ _ _ H Dw l Xo c TF U D K _ _ P₀ hU
  set φ := ev (frX P₀ ≫ TF.Y.j) U.1 hU with hφ
  let θ : Γ(TF.Y.X, U.1) →+* DualNumber K :=
    { toFun := fun r => TrivSqZeroExt.inl (φ r) + TrivSqZeroExt.inr (φ (D.1 r))
      map_one' := by ext <;> simp
      map_mul' := fun a b => by
        ext
        · simp
        · simp [Derivation.leibniz, smul_eq_mul]; ring
      map_zero' := by ext <;> simp
      map_add' := fun a b => by ext <;> simp <;> ring }
  have hθ : ∀ r, θ r = TrivSqZeroExt.inl (φ r) + TrivSqZeroExt.inr (φ (D.1 r)) := fun _ => rfl
  let z : Sp (DualNumber K) ⟶ TF.Y.X := spMap θ ≫ U.2.fromSpec
  have hred : spMap (FlagTan.red c K).toRingHom ≫ z = frX P₀ ≫ TF.Y.j := by
    have e : (FlagTan.red c K).toRingHom.comp θ = φ := RingHom.ext fun r => by simp [hθ]
    rw [← Category.assoc, spMap_comp_spMap', e]
    exact FlagMod.spMap_ev _ U.2 hU
  have hint : Set.range z ⊆ Set.range TF.Y.j := by
    have h1 : ⊤ ≤ z ⁻¹ᵁ TF.Y.j.opensRange :=
      le_preimage_of_dualNumber _ z _ (by rw [hred]; rintro s -; exact ⟨frX P₀ s, rfl⟩)
    rintro _ ⟨s, rfl⟩
    exact h1 (Set.mem_univ s)
  let y' := IsOpenImmersion.lift TF.Y.j z hint
  have hy' : y' ≫ TF.Y.j = z := IsOpenImmersion.lift_fac _ _ _
  have hzU : ⊤ ≤ z ⁻¹ᵁ U.1 := FlagMod.le_preimage_comp (spMap θ) (FlagMod.tau_le U.2 le_rfl)
  have hU' : ⊤ ≤ (y' ≫ TF.Y.j) ⁻¹ᵁ U.1 := by rw [hy']; exact hzU
  have hevz : ev z U.1 hzU = θ := FlagMod.ev_spMap_tau U.2 θ hzU

  have hjs : TF.Y.j ≫ TF.Y.s = pullback.snd _ _ := by
    rw [Model.j, Category.assoc, pullback.condition, ← Category.assoc, TF.Y.jQ_over]
    exact (congrArg (_ ≫ ·) (Spec.map_id _)).trans (Category.comp_id _)
  have htop : ∀ {S : Type} [CommRing S] (w : Sp S ⟶ Sp c.F), ⊤ ≤ w ⁻¹ᵁ ⊤ := fun _ => fun _ _ => trivial
  have hUs : U.1 ≤ TF.Y.s ⁻¹ᵁ ⊤ := fun _ _ => trivial
  refine ⟨y', hU', ?_, ?_, fun r => ?_⟩
  ·
    have e1 : y' ≫ pullback.snd _ _ = z ≫ TF.Y.s := by rw [← hjs, ← Category.assoc, hy']
    rw [e1]
    refine sp_ext_ev (htop _) (htop _) fun a => ?_
    rw [← FlagMod.ev_appLE z TF.Y.s hUs hzU (htop _) a, hevz, hθ]
    have hc : (TF.Y.s.appLE ⊤ U.1 hUs).hom a =
        constFn TF.Y.s U.1 ((Scheme.ΓSpecIso (CommRingCat.of c.F)).hom.hom a) := by
      simp only [constFn]
      congr 1
      simp
    have hD : D.1 ((TF.Y.s.appLE ⊤ U.1 hUs).hom a) = 0 := by rw [hc]; exact D.2.1 _
    rw [hD, map_zero, TrivSqZeroExt.inr_zero, add_zero, hφ,
      FlagMod.ev_appLE (frX P₀ ≫ TF.Y.j) TF.Y.s hUs hU (htop _) a,
      FlagMod.ev_congr (show (frX P₀ ≫ TF.Y.j) ≫ TF.Y.s = spMap (algebraMap c.F K) by
        rw [Category.assoc, hjs, FlagMod.frX_snd]) ⊤ (htop _) (htop _),
      ev_spMap_top _ (htop _) (fun _ _ => trivial), ev_spMap_top _ (htop _) (fun _ _ => trivial), TrivSqZeroExt.algebraMap_eq_inl']
  · rw [← cancel_mono TF.Y.j, Category.assoc, hy', hred]
  · rw [FlagMod.ev_congr hy' U.1 hU' hzU, hevz]
    exact hθ r
