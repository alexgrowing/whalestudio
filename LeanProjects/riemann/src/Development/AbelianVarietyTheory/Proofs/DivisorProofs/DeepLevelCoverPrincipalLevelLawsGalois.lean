import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.CongModRefl
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RuleBaseChangeSectionValuesSemilinear
import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.ComplexMultiplication.ExtEmbEquivComp

set_option autoImplicit false

noncomputable section

open NumberField Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CovTop GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC

namespace GlobalTheory.DeepLaws

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem isGalois_of_aut (K L : IntermediateField ℚ ℂ) [FiniteDimensional ℚ L] (j : K →+* L)
    (hj : ∀ a : K, ((j a : L) : ℂ) = a)
    (hs : ∀ s : ℂ ≃+* ℂ, (∀ a ∈ K, s a = a) → ∀ a ∈ L, s a ∈ L) :
    letI : Algebra K L := j.toAlgebra
    IsGalois K L := by
  letI : Algebra K L := j.toAlgebra
  haveI : IsScalarTower K L ℂ := IsScalarTower.of_algebraMap_eq fun a => (hj a).symm
  haveI : IsScalarTower ℚ K L := IsScalarTower.of_algebraMap_eq fun a => by simp
  haveI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.tower_top (K := ℚ) K
  have : Normal K L := by
    refine normal_iff.2 fun x => ⟨Algebra.IsIntegral.isIntegral x, ?_⟩
    refine Polynomial.Splits.of_splits_map (algebraMap L ℂ) (IsAlgClosed.splits _) fun a ha => ?_
    have hroot : a ∈ (minpoly K x).rootSet ℂ := by
      rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq] at ha
      exact Finset.mem_coe.2 (Multiset.mem_toFinset.2 ha)
    rw [← Algebra.IsAlgebraic.range_eval_eq_rootSet_minpoly] at hroot
    obtain ⟨φ, rfl⟩ := hroot
    obtain ⟨s, hsφ⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.extendEmb_holds L inferInstance (φ.restrictScalars ℚ)
    have hfix : ∀ a ∈ K, s a = a := by
      intro a ha
      have h1 := hsφ (j ⟨a, ha⟩)
      rw [hj] at h1
      refine h1.trans ?_
      exact φ.commutes (⟨a, ha⟩ : K)
    have hmem : s (x : ℂ) ∈ L := hs s hfix _ x.2
    refine ⟨⟨s (x : ℂ), hmem⟩, ?_⟩
    exact hsφ x
  exact IsGalois.mk

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
  {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l}

theorem frPt_eq {S : Type} [CommRing S] [Algebra c.F S] {y z : FrPt Xo c S} (hx : y.x = z.x) (hu : y.u = z.u)
    (hs : HEq y.s z.s) : y = z := by
  obtain ⟨x, xo, u, t, e, b, s, g⟩ := y
  obtain ⟨x', xo', u', t', e', b', s', g'⟩ := z
  obtain rfl : x = x' := hx
  obtain rfl : u = u' := hu
  obtain rfl : s = s' := eq_of_heq hs
  rfl

theorem laws_galois_pull : ∀ (D : D7) (T : CoreJ D) (j : ℕ) (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), LawsJ T → InR D j → Y.Good e o → (∀ σ, GoodEmb Y.d.c₂ σ → ∀ g τ k, ‖dmin ((Y.U σ).X (Y.dict σ g).1).Gm (Y.dict σ g).2 τ k‖ = 1) → (∀ σ, GoodEmb Y.d.c₂ σ → ∃ hr : (D.sp.W j).rank = D.R.r, ∀ k, ModelW (D.sp.W j) hr ((Y.U σ).X k)) → Laws D j Y.d.Xo₂ Y.d.c₂ Y.U Y.dict ∧ (letI : Algebra T.Q.c.F Y.d.c₂.F := ((Y.d.eF : Y.c'.F →+* Y.d.c₂.F).comp (incF T.Q.c Y.c' Y.hle)).toAlgebra; IsGalois T.Q.c.F Y.d.c₂.F) ∧ ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ sec (T.Q.Xo j) T.Q.c a n, ∀ g, Y.Pull f g ↔ Pull Y.d (rulBC Y.hle f) g := by
  intro D T j Y e o hJ hj hG hdm hmod
  refine ⟨?_, ?_, ?_⟩
  · exact
      { inR := hj
        host := hJ.pins.1
        dat := hJ.pins.2.2.2 j hj
        levA := hG.lev.2
        unf := hG.unf
        chiTriv := hG.chiTriv
        dictU := fun σ hσ => by
          obtain ⟨th, hr, h1, h2⟩ := hG.dictU σ hσ
          refine ⟨Y.Kf, th, hr, ?_, h1, h2, hdm σ hσ⟩
          have hM : Y.d.l₂.M = D.host.g 0 * D.host.g 1 * Y.d.pd := by
            rw [hG.lev.1.2.1, hJ.pins.2.1.1]
          rw [hM]
          exact hG.levelK
        modelW := hmod }
  · haveI := Y.d.c₂.fin
    refine isGalois_of_aut T.Q.c.F Y.d.c₂.F _ (fun a => rfl) fun s hs a ha => ?_
    have hF := Y.d.hF
    rw [hF] at ha ⊢
    exact hG.normal s hs a ha
  · intro a n f hf g
    have hV := (rulBC_sec_val_linear D.host.E T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c Y.c' Y.hle).1 a n f hf
    constructor
    · intro hP k _ _ _ _ hk y₂ y hO
      letI : Algebra T.Q.c.F k := resAlg Y.hle k
      have hA : AlgOver T.Q.c Y.c' Y.hle k := fun _ => rfl
      rw [hV.2 k hA y]
      exact hP k hA hk y₂ y (y.res Y.hle hA) hO rfl rfl HEq.rfl
    · intro hP k _ _ _ _ _ hA hk y₂ y' y hO hx hu hs
      have hy : y = y'.res Y.hle hA := frPt_eq hx hu hs
      rw [hy, ← hV.2 k hA y']
      exact hP k hk y₂ y' hO

end GlobalTheory.DeepLaws

end
