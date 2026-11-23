import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.StGlob
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalOperatorActsByLocalComponentScalarStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceUnitaryLocalPointsEquivGL
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open MeasureTheory GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

private theorem exists_map_eq {α : Type} {a : ℕ} (B : Multiset α) (hB : Multiset.card B = a) :
    ∃ z : Fin a → α, Finset.univ.val.map z = B := by
  obtain ⟨l, rfl⟩ := Quotient.exists_rep B
  have hl : l.length = a := hB
  subst hl
  exact ⟨l.get, by rw [Fin.univ_val_map, List.ofFn_get]; rfl⟩

theorem UpperTheory.Gal.Gen.globOp_pf :
    UpperTheory.Gal.Gen.LocOp → UpperTheory.Gal.Gen.GlobOp := by
  classical
  intro hLoc E _ _ _ a K w hw hK
  obtain ⟨C, hC⟩ := hLoc E w a
  refine ⟨C, fun p hp => ?_⟩
  obtain ⟨h, hdist, hsum, hact⟩ := hC p hp
  let zf : SmIrr (GL (Fin a) (w.adicCompletion E)) → ℂ := fun σ =>
    if hz : ∃ z : Fin a → ℂˣ, GlobalTheory.LFun.HasSatGL w σ.ρ (Finset.univ.val.map z) then evalAt hz.choose p else 0
  have hop : ∀ (σ : SmIrr (GL (Fin a) (w.adicCompletion E))), ∀ v ∈ GlobalTheory.PRep.fixed σ.ρ (GlobalTheory.LFun.KGL w a),
      opOf σ.ρ h v = zf σ • v := by
    intro σ v hv
    by_cases hv0 : v = 0
    · subst hv0
      simp [opOf]
    · obtain ⟨B, hB⟩ := GlobalTheory.SatInd.exists_hasSatGL_of_isIrreducible σ.smooth σ.irred
        ((Submodule.ne_bot_iff _).2 ⟨v, hv, hv0⟩)
      obtain ⟨z, rfl⟩ := exists_map_eq B (GlobalTheory.LFun.HasSatGL.card hB)
      have hz : ∃ z : Fin a → ℂˣ, GlobalTheory.LFun.HasSatGL w σ.ρ (Finset.univ.val.map z) := ⟨z, hB⟩
      have hzf : zf σ = evalAt hz.choose p := dif_pos hz
      rw [hzf]
      exact hact σ _ hz.choose_spec v hv
  obtain ⟨hKo, hKc⟩ := GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL (E := E) w a
  obtain ⟨h', hsup, hU⟩ := GlobalTheory.T.localOperator_acts_by_localComponentScalar E a w hw (GlobalTheory.LFun.KGL w a) hKc hKo h zf hop
  obtain ⟨e, he⟩ := GlobalTheory.locU_equiv_GL E a w hw
  have hinj : ∀ g ∈ locU a w, ∀ g' ∈ locU a w, cLoc w g = cLoc w g' → g = g' := by
    intro g hg g' hg' hgg
    have : (⟨g, hg⟩ : locU a w) = ⟨g', hg'⟩ := e.injective (by rw [he, he]; exact hgg)
    exact congrArg Subtype.val this
  have hmem : ∀ g ∈ h'.support, cLoc w g ∈ h.support := by
    intro g hg
    rw [Finsupp.mem_support_iff, ← (hsup g hg).2]
    exact Finsupp.mem_support_iff.1 hg
  refine ⟨h', fun g hg => (hsup g hg).1, ?_, ?_, ?_⟩
  · intro g hg g' hg' hgK
    have hl : g⁻¹ * g' ∈ locU a w := (locU a w).mul_mem ((locU a w).inv_mem (hsup g hg).1) (hsup g' hg').1
    have hk := (hK _ hl).1 hgK
    rw [map_mul, map_inv] at hk
    exact hinj g (hsup g hg).1 g' (hsup g' hg').1 (hdist _ (hmem g hg) _ (hmem g' hg') hk)
  · refine le_trans ?_ hsum
    have h1 : ∑ g ∈ h'.support, ‖h' g‖ ^ 2 = ∑ x ∈ h'.support.image (cLoc w), ‖h x‖ ^ 2 := by
      rw [Finset.sum_image fun g hg g' hg' hgg => hinj g (hsup g hg).1 g' (hsup g' hg').1 hgg]
      exact Finset.sum_congr rfl fun g hg => by rw [(hsup g hg).2]
    rw [h1]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => by positivity
    intro x hx
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.1 hx
    exact hmem g hg
  · rintro U hUa z ⟨σ, hcomp, hsat⟩ φ hφ hfix
    rw [hU U hUa σ hcomp φ hφ fun x hx hk => hfix x ((hK x hx).2 hk)]
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hsat.1
    have h1 := hop σ v hv
    rw [hact σ z hsat v hv] at h1
    rw [smul_left_injective ℂ hv0 h1]
