import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.VuOntoA
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.VuOntoB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SerreHolomorphicSectionsHolds
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ToroidalFlagSmoothProjectiveStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexSectionFiniteCombinationStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolomorphicExtensionSectionReadingStatement

open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.CompanionTheory.Ar.OntoDef GlobalTheory.CompHS
open GlobalTheory.CompanionTheory.Ar.HolExt DifferentiableLines

noncomputable section

namespace PositivityTheory.UnitarySelfGeneration.VuOnto

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {r : ℕ} {σ : c.F →+* ℂ}

open GlobalTheory.CxPts

theorem exists_comb {V : Unf Xo c σ r} (hσ : GoodEmb c σ) (hU : IsUnf V) (T : TorFlag Xo c)
    {e : Ix D → ℤ} (he : e none = 0) {la : ∀ k, ReciprocityTheory.ChartRestriction.G.FD.Wt (V.X k).Ψ r} (hT : ∀ k, Tw V e k (la k))
    {P : ∀ k, Frame (V.X k).Ψ r → ℂ} (hP : ∀ k, P k ∈ (V.X k).SS (la k)) :
    ∃ (m : ℕ) (as : Fin m → ℂ) (fs : Fin m → Rul Xo c), (∀ i, fs i ∈ extVanZ T.X e) ∧
      ∀ k, ∀ x ∈ (V.X k).dom, P k x = ∑ i, as i * rdU V (fs i) k x := by
  classical
  letI := V.fin
  obtain ⟨-, g1, g2, -⟩ := GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H D l Xo c (CAt σ)
  obtain ⟨d, hsm, hpr⟩ := GlobalTheory.T.toroidal_flag_smooth_projective E H D l Xo c T
  let R : GlobalTheory.AnRead (flagStr T.X) σ d := GlobalTheory.AnRead.all _ _ _
  choose hk hf hR hZ using fun k => open_secZ hU T (hT k) (hP k).1.1
  have hh : ∀ k, hk k ∈ R.holSec (T.X.LL e) := fun k =>
    ⟨hf k, holoOn_bdZ hσ hU T he (hP k) R (hR k) (hZ k) (open_holoZ hσ hU T (hT k) (hP k).1.1 R (hR k) (hZ k))⟩
  let h : (T.X.LL e).ι → GlobalTheory.CxPts (flagStr T.X) σ → ℂ := ∑ k, hk k
  have hh' : h ∈ R.holSec (T.X.LL e) := Submodule.sum_mem _ fun k _ => hh k
  have hap : ∀ (i : (T.X.LL e).ι) y, h i y = ∑ k, hk k i y := fun i y => by simp only [h, Finset.sum_apply]
  have hv : ∀ i y, y ∉ ptsIn (flagStr T.X) σ (flagOpen T.X) → h i y = 0 := fun i y hy => by
    simp only [h, Finset.sum_apply]
    exact Finset.sum_eq_zero fun k _ => hZ k i y fun x hx e' => hy (mem_open_of_ptY T _ _ e')
  have hRh : ∀ k, Reads V T e k (P k) h := fun k x hx i y hz Q t hxy hQ ht => by
    have e₁ : h i y = hk k i y := by
      refine (hap i y).trans (Finset.sum_eq_single k (fun k' _ hne => hZ k' i y fun x' hx' e' => hne ?_)
        fun h' => (h' (Finset.mem_univ _)).elim)
      have e'' : T.X.ptY (V.un k' ⟨x', hx'⟩) = zOf y := e'
      have hlx : T.X.F.Lies (zOf y) (V.un k' ⟨x', hx'⟩) := e'' ▸ T.X.lies_ptY _
      obtain ⟨t', ht'⟩ := GlobalTheory.FlagMod.Frames.ChartFr.exists_frBor (z := zOf y) hQ hlx
      obtain ⟨γ, -, β, -, h'⟩ := (hU.2.2.2.1 k k' _ _).1 ⟨_, g1 _ _ _ _ _ (g2 _ _ _ ht) ht'⟩
      exact (Sigma.mk.inj h').1
    rw [e₁]
    exact hR k x hx i y hz Q t hxy hQ ht
  have hB := T.X.F.isLB_LL e
  obtain ⟨xC, hx⟩ := (GlobalTheory.AnRead.bijective_valC hpr R hB).2 ⟨h, hh'⟩
  have hxv : GlobalTheory.SecC.val xC = h := congrArg Subtype.val hx
  have hlft : LocallyOfFiniteType (flagStr T.X) := by
    haveI := hsm
    haveI : Smooth (flagStr T.X) := SmoothOfRelativeDimension.smooth d _
    infer_instance
  obtain ⟨m, as, ss, hss, hsum⟩ := GlobalTheory.T.complex_section_finite_combination c.F T.X.YY (flagStr T.X) σ hlft _ hB (flagOpen T.X) xC
    (fun i y hy => by rw [hxv]; exact hv i y hy)
  refine ⟨m, as, fun j => ruleTop T.X _ (GlobalTheory.Vanishing.H0.ofSec (flagStr T.X) ⊤ (ss j)), fun j => ?_,
    fun k => GlobalTheory.T.holomorphic_extension_section_reading E H D l Xo c r σ V T e k (P k) h (hRh k) m as ss (hxv.symm.trans hsum)⟩
  refine ruleTop_mem_extVanZ.2 (mem_vanOut_iff_le.2 ?_)
  have e' : toSec (GlobalTheory.Vanishing.H0.ofSec (flagStr T.X) ⊤ (ss j)) = ss j :=
    (Equiv.ofBijective _ GlobalTheory.Vanishing.H0.bijective_ofSec_top).symm_apply_apply (ss j)
  rw [e']
  exact hss j

end PositivityTheory.UnitarySelfGeneration.VuOnto
