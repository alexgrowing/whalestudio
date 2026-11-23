import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TameParahoricRepSplitsAsProduct
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.TraceQuot
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalDoubleCosets.OfSupportHolds
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsTorusEigenformOfCompactTorusEigenvectorStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.BernsteinZelevinskyFinitenessStatement
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.SubQuot
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.QuotEmb

open MeasureTheory NumberField IsDedekindDomain Filter ValuativeRel
open GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Loc GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open UpperTheory.Gal.LocD UpperTheory.Gal.InertialTypesAlt.G UpperTheory.Gal.Join
open scoped Classical

private theorem continuous_mulSingle_units {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] {n : ℕ} (i : Fin n) :
    Continuous (MonoidHom.mulSingle (fun _ : Fin n => kˣ) i) :=
  continuous_mulSingle (A := fun _ : Fin n => kˣ) i

theorem UpperTheory.Gal.Join.expSub :
    UpperTheory.Gal.Join.ExpSub := by
  intro k _ _ _ _ n V _ _ π hsm hirr μ hexp
  obtain ⟨y, hy0, hy⟩ := hexp
  have hJs : IsSmooth (jacB π) := isSmooth_jacB hsm
  have hμ : IsSmoothChar μ := by
    show IsOpen (μ.ker : Set (Fin n → kˣ))
    refine Subgroup.isOpen_of_mem_nhds μ.ker (g := 1) ?_
    refine Filter.mem_of_superset ((hJs y).mem_nhds (by simp)) ?_
    intro t ht
    have h1 : ((μ t : ℂˣ) : ℂ) • y = (1 : ℂ) • y := by
      rw [one_smul, ← hy t]
      exact ht
    have h2 : ((μ t : ℂˣ) : ℂ) = 1 := smul_left_injective ℂ hy0 h1
    simp only [SetLike.mem_coe, MonoidHom.mem_ker]
    exact Units.ext h2
  set ω : Fin n → kˣ →* ℂˣ := fun i => μ.comp (MonoidHom.mulSingle (fun _ : Fin n => kˣ) i) with hωdef
  have hωμ : torusChar ω = μ := by
    refine MonoidHom.ext fun t => ?_
    rw [torusChar_apply]
    simp only [hωdef, MonoidHom.comp_apply, MonoidHom.mulSingle_apply]
    rw [← map_prod, Finset.univ_prod_mulSingle]
  have hωs : ∀ i, IsSmoothChar (ω i) := fun i => hμ.comp _ (continuous_mulSingle_units i)
  have hlen : HasFiniteLength (jacB π) := by
    have hj := (GlobalTheory.T.bernstein_zelevinsky_finiteness k).2.1 (Fin n) (Fin n) (fun _ => Unit) (points (Fin n)) V π hsm
      (hasFiniteLength_of_isIrreducible hirr)
    exact (hasFiniteLength_comp_iff _ _ (leviTorus k (Fin n)).surjective).mpr hj
  obtain ⟨ψ, l, hl0, hl, hψω⟩ := GlobalTheory.T.exists_torusEigenform_of_compactTorus_eigenvector k n _ (jacB π) y ω hJs hlen hωs hy0
    (fun t _ => by rw [hy t, hωμ])
  have hψs : ∀ i, IsSmoothChar (ψ i) := fun i =>
    GlobalTheory.TameIwahori.isSmoothChar_of_eq_on_units (hωs i) (hψω i)
  have hsubψ : IsSubquotient π (prinSeries ψ) := quotEmb k n V π hsm hirr ψ l hl0 hl
  haveI : Nontrivial V := GroundTheory.Automorphic.RestrictedTensor.nontrivial_of_isIrreducible hirr
  have hcyc : Cyc (RingEquiv.refl k) 1 := ⟨fun _ => rfl, one_pos, fun _ => rfl⟩
  have hsemi : Semi (RingEquiv.refl k) π LinearMap.id := by
    intro g v
    simp [sg]
  have hinv : ∀ i, UpperTheory.Gal.LocD.Inv (RingEquiv.refl k) (ψ i) := by
    intro i x
    congr 1
  obtain ⟨-, hfd, -⟩ := locDesc_holds k n (RingEquiv.refl k) 1 hcyc V π hirr ψ hψs hinv hsubψ LinearMap.id hsemi
    (by
      intro h
      obtain ⟨v, hv⟩ := exists_ne (0 : V)
      exact hv (by simpa using LinearMap.congr_fun h v))
  haveI := hfd
  obtain ⟨l', hl'0, hl'⟩ := (subQuot (Fin n → kˣ) _ (jacB π) μ).2 ⟨y, hy0, hy⟩
  refine ⟨ω, hωμ.symm, hωs, quotEmb k n V π hsm hirr ω l' hl'0 ?_⟩
  intro t z
  rw [hωμ]
  exact hl' t z
