import Development.WeilBound.CoreStatements.AutomorphicKernels.LocalGlobalCompatibility.TemperedLocalGlobal.WeilGroupRestriction.IwahoriCompatibilityOfChains
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FontaineParameterInvariantUnderConjugation
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PstAndWdAtOfIsRegAlg
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
import Development.WeilBound.CoreStatements.PublishedTheorems.FiniteGLInvariants.AffineLieInvariants.Imports
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPadicAlgClRingEquivComplexCompEqOfCountabl

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
open GlobalTheory GlobalTheory.GalOfCusp GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.Pst GlobalTheory.UnitaryBC GlobalTheory.HeckeGal Neutral.B1 Formalism.L2.Host Formalism.MainNotions.N
open PositivityTheory.Pf1.CLGD.DescRes

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Pf1.CLGD.K

namespace CharPolyRestriction

theorem natCast_mem_iff {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] {A : ValuationSubring Ω}
    {v : HeightOneSpectrum (𝓞 K)} (h : IsPlaceOver A v) (n : ℕ) :
    ((n : ℕ) : 𝓞 K) ∈ v.asIdeal ↔ A.valuation ((n : ℕ) : Ω) < 1 := by
  rw [← h ((n : ℕ) : 𝓞 K)]
  simp

theorem natCast_not_mem {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hne : q ≠ p) (hpv : ((p : ℕ) : 𝓞 K) ∈ v.asIdeal) :
    ((q : ℕ) : 𝓞 K) ∉ v.asIdeal := by
  intro hqv
  have hc : IsCoprime (p : ℤ) (q : ℤ) := Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hp hq).2 hne.symm)
  obtain ⟨u, t, hut⟩ := hc.map (Int.castRingHom (𝓞 K))
  have h1 : (1 : 𝓞 K) ∈ v.asIdeal := by
    rw [← hut]
    simp only [map_natCast]
    exact v.asIdeal.add_mem (v.asIdeal.mul_mem_left u hpv) (v.asIdeal.mul_mem_left t hqv)
  exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)

section

variable {E E' Ω : Type} [Field E] [NumberField E] [Field E'] [NumberField E'] [Field Ω]
  [Algebra E E'] [Algebra E Ω] [Algebra E' Ω] [IsScalarTower E E' Ω] [IsAlgClosure E Ω] [IsAlgClosure E' Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {w' : HeightOneSpectrum (𝓞 E')}
  (h : IsPlaceOver A w) (h' : IsPlaceOver A w')

theorem charPol_res (x : WD h) (t : Weil h') : WD.charPol (WD.res h h' x) t = WD.charPol x (resW h h' t) := by
  obtain ⟨m, b, rfl⟩ := WD.exists_rep x
  rw [WD.res_mk, WD.charPol_mk, WD.charPol_mk, resRep_ρ]

end

end CharPolyRestriction

open CharPolyRestriction in
theorem char_poly_restriction_holds : IwahoriLocalGlobal := by
  intro hG hB hL _k2c hCL k5 k6 k7 E Ω _ _ _ _ _ _ l _ ι a ha π hc hr r wt HT H P AI hT w hw A h O _ _ _ Bw hj σ hσ rc hrc U hU hU1
  obtain ⟨T⟩ := hT
  obtain ⟨Y, P', w', h', hrange, -, hLift⟩ := hCL E Ω a ha π hc hr A w h U hU

  obtain ⟨l', hl'ge, hl'p⟩ := Nat.exists_infinite_primes (l + 1)
  have : Fact l'.Prime := ⟨hl'p⟩
  have hne : l' ≠ l := by omega
  obtain ⟨ι'⟩ : Nonempty (Qbar l' ≃+* ℂ) := GlobalTheory.nonempty_padicAlgCl_ringEquiv_complex l'
  have hlw : ((l : ℕ) : 𝓞 E) ∈ w.asIdeal := hw
  have hl'w : ((l' : ℕ) : 𝓞 E) ∉ w.asIdeal := natCast_not_mem w (Fact.out) hl'p hne hlw
  have hl'w' : ((l' : ℕ) : 𝓞 Y.M) ∉ w'.asIdeal := by
    rw [natCast_mem_iff h', ← natCast_mem_iff h]
    exact hl'w

  obtain ⟨r1, wt1, HT1, H1⟩ := GlobalTheory.Published.GaloisRepOfPolarizedCuspidal.of_isCsd hG Ω ι' ha hr hc
  obtain ⟨r1', wt1', HT1', H1'⟩ := GlobalTheory.Published.GaloisRepOfPolarizedCuspidal.of_isCsd hG Ω ι' ha hLift.reg hLift.csd
  obtain ⟨p1, hp1⟩ := hLift.res l' ι' r1 wt1 HT1 r1' wt1' HT1' H1 H1'

  obtain ⟨σ', hσ', -⟩ := GlobalTheory.CuspRep.LocEx.exists_isLocComp CuspFormAutomorphicBounds.automorphicFormsFiniteGL Y.M a P' w'
  obtain ⟨rc', hrc', -⟩ := hL.1 Y.M Ω A w' h'

  have hx : IsWDOf ι' r1 (rc (algNorm σ)) := H1.away w hl'w A h rc hrc σ hσ
  have hres : IsWDOf ι' (r1.comp (resG E (E' := Y.M))) (WD.res h h' (rc (algNorm σ))) :=
    k5 E Ω Y l' a ι' r1 H1.cont A w h w' h' hl'w _ hx
  have hres' : IsWDOf ι' r1' (WD.res h h' (rc (algNorm σ))) :=
    IsWDOf.of_conj hl'w' p1 (fun g => by rw [MonoidHom.comp_apply, hp1 g, inv_mul_cancel_right]) hres
  have hx' : IsWDOf ι' r1' (rc' (algNorm σ')) := H1'.away w' hl'w' A h' rc' hrc' σ' hσ'
  have heq : rc' (algNorm σ') = WD.res h h' (rc (algNorm σ)) := IsWDOf.unique hl'w' hx' hres'

  have hfix : PRep.fixed σ'.ρ (SmGL.iwahori (w'.adicCompletion Y.M) (Fin a)) ≠ ⊥ := by
    refine k7 Y.M Ω A w' h' rc' hrc' a σ' fun t ht => ?_
    rw [heq, charPol_res]
    refine hU1 _ ?_ ?_
    · rw [← hrange]
      exact ⟨t, rfl⟩
    · rw [deg_resW, ht, mul_zero]

  obtain ⟨r2, wt2, HT2, H2⟩ := GlobalTheory.Published.GaloisRepOfPolarizedCuspidal.of_isCsd hG Ω ι ha hLift.reg hLift.csd
  obtain ⟨p2, hp2⟩ := hLift.res l ι r wt HT r2 wt2 HT2 H H2
  have hpst : IsPstAt P Bw (r.comp (Dec (F := E) A).subtype) := H.isPstAt hB T h Bw hj
  obtain ⟨O', _, _, _, Bw', hj', hpst', h6⟩ := k6 E Ω Y l a ι r H.cont P AI ⟨T⟩ A w h w' h' O Bw hj hpst
  obtain ⟨-, hconj⟩ := GlobalTheory.PstConj.main Y.M Ω l ι a P AI ⟨T⟩ w' A h' O' Bw' hj'
    ((r.comp (resG E (E' := Y.M))).comp (Dec (F := Y.M) A).subtype) (r2.comp (Dec (F := Y.M) A).subtype) p2
    (fun g => hp2 g) hpst'
  have hiw := ((H2.above P AI ⟨T⟩ w' A h' O' Bw' hj').iwahori σ' hσ' hfix).2 rc' hrc'
  refine ⟨Y, w', h', hrange, ?_⟩
  rw [← h6, ← hconj, hiw, heq]

end PositivityTheory.Pf1.CLGD.K

end
