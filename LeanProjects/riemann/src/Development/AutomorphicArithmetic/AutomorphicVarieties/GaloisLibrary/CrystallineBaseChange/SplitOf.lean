import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.BcStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.BcAtt0
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.BcDual0
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.PlaceOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.WdAway
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.RecInv
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AdTransfer
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsQuadraticSignCharacter
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SemisimpleRestrictionToNormalSubgroup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLanglandsOfHyp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPadicAlgClRingEquivComplexCompEqOfCountabl

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem exists_prime_notMem {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    ∃ l : ℕ, l.Prime ∧ ((l : ℕ) : 𝓞 F) ∉ v.asIdeal := by
  by_cases h2 : ((2 : ℕ) : 𝓞 F) ∈ v.asIdeal
  · refine ⟨3, Nat.prime_three, fun h3 => v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 ?_)⟩
    have := v.asIdeal.sub_mem h3 h2
    convert this using 1
    push_cast
    ring
  · exact ⟨2, Nat.prime_two, h2⟩

theorem UpperTheory.V.Br.splitOf :
    UpperTheory.V.Br.SplitOf := by
  intro N exC exR F K _ _ _ _ _ _ _ hK n _ hn π χ Q hreg hpol hQ v w i hi hloc σ σ' hσ hσ'
  obtain ⟨l, hl, hlv⟩ := exists_prime_notMem v
  haveI : Fact l.Prime := ⟨hl⟩
  obtain ⟨ι⟩ : Nonempty (Qbar l ≃+* ℂ) := GlobalTheory.nonempty_padicAlgCl_ringEquiv_complex l
  have hL : GlobalTheory.Published.LocalLanglandsGL :=
    GlobalTheory.LocLanglandsBridge.localLanglandsGL_of_depthZero_zelevinsky_bernstein N.loc.llc N.loc.conv N.loc.dzc N.loc.dzi
      N.loc.brauer N.loc.chev N.aut.art N.loc.exh N.loc.multi N.loc.cos N.loc.zel N.loc.geo N.loc.bz
  let Ω := AlgebraicClosure K
  haveI : IsAlgClosure F Ω := ⟨IsAlgClosure.isAlgClosed K, by
    haveI : Algebra.IsAlgebraic K Ω := IsAlgClosure.isAlgebraic
    exact Algebra.IsAlgebraic.trans F K Ω⟩
  obtain ⟨r, wt, HT, hG, hatt, -⟩ := exR F Ω l ι n hn π χ hreg hpol
  have hnorm : (Bc.res F Ω K).range.Normal := by
    obtain ⟨δ, -, -, hδ, -⟩ := UpperTheory.exists_quadratic_sign_character F K Ω l hK
    rw [show (Bc.res F Ω K).range = δ.ker from Subgroup.ext fun s => (hδ.1 s).symm]
    infer_instance
  obtain ⟨hQr, hQa⟩ := UpperTheory.V.Br.bcAtt0 F K Ω l ι n r π Q hQ
  replace hQr := hQr hreg
  replace hQa := hQa hatt (UpperTheory.semisimple_restriction_to_normal_subgroup _ _ _ n r _ hnorm hatt.1)
  obtain ⟨χ', hsg, hd⟩ := UpperTheory.V.Br.bcDual0 N.aut.js.1 N.aut.gk F K hK n hn π χ Q hpol hQ
  obtain ⟨χ'', r', wt', HT', -, -, -, hG'⟩ := exC K Ω l ι n hn Q χ' hQr hsg hd
  replace hG' := hG' _ (hG.cont.comp (continuous_restrictScalarsHom F K Ω)) hQa
  obtain ⟨hw, A, h, h', hiso⟩ := UpperTheory.V.Br.placeOf F K Ω v w i hi hloc
  have hlw : ((l : ℕ) : 𝓞 K) ∉ w.asIdeal := fun hm => hlv <| by
    rw [← hw]
    change algebraMap (𝓞 F) (𝓞 K) _ ∈ w.asIdeal
    rwa [map_natCast]
  obtain ⟨rc, hrc, -⟩ := hL.1 F Ω A v h
  obtain ⟨rc', hrc', -⟩ := hL.1 K Ω A w h'
  exact UpperTheory.V.Br.recInv hL F K Ω A v w h h' _ i hiso n σ σ' rc rc' hrc hrc'
    (UpperTheory.V.Br.wdAway F K Ω l ι A v w h h' i hiso hlv hlw n r _ _ (hG.away v hlv A h rc hrc σ hσ)
      (hG'.away w hlw A h' rc' hrc' σ' hσ'))
