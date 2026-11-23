import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.HodgeTrAt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.SubtractHolds
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PotSemistableOfPotCrystallineDecompositionGroup

open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open GlobalTheory.GalV (HTower)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (algSat tw)
open UpperTheory.Gal.TP.Sub (Cl unrPol)
open UpperTheory.Gal.crystallineComparison (heckePol rootPol)
open UpperTheory.Gal.Int.Div (CrysAt PhiKilled HTRichEx JumpsOcc VBase)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem rootPol_pow (R : Multiset ℂ) (k : ℕ) : rootPol R ^ k = rootPol (k • R) := by
  simp [rootPol, Multiset.map_nsmul, Multiset.prod_nsmul]

private theorem rootPol_map_dvd (S R : Multiset ℂ) (c : ℂ) (k : ℕ) (h : rootPol S ∣ rootPol R ^ k) :
    rootPol (S.map (· * c)) ∣ rootPol (R.map (· * c)) ^ k := by
  rw [rootPol_pow] at h ⊢
  have hne : rootPol (k • R) ≠ 0 :=
    (Polynomial.monic_multiset_prod_of_monic _ _ fun a _ => monic_X_sub_C a).ne_zero
  have hle : S ≤ k • R := by
    have := Polynomial.roots.le_of_dvd hne h
    simpa only [rootPol, Polynomial.roots_multiset_prod_X_sub_C] using this
  have h2 : S.map (· * c) ≤ k • R.map (· * c) := by
    rw [← Multiset.map_nsmul]
    exact Multiset.map_le_map hle
  exact Multiset.prod_dvd_prod_of_le (Multiset.map_le_map h2)

private theorem unrPol_neg_one (S : Multiset ℂ) : unrPol S (-1) = rootPol S := by
  simp [unrPol, rootPol]

private theorem charPol_eq_rootPol {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : Formalism.ConjugateSelfDual.IsPlaceOver A w} (x : WD h) (g : Weil h) :
    x.charPol g = rootPol (x.charPol g).roots := by
  have hm : (x.charPol g).Monic := by
    induction x using WD.ind with
    | hP n a =>
      rw [WD.charPol_mk]
      exact LinearMap.charpoly_monic _
  exact (IsAlgClosed.splits _).eq_prod_roots_of_monic hm

private theorem pst_of_crys {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (hT : Nonempty (LocTied l P AI))
    {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω}
    {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] {Bw : LocBridge l E Ω (ReciprocityTheory.Gal.Dec (F := E) A) O} {a : ℕ}
    {r : ↥(ReciprocityTheory.Gal.Dec (F := E) A) →* GL (Fin a) (Qbar l)} (hc : IsCrysAt P Bw r) : IsPstAt P Bw r := by
  obtain ⟨T⟩ := hT
  obtain ⟨LL', r', hm, h⟩ := hc
  exact ⟨LL', r', hm, GlobalTheory.PstOfCrys.isPst_of_isCrys T _ h⟩

theorem UpperTheory.Gal.Int.Geo.twPhi :
    UpperTheory.Gal.Int.Geo.TwPhi := by
  intro E Ω _ _ _ _ _ l _ ι dd ρ χ hρ hχ w c m h1 R h2 P AI hT A h O _ _ _ Bw hj
  obtain ⟨c1, -, -, p1⟩ := h1.2 P AI hT A h O Bw hj
  obtain ⟨c2, g, hg, k, hk⟩ := h2 P AI hT A h O Bw hj
  have e1 : (rk1 χ).comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype = rk1 (χ.comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype) := by
    ext g i j
    rfl
  have e2 : (tw ρ χ).comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype =
      tw (ρ.comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype) (χ.comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype) := by
    ext g i j
    simp [UpperTheory.V.Af.tw_val]
  have e3 : Formalism.MainNotions.SumRepresentations.At.twGL (ρ.comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype)
      (Matrix.GeneralLinearGroup.det.comp (rk1 (χ.comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype))) =
      tw (ρ.comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype) (χ.comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype) := by
    have hdet : Matrix.GeneralLinearGroup.det.comp (rk1 (χ.comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype))
        = χ.comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype := by
      ext g
      simp [GlobalTheory.TripleGal.rk1, Matrix.det_unique]
    rw [hdet]
    ext g i j
    simp [Formalism.MainNotions.SumRepresentations.At.twGL, UpperTheory.V.Af.tw_val, Algebra.algebraMap_eq_smul_one, Matrix.smul_apply]
  rw [e1] at c1 p1
  rw [e2]
  have cs : Continuous (ρ.comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype) := hρ.comp continuous_subtype_val
  have cμ : Continuous (χ.comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype) := hχ.comp continuous_subtype_val
  have ck := (UpperTheory.Gal.TP.Sub.contLeft_holds _ (Qbar l) 1 1).2.2.2 _ cμ
  obtain ⟨-, l2⟩ := UpperTheory.Gal.TP.Sub.twLoc_holds l P AI hT E Ω A O Bw dd (ρ.comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype)
    (χ.comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype)
  have ct := l2 c2 c1
  refine ⟨ct, g, hg, k, ?_⟩
  have q3 := pst_of_crys hT ct
  have hcs : Continuous fun g : ↥(ReciprocityTheory.Gal.Dec (F := E) A) =>
      ((ρ.comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype g : GL (Fin dd) (Loc.Om l)) : Matrix (Fin dd) (Fin dd) (Loc.Om l)) :=
    Units.continuous_val.comp cs
  have hck : Continuous fun g : ↥(ReciprocityTheory.Gal.Dec (F := E) A) =>
      ((rk1 (χ.comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype) g : GL (Fin 1) (Loc.Om l)) : Matrix (Fin 1) (Fin 1) (Loc.Om l)) :=
    Units.continuous_val.comp ck
  rw [← e3] at q3
  have key := GlobalTheory.T.fontaineParameter_twist_potentiallySemistable l P AI hT ι E Ω A w h O Bw hj dd _ _ hcs hck (pst_of_crys hT c2) (pst_of_crys hT c1) q3
  rw [e3] at key
  rw [key]
  have hx := charPol_eq_rootPol (wdAt P ι Bw h hj (ρ.comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype)) g
  have hx' := hx
  rw [← unrPol_neg_one, ← hg] at hx'
  have hy := p1 g
  have hr := (UpperTheory.Gal.TP.Sub.wDFacts_holds E Ω A w h _ _).2.2.2 g _ c hx' hy
  rw [hr, hg, unrPol_neg_one]
  rw [hx] at hk
  exact rootPol_map_dvd _ R c k hk
