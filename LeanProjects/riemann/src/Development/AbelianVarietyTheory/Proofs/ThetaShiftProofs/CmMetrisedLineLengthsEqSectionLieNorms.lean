import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.DegenerationDataBaseChangesExistPid
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.DualNumberRingHomExt
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyPBOn
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.PolFibreIdCompCancel
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsIsPolFibreOfKeyPB
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.FormEqPiMulHermForm
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.EqZeroOfPow
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsFibreOfIffIsPolFibre
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LamLenOfIsHerm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries ComplexOrder

namespace GlobalTheory.ArcCM.NormTie

theorem isThNormAt_of_keyArchAt {K K' : Type} [Field K] [NumberField K] [Field K'] {x : KeyIn K} {T abelian₂ : MLine K}
    {σ : K →+* ℂ} (h : KeyArchAt x T abelian₂ σ) (y : KeyIn K') (τ : K' →+* ℂ)
    (hy : ∀ z : KeyIn ℂ, KeyPB z x σ → KeyPB z y τ) : Arch.IsThNormAt y.P y.rig y.th τ (T.n σ ^ 2) := by
  obtain ⟨z, u, Hm, W, χ, θ, Fd, hpb, hA, hR, hF, -, hD, e, -⟩ := h
  obtain ⟨φ, he, w, hg, F, hφ, hw, h1, h2, -⟩ := hy z hpb
  exact ⟨z.P, z.rig, z.th, φ, he, w, hφ, hw, h1, h2, u, Hm, χ, θ, Fd, hA, hR, hF, hD, e⟩

theorem isLieNormAt_of_isVecLine {K : Type} [Field K] [NumberField K] {A : Out.PolAV (Sp (𝓞 K))} {x : KeyIn K}
    {φ : x.P.A.left ⟶ A.A.left} {i : Fin x.P.g} {ℓ : MLine K} (h : IsVecLine A x φ i ℓ) (σ : K →+* ℂ) :
    Arch.IsLieNormAt x.P (x.v i) σ (Real.log (ℓ.n σ)) := by
  obtain ⟨xs, u, Hm, χ, W, hg, hpb, hA, hW, e⟩ := h.2.2 σ
  obtain ⟨ψ, hg', hψ, hv⟩ := GlobalTheory.KeyFibre.exists_isPolFibre_of_keyPB K ℂ σ x xs hpb
  obtain ⟨w, hw⟩ := LBIso.symm hψ.2.2
  refine ⟨xs.P, ψ, w, _, hψ.2.1, hw, hv (i.cast hg.symm), u, Hm, χ, W, hA, hW, ?_⟩
  rw [← e, Real.log_pow]
  push_cast
  ring

section Pull

variable {K : Type} [Field K] {D₀ : Out.DegPre K} {DC : Out.DegPre ℂ} {σ : K →+* ℂ} (p : Out.IsPullDeg σ D₀ DC)

include p in
theorem g_eq : DC.P.g = D₀.P.g :=
  ReciprocityTheory.ChartRestriction.G.H1.dim_unique DC.P.A.hom DC.P.smoothDim
    ((smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (pull_grp p).1 D₀.P.smoothDim)
    (eSec DC.P.A (default : PrimeSpectrum ℂ))

theorem isPolFibre_prj : IsPolFibre σ D₀.P DC.P (prj p) :=
  ⟨g_eq p, pull_grp p, LBIso.symm ⟨p.w, p.w_gen⟩⟩

theorem exists_keyPB {th : D₀.P.L.Sec} {thC : DC.P.L.Sec} (h : ThBC p th thC) (hg : 1 ≤ D₀.P.g) (hn : ThNZ th)
    (v : Fin D₀.P.g → (epsR K ⟶ D₀.P.A)) (hv : IsLieBasis v) :
    ∃ hg' hn' v' hv', KeyPB ⟨DC.P, hg', DC.rig, DC.rig_gen, thC, hn', v', hv'⟩
      ⟨D₀.P, hg, D₀.rig, D₀.rig_gen, th, hn, v, hv⟩ σ := by
  have e := g_eq p
  have c₁ : IsCommMonObj D₀.P.A := D₀.P.isAb.comm
  have c₂ : IsCommMonObj DC.P.A := DC.P.isAb.comm
  obtain ⟨v', hb', hv'⟩ := exists_isLieBasis_baseChange K ℂ σ D₀.P.A DC.P.A (prj p) (pull_grp p)
    D₀.P.isAb.smooth D₀.P.g v hv
  refine ⟨e ▸ hg, GlobalTheory.ArcQBC.thNZ_of_thBC p h hn, fun i => v' (i.cast e), GlobalTheory.KeyTf.isLieBasis_cast e hb',
    prj p, p.he, p.w, e, Chart.dualMapR σ, pull_grp p, p.w_gen, p.w_rig,
    GlobalTheory.KeyPow.appLE_eq_of_stalk _ th thC ((GlobalTheory.ArcQBC.through_iff _ _).1 h), fun a => ?_, ?_, fun i => hv' _⟩
  · ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  · ext <;> simp [Chart.dualMapR]

end Pull

theorem exists_isLieNormAt (hU : ThetaUnifAV) (P : Out.PolAV (Sp ℂ)) (v : epsR ℂ ⟶ P.A) (hv : IsTangent v) :
    ∃ (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (z : Fin P.g → ℂ),
      u.IsAH Hm χ ∧ u.IsDiff z v ∧
        Arch.IsLieNormAt P v (RingHom.id ℂ) (Real.log (Real.pi * (hermForm Hm z z).re) / 2) := by
  obtain ⟨rig, hr⟩ := P.rigid
  obtain ⟨u, Hm, χ, -, hA, -, hd, -⟩ := hU P rig hr
  obtain ⟨z, hz, -⟩ := hd v hv
  obtain ⟨h₁, h₂⟩ := GlobalTheory.polFibre_id_comp_cancel.1 ℂ P v
  obtain ⟨w, hw⟩ := LBIso.symm h₁.2.2
  exact ⟨u, Hm, χ, z, hA, hz, P, _, w, v, h₁.2.1, hw, h₂, u, Hm, χ, z, hA, hz, rfl⟩

theorem exists_letter_bound (hU : ThetaUnifAV) (hL : Out.Laws) {E : Type} [Field E] [NumberField E] [IsCMField E]
    [StarRing (𝓞 E)] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {l : Level H} {c : Coeff l} (hs : ∀ a : 𝓞 E, star a = H.bar a)
    {nΨ n' f : ℕ} {o : LamObj c nΨ n'} {La : ℝ} (hG : LamObjGood o f La) (L : LamLetters o) (hLg : L.IsGood)
    (σ : o.K₁ →+* ℂ) (Q : Out.PolAV (Sp ℂ)) (ψ : Q.A.left ⟶ o.xB.P.A.left) (hQ : IsPolFibre σ o.xB.P Q ψ)
    (m : Fin o.xB.P.g) (u : epsR o.K₁ ⟶ o.xB.P.A) (uC : epsR ℂ ⟶ Q.A) (hu : L.IsLetter m u)
    (hC : IsVecOver σ ψ u uC) :
    ∃ x, Arch.IsLieNormAt Q uC (RingHom.id ℂ) x ∧ (0 < La → x ≤ Real.log (La * (L.ℓ m).n σ)) := by
  have hB := hG.2.2.2.1
  have hp : IsPolFibre (algebraMap (𝓞 o.K₁) o.K₁) o.B o.xB.P o.φB :=
    (isFibreOf_iff_isPolFibre (𝓞 o.K₁) o.K₁ (algebraMap (𝓞 o.K₁) o.K₁) o.B o.xB o.φB).1 hB
  obtain ⟨h, Hh⟩ := (GlobalTheory.CM.LieMetric.exists_unique_isHerm hU hL o.K₁ o.B
    (GlobalTheory.CM.GenFib.mk o.xB.P o.φB hp o.xB.v o.xB.basis)).1
  obtain ⟨w, hw1, hw2⟩ := hLg.2.2.1 m
  obtain rfl : u = w := by
    refine Over.OverMorphism.ext (hp.2.1.1.hom_ext ?_ ((Over.w u).trans (Over.w w).symm))
    unfold LamLetters.IsLetter at hu hw1
    cases hq : L.src m with
    | inl q => rw [hq] at hu hw1; exact hu.trans hw1.symm
    | inr q => rw [hq] at hu hw1; exact hu.trans hw1.symm
  have c₁ : IsCommMonObj o.xB.P.A := o.xB.P.isAb.comm
  have ht : IsTangent u := by
    rw [(LieComb.isLieComb_iff_tanExp _ _).1 hw2]
    exact LieComb.isTangent_tanExp o.xB.basis.1 _
  obtain ⟨uu, Hm, χ, z, hA, hz, hN⟩ := exists_isLieNormAt hU Q uC (hC.isTangent hQ.2.1 ht)
  refine ⟨_, hN, fun hLa => ?_⟩
  have e := GlobalTheory.CM.LieMetric.form_eq_pi_mul_hermForm hU hL o.K₁ o.B _ h Hh σ Q ψ uu Hm χ hQ hA
    _ _ _ _ _ _ z z hw2 hw2 hC hC hz hz
  have e' : Real.pi * (hermForm Hm z z).re = (h.form σ (L.U m) (L.U m)).re := by
    rw [e, Complex.re_ofReal_mul]
  have b := (lamLen_of_isHerm hU hL E H l c nΨ n' f o La hG L hLg hp h Hh σ).2 m
  have hd := GlobalTheory.LamF.Ind.lamInd E H l c hs nΨ n' f o La hG L hLg
  have hne : L.U m ≠ 0 := fun h0 => hd (Matrix.det_eq_zero_of_row_eq_zero m (congrFun h0))
  have hpos : 0 < (h.form σ (L.U m) (L.U m)).re := by
    have := (h.posDef σ 1 ![L.U m] (by simpa [linearIndependent_unique_iff] using hne)).diag_pos (i := 0)
    exact (Complex.pos_iff.1 this).1
  rw [e']
  have := Real.log_le_log hpos b
  rw [Real.log_pow] at this
  push_cast at this
  linarith

theorem lengths_eq_norms : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra c.F K₁] (a : ArcIn Dw l (RingHom.id c.F) K₁ (algebraMap c.F K₁)) (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR K₁)) (th : a.D₀.P.L.Sec) (jj : ℤ) (n' : ℕ) (La c₁ : ℝ) (s : CMIn a e th jj n' La c₁) (em : K₁ →+* ℂ), letI := H.starRing; Arch.IsThNormAt a.D₀.P a.D₀.rig th em (s.Tl.n em ^ 2) ∧ (∀ i, Arch.IsLieNormAt s.xΨ.P (s.xΨ.v i) em (Real.log ((s.ℓΨ i).n em))) ∧ (∀ i, Arch.IsLieNormAt s.x'.P (s.x'.v i) em (Real.log ((s.ℓ' i).n em))) ∧ ∀ (DC : Out.DegPre ℂ) (p : Out.IsPullDeg em a.D₀ DC), (∀ thC, ThBC p th thC → Arch.IsThNormAt DC.P DC.rig thC (RingHom.id ℂ) (s.Tl.n em ^ 2)) ∧ ∀ m (u : epsR K₁ ⟶ a.D₀.P.A) (uC : epsR ℂ ⟶ DC.P.A), s.L.IsLetter m u → uC.left ≫ prj p = spMap (dualMap em) ≫ u.left → ∃ x, Arch.IsLieNormAt DC.P uC (RingHom.id ℂ) x ∧ (0 < La → x ≤ Real.log (La * (s.L.ℓ m).n em)) := by
  intro hK E _ _ _ H Dw l c K₁ _ _ _ a e th jj n' La c₁ s em
  letI := H.starRing
  have hG := s.good
  have hA : KeyArchAt s.xB s.Tl s.LamL em := hG.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 em
  refine ⟨isThNormAt_of_keyArchAt hA s.xB em fun _ h => h,
    fun i => isLieNormAt_of_isVecLine (hG.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 i) em,
    fun i => isLieNormAt_of_isVecLine (hG.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 i) em, fun DC p => ⟨fun thC hC => ?_,
    fun m u uC hu hC => ?_⟩⟩
  · obtain ⟨hg', hn', v', hv', h⟩ := exists_keyPB p hC s.g_pos s.th_nz s.v s.basis
    exact isThNormAt_of_keyArchAt hA ⟨DC.P, hg', DC.rig, DC.rig_gen, thC, hn', v', hv'⟩ (RingHom.id ℂ) fun z hz =>
      GlobalTheory.KeyCancel.keyPB_cancel K₁ ℂ ℂ _ _ z em (RingHom.id ℂ) h (by rwa [RingHom.id_comp])
  · exact exists_letter_bound hK.theta hK.laws (fun _ => rfl) hG s.L s.L_good em DC.P (prj p) (isPolFibre_prj p)
      m u uC hu hC

end GlobalTheory.ArcCM.NormTie
