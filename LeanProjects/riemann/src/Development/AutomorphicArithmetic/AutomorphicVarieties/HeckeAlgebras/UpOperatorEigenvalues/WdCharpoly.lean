import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LocCFTAll
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.Classical
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CharpolyEqProd
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.dvrFinite
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.MapApi
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.RepApi
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.RepCont
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.ExtDense
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.BnRepLin
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.ExistsAdjoinCoeffCharacterSubMemMaximalIdealPow
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGext
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.EpsArt
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.WeilGroupDenseInGaloisGroup
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.BuildingComponentUniqueness
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IsSplitAtOfDecompositionLeRestrictionRange
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.EqOneOfTraceTranslationInvariantSemisimple
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitarySphericalIffHasSatakeInert
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceUnitaryLocalPointsEquivGLStatement
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.UpOperatorEigenvalues.PtSmall
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.UpOperatorEigenvalues.DiagOfCong
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

namespace UpperTheory.V.Hi.Up

theorem comp_ex {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {σ : Submodule ℂ (UA L n → ℂ)} (hσ : IsAutRepU σ)
    {w : Plc L} (hw : IsSplitAt w) :
    ∃ τ : SmIrr (GLw n w), IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ := by
  obtain ⟨e, he⟩ := GlobalTheory.T.splitPlace_unitaryLocalPoints_equiv_GL L n w hw
  obtain ⟨τ, -, -, f, h0, h1, h2⟩ := GlobalTheory.T.exists_admissible_localComponent_definiteUnitary L n ⟨σ, hσ⟩ w
  refine ⟨GlobalTheory.InertSatake.transport e τ, (GlobalTheory.InertSatake.transport e τ).irred, f, h0, h1, fun x v => ?_⟩
  have := GlobalTheory.InertSatake.transport_apply e τ x v
  rw [he] at this
  exact (congrArg f this).trans (h2 x v)

section WD

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
  {ι : Qbar l ≃+* ℂ} {w : Plc F} {A : ValuationSubring Ω} {h : IsPlaceOver A w}

theorem wd_charpoly (hl : ((l : ℕ) : 𝓞 F) ∉ w.asIdeal) {r r' : G F Ω →* GL (Fin n) (Qbar l)} {x : WD h}
    (hx : IsWDOf ι r x) (hx' : IsWDOf ι r' x) (g : Weil h) :
    (r g : Matrix (Fin n) (Fin n) (Qbar l)).charpoly = (r' g : Matrix (Fin n) (Fin n) (Qbar l)).charpoly := by
  have e := hx.wdOf_eq hl
  have e' := hx'.wdOf_eq hl
  obtain ⟨t, ht, φ, hφ, N, b, hN, -⟩ := hx
  obtain ⟨t', ht', φ', hφ', N', b', hN', -⟩ := hx'
  refine Polynomial.map_injective ι.toRingHom ι.injective ?_
  rw [← hN.charPol_wdOf hl ht ι g, ← hN'.charPol_wdOf hl ht' ι g, e, e']

theorem wd_type (hl : ((l : ℕ) : 𝓞 F) ∉ w.asIdeal) {r : G F Ω →* GL (Fin n) (Qbar l)} (χ : Fin n → Ine (F := F) A →* (Qbar l)ˣ)
    (hχ : ∀ i, IsOpen ((χ i).ker : Set (Ine (F := F) A))) (g : GL (Fin n) (Qbar l))
    (hg : ∀ s : Ine (F := F) A, ((g * r s * g⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) =
      Matrix.diagonal fun i => (χ i s : Qbar l)) {x : WD h} (hx : IsWDOf ι r x) :
    IsTypeWD h (fun i => W.pushCh ι.toRingHom (χ i)) x := by
  let r' : G F Ω →* GL (Fin n) (Qbar l) := (MulAut.conj g).toMonoidHom.comp r
  have hr' : ∀ s, r' s = g * r s * g⁻¹ := fun s => rfl
  have hx' : IsWDOf ι r' x := hx.of_conj hl g fun s => by rw [hr', inv_mul_cancel_right]
  obtain ⟨t, ht, φ, hφ, N, a, hN, ha, rfl⟩ := hx'
  have hs : IsSmooth (r'.comp (Weil h).subtype) := by
    refine .of_open (isOpen_iInter_of_finite hχ) (Set.mem_iInter.2 fun i => (χ i).ker.one_mem) fun σ hσ => Units.ext ?_
    change (r' σ : Matrix (Fin n) (Fin n) (Qbar l)) = 1
    rw [hr', hg σ]
    simp [fun i => show χ i σ = 1 from Set.mem_iInter.1 hσ i]
  obtain rfl : N = 0 := hN.unique ht ((isMonodromy_zero_iff (h := h)).mpr hs)
  refine ⟨a, rfl, ?_, fun s => ?_⟩
  · rw [ha.1, map_zero]
  · rw [IsFrobSS.ρ_ineIncl (ρ := hN.rep hl ht hφ ι) ha (hN.isSmooth_rep hl ht _ ι), hN.rep_apply, wdMat_zero, coe_ineIncl, hr',
      hg s, toEndC_apply, Matrix.diagonal_map (map_zero ι)]
    rfl

end WD

theorem chi_comap {n : ℕ} {A G H : Type} [CommRing A] [Group G] [Group H] (D : W.GDet n A G) (φ : H →* G) (y : MonoidAlgebra A H) :
    (D.comap φ).chi y = D.chi (MonoidAlgebra.mapDomainRingHom A φ y) := by
  change D.D A[X] (MonoidAlgebra.mapDomainRingHom A[X] φ _) = D.D A[X] _
  congr 1
  rw [map_sub]
  congr 1
  · simp
  · induction y using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | single g r => simp

section Pt

variable {l : ℕ} [Fact l.Prime] {F : W.GFrame l} {c : Coef l} {n : ℕ} {r : Resid F c.O n} {B : UniversalOrdinaryDeterminantRing r}
  (x : B.B →ₐ[c.O] Qbar l) {Γ : Type} [Group Γ] (p : Γ →* F.G₀) (ρ : Γ →* GL (Fin n) (Qbar l))
  (hx : (B.u.D.map (x : B.B →+* Qbar l)).comap p = W.GDet.ofRep (W.mat ρ))

include hx

theorem chi_pt (g : Γ) : (B.u.D.chi (MonoidAlgebra.single (p g) 1)).map (x : B.B →+* Qbar l) =
    (ρ g : Matrix (Fin n) (Fin n) (Qbar l)).charpoly := by
  have e := (AlgebraTools.Det.repApi (W.mat ρ)).2.1 g
  rw [← hx, chi_comap] at e
  rw [← (AlgebraTools.Det.mapApi B.u.D (x : B.B →+* Qbar l)).1]
  simp only [MonoidAlgebra.mapRingHom_single, map_one]
  simp only [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single] at e
  exact e

theorem chi_cong (g : Γ) (P : c.O[X]) (hP : r.Dbar.chi (MonoidAlgebra.single (p g) 1) = P.map (residue c.O)) (k : ℕ) :
    ‖(ρ g : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.coeff k - (P.map (algebraMap c.O (Qbar l))).coeff k‖ < 1 := by
  rw [← chi_pt x p ρ hx, coeff_map, coeff_map]
  refine pt_res x _ _ ?_
  have e := (AlgebraTools.Det.mapApi B.u.D (Alg.res c.O B.B : B.B →+* ResidueField c.O)).1 (MonoidAlgebra.single (p g) 1)
  rw [B.u.red, MonoidAlgebra.mapRingHom_single, map_one, hP] at e
  have := congrArg (·.coeff k) e
  simp only [coeff_map] at this
  exact this.symm

theorem diag_pt (hn : 1 ≤ n) (hs : Formalism.MainNotions.N.IsSSRep ρ) (t : Fin n → F.G₀ →* c.Oˣ) (ht : r.IsTeich t) (u : F.St) (I : Subgroup Γ)
    (hI : ∀ g ∈ I, p g ∈ F.Iu u) : ∃ P : GL (Fin n) (Qbar l), ∀ g : I,
      ((P * ρ g * P⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) =
        Matrix.diagonal fun i => (W.pushCh (algebraMap c.O (Qbar l)) ((t i).comp (p.comp I.subtype)) g : Qbar l) := by
  obtain ⟨-, hfin, -⟩ := UpperTheory.V.abelian₂.dvr_finite l c.O
  refine diag_of_cong (N := Nat.card (ResidueField c.O) - 1) ?_ _ (fun i g => ?_) (ρ.comp I.subtype) (fun g hg => ?_) fun g k => ?_
  · have h1 : IsUnit ((Nat.card (ResidueField c.O) - 1 : ℕ) : c.O) := by
      rw [← residue_ne_zero_iff_isUnit, map_natCast, Nat.cast_pred Nat.card_pos]
      letI := Fintype.ofFinite (ResidueField c.O)
      simp [Nat.card_eq_fintype_card]
    have := pt_unit x (h1.map (algebraMap c.O B.B)).unit
    rwa [IsUnit.unit_spec, map_natCast, map_natCast] at this
  · rw [MonoidHom.comp_apply, ← map_pow]
    exact (congrArg _ (ht i _).2).trans (map_one _)
  · refine UpperTheory.eq_one_of_trace_translation_invariant_semisimple Γ (Qbar l) n ρ hs g fun h => ?_
    have h1 : p g ∈ r.Ip u := ⟨hI g g.2, Subgroup.mem_iInf.2 fun i => Units.ext (by
      have h2 : (t i (p g) : c.O) = 1 := Subtype.ext (congrArg Units.val (hg i))
      rw [← (ht i _).1, h2, map_one, Units.val_one])⟩
    have h2 := congrArg x (B.u.I u _ h1 (p h))
    have h3 := (AlgebraTools.Det.repApi (W.mat ρ)).2.2.1 hn (MonoidAlgebra.single h 1 * (MonoidAlgebra.single (g : Γ) 1 - 1))
    rw [← hx, W.GDet.tr, W.GDet.lam, chi_comap] at h3
    have h4 := (AlgebraTools.Det.mapApi B.u.D (x : B.B →+* Qbar l)).2.1 1 (MonoidAlgebra.single (p h) 1 * (MonoidAlgebra.single (p g) 1 - 1))
    rw [W.GDet.lam] at h4
    simp only [map_mul, map_sub, map_one, MonoidAlgebra.mapRingHom_single] at h4
    simp only [map_mul, map_sub, map_one] at h3
    simp only [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single] at h3
    have h5 := h3.symm.trans (h4.trans (h2.trans (map_zero x)))
    simp only [W.GDet.repAlg, MonoidAlgebra.lift_single, one_smul] at h5
    rw [mul_sub, mul_one, Matrix.trace_sub, sub_eq_zero, ← map_mul] at h5
    simpa [W.mat] using h5
  · have := chi_cong x p ρ hx g (∏ i, (X - C (t i (p g) : c.O))) (by
      rw [Resid.Dbar, (AlgebraTools.Det.repApi _).2.1, Polynomial.map_prod]
      simp only [Polynomial.map_sub, map_X, map_C, (ht _ _).1]
      exact Matrix.charpoly_diagonal _) k
    simp only [Polynomial.map_prod, Polynomial.map_sub, map_X, map_C] at this
    exact this

end Pt

end UpperTheory.V.Hi.Up
