import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.ResCoeff
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubMemOfMk
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StCocycle
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedFormCocycle
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedFormAdd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedFormAction
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedFormLocalOfFrame
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SheafFiltrationProperty
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartIsGood
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartDividedPowersGradedConstant
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsChartFromCoordinates
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsChart
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LiftCocycleMem
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubMemOfLift
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedCechCohomologyFinite
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoverCupActionBasis
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StableCoverCechVanishing
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TruncatedWittIsNoetherian
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalGradedVanishing
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoordinatesRestrictAffineOpenStatement
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobSerre
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.PolynomialSiteTraces.PolyAll
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PreimageMono
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

noncomputable section
namespace GlobalTheory.CompanionTheory.FibGr

section Abs
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C]

theorem fin_vb [IsNoetherianRing R] {Z : Scheme.{0}} (z : Z ⟶ Spec (CommRingCat.of R)) [IsProper z] (F : C ⥤ ModuleCat.{0} R)
    {ι : Type} [Fintype ι] (U : ι → Z.Opens) (P : ι → ObjectProperty C) (m : ℕ) (hU : (⨆ α, U α) = ⊤)
    (ha : ∀ n (i : Fin (n + 1) → ι), IsAffineOpen (capO U i))
    (V : VB (fun W : Z.Opens => strV z W) U (CrystallineSemistableComparison.Pb.cechH F P m)) (a : ℕ) :
    Module.Finite R ((CrystallineSemistableComparison.Pb.cechH F P m).cx.H a) :=
  vb_fin z U hU ha (CrystallineSemistableComparison.Pb.cechH F P m) V a

theorem fin_zero (F : C ⥤ ModuleCat.{0} R) {ι : Type} (P : ι → ObjectProperty C) (b a : ℕ)
    (h : ∀ i : Fin (a + 1) → ι, Subsingleton (HU F (capT P i) b)) :
    Module.Finite R ((CrystallineSemistableComparison.Pb.cechH F P b).cx.H a) := by
  haveI : Subsingleton ((CrystallineSemistableComparison.Pb.cechH F P b).X a) := ⟨fun x y => funext fun i => (h i).elim _ _⟩
  haveI : Subsingleton ((CrystallineSemistableComparison.Pb.cechH F P b).cx.H a) :=
    ⟨fun x y => by
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      exact congrArg _ (Subtype.ext (Subsingleton.elim _ _))⟩
  infer_instance

end Abs

section Main
variable {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} (hI : I = ⊥) {X : Scheme.{0}}
  {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} {γ : DividedPowers I} {p : ℕ}

theorem serre_red [IsNoetherianRing R] (F : Thick (nlFun γ p X q κ) ⥤ ModuleCat.{0} R) (Q : ObjectProperty (Thick (nlFun γ p X q κ)))
    {ι : Type} (U : ι → X.Opens) (j : ℕ)
    (h : ∀ a b, a + b = j → Module.Finite R ((CrystallineSemistableComparison.Pb.cechH F (fun α => St Q {U α}) b).cx.H a)) :
    Module.Finite R (HU F (St Q (Set.range U)) j) := by
  obtain ⟨𝒮, h𝒮⟩ := serre_fg R
  exact (h𝒮 _).1 (GlobalTheory.CompanionTheory.GlobSt.glob_st.2.1 F Q U 𝒮 j fun a b hab => (h𝒮 _).2 (h a b hab))

include hI in

theorem fin_gen [IsNoetherianRing R] (hp : p ≠ 0) (hn : IsNilpotent (p : R)) [IsProper q] (U : Cov q) (r j : ℕ) :
    Module.Finite R (HU (GF (nlFun γ p X q κ) r) (St ⊤ (Set.range U.U)) j) := by
  refine serre_red (GF (nlFun γ p X q κ) r) ⊤ U.U j fun a b _ => ?_
  by_cases hb : b = r
  · subst hb
    have : IsProper (qF hI q κ) := MorphismProperty.pullback_snd (P := @IsProper) _ _ inferInstance
    obtain ⟨V⟩ := vb_cech (γ := γ) (p := p) (κ := κ) hI hp hn U b
    have ha : ∀ n (i : Fin (n + 1) → U.ι), IsAffineOpen (capO (fun α => jF hI q κ ⁻¹ᵁ U.U α) i) := fun n i => by
      rw [capO_pre]
      exact aff_pre hI (GlobalTheory.CompanionTheory.GrCech.capO_affine U n i)
    have e : (fun α => St (⊤ : ObjectProperty (Thick (nlFun γ p X q κ))) {U.U α}) = fun α => SQ q κ γ p (U.U α) := rfl
    rw [e]
    exact fin_vb (qF hI q κ) _ _ _ b (cover_pre hI U) ha V a
  · refine fin_zero _ _ b a fun i => ?_
    have e := GlobalTheory.CompanionTheory.GrCech.capT_eq (⊤ : ObjectProperty (Thick (nlFun γ p X q κ))) U.U i
    obtain ⟨c', -⟩ := GlobalTheory.T.coordinates_restrict_affine_open (U.c (i 0)) (capO_le U.U i 0) (GlobalTheory.CompanionTheory.GrCech.capO_affine U a i)
    have h := off_at (γ := γ) (p := p) (κ := κ) hI hp hn c' r b hb
    rw [show capT (fun α => St (⊤ : ObjectProperty (Thick (nlFun γ p X q κ))) {U.U α}) i = SQ q κ γ p (capO U.U i) from e]
    exact h

end Main

theorem level_one_gr_finite : ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] [PerfectRing k l] {O : Type} [CommRing O] {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) [IsProper q] (ρ : O →+* k) (U : Cov q) (r j : ℕ),
    Module.Finite (Wc.Wm l k 1) (CH.H (sq (sFil (St (γ := Wc.pd l k 1) (p := l) (q := q) (κ := (Wc.res l k 1).comp ρ) ⊤ (Set.range U.U)) r) (sFil (St (γ := Wc.pd l k 1) (p := l) (q := q) (κ := (Wc.res l k 1).comp ρ) ⊤ (Set.range U.U)) ((r : ℤ) + 1))) j) := by
  intro l _ k _ _ _ O _ X q _ ρ U r j
  have hI : Wc.Im l k 1 = ⊥ := (Ideal.map_eq_bot_iff_le_ker _).2 (by
    rw [Ideal.mk_ker, pow_one])
  have hl : ((l : ℕ) : Wc.Wm l k 1) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk (Ideal.span {(l : WittVector l k) ^ 1}))]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (by rw [pow_one]; exact Ideal.mem_span_singleton_self _)
  have hn : IsNilpotent ((l : ℕ) : Wc.Wm l k 1) := by
    rw [hl]
    exact IsNilpotent.zero
  haveI := GlobalTheory.CompanionTheory.WittLevel.isNoetherianRing_Wm_one (l := l) (k := k)
  have h := fin_gen (γ := Wc.pd l k 1) (p := l) (κ := (Wc.res l k 1).comp ρ) hI (Fact.out : l.Prime).ne_zero hn U r j
  exact h

end GlobalTheory.CompanionTheory.FibGr
end
