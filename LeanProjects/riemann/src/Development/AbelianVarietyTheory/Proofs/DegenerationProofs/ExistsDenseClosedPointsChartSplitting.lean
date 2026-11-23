import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PullPullAndSplitPull
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.KbIsAlgClosedAndConj
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsClassicalPointLiftingResiduePoint
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.JacobsonClosedPointsToolsInt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

noncomputable section
namespace GlobalTheory.ZJ.DenseSplit

theorem exists_ringHom_kb (F : Type) [Field F] [Finite F] :
    ∃ (p : ℕ) (_ : Fact p.Prime), Nonempty (F →+* kb p) := by
  obtain ⟨p, hp⟩ := CharP.exists F
  have hpp : Fact p.Prime := ⟨CharP.char_is_prime F p⟩
  have : CharP (kb p) p := (CharP.charP_iff_prime_eq_zero hpp.out).mpr
    (GlobalTheory.natCast_self_residueField_padicAlgCl_eq_zero p)
  have := (kb_isAlgClosed_and_conj p).1
  letI : Algebra (ZMod p) F := ZMod.algebra F p
  letI : Algebra (ZMod p) (kb p) := ZMod.algebra _ p
  have : Module.Finite (ZMod p) F := Module.Finite.of_finite
  exact ⟨p, hpp, ⟨(IsAlgClosed.lift (R := ZMod p) (S := F) (M := kb p)).toRingHom⟩⟩

theorem isNoetherianRing_of_lft (R : Type) [CommRing R] (π : Sp R ⟶ Sp ℤ) [LocallyOfFiniteType π] :
    IsNoetherianRing R := by
  have : IsLocallyNoetherian (Sp R) := LocallyOfFiniteType.isLocallyNoetherian π
  exact isLocallyNoetherian_Spec.mp this

theorem exists_dense_splitOn : ∀ (C : Core) (L : C.Law), C.HasTests → C.HasCharts → letI := L.grp; letI := L.comm; ∀ z : C.Z, ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsNoetherianRing R) (t : Sp R ⟶ C.Z) (_ : IsImmersion t), t (⊥ : PrimeSpectrum R) = z ∧ ∃ (Ch : Charts ((Over.pullback t).obj C.GG).left) (d : ℕ) (c : Fin d → Ch.Cl) (Sg : Set (Sp R)), Dense Sg ∧ Ch.SplitOn c Sg ∧ ∀ x ∈ Sg, IsClosed ({t x} : Set C.Z) := by
  intro C L hT hC z
  letI := L.grp; letI := L.comm
  obtain ⟨R, _, _, t, _, htz, Ch, hCh⟩ := hC z
  have := C.lft
  have := C.flat
  obtain ⟨-, hfin, -, -, hdense⟩ := GlobalTheory.jacobson_closedPoints_tools_int (Sp R) (t ≫ C.π)
  refine ⟨R, inferInstance, inferInstance, isNoetherianRing_of_lft R (t ≫ C.π), t, inferInstance, htz, Ch, ?_⟩
  let κ := Σ d : Fin (C.g + 1), (Fin d → Ch.Cl)
  let Sg : κ → Set (Sp R) := fun k => {x | Charts.SplitOn (G := (Over.pullback t).obj C.GG) Ch k.2 {x} ∧
    IsClosed ({t x} : Set C.Z)}
  obtain ⟨k, hk⟩ := hdense κ Sg inferInstance (by
    intro x hx
    have := hfin x hx
    obtain ⟨p, hp, ⟨r⟩⟩ := exists_ringHom_kb ((Sp R).residueField x)
    let xb : Sp (kb p) ⟶ Sp R := Spec.map (CommRingCat.ofHom r) ≫ (Sp R).fromSpecResidueField x
    have hxb : ∀ s, xb s = x := fun s => by
      have : xb s ∈ Set.range ((Sp R).fromSpecResidueField x) := ⟨_, (Scheme.Hom.comp_apply _ _ _).symm⟩
      rwa [Scheme.range_fromSpecResidueField] at this
    have hrange : Set.range xb = {x} := by
      ext w
      exact ⟨fun ⟨s, hs⟩ => hs ▸ hxb s, fun hw => ⟨IsLocalRing.closedPoint (kb p), (hxb _).trans hw.symm⟩⟩
    obtain ⟨hlift, hcl⟩ := GlobalTheory.exists_integral_point_lifting_residue_point C.Z C.π C.U C.ne p
    obtain ⟨y, hy, hyU⟩ := hlift (xb ≫ t)
    obtain ⟨τ⟩ := hT p y hyU
    have e : (rPt p ≫ spMap τ.j) ≫ τ.y₀ = xb ≫ t := by rw [Category.assoc, τ.fac, hy]
    have g1 : IsGrpPullback ((Over.pullback (rPt p ≫ spMap τ.j)).obj τ.H) C.GG (xb ≫ t)
        (pullback.fst τ.H.hom (rPt p ≫ spMap τ.j) ≫ τ.f) :=
      ((isGrpPullback_pullback _ _).comp (L.test p y τ)).congr e rfl
    have g2 : IsGrpPullback ((Over.pullback t).obj C.GG) C.GG t (pullback.fst C.GG.hom t) :=
      isGrpPullback_pullback _ _
    have g3 : IsGrpPullback ((Over.pullback xb).obj ((Over.pullback t).obj C.GG)) ((Over.pullback t).obj C.GG) xb
        (pullback.fst ((Over.pullback t).obj C.GG).hom xb) :=
      isGrpPullback_pullback _ _
    let h : pullback τ.H.hom (rPt p ≫ spMap τ.j) ⟶ pullback C.GG.hom t :=
      pullback.lift (pullback.fst _ _ ≫ τ.f) (pullback.snd _ _ ≫ xb) (g1.1.w.trans (Category.assoc _ _ _).symm)
    have h1 : h ≫ pullback.fst _ _ = pullback.fst _ _ ≫ τ.f := pullback.lift_fst _ _ _
    have h2 : h ≫ pullback.snd _ _ = pullback.snd _ _ ≫ xb := pullback.lift_snd _ _ _
    have g4 : IsGrpPullback ((Over.pullback (rPt p ≫ spMap τ.j)).obj τ.H) ((Over.pullback t).obj C.GG) xb h :=
      g2.cancel (g1.congr rfl h1.symm) h2
    have ha : IsAffineHom h := MorphismProperty.of_isPullback (P := @IsAffineHom) g4.1.flip inferInstance
    have ha' : IsAffineHom (pullback.fst ((Over.pullback t).obj C.GG).hom xb) :=
      MorphismProperty.of_isPullback (P := @IsAffineHom) g3.1.flip inferInstance
    obtain ⟨d, hd, c, hs⟩ := hCh p y τ xb hy.symm h h1 h2
    have w : pullback.fst ((Over.pullback t).obj C.GG).hom xb ≫ ((Over.pullback t).obj C.GG).hom =
      ((Over.pullback xb).obj ((Over.pullback t).obj C.GG)).hom ≫ xb := g3.1.w
    let φ := g4.1.lift _ _ w
    have f1 : φ ≫ h = _ := g4.1.lift_fst _ _ w
    have f2 : φ ≫ _ = _ := g4.1.lift_snd _ _ w
    have g5 : IsGrpPullback ((Over.pullback xb).obj ((Over.pullback t).obj C.GG))
        ((Over.pullback (rPt p ≫ spMap τ.j)).obj τ.H) (𝟙 _) φ :=
      g4.cancel (g3.congr (Category.id_comp _).symm f1.symm) (f2.trans (Category.comp_id _).symm)
    have hφ : IsAffineHom φ := MorphismProperty.of_isPullback (P := @IsAffineHom) g5.1.flip inferInstance
    have hs' := @SplitPull.pull_pull_and_split_pull.2 (kb p) (kb p) _ _
      ((Over.pullback (rPt p ≫ spMap τ.j)).obj τ.H) _ ((Over.pullback xb).obj ((Over.pullback t).obj C.GG)) _
      (𝟙 _) φ hφ g5 (Ch.pull h) d c hs
    refine ⟨⟨⟨d, Nat.lt_succ_of_le hd⟩, c⟩, ?_, ?_⟩
    · rintro _ rfl
      refine ⟨kb p, inferInstance, xb, ha', hrange, ?_⟩
      have key : ∀ (ψ : ((Over.pullback xb).obj ((Over.pullback t).obj C.GG)).left ⟶ pullback C.GG.hom t)
          [IsAffineHom ψ], φ ≫ h = ψ →
          Charts.Split (H := (Over.pullback xb).obj ((Over.pullback t).obj C.GG)) (Ch.pull ψ) c := by
        intro ψ _ hψ
        subst hψ
        exact hs'
      exact @key _ ha' f1
    · have := hcl (xb ≫ t) (IsLocalRing.closedPoint (kb p))
      exact ((Scheme.Hom.comp_apply xb t _).trans (congrArg t (hxb _))) ▸ this)
  exact ⟨k.1, k.2, Sg k, hk, fun x hx => hx.1 x rfl, fun x hx => hx.2⟩

end GlobalTheory.ZJ.DenseSplit
end
