import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ISupNonzeroLocusEmbH
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorFieldPointThroughGenericPoint
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpansionOfIntegralSectionIsIntegral
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionArithmetic
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.TorsionZeroCountTwist
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.GenAmple
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.SecEmb

theorem sec_eq_of_inj {X Y Y' : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} {s s' : LB.Sec (LB.LinComb L φ ε)} {h : Y' ⟶ Y}
    (hinj : ∀ W : Y.Opens, Function.Injective (h.app W).hom)
    (H : ∀ y J, Good L y J → sval s (𝟙 Y' ≫ h) y J = sval s' (𝟙 Y' ≫ h) y J) : s = s' := by
  have e : ∀ j, s.f j = s'.f j := fun j => by
    refine hinj _ (fn_ext fun y hy => ?_)
    choose J hJ using fun ψ : Y' ⟶ X => exists_chart hL (ψ y)
    have hJ' : Good L y J := hJ
    have hy' : (𝟙 Y' ≫ h) y ∈ LB.wchart L φ j := hy
    have m := hJ'.mem φ (𝟙 Y' ≫ h)
    refine (gs_pull (𝟙 Y') h y _ hy _).trans (Eq.trans ?_ (gs_pull (𝟙 Y') h y _ hy _).symm)
    exact (sec_trans s _ y hy' m).trans ((congrArg _ (H y J hJ')).trans (sec_trans s' _ y hy' m).symm)
  cases s
  cases s'
  congr
  exact funext e

end GlobalTheory.Mum.SecEmb

namespace GlobalTheory.Mum.SecEmb

theorem traitRed_cover : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R))
    (C C' : LabCover D) (Sc : Secs C.toModif C.G C.P.L.L C.α) (h : C'.S ⟶ C.S) (β : C'.G.left ⟶ C.G.left),
    h ≫ C.π = C'.π → IsGrpPullback C'.G C.G h β → LBIso C'.P.L.L (C.P.L.L.pull β) →
    ∀ σ : Fin (Sc.N + 1) → SecK C.P.L.L β Sc.k, (∀ i, Agree C.P.L.L (σ i) (Sc.s i)) →
    ∀ θ₀ : SecK C.P.L.L β 1, Agree C.P.L.L θ₀ Sc.θ →
    ∃ θ : C'.P.L.L.Sec, GlobalTheory.Mum.SecEmb.TraitRed C'.toModif C'.G σ θ Sc.Y Sc.j Sc.O := by
  intro R _ _ _ _ D C C' Sc h β hπ hpb hiso σ hσ θ₀ hθ₀
  have hL : C.P.L.L.IsLB := C.P.L.isLB
  obtain ⟨θ₁, hθ₁⟩ := exists_sec hL (φ := fun _ : Fin 1 => β) (ε := fun _ => ((1 : ℕ) : ℤ))
    (φ' := fun _ : PUnit => β) (ε' := fun _ => 1) (fun U _ g => by simp) θ₀
  obtain ⟨w, hw⟩ := hiso
  refine ⟨DVR.secOfIso (u := w) θ₁ hw C'.P.L.isLB (LB.isLB_pull hL β), ?_⟩
  intro W _ _ _ hW φ ξ hφ hloc hξ
  obtain ⟨W', _, _, _, io, G'', _, β'', σ'', θ'', κ, e, hW', hio, hfin, hG'', hκ, he, hσ'', hθ'', hfib⟩ :=
    Sc.trait W hW φ (ξ ≫ h) hφ hloc (by rw [Category.assoc, hπ]; exact hξ)
  obtain ⟨β', hβ'1, hβ'2⟩ : ∃ β' : G''.left ⟶ C'.G.left, β' ≫ β = β'' ∧ β' ≫ C'.G.hom = G''.hom ≫ spMap io ≫ ξ :=
    ⟨hpb.1.lift β'' (G''.hom ≫ spMap io ≫ ξ) (by rw [hG''.1.w]; simp), hpb.1.lift_fst _ _ _, hpb.1.lift_snd _ _ _⟩
  subst hβ'1

  have hρ : Function.Injective ((algebraMap W' (FractionRing W')).comp (io.comp φ)) :=
    (IsFractionRing.injective W' (FractionRing W')).comp (hio.comp hφ)
  obtain ⟨ga, -, hga⟩ := Modif.factor_gp R C.toModif (FractionRing W') _ (jK W' ≫ spMap io ≫ ξ ≫ h) hρ (by
    rw [Category.assoc, Category.assoc, Category.assoc, hπ, hξ]
    simp only [jK, spMap, ← Spec.map_comp]
    rfl)

  have : Smooth C.G.hom := C.semi.smooth
  have : Flat G''.hom := MorphismProperty.of_isPullback (P := @Flat) hG''.1 inferInstance

  have hgen : ∀ (Z : Scheme.{0}) (r : Z ⟶ pullback G''.hom (jK W')), ∃ q : Z ⟶ C.A.A.left,
      q ≫ C.α = r ≫ pullback.fst G''.hom (jK W') ≫ β' ≫ β := fun Z r => by
    refine ⟨C.α_cart.1.lift (r ≫ pullback.fst G''.hom (jK W') ≫ β' ≫ β)
      (r ≫ pullback.snd G''.hom (jK W') ≫ spMap ga) ?_, C.α_cart.1.lift_fst _ _ _⟩
    have w₁ := hG''.1.w
    simp only [Category.assoc] at w₁ ⊢
    rw [w₁, ← hga, pullback.condition_assoc]

  have key : ∀ {n : ℕ} (a : SecK C.P.L.L (β' ≫ β) n) (b : SecK C.P.L.L β n) (c : SecK C.P.L.L C.α n),
      Agree C.P.L.L a c → Agree C.P.L.L b c → ∀ (Z : Scheme.{0}) (r : Z ⟶ G''.left) (z : Z) (J), Good C.P.L.L z J →
        sval a r z J = sval b (r ≫ β') z J := by
    intro n a b c ha hb
    have e₁ : a = ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.pullSec b β' := by
      refine sec_eq_of_inj hL (GlobalTheory.ExpInt.generic_app_injective G'') fun y J hJ => ?_
      rw [ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.sval_pullSec _ _ _ _ hJ]
      obtain ⟨q, hq⟩ := hgen _ (𝟙 _)
      have hq' : q ≫ C.α = (𝟙 _ ≫ pullback.fst G''.hom (jK W')) ≫ β' ≫ β := by rw [hq]; simp
      refine (ha _ _ q hq'.symm y J hJ).trans (hb _ _ q ?_ y J hJ).symm
      rw [hq']; simp
    intro Z r z J hJ
    rw [e₁, ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.sval_pullSec _ _ _ _ hJ]
  have hv : ∀ i (Z : Scheme.{0}) (r : Z ⟶ G''.left) (z : Z) (J), Good C.P.L.L z J →
      sval (σ'' i) r z J = sval (σ i) (r ≫ β') z J := fun i => key _ _ _ (hσ'' i) (hσ i)
  have hvθ := key _ _ _ hθ'' hθ₀
  refine ⟨W', inferInstance, inferInstance, inferInstance, io, G'', inferInstance, β', κ, e, hW', hio, hfin,
    IsGrpPullback.cancel hpb (by rw [Category.assoc]; exact hG'') hβ'2, hκ, he, ?_⟩
  intro Ω _ p p' y hp hy
  obtain ⟨⟨hs, hproj⟩, hnz⟩ := hfib Ω p p' y hp hy
  have hnzi : ∀ (x : Sp Ω) i, p' x ∈ nonzeroLocus (σ'' i) ↔ (p' ≫ β') x ∈ nonzeroLocus (σ i) := fun x i => by
    choose J hJ using fun ψ : Sp Ω ⟶ C.G.left => exists_chart hL (ψ x)
    rw [GlobalTheory.TwistZero.mem_nonzeroLocus_iff _ _ _ hJ, GlobalTheory.TwistZero.mem_nonzeroLocus_iff _ _ _ hJ, hv i _ _ _ _ hJ]
  have ht : ⨆ i, nonzeroLocus (GlobalTheory.secPull (σ i) (p' ≫ β')) = ⊤ := by
    refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hs.ge (Set.mem_univ x))
    rw [GlobalTheory.nonzeroLocus_secPull] at hi
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨i, ?_⟩
    rw [GlobalTheory.nonzeroLocus_secPull]
    exact (hnzi x i).1 hi
  refine ⟨⟨ht, ?_⟩, fun x hx => ?_⟩
  · rw [← hproj]
    refine GlobalTheory.ProjSpace.toProj_eq_of_locally hs ht fun x => ?_
    obtain ⟨c, hc⟩ := exists_chart hL ((p' ≫ β' ≫ β) x)
    have m₁ : x ∈ (LB.pull (LB.LinComb C.P.L.L (fun _ : Fin 1 => β' ≫ β) (fun _ => (Sc.k : ℤ))) p').U
        (fun _ => fun _ => c) :=
      mem_pull.2 (Set.mem_iInter.2 fun _ => by simpa using hc)
    have m₂ : x ∈ (LB.pull (LB.LinComb C.P.L.L (fun _ : Fin 1 => β) (fun _ => (Sc.k : ℤ))) (p' ≫ β')).U
        (fun _ => fun _ => c) :=
      mem_pull.2 (Set.mem_iInter.2 fun _ => by simpa using hc)
    refine ⟨(LB.pull (LB.LinComb C.P.L.L (fun _ : Fin 1 => β' ≫ β) (fun _ => (Sc.k : ℤ))) p').U (fun _ => fun _ => c) ⊓
      (LB.pull (LB.LinComb C.P.L.L (fun _ : Fin 1 => β) (fun _ => (Sc.k : ℤ))) (p' ≫ β')).U (fun _ => fun _ => c),
      ⟨m₁, m₂⟩, _, inf_le_left, _, inf_le_right, 1, fun j => ?_⟩
    rw [_root_.one_mul]
    refine fn_ext fun z hz => ?_
    have hz' : (p' ≫ β' ≫ β) z ∈ C.P.L.L.U c := by
      have := Set.mem_iInter.1 (mem_pull.1 hz.1) 0
      simpa using this
    obtain ⟨J, hJ, eJ⟩ := exists_good C.P.L.L hL z (fun _ : PUnit => p' ≫ β' ≫ β) (fun _ => c)
      (fun _ _ _ => rfl) (fun _ => hz')
    rw [gs_res _ _ _ hz, gs_res _ _ _ hz]
    refine (GlobalTheory.gs_chartSec (GlobalTheory.chartPullPull _ _) (σ j) (𝟙 _) z _ hz.2).trans
      (Eq.trans ?_ (GlobalTheory.gs_chartSec (GlobalTheory.chartPullPull _ _) (σ'' j) (𝟙 _) z _ hz.1).symm)
    rw [Category.id_comp, Category.id_comp]
    exact (sval_of (σ j) (p' ≫ β') z J (fun _ => c) (fun _ => by rw [Category.assoc]; exact eJ ⟨⟩)).symm.trans
      ((hv j _ _ _ _ hJ).symm.trans (sval_of (σ'' j) p' z J (fun _ => c) (fun _ => eJ ⟨⟩)))
  · have h₁ := hnz x hx
    choose J hJ using fun ψ : Sp Ω ⟶ C.G.left => exists_chart hL (ψ x)
    rw [GlobalTheory.TwistZero.mem_nonzeroLocus_iff _ _ _ hJ, hvθ _ _ _ _ hJ] at h₁
    refine DVR.nonzeroLocus_secOfIso w θ₁ hw C'.P.L.isLB (LB.isLB_pull hL β) ?_
    rw [GlobalTheory.TwistZero.mem_nonzeroLocus_iff _ _ _ hJ, hθ₁ _ _ _ _ hJ]
    exact h₁

end GlobalTheory.Mum.SecEmb
