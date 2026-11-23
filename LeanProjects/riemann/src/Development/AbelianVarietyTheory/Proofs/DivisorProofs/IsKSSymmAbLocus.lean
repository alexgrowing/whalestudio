import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResV
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerMatrixTransposeEqAtPolarizedPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpMapDualMapCompEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartFrameBaseHolds
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkBaseChange
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HeatV

theorem isKS_symm_abLocus : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (m : ℕ) (tt : Fin m → R), (∀ i, tt i ≠ 0) → (∀ p : Sp R, p ∈ abLocus t.G ↔ ∏ i, tt i ∉ p.asIdeal) → ∀ (c : R), c = ∏ i, tt i → ∀ (n : ℕ) (v' : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) t.G)) (dd' : Fin n → Fld t.G.left), (∀ a, IsInv t.G (v' a) (dd' a)) → ∀ (DV : Γ(Sp R, (GlobalTheory.HeatV.bo R c).1) → Γ(Sp R, (GlobalTheory.HeatV.bo R c).1)) (Θ₁ : Matrix (Fin n) (Fin n) Γ(Sp R, (GlobalTheory.HeatV.bo R c).1)), IsKS t (GlobalTheory.HeatV.bo R c).1 (GlobalTheory.HeatV.bo R c) (fun a => spMap (dualMap (GlobalTheory.HeatV.resV R c)) ≫ (tv (v' a)).left) DV Θ₁ → Θ₁ᵀ = Θ₁ := by
  intro E _ _ _ H R _ _ _ _ _ _ t P m tt htt hab c hc n v' dd' hinv DV Θ₁ hKS

  have hc' : spMap (resV R c) ≫ 𝟙 (Sp R) = chart (bo R c) := by
    rw [Category.comp_id]; exact spMap_resV R c
  obtain ⟨hv, hb⟩ : (∀ i, IsTanAtG t (spMap (resV R c) ≫ 𝟙 (Sp R))
        (spMap (dualMap (resV R c)) ≫ (tv (v' i)).left)) ∧
      ∀ w, IsTanAtG t (spMap (resV R c) ≫ 𝟙 (Sp R)) w →
        ∃! a : Fin n → Γ(Sp R, (bo R c).1), IsCombAtG t (spMap (resV R c) ≫ 𝟙 (Sp R))
          (fun i => spMap (dualMap (resV R c)) ≫ (tv (v' i)).left) a w := by
    refine GlobalTheory.LocM.FrameBase.tanBasis_baseChange t (resV R c) (𝟙 (Sp R)) n _
      (fun i => GlobalTheory.LieMet.isTan_tv (v' i)) ?_
    intro w hw
    refine ⟨v'.repr (GlobalTheory.LieMet.tanOf hw), ?_, fun a ha => ?_⟩
    · show IsCombAtG t _ _ _ (tv (GlobalTheory.LieMet.tanOf hw)).left
      rw [GlobalTheory.LieMet.isComb_iff]
      exact (v'.sum_repr _).symm
    · have h := (GlobalTheory.LieMet.isComb_iff v' a (GlobalTheory.LieMet.tanOf hw)).1 ha
      rw [h]
      ext i
      simp [Finsupp.single_apply]
  rw [hc'] at hv hb

  have hc0 : c ≠ 0 := by
    rw [hc]; exact Finset.prod_ne_zero_iff.2 fun i _ => htt i
  let s : Γ(Sp R, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c
  let gg : Γ(Sp R, ⊤) →+* FractionRing R :=
    (algebraMap R (FractionRing R)).comp (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom
  have hs : (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom s = c := by simp [s]
  have hu : IsUnit (gg s) := by
    rw [isUnit_iff_ne_zero]
    simp only [gg, RingHom.comp_apply, hs]
    exact (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hc0))
  have gg_inj : Function.Injective gg := by
    intro x y h
    have h1 := IsFractionRing.injective R (FractionRing R) h
    simpa using congrArg (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom h1
  let x₀ : Γ(Sp R, (bo R c).1) →+* FractionRing R :=
    IsLocalization.Away.lift (S := Γ(Sp R, (Sp R).basicOpen s)) s hu
  have hx₀ : ∀ y, x₀ (algebraMap Γ(Sp R, ⊤) Γ(Sp R, (Sp R).basicOpen s) y) = gg y := by
    intro y
    show IsLocalization.Away.lift (S := Γ(Sp R, (Sp R).basicOpen s)) s hu _ = _
    rw [IsLocalization.Away.lift, IsLocalization.lift_eq]
  have hinj : Function.Injective x₀ := by
    show Function.Injective (IsLocalization.Away.lift (S := Γ(Sp R, (Sp R).basicOpen s)) s hu)
    rw [IsLocalization.Away.lift, IsLocalization.lift_injective_iff]
    intro x y
    constructor
    · intro h
      have := congrArg x₀ h
      rwa [hx₀, hx₀] at this
    · intro h
      rw [gg_inj h]
  have hres : x₀.comp (resV R c) = algebraMap R (FractionRing R) := by
    ext r
    show x₀ (algebraMap Γ(Sp R, ⊤) Γ(Sp R, (Sp R).basicOpen s) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) = _
    rw [hx₀]
    simp [gg]
  have hsp : spMap x₀ ≫ chart (bo R c) = ReciprocityTheory.ChartRestriction.G.Out.jK R := by
    rw [← spMap_resV R c]
    show Spec.map (CommRingCat.ofHom x₀) ≫ Spec.map (CommRingCat.ofHom (resV R c)) =
      Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))
    rw [← hres, ← Spec.map_comp]
    rfl

  have gpG := GlobalTheory.ThetaBaseChange.grp_generic P.U.toUnifPre
  have hgi : P.U.gen.inv.left ≫ P.U.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have hext : LBIso (P.A.L.pull P.U.gen.hom.left)
      (t.PP.L.pull (pullback.fst t.G.hom (ReciprocityTheory.ChartRestriction.G.Out.jK R))) := by
    have h := P.U.ext
    rw [P.bundle] at h
    exact h
  have hL : LBIso P.A.L (t.PP.L.pull (P.U.gen.inv.left ≫ pullback.fst t.G.hom (ReciprocityTheory.ChartRestriction.G.Out.jK R))) := by
    have h1 : LBIso (P.A.L.pull (P.U.gen.inv.left ≫ P.U.gen.hom.left))
        (t.PP.L.pull (P.U.gen.inv.left ≫ pullback.fst t.G.hom (ReciprocityTheory.ChartRestriction.G.Out.jK R))) :=
      LBIso.chartPull (chartPullSame P.A.L _ (fun _ => P.U.gen.hom.left) _ P.U.gen.inv.left fun _ => rfl)
        (chartPullSame t.PP.L _ (fun _ => pullback.fst t.G.hom (ReciprocityTheory.ChartRestriction.G.Out.jK R)) _ P.U.gen.inv.left
          fun _ => rfl) hext
    exact LBIso.chartPull (chartPullUnpull P.A.L _ hgi)
      (chartPullSame t.PP.L _ _ _ (𝟙 _) fun _ => (Category.id_comp _).symm) h1
  haveI : CharZero R := charZero_of_injective_algebraMap (algebraMap ℚ R).injective
  haveI : CharZero (FractionRing R) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective R (FractionRing R))
  have key := GlobalTheory.T.kodairaSpencer_matrix_transpose_eq_at_polarized_point E H (Sp R) t (bo R c).1 (bo R c) n _ hv hb (FractionRing R) x₀ P.A
    (P.U.gen.inv.left ≫ pullback.fst t.G.hom (ReciprocityTheory.ChartRestriction.G.Out.jK R)) (gpG.congr hsp.symm rfl) hL le_rfl DV Θ₁ hKS
  ext a b
  apply hinj
  have := congrFun (congrFun key a) b
  simpa [Matrix.transpose_apply, Matrix.map_apply] using this

end GlobalTheory.HeatV
