import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RealisesEtaleFCrystalPullbackGaloisStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPrismGaloisLiftIsPrismHomStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoversTameActsRingEndoWittPowerSeriesStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section
namespace GlobalTheory.GKinfStable
variable {l : ℕ} [hl : Fact l.Prime]

theorem map_field_le (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (he : e + 1 = l ^ a) (g : GQ l)
    {x : Om l} (hx : x ∈ (ϖ.field a).1) : g x ∈ (ϖ.field a).1 := by
  have hd : e ∣ l ^ a - 1 := ⟨1, by omega⟩
  have := ϖ.isGalois_field a hd
  exact (IntermediateField.normal_iff_forall_map_le'.1 inferInstance g) ⟨x, hx, rfl⟩

theorem conj_mem (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (he : e + 1 = l ^ a) (g : GQ l) :
    ∀ h ∈ GK (ϖ.field a), g⁻¹ * h * g ∈ GK (ϖ.field a) := by
  intro h hh
  refine (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun x hx => ?_
  have h1 := (IntermediateField.mem_fixingSubgroup_iff _ _).1 hh (g x) (map_field_le a e ϖ he g hx)
  simp only [AlgEquiv.mul_apply, h1]
  rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]

theorem res_exists (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (he : e + 1 = l ^ a) (g : GQ l) :
    ∃ σ : ↥(OL (ϖ.field a)) →+* ↥(OL (ϖ.field a)),
      ∀ x, (((σ x : ↥(ϖ.field a).1) : Om l)) = g ((x : ↥(ϖ.field a).1) : Om l) := by
  let F := (ϖ.field a).1
  let φ : ↥F →ₐ[ℚ_[l]] ↥F :=
    { toFun := fun y => ⟨g y, map_field_le a e ϖ he g y.2⟩
      map_one' := Subtype.ext (map_one g : g (1 : Om l) = 1)
      map_mul' := fun y z => Subtype.ext (map_mul g (y : Om l) (z : Om l))
      map_zero' := Subtype.ext (map_zero g : g (0 : Om l) = 0)
      map_add' := fun y z => Subtype.ext (map_add g (y : Om l) (z : Om l))
      commutes' := fun q => Subtype.ext (g.commutes q) }
  refine ⟨{ toFun := fun x => ⟨φ x, x.2.map (φ.restrictScalars ℤ_[l])⟩
            map_one' := Subtype.ext (map_one φ : φ (1 : ↥F) = 1)
            map_mul' := fun y z => Subtype.ext (map_mul φ (y : ↥F) (z : ↥F))
            map_zero' := Subtype.ext (map_zero φ : φ (0 : ↥F) = 0)
            map_add' := fun y z => Subtype.ext (map_add φ (y : ↥F) (z : ↥F)) }, fun x => rfl⟩

theorem kappa_act {LL : FinExt l} (T : QLat LL) (g : Gl l) (z : letI := zlLat T; WCb l ⊗[ℤ_[l]] ↥T.L.T) :
    letI := zlLat T
    TWact (galOW (↥(OL LL)) (sQ l g)) T g (kappa T z) =
      kappa T (TensorProduct.map (galW l (sQ l g)).toLinearMap (actZ T g) z) := by
  letI := zlLat T
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul w x => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem actZ_mul_apply {LL : FinExt l} (T : QLat LL) (g h : Gl l) (x : ↥T.L.T) :
    letI := zlLat T
    actZ T g (actZ T h x) = actZ T (g * h) x :=
  Subtype.ext (LinearMap.congr_fun (map_mul T.ρ g h) (x : T.V)).symm

theorem actZ_one_apply {LL : FinExt l} (T : QLat LL) (x : ↥T.L.T) :
    letI := zlLat T
    actZ T 1 x = x :=
  Subtype.ext (LinearMap.congr_fun (map_one T.ρ) (x : T.V))

end GlobalTheory.GKinfStable

open GlobalTheory.GKinfStable in

theorem GlobalTheory.GKinfStable.main : GlobalTheory.Published.BhattScholzeCrystallineLattices → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T), IsBK (T := resF T (ϖ.field a)) (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)) → ∀ (g : Gl l) (γ : TameGal ↥LL.1 l e a), Covers ↥LL.1 (thetaW a LL) ϖ (sQ l g) γ → ∀ v : ME P, v.1 ∈ P.M → ∃ v' : ME P, v'.1 ∈ P.M ∧ I.act (sQ l g) g (toW (thetaW a LL) ϖ P v) = toW (thetaW a LL) ϖ P v' := by
  intro BS l _ a e _ _ ϖ LL _ _ ι _ _ P T I hBK g γ hcov v hv
  have he : e + 1 = l ^ a := TameDescentExponentData.succ_eq (K := ↥LL.1)
  choose σ hσ using res_exists (l := l) a e ϖ he (sQ l g)
  choose ψ hψ using GlobalTheory.T.covers_tame_acts_ringEndo_wittPowerSeries a e ϖ LL (sQ l g) γ hcov
  choose H hH using GlobalTheory.T.breuilKisinPrism_galoisLift_isPrismHom a e ϖ (sQ l g) σ hσ ψ hψ
  letI := zlLat T
  obtain ⟨E, j, hR, hiff⟩ := hBK
  let ρg : ↥T.L.T ≃ₗ[ℤ_[l]] ↥T.L.T :=
    LinearEquiv.ofLinear (actZ T g) (actZ T g⁻¹)
      (LinearMap.ext fun x => (actZ_mul_apply T g g⁻¹ x).trans
        ((congrArg (fun k => actZ T k x) (mul_inv_cancel g)).trans (actZ_one_apply T x)))
      (LinearMap.ext fun x => (actZ_mul_apply T g⁻¹ g x).trans
        ((congrArg (fun k => actZ T k x) (inv_mul_cancel g)).trans (actZ_one_apply T x)))
  have hPR := GlobalTheory.T.realisesEtaleFCrystal_pullback_galois (ϖ.field a) E ↥T.L.T _ j hR (sQ l g) σ hσ
    (conj_mem (l := l) a e ϖ he (sQ l g)) ρg (fun h h' hh x => by
      have e2 : g * inclG (ϖ.field a) h' = inclG (ϖ.field a) h * g := by
        rw [show inclG (ϖ.field a) h' = g⁻¹ * inclG (ϖ.field a) h * g from Subtype.ext hh]
        group
      exact (actZ_mul_apply T g _ x).trans ((congrArg (fun k => actZ T k x) e2).trans
        (actZ_mul_apply T _ g x).symm))
  choose gH j' hgH hR' hj' using hPR
  have hBS := (BS l (ϖ.field a) (ainfObj _) (ainfId _) (isAinf_ainfObj _)).2 ↥T.L.T ↥T.L.T _ _
    (E.pullback σ) E j' j hR' hR LinearMap.id (fun _ _ => rfl)
  choose u hu using hBS.exists
  have hx := (hiff (I.j (toW (thetaW a LL) ϖ P v))).2 ⟨v.1, hv, rfl⟩
  choose x hx using hx
  have hm := (hiff (kappa T (j (E.tr (ϖ.toAinf a) (u.u (ϖ.prism a) (E.tr H x)))))).1 ⟨_, rfl⟩
  choose m' hm' hm'eq using hm
  have e1 : gH.comp (ϖ.toAinf a) = ((ϖ.toAinf a).restrict σ).comp H :=
    Hom.ext' (RingHom.ext fun y => by
      change gH.f (ϖ.ev a y) = ϖ.ev a (H.f y)
      rw [hH]
      exact (hgH _).trans (hψ y).symm)
  have key : TensorProduct.map (galW l (sQ l g)).toLinearMap (actZ T g) (j (E.tr (ϖ.toAinf a) x)) =
      j (E.tr (ϖ.toAinf a) (u.u (ϖ.prism a) (E.tr H x))) := by
    have h2 : j (u.u (ainfObj _) ((E.pullback σ).tr (ϖ.toAinf a) (E.tr H x))) =
        j' ((E.pullback σ).tr (ϖ.toAinf a) (E.tr H x)) := by
      refine (hu _).trans ?_
      exact LinearMap.lTensor_id_apply _ _ _
    refine (hj' (E.tr (ϖ.toAinf a) x)).symm.trans ?_
    refine Eq.trans ?_ ((congrArg j (u.u_tr (ϖ.toAinf a) (E.tr H x))).symm.trans h2).symm
    refine congrArg j' ?_
    refine ((E.tr_comp _ _ x).symm).trans ?_
    refine (congrArg (fun f => E.tr f x) e1).trans ?_
    exact E.tr_comp _ _ x
  refine ⟨⟨m', mem_ME_of_mem_M hm'⟩, hm', ?_⟩
  apply I.j.injective
  refine (Ident.j_act _ _ _ _).trans ?_
  refine Eq.trans ?_ hm'eq
  refine (congrArg (TWact (galOW (↥(OL LL)) (sQ l g)) T g) hx).trans ?_
  exact (kappa_act T g _).trans (congrArg _ key)
