import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExponentialDerivativeAtZeroIsTangent
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsCombAtIffIsDerivAt0
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsEigAtIffOfIsDerivAt0
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.Flat.EigDir

open GlobalTheory.HolHom GlobalTheory.DerivEig

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {σK : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}

theorem isComb_iff_isCombAt (x : Sp ℂ ⟶ Xo.X) {n : ℕ} (c : Fin n → ℂ) (v : Fin n → (epsAt x ⟶ Xo.univ.t.G))
    (w : epsAt x ⟶ Xo.univ.t.G) :
    GlobalTheory.CompanionTheory.Ar.Fl.IsComb c v w ↔ Formalism.L2.Pj.IsCombAt x (fun i => (v i).left) c w.left := by
  constructor
  · rintro ⟨u, hu, hw⟩
    exact ⟨u, hu, by rw [hw]⟩
  · rintro ⟨u, hu, hw⟩
    exact ⟨u, hu, Over.OverMorphism.ext hw.symm⟩

theorem isTanAt_of_isEigVec (x : Sp ℂ ⟶ Xo.X) (χ : 𝓞 E →+* ℂ) (v : epsAt x ⟶ Xo.univ.t.G)
    (h : GlobalTheory.CompanionTheory.Ar.Fl.IsEigVec Xo.univ.t.act x χ v) : Formalism.L2.Pj.IsTanAt x v.left :=
  ⟨Over.w v, h.1⟩

theorem isEigVec_of_isDerivAt0 (FU : FamilyUnif Xo σK ty) (i : Fin FU.n) (P : (FU.Di i).La →+ (Fin g → ℂ))
    (hP : IsPeriod (FU.Di i) ty P) (χ : 𝓞 E →+* ℂ) (τ : E →+* ℂ) (hχ : ∀ a : 𝓞 E, χ a = τ (a : E))
    (w : Fin g → ℂ) (hw : ∀ k, w k ≠ 0 → ty k = τ) (v : epsAt (FU.u i P) ⟶ Xo.univ.t.G)
    (hv : IsDerivAt0 (fun z => (FU.ex i P z).left) w v.left) :
    GlobalTheory.CompanionTheory.Ar.Fl.IsEigVec Xo.univ.t.act (FU.u i P) χ v := by
  obtain ⟨h1, -, -⟩ := GlobalTheory.isDerivAt0_ex_isTanAt E H D l Xo σK g ty FU i P hP
  have hhol : HolAt (fun z => (FU.ex i P z).left) 0 := holAt_of_isHolTo (isHolTo_ex FU i hP) (Set.mem_univ 0)
  have hv' := (isDerivAt0_iff _ _ _).1 hv
  refine ⟨(h1 _ _ hv).2, fun a => ?_⟩
  let L : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ) :=
    ContinuousLinearMap.pi fun k => ty k (a : E) • ContinuousLinearMap.proj k
  have e1 := hv'.comp (Xo.univ.t.act.act a).left
  have e2 : (fun t => (FU.ex i P t).left ≫ (Xo.univ.t.act.act a).left) = fun t => (FU.ex i P (L t)).left := by
    funext t
    rw [← Over.comp_left, ← FU.ex_lin i P hP a t]
    rfl
  rw [e2] at e1
  have e3 := isDerivAt_of_comp_linear hhol L e1
  have e4 : L w = χ a • w := by
    funext k
    by_cases hk : w k = 0
    · simp [L, hk]
    · simp [L, hw k hk, hχ a]
  rw [e4] at e3
  exact e3.unique (isDerivAt_epsMul hv' _)

end GlobalTheory.CompanionTheory.Ar.Flat.EigDir

open GlobalTheory.CompanionTheory.Ar.Flat.EigDir in

theorem GlobalTheory.CompanionTheory.Ar.Flat.exists_directions_of_isEigFrame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σK : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo σK ty) (i : Fin FU.n) (P : (FU.Di i).La →+ (Fin g → ℂ)) (x : Sp ℂ ⟶ Xo.X) (χ : 𝓞 E →+* ℂ) (τ : E →+* ℂ) (n : ℕ) (v : Fin n → (epsAt x ⟶ Xo.univ.t.G)), IsPeriod (FU.Di i) ty P → x = FU.u i P → (∀ a : 𝓞 E, χ a = τ (a : E)) → IsEigFrame Xo.univ.t.act x χ v → ∃ V : Fin n → Fin g → ℂ, (∀ a u, IsDerivAt0 (fun z => (FU.ex i P z).left) u (v a).left ↔ u = V a) ∧ LinearIndependent ℂ V ∧ ∀ z, tyPart ty τ z ∈ Submodule.span ℂ (Set.range V) := by
  intro E _ _ _ H D l Xo σK g ty FU i P x χ τ n v hP hx hχ hF
  subst hx
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.isDerivAt0_ex_isTanAt E H D l Xo σK g ty FU i P hP
  have ht : ∀ a, Formalism.L2.Pj.IsTanAt (FU.u i P) (v a).left := fun a => isTanAt_of_isEigVec _ χ _ (hF.1 a)
  choose V hV hVu using fun a => h3 _ (ht a)
  have comb : ∀ (c : Fin n → ℂ) (w : epsAt (FU.u i P) ⟶ Xo.univ.t.G),
      GlobalTheory.CompanionTheory.Ar.Fl.IsComb c v w ↔ IsDerivAt0 (fun z => (FU.ex i P z).left) (∑ k, c k • V k) w.left := fun c w =>
    (isComb_iff_isCombAt _ c v w).trans
      (GlobalTheory.DerLin.isCombAt_iff_isDerivAt0 E H D l Xo σK g ty FU i P hP n (fun k => (v k).left) V hV c w.left)
  refine ⟨V, fun a u => ⟨fun h => hVu a u h, fun h => h ▸ hV a⟩, ?_, fun z => ?_⟩
  · refine Fintype.linearIndependent_iff.2 fun c hc => ?_
    obtain ⟨w, hw, -⟩ := (FU.ex_diff i P hP).1 0
    have hw' : GlobalTheory.CompanionTheory.Ar.Fl.IsEigVec Xo.univ.t.act (FU.u i P) χ w :=
      isEigVec_of_isDerivAt0 FU i P hP χ τ hχ 0 (fun k hk => absurd rfl hk) w hw
    obtain ⟨c₀, -, hu⟩ := hF.2 w hw'
    have a1 := hu c ((comb c w).2 (by rw [hc]; exact hw))
    have a2 := hu 0 ((comb 0 w).2 (by simpa using hw))
    intro k
    exact congrFun (a1.trans a2.symm) k
  · obtain ⟨w, hw, -⟩ := (FU.ex_diff i P hP).1 (tyPart ty τ z)
    have hw' : GlobalTheory.CompanionTheory.Ar.Fl.IsEigVec Xo.univ.t.act (FU.u i P) χ w :=
      isEigVec_of_isDerivAt0 FU i P hP χ τ hχ _ (fun k hk => ?_) w hw
    · obtain ⟨c, hc, -⟩ := hF.2 w hw'
      have e := (h3 _ (isTanAt_of_isEigVec _ χ _ hw')).unique ((comb c w).1 hc) hw
      rw [← e]
      exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
    · by_contra hne
      exact hk (by simp [tyPart, hne])
