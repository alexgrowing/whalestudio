import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlopeBoundSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsAbLift
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.Taylor
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.QuotLoc

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.Flat

section Curve

variable {R : Type} [CommRing R] {n : ℕ} {ψ : (Fin n → ℂ) → (R →+* ℂ)} {z : Fin n → ℂ}

def diagLine (z : Fin n → ℂ) (T : ℂ) : Fin n → ℂ := fun i => z i + T

theorem diagLine_zero (z : Fin n → ℂ) : diagLine z 0 = z := by
  funext i; simp [diagLine]

theorem diagLine_mem_ball (hz : z ∈ Metric.ball (0 : Fin n → ℂ) 1) {T : ℂ}
    (hT : T ∈ Metric.ball (0 : ℂ) (1 - ‖z‖)) : diagLine z T ∈ Metric.ball (0 : Fin n → ℂ) 1 := by
  rw [mem_ball_zero_iff] at hT ⊢
  rw [pi_norm_lt_iff one_pos]
  intro i
  have h₁ := norm_le_pi_norm z i
  calc ‖z i + T‖ ≤ ‖z i‖ + ‖T‖ := norm_add_le _ _
    _ < 1 := by linarith

theorem analyticOnNhd_diagLine (h : IsHolPts (Metric.ball 0 1) ψ) (hz : z ∈ Metric.ball (0 : Fin n → ℂ) 1) (x : R) :
    AnalyticOnNhd ℂ (fun T => ψ (diagLine z T) x) (Metric.ball (0 : ℂ) (1 - ‖z‖)) := by
  have hl : DifferentiableOn ℂ (diagLine z) (Metric.ball (0 : ℂ) (1 - ‖z‖)) :=
    (differentiable_pi.2 fun i => (differentiable_const (z i)).add differentiable_id).differentiableOn
  exact ((h.2 x).comp hl fun T hT => diagLine_mem_ball hz hT).analyticOnNhd Metric.isOpen_ball

theorem zero_mem_ball_norm (hz : z ∈ Metric.ball (0 : Fin n → ℂ) 1) : (0 : ℂ) ∈ Metric.ball (0 : ℂ) (1 - ‖z‖) := by
  have := mem_ball_zero_iff.1 hz
  simpa using this

theorem analyticAt_diagLine (h : IsHolPts (Metric.ball 0 1) ψ) (hz : z ∈ Metric.ball (0 : Fin n → ℂ) 1) (x : R) :
    AnalyticAt ℂ (fun T => ψ (diagLine z T) x) 0 :=
  analyticOnNhd_diagLine h hz x 0 (zero_mem_ball_norm hz)

def taylorHom (h : IsHolPts (Metric.ball 0 1) ψ) (hz : z ∈ Metric.ball (0 : Fin n → ℂ) 1) : R →+* PowerSeries ℂ where
  toFun x := Formalism.L2.Th1.F.taylor0 (fun T => ψ (diagLine z T) x)
  map_one' := by
    simp only [map_one]
    rw [Formalism.L2.Th1.F.Taylor.taylor0_const, map_one]
  map_zero' := by
    simp only [map_zero]
    rw [Formalism.L2.Th1.F.Taylor.taylor0_const, map_zero]
  map_mul' x y := by
    simp only [map_mul]
    exact Formalism.L2.Th1.F.Taylor.taylor0_mul (analyticAt_diagLine h hz x) (analyticAt_diagLine h hz y)
  map_add' x y := by
    simp only [map_add]
    exact Formalism.L2.Th1.F.Taylor.taylor0_add (analyticAt_diagLine h hz x) (analyticAt_diagLine h hz y)

theorem constantCoeff_comp_taylorHom (h : IsHolPts (Metric.ball 0 1) ψ) (hz : z ∈ Metric.ball (0 : Fin n → ℂ) 1) :
    (PowerSeries.constantCoeff (R := ℂ)).comp (taylorHom h hz) = ψ z := by
  ext x
  have e := Formalism.L2.Th1.F.Taylor.coeff_taylor0 (fun T => ψ (diagLine z T) x) 0
  simp only [iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, div_one, diagLine_zero, PowerSeries.coeff_zero_eq_constantCoeff_apply] at e
  exact e

theorem eq_zero_of_taylorHom (h : IsHolPts (Metric.ball 0 1) ψ) (hz : z ∈ Metric.ball (0 : Fin n → ℂ) 1) {x : R}
    (hx : taylorHom h hz x = 0) {T : ℂ} (hT : T ∈ Metric.ball (0 : ℂ) (1 - ‖z‖)) : ψ (diagLine z T) x = 0 := by
  have h₀ : Formalism.L2.Th1.F.taylor0 (fun T => ψ (diagLine z T) x) = Formalism.L2.Th1.F.taylor0 (fun _ => (0 : ℂ)) := by
    rw [Formalism.L2.Th1.F.Taylor.taylor0_const, map_zero]
    exact hx
  have he := Formalism.L2.Th1.F.Taylor.taylor0_inj (analyticAt_diagLine h hz x) analyticAt_const h₀
  exact (analyticOnNhd_diagLine h hz x).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (convex_ball _ _).isPreconnected (zero_mem_ball_norm hz) he hT

theorem exists_diagLine_mem_punct (a : ℕ) (hz : z ∈ Metric.ball (0 : Fin n → ℂ) 1) :
    ∃ T ∈ Metric.ball (0 : ℂ) (1 - ‖z‖), diagLine z T ∈ punct n a 1 := by
  have hinf : (Metric.ball (0 : ℂ) (1 - ‖z‖)).Infinite :=
    infinite_of_mem_nhds 0 (Metric.isOpen_ball.mem_nhds (zero_mem_ball_norm hz))
  obtain ⟨T, hT, hn⟩ := hinf.exists_notMem_finset (Finset.univ.image fun i : Fin n => -z i)
  refine ⟨T, hT, diagLine_mem_ball hz hT, fun i _ he => hn ?_⟩
  refine Finset.mem_image.2 ⟨i, Finset.mem_univ _, ?_⟩
  have : z i + T = 0 := he
  linear_combination -this

end Curve

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

theorem range_jK_taylorHom_subset {Xo : Moduli D l} {σ : KA l →+* ℂ} {n a : ℕ} (C : Flat.BdryChart Xo σ n a)
    {z : Fin n → ℂ} (hz : z ∈ Metric.ball (0 : Fin n → ℂ) 1) :
    Set.range (Out.jK (PowerSeries ℂ) ≫ spMap (taylorHom C.hol hz)) ⊆ Set.range C.j := by
  have := C.j_open
  rintro _ ⟨q, rfl⟩
  obtain ⟨T, hT, hp⟩ := exists_diagLine_mem_punct a hz
  obtain ⟨s⟩ : Nonempty (Sp ℂ) := inferInstance
  have hw : spMap (C.ψ (diagLine z T)) s ∈ Set.range C.j :=
    ⟨C.pt (diagLine z T) s, by rw [← (C.pt_eq _ hp).1, Scheme.Hom.comp_apply]⟩
  refine Specializes.mem_open ?_ C.j.isOpenEmbedding.isOpen_range hw
  refine (PrimeSpectrum.le_iff_specializes _ _).1 fun x hx => ?_
  have hq : q.asIdeal = ⊥ := (Ideal.eq_bot_or_top q.asIdeal).resolve_right q.isPrime.ne_top
  rw [Scheme.Hom.comp_apply] at hx
  have h₁ : algebraMap (PowerSeries ℂ) (FractionRing (PowerSeries ℂ)) (taylorHom C.hol hz x) ∈ q.asIdeal := hx
  rw [hq, Ideal.mem_bot, map_eq_zero_iff _ (IsFractionRing.injective _ _)] at h₁
  have h₂ : C.ψ (diagLine z T) x = 0 := eq_zero_of_taylorHom C.hol hz h₁ hT
  show C.ψ (diagLine z T) x ∈ s.asIdeal
  rw [h₂]
  exact Ideal.zero_mem _

section Pulled

open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem polAt_of_pulled {S S' X : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {f : S' ⟶ S} (m : SABMap t' t f)
    {K : Type} [Field K] {tK : SAB H (Sp K)} {j : Sp K ⟶ S} (mK : SABMap tK t j)
    {u : SAB H X} {x : Sp K ⟶ X} (mx : SABMap tK u x) (hp : IsProper u.G.hom) (ha : Out.RelAmple u.G u.PP.L)
    (hk : Out.KTriv u.G u.PP.L) (j' : Sp K ⟶ S') (h : j' ≫ f = j) : GlobalTheory.LN.PolAt t' j' := by
  obtain ⟨PP', cub, sym, adj, prim, m₂, hm₂⟩ := sabPull Out.CubePf.cubePull j' t'
  obtain ⟨n, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m m₂
  have cancel : ∀ (t₂ : SAB H (Sp K)) (p : Sp K ⟶ S) (_ : p = 𝟙 _ ≫ j) (_ : SABMap t₂ t p),
      Nonempty (SABMap t₂ u (𝟙 _ ≫ x)) := by
    intro t₂ p hp n
    subst hp
    exact ⟨(sabComp pullCubComp E H _ _ _ _ _ _ _ _ mx
      (sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ mK n).choose).choose⟩
  obtain ⟨m₃⟩ := cancel _ _ (h.trans (Category.id_comp _).symm) n
  have h₂ : LBIso PP'.L (t'.PP.L.pull m₂.φ) := m₂.lin.imp fun _ h => h.1
  rw [hm₂] at h₂
  have h₃ : LBIso PP'.L (u.PP.L.pull m₃.φ) := m₃.lin.imp fun _ h => h.1
  have hL := LB.isLB_pull t'.PP.isLB (pullback.fst t'.G.hom j')
  exact ⟨MorphismProperty.of_isPullback (P := @IsProper) m₃.cart.1 hp,
    amplePt _ _ (𝟙 _ ≫ x) _ _ m₃.φ m₃.cart _ _ u.PP.isLB hL
      (LBIso.trans hL PP'.isLB (LB.isLB_pull u.PP.isLB _) h₂.symm h₃) ha hk⟩

end Pulled

theorem exists_curve_through_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (n a : ℕ) (C : Flat.BdryChart Xo σ n a) (z : Fin n → ℂ), z ∈ Metric.ball (0 : Fin n → ℂ) 1 → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V) (f : C.R →+* V) (r : V →+* ℂ) (tV : SAB H (Sp V)) (_ : SABMap tV C.t (spMap f)), GlobalTheory.LN.CDvr V ∧ Function.Surjective r ∧ RingHom.ker r = IsLocalRing.maximalIdeal V ∧ r.comp f = C.ψ z ∧ GlobalTheory.LN.PolAt tV (Out.jK V) := by
  intro E _ _ _ H D l Xo σ n a C z hz
  have := C.j_open
  obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull (spMap (taylorHom C.hol hz)) C.t
  have hc : GlobalTheory.LN.CDvr (PowerSeries ℂ) :=
    ⟨inferInstance, by rw [PowerSeries.maximalIdeal_eq_span_X]; infer_instance, algebraRat.charZero _⟩
  have hsurj : Function.Surjective (PowerSeries.constantCoeff (R := ℂ)) := fun c =>
    ⟨PowerSeries.C c, by simp⟩
  refine ⟨PowerSeries ℂ, inferInstance, inferInstance, inferInstance, taylorHom C.hol hz,
    PowerSeries.constantCoeff (R := ℂ), _, m, hc, hsurj, ?_, constantCoeff_comp_taylorHom C.hol hz, ?_⟩
  · have := RingHom.ker_isMaximal_of_surjective _ hsurj
    exact IsLocalRing.eq_maximalIdeal this
  · have hr := range_jK_taylorHom_subset C hz
    let y := IsOpenImmersion.lift C.j _ hr
    have hy : y ≫ C.j = Out.jK (PowerSeries ℂ) ≫ spMap (taylorHom C.hol hz) := IsOpenImmersion.lift_fac _ _ _
    obtain ⟨_, _, _, _, _, m₀, -⟩ := sabPull Out.CubePf.cubePull y C.tV
    obtain ⟨mK, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ C.m₁ m₀
    obtain ⟨mx, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ C.m₂ m₀
    exact polAt_of_pulled m mK mx Xo.univ.proper Xo.univ.ample Xo.univ.ktriv (Out.jK (PowerSeries ℂ)) hy.symm

end GlobalTheory.CompanionTheory.Ar.QuotLoc
