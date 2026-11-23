import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EightDvdNCol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.CongModRefl
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IntegralOfFramedPointOverIntegral
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.LiftBaseChange
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPullbackSectionToLevelCover
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.RelativeGroupHatForm

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CoverDown

section Integral

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ} (d : DeltaDat Xo c n)

theorem integral_below (T : CDVR) (io : c.F →+* T.Fr) (io₂ : d.c₂.F →+* T.Fr) (hio : ∀ a : c.F, io₂ (d.eF a) = io a)
    (y : letI := io.toAlgebra; FrPt Xo c T.Fr) (y₂ : letI := io₂.toAlgebra; FrPt d.Xo₂ d.c₂ T.Fr)
    (hy : letI := io.toAlgebra; letI := io₂.toAlgebra; FrOver d y₂ y) (h : Integral T io₂ y₂) : Integral T io y := by
  letI := io.toAlgebra
  letI := io₂.toAlgebra
  obtain ⟨G, t', m1, m2, ⟨ub, b1, b2, b3, b4⟩, θ, hθ, w1, w2, σ, s1, θ2, r1, r2, i1, i2, p2, hg⟩ := h
  obtain ⟨e, hu, w, p, hw, p₁, p₂, R⟩ := (FrameLift.frOver_iff d y₂ y).1 hy
  obtain ⟨m', e₁⟩ := LiftBaseChange.exists_comp' d.m m1 y.x e.symm
  have eig : ∀ τ v, Formalism.L2.Pj.IsEigV d.c₂ io₂ G τ v ↔ Formalism.L2.Pj.IsEigV c io G τ v := fun τ v =>
    forall_congr' fun a => forall_congr' fun z => by rw [← FrameLift.embK_eF d τ a, hio]
  obtain ⟨w', r', tri⟩ := LiftBaseChange.rigIso_comp d.m m1 m' e.symm e₁ (w := w) hw r1
  obtain ⟨s', hs'⟩ := thf_secUp ((isGen_iff w').1 r'.1) Xo.univ.t.PP.isLB t'.PP.isLB σ
  refine ⟨G, t', m', m2, ⟨ub, b1, fun τ i => (eig τ _).1 (b2 τ i), fun τ v h1 h2 => b3 τ v h1 ((eig τ v).2 h2),
    fun τ i => ?_⟩, θ, hθ, w', w2, σ, s', θ2, r', r2,
    (ArcQ.FrUniq.isoMaps_iff w' σ s').2 fun Z r z j k hj hk => hs' Z r z (fun _ => j) k (mem_pull.2 hj) hk,
    i2, p2, ?_⟩
  · obtain ⟨q, h2, h3⟩ := b4 τ i
    exact ⟨q, by rw [e₁, ← Category.assoc, h2, hu], h3⟩
  · intro g g₁ g₂ (J : PUnit → Xo.univ.t.PP.L.ι) hJ
    obtain ⟨g', a₁, a₂⟩ := FrameLift.exists_pm (G := d.Xo₂.univ.t.G) (x := y₂.x) t'.G.hom m1.φ m1.cart.1.w.symm
    have eg : g' ≫ p = g := by
      refine FrameLift.pm_ext ?_ ?_
      · rw [Category.assoc, p₁, ← Category.assoc, a₁, g₁, e₁]
      · rw [Category.assoc, p₂, a₂, g₂]
    refine fn_ext fun z hz => ?_
    obtain ⟨k, hk⟩ := exists_chart t'.PP.isLB z
    obtain ⟨i, hi⟩ := exists_chart d.Xo₂.univ.t.PP.isLB (m1.φ z)
    have hj : m'.φ z ∈ Xo.univ.t.PP.L.U (J PUnit.unit) := mem_pull.1 hz
    have hj' : d.m.φ (m1.φ z) ∈ Xo.univ.t.PP.L.U (J PUnit.unit) :=
      (congrArg (· ∈ Xo.univ.t.PP.L.U (J PUnit.unit)) (FrameLift.pt_eq e₁ z)).mp hj
    have le : (d.Xo₂.univ.t.PP.L.pull m1.φ).U (fun _ => i) ≤ g' ⁻¹ᵁ (PPx y₂.x).U (fun _ => i) := fun q hq =>
      Set.mem_iInter.2 fun _ => (congrArg (· ∈ d.Xo₂.univ.t.PP.L.U i) (FrameLift.pt_eq a₁ q)).mpr (mem_pull.1 hq)
    have u₁ := (ArcQ.FrUniq.isoMaps_iff w1 σ s1).1 i1 _ (𝟙 _) z i k hi hk
    rw [hg g' a₁ a₂ (fun _ => i) le, gs_appLE g' _ _ le (𝟙 _) z (mem_pull.2 hi), Category.id_comp] at u₁
    have u₂ := R _ g' z (J PUnit.unit) i
      ((congrArg (fun t => d.m.φ t ∈ Xo.univ.t.PP.L.U (J PUnit.unit)) (FrameLift.pt_eq a₁ z)).mpr hj')
      ((congrArg (· ∈ d.Xo₂.univ.t.PP.L.U i) (FrameLift.pt_eq a₁ z)).mpr hi)
    rw [a₁, eg] at u₂
    have u₃ := tri _ (𝟙 _) z (J PUnit.unit) i k hj' hi hk
    rw [Category.id_comp] at u₃
    rw [hs' _ (𝟙 _) z J k hz hk, gs_appLE _ _ _ hJ (𝟙 _) z hz, Category.id_comp]
    refine Eq.trans ?_ (u₂.trans (congrArg _ u₁)).symm
    rw [← _root_.mul_assoc, ← Units.val_mul, ← u₃]

theorem evR_eq_of_pull {d : DeltaDat Xo c 0} {a : (E →+* ℂ) × ℕ → ℕ} {m : ℕ} {f : Rul Xo c} {g : Rul d.Xo₂ d.c₂}
    (hf : f ∈ sec Xo c a m) (hg : g ∈ sec d.Xo₂ d.c₂ a m) (h : GlobalTheory.LevPull.Pull d f g) {K : Type} [Field K]
    [Algebra c.F K] [Algebra d.c₂.F K] (hc : ∀ a : c.F, algebraMap d.c₂.F K (d.eF a) = algebraMap c.F K a)
    {y₂ : FrPt d.Xo₂ d.c₂ K} {y : FrPt Xo c K} (hy : FrOver d y₂ y) : evR d.Xo₂ d.c₂ g y₂ = evR Xo c f y := by
  let j : K →+* AlgebraicClosure K := algebraMap _ _
  letI : Algebra c.F (AlgebraicClosure K) := (j.comp (algebraMap c.F K)).toAlgebra
  letI : Algebra d.c₂.F (AlgebraicClosure K) := (j.comp (algebraMap d.c₂.F K)).toAlgebra
  let ψ : K →ₐ[c.F] AlgebraicClosure K := ⟨j, fun _ => rfl⟩
  let ψ₂ : K →ₐ[d.c₂.F] AlgebraicClosure K := ⟨j, fun _ => rfl⟩
  obtain ⟨z, hz⟩ := GlobalTheory.TransferCompare.frBC_framed Xo c K _ ψ y
  obtain ⟨z₂, hz₂⟩ := GlobalTheory.TransferCompare.frBC_framed d.Xo₂ d.c₂ K _ ψ₂ y₂
  have e := h (AlgebraicClosure K) (fun a => congrArg j (hc a)) z₂ z
    (GlobalTheory.FrameLift.frOver_map d (ψ := ψ) (ψ₂ := ψ₂) rfl hy hz hz₂)
  rw [GlobalTheory.SupLawProbe.evR_map (GlobalTheory.TransferCompare.evalWD_framed Xo c) f hf.1 ψ y
      (GlobalTheory.TransferCompare.allTest_framed Xo c K y) z hz,
    GlobalTheory.SupLawProbe.evR_map (GlobalTheory.TransferCompare.evalWD_framed d.Xo₂ d.c₂) g hg.1 ψ₂ y₂
      (GlobalTheory.TransferCompare.allTest_framed d.Xo₂ d.c₂ K y₂) z₂ hz₂] at e
  exact j.injective e

end Integral

open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum

theorem exists_intFr_below : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (d : DeltaDat Xo c 0), 1 ≤ Dw.p + Dw.q → d.IsLev → ((Dw.p ≠ Dw.q ∧ l.A = 1) ∨ GlobalTheory.ClsVal.Cmp.OverBase d) → ∀ (T : CDVR) (io₂ : d.c₂.F →+* T.Fr) (y₂ : IntFr d.Xo₂ d.c₂ T io₂), y₂.IsAlg → ∃ y : IntFr Xo c T (io₂.comp (d.eF : c.F →+* d.c₂.F)), y.IsAlg ∧ (∀ φ : ℝ, HasPhi y₂ φ → HasPhi y φ) ∧ ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ sec Xo c a n, ∀ g ∈ sec d.Xo₂ d.c₂ a n, GlobalTheory.LevPull.Pull d f g → evI y₂ g = evI y f := by
  intro E _ _ _ H Dw l Xo c d _ hlev hO T io₂ y₂ halg
  have hO' : GlobalTheory.ClsVal.Cmp.OverBase d := hO.elim (fun h => GlobalTheory.ClsVal.Cmp.overBase_of_ne h.1 h.2 d) id
  letI := io₂.toAlgebra
  letI := (io₂.comp (d.eF : c.F →+* d.c₂.F)).toAlgebra
  obtain ⟨y, hy⟩ := GlobalTheory.CovPull.below_exists d hO' (GlobalTheory.IndefiniteRowSideFullHecke.RelativeGroupHatForm.KA_le hlev.1) (S := T.Fr) (fun _ => rfl) y₂.1
  refine ⟨⟨y, GlobalTheory.TransferCompare.allTest_framed Xo c T.Fr y,
    integral_below d T _ io₂ (fun _ => rfl) y y₂.1 hy y₂.2.2⟩, halg, ?_, fun a n f hf g hg h => ?_⟩
  · rintro φ ⟨G, t', m1, m2, h⟩
    obtain ⟨m', -⟩ := LiftBaseChange.exists_comp' d.m m1 y.x hy.1.symm
    exact ⟨G, t', m', m2, h⟩
  · exact evR_eq_of_pull hf hg h (fun _ => rfl) hy

end GlobalTheory.CoverDown
