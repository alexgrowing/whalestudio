import Mathlib
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.PlaceIdem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ChartValJ
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FramedPointsLiftToLevelCover
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsFramedPointOfArcBaseChange
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcFramedPointUniqueAndBaseChange

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

namespace GlobalTheory.PlaceInt

theorem integral_of_frOver : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n) (T : CDVR) (io : c.F →+* T.Fr) (io₂ : d.c₂.F →+* T.Fr) (y : IntFr Xo c T io), letI := io.toAlgebra; letI := io₂.toAlgebra; (∀ a : c.F, io₂ (d.eF a) = io a) → ∀ y₂ : FrPt d.Xo₂ d.c₂ T.Fr, FrOver d y₂ y.1 → Integral T io₂ y₂ := by
  intro E _ _ _ H Dw l Xo c n d T io io₂ y hio y₂ hy
  letI := io.toAlgebra
  letI := io₂.toAlgebra
  obtain ⟨y, hInt⟩ := y
  have hy' : FrOver d y₂ y := hy
  obtain ⟨G, t', m1, m2, ⟨ub, b1, b2, b3, b4⟩, θ, hθ, w1, w2, σ, s1, θ2, r1, r2, i1, i2, p2, hg⟩ := hInt.2
  obtain ⟨e, hu, w, p, hw, p₁, p₂, R⟩ := (FrameLift.frOver_iff d y₂ y).1 hy'
  have key : ∀ (x : Sp T.Fr ⟶ Xo.X) (m : SABMap t' Xo.univ.t x), x = y₂.x ≫ d.r →
      ∃ m' : SABMap t' d.Xo₂.univ.t y₂.x, m.φ = m'.φ ≫ d.m.φ := by
    intro x m hx
    subst hx
    exact sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ d.m m
  obtain ⟨m', e₁⟩ := key _ m1 e.symm
  have eig : ∀ τ v, Formalism.L2.Pj.IsEigV d.c₂ io₂ G τ v ↔ Formalism.L2.Pj.IsEigV c io G τ v := fun τ v =>
    forall_congr' fun a => forall_congr' fun z => by rw [← FrameLift.embK_eF d τ a, hio]
  have he : m1.cm.e = m'.cm.e ≫ d.m.cm.e := by rw [m1.base, m'.base, d.m.base]; exact e.symm
  obtain ⟨w', r', tri⟩ := ArcQ.FrBC.exists_rigIso_cancel d.m.cm m'.cm m1.cm e₁ he t'.PP d.Xo₂.univ.t.PP Xo.univ.t.PP
    w w1 hw r1
  obtain ⟨s', hs'⟩ := thf_secUp ((isGen_iff w').1 r'.1) d.Xo₂.univ.t.PP.isLB t'.PP.isLB σ
  refine ⟨G, t', m', m2, ⟨ub, b1, fun τ i => (eig τ _).2 (b2 τ i), fun τ v h1 h2 => b3 τ v h1 ((eig τ v).1 h2),
    fun τ i => ?_⟩, θ, hθ, w', w2, σ, s', θ2, r', r2,
    (ArcQ.FrUniq.isoMaps_iff w' σ s').2 fun Z r z j k hj hk => hs' Z r z (fun _ => j) k (mem_pull.2 hj) hk,
    i2, p2, ?_⟩
  · obtain ⟨q, h2, h3⟩ := b4 τ i
    have ubo : (ub τ i).left ≫ G.G.hom = spMap (algebraMap T.V (DualNumber T.V)) := Over.w (ub τ i)
    have h4 : q ≫ t'.G.hom = spMap (algebraMap T.Fr (DualNumber T.Fr)) := by
      have : Mono (spMap (algebraMap T.V T.Fr)) :=
        haveI := IsPreimmersion.of_isLocalization (R := CommRingCat.of T.V) (S := CommRingCat.of T.Fr)
          (nonZeroDivisors T.V)
        inferInstanceAs (Mono (Spec.map (CommRingCat.ofHom (algebraMap T.V T.Fr))))
      rw [← cancel_mono (spMap (algebraMap T.V T.Fr)), Category.assoc, ← m2.cart.1.w, ← Category.assoc, h3,
        Category.assoc]
      exact (congrArg _ ubo).trans (ArcQ.FrBC.dual_alg _)
    refine ⟨q, d.m.cart.1.hom_ext ?_ ?_, h3⟩
    · exact (Category.assoc _ _ _).trans ((congrArg (q ≫ ·) e₁.symm).trans (h2.trans (hu τ i).symm))
    · rw [Category.assoc, m'.cart.1.w, ← Category.assoc, h4]
      exact (y₂.tan τ i).1.symm
  · intro g g₁ g₂ (J : PUnit → d.Xo₂.univ.t.PP.L.ι) hJ
    refine fn_ext fun z hz => ?_
    obtain ⟨k, hk⟩ := exists_chart t'.PP.isLB z
    obtain ⟨j, hj⟩ := exists_chart Xo.univ.t.PP.isLB (d.m.φ (m'.φ z))
    have hi : m'.φ z ∈ d.Xo₂.univ.t.PP.L.U (J PUnit.unit) := mem_pull.1 hz
    have hj' : m1.φ z ∈ Xo.univ.t.PP.L.U j :=
      (congrArg (· ∈ Xo.univ.t.PP.L.U j) (FrameLift.pt_eq e₁ z)).mpr hj
    have a₁ : (g ≫ p) ≫ (snd (Over.mk y.x) Xo.univ.t.G).left = m1.φ := by
      rw [Category.assoc, p₁, ← Category.assoc, g₁, e₁]
    have a₂ : (g ≫ p) ≫ (fst (Over.mk y.x) Xo.univ.t.G).left = t'.G.hom := by
      rw [Category.assoc, p₂, g₂]
    have le : (Xo.univ.t.PP.L.pull m1.φ).U (fun _ => j) ≤ (g ≫ p) ⁻¹ᵁ (PPx y.x).U (fun _ => j) := fun q hq =>
      Set.mem_iInter.2 fun _ => (congrArg (· ∈ Xo.univ.t.PP.L.U j) (FrameLift.pt_eq a₁ q)).mpr (mem_pull.1 hq)
    have u₁ := (ArcQ.FrUniq.isoMaps_iff w1 σ s1).1 i1 _ (𝟙 _) z j k hj' hk
    rw [hg (g ≫ p) a₁ a₂ (fun _ => j) le, gs_appLE (g ≫ p) _ _ le (𝟙 _) z (mem_pull.2 hj'),
      tri _ (𝟙 _) z j (J PUnit.unit) k hj hi hk, Category.id_comp, Category.id_comp] at u₁
    have u₂ := R _ g z j (J PUnit.unit)
      ((congrArg (fun t => d.m.φ t ∈ Xo.univ.t.PP.L.U j) (FrameLift.pt_eq g₁ z)).mpr hj)
      ((congrArg (· ∈ d.Xo₂.univ.t.PP.L.U (J PUnit.unit)) (FrameLift.pt_eq g₁ z)).mpr hi)
    rw [g₁] at u₂
    have u₃ := u₁.symm.trans u₂
    rw [Units.val_mul, _root_.mul_assoc, Units.mul_right_inj] at u₃
    rw [hs' _ (𝟙 _) z J k hz hk, gs_appLE _ _ _ hJ (𝟙 _) z hz, Category.id_comp]
    exact u₃

end GlobalTheory.PlaceInt
