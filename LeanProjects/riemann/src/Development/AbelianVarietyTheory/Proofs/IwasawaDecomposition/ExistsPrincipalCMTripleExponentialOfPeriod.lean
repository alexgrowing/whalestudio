import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrbitThickSt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArithmeticCMKnownTheoremsProof
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPointOfIsPeriod
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TensorObjectAndCurveExistsIff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverOfIsIso
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPatOfObj
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPullback

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory GlobalTheory.ArcQ GlobalTheory.ArcCM GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.CuspFrom
open scoped LaurentSeries

noncomputable section

namespace GlobalTheory.CuspFrom.PeriodTriple

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {D : Datum H}
  {g : ℕ} {ty : Fin g → (E →+* ℂ)} {P : D.La →+ (Fin g → ℂ)}

theorem exists_isExp_of_sabMap {S : Scheme.{0}} {t : SAB H S} {y : Sp ℂ ⟶ S} (B : GlobalTheory.CM.PAT H (Sp ℂ))
    (m : SABMap B.t t y) (e : (Fin g → ℂ) → (Over.mk y ⟶ t.G)) (hP : IsPeriod D ty P)
    (hol : IsHolTo Set.univ fun z => (e z).left) (add : ∀ z w, e (z + w) = e z * e w) (onto : Function.Surjective e)
    (ker : ∀ z, e z = 1 ↔ z ∈ P.range) (lin : ∀ (a : 𝓞 E) z, e (fun k => ty k (a : E) * z k) = e z ≫ t.act.act a)
    (weil : ∀ (k : ℕ) (a b : D.La) (c : ℂˣ), 0 < k →
      (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D.EF a b : ℂ) / k) →
      Out.WeilIs t.G t.PP.L k (e ((k : ℂ)⁻¹ • P a)) (e ((k : ℂ)⁻¹ • P b)) (unitOn c)) :
    ∃ ex : (Fin g → ℂ) → (Over.mk (spMap (RingHom.id ℂ)) ⟶ B.t.G), GlobalTheory.CM.IsExp B (RingHom.id ℂ) D ty P ex := by
  have hid : spMap (RingHom.id ℂ) = 𝟙 (Sp ℂ) := Spec.map_id _
  have hy : y = spMap (RingHom.id ℂ) ≫ y := by rw [hid, Category.id_comp]
  obtain ⟨p, hp⟩ := LiePull.exists_pushEquiv m.cart (Over.mk (spMap (RingHom.id ℂ))) y hy
  have hp' : ∀ z, (p.symm (e z)).left ≫ m.φ = (e z).left := fun z => by
    rw [← hp, p.apply_symm_apply]
  refine ⟨fun z => p.symm (e z), hP, ?_, fun z w => ?_, p.symm.surjective.comp onto, fun z => ?_, fun a z => ?_,
    fun k a b c hk hc => ?_⟩
  · refine ThetaPoint.isHolTo_fibre m.cart.1 _ (fun z => (Over.w (p.symm (e z))).trans hid) ?_
    have h : (fun z => (p.symm (e z)).left ≫ m.cm.F) = fun z => (e z).left := funext hp'
    exact h ▸ hol
  · beta_reduce
    rw [add, map_mul]
  · exact (map_eq_one_iff _ p.symm.injective).trans (ker z)
  · beta_reduce
    rw [lin, p.symm_apply_eq]
    apply Over.OverMorphism.ext
    rw [hp, Over.comp_left, Over.comp_left, Category.assoc, m.act, ← Category.assoc]
    exact congrArg (· ≫ _) (hp' z).symm
  · exact (GlobalTheory.CM.ExCompare.weilIs_iff m _ _ hy k _ _ _ _ c (hp' _).symm (hp' _).symm).2 (weil k a b c hk hc)

theorem exists_isExp_of_rank_zero (l : Level H) (hD : D.p + D.q = 0) (hP : IsPeriod D ty P) :
    ∃ (B : GlobalTheory.CM.PAT H (Sp ℂ)) (ex : (Fin g → ℂ) → (Over.mk (spMap (RingHom.id ℂ)) ⟶ B.t.G)),
      GlobalTheory.CM.IsExp B (RingHom.id ℂ) D ty P ex := by
  obtain ⟨B, hB, -⟩ := GlobalTheory.CM.exists_pat_of_obj E H D l _ _ _ _
    (Models.RankZero.zeroObj hD l (spMap (algebraMap (KA l) ℂ)))
  have hz : IsIso B.t.G.hom := by
    rw [hB]
    exact Models.RankZero.isIso_zeroTriple _
  have := Models.RankZero.subsingleton_La hD
  have h0 : ∀ z : Fin g → ℂ, z = 0 := fun z => by
    have hz : z ∈ Submodule.span ℝ (Set.range P) := hP.2.2.2.1 ▸ Submodule.mem_top
    refine (Submodule.span_le (p := ⊥)).2 ?_ hz
    rintro _ ⟨a, rfl⟩
    rw [Subsingleton.elim a 0, map_zero]
    exact Submodule.zero_mem _
  refine ⟨B, fun _ => 1, hP, fun U f => ⟨?_, differentiableOn_const _⟩, fun _ _ => (_root_.mul_one _).symm,
    fun x => ⟨0, Models.RankZero.hom_unique hz _ _⟩, fun z => ⟨fun _ => ⟨0, by rw [map_zero, h0 z]⟩, fun _ => rfl⟩,
    fun _ _ => Models.RankZero.hom_unique hz _ _, fun k a b c hk hc => ?_⟩
  · simp only [Set.mem_univ, true_and]
    exact isOpen_const
  · have e : c = 1 := Units.ext (by rw [hc, Subsingleton.elim b 0, map_zero]; simp)
    rw [e, unitOn, map_one]
    exact Models.RankZero.weilIs_zero hz B.t.PP.isLB (Models.RankZero.triv_rig hz _) _ _ _

end GlobalTheory.CuspFrom.PeriodTriple

namespace GlobalTheory.CuspFrom

theorem exists_pat_isExp_of_isPeriod : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) (DB : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (PB : DB.La →+ (Fin g → ℂ)), IsTypeFn H DB.p DB.q ty → IsPeriod DB ty PB → ∃ (B : GlobalTheory.CM.PAT H (Sp ℂ)) (ex : (Fin g → ℂ) → (Over.mk (spMap (RingHom.id ℂ)) ⟶ B.t.G)), GlobalTheory.CM.IsExp B (RingHom.id ℂ) DB ty PB ex := by
  intro E _ _ _ H l₀ DB g ty PB hty hP
  rcases Nat.eq_zero_or_pos (DB.p + DB.q) with h0 | hpq
  · exact PeriodTriple.exists_isExp_of_rank_zero l₀ h0 hP
  have kn := known_holds
  obtain ⟨l, hA⟩ : ∃ l : Level H, l.A = 1 := ⟨{ l₀ with A := 1, A_pos := one_pos }, rfl⟩
  obtain ⟨Xo⟩ := kn.n1ab E H DB l hpq
  have hζ : algebraMap (KA l) ℂ (baseKA l).ζ =
      Complex.exp (-(2 * Real.pi * Complex.I) * (((1 : ℤ) : ℂ)) / l.A) := by
    show zeta l.A = _
    rw [hA, zeta]
    simp [Complex.exp_neg]
  obtain ⟨y, e, -, -, ⟨add, onto, hol, -⟩, ker, lin, weil, -⟩ := GlobalTheory.Moduli.exists_point_of_isPeriod kn.theta kn.laws
    E H DB l Xo (algebraMap (KA l) ℂ) g ty hpq rfl hty DB LinearMap.id PB
    ⟨rfl, rfl, fun _ => LinearMap.id, fun _ => 1, fun n m _ _ a => ⟨0, by simp⟩,
      fun n _ => ⟨fun a => Iff.rfl, fun a => ⟨a, 0, by simp⟩⟩, fun n _ a a' => by simp, hζ, rfl⟩ hP
  obtain ⟨U, hU, -⟩ := GlobalTheory.CM.exists_pat_of_obj E H DB l _ _ _ _ Xo.univ
  obtain ⟨B, m, -⟩ := GlobalTheory.CM.PAT.exists_pullback E H _ _ y U
  exact ⟨B, PeriodTriple.exists_isExp_of_sabMap B (hU ▸ m) e hP hol add onto ker lin weil⟩

end GlobalTheory.CuspFrom
