import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IdealPart
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsRepresentativesModNsmul
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FormalThetaSumShiftPeriodDiv
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstFamComponentsBasisExpansion
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.MemThetaShiftZero
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsSectionValuesFormalThetaSumStatement

noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.ConstSpan

open GlobalTheory.FieldBaseChange

theorem exists_relation {R M J : Type} [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M] [Fintype J]
    (σ σ' : J → M) (h : ∀ s, ∃ t : R, t ≠ 0 ∧ t • s ∈ Submodule.span R (Set.range σ)) (s : M) :
    ∃ (t : R) (r : J → R), (t = 0 → ∃ i, r i ≠ 0) ∧ t • s + ∑ i, r i • σ' i = 0 := by
  classical
  choose t ht hm using h
  let v : Option J → M := fun o => o.elim s σ'
  have hn : ¬ LinearIndependent R (fun o => t (v o) • v o) := fun hi => by
    have := linearIndependent_le_span_aux' _ hi (Set.range σ) (by rintro _ ⟨o, rfl⟩; exact hm _)
    have h2 := Fintype.card_range_le σ
    rw [Fintype.card_option] at this
    omega
  obtain ⟨g, hg, o, ho⟩ := Fintype.not_linearIndependent_iff.1 hn
  refine ⟨g none * t s, fun i => g (some i) * t (σ' i), fun h0 => ?_, ?_⟩
  · cases o with
    | none => exact absurd h0 (mul_ne_zero ho (ht _))
    | some i => exact ⟨i, mul_ne_zero ho (ht _)⟩
  · simpa only [Fintype.sum_option, smul_smul, v, Option.elim] using hg

theorem map_relation {R M J : Type} [CommRing R] [AddCommGroup M] [Module R M] [Fintype J] {t : R} {s : M} {r : J → R}
    {σ : J → M} (h : t • s + ∑ i, r i • σ i = 0) (ev : M →ₗ[R] R) : t * ev s + ∑ i, r i * ev (σ i) = 0 := by
  simpa only [map_add, map_sum, map_smul, map_zero, smul_eq_mul] using congrArg ev h

theorem smul_eq_zero_of_relation {R M J : Type} [CommRing R] [AddCommGroup M] [Module R M] [Fintype J] {t : R} {s : M}
    {r : J → R} {σ : J → M} (h : t • s + ∑ i, r i • σ i = 0) (hr : ∀ i, r i = 0) : t • s = 0 := by
  simpa only [hr, zero_smul, Finset.sum_const_zero, add_zero] using h

theorem eq_zero_of_smul {R : Type} [CommRing R] [IsDomain R] (G : Over (Spec (CommRingCat.of R))) [Smooth G.hom]
    (L : LB G.left) (j : ℤ) {t : R} (ht : t ≠ 0)
    (s : SecOver G.hom (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => j))) (h : t • s = 0) : s = 0 := by
  have hinj : Function.Injective (algebraMap R (FractionRing R)) := IsFractionRing.injective R _
  have : IsDominant (Out.jK R) :=
    ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2 (by
      rw [CommRingCat.hom_ofHom, (RingHom.injective_iff_ker_eq_bot _).1 hinj]; exact bot_le)⟩
  have := IsSchemeTheoreticallyDominant.of_isDominant (Out.jK R)
  have : IsSchemeTheoreticallyDominant (pullback.fst G.hom (Out.jK R)) :=
    .of_isPullback (IsPullback.of_hasPullback G.hom (Out.jK R)).flip
  have hp : pullback.fst G.hom (Out.jK R) ≫ G.hom =
      pullback.snd G.hom (Out.jK R) ≫ Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))) :=
    pullback.condition
  have hφ : ∀ k : Fin 1, (fun _ : Fin 1 => pullback.fst G.hom (Out.jK R)) k =
      pullback.fst G.hom (Out.jK R) ≫ (fun _ : Fin 1 => 𝟙 G.left) k := fun _ => (Category.comp_id _).symm
  have hρ := ConstFam.pullOver_injective_of_dominant L (fun _ : Fin 1 => j) hp hφ
  have ht' : algebraMap R (FractionRing R) t ≠ 0 := fun h => ht (hinj (h.trans (map_zero _).symm))
  have e := congrArg (pullOver L (fun _ : Fin 1 => j) hp hφ) h
  rw [map_smulₛₗ, map_zero] at e
  exact hρ (((smul_eq_zero.1 e).resolve_left ht').trans (map_zero _).symm)

def valLin {R : Type} [CommRing R] {Y : Scheme.{0}} (π : Y ⟶ Sp R) (x : Sp R ⟶ Y) (hx : x ≫ π = 𝟙 _) (U : Y.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ U) : FnOver π U →ₗ[R] R where
  toFun f := valR x U f
  map_add' f g := Points.valR_add x U h f g
  map_smul' c f := (Points.valR_mul x U h (constFn π U c) f).trans
    (congrArg (· * _) (Points.valR_constFn_of_section π x hx U h c))

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} [StarRing (𝓞 E)]
variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
variable [Algebra (FractionRing ℂ) ℂ] {Y : Model Xo c β} {b : O →+* ℂ} {a : ArcIn D l β ℂ b} {χ : Sp ℂ⟦X⟧ ⟶ Y.X}
  {W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ} {Λ : GtAn a}

theorem tau_ne_zero (Ξ : ConstPts W Λ) (v : Λ.A.V) (j : W.P.U.LG.L.ι) (h : ⊤ ≤ (Ξ.x v).left ⁻¹ᵁ W.P.U.LG.L.U j) :
    Ξ.τ v j ≠ 0 := by
  have hb : (show Sp ℂ⟦X⟧ ⟶ _ from (Ξ.g v).b.left) ≫ W.φ = spMap (PowerSeries.C (R := ℂ)) ≫ (Λ.u.ex v.2).left :=
    ((Ξ.g_rel v 0).1 2).trans (congrArg (spMap (PowerSeries.C (R := ℂ)) ≫ ·) (Λ.ex0_b v))
  obtain ⟨jM, hM⟩ := exists_chart W.P.D.toPre.P.isLB ((show Sp ℂ⟦X⟧ ⟶ _ from (Ξ.g v).b.left) (cpt ℂ⟦X⟧))
  have h₀ := FrameValue.le_chartAt a.D₀.P.isLB (Λ.u.ex v.2).left
  have hj : ⊤ ≤ (show Sp ℂ⟦X⟧ ⟶ _ from (Ξ.g v).b.left) ⁻¹ᵁ (LB.div (a.D₀.P.L.pull W.φ) W.P.D.toPre.P.L).U
      (fun _ => FrameValue.chartAt a.D₀.P.isLB (Λ.u.ex v.2).left, jM) := (top_le_iff_cpt _ _).2 ⟨mem_pull.2
    ((congrArg (fun q => q (cpt ℂ⟦X⟧) ∈ a.D₀.P.L.U _) hb).mpr (FormalValue.top_le_comp h₀ _ trivial)), hM⟩
  refine (isUnit_of_mul_isUnit_right ((congrArg IsUnit (Ξ.τ_eq v j jM _ h hj)).mpr ?_)).ne_zero
  exact (Units.isUnit _).mul ((Ne.isUnit (Λ.u.fr_ne _ v.2 h₀)).map _)

end

theorem main : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : GtAn a) (Ξ : ConstPts W Λ) (j : ℕ) [NeZero j] (σ : Out.H0 W.P.U.LG.L j), ∃ f, IsComb Λ.A j Set.univ f ∧ Ξ.Vals σ f ∧ ((∀ v, f v = 0) → ∀ i, σ.f i = 0) := by
  classical
  intro hL hL2 E _ _ _ H _ D l Xo c O _ β Y _ _ b a χ W Λ Ξ j _ s
  have hj : 1 ≤ j := Nat.one_le_iff_ne_zero.2 (NeZero.ne j)
  have hW : WitData a W.P.D W.P.oD W.φ W.he W.w W.e := ⟨W.spec.1, W.spec.2.1, W.spec.2.2.1, W.spec.2.2.2.1,
    W.spec.2.2.2.2.1, fun F _ _ _ _ uF h₁ h₂ => (W.spec.2.2.2.2.2 F uF h₁ h₂).1⟩
  obtain ⟨-, rep, hrep⟩ := exists_representatives_mod_nsmul Λ.A.X j hj
  obtain ⟨hfn, hfin, -⟩ := ArcThetaSpaces.sections_theta hL hL2 E H D l c O β b a Λ
  let fn := fun x => TwistedTheta.secFn a.D₀ Λ.u j (Λ.ε (rep x)) (Λ.A.ct (rep x))
  have hinj : ∀ x, Function.Injective (fn x) := fun x => TwistedTheta.secFn_injective (Λ.ct _)
  have hmem : ∀ x s, fn x s ∈ Λ.A.Theta j (rep x) := fun x s => (hfn j (rep x) hj).1 s
  have : ∀ x, Module.Finite ℂ (ConstFam.SecBMod a.D₀ j (Λ.ε (rep x))) := fun x =>
    have := hfin.1 j (rep x) hj
    Module.Finite.of_injective ((fn x).codRestrict _ (hmem x)) fun _ _ e => hinj x (congrArg Subtype.val e)
  let bas := fun x => Module.finBasis ℂ (ConstFam.SecBMod a.D₀ j (Λ.ε (rep x)))
  let th := fun x i => fn x (bas x i)
  have hth : ∀ x, LinearIndependent ℂ (th x) := fun x =>
    (bas x).linearIndependent.map' (fn x) (LinearMap.ker_eq_bot.2 (hinj x))
  have hrep' : ∀ α, ∃! x, ∃ mu, Λ.ε (rep x) + j • mu = α := fun α => by
    refine (existsUnique_congr fun x => ⟨?_, ?_⟩).1 (hrep (Λ.ε.symm α))
    · rintro ⟨m, hm⟩
      exact ⟨Λ.ε m, by rw [← map_nsmul, ← map_add, ← hm, LinearEquiv.apply_symm_apply]⟩
    · rintro ⟨m, rfl⟩
      exact ⟨Λ.ε.symm m, by rw [map_add, map_nsmul, LinearEquiv.symm_apply_apply]⟩
  have hrep'' : ∀ x x' mu, rep x = rep x' + j • mu → x = x' := fun x x' mu h =>
    (hrep (rep x)).unique ⟨0, by simp⟩ ⟨mu, h⟩
  choose m₀ hm₀ using fun i : Σ x, Fin (Module.finrank ℂ (ConstFam.SecBMod a.D₀ j (Λ.ε (rep x)))) =>
    ConstFam.exists_expandsAt hW hL.globalFns hj W.P.U (Λ.ε (rep i.1)) (bas i.1 i.2)
  choose f σ hf hE using fun i => hm₀ i _ le_rfl
  have hspan := ConstFam.exists_pow_smul_mem_span hW hL.globalFns hj W.P.U _ hrep' bas m₀ f σ hf hE
  choose m σ' hσ' using fun i : Σ x, Fin (Module.finrank ℂ (ConstFam.SecBMod a.D₀ j (Λ.ε (rep x)))) =>
    GlobalTheory.T.exists_section_values_formalThetaSum hL hL2 E H D l Xo c O β Y b a χ W Λ Ξ j (rep i.1) (th i.1 i.2) (hmem _ _)
  obtain ⟨t, r, hne, hrel⟩ := exists_relation (R := ℂ⟦X⟧) (M := SecOver W.t.G.hom
    (LB.LinComb W.P.U.LG.L (K := Fin 1) (fun _ => 𝟙 W.t.G.left) (fun _ => (j : ℤ)))) σ σ'
    (fun s => (hspan s).elim fun n hn => ⟨_, pow_ne_zero n PowerSeries.X_ne_zero, hn⟩) s
  have hφ : Function.Injective (algebraMap ℂ⟦X⟧ ℂ⸨X⸩) := IsFractionRing.injective _ _
  set φ := algebraMap ℂ⟦X⟧ ℂ⸨X⸩ with hφdef
  let S : Λ.A.V → ℂ⸨X⸩ := fun v => ∑ i, (φ (r i) * HahnSeries.single (m i : ℤ) (1 : ℂ)) *
    Λ.A.FSum j (rep i.1) (th i.1 i.2) v
  have key : ∀ v jL, ⊤ ≤ (Ξ.x v).left ⁻¹ᵁ W.P.U.LG.L.U jL →
      φ t * φ (FormalValue.secVal W.P.U.toUnifPre s (Ξ.x v).left jL) + S v * φ (Ξ.τ v jL) ^ j = 0 := by
    intro v jL h
    have hx : (show Sp ℂ⟦X⟧ ⟶ _ from (Ξ.x v).left) ≫ W.t.G.hom = 𝟙 _ := (Over.w (Ξ.x v)).trans (Spec.map_id _)
    let ev := (valLin W.t.G.hom (Ξ.x v).left hx _ (FormalValue.top_le_secChart (U := W.P.U.toUnifPre) h)).comp
      (chartLin W.t.G.hom (LB.LinComb W.P.U.LG.L (K := Fin 1) (fun _ => 𝟙 W.t.G.left) (fun _ => (j : ℤ)))
        (fun _ => jL))
    have e₀ : t * FormalValue.secVal W.P.U.toUnifPre s (Ξ.x v).left jL +
        ∑ i, r i * FormalValue.secVal W.P.U.toUnifPre (σ' i) (Ξ.x v).left jL = 0 := map_relation hrel ev
    have e := congrArg φ e₀
    simp only [map_add, map_sum, map_zero, map_mul] at e
    refine Eq.trans (congrArg₂ (· + ·) rfl ?_) e
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hσ' i v jL h]
    ring
  have hS : (∀ v, S v = 0) → ∀ i, r i = 0 := fun h i => by
    have := Λ.A.eq_zero_of_sum_FSum hrep'' hth
      (r := fun x k => φ (r ⟨x, k⟩) * HahnSeries.single (m ⟨x, k⟩ : ℤ) (1 : ℂ))
      (fun v => (Fintype.sum_sigma _).symm.trans (h v)) i.1 i.2
    exact hφ (((mul_eq_zero.1 this).resolve_right (HahnSeries.single_ne_zero one_ne_zero)).trans (map_zero _).symm)
  have ht : t ≠ 0 := fun h0 => by
    obtain ⟨i, hi⟩ := hne h0
    refine hi (hS (fun v => ?_) i)
    obtain ⟨jL, hjL⟩ := exists_chart W.P.U.LG.isLB ((show Sp ℂ⟦X⟧ ⟶ _ from (Ξ.x v).left) (cpt ℂ⟦X⟧))
    have h := (top_le_iff_cpt (show Sp ℂ⟦X⟧ ⟶ _ from (Ξ.x v).left) _).2 hjL
    have e := key v jL h
    rw [h0, map_zero, zero_mul, zero_add] at e
    exact (mul_eq_zero.1 e).resolve_right (pow_ne_zero _ fun e => tau_ne_zero Ξ v jL h (hφ (e.trans (map_zero _).symm)))
  have ht' : φ t ≠ 0 := fun h => ht (hφ (h.trans (map_zero _).symm))
  refine ⟨fun v => -(φ t)⁻¹ * S v, ?_, fun v jL h => ?_, fun h i => ?_⟩
  · let e := (Fintype.equivFin (Σ x, Fin (Module.finrank ℂ (ConstFam.SecBMod a.D₀ j (Λ.ε (rep x)))))).symm
    refine ⟨_, fun k => -(φ t)⁻¹ * (φ (r (e k)) * HahnSeries.single (m (e k) : ℤ) (1 : ℂ)), fun k => rep (e k).1,
      fun k => th (e k).1 (e k).2, fun k => ⟨trivial, hmem _ _⟩, fun v => ?_⟩
    refine (Finset.mul_sum _ _ _).trans ((e.sum_comp _).symm.trans (Finset.sum_congr rfl fun k _ => ?_))
    exact (_root_.mul_assoc _ _ _).symm
  · refine mul_left_cancel₀ ht' ((eq_neg_of_add_eq_zero_left (key v jL h)).trans ?_)
    rw [← _root_.mul_assoc, ← _root_.mul_assoc, mul_neg, mul_inv_cancel₀ ht', neg_one_mul, neg_mul]
  · have hr := hS fun v => (mul_eq_zero.1 (h v)).resolve_left (neg_ne_zero.2 (inv_ne_zero ht'))
    have := W.P.U.smooth
    exact congrArg (fun q => LB.Sec.f q i) (eq_zero_of_smul W.t.G _ _ ht s (smul_eq_zero_of_relation hrel hr))

end GlobalTheory.ConstSpan
