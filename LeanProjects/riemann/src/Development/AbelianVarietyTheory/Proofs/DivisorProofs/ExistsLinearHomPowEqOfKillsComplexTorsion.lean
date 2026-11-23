import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLinearHomProd
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsEqPowOfTorsionCompEqOne
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowEqOneOfSurjective
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsDescOfPoints
open NumberField
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CM
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.DivisibleLinear

variable {S S' : Scheme.{0}}

theorem eq_one_iff {G T : Over S} [GrpObj G] (z : T ⟶ G) : z = 1 ↔ z.left = T.hom ≫ η[G].left := by
  have hu : (toUnit T).left = T.hom := by simpa using Over.w (toUnit T)
  constructor
  · rintro rfl
    rw [Hom.one_def, Over.comp_left, hu]
  · intro h
    apply Over.OverMorphism.ext
    rw [h, Hom.one_def, Over.comp_left, hu]

section BaseChange

variable {f : S' ⟶ S} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {g : G'.left ⟶ G.left}

theorem toBase_injective (hg : IsPullback g G'.hom G.hom f) {T : Over S'} {x y : T ⟶ G'}
    (h : Out.toBase hg.w x = Out.toBase hg.w y) : x = y := by
  apply Over.OverMorphism.ext
  apply hg.hom_ext
  · simpa [Out.toBase] using congrArg (·.left) h
  · rw [Over.w x, Over.w y]

variable (hg : IsPullback g G'.hom G.hom f)
  (hm : ∀ (T : Over S') (x y : T ⟶ G'), Out.toBase hg.w (x * y) = Out.toBase hg.w x * Out.toBase hg.w y)
include hm

theorem toBase_one (T : Over S') : Out.toBase hg.w (1 : T ⟶ G') = 1 := by
  have h := hm T 1 1
  rw [_root_.mul_one] at h
  exact mul_eq_left.mp h.symm

theorem toBase_pow {T : Over S'} (x : T ⟶ G') (n : ℕ) : Out.toBase hg.w (x ^ n) = Out.toBase hg.w x ^ n := by
  induction n with
  | zero => simpa using toBase_one hg hm T
  | succ k ih => rw [pow_succ, hm, ih, pow_succ]

end BaseChange

end GlobalTheory.DivisibleLinear

namespace GlobalTheory.DivisibleLinear

theorem torsion_comp_eq_one {K : Type} [Field K] [NumberField K] (σ : K →+* ℂ)
    (P Q : Out.PolAV (Sp (𝓞 K))) (ψ : P.A ⟶ Q.A) [IsMonHom ψ] (n : ℕ) (hn : 0 < n)
    (h : ∀ u : Over.mk (spMap (σ.comp (algebraMap (𝓞 K) K))) ⟶ P.A, u ^ n = 1 → u ≫ ψ = 1)
    (T : Over (Sp (𝓞 K))) (x : T ⟶ P.A) (hx : x ^ n = 1) : x ≫ ψ = 1 := by
  set gc : 𝓞 K →+* ℂ := σ.comp (algebraMap (𝓞 K) K) with hgc
  set t : Sp ℂ ⟶ Sp (𝓞 K) := spMap gc with ht
  have hgci : Function.Injective gc :=
    σ.injective.comp (IsFractionRing.injective (𝓞 K) K)
  have hL := GlobalTheory.abelianSchemeLaws_all.1
  obtain ⟨P', gA, hgA, -, hmA, -⟩ := hL.polBaseChange (Sp (𝓞 K)) (Sp ℂ) t P
  obtain ⟨Q', gB, hgB, -, hmB, -⟩ := hL.polBaseChange (Sp (𝓞 K)) (Sp ℂ) t Q
  have := Q.isAb.proper
  have := Q'.isAb.proper

  let ψ' : P'.A ⟶ Q'.A := Over.homMk (hgB.lift (gA ≫ ψ.left) P'.A.hom
    (by rw [Category.assoc, Over.w ψ, hgA.w])) (hgB.lift_snd _ _ _)
  have tb : ∀ (T' : Over (Sp ℂ)) (y : T' ⟶ P'.A),
      Out.toBase hgB.w (y ≫ ψ') = Out.toBase hgA.w y ≫ ψ := by
    intro T' y
    apply Over.OverMorphism.ext
    simp [Out.toBase, ψ']
  have : IsMonHom ψ' := GlobalTheory.DivisibleHom.isMonHom_of_mul_points ψ' fun T' y₁ y₂ =>
    toBase_injective hgB (by rw [tb, hmA, MonObj.mul_comp, hmB, tb, tb])

  have hC : ∀ y : 𝟙_ (Over (Sp ℂ)) ⟶ P'.A, y ^ n = 1 → y ≫ ψ' = 1 := by
    intro y hy
    let e : Over.mk t ⟶ Over.mk ((𝟙_ (Over (Sp ℂ))).hom ≫ t) := Over.homMk (𝟙 _) (by simp)
    have h1 : (e ≫ Out.toBase hgA.w y) ^ n = 1 := by
      rw [← MonObj.comp_pow, ← toBase_pow hgA hmA, hy, toBase_one hgA hmA, MonObj.comp_one]
    have h2 := h _ h1
    apply toBase_injective hgB
    rw [tb, toBase_one hgB hmB, eq_one_iff]
    have h3 := (eq_one_iff _).1 h2
    simpa [e] using h3
  obtain ⟨α, hα, hfac⟩ := GlobalTheory.HolUnifEnd.exists_factor_pow P'.A Q'.A P'.isAb n hn ψ' hC
  have kill' : ∀ (T' : Over (Sp ℂ)) (y : T' ⟶ P'.A), y ^ n = 1 → y ≫ ψ' = 1 := by
    intro T' y hy
    rw [← hfac, ← Category.assoc, MonObj.comp_pow, Category.comp_id, hy, MonObj.one_comp]

  obtain ⟨_, hfl, _, _, -⟩ := hL.mulN (Sp (𝓞 K)) P n hn
  let Z := pullback (Out.mulA P.A n) η[P.A]
  let inc : Z ⟶ P.A := pullback.fst (Out.mulA P.A n) η[P.A]
  have hinc : inc ^ n = 1 := by
    rw [← GlobalTheory.DivisibleHom.comp_mulA, pullback.condition, Hom.one_def,
      toUnit_unique (pullback.snd (Out.mulA P.A n) η[P.A]) (toUnit Z)]
  have hp := (IsPullback.of_hasPullback (Out.mulA P.A n) η[P.A]).map (Over.forget (Sp (𝓞 K)))
  have hf : Flat (pullback.snd (Out.mulA P.A n) η[P.A]).left :=
    MorphismProperty.of_isPullback (P := @Flat) hp hfl
  have hw : (pullback.snd (Out.mulA P.A n) η[P.A]).left = Z.hom := by
    simpa using Over.w (pullback.snd (Out.mulA P.A n) η[P.A])
  rw [hw] at hf
  have hx' : x ≫ Out.mulA P.A n = toUnit T ≫ η[P.A] := by
    rw [GlobalTheory.DivisibleHom.comp_mulA, hx, Hom.one_def]
  suffices hZ : inc ≫ ψ = 1 by
    rw [← pullback.lift_fst x (toUnit T) hx', Category.assoc]
    change _ ≫ inc ≫ ψ = 1
    rw [hZ, MonObj.comp_one]
  rw [eq_one_iff]
  refine GlobalTheory.ArcDataDescent.ext_of_injective hgci (IsPullback.of_hasPullback Z.hom t) Q.A.hom ?_ ?_
  · simp
  · let π := pullback.fst Z.hom t
    let p' := pullback.snd Z.hom t
    let w := hgA.lift (π ≫ inc.left) p' (by rw [Category.assoc, Over.w inc, pullback.condition])
    let x' : Over.mk p' ⟶ P'.A := Over.homMk w (hgA.lift_snd _ _ _)
    let πZ : Over.mk (p' ≫ t) ⟶ Z := Over.homMk π pullback.condition
    have hb : Out.toBase hgA.w x' = πZ ≫ inc := by
      apply Over.OverMorphism.ext
      simp [Out.toBase, x', w, πZ]
    have hx'n : x' ^ n = 1 := by
      apply toBase_injective hgA
      rw [toBase_pow hgA hmA, hb, ← MonObj.comp_pow, hinc, MonObj.comp_one, toBase_one hgA hmA]
    have k2 := congrArg (Out.toBase hgB.w) (kill' _ x' hx'n)
    rw [tb, toBase_one hgB hmB, hb, eq_one_iff] at k2
    simp only [Over.comp_left] at k2 ⊢
    rw [pullback.condition_assoc]
    simpa [πZ] using k2

end GlobalTheory.DivisibleLinear

namespace GlobalTheory.DivisibleLinear

theorem exists_linear_pow_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (A B : GlobalTheory.CM.PAT H (Sp (𝓞 K)))
    (ψ : A.t.G ⟶ B.t.G), GlobalTheory.Serre.IsLinearHom A.t.act B.t.act ψ → ∀ n : ℕ, 0 < n →
    (∀ u : Over.mk (spMap (σ.comp (algebraMap (𝓞 K) K))) ⟶ A.t.G, u ^ n = 1 → u ≫ ψ = 1) →
    ∃ χ : A.t.G ⟶ B.t.G, GlobalTheory.Serre.IsLinearHom A.t.act B.t.act χ ∧ χ ^ n = ψ := by
  intro E _ _ _ H K _ _ σ A B ψ hψ n hn hk
  have := hψ.isMonHom
  have hker := torsion_comp_eq_one σ A.pol B.pol ψ n hn hk
  obtain ⟨⟨χ, hχ, hχψ⟩, -⟩ := GlobalTheory.DivisibleHom.exists_eq_pow_of_torsion_comp_eq_one
    (fun S _ P m hm => by
      obtain ⟨h1, h2, h3, h4, -⟩ := GlobalTheory.abelianSchemeLaws_all.1.mulN S P m hm
      exact ⟨h1, h2, h3, h4⟩)
    (Sp (𝓞 K)) A.pol B.t.G n hn ψ hψ.isMonHom hker
  refine ⟨χ, ⟨hχ, fun c => ?_⟩, hχψ.symm⟩
  have := B.t.act.hom c
  have := A.t.act.hom c
  obtain ⟨_, hfl, hsu, -⟩ := GlobalTheory.abelianSchemeLaws_all.1.mulN (Sp (𝓞 K)) A.pol n hn
  have : Flat (Out.mulA A.t.G n).left := hfl
  have : Surjective (Out.mulA A.t.G n).left := hsu
  apply GlobalTheory.DivisibleHom.cancel_of_flat_surjective (Out.mulA A.t.G n)
  rw [GlobalTheory.DivisibleHom.mulA_comp, GlobalTheory.DivisibleHom.mulA_comp, ← MonObj.comp_pow, ← hχψ, hψ.comm c, hχψ,
    MonObj.pow_comp]

end GlobalTheory.DivisibleLinear
