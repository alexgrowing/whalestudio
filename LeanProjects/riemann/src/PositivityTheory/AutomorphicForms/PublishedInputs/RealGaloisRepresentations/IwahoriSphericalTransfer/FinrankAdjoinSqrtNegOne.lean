import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcDefs

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc

namespace GlobalTheory.RealGal

structure QCM (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] where

  K : IntermediateField F Ω
  nf : NumberField ↥K
  cm : @IsCMField ↥K _ nf.to_charZero
  two : Module.finrank F ↥K = 2

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]

instance (Q : QCM F Ω) : NumberField ↥Q.K := Q.nf

instance (Q : QCM F Ω) : IsCMField ↥Q.K := Q.cm

instance [IsAlgClosure F Ω] (Q : QCM F Ω) : IsAlgClosure ↥Q.K Ω :=
  ⟨IsAlgClosure.isAlgClosed F, haveI : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic; Algebra.IsAlgebraic.tower_top (K := F) _⟩

section Gauss

open Polynomial
open scoped IntermediateField

theorem QCM.sq_ne_neg_one_of_isReal {E : Type} [Field E] {v : InfinitePlace E} (hv : v.IsReal) (x : E) : x ^ 2 ≠ -1 := fun h => by
  have := congrArg (InfinitePlace.embedding_of_isReal hv) h
  rw [map_pow, map_neg, map_one] at this
  nlinarith [sq_nonneg (InfinitePlace.embedding_of_isReal hv x)]

omit [NumberField F] in

theorem QCM.isIntegral_sqrt_neg_one {i : Ω} (hi : i ^ 2 = -1) : IsIntegral F i :=
  ⟨X ^ 2 - C (-1), monic_X_pow_sub_C _ two_ne_zero, by simp [hi]⟩

theorem QCM.finrank_adjoin_sqrt_neg_one [IsTotallyReal F] {i : Ω} (hi : i ^ 2 = -1) : Module.finrank F F⟮i⟯ = 2 := by
  obtain ⟨v⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hirr : Irreducible (X ^ 2 - C (-1) : F[X]) :=
    X_pow_sub_C_irreducible_of_prime Nat.prime_two (QCM.sq_ne_neg_one_of_isReal (IsTotallyReal.isReal v))
  rw [IntermediateField.adjoin.finrank (QCM.isIntegral_sqrt_neg_one hi),
    ← minpoly.eq_of_irreducible_of_monic hirr (by simp [hi]) (monic_X_pow_sub_C _ two_ne_zero), natDegree_X_pow_sub_C]

def QCM.gauss [IsTotallyReal F] {i : Ω} (hi : i ^ 2 = -1) : QCM F Ω :=
  haveI := IntermediateField.adjoin.finiteDimensional (QCM.isIntegral_sqrt_neg_one (F := F) hi)
  haveI nf : NumberField F⟮i⟯ := NumberField.of_module_finite F _
  haveI : IsTotallyComplex F⟮i⟯ := ⟨fun v => by
    rw [← InfinitePlace.not_isReal_iff_isComplex]
    exact fun hv => QCM.sq_ne_neg_one_of_isReal hv (IntermediateField.AdjoinSimple.gen F i) (Subtype.ext (by simpa using hi))⟩
  haveI : Algebra.IsQuadraticExtension F F⟮i⟯ := { finrank_eq_two' := QCM.finrank_adjoin_sqrt_neg_one hi }
  { K := F⟮i⟯
    nf := nf
    cm := IsCMField.ofCMExtension F _
    two := QCM.finrank_adjoin_sqrt_neg_one hi }

theorem QCM.gauss_K [IsTotallyReal F] {i : Ω} (hi : i ^ 2 = -1) : (QCM.gauss (F := F) hi).K = F⟮i⟯ := rfl

theorem QCM.nonempty [IsTotallyReal F] [IsAlgClosure F Ω] : Nonempty (QCM F Ω) := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  obtain ⟨i, hi⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : Ω) two_pos
  exact ⟨QCM.gauss hi⟩

def QCM.cyclo {Ω : Type} [Field Ω] [CharZero Ω] [Algebra.IsIntegral ℚ Ω] {n : ℕ} (hn : 2 < n) (h2 : n.totient = 2) {ζ : Ω}
    (hζ : IsPrimitiveRoot ζ n) : QCM ℚ Ω :=
  haveI : NeZero n := ⟨by omega⟩
  haveI hc : IsCyclotomicExtension {n} ℚ ℚ⟮ζ⟯ := hζ.intermediateField_adjoin_isCyclotomicExtension ℚ
  haveI nf : NumberField ℚ⟮ζ⟯ := IsCyclotomicExtension.numberField {n} ℚ _
  { K := ℚ⟮ζ⟯
    nf := nf
    cm := IsCyclotomicExtension.Rat.isCMField _ (S := {n}) ⟨n, rfl, hn⟩
    two := (IsCyclotomicExtension.Rat.finrank n _).trans h2 }

example : (QCM.gauss (F := ℚ) Complex.I_sq).K = ℚ⟮Complex.I⟯ := rfl

example [IsTotallyReal F] : Nonempty (QCM F (AlgebraicClosure F)) := QCM.nonempty

end Gauss

def AttRes [IsTotallyReal F] {l : ℕ} [Fact l.Prime] {a : ℕ} (π : TR.CuspSub F a) (ι : Qbar l ≃+* ℂ)
    (L : Type) [Field L] [NumberField L] [Algebra F L] [Algebra L Ω] (r : G L Ω →* GL (Fin a) (Qbar l)) : Prop :=
  ∀ᶠ w : HeightOneSpectrum (𝓞 L) in Filter.cofinite, ∀ f : ℕ, normV w = normV (w.under (𝓞 F)) ^ f →
    ∃ B, π.HasSat (w.under (𝓞 F)) B ∧ FrobEig ι r w ((algSat a (normV (w.under (𝓞 F))) B).map (· ^ f))

section Att

variable {L : Type} [Field L] [NumberField L] [Algebra F L]

theorem AttRes.normV_eq_pow (w : HeightOneSpectrum (𝓞 L)) :
    normV w = normV (w.under (𝓞 F)) ^ w.asIdeal.inertiaDeg (𝓞 F) := by
  have : w.asIdeal.LiesOver (w.under (𝓞 F)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 F)).isMaximal
  show Ideal.absNorm w.asIdeal = Ideal.absNorm (w.under (𝓞 F)).asIdeal ^ w.asIdeal.inertiaDeg (𝓞 F)
  rw [← Ideal.absNorm_relNorm (𝓞 F) (𝓞 L) w.asIdeal,
    Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal (w.under (𝓞 F)).asIdeal, map_pow]

omit [Algebra F Ω] in

theorem AttRes.iff_inertiaDeg [IsTotallyReal F] [Algebra L Ω] {l : ℕ} [Fact l.Prime] {a : ℕ} (π : TR.CuspSub F a)
    (ι : Qbar l ≃+* ℂ) (r : G L Ω →* GL (Fin a) (Qbar l)) :
    AttRes π ι L r ↔ ∀ᶠ w : HeightOneSpectrum (𝓞 L) in Filter.cofinite, ∃ B, π.HasSat (w.under (𝓞 F)) B ∧
      FrobEig ι r w ((algSat a (normV (w.under (𝓞 F))) B).map (· ^ w.asIdeal.inertiaDeg (𝓞 F))) := by
  refine Filter.eventually_congr (Filter.Eventually.of_forall fun w =>
    ⟨fun h => h _ (AttRes.normV_eq_pow w), fun h f hf => ?_⟩)
  obtain rfl : f = w.asIdeal.inertiaDeg (𝓞 F) :=
    Nat.pow_right_injective (NumberField.HeightOneSpectrum.one_lt_absNorm (w.under (𝓞 F)))
      (hf.symm.trans (AttRes.normV_eq_pow w))
  exact h

theorem AttRes.hasSat_trivial [IsTotallyReal F] (v : HeightOneSpectrum (𝓞 F)) :
    (TR.CuspSub.triv F (le_refl 1)).HasSat v {1} := by
  have hact : ∀ g y, (TR.CuspSub.triv F (le_refl 1)).locRep v g y = y := fun g y => by
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 y.2
    obtain ⟨y, hy⟩ := y
    obtain rfl : c • TR.oneFn F 1 = y := hc
    rfl
  let e := LinearEquiv.toSpanNonzeroSingleton ℂ _ (TR.oneFn F 1) TR.oneFn_ne_zero
  refine ⟨(Submodule.ne_bot_iff _).2 ⟨⟨TR.oneFn F 1, Submodule.mem_span_singleton_self _⟩,
    GlobalTheory.LGrp.mem_fixed.2 fun k _ => hact k _, fun h => TR.oneFn_ne_zero (congrArg Subtype.val h)⟩, fun x _ h0 => ?_⟩
  let f : (TR.CuspSub.triv F (le_refl 1)).V →ₗ[ℂ] (GL (Fin 1) (v.adicCompletion F) → ℂ) :=
    (LinearMap.toSpanSingleton ℂ _ (fun _ => 1)).comp e.symm.toLinearMap
  have hi : Function.Injective f := fun a b h => by
    have := congrFun h 1
    have h2 : e.symm a • (1 : ℂ) = e.symm b • (1 : ℂ) := this
    exact e.symm.injective (smul_left_injective ℂ one_ne_zero h2)
  refine GlobalTheory.LFun.IsSatVecGL.of_map (ρ' := GlobalTheory.PRep.rightReg ℂ _ ℂ) f (fun g y => by rw [hact]; rfl) hi ?_
  have := GlobalTheory.LFun.isSatVecGL_of_isSpherical (w := v) (α := fun _ : Fin 1 => 1) (φ := f x)
    (fun b g k _ _ => by simp [f, Formalism.UG.chiDelta]; rfl) (fun h => h0 (hi (by rw [h, map_zero])))
  simpa using this

omit [Algebra F Ω] in

theorem AttRes.one_triv [IsTotallyReal F] [Algebra L Ω] {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) :
    AttRes (Ω := Ω) (TR.CuspSub.triv F (le_refl 1)) ι L 1 := by
  refine Filter.Eventually.of_forall fun w f _ =>
    ⟨{1}, AttRes.hasSat_trivial _, fun A _ => ⟨fun _ _ => rfl, fun σ _ => ?_⟩⟩
  simp [algSat, Matrix.charpoly_one]

example [IsTotallyReal F] (Q : QCM F Ω) {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) :
    AttRes (Ω := Ω) (TR.CuspSub.triv F (le_refl 1)) ι Q.K 1 := AttRes.one_triv ι

end Att

end GlobalTheory.RealGal

end
