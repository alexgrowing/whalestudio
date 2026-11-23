import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.HodgeC
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GrCechFin
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictPullBijectiveOfForall
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison

namespace GlobalTheory.CompanionTheory.OmLoc

open Pb

theorem mor_mk_congr {R R' : Type} [CommRing R] [CommRing R'] {C C' : Type 1} [Category.{0} C] [Category.{0} C']
    {F : C ⥤ ModuleCat.{0} R} {F' : C' ⥤ ModuleCat.{0} R'} {σ : R →+* R'} (G : C' ⥤ C)
    (τ τ' : (T : C') → F.obj (G.obj T) →ₛₗ[σ] F'.obj T) (n n') (h : τ = τ') :
    (⟨G, τ, n⟩ : CH.Mor F F' σ) = ⟨G, τ', n'⟩ := by
  subst h; rfl

theorem sq_incl_eq {b : Base} {L : b.Fun} {Q Q' : ObjectProperty (Thick L)} (h : Q' ≤ Q) (r r' : ℤ) :
    (incl h).sq (incl_fil h r) (incl_fil h r') =
      (CH.Mor.restrict (sq (sFil Q r) (sFil Q r')) (ObjectProperty.ιOfLE h) :) := by
  refine mor_mk_congr _ _ _ _ _ ?_
  funext T
  refine LinearMap.ext fun x => ?_
  obtain ⟨x, hx⟩ := x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

theorem chain {b : Base} {L : b.Fun} (r r' : ℤ) (Q1 Q2 Q3 : ObjectProperty (Thick L)) (h12 : Q2 ≤ Q1) (h23 : Q3 ≤ Q2) (n : ℕ)
    (b1 : Function.Bijective ((CH.Mor.restrict (sq (thFil L r) (thFil L r')) Q1.ι).pull n))
    (b2 : Function.Bijective (((incl h12).sq (incl_fil h12 r) (incl_fil h12 r')).pull n))
    (b3 : Function.Bijective (((incl h23).sq (incl_fil h23 r) (incl_fil h23 r')).pull n)) :
    Function.Bijective ((CH.Mor.restrict (sq (thFil L r) (thFil L r')) Q3.ι).pull n) := by
  have e : CH.Mor.restrict (sq (thFil L r) (thFil L r')) Q3.ι =
      (CH.Mor.restrict (sq (thFil L r) (thFil L r')) Q1.ι).comp
        (F' := sq (sFil Q1 r) (sFil Q1 r')) (σ' := RingHom.id _) (σ'' := RingHom.id _)
        (((incl h12).sq (incl_fil h12 r) (incl_fil h12 r')).comp (σ'' := RingHom.id _) ((incl h23).sq (incl_fil h23 r) (incl_fil h23 r'))) := by
    rw [sq_incl_eq, sq_incl_eq]
    rfl
  have f : ⇑((CH.Mor.restrict (sq (thFil L r) (thFil L r')) Q3.ι).pull n) =
      ⇑(((incl h23).sq (incl_fil h23 r) (incl_fil h23 r')).pull n) ∘
        ⇑(((incl h12).sq (incl_fil h12 r) (incl_fil h12 r')).pull n) ∘
          ⇑((CH.Mor.restrict (sq (thFil L r) (thFil L r')) Q1.ι).pull n) := by
    funext x
    rw [e]
    exact (P.pull_comp _ _ n x).1.trans ((P.pull_comp _ _ n _).1)
  rw [f]
  exact b3.comp (b2.comp b1)

theorem grT_restrict_bijective : ∀ {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (𝒱 : Set X.Opens), sSup 𝒱 = ⊤ →
    ∀ (a s : ℕ), a < s → ∀ n : ℕ, Function.Bijective ((CH.Mor.restrict (HT.grT (smFun X q) a) (Pb.KS q s 𝒱).ι).pull n) := by
  intro K _ X q 𝒱 h𝒱 a s has n
  have hI : ∀ T : Thick (nlFun (dividedPowersBot K) 0 X q (Ideal.Quotient.mk ⊥)), InU ⊤ T := fun T => le_of_eq rfl
  have h12 : St (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) (TF 1 s) {⊤} ≤ St ⊤ {⊤} :=
    fun T hT => ⟨trivial, hT.2⟩
  have h23 : St (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) (TF 1 s) 𝒱 ≤ St (TF 1 s) {⊤} :=
    fun T hT => ⟨hT.1, ⊤, rfl, hI T⟩
  exact chain (L := nlFun (dividedPowersBot K) 0 X q (Ideal.Quotient.mk ⊥)) (a : ℤ) ((a : ℤ) + 1) _ _ _ h12 h23 n
    (GlobalTheory.CompanionTheory.OmRes.restrict_pull_bijective_of_forall _ _ (fun T => ⟨trivial, ⊤, rfl, hI T⟩) n)
    (Pb.refl ⊤ 1 s (Or.inl ⟨rfl, rfl⟩) {⊤} h12 (a : ℤ) ((a : ℤ) + 1) (by omega) n)
    ((Pb.zar (TF 1 s) (Or.inl ⟨rfl, 1, s, rfl⟩) 𝒱 {⊤} h23 (by rintro W rfl; exact h𝒱.ge) n).1 (a : ℤ) ((a : ℤ) + 1))

end GlobalTheory.CompanionTheory.OmLoc
