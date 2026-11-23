import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeReadOfReadsExist
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMemDecIsFrob
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.TwInputs.HeckePinRead

theorem pull_locE {D : D7} {Ω : Type} [Field Ω] [Algebra D.host.E Ω] {A : Type} [CommGroup A] (a : Recip D Ω) (ha : a.Good)
    (φ : G D.host.E Ω →* A) (hφ : IsOpen (φ.ker : Set (G D.host.E Ω))) (P : Pl D.host.E) (e : AE D)
    (he : Formalism.L2.JoinChr.IsPlIdem D e P) (k : D.host.Eˣ)
    (hk : Valued.v ((Formalism.L2.Host.atFin P k : (P.adicCompletion D.host.E)ˣ) : P.adicCompletion D.host.E) = WithZero.exp (-1 : ℤ))
    (x : (AE D)ˣ) (hx : (x : AE D) = Formalism.L2.JoinChr.locE D e (k : D.host.E)) (B : ValuationSubring Ω)
    (hB : IsPlaceOver (F := D.host.E) B P) (hine : ∀ τ ∈ Ine (F := D.host.E) B, φ τ = 1) (σ : G D.host.E Ω)
    (hσ : IsFrob (F := D.host.E) B (normV P) σ) : a.pull φ x = (φ σ)⁻¹ := by
  have hκ : a.κ (x : AE D) = ((Neutral.B1.localIdele D.host.E P (Formalism.L2.Host.atFin P k) : Neutral.B1.Ideles D.host.E) :
      AdeleRing (𝓞 D.host.E) D.host.E) := by
    rw [hx]; exact ha.loc P e he k
  have hsym : a.sym x = a.art (Neutral.B1.localIdele D.host.E P (Formalism.L2.Host.atFin P k)) := by
    rw [Recip.sym, MonoidHom.comp_apply]
    congr 1
    exact Units.ext hκ
  obtain ⟨y, hy, hyσ⟩ := (ha.artin.frob P B hB _).mpr ⟨σ, hσ, rfl⟩
  have hu : Valued.v (((Formalism.L2.Host.atFin P k * y⁻¹ : (P.adicCompletion D.host.E)ˣ)) : P.adicCompletion D.host.E) = 1 := by
    have hy' : Valued.v ((y : (P.adicCompletion D.host.E)ˣ) : P.adicCompletion D.host.E) = WithZero.exp (-1 : ℤ) := hy
    rw [Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀, hk, hy']
    exact mul_inv_cancel₀ WithZero.exp_ne_zero
  obtain ⟨τ, hτ, hτu⟩ := (ha.artin.ine P B hB _).mp ⟨_, hu, rfl⟩
  have hs : a.sym x = GlobalTheory.HeckeGal.toAb D.host.E Ω (τ * σ⁻¹) := by
    rw [hsym, show Formalism.L2.Host.atFin P k = (Formalism.L2.Host.atFin P k * y⁻¹) * y by group, map_mul, map_mul, hyσ,
      ← hτu, map_mul]
  rw [a.pull_eq hφ hs, map_mul, hine τ hτ, map_inv, one_mul]

theorem isOpen_ker_psiAt (D : D7) (i : D.ntw.Tw) (b : Bool) :
    IsOpen ((Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker : Set (G D.host.E D.nd.Om)) := by
  have e : (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker = (D.ntw.delta i).ker := by
    ext g
    cases b <;> simp [Formalism.MainNotions.BlochKatoReduction.Gen.psiAt, MonoidHom.mem_ker]
  rw [e]
  exact D.ntw.delta_open i

theorem chi_locU_unif {D : D7} {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (P : PlE D.host)
    (hP : P ∉ D.ntw.S0 i) {e : AE D} (he : Formalism.L2.JoinChr.IsPlIdem D e P) (hee : e * e = e) (σ : G D.host.E D.nd.Om)
    (hσ : IsFrob (F := D.host.E) (D.nd.plOm.1 P) (normV P) σ) :
    (((ρ.B i j b).de.chi (Formalism.L2.JoinChr.locU hee (Formalism.L2.Host.unif P)) : Circle) : ℂ) =
      (ρ.eO i b (algebraMap (D.ntw.O0 i) (D.ntw.O i)
        ((Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i) σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i)))⁻¹ := by
  rw [hρ.delta i j b]
  have hopen := isOpen_ker_psiAt D i b
  have : Finite (G D.host.E D.nd.Om ⧸ (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker) :=
    Subgroup.quotient_finite_of_isOpen _ hopen
  have hfi : (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hn : (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
  have hpow : Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i) σ⁻¹ ^ (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker.index = 1 := by
    rw [← map_pow]
    exact MonoidHom.mem_ker.1 (Subgroup.pow_index_mem _ σ⁻¹)
  have hine : ∀ τ ∈ Ine (F := D.host.E) (D.nd.plOm.1 P), Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i) τ = 1 := by
    intro τ hτ
    have h : D.ntw.delta i τ = 1 := by
      by_contra hne
      exact hP (D.ntw.primes_subset_exceptional i ((D.ntw.delta_ram i P _ (D.nd.plOm.2 P)).1 ⟨τ, hτ, hne⟩))
    cases b <;> simp [Formalism.MainNotions.BlochKatoReduction.Gen.psiAt, h]
  have hpull := pull_locE ρ.rc hρ.rc _ hopen P e he (Formalism.L2.Host.unif P) (Formalism.L2.Host.unif_spec P) _
    (Formalism.L2.JoinChr.locU_val hee _) _ (D.nd.plOm.2 P) hine σ hσ
  change ((charOf ρ.rc ((ρ.eO i b).comp (algebraMap (D.ntw.O0 i) (D.ntw.O i)))
    (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)) _ : Circle) : ℂ) = _
  rw [charOf, MonoidHom.comp_apply, MonoidHom.comp_apply, hpull, unitPart_of_pow hn]
  · simp
  · rw [← map_pow, ← map_inv, ← map_pow, map_pow (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)), hpow, map_one]

def frobU (D : D7) (P : PlE D.host) : G D.host.E D.nd.Om :=
  (GlobalTheory.TripleGal.exists_mem_Dec_isFrob D P (D.nd.plOm.1 P) (D.nd.plOm.2 P)).choose

theorem frobU_spec (D : D7) (P : PlE D.host) : IsFrob (F := D.host.E) (D.nd.plOm.1 P) (normV P) (frobU D P) :=
  (GlobalTheory.TripleGal.exists_mem_Dec_isFrob D P (D.nd.plOm.1 P) (D.nd.plOm.2 P)).choose_spec.2

def uD (D : D7) : ∀ i : D.ntw.Tw, Bool → PlE D.host → (D.ntw.O i)ˣ := fun i b P =>
  Units.map (algebraMap (D.ntw.O0 i) (D.ntw.O i)).toMonoidHom (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i) (frobU D P))

variable {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type}

theorem isDeltaInv_uD {D : D7} {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks]
    [Algebra Ks D.what₂.LL] {Rl : RealDat3 D A3 Ks} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {ρ : Setup D.ntw} (hρ : ρ.Good)
    (hpin : RealPin Rl cG ρ) : IsDeltaInv ρ (uD D) := by
  intro i j b k P hk α z hα hz
  obtain ⟨-, -, hsp, hP⟩ := hk
  have hdQ : Bridge.SplitOff P (((ρ.B i j b).de.Q : Finset _) : Set (Pl D.host.E)) :=
    GlobalTheory.SplitOffS0.main hρ i _ (fun P' hP' => by
      rw [hρ.delta i j b] at hP'
      exact D.ntw.primes_subset_exceptional i (mem_half.1 hP').1) P hsp hP
  obtain ⟨e, he⟩ := GlobalTheory.MovedIdem.exists_isIdemAt P hdQ.1
  have hee : e * e = e := he.1.1
  have h1 := (hpin.delta i j b).2 P e (GlobalTheory.HeckeDetChar.isPlIdem he) (Formalism.L2.Host.unif P) _
    (Formalism.L2.JoinChr.locU_val hee (Formalism.L2.Host.unif P))
  have h2 := chi_locU_unif hρ i j b P hP (GlobalTheory.HeckeDetChar.isPlIdem he) hee (frobU D P) (frobU_spec D P)
  rw [GlobalTheory.HeckeDetChar.chi_detAt (hpin.delta i j b) (hρ.base i j b).de.unram (hρ.base i j b).de.split hdQ hα hz,
    show (((Rl.C.delAt (D.ntw.l i)).val P : ℂˣ) : ℂ) = (((ρ.B i j b).de.chi (Formalism.L2.JoinChr.locU hee (Formalism.L2.Host.unif P)) : Circle) : ℂ)
      from h1.symm, h2, inv_pow, inv_inv]
  rfl

end GlobalTheory.TwInputs.HeckePinRead

namespace GlobalTheory.TwInputs

end GlobalTheory.TwInputs
