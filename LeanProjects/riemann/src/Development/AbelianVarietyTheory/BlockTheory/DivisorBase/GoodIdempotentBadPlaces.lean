import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.LevelCuspCharacters

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta
open Formalism.IndefR.Lev Formalism.IndefR.Mult
open Formalism.L2.DIV (Pl kP primesOf IsTypeDatum G0 LevDat P0 IsGenericPsi)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters (SSParam GoodAt typeChar centralIdem chiTame IsGeneratorFamily)
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.GoodIdempotentBadPlaces

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters.factPrime

variable {D : D7}

abbrev typePl (pb : Fin 2 → 𝓞 D.host.E) : Finset (Pl D.host.E) := primesOf (pb 0 * pb 1)

abbrev PlOf (pb : Fin 2 → 𝓞 D.host.E) (i : Fin 2) : Type := {w : ↥(typePl pb) // pb i ∈ w.1.asIdeal}

abbrev PlAll (pb : Fin 2 → 𝓞 D.host.E) : Type := Σ i : Fin 2, PlOf pb i

instance finite_kP (w : Pl D.host.E) : Finite (kP w) :=
  Ideal.finiteQuotientOfFreeOfNeBot w.asIdeal w.ne_bot

def resIso {pb : Fin 2 → 𝓞 D.host.E} (h : IsTypeDatum D.host.g pb) (v : PlAll pb) :
    ZMod (D.host.g v.1) ≃+* kP v.2.1.1 :=
  haveI := Fintype.ofFinite (kP v.2.1.1)
  ZMod.ringEquivOfPrime _ (h.prime v.1) (by rw [← Nat.card_eq_fintype_card]; exact h.deg1 v.1 _ v.2.2)

def compAt {pb : Fin 2 → 𝓞 D.host.E} (h : IsTypeDatum D.host.g pb) {n : ℕ} (a : G0 (typePl pb) n) (v : PlAll pb) :
    GL (Fin n) (ZMod (D.host.g v.1)) :=
  Matrix.GeneralLinearGroup.map ((resIso h v).symm : kP v.2.1.1 →+* ZMod (D.host.g v.1)) (a v.2.1)

def tupleChar {pb : Fin 2 → 𝓞 D.host.E} (h : IsTypeDatum D.host.g pb) {n : ℕ}
    (s : ∀ v : PlAll pb, SSParam (D.host.g v.1) ℂ n) (a : G0 (typePl pb) n) : ℂ :=
  haveI := Fintype.ofFinite (PlAll pb)
  ∏ v : PlAll pb, typeChar (s v) (compAt h a v)

def goodTypes {pb : Fin 2 → 𝓞 D.host.E} (h : IsTypeDatum D.host.g pb)
    (om : ∀ i : Fin 2, (ZMod (D.host.g i))ˣ →* ℂˣ) (n : ℕ) : Set (G0 (typePl pb) n → ℂ) :=
  tupleChar h '' {s | ∀ i : Fin 2, GoodAt (chiTame (H := D.host) om i) (fun w : PlOf pb i => s ⟨i, w⟩)}

theorem goodTypes_finite {pb : Fin 2 → 𝓞 D.host.E} (h : IsTypeDatum D.host.g pb)
    (om : ∀ i : Fin 2, (ZMod (D.host.g i))ˣ →* ℂˣ) (n : ℕ) : (goodTypes h om n).Finite :=
  (Set.toFinite _).image _

def goodIdem {pb : Fin 2 → 𝓞 D.host.E} (h : IsTypeDatum D.host.g pb)
    (om : ∀ i : Fin 2, (ZMod (D.host.g i))ˣ →* ℂˣ) (n : ℕ) : MonoidAlgebra ℂ (G0 (typePl pb) n) :=
  ∑ τ ∈ (goodTypes_finite h om n).toFinset, centralIdem τ

def eLin (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (L : LevDat D.host.E ℂ V.rank) (e : G0 L.Pg L.r →₀ ℂ) :
    (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ) where
  toFun := eAct V β L e
  map_add' F F' := by
    funext x
    simp only [eAct, Finsupp.sum, Pi.add_apply, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun g _ => ?_
    unfold actG0
    split_ifs
    · simp only [Pi.add_apply]; ring
    · simp
  map_smul' a F := by
    funext x
    simp only [eAct, Finsupp.sum, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    unfold actG0
    split_ifs
    · simp only [Pi.smul_apply, smul_eq_mul]; ring
    · simp

variable (D) in

def badPl : Finset (HeightOneSpectrum (𝓞 D.host.F)) := primesOf ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.F)

theorem mem_badPl (v : HeightOneSpectrum (𝓞 D.host.F)) :
    v ∈ badPl D ↔ ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal := by
  rw [badPl, Formalism.L2.DIV.mem_primesOf]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  exact_mod_cast mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero

def levelDatumAtBasePrime (V : HSp D) (pb : Fin 2 → 𝓞 D.host.E) (ψ : ∀ w : Pl D.host.E, AddChar (kP w) ℂ) : LevDat D.host.E ℂ V.rank :=
  datW V.rank (typePl pb) (P0 (typePl pb) V.rank ψ) Frm.A

abbrev Model (D : D7) (j : ℕ) : Type 1 := DSModel (D.sp.W j) (parW (D.sp.W j) (Formalism.L2.NTheta.wtOf D (D.sp.W j)))

abbrev EigSys (D : D7) : Type := HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ

section Spaces

variable (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
  {pb : Fin 2 → 𝓞 D.host.E} (h : IsTypeDatum D.host.g pb) (om : ∀ i : Fin 2, (ZMod (D.host.g i))ˣ →* ℂˣ)
  (ψ : ∀ w : Pl D.host.E, AddChar (kP w) ℂ)
  (j : ℕ) (β : GL (Fin (D.sp.W j).rank) (EAf D)) (M : Model D j)

def levP0 (pb : Fin 2 → 𝓞 D.host.E) (ψ : ∀ w : Pl D.host.E, AddChar (kP w) ℂ) (j : ℕ)
    (β : GL (Fin (D.sp.W j).rank) (EAf D)) : Set (GA D (D.sp.W j)) :=
  levG (D.sp.W j) β (levelDatumAtBasePrime (D.sp.W j) pb ψ)

def chiP0 (pb : Fin 2 → 𝓞 D.host.E) (ψ : ∀ w : Pl D.host.E, AddChar (kP w) ℂ) (j : ℕ)
    (β : GL (Fin (D.sp.W j).rank) (EAf D)) : GA D (D.sp.W j) → ℂ :=
  levChi (D.sp.W j) β (levelDatumAtBasePrime (D.sp.W j) pb ψ)

def eW : (GA D (D.sp.W j) → ℂ) →ₗ[ℂ] (GA D (D.sp.W j) → ℂ) :=
  eLin (D.sp.W j) β (levelDatumAtBasePrime (D.sp.W j) pb ψ) (goodIdem h om (D.sp.W j).rank).coeff

def goodForms : Submodule ℂ (MMap M) :=
  WgoodRec θ j M (levP0 pb ψ j β) (chiP0 pb ψ j β) (eW h om ψ j β)

def heckePart (c : EigSys D) : Submodule ℂ (MMap M) :=
  Wpart θ j M (levP0 pb ψ j β) (chiP0 pb ψ j β) (eW h om ψ j β) (badPl D) c

def occurring : Set (EigSys D) :=
  IxFull θ M (levP0 pb ψ j β) (chiP0 pb ψ j β) (badPl D) (eW h om ψ j β)

theorem heckePart_le (c : EigSys D) : heckePart θ h om ψ j β M c ≤ goodForms θ h om ψ j β M := inf_le_right

theorem mem_heckePart (c : EigSys D) (T : MMap M) :
    T ∈ heckePart θ h om ψ j β M c ↔ T ∈ goodForms θ h om ψ j β M ∧
      ∀ P d R, Hecke₂ (D.sp.W j) (levP0 pb ψ j β) (chiP0 pb ψ j β) (badPl D) P d R →
        ∀ v, heckeLin (D.sp.W j) R (T v) = c P d • T v := by
  constructor
  · exact fun hT => ⟨hT.2, ((mem_partFull θ M _ _ _ c T).1 hT.1).2⟩
  · exact fun hT => ⟨(mem_partFull θ M _ _ _ c T).2 ⟨hT.1.1, hT.2⟩, hT.1⟩

theorem heckePart_ne_bot {c : EigSys D} (hc : c ∈ occurring θ h om ψ j β M) : heckePart θ h om ψ j β M c ≠ ⊥ := hc.2

def IsOrthSum (I : Set (EigSys D)) : Prop :=
  I.Finite ∧
  goodForms θ h om ψ j β M = ⨆ c ∈ I, heckePart θ h om ψ j β M c ∧
  (iSupIndep fun c : I => heckePart θ h om ψ j β M c.1) ∧
  ∀ (μ : Measure (GA D (D.sp.W j))) (𝓕 : Set (GA D (D.sp.W j))), μ.IsHaarMeasure →
    IsFundamentalDomain (GQ (D.sp.W j)) 𝓕 μ → ∀ c ∈ I, ∀ c' ∈ I, c ≠ c' →
      ∀ T ∈ heckePart θ h om ψ j β M c, ∀ T' ∈ heckePart θ h om ψ j β M c', IsMultIP M μ 𝓕 T T' 0

end Spaces

def IsTypeFrame (V : HSp D) (β : GL (Fin V.rank) (EAf D)) : Prop :=
  ∃ (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (a : ℕ), IsBaseFrame V β Λ ((D.host.g 0 * D.host.g 1) ^ a)

def GoodFormsOrthSum (D : D7) : Prop :=
  ∀ (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ →
  ∀ (pb : Fin 2 → 𝓞 D.host.E) (h : IsTypeDatum D.host.g pb)
    (om : ∀ i : Fin 2, (ZMod (D.host.g i))ˣ →* ℂˣ), IsGeneratorFamily (H := D.host) om →
  ∀ (ψ : ∀ w : Pl D.host.E, AddChar (kP w) ℂ), IsGenericPsi (typePl pb) ψ →
  ∀ (βm : GL (Fin (D.sp.W D.R.m).rank) (EAf D)), IsTypeFrame (D.sp.W D.R.m) βm → ∀ Mm : Model D D.R.m,
  ∀ j, 1 ≤ j → j ≤ D.R.m →
  ∀ (β : GL (Fin (D.sp.W j).rank) (EAf D)), IsTypeFrame (D.sp.W j) β → ∀ M : Model D j,
    IsOrthSum θ h om ψ j β M (occurring θ h om ψ D.R.m βm Mm)

example (D : D7) : (D.sp.W D.R.m).IsPosDef := by
  intro τ
  have h2 := D.R.two_le_m
  rw [D.sp.W_sigval _ (by omega) le_rfl, D.sp.W_rank _ (by omega) le_rfl]
  simp [Ranks.sigW, Ranks.r]

end GlobalTheory.IndefiniteRowSideFullHecke.GoodIdempotentBadPlaces
