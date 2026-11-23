import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU

noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep

namespace GlobalTheory.CellDec

variable (E : Type) [Field E] [NumberField E] (n : ℕ)

abbrev NA : Subgroup (GA E n) := GlobalTheory.SmGL.unipB (Ad E) (Fin n)

def NE : Subgroup (GA E n) := (GlobalTheory.SmGL.unipB E (Fin n)).map (ratGL E n)

def compV (v : HeightOneSpectrum (𝓞 E)) : GA E n →* GL (Fin n) (v.adicCompletion E) :=
  GeneralLinearGroup.map ((pLoc E v).comp (pFin E))

def US (S : Finset (HeightOneSpectrum (𝓞 E))) : Subgroup (GA E n) :=
  ⨅ (v : HeightOneSpectrum (𝓞 E)) (_ : v ∉ S), (GlobalTheory.LFun.KGL v n).comap (compV E n v)

def C0 (S : Finset (HeightOneSpectrum (𝓞 E))) : Set (GA E n) :=
  {g | ∃ u ∈ NA E n, ∃ k ∈ US E n S, g = u * k}

abbrev abelian₂ (S : Finset (HeightOneSpectrum (𝓞 E))) : Type :=
  {l : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ) // ∀ v ∈ S, l v = 0}

variable {E}

def adl (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ) (m : HeightOneSpectrum (𝓞 E) →₀ ℤ) : (Af E)ˣ where
  val := ⟨fun v => ((ϖ v ^ m v : (v.adicCompletion E)ˣ) : v.adicCompletion E), by
    filter_upwards [m.finite_support.compl_mem_cofinite] with v hv
    have hv : m v = 0 := by simpa using hv
    rw [hv, zpow_zero, Units.val_one]
    exact one_mem _⟩
  inv := ⟨fun v => ((ϖ v ^ (-m v) : (v.adicCompletion E)ˣ) : v.adicCompletion E), by
    filter_upwards [m.finite_support.compl_mem_cofinite] with v hv
    have hv : m v = 0 := by simpa using hv
    rw [hv, neg_zero, zpow_zero, Units.val_one]
    exact one_mem _⟩
  val_inv := FiniteAdeleRing.ext _ fun v => by
    change ((ϖ v ^ m v : (v.adicCompletion E)ˣ) : v.adicCompletion E) * ((ϖ v ^ (-m v) : (v.adicCompletion E)ˣ) : _) = 1
    rw [← Units.val_mul, ← _root_.zpow_add, add_neg_cancel, zpow_zero, Units.val_one]
  inv_val := FiniteAdeleRing.ext _ fun v => by
    change ((ϖ v ^ (-m v) : (v.adicCompletion E)ˣ) : v.adicCompletion E) * ((ϖ v ^ m v : (v.adicCompletion E)ˣ) : _) = 1
    rw [← Units.val_mul, ← _root_.zpow_add, neg_add_cancel, zpow_zero, Units.val_one]

def tl (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ) (l : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ)) : GA E n :=
  finGL E n (GlobalTheory.SmGL.diagT (Af E) (Fin n) fun i => adl ϖ (Finsupp.mapRange (fun x : Fin n → ℤ => x i) rfl l))

def wtS (a : Fin n → ℤ) : ℤ := ∑ i : Fin n, ∑ j : Fin n, if i < j then a i - a j else 0

def dinv (l : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ)) : ℝ :=
  ∏ v ∈ l.support, (qV E v : ℝ) ^ wtS n (l v)

end GlobalTheory.CellDec

namespace GlobalTheory.CellDec
open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep
variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem diagT_conj_mem {R : Type} [CommRing R] (w : Fin n → Rˣ) {u : GL (Fin n) R}
    (hu : u ∈ GlobalTheory.SmGL.unipB R (Fin n)) :
    GlobalTheory.SmGL.diagT R (Fin n) w * u * (GlobalTheory.SmGL.diagT R (Fin n) w)⁻¹ ∈ GlobalTheory.SmGL.unipB R (Fin n) := by
  rw [← map_inv]
  obtain ⟨h1, h2⟩ := (GlobalTheory.SmGL.mem_unipB R).1 hu
  refine (GlobalTheory.SmGL.mem_unipB R).2 ⟨fun i j hij => ?_, fun i => ?_⟩
  · simp only [Units.val_mul, GlobalTheory.SmGL.val_diagT, Matrix.diagonal_mul, Matrix.mul_diagonal, h1 i j hij]
    simp
  · simp only [Units.val_mul, GlobalTheory.SmGL.val_diagT, Matrix.diagonal_mul, Matrix.mul_diagonal, h2 i]
    simp

theorem countable_places (F : Type) [Field F] [NumberField F] : Countable (HeightOneSpectrum (𝓞 F)) := by
  have : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
  have : Countable (𝓞 F) := (RingOfIntegers.coe_injective (K := F)).countable
  have : Countable (Ideal (𝓞 F)) := by
    have hs : Function.Surjective (fun t : Finset (𝓞 F) => Ideal.span (t : Set (𝓞 F))) := fun I => by
      obtain ⟨t, ht⟩ := (IsNoetherian.noetherian I : I.FG)
      exact ⟨t, ht⟩
    exact hs.countable
  have hi : Function.Injective (HeightOneSpectrum.asIdeal (R := 𝓞 F)) := fun v w h => HeightOneSpectrum.ext h
  exact hi.countable

instance countable_Lam (S : Finset (HeightOneSpectrum (𝓞 E))) : Countable (abelian₂ E n S) := by
  have := countable_places E
  exact Subtype.countable

theorem tl_eq_diagT (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ) (l : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ)) :
    tl n ϖ l = GlobalTheory.SmGL.diagT (Ad E) (Fin n) fun i => finId E (adl ϖ (Finsupp.mapRange (fun x : Fin n → ℤ => x i) rfl l)) := by
  apply Units.ext
  rw [GlobalTheory.SmGL.val_diagT]
  ext i j
  change (1 : Matrix (Fin n) (Fin n) (Ad E)) i j - sFin E ((1 : Matrix (Fin n) (Fin n) (Af E)) i j) +
    sFin E ((GlobalTheory.SmGL.diagT (Af E) (Fin n) _ : Matrix (Fin n) (Fin n) (Af E)) i j) = _
  rw [GlobalTheory.SmGL.val_diagT]
  by_cases h : i = j
  · subst h; simp [finId, GlobalTheory.CuspRep.corner]
  · simp [h]

theorem tl_conj_mem (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ) (l : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ))
    {u : GA E n} (hu : u ∈ NA E n) : tl n ϖ l * u * (tl n ϖ l)⁻¹ ∈ NA E n := by
  rw [tl_eq_diagT]; exact diagT_conj_mem _ hu

theorem adelicUnitriangular_mul_mem_unipotentTimesIntegral {S : Finset (HeightOneSpectrum (𝓞 E))} {u g : GA E n} (hu : u ∈ NA E n) (hg : g ∈ C0 E n S) :
    u * g ∈ C0 E n S := by
  obtain ⟨v, hv, k, hk, rfl⟩ := hg
  exact ⟨u * v, mul_mem hu hv, k, hk, (mul_assoc _ _ _).symm⟩

end GlobalTheory.CellDec
