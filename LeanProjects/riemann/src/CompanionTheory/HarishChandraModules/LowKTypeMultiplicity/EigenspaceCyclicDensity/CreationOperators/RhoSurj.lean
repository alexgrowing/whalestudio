import Mathlib
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOneP
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds

noncomputable section

namespace GlobalTheory.CompanionTheory.LKDens

open CompanionTheory.D.LK
open CompanionTheory.D.DSIC (KStab)

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

theorem burnside {A : Type} [Ring A] [Algebra ℂ A] [FiniteDimensional ℂ V] (ρ : A →ₐ[ℂ] Module.End ℂ V)
    (hnt : Nontrivial V) (hirr : ∀ W : Submodule ℂ V, (∀ a : A, ∀ w ∈ W, ρ a w ∈ W) → W = ⊥ ∨ W = ⊤) :
    Function.Surjective ρ := by
  classical
  letI : Module A V := Module.compHom V (ρ : A →+* Module.End ℂ V)
  have hsm : ∀ (a : A) (x : V), a • x = ρ a x := fun _ _ => rfl
  haveI : IsScalarTower ℂ A V := ⟨fun c a x => by simp [hsm]⟩
  haveI : IsSimpleModule A V := by
    rw [isSimpleModule_iff]
    refine { eq_bot_or_eq_top := fun W => ?_ }
    rcases hirr (W.restrictScalars ℂ) (fun a w hw => W.smul_mem a hw) with h | h
    · left; exact (Submodule.restrictScalars_eq_bot_iff ℂ A V).1 h
    · right; exact (Submodule.restrictScalars_eq_top_iff ℂ A V).1 h
  have hscal : ∀ φ : Module.End A V, ∃ c : ℂ, ∀ m, φ m = c • m := by
    intro φ
    obtain ⟨c, hc⟩ := (IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed (A := A) (V := V) ℂ).2 φ
    exact ⟨c, fun m => by rw [← hc]; rfl⟩
  intro f
  let F : Module.End (Module.End A V) V :=
    { toFun := f
      map_add' := fun x y => by simp
      map_smul' := fun φ m => by
        obtain ⟨c, hc⟩ := hscal φ
        simp only [Module.End.smul_def, RingHom.id_apply, hc, map_smul] }
  let b := Module.finBasis ℂ V
  obtain ⟨r, hr⟩ := jacobson_density F (Finset.univ.image b)
  refine ⟨r, b.ext fun i => ?_⟩
  exact (hr _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))).symm

def rho (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (L : Submodule ℂ V) (hL : KStab ε E L) :
    FreeAlgebra ℂ (Fin n × Fin n) →ₐ[ℂ] Module.End ℂ L :=
  FreeAlgebra.lift ℂ fun p => if h : ε p.1 = ε p.2 then (E p.1 p.2).restrict (hL p.1 p.2 h) else 0

def psi (ε : Fin n → Bool) : FreeAlgebra ℂ (Fin n × Fin n) →ₐ[ℂ] FreeAlgebra ℂ (Fin n × Fin n) :=
  FreeAlgebra.lift ℂ fun p => if ε p.1 = ε p.2 then FreeAlgebra.ι ℂ p else 0

theorem ev_psi (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (L : Submodule ℂ V) (hL : KStab ε E L)
    (r : FreeAlgebra ℂ (Fin n × Fin n)) : ∀ s : L, ev E (psi ε r) s = (rho ε E L hL r s : V) := by
  induction r using FreeAlgebra.induction with
  | grade0 c => intro s; simp [Module.algebraMap_end_apply]
  | grade1 p =>
    intro s
    by_cases h : ε p.1 = ε p.2
    · simp [psi, rho, ev, h]
    · simp [psi, rho, ev, h]
  | mul a b ha hb => intro s; simp [map_mul, Module.End.mul_apply, ha, hb]
  | add a b ha hb => intro s; simp [map_add, ha, hb]

theorem rho_surj (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (L : Submodule ℂ V) (hL : KStab ε E L)
    [FiniteDimensional ℂ L] {v : V} (hv : v ≠ 0) (hvL : v ∈ L)
    (hirr : ∀ L' ≤ L, KStab ε E L' → L' = ⊥ ∨ L' = L) : Function.Surjective (rho ε E L hL) := by
  refine burnside (rho ε E L hL) ⟨⟨v, hvL⟩, 0, fun h => hv (congrArg Subtype.val h)⟩ ?_
  intro W hW
  have hst : KStab ε E (W.map L.subtype) := by
    rintro a b hab _ ⟨w, hw, rfl⟩
    refine ⟨rho ε E L hL (FreeAlgebra.ι ℂ (a, b)) w, hW _ w hw, ?_⟩
    simp [rho, hab]
  rcases hirr _ (Submodule.map_subtype_le L W) hst with h | h
  · left
    apply Submodule.map_injective_of_injective L.injective_subtype
    simpa using h
  · right
    apply Submodule.map_injective_of_injective L.injective_subtype
    simpa using h

theorem dens : CompanionTheory.D.LK.Dens := by
  intro n ε V _ _ E μ v L _ _ hv hvL _ hfd hL hirr _
  have hs := rho_surj ε E L hL hv hvL hirr
  let b := Module.finBasis ℂ L
  constructor
  · intro x hx
    obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one ℂ
      (show (⟨v, hvL⟩ : L) ≠ 0 from fun h => hv (congrArg Subtype.val h))
    obtain ⟨r, hr⟩ := hs (f.smulRight (⟨x, hx⟩ : L))
    refine ⟨psi ε r, ?_⟩
    have := ev_psi ε E L hL r ⟨v, hvL⟩
    rw [hr] at this
    simpa [hf] using this
  · intro φ hφ
    choose u hu using fun i => hφ (b i)
    choose r hr using fun i => hs ((b.coord i).smulRight (⟨v, hvL⟩ : L))
    refine ⟨∑ i, u i * psi ε (r i), fun s => ?_⟩
    have hu' : ∀ i, ev E (u i) v = φ (b i) := fun i => by simpa using hu i
    conv_rhs => rw [← b.sum_repr s]
    simp only [map_sum, map_mul, LinearMap.sum_apply, Module.End.mul_apply, ev_psi ε E L hL, hr, map_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [hu']

end GlobalTheory.CompanionTheory.LKDens
