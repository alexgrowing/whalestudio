import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.W8AddTransposeEqE8
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

noncomputable section
namespace GlobalTheory.ZM
variable {o : Type} [CommRing o] {S : Scheme.{0}} {g k : ℕ} {J : Type} {b : TBase o k} {s : S ⟶ Sp o}
section PEL
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def IsSympBasis (D : Datum H) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La) : Prop :=
  ∀ i j, D.EF (bas (Pi.single i 1)) (bas (Pi.single j 1)) = Out.stdSymp g i j

def IsPEL (D : Datum H) (a : J → 𝓞 E) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La) (ρ : o) (t : TObj g k J b s) (τ : SAB H S) : Prop :=
  ∃ φ : τ.G ≅ t.A, IsMonHom φ.hom ∧ LBIso τ.PP.L (t.L.pull φ.hom.left) ∧ (∀ j, τ.act.act (a j) ≫ φ.hom = φ.hom ≫ t.act j) ∧
    ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (x : Sp K ⟶ S) (β : o →+* K), x ≫ s = spMap β →
      DetCond D τ.act x (β ρ) ∧ ∃ I : TateIso D K (Over.mk x ⟶ τ.G) (fun c y => y ≫ τ.act.act c)
          (fun n y y' c => Out.WeilIs τ.G τ.PP.L n y y' (unitOn c)),
        (I.ζ k : K) = β b.ζ ∧ ∀ i, I.ev k (bas (Pi.single i 1)) ≫ φ.hom =
          (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver S) ≫ t.pt i

def PELClass (D : Datum H) (a : J → 𝓞 E) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La) (ρ : o) (em : o →+* ℂ)
    (t : TObj g k J b (spMap em)) : Prop := ∃ τ, IsPEL D a bas ρ t τ
end PEL
section Siegel
variable {h : ℕ}

def IsE8 (W : Matrix (Fin 8) (Fin 8) ℤ) : Prop := ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef ∧ (W + W.transpose).det = 1

def IsSharpBasis (W : Matrix (Fin 8) (Fin 8) ℤ) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))) : Prop :=
  ∀ i j, ∑ u, ∑ v, (W + W.transpose) u v * omegaStd (bas (Pi.single i 1) u) (bas (Pi.single j 1) v) = Out.stdSymp g i j

def IsSharp (W : Matrix (Fin 8) (Fin 8) ℤ) (a : J → Matrix (Fin 8) (Fin 8) ℤ)
    (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))) (t : TObj g k J b s) (c : SiegPre h k (b.ζ : o) s) : Prop :=
  ∃ pr : Fin 8 → (t.A ⟶ c.A), (∀ u, IsMonHom (pr u)) ∧
    (∀ (T : Over S) (y : Fin 8 → (T ⟶ c.A)), ∃! x : T ⟶ t.A, ∀ u, x ≫ pr u = y u) ∧
    LBIso t.L (LB.LinComb c.P (K := Fin 8 × Fin 8) (fun uv => (lift (pr uv.1) (pr uv.2)).left) (fun uv => W uv.1 uv.2)) ∧
    (∀ j u, t.act j ≫ pr u = (List.ofFn fun v => pr v ^ a j u v).prod) ∧
    ∀ i u, (t.pt i ≫ pr u).left = (c.lev (bas (Pi.single i 1) u)).left

def SharpClass (W : Matrix (Fin 8) (Fin 8) ℤ) (a : J → Matrix (Fin 8) (Fin 8) ℤ)
    (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))) (em : o →+* ℂ) (t : TObj g k J b (spMap em)) : Prop :=
  ∃ c : SiegPre h k (b.ζ : o) (spMap em), c.Principal ∧ IsSharp W a bas t c
end Siegel

def ArBase (em : o →+* ℂ) : Prop := IsDedekindDomain o ∧ Algebra.FiniteType ℤ o ∧ Function.Injective em
section Inhabitants

theorem isE8_W8 : IsE8 W8 := by
  unfold IsE8
  rw [w8_add_transpose_eq_e8]
  exact ⟨e8_posDef, e8_det_eq_one⟩

theorem exists_arBase_away {F : Type} [Field F] [NumberField F] (φ : F →+* ℂ) {n : ℕ} (hn : n ≠ 0) :
    ∃ em : Localization.Away (n : 𝓞 F) →+* ℂ, ArBase em ∧
      em.comp (algebraMap (𝓞 F) (Localization.Away (n : 𝓞 F))) = φ.comp (algebraMap (𝓞 F) F) := by

  have hn' : (n : 𝓞 F) ≠ 0 := by exact_mod_cast hn
  have hM : Submonoid.powers (n : 𝓞 F) ≤ nonZeroDivisors (𝓞 F) :=
    powers_le_nonZeroDivisors_of_noZeroDivisors hn'
  have : IsDomain (Localization.Away (n : 𝓞 F)) := IsLocalization.isDomain_of_le_nonZeroDivisors _ hM

  set ψ : 𝓞 F →+* ℂ := φ.comp (algebraMap (𝓞 F) F) with hψ
  have hu : IsUnit (ψ (n : 𝓞 F)) := by
    rw [map_natCast]
    exact isUnit_iff_ne_zero.mpr (by exact_mod_cast hn)
  have hψinj : Function.Injective ψ :=
    φ.injective.comp (FaithfulSMul.algebraMap_injective (𝓞 F) F)
  refine ⟨IsLocalization.Away.lift (n : 𝓞 F) hu, ⟨?_, ?_, ?_⟩, ?_⟩
  · exact IsLocalization.isDedekindDomain (𝓞 F) hM _
  ·
    convert (inferInstance : Algebra.FiniteType ℤ (Localization.Away (n : 𝓞 F))) <;>
      first | rfl | exact Subsingleton.elim _ _
  · unfold IsLocalization.Away.lift
    rw [IsLocalization.lift_injective_iff]
    intro x y
    rw [(IsLocalization.injective (Localization.Away (n : 𝓞 F)) hM).eq_iff, hψinj.eq_iff]
  · exact IsLocalization.lift_comp _
end Inhabitants
end GlobalTheory.ZM
end
