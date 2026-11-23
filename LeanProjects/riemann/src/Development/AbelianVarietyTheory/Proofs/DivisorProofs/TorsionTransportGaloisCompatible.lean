import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAdeleApproximationModConductorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAdeleClearDenominatorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeMultipleMemSublatticeStatement
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDetGen
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ConjUnifLattice

theorem lattice_of_conj_unif : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal → ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K) (io : K →+* ℂ), Module.finrank ℚ K = 2 → 0 < d → δ ^ 2 = -(d : K) →
    ∀ (g : ℂ ≃+* ℂ) (t : (Af K)ˣ) (Λ₀ Λ₁ : PeriodPair) (Ω₀ Ω₁ : ℂ), Ω₀ ^ 12 = latDisc Λ₀ → TorsTransport io g t Λ₀ Λ₁ Ω₀ Ω₁ →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra K E] (I : Type) [Fintype I] (φ : I → E →+* ℂ),
      IsCMType φ → (∀ i, (φ i).comp (algebraMap K E) = io) → ∀ (c : Ideal (OF E)) (y : (Af E)ˣ), c ≠ ⊥ →
      ∀ (𝔠 : FracId (FR E)) (T : CxPt 𝔠 φ (lattice c y)) (X' : Obj (FR E) 𝔠 (Sp ℂ)) (p : X'.A.left ⟶ T.X.A.left),
        X'.IsPullBy T.X (spMap (g : ℂ →+* ℂ)) p →
        ∀ u' : HolUnif X'.A (X'.diag T.U.c) (Module.finrank ℚ (FR E)),
 (∀ x x' : E, ((upIdele K E t : Af E) * algebraMap E (Af E) x' - algebraMap E (Af E) x) * ((y⁻¹ : (Af E)ˣ) : Af E) ∈ hatO c →
            (u'.ex (fun j ↦ g (φ (T.U.e j) x'))).left ≫ p = spMap (g : ℂ →+* ℂ) ≫ (T.U.u.ex (fun j ↦ φ (T.U.e j) x)).left) → (∀ w, w ∈ u'.Λ ↔ ∃ x ∈ lattice c (y * (upIdele K E t)⁻¹), w = fun j ↦ GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.defCoord (fun i ↦ (g : ℂ →+* ℂ).comp (φ i)) 0 x (T.U.e j)) := by
  intro _ _ _ K _ _ d δ io hK hd hδ g t Λ₀ Λ₁ Ω₀ Ω₁ hΩ hT E _ _ _ _ I _ φ hφ hio c y hc 𝔠 T X' p hp u' H

  have hex0 : ∀ {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {m : ℕ} (u : HolUnif A L m), u.ex 0 = 1 := by
    intro A _ L m u
    have h := u.ex_add 0 0
    rw [add_zero] at h
    simpa using h

  have hpb : ∀ a b : 𝟙_ (Over (Sp ℂ)) ⟶ X'.A, a.left ≫ p = b.left ≫ p → a = b := by
    intro a b h
    exact Over.OverMorphism.ext (hp.grp.1.hom_ext h (by rw [Over.w a, Over.w b]))

  have hepi : ∀ a b : 𝟙_ (Over (Sp ℂ)) ⟶ T.X.A, spMap (g : ℂ →+* ℂ) ≫ a.left = spMap (g : ℂ →+* ℂ) ≫ b.left → a = b := by
    intro a b h
    haveI : IsIso (CommRingCat.ofHom (g : ℂ →+* ℂ)) := (RingEquiv.toCommRingCatIso g).isIso_hom
    haveI : IsIso (spMap (g : ℂ →+* ℂ)) := by unfold spMap; infer_instance
    exact Over.OverMorphism.ext ((cancel_epi _).1 h)
  have H0 : (u'.ex 0).left ≫ p = spMap (g : ℂ →+* ℂ) ≫ (T.U.u.ex 0).left := by
    have := H 0 0 (by simp)
    simp only [map_zero] at this
    exact this

  have hmemL : ∀ x' : E, x' ∈ lattice c (y * (upIdele K E t)⁻¹) ↔
      ((upIdele K E t : Af E) * algebraMap E (Af E) x' - algebraMap E (Af E) 0) * ((y⁻¹ : (Af E)ˣ) : Af E) ∈ hatO c := by
    intro x'
    have e : ((y * (upIdele K E t)⁻¹)⁻¹ : (Af E)ˣ) = upIdele K E t * y⁻¹ := by rw [mul_inv_rev, inv_inv]
    show _ * ((((y * (upIdele K E t)⁻¹)⁻¹ : (Af E)ˣ)) : Af E) ∈ hatO c ↔ _
    rw [e, Units.val_mul, map_zero, sub_zero]
    constructor <;> intro h <;> convert h using 1 <;> ring
  have hdef : ∀ x : E, (fun j ↦ GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.defCoord (fun i ↦ (g : ℂ →+* ℂ).comp (φ i)) 0 x (T.U.e j)) =
      fun j ↦ g (φ (T.U.e j) x) := by
    intro x; funext j; simp [GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.defCoord]
  have hdef0 : ∀ x : E, (fun j ↦ GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.defCoord φ 0 x (T.U.e j)) = fun j ↦ φ (T.U.e j) x := by
    intro x; funext j; simp [GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.defCoord]

  have hsup : ∀ x' ∈ lattice c (y * (upIdele K E t)⁻¹), (fun j ↦ g (φ (T.U.e j) x')) ∈ u'.Λ := by
    intro x' hx'
    have h1 := H 0 x' ((hmemL x').1 hx')
    simp only [map_zero] at h1
    rw [← u'.ker, ← hex0 u']
    refine hpb _ _ ?_
    rw [H0]
    exact h1

  have hsubL : ∀ y₁ : (Af E)ˣ, ∃ S : AddSubgroup E, (S : Set E) = lattice c y₁ := by
    intro y₁
    refine ⟨{ carrier := lattice c y₁, add_mem' := ?_, zero_mem' := ?_, neg_mem' := ?_ }, rfl⟩
    · intro a b ha hb
      show _ ∈ hatO c
      rw [map_add, add_mul]
      exact add_mem ha hb
    · show _ ∈ hatO c
      rw [map_zero, zero_mul]
      exact zero_mem _
    · intro a ha
      show _ ∈ hatO c
      rw [map_neg, neg_mul]
      exact neg_mem ha
  obtain ⟨SL, hSL⟩ := hsubL y
  obtain ⟨SL', hSL'⟩ := hsubL (y * (upIdele K E t)⁻¹)
  have hpos : 0 < Module.finrank ℚ (FR E) := Module.finrank_pos
  let j₀ : Fin (Module.finrank ℚ (FR E)) := ⟨0, hpos⟩
  let Φ : E →ₗ[ℤ] (Fin (Module.finrank ℚ (FR E)) → ℂ) :=
    { toFun := fun x j ↦ φ (T.U.e j) x
      map_add' := by intros; funext j; simp
      map_smul' := by intros; funext j; simp }
  let Φ' : E →ₗ[ℤ] (Fin (Module.finrank ℚ (FR E)) → ℂ) :=
    { toFun := fun x j ↦ g (φ (T.U.e j) x)
      map_add' := by intros; funext j; simp
      map_smul' := by intros; funext j; simp }
  have hΦinj : Function.Injective Φ := fun a b h ↦ (φ (T.U.e j₀)).injective (congrFun h j₀)
  have hΦ'inj : Function.Injective Φ' := fun a b h ↦ (φ (T.U.e j₀)).injective (g.injective (congrFun h j₀))
  have hΛ : T.U.u.Λ = SL.toIntSubmodule.map Φ := by
    ext w
    rw [T.U.lat, Submodule.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨x, ?_, ?_⟩
      · show x ∈ (SL : Set E)
        rw [hSL]; exact hx
      · rw [hdef0]; rfl
    · rintro ⟨x, hx, rfl⟩
      refine ⟨x, ?_, ?_⟩
      · rw [← hSL]; exact hx
      · rw [hdef0]; rfl
  let M : Submodule ℤ (Fin (Module.finrank ℚ (FR E)) → ℂ) := SL'.toIntSubmodule.map Φ'
  have hMle : M ≤ u'.Λ := by
    rintro w ⟨x', hx', rfl⟩
    exact hsup x' (by rw [← hSL']; exact hx')
  obtain ⟨m, hm0, hm⟩ := GlobalTheory.T.finite_adele_clear_denominator E c hc (upIdele K E t : Af E)
  have hrank : Module.rank ℤ T.U.u.Λ ≤ Module.rank ℤ M := by
    rw [hΛ, ← (Submodule.equivMapOfInjective _ hΦinj _).rank_eq,
      ← (Submodule.equivMapOfInjective _ hΦ'inj _).rank_eq]
    let mulm : E →ₗ[ℤ] E := (AddMonoidHom.mulLeft m).toIntLinearMap
    have hmulm : Function.Injective mulm := mul_right_injective₀ hm0
    calc Module.rank ℤ SL.toIntSubmodule = Module.rank ℤ (SL.toIntSubmodule.map mulm) :=
          (Submodule.equivMapOfInjective _ hmulm _).rank_eq
      _ ≤ Module.rank ℤ SL'.toIntSubmodule := by
          refine Submodule.rank_mono ?_
          rintro _ ⟨x, hx, rfl⟩
          have hx' : x ∈ lattice c y := by rw [← hSL]; exact hx
          show m * x ∈ (SL' : Set E)
          rw [hSL']
          have e : ((y * (upIdele K E t)⁻¹)⁻¹ : (Af E)ˣ) = upIdele K E t * y⁻¹ := by rw [mul_inv_rev, inv_inv]
          show _ * ((((y * (upIdele K E t)⁻¹)⁻¹ : (Af E)ˣ)) : Af E) ∈ hatO c
          rw [e, Units.val_mul, map_mul]
          have := mul_mem hm hx'
          convert this using 1
          ring
  intro w
  constructor
  · intro hw
    obtain ⟨k, hk, hkw⟩ := GlobalTheory.T.lattice_multiple_mem_sublattice _ u'.Λ T.U.u.Λ M u'.discrete T.U.u.discrete u'.full T.U.u.full hMle hrank w hw
    obtain ⟨x'', hx'', hx''e⟩ := Submodule.mem_map.1 hkw
    have hk' : (k : E) ≠ 0 := Int.cast_ne_zero.2 hk
    have hw' : w = Φ' (x'' / k) := by
      apply smul_right_injective (Fin (Module.finrank ℚ (FR E)) → ℂ) hk
      show k • w = k • Φ' (x'' / k)
      rw [← map_zsmul, ← hx''e]
      congr 1
      rw [zsmul_eq_mul, mul_div_cancel₀ _ hk']
    set x' := x'' / k
    obtain ⟨x, hx⟩ := GlobalTheory.T.finite_adele_approximation_mod_conductor E c hc y ((upIdele K E t : Af E) * algebraMap E (Af E) x')
    have h1 := H x x' hx
    have hw1 : u'.ex (fun j ↦ g (φ (T.U.e j) x')) = 1 := (u'.ker _).2 (by rw [hw'] at hw; exact hw)
    rw [hw1, ← hex0 u', H0] at h1
    have h2 := hepi _ _ h1
    have h3 : (fun j ↦ φ (T.U.e j) x) ∈ T.U.u.Λ := (T.U.u.ker _).1 (by rw [← h2, hex0])
    rw [T.U.lat] at h3
    obtain ⟨x₀, hx₀, he⟩ := h3
    rw [hdef0] at he
    have hxx : x = x₀ := (φ (T.U.e j₀)).injective (congrFun he j₀)
    subst hxx
    refine ⟨x', ?_, by rw [hdef]; exact hw'⟩
    rw [hmemL, map_zero, sub_zero]
    have := add_mem hx hx₀
    convert this using 1
    ring
  · rintro ⟨x', hx', rfl⟩
    rw [hdef]
    exact hsup x' hx'

end GlobalTheory.ConjUnifLattice
