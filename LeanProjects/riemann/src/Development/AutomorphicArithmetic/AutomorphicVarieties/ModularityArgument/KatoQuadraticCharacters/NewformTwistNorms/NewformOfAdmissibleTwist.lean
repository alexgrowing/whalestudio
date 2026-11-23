import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.Imports
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GalUnitary
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.RepNewform
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.RankTwoAutomorphyDescendsFromAbelianCMToRat
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.DenseRangeUnitsR
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.AutBridge
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.AlgOfCyc
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.NewformAut
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.NewformTwistNorms.AutomorphicNewformOfHyp

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2.TwNewform

instance (priority := high + 1) torsionFree (L Ω : Type) [Field L] [Field Ω] [Algebra L Ω] : Module.IsTorsionFree L Ω :=
  DivisionSemiring.to_moduleIsTorsionFree

theorem cont_units {Γ R : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Monoid R]
    [TopologicalSpace R] (f : Γ →* Rˣ) (h : Continuous fun s => (f s : R)) : Continuous f := by
  refine Units.continuous_iff.2 ⟨h, ?_⟩
  simp only [← map_inv]
  exact h.comp continuous_inv

theorem tw_tw {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) (a b : Γ →* kˣ) :
    tw (tw r a) b = tw r (b * a) := by
  ext1 s
  apply Units.ext
  simp only [tw_val, smul_smul, MonoidHom.mul_apply, Units.val_mul]

theorem kills_dvd {Ω : Type} [Field Ω] [Algebra ℚ Ω] {C : Type} [Monoid C] {M N : ℕ} {χ : G ℚ Ω →* C}
    (h : KillsMu M χ) (hMN : M ∣ N) : KillsMu N χ := fun s hs => h s fun ζ hζ => hs ζ (by
  obtain ⟨c, rfl⟩ := hMN
  rw [pow_mul, hζ, one_pow])

theorem kills_mul {Ω : Type} [Field Ω] [Algebra ℚ Ω] {C : Type} [CommMonoid C] {M : ℕ} {χ ψ : G ℚ Ω →* C}
    (h : KillsMu M χ) (h' : KillsMu M ψ) : KillsMu M (χ * ψ) := fun s hs => by
  rw [MonoidHom.mul_apply, h s hs, h' s hs, one_mul]

theorem kills_inv {Ω : Type} [Field Ω] [Algebra ℚ Ω] {C : Type} [CommGroup C] {M : ℕ} {χ : G ℚ Ω →* C}
    (h : KillsMu M χ) : KillsMu M χ⁻¹ := fun s hs => by
  rw [MonoidHom.inv_apply, h s hs, inv_one]

theorem kills_open {Ω C : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] [Group C] {M : ℕ} (hM : 1 ≤ M)
    {φ : G ℚ Ω →* C} (hφ : KillsMu M φ) : IsOpen (φ.ker : Set (G ℚ Ω)) := by
  have hfin : {ζ : Ω | ζ ^ M = 1}.Finite := by
    classical
    refine (Polynomial.nthRoots M (1 : Ω)).toFinset.finite_toSet.subset fun ζ hζ => ?_
    simpa [Polynomial.mem_nthRoots hM] using hζ
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset
    ((hfin.isOpen_biInter fun ζ _ => stabilizer_isOpen_of_isIntegral (K := ℚ) ζ).mem_nhds ?_) fun s hs => ?_)
  · simp only [Set.mem_iInter]
    exact fun ζ _ => Subgroup.one_mem _
  · simp only [Set.mem_iInter] at hs
    exact hφ s fun ζ hζ => hs ζ hζ

theorem cont_kills {Ω C : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] [Group C] [TopologicalSpace C]
    [IsTopologicalGroup C] {M : ℕ} (hM : 1 ≤ M) {φ : G ℚ Ω →* C} (hφ : KillsMu M φ) : Continuous φ := by
  refine continuous_of_continuousAt_one φ ?_
  refine (continuousAt_const (y := (1 : C))).congr ?_
  filter_upwards [(kills_open hM hφ).mem_nhds φ.ker.one_mem] with s hs
  exact hs.symm

theorem kills_pow {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {C : Type} [CommGroup C] {M : ℕ} (hM : 1 ≤ M)
    {χ : G ℚ Ω →* C} (hχ : KillsMu M χ) : ∃ k : ℕ, 0 < k ∧ ∀ s, χ s ^ k = 1 := by
  haveI : NeZero M := ⟨by omega⟩
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  obtain ⟨μ, hμ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω M
  refine ⟨Fintype.card (ZMod M)ˣ, Fintype.card_pos, fun s => ?_⟩
  rw [← map_pow]
  refine hχ _ fun ζ h => ?_
  have h1 := hμ.autToPow_spec ℚ (s ^ Fintype.card (ZMod M)ˣ)
  rw [map_pow, pow_card_eq_one, Units.val_one, ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod _ hμ.pow_eq_one, pow_one] at h1
  obtain ⟨i, -, rfl⟩ := hμ.eq_pow_of_pow_eq_one h
  rw [map_pow, ← h1]

theorem irr_tw {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) (H : Subgroup Γ) (φ : Γ →* kˣ)
    (h : IsIrr (r.comp H.subtype)) : IsIrr (tw r φ) := by
  obtain ⟨hne, -, hmin⟩ := h
  refine ⟨hne, fun _ _ _ => Submodule.mem_top, fun W' _ hW' => hmin W' le_top fun s v hv => ?_⟩
  have e : ((r.comp H.subtype) s : Matrix (Fin n) (Fin n) k).mulVec v =
      ((φ s)⁻¹ : kˣ).val • (tw r φ (s : Γ) : Matrix (Fin n) (Fin n) k).mulVec v := by
    rw [tw_val, Matrix.smul_mulVec, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
    rfl
  rw [e]
  exact W'.smul_mem _ (hW' _ v hv)

end GlobalTheory.Ord2.TwNewform

namespace GlobalTheory.Ord2

open GlobalTheory.Ord2.TwNewform in

theorem newform_twist_of_admissible (P : Af.HypothesesH) (hR : Published.RepNewform) (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [CharZero Ω]
    [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ) (W : R2 Ω l) (he : 1 ≤ e) (hA : admitted ι e W) (M : ℕ)
    (φ : G ℚ Ω →* (Qbar l)ˣ) (hM : 1 ≤ M) (hφ : KillsMu M φ) :
    ∃ g : Newform (2 * e + 1), g.Att ι (tw (tw W φ) (cycBar ℚ Ω l ^ (-(e : ℤ)))) := by
  obtain ⟨f, M', φ', hM', hφ', hf⟩ := hA.modular

  have h1 : IsAutR ι (tw W φ') :=
    newformAutR P.toClassicalTheorems (2 * e + 1) (by omega) f l Ω ι (tw W φ') (-(e : ℤ)) (by rwa [tw_tw])

  set κ : G ℚ Ω →* (Qbar l)ˣ := φ * φ'⁻¹ with hκ
  have hMM : 1 ≤ M * M' := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  have hκM : KillsMu (M * M') κ :=
    kills_mul (kills_dvd hφ (dvd_mul_right M M')) (kills_inv (kills_dvd hφ' (dvd_mul_left M' M)))
  obtain ⟨k, hk, hpow⟩ := kills_pow hMM hκM
  have halg : IsAlgChar ι κ := by
    refine (algOfCyc P ℚ Ω l ι).1 κ (cont_kills hMM hκM) fun w _ => ?_
    obtain ⟨A, hA⟩ : ∃ A : ValuationSubring Ω, IsPlaceOver A w := exists_isPlaceOver Ω w
    exact ⟨A, hA, 0, k, hk, fun s _ => by rw [neg_zero, zpow_zero, mul_one, hpow]⟩
  have h2 : IsAut ι (tw (tw W φ') κ) :=
    twi P ℚ Ω l ι 2 (tw W φ') κ ((autBridge P ℚ Ω l ι 2 (tw W φ')).1.2 h1) halg
  have e1 : tw (tw W φ') κ = tw W φ := by
    rw [tw_tw, hκ, inv_mul_cancel_right]
  rw [e1] at h2
  have h3 : IsAutR ι (tw W φ) := (autBridge P ℚ Ω l ι 2 (tw W φ)).1.1 h2

  have hc : Continuous (tw W φ) := by
    have hφc : Continuous φ := cont_kills hM hφ
    refine cont_units _ ?_
    simp only [tw_val]
    exact (Units.continuous_val.comp hφc).smul (Units.continuous_val.comp hA.cont)
  have hirr : IsIrr (tw W φ) := irr_tw W (H0g W) φ hA.irr

  obtain ⟨A, χ, κ', hAl, hχ, ⟨g, hg⟩, -, hin⟩ := hA.flag
  obtain ⟨v, hAv, hlv⟩ := hAl
  have hval : A.valuation (l : Ω) < 1 := by
    have := (hAv ((l : ℕ) : 𝓞 ℚ)).2 hlv
    simpa using this
  have hχφ : KillsMu (l * M) (χ * φ) :=
    kills_mul (kills_dvd hχ (dvd_mul_right l M)) (kills_dvd hφ (dvd_mul_left M l))
  have hlM : 1 ≤ l * M := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (Fact.out : l.Prime).ne_zero (by omega))
  refine autNewformOfKnownTheorems P hR Ω l ι e he (tw W φ) hc hirr h3 A hval (χ * φ).ker (kills_open hlM hχφ) ⟨g, fun s => ?_⟩
  have hsD : (s : G ℚ Ω) ∈ Dec (F := ℚ) A := Ine_le_Dec A s.2.2
  have hsk : χ s * φ s = 1 := s.2.1
  have hmat : (g * tw W φ (s : G ℚ Ω) * g⁻¹).val = (φ (s : G ℚ Ω) : Qbar l) • (g * W (s : G ℚ Ω) * g⁻¹).val := by
    simp only [Units.val_mul, tw_val, Matrix.mul_smul, Matrix.smul_mul]
  have hlow : ∀ i j : Fin 2, j < i → (g * W (s : G ℚ Ω) * g⁻¹).val i j = 0 := (hg ⟨s, hsD⟩).1
  have hdiag : ∀ i : Fin 2, (g * W (s : G ℚ Ω) * g⁻¹).val i i = (κ' i ⟨s, hsD⟩ : Qbar l) := (hg ⟨s, hsD⟩).2
  obtain ⟨h0, h1'⟩ := hin ⟨s, hsD⟩ s.2.2
  have hsk' : (χ s : Qbar l) * (φ s : Qbar l) = 1 := by rw [← Units.val_mul, hsk, Units.val_one]
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [hmat, Matrix.smul_apply, smul_eq_mul, hlow i j hij, mul_zero]
  · rw [hmat, Matrix.smul_apply, smul_eq_mul, hdiag i]
    fin_cases i
    · show (φ s : Qbar l) * (κ' 0 ⟨s, hsD⟩ : Qbar l) = ((cycBar ℚ Ω l (s : G ℚ Ω) ^ (e : ℤ) : (Qbar l)ˣ) : Qbar l)
      rw [h0, Units.val_mul]
      linear_combination ((cycBar ℚ Ω l (s : G ℚ Ω) ^ (e : ℤ) : (Qbar l)ˣ) : Qbar l) * hsk'
    · show (φ s : Qbar l) * (κ' 1 ⟨s, hsD⟩ : Qbar l) = ((cycBar ℚ Ω l (s : G ℚ Ω) ^ (-(e : ℤ)) : (Qbar l)ˣ) : Qbar l)
      rw [h1', Units.val_mul]
      linear_combination ((cycBar ℚ Ω l (s : G ℚ Ω) ^ (-(e : ℤ)) : (Qbar l)ˣ) : Qbar l) * hsk'

theorem twNewform : Af.HypothesesH → Published.RepNewform → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω]
    [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ) (W : R2 Ω l), l ≠ 2 → 1 ≤ e → admitted ι e W → ∀ (M : ℕ)
    (φ : G ℚ Ω →* (Qbar l)ˣ), 1 ≤ M → KillsMu M φ →
    ∃ g : Newform (2 * e + 1), g.Att ι (tw (tw W φ) (cycBar ℚ Ω l ^ (-(e : ℤ)))) := by
  intro P hR l _ Ω _ inst _ ι e W _ he hA M φ hM hφ
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  obtain rfl : inst = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
  exact newform_twist_of_admissible P hR l Ω ι e W he hA M φ hM hφ

end GlobalTheory.Ord2

end

end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.newform_of_admissible_twist : Af.HypothesesH → Published.RepNewform → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ) (W : R2 Ω l), l ≠ 2 → 1 ≤ e → admitted ι e W → ∀ (M : ℕ) (φ : G ℚ Ω →* (Qbar l)ˣ), 1 ≤ M → KillsMu M φ → ∃ g : Newform (2 * e + 1), g.Att ι (tw (tw W φ) (cycBar ℚ Ω l ^ (-(e : ℤ)))) := by
  first | exact @GlobalTheory.Ord2.twNewform | exact GlobalTheory.Ord2.twNewform | (intros; apply GlobalTheory.Ord2.twNewform <;> assumption)

end
