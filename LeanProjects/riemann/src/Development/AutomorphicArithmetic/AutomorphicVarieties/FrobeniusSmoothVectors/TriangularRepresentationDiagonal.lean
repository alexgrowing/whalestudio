import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Integral
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.AdicCharUnipotentPgroupQuotient
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Imports
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsFurtherTer
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LocallyConstantOfKernel

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem lc_of_ker {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group H]
    (φ : G →* H) (h : IsOpen (φ.ker : Set G)) : IsLocallyConstant φ :=
  _root_.UpperTheory.Reformulated.B.LocallyConstantOfKernel.lc_of_ker φ h

private theorem diag_mul {n : ℕ} {Q : Type} [CommRing Q] (a b : Matrix (Fin n) (Fin n) Q)
    (ha : ∀ i j, i < j → a i j = 0) (hb : ∀ i j, i < j → b i j = 0) (i : Fin n) :
    (a * b) i i = a i i * b i i :=
  _root_.UpperTheory.Reformulated.B.Qk64.diag_mul a b ha hb i

private theorem key {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ n : ℕ}
    (hF : F.Ok C₀) {Q : Type} [CommRing Q] [IsDomain Q] [IsLocalRing Q] [IsNoetherianRing Q]
    [Finite (ResidueField Q)] (f : k →+* Q) (ρ : NRep F n Q) (hc : ρ.Cont (maximalIdeal Q))
    (hb : (ρ.map (residue Q)).IsBar ((residue Q).comp f)) (ht : ρ.triM = ⊥) (h : ℕ) (h0 : h ≠ 0) (i : Fin n)
    (H : ∀ (A : Type) [CommGroup A] [Finite A], IsPGroup l A → ∀ ψ : F.G0 →* A, IsOpen (ψ.ker : Set F.G0) →
      (∀ g g', ρ.r g i i = ρ.r g' i i → F.Ψ g ^ w n i = F.Ψ g' ^ w n i → ψ g = ψ g') → ∀ g, ψ g ^ h = 1)
    (g : F.G0) : ρ.r g i i = f ((F.Ψ g ^ w n i : kˣ) : k) := by
  haveI : CharP Q l := charP_of_injective_ringHom f.injective l
  have hz : ∀ g i j, i < j → ρ.r g i j = 0 := fun g i j hij => by
    have : ρ.r g i j ∈ ρ.triM := Ideal.subset_span ⟨g, i, j, hij, rfl⟩
    rwa [ht, Ideal.mem_bot] at this
  let χ : F.G0 →* Q :=
    { toFun := fun g => ρ.r g i i * f (((F.Ψ g ^ w n i)⁻¹ : kˣ) : k)
      map_one' := by simp
      map_mul' := fun a b => by
        rw [map_mul, diag_mul _ _ (hz a) (hz b), Subgroup.coe_mul, map_mul, mul_zpow, mul_inv, Units.val_mul,
          map_mul]
        ring }
  have hχ : ∀ g, χ g = ρ.r g i i * f (((F.Ψ g ^ w n i)⁻¹ : kˣ) : k) := fun _ => rfl
  have hinv : ∀ g : F.G0, f (((F.Ψ g ^ w n i)⁻¹ : kˣ) : k) * f ((F.Ψ g ^ w n i : kˣ) : k) = 1 := fun g => by
    rw [← map_mul, Units.inv_mul, map_one]
  have hΨ : IsLocallyConstant fun g : F.G0 => F.Ψ g :=
    (lc_of_ker F.Ψ hF.Ψ_open).comp_continuous continuous_subtype_val
  have h1 : χ g = 1 := by
    refine adic_char_unipotent_pgroup_quotient (l := l) χ h h0 (fun N => ?_) (fun g => ?_) (fun A _ _ hA ψ hψ hh => H A hA ψ hψ ?_) g
    · have := (hc.1 i i N).mul (hΨ.comp fun u : kˣ =>
        Ideal.Quotient.mk (maximalIdeal Q ^ N) (f (((u ^ w n i)⁻¹ : kˣ) : k)))
      convert this using 1
      funext g
      simp only [hχ, map_mul, Pi.mul_apply, Function.comp]
    · rw [← residue_eq_zero_iff, map_sub, map_one, sub_eq_zero, hχ, map_mul]
      have h2 : residue Q (ρ.r g i i) = residue Q (f ((F.Ψ g ^ w n i : kˣ) : k)) := hb.1 g i
      rw [h2, ← map_mul, mul_comm, hinv, map_one]
    · intro g g' e1 e2
      exact hh g g' (by rw [hχ, hχ, e1, e2])
  rw [hχ] at h1
  calc ρ.r g i i = ρ.r g i i * (f (((F.Ψ g ^ w n i)⁻¹ : kˣ) : k) * f ((F.Ψ g ^ w n i : kˣ) : k)) := by
        rw [hinv, mul_one]
    _ = _ := by rw [← mul_assoc, h1, one_mul]

theorem UpperTheory.V.Fr.triangular_representation_diagonal :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ {Q : Type} [CommRing Q] [IsDomain Q] [IsLocalRing Q] [IsNoetherianRing Q] [Finite (ResidueField Q)] (f : k →+* Q) (ρ : NRep F n Q), ρ.Cont (maximalIdeal Q) → (ρ.map (residue Q)).IsBar ((residue Q).comp f) → ρ.triM = ⊥ → ∀ {ι ι' : Type} (s : ι → F.G0) (s' : ι' → F.G0) (h : ℕ), h ≠ 0 → (∀ a, F.Ψ (s a) = 1) → (∀ (A : Type) [CommGroup A] [Finite A], IsPGroup l A → ∀ χ : F.G0 →* A, IsOpen (χ.ker : Set F.G0) → ((∀ a, χ (s a) = 1) → ∀ g, χ g ^ h = 1) ∧ ((∀ g, χ (F.star g) = χ g) → (∀ a, χ (s' a) = 1) → ∀ g, χ g ^ h = 1)) → (∀ a (i : Fin n), (i : ℕ) = 0 → ρ.r (s a) i i = 1) → (∀ a (i : Fin n), w n i = 0 → ρ.r (s' a) i i = 1) → ∀ (g : F.G0) (i : Fin n), ρ.r g i i = f ((F.Ψ g ^ w n i : kˣ) : k) := by
  intro l _ k _ _ F C₀ n hF hn Q _ _ _ _ _ f ρ hc hb ht ι ι' s s' h h0 hs H h1 h2
  obtain ⟨-, -, sΨ, -, sr⟩ := UpperTheory.V.Fr.star hF
  have A0 : ∀ (i : Fin n), (i : ℕ) = 0 → ∀ g, ρ.r g i i = f ((F.Ψ g ^ w n i : kˣ) : k) := fun i hi =>
    key hF f ρ hc hb ht h h0 i fun A _ _ hA ψ hψ hh => (H A hA ψ hψ).1 fun a => by
      rw [← map_one ψ]
      refine hh _ _ ?_ ?_
      · rw [h1 a i hi]; simp
      · rw [hs a]; simp
  have A1 : ∀ (i : Fin n), w n i = 0 → i.rev = i → ∀ g, ρ.r g i i = f ((F.Ψ g ^ w n i : kˣ) : k) :=
    fun i hi hr => key hF f ρ hc hb ht h h0 i fun A _ _ hA ψ hψ hh => (H A hA ψ hψ).2
      (fun g => hh _ _ (by rw [sr, hr]) (by simp [hi])) fun a => by
      rw [← map_one ψ]
      refine hh _ _ ?_ ?_
      · rw [h2 a i hi]; simp
      · simp [hi]
  have A2 : ∀ (i : Fin n), (i : ℕ) = 0 → w n i.rev = - w n i →
      ∀ g, ρ.r g i.rev i.rev = f ((F.Ψ g ^ w n i.rev : kˣ) : k) := fun i hi hw g => by
    rw [← sr, A0 i hi, sΨ, hw, _root_.zpow_neg, _root_.inv_zpow]
  intro g i
  rcases hn with rfl | rfl
  · fin_cases i
    · exact A0 0 rfl g
    · exact A2 0 rfl (by decide) g
  · fin_cases i
    · exact A0 0 rfl g
    · exact A1 1 (by decide) (by decide) g
    · exact A2 0 rfl (by decide) g
