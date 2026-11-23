import Formalism.WachLatticeTwists.LagrangeExtensionCocycles.ExtensionCocycleProofs.GrothendieckTopDegree
import Formalism.WachLatticeTwists.LagrangeExtensionCocycles.ExtensionCocycleProofs.PhiOnto

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.N2

open Polynomial Formalism.CoboundaryTransfers

section

variable {ℓ : ℕ} [Fact ℓ.Prime] {A : Type} [CommRing A] [Algebra ℤ_[ℓ] A] {B : Base ℤ_[ℓ] A} {M : ℕ}
  {D D' : Type} [AddCommGroup D] [Module A D] [Module ℤ_[ℓ] D] [IsScalarTower ℤ_[ℓ] A D]
  [AddCommGroup D'] [Module A D'] [Module ℤ_[ℓ] D'] [IsScalarTower ℤ_[ℓ] A D']

def gbase (B : Base ℤ_[ℓ] A) (u : ℤ_[ℓ]ˣ) (h : B.GammaX (u : ℤ_[ℓ])) : GBase ℓ A :=
  { γ := B.γ, X := B.X, u := u, γX := h }

def pairOfHom {W : WachMod B M D} {W' : WachMod B M D'} (F : Hom W W') (u : ℤ_[ℓ]ˣ)
    (h : B.GammaX (u : ℤ_[ℓ])) : GPair (gbase B u h) D' :=
  { N := W'.N
    N' := W.N.map F.f
    le := by rintro _ ⟨x, hx, rfl⟩; exact F.N_le x hx
    γ := W'.γ
    γ_smul := W'.γ_smul
    X_inj := W'.X_inj
    γ_N := W'.γ_N
    γ_N' := by
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨x', hx', h⟩ := W.γ_N x hx
      exact ⟨F.f x', ⟨x', hx', rfl⟩, by rw [← F.γ_comm, ← map_sub, h, map_smul]; rfl⟩ }

theorem kills_iff {W : WachMod B M D} {W' : WachMod B M D'} (F : Hom W W') (u : ℤ_[ℓ]ˣ)
    (h : B.GammaX (u : ℤ_[ℓ])) (a : A) :
    (pairOfHom F u h).Kills a ↔ ∀ n ∈ W'.N, ∃ n₁ ∈ W.N, F.f n₁ = a • n := by
  constructor
  · intro hk n hn
    obtain ⟨x, hx, hfx⟩ := Submodule.mem_map.1 (hk n hn)
    exact ⟨x, hx, hfx⟩
  · intro h' n hn
    obtain ⟨x, hx, hfx⟩ := h' n hn
    exact Submodule.mem_map.2 ⟨x, hx, hfx⟩

theorem natCast_pow_smul (e : ℕ) (n : D) : ((ℓ : A) ^ e) • n = ((ℓ : ℤ_[ℓ]) ^ e) • n := by
  rw [← map_natCast (algebraMap ℤ_[ℓ] A), ← map_pow, algebraMap_smul]

theorem homKillsB {W : WachMod B M D} {W' : WachMod B M D'} (F : Hom W W') (u : ℤ_[ℓ]ˣ)
    (h : B.GammaX (u : ℤ_[ℓ])) (s a : ℕ) (hs : 1 ≤ s) (h2 : ℓ = 2 → 2 ≤ s)
    (hv : PadicInt.valuation ((u : ℤ_[ℓ]) - 1) = s) (hK : XKills F a) :
    ∀ n ∈ W'.N, ∃ n₁ ∈ W.N, F.f n₁ = ((ℓ : ℤ_[ℓ]) ^ eWB ℓ a s) • n := by
  have := unit_lemma_case_b_holds ℓ A (gbase B u h) D' (pairOfHom F u h) s a hs h2 hv ((kills_iff F u h _).2 hK)
  intro n hn
  obtain ⟨n₁, hn₁, e⟩ := (kills_iff F u h _).1 this n hn
  exact ⟨n₁, hn₁, by rw [e, natCast_pow_smul]⟩

theorem aeval_mem (N : Submodule ℤ_[ℓ] D) (γ : D →ₗ[ℤ_[ℓ]] D) (h : ∀ n ∈ N, γ n ∈ N)
    (R : ℤ_[ℓ][X]) : ∀ n ∈ N, aeval γ R n ∈ N := by
  induction R using Polynomial.induction_on with
  | C a =>
    intro n hn
    rw [aeval_C, Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, Module.End.one_apply]
    exact N.smul_mem a hn
  | add p q hp hq =>
    intro n hn
    rw [map_add, LinearMap.add_apply]
    exact N.add_mem (hp n hn) (hq n hn)
  | monomial k a ih =>
    intro n hn
    rw [pow_succ, ← mul_assoc, map_mul, aeval_X, Module.End.mul_apply]
    exact ih _ (h n hn)

theorem zero_notMem_JSet (jumps : Finset ℤ) (M : ℕ) : (0 : ℤ) ∉ JSet jumps M := by
  simp [JSet]

theorem eigSet_subset (jumps : Finset ℤ) (M : ℕ) : eigSet jumps M ⊆ insert 0 (JSet jumps M) := by
  intro x hx
  by_cases h0 : x = 0
  · exact Finset.mem_insert.2 (Or.inl h0)
  · exact Finset.mem_insert.2 (Or.inr (Finset.mem_union.2 (Or.inl (Finset.mem_erase.2 ⟨h0, hx⟩))))

theorem prod_eig_dvd (jumps : Finset ℤ) (M : ℕ) (f : ℤ → ℤ_[ℓ][X]) :
    (∏ j ∈ eigSet jumps M, f j) ∣ f 0 * ∏ j ∈ JSet jumps M, f j := by
  have h := Finset.prod_dvd_prod_of_subset _ _ f (eigSet_subset jumps M)
  rwa [Finset.prod_insert (zero_notMem_JSet jumps M)] at h

end

theorem lift_exists_second_case : StatLiftB := by
  intro ℓ _ A _ _ B M u s H jumps hp hφX hγX hγQ hs h2 hv D₀ D₁ D₂ _ _ _ _ _ _ _ _ _ _ _ _ W₀ W₁ W₂ S
    H₁ H₂ _ _ _ _ cl₁ cl₂ Hf₁ Hf₂ g I _ hQI hφI hRX hRL hNT hXK hSemi hNat hC1 hC2 hInj hE1 hE2 hRO
  set eW := eWB ℓ H s with heW

  have hCK : CokerKilled S eW := by
    intro n hn
    rw [hp]
    exact homKillsB S.π u hγX s H hs h2 hv hXK n hn

  have hInt₁ : ∀ κ ∈ Hf₁, ∃ pr : W₁.Z1, W₁.Cocycle (pr : D₁ × D₁).1 (pr : D₁ × D₁).2 ∧
      cl₁ pr = ((ℓ : ℤ_[ℓ]) ^ eW) • κ := by
    intro κ hκ
    obtain ⟨E, hEK, hED⟩ := hE1 κ hκ
    exact extension_class_is_cocycle ℓ A B M D₁ W₁ H₁ cl₁ κ E eW hED (homKillsB E.S.π u hγX s H hs h2 hv hEK)
  have hInt₂ : ∀ κ ∈ Hf₂, ∃ pr : W₂.Z1, W₂.Cocycle (pr : D₂ × D₂).1 (pr : D₂ × D₂).2 ∧
      cl₂ pr = ((ℓ : ℤ_[ℓ]) ^ eW) • κ := by
    intro κ hκ
    obtain ⟨E, hEK, hED⟩ := hE2 κ hκ
    exact extension_class_is_cocycle ℓ A B M D₂ W₂ H₂ cl₂ κ E eW hED (homKillsB E.S.π u hγX s H hs h2 hv hEK)

  have hRS : RatSurj S :=
    rational_points_map_surjective ℓ A B M D₀ D₁ D₂ W₀ W₁ W₂ S H₁ H₂ cl₁ cl₂ Hf₁ Hf₂ g eW hp hNat hC2 hInj hRO hInt₁

  have h1 := phi_map_surjective ℤ_[ℓ] A B M D₀ W₀ I 1 (M + 1) ⟨1, by rw [hφX]; ring⟩ (by omega) hQI hφI

  have hstab : ∀ n ∈ W₀.N.restrictScalars ℤ_[ℓ], W₀.γ n ∈ W₀.N.restrictScalars ℤ_[ℓ] := by
    intro n hn
    obtain ⟨x', hx', h⟩ := W₀.γ_N n hn
    have : W₀.γ n = n + B.X • x' := by rw [← h]; abel
    rw [this]
    exact W₀.N.add_mem hn (W₀.N.smul_mem _ hx')
  have h3 : ∀ y, W₀.QInv y → aeval W₀.γ ((X - 1) *
      ∏ j ∈ JSet jumps M, (X - C (((u ^ (-j) : ℤ_[ℓ]ˣ) : ℤ_[ℓ])))) y ∈ W₀.N := by
    intro y hy
    obtain ⟨R, hR⟩ := prod_eig_dvd jumps M (fun j => (X - C (((u ^ (-j) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]))))
    have e0 : (X - C (((u ^ (-(0 : ℤ)) : ℤ_[ℓ]ˣ) : ℤ_[ℓ])) : ℤ_[ℓ][X]) = X - 1 := by simp
    simp only [e0] at hR
    rw [hR, mul_comm, map_mul, Module.End.mul_apply]
    exact aeval_mem _ W₀.γ hstab R _ (hSemi y hy)
  have hL : Lifts S ((ℓ : ℤ_[ℓ]) ^ (eW + Formalism.LIFT.eU ℓ M s (JSet jumps M))) :=
    wachLatticeUnramified_statement ℓ A B M u hp hφX hγX hγQ D₀ D₁ D₂ W₀ W₁ W₂ S eW s (JSet jumps M) hs h2 hv
      (zero_notMem_JSet jumps M) h1 (regulator_bound_for_x ℓ A B M D₀ W₀ hRX) h3
      (regulator_bound_for_l ℓ A B M D₀ W₀ hRL hNT) hCK hRS
  intro κ hκ
  obtain ⟨κ₁, hκ₁, h⟩ := finiteClassesLift_holds ℤ_[ℓ] A B M D₀ D₁ D₂ W₀ W₁ W₂ S H₁ H₂ cl₁ cl₂ Hf₁ Hf₂ g eW _
    hNat hC1 ⟨hC2, by rw [hp]; exact hInt₂⟩ hL κ hκ
  refine ⟨κ₁, hκ₁, ?_⟩
  rw [h, hp, ← pow_add]
  congr 2
  simp only [eUB, Formalism.LIFT.eU]
  ring

end Formalism.RepresentationBoundsCohomology.N2
