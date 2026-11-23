import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.IsFixMapIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.SplitUnitElements.SplitS
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.SplitUnitElements.IntE
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.CintIdx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.H90
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.NormEx

open QuadraticAlgebra Matrix UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

theorem UpperTheory.V.Z.Sym.Loc.One.snd :
    ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ →
        (∃ u : Oˣ, algebraMap O K u = τ ^ 2 - 4) → ∀ (c : K) (d m : EL Δ τ), IsDat c d m → ∀ (s : K) (ε : Oˣ), Δ * s ^ 2 = algebraMap O K ε →
        ∃ y₀ : (EL Δ τ)ˣ, ∀ S : Set (Sp Δ τ), IsFix O c d m S → ∀ x : EL Δ τ, ((0, x) : Sp Δ τ) ∈ S ↔
          ∃ a b : Etau K τ, x = (y₀ : EL Δ τ) * (ofE Δ a + (⟨0, s⟩ : Lsq K Δ) • ofE Δ b) ∧
            ((0, (y₀ : EL Δ τ) * ofE Δ a) : Sp Δ τ) ∈ S ∧ ((0, (y₀ : EL Δ τ) * ofE Δ b) : Sp Δ τ) ∈ S := by
  intro O K _ _ _ _ _ Δ τ L hD c d m h s ε hε
  obtain ⟨hτ, hu, ⟨n, hn⟩, -⟩ := One.intE O K Δ τ L hD
  have h2 := two_ne_zero_of_isLoc L
  have hε0 : algebraMap O K ε ≠ 0 := (ε.isUnit.map _).ne_zero
  have hn0 : 2 + τ ≠ 0 := hn ▸ (n.isUnit.map _).ne_zero
  have hs0 : s ≠ 0 := fun h => hε0 (by rw [← hε, h]; ring)
  have alg : ∀ x : O, algebraMap O (Lsq K Δ) x = algebraMap K _ (algebraMap O K x) := fun x => IsScalarTower.algebraMap_apply O K _ x
  have hww : (⟨0, s⟩ : Lsq K Δ) * ⟨0, s⟩ = algebraMap K _ (algebraMap O K ε) := by
    ext <;> simp
    rw [← hε]; ring
  have hw : IsInt O (⟨0, s⟩ : Lsq K Δ) := by
    refine IsIntegral.of_pow (n := 2) (by norm_num) ?_
    rw [sq, hww, ← alg]; exact isIntegral_algebraMap
  obtain ⟨i, hi⟩ := L.two.exists_right_inv
  have hi' : algebraMap K (Lsq K Δ) (algebraMap O K i) * 2 = 1 := by
    rw [← alg, ← map_ofNat (algebraMap O (Lsq K Δ)) 2, ← map_mul, mul_comm, hi, map_one]
  have hε' : algebraMap K (Lsq K Δ) (algebraMap O K (ε⁻¹ : Oˣ)) * algebraMap K _ (algebraMap O K ε) = 1 := by
    rw [← map_mul, ← map_mul, Units.inv_mul, map_one, map_one]
  have hn' : algebraMap K (Lsq K Δ) (algebraMap O K (n⁻¹ : Oˣ)) * algebraMap K _ (2 + τ) = 1 := by
    rw [← hn, ← map_mul, ← map_mul, Units.inv_mul, map_one, map_one]
  obtain ⟨lam, hl, hln⟩ := normEx O K Δ L n
  have hll : lam * star lam = algebraMap K _ (2 + τ) := by rw [← hn, ← hln, QuadraticAlgebra.algebraMap_norm_eq_mul_star]
  set r : Lsq K Δ := algebraMap O _ ((n⁻¹ : Oˣ) : O) * lam with hr
  have hri : IsInt O r := isIntegral_algebraMap.mul hl
  have hrr : r * star r * algebraMap K _ (2 + τ) = 1 := by
    have : star (algebraMap K (Lsq K Δ) (algebraMap O K (n⁻¹ : Oˣ))) = algebraMap K _ (algebraMap O K (n⁻¹ : Oˣ)) := by ext <;> simp
    rw [hr, star_mul', alg, this]
    linear_combination (algebraMap K (Lsq K Δ) (algebraMap O K (n⁻¹ : Oˣ)) ^ 2 * algebraMap K (Lsq K Δ) (2 + τ)) * hll +
      (algebraMap K (Lsq K Δ) (algebraMap O K (n⁻¹ : Oˣ)) * algebraMap K (Lsq K Δ) (2 + τ) + 1) * hn'
  have sg : ∀ (a : Lsq K Δ) (x : EL Δ τ), sigL (a • x) = star a • sigL x := fun a x => by ext <;> simp [sigL] <;> ring
  set d' : EL Δ τ := r • (ofE Δ ⟨1 + τ, -1⟩ * d) with hd'
  have hdd : sigL d' * sigL (sigL d') = 1 := by
    have e : ofE Δ (⟨1 + τ, -1⟩ : Etau K τ) * ofE Δ ⟨1 + τ, -1⟩ * ofE Δ ω = algebraMap K (Lsq K Δ) (2 + τ) • (1 : EL Δ τ) := by
      ext <;> simp [ofE, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one] <;> ring
    rw [sigL_sigL, hd', sg, sigL_mul, sigL_ofE, smul_mul_smul_comm,
      show ofE Δ (⟨1 + τ, -1⟩ : Etau K τ) * sigL d * (ofE Δ ⟨1 + τ, -1⟩ * d) = ofE Δ ⟨1 + τ, -1⟩ * ofE Δ ⟨1 + τ, -1⟩ * (d * sigL d) by ring,
      h.d_norm, e, smul_smul, mul_comm (star r), hrr, one_smul]
  obtain ⟨y, hy⟩ := h90 O K Δ τ L h.reg _ hdd
  have hy' : d' * sigL (y : EL Δ τ) = y := by
    have := congrArg sigL hy
    rwa [sigL_mul, sigL_sigL, sigL_sigL, eq_comm] at this
  refine ⟨y, fun S hS x => ?_⟩
  obtain ⟨A, M, -, E⟩ := One.splitS O K Δ τ L hτ hu c d m h S hS
  have add : ∀ a b : EL Δ τ, ((0, a) : Sp Δ τ) ∈ S → ((0, b) : Sp Δ τ) ∈ S → ((0, a + b) : Sp Δ τ) ∈ S := fun a b ha hb => by
    simpa using A _ ha _ hb
  have mul : ∀ (t : Lsq K Δ) (a : EL Δ τ), IsInt O t → ((0, a) : Sp Δ τ) ∈ S → ((0, t • a) : Sp Δ τ) ∈ S := fun t a ht ha => by
    simpa using M _ ha t ht
  constructor
  · intro hx
    have h1 : ((0, d' * sigL x) : Sp Δ τ) ∈ S := by
      have a1 : semi d (0, x) ∈ S := hS.stab ▸ Set.mem_image_of_mem _ hx
      obtain ⟨τ₀, e₀⟩ := hτ
      have := mul r _ hri (E _ a1 ⟨1 + τ, -1⟩ ⟨1 + τ₀, by simp [e₀]⟩ ⟨-1, by simp⟩)
      rwa [hd', smul_mul_assoc, mul_assoc]
    obtain ⟨X, rfl⟩ : ∃ X, x = (y : EL Δ τ) * X := ⟨(y⁻¹ : (EL Δ τ)ˣ) * x, by simp⟩
    obtain ⟨a, b, rfl⟩ : ∃ a b : Etau K τ, X = ofE Δ a + (⟨0, s⟩ : Lsq K Δ) • ofE Δ b :=
      ⟨⟨X.re.re, X.im.re⟩, ⟨X.re.im / s, X.im.im / s⟩, by ext <;> simp [ofE] <;> field_simp⟩
    have e : sigL (ofE Δ a + (⟨0, s⟩ : Lsq K Δ) • ofE Δ b) = ofE Δ a - (⟨0, s⟩ : Lsq K Δ) • ofE Δ b := by
      ext <;> simp [sigL, ofE]
    rw [sigL_mul, ← mul_assoc, hy', e] at h1
    refine ⟨a, b, rfl, ?_, ?_⟩
    · convert mul _ _ (isIntegral_algebraMap (x := i)) (add _ _ hx h1) using 2
      rw [show (y : EL Δ τ) * (ofE Δ a + (⟨0, s⟩ : Lsq K Δ) • ofE Δ b) + (y : EL Δ τ) * (ofE Δ a - (⟨0, s⟩ : Lsq K Δ) • ofE Δ b) =
        (2 : Lsq K Δ) • ((y : EL Δ τ) * ofE Δ a) by rw [two_smul]; ring, smul_smul, alg, hi', one_smul]
    · convert mul _ _ (((isIntegral_algebraMap (x := i)).mul (isIntegral_algebraMap (x := ((ε⁻¹ : Oˣ) : O)))).mul hw)
        (add _ _ hx (mul _ _ isIntegral_one.neg h1)) using 2
      rw [show (y : EL Δ τ) * (ofE Δ a + (⟨0, s⟩ : Lsq K Δ) • ofE Δ b) + (-1 : Lsq K Δ) • ((y : EL Δ τ) * (ofE Δ a - (⟨0, s⟩ : Lsq K Δ) • ofE Δ b)) =
        ((2 : Lsq K Δ) * ⟨0, s⟩) • ((y : EL Δ τ) * ofE Δ b) by rw [mul_smul, two_smul, neg_one_smul, ← mul_smul_comm]; ring, smul_smul, alg, alg]
      rw [show algebraMap K (Lsq K Δ) (algebraMap O K i) * algebraMap K (Lsq K Δ) (algebraMap O K (ε⁻¹ : Oˣ)) * ⟨0, s⟩ * (2 * ⟨0, s⟩) = 1 by
        linear_combination (2 * algebraMap K (Lsq K Δ) (algebraMap O K i) * algebraMap K (Lsq K Δ) (algebraMap O K (ε⁻¹ : Oˣ))) * hww +
          (2 * algebraMap K (Lsq K Δ) (algebraMap O K i)) * hε' + hi', one_smul]
  · rintro ⟨a, b, rfl, ha, hb⟩
    rw [mul_add, mul_smul_comm]
    exact add _ _ ha (mul _ _ hw hb)
