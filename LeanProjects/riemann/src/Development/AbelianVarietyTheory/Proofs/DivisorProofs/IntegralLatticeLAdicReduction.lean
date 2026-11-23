import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ConjugateOrderData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPlaceRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SzPeriodsOfTangent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyOfForall
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLinearOfIsMonHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeMapGivesHomomorphism
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveOfSurjectiveOnPoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyFiniteFlat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicLatticeOrderCoprimeIndex

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CMPowerIsogeny

theorem exists_mem_condQ {E : Type} [Field E] [NumberField E] {𝔣 : Ideal (OF E)} (h𝔣 : IsBaseCond 𝔣) {l : ℕ} (hl : l.Prime)
    (Q : Finset (HeightOneSpectrum (OF E))) (hQ : ∀ q ∈ Q, (l : OF E) ∉ q.asIdeal) :
    condQ 𝔣 Q ≠ ⊥ ∧ ∃ m : ℕ, ¬ l ∣ m ∧ ((l ^ a0 𝔣 l * m : ℕ) : OF E) ∈ condQ 𝔣 Q := by
  have hc : condQ 𝔣 Q ≠ ⊥ := mul_ne_zero h𝔣.1 (Finset.prod_ne_zero_iff.2 fun q _ => q.ne_bot)
  refine ⟨hc, ?_⟩
  have hN : Ideal.absNorm (condQ 𝔣 Q) ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
  obtain ⟨k, m, hlm, hkm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN l hl.one_lt.ne'
  refine ⟨m, hlm, ?_⟩
  set x : OF E := ((l ^ a0 𝔣 l * m : ℕ) : OF E) with hx
  let J : Ideal (OF E) := Submodule.comap (LinearMap.mulRight (OF E) x) (condQ 𝔣 Q)
  have hJ : ∀ r, r ∈ J ↔ r * x ∈ condQ 𝔣 Q := fun r => Iff.rfl
  by_contra hne
  have hJt : J ≠ ⊤ := fun h => hne (by simpa using (hJ 1).1 (h ▸ Submodule.mem_top))
  obtain ⟨P, hP, hJP⟩ := Ideal.exists_le_maximal J hJt
  have hlk : ((l : OF E)) ^ k ∈ J := by
    rw [hJ, hx]
    have h1 := Ideal.absNorm_mem (condQ 𝔣 Q)
    rw [hkm] at h1
    have h2 := Ideal.mul_mem_left _ ((l : OF E) ^ a0 𝔣 l) h1
    convert h2 using 1
    push_cast; ring
  have hlP : (l : OF E) ∈ P := hP.isPrime.mem_of_pow_mem k (hJP hlk)
  have hP0 : P ≠ ⊥ := by
    rintro rfl
    exact hl.ne_zero (by exact_mod_cast (Ideal.mem_bot.1 hlP))
  let v : HeightOneSpectrum (OF E) := ⟨P, hP.isPrime, hP0⟩
  obtain ⟨J', hJ', hnd⟩ := (FiniteMultiplicity.of_prime_left v.prime h𝔣.1).exists_eq_pow_mul_and_not_dvd
  have hle : expIn 𝔣 v ≤ a0 𝔣 l := by
    refine le_csSup ⟨2, ?_⟩ ⟨v, hlP, rfl⟩
    rintro _ ⟨w, -, rfl⟩
    by_cases hw : w.asIdeal ∣ 𝔣
    · exact (h𝔣.2.2 w hw).2.1
    · rw [expIn, multiplicity_eq_zero.2 hw]; omega
  have hnd' : ¬ (J' * ∏ q ∈ Q, q.asIdeal) ≤ P := by
    intro h
    rcases hP.isPrime.mul_le.1 h with h | h
    · exact hnd (Ideal.dvd_iff_le.2 h)
    · obtain ⟨q, hq, hqP⟩ := (Ideal.IsPrime.prod_le hP.isPrime).1 h
      exact hQ q hq (by rw [q.isMaximal.eq_of_le hP.ne_top hqP]; exact hlP)
  refine hnd' fun r hr => hJP ?_
  rw [hJ, hx, condQ]
  have h1 : (l : OF E) ^ a0 𝔣 l ∈ v.asIdeal ^ multiplicity v.asIdeal 𝔣 :=
    Ideal.pow_le_pow_right hle (Ideal.pow_mem_pow hlP _)
  have h2 := Ideal.mul_mem_right (m : OF E) _ (Ideal.mul_mem_mul h1 hr)
  rw [← _root_.mul_assoc, ← hJ'] at h2
  convert h2 using 1
  push_cast; ring

theorem sz_inv_pow_mul (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (a m : ℕ) (hm : ¬ l ∣ m) :
    Sz l lam a (((l ^ a * m : ℕ) : ℂ)⁻¹) := by
  refine ⟨inv_mem (natCast_mem _ _), ?_⟩
  have e : (⟨((l ^ a * m : ℕ) : ℂ)⁻¹, inv_mem (natCast_mem _ _)⟩ : algebraicClosure ℚ ℂ) =
      ((l ^ a * m : ℕ) : algebraicClosure ℚ ℂ)⁻¹ := Subtype.ext (by simp)
  have hn : ∀ n : ℕ, ‖(n : ℂ_[l])‖ = ‖(n : ℚ_[l])‖ := fun n => by
    rw [← norm_algebraMap' ℂ_[l] (n : ℚ_[l]), map_natCast]
  have h1 : ‖(m : ℚ_[l])‖ = 1 :=
    Padic.norm_natCast_eq_one_iff.2 ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hm)
  rw [e, map_inv₀, map_natCast, norm_inv, hn, Nat.cast_mul, norm_mul, h1, Nat.cast_pow, norm_pow, Padic.norm_p]
  simp

theorem exists_separating (E : Type) [Field E] [NumberField E] :
    ∃ θ : 𝓞 E, ∀ σ τ : E →+* ℂ, σ θ = τ θ → σ = τ := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element ℚ E
  obtain ⟨m, hm, hint⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic α)).exists_integral_multiple
  refine ⟨⟨m • α, hint⟩, fun σ τ h => ?_⟩
  have h1 : σ α = τ α := by
    have h2 : σ (m • α) = τ (m • α) := h
    rw [map_zsmul, map_zsmul] at h2
    exact smul_right_injective ℂ hm h2
  have h3 : σ.toRatAlgHom = τ.toRatAlgHom := by
    have := (Field.primitive_element_iff_algHom_eq_of_eval' ℚ ℂ (fun x => IsAlgClosed.splits _) α).1 hα
    exact this h1
  exact RingHom.ext fun x => DFunLike.congr_fun h3 x

theorem exists_kill (A B : CategoryTheory.Over (Sp ℂ)) [GrpObj A] [GrpObj B] (hA : IsAbelianScheme A) (hB : IsAbelianScheme B)
    (ψ : A ⟶ B) [IsMonHom ψ] [IsFinite ψ.left] :
    ∃ n : ℕ, 1 ≤ n ∧ ∀ (T : CategoryTheory.Over (Sp ℂ)) (x : T ⟶ A), x ≫ ψ = 1 → x ^ n = 1 := by
  have := hB.proper
  have := hA.proper
  have := hA.comm
  obtain ⟨Z, _, i, _, hi, hZ, hk⟩ := GlobalTheory.IsogenyModel.exists_kernel ψ
  have hm : Mono i := (Over.forget _).mono_of_mono_map (inferInstanceAs (Mono i.left))
  have := isCommMonObj_of_mono i
  obtain ⟨N, hN, hZN⟩ := FiniteFlatKilled.main ℂ Z hZ inferInstance
  refine ⟨N, hN, fun T x hx => ?_⟩
  have h1 : i ^ N = 1 := by
    rw [← Category.id_comp i, ← MonObj.pow_comp, hZN, MonObj.one_comp]
  rw [← hk.lift_fst x (toUnit _) hx, ← MonObj.comp_pow, h1, MonObj.comp_one]

theorem exists_isogeny : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (I : Type) [Fintype I] (d : ℕ)
    (φ : I → E →+* ℂ), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData d φ → ∀ (𝔣 : Ideal (OF E)) (Λ : PeriodPair), IsBaseCond 𝔣 →
    GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsIntLattice d Λ →
    ∀ (l : ℕ) [Fact l.Prime] (Q : Finset (HeightOneSpectrum (OF E))), IsFinSetSplitPlacesCoprimeConductor 𝔣 Q → (∀ q ∈ Q, (l : OF E) ∉ q.asIdeal) →
    ∀ y : (Af E)ˣ, OneOver l y → ∀ (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (𝔠 : FracId (FR E)) (X : Obj (FR E) 𝔠 (Sp ℂ))
    (U : Unif φ (lattice (condQ 𝔣 Q) y) 0 X) (A' : Over (Sp ℂ)) [GrpObj A'] (L' : LB A'.left)
    (u : HolUnif A' L' (Module.finrank ℚ (FR E))), IsAbelianScheme A' →
    SmoothOfRelativeDimension (Module.finrank ℚ (FR E)) A'.hom → (∀ w, w ∈ u.Λ ↔ ∀ j, w j ∈ Λ.lattice) →
    ∀ j₀ : Fin (Module.finrank ℚ (FR E)),
    ∃ (α : A' ⟶ X.A) (M : (Fin (Module.finrank ℚ (FR E)) → ℂ) →ₗ[ℂ] (Fin (Module.finrank ℚ (FR E)) → ℂ)) (n N : ℕ),
      IsMonHom α ∧ IsFinite α.left ∧ Flat α.left ∧ Surjective α.left ∧ 1 ≤ N ∧
      (∀ (T : Over (Sp ℂ)) (x : T ⟶ A'), x ≫ α = 1 → x ^ N = 1) ∧ (∀ w, U.u.ex (M w) = u.ex w ≫ α) ∧
      M (Pi.single j₀ 1) = (fun _ ↦ (n : ℂ)) ∧ 0 < n ∧ Sz l lam (a0 𝔣 l) ((n : ℂ)⁻¹) := by
  intro E _ _ _ _ I _ d φ hφ 𝔣 Λ h𝔣 hΛ l _ Q _ hQ y hy lam 𝔠 X U A' _ L' u hA' hg hu j₀
  classical
  have hl : l.Prime := Fact.out
  obtain ⟨-, -, -, -, -, -, hCM, ω, -, hω⟩ := hφ
  obtain ⟨hc, m, hm, hmc⟩ := exists_mem_condQ h𝔣 hl Q hQ
  obtain ⟨m', hm', -, hm'L⟩ := GlobalTheory.CMVal.LatLoc.lattice_near_orderC E _ hc l hl y hy
  have hmm : ¬ l ∣ m * m' := fun h =>
    (hl.dvd_mul.1 h).elim hm ((Nat.Prime.coprime_iff_not_dvd hl).1 hm'.symm)
  set n : ℕ := l ^ a0 𝔣 l * (m * m') with hn
  have hn0 : 0 < n := Nat.mul_pos (pow_pos hl.pos _) (Nat.pos_of_ne_zero fun h => hmm (h ▸ dvd_zero l))
  have hnL : ∀ b : 𝓞 E, (n : E) * (b : E) ∈ lattice (condQ 𝔣 Q) y := fun b => by
    have h1 := hm'L (((l ^ a0 𝔣 l * m : ℕ) : E) * (b : E)) (mem_orderC.2 ⟨0, _, Ideal.mul_mem_right b _
      (Ideal.mem_map_of_mem (algebraMap (OF E) (𝓞 E)) hmc), by rw [map_zero, zero_add, map_mul, map_natCast, map_natCast]⟩)
    convert h1 using 1
    rw [hn]; push_cast; ring
  obtain ⟨θ, hθ⟩ := exists_separating E
  have hinj : Function.Injective fun k => φ (U.e k) (θ : E) := fun k k' h => by
    have h1 := hθ _ _ h
    exact U.e.injective ((hCM (φ (U.e k))).unique (Or.inl rfl) (Or.inl h1))
  let z : Fin (Module.finrank ℚ (FR E)) := ⟨0, j₀.pos⟩
  let s := Equiv.swap j₀ z
  let V : Matrix (Fin (Module.finrank ℚ (FR E))) (Fin (Module.finrank ℚ (FR E))) ℂ :=
    (n : ℂ) • (Matrix.vandermonde fun k => φ (U.e k) (θ : E)).submatrix id s
  have hV : V.det ≠ 0 := by
    rw [Matrix.det_smul, Matrix.det_permute']
    refine mul_ne_zero (pow_ne_zero _ (by exact_mod_cast hn0.ne')) (mul_ne_zero ?_ ?_)
    · exact_mod_cast Units.ne_zero _
    · exact Matrix.det_vandermonde_ne_zero_iff.2 hinj
  have hVe : ∀ x k, Matrix.toLin' V x k = ∑ j, (n : ℂ) * φ (U.e k) (θ : E) ^ (s j : ℕ) * x j := fun x k => rfl
  have hsurj : Function.Surjective (Matrix.toLin' V) := fun w =>
    ⟨V⁻¹.mulVec w, by rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (IsUnit.mk0 _ hV),
      Matrix.one_mulVec]⟩
  have hlift : ∀ x ∈ Λ.lattice, ∃ b : 𝓞 E, ∀ i, φ i (b : E) = x := fun x hx => by
    obtain ⟨hint, a, b, hab⟩ := (hΛ x).1 hx
    have h1 : ∀ i, φ i ((a : E) + (b : E) * ω) = x := fun i => by
      rw [map_add, map_mul, map_ratCast, map_ratCast, hω, hab]
    refine ⟨⟨(a : E) + (b : E) * ω, ?_⟩, h1⟩
    rw [← h1 (U.e j₀)] at hint
    exact (isIntegral_algHom_iff (φ (U.e j₀)).toIntAlgHom (φ (U.e j₀)).injective).1 hint
  have hM : ∀ x ∈ u.Λ, Matrix.toLin' V x ∈ U.u.Λ := fun x hx => by
    choose b hb using fun j => hlift (x j) ((hu x).1 hx j)
    refine (U.lat _).2 ⟨_, hnL (∑ j, θ ^ (s j : ℕ) * b j), funext fun k => ?_⟩
    have e : ((∑ j, θ ^ (s j : ℕ) * b j : 𝓞 E) : E) = ∑ j, (θ : E) ^ (s j : ℕ) * (b j : E) := by
      simp only [RingOfIntegers.coe_eq_algebraMap, map_sum, map_mul, map_pow]
    rw [hVe, e, GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.defCoord, Pi.zero_apply, zero_mul, add_zero, map_mul, map_natCast, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, map_pow, hb, _root_.mul_assoc]
  obtain ⟨α, hα, hαe⟩ := GlobalTheory.HolUnifHom.exists_isMonHom_of_map_lattice A' X.A _ hA' X.ab hg X.dim L' _ u U.u
    (Matrix.toLin' V) hM
  haveI : Surjective α.left := GlobalTheory.ComplexAbVarSurj.surjective_of_surjective_points A' X.A α hA' X.ab fun p => by
    obtain ⟨w, rfl⟩ := U.u.ex_onto p
    obtain ⟨w', rfl⟩ := hsurj w
    exact ⟨u.ex w', (hαe w').symm⟩
  obtain ⟨hfin, hflat⟩ := GlobalTheory.SurjHomFlat.finite_flat A' X.A _ hA' X.ab hg X.dim α
  obtain ⟨N, hN, hkill⟩ := exists_kill A' X.A hA' X.ab α
  refine ⟨α, Matrix.toLin' V, n, N, hα, hfin, hflat, inferInstance, hN, hkill, hαe, funext fun k => ?_, hn0,
    sz_inv_pow_mul l lam _ _ hmm⟩
  rw [hVe, Finset.sum_eq_single j₀ (fun j _ hj => by rw [Pi.single_eq_of_ne hj, mul_zero]) (by simp), Pi.single_eq_same,
    show s j₀ = z from Equiv.swap_apply_left _ _]
  simp [z]

end GlobalTheory.CMPowerIsogeny
