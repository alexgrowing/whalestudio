import Mathlib
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.IsOrthCo
import Formalism.LocalToGlobal.Columns.RecLevel
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AlgebraMapApply
open NumberField IsDedekindDomain Formalism.UG Formalism.UG.P Formalism.L2.PairingIndexBounds.F
open scoped TensorProduct Matrix

namespace GlobalTheory.LatAdLoc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

local notation "𝔸" => FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
local notation "ι" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)

theorem latAd_eq_globLat {N : ℕ} (x : GL (Fin N) (E ⊗[F] 𝔸)) (Lb : Submodule (𝓞 E) (Fin N → E)) :
    latAd x Lb = Formalism.UG.CS.globLat x Lb :=
  Submodule.span_eq (Formalism.UG.CS.globLat x Lb)

theorem incl_smul {N : ℕ} (s : 𝓞 E) (w : Fin N → E) :
    (fun i => ι ((s • w) i)) = ι (algebraMap (𝓞 E) E s) • fun i => ι (w i) := by
  ext i; simp [Algebra.smul_def]

theorem exists_den_vec {N : ℕ} (Lb : Submodule (𝓞 E) (Fin N → E))
    (hspan : Submodule.span E (Lb : Set (Fin N → E)) = ⊤) (z : Fin N → E ⊗[F] 𝔸) :
    ∃ d : 𝓞 F, d ≠ 0 ∧ levelafC E d • z ∈ latS (F := F) 𝔸 𝒮 Lb := by
  classical
  obtain ⟨m, hm0, hm⟩ := csGlob_single Lb hspan
  choose d hd0 hd using fun i => levelaf_denom (E := E) (z i)
  have hP : ∀ i, levelafC E (∏ k, d k) * z i ∈ 𝒮 := fun i => by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), levelafC_mul,
      mul_comm (levelafC E (d i)), mul_assoc]
    exact mul_mem (levelafC_mem _) (hd i)
  have hmC : levelafC E ((m : ℤ) : 𝓞 F) = ((m : ℤ) : E ⊗[F] 𝔸) := by
    rw [levelafC, map_intCast, ← Algebra.TensorProduct.includeRight_apply, map_intCast]
  refine ⟨(∏ k, d k) * ((m : ℤ) : 𝓞 F),
    mul_ne_zero (Finset.prod_ne_zero_iff.2 fun i _ => hd0 i) (Int.cast_ne_zero.2 hm0), ?_⟩
  have e : levelafC E ((∏ k, d k) * ((m : ℤ) : 𝓞 F)) • z =
      ∑ k, (⟨_, hP k⟩ : 𝒮) • (fun i => ι ((Pi.single k (m : E) : Fin N → E) i)) := by
    funext j
    rw [Finset.sum_apply, Finset.sum_eq_single j]
    · simp only [Pi.smul_apply, Subring.smul_def, smul_eq_mul, Pi.single_eq_same, map_intCast,
        levelafC_mul, hmC]
      ring
    · intro k _ hkj
      simp only [Pi.smul_apply, Subring.smul_def, smul_eq_mul, Pi.single_eq_of_ne (Ne.symm hkj),
        map_zero, mul_zero]
    · exact fun h => absurd (Finset.mem_univ j) h
  rw [e]
  exact sum_mem fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hm k, rfl⟩)

theorem mem_loc_latAd (hc : Formalism.BasicNotions.CMData F E) (Q : HeightOneSpectrum (𝓞 E))
    (v : HeightOneSpectrum (𝓞 F)) (hQ : Formalism.L2.Col.IsOver v Q) {N : ℕ}
    (Lb : Submodule (𝓞 E) (Fin N → E)) (hspan : Submodule.span E (Lb : Set (Fin N → E)) = ⊤)
    (x : GL (Fin N) (E ⊗[F] 𝔸)) (w : Fin N → E) :
    w ∈ Formalism.HermitianLatticesTheory.loc (K := E) Q.asIdeal (latAd x Lb) ↔
      afsplitEps E v • (((x⁻¹ : GL (Fin N) (E ⊗[F] 𝔸)) : Matrix (Fin N) (Fin N) (E ⊗[F] 𝔸)) *ᵥ
        fun i => ι (w i)) ∈ latS (F := F) 𝔸 𝒮 Lb := by
  rw [latAd_eq_globLat]
  have hpv : Q.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E)) = v.asIdeal := hQ.symm
  have hp : Q.asIdeal.IsPrime := Q.isPrime
  have hs : ∀ e, (hc.sig : E →+* E) ((hc.sig : E →+* E) e) = e := fun e => star_star e
  have hfix : ∀ e : E, hc.sig e = e → ∃ a : F, algebraMap F E a = e := fun e he => (hc.fixed e).1 he
  constructor
  · rintro ⟨s, hsc, hsx⟩
    have key : ∀ s ∈ Formalism.HermitianLatticesTheory.hcompl (K := E) Q.asIdeal,
        ∃ u ∈ 𝒮, u * ι (algebraMap (𝓞 E) E s) = afsplitEps E v := by
      intro s hs'
      induction hs' using Submonoid.closure_induction with
      | mem s h => exact GlobalTheory.LocDict.exists_inv_gen hc.sig hs hfix v Q.asIdeal hp hpv s h.1 h.2
      | one => exact ⟨_, afsplit_eps_int v, by rw [map_one, map_one, mul_one]⟩
      | mul a b _ _ ha hb =>
        obtain ⟨u, hu, e⟩ := ha
        obtain ⟨u', hu', e'⟩ := hb
        refine ⟨u * u', mul_mem hu hu', ?_⟩
        rw [map_mul, map_mul, mul_mul_mul_comm, e, e', afsplit_eps_idem]
    obtain ⟨u, hu, e⟩ := key s hsc
    have hsx' : ((x⁻¹ : GL (Fin N) (E ⊗[F] 𝔸)) : Matrix (Fin N) (Fin N) (E ⊗[F] 𝔸)) *ᵥ
        (fun i => ι ((s • w) i)) ∈ latS (F := F) 𝔸 𝒮 Lb := hsx
    have h := Submodule.smul_mem (latS (F := F) 𝔸 𝒮 Lb) ⟨u, hu⟩ hsx'
    convert h using 1
    rw [incl_smul, Matrix.mulVec_smul, Subring.smul_def, smul_smul, e]
  · intro hx
    obtain ⟨d, hd0, hd⟩ := exists_den_vec Lb hspan
      (((x⁻¹ : GL (Fin N) (E ⊗[F] 𝔸)) : Matrix (Fin N) (Fin N) (E ⊗[F] 𝔸)) *ᵥ fun i => ι (w i))
    obtain ⟨t, ht, y, hy, e⟩ := GlobalTheory.LocDict.exists_approx v d hd0
    have hinj : Function.Injective (algebraMap (𝓞 E) E) := IsFractionRing.injective (𝓞 E) E
    have htp : algebraMap (𝓞 F) (𝓞 E) t ∉ Q.asIdeal := by
      rw [← Ideal.mem_comap, hpv]; exact ht
    refine ⟨algebraMap (𝓞 F) (𝓞 E) t, Submonoid.subset_closure ⟨htp, fun r hr => ?_⟩, ?_⟩
    · have : r = algebraMap (𝓞 F) (𝓞 E) t := by
        apply hinj
        rw [hr, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 F) F E]
        exact (hc.fixed _).2 ⟨_, rfl⟩
      rw [this]; exact htp
    · show ((x⁻¹ : GL (Fin N) (E ⊗[F] 𝔸)) : Matrix (Fin N) (Fin N) (E ⊗[F] 𝔸)) *ᵥ
        (fun i => ι ((algebraMap (𝓞 F) (𝓞 E) t • w) i)) ∈ latS (F := F) 𝔸 𝒮 Lb
      rw [incl_smul, Matrix.mulVec_smul, ← IsScalarTower.algebraMap_apply, adelstab_incl_C]
      have e2 : levelafC E t = levelafC E t * afsplitEps E v +
          ((1 : E) ⊗ₜ[F] y) * levelafC E d := by
        rw [GlobalTheory.LocDict.eps_eq, levelafC, levelafC, Algebra.TensorProduct.tmul_mul_tmul,
          Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← TensorProduct.tmul_add, ← e]
      rw [e2, add_smul, ← smul_smul, ← smul_smul]
      exact add_mem (Submodule.smul_mem _ ⟨_, levelafC_mem (E := E) t⟩ hx)
        (Submodule.smul_mem _ ⟨_, GlobalTheory.LocDict.one_tmul_mem hy⟩ hd)

theorem eps_smul_inv_mulVec {N : ℕ} (v : HeightOneSpectrum (𝓞 F)) (x x₁ : GL (Fin N) (E ⊗[F] 𝔸))
    (h : bc (prV (E := E) v) x₁ = bc (prV (E := E) v) x) (z : Fin N → E ⊗[F] 𝔸) :
    afsplitEps E v • (((x₁⁻¹ : GL (Fin N) (E ⊗[F] 𝔸)) : Matrix (Fin N) (Fin N) (E ⊗[F] 𝔸)) *ᵥ z) =
      afsplitEps E v • (((x⁻¹ : GL (Fin N) (E ⊗[F] 𝔸)) : Matrix (Fin N) (Fin N) (E ⊗[F] 𝔸)) *ᵥ z) := by
  have hinv : bc (prV (E := E) v) x₁⁻¹ = bc (prV (E := E) v) x⁻¹ := by rw [map_inv, map_inv, h]
  have hij : ∀ i j, prV (E := E) v (((x₁⁻¹ : GL (Fin N) (E ⊗[F] 𝔸)) : Matrix (Fin N) (Fin N) (E ⊗[F] 𝔸)) i j) =
      prV (E := E) v (((x⁻¹ : GL (Fin N) (E ⊗[F] 𝔸)) : Matrix (Fin N) (Fin N) (E ⊗[F] 𝔸)) i j) := fun i j =>
    by
    have := congrArg (fun g : GL (Fin N) (E ⊗[F] v.adicCompletion F) =>
      ((g : Matrix (Fin N) (Fin N) (E ⊗[F] v.adicCompletion F)) i j)) hinv
    exact this
  funext i
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← mul_assoc, ← mul_assoc, ← afsplit_decomp, ← afsplit_decomp, hij]

theorem loc_latAd_eq : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : Formalism.BasicNotions.CMData F E) (Q : HeightOneSpectrum (𝓞 E)) (v : HeightOneSpectrum (𝓞 F)), Formalism.L2.Col.IsOver v Q → ∀ {N : ℕ} (Lb : Submodule (𝓞 E) (Fin N → E)), Module.Finite (𝓞 E) Lb → Submodule.span E (Lb : Set (Fin N → E)) = ⊤ → ∀ (x x₁ : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)), bc (prV (E := E) v) x₁ = bc (prV (E := E) v) x → Formalism.HermitianLatticesTheory.loc (K := E) Q.asIdeal (latAd x₁ Lb) = Formalism.HermitianLatticesTheory.loc (K := E) Q.asIdeal (latAd x Lb) := by
  intro F E _ _ _ _ _ _ hc Q v hQ N Lb _ hspan x x₁ h
  ext w
  rw [mem_loc_latAd hc Q v hQ Lb hspan x₁ w, mem_loc_latAd hc Q v hQ Lb hspan x w,
    eps_smul_inv_mulVec v x x₁ h]

end GlobalTheory.LatAdLoc
