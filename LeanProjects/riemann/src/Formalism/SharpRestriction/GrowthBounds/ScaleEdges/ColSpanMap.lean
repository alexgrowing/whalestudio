import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.ManyEdges
import Formalism.SharpRestriction.GrowthBounds.LatticeSystems

noncomputable section

namespace Formalism.MainNotions.Pf14

open Formalism.MainNotions.G

section Incl

variable (W Qq : Type) [CommRing W] [IsDomain W] [Field Qq] [Algebra W Qq]

def incl (k : ℕ) : (Fin k → W) →ₗ[W] (Fin k → Qq) := (Algebra.linearMap W Qq).compLeft (Fin k)

variable {W Qq}

theorem incl_apply {k : ℕ} (y : Fin k → W) (i : Fin k) : incl W Qq k y i = algebraMap W Qq (y i) := rfl

theorem incl_inj [IsFractionRing W Qq] (k : ℕ) : Function.Injective (incl W Qq k) := by
  intro x y h
  funext i
  have h1 := congrFun h i
  rw [incl_apply, incl_apply] at h1
  exact IsFractionRing.injective W Qq h1

theorem colSpan_map {k : ℕ} (M : Matrix (Fin k) (Fin k) W) :
    colSpan W (M.map (algebraMap W Qq)) =
      (Submodule.span W (Set.range fun c : Fin k => fun i => M i c)).map (incl W Qq k) := by
  unfold colSpan
  rw [Submodule.map_span, ← Set.range_comp]
  rfl

theorem colSpan_one (k : ℕ) :
    colSpan W (1 : Matrix (Fin k) (Fin k) Qq) = LinearMap.range (incl W Qq k) := by
  have h1 : (1 : Matrix (Fin k) (Fin k) Qq) = (1 : Matrix (Fin k) (Fin k) W).map (algebraMap W Qq) :=
    (Matrix.map_one _ (map_zero _) (map_one _)).symm
  rw [h1, colSpan_map, LinearMap.range_eq_map]
  congr 1
  rw [← (Pi.basisFun W (Fin k)).span_eq]
  congr 1
  ext x
  simp only [Set.mem_range]
  constructor
  · rintro ⟨c, rfl⟩
    refine ⟨c, ?_⟩
    funext i
    simp [Matrix.one_apply, Pi.single_apply]
  · rintro ⟨c, rfl⟩
    refine ⟨c, ?_⟩
    funext i
    simp [Matrix.one_apply, Pi.single_apply]

theorem lattice_of [IsPrincipalIdealRing W] [IsFractionRing W Qq] (p k : ℕ) (hp0 : (p : W) ≠ 0)
    (N : Submodule W (Fin k → W)) (hpN : ∀ x, (p : W) • x ∈ N) : IsLattice W (N.map (incl W Qq k)) := by
  classical
  haveI : Module.Free W N := Module.Free.of_basis (Submodule.basisOfPid (Pi.basisFun W (Fin k)) N).2
  have hfin : Module.finrank W N = k := by
    apply le_antisymm
    · calc Module.finrank W N ≤ Module.finrank W (Fin k → W) := Submodule.finrank_le N
        _ = k := by simp
    · let f : (Fin k → W) →ₗ[W] N := LinearMap.codRestrict N ((p : W) • LinearMap.id) (fun c => by simpa using hpN c)
      have hinj : Function.Injective f := by
        intro x y hxy
        have h2 := congrArg Subtype.val hxy
        simp only [f, LinearMap.codRestrict_apply, LinearMap.smul_apply, LinearMap.id_apply] at h2
        exact smul_right_injective (Fin k → W) hp0 h2
      have h3 := LinearMap.finrank_le_finrank_of_injective hinj
      simpa using h3
  let b' : Module.Basis (Fin k) W N := Module.finBasisOfFinrankEq W N hfin
  let M : Matrix (Fin k) (Fin k) W := fun i c => (b' c : Fin k → W) i
  have hspan : Submodule.span W (Set.range fun c => (b' c : Fin k → W)) = N := by
    have h1 := congrArg (Submodule.map N.subtype) b'.span_eq
    rw [Submodule.map_span, Submodule.map_subtype_top, ← Set.range_comp] at h1
    exact h1
  let A : Matrix (Fin k) (Fin k) W := fun c i => b'.repr ⟨(p : W) • Pi.single i 1, hpN _⟩ c
  have hMA : M * A = (p : W) • (1 : Matrix (Fin k) (Fin k) W) := by
    ext a i
    have hx := congrArg (fun v : N => (v : Fin k → W) a) (b'.sum_repr ⟨(p : W) • Pi.single i 1, hpN _⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Pi.single_apply] at hx
    rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, ← hx]
    exact Finset.sum_congr rfl (fun c _ => by simp only [M, A]; ring)
  have hdetM : M.det ≠ 0 := by
    intro h0
    have h4 := congrArg Matrix.det hMA
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at h4
    exact pow_ne_zero k hp0 h4.symm
  refine ⟨M.map (algebraMap W Qq), ?_, ?_⟩
  · rw [isUnit_iff_ne_zero, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero_iff _ (IsFractionRing.injective W Qq)).mpr hdetM
  · rw [colSpan_map]
    congr 1
    exact hspan.symm

theorem card_quot [IsFractionRing W Qq] (k : ℕ) (T : Submodule W (Fin k → Qq))
    (hT : T = LinearMap.range (incl W Qq k)) (N : Submodule W (Fin k → W)) :
    Nat.card (↥T ⧸ Submodule.comap T.subtype (N.map (incl W Qq k))) = Nat.card ((Fin k → W) ⧸ N) := by
  subst hT
  refine Nat.card_congr (Submodule.Quotient.equiv N _ (LinearEquiv.ofInjective (incl W Qq k) (incl_inj k)) ?_).toEquiv.symm
  ext ⟨y, hy⟩
  simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply]
  constructor
  · rintro ⟨x, hx, hxy⟩
    refine ⟨x, hx, ?_⟩
    have h1 := congrArg Subtype.val hxy
    simpa [LinearEquiv.ofInjective_apply] using h1
  · rintro ⟨x, hx, hxy⟩
    refine ⟨x, hx, ?_⟩
    apply Subtype.ext
    simpa [LinearEquiv.ofInjective_apply] using hxy

end Incl

section Psi

variable {W : Type} [CommRing W]

def psi {r K : ℕ} (I : Ideal W) (A : Fin r → Fin K → W) : (Fin (r + K) → W) →ₗ[W] (Fin r → W ⧸ I) :=
  LinearMap.pi fun i =>
    (Submodule.mkQ I) ∘ₗ (LinearMap.proj (Fin.castAdd K i) + ∑ c, A i c • LinearMap.proj (Fin.natAdd r c))

theorem psi_apply {r K : ℕ} (I : Ideal W) (A : Fin r → Fin K → W) (y : Fin (r + K) → W) (i : Fin r) :
    psi I A y i = Ideal.Quotient.mk I (y (Fin.castAdd K i) + ∑ c, A i c * y (Fin.natAdd r c)) := by
  simp [psi, LinearMap.sum_apply]

theorem psi_surj {r K : ℕ} (I : Ideal W) (A : Fin r → Fin K → W) : Function.Surjective (psi I A) := by
  intro z
  choose f hf using fun i => Ideal.Quotient.mk_surjective (I := I) (z i)
  refine ⟨Fin.append f 0, ?_⟩
  funext i
  rw [psi_apply, Fin.append_left]
  simp [Fin.append_right, hf]

theorem psi_smul {r K : ℕ} (I : Ideal W) (a : W) (ha : a ∈ I) (A : Fin r → Fin K → W) (x : Fin (r + K) → W) :
    a • x ∈ LinearMap.ker (psi I A) := by
  rw [LinearMap.mem_ker, map_smul]
  funext i
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (psi I A x i)
  rw [Pi.smul_apply, ← hy, Algebra.smul_def, Ideal.Quotient.algebraMap_eq,
    Ideal.Quotient.eq_zero_iff_mem.mpr ha, zero_mul, Pi.zero_apply]

theorem psi_ker_inj {r K : ℕ} (I : Ideal W) (A B : Fin r → Fin K → W)
    (h : LinearMap.ker (psi I A) = LinearMap.ker (psi I B)) (i : Fin r) (c : Fin K) :
    Ideal.Quotient.mk I (A i c) = Ideal.Quotient.mk I (B i c) := by
  have key : ∀ Z : Fin r → Fin K → W, ∀ i', psi I Z (Fin.append (fun i'' => -A i'' c) (Pi.single c 1)) i' =
      Ideal.Quotient.mk I (-A i' c + Z i' c) := by
    intro Z i'
    rw [psi_apply, Fin.append_left]
    congr 1
    simp [Fin.append_right, Pi.single_apply]
  have hA : Fin.append (fun i'' => -A i'' c) (Pi.single c 1) ∈ LinearMap.ker (psi I A) := by
    rw [LinearMap.mem_ker]
    funext i'
    rw [key, Pi.zero_apply]
    simp
  rw [h, LinearMap.mem_ker] at hA
  have h1 := congrFun hA i
  rw [key, Pi.zero_apply, Ideal.Quotient.eq_zero_iff_mem] at h1
  rw [eq_comm, Ideal.Quotient.eq]
  convert h1 using 1
  ring

end Psi

theorem manyEdges : ManyEdges := by
  classical
  intro p n' W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w hS k r hrk
  obtain ⟨K, rfl⟩ : ∃ K, k = r + K := ⟨k - r, by omega⟩
  haveI := hS.frac_alt
  set I : Ideal W := Ideal.span {(p : W)} with hI
  have hpI : (p : W) ∈ I := Ideal.mem_span_singleton_self _
  have hp0 : (p : W) ≠ 0 := hS.p_unif.ne_zero
  have hcard : Nat.card (W ⧸ I) = p ^ n' := hS.res_card
  haveI : Finite (W ⧸ I) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ hS.prime.ne_zero)
  haveI : Fintype (W ⧸ I) := Fintype.ofFinite _
  choose lift hlift using (Ideal.Quotient.mk_surjective (I := I))
  let ed : (Fin r → Fin K → W ⧸ I) → Edge W Qq (r + K) := fun A =>
    ⟨(LinearMap.ker (psi I (fun i c => lift (A i c)))).map (incl W Qq (r + K)),
      colSpan W (1 : Matrix (Fin (r + K)) (Fin (r + K)) Qq)⟩
  have hinj : Function.Injective ed := by
    intro A B hAB
    have h1 := congrArg Edge.src hAB
    have h2 := Submodule.map_injective_of_injective (incl_inj (W := W) (Qq := Qq) (r + K)) h1
    funext i c
    have h3 := psi_ker_inj I _ _ h2 i c
    rwa [hlift, hlift] at h3
  refine ⟨Finset.univ.image ed, ?_, ?_⟩
  · intro e he
    obtain ⟨A, -, rfl⟩ := Finset.mem_image.mp he
    refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, rfl⟩
    · exact lattice_of (Qq := Qq) p (r + K) hp0 _ (fun x => psi_smul I (p : W) hpI _ x)
    · exact ⟨1, by simp, rfl⟩
    · show _ ≤ colSpan W (1 : Matrix (Fin (r + K)) (Fin (r + K)) Qq)
      rw [colSpan_one]
      exact LinearMap.map_le_range
    · intro x hx
      change x ∈ colSpan W (1 : Matrix (Fin (r + K)) (Fin (r + K)) Qq) at hx
      rw [colSpan_one] at hx
      obtain ⟨y, rfl⟩ := LinearMap.mem_range.mp hx
      exact Submodule.mem_map.mpr ⟨(p : W) • y, psi_smul I (p : W) hpI _ y, map_smul _ _ _⟩
    · refine (card_quot (r + K) _ (colSpan_one (r + K)) _).trans ?_
      rw [Nat.card_congr (LinearMap.quotKerEquivOfSurjective _ (psi_surj I _)).toEquiv]
      rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin, ← Nat.card_eq_fintype_card, hcard,
        ← pow_mul]
  · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fun, Fintype.card_fun,
      Fintype.card_fin, Fintype.card_fin, ← Nat.card_eq_fintype_card, hcard, Nat.add_sub_cancel_left,
      ← pow_mul, ← pow_mul]
    apply le_of_eq
    congr 1
    ring

end Formalism.MainNotions.Pf14
