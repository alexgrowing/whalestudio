import Mathlib
import Formalism.QuotientMetricDivisors.ClassSumDualLe
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.RatHerm
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.IdxChange
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.LocBasis
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ReductionLemmaFirst
import Lemmata.HermitianVanishing.KeyZero

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.DivisionValues

namespace exponent_index_lattice

section Abs

variable {R K V W : Type} [CommRing R] [Field K] [StarRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
  [AddCommGroup W] [Module K W] [Module R W] [IsScalarTower R K W]

theorem dual_map (hV : V →ₗ⋆[K] V →ₗ[K] K) (hW : W →ₗ⋆[K] W →ₗ[K] K) (E : W →ₗ[K] V)
    (P : V →ₗ[K] W) (adj : ∀ x z, hW (P x) z = hV x (E z)) (A : Submodule R V) :
    Formalism.HermitianLatticesTheory.dual hW (A.map (P.restrictScalars R)) =
      (Formalism.HermitianLatticesTheory.dual hV A).comap (E.restrictScalars R) := by
  ext x
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, Submodule.mem_map,
    LinearMap.coe_restrictScalars, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, adj]

theorem map_isLattice (P : V →ₗ[K] W) (hP : Function.Surjective P) (B : Submodule R V)
    (hB : Submodule.IsLattice K B) : Submodule.IsLattice K (B.map (P.restrictScalars R)) := by
  refine ⟨hB.fg.map _, ?_⟩
  rw [Submodule.map_coe, LinearMap.coe_restrictScalars, Submodule.span_image, hB.span_eq_top,
    Submodule.map_top, LinearMap.range_eq_top.mpr hP]

theorem dual_comap [IsDedekindDomain R] [IsFractionRing R K] [FiniteDimensional K V]
    [FiniteDimensional K W] (hV : V →ₗ⋆[K] V →ₗ[K] K) (hVs : hV.IsSymm) (hVn : hV.Nondegenerate)
    (hW : W →ₗ⋆[K] W →ₗ[K] K) (hWs : hW.IsSymm)
    (hstar : ∀ r : R, star (algebraMap R K r) ∈ Set.range (algebraMap R K))
    (E : W →ₗ[K] V) (P : V →ₗ[K] W) (adj : ∀ x z, hW (P x) z = hV x (E z))
    (hE : Function.Injective E) (hP : Function.Surjective P)
    (A : Submodule R V) (hA : Submodule.IsLattice K A) :
    Formalism.HermitianLatticesTheory.dual hW (A.comap (E.restrictScalars R)) =
      (Formalism.HermitianLatticesTheory.dual hV A).map (P.restrictScalars R) := by
  obtain ⟨hL, hdd, -⟩ := Formalism.HermitianLatticesTheory.dualLattice R K V hV hVs hVn hstar A hA
  have h1 := dual_map (R := R) hV hW E P adj (Formalism.HermitianLatticesTheory.dual hV A)
  rw [hdd] at h1
  have hsep : hW.SeparatingRight := by
    intro z hz
    apply hE
    rw [map_zero]
    apply hVn.2
    intro x
    rw [← adj]
    exact hz _
  have hWn : hW.Nondegenerate := by
    refine ⟨fun x hx => hsep x fun y => ?_, hsep⟩
    rw [← hWs.eq x y, hx y, map_zero]
  have hBP := map_isLattice (R := R) P hP _ hL
  rw [← h1]
  exact (Formalism.HermitianLatticesTheory.dualLattice R K W hW hWs hWn hstar _ hBP).2.1

end Abs

variable {K : Type} [Field K] [NumberField K] [StarRing K]

open RationalHermitianForm

theorem hstar : ∀ r : 𝓞 K, star (algebraMap (𝓞 K) K r) ∈ Set.range (algebraMap (𝓞 K) K) := fun r =>
  (IsIntegralClosure.isIntegral_iff (R := ℤ) (A := 𝓞 K)).mp
    (((IsIntegralClosure.isIntegral_iff (R := ℤ) (A := 𝓞 K)).mpr ⟨r, rfl⟩).map
      (starRingEnd K).toIntAlgHom)

theorem herm_entry' {n : ℕ} {H : Matrix (Fin n) (Fin n) K} (hH : Hᴴ = H) (i j : Fin n) :
    H j i = star (H i j) := by
  have h := congrFun (congrFun hH j) i
  rw [Matrix.conjTranspose_apply] at h
  exact h.symm

theorem herm_cut {n d : ℕ} {H : Matrix (Fin n) (Fin n) K} (hH : Hᴴ = H)
    (E : Matrix (Fin n) (Fin d) K) : (Eᴴ * H * E)ᴴ = Eᴴ * H * E := by
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hH, Matrix.mul_assoc]

theorem orth_eq {n d : ℕ} {H : Matrix (Fin n) (Fin n) K} (hH : Hᴴ = H)
    {E : Matrix (Fin n) (Fin d) K} {Pr : Matrix (Fin d) (Fin n) K} (hO : IsOrthProj H E Pr) :
    H * E = Prᴴ * (Eᴴ * H * E) := by
  have h2 : Eᴴ * H = Eᴴ * H * (E * Pr) := by
    have h := hO.2
    rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at h
    exact h
  have h3 := congrArg Matrix.conjTranspose h2
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hH] at h3
  rw [h3]
  simp only [Matrix.mul_assoc]

theorem adj {n d : ℕ} {H : Matrix (Fin n) (Fin n) K} (hH : Hᴴ = H)
    {E : Matrix (Fin n) (Fin d) K} {Pr : Matrix (Fin d) (Fin n) K} (hO : IsOrthProj H E Pr)
    (x : Fin n → K) (z : Fin d → K) :
    hform (Eᴴ * H * E) (Matrix.mulVecLin Pr x) z = hform H x (Matrix.mulVecLin E z) := by
  have key : ∀ {m : ℕ} (M : Matrix (Fin m) (Fin m) K) (u v : Fin m → K),
      hform M u v = star u ⬝ᵥ (M *ᵥ v) := by
    intro m M u v
    simp only [hform_apply, dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply, mul_assoc]
  rw [key, key, Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, Matrix.star_mulVec,
    ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← orth_eq hH hO]

theorem E_inj {n d : ℕ} {H : Matrix (Fin n) (Fin n) K}
    {E : Matrix (Fin n) (Fin d) K} {Pr : Matrix (Fin d) (Fin n) K} (hO : IsOrthProj H E Pr) :
    Function.Injective (Matrix.mulVecLin E) := by
  intro x y hxy
  have h := congrArg (Matrix.mulVec Pr) hxy
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hO.1, Matrix.one_mulVec] at h
  exact h

theorem Pr_surj {n d : ℕ} {H : Matrix (Fin n) (Fin n) K}
    {E : Matrix (Fin n) (Fin d) K} {Pr : Matrix (Fin d) (Fin n) K} (hO : IsOrthProj H E Pr) :
    Function.Surjective (Matrix.mulVecLin Pr) := by
  intro z
  refine ⟨E.mulVec z, ?_⟩
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hO.1, Matrix.one_mulVec]

theorem isOrthProj_formula {n d : ℕ} (H : Matrix (Fin n) (Fin n) K) (E : Matrix (Fin n) (Fin d) K)
    (hZ : IsUnit (Eᴴ * H * E).det) : IsOrthProj H E ((Eᴴ * H * E)⁻¹ * (Eᴴ * H)) := by
  constructor
  · rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hZ]
  · rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero, ← Matrix.mul_assoc (Eᴴ * H) E,
      ← Matrix.mul_assoc (Eᴴ * H * E), Matrix.mul_nonsing_inv _ hZ, Matrix.one_mul]

theorem isOrthProj_unique {n d : ℕ} {H : Matrix (Fin n) (Fin n) K} {E : Matrix (Fin n) (Fin d) K}
    {Pr : Matrix (Fin d) (Fin n) K} (hZ : IsUnit (Eᴴ * H * E).det) (hO : IsOrthProj H E Pr) :
    Pr = (Eᴴ * H * E)⁻¹ * (Eᴴ * H) := by
  have h2 : Eᴴ * H = Eᴴ * H * E * Pr := by
    have h := hO.2
    rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero, ← Matrix.mul_assoc (Eᴴ * H) E Pr] at h
    exact h
  calc Pr = (Eᴴ * H * E)⁻¹ * (Eᴴ * H * E) * Pr := by rw [Matrix.nonsing_inv_mul _ hZ, Matrix.one_mul]
    _ = (Eᴴ * H * E)⁻¹ * (Eᴴ * H) := by rw [Matrix.mul_assoc (Eᴴ * H * E)⁻¹ (Eᴴ * H * E) Pr, ← h2]

end exponent_index_lattice

open exponent_index_lattice RationalHermitianForm

theorem projection_dual_lattice : ProjDualLat := by
  intro K _ _ _ n d H hH E Pr hO A
  exact dual_map (hform H) (hform (Eᴴ * H * E)) (Matrix.mulVecLin E) (Matrix.mulVecLin Pr) (adj hH hO) A

theorem sectioned_dual_lattice : CutDualLat := by
  intro K _ _ _ n d H hH hdet E Pr hO A hA
  have hs := hform_isSymm H (herm_entry' hH)
  exact dual_comap (hform H) hs (hform_nondeg H hs hdet.ne_zero) (hform (Eᴴ * H * E))
    (hform_isSymm _ (herm_entry' (herm_cut hH E))) hstar (Matrix.mulVecLin E) (Matrix.mulVecLin Pr)
    (adj hH hO) (E_inj hO) (Pr_surj hO) A hA

namespace exponent_index_lattice

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem idxB {D : ℕ} (w : HeightOneSpectrum (𝓞 K)) (A B C : Submodule (𝓞 K) (Fin D → K))
    (hA : Submodule.IsLattice K A) (hB : Submodule.IsLattice K B) (hC : Submodule.IsLattice K C) :
    idx w A B = - idx w B A ∧ idx w A C = idx w A B + idx w B C ∧
      (B ≤ A → idx w A B = Formalism.HermitianLatticesTheory.locLen w.asIdeal A B) := by
  have hH : (1 : Matrix (Fin D) (Fin D) K)ᴴ = 1 := Matrix.conjTranspose_one
  have hs := hform_isSymm (1 : Matrix (Fin D) (Fin D) K) (herm_entry' hH)
  have hn := hform_nondeg (1 : Matrix (Fin D) (Fin D) K) hs (by simp)
  have : w.asIdeal.IsMaximal := w.isMaximal
  have h := Formalism.HermitianLatticesTheory.indexBasic (𝓞 K) K (Fin D → K) (hform 1) hs hn hstar w.asIdeal A B C hA hB hC
  exact ⟨h.2.1, h.2.2.1, h.2.2.2.1⟩

def sm (D : ℕ) (a : K) : (Fin D → K) →ₗ[K] (Fin D → K) := a • LinearMap.id

theorem sm_surj (D : ℕ) {a : K} (ha : a ≠ 0) : Function.Surjective (sm D a) := by
  intro y
  refine ⟨a⁻¹ • y, ?_⟩
  simp [sm, smul_smul, ha]

def smLat {D : ℕ} (a : K) (A : Submodule (𝓞 K) (Fin D → K)) : Submodule (𝓞 K) (Fin D → K) :=
  A.map ((sm D a).restrictScalars (𝓞 K))

theorem mem_smLat {D : ℕ} (a : K) (A : Submodule (𝓞 K) (Fin D → K)) (x : Fin D → K) :
    x ∈ smLat a A ↔ ∃ y ∈ A, a • y = x := by
  unfold smLat
  rw [Submodule.mem_map]
  exact Iff.rfl

theorem loc_smLat_le {D : ℕ} (a : K) (p : Ideal (𝓞 K)) {L L' : Submodule (𝓞 K) (Fin D → K)}
    (h : Formalism.HermitianLatticesTheory.loc (K := K) p L ≤ Formalism.HermitianLatticesTheory.loc (K := K) p L') :
    Formalism.HermitianLatticesTheory.loc (K := K) p (smLat a L) ≤ Formalism.HermitianLatticesTheory.loc (K := K) p (smLat a L') := by
  intro x hx
  have hx' : ∃ s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p, s • x ∈ smLat a L := hx
  obtain ⟨s, hs, hsx⟩ := hx'
  obtain ⟨y, hy, hya⟩ := (mem_smLat a L _).mp hsx
  show ∃ t ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p, t • x ∈ smLat a L'
  by_cases ha : a = 0
  · refine ⟨s, hs, ?_⟩
    rw [← hya, ha, zero_smul]
    exact Submodule.zero_mem _
  · have hyloc : a⁻¹ • x ∈ Formalism.HermitianLatticesTheory.loc (K := K) p L := by
      show ∃ s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p, s • a⁻¹ • x ∈ L
      refine ⟨s, hs, ?_⟩
      rw [smul_comm, ← hya, smul_smul, inv_mul_cancel₀ ha, one_smul]
      exact hy
    have hty : ∃ t ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p, t • a⁻¹ • x ∈ L' := h hyloc
    obtain ⟨t, ht, htL⟩ := hty
    refine ⟨t, ht, (mem_smLat a L' _).mpr ⟨t • a⁻¹ • x, htL, ?_⟩⟩
    rw [smul_comm a t, smul_smul, mul_inv_cancel₀ ha, one_smul]

theorem idx_smLat {D : ℕ} (w : HeightOneSpectrum (𝓞 K)) (A : Submodule (𝓞 K) (Fin D → K))
    (hA : Submodule.IsLattice K A) {a : K} (ha : a ≠ 0) :
    idx w A (smLat a A) = (D : ℤ) * vw w a := by
  obtain ⟨f, hf⟩ := semilocal_basis_exists K D A hA w
  have haA : Submodule.IsLattice K (smLat a A) := map_isLattice (sm D a) (sm_surj D ha) A hA
  have hspK : Submodule.span K (Set.range f) = ⊤ :=
    hf.1.span_eq_top_of_card_eq_finrank' (by simp)
  have hspan_f : Submodule.IsLattice K (Submodule.span (𝓞 K) (Set.range f)) :=
    ⟨Submodule.fg_span (Set.finite_range f), by rw [Submodule.span_span_of_tower, hspK]⟩
  have hone_f : (fun i => ∑ k, (1 : Matrix (Fin D) (Fin D) K) k i • f k) = f := by
    funext i
    simp [Matrix.one_apply]
  have ha_f : (fun i => ∑ k, (a • (1 : Matrix (Fin D) (Fin D) K)) k i • f k) = fun i => a • f i := by
    funext i
    simp [Matrix.one_apply]
  have i1 := (index_change_formula K D A hA f hf.1 w 1 (by rw [hone_f]; exact hf)).1
  have hspan_af : Submodule.span (𝓞 K) (Set.range fun i => a • f i) =
      smLat a (Submodule.span (𝓞 K) (Set.range f)) := by
    unfold smLat
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  have hloc : IsLocBasis (smLat a A) w (fun i => a • f i) := by
    refine ⟨?_, ?_⟩
    · exact hf.1.units_smul (fun _ => Units.mk0 a ha)
    · rw [hspan_af]
      exact le_antisymm (loc_smLat_le a _ hf.2.le) (loc_smLat_le a _ hf.2.ge)
  have i2 := (index_change_formula K D (smLat a A) haA f hf.1 w (a • 1) (by rw [ha_f]; exact hloc)).1
  rw [Matrix.det_one, ValuationRepresentative.vw_one] at i1
  rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin, ReductionFirst.vw_pow] at i2
  have h := idxB w A (Submodule.span (𝓞 K) (Set.range f)) (smLat a A) hA hspan_f haA
  rw [h.2.1, h.1, i1, i2]
  ring

end exponent_index_lattice

theorem exponent_index_local : ExpIndexLoc := by
  intro K _ _ _ D A B hA hB w a ha hAB
  have ha' : (a : K) ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr ha
  have hC : Submodule.IsLattice K (smLat (a : K) A) := map_isLattice (sm D (a : K)) (sm_surj D ha') A hA
  obtain ⟨-, hsum, -⟩ := idxB w A (smLat (a : K) A) B hA hC hB
  rw [hsum, idx_smLat w A hA ha']
  have htop : (Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (smLat (a : K) A ⊓ B)).comap
      (Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (smLat (a : K) A)).subtype = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨x, hx⟩ -
    simp only [Submodule.mem_comap, Submodule.subtype_apply]
    obtain ⟨s, hs, hsx⟩ : ∃ s ∈ w.asIdeal.primeCompl, s • x ∈ smLat (a : K) A := hx
    obtain ⟨y, hy, hyx⟩ := (mem_smLat (a : K) A _).mp hsx
    obtain ⟨t, ht, htB⟩ : ∃ t ∈ w.asIdeal.primeCompl, t • a • y ∈ B := hAB y hy
    show ∃ u ∈ w.asIdeal.primeCompl, u • x ∈ smLat (a : K) A ⊓ B
    refine ⟨t * s, w.asIdeal.primeCompl.mul_mem ht hs, Submodule.mem_inf.mpr ⟨?_, ?_⟩⟩
    · rw [mul_smul]
      exact Submodule.smul_mem _ t hsx
    · rw [mul_smul, ← hyx, show ((a : K)) • y = a • y from algebraMap_smul K a y]
      exact htB
  have hz : Formalism.HermitianLatticesTheory.locLen w.asIdeal (smLat (a : K) A) (smLat (a : K) A ⊓ B) = 0 := by
    unfold Formalism.HermitianLatticesTheory.locLen
    have hsub : Subsingleton (↥(Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (smLat (a : K) A)) ⧸
      (Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (smLat (a : K) A ⊓ B)).comap (Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (smLat (a : K) A)).subtype) :=
    ⟨fun u v => Submodule.Quotient.induction_on _ u (fun x => Submodule.Quotient.induction_on _ v (fun y =>
      (Submodule.Quotient.eq _).mpr (by rw [htop]; trivial)))⟩
    rw [Module.length_eq_zero_iff.mpr hsub]
    rfl
  have hle : idx w (smLat (a : K) A) B ≤ 0 := by
    unfold idx Formalism.HermitianLatticesTheory.lidx
    rw [hz]
    simp
  linarith

namespace exponent_index_lattice

section Abs2

variable {K V W : Type} [Field K] [StarRing K]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

theorem nondeg_of_adj (hV : V →ₗ⋆[K] V →ₗ[K] K) (hVn : hV.Nondegenerate)
    (hW : W →ₗ⋆[K] W →ₗ[K] K) (hWs : hW.IsSymm) (E : W →ₗ[K] V) (P : V →ₗ[K] W)
    (adj : ∀ x z, hW (P x) z = hV x (E z)) (hE : Function.Injective E) : hW.Nondegenerate := by
  have hR : hW.SeparatingRight := by
    intro z hz
    apply hE
    rw [map_zero]
    exact hVn.2 (E z) (fun x => by rw [← adj]; exact hz (P x))
  exact ⟨fun w hw => hR w (fun z => hWs.isRefl w z (hw z)), hR⟩

end Abs2

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem mem_cutLat {n d : ℕ} (E : Matrix (Fin n) (Fin d) K) (A : Submodule (𝓞 K) (Fin n → K))
    (z : Fin d → K) : z ∈ cutLat E A ↔ E.mulVec z ∈ A := Iff.rfl

theorem mem_matLat {n d : ℕ} (P : Matrix (Fin d) (Fin n) K) (A : Submodule (𝓞 K) (Fin n → K))
    (z : Fin d → K) : z ∈ matLat P A ↔ ∃ x ∈ A, P.mulVec x = z := by
  exact Iff.rfl

theorem mulVec_osmul {n d : ℕ} (E : Matrix (Fin n) (Fin d) K) (r : 𝓞 K) (z : Fin d → K) :
    E.mulVec (r • z) = r • E.mulVec z := Matrix.mulVec_smul E r z

theorem cut_isLattice {n d : ℕ} (E : Matrix (Fin n) (Fin d) K)
    (hE : Function.Injective (Matrix.mulVecLin E)) (A : Submodule (𝓞 K) (Fin n → K))
    (hA : Submodule.IsLattice K A) : Submodule.IsLattice K (cutLat E A) := by
  refine ⟨?_, ?_⟩
  · have hN : IsNoetherian (𝓞 K) A := isNoetherian_of_fg_of_noetherian A hA.fg
    apply Submodule.fg_of_fg_map_injective ((Matrix.mulVecLin E).restrictScalars (𝓞 K)) hE
    exact isNoetherian_submodule.mp hN _ (Submodule.map_comap_le _ _)
  · rw [eq_top_iff]
    intro z _
    have hv : E.mulVec z ∈ Submodule.span K (A : Set (Fin n → K)) := by
      rw [hA.span_eq_top]
      trivial
    rw [IsLocalization.mem_span_iff (M := nonZeroDivisors (𝓞 K))] at hv
    obtain ⟨y, hy, r, hr⟩ := hv
    rw [Submodule.span_eq] at hy
    have hmem : (r : 𝓞 K) • z ∈ cutLat E A := by
      rw [mem_cutLat, mulVec_osmul, hr, ← smul_assoc,
        Algebra.smul_def (r : 𝓞 K) (IsLocalization.mk' K (1 : 𝓞 K) r), IsLocalization.mk'_spec', map_one,
        one_smul]
      exact hy
    have hr0 : algebraMap (𝓞 K) K r ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors r.2
    have hz : z = (algebraMap (𝓞 K) K r)⁻¹ • ((r : 𝓞 K) • z) := by
      rw [← algebraMap_smul K (r : 𝓞 K) z, smul_smul, inv_mul_cancel₀ hr0, one_smul]
    rw [hz]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

theorem coe_natCast (m : ℕ) : (((m : 𝓞 K)) : K) = (m : K) := by simp

end exponent_index_lattice

theorem ValuationLatticeDual : BoundsIVGen := by
  intro K _ _ _ n d H hH hdet E Pr hO A B hA DG hDG hB w a ha haB
  have hs := hform_isSymm H (herm_entry' hH)
  have hn := hform_nondeg H hs hdet.ne_zero
  have hsZ := hform_isSymm _ (herm_entry' (herm_cut hH E))
  have hnZ := nondeg_of_adj (hform H) hn (hform (Eᴴ * H * E)) hsZ (Matrix.mulVecLin E)
    (Matrix.mulVecLin Pr) (adj hH hO) (E_inj hO)
  have hT : Submodule.IsLattice K (matLat Pr A) :=
    map_isLattice (Matrix.mulVecLin Pr) (Pr_surj hO) A hA
  have hC : Submodule.IsLattice K (cutLat E A) := cut_isLattice E (E_inj hO) A hA
  have hCT : cutLat E A ≤ matLat Pr A := by
    intro z hz
    exact (mem_matLat _ _ _).mpr ⟨E.mulVec z, hz, by simp [Matrix.mulVec_mulVec, hO.1]⟩
  refine ⟨hT, hC, hCT, ?_⟩
  have hTh : Submodule.IsLattice K (Formalism.HermitianLatticesTheory.dual (hform (Eᴴ * H * E)) (matLat Pr A)) :=
    (Formalism.HermitianLatticesTheory.dualLattice (𝓞 K) K (Fin d → K) _ hsZ hnZ hstar _ hT).1
  have hL1 := projection_dual_lattice K n d H hH E Pr hO A
  have hDG0 : (DG : 𝓞 K) ≠ 0 := by exact_mod_cast hDG.ne'
  have ha' : (a : K) ≠ 0 := by simpa using ha
  have hDG' : (DG : K) ≠ 0 := by exact_mod_cast hDG.ne'
  have h2 := exponent_index_local K d (cutLat E A) _ hC hTh w (a * (DG : 𝓞 K)) (mul_ne_zero ha hDG0)
    (by
      intro z hz
      obtain ⟨s, hs, hsz⟩ := haB z hz
      refine ⟨s, hs, ?_⟩
      rw [mem_cutLat, mulVec_osmul, mulVec_osmul] at hsz
      rw [hL1, mem_cutLat, mulVec_osmul, mulVec_osmul]
      have := hB _ hsz
      have e : s • (a * (DG : 𝓞 K)) • E.mulVec z = (DG : 𝓞 K) • s • a • E.mulVec z := by
        simp only [smul_smul]
        congr 1
        ring
      rw [e]
      exact this)
  have hv : vw w ((a * (DG : 𝓞 K) : 𝓞 K) : K) = vw w (a : K) + vw w (DG : K) := by
    rw [show ((a * (DG : 𝓞 K) : 𝓞 K) : K) = (a : K) * ((DG : 𝓞 K) : K) from
      map_mul (algebraMap (𝓞 K) K) a _, coe_natCast, ValuationRepresentative.vw_mul w _ _ ha' hDG']
  rw [hv] at h2
  have h3 := idxB w (matLat Pr A) (cutLat E A) _ hT hC hTh
  change idx w (matLat Pr A) (Formalism.HermitianLatticesTheory.dual (hform (Eᴴ * H * E)) (matLat Pr A)) ≤ _
  rw [h3.2.1, h3.2.2 hCT]
  linarith

theorem bounds_fourth : BoundsIV := by
  intro K _ _ _ n d H hH hdet E Pr hO A B hA DG hDG hB w ϖ J hv hJ
  have hϖ : ϖ ≠ 0 := by
    rintro rfl
    simp [vw, FractionalIdeal.count_zero] at hv
  have hvJ : vw w (((ϖ ^ J : 𝓞 K)) : K) = J := by
    have e : (((ϖ ^ J : 𝓞 K)) : K) = (ϖ : K) ^ J := by exact map_pow (algebraMap (𝓞 K) K) ϖ J
    unfold vw
    rw [e, ← FractionalIdeal.spanSingleton_pow, FractionalIdeal.count_pow]
    unfold vw at hv
    rw [hv, mul_one]
  obtain ⟨h1, h2, h3, h4⟩ := ValuationLatticeDual K n d H hH hdet E Pr hO A B hA DG hDG hB w (ϖ ^ J)
    (pow_ne_zero J hϖ) hJ
  rw [hvJ] at h4
  exact ⟨h1, h2, h3, h4⟩

theorem divisor_bounds_first : BoundsI := by
  intro K _ _ _ n' n H' hH hdet E Pr hO A B hA s hs G hG
  refine ⟨cut_isLattice E (E_inj hO) A hA, ?_⟩
  intro x hx
  rw [sectioned_dual_lattice K n' n H' hH hdet E Pr hO A hA] at hx
  obtain ⟨y, hy, rfl⟩ := (mem_matLat Pr _ x).mp hx
  rw [mem_cutLat]
  have h1 := hG _ (hs y hy)
  convert h1 using 1
  rw [mulVec_osmul, mulVec_osmul, Matrix.mulVec_mulVec, Nat.cast_mul, smul_smul]

theorem bounds_fourth_general : BoundsIVal := by
  intro K _ _ _ _ K0 hcm v0 hv0 n' n D H' hH hdet E Pr hO hK0 hpos P hP A B hA s hs0 hAB G hG0 hG
    w e he
  obtain ⟨hL, hincl⟩ := divisor_bounds_first K n' n H' hH hdet E Pr hO A B hA s hAB G hG
  have h := reduction_lemma_first K K0 hcm v0 hv0 n D (Eᴴ * H' * E) hK0 hpos P hP (cutLat E A) hL (G * s) 1
    (Nat.mul_pos hG0 hs0) (by intro x hx; rw [pow_one]; exact hincl x hx) w e he
  have hG' : (G : K) ≠ 0 := by exact_mod_cast hG0.ne'
  have hs' : (s : K) ≠ 0 := by exact_mod_cast hs0.ne'
  rw [Nat.cast_mul, ValuationRepresentative.vw_mul w _ _ hG' hs'] at h
  simpa using h

theorem projection_integral : ProjIntegral := by
  intro K _ _ _ n G0 _ r c G hc B hB x hx
  choose a ha using hc
  have hs : ∀ s (w : Fin n → K), a s • w = ((a s : K)) • w := fun s w => (algebraMap_smul K (a s) w).symm
  have hsum : (∑ s, c s • r s).mulVec x = ∑ s, c s • (r s).mulVec x := by
    have h := map_sum (Matrix.mulVec.addMonoidHomLeft x) (fun s => c s • r s) Finset.univ
    change (∑ s, c s • r s).mulVec x = ∑ s, (c s • r s).mulVec x at h
    rw [h]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    ext i
    simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  rw [Nat.cast_smul_eq_nsmul, hsum, Finset.smul_sum]
  refine Submodule.sum_mem _ (fun s _ => ?_)
  rw [← Nat.cast_smul_eq_nsmul K, smul_smul, ← ha s, ← hs]
  exact B.smul_mem (a s) (hB s x hx)

namespace exponent_index_lattice

variable {K : Type} [Field K] [NumberField K] [StarRing K]

section Inv

variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  {Γ : Type} [Group Γ] [Fintype Γ] (ρ : Γ →* Module.End K V)

def invSub : Submodule K V where
  carrier := {v | ∀ γ, ρ γ v = v}
  add_mem' := fun {a b} ha hb γ => by rw [map_add, ha γ, hb γ]
  zero_mem' := fun γ => map_zero _
  smul_mem' := fun c v hv γ => by rw [map_smul, hv γ]

theorem tr_inv (v : V) (γ : Γ) : ρ γ (∑ δ, ρ δ v) = ∑ δ, ρ δ v := by
  rw [map_sum]
  have h : ∀ δ, ρ γ (ρ δ v) = ρ (γ * δ) v := fun δ => by rw [map_mul]; rfl
  simp_rw [h]
  exact Fintype.sum_bijective (γ * ·) (Group.mulLeft_bijective γ) _ _ (fun _ => rfl)

theorem avg_mem (v : V) :
    (((Fintype.card Γ : K)⁻¹) • ∑ δ, ρ δ : V →ₗ[K] V) v ∈ invSub ρ := by
  intro γ
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, tr_inv]

def avg : V →ₗ[K] invSub ρ :=
  LinearMap.codRestrict (invSub ρ) (((Fintype.card Γ : K)⁻¹) • ∑ δ, ρ δ) (avg_mem ρ)

theorem avg_coe (v : V) : ((avg ρ v : invSub ρ) : V) = ((Fintype.card Γ : K)⁻¹) • ∑ δ, ρ δ v := by
  simp only [avg, LinearMap.codRestrict_apply, LinearMap.smul_apply, LinearMap.sum_apply]

theorem card_ne : (Fintype.card Γ : K) ≠ 0 := by
  exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero

theorem inv_dual [FiniteDimensional K V] (pair : V →ₗ⋆[K] V →ₗ[K] K) (hs : pair.IsSymm)
    (hn : pair.Nondegenerate) (hiso : ∀ γ x y, pair (ρ γ x) (ρ γ y) = pair x y)
    (A : Submodule (𝓞 K) V) (hA : Submodule.IsLattice K A) :
    Formalism.HermitianLatticesTheory.dual (pair.domRestrict₁₂ (invSub ρ) (invSub ρ))
              (A.comap ((invSub ρ).subtype.restrictScalars (𝓞 K))) =
      (Formalism.HermitianLatticesTheory.dual pair A).map ((avg ρ).restrictScalars (𝓞 K)) := by
  refine dual_comap (R := 𝓞 K) pair hs hn (pair.domRestrict₁₂ (invSub ρ) (invSub ρ))
    ⟨fun x y => hs.eq _ _⟩ hstar (invSub ρ).subtype (avg ρ)
    ?_ (Submodule.subtype_injective _) ?_ A hA
  · intro x z
    rw [LinearMap.domRestrict₁₂_apply, avg_coe, map_smulₛₗ, LinearMap.smul_apply, map_sum,
      LinearMap.sum_apply]
    have : ∀ δ, pair (ρ δ x) (z : V) = pair x (z : V) := by
      intro δ
      conv_lhs => rw [← z.2 δ]
      exact hiso δ x z
    simp only [this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, smul_eq_mul, map_inv₀,
      map_natCast, Submodule.subtype_apply]
    rw [← mul_assoc, inv_mul_cancel₀ (card_ne (K := K) (Γ := Γ)), one_mul]
  · intro z
    refine ⟨z, Subtype.ext ?_⟩
    rw [avg_coe]
    have hz : ∀ δ, ρ δ (z : V) = z := z.2
    simp only [hz, Finset.sum_const, Finset.card_univ]
    rw [← Nat.cast_smul_eq_nsmul K, smul_smul, inv_mul_cancel₀ (card_ne (K := K) (Γ := Γ)), one_smul]

end Inv

end exponent_index_lattice

namespace exponent_index_lattice

variable {K : Type} [Field K] [NumberField K] [StarRing K]

end exponent_index_lattice

theorem orthogonal_projection_exists : OrthProjExists := by
  intro K _ _ _ v0 hc0 n d H hPD E hE
  have hc : ∀ a : K, v0.embedding (star a) = starRingEnd ℂ (v0.embedding a) := hc0
  have hH : Hᴴ = H := by
    ext i j
    apply v0.embedding.injective
    have h1 := hPD.1.apply i j
    simp only [Matrix.map_apply] at h1
    simp only [Matrix.conjTranspose_apply]
    rw [hc, starRingEnd_apply, h1]
  have hdet : IsUnit H.det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    have h1 := hPD.det_pos
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero] at h1
    exact lt_irrefl _ h1
  have hmap : ∀ u : Fin n → K, star (fun i => v0.embedding (u i)) ⬝ᵥ
      ((H.map v0.embedding) *ᵥ (fun i => v0.embedding (u i))) = v0.embedding (star u ⬝ᵥ (H *ᵥ u)) := by
    intro u
    simp only [dotProduct, Matrix.mulVec, map_sum, map_mul, Pi.star_apply, hc, starRingEnd_apply, Matrix.map_apply]
  have hZ : IsUnit (Eᴴ * H * E).det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    obtain ⟨z, hz, hz0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec] at hz0
    have h2 : star (E *ᵥ z) ⬝ᵥ (H *ᵥ (E *ᵥ z)) = 0 := by
      rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, hz0]
      simp
    have hu : E *ᵥ z ≠ 0 := fun h => hz (hE (by rw [h, Matrix.mulVec_zero]))
    have hne : (fun i => v0.embedding ((E *ᵥ z) i)) ≠ 0 := by
      intro h
      apply hu
      funext i
      have h5 := congrFun h i
      simp only [Pi.zero_apply, map_eq_zero] at h5
      simpa using h5
    have h3 : 0 < star (fun i => v0.embedding ((E *ᵥ z) i)) ⬝ᵥ
        ((H.map v0.embedding) *ᵥ (fun i => v0.embedding ((E *ᵥ z) i))) := by
      first
        | exact hPD.dotProduct_mulVec_pos hne
        | exact (Matrix.posDef_iff_dotProduct_mulVec.mp hPD).2 _ hne
    rw [hmap, h2, map_zero] at h3
    exact lt_irrefl _ h3
  exact ⟨hH, hdet, hZ, isOrthProj_formula H E hZ, fun Pr hO => isOrthProj_unique hZ hO⟩

end Formalism.DivisionValues
