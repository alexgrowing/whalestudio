import Mathlib
import Formalism.MeanHeightDescent.MuMaxMinkowski
import Formalism.HarderNarasimhan.ShiftInvariance

open Module NumberField

noncomputable section

namespace Formalism.ExtensionFiltration

open Formalism.HN

namespace HermitianIdempotentFrameLemmas

variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {V ι : Type} [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]

theorem norm_herm_idem_le (R : Matrix ι ι ℂ) (h1 : R.IsHermitian) (h2 : R * R = R)
    (z : EuclideanSpace ℂ ι) : ‖Matrix.toEuclideanLin R z‖ ≤ ‖z‖ := by
  have hs : (Matrix.toEuclideanLin R).IsSymmetric := (Matrix.isHermitian_iff_isSymmetric).1 h1
  have hTT : ∀ w, Matrix.toEuclideanLin R (Matrix.toEuclideanLin R w) = Matrix.toEuclideanLin R w := by
    intro w
    rw [Matrix.toEuclideanLin_eq_toLin, ← LinearMap.comp_apply, ← Matrix.toLin_mul, h2]
  set y := Matrix.toEuclideanLin R z with hy
  have h3 : @inner ℂ _ _ y y = @inner ℂ _ _ z y := by
    have h4 := hs z y
    rw [hy, hTT z] at h4
    rw [hy]
    exact h4
  have h5 : ‖y‖ ^ 2 ≤ ‖z‖ * ‖y‖ := by
    have h6 := re_inner_le_norm (𝕜 := ℂ) z y
    have h7 : RCLike.re (@inner ℂ _ _ y y) = ‖y‖ ^ 2 := inner_self_eq_norm_sq y
    rw [h3] at h7
    linarith
  have hy0 : 0 ≤ ‖y‖ := norm_nonneg _
  have hz0 : 0 ≤ ‖z‖ := norm_nonneg _
  nlinarith

theorem frameMat_herm (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (e : V →ₗ[K] V) (v : InfinitePlace K)
    (hsa : ∀ x y, Formalism.HermitianLatticesTheory.majAt b X v (e x) y = Formalism.HermitianLatticesTheory.majAt b X v x (e y)) :
    ((X v)⁻¹ * (LinearMap.toMatrix b b e).map v.embedding * X v).IsHermitian := by
  have hXU : X v * (X v)⁻¹ = 1 := Matrix.mul_nonsing_inv _ (hX v)
  have hUu : IsUnit ((X v)⁻¹).det := Matrix.isUnit_nonsing_inv_det _ (hX v)
  set U := (X v)⁻¹ with hUdef
  set M := (LinearMap.toMatrix b b e).map v.embedding with hMdef
  have hcol : ∀ k l, (U.mulVec (fun i => v.embedding ((b.repr (b k)) i))) l = U l k := by
    intro k l
    have hv : (fun i => v.embedding ((b.repr (b k)) i)) = Pi.single k 1 := by
      funext i
      by_cases h : i = k
      · subst h
        simp
      · simp [Finsupp.single_apply, Pi.single_apply, h, Ne.symm h]
    rw [hv]
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have hcolM : ∀ k l, (U.mulVec (fun i => v.embedding ((b.repr (e (b k))) i))) l = (U * M) l k := by
    intro k l
    have hv2 : (fun i => v.embedding ((b.repr (e (b k))) i)) = fun i => M i k := by
      funext i
      rw [hMdef, Matrix.map_apply, LinearMap.toMatrix_apply]
    rw [hv2]
    rfl
  have key : (U * M).conjTranspose * U = U.conjTranspose * (U * M) := by
    ext k l
    have h := hsa (b k) (b l)
    unfold Formalism.HermitianLatticesTheory.majAt Formalism.HermitianLatticesTheory.fcoord Formalism.HermitianLatticesTheory.vecAt at h
    rw [← hUdef] at h
    simp only [hcol, hcolM] at h
    rw [Matrix.mul_apply, Matrix.mul_apply]
    exact h
  have hUHu : IsUnit U.conjTranspose.det := by
    rw [Matrix.det_conjTranspose]
    exact hUu.star
  have hFU : U * M * X v * U = U * M := by
    rw [Matrix.mul_assoc (U * M), hXU, Matrix.mul_one]
  have key2 : U.conjTranspose * (U * M * X v).conjTranspose * U = U.conjTranspose * (U * M * X v) * U := by
    calc U.conjTranspose * (U * M * X v).conjTranspose * U = (U * M * X v * U).conjTranspose * U := by
          rw [Matrix.conjTranspose_mul (U * M * X v) U]
      _ = (U * M).conjTranspose * U := by rw [hFU]
      _ = U.conjTranspose * (U * M) := key
      _ = U.conjTranspose * (U * M * X v * U) := by rw [hFU]
      _ = U.conjTranspose * (U * M * X v) * U := by simp only [Matrix.mul_assoc]
  have hinvL : (U.conjTranspose)⁻¹ * U.conjTranspose = 1 := Matrix.nonsing_inv_mul _ hUHu
  have hinvR : U * U⁻¹ = 1 := Matrix.mul_nonsing_inv _ hUu
  unfold Matrix.IsHermitian
  calc (U * M * X v).conjTranspose = (U.conjTranspose)⁻¹ * (U.conjTranspose * (U * M * X v).conjTranspose * U) * U⁻¹ := by
        simp only [Matrix.mul_assoc]
        rw [hinvR, Matrix.mul_one, ← Matrix.mul_assoc (U.conjTranspose)⁻¹, hinvL, Matrix.one_mul]
    _ = (U.conjTranspose)⁻¹ * (U.conjTranspose * (U * M * X v) * U) * U⁻¹ := by rw [key2]
    _ = U * M * X v := by
        simp only [Matrix.mul_assoc]
        rw [hinvR, Matrix.mul_one, ← Matrix.mul_assoc (U.conjTranspose)⁻¹, hinvL, Matrix.one_mul]

theorem frameMat_idem (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (e : V →ₗ[K] V) (v : InfinitePlace K) (hee : e ∘ₗ e = e) :
    ((X v)⁻¹ * (LinearMap.toMatrix b b e).map v.embedding * X v) *
      ((X v)⁻¹ * (LinearMap.toMatrix b b e).map v.embedding * X v) =
      (X v)⁻¹ * (LinearMap.toMatrix b b e).map v.embedding * X v := by
  set M := (LinearMap.toMatrix b b e).map v.embedding with hMdef
  have hM : M * M = M := by
    rw [hMdef, ← Matrix.map_mul, ← LinearMap.toMatrix_comp, hee]
  have hXinv : X v * (X v)⁻¹ = 1 := Matrix.mul_nonsing_inv _ (hX v)
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (X v) (X v)⁻¹, hXinv, Matrix.one_mul, ← Matrix.mul_assoc M M, hM]

theorem opNormAt_le (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (e : V →ₗ[K] V) (g : ℕ) (v : InfinitePlace K) (hee : e ∘ₗ e = e)
    (hsa : ∀ x y, Formalism.HermitianLatticesTheory.majAt b X v (e x) y = Formalism.HermitianLatticesTheory.majAt b X v x (e y)) :
    opNormAt b X b X v ((g : K) • (LinearMap.id - e)) ≤ (g : ℝ) := by
  have hH := frameMat_herm b X hX e v hsa
  have hI := frameMat_idem b X hX e v hee
  have hXinv : (X v)⁻¹ * X v = 1 := Matrix.nonsing_inv_mul _ (hX v)
  set F := (X v)⁻¹ * (LinearMap.toMatrix b b e).map v.embedding * X v with hF
  have h1 : LinearMap.toMatrix b b ((g : K) • (LinearMap.id - e)) =
      g • (1 - LinearMap.toMatrix b b e) := by
    rw [Nat.cast_smul_eq_nsmul, map_nsmul, map_sub, LinearMap.toMatrix_id]
  have h2 : (g • (1 - LinearMap.toMatrix b b e)).map v.embedding =
      g • (1 - (LinearMap.toMatrix b b e).map v.embedding) := by
    have h3 := map_nsmul (v.embedding.mapMatrix) g (1 - LinearMap.toMatrix b b e)
    rw [map_sub, map_one] at h3
    exact h3
  have hmat : (X v)⁻¹ * (LinearMap.toMatrix b b ((g : K) • (LinearMap.id - e))).map v.embedding * X v =
      g • (1 - F) := by
    rw [h1, h2, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hXinv, hF]
  have hH' : (1 - F).IsHermitian := by
    unfold Matrix.IsHermitian at hH ⊢
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hH]
  have hI' : (1 - F) * (1 - F) = 1 - F := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hI]
    abel
  unfold opNormAt
  rw [hmat]
  apply ContinuousLinearMap.opNorm_le_bound _ (Nat.cast_nonneg g)
  intro z
  have hz := norm_herm_idem_le (1 - F) hH' hI' z
  have happ : (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (g • (1 - F)))) z =
      g • Matrix.toEuclideanLin (1 - F) z := by
    rw [LinearMap.coe_toContinuousLinearMap', map_nsmul, LinearMap.smul_apply]
  rw [happ, ← Nat.cast_smul_eq_nsmul ℂ, norm_smul]
  have hgn : ‖(g : ℂ)‖ = g := by simp
  rw [hgn]
  exact mul_le_mul_of_nonneg_left hz (Nat.cast_nonneg g)

section Mod

variable [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem natCast_smul_mem (N : Submodule (𝓞 K) V) (g : ℕ) {x : V} (hx : x ∈ N) :
    (g : K) • x ∈ N := by
  rw [Nat.cast_smul_eq_nsmul]
  exact N.nsmul_mem hx g

theorem idem_apply (e : V →ₗ[K] V) (hee : e ∘ₗ e = e) (x : V) : e (e x) = e x := LinearMap.congr_fun hee x

theorem cut_mem (e : V →ₗ[K] V) (g : ℕ) (N : Submodule (𝓞 K) V) (hee : e ∘ₗ e = e)
    (hint : ∀ x ∈ N, (g : K) • e x ∈ N) {x : V} (hx : x ∈ N) :
    (g : K) • (x - e x) ∈ N ⊓ (LinearMap.ker e).restrictScalars (𝓞 K) := by
  refine ⟨?_, ?_⟩
  · rw [smul_sub]
    exact N.sub_mem (natCast_smul_mem N g hx) (hint x hx)
  · show e ((g : K) • (x - e x)) = 0
    rw [map_smul, map_sub, idem_apply e hee x, sub_self, smul_zero]

theorem rk_add (b : Basis ι K V) (e : V →ₗ[K] V) (g : ℕ) (N : Submodule (𝓞 K) V) (hg : 1 ≤ g)
    (hee : e ∘ₗ e = e) (hint : ∀ x ∈ N, (g : K) • e x ∈ N) :
    rkK (N ⊓ (LinearMap.range e).restrictScalars (𝓞 K)) +
      rkK (N ⊓ (LinearMap.ker e).restrictScalars (𝓞 K)) = rkK N := by
  haveI : FiniteDimensional K V := Module.Finite.of_basis b
  have hg0 : (g : K) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hinv : ∀ y : V, (g : K)⁻¹ • ((g : K) • y) = y := fun y => by
    rw [smul_smul, inv_mul_cancel₀ hg0, one_smul]
  set S : Submodule K V := Submodule.span K (N : Set V) with hS
  have hNS : ∀ x ∈ N, x ∈ S := fun x hx => Submodule.subset_span hx
  have heS : ∀ x ∈ S, e x ∈ S := by
    have hle : S.map e ≤ S := by
      rw [hS, Submodule.map_span, Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      have h1 : (g : K) • e x ∈ S := hNS _ (hint x hx)
      have h2 := S.smul_mem ((g : K)⁻¹) h1
      rw [hinv] at h2
      exact h2
    intro x hx
    exact hle ⟨x, hx, rfl⟩
  have hA : Submodule.span K ((N ⊓ (LinearMap.range e).restrictScalars (𝓞 K) : Submodule (𝓞 K) V) : Set V) =
      S.map e := by
    apply le_antisymm
    · rw [Submodule.span_le]
      intro y hy
      obtain ⟨hyN, hyr⟩ := hy
      obtain ⟨z, hz⟩ := LinearMap.mem_range.mp hyr
      refine ⟨y, hNS y hyN, ?_⟩
      rw [← hz, idem_apply e hee z]
    · rw [hS, Submodule.map_span, Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      have h1 : (g : K) • e x ∈ (N ⊓ (LinearMap.range e).restrictScalars (𝓞 K) : Submodule (𝓞 K) V) :=
        Submodule.mem_inf.mpr ⟨hint x hx, LinearMap.mem_range.mpr ⟨(g : K) • x, map_smul e _ x⟩⟩
      have h3 : (g : K) • e x ∈ Submodule.span K ((N ⊓ (LinearMap.range e).restrictScalars (𝓞 K) :
          Submodule (𝓞 K) V) : Set V) := Submodule.subset_span h1
      have h2 := Submodule.smul_mem _ ((g : K)⁻¹) h3
      rw [hinv] at h2
      exact h2
  have hB : Submodule.span K ((N ⊓ (LinearMap.ker e).restrictScalars (𝓞 K) : Submodule (𝓞 K) V) : Set V) =
      S.map (LinearMap.id - e : V →ₗ[K] V) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      intro y hy
      obtain ⟨hyN, hyk⟩ := hy
      have hy0 : e y = 0 := hyk
      refine ⟨y, hNS y hyN, ?_⟩
      show y - e y = y
      rw [hy0, sub_zero]
    · rw [hS, Submodule.map_span, Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      have h1 := cut_mem e g N hee hint hx
      have h3 : (g : K) • (x - e x) ∈ Submodule.span K ((N ⊓ (LinearMap.ker e).restrictScalars (𝓞 K) :
          Submodule (𝓞 K) V) : Set V) := Submodule.subset_span h1
      have h2 := Submodule.smul_mem _ ((g : K)⁻¹) h3
      rw [hinv] at h2
      exact h2
  have hsup : S.map e ⊔ S.map (LinearMap.id - e : V →ₗ[K] V) = S := by
    apply le_antisymm
    · apply sup_le
      · rintro _ ⟨x, hx, rfl⟩
        exact heS x hx
      · rintro _ ⟨x, hx, rfl⟩
        exact S.sub_mem hx (heS x hx)
    · intro x hx
      have h1 : e x + (LinearMap.id - e : V →ₗ[K] V) x ∈ S.map e ⊔ S.map (LinearMap.id - e : V →ₗ[K] V) :=
        Submodule.add_mem_sup ⟨x, hx, rfl⟩ ⟨x, hx, rfl⟩
      have h2 : e x + (LinearMap.id - e : V →ₗ[K] V) x = x := by
        simp
      rw [h2] at h1
      exact h1
  have hinf : S.map e ⊓ S.map (LinearMap.id - e : V →ₗ[K] V) = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨⟨a, ha, hay⟩, ⟨c, hc, hcy⟩⟩
    have h1 : e y = y := by rw [← hay, idem_apply e hee a]
    have h2 : e y = 0 := by
      rw [← hcy]
      show e (c - e c) = 0
      rw [map_sub, idem_apply e hee c, sub_self]
    exact (Submodule.mem_bot K).mpr (h1.symm.trans h2)
  have key := Submodule.finrank_sup_add_finrank_inf_eq (S.map e) (S.map (LinearMap.id - e : V →ₗ[K] V))
  rw [hsup, hinf, finrank_bot, add_zero] at key
  unfold rkK
  rw [hA, hB]
  exact key.symm

theorem ker_cut (e : V →ₗ[K] V) (g : ℕ) (hg : 1 ≤ g) (hee : e ∘ₗ e = e) :
    LinearMap.ker ((g : K) • (LinearMap.id - e)) = LinearMap.range e := by
  ext x
  have hg0 : (g : K) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  constructor
  · intro h
    have h' : (g : K) • (x - e x) = 0 := h
    have h'' : x - e x = 0 := (smul_eq_zero.mp h').resolve_left hg0
    exact ⟨x, (sub_eq_zero.mp h'').symm⟩
  · rintro ⟨y, rfl⟩
    show (g : K) • (e y - e (e y)) = 0
    rw [idem_apply e hee y, sub_self, smul_zero]

theorem map_cut_le (e : V →ₗ[K] V) (g : ℕ) (N : Submodule (𝓞 K) V) (hee : e ∘ₗ e = e)
    (hint : ∀ x ∈ N, (g : K) • e x ∈ N) :
    N.map (((g : K) • (LinearMap.id - e) : V →ₗ[K] V).restrictScalars (𝓞 K)) ≤
      N ⊓ (LinearMap.ker e).restrictScalars (𝓞 K) := by
  rintro _ ⟨x, hx, rfl⟩
  exact cut_mem e g N hee hint hx

theorem smul_mem_map_cut (e : V →ₗ[K] V) (g : ℕ) (N : Submodule (𝓞 K) V) {y : V}
    (hy : y ∈ N ⊓ (LinearMap.ker e).restrictScalars (𝓞 K)) :
    (g : K) • y ∈ N.map (((g : K) • (LinearMap.id - e) : V →ₗ[K] V).restrictScalars (𝓞 K)) := by
  obtain ⟨hyN, hyk⟩ := hy
  refine ⟨y, hyN, ?_⟩
  have hy0 : e y = 0 := hyk
  show (g : K) • (y - e y) = (g : K) • y
  rw [hy0, sub_zero]

theorem rk_map_cut (e : V →ₗ[K] V) (g : ℕ) (N : Submodule (𝓞 K) V) (hg : 1 ≤ g)
    (hee : e ∘ₗ e = e) (hint : ∀ x ∈ N, (g : K) • e x ∈ N) :
    rkK (N ⊓ (LinearMap.ker e).restrictScalars (𝓞 K)) =
      rkK (N.map (((g : K) • (LinearMap.id - e) : V →ₗ[K] V).restrictScalars (𝓞 K))) := by
  have hg0 : (g : K) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hspan : Submodule.span K ((N ⊓ (LinearMap.ker e).restrictScalars (𝓞 K) : Submodule (𝓞 K) V) : Set V) =
      Submodule.span K ((N.map (((g : K) • (LinearMap.id - e) : V →ₗ[K] V).restrictScalars (𝓞 K)) :
        Submodule (𝓞 K) V) : Set V) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      intro y hy
      have h1 := smul_mem_map_cut e g N hy
      have h2 : (g : K) • y ∈ Submodule.span K ((N.map (((g : K) • (LinearMap.id - e) : V →ₗ[K] V).restrictScalars (𝓞 K)) :
          Submodule (𝓞 K) V) : Set V) := Submodule.subset_span h1
      have h3 := Submodule.smul_mem _ ((g : K)⁻¹) h2
      rwa [smul_smul, inv_mul_cancel₀ hg0, one_smul] at h3
    · exact Submodule.span_mono (SetLike.coe_subset_coe.mpr (map_cut_le e g N hee hint))
  unfold rkK
  rw [hspan]

theorem rkK_ne_zero (b : Basis ι K V) (A : Submodule (𝓞 K) V) (hA : A ≠ ⊥) :
    rkK (K := K) A ≠ 0 := by
  haveI : FiniteDimensional K V := Module.Finite.of_basis b
  unfold rkK
  intro h
  apply hA
  rw [Submodule.finrank_eq_zero] at h
  rw [eq_bot_iff]
  intro x hx
  have hx' : x ∈ Submodule.span K (A : Set V) := Submodule.subset_span hx
  rw [h] at hx'
  exact (Submodule.mem_bot _).mpr ((Submodule.mem_bot K).mp hx')

theorem rkK_bot : rkK (K := K) (⊥ : Submodule (𝓞 K) V) = 0 := by
  unfold rkK
  simp

theorem nPl_ne_zero : (nPl K : ℝ) ≠ 0 := by
  unfold nPl
  exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero

theorem disc_pos : 0 < |(NumberField.discr K : ℝ)| := abs_pos.mpr (Int.cast_ne_zero.mpr (NumberField.discr_ne_zero K))

theorem log_ht (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (hX : ∀ v, IsUnit (X v).det)
    (L : Submodule (𝓞 K) V) (hL : L.FG) :
    Real.log (ht b X L) = (nPl K : ℝ) * (rkK L : ℝ) * Real.log 2 - (rkK L : ℝ) / 2 * logDisc K -
      deg (Formalism.HermitianLatticesTheory.realize b X) L := by
  have hpos := (place_lattice_structure K V ι b X hX L hL).2.2
  have hc : Formalism.F.covol (zl (Formalism.HermitianLatticesTheory.realize b X) L) ≠ 0 := by
    intro h0
    rw [ht, h0, mul_zero] at hpos
    exact lt_irrefl _ hpos
  have h2 : ((2 : ℝ) ^ (nPl K * rkK L)) ≠ 0 := by positivity
  have h3 : |(NumberField.discr K : ℝ)| ^ (-(rkK L : ℝ) / 2) ≠ 0 :=
    (Real.rpow_pos_of_pos disc_pos _).ne'
  rw [ht, Real.log_mul (mul_ne_zero h2 h3) hc, Real.log_mul h2 h3, Real.log_pow,
    Real.log_rpow disc_pos]
  simp only [deg, Formalism.F.deg, logDisc]
  push_cast
  ring

theorem log_htQ (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (hX : ∀ v, IsUnit (X v).det)
    (L S : Submodule (𝓞 K) V) (hL : L.FG) (hS : S.FG) (hsat : IsSat (Formalism.HermitianLatticesTheory.realize b X) L S)
    (hpos : 0 < htQ b X L S) :
    Real.log (htQ b X L S) = Real.log (ht b X L) - Real.log (ht b X S) := by
  have hlat := (place_lattice_structure K V ι b X hX L hL).1
  have hq := ((saturation_basic_properties (𝓞 K) V _ (Formalism.HermitianLatticesTheory.realize b X) L hlat).2.2.2.2.2.2.2 S hsat).2.2
  have hc : Formalism.F.covol (Formalism.F.quot (zl (Formalism.HermitianLatticesTheory.realize b X) L) (zl (Formalism.HermitianLatticesTheory.realize b X) S)) ≠ 0 := by
    intro h0
    rw [htQ, h0, mul_zero] at hpos
    exact lt_irrefl _ hpos
  have h2 : ((2 : ℝ) ^ ((nPl K : ℝ) * ((rkK L : ℝ) - rkK S))) ≠ 0 :=
    (Real.rpow_pos_of_pos (by norm_num) _).ne'
  have h3 : |(NumberField.discr K : ℝ)| ^ (-((rkK L : ℝ) - rkK S) / 2) ≠ 0 :=
    (Real.rpow_pos_of_pos disc_pos _).ne'
  rw [log_ht b X hX L hL, log_ht b X hX S hS, htQ, Real.log_mul (mul_ne_zero h2 h3) hc,
    Real.log_mul h2 h3, Real.log_rpow (by norm_num), Real.log_rpow disc_pos]
  have hq' : Real.log (Formalism.F.covol (Formalism.F.quot (zl (Formalism.HermitianLatticesTheory.realize b X) L)
      (zl (Formalism.HermitianLatticesTheory.realize b X) S))) =
      -(deg (Formalism.HermitianLatticesTheory.realize b X) L - deg (Formalism.HermitianLatticesTheory.realize b X) S) := by
    rw [← hq, Formalism.F.deg, neg_neg]
  rw [hq']
  simp only [logDisc]
  ring

theorem rk_mul_mu [IsTotallyComplex K] (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (L : Submodule (𝓞 K) V) (hL : L.FG) :
    (rkK L : ℝ) * muDef b X L = -Real.log (ht b X L) / (nPl K : ℝ) := by
  by_cases h0 : L = ⊥
  · have hlat := (place_lattice_structure K V ι b X hX L hL).1
    have hd := (saturation_basic_properties (𝓞 K) V _ (Formalism.HermitianLatticesTheory.realize b X) L hlat).2.2.2.2.1
    rw [log_ht b X hX L hL, h0, rkK_bot, hd]
    simp
  · have hpos := (place_lattice_structure K V ι b X hX L hL).2.2
    have hj : (rkK L : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (rkK_ne_zero b L h0)
    have hf : (nPl K : ℝ) ≠ 0 := nPl_ne_zero
    rw [(size_maximal_slope K V ι b X hX L hL h0).2.1, size, Real.log_rpow hpos]
    field_simp

end Mod

end HermitianIdempotentFrameLemmas

open HermitianIdempotentFrameLemmas in
theorem good_bad_split : GoodBadCut := by
  intro K V ι _ _ _ _ _ _ _ _ _ _ b X hX e g N hN hg hee hsa hint
  set Ng := N ⊓ (LinearMap.range e).restrictScalars (𝓞 K) with hNg
  set Nb := N ⊓ (LinearMap.ker e).restrictScalars (𝓞 K) with hNb
  have hNgfg : Ng.FG := Submodule.FG.of_le hN inf_le_left
  have hNbfg : Nb.FG := Submodule.FG.of_le hN inf_le_left
  have hf : (0 : ℝ) < (nPl K : ℝ) := lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm nPl_ne_zero)
  have hg0 : (g : K) ≠ 0 := by exact_mod_cast (by omega : g ≠ 0)
  have hgR : (0 : ℝ) < (g : ℝ) := by exact_mod_cast hg
  refine ⟨rk_add b e g N hg hee hint, ?_, ?_⟩
  · set φ : V →ₗ[K] V := (g : K) • (LinearMap.id - e) with hφ
    set I := N.map (φ.restrictScalars (𝓞 K)) with hI
    have hIfg : I.FG := hN.map _
    obtain ⟨hsat, him⟩ := height_image_formula K V ι V ι b X b X hX hX φ N hN
    rw [ker_cut e g hg hee] at hsat him
    have hrk : rkK Nb = rkK I := rk_map_cut e g N hg hee hint
    have hIle : I ≤ Nb := map_cut_le e g N hee hint
    have hIpos := (place_lattice_structure K V ι b X hX I hIfg).2.2
    have hNbpos := (place_lattice_structure K V ι b X hX Nb hNbfg).2.2

    have h1 : ht b X Nb ≤ ht b X I := by
      by_cases hb : Nb = ⊥
      · have : I = Nb := by rw [hb]; exact le_bot_iff.1 (hb ▸ hIle)
        rw [this]
      · have hI0 : I ≠ ⊥ := by
          intro h0
          obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hb
          have h2 : (g : K) • y ∈ I := smul_mem_map_cut e g N hy
          rw [h0, Submodule.mem_bot] at h2
          exact hy0 ((smul_eq_zero.1 h2).resolve_left hg0)
        exact (size_maximal_slope K V ι b X hX I hIfg hI0).2.2.2.2.2 Nb hIle hNbfg hrk

    have hP0 : 0 ≤ ∏ v, opNormAt b X b X v φ ^ (2 * rkK I) :=
      Finset.prod_nonneg fun v _ => pow_nonneg (norm_nonneg _) _
    have hP : ∏ v, opNormAt b X b X v φ ^ (2 * rkK I) ≤ (g : ℝ) ^ (nPl K * (2 * rkK I)) := by
      calc ∏ v, opNormAt b X b X v φ ^ (2 * rkK I) ≤ ∏ _v : InfinitePlace K, (g : ℝ) ^ (2 * rkK I) :=
            Finset.prod_le_prod (fun v _ => pow_nonneg (norm_nonneg _) _) fun v _ =>
              pow_le_pow_left₀ (norm_nonneg _) (opNormAt_le b X hX e g v hee (hsa v)) _
        _ = (g : ℝ) ^ (nPl K * (2 * rkK I)) := by
            rw [Finset.prod_const, ← pow_mul, nPl, Finset.card_univ, mul_comm]
    have hQpos : 0 < htQ b X N Ng := by
      by_contra h
      have := mul_nonpos_of_nonneg_of_nonpos hP0 (not_lt.1 h)
      linarith
    have h2 : ht b X Nb ≤ (g : ℝ) ^ (nPl K * (2 * rkK I)) * htQ b X N Ng :=
      h1.trans (him.trans (mul_le_mul_of_nonneg_right hP hQpos.le))
    have h3 := Real.log_le_log hNbpos h2
    rw [Real.log_mul (pow_pos hgR _).ne' hQpos.ne', Real.log_pow,
      log_htQ b X hX N Ng hN hNgfg hsat hQpos] at h3
    rw [rk_mul_mu b X hX N hN, rk_mul_mu b X hX Ng hNgfg, rk_mul_mu b X hX Nb hNbfg, hrk]
    push_cast at h3
    have h4 : -Real.log (ht b X N) ≤ -Real.log (ht b X Ng) + -Real.log (ht b X Nb) +
        (nPl K : ℝ) * (2 * (rkK I : ℝ) * Real.log g) := by linarith
    have h5 := div_le_div_of_nonneg_right h4 hf.le
    rw [add_div, add_div, mul_div_cancel_left₀ _ hf.ne'] at h5
    exact h5
  · intro M hM hNM
    by_cases hb : Nb = ⊥
    · rw [hb, rkK_bot]; simp
    · have hNbM : Nb ≤ M := inf_le_left.trans hNM
      have hM0 : M ≠ ⊥ := fun h => hb (le_bot_iff.1 (h ▸ hNbM))
      have hlat := (place_lattice_structure K V ι b X hX M hM).1
      have hmax := ((slope_characterization (𝓞 K) V _ (Formalism.HermitianLatticesTheory.realize b X) M hlat hM0).1
        (muMax (Formalism.HermitianLatticesTheory.realize b X) M)).1 le_rfl Nb hNbM
      have hr0 : rk (Formalism.HermitianLatticesTheory.realize b X) Nb ≠ 0 := fun h =>
        hb (((saturation_basic_properties (𝓞 K) V _ (Formalism.HermitianLatticesTheory.realize b X) M hlat).2.2.2.1 Nb hNbM).1 h)
      have hrpos : (0 : ℝ) < (rk (Formalism.HermitianLatticesTheory.realize b X) Nb : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero hr0
      have hs : slope (Formalism.HermitianLatticesTheory.realize b X) Nb ≤ muMax (Formalism.HermitianLatticesTheory.realize b X) M := by
        change deg (Formalism.HermitianLatticesTheory.realize b X) Nb / (rk (Formalism.HermitianLatticesTheory.realize b X) Nb : ℝ) ≤ _
        rw [div_le_iff₀ hrpos]
        exact hmax
      refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
      unfold muDef muMaxDef
      linarith

end Formalism.ExtensionFiltration
