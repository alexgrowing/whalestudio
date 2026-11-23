import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LogPeriodLimit
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsIsChart
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsotropicSublatticeCovolumePositiveStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RiemannLatticeEigenProjectionStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsEigenComponentPolynomialStatement

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
open GlobalTheory.CompanionTheory.Ar.RiemannLimit GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.IsoSplit

theorem det_fromBlocks_factor {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m m ℂ) (X : Matrix m n ℂ) (Y : Matrix n m ℂ) (M : Matrix n n ℂ) :
    (Matrix.fromBlocks A (A * X) (Y * A) (Y * A * X + M)).det = A.det * M.det := by
  have h : Matrix.fromBlocks A (A * X) (Y * A) (Y * A * X + M) =
      Matrix.fromBlocks 1 0 Y 1 * Matrix.fromBlocks A 0 0 M * Matrix.fromBlocks 1 X 0 1 := by
    simp [Matrix.fromBlocks_multiply]
  rw [h, Matrix.det_mul, Matrix.det_mul]
  simp [Matrix.det_fromBlocks_zero₁₂, Matrix.det_fromBlocks_zero₂₁]

section Riem

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]
  (R : RiemLat E g Λ)

theorem ip_add_right (x y y' : Fin g → ℂ) : R.ip x (y + y') = R.ip x y + R.ip x y' := by
  simp [RiemLat.ip, add_dotProduct]

theorem ip_smul_right (x : Fin g → ℂ) (c : ℂ) (y : Fin g → ℂ) : R.ip x (c • y) = c * R.ip x y := by
  simp [RiemLat.ip, smul_dotProduct]

theorem ip_add_left (x x' y : Fin g → ℂ) : R.ip (x + x') y = R.ip x y + R.ip x' y := by
  simp [RiemLat.ip, star_add, mulVec_add, dotProduct_add]

theorem ip_smul_left (c : ℂ) (x y : Fin g → ℂ) : R.ip (c • x) y = starRingEnd ℂ c * R.ip x y := by
  simp [RiemLat.ip, star_smul, mulVec_smul, dotProduct_smul]

theorem ip_zero_left (y : Fin g → ℂ) : R.ip 0 y = 0 := by
  simp [RiemLat.ip]

theorem ip_zero_right (x : Fin g → ℂ) : R.ip x 0 = 0 := by
  simp [RiemLat.ip]

theorem ip_sum_right {ι : Type} (t : Finset ι) (x : Fin g → ℂ) (f : ι → Fin g → ℂ) :
    R.ip x (∑ i ∈ t, f i) = ∑ i ∈ t, R.ip x (f i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [ip_zero_right]
  | insert i t hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, ip_add_right, ih]

theorem ip_sum_left {ι : Type} (t : Finset ι) (f : ι → Fin g → ℂ) (y : Fin g → ℂ) :
    R.ip (∑ i ∈ t, f i) y = ∑ i ∈ t, R.ip (f i) y := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [ip_zero_left]
  | insert i t hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, ip_add_left, ih]

theorem conj_ip (x y : Fin g → ℂ) : starRingEnd ℂ (R.ip y x) = R.ip x y := by
  show star (x ⬝ᵥ R.Hm *ᵥ star y) = y ⬝ᵥ R.Hm *ᵥ star x
  rw [← star_dotProduct_star, star_mulVec, star_star, R.herm.eq, dotProduct_mulVec]

theorem ip_symm_zero {x y : Fin g → ℂ} (h : R.ip x y = 0) : R.ip y x = 0 := by
  rw [← conj_ip R y x, h, map_zero]

theorem gram_append_of_frame {r k : ℕ} (f : Fin r → Fin g → ℂ) (q p' : Fin k → Fin g → ℂ)
    (l : Matrix (Fin k) (Fin r) ℂ) (M : Matrix (Fin k) (Fin k) ℂ)
    (hq : ∀ c, q c = p' c + ∑ b, l c b • f b) (ho : ∀ c a, R.ip (f a) (p' c) = 0)
    (hM : ∀ c c', R.ip (p' c) (q c') = M c c') :
    (R.gram (Fin.append f q)).det = (R.gram f).det * M.det := by
  set A := R.gram f with hA
  set Y : Matrix (Fin k) (Fin r) ℂ := l.map (starRingEnd ℂ) with hY
  have e2 : ∀ a c, R.ip (f a) (q c) = (A * lᵀ) a c := by
    intro a c
    rw [hq c, ip_add_right, ho, zero_add, ip_sum_right, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [ip_smul_right, mul_comm]
    rfl
  have e3 : ∀ c a, R.ip (q c) (f a) = (Y * A) c a := by
    intro c a
    rw [hq c, ip_add_left, ip_symm_zero R (ho c a), zero_add, ip_sum_left, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [ip_smul_left]
    rfl
  have e4 : ∀ c c', R.ip (q c) (q c') = (Y * A * lᵀ + M) c c' := by
    intro c c'
    have h : R.ip (q c) (q c') = R.ip (p' c) (q c') + ∑ b, starRingEnd ℂ (l c b) * R.ip (f b) (q c') := by
      conv_lhs => rw [hq c]
      rw [ip_add_left, ip_sum_left]
      simp only [ip_smul_left]
    rw [h, hM, Matrix.add_apply, Matrix.mul_assoc, Matrix.mul_apply, add_comm]
    congr 1
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [e2]
    rfl
  have hblock : (R.gram (Fin.append f q)).submatrix finSumFinEquiv finSumFinEquiv =
      Matrix.fromBlocks A (A * lᵀ) (Y * A) (Y * A * lᵀ + M) := by
    ext (a | a) (b | b)
    · simp [RiemLat.gram, hA]
    · simpa [RiemLat.gram] using e2 a b
    · simpa [RiemLat.gram] using e3 a b
    · simpa [RiemLat.gram] using e4 a b
  rw [← Matrix.det_submatrix_equiv_self finSumFinEquiv, hblock, det_fromBlocks_factor]

theorem exists_eigLin (s : 𝓞 E →+* ℂ) :
    ∃ L : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), ∀ x, L x = eigComp R.B s x := by
  obtain ⟨-, -, h1, -, -⟩ := GlobalTheory.T.riemann_lattice_eigen_projection E g Λ Unit R
  have hl := (h1 s).2.2.1
  have h0 : eigComp R.B s 0 = 0 := by simpa using hl (-1) 0 0
  exact ⟨{ toFun := eigComp R.B s
           map_add' := fun x y => by simpa using hl 1 x y
           map_smul' := fun c x => by simpa [h0] using hl c x 0 }, fun _ => rfl⟩

omit [IsCMField E] in

theorem emb_injective (s : 𝓞 E →+* ℂ) : Function.Injective s := by
  have hc : (RingHom.ker s).comap (algebraMap ℤ (𝓞 E)) = ⊥ := by
    rw [RingHom.comap_ker]
    exact (RingHom.injective_iff_ker_eq_bot _).1 (RingHom.injective_int _)
  exact (RingHom.injective_iff_ker_eq_bot s).2 (Ideal.eq_bot_of_comap_eq_bot hc)

def extEmb (s : 𝓞 E →+* ℂ) : E →+* ℂ := IsFractionRing.lift (emb_injective s)

omit [IsCMField E] in
theorem extEmb_apply (s : 𝓞 E →+* ℂ) (a : 𝓞 E) : extEmb s (algebraMap (𝓞 E) E a) = s a :=
  IsFractionRing.lift_algebraMap (emb_injective s) a

omit [IsCMField E] in

theorem exists_ext (s : 𝓞 E →+* ℂ) : ∃ t : E →+* ℂ, t.comp (algebraMap (𝓞 E) E) = s :=
  ⟨extEmb s, RingHom.ext (extEmb_apply s)⟩

theorem comp_ne {s : 𝓞 E →+* ℂ} {t t₀ : E →+* ℂ} (h₀ : t₀.comp (algebraMap (𝓞 E) E) = s) (h : t ≠ t₀) :
    t.comp (algebraMap (𝓞 E) E) ≠ s := fun e =>
  h (IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (e.trans h₀.symm))

theorem eigComp_adjoint (s : 𝓞 E →+* ℂ) (x y : Fin g → ℂ) :
    R.ip x (eigComp R.B s y) = R.ip (eigComp R.B s x) y := by
  obtain ⟨-, -, h1, h2, h3⟩ := GlobalTheory.T.riemann_lattice_eigen_projection E g Λ Unit R
  obtain ⟨t₀, ht₀⟩ := exists_ext s
  have hl : R.ip x (eigComp R.B s y) = R.ip (eigComp R.B s x) (eigComp R.B s y) := by
    calc R.ip x (eigComp R.B s y)
        = R.ip (∑ t : E →+* ℂ, eigComp R.B (t.comp (algebraMap (𝓞 E) E)) x) (eigComp R.B s y) := by rw [h2 x]
      _ = ∑ t : E →+* ℂ, R.ip (eigComp R.B (t.comp (algebraMap (𝓞 E) E)) x) (eigComp R.B s y) := ip_sum_left R _ _ _
      _ = R.ip (eigComp R.B (t₀.comp (algebraMap (𝓞 E) E)) x) (eigComp R.B s y) :=
        Finset.sum_eq_single t₀ (fun t _ ht => h3 _ _ (comp_ne ht₀ ht) _ ((h1 _).1 x) _ ((h1 _).1 y))
          (fun h => absurd (Finset.mem_univ _) h)
      _ = R.ip (eigComp R.B s x) (eigComp R.B s y) := by rw [ht₀]
  have hr : R.ip (eigComp R.B s x) y = R.ip (eigComp R.B s x) (eigComp R.B s y) := by
    calc R.ip (eigComp R.B s x) y
        = R.ip (eigComp R.B s x) (∑ t : E →+* ℂ, eigComp R.B (t.comp (algebraMap (𝓞 E) E)) y) := by rw [h2 y]
      _ = ∑ t : E →+* ℂ, R.ip (eigComp R.B s x) (eigComp R.B (t.comp (algebraMap (𝓞 E) E)) y) := ip_sum_right R _ _ _
      _ = R.ip (eigComp R.B s x) (eigComp R.B (t₀.comp (algebraMap (𝓞 E) E)) y) :=
        Finset.sum_eq_single t₀ (fun t _ ht => h3 _ _ (comp_ne ht₀ ht).symm _ ((h1 _).1 x) _ ((h1 _).1 y))
          (fun h => absurd (Finset.mem_univ _) h)
      _ = R.ip (eigComp R.B s x) (eigComp R.B s y) := by rw [ht₀]
  rw [hl, hr]

theorem eigComp_mem_span (I : Submodule (𝓞 E) Λ) (s : 𝓞 E →+* ℂ) {u : Fin g → ℂ}
    (hu : u ∈ Submodule.span ℂ (R.P '' (I : Set Λ))) :
    eigComp R.B s u ∈ Submodule.span ℂ (R.P '' (I : Set Λ)) := by
  have hst : ∀ a, R.B a u ∈ Submodule.span ℂ (R.P '' (I : Set Λ)) := by
    intro a
    have hle : (Submodule.span ℂ (R.P '' (I : Set Λ))).map (R.B a) ≤ Submodule.span ℂ (R.P '' (I : Set Λ)) := by
      rw [Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨v, hv, rfl⟩, rfl⟩
      exact Submodule.subset_span ⟨a • v, I.smul_mem a hv, R.act a v⟩
    exact hle (Submodule.mem_map_of_mem hu)
  obtain ⟨c, hc⟩ := GlobalTheory.T.exists_eigenComponent_polynomial E s
  rw [(hc (Fin g → ℂ) R.B).1 u]
  exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (hst a)

theorem eigComp_P_mem_span (s : 𝓞 E →+* ℂ) {r : ℕ} (y : Fin r → Λ) {z : Λ}
    (hz : z ∈ Submodule.span (𝓞 E) (Set.range y)) :
    eigComp R.B s (R.P z) ∈ Submodule.span ℂ (Set.range fun a => eigComp R.B s (R.P (y a))) := by
  obtain ⟨-, -, h1, -, -⟩ := GlobalTheory.T.riemann_lattice_eigen_projection E g Λ Unit R
  obtain ⟨L, hL⟩ := exists_eigLin R s
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    exact Submodule.subset_span ⟨a, rfl⟩
  | zero =>
    rw [map_zero, ← hL, map_zero]
    exact Submodule.zero_mem _
  | add x x' _ _ hx hx' =>
    rw [map_add, ← hL, map_add, hL, hL]
    exact Submodule.add_mem _ hx hx'
  | smul a x _ hx =>
    rw [R.act, (h1 s).2.2.2 a]
    exact Submodule.smul_mem _ _ hx

theorem eigComp_span_le (I : Submodule (𝓞 E) Λ) (s : 𝓞 E →+* ℂ) {r : ℕ} (y : Fin r → Λ)
    (hidx : (Submodule.span (𝓞 E) (Set.range y)).toAddSubgroup.relIndex I.toAddSubgroup ≠ 0)
    {u : Fin g → ℂ} (hu : u ∈ Submodule.span ℂ (R.P '' (I : Set Λ))) :
    eigComp R.B s u ∈ Submodule.span ℂ (Set.range fun a => eigComp R.B s (R.P (y a))) := by
  obtain ⟨L, hL⟩ := exists_eigLin R s
  set W := Submodule.span ℂ (Set.range fun a => eigComp R.B s (R.P (y a))) with hW
  have hle : Submodule.span ℂ (R.P '' (I : Set Λ)) ≤ W.comap L := by
    rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨n, hn, -, hmem⟩ := AddSubgroup.exists_nsmul_mem_of_relIndex_ne_zero hidx (a := x) hx
    have h1 : eigComp R.B s (R.P (n • x)) ∈ W := eigComp_P_mem_span R s y hmem.1
    rw [map_nsmul, ← hL, map_nsmul] at h1
    have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
    have h2 : L (R.P x) = (n : ℂ)⁻¹ • (n • L (R.P x)) := by
      rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hn', one_smul]
    show L (R.P x) ∈ W
    rw [h2]
    exact W.smul_mem _ h1
  have := hle hu
  rwa [Submodule.mem_comap, hL] at this

theorem ip_eigComp_eq_zero (I : Submodule (𝓞 E) Λ) (s : 𝓞 E →+* ℂ) {z : Fin g → ℂ}
    (hz : ∀ x ∈ I, R.ip (R.P x) z = 0) {u : Fin g → ℂ}
    (hu : u ∈ Submodule.span ℂ (R.P '' (I : Set Λ))) : R.ip u (eigComp R.B s z) = 0 := by
  have hspan : ∀ v ∈ Submodule.span ℂ (R.P '' (I : Set Λ)), R.ip v z = 0 := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨w, hw, rfl⟩ := hx
      exact hz w hw
    | zero => exact ip_zero_left R z
    | add x x' _ _ hx hx' => rw [ip_add_left, hx, hx', add_zero]
    | smul c x _ hx => rw [ip_smul_left, hx, mul_zero]
  rw [eigComp_adjoint]
  exact hspan _ (eigComp_mem_span R I s hu)

end Riem

theorem gram_append_split : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (R : RiemLat E g Λ) (I : Submodule (𝓞 E) Λ) (s₀ : 𝓞 E →+* ℂ) (r k : ℕ) (y : Fin r → Λ) (q p : Fin k → Fin g → ℂ), (∀ a, y a ∈ I) → (Submodule.span (𝓞 E) (Set.range y)).toAddSubgroup.relIndex I.toAddSubgroup ≠ 0 → (∀ c, q c ∈ eigSp R.B s₀) → (∀ c, p c - q c ∈ Submodule.span ℂ (R.P '' (I : Set Λ))) → (∀ c, ∀ x ∈ I, R.ip (R.P x) (p c) = 0) → (R.gram (Fin.append (fun a => eigComp R.B s₀ (R.P (y a))) q)).det = (R.gram fun a => eigComp R.B s₀ (R.P (y a))).det * (Matrix.of fun c c' => R.ip (p c) (q c')).det := by
  intro E _ _ _ g Λ _ _ R I s₀ r k y q p hy hidx hq hpq hp
  classical
  obtain ⟨-, -, h1, -, -⟩ := GlobalTheory.T.riemann_lattice_eigen_projection E g Λ Unit R
  obtain ⟨L, hL⟩ := exists_eigLin R s₀
  have hqfix : ∀ c, eigComp R.B s₀ (q c) = q c := fun c => (h1 s₀).2.1 _ (hq c)
  have hdiff : ∀ c, q c - eigComp R.B s₀ (p c) ∈
      Submodule.span ℂ (Set.range fun a => eigComp R.B s₀ (R.P (y a))) := by
    intro c
    have h := eigComp_span_le R I s₀ y hidx (hpq c)
    have e : q c - eigComp R.B s₀ (p c) = -eigComp R.B s₀ (p c - q c) := by
      rw [← hL (p c - q c), map_sub, hL, hL, hqfix, neg_sub]
    rw [e]
    exact Submodule.neg_mem _ h
  choose l hl using fun c => (Submodule.mem_span_range_iff_exists_fun ℂ).1 (hdiff c)
  refine gram_append_of_frame R _ q (fun c => eigComp R.B s₀ (p c)) (Matrix.of l) _ ?_ ?_ ?_
  · intro c
    simp only [Matrix.of_apply]
    rw [hl c, add_sub_cancel]
  · intro c a
    exact ip_eigComp_eq_zero R I s₀ (hp c)
      (eigComp_mem_span R I s₀ (Submodule.subset_span ⟨y a, hy a, rfl⟩))
  · intro c c'
    rw [← eigComp_adjoint, hqfix]
    rfl

end GlobalTheory.CompanionTheory.Ar.Cusp.IsoSplit
