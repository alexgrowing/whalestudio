import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RiemannLatticeEigenProjectionStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsotropicEigencomponentConjugateFormStatement

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.SchurGram

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree
  GroundTheory.Heights₂.Heights.Regular

section Proj

variable {V O : Type} [AddCommGroup V] [Module ℂ V] [CommRing O]

theorem mem_eigSp_iff (B : O →+* Module.End ℂ V) (s : O →+* ℂ) (y : V) :
    y ∈ eigSp B s ↔ ∀ a, B a y = s a • y := by
  simp [eigSp, Submodule.mem_iInf, sub_eq_zero]

theorem exists_proj (B : O →+* Module.End ℂ V) (W : Submodule ℂ V) (hW : ∀ a, ∀ y ∈ W, B a y ∈ W)
    (s : O →+* ℂ) (F : Finset (O →+* ℂ)) (hF : s ∉ F) :
    ∃ L : V →ₗ[ℂ] V, (∀ y ∈ W, L y ∈ W) ∧ (∀ y ∈ eigSp B s, L y = y) ∧
      ∀ t ∈ F, ∀ y ∈ eigSp B t, L y = 0 := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨LinearMap.id, fun y hy => hy, fun _ _ => rfl, by simp⟩
  | insert t F ht ih =>
    obtain ⟨L, hLW, hLs, hLF⟩ := ih (fun h => hF (Finset.mem_insert_of_mem h))
    have hts : t ≠ s := fun h => hF (h ▸ Finset.mem_insert_self _ _)
    obtain ⟨a, ha⟩ : ∃ a, t a ≠ s a := by
      by_contra h
      push Not at h
      exact hts (RingHom.ext h)
    have hc : s a - t a ≠ 0 := sub_ne_zero.2 ha.symm
    let T : V →ₗ[ℂ] V := (s a - t a)⁻¹ • ((B a : V →ₗ[ℂ] V) - t a • (LinearMap.id : V →ₗ[ℂ] V))
    have hT : ∀ y, T y = (s a - t a)⁻¹ • (B a y - t a • y) := fun y => rfl
    refine ⟨L ∘ₗ T, ?_, ?_, ?_⟩
    · intro y hy
      rw [LinearMap.comp_apply, hT]
      exact hLW _ (W.smul_mem _ (W.sub_mem (hW a y hy) (W.smul_mem _ hy)))
    · intro y hy
      have e : T y = y := by
        rw [hT, (mem_eigSp_iff B s y).1 hy a, ← sub_smul, smul_smul, inv_mul_cancel₀ hc, one_smul]
      rw [LinearMap.comp_apply, e, hLs y hy]
    · intro t' ht' y hy
      have e : T y = ((s a - t a)⁻¹ * (t' a - t a)) • y := by
        rw [hT, (mem_eigSp_iff B t' y).1 hy a, ← sub_smul, smul_smul]
      rw [LinearMap.comp_apply, e, map_smul]
      rcases Finset.mem_insert.1 ht' with rfl | h
      · simp
      · rw [hLF t' h y hy, smul_zero]

end Proj

section Riem

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]
  (R : RiemLat E g Λ)

theorem ip_add_right (x y y' : Fin g → ℂ) : R.ip x (y + y') = R.ip x y + R.ip x y' := by
  simp [RiemLat.ip, add_dotProduct]

theorem ip_sub_right (x y y' : Fin g → ℂ) : R.ip x (y - y') = R.ip x y - R.ip x y' := by
  simp [RiemLat.ip, sub_dotProduct]

theorem ip_smul_right (x : Fin g → ℂ) (c : ℂ) (y : Fin g → ℂ) : R.ip x (c • y) = c * R.ip x y := by
  simp [RiemLat.ip, smul_dotProduct]

theorem ip_sub_left (x x' y : Fin g → ℂ) : R.ip (x - x') y = R.ip x y - R.ip x' y := by
  simp [RiemLat.ip, star_sub, mulVec_sub, dotProduct_sub]

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

theorem eq_zero_of_ip_self (y : Fin g → ℂ) (h : R.ip y y = 0) : y = 0 := by
  by_contra hy
  have := R.pos y hy
  rw [show y ⬝ᵥ R.Hm *ᵥ star y = R.ip y y from rfl, h] at this
  simp at this

theorem gram_det_ne_zero {r : ℕ} (w : Fin r → Fin g → ℂ) (hw : LinearIndependent ℂ w) : (R.gram w).det ≠ 0 := by
  intro h
  obtain ⟨c, hc, hAc⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h
  have h1 : ∀ a, R.ip (w a) (∑ b, c b • w b) = 0 := fun a => by
    have e := congrFun hAc a
    rw [ip_sum_right]
    simp only [ip_smul_right]
    simpa [mulVec, dotProduct, RiemLat.gram, mul_comm] using e
  have h2 : R.ip (∑ b, c b • w b) (∑ b, c b • w b) = 0 := by
    rw [ip_sum_left]
    simp only [ip_smul_left, h1, mul_zero, Finset.sum_const_zero]
  exact hc (funext (Fintype.linearIndependent_iff.mp hw c (eq_zero_of_ip_self R _ h2)))

theorem gram_append_det {r k : ℕ} (w : Fin r → Fin g → ℂ) (x : Fin k → Fin g → ℂ) (hw : LinearIndependent ℂ w) :
    ∃ M : Matrix (Fin r) (Fin k) ℂ,
      (∀ b j, R.ip (w b) (x j - ∑ a, M a j • w a) = 0) ∧
      (R.gram (Fin.append w x)).det =
        (R.gram w).det * (R.gram fun j => x j - ∑ a, M a j • w a).det := by
  classical
  have hdet : IsUnit (R.gram w).det := isUnit_iff_ne_zero.2 (gram_det_ne_zero R w hw)
  set A := R.gram w with hA
  let _ := Matrix.invertibleOfIsUnitDet A hdet
  let Bm : Matrix (Fin r) (Fin k) ℂ := Matrix.of fun a j => R.ip (w a) (x j)
  let C : Matrix (Fin k) (Fin r) ℂ := Matrix.of fun i b => R.ip (x i) (w b)
  let D := R.gram x
  let M := A⁻¹ * Bm
  have hAM : A * M = Bm := Matrix.mul_nonsing_inv_cancel_left _ _ hdet
  have horth : ∀ b j, R.ip (w b) (x j - ∑ a, M a j • w a) = 0 := by
    intro b j
    have e := congrFun (congrFun hAM b) j
    rw [Matrix.mul_apply] at e
    have h2 : ∑ a, M a j * R.ip (w b) (w a) = R.ip (w b) (x j) := by
      simpa [mul_comm, A, RiemLat.gram, Bm] using e
    rw [ip_sub_right, ip_sum_right]
    simp only [ip_smul_right]
    rw [h2, sub_self]
  refine ⟨M, horth, ?_⟩
  have hblock : (R.gram (Fin.append w x)).submatrix finSumFinEquiv finSumFinEquiv =
      Matrix.fromBlocks A Bm C D := by
    ext (a | a) (b | b) <;> simp [RiemLat.gram, Bm, C, D, A]
  rw [← Matrix.det_submatrix_equiv_self finSumFinEquiv, hblock, Matrix.det_fromBlocks₁₁,
    Matrix.invOf_eq_nonsing_inv]
  congr 2
  ext i j
  have e1 : (D - C * A⁻¹ * Bm) i j = R.ip (x i) (x j) - ∑ a, M a j * R.ip (x i) (w a) := by
    rw [Matrix.mul_assoc, Matrix.sub_apply, Matrix.mul_apply]
    simp [D, C, RiemLat.gram, M, mul_comm]
  have e2 : R.ip (x i - ∑ a, M a i • w a) (x j - ∑ a, M a j • w a) =
      R.ip (x i) (x j) - ∑ a, M a j * R.ip (x i) (w a) := by
    rw [ip_sub_left, ip_sum_left]
    simp only [ip_smul_left, horth, mul_zero, Finset.sum_const_zero, sub_zero]
    rw [ip_sub_right, ip_sum_right]
    simp only [ip_smul_right]
  rw [e1]
  exact e2.symm

theorem exists_eigLin (s : 𝓞 E →+* ℂ) :
    ∃ L : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), ∀ x, L x = eigComp R.B s x := by
  obtain ⟨-, -, h1, -, -⟩ := GlobalTheory.T.riemann_lattice_eigen_projection E g Λ Unit R
  have hl := (h1 s).2.2.1
  have h0 : eigComp R.B s 0 = 0 := by simpa using hl (-1) 0 0
  exact ⟨{ toFun := eigComp R.B s
           map_add' := fun x y => by simpa using hl 1 x y
           map_smul' := fun c x => by simpa [h0] using hl c x 0 }, fun _ => rfl⟩

theorem eigComp_mem (W : Submodule ℂ (Fin g → ℂ)) (hW : ∀ a, ∀ y ∈ W, R.B a y ∈ W) (s : 𝓞 E →+* ℂ)
    {y : Fin g → ℂ} (hy : y ∈ W) : eigComp R.B s y ∈ W := by
  classical
  obtain ⟨-, -, h1, h2, -⟩ := GlobalTheory.T.riemann_lattice_eigen_projection E g Λ Unit R
  obtain ⟨Ls, hLs⟩ := exists_eigLin R s
  obtain ⟨L, hLW, hLid, hLF⟩ := exists_proj R.B W hW s
    ((Finset.univ.image fun t : E →+* ℂ => t.comp (algebraMap (𝓞 E) E)).erase s) (Finset.notMem_erase _ _)
  have key : ∀ t : E →+* ℂ, ∀ x ∈ eigSp R.B (t.comp (algebraMap (𝓞 E) E)), L x = Ls x := by
    intro t x hx
    by_cases ht : t.comp (algebraMap (𝓞 E) E) = s
    · rw [ht] at hx
      rw [hLid x hx, hLs, (h1 s).2.1 x hx]
    · rw [hLF _ (Finset.mem_erase.2 ⟨ht, Finset.mem_image_of_mem _ (Finset.mem_univ t)⟩) x hx]
      obtain ⟨a, ha⟩ : ∃ a, (t.comp (algebraMap (𝓞 E) E)) a ≠ s a := by
        by_contra h
        push Not at h
        exact ht (RingHom.ext h)
      have e1 := (h1 s).2.2.2 a x
      rw [(mem_eigSp_iff _ _ _).1 hx a, ← hLs, ← hLs, map_smul] at e1
      have e2 : ((t.comp (algebraMap (𝓞 E) E)) a - s a) • Ls x = 0 := by rw [sub_smul, e1, sub_self]
      exact ((smul_eq_zero.1 e2).resolve_left (sub_ne_zero.2 ha)).symm
  have e : L y = Ls y := by
    calc L y = L (∑ t : E →+* ℂ, eigComp R.B (t.comp (algebraMap (𝓞 E) E)) y) := by rw [h2 y]
      _ = Ls (∑ t : E →+* ℂ, eigComp R.B (t.comp (algebraMap (𝓞 E) E)) y) := by
        rw [map_sum, map_sum]
        exact Finset.sum_congr rfl fun t _ => key t _ ((h1 _).1 y)
      _ = Ls y := by rw [h2 y]
  rw [← hLs, ← e]
  exact hLW y hy

end Riem

theorem gram_append_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g g' : ℕ) (Λ Λ' : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] [AddCommGroup Λ'] [Module (𝓞 E) Λ'] (R : RiemLat E g Λ) (R' : RiemLat E g' Λ') (q : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)) (I : Submodule (𝓞 E) Λ) (s : 𝓞 E →+* ℂ) (r k : ℕ) (v : Fin r → Λ) (x : Fin k → Fin g → ℂ), IsIsoSub R.form I → IsNzFamily I r v → LinearMap.ker q = Submodule.span ℂ (R.P '' I) → (∀ y z, (∀ u ∈ I, R.ip (R.P u) y = 0) → R'.ip (q y) (q z) = R.ip y z) → (∀ j, x j ∈ eigSp R.B s) → (R.gram (Fin.append (fun a => eigComp R.B s (R.P (v a))) x)).det = (R.gram (fun a => eigComp R.B s (R.P (v a)))).det * (R'.gram (fun j => q (x j))).det := by
  intro E _ _ _ g g' Λ Λ' _ _ _ _ R R' q I s r k v x hI hv hq hR hx
  classical
  obtain ⟨-, hvI, hvli, hidx⟩ := hv
  obtain ⟨-, -, h1, h2, h3⟩ := GlobalTheory.T.riemann_lattice_eigen_projection E g Λ Unit R
  have hwli : LinearIndependent ℂ fun a => eigComp R.B s (R.P (v a)) :=
    (GlobalTheory.T.isotropic_eigencomponent_conjugate_form E g Λ Unit R I hI s).2 r v hvI hvli
  obtain ⟨M, hz, hdet⟩ := gram_append_det R _ x hwli
  rw [hdet]
  congr 2
  obtain ⟨Ls, hLs⟩ := exists_eigLin R s
  set w : Fin r → Fin g → ℂ := fun a => eigComp R.B s (R.P (v a)) with hw
  set z : Fin k → Fin g → ℂ := fun j => x j - ∑ a, M a j • w a with hzdef
  have hstable : ∀ a, ∀ y ∈ Submodule.span ℂ (R.P '' I), R.B a y ∈ Submodule.span ℂ (R.P '' I) := by
    intro a y hy
    have hle : (Submodule.span ℂ (R.P '' I)).map (R.B a) ≤ Submodule.span ℂ (R.P '' I) := by
      rw [Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨u, hu, rfl⟩, rfl⟩
      exact Submodule.subset_span ⟨a • u, I.smul_mem a hu, R.act a u⟩
    exact hle (Submodule.mem_map_of_mem hy)
  have hwq : ∀ a, q (w a) = 0 := fun a => by
    have : w a ∈ LinearMap.ker q := by
      rw [hq]
      exact eigComp_mem R _ hstable s (Submodule.subset_span ⟨v a, hvI a, rfl⟩)
    exact this
  have hqz : ∀ j, q (z j) = q (x j) := fun j => by
    simp [hzdef, map_sub, map_sum, hwq]
  have hzeig : ∀ j, z j ∈ eigSp R.B s := fun j =>
    Submodule.sub_mem _ (hx j) (Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ ((h1 s).1 _))
  have hspan : ∀ u ∈ I, ∀ j, R.ip (eigComp R.B s (R.P u)) (z j) = 0 := by
    intro u hu j
    obtain ⟨n, hn, -, hmem⟩ := AddSubgroup.exists_nsmul_mem_of_relIndex_ne_zero hidx (a := u) hu
    have hmem' : n • u ∈ Submodule.span (𝓞 E) (Set.range v) := hmem.1
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 E)).1 hmem'
    have e1 : (n : ℂ) • eigComp R.B s (R.P u) = ∑ a, s (c a) • w a := by
      have e2 := (h1 s).2.2.2 (n : 𝓞 E) (R.P u)
      rw [← R.act, Nat.cast_smul_eq_nsmul, ← hc, map_natCast] at e2
      rw [← e2, map_sum, ← hLs, map_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [R.act, hLs, (h1 s).2.2.2, hw]
    have e3 : starRingEnd ℂ (n : ℂ) * R.ip (eigComp R.B s (R.P u)) (z j) = 0 := by
      rw [← ip_smul_left, e1, ip_sum_left]
      simp only [ip_smul_left]
      exact Finset.sum_eq_zero fun a _ => by rw [hz a j, mul_zero]
    refine (mul_eq_zero.1 e3).resolve_left ?_
    simpa using hn.ne'
  have horth : ∀ j, ∀ u ∈ I, R.ip (R.P u) (z j) = 0 := by
    intro j u hu
    rw [← h2 (R.P u), ip_sum_left]
    refine Finset.sum_eq_zero fun t _ => ?_
    by_cases ht : t.comp (algebraMap (𝓞 E) E) = s
    · rw [ht]
      exact hspan u hu j
    · exact h3 _ s ht _ ((h1 _).1 _) _ (hzeig j)
  ext i j
  simp only [RiemLat.gram, Matrix.of_apply]
  rw [← hqz i, ← hqz j]
  exact (hR _ _ (horth i)).symm

end GlobalTheory.CompanionTheory.Ar.Cusp.SchurGram
