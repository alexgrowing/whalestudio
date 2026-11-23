import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsHermRingRat
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct

set_option linter.unusedSectionVars false

noncomputable section

namespace GlobalTheory.CompanionTheory.KFin.AE

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {v : HeightOneSpectrum (𝓞 F)}

theorem sigR_inclR (e : E) : sigR (Fv F v) σ (inclR (Fv F v) e) = inclR (Fv F v) (σ e) := rfl

theorem hR_apply (x y : Fin n → Fv F v ⊗[F] E) :
    hR (Fv F v) σ J x y = ∑ i, ∑ j, sigR (Fv F v) σ (x i) * inclR (Fv F v) (J i j) * y j := rfl

theorem sigR_sigR (hσ : ∀ e, σ (σ e) = e) (y : Fv F v ⊗[F] E) : sigR (Fv F v) σ (sigR (Fv F v) σ y) = y := by
  induction y with
  | zero => simp
  | tmul a b => simp [sigR, hσ]
  | add a b ha hb => rw [map_add, map_add, ha, hb]

theorem sigR_hR (hσ : ∀ e, σ (σ e) = e) (hJ : ∀ i j, σ (J j i) = J i j) (x y : Fin n → Fv F v ⊗[F] E) :
    sigR (Fv F v) σ (hR (Fv F v) σ J x y) = hR (Fv F v) σ J y x := by
  rw [hR_apply, hR_apply, Finset.sum_comm]
  simp only [map_sum, map_mul, sigR_sigR hσ, sigR_inclR]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← hJ i j]
  ring

theorem hR_mem (hJv : ∀ i j, inclR (Fv F v) (J i j) ∈ intLoc F E v) {x y : Fin n → Fv F v ⊗[F] E}
    (hx : ∀ i, x i ∈ intLoc F E v) (hy : ∀ i, y i ∈ intLoc F E v) : hR (Fv F v) σ J x y ∈ intLoc F E v := by
  rw [hR_apply]
  exact sum_mem fun i _ => sum_mem fun j _ => mul_mem (mul_mem (sigR_mem_intLoc σ (hx i)) (hJv i j)) (hy j)

theorem hR_single (i : Fin n) (z : Fin n → Fv F v ⊗[F] E) :
    hR (Fv F v) σ J (Pi.single i 1) z = (J.map (inclR (F := F) (Fv F v)) *ᵥ z) i := by
  rw [hR_apply, Finset.sum_eq_single i]
  · simp [Matrix.mulVec, dotProduct]
  · intro j _ hj
    simp [Pi.single_apply, hj]
  · simp

theorem mem_of_hR_single (hdet : J.det ≠ 0) (hJi : ∀ i j, inclR (Fv F v) (J⁻¹ i j) ∈ intLoc F E v)
    {z : Fin n → Fv F v ⊗[F] E} (hz : ∀ i, hR (Fv F v) σ J (Pi.single i 1) z ∈ intLoc F E v) (a : Fin n) :
    z a ∈ intLoc F E v := by
  have e : J⁻¹.map (inclR (F := F) (Fv F v)) * J.map (inclR (F := F) (Fv F v)) = 1 := by
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hdet), Matrix.map_one _ (map_zero _) (map_one _)]
  have hz' : z = J⁻¹.map (inclR (F := F) (Fv F v)) *ᵥ (J.map (inclR (F := F) (Fv F v)) *ᵥ z) := by
    rw [Matrix.mulVec_mulVec, e, Matrix.one_mulVec]
  obtain ⟨w, hw⟩ : ∃ w, w = J.map (inclR (F := F) (Fv F v)) *ᵥ z := ⟨_, rfl⟩
  have hw' : ∀ j, w j ∈ intLoc F E v := fun j => by rw [hw, ← hR_single (σ := σ)]; exact hz j
  rw [← hw] at hz'
  rw [hz']
  simp only [Matrix.mulVec, dotProduct]
  exact sum_mem fun j _ => mul_mem (hJi a j) (hw' j)

end GlobalTheory.CompanionTheory.KFin.AE

namespace GlobalTheory.CompanionTheory.KFin.AE

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {v : HeightOneSpectrum (𝓞 F)}

theorem single_mem_latLoc_std (i : Fin n) :
    (Pi.single i 1 : Fin n → Fv F v ⊗[F] E) ∈ latLoc F (stdLattice E n) v := by
  refine mem_latLoc_stdLattice.2 fun j => ?_
  by_cases h : j = i
  · subst h; simp only [Pi.single_eq_same]; exact one_mem _
  · rw [Pi.single_eq_of_ne h]; exact zero_mem _

theorem sum_single_smul (y : Fin n → Fv F v ⊗[F] E) : ∑ i, y i • (Pi.single i 1 : Fin n → Fv F v ⊗[F] E) = y := by
  funext j
  simp [Finset.sum_apply, Pi.single_apply]

theorem isLat_latLoc_std : IsLat (intLoc F E v) (latLoc F (stdLattice E n) v) := by
  constructor
  · refine Submodule.fg_def.2 ⟨Set.range fun i => (Pi.single i 1 : Fin n → Fv F v ⊗[F] E), Set.finite_range _,
      le_antisymm ?_ ?_⟩
    · rw [Submodule.span_le]
      rintro y ⟨i, rfl⟩
      exact single_mem_latLoc_std i
    · intro y hy
      have h := mem_latLoc_stdLattice.1 hy
      rw [← sum_single_smul y]
      refine sum_mem fun i _ => ?_
      have : y i • (Pi.single i 1 : Fin n → Fv F v ⊗[F] E) =
          (⟨y i, h i⟩ : intLoc F E v) • (Pi.single i 1 : Fin n → Fv F v ⊗[F] E) := rfl
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))
  · rw [eq_top_iff]
    intro y _
    rw [← sum_single_smul y]
    exact sum_mem fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (single_mem_latLoc_std i))

end GlobalTheory.CompanionTheory.KFin.AE

namespace GlobalTheory.CompanionTheory.KFin.AE

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {v : HeightOneSpectrum (𝓞 F)}

theorem hR_self_eq (hσ : ∀ e, σ (σ e) = e) (hJ : ∀ i j, σ (J j i) = J i j) (x : Fin n → Fv F v ⊗[F] E) :
    hR (Fv F v) σ J x x = inclR (Fv F v) (2⁻¹ : E) * hR (Fv F v) σ J x x +
      sigR (Fv F v) σ (inclR (Fv F v) (2⁻¹ : E) * hR (Fv F v) σ J x x) := by
  have hs : σ (2⁻¹ : E) = 2⁻¹ := by rw [map_inv₀, map_ofNat]
  rw [map_mul, sigR_hR hσ hJ, sigR_inclR, hs, ← add_mul, ← map_add]
  have : (2⁻¹ : E) + 2⁻¹ = 1 := by norm_num
  rw [this, map_one, one_mul]

theorem isMaxEven_isAdapted_std (hσ : ∀ e, σ (σ e) = e) (hJ : IsHermND σ J)
    (hJv : ∀ i j, inclR (Fv F v) (J i j) ∈ intLoc F E v) (hJi : ∀ i j, inclR (Fv F v) (J⁻¹ i j) ∈ intLoc F E v)
    (h2 : inclR (Fv F v) (2⁻¹ : E) ∈ intLoc F E v) {r : ℕ} (x y : Fin r → Fin n → Fv F v ⊗[F] E)
    (hx : ∀ i a, x i a ∈ intLoc F E v) (hy : ∀ i a, y i a ∈ intLoc F E v) :
    IsMaxEven (sigR (Fv F v) σ) (intLoc F E v) (hR (Fv F v) σ J) (latLoc F (stdLattice E n) v) ∧
      IsAdapted (intLoc F E v) (hR (Fv F v) σ J) x y (latLoc F (stdLattice E n) v) := by
  have hint : ∀ a ∈ latLoc F (stdLattice E n) v, ∀ b ∈ latLoc F (stdLattice E n) v,
      hR (Fv F v) σ J a b ∈ intLoc F E v := fun a ha b hb =>
    hR_mem hJv (mem_latLoc_stdLattice.1 ha) (mem_latLoc_stdLattice.1 hb)
  refine ⟨⟨isLat_latLoc_std, ⟨hint, fun a ha => ⟨_, mul_mem h2 (hint a ha a ha), hR_self_eq hσ hJ.1 a⟩⟩, ?_⟩, ?_⟩
  · intro L' hL' hle z hz
    refine mem_latLoc_stdLattice.2 (mem_of_hR_single (σ := σ) hJ.2 hJi fun i => ?_)
    exact hL'.1 _ (hle (single_mem_latLoc_std i)) _ hz
  · intro z
    simp only [mem_latLoc_stdLattice]
    have hc : ∀ (c d : Fin r → Fv F v ⊗[F] E) (a : Fin n),
        (z - ∑ i, c i • x i - ∑ i, d i • y i) a = z a - ∑ i, c i * x i a - ∑ i, d i * y i a := by
      intro c d a
      simp [Finset.sum_apply]
    constructor
    · intro hz
      have h1 : ∀ i, hR (Fv F v) σ J (x i) z ∈ intLoc F E v := fun i => hR_mem hJv (hx i) hz
      have h3 : ∀ i, hR (Fv F v) σ J (y i) z ∈ intLoc F E v := fun i => hR_mem hJv (hy i) hz
      refine ⟨h1, h3, fun a => ?_⟩
      rw [hc]
      exact sub_mem (sub_mem (hz a) (sum_mem fun i _ => mul_mem (h3 i) (hx i a)))
        (sum_mem fun i _ => mul_mem (h1 i) (hy i a))
    · rintro ⟨h1, h3, hw⟩ a
      have := hw a
      rw [hc] at this
      have e : z a = (z a - ∑ i, hR (Fv F v) σ J (y i) z * x i a - ∑ i, hR (Fv F v) σ J (x i) z * y i a) +
          ∑ i, hR (Fv F v) σ J (y i) z * x i a + ∑ i, hR (Fv F v) σ J (x i) z * y i a := by ring
      rw [e]
      exact add_mem (add_mem this (sum_mem fun i _ => mul_mem (h3 i) (hx i a)))
        (sum_mem fun i _ => mul_mem (h1 i) (hy i a))

end GlobalTheory.CompanionTheory.KFin.AE

namespace GlobalTheory.CompanionTheory.KFin.AE

theorem exists_lattice_maxEven_adapted : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}, IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → ∃ (L : Submodule (𝓞 E) (Fin n → E)) (_ : Submodule.IsLattice E L), ∀ᶠ v in Filter.cofinite, IsMaxEven (sigR (Fv F v) σ) (intLoc F E v) (hR (Fv F v) σ J) (latLoc F L v) ∧ IsAdapted (intLoc F E v) (hR (Fv F v) σ J) (colV v X) (colV v Y) (latLoc F L v) := by
  intro F E _ _ _ _ _ σ n J r X Y hcm hJ _hW
  have hσ : ∀ e, σ (σ e) = e := fun e => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    exact τ.injective (by rw [hcm.2.2.2, hcm.2.2.2, star_star])
  refine ⟨stdLattice E n, isLattice_stdLattice, ?_⟩
  filter_upwards [Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => eventually_one_tmul_mem_intLoc (F := F) (J i j),
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => eventually_one_tmul_mem_intLoc (F := F) (J⁻¹ i j),
    eventually_one_tmul_mem_intLoc (F := F) (2⁻¹ : E),
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun a => eventually_one_tmul_mem_intLoc (F := F) (X a i),
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun a => eventually_one_tmul_mem_intLoc (F := F) (Y a i)]
    with v h1 h2 h3 h4 h5
  exact isMaxEven_isAdapted_std hσ hJ h1 h2 h3 (colV v X) (colV v Y) h4 h5

end GlobalTheory.CompanionTheory.KFin.AE
