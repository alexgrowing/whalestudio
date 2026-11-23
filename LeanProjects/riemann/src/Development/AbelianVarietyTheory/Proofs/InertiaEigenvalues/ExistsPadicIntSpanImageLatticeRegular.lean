import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZlSpanImageContinuousRepFinite
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKLim

theorem exists_zl_span_lattice_reads : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] (a : ℕ) (r : Γ →* GL (Fin a) (Om l)), Continuous r → ∃ (d : ℕ) (ρ : Γ →* GL (Fin d) ℤ_[l]) (b : Fin d → Matrix (Fin a) (Fin a) (Om l)) (e : Fin d → ℤ_[l]), Continuous ρ ∧ Reads ρ r b e ∧ LinearIndependent ℚ_[l] b ∧ ∀ i, ∃ f : Γ →₀ ℤ_[l], b i = f.sum fun h c => zOm l c • (r h).val := by
  intro l _ Γ _ _ _ _ a r hr
  classical
  have hz : ∀ c : ℤ_[l], zOm l c = algebraMap ℤ_[l] (Om l) c := fun c =>
    (IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (Om l) c).symm
  have hsm : ∀ (c : ℤ_[l]) (x : Matrix (Fin a) (Fin a) (Om l)), c • x = zOm l c • x := by
    intro c x; ext i j; simp [Matrix.smul_apply, Algebra.smul_def, hz]
  have hsq : ∀ (c : ℤ_[l]) (x : Matrix (Fin a) (Fin a) (Om l)), c • x = (c : ℚ_[l]) • x := by
    intro c x; rw [hsm]; ext i j; simp [Matrix.smul_apply, Algebra.smul_def, zOm]
  let v : Γ → Matrix (Fin a) (Fin a) (Om l) := fun h => (r h).val
  let M : Submodule ℤ_[l] (Matrix (Fin a) (Fin a) (Om l)) := Submodule.span ℤ_[l] (Set.range v)

  obtain ⟨t, ht⟩ := GlobalTheory.zl_span_image_finite l Γ a r hr
  have hfg : M.FG := by
    refine ⟨t.image v, le_antisymm ?_ ?_⟩
    · rw [Finset.coe_image]; exact Submodule.span_mono (Set.image_subset_range _ _)
    · rw [Submodule.span_le]
      rintro _ ⟨h, rfl⟩
      obtain ⟨f', hf't, hf'⟩ := ht (Finsupp.single h 1)
      have hvh : v h = f'.sum fun h c => ((algebraMap ℚ_[l] (PadicAlgCl l)) (c : ℚ_[l])) •
          ((r h : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l)) := by
        rw [← hf', Finsupp.sum_single_index (by simp)]
        simp [v]
      rw [SetLike.mem_coe, hvh]
      refine Submodule.sum_mem _ fun k hk => ?_
      have : ((algebraMap ℚ_[l] (PadicAlgCl l)) (f' k : ℚ_[l])) •
          ((r k : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l)) = f' k • v k := by
        rw [hsm]; rfl
      refine (show _ ∈ _ from ?_)
      beta_reduce
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image_of_mem v (hf't hk))))
  haveI : Module.Finite ℤ_[l] M := Module.Finite.iff_fg.mpr hfg
  haveI : Module.IsTorsionFree ℤ_[l] M := Module.IsTorsionFree.of_smul_eq_zero fun c m h => by
    have h' : (c : ℚ_[l]) • (m : Matrix (Fin a) (Fin a) (Om l)) = 0 := by
      rw [← hsq]; exact congrArg Subtype.val h
    rcases smul_eq_zero.1 h' with h0 | h0
    · left; exact Subtype.ext h0
    · right; exact Subtype.ext h0
  haveI : Module.Free ℤ_[l] M := Module.free_of_finite_type_torsion_free'
  let d := Module.finrank ℤ_[l] M
  let B : Module.Basis (Fin d) ℤ_[l] M := Module.finBasis ℤ_[l] M

  have hstab : ∀ (g : Γ) (x : Matrix (Fin a) (Fin a) (Om l)), x ∈ M → v g * x ∈ M := by
    intro g x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨h, rfl⟩ := hy
      exact Submodule.subset_span ⟨g * h, by simp [v, map_mul]⟩
    | zero => simp
    | add y z _ _ hy hz => rw [Matrix.mul_add]; exact M.add_mem hy hz
    | smul c y _ hy => rw [Matrix.mul_smul]; exact M.smul_mem c hy
  let Lm : Γ → Module.End ℤ_[l] M := fun g =>
    { toFun := fun x => ⟨v g * x, hstab g x x.2⟩
      map_add' := fun x y => Subtype.ext (Matrix.mul_add _ _ _)
      map_smul' := fun c x => Subtype.ext (Matrix.mul_smul _ _ _) }
  let L : Γ →* Module.End ℤ_[l] M :=
    { toFun := Lm
      map_one' := LinearMap.ext fun x => Subtype.ext (by simp [Lm, v])
      map_mul' := fun g h => LinearMap.ext fun x => Subtype.ext (by simp [Lm, v, map_mul, Matrix.mul_assoc]) }
  let ρ₀ : Γ →* Matrix (Fin d) (Fin d) ℤ_[l] :=
    (LinearMap.toMatrixAlgEquiv B).toAlgHom.toRingHom.toMonoidHom.comp L
  let ρ : Γ →* GL (Fin d) ℤ_[l] := ρ₀.toHomUnits
  have hρ : ∀ g i j, (ρ g).val i j = B.repr (Lm g (B j)) i := by
    intro g i j
    exact LinearMap.toMatrixAlgEquiv_apply B (L g) i j
  let b : Fin d → Matrix (Fin a) (Fin a) (Om l) := fun i => (B i : Matrix (Fin a) (Fin a) (Om l))
  have hrepr : ∀ x : M, ∑ i, zOm l (B.repr x i) • b i = x := by
    intro x
    have := congrArg Subtype.val (B.sum_repr x)
    rw [Submodule.coe_sum] at this
    simpa [b, hsm] using this
  have h1M : (1 : Matrix (Fin a) (Fin a) (Om l)) ∈ M := Submodule.subset_span ⟨1, by simp [v]⟩
  let e : Fin d → ℤ_[l] := fun i => B.repr ⟨1, h1M⟩ i
  have hreads : Reads ρ r b e := by
    refine ⟨fun g j => ?_, ?_⟩
    · simp_rw [hρ]
      rw [hrepr]
      rfl
    · exact hrepr ⟨1, h1M⟩

  have hliZ : LinearIndependent ℤ_[l] b := B.linearIndependent.map' M.subtype (Submodule.ker_subtype M)
  have hli : LinearIndependent ℚ_[l] b := (LinearIndependent.iff_fractionRing ℤ_[l] ℚ_[l]).1 hliZ
  refine ⟨d, ρ, b, e, ?_, hreads, hli, fun i => ?_⟩
  rotate_left
  · obtain ⟨f, hf⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).1 (B i).2
    refine ⟨f, ?_⟩
    show (B i : Matrix (Fin a) (Fin a) (Om l)) = _
    rw [← hf]
    simp [Finsupp.sum, hsm, v]

  let Wq := Submodule.span ℚ_[l] (Set.range b)
  let Bq : Module.Basis (Fin d) ℚ_[l] Wq := Module.Basis.span hli
  haveI : FiniteDimensional ℚ_[l] Wq := Module.Finite.of_basis Bq
  have hmemW : ∀ x : M, (x : Matrix (Fin a) (Fin a) (Om l)) ∈ Wq := by
    intro x
    rw [← hrepr x]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [← hsm, hsq]
    exact Wq.smul_mem _ (Submodule.subset_span ⟨i, rfl⟩)
  have hcoord : ∀ x : M, ∀ i, ((B.repr x i : ℤ_[l]) : ℚ_[l]) = Bq.repr ⟨x, hmemW x⟩ i := by
    intro x i
    have hx : (⟨x, hmemW x⟩ : Wq) = ∑ k, ((B.repr x k : ℤ_[l]) : ℚ_[l]) • Bq k := by
      apply Subtype.ext
      rw [Submodule.coe_sum]
      conv_lhs => rw [← hrepr x]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Submodule.coe_smul, Module.Basis.span_apply, ← hsm, hsq]
    rw [hx, Module.Basis.repr_sum_self]
  have hcv : Continuous v := Units.continuous_val.comp hr
  have hval : Continuous fun g => (ρ g).val := by
    refine continuous_matrix fun i j => ?_
    have : (fun g => (((ρ g).val i j : ℤ_[l]) : ℚ_[l])) = fun g => Bq.coord i ⟨v g * b j, hmemW (Lm g (B j))⟩ := by
      funext g
      rw [hρ, hcoord]
      rfl
    have hcq : Continuous (fun g => (((ρ g).val i j : ℤ_[l]) : ℚ_[l])) := by
      rw [this]
      refine (LinearMap.continuous_of_finiteDimensional (Bq.coord i)).comp ?_
      exact (hcv.mul continuous_const).subtype_mk _
    exact continuous_induced_rng.2 hcq
  refine Units.continuous_iff.2 ⟨hval, ?_⟩
  have : (fun g => ((ρ g)⁻¹ : GL (Fin d) ℤ_[l]).val) = (fun g => (ρ g).val) ∘ fun g => g⁻¹ := by
    funext g; simp [map_inv]
  rw [this]
  exact hval.comp continuous_inv

end GlobalTheory.BKLim
