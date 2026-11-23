import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ConnectionKillsSeries

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory.IntSeries

variable {R : Type} [CommRing R] {k : Type} [CommRing k] [Algebra R k] {σ τ : Type}

theorem intAA_zero : IntAA (R := R) k (0 : MvPowerSeries σ k) := fun n => by
  rw [map_zero]; exact Subring.zero_mem _

theorem intAA_map (f : MvPowerSeries σ R) :
    IntAA (R := R) k (MvPowerSeries.map (algebraMap R k) f) := fun n => by
  rw [coeff_map]; exact ⟨_, rfl⟩

theorem intAA_one : IntAA (R := R) k (1 : MvPowerSeries σ k) := by
  simpa using intAA_map (k := k) (1 : MvPowerSeries σ R)

theorem intAA_X (s : σ) : IntAA (R := R) k (X s : MvPowerSeries σ k) := by
  simpa using intAA_map (k := k) (X s : MvPowerSeries σ R)

theorem intAA_C (r : R) : IntAA (R := R) k (C (algebraMap R k r) : MvPowerSeries σ k) := by
  simpa using intAA_map (k := k) (C r : MvPowerSeries σ R)

theorem intAA_iff_exists_map {f : MvPowerSeries σ k} :
    IntAA (R := R) k f ↔ ∃ g : MvPowerSeries σ R, MvPowerSeries.map (algebraMap R k) g = f := by
  refine ⟨fun h => ?_, fun ⟨g, hg⟩ => hg ▸ intAA_map g⟩
  choose g hg using h
  exact ⟨g, MvPowerSeries.ext fun n => (coeff_map _ _ _).trans (hg n)⟩

theorem intAA_add {f g : MvPowerSeries σ k} (hf : IntAA (R := R) k f) (hg : IntAA (R := R) k g) :
    IntAA (R := R) k (f + g) := fun n => by
  rw [map_add]; exact Subring.add_mem _ (hf n) (hg n)

theorem intAA_neg {f : MvPowerSeries σ k} (hf : IntAA (R := R) k f) :
    IntAA (R := R) k (-f) := fun n => by
  rw [map_neg]; exact Subring.neg_mem _ (hf n)

theorem intAA_sub {f g : MvPowerSeries σ k} (hf : IntAA (R := R) k f) (hg : IntAA (R := R) k g) :
    IntAA (R := R) k (f - g) := fun n => by
  rw [map_sub]; exact Subring.sub_mem _ (hf n) (hg n)

theorem intAA_mul {f g : MvPowerSeries σ k} (hf : IntAA (R := R) k f) (hg : IntAA (R := R) k g) :
    IntAA (R := R) k (f * g) := fun n => by
  classical
  rw [coeff_mul]
  exact Subring.sum_mem _ fun p _ => Subring.mul_mem _ (hf _) (hg _)

theorem intAA_smul (r : R) {f : MvPowerSeries σ k} (hf : IntAA (R := R) k f) :
    IntAA (R := R) k (algebraMap R k r • f) := fun n => by
  rw [map_smul, smul_eq_mul]; exact Subring.mul_mem _ ⟨r, rfl⟩ (hf n)

theorem intAA_pow {f : MvPowerSeries σ k} (hf : IntAA (R := R) k f) (m : ℕ) :
    IntAA (R := R) k (f ^ m) := by
  induction m with
  | zero => simpa using intAA_one
  | succ m ih => rw [pow_succ]; exact intAA_mul ih hf

theorem intAA_sum {ι : Type*} (t : Finset ι) {f : ι → MvPowerSeries σ k}
    (hf : ∀ i ∈ t, IntAA (R := R) k (f i)) : IntAA (R := R) k (∑ i ∈ t, f i) := fun n => by
  rw [map_sum]; exact Subring.sum_mem _ fun i hi => hf i hi n

theorem intAA_prod {ι : Type*} (t : Finset ι) {f : ι → MvPowerSeries σ k}
    (hf : ∀ i ∈ t, IntAA (R := R) k (f i)) : IntAA (R := R) k (∏ i ∈ t, f i) :=
  Finset.prod_induction f (IntAA (R := R) k) (fun _ _ => intAA_mul) intAA_one hf

theorem intAA_pderiv {f : MvPowerSeries σ k} (s : σ) (hf : IntAA (R := R) k f) :
    IntAA (R := R) k (pderiv k s f) := fun n => by
  rw [coeff_pderiv]
  exact Subring.mul_mem _ (hf _) (Subring.add_mem _ (natCast_mem _ _) (Subring.one_mem _))

theorem intAA_subst_of_hasSubst {a : σ → MvPowerSeries τ k} (ha : HasSubst a)
    {f : MvPowerSeries σ k} (hai : ∀ s, IntAA (R := R) k (a s)) (hf : IntAA (R := R) k f) :
    IntAA (R := R) k (MvPowerSeries.subst a f) := fun n => by
  rw [coeff_subst ha]
  refine finsum_induction (· ∈ (algebraMap R k).range) (Subring.zero_mem _)
    (fun _ _ => Subring.add_mem _) fun d => ?_
  rw [smul_eq_mul]
  exact Subring.mul_mem _ (hf d) (intAA_prod _ (fun s _ => intAA_pow (hai s) _) n)

theorem intAA_subst [Finite σ] {a : σ → MvPowerSeries τ k} {f : MvPowerSeries σ k}
    (ha : ∀ s, constantCoeff (a s) = 0) (hai : ∀ s, IntAA (R := R) k (a s))
    (hf : IntAA (R := R) k f) : IntAA (R := R) k (MvPowerSeries.subst a f) :=
  intAA_subst_of_hasSubst (hasSubst_of_constantCoeff_zero ha) hai hf

theorem main : ∀ (R : Type) [CommRing R] (k : Type) [CommRing k] [Algebra R k],
  (∀ (σ : Type) (f g : MvPowerSeries σ k), IntAA (R := R) k f → IntAA (R := R) k g → IntAA (R := R) k (f + g) ∧ IntAA (R := R) k (f - g) ∧ IntAA (R := R) k (f * g)) ∧
  (∀ (σ : Type) (f : MvPowerSeries σ k) (s : σ), IntAA (R := R) k f → IntAA (R := R) k (pderiv k s f)) ∧
  (∀ (σ : Type) (f : MvPowerSeries σ R), IntAA (R := R) k (MvPowerSeries.map (algebraMap R k) f)) ∧
  (∀ (σ τ : Type) [Finite σ] (a : σ → MvPowerSeries τ k) (f : MvPowerSeries σ k), (∀ s, constantCoeff (a s) = 0) → (∀ s, IntAA (R := R) k (a s)) → IntAA (R := R) k f → IntAA (R := R) k (MvPowerSeries.subst a f)) :=
  fun _ _ _ _ _ =>
    ⟨fun _ _ _ hf hg => ⟨intAA_add hf hg, intAA_sub hf hg, intAA_mul hf hg⟩,
      fun _ _ s hf => intAA_pderiv s hf, fun _ f => intAA_map f,
      fun _ _ _ _ _ ha hai hf => intAA_subst ha hai hf⟩

end GlobalTheory.IntSeries
