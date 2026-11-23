import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.AinfActionTiltFixedOfFrobeniusRelation
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsAlgebraicVectorSpanningSubspace
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.MemIK
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LaWDDefs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedIsCrysAndJumpEqZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ConclusionFinite
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.WeilDeligne GlobalTheory.GalOfCusp GlobalTheory.HeckeGal GlobalTheory.LocLanglands GlobalTheory.Published UpperTheory.V.W
set_option synthInstance.maxHeartbeats 400000

open Module in

private theorem exists_int_basis {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [CompactSpace G]
    {V : Type} [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V]
    [IsModuleTopology ℚ_[l] V] (ρ : Representation ℚ_[l] G V) (hρ : ∀ x, Continuous fun g => ρ g x) :
    ∃ (n : ℕ) (e : Basis (Fin n) ℚ_[l] V), ∀ g i j, ‖e.repr (ρ g (e j)) i‖ ≤ 1 := by
  classical
  letI : Module ℤ_[l] V := Module.compHom V (algebraMap ℤ_[l] ℚ_[l])
  haveI : IsScalarTower ℤ_[l] ℚ_[l] V := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let e₀ := Module.finBasis ℚ_[l] V
  let Λ : Submodule ℤ_[l] V := Submodule.span ℤ_[l] (Set.range fun p : G × Fin (finrank ℚ_[l] V) => ρ p.1 (e₀ p.2))
  have hc : Continuous fun g : G => (fun i j => e₀.repr (ρ g (e₀ j)) i) :=
    continuous_pi fun i => continuous_pi fun j =>
      (IsModuleTopology.continuous_of_linearMap (e₀.coord i)).comp (hρ _)
  obtain ⟨C, hC⟩ := (isCompact_range hc).isBounded.exists_norm_le
  obtain ⟨c, hc0, hcC⟩ : ∃ c : ℚ_[l], c ≠ 0 ∧ C ≤ ‖c‖ := by
    obtain ⟨c, hc⟩ := NormedField.exists_lt_norm ℚ_[l] (max C 0)
    exact ⟨c, norm_pos_iff.1 (lt_of_le_of_lt (le_max_right _ _) hc), ((le_max_left _ _).trans hc.le)⟩
  have hle : Λ ≤ Submodule.span ℤ_[l] (Set.range fun i => c • e₀ i) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨⟨g, j⟩, rfl⟩
    change ρ g (e₀ j) ∈ _
    rw [← e₀.sum_repr (ρ g (e₀ j))]
    refine Submodule.sum_mem _ fun i _ => ?_
    have h1 : ‖e₀.repr (ρ g (e₀ j)) i / c‖ ≤ 1 := by
      rw [norm_div]
      refine div_le_one_of_le₀ (le_trans ?_ hcC) (norm_nonneg _)
      exact ((norm_le_pi_norm _ j).trans (norm_le_pi_norm (fun i j => e₀.repr (ρ g (e₀ j)) i) i)).trans
        (hC _ ⟨g, rfl⟩)
    let z : ℤ_[l] := ⟨_, h1⟩
    have h2 : e₀.repr (ρ g (e₀ j)) i • e₀ i = z • c • e₀ i := by
      change _ = (e₀.repr (ρ g (e₀ j)) i / c) • c • e₀ i
      rw [smul_smul, div_mul_cancel₀ _ hc0]
    rw [h2]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  haveI : Submodule.IsLattice ℚ_[l] Λ :=
    { fg := (Submodule.fg_span (Set.finite_range _)).of_le hle
      span_eq_top := by
        rw [eq_top_iff, ← e₀.span_eq]
        refine Submodule.span_mono ?_
        rintro _ ⟨i, rfl⟩
        exact Submodule.subset_span ⟨(1, i), by simp⟩ }
  haveI : Module.Free ℤ_[l] Λ := Submodule.IsLattice.free ℚ_[l] Λ
  haveI : Module.Finite ℤ_[l] Λ := Submodule.IsLattice.finite ℚ_[l] Λ
  let b := Module.finBasis ℤ_[l] Λ
  have hst : ∀ g, ∀ x ∈ Λ, ρ g x ∈ Λ := by
    intro g x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨⟨h, j⟩, rfl⟩ := hx
      exact Submodule.subset_span ⟨(g * h, j), by simp⟩
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact Λ.add_mem hx hy
    | smul a x _ hx => rw [LinearMap.map_smul_of_tower]; exact Λ.smul_mem a hx
  refine ⟨_, b.extendOfIsLattice ℚ_[l], fun g i j => ?_⟩
  have h1 : ρ g (b.extendOfIsLattice ℚ_[l] j) =
      ∑ k, ((b.repr ⟨_, hst g _ (b j).2⟩ k : ℤ_[l]) : ℚ_[l]) • b.extendOfIsLattice ℚ_[l] k := by
    have := congrArg Λ.subtype (b.sum_repr ⟨_, hst g _ (b j).2⟩)
    rw [map_sum] at this
    simp only [Basis.extendOfIsLattice_apply]
    exact this.symm
  rw [h1, Basis.repr_sum_self]
  exact PadicInt.norm_le_one _

private theorem map_iterFrob {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] [CharP R p] (k : ℕ)
    (x : WittVector p R) :
    WittVector.map (iterateFrobenius R p (k + 1)) x =
      WittVector.frobenius (WittVector.map (iterateFrobenius R p k) x) := by
  rw [WittVector.frobenius_eq_map_frobenius]
  ext i
  simp [iterateFrobenius_def, frobenius_def, pow_succ, pow_mul]

open TensorProduct GlobalTheory.Pst in

private theorem phiV_pow {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) {LL : Type} [Field LL]
    [Algebra ℚ_[l] LL] {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
    (k : ℕ) (v : V) (w : Ainf l) :
    (phiV P LL V ^ k) (v ⊗ₜ[ℚ_[l]] (Polynomial.C (AI.ιA w) : Bst P)) =
      v ⊗ₜ[ℚ_[l]] (Polynomial.C (AI.ιA (WittVector.map (iterateFrobenius _ l k) w)) : Bst P) := by
  induction k with
  | zero =>
    rw [pow_zero, Module.End.one_apply]
    congr 3
    ext i
    simp
  | succ k ih => rw [pow_succ', Module.End.mul_apply, ih, phiV_tmul, phiSt_C, map_iterFrob, AI.ιA_φ]

open GlobalTheory.Pst in
private theorem coe_phiD_pow {l : ℕ} [Fact l.Prime] (P : LocPrime l) {LL : Type} [Field LL]
    [Algebra ℚ_[l] LL] {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
    {K : FinExt l} (ρ : Representation LL ↥(GK K) V) (k : ℕ) (x : ↥(Dpst P ρ)) :
    ((phiD P ρ ^ k) x).1 = (phiV P LL V ^ k) x.1 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, coe_phiD, ih]

open TensorProduct GlobalTheory.Pst GlobalTheory.UnramifiedRep GlobalTheory.UnramifiedCrys in
private theorem period {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (Ti : LocTied l P AI)
    {K K' : FinExt l} (hKK : K.1 ≤ K'.1) {LL : Type} [Field LL] [Algebra ℚ_[l] LL] {V : Type} [AddCommGroup V]
    [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V] [FiniteDimensional ℚ_[l] V] [Nontrivial V]
    [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] (m : ↥(GK K) → LL) (ρ : Representation LL ↥(GK K) V)
    (hρ : ∀ g v, ρ g v = m g • v) (hc : ∀ x, Continuous fun g => ρ g x)
    (hI : ∀ g : ↥(GK K), (g : GQ l) ∈ GK K' → (g : GQ l) ∈ (MaximalUnramifiedExtension l).fixingSubgroup → m g = 1) :
    ∃ x : ↥(Dpst P ρ), x ≠ 0 ∧ ∀ (g : ↥(GK K)) (a b : ℕ),
      (∀ c : ↥(MaximalUnramifiedExtension l), (g : GQ l) (((frobUr l ^ b) c : ↥(MaximalUnramifiedExtension l)) : Om l) = (((frobUr l ^ a) c : ↥(MaximalUnramifiedExtension l)) : Om l)) →
      actD P ρ g ((phiD P ρ ^ b) x) = m g • (phiD P ρ ^ a) x := by
  classical
  have := compactSpace_GK K'
  let ρ' : Representation LL ↥(GK K') V := resTo ρ hKK
  let ρq : Representation ℚ_[l] ↥(GK K') V :=
    { toFun := fun g => (ρ' g).restrictScalars ℚ_[l]
      map_one' := by rw [map_one]; rfl
      map_mul' := fun g h => by rw [map_mul]; rfl }
  have hinc : Continuous (Subgroup.inclusion (GK_le hKK)) := continuous_inclusion (GK_le hKK)
  have hcont : ∀ x, Continuous fun g => ρ' g x := fun x => (hc x).comp hinc
  obtain ⟨n, e, hint⟩ := exists_int_basis ρq hcont
  obtain ⟨M, hM⟩ := exists_matrixHom ρ' e hint
  obtain ⟨W, hW, hWg, hWc⟩ := UpperTheory.exists_algebraic_vector_spanning_subspace P AI K' M
    (continuous_pi fun i => continuous_pi fun j => continuous_induced_rng.2 (by
      have h := (IsModuleTopology.continuous_of_linearMap (e.coord i)).comp (hcont (e j))
      exact h.congr fun g => (hM g i j).symm))
    (fun g hg => by
      have h : ∀ x, ρ' g x = x := fun x => by
        refine (hρ _ x).trans ?_
        rw [hI (Subgroup.inclusion (GK_le hKK) g) g.2 ((UpperTheory.V.Loc.memIK K' g).1 hg), one_smul]
      rw [← map_one M]
      ext i j
      apply PadicInt.ext
      rw [hM, hM, h, map_one, Module.End.one_apply])
  haveI : Nontrivial P.R.B := nontrivial_B P
  haveI : Nontrivial (Ainf l) := AI.ιA.domain_nontrivial
  haveI : Nonempty (Fin n) := e.index_nonempty
  obtain ⟨i0, j0, hij⟩ : ∃ i j, W i j ≠ 0 := by
    by_contra hc
    push Not at hc
    have : W = 0 := Matrix.ext hc
    rw [this, Matrix.det_zero] at hW
    exact not_isUnit_zero hW
  let x : V ⊗[ℚ_[l]] Bst P := ∑ i, e i ⊗ₜ (Polynomial.C (AI.ιA (W i j0)) : Bst P)
  have hx : x ∈ Dpst P ρ := ⟨K', hKK, (mem_Dst P _).2 fun g => by
    have h1 : ∀ i, AI.ιA (W i j0) = ∑ k, e.repr (ρ' g (e k)) i • P.actQ g (AI.ιA (W k j0)) := fun i => by
      conv_lhs => rw [← hWg g, Matrix.mul_apply, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_mul, Matrix.map_apply, Matrix.map_apply, ιA_zlW AI Ti, hM, ← AI.ιA_act, Algebra.smul_def]
      rfl
    have h2 : x = ∑ i, ∑ k, (e.repr (ρ' g (e k)) i • e i) ⊗ₜ[ℚ_[l]]
        (Polynomial.C (P.actQ g (AI.ιA (W k j0))) : Bst P) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [h1 i, map_sum, tmul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← Polynomial.smul_C, smul_tmul]
    conv_rhs => rw [h2, Finset.sum_comm]
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [stRep_tmul, actSt_C, ← sum_tmul, e.sum_repr]⟩
  refine ⟨⟨x, hx⟩, fun h0 => hij ?_, fun g a b hg => Subtype.ext ?_⟩
  · have h1 : x = 0 := congrArg Subtype.val h0
    have h2 := congrArg (fun y => TensorProduct.lid ℚ_[l] _ (LinearMap.rTensor (Bst P) (e.coord i0) y)) h1
    simp only [x, map_sum, LinearMap.rTensor_tmul, lid_tmul, Module.Basis.coord_apply, Module.Basis.repr_self,
      Finsupp.single_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true, map_zero,
      Polynomial.C_eq_zero] at h2
    exact AI.ιA_inj (h2.trans (map_zero _).symm)
  · rw [coe_actD, Submodule.coe_smul, coe_phiD_pow, coe_phiD_pow]
    simp only [x, map_sum, phiV_pow, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [stRep_tmul, actSt_C, hρ, smul_tmul', ← AI.ιA_act]
    congr 3
    ext k
    obtain ⟨r, hr, hy⟩ := hWc i j0 k
    exact UpperTheory.Ainf_action_tilt_fixed_of_frobenius_relation P AI g a b hg _ r hr hy

theorem UpperTheory.exists_dpst_frobenius_eigenvector_of_character :
    ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K K' L : FinExt l), K.1 ≤ K'.1 → ∀ (m : ↥(GK K) →* (↥L.1)ˣ) (ρ : Representation ↥L.1 ↥(GK K) (Fin 1 → ↥L.1)), (∀ g v, ρ g v = (m g : ↥L.1) • v) → Continuous (fun g => ((m g : ↥L.1) : Om l)) → (∀ g : ↥(GK K), (g : GQ l) ∈ GK K' → (g : GQ l) ∈ (MaximalUnramifiedExtension l).fixingSubgroup → m g = 1) → ∃ x : ↥(GlobalTheory.Pst.Dpst P ρ), x ≠ 0 ∧ ∀ (g : ↥(GK K)) (a b : ℕ), (∀ c : ↥(MaximalUnramifiedExtension l), (g : GQ l) (((GlobalTheory.Pst.frobUr l ^ b) c : ↥(MaximalUnramifiedExtension l)) : Om l) = (((GlobalTheory.Pst.frobUr l ^ a) c : ↥(MaximalUnramifiedExtension l)) : Om l)) → GlobalTheory.Pst.actD P ρ g ((GlobalTheory.Pst.phiD P ρ ^ b) x) = (m g : ↥L.1) • (GlobalTheory.Pst.phiD P ρ ^ a) x := by
  intro l _ P AI Ti K K' L hKK m ρ hρ hm hI
  have := L.2
  have : IsModuleTopology ℚ_[l] (Fin 1 → ↥L.1) := isModuleTopologyOfFiniteDimensional
  have h1 : Continuous fun g => (m g : ↥L.1) := continuous_induced_rng.2 hm
  exact period P AI Ti hKK (fun g => (m g : ↥L.1)) ρ hρ
    (fun x => (h1.smul (continuous_const (y := x))).congr fun g => (hρ g x).symm)
    (fun g h h' => by rw [hI g h h', Units.val_one])
