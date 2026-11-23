import Mathlib
import Formalism.PeriodIntegrals.CdHaarScale

noncomputable section

open MeasureTheory MeasureTheory.Measure Matrix

namespace PI.UnitaryGroupMassFormula.CdHaarScale.Main

instance instTGUpqT (P Q : ℕ) : IsTopologicalGroup (Formalism.BasicNotions.UpqT P Q) :=
  inferInstanceAs (IsTopologicalGroup (Formalism.UG.Upq P Q))

instance instBorelUpqT (P Q : ℕ) : BorelSpace (Formalism.BasicNotions.UpqT P Q) := ⟨rfl⟩

def rmap {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] (e : m ≃ n) :
    Matrix m m ℂ →* Matrix n n ℂ where
  toFun := reindex e e
  map_one' := map_one (reindexAlgEquiv ℂ ℂ e)
  map_mul' := map_mul (reindexAlgEquiv ℂ ℂ e)

theorem rmap_apply {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] (e : m ≃ n)
    (M : Matrix m m ℂ) : rmap e M = reindex e e M := rfl

theorem reindex_conj {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (e : m ≃ n) (M J : Matrix m m ℂ) :
    reindex e e (Mᴴ * J * M) = (reindex e e M)ᴴ * reindex e e J * reindex e e M := by
  simp only [Matrix.reindex_apply, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv]

def transp {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] (e : m ≃ n)
    (H : Subgroup (Matrix m m ℂ)ˣ) (K : Subgroup (Matrix n n ℂ)ˣ)
    (hHK : ∀ x : (Matrix m m ℂ)ˣ, x ∈ H ↔ Units.map (rmap e) x ∈ K) : H ≃ₜ* K where
  toFun g := ⟨Units.map (rmap e) g.1, (hHK g.1).1 g.2⟩
  invFun a := ⟨Units.map (rmap e.symm) a.1, by
    rw [hHK]
    have : Units.map (rmap e) (Units.map (rmap e.symm) a.1) = a.1 := by
      ext1; simp [rmap_apply]
    rw [this]; exact a.2⟩
  left_inv g := by
    apply Subtype.ext; apply Units.ext
    simp [rmap_apply]
  right_inv a := by
    apply Subtype.ext; apply Units.ext
    simp [rmap_apply]
  map_mul' g h := Subtype.ext (map_mul (Units.map (rmap e)) g.1 h.1)
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (Units.continuous_map (f := rmap e) (continuous_id.matrix_reindex e e)).comp
      continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact (Units.continuous_map (f := rmap e.symm) (continuous_id.matrix_reindex e.symm e.symm)).comp
      continuous_subtype_val

theorem cT_eq {m : Type} (M : Matrix m m ℂ) : Formalism.UG.cT (starRingEnd ℂ) M = Mᴴ := by
  ext i j
  simp [Formalism.UG.cT, Matrix.conjTranspose_apply]

theorem reindex_Jpq {P Q n : ℕ} {ε : Fin n → Bool} (e : Fin P ⊕ Fin Q ≃ Fin n)
    (h1 : ∀ i, ε (e (Sum.inl i)) = true) (h2 : ∀ j, ε (e (Sum.inr j)) = false) :
    reindex e e (Formalism.UG.Jpq P Q) = Formalism.REAL.Jm ε := by
  ext i j
  obtain ⟨a, rfl⟩ := e.surjective i
  obtain ⟨b, rfl⟩ := e.surjective j
  rcases a with a | a <;> rcases b with b | b <;>
    simp [Formalism.UG.Jpq, Formalism.REAL.Jm, Matrix.diagonal_apply, Matrix.one_apply, h1, h2] <;>
    (try split_ifs <;> simp)

theorem reindex_Jm {n : ℕ} {ε : Fin n → Bool} (π : Fin n ≃ Fin n) (hπ : ∀ i, ε (π i) = ε i) :
    reindex π π (Formalism.REAL.Jm ε) = Formalism.REAL.Jm ε := by
  have hs : ∀ i, ε (π.symm i) = ε i := fun i => by simpa using (hπ (π.symm i)).symm
  ext i j
  simp [Formalism.REAL.Jm, Matrix.diagonal_apply, hs]

theorem memUpq_iff {P Q n : ℕ} {ε : Fin n → Bool} (e : Fin P ⊕ Fin Q ≃ Fin n)
    (h1 : ∀ i, ε (e (Sum.inl i)) = true) (h2 : ∀ j, ε (e (Sum.inr j)) = false)
    (x : (Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)ˣ) :
    x ∈ Formalism.UG.Upq P Q ↔ Units.map (rmap e) x ∈ Formalism.REAL.UJ ε := by
  have key : (Formalism.UG.cT (starRingEnd ℂ) (x : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) *
      Formalism.UG.Jpq P Q * (x : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) = Formalism.UG.Jpq P Q) ↔
      Formalism.REAL.inUJ ε (reindex e e (x : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)) := by
    rw [cT_eq, Formalism.REAL.inUJ, ← reindex_Jpq e h1 h2, ← reindex_conj]
    exact (Matrix.reindex e e).injective.eq_iff.symm
  exact key

theorem memUJ_iff {n : ℕ} {ε : Fin n → Bool} (π : Fin n ≃ Fin n) (hπ : ∀ i, ε (π i) = ε i)
    (x : (Matrix (Fin n) (Fin n) ℂ)ˣ) :
    x ∈ Formalism.REAL.UJ ε ↔ Units.map (rmap π) x ∈ Formalism.REAL.UJ ε := by
  have key : Formalism.REAL.inUJ ε (x : Matrix (Fin n) (Fin n) ℂ) ↔
      Formalism.REAL.inUJ ε (reindex π π (x : Matrix (Fin n) (Fin n) ℂ)) := by
    rw [Formalism.REAL.inUJ, Formalism.REAL.inUJ]
    conv_rhs => rw [← reindex_Jm π hπ, ← reindex_conj]
    exact (Matrix.reindex π π).injective.eq_iff.symm
  exact key

def phi {P Q n : ℕ} {ε : Fin n → Bool} (e : Fin P ⊕ Fin Q ≃ Fin n)
    (h1 : ∀ i, ε (e (Sum.inl i)) = true) (h2 : ∀ j, ε (e (Sum.inr j)) = false) :
    Formalism.BasicNotions.UpqT P Q ≃ₜ* Formalism.REAL.UJ ε :=
  transp e (Formalism.UG.Upq P Q) (Formalism.REAL.UJ ε) (memUpq_iff e h1 h2)

theorem umat_phi {P Q n : ℕ} {ε : Fin n → Bool} (e : Fin P ⊕ Fin Q ≃ Fin n)
    (h1 : ∀ i, ε (e (Sum.inl i)) = true) (h2 : ∀ j, ε (e (Sum.inr j)) = false)
    (g : Formalism.BasicNotions.UpqT P Q) :
    PI.CdHaarScale.umat (phi e h1 h2 g) = reindex e e (Formalism.BasicNotions.UpqT.mat g) := rfl

def rho {n : ℕ} {ε : Fin n → Bool} (π : Fin n ≃ Fin n) (hπ : ∀ i, ε (π i) = ε i) :
    Formalism.REAL.UJ ε ≃ₜ* Formalism.REAL.UJ ε :=
  transp π (Formalism.REAL.UJ ε) (Formalism.REAL.UJ ε) (memUJ_iff π hπ)

theorem umat_rho {n : ℕ} {ε : Fin n → Bool} (π : Fin n ≃ Fin n) (hπ : ∀ i, ε (π i) = ε i)
    (a : Formalism.REAL.UJ ε) :
    PI.CdHaarScale.umat (rho π hπ a) = reindex π π (PI.CdHaarScale.umat a) := rfl

theorem umat_injective {n : ℕ} {ε : Fin n → Bool} :
    Function.Injective (PI.CdHaarScale.umat (ε := ε)) := by
  intro a b h
  exact Subtype.ext (Units.ext h)

theorem rho_iterate {n : ℕ} {ε : Fin n → Bool} (π : Fin n ≃ Fin n) (hπ : ∀ i, ε (π i) = ε i)
    (m : ℕ) (a : Formalism.REAL.UJ ε) (i j : Fin n) :
    PI.CdHaarScale.umat ((rho π hπ)^[m] a) i j =
      PI.CdHaarScale.umat a ((π.symm)^[m] i) ((π.symm)^[m] j) := by
  induction m generalizing i j with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', umat_rho, Matrix.reindex_apply, Matrix.submatrix_apply, ih,
      Function.iterate_succ_apply, Function.iterate_succ_apply]

theorem rho_finite_order {n : ℕ} {ε : Fin n → Bool} (π : Fin n ≃ Fin n) (hπ : ∀ i, ε (π i) = ε i) :
    ∃ N : ℕ, N ≠ 0 ∧ ∀ a, (rho π hπ)^[N] a = a := by
  refine ⟨orderOf π, (orderOf_pos π).ne', fun a => ?_⟩
  have hid : ∀ i, (π.symm)^[orderOf π] i = i := by
    intro i
    rw [show π.symm = π⁻¹ from rfl, Equiv.Perm.iterate_eq_pow, inv_pow, pow_orderOf_eq_one, inv_one]
    rfl
  apply umat_injective
  ext i j
  rw [rho_iterate, hid, hid]

theorem map_eq_self_of_iterate {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] (ψ : G ≃ₜ* G) (N : ℕ) (hN : N ≠ 0)
    (hψ : ∀ x, ψ^[N] x = x) : μ.map ψ = μ := by
  have hm : Measurable ψ := ψ.continuous.measurable
  haveI : (μ.map ψ).IsHaarMeasure := inferInstance
  set c := (μ.map ψ).haarScalarFactor μ with hc
  have hμc : μ.map ψ = c • μ := isMulLeftInvariant_eq_smul _ _
  have hk : ∀ k : ℕ, μ.map (ψ^[k]) = c ^ k • μ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ', ← Measure.map_map hm (hm.iterate k), ih, Measure.map_smul, hμc,
        smul_smul, pow_succ]
  have hid : (⇑ψ)^[N] = id := funext hψ
  have hN' : μ = c ^ N • μ := by rw [← hk N, hid, Measure.map_id]
  obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : G)
  have h0 : μ K ≠ 0 := (measure_pos_of_mem_nhds μ hK1).ne'
  have htop : μ K ≠ ⊤ := hK.measure_lt_top.ne
  have hKeq : ((c ^ N : NNReal) : ENNReal) * μ K = 1 * μ K := by
    have := congrArg (fun ν : Measure G => ν K) hN'
    simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at this
    rw [one_mul]
    exact this.symm
  have hcN : (c : ℝ) ^ N = 1 := by
    have h3 := congrArg ENNReal.toReal hKeq
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul] at h3
    have hpos : 0 < (μ K).toReal := ENNReal.toReal_pos h0 htop
    have h4 := mul_right_cancel₀ hpos.ne' h3
    simpa using h4
  have hc1 : c = 1 := by
    have := (pow_eq_one_iff_of_nonneg c.2 hN).1 hcN
    exact NNReal.eq (this.trans NNReal.coe_one.symm)
  rw [hμc, hc1, one_smul]

theorem card_true {P Q n : ℕ} {ε : Fin n → Bool} (e : Fin P ⊕ Fin Q ≃ Fin n)
    (h1 : ∀ i, ε (e (Sum.inl i)) = true) (h2 : ∀ j, ε (e (Sum.inr j)) = false) :
    (Finset.univ.filter (fun i : Fin n => ε i = true)).card = P := by
  have hset : Finset.univ.filter (fun i : Fin n => ε i = true) =
      (Finset.univ : Finset (Fin P)).map ⟨fun a => e (Sum.inl a), fun a b h => by simpa using h⟩ := by
    ext i
    obtain ⟨s, rfl⟩ := e.surjective i
    rcases s with a | a <;> simp [h1, h2]
    · exact ⟨a, rfl⟩
    · intro x hx
      exact Sum.inl_ne_inr (e.injective hx)
  rw [hset, Finset.card_map, Finset.card_univ, Fintype.card_fin]

theorem card_false {P Q n : ℕ} {ε : Fin n → Bool} (e : Fin P ⊕ Fin Q ≃ Fin n)
    (h1 : ∀ i, ε (e (Sum.inl i)) = true) (h2 : ∀ j, ε (e (Sum.inr j)) = false) :
    (Finset.univ.filter (fun i : Fin n => ε i = false)).card = Q := by
  have hset : Finset.univ.filter (fun i : Fin n => ε i = false) =
      (Finset.univ : Finset (Fin Q)).map ⟨fun a => e (Sum.inr a), fun a b h => by simpa using h⟩ := by
    ext i
    obtain ⟨s, rfl⟩ := e.surjective i
    rcases s with a | a <;> simp [h1, h2]
    · intro x hx
      exact Sum.inr_ne_inl (e.injective hx)
    · exact ⟨a, rfl⟩
  rw [hset, Finset.card_map, Finset.card_univ, Fintype.card_fin]

theorem map_phi_indep {P Q n : ℕ} {ε : Fin n → Bool} (e e' : Fin P ⊕ Fin Q ≃ Fin n)
    (h1 : ∀ i, ε (e (Sum.inl i)) = true) (h2 : ∀ j, ε (e (Sum.inr j)) = false)
    (h1' : ∀ i, ε (e' (Sum.inl i)) = true) (h2' : ∀ j, ε (e' (Sum.inr j)) = false)
    (μ : Measure (Formalism.BasicNotions.UpqT P Q)) [μ.IsHaarMeasure] :
    μ.map (phi e' h1' h2') = μ.map (phi e h1 h2) := by
  set π : Fin n ≃ Fin n := e.symm.trans e' with hπdef
  have hπ : ∀ i, ε (π i) = ε i := by
    intro i
    obtain ⟨s, rfl⟩ := e.surjective i
    rcases s with a | a <;> simp [hπdef, h1, h2, h1', h2']
  have hcomp : ⇑(phi e' h1' h2') = ⇑(rho π hπ) ∘ ⇑(phi e h1 h2) := by
    funext g
    apply umat_injective
    rw [Function.comp_apply, umat_rho, umat_phi, umat_phi]
    ext i j
    simp [hπdef, Matrix.reindex_apply]
  obtain ⟨N, hN, hN'⟩ := rho_finite_order π hπ
  have hmr : Measurable ⇑(rho π hπ) := (rho π hπ).continuous.measurable
  have hmp : Measurable ⇑(phi e h1 h2) := (phi e h1 h2).continuous.measurable
  rw [hcomp, ← Measure.map_map hmr hmp]
  exact map_eq_self_of_iterate _ (rho π hπ) N hN hN'

theorem tie_set {P Q n : ℕ} {ε : Fin n → Bool} (e : Fin P ⊕ Fin Q ≃ Fin n)
    (h1 : ∀ i, ε (e (Sum.inl i)) = true) (h2 : ∀ j, ε (e (Sum.inr j)) = false)
    (A : Set (Formalism.REAL.UJ ε)) :
    {g : Formalism.BasicNotions.UpqT P Q | ∃ a ∈ A, PI.CdHaarScale.umat a = reindex e e (Formalism.BasicNotions.UpqT.mat g)} =
      (phi e h1 h2) ⁻¹' A := by
  ext g
  simp only [Set.mem_setOf_eq, Set.mem_preimage]
  constructor
  · rintro ⟨a, ha, h⟩
    have : a = phi e h1 h2 g := umat_injective (h.trans (umat_phi e h1 h2 g).symm)
    exact this ▸ ha
  · intro hg
    exact ⟨_, hg, umat_phi e h1 h2 g⟩

end PI.UnitaryGroupMassFormula.CdHaarScale.Main
