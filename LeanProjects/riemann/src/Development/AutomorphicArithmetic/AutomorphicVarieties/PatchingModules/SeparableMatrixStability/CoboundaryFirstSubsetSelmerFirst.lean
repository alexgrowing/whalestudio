import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.MapEta
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.RhoHom

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem bd_mem_iff {A X : Type} [CommRing A] [CommRing X] [Algebra A X] {g n a : ℕ}
    (Z : Matrix (Fin n) (Fin n) (DD X g)) : Z ∈ W1 n A X g a ↔ ∀ i j : Fin n,
      (Z i j).ep' = 0 ∧ (Z i j).eta = 0 ∧ ((((i : ℕ) < a) ↔ ((j : ℕ) < a)) → (Z i j).ep = 0) ∧
        (¬ (((i : ℕ) < a) ↔ ((j : ℕ) < a)) → (Z i j).a = 0) := by
  simp only [W1, blkMat, ddPart, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
    Set.mem_setOf_eq]
  refine forall_congr' fun i => forall_congr' fun j => ?_
  by_cases hd : ((i : ℕ) < a ↔ (j : ℕ) < a) <;> simp [hd] <;> tauto

private theorem dd_components_finset_sum {X ι : Type} [CommRing X] {g : ℕ} (s : Finset ι) (f : ι → DD X g) :
    (∑ k ∈ s, f k).a = ∑ k ∈ s, (f k).a ∧ (∀ j, (∑ k ∈ s, f k).ep j = ∑ k ∈ s, (f k).ep j) ∧
      (∀ j, (∑ k ∈ s, f k).ep' j = ∑ k ∈ s, (f k).ep' j) ∧ (∑ k ∈ s, f k).eta = ∑ k ∈ s, (f k).eta := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [DD.zero_a, DD.zero_ep, DD.zero_ep', DD.zero_eta]
  | insert k s hk ih =>
    obtain ⟨h1, h2, h3, h4⟩ := ih
    refine ⟨?_, fun j => ?_, fun j => ?_, ?_⟩ <;>
      simp [Finset.sum_insert hk, DD.add_a, DD.add_ep, DD.add_ep', DD.add_eta, h1, h2, h3, h4]

private theorem bd_mul_mem {A X : Type} [CommRing A] [CommRing X] [Algebra A X] {g n a : ℕ}
    {Z Z' : Matrix (Fin n) (Fin n) (DD X g)} (h : Z ∈ W1 n A X g a) (h' : Z' ∈ W1 n A X g a) :
    Z * Z' ∈ W1 n A X g a := by
  rw [bd_mem_iff] at h h' ⊢
  intro i j
  obtain ⟨ha, hep, hep', heta⟩ := dd_components_finset_sum Finset.univ (fun k => Z i k * Z' k j)
  rw [Matrix.mul_apply]
  refine ⟨?_, ?_, ?_, ?_⟩
  · funext m
    rw [hep']
    exact Finset.sum_eq_zero fun k _ => by simp [DD.mul_ep', (h i k).1, (h' k j).1]
  · rw [heta]
    exact Finset.sum_eq_zero fun k _ => by
      simp [DD.mul_eta, (h i k).1, (h' k j).1, (h i k).2.1, (h' k j).2.1]
  · intro hd
    funext m
    rw [hep]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [DD.mul_ep]
    by_cases hk : ((i : ℕ) < a ↔ (k : ℕ) < a)
    · have hk' : ((k : ℕ) < a ↔ (j : ℕ) < a) := hk.symm.trans hd
      rw [congrFun ((h i k).2.2.1 hk) m, congrFun ((h' k j).2.2.1 hk') m]
      simp
    · have hk' : ¬((k : ℕ) < a ↔ (j : ℕ) < a) := fun hh => hk (hd.trans hh.symm)
      rw [(h i k).2.2.2 hk, (h' k j).2.2.2 hk']
      simp
  · intro hd
    rw [ha]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [DD.mul_a]
    by_cases hk : ((i : ℕ) < a ↔ (k : ℕ) < a)
    · have hk' : ¬((k : ℕ) < a ↔ (j : ℕ) < a) := fun hh => hd (hk.trans hh)
      rw [(h' k j).2.2.2 hk', mul_zero]
    · rw [(h i k).2.2.2 hk, zero_mul]

private theorem bd_rho_mem {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} {x : NP F n} (k : Kap x) (X : Type)
    [CommRing X] [Algebra x.A X] (g : F.G₀) : k.ρ1 X g ∈ W1 n x.A X k.g x.a := by
  have hC : ∀ c : x.A, algebraMap x.A (DD X k.g) c = DD.C (algebraMap x.A X c) := fun _ => rfl
  have hK : ∀ m (i j : Fin n), ((i : ℕ) < x.a ↔ (j : ℕ) < x.a) → k.κ m g i j = 0 := by
    intro m i j hd
    have hm := (k.mem m).1 g
    simp only [Od, blkMat, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
      Set.mem_setOf_eq, Submodule.mem_bot] at hm
    exact (hm i j).1 hd
  have hR : ∀ i j : Fin n, ¬((i : ℕ) < x.a ↔ (j : ℕ) < x.a) → (mat x.ρ) g i j = 0 := by
    intro i j hd
    have hm := x.blk g
    simp only [Ev, blkMat, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
      Set.mem_setOf_eq, Submodule.mem_bot] at hm
    exact (hm i j).2 hd
  apply bd_mul_mem
  · rw [bd_mem_iff]
    intro i j
    by_cases hij : i = j
    · subst hij
      refine ⟨?_, ?_, fun _ => ?_, fun hd => absurd Iff.rfl hd⟩
      · funext m
        simp [DD.epM, DD.add_ep', DD.one_ep']
      · simp [DD.epM, DD.add_eta, DD.one_eta]
      · funext m
        simp [DD.epM, DD.add_ep, DD.one_ep, hK m i i Iff.rfl]
    · refine ⟨?_, ?_, fun hd => ?_, fun hd => ?_⟩
      · funext m
        simp [DD.epM, DD.add_ep', Matrix.one_apply_ne hij, DD.zero_ep']
      · simp [DD.epM, DD.add_eta, Matrix.one_apply_ne hij, DD.zero_eta]
      · funext m
        simp [DD.epM, DD.add_ep, Matrix.one_apply_ne hij, DD.zero_ep, hK m i j hd]
      · simp [DD.epM, DD.add_a, Matrix.one_apply_ne hij, DD.zero_a]
  · rw [bd_mem_iff]
    intro i j
    simp only [NP.ρX, Matrix.map_apply, hC]
    refine ⟨?_, ?_, fun _ => ?_, fun hd => ?_⟩
    · funext m
      exact DD.C_ep' _ m
    · exact DD.C_eta _
    · funext m
      exact DD.C_ep _ m
    · rw [DD.C_a, hR i j hd, map_zero]

private theorem bd_epM_mul {X : Type} [CommRing X] {g n : ℕ} (Z Z' : Fin g → Matrix (Fin n) (Fin n) X) :
    DD.epM Z * DD.epM Z' = 0 := by
  refine Matrix.ext fun i j => ?_
  rw [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun m _ => ?_
  ext <;> simp [DD.epM]

private theorem bd_polar {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} {x : NP F n} (k : Kap x) (X : Type)
    [CommRing X] [Algebra x.A X] (g : F.G₀) : (k.ρ1 X g)ᵀ * k.ρ1 X (F.conj g) =
      algebraMap x.A (DD X k.g) ((F.eps ℤ_[l] x.A g ^ (1 - (n : ℤ)) : x.Aˣ) : x.A) • (1 : Matrix (Fin n) (Fin n) (DD X k.g)) := by
  set E : F.G₀ → Matrix (Fin n) (Fin n) (DD X k.g) :=
    fun g => DD.epM fun j => (k.κ j g).map ⇑(algebraMap x.A X) with hE
  have hρ1 : ∀ g, k.ρ1 X g = (1 + E g) * (x.ρX (DD X k.g) g) := fun _ => rfl
  have hT : (E g)ᵀ = DD.epM fun j => ((k.κ j g).map ⇑(algebraMap x.A X))ᵀ :=
    Matrix.ext fun _ _ => rfl
  have hc : E (F.conj g) = -(E g)ᵀ := by
    refine Matrix.ext fun i i' => DD.ext ?_ ?_ ?_ ?_
    · simp [hE, DD.epM, DD.neg_a]
    · funext m
      have h4 := (k.mem m).2.2.2.1 g
      simp [hE, DD.epM, DD.neg_ep, h4]
    · funext m
      simp [hE, DD.epM, DD.neg_ep']
    · simp [hE, DD.epM, DD.neg_eta]
  have hmid : (1 + E g)ᵀ * (1 + E (F.conj g)) = 1 := by
    have hTT : (E g)ᵀ * (E g)ᵀ = 0 := by
      rw [hT]
      exact bd_epM_mul _ _
    rw [Matrix.transpose_add, Matrix.transpose_one, hc, add_mul, one_mul, mul_add, mul_one, mul_neg,
      hTT, neg_zero, add_zero, neg_add_cancel_right]
  have hsc : ∀ c : x.A, (c • (1 : Matrix (Fin n) (Fin n) x.A)).map ⇑(algebraMap x.A (DD X k.g)) =
      algebraMap x.A (DD X k.g) c • (1 : Matrix (Fin n) (Fin n) (DD X k.g)) := by
    intro c
    refine Matrix.ext fun i j => ?_
    by_cases hij : i = j
    · subst hij
      simp
    · simp [Matrix.one_apply_ne hij]
  rw [hρ1, hρ1, Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc ((1 + E g)ᵀ), hmid,
    Matrix.one_mul]
  have hf := x.form g
  simp only [Units.val_one, Matrix.mul_one] at hf
  simp only [NP.ρX, ← Matrix.transpose_map, ← Matrix.map_mul, hf]
  exact hsc _

private theorem bd_cont {Γ R : Type} [TopologicalSpace Γ] [Group Γ] [IsTopologicalGroup Γ] [CommRing R] {n : ℕ} (I : Ideal R)
    (ρ : Γ → Matrix (Fin n) (Fin n) R) (hρ : ∀ i j, AdicCont I fun g => ρ g i j) (Y : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    AdicCont I fun g => (ρ g * Y * ρ g⁻¹ - Y) i j := by
  intro N
  have hl : ∀ i j, IsLocallyConstant fun g => Ideal.Quotient.mk (I ^ N) (ρ g i j) :=
    fun i j => hρ i j N
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have h1 : ∀ᶠ y in nhds x, ∀ p : Fin n × Fin n,
      Ideal.Quotient.mk (I ^ N) (ρ y p.1 p.2) = Ideal.Quotient.mk (I ^ N) (ρ x p.1 p.2) := by
    rw [Filter.eventually_all]
    intro p
    exact (IsLocallyConstant.iff_eventually_eq _).mp (hl p.1 p.2) x
  have h2 : ∀ᶠ y in nhds x, ∀ p : Fin n × Fin n,
      Ideal.Quotient.mk (I ^ N) (ρ y⁻¹ p.1 p.2) = Ideal.Quotient.mk (I ^ N) (ρ x⁻¹ p.1 p.2) := by
    rw [Filter.eventually_all]
    intro p
    have hx := (IsLocallyConstant.iff_eventually_eq _).mp (hl p.1 p.2) x⁻¹
    exact (continuous_inv.tendsto x).eventually hx
  filter_upwards [h1, h2] with y hy1 hy2
  have e1 : (Ideal.Quotient.mk (I ^ N)).mapMatrix (ρ y) = (Ideal.Quotient.mk (I ^ N)).mapMatrix (ρ x) :=
    Matrix.ext fun i j => hy1 (i, j)
  have e2 : (Ideal.Quotient.mk (I ^ N)).mapMatrix (ρ y⁻¹) =
      (Ideal.Quotient.mk (I ^ N)).mapMatrix (ρ x⁻¹) :=
    Matrix.ext fun i j => hy2 (i, j)
  have key : ∀ z, Ideal.Quotient.mk (I ^ N) ((ρ z * Y * ρ z⁻¹ - Y) i j) =
      ((Ideal.Quotient.mk (I ^ N)).mapMatrix (ρ z) * (Ideal.Quotient.mk (I ^ N)).mapMatrix Y *
        (Ideal.Quotient.mk (I ^ N)).mapMatrix (ρ z⁻¹) - (Ideal.Quotient.mk (I ^ N)).mapMatrix Y) i j := by
    intro z
    rw [← map_mul, ← map_mul, ← map_sub]
    rfl
  show Ideal.Quotient.mk (I ^ N) ((ρ y * Y * ρ y⁻¹ - Y) i j) = Ideal.Quotient.mk (I ^ N) ((ρ x * Y * ρ x⁻¹ - Y) i j)
  rw [key y, key x, e1, e2]

theorem UpperTheory.V.Pa.coboundary_first_subset_selmer_first :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n) (k : Kap x) (X : Type) [CommRing X] [Algebra x.A X], Bd1 h X k ⊆ Sel1 h X k := by
  intro l _ L G G0 h n x k X _ _ z hz
  obtain ⟨Y, hY, hYT, rfl⟩ := hz
  obtain ⟨hρ1, hmul, hcont⟩ := (rho_hom l G0.frame n x k X).2.1
  have hinv : ∀ g, k.ρ1 X g * k.ρ1 X g⁻¹ = 1 := fun g => by rw [← hmul, mul_inv_cancel, hρ1]
  have hz : dY G.frame (fun g => k.ρ1 X (h.p₀ g)) Y = fun g => dY G0.frame (k.ρ1 X) Y (h.p₀ g) :=
    funext fun g => h.dY_comp _ Y g
  rw [hz]
  refine (h.sel_iff x.t (k.ρ1 X) (k.w1 X) (k.wi1 X) (W1 n x.A X k.g x.a) (dY G0.frame (k.ρ1 X) Y)).mpr
    ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g
    exact Submodule.sub_mem _ (bd_mul_mem (bd_mul_mem (bd_rho_mem k X g) hY) (bd_rho_mem k X g⁻¹)) hY
  · intro i j
    exact bd_cont _ (k.ρ1 X) hcont Y i j
  · intro g g'
    show k.ρ1 X (g * g') * Y * k.ρ1 X (g * g')⁻¹ - Y =
      (k.ρ1 X g * Y * k.ρ1 X g⁻¹ - Y) + k.ρ1 X g * (k.ρ1 X g' * Y * k.ρ1 X g'⁻¹ - Y) * k.ρ1 X g⁻¹
    rw [_root_.mul_inv_rev, hmul, hmul]
    noncomm_ring
  · intro g
    have hs : ∀ g : G0.frame.G₀,
        algebraMap x.A (DD X k.g) ((G0.frame.eps ℤ_[l] x.A g⁻¹ ^ (1 - (n : ℤ)) : x.Aˣ) : x.A) *
          algebraMap x.A (DD X k.g) ((G0.frame.eps ℤ_[l] x.A g ^ (1 - (n : ℤ)) : x.Aˣ) : x.A) = 1 := by
      intro g
      rw [← map_mul, ← Units.val_mul, ← mul_zpow, ← map_mul, inv_mul_cancel, map_one, _root_.one_zpow,
        Units.val_one, map_one]
    have hA : ∀ g : G0.frame.G₀, k.ρ1 X (G0.frame.conj g) =
        algebraMap x.A (DD X k.g) ((G0.frame.eps ℤ_[l] x.A g ^ (1 - (n : ℤ)) : x.Aˣ) : x.A) •
          (k.ρ1 X g⁻¹)ᵀ := by
      intro g
      have e : (k.ρ1 X g⁻¹)ᵀ * (k.ρ1 X g)ᵀ = 1 := by
        rw [← Matrix.transpose_mul, hinv, Matrix.transpose_one]
      calc k.ρ1 X (G0.frame.conj g) = ((k.ρ1 X g⁻¹)ᵀ * (k.ρ1 X g)ᵀ) * k.ρ1 X (G0.frame.conj g) := by
            rw [e, Matrix.one_mul]
        _ = _ := by rw [Matrix.mul_assoc, bd_polar k X g, Matrix.mul_smul, Matrix.mul_one]
    show k.ρ1 X (G0.frame.conj g) * Y * k.ρ1 X (G0.frame.conj g)⁻¹ - Y =
      -(k.ρ1 X g * Y * k.ρ1 X g⁻¹ - Y)ᵀ
    rw [← map_inv G0.frame.conj g, hA, hA, inv_inv, Matrix.transpose_sub, Matrix.transpose_mul,
      Matrix.transpose_mul, hYT, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul, hs g,
      one_smul]
    noncomm_ring
  · intro u g hg
    have hone : ∀ g ∈ G0.frame.Iu u, k.ρ1 X g = 1 := by
      intro g hg
      have h0 : ∀ j, k.κ j g = 0 := fun j => (k.mem j).2.2.2.2.1 u g hg
      have hm : (mat x.ρ) g = 1 := by simp [mat, x.ine u g hg]
      have h1 : x.ρX (DD X k.g) g = 1 := by simp [NP.ρX, hm]
      have h2 : (DD.epM fun j => (k.κ j g).map ⇑(algebraMap x.A X)) = 0 := by
        refine Matrix.ext fun i i' => DD.ext ?_ ?_ ?_ ?_
        · simp [DD.epM, DD.zero_a]
        · funext m
          simp [DD.epM, DD.zero_ep, h0]
        · funext m
          simp [DD.epM, DD.zero_ep']
        · simp [DD.epM, DD.zero_eta]
      show (1 + DD.epM fun j => (k.κ j g).map ⇑(algebraMap x.A X)) * x.ρX (DD X k.g) g = 1
      rw [h1, h2, add_zero, mul_one]
    show k.ρ1 X g * Y * k.ρ1 X g⁻¹ - Y = 0
    rw [hone g hg, hone g⁻¹ (inv_mem hg)]
    simp
  · intro v
    exact ⟨Y, hY, fun g' => ⟨fun i j _ => by simp, fun _ i => by simp⟩⟩
