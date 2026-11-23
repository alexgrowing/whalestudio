import Formalism.LocalToGlobal.CharacterGerms.PderivSubGOff

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds.RF

open Formalism.IncomingBounds Formalism.L2.Pj MvPolynomial

theorem letter_cast {T : Type} {r : T → ℕ} {n : ℕ} {σ σ' : T} (h : σ = σ') (a : Fin (r σ)) :
    ∃ a' : Fin (r σ'), ∀ b : Fin n, (⟨σ, a, b⟩ : Letter T r n) = ⟨σ', a', b⟩ := by
  subst h
  exact ⟨a, fun b => rfl⟩

section Plane

variable {C : Type} [Field C] {T Orb : Type} [Fintype Orb] {r : T → ℕ} {tau : Orb → ZMod 2 → T}
  {gm : Orb → ZMod 2 → Matrix (Fin 2) (Fin 2) C} {N n : ℕ} (plc : Fin N × Fin 2 ↪ Fin n)

theorem lap_plane (inj : Function.Injective fun x : Orb × ZMod 2 => tau x.1 x.2)
    (gm_hyp : ∀ o t (s s' : Fin 2), ∑ q, gm o (t + 1) q s * gm o t q s' = if s = s' then 0 else 1)
    (Q : MvPolynomial (Fin N × WVO fun o (_ : Fin 2) => IIs r tau o) C) (o : Orb) (t : ZMod 2)
    (a1 : Fin (r (tau o t))) (a2 : Fin (r (tau o (t + 1))))
    (hno : ∀ ρ g1 g2, g1 ≠ g2 → (eW r tau N).symm ((ρ, ⟨o, ⟨t, a1⟩⟩), g1) ∈ Q.vars →
      (eW r tau N).symm ((ρ, ⟨o, ⟨t + 1, a2⟩⟩), g2) ∈ Q.vars → False) :
    ∑ b, pderiv (⟨tau o t, a1, b⟩ : Letter T r n) (pderiv (⟨tau o (t + 1), a2, b⟩ : Letter T r n)
      (subG r tau gm plc Q)) = 0 := by
  have hoff : ∀ b ∈ (Finset.univ : Finset (Fin n)), b ∉ Finset.univ.map plc →
      pderiv (⟨tau o t, a1, b⟩ : Letter T r n) (pderiv (⟨tau o (t + 1), a2, b⟩ : Letter T r n)
        (subG r tau gm plc Q)) = 0 := by
    intro b _ hb
    rw [pderiv_subG_off plc (ℓ := ⟨tau o (t + 1), a2, b⟩), map_zero]
    intro z e
    apply hb
    rw [Finset.mem_map]
    exact ⟨(z.1.1, z.2), Finset.mem_univ _, (congrArg (fun ℓ : Letter T r n => ℓ.2.2) e).symm⟩
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map plc)) hoff, Finset.sum_map, Fintype.sum_prod_type]
  refine Finset.sum_eq_zero fun ρ _ => ?_
  have hf : ∀ col, pderiv (⟨tau o t, a1, plc (ρ, col)⟩ : Letter T r n)
      (pderiv (⟨tau o (t + 1), a2, plc (ρ, col)⟩ : Letter T r n) (subG r tau gm plc Q)) =
      ∑ g1, ∑ g2, MvPolynomial.C (gm o t col g1 * gm o (t + 1) col g2) *
        subG r tau gm plc (pderiv ((eW r tau N).symm ((ρ, ⟨o, ⟨t, a1⟩⟩), g1))
          (pderiv ((eW r tau N).symm ((ρ, ⟨o, ⟨t + 1, a2⟩⟩), g2)) Q)) := by
    intro col
    have e2 := pderiv_subG_lam (gm := gm) plc inj ((ρ, ⟨o, ⟨t + 1, a2⟩⟩) : AA r tau N) col Q
    have e2' : pderiv (⟨tau o (t + 1), a2, plc (ρ, col)⟩ : Letter T r n) (subG r tau gm plc Q) = _ := e2
    rw [e2', map_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun g2 _ => ?_
    rw [Derivation.leibniz, pderiv_C, smul_zero, add_zero, smul_eq_mul]
    have e1 := pderiv_subG_lam (gm := gm) plc inj ((ρ, ⟨o, ⟨t, a1⟩⟩) : AA r tau N) col
      (pderiv ((eW r tau N).symm ((ρ, ⟨o, ⟨t + 1, a2⟩⟩), g2)) Q)
    have e1' : pderiv (⟨tau o t, a1, plc (ρ, col)⟩ : Letter T r n) (subG r tau gm plc
      (pderiv ((eW r tau N).symm ((ρ, ⟨o, ⟨t + 1, a2⟩⟩), g2)) Q)) = _ := e1
    rw [e1', Finset.mul_sum]
    refine Finset.sum_congr rfl fun g1 _ => ?_
    rw [map_mul]
    unfold Gm
    ring
  simp only [hf]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun g1 _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun g2 _ => ?_
  rw [← Finset.sum_mul, ← map_sum]
  by_cases hg : g1 = g2
  · have hK : ∑ col, gm o t col g1 * gm o (t + 1) col g2 = 0 := by
      have h := gm_hyp o t g2 g1
      rw [if_pos hg.symm] at h
      rw [← h]
      exact Finset.sum_congr rfl fun q _ => mul_comm _ _
    rw [hK, map_zero, zero_mul]
  · have hz : pderiv ((eW r tau N).symm ((ρ, ⟨o, ⟨t, a1⟩⟩), g1))
        (pderiv ((eW r tau N).symm ((ρ, ⟨o, ⟨t + 1, a2⟩⟩), g2)) Q) = 0 := by
      by_cases h2 : (eW r tau N).symm ((ρ, ⟨o, ⟨t + 1, a2⟩⟩), g2) ∈ Q.vars
      · have h1 : (eW r tau N).symm ((ρ, ⟨o, ⟨t, a1⟩⟩), g1) ∉ Q.vars := fun h1 => hno ρ g1 g2 hg h1 h2
        rw [pderiv_comm', pderiv_eq_zero_of_notMem_vars h1, map_zero]
      · rw [pderiv_eq_zero_of_notMem_vars h2, map_zero]
    rw [hz, map_zero, mul_zero]

end Plane

section Fam

theorem mem_vars_blkProdG {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d] {Orb : Type} [Fintype Orb]
    {I J : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)] [∀ o g, Fintype (J o g)]
    {X : ∀ o, RowData C V d (I o) (J o)} {F : ∀ o, Flag (X o)} {n : ℕ} {L : Orb → List (GlobalTheory d × ℝ)}
    {pl : (Σ o, Σ i : Fin (L o).length, Fin (rowsAt X L o i)) → Fin n} {b : Fin n} {o : Orb} {w : WV (I o)}
    (hx : ((b, ⟨o, w⟩) : Fin n × WVO I) ∈ (blkProd X F n L pl).vars) :
    (b, w) ∈ (prodAll (plAt n pl o) fun i => (blkAt L o i).poly (X o) (F o)).vars := by
  first
  | unfold blkProd at hx
  | simp only [blkProd] at hx
  first
  | unfold toAll at hx
  | simp only [toAll] at hx
  have h1 := MvPolynomial.vars_prod _ hx
  rw [Finset.mem_biUnion] at h1
  obtain ⟨o', -, h2⟩ := h1
  have h3 := MvPolynomial.vars_rename _ _ h2
  rw [Finset.mem_image] at h3
  obtain ⟨x, hx1, hx2⟩ := h3
  simp only [Prod.mk.injEq, Sigma.mk.inj_iff] at hx2
  obtain ⟨hb, ho, hw⟩ := hx2
  subst ho
  obtain rfl := eq_of_heq hw
  subst hb
  exact hx1

variable {C : Type} [Field C] {V : VF C} {T : Type} {r : T → ℕ} {cc : T → T} {a : T → ℕ → ℕ}
  {Orb : Type} [Fintype Orb] {tau : Orb → ZMod 2 → T} {gm : Orb → ZMod 2 → Matrix (Fin 2) (Fin 2) C}
  {J : Orb → Fin 2 → Type} [∀ o g, Fintype (J o g)]
  {X : ∀ o, RowData C V 2 (fun _ => IIs r tau o) (J o)} {F : ∀ o, Flag (X o)}
  {gaC : Orb → ZMod 2 → ℕ → ℕ} {N : ℕ} {L : Orb → List (GlobalTheory 2 × ℝ)}
  {pl : (Σ o, Σ i : Fin (L o).length, Fin (rowsAt X L o i)) → Fin N}

theorem zmod_two_add_one_add_one_eq : ∀ t : ZMod 2, t + 1 + 1 = t := by
  decide

theorem SelfConjugatePlaceSetting.rowsOK (H : SelfConjugatePlaceSetting r cc a tau gm X F gaC N L pl) (o : Orb) :
    ∃ kind : Fin N → Knd 2, RowsOK (X o).G (X o).Alt
      (prodAll (plAt N pl o) fun i => (blkAt L o i).poly (X o) (F o)) kind := by
  have h : ∀ i : Fin (L o).length, ∃ kind : Fin (rowsAt X L o i) → Knd 2,
      RowsOK (X o).G (X o).Alt ((blkAt L o i).poly (X o) (F o)) kind := by
    intro i
    refine exists_rowsOK (X o) (F o) (Or.inl (H.alt o)) (H.hj o) _ fun g t k hk => ?_
    have hsum : ∀ s, (blkAt L o i).wt (X o) 0 s k + (blkAt L o i).wt (X o) 1 (s + 1) k ≤ gaC o s k := by
      intro s
      rw [← H.wt o s k]
      exact le_sum_map (L o) (fun q => q.1.wt (X o) 0 s k + q.1.wt (X o) 1 (s + 1) k) (List.get_mem (L o) i)
    by_cases hg : g = 0
    · subst hg
      have h1 := hsum t
      exact (H.supp o t k (by omega)).2
    · have hg1 : g = 1 := Fin.eq_one_of_ne_zero g hg
      subst hg1
      have h1 := hsum (t + 1)
      rw [zmod_two_add_one_add_one_eq] at h1
      have h2 := (H.supp o (t + 1) k (by omega)).2
      rw [H.rkF_eq o 0 (t + 1)] at h2
      rw [H.rkF_eq o 1 t]
      exact h2
  choose kind hk using h
  exact ⟨_, rowsOK_prodAll _ _ (plAt_inj N H.plinj o) _ kind hk⟩

theorem lab_eq : ∀ g1 g2 : Fin 2, g1 ≠ g2 → ∀ t : ZMod 2,
    (if g1 = 0 then t else t + 1) = (if g2 = 0 then t + 1 else t + 1 + 1) := by
  decide

theorem SelfConjugatePlaceSetting.no_conj (H : SelfConjugatePlaceSetting r cc a tau gm X F gaC N L pl) (ρ : Fin N) (o : Orb) (g1 g2 : Fin 2) (hne : g1 ≠ g2)
    (t : ZMod 2) (a1 : Fin (r (tau o t))) (a2 : Fin (r (tau o (t + 1))))
    (hx : (eW r tau N).symm ((ρ, ⟨o, ⟨t, a1⟩⟩), g1) ∈ (blkProd X F N L pl).vars)
    (hx' : (eW r tau N).symm ((ρ, ⟨o, ⟨t + 1, a2⟩⟩), g2) ∈ (blkProd X F N L pl).vars) : False := by
  obtain ⟨kind, hk⟩ := H.rowsOK o
  have hx1 : ((ρ, ⟨o, ⟨g1, ⟨t, a1⟩⟩⟩) : Fin N × WVO fun o (_ : Fin 2) => IIs r tau o) ∈ (blkProd X F N L pl).vars := hx
  have hx2 : ((ρ, ⟨o, ⟨g2, ⟨t + 1, a2⟩⟩⟩) : Fin N × WVO fun o (_ : Fin 2) => IIs r tau o) ∈ (blkProd X F N L pl).vars := hx'
  have h1 := mem_vars_blkProdG hx1
  have h2 := mem_vars_blkProdG hx2
  have ht : tyW (X o).G (⟨g1, ⟨t, a1⟩⟩ : WV fun _ => IIs r tau o) = tyW (X o).G (⟨g2, ⟨t + 1, a2⟩⟩ : WV fun _ => IIs r tau o) :=
    (H.hty o g1 ⟨t, a1⟩).trans ((lab_eq g1 g2 hne t).trans (H.hty o g2 ⟨t + 1, a2⟩).symm)
  exact no_conj_of_rowsOK hk h1 h2 hne ht

end Fam

theorem isotropic_to_std_subst_harmonic : IsotropicToStdSubstHarmonic := by
  intro C _ V T r cc a Orb _ tau gm J _ X F gaC N L pl H n plc isX
  simp only [harmK, Submodule.mem_iInf, LinearMap.mem_ker]
  intro τ _ a1 a2
  rw [lap_one_apply]
  have hdiag : ∀ b, (∑ b', (1 : Matrix (Fin n) (Fin n) C) b b' •
      pderiv (⟨τ, a1, b⟩ : Letter T r n) (pderiv (⟨cc τ, a2, b'⟩ : Letter T r n)
        (subG r tau gm plc (blkProd X F N L pl)))) =
      pderiv (⟨τ, a1, b⟩ : Letter T r n) (pderiv (⟨cc τ, a2, b⟩ : Letter T r n)
        (subG r tau gm plc (blkProd X F N L pl))) := by
    intro b
    rw [Finset.sum_eq_single b]
    · rw [Matrix.one_apply_eq, one_smul]
    · intro b' _ hb
      rw [Matrix.one_apply_ne (Ne.symm hb), zero_smul]
    · intro h; exact absurd (Finset.mem_univ _) h
  simp only [hdiag]
  by_cases hτ : ∃ o t, tau o t = τ
  · obtain ⟨o, t, rfl⟩ := hτ
    obtain ⟨a2', ha2⟩ := letter_cast (n := n) (H.conj o t) a2
    simp only [ha2]
    exact lap_plane plc H.inj H.gm_hyp _ o t a1 a2' fun ρ g1 g2 hne h1 h2 => H.no_conj ρ o g1 g2 hne t a1 a2' h1 h2
  · push Not at hτ
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [pderiv_comm', pderiv_subG_off plc (ℓ := ⟨τ, a1, b⟩), map_zero]
    intro z e
    exact hτ _ _ (congrArg Sigma.fst e).symm

end Formalism.L2.FormalSeriesBounds.RF
