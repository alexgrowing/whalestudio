import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.DerUnipLeUnipB
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhitKerLeComapMap
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.StdMaxParabolicRadicalLeBlockUnipotentRadical

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir GlobalTheory.CompanionTheory.BZNuPair

noncomputable section

namespace GlobalTheory.CompanionTheory.BZNuPair.DerComap

section Groups

variable {k : Type} [Field k] {N : ℕ} (d : Fin 2 → ℕ) (h : ∑ a, d a = N)

theorem stdBlocks_zero_val (i : Fin (d 0)) : (stdBlocks d h ⟨0, i⟩ : ℕ) = i := by
  simpa using stdBlocks_val d h 0 i

theorem stdBlocks_one_val (i : Fin (d 1)) : (stdBlocks d h ⟨1, i⟩ : ℕ) = d 0 + i := by
  have := stdBlocks_val d h 1 i
  simpa using this

theorem idx_cases (i : Fin N) : (∃ a : Fin (d 0), i = stdBlocks d h ⟨0, a⟩) ∨
    ∃ a : Fin (d 1), i = stdBlocks d h ⟨1, a⟩ := by
  obtain ⟨⟨c, i'⟩, rfl⟩ := (stdBlocks d h).surjective i
  have key : ∀ (c : Fin 2) (i' : Fin (d c)),
      (∃ a : Fin (d 0), stdBlocks d h ⟨c, i'⟩ = stdBlocks d h ⟨0, a⟩) ∨
        ∃ a : Fin (d 1), stdBlocks d h ⟨c, i'⟩ = stdBlocks d h ⟨1, a⟩ :=
    Fin.forall_fin_two.2 ⟨fun i' => Or.inl ⟨i', rfl⟩, fun i' => Or.inr ⟨i', rfl⟩⟩
  exact key c i'

theorem blk_two (i : Fin N) : blk (stdBlocks d h) i = if (i : ℕ) < d 0 then 0 else 1 := by
  rcases idx_cases d h i with ⟨a, rfl⟩ | ⟨a, rfl⟩
  · rw [blk_apply, stdBlocks_zero_val, if_pos a.2]
  · rw [blk_apply, stdBlocks_one_val, if_neg (by omega)]

theorem mem_unipRad_iff {g : GL (Fin N) k} :
    g ∈ unipRad k (stdBlocks d h) ↔
      ∀ i j : Fin N, ¬ ((i : ℕ) < d 0 ∧ d 0 ≤ (j : ℕ)) →
        (g : Matrix (Fin N) (Fin N) k) i j = (1 : Matrix (Fin N) (Fin N) k) i j := by
  rw [GlobalTheory.RadRev.mem_unipRad_entries]
  refine forall_congr' fun i => forall_congr' fun j => ?_
  rw [blk_two, blk_two]
  have : ((if (i : ℕ) < d 0 then (0 : Fin 2) else 1) < if (j : ℕ) < d 0 then 0 else 1) ↔
      ((i : ℕ) < d 0 ∧ d 0 ≤ (j : ℕ)) := by
    by_cases hi : (i : ℕ) < d 0 <;> by_cases hj : (j : ℕ) < d 0 <;> simp [hi, hj] <;> omega
  rw [this]

theorem derUnip_col {n : ℕ} {w : GL (Fin N) k} (hw : w ∈ derUnip k N n) (r i : Fin N) (hi : (i : ℕ) < n) :
    (w : Matrix (Fin N) (Fin N) k) r i = (1 : Matrix (Fin N) (Fin N) k) r i := by
  have h1 := congrFun ((Subgroup.mem_inf.1 hw).2 i hi) r
  have hc : ((w : Matrix (Fin N) (Fin N) k) *ᵥ Pi.single i 1) r = (w : Matrix (Fin N) (Fin N) k) r i := by
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [hc] at h1
  rw [h1, Matrix.one_apply, Pi.single_apply]

theorem mem_derUnip_of_col {n : ℕ} {g : GL (Fin N) k} (hg : g ∈ unipB k (Fin N))
    (hc : ∀ r i : Fin N, (i : ℕ) < n →
      (g : Matrix (Fin N) (Fin N) k) r i = (1 : Matrix (Fin N) (Fin N) k) r i) :
    g ∈ derUnip k N n := by
  refine Subgroup.mem_inf.2 ⟨hg, fun i hi => ?_⟩
  ext r
  have e : ((g : Matrix (Fin N) (Fin N) k) *ᵥ Pi.single i 1) r = (g : Matrix (Fin N) (Fin N) k) r i := by
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [e, hc r i hi, Matrix.one_apply, Pi.single_apply]

theorem unipRad_le_derUnip : unipRad k (stdBlocks d h) ≤ derUnip k N (d 0) := by
  intro g hg
  have hE := (mem_unipRad_iff d h).1 hg
  refine mem_derUnip_of_col ((mem_unipB k).2 ⟨fun i j hji => ?_, fun i => ?_⟩) fun r i hi => ?_
  · have := Fin.lt_def.1 hji
    rw [hE i j (by omega), one_apply_ne (ne_of_gt hji)]
  · rw [hE i i (by omega), one_apply_eq]
  · exact hE r i (by omega)

def secEmb : GL (Fin (d 1)) k →* GL (Fin N) k := (leviEmb k (stdBlocks d h)).comp (secondEmb d)

theorem secEmb_one_one (u : GL (Fin (d 1)) k) (a b : Fin (d 1)) :
    (secEmb d h u : Matrix (Fin N) (Fin N) k) (stdBlocks d h ⟨1, a⟩) (stdBlocks d h ⟨1, b⟩) =
      (u : Matrix (Fin (d 1)) (Fin (d 1)) k) a b := by
  simp [secEmb, secondEmb]

theorem secEmb_zero_zero (u : GL (Fin (d 1)) k) (a b : Fin (d 0)) :
    (secEmb d h u : Matrix (Fin N) (Fin N) k) (stdBlocks d h ⟨0, a⟩) (stdBlocks d h ⟨0, b⟩) =
      (1 : Matrix (Fin (d 0)) (Fin (d 0)) k) a b := by
  simp [secEmb, secondEmb]

theorem secEmb_zero_one (u : GL (Fin (d 1)) k) (a : Fin (d 0)) (b : Fin (d 1)) :
    (secEmb d h u : Matrix (Fin N) (Fin N) k) (stdBlocks d h ⟨0, a⟩) (stdBlocks d h ⟨1, b⟩) = 0 :=
  leviEmb_apply_ne (m := fun a => Fin (d a)) k (stdBlocks d h) (secondEmb d u) (a := 0) (b := 1) (by decide) a b

theorem secEmb_one_zero (u : GL (Fin (d 1)) k) (a : Fin (d 1)) (b : Fin (d 0)) :
    (secEmb d h u : Matrix (Fin N) (Fin N) k) (stdBlocks d h ⟨1, a⟩) (stdBlocks d h ⟨0, b⟩) = 0 :=
  leviEmb_apply_ne (m := fun a => Fin (d a)) k (stdBlocks d h) (secondEmb d u) (a := 1) (b := 0) (by decide) a b

theorem secEmb_mem {u : GL (Fin (d 1)) k} (hu : u ∈ unipB k (Fin (d 1))) :
    secEmb d h u ∈ derUnip k N (d 0) := by
  obtain ⟨u1, u2⟩ := (mem_unipB k).1 hu
  refine mem_derUnip_of_col ((mem_unipB k).2 ⟨fun i j hji => ?_, fun i => ?_⟩) fun r i hi => ?_
  · have hlt := Fin.lt_def.1 hji
    rcases idx_cases d h i with ⟨a, rfl⟩ | ⟨a, rfl⟩ <;> rcases idx_cases d h j with ⟨b, rfl⟩ | ⟨b, rfl⟩
    · rw [secEmb_zero_zero, one_apply_ne]
      rintro rfl
      exact lt_irrefl _ hlt
    · exact secEmb_zero_one d h u a b
    · exact secEmb_one_zero d h u a b
    · rw [secEmb_one_one]
      rw [stdBlocks_one_val, stdBlocks_one_val] at hlt
      exact u1 a b (Fin.lt_def.2 (by omega))
  · rcases idx_cases d h i with ⟨a, rfl⟩ | ⟨a, rfl⟩
    · rw [secEmb_zero_zero, one_apply_eq]
    · rw [secEmb_one_one, u2]
  · rcases idx_cases d h i with ⟨b, rfl⟩ | ⟨b, rfl⟩
    · rcases idx_cases d h r with ⟨a, rfl⟩ | ⟨a, rfl⟩
      · rw [secEmb_zero_zero]
        by_cases e : a = b
        · subst e; simp
        · rw [one_apply_ne e, one_apply_ne fun e' => e (by simpa using e')]
      · rw [secEmb_one_zero, one_apply_ne]
        intro e'
        have h1 := congrArg Fin.val e'
        rw [stdBlocks_one_val, stdBlocks_zero_val] at h1
        have := b.2
        omega
    · rw [stdBlocks_one_val] at hi
      omega

theorem det_eq_one {m : ℕ} {u : GL (Fin m) k} (hu : u ∈ unipB k (Fin m)) :
    GeneralLinearGroup.det u = 1 := by
  obtain ⟨u1, u2⟩ := (mem_unipB k).1 hu
  ext
  rw [GeneralLinearGroup.val_det_apply, Matrix.det_of_upperTriangular (fun i j hij => u1 i j hij)]
  simp [u2]

theorem exists_decomp {w : GL (Fin N) k} (hw : w ∈ derUnip k N (d 0)) :
    ∃ r ∈ unipRad k (stdBlocks d h), ∃ u ∈ unipB k (Fin (d 1)), w = r * secEmb d h u := by
  have hB := (mem_unipB k).1 (derUnip_le_unipB k N (d 0) hw)
  have hp : w ∈ parab k (stdBlocks d h) := by
    refine mem_parab.2 fun i j hij => ?_
    rw [blk_two, blk_two] at hij
    refine hB.1 i j (Fin.lt_def.2 ?_)
    by_cases hi : (i : ℕ) < d 0 <;> by_cases hj : (j : ℕ) < d 0 <;> simp [hi, hj] at hij
    omega
  obtain ⟨r', hr', e1⟩ := exists_levi_mul_unip k (stdBlocks d h) ⟨w, hp⟩
  set l := leviProj k (stdBlocks d h) ⟨w, hp⟩ with hl
  have hl0 : l 0 = 1 := by
    ext i j
    rw [hl, leviProj_apply]
    have := derUnip_col hw (stdBlocks d h ⟨0, i⟩) (stdBlocks d h ⟨0, j⟩)
      (by rw [stdBlocks_zero_val]; exact j.2)
    refine this.trans ?_
    rw [Units.val_one]
    by_cases e : i = j
    · subst e; simp
    · rw [one_apply_ne e, one_apply_ne fun e' => e (by simpa using e')]
  have hlsec : l = secondEmb d (l 1) := by
    have key : ∀ a, l a = secondEmb d (l 1) a :=
      Fin.forall_fin_two.2 ⟨by simp [secondEmb, hl0], by simp [secondEmb]⟩
    exact funext key
  have hu : l 1 ∈ unipB k (Fin (d 1)) := by
    refine (mem_unipB k).2 ⟨fun a c hca => ?_, fun a => ?_⟩
    · rw [hl, leviProj_apply]
      refine hB.1 _ _ (Fin.lt_def.2 ?_)
      rw [stdBlocks_one_val, stdBlocks_one_val]
      have := Fin.lt_def.1 hca
      omega
    · rw [hl, leviProj_apply]
      exact hB.2 _
  have hs : secEmb d h (l 1) = leviEmb k (stdBlocks d h) l := by
    show leviEmb k (stdBlocks d h) (secondEmb d (l 1)) = _
    rw [← hlsec]
  have e1' : w = leviEmb k (stdBlocks d h) l * r' := e1
  refine ⟨leviEmb k (stdBlocks d h) l * r' * (leviEmb k (stdBlocks d h) l)⁻¹,
    (Subgroup.mem_normalizer_iff.1 (leviEmb_mem_normalizer k (stdBlocks d h) l) r').1 hr', l 1, hu, ?_⟩
  rw [hs]
  exact e1'.trans (by group)

end Groups

section Chars

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {N : ℕ} (d : Fin 2 → ℕ) (h : ∑ a, d a = N)

theorem derChar_eq_one_of_mem_unipRad (ψ : AddChar k Circle) (u : derUnip k N (d 0))
    (hu : (u : GL (Fin N) k) ∈ unipRad k (stdBlocks d h)) : derChar k ψ N (d 0) u = 1 := by
  have hE := (mem_unipRad_iff d h).1 hu
  show Circle.toUnits _ = 1
  rw [Finset.sum_eq_zero, AddChar.map_zero_eq_one, map_one]
  intro p hp
  obtain ⟨h1, h2⟩ := (Finset.mem_filter.1 hp).2
  refine (hE p.1 p.2 (by omega)).trans (one_apply_ne fun e => ?_)
  rw [e] at h1
  omega

theorem derChar_secEmb (ψ : AddChar k Circle) (u : unipB k (Fin (d 1)))
    (hs : secEmb d h (u : GL (Fin (d 1)) k) ∈ derUnip k N (d 0)) :
    derChar k ψ N (d 0) ⟨_, hs⟩ = whitChar ψ (d 1) u := by
  show Circle.toUnits _ = Circle.toUnits _
  refine congrArg _ (congrArg _ ?_)
  symm
  refine Finset.sum_bij (fun q _ => (stdBlocks d h ⟨1, q.1⟩, stdBlocks d h ⟨1, q.2⟩)) ?_ ?_ ?_ ?_
  · intro q hq
    have := (Finset.mem_filter.1 hq).2
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_, ?_⟩
    · simp only [stdBlocks_one_val]
      omega
    · simp only [stdBlocks_one_val]
      omega
  · rintro ⟨a, b⟩ _ ⟨a', b'⟩ _ e
    have e1 := (stdBlocks d h).injective (congrArg Prod.fst e)
    have e2 := (stdBlocks d h).injective (congrArg Prod.snd e)
    simp only [Sigma.mk.injEq, heq_eq_eq, true_and] at e1 e2
    simp [e1, e2]
  · rintro ⟨p1, p2⟩ hp
    obtain ⟨h1, h2⟩ := (Finset.mem_filter.1 hp).2
    simp only at h1 h2
    rcases idx_cases d h p1 with ⟨a, rfl⟩ | ⟨a, rfl⟩
    · rw [stdBlocks_zero_val] at h2
      have := a.2
      omega
    rcases idx_cases d h p2 with ⟨b, rfl⟩ | ⟨b, rfl⟩
    · rw [stdBlocks_zero_val, stdBlocks_one_val] at h1
      have := b.2
      omega
    refine ⟨(a, b), Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩, rfl⟩
    rw [stdBlocks_one_val, stdBlocks_one_val] at h1
    simp only
    omega
  · intro q _
    exact (secEmb_one_one d h _ q.1 q.2).symm

theorem deltaHalf_secondEmb {u : GL (Fin (d 1)) k} (hu : u ∈ unipB k (Fin (d 1))) :
    deltaHalf k (fun a => Fin (d a)) (secondEmb d u) = 1 := by
  rw [deltaHalf_apply]
  refine Finset.prod_eq_one fun a _ => ?_
  have key : ∀ a, GeneralLinearGroup.det ((secondEmb d u : Levi k fun a => Fin (d a)) a) = 1 :=
    Fin.forall_fin_two.2 ⟨by simp [secondEmb], by simpa [secondEmb] using det_eq_one hu⟩
  rw [key, map_one]

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem twKer_unipRad_le (ψ : AddChar k Circle) (π : Representation ℂ (GL (Fin N) k) V) :
    twKer π (unipRad k (stdBlocks d h)) 1 ≤ twKer π (derUnip k N (d 0)) (derChar k ψ N (d 0)) := by
  refine Submodule.span_mono ?_
  rintro _ ⟨u, v, rfl⟩
  refine ⟨⟨u, unipRad_le_derUnip d h u.2⟩, v, ?_⟩
  rw [derChar_eq_one_of_mem_unipRad d h ψ _ u.2]
  simp

theorem jac_secondEmb (π : Representation ℂ (GL (Fin N) k) V) {u : GL (Fin (d 1)) k}
    (hu : u ∈ unipB k (Fin (d 1))) (v : V) :
    jac (stdBlocks d h) π (secondEmb d u) (Submodule.Quotient.mk v) =
      Submodule.Quotient.mk (π (secEmb d h u) v) := by
  rw [jac_mk, deltaHalf_secondEmb d hu]
  simp [secEmb]

theorem whitKer_jac_eq_map (ψ : AddChar k Circle) (π : Representation ℂ (GL (Fin N) k) V) :
    whitKer ψ d (jac (stdBlocks d h) π) =
      (twKer π (derUnip k N (d 0)) (derChar k ψ N (d 0))).map
        (Submodule.mkQ (twKer π (unipRad k (stdBlocks d h)) 1)) := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨u, x, rfl⟩
    obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective _ x
    have hs := secEmb_mem d h u.2
    refine ⟨π (secEmb d h u) v - (whitChar ψ (d 1) u : ℂ) • v,
      Submodule.subset_span ⟨⟨_, hs⟩, v, ?_⟩, ?_⟩
    · rw [derChar_secEmb d h ψ u hs]
    · rw [map_sub, map_smul]
      exact congrArg₂ _ (jac_secondEmb d h π u.2 v).symm rfl
  · refine Submodule.map_le_iff_le_comap.2 (Submodule.span_le.2 ?_)
    rintro _ ⟨⟨w, hw⟩, v, rfl⟩
    obtain ⟨r, hr, u, hu, rfl⟩ := exists_decomp d h hw
    have hs := secEmb_mem d h hu
    have hc : derChar k ψ N (d 0) ⟨_, hw⟩ = whitChar ψ (d 1) ⟨u, hu⟩ := by
      have e : (⟨_, hw⟩ : derUnip k N (d 0)) = ⟨r, unipRad_le_derUnip d h hr⟩ * ⟨_, hs⟩ := rfl
      rw [e, map_mul, derChar_eq_one_of_mem_unipRad d h ψ _ hr, one_mul]
      exact derChar_secEmb d h ψ ⟨u, hu⟩ hs
    have hr' : Submodule.mkQ (twKer π (unipRad k (stdBlocks d h)) 1) (π (r * secEmb d h u) v) =
        Submodule.Quotient.mk (π (secEmb d h u) v) := by
      refine (Submodule.Quotient.eq _).2 (Submodule.subset_span ⟨⟨r, hr⟩, π (secEmb d h u) v, ?_⟩)
      simp
    rw [SetLike.mem_coe, Submodule.mem_comap]
    rw [hc, map_sub, map_smul, hr', ← jac_secondEmb d h π hu v]
    exact Submodule.subset_span ⟨⟨u, hu⟩, Submodule.Quotient.mk v, rfl⟩

theorem comap_whitKer_jac (ψ : AddChar k Circle) (π : Representation ℂ (GL (Fin N) k) V) :
    (whitKer ψ d (jac (stdBlocks d h) π)).comap
        (Submodule.mkQ (twKer π (unipRad k (stdBlocks d h)) 1)) =
      twKer π (derUnip k N (d 0)) (derChar k ψ N (d 0)) := by
  rw [whitKer_jac_eq_map, Submodule.comap_map_eq, Submodule.ker_mkQ]
  exact sup_eq_left.2 (twKer_unipRad_le d h ψ π)

end Chars

theorem whitKer_jac_comap_eq_twKer_derUnip : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (n j : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin (n + j + 1)) k) V) (hd : ∑ a, (![n, j + 1] a) = n + j + 1),
    (whitKer ψ ![n, j + 1] (jac (stdBlocks ![n, j + 1] hd) π)).comap
        (Submodule.mkQ (twKer π (unipRad k (stdBlocks ![n, j + 1] hd)) 1)) =
      twKer π (derUnip k (n + j + 1) n) (derChar k ψ (n + j + 1) n) :=
  fun _ _ _ _ _ ψ _ _ _ _ _ π hd => comap_whitKer_jac _ hd ψ π

end GlobalTheory.CompanionTheory.BZNuPair.DerComap

end
