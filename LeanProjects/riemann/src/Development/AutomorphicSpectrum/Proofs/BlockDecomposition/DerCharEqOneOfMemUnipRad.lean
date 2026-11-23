import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.RightWhit
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicTwistedKernelDerivativeZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedJacquetPhiMinusEquiv
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictionMirabolicTwistedKernel

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir

noncomputable section

namespace GlobalTheory.CompanionTheory.BZMirJac

section Abstract

variable {M V X Y : Type} [Group M] [AddCommGroup V] [Module ℂ V] [AddCommGroup X] [Module ℂ X]
  [AddCommGroup Y] [Module ℂ Y]

theorem equiv_of_common_quotient (ρ : Representation ℂ M X) (σ : Representation ℂ M Y) (T : M → V → V)
    (p : V →ₗ[ℂ] X) (q : V →ₗ[ℂ] Y) (hp : Function.Surjective p) (hq : Function.Surjective q)
    (hk : LinearMap.ker p = LinearMap.ker q) (hpT : ∀ m v, p (T m v) = ρ m (p v))
    (hqT : ∀ m v, q (T m v) = σ m (q v)) : Nonempty (ρ.Equiv σ) := by
  let e : X ≃ₗ[ℂ] Y := (p.quotKerEquivOfSurjective hp).symm.trans
    ((Submodule.quotEquivOfEq _ _ hk).trans (q.quotKerEquivOfSurjective hq))
  have he : ∀ v, e (p v) = q v := by
    intro v
    have h1 : (p.quotKerEquivOfSurjective hp).symm (p v) = Submodule.Quotient.mk v := by
      rw [LinearEquiv.symm_apply_eq]
      rfl
    show q.quotKerEquivOfSurjective hq (Submodule.quotEquivOfEq _ _ hk
      ((p.quotKerEquivOfSurjective hp).symm (p v))) = q v
    rw [h1]
    rfl
  refine ⟨Representation.Equiv.mk e fun m => LinearMap.ext fun x => ?_⟩
  obtain ⟨v, rfl⟩ := hp x
  show e (ρ m (p v)) = σ m (e (p v))
  rw [← hpT, he, he, hqT]

theorem ker_comp_mkQ (K₁ K : Submodule ℂ V) (q : (V ⧸ K₁) →ₗ[ℂ] X) (e : LinearMap.ker q = K.map K₁.mkQ)
    (hle : K₁ ≤ K) : LinearMap.ker (q ∘ₗ K₁.mkQ) = K := by
  rw [LinearMap.ker_comp, e, Submodule.comap_map_eq, Submodule.ker_mkQ, sup_eq_left.2 hle]

end Abstract

section Iter

variable (k : Type) [Field k]

noncomputable def embedding₂ (n : ℕ) : (j : ℕ) → GL (Fin n) k →* Mir k (n + j)
  | 0 => levi k n
  | j + 1 => ((levi k (n + j + 1)).comp (Mir k (n + j)).subtype).comp (embedding₂ n j)

end Iter

section IterRep

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem iterPhi_quotient (ψ : AddChar k Circle) (n : ℕ) : ∀ (j : ℕ) (τ : MRep k (n + j)),
    ∃ q : τ.V →ₗ[ℂ] TwJacquet (iterPhi k ψ j τ).ρ (MirUin k n) 1, Function.Surjective q ∧
      LinearMap.ker q = twKer τ.ρ (derUnipM k (n + j) n) (derCharM k ψ (n + j) n) ∧
      ∀ g v, q (τ.ρ (embedding₂ k n j g) v) = psiMinus k (iterPhi k ψ j τ).ρ g (q v)
  | 0, τ => ⟨Submodule.mkQ _, Submodule.mkQ_surjective _,
      (Submodule.ker_mkQ _).trans (GlobalTheory.CompanionTheory.BZMir.twKer_MirUin_eq_derUnipM k ψ n τ.V τ.ρ), fun _ _ => rfl⟩
  | j + 1, τ => by
    obtain ⟨q', hs, hk, hi⟩ := iterPhi_quotient ψ n j (MRep.phiM k ψ τ)
    have hnm : n ≤ n + j := Nat.le_add_right n j
    obtain ⟨e, hle⟩ := GlobalTheory.CompanionTheory.BZMirStep.twKer_twAct_eq_map τ.ρ (MirUin k (n + j + 1)) (mirChar k ψ (n + j)) _
      (levi_stab ψ (n + j)) (derUnipM k (n + j) n) (derCharM k ψ (n + j) n) (derUnipM k (n + j + 1) n)
      (derCharM k ψ (n + j + 1) n) (GlobalTheory.CompanionTheory.BZMirStep.MirUin_step ψ hnm) (GlobalTheory.CompanionTheory.BZMirStep.levi_step ψ hnm)
      (GlobalTheory.CompanionTheory.BZMirStep.derUnipM_decomp hnm)
    refine ⟨q' ∘ₗ Submodule.mkQ _, hs.comp (Submodule.mkQ_surjective _), ?_, fun g v => ?_⟩
    · exact ker_comp_mkQ _ _ q' (hk.trans e) hle
    · exact hi g (Submodule.Quotient.mk v)

end IterRep

section Concrete

variable {k : Type} [Field k]

theorem emb_inl_inl {n t N : ℕ} (h : n + t = N) (g : GL (Fin n) k × GL (Fin t) k) (i j : Fin n) :
    (emb₂ k (stdSum h) g : Matrix (Fin N) (Fin N) k) (stdSum h (Sum.inl i)) (stdSum h (Sum.inl j)) =
      (g.1 : Matrix (Fin n) (Fin n) k) i j := by
  rw [val_emb₂]
  simp [reindex_apply, submatrix_apply]

theorem emb_inl_inr {n t N : ℕ} (h : n + t = N) (g : GL (Fin n) k × GL (Fin t) k) (i : Fin n) (j : Fin t) :
    (emb₂ k (stdSum h) g : Matrix (Fin N) (Fin N) k) (stdSum h (Sum.inl i)) (stdSum h (Sum.inr j)) = 0 := by
  rw [val_emb₂]
  simp [reindex_apply, submatrix_apply]

theorem emb_inr_inl {n t N : ℕ} (h : n + t = N) (g : GL (Fin n) k × GL (Fin t) k) (i : Fin t) (j : Fin n) :
    (emb₂ k (stdSum h) g : Matrix (Fin N) (Fin N) k) (stdSum h (Sum.inr i)) (stdSum h (Sum.inl j)) = 0 := by
  rw [val_emb₂]
  simp [reindex_apply, submatrix_apply]

theorem emb_inr_inr {n t N : ℕ} (h : n + t = N) (g : GL (Fin n) k × GL (Fin t) k) (i j : Fin t) :
    (emb₂ k (stdSum h) g : Matrix (Fin N) (Fin N) k) (stdSum h (Sum.inr i)) (stdSum h (Sum.inr j)) =
      (g.2 : Matrix (Fin t) (Fin t) k) i j := by
  rw [val_emb₂]
  simp [reindex_apply, submatrix_apply]

theorem one_inl_inl {n t N : ℕ} (h : n + t = N) (i j : Fin n) :
    (1 : Matrix (Fin N) (Fin N) k) (stdSum h (Sum.inl i)) (stdSum h (Sum.inl j)) =
      (1 : Matrix (Fin n) (Fin n) k) i j := by
  simp [one_apply]

theorem one_inr_inr {n t N : ℕ} (h : n + t = N) (i j : Fin t) :
    (1 : Matrix (Fin N) (Fin N) k) (stdSum h (Sum.inr i)) (stdSum h (Sum.inr j)) =
      (1 : Matrix (Fin t) (Fin t) k) i j := by
  simp [one_apply]

theorem one_inl_inr {n t N : ℕ} (h : n + t = N) (i : Fin n) (j : Fin t) :
    (1 : Matrix (Fin N) (Fin N) k) (stdSum h (Sum.inl i)) (stdSum h (Sum.inr j)) = 0 := by
  simp [one_apply]

theorem one_inr_inl {n t N : ℕ} (h : n + t = N) (i : Fin t) (j : Fin n) :
    (1 : Matrix (Fin N) (Fin N) k) (stdSum h (Sum.inr i)) (stdSum h (Sum.inl j)) = 0 := by
  simp [one_apply]

theorem unipRad_entries {n t N : ℕ} (h : n + t = N) {g : GL (Fin N) k} (hg : g ∈ unipRad k (two (stdSum h)))
    (i j : Fin N) (hij : ¬ ((i : ℕ) < n ∧ n ≤ (j : ℕ))) :
    (g : Matrix (Fin N) (Fin N) k) i j = (1 : Matrix (Fin N) (Fin N) k) i j := by
  obtain ⟨hP, hD⟩ := mem_unipRad.1 hg
  obtain ⟨x, rfl⟩ := (stdSum h).surjective i
  obtain ⟨y, rfl⟩ := (stdSum h).surjective j
  rcases x with x | x <;> rcases y with y | y
  · rw [one_inl_inl]
    exact hD false x y
  · simp at hij
  · rw [one_inr_inl]
    exact mem_parab_iff.1 hP true false x y (by decide)
  · rw [one_inr_inr]
    exact hD true x y

theorem unipRad_le_derUnip {n t N : ℕ} (h : n + t = N) : unipRad k (two (stdSum h)) ≤ derUnip k N n := by
  intro g hg
  have hE := unipRad_entries h hg
  refine Subgroup.mem_inf.2 ⟨(mem_unipB k).2 ⟨fun i j hji => ?_, fun i => ?_⟩,
    (GlobalTheory.CompanionTheory.BZMirStep.mem_colFix_iff _).2 fun i j hj => hE i j (by omega)⟩
  · have := Fin.lt_def.1 hji
    rw [hE i j (by omega), one_apply_ne (ne_of_gt hji)]
  · rw [hE i i (by omega), one_apply_eq]

theorem emb_mem_derUnip {n t N : ℕ} (h : n + t = N) (a : rightUnip k n t) :
    emb₂ k (stdSum h) (a : GL (Fin n) k × GL (Fin t) k) ∈ derUnip k N n := by
  obtain ⟨⟨a1, a2⟩, ha⟩ := a
  obtain ⟨h1, h2⟩ := Subgroup.mem_prod.1 ha
  have h1' : a1 = 1 := Subgroup.mem_bot.1 h1
  subst h1'
  obtain ⟨u1, u2⟩ := (mem_unipB k).1 h2
  refine Subgroup.mem_inf.2 ⟨(mem_unipB k).2 ⟨fun i j hji => ?_, fun i => ?_⟩,
    (GlobalTheory.CompanionTheory.BZMirStep.mem_colFix_iff _).2 fun i j hj => ?_⟩
  · obtain ⟨x, rfl⟩ := (stdSum h).surjective i
    obtain ⟨y, rfl⟩ := (stdSum h).surjective j
    have hlt := Fin.lt_def.1 hji
    rcases x with x | x <;> rcases y with y | y
    · rw [emb_inl_inl]
      refine one_apply_ne fun e => ?_
      subst e
      exact lt_irrefl _ hlt
    · simp at hlt
      have := x.2
      omega
    · exact emb_inr_inl h _ x y
    · rw [emb_inr_inr]
      refine u1 x y (Fin.lt_def.2 ?_)
      simp at hlt
      exact hlt
  · obtain ⟨x, rfl⟩ := (stdSum h).surjective i
    rcases x with x | x
    · rw [emb_inl_inl]
      simp
    · rw [emb_inr_inr]
      exact u2 x
  · obtain ⟨x, rfl⟩ := (stdSum h).surjective i
    obtain ⟨y, rfl⟩ := (stdSum h).surjective j
    rcases y with y | y
    · rcases x with x | x
      · rw [emb_inl_inl, one_inl_inl]
        rfl
      · rw [emb_inr_inl, one_inr_inl]
    · simp at hj

theorem derUnip_decomp {n t N : ℕ} (h : n + t = N) (u : derUnip k N n) :
    ∃ u₁ : unipRad k (two (stdSum h)), ∃ a : rightUnip k n t,
      (u : GL (Fin N) k) = u₁ * emb₂ k (stdSum h) (a : GL (Fin n) k × GL (Fin t) k) := by
  obtain ⟨hB, hC⟩ := Subgroup.mem_inf.1 u.2
  rw [mem_unipB] at hB
  rw [GlobalTheory.CompanionTheory.BZMirStep.mem_colFix_iff] at hC
  have hP : (u : GL (Fin N) k) ∈ parab k (two (stdSum h)) := by
    refine mem_parab_iff.2 ?_
    rintro (_ | _) (_ | _) i j hab
    · exact absurd hab (by decide)
    · exact absurd hab (by decide)
    · show ((u : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) (stdSum h (Sum.inr i)) (stdSum h (Sum.inl j)) = 0
      rw [hC _ _ (by simp), one_inr_inl]
    · exact absurd hab (by decide)
  let p : parab k (two (stdSum h)) := ⟨u, hP⟩
  let L := leviProj k (two (stdSum h)) p
  have hL1 : L false = 1 := by
    ext i j
    show ((u : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) (stdSum h (Sum.inl i)) (stdSum h (Sum.inl j)) = _
    rw [hC _ _ (by simp), one_inl_inl]
    rfl
  have hL2 : L true ∈ unipB k (Fin t) := by
    refine (mem_unipB k).2 ⟨fun i j hji => ?_, fun i => ?_⟩
    · show ((u : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) (stdSum h (Sum.inr i)) (stdSum h (Sum.inr j)) = 0
      refine hB.1 _ _ (Fin.lt_def.2 ?_)
      have := Fin.lt_def.1 hji
      simp
      exact this
    · exact hB.2 _
  have hLL : leviTwo k (Fin n) (Fin t) (L false, L true) = L := (leviTwo k (Fin n) (Fin t)).apply_symm_apply L
  let q : parab k (two (stdSum h)) := ⟨_, leviEmb_mem_parab k (two (stdSum h)) L⟩
  have hq : (q : GL (Fin N) k) = emb₂ k (stdSum h) (L false, L true) := by
    show leviEmb k (two (stdSum h)) L = leviEmb k (two (stdSum h)) (leviTwo k (Fin n) (Fin t) (L false, L true))
    rw [hLL]
  have hm : ((p * q⁻¹ : parab k (two (stdSum h))) : GL (Fin N) k) ∈ unipRad k (two (stdSum h)) := by
    refine (coe_mem_unipRad k _).2 ?_
    rw [map_mul, map_inv, leviProj_leviEmb]
    exact mul_inv_cancel _
  refine ⟨⟨_, hm⟩, ⟨(L false, L true), Subgroup.mem_prod.2 ⟨Subgroup.mem_bot.2 hL1, hL2⟩⟩, ?_⟩
  show (u : GL (Fin N) k) = ((p * q⁻¹ : parab k (two (stdSum h))) : GL (Fin N) k) * emb₂ k (stdSum h) (L false, L true)
  rw [← hq]
  simp [p]

end Concrete

section ConcreteChar

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem derChar_eq_one_of_mem_unipRad {n t N : ℕ} (ψ : AddChar k Circle) (h : n + t = N)
    (u : derUnip k N n) (hu : (u : GL (Fin N) k) ∈ unipRad k (two (stdSum h))) : derChar k ψ N n u = 1 := by
  have hE := unipRad_entries h hu
  show Circle.toUnits _ = 1
  rw [Finset.sum_eq_zero, AddChar.map_zero_eq_one, map_one]
  intro p hp
  obtain ⟨h1, h2⟩ := (Finset.mem_filter.1 hp).2
  refine (hE p.1 p.2 (by omega)).trans (one_apply_ne fun e => ?_)
  rw [e] at h1
  omega

theorem derChar_emb {n t N : ℕ} (ψ : AddChar k Circle) (h : n + t = N) (a : rightUnip k n t) :
    derChar k ψ N n ⟨_, emb_mem_derUnip h a⟩ = rightWhit k ψ n t a := by
  obtain ⟨⟨a1, a2⟩, ha⟩ := a
  show Circle.toUnits (ψ _) = Circle.toUnits (ψ _)
  congr 2
  symm
  refine Finset.sum_nbij (fun q => (stdSum h (Sum.inr q.1), stdSum h (Sum.inr q.2))) ?_ ?_ ?_ ?_
  · intro q hq
    have hc := (Finset.mem_filter.1 hq).2
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_, ?_⟩
    · simp only [stdSum_inr]
      omega
    · simp only [stdSum_inr]
      omega
  · rintro ⟨a, b⟩ _ ⟨c, d⟩ _ e
    simpa using e
  · rintro ⟨i, j⟩ hp
    obtain ⟨h1, h2⟩ := (Finset.mem_filter.1 (Finset.mem_coe.1 hp)).2
    obtain ⟨x, rfl⟩ := (stdSum h).surjective i
    obtain ⟨y, rfl⟩ := (stdSum h).surjective j
    rcases x with x | x
    · simp only [stdSum_inl] at h2
      have := x.2
      omega
    rcases y with y | y
    · simp only [stdSum_inl, stdSum_inr] at h1
      have := y.2
      omega
    refine ⟨(x, y), Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩), rfl⟩
    simp only [stdSum_inr] at h1
    show (y : ℕ) = x + 1
    omega
  · intro q _
    exact (emb_inr_inr (k := k) h (a1, a2) q.1 q.2).symm

theorem emb_stab {n t N : ℕ} (h : n + t = N) (m : GL (Fin n) k × GL (Fin t) k) (x : unipRad k (two (stdSum h))) :
    ∃ hh : emb₂ k (stdSum h) m * (x : GL (Fin N) k) * (emb₂ k (stdSum h) m)⁻¹ ∈ unipRad k (two (stdSum h)),
      (1 : unipRad k (two (stdSum h)) →* ℂˣ) ⟨_, hh⟩ = (1 : unipRad k (two (stdSum h)) →* ℂˣ) x := by
  have hm : leviEmb k (two (stdSum h)) (leviTwo k (Fin n) (Fin t) m) ∈
      Subgroup.normalizer (unipRad k (two (stdSum h)) : Set (GL (Fin N) k)) :=
    leviEmb_mem_normalizer k (two (stdSum h)) _
  exact ⟨(Subgroup.mem_normalizer_iff.1 hm (x : GL (Fin N) k)).1 x.2, by simp only [MonoidHom.one_apply]⟩

theorem jacU₂_eq_twAct {n t N : ℕ} (h : n + t = N) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) :
    jacU₂ (stdSum h) π = twAct π (unipRad k (two (stdSum h))) 1 (emb₂ k (stdSum h)) (emb_stab h) :=
  MonoidHom.ext fun _ => rfl

theorem derRep_quotient {n t N : ℕ} (ψ : AddChar k Circle) (h : n + t = N) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) :
    ∃ q : V →ₗ[ℂ] TwJacquet (jacU₂ (stdSum h) π) (rightUnip k n t) (rightWhit k ψ n t), Function.Surjective q ∧
      LinearMap.ker q = twKer π (derUnip k N n) (derChar k ψ N n) ∧
      ∀ g v, q (π (emb₂ k (stdSum h) (g, 1)) v) = derRep k ψ h π g (q v) := by
  obtain ⟨e, hle⟩ := GlobalTheory.CompanionTheory.BZMirStep.twKer_twAct_eq_map π (unipRad k (two (stdSum h))) 1 (emb₂ k (stdSum h))
    (emb_stab h) (rightUnip k n t) (rightWhit k ψ n t) (derUnip k N n) (derChar k ψ N n)
    (fun u => ⟨unipRad_le_derUnip h u.2, derChar_eq_one_of_mem_unipRad ψ h _ u.2⟩)
    (fun a => ⟨emb_mem_derUnip h a, derChar_emb ψ h a⟩) (derUnip_decomp h)
  rw [← jacU₂_eq_twAct h π] at e
  refine ⟨Submodule.mkQ _ ∘ₗ Submodule.mkQ _, (Submodule.mkQ_surjective _).comp (Submodule.mkQ_surjective _), ?_,
    fun g v => rfl⟩
  exact ker_comp_mkQ _ _ _ ((Submodule.ker_mkQ _).trans e) hle

end ConcreteChar

section Entries

variable {k : Type} [Field k]

theorem glEmbMat_block_apply {n m : ℕ} (hnm : n ≤ m) (g : Matrix (Fin n) (Fin n) k) (A : Matrix (Fin m) (Fin m) k)
    (hA : ∀ r s : Fin m, A r s = if h : (r : ℕ) < n ∧ (s : ℕ) < n then g ⟨r, h.1⟩ ⟨s, h.2⟩
      else (1 : Matrix (Fin m) (Fin m) k) r s) (r s : Fin (m + 1)) :
    glEmbMat k m A r s = if h : (r : ℕ) < n ∧ (s : ℕ) < n then g ⟨r, h.1⟩ ⟨s, h.2⟩
      else (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) r s := by
  induction r using Fin.lastCases with
  | last =>
    rw [dif_neg (fun h => by have := h.1; simp at this; omega)]
    induction s using Fin.lastCases with
    | last => rw [GlobalTheory.CompanionTheory.BZMirStep.glEmbMat_last_last, one_apply_eq]
    | cast s => rw [GlobalTheory.CompanionTheory.BZMirStep.glEmbMat_last_castSucc, one_apply_ne (Fin.castSucc_ne_last s).symm]
  | cast r =>
    induction s using Fin.lastCases with
    | last =>
      rw [dif_neg (fun h => by have := h.2; simp at this; omega), GlobalTheory.CompanionTheory.BZMirStep.glEmbMat_castSucc_last,
        one_apply_ne (Fin.castSucc_ne_last r)]
    | cast s =>
      rw [GlobalTheory.CompanionTheory.BZMirStep.glEmbMat_castSucc_castSucc, hA r s]
      by_cases h : (r : ℕ) < n ∧ (s : ℕ) < n
      · rw [dif_pos h, dif_pos (by simpa using h)]
        rfl
      · rw [dif_neg h, dif_neg (by simpa using h)]
        simp [one_apply]

theorem iotaM_apply (n : ℕ) (g : GL (Fin n) k) : ∀ (j : ℕ) (r s : Fin (n + j + 1)),
    (((embedding₂ k n j g : Mir k (n + j)) : GL (Fin (n + j + 1)) k) : Matrix (Fin (n + j + 1)) (Fin (n + j + 1)) k) r s =
      if h : (r : ℕ) < n ∧ (s : ℕ) < n then (g : Matrix (Fin n) (Fin n) k) ⟨r, h.1⟩ ⟨s, h.2⟩
      else (1 : Matrix (Fin (n + j + 1)) (Fin (n + j + 1)) k) r s
  | 0, r, s => glEmbMat_block_apply le_rfl (g : Matrix (Fin n) (Fin n) k) (g : Matrix (Fin n) (Fin n) k)
      (fun r s => by rw [dif_pos ⟨r.2, s.2⟩]) r s
  | j + 1, r, s => glEmbMat_block_apply (by omega) (g : Matrix (Fin n) (Fin n) k) _ (iotaM_apply n g j) r s

theorem iotaM_eq_emb (n j : ℕ) (g : GL (Fin n) k) :
    ((embedding₂ k n j g : Mir k (n + j)) : GL (Fin (n + j + 1)) k) =
      emb₂ k (stdSum (rfl : n + (j + 1) = n + j + 1)) (g, 1) := by
  apply Units.ext
  ext r s
  rw [iotaM_apply]
  obtain ⟨x, rfl⟩ := (stdSum (rfl : n + (j + 1) = n + j + 1)).surjective r
  obtain ⟨y, rfl⟩ := (stdSum (rfl : n + (j + 1) = n + j + 1)).surjective s
  rcases x with x | x <;> rcases y with y | y
  · rw [emb_inl_inl, dif_pos (by simp)]
    congr 1
  · rw [emb_inl_inr, dif_neg (by simp), one_inl_inr]
  · rw [emb_inr_inl, dif_neg (by simp), one_inr_inl]
  · rw [emb_inr_inr, dif_neg (by simp), one_inr_inr]
    rfl

end Entries

theorem deriv_equiv_derRep : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (n j : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin (n + j + 1)) k) V),
    Nonempty ((deriv k ψ j π).Equiv (derRep k ψ (rfl : n + (j + 1) = n + j + 1) π)) := by
  intro k _ _ _ _ ψ n j V _ _ π
  obtain ⟨p, hp, hpk, hpi⟩ := iterPhi_quotient ψ n j (resM k π)
  obtain ⟨q, hq, hqk, hqi⟩ := derRep_quotient ψ (rfl : n + (j + 1) = n + j + 1) π
  refine equiv_of_common_quotient (deriv k ψ j π) (derRep k ψ (rfl : n + (j + 1) = n + j + 1) π)
    (fun g v => π (emb₂ k (stdSum (rfl : n + (j + 1) = n + j + 1)) (g, 1)) v) p q hp hq ?_ ?_ hqi
  · exact hpk.trans ((GlobalTheory.CompanionTheory.BZMirDer.twKer_resM_derUnipM k ψ (n + j) n V π).trans hqk.symm)
  · intro g v
    rw [← iotaM_eq_emb]
    exact hpi g v

end GlobalTheory.CompanionTheory.BZMirJac

end
