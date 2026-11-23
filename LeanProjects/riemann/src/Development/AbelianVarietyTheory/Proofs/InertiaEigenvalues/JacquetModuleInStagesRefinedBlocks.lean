import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSubquotientOfEquiv
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FinSigmaFinEquivSymmStrictMonoToLex
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ParabolicModulusSqrtCharRefinedBlocksInStagesStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.JacStages

namespace GlobalTheory.JacStagesProof

section Groups

open Matrix

variable {R : Type} [CommRing R]

theorem mem_unipRad_iff_entries' {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
    [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
    {e : (Σ a, m a) ≃ n} {g : GL n R} :
    g ∈ unipRad R e ↔ ∀ i j, ¬ blk e i < blk e j → (g : Matrix n n R) i j = (1 : Matrix n n R) i j := by
  rw [mem_unipRad]
  constructor
  · rintro ⟨hp, hd⟩ i j hij
    rcases lt_or_eq_of_le (not_lt.1 hij) with h | h
    · rw [mem_parab.1 hp i j h, one_apply_ne (fun hij' => by rw [hij'] at h; exact lt_irrefl _ h)]
    · obtain ⟨⟨a, x⟩, rfl⟩ := e.surjective i
      obtain ⟨⟨b, y⟩, rfl⟩ := e.surjective j
      simp only [blk_apply] at h
      subst h
      rw [hd _ x y]
      simp only [one_apply, EmbeddingLike.apply_eq_iff_eq, Sigma.mk.injEq, heq_eq_eq, true_and]
  · intro h
    refine ⟨fun i j hji => ?_, fun a x y => ?_⟩
    · rw [h i j (not_lt.2 hji.le), one_apply_ne (fun hij' => by rw [hij'] at hji; exact lt_irrefl _ hji)]
    · rw [h _ _ (by simp)]
      simp only [one_apply, EmbeddingLike.apply_eq_iff_eq, Sigma.mk.injEq, heq_eq_eq, true_and]

variable {s n : ℕ} {d : Fin s → ℕ} {t : Fin s → ℕ} {d' : ∀ a, Fin (t a) → ℕ}

theorem sigma_eq_of_refine (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a)) (a : Fin s) (y : Fin (d a)) :
    ∀ (p : Σ a, Fin (t a)) (i : Fin (d' p.1 p.2)),
      (⟨p.1, e' p.1 ⟨p.2, i⟩⟩ : Σ a, Fin (d a)) = ⟨a, y⟩ → p = ⟨a, blk (e' a) y⟩ := by
  rintro ⟨a', b⟩ i h
  obtain ⟨rfl, h2⟩ := Sigma.mk.inj_iff.1 h
  obtain rfl := eq_of_heq h2
  simp

theorem symm_blk_refinePlace (e : (Σ a, Fin (d a)) ≃ Fin n) (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a))
    (a : Fin s) (y : Fin (d a)) :
    finSigmaFinEquiv.symm (blk (refinePlace e e') (e ⟨a, y⟩)) = ⟨a, blk (e' a) y⟩ := by
  obtain ⟨⟨c, i⟩, hc⟩ := (refinePlace e e').surjective (e ⟨a, y⟩)
  rw [← hc, blk_apply]
  rw [refinePlace_apply] at hc
  exact sigma_eq_of_refine e' a y _ i (e.injective hc)

theorem blk_eq_fst (e : (Σ a, Fin (d a)) ≃ Fin n) (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a)) (x : Fin n) :
    blk e x = (finSigmaFinEquiv.symm (blk (refinePlace e e') x)).1 := by
  obtain ⟨⟨a, y⟩, rfl⟩ := e.surjective x
  rw [symm_blk_refinePlace, blk_apply]

theorem blk_refine_lt_iff (e : (Σ a, Fin (d a)) ≃ Fin n) (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a))
    (x y : Fin n) :
    blk (refinePlace e e') x < blk (refinePlace e e') y ↔
      toLex (finSigmaFinEquiv.symm (blk (refinePlace e e') x)) <
        toLex (finSigmaFinEquiv.symm (blk (refinePlace e e') y)) :=
  (GlobalTheory.finSigmaFinEquiv_symm_strictMono_lex s t).lt_iff_lt.symm

theorem blk_refine_lt_of_lt (e : (Σ a, Fin (d a)) ≃ Fin n) (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a))
    {x y : Fin n} (h : blk e x < blk e y) : blk (refinePlace e e') x < blk (refinePlace e e') y := by
  rw [blk_refine_lt_iff]
  rw [blk_eq_fst e e', blk_eq_fst e e' y] at h
  exact Sigma.Lex.lt_def.2 (Or.inl h)

theorem blk_refine_lt_iff_same (e : (Σ a, Fin (d a)) ≃ Fin n) (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a))
    (a : Fin s) (x y : Fin (d a)) :
    blk (refinePlace e e') (e ⟨a, x⟩) < blk (refinePlace e e') (e ⟨a, y⟩) ↔ blk (e' a) x < blk (e' a) y := by
  rw [blk_refine_lt_iff, symm_blk_refinePlace, symm_blk_refinePlace, Sigma.Lex.lt_def]
  constructor
  · rintro (h | ⟨h, h2⟩)
    · exact absurd h (lt_irrefl _)
    · exact h2
  · intro h
    exact Or.inr ⟨rfl, h⟩

end Groups

end GlobalTheory.JacStagesProof

namespace GlobalTheory.JacStagesProof

section Groups2

open Matrix

variable {R : Type} [Field R] [ValuativeRel R] [TopologicalSpace R] [IsNonarchimedeanLocalField R] {s n : ℕ} {d : Fin s → ℕ} {t : Fin s → ℕ} {d' : ∀ a, Fin (t a) → ℕ}

theorem one_apply_e (e : (Σ a, Fin (d a)) ≃ Fin n) (a : Fin s) (x y : Fin (d a)) :
    (1 : Matrix (Fin n) (Fin n) R) (e ⟨a, x⟩) (e ⟨a, y⟩) = (1 : Matrix (Fin (d a)) (Fin (d a)) R) x y := by
  simp only [one_apply, EmbeddingLike.apply_eq_iff_eq, Sigma.mk.injEq, heq_eq_eq, true_and]

theorem unipRad_le_refine (e : (Σ a, Fin (d a)) ≃ Fin n) (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a)) :
    unipRad R e ≤ unipRad R (refinePlace e e') := by
  intro u hu
  rw [mem_unipRad_iff_entries'] at hu ⊢
  exact fun i j h => hu i j fun h' => h (blk_refine_lt_of_lt e e' h')

theorem leviEmb_mem_unipRad_refine (e : (Σ a, Fin (d a)) ≃ Fin n) (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a))
    (l : ∀ a, GL (Fin (d a)) R) (hl : l ∈ relUnipD R e') :
    leviEmb R e l ∈ unipRad R (refinePlace e e') := by
  rw [mem_unipRad_iff_entries']
  intro i j h
  obtain ⟨⟨a, x⟩, rfl⟩ := e.surjective i
  obtain ⟨⟨b, y⟩, rfl⟩ := e.surjective j
  by_cases hab : a = b
  · subst hab
    rw [leviEmb_apply_same, one_apply_e]
    have := mem_unipRad_iff_entries'.1 (hl a (Set.mem_univ a)) x y
      (fun h' => h ((blk_refine_lt_iff_same e e' a x y).2 h'))
    exact this
  · rw [leviEmb_apply_ne R e l hab, one_apply_ne]
    intro h'
    exact hab (congrArg Sigma.fst (e.injective h'))

theorem exists_decomp_refine (e : (Σ a, Fin (d a)) ≃ Fin n) (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a))
    (u : GL (Fin n) R) (hu : u ∈ unipRad R (refinePlace e e')) :
    ∃ l ∈ relUnipD R e', ∃ u' ∈ unipRad R e, u = leviEmb R e l * u' := by
  have hu' := mem_unipRad_iff_entries'.1 hu
  have hp : u ∈ parab R e := by
    refine mem_parab.2 fun i j hji => ?_
    have h1 := blk_refine_lt_of_lt e e' hji
    rw [hu' i j (not_lt.2 h1.le), one_apply_ne]
    rintro rfl
    exact lt_irrefl _ hji
  obtain ⟨w, hw, hdec⟩ := exists_levi_mul_unip R e ⟨u, hp⟩
  refine ⟨leviProj R e ⟨u, hp⟩, fun a _ => ?_, w, hw, hdec⟩
  show leviProj R e ⟨u, hp⟩ a ∈ unipRad R (e' a)
  rw [mem_unipRad_iff_entries']
  intro x y h
  rw [leviProj_apply, ← one_apply_e e]
  exact hu' _ _ fun h' => h ((blk_refine_lt_iff_same e e' a x y).1 h')

theorem leviEmb_relEmbD_ne (e : (Σ a, Fin (d a)) ≃ Fin n) (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a))
    (g : ∀ a b, GL (Fin (d' a b)) R) :
    ∀ (p p' : Σ a, Fin (t a)), p ≠ p' → ∀ (x : Fin (d' p.1 p.2)) (y : Fin (d' p'.1 p'.2)),
      (leviEmb R e (relEmbD R e' g) : Matrix (Fin n) (Fin n) R) (e ⟨p.1, e' _ ⟨p.2, x⟩⟩)
        (e ⟨p'.1, e' _ ⟨p'.2, y⟩⟩) = 0 := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ hne x y
  by_cases ha : a = a'
  · subst ha
    have hb : b ≠ b' := fun h => hne (by rw [h])
    rw [leviEmb_apply_same, relEmbD_apply]
    exact leviEmb_apply_ne R (e' a) (g a) hb x y
  · exact leviEmb_apply_ne R e _ ha _ _

theorem leviEmb_refine_flatHom (e : (Σ a, Fin (d a)) ≃ Fin n) (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a))
    (g : ∀ a b, GL (Fin (d' a b)) R) :
    leviEmb R (refinePlace e e') (flatHom (fun a b => GL (Fin (d' a b)) R) g) =
      leviEmb R e (relEmbD R e' g) := by
  ext i j
  obtain ⟨⟨c, x⟩, rfl⟩ := (refinePlace e e').surjective i
  obtain ⟨⟨c', y⟩, rfl⟩ := (refinePlace e e').surjective j
  by_cases hc : c = c'
  · subst hc
    rw [leviEmb_apply_same, refinePlace_apply, refinePlace_apply, leviEmb_apply_same, relEmbD_apply,
      leviEmb_apply_same, flatHom_apply]
  · rw [leviEmb_apply_ne R _ _ hc, refinePlace_apply, refinePlace_apply]
    exact (leviEmb_relEmbD_ne e e' g _ _ (fun h => hc (finSigmaFinEquiv.symm.injective h)) x y).symm

end Groups2

end GlobalTheory.JacStagesProof

namespace GlobalTheory.JacStagesProof

theorem deltaHalf_relUnipD {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {s : ℕ} {d : Fin s → ℕ} {t : Fin s → ℕ} {d' : ∀ a, Fin (t a) → ℕ}
    (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a)) (l : ∀ a, GL (Fin (d a)) k) (hl : l ∈ relUnipD k e') :
    deltaHalf k (fun a => Fin (d a)) l = 1 := by
  rw [deltaHalf_apply]
  refine Finset.prod_eq_one fun a _ => ?_
  rw [det_eq_one_of_mem_unipRad k (hl a (Set.mem_univ a)), map_one]

theorem jac_refinePlace_equiv : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (s n : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n) (t : Fin s → ℕ) (d' : ∀ a, Fin (t a) → ℕ)
    (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a)) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) k) V),
    Nonempty (Representation.Equiv ((jac (refinePlace e e') π).comp (flatHom fun a b => GL (Fin (d' a b)) k))
      (relJacD e' (jac e π))) := by
  intro k _ _ _ _ s n d e t d' e' V _ _ π
  classical
  set A := twKer π (unipRad k e) 1 with hA
  set B := twKer π (unipRad k (refinePlace e e')) 1 with hB
  set C : Submodule ℂ V := Submodule.span ℂ
    {w | ∃ (l : relUnipD k e') (v : V), w = π (leviEmb k e (l : ∀ a, GL (Fin (d a)) k)) v - v} with hC
  have hAB : A ≤ B := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨u, v, rfl⟩
    exact Submodule.subset_span ⟨⟨u, unipRad_le_refine e e' u.2⟩, v, rfl⟩
  have hCB : C ≤ B := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨l, v, rfl⟩
    exact Submodule.subset_span ⟨⟨_, leviEmb_mem_unipRad_refine e e' l.1 l.2⟩, v, by simp⟩
  have hBAC : B ≤ A ⊔ C := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨u, v, rfl⟩
    obtain ⟨l, hl, u', hu', hu⟩ := exists_decomp_refine e e' u.1 u.2
    have : π (u : GL (Fin n) k) v - ((1 : unipRad k (refinePlace e e') →* ℂˣ) u : ℂ) • v =
        (π u' v - ((1 : unipRad k e →* ℂˣ) ⟨u', hu'⟩ : ℂ) • v) +
          (π (leviEmb k e l) (π u' v) - π u' v) := by
      rw [hu, map_mul, Module.End.mul_apply]; simp
    rw [SetLike.mem_coe, this]
    exact Submodule.add_mem_sup (Submodule.subset_span ⟨⟨u', hu'⟩, v, rfl⟩)
      (Submodule.subset_span ⟨⟨l, hl⟩, π u' v, rfl⟩)
  have hK : twKer (jac e π) (relUnipD k e') 1 = B.map A.mkQ := by
    have hB' : B.map A.mkQ = C.map A.mkQ := by
      rw [le_antisymm hBAC (sup_le hAB hCB), Submodule.map_sup, Submodule.mkQ_map_self, bot_sup_eq]
    rw [hB', hC, Submodule.map_span]
    apply le_antisymm
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨l, x, rfl⟩
      obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      refine Submodule.subset_span ⟨_, ⟨l, v, rfl⟩, ?_⟩
      rw [jac_mk, deltaHalf_relUnipD e' l.1 l.2]
      simp
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨_, ⟨l, v, rfl⟩, rfl⟩
      refine Submodule.subset_span ⟨l, Submodule.Quotient.mk v, ?_⟩
      rw [jac_mk, deltaHalf_relUnipD e' l.1 l.2]
      simp
  let φ : (V ⧸ B) ≃ₗ[ℂ] (V ⧸ A) ⧸ twKer (jac e π) (relUnipD k e') 1 :=
    (Submodule.quotientQuotientEquivQuotient A B hAB).symm.trans (Submodule.quotEquivOfEq _ _ hK.symm)
  have hφ : ∀ v : V, φ (Submodule.Quotient.mk v) = Submodule.Quotient.mk (Submodule.Quotient.mk v) := by
    intro v
    simp only [φ, LinearEquiv.trans_apply]
    rw [show (Submodule.quotientQuotientEquivQuotient A B hAB).symm (Submodule.Quotient.mk v) =
      Submodule.Quotient.mk (Submodule.Quotient.mk v) from
        (LinearEquiv.symm_apply_eq _).2 rfl]
    rfl
  refine ⟨Representation.Equiv.mk φ fun g => ?_⟩
  refine Submodule.linearMap_qext _ (LinearMap.ext fun v => ?_)
  simp only [LinearMap.comp_apply, Submodule.mkQ_apply, LinearEquiv.coe_coe, MonoidHom.coe_comp,
    Function.comp_apply]
  rw [jac_mk, map_smul, hφ, hφ, relJacD_mk, jac_mk, leviEmb_refine_flatHom, GlobalTheory.T.parabolicModulusSqrtChar_refinedBlocks_in_stages k s d t d' e' g, Submodule.Quotient.mk_smul, smul_smul, mul_inv,
    Units.val_mul, mul_comm]

end GlobalTheory.JacStagesProof
