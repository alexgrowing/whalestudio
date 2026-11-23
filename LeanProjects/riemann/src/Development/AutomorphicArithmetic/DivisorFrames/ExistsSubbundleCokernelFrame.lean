import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFrameOfBijectiveStalk
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.VB
open GlobalTheory.QCoh (pullbackSections)
open GlobalTheory.Twist (resM)

private theorem UpperTheory.frame_defines_endomorphism {X : Scheme.{0}} {E : X.Modules} {ι : Type} [Fintype ι]
    {e : ι → Γ(E, ⊤)} (he : IsFrame e) (q : ι → Γ(E, ⊤)) :
    ∃ p : E ⟶ E, ∀ j, p.app ⊤ (e j) = q j := by
  refine ⟨LB.homOfLinear (fun V => (he.basis (le_top : V ≤ ⊤)).constr ℕ
    (fun j => resM E (le_top : V ≤ ⊤) (q j))) ?_, fun j => ?_⟩
  · intro V W h s
    have key (V : X.Opens) (j : ι) : (he.basis (le_top : V ≤ ⊤)).constr ℕ
        (fun j => resM E (le_top : V ≤ ⊤) (q j)) (resM E le_top (e j)) = resM E le_top (q j) := by
      rw [← he.basis_apply, Module.Basis.constr_basis]
    obtain ⟨c, rfl⟩ := (he V le_top).2 s
    change (he.basis (le_top : W ≤ ⊤)).constr ℕ (fun j => resM E (le_top : W ≤ ⊤) (q j)) (resM E h _) =
      resM E h _
    simp only [Fintype.linearCombination_apply, map_sum, Twist.resM_smul, Twist.resM_resM,
      map_smul, key]
  · rw [LB.homOfLinear_app]
    have := (he.basis (le_top : (⊤ : X.Opens) ≤ ⊤)).constr_basis ℕ
      (fun j => resM E (le_top : (⊤ : X.Opens) ≤ ⊤) (q j)) j
    rwa [he.basis_apply, Twist.resM_self, Twist.resM_self] at this

theorem UpperTheory.exists_subbundle_cokernel_frame :
    ∀ (X : Scheme.{0}) (E : X.Modules) (m r : ℕ) (e : Fin m ⊕ Fin r → Γ(E, ⊤)) (a : Fin m → Fin r → Γ(X, ⊤)),
        IsFrame e → ∃ N : GlobalTheory.VB.Sub E, IsFrame (fun k => (cokernel.π N.incl).app ⊤ (e (Sum.inr k))) ∧
          ∀ i, (cokernel.π N.incl).app ⊤ (e (Sum.inl i)) = ∑ k, a i k • (cokernel.π N.incl).app ⊤ (e (Sum.inr k)) := by
  intro X E m r e a he
  obtain ⟨p, hp⟩ := UpperTheory.frame_defines_endomorphism he
    (Sum.elim (fun i => ∑ k, a i k • e (Sum.inr k)) (fun k => e (Sum.inr k)))
  have hr (k : Fin r) : p.app ⊤ (e (Sum.inr k)) = e (Sum.inr k) := hp _
  have hl (i : Fin m) : p.app ⊤ (e (Sum.inl i)) = ∑ k, a i k • e (Sum.inr k) := hp _
  have hz (V : X.Opens) (s : Γ(E, V)) :
      (cokernel.π (Sub.ker p).incl).app V s = 0 ↔ p.app V s = 0 :=
    (Sub.ker p).cokernel_π_app_eq_zero_iff
  have h2 (i : Fin m) : (cokernel.π (Sub.ker p).incl).app ⊤ (e (Sum.inl i)) =
      ∑ k, a i k • (cokernel.π (Sub.ker p).incl).app ⊤ (e (Sum.inr k)) := by
    simp only [← Scheme.Modules.Hom.app_smul]
    rw [← map_sum, ← sub_eq_zero, ← map_sub, hz, map_sub, hl, map_sum]
    simp only [Scheme.Modules.Hom.app_smul, hr, sub_self]
  refine ⟨Sub.ker p, ?_, h2⟩
  have hgen (V : X.Opens) (h : V ≤ ⊤) (s : Γ(E, V)) : (cokernel.π (Sub.ker p).incl).app V s ∈
      Submodule.span Γ(X, V) (Set.range fun k =>
        resM _ h ((cokernel.π (Sub.ker p).incl).app ⊤ (e (Sum.inr k)))) := by
    obtain ⟨c, rfl⟩ := (he V h).2 s
    rw [Fintype.linearCombination_apply, map_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [Scheme.Modules.Hom.app_smul, Twist.app_resM]
    refine Submodule.smul_mem _ _ ?_
    rcases j with i | k
    · rw [h2, map_sum]
      refine Submodule.sum_mem _ fun k _ => ?_
      rw [Twist.resM_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
    · exact Submodule.subset_span ⟨k, rfl⟩
  have hpp (V : X.Opens) (s : Γ(E, V)) : p.app V (p.app V s) = p.app V s := by
    obtain ⟨c, rfl⟩ := (he V le_top).2 s
    simp only [Fintype.linearCombination_apply, map_sum, Scheme.Modules.Hom.app_smul,
      Twist.app_resM]
    refine Finset.sum_congr rfl fun j _ => ?_
    rcases j with i | k
    · simp only [hl, map_sum, Scheme.Modules.Hom.app_smul, hr]
    · simp only [hr]
  have h0 : (Sub.ker p).incl ≫ p = 0 := by
    refine Scheme.Modules.hom_ext _ _ fun V => ?_
    ext s
    exact (QCoh.app_app _ _ V s).symm.trans ((Sub.ker p).incl_app_mem s)
  have h1 : cokernel.desc _ p h0 ≫ cokernel.π (Sub.ker p).incl = 𝟙 _ := by
    rw [← cancel_epi (cokernel.π (Sub.ker p).incl), cokernel.π_desc_assoc, Category.comp_id]
    refine Scheme.Modules.hom_ext _ _ fun V => ?_
    ext s
    refine (QCoh.app_app _ _ V s).symm.trans ?_
    change _ = (cokernel.π (Sub.ker p).incl).app V s
    rw [← sub_eq_zero, ← map_sub, hz, map_sub, hpp, sub_self]
  refine isFrame_iff.2 fun V h => ⟨?_, fun t _ => ?_⟩
  · have hli := ((isFrame_iff.1 he V h).1).comp Sum.inr Sum.inr_injective
    rw [Fintype.linearIndependent_iff] at hli ⊢
    intro c hc
    apply hli c
    simp only [← Twist.app_resM, ← Scheme.Modules.Hom.app_smul] at hc
    rw [← map_sum, hz, map_sum] at hc
    simpa only [Scheme.Modules.Hom.app_smul, Twist.app_resM, hr, Function.comp_apply] using hc
  · have := hgen V h ((cokernel.desc _ p h0).app V t)
    rwa [QCoh.app_app, h1] at this
