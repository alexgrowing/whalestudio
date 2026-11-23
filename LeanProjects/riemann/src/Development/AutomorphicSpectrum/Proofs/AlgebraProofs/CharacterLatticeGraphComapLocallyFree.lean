import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LieLatticeData
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LocFreeMapMkQIff
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeGoodBaseChangeStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.KernelGraphBaseChangeHoldsStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LocallyFreeBaseChangeQuotientStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Imports

open GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num.LatticeGoodness

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {F : Type} [Zero F] {n : ℕ}
  {Sg : Type} {r s : Sg → ℕ}

theorem mem_stepGraph_iff (D : LieLatticeData Ω F n Sg r s) (τ : Sg) (χ : F → Ω) (i : Fin n) (c : Ω)
    (m : Fin (r τ) → Ω) :
    (c, m) ∈ D.stepGraph τ χ i ↔
      ∃ g u, (g, m) ∈ D.Th τ ∧ u ∈ vanSub Ω F n ((i : ℕ) + 1) ∧
        c • (fun x : Fin n → F => χ (x i)) = g + u := by
  unfold LieLatticeData.stepGraph
  rw [AddSubgroup.mem_comap, AddSubgroup.mem_sup]
  constructor
  · rintro ⟨⟨g, m'⟩, hy, ⟨u, m''⟩, hz, he⟩
    obtain ⟨hu, hm⟩ := AddSubgroup.mem_prod.1 hz
    have hm0 : m'' = 0 := hm
    subst hm0
    have h1 : g + u = c • (fun x : Fin n → F => χ (x i)) := congrArg Prod.fst he
    have h2 : m' + 0 = m := congrArg Prod.snd he
    rw [add_zero] at h2
    subst h2
    exact ⟨g, u, hy, hu, h1.symm⟩
  · rintro ⟨g, u, hg, hu, he⟩
    refine ⟨(g, m), hg, (u, 0), AddSubgroup.mem_prod.2 ⟨hu, rfl⟩, ?_⟩
    exact Prod.ext he.symm (add_zero m)

theorem vanSub_apply_zero {i : ℕ} {u : (Fin n → F) → Ω} (hu : u ∈ vanSub Ω F n i) : u 0 = 0 := by
  have h := (Submodule.mem_pi.1 hu) (0 : Fin n → F) (fun _ _ => rfl)
  simpa using h

theorem stepGraph_stable [Fintype F] (D : LieLatticeData Ω F n Sg r s) {R : Subalgebra o Ω} {p : ℕ} {w : Ω}
    (hB : D.Base R p w) (τ : Sg) (χ : F → Ω) (i : Fin n) :
    ∀ a ∈ R, ∀ v ∈ D.stepGraph τ χ i, a • v ∈ D.stepGraph τ χ i := by
  rintro a ha ⟨c, m⟩ h
  obtain ⟨g, u, hg, hu, he⟩ := (mem_stepGraph_iff D τ χ i c m).1 h
  refine (mem_stepGraph_iff D τ χ i (a • c) (a • m)).2
    ⟨a • g, a • u, (hB.stable τ a ha).2.2 (g, m) hg, Submodule.smul_mem _ _ hu, ?_⟩
  rw [smul_assoc, he, smul_add]

theorem fst_mem_xId_of_mem_stepGraph [Fintype F] (D : LieLatticeData Ω F n Sg r s) {R : Subalgebra o Ω}
    {p : ℕ} {w : Ω} (hB : D.Base R p w) (τ : Sg) (χ : F → Ω) (i : Fin n) {c : Ω}
    {m : Fin (r τ) → Ω} (h : (c, m) ∈ D.stepGraph τ χ i) : c ∈ D.xId χ i := by
  obtain ⟨g, u, hg, hu, he⟩ := (mem_stepGraph_iff D τ χ i c m).1 h
  have hgM : g ∈ D.M := (((hB.th τ).1 g).1 ⟨m, hg⟩).1
  refine AddSubgroup.mem_comap.2 (AddSubgroup.mem_sup.2 ⟨g, hgM, u, hu, ?_⟩)
  exact he.symm

theorem exists_mem_stepGraph_of_mem_xId [Fintype F] (D : LieLatticeData Ω F n Sg r s) {R : Subalgebra o Ω}
    {p : ℕ} {w : Ω} (hB : D.Base R p w) (τ : Sg) (χ : F → Ω) (h0 : χ 0 = 0) (i : Fin n) {c : Ω}
    (h : c ∈ D.xId χ i) : ∃ m, (c, m) ∈ D.stepGraph τ χ i := by
  obtain ⟨g, hg, u, hu, he⟩ := AddSubgroup.mem_sup.1 (AddSubgroup.mem_comap.1 h)
  have he' : g + u = c • (fun x : Fin n → F => χ (x i)) := he
  have hu0 : u 0 = 0 := vanSub_apply_zero hu
  have hg0 : g 0 = 0 := by
    have := congrFun he' 0
    simpa [h0, hu0] using this
  obtain ⟨m, hm⟩ := ((hB.th τ).1 g).2 ⟨hg, hg0⟩
  exact ⟨m, (mem_stepGraph_iff D τ χ i c m).2 ⟨g, u, hm, hu, he'.symm⟩⟩

theorem zero_mem_stepGraph_iff (D : LieLatticeData Ω F n Sg r s) (τ : Sg) (χ : F → Ω) (i : Fin n)
    (m : Fin (r τ) → Ω) : (0, m) ∈ D.stepGraph τ χ i ↔ m ∈ D.kk τ ((i : ℕ) + 1) := by
  rw [mem_stepGraph_iff]
  constructor
  · rintro ⟨g, u, hg, hu, he⟩
    rw [zero_smul] at he
    have hgu : g = -u := eq_neg_of_add_eq_zero_left he.symm
    refine ⟨(g, m), ⟨hg, AddSubgroup.mem_prod.2 ⟨?_, trivial⟩⟩, rfl⟩
    rw [hgu]
    exact neg_mem hu
  · rintro ⟨⟨g, m'⟩, ⟨hg, hp⟩, rfl⟩
    have hv : g ∈ vanSub Ω F n ((i : ℕ) + 1) := (AddSubgroup.mem_prod.1 hp).1
    refine ⟨g, -g, hg, neg_mem hv, ?_⟩
    simp

theorem stepKer : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (w : Ω) (χ : Sg → F → Ω), CharData R p w χ → D.Base R p w → D.Good₁ R p χ → D.Good₂ R p χ → (∀ τ i, LocFree R 1 ((D.stepGraph τ (χ τ) i).comap (AddMonoidHom.inl _ _))) ∧ ∀ (C : Type) [Field C] [Algebra o C] [Algebra Ω C] [IsScalarTower o Ω C] (RC : Subalgebra o C), (∀ a ∈ R, algebraMap Ω C a ∈ RC) → ∀ τ i, ((D.bc RC).stepGraph τ (fun a => algebraMap Ω C (χ τ a)) i).comap (AddMonoidHom.inl _ _) = spanOver RC (algebraMap Ω C '' (D.stepGraph τ (χ τ) i).comap (AddMonoidHom.inl _ _)) := by
  intro o Ω _ _ _ F _ _ _ n Sg r s D R p w χ hχ hB hG1 hG2
  refine ⟨fun τ i => ?_, fun C _ _ _ _ RC hRC τ i => ?_⟩
  · have h0 : χ τ 0 = 0 := (hχ.2.2.2.2 τ).1
    exact (LocFreeSchanuel.main R 1 (r τ) (D.xId (χ τ) i)
      ((D.stepGraph τ (χ τ) i).map (AddMonoidHom.snd _ _)) (D.kk τ ((i : ℕ) + 1))
      (D.stepGraph τ (χ τ) i) (((GlobalTheory.T.lattice_good_base_change D R p w χ hχ hB hG1).1 τ).2.2.2 i) (hG2.step τ i)
      (hG2.kk τ _) (stepGraph_stable D hB τ (χ τ) i)
      (fun c m h => ⟨fst_mem_xId_of_mem_stepGraph D hB τ (χ τ) i h, ⟨(c, m), h, rfl⟩⟩)
      (fun c h => exists_mem_stepGraph_of_mem_xId D hB τ (χ τ) h0 i h)
      (zero_mem_stepGraph_iff D τ (χ τ) i)
      (by
        rintro _ ⟨⟨c, m⟩, h, rfl⟩
        exact ⟨c, h⟩)).2
  · have hst := stepGraph_stable D hB τ (χ τ) i
    rw [(GlobalTheory.T.kernel_graph_base_change_holds D R p w χ hχ hB hG1 C RC hRC τ).2 i]
    let sw := (AddEquiv.prodComm (M := Ω) (N := Fin (r τ) → Ω)).toAddMonoidHom
    let Δ' : AddSubgroup ((Fin (r τ) → Ω) × Ω) := (D.stepGraph τ (χ τ) i).map sw
    have hst' : ∀ a ∈ R, ∀ v ∈ Δ', a • v ∈ Δ' := by
      rintro a ha _ ⟨x, hx, rfl⟩
      exact ⟨a • x, hst a ha x hx, rfl⟩
    have hfst : Δ'.map (AddMonoidHom.fst _ _) =
        (D.stepGraph τ (χ τ) i).map (AddMonoidHom.snd _ _) := by
      rw [AddSubgroup.map_map]
      rfl
    have key := (GlobalTheory.T.locally_free_base_change_quotient R RC hRC (bcMap Ω C (Fin (r τ))) (Algebra.linearMap Ω C)
      (isBaseChange_bcMap Ω C _) (IsBaseChange.linearMap Ω C) Δ' ⊥ (r τ) hst'
      (hfst ▸ hG2.step τ i) bot_le (by
        intro a _ v hv
        rw [AddSubgroup.mem_bot] at hv ⊢
        rw [hv, smul_zero])).2
    have hsw := spanOver_swap RC (bcMap Ω C (Fin (r τ))) (Algebra.linearMap Ω C)
      (D.stepGraph τ (χ τ) i)
    have e1 : Δ'.comap (AddMonoidHom.inr _ _) =
        (D.stepGraph τ (χ τ) i).comap (AddMonoidHom.inl _ _) := by
      ext c
      constructor
      · rintro ⟨⟨c', m⟩, h, he⟩
        have h1 : m = 0 := congrArg Prod.fst he
        have h2 : c' = c := congrArg Prod.snd he
        subst h1 h2
        exact h
      · intro h
        exact ⟨_, h, rfl⟩
    have e2 : ∀ X : AddSubgroup (C × (Fin (r τ) → C)),
        (X.map (AddEquiv.prodComm (M := C) (N := Fin (r τ) → C)).toAddMonoidHom).comap
          (AddMonoidHom.inr _ _) = X.comap (AddMonoidHom.inl _ _) := by
      intro X
      ext c
      constructor
      · rintro ⟨⟨c', m⟩, h, he⟩
        have h1 : m = 0 := congrArg Prod.fst he
        have h2 : c' = c := congrArg Prod.snd he
        subst h1 h2
        exact h
      · intro h
        exact ⟨_, h, rfl⟩
    rw [hsw, e2, e1] at key
    exact key

end GlobalTheory.CompanionTheory.Ar.Num.LatticeGoodness
