import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.ResidueOfTraceIsFiberSum

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

namespace UpperTheory.Gal.productCup_of_system

section
variable {A : Type} [Field A] [Algebra ℂ A]

end

end UpperTheory.Gal.productCup_of_system

private theorem stab_lemma {L : Type} [Field L] [Algebra ℂ L] (B : Subalgebra ℂ L) (q : ℕ) :
    Stab (Algebra.lsmul ℂ ℂ (DR ℂ L)) B (omB ℂ L B q) := by
  intro b hb m hm
  change b • m ∈ omB ℂ L B q
  induction hm using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, ha, v, hv, rfl⟩ := hy
    apply Submodule.subset_span
    exact ⟨b * a, B.mul_mem hb ha, v, hv, by rw [mul_smul]⟩
  | zero => rw [smul_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [smul_add]; exact Submodule.add_mem _ hy hz
  | smul c y _ hy => rw [smul_comm]; exact Submodule.smul_mem _ c hy

private theorem kos_Z_mono_of_le {S E : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E]
    (act : S →ₐ[ℂ] Module.End ℂ E) {κ : Type} [LinearOrder κ] {M M' : Submodule ℂ E}
    (h : M ≤ M') (r : κ → S) (m : ℤ) : (kos act M r).Z m ≤ (kos act M' r).Z m := by
  intro c hc
  simp only [GlobalTheory.PD.Cx.Z, kos, acx, Submodule.mem_inf, Submodule.mem_pi, Set.mem_univ,
    forall_const, true_implies, LinearMap.mem_ker] at hc ⊢
  refine ⟨fun s => ?_, hc.2⟩
  have hs := hc.1 s
  split_ifs at hs ⊢ with hcard
  · exact h hs
  · exact hs

theorem UpperTheory.Gal.productCup_of_system.yKE_of :
    LG → OmLoc → RYFT → Htpy → K1 → LocReg → ValBasic → RYBasic → YKE := by
  intro hLG hOm hFT hH hK1 hLR hVB hRB F K K' _ _ _ _ _ _ _ _ _ _ _ _ _ d x j2 hY κ _ _ r I J hI hr
  have hact : (sysY x j2 d).act = Algebra.lsmul ℂ ℂ (DR ℂ K') := rfl
  have hM : (sysY x j2 d).M I J = omB ℂ K' (RY (xv x) j2 I J) d := rfl
  rw [hact, hM]
  haveI : Algebra.FiniteType ℂ ↥(RY (xv x) j2 I J) := hFT F K K' d x j2 hY I J hI
  set B := RY (xv x) j2 I J with hB
  have hglob : ∀ (m : ℤ) (c : Finset κ → DR ℂ K'),
      (∀ e : ↥B →ₐ[ℂ] ℂ, c ∈ (kos (Algebra.lsmul ℂ ℂ (DR ℂ K')) (omB ℂ K' (loc B e) d) r).B m) →
      c ∈ (kos (Algebra.lsmul ℂ ℂ (DR ℂ K')) (omB ℂ K' B d) r).B m := by
    intro m c hc
    refine (hLG K' B (DR ℂ K') κ (fun _ => omB ℂ K' B d) r (fun _ => stab_lemma B d)).1 m c
      (fun e => ?_)
    simp only [(hOm K' B e d).1]
    exact hc e
  have hloc : ∀ e : ↥B →ₐ[ℂ] ℂ, ¬ (∀ l, Val B e (r l) 0) → ∃ l, r l ≠ 0 ∧ (r l)⁻¹ ∈ loc B e := by
    intro e h
    push_neg at h
    obtain ⟨l, hl⟩ := h
    obtain ⟨-, -, hval, hinv⟩ := hVB K' B e
    have hv := hval ⟨r l, hr l⟩
    have hc0 : e ⟨r l, hr l⟩ ≠ 0 := by
      intro h0
      rw [h0] at hv
      exact hl hv
    exact ⟨l, hinv _ _ hv hc0⟩
  have hle : ∀ e : ↥B →ₐ[ℂ] ℂ, omB ℂ K' B d ≤ omB ℂ K' (loc B e) d :=
    fun e => (hOm K' B e d).2.2 _ (hVB K' B e).1
  have hbad : ∀ (m : ℤ) (c : Finset κ → DR ℂ K'),
      c ∈ (kos (Algebra.lsmul ℂ ℂ (DR ℂ K')) (omB ℂ K' B d) r).Z m →
      ∀ e : ↥B →ₐ[ℂ] ℂ, ¬ (∀ l, Val B e (r l) 0) →
      c ∈ (kos (Algebra.lsmul ℂ ℂ (DR ℂ K')) (omB ℂ K' (loc B e) d) r).B m := by
    intro m c hc e h
    obtain ⟨l, hl0, hlinv⟩ := hloc e h
    have hIn : InSp (loc B e) r 1 := by
      refine ⟨fun l' => if l' = l then (r l)⁻¹ else 0, fun l' => ?_, ?_⟩
      · dsimp only
        split_ifs
        · exact hlinv
        · exact (loc B e).zero_mem
      · simp [ite_mul, hl0]
    have := hH K' (DR ℂ K') (Algebra.lsmul ℂ ℂ (DR ℂ K')) κ (loc B e)
      (omB ℂ K' (loc B e) d) r (stab_lemma _ d) m c (kos_Z_mono_of_le _ (hle e) r m hc) 1 hIn
    simpa using this
  refine ⟨?_, ?_, ?_⟩
  · intro hyp m hm c hc
    apply hglob m c
    intro e
    by_cases h : ∀ l, Val B e (r l) 0
    · obtain ⟨e0, hOv, hIn⟩ := hyp e h
      have hlocEq : loc B e = loc (rB ℂ K' (xv x) {0}) e0.1 := hOv.2.1
      have hReg : Reg (Algebra.lsmul ℂ ℂ (DR ℂ K')) (omB ℂ K' (loc B e) d) (tt K' x) := by
        rw [hlocEq]
        exact hLR F K' d x hY.covY hY.red e0
      have hKE := hK1 K' (DR ℂ K') (Algebra.lsmul ℂ ℂ (DR ℂ K')) κ (loc B e)
        (omB ℂ K' (loc B e) d) r d (tt K' x) (stab_lemma _ d) (fun l => (hVB K' B e).1 (hr l))
        hReg (fun j => by rw [hlocEq]; exact hIn j)
      exact hKE m hm (kos_Z_mono_of_le _ (hle e) r m hc)
    · exact hbad m c hc e h
  · intro m c hc hyp
    apply hglob m c
    intro e
    by_cases h : ∀ l, Val B e (r l) 0
    · exact hyp e h
    · exact hbad m c hc e h
  · intro y hy hyp
    refine (hLG K' B (DR ℂ K') κ (fun _ => omB ℂ K' B d) r (fun _ => stab_lemma B d)).2 y
      (fun e => ?_)
    simp only [(hOm K' B e d).1]
    by_cases h : ∀ l, Val B e (r l) 0
    · exact hyp e h
    · obtain ⟨l, hl0, hlinv⟩ := hloc e h
      unfold sm
      refine Submodule.mem_iSup_of_mem (r l) (Submodule.mem_iSup_of_mem (Set.mem_range_self l) ?_)
      refine Submodule.mem_map.mpr ⟨_, stab_lemma (loc B e) d _ hlinv y (hle e hy), ?_⟩
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel₀ hl0, map_one, Module.End.one_apply]
