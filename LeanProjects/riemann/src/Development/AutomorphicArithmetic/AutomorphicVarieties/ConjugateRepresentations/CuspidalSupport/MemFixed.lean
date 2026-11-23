import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.HeckeLocalBlock

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

private theorem mem_fixed' {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
    {H : Subgroup G} {v : V} : v ∈ fixed ρ H ↔ ∀ k ∈ H, ρ k v = v := by
  change (∀ h : H, ρ (h : G) v = (((1 : H →* ℂˣ) h : ℂˣ) : ℂ) • v) ↔ _
  simp

private theorem blk_mul {r s : ℕ} {R : Type} [CommRing R] (a a' : GL (Fin r) R) (b b' : GL (Fin s) R) :
    blk (a * a') (b * b') = blk a b * blk a' b' := by
  simp only [blk, map_mul, mul_assoc]
  rw [← mul_assoc (emb (e2 r s) b), ← UpperTheory.V.Af.Fin.emb_comm, mul_assoc]

private theorem fL_apply {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {n : ℕ} (w : Pl E)
    (b : GL (Fin n) (w.adicCompletion E)) (φ : Sm E n) (x : GA E n) :
    (fL n w b φ).1 x = φ.1 (x * finGL E n (locGL E n w b)) := rfl

private theorem tOp_apply (hS : HkSum) {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {n : ℕ} (w : Pl E)
    {ϖ : w.adicCompletion E} (hϖ : ϖ ∈ Ov E w) (hu : IsUnifV E w ϖ) [Fintype (satakeRes (Ov E w) ⟨ϖ, hϖ⟩)] (j : ℕ)
    (hj : j ≤ n) (φ : Sm E n) (hφ : φ ∈ fixed (fL n w) (KGL w n)) (x : GA E n) :
    (tOp n w hu j φ).1 x =
      ∑ i : SatakeIdx w hϖ (n := n) j, φ.1 (x * finGL E n (locGL E n w (satakeB w hϖ hu i))) := by
  have h := hS E w n (Sm E n) (fL n w) ϖ hϖ hu j hj φ hφ
  have h' : tOp n w hu j φ = ∑ i : SatakeIdx w hϖ (n := n) j, fL n w (satakeB w hϖ hu i) φ := h
  rw [h', Submodule.coe_sum, Finset.sum_apply]
  rfl

theorem UpperTheory.V.Cj.S.hkRel :
    UpperTheory.V.Cj.S.Slice → UpperTheory.V.Cj.S.HkSum → UpperTheory.V.Cj.S.HkLocal → UpperTheory.V.Cj.S.HeckeLocalBlock → UpperTheory.V.Cj.S.HkRel := by
  intro hSl hS hL hB E _ _ _ r s ψ hN w hψ ϖ hu j hj
  have hϖ : ϖ ∈ Ov E w := mem_Ov_of_isUnifV hu
  have := satake_res_finite w hϖ hu
  letI : Fintype (satakeRes (Ov E w) ⟨ϖ, hϖ⟩) := Fintype.ofFinite _
  obtain ⟨b1, b2, b3, b4⟩ := hB E w r s
  have hfix : ∀ k ∈ KGL w (r + s), ∀ g, ψ.1 (g * finGL E _ (locGL E _ w k)) = ψ.1 g := fun k hk g =>
    congrFun (congrArg Subtype.val (mem_fixed'.1 hψ k hk)) g
  have hs1 : ∀ y : GA E s, ∃ f : Sm E r, (∀ x, f.1 x = ψ.1 (blk x y)) ∧ f ∈ fixed (fL r w) (KGL w r) := fun y => by
    obtain ⟨f, hf, -⟩ := hSl E r (r + s) (e1 r s) (emb (e2 r s) y)
    have hf' : ∀ x, (f ψ).1 x = ψ.1 (blk x y) := fun x => by rw [hf, blk, UpperTheory.V.Af.Fin.emb_comm]
    refine ⟨f ψ, hf', mem_fixed'.2 fun k hk => Subtype.ext (funext fun x => ?_)⟩
    rw [fL_apply, hf', hf', ← hfix _ (b4 k hk 1 (one_mem _)) (blk x y), b1, ← blk_mul, map_one, map_one, mul_one]
  have hs2 : ∀ x : GA E r, ∃ f : Sm E s, (∀ y, f.1 y = ψ.1 (blk x y)) ∧ f ∈ fixed (fL s w) (KGL w s) := fun x => by
    obtain ⟨f, hf, -⟩ := hSl E s (r + s) (e2 r s) (emb (e1 r s) x)
    have hf' : ∀ y, (f ψ).1 y = ψ.1 (blk x y) := fun y => by rw [hf, blk]
    refine ⟨f ψ, hf', mem_fixed'.2 fun k hk => Subtype.ext (funext fun y => ?_)⟩
    rw [fL_apply, hf', hf', ← hfix _ (b4 1 (one_mem _) k hk) (blk x y), b1, ← blk_mul, map_one, map_one, mul_one]
  choose f2 hf2 hf2' using hs2
  refine ⟨fun p x y => ∑ i₁ : SatakeIdx w hϖ (n := r) p.1, ∑ i₂ : SatakeIdx w hϖ (n := s) p.2,
    ψ.1 (blk (x * finGL E r (locGL E r w (satakeB w hϖ hu i₁))) (y * finGL E s (locGL E s w (satakeB w hϖ hu i₂)))),
    fun p => ⟨fun x y => ∑ i₁ : SatakeIdx w hϖ (n := r) p.1,
      ψ.1 (blk (x * finGL E r (locGL E r w (satakeB w hϖ hu i₁))) y), fun y => ?_, fun x => ?_⟩, fun x y => ?_⟩
  · obtain ⟨f, hf, hf'⟩ := hs1 y
    refine ⟨f, funext hf, funext fun x => ?_⟩
    rw [tOp_apply hS w hϖ hu _ (Nat.lt_succ_iff.mp p.1.2) f hf']
    simp only [hf]
  · have hv : ∀ y, (∑ i₁ : SatakeIdx w hϖ (n := r) p.1,
        f2 (x * finGL E r (locGL E r w (satakeB w hϖ hu i₁)))).1 y = ∑ i₁ : SatakeIdx w hϖ (n := r) p.1,
        ψ.1 (blk (x * finGL E r (locGL E r w (satakeB w hϖ hu i₁))) y) := fun y => by
      rw [Submodule.coe_sum, Finset.sum_apply]
      simp only [hf2]
    refine ⟨_, funext hv, funext fun y => ?_⟩
    rw [tOp_apply hS w hϖ hu _ (Nat.lt_succ_iff.mp p.2.2) _ (Submodule.sum_mem _ fun i _ => hf2' _)]
    simp only [hv]
    exact Finset.sum_comm
  · rw [res, tOp_apply hS w hϖ hu j hj ψ hψ,
      hL E w r s ϖ hϖ hu j (fun g => ψ.1 (blk x y * finGL E _ (locGL E _ w g))) (fun X g => by
        obtain ⟨Y, hY⟩ := b2 X
        obtain ⟨Y', hY'⟩ := b3 x y Y
        simp only [map_mul]
        rw [hY, ← mul_assoc, hY', mul_assoc, hN])]
    simp only [b1, blk_mul]
