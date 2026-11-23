import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.HeckeLocalBlock

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

private theorem UpperTheory.V.Cj.S.eig_of_joint (hS : SatOfEig) (hC : CapOfEig)
    {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} {T : Set (Pl E)} (hT : T.Finite)
    (φ : Sm E a) (h0 : φ ≠ 0) (haut : IsAutForm φ) (hfix : ∀ w ∉ T, φ ∈ fixed (fL a w) (KGL w a))
    (l : Ix a T → ℂ) (hl : ∀ i, opIx i φ = l i • φ) :
    ∃ (m : (E →+* ℂ) → Multiset ℂ) (B : Pl E → Multiset ℂˣ), Eig φ m B ∧
      (∀ t u, l (.inl (t, u)) = ((m t).map (u + ·)).prod) ∧
      ∀ (w : Pl E) (hw : w ∉ T) (ϖ : HeightOneSpectrum.adicCompletion E w) (hu : IsUnifV E w ϖ), ∀ j ≤ a,
        l (.inr ⟨⟨w, hw⟩, ⟨_, Tj_mem_hecke hu j⟩⟩) = satEig (qV E w) a (B w) j := by
  classical
  obtain ⟨m, hm⟩ := hC E a φ h0 fun t u => ⟨_, hl (.inl (t, u))⟩
  have hB : ∀ w : Pl E, ∃ B : Multiset ℂˣ, w ∉ T → IsSatVecGL w (fL a w) φ B := by
    intro w
    by_cases hw : w ∈ T
    · exact ⟨0, fun h => (h hw).elim⟩
    · obtain ⟨B, hB⟩ := hS E w a _ (fL a w) φ h0 (hfix w hw) fun h hh => ⟨_, hl (.inr ⟨⟨w, hw⟩, ⟨h, hh⟩⟩)⟩
      exact ⟨B, fun _ => hB⟩
  choose B hB using hB
  refine ⟨m, B, ⟨h0, haut, hm, ?_⟩, fun t u => ?_, fun w hw ϖ hu j hj => ?_⟩
  · exact hT.eventually_cofinite_notMem.mono hB
  · exact smul_left_injective ℂ h0 ((hl (.inl (t, u))).symm.trans ((hm t).2 u))
  · exact smul_left_injective ℂ h0
      ((hl (.inr ⟨⟨w, hw⟩, ⟨_, Tj_mem_hecke hu j⟩⟩)).symm.trans ((hB w hw).2.2.2 ϖ hu j hj))

theorem UpperTheory.V.Cj.S.pairEig :
    UpperTheory.V.Cj.S.TwoVar → UpperTheory.V.Cj.S.StabSp → UpperTheory.V.Cj.S.OpComm → UpperTheory.V.Cj.S.SatOfEig → UpperTheory.V.Cj.S.CapOfEig → UpperTheory.V.Cj.S.PairEig := by
  intro hTV hSt hOp hS hC E _ _ _ r s F S₁ S₂ b₁ b₂ hF h₁ h₂
  obtain ⟨T₁, hT₁, V₁, hS₁, fd₁, aut₁, fix₁, st₁⟩ := hSt E r S₁ b₁
  obtain ⟨T₂, hT₂, V₂, hS₂, fd₂, aut₂, fix₂, st₂⟩ := hSt E s S₂ b₂
  obtain ⟨φ₁, hφ₁, φ₂, hφ₂, l₁, l₂, n₁, n₂, e₁, e₂, H⟩ :=
    hTV _ _ (Sm E r) (Sm E s) V₁ V₂ fd₁ fd₂ (Ix r T₁) (Ix s T₂) opIx opIx st₁ st₂
      (fun i i' v hv => hOp E r T₁ i i' v fun w hw => fix₁ w hw hv)
      (fun i i' v hv => hOp E s T₂ i i' v fun w hw => fix₂ w hw hv) F hF
      (fun y => (h₁ y).imp fun f hf => ⟨hS₁ hf.1, hf.2⟩) (fun x => (h₂ x).imp fun f hf => ⟨hS₂ hf.1, hf.2⟩)
  obtain ⟨m₁, B₁, E₁, c₁, s₁⟩ := eig_of_joint hS hC hT₁ φ₁ n₁ (aut₁ _ hφ₁) (fun w hw => fix₁ w hw hφ₁) l₁ e₁
  obtain ⟨m₂, B₂, E₂, c₂, s₂⟩ := eig_of_joint hS hC hT₂ φ₂ n₂ (aut₂ _ hφ₂) (fun w hw => fix₂ w hw hφ₂) l₂ e₂
  refine ⟨φ₁, φ₂, m₁, m₂, B₁, B₂, E₁, E₂, fun t u v G e hG he => ?_, ?_⟩
  · have := H Unit (fun _ => 1) (fun _ => .inl (t, u)) (fun _ => .inl (t, v)) (fun _ => G) e (fun _ => hG)
      (fun x y => by simpa using he x y)
    rw [← c₁, ← c₂]
    simpa using this
  · filter_upwards [hT₁.eventually_cofinite_notMem, hT₂.eventually_cofinite_notMem] with w hw₁ hw₂ ϖ hu c G e hG he
    have := H (Fin (r + 1) × Fin (s + 1)) c (fun p => .inr ⟨⟨w, hw₁⟩, ⟨_, Tj_mem_hecke hu p.1⟩⟩)
      (fun p => .inr ⟨⟨w, hw₂⟩, ⟨_, Tj_mem_hecke hu p.2⟩⟩) G e hG he
    rw [← this]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [s₁ w hw₁ ϖ hu p.1 (Nat.lt_succ_iff.1 p.1.2), s₂ w hw₂ ϖ hu p.2 (Nat.lt_succ_iff.1 p.2.2)]
