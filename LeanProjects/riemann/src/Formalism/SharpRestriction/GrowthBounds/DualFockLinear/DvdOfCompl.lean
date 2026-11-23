import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.IsMultiHom

noncomputable section

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 MvPolynomial
open Formalism.L2.G.Model (Nv)

def TransStep : Prop :=
  ∀ (p n' : ℕ) [Fact p.Prime] (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (w : O) (hS : HidaSetting p n' W Qq O Kf ι σ j w)
    (φ : WF p n' ≃+* W), IsWittIdent σ φ → ∀ (m r : ℕ), 2 ≤ m → 1 ≤ r → r < m + 1 →
  ∀ (d : Fin n' → ℕ) (rest lam0 : Fin n' → Fin (m + 1) → ℤ), lam0 = flW d + rest → IsDominant rest →
  ∀ (e : Edge W Qq (m + 1)), IsEdge p n' r e →
  ∀ (hm : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) (g : Matrix (Fin (m + 1)) (Fin (m + 1)) (WF p n')),
    IsUnit hm.det → IsGLW g → IsEdgeBasis p r e (hm * ((matQ φ g)⁻¹).transpose) →
  letI : Algebra (WF p n') O := algOfIdent j φ
  ∀ Θ : ↥((Pol (KK O) (ι := Fin n') (m + 1) d).restrictScalars O) ≃ₗ[O] ↥(Vsp Kf (flW (m := m) d)),
    IsTrueTheta hS d (flW d) (vecE n') hm Θ →
  ∀ (I : Type) [Fintype I] (sO : I → MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) O),
    (∀ i, sO i ∈ tensorLat O O (fun s => dualWeyl O (m + 1) (m + 1) (nuOf (lamAt rest s)))) →
    ∃ sh : I → Vsp Kf rest, (∀ i, sh i ∈ Re p ι σ w r rest e) ∧
      ∀ (P : I → ↥((Pol (KK O) (ι := Fin n') (m + 1) d).restrictScalars O))
        (Q : I → MvPolynomial (Fin n' × Fin (m + 1)) O),
        (∀ i, subst p n' O w n' r g (P i : MvPolynomial (TV n' (m + 1)) (KK O)) = map (algebraMap O (KK O)) (Q i)) →
        ∀ v : Vsp Kf lam0,
          ((v : Vsp Kf lam0) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) =
            ∑ i, ((Θ (P i) : Vsp Kf (flW (m := m) d)) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) *
              ((sh i : Vsp Kf rest) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) →
          v ∈ scale (algebraMap O Kf w ^ (1 : ℤ)) (Re p ι σ w r lam0 e) →
          ∃ R : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) O,
            ∑ i, thAll O n' m (vecE n') (Q i) * sO i = C w * R

def SPStep (C : ℝ) : Prop :=
  ∀ (p : ℕ) (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (w : O)
    (n' m r : ℕ) [Fact p.Prime] [NeZero n'] (TT : Finset (Fin n')) (L₁ L₂ : ℕ) (de h x : ℝ)
    (lam0 : Fin n' → Fin (m + 1) → ℤ) (aT bT : Fin n' → ℤ) (a Y : ℝ) (cpp c0 Dp cStar : ℕ),
    UnramifiedQuadraticSetting p n' W Qq O Kf ι σ j w →
    Hyps C p n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar →
    ∀ φ : WF p n' ≃+* W, IsWittIdent σ φ →
    ∀ (hrk : r ≤ m + 1),
    ∀ F : Frames n' r, FramesOK TT L₁ L₂ (orbitWindowCount r de h x) (goodG' r de h x) F →
    ∀ (g : Matrix (Fin (m + 1)) (Fin (m + 1)) (WF p n')), IsGLW g →
    letI : Algebra (WF p n') O := algOfIdent j φ
    ∀ c' Q : ℕ, ∃ SPO : MvPolynomial (TV n' (m + 1)) O,
      subst p n' O w n' r g (SPtrue p n' O F hrk g c' Q) = map (algebraMap O (KK O)) SPO ∧
        map (IsLocalRing.residue O) SPO ≠ 0

def SubstPol : Prop :=
  ∀ (p n' : ℕ) [Fact p.Prime] (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (w : O), HidaSetting p n' W Qq O Kf ι σ j w →
    ∀ (φ : WF p n' ≃+* W), IsWittIdent σ φ → ∀ (k r : ℕ) (d : Fin n' → ℕ) (g : Matrix (Fin k) (Fin k) (WF p n')), IsGLW g →
    letI : Algebra (WF p n') O := algOfIdent j φ
    ∀ F ∈ Pol (KK O) (ι := Fin n') k d, subst p n' O w n' r g F ∈ Pol (KK O) (ι := Fin n') k d

theorem deg_map {τ : Type} (mo : MonomialOrder τ) {R S : Type} [CommRing R] [CommRing S] [Nontrivial S] (f : R →+* S)
    (P : MvPolynomial τ R) (h : mo.leadingCoeff P = 1) :
    mo.degree (map f P) = mo.degree P ∧ mo.leadingCoeff (map f P) = 1 := by
  have hP : MvPolynomial.coeff (mo.degree P) P = 1 := h
  have h1 : MvPolynomial.coeff (mo.degree P) (map f P) = 1 := by
    rw [MvPolynomial.coeff_map, hP, map_one]
  have hd : mo.degree (map f P) = mo.degree P := by
    apply mo.toSyn.injective
    apply le_antisymm
    · rw [MonomialOrder.degree_le_iff]
      intro c hc
      apply MonomialOrder.le_degree
      rw [MvPolynomial.mem_support_iff] at hc ⊢
      rw [MvPolynomial.coeff_map] at hc
      intro h0
      apply hc
      rw [h0, map_zero]
    · apply MonomialOrder.le_degree
      rw [MvPolynomial.mem_support_iff, h1]
      exact one_ne_zero
  refine ⟨hd, ?_⟩
  unfold MonomialOrder.leadingCoeff
  rw [hd, h1]

theorem dvd_of_compl {O M : Type} [CommRing O] [IsDomain O] [AddCommGroup M] [Module O M] {nb : ℕ} (B : Fin nb → M)
    (hli : LinearIndependent O B) (T : Submodule O M) (hc : IsCompl (Submodule.span O (Set.range B)) T)
    (ϖ : O) (c : Fin nb → O) (y : M) (h : ∑ b, c b • B b = ϖ • y) : ∀ b, ϖ ∣ c b := by
  have hy : y ∈ Submodule.span O (Set.range B) ⊔ T := by rw [hc.sup_eq_top]; trivial
  obtain ⟨y₁, hy₁, y₂, hy₂, hy12⟩ := Submodule.mem_sup.1 hy
  obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun O).1 hy₁
  have e : ∑ b, c b • B b - ϖ • y₁ = ϖ • y₂ := by
    rw [h, ← hy12, smul_add]
    abel
  have hmem1 : ∑ b, c b • B b - ϖ • y₁ ∈ Submodule.span O (Set.range B) := by
    refine Submodule.sub_mem _ (Submodule.sum_mem _ fun b _ => ?_) (Submodule.smul_mem _ _ hy₁)
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)
  have hmem2 : ∑ b, c b • B b - ϖ • y₁ ∈ T := by
    rw [e]
    exact Submodule.smul_mem _ _ hy₂
  have hzero := (Submodule.disjoint_def.1 hc.disjoint) _ hmem1 hmem2
  have hsum : ∑ b, (c b - ϖ * d b) • B b = 0 := by
    rw [← hd, Finset.smul_sum] at hzero
    simp only [sub_smul, Finset.sum_sub_distrib, mul_smul]
    exact hzero
  intro b
  have := Fintype.linearIndependent_iff.1 hli _ hsum b
  exact ⟨d b, by linear_combination this⟩

end Formalism.MainNotions.TestSideCounting
