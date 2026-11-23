import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsUnitarisableTrivChar
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotientsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteAutomorphicRepGLLocalComponentIsUnitarisStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqOfNodupSumMultisetOfEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAlgebraicWeightOfAutomorphicDefiniteUnitarStatement
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DefiniteBC GlobalTheory.BcSpeh
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BcSpehProof

theorem hasInfCharGL_unique {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {N : ℕ}
    {V : Submodule ℂ (Sm E N)} (hV : V ≠ ⊥) {τ : E →+* ℂ} {m m' : Multiset ℂ} (h : HasInfCharGL V τ m)
    (h' : HasInfCharGL V τ m') : m = m' := by
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 hV
  have e : ((m.map Neg.neg).map fun z => Polynomial.X - Polynomial.C z).prod =
      ((m'.map Neg.neg).map fun z => Polynomial.X - Polynomial.C z).prod := by
    refine Polynomial.funext fun u => ?_
    have := smul_left_injective ℂ h0 ((h.2 u φ hφ).symm.trans (h'.2 u φ hφ))
    simpa [Polynomial.eval_multiset_prod, Multiset.map_map] using this
  have e2 := congrArg Polynomial.roots e
  rw [Polynomial.roots_multiset_prod_X_sub_C, Polynomial.roots_multiset_prod_X_sub_C] at e2
  exact Multiset.map_injective neg_injective e2

theorem spehInf_eq (d : ℕ) (m : Multiset ℂ) : GlobalTheory.SphGal.spehInf d m = GlobalTheory.DefiniteBC.spehInf d m := by
  unfold GlobalTheory.SphGal.spehInf GlobalTheory.DefiniteBC.spehInf
  rw [← List.sum_ofFn, List.ofFn_eq_map, ← List.map_coe_finRange_eq_range, List.map_map]
  rfl

end GlobalTheory.BcSpehProof

namespace GlobalTheory.BcSpehProof

theorem isUnitarisable_of_equiv' {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ G V} {σ : Representation ℂ G W}
    (φ : π.Equiv σ) (h : IsUnitarisable π) : IsUnitarisable σ := by
  obtain ⟨B, h1, h2, h3⟩ := h
  refine ⟨(B ∘ₗ φ.symm.toLinearEquiv.toLinearMap).compl₂ φ.symm.toLinearEquiv.toLinearMap, fun v w => h1 _ _,
    fun v hv => h2 _ (φ.symm.toLinearEquiv.map_ne_zero_iff.2 hv), fun g v w => ?_⟩
  have e : ∀ v, φ.symm.toLinearEquiv (σ g v) = π g (φ.symm.toLinearEquiv v) := fun v =>
    φ.symm.toIntertwiningMap.isIntertwining _ _ g v
  show B (φ.symm.toLinearEquiv (σ g v)) (φ.symm.toLinearEquiv (σ g w)) = _
  rw [e, e, h3]
  rfl

theorem isUnitarisable_of_isLocComp (H : GlobalTheory.Published.DiscreteSpectrumGL) {E : Type} [Field E] [NumberField E]
    [IsCMField E] {a : ℕ} (ha : 1 ≤ a) (P : CuspSub E a) (hP : GlobalTheory.DiscSpec.IsNormalised P)
    (w : HeightOneSpectrum (𝓞 E)) (ρ : LocIrr w a) (hρ : P.IsLocComp w ρ) : IsUnitarisable ρ.ρ := by
  obtain ⟨V, ⟨hV, hS⟩, -⟩ := (H E a ha).2.1 a 1 P (one_mul a) hP
  have hc := (H E a ha).2.2.2.2 V hV a 1 P hP hS
  obtain ⟨-, σ', -, hσ'⟩ := hc.exLoc w
  obtain ⟨hd, h1⟩ := hc.loc w ρ σ' hρ hσ'
  obtain ⟨hd', h2⟩ := GlobalTheory.LocGL.isSpeh_one (GlobalTheory.LocGL.IrrGL.of ρ.ρ ρ.smooth ρ.irred)
  obtain ⟨e⟩ := h1.unique h2
  have hu := GlobalTheory.T.discreteAutomorphicRepGL_localComponent_isUnitarisable E a V hV w σ' hσ'
  exact isUnitarisable_of_equiv' ((GlobalTheory.LocGL.IrrGL.equivOf ρ.ρ ρ.smooth ρ.irred).trans e).symm hu

theorem hasInfChar_eq_of_sigma {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a b : ℕ} {P : CuspSub E a}
    {Q : CuspSub E b} (h : (⟨a, CG.mk P⟩ : Σ c, CG E c) = ⟨b, CG.mk Q⟩) {τ : E →+* ℂ} {m m' : Multiset ℂ}
    (hm : P.HasInfChar τ m) (hm' : Q.HasInfChar τ m') : m = m' := by
  obtain ⟨rfl, h2⟩ := Sigma.mk.inj_iff.1 h
  exact (CuspSub.Iso.hasInfChar (Quotient.exact (eq_of_heq h2)) hm).unique hm'

end GlobalTheory.BcSpehProof

namespace GlobalTheory.BcSpehProof

theorem baseChange_speh_of_discreteSeries (H : GlobalTheory.Published.DiscreteSpectrumGL)
    (hW : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n →
      ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π → ∀ τ : E →+* ℂ, ∃ lam : Formalism.BasicNotions.DomWeight n, HasWeightAt π τ lam)
    {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (hn : 1 ≤ n)
    {π : Submodule ℂ (UA E n → ℂ)} (hπ : IsAutRepU π) {c : ℕ} {N : Fin c → ℕ} {h : ∑ i, N i = n}
    {V : ∀ i, Submodule ℂ (Sm E (N i))} {σ : ∀ i (w : HeightOneSpectrum (𝓞 E)), SmIrr (GL (Fin (N i)) (w.adicCompletion E))}
    {m : Fin c → (E →+* ℂ) → Multiset ℂ} (bc : IsBaseChange π h V σ m) (a d : Fin c → ℕ) (P : ∀ i, CuspSub E (a i))
    (hPn : ∀ i, GlobalTheory.DiscSpec.IsNormalised (P i)) (hPs : ∀ i, GlobalTheory.DiscSpec.IsSpehOf (V i) (P i) (d i))
    (hNad : ∀ i, N i = d i * a i) :
    ∃ (c : ℕ) (a d : Fin c → ℕ) (h : ∑ i, d i * a i = n) (P : ∀ i, CuspSub E (a i)) (ρ : ∀ i (w : HeightOneSpectrum (𝓞 E)), LocIrr w (a i))
        (m : Fin c → (E →+* ℂ) → Multiset ℂ) (σ : ∀ i (w : HeightOneSpectrum (𝓞 E)), LocIrr w (d i * a i)), Parts π a d h P ρ m ∧
        (∀ i w, IsUnitarisable (ρ i w).ρ ∧ IsUnitarisable (σ i w).ρ ∧ GlobalTheory.LocGL.IsSpeh (GlobalTheory.LocGL.IrrGL.of (ρ i w).ρ (ρ i w).smooth (ρ i w).irred) (d i) (σ i w).ρ) ∧
        ∀ w, IsSplitAt w → IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) (locProd h w (σ · w)) := by
  have hN : ∀ i, 1 ≤ N i := bc.pos
  have hc : ∀ i, GlobalTheory.DiscSpec.HasSpehComp (V i) (P i) (d i) := fun i =>
    (H E (N i) (hN i)).2.2.2.2 (V i) (bc.discrete i) (a i) (d i) (P i) (hPn i) (hPs i)
  choose ρ σ' hρ hσ' using fun i w => (hc i).exLoc w
  choose m' hm1 hm2 using fun i τ => (hc i).inf τ
  have hmm : ∀ i τ, m i τ = GlobalTheory.DefiniteBC.spehInf (d i) (m' i τ) := fun i τ =>
    (hasInfCharGL_unique (bc.discrete i).ne_bot (bc.inf i τ) (hm2 i τ)).trans (spehInf_eq _ _)
  have hpos : ∀ i, 1 ≤ a i ∧ 1 ≤ d i := fun i => by
    have := hN i
    rw [hNad i] at this
    exact ⟨Nat.one_le_iff_ne_zero.2 fun e => by simp [e] at this, Nat.one_le_iff_ne_zero.2 fun e => by simp [e] at this⟩
  have hcsd : ∀ i, (P i).IsCsd := fun i =>
    GlobalTheory.DiscSpec.isCsd_of_isSpehOf H (hN i) (bc.discrete i) (bc.csd i) (hPn i) (hPs i)
  have hsp : ∀ i w, GlobalTheory.LocGL.IsSpeh (GlobalTheory.LocGL.IrrGL.of (ρ i w).ρ (ρ i w).smooth (ρ i w).irred) (d i) (σ i w).ρ :=
    fun i w => (hc i).loc w (ρ i w) (σ i w) (hρ i w) (bc.loc i w)
  have hun : ∀ i w, IsUnitarisable (ρ i w).ρ ∧ IsUnitarisable (σ i w).ρ := fun i w =>
    ⟨isUnitarisable_of_isLocComp H (hpos i).1 (P i) (hPn i) w (ρ i w) (hρ i w),
      GlobalTheory.T.discreteAutomorphicRepGL_localComponent_isUnitarisable E (N i) (V i) (bc.discrete i) w (σ i w) (bc.loc i w)⟩
  have hm0 : ∀ i τ, m i τ ≠ 0 := fun i τ h0 => by
    have h1 := (bc.inf i τ).1
    rw [h0, Multiset.card_zero] at h1
    have := hN i
    omega
  obtain rfl : N = fun i => d i * a i := funext hNad
  refine ⟨c, a, d, h, P, ρ, m', σ, ⟨hpos, hcsd, hρ, hm1, fun τ lam hl => ?_, fun i j hd hs => ?_, ?_⟩,
    fun i w => ⟨(hun i w).1, (hun i w).2, hsp i w⟩, bc.split⟩
  · rw [← bc.weight τ lam hl]
    exact Finset.sum_congr rfl fun i _ => (hmm i τ).symm
  · obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    obtain ⟨lam, hl⟩ := hW E n hn π hπ τ
    refine GlobalTheory.eq_of_nodup_sum_multiset_of_eq (Fin c) (m · τ) (bc.weight τ lam hl ▸ nodup_infOfWeight lam) i j
      (hm0 i τ) ?_
    rw [hmm i τ, hmm j τ, hd, hasInfChar_eq_of_sigma hs (hm1 i τ) (hm1 j τ)]
  · intro w s ϖ q hs hU α hα
    exact GlobalTheory.T.satakeParameter_spherical_product_spehQuotients E w c n a d h (ρ · w) (σ · w) (fun i => (hpos i).2) (fun i => hsp i w) _
      (bc.inert w s ϖ q hs hU α hα)

end GlobalTheory.BcSpehProof

theorem GlobalTheory.BcSpeh.bcSpeh_of_baseChange : GlobalTheory.Published.BaseChangeDefiniteUnitary → GlobalTheory.Published.DiscreteSpectrumGL → BcSpeh := by
  intro H1 H2 E _ _ _ hE n hn π hπ
  obtain ⟨c, N, h, V, σ, m, bc⟩ := H1 E hE n hn π hπ
  choose a d P _ hPn hPs using fun i => (H2 E (N i) (bc.pos i)).1 (V i) (bc.discrete i)
  exact GlobalTheory.BcSpehProof.baseChange_speh_of_discreteSeries H2 GlobalTheory.T.exists_algebraicWeight_of_automorphic_definiteUnitary hn hπ bc a d P hPn hPs fun i => (hPs i).mul_eq.symm
