import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.SatPowNonvan
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.JointGeneralisedEigenvectors.CasselmanStrictlyDominantExample
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetLemmaHoldsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwahoriUnipotentDatumStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DominantUnipotentContraction
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsStrictDom

open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct

namespace GlobalTheory.CompanionTheory.EqForm

section LinAlg

theorem exists_form_of_faithful {k Q : Type} [Field k] [AddCommGroup Q] [Module k Q] [FiniteDimensional k Q]
    (R : Type) [CommRing R] [Algebra k R] [Module R Q] [IsScalarTower k R Q]
    (hf : ∀ r : R, (∀ x : Q, r • x = 0) → r = 0) (q₀ : Q) (h0 : q₀ ≠ 0) :
    ∃ μ : Module.Dual k Q, μ ≠ 0 ∧ ∀ (r : R) (c : k), r • q₀ = c • q₀ → ∀ x, μ (r • x) = c * μ x := by
  let I : Ideal R := LinearMap.ker (LinearMap.toSpanSingleton R Q q₀)
  have hI : ∀ r : R, r ∈ I ↔ r • q₀ = 0 := fun r => by simp [I, LinearMap.mem_ker]
  haveI : Module.Finite R Q := Module.Finite.of_restrictScalars_finite k R Q
  have hne : I • (⊤ : Submodule R Q) ≠ ⊤ := by
    intro htop
    obtain ⟨r, hr1, hr2⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul I (⊤ : Submodule R Q)
      Module.Finite.fg_top (by rw [htop])
    have hr0 : r = 0 := hf r fun x => hr2 x trivial
    rw [hr0, zero_sub, hI] at hr1
    apply h0
    simpa using hr1
  let M : Submodule k Q := (I • (⊤ : Submodule R Q)).restrictScalars k
  have hM : M < ⊤ := by
    refine lt_top_iff_ne_top.2 fun h => hne ?_
    apply Submodule.restrictScalars_injective k
    simpa [M] using h
  obtain ⟨μ, hμ0, hμ⟩ := Submodule.exists_le_ker_of_lt_top M hM
  refine ⟨μ, hμ0, fun r c hr x => ?_⟩
  have hmem : r - algebraMap k R c ∈ I := by
    rw [hI, sub_smul, hr, algebraMap_smul, sub_self]
  have hx : (r - algebraMap k R c) • x ∈ M := by
    have h2 : (r - algebraMap k R c) • x ∈ I • (⊤ : Submodule R Q) :=
      Submodule.smul_mem_smul hmem (Submodule.mem_top)
    exact (Submodule.restrictScalars_mem k _ _).2 h2
  have h1 : μ ((r - algebraMap k R c) • x) = 0 := hμ hx
  rw [sub_smul, algebraMap_smul, map_sub, μ.map_smul c x, smul_eq_mul, sub_eq_zero] at h1
  exact h1

theorem exists_eigenform_of_commute {Q : Type} [AddCommGroup Q] [Module ℂ Q] [FiniteDimensional ℂ Q] {ι : Type}
    (A : ι → Module.End ℂ Q) (hc : ∀ i j, Commute (A i) (A j))
    (ξ : ι → ℂ) (q₀ : Q) (h0 : q₀ ≠ 0) (hq : ∀ i, A i q₀ = ξ i • q₀) :
    ∃ μ : Module.Dual ℂ Q, μ ≠ 0 ∧ ∀ i x, μ (A i x) = ξ i * μ x := by
  have hcomm : ∀ a ∈ Set.range A, ∀ b ∈ Set.range A, a * b = b * a := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact hc i j
  letI : CommRing (Algebra.adjoin ℂ (Set.range A)) := Algebra.adjoinCommRingOfComm ℂ hcomm
  obtain ⟨μ, hμ0, hμ⟩ := exists_form_of_faithful (k := ℂ) (Q := Q) (Algebra.adjoin ℂ (Set.range A))
    (fun r hr => Subtype.ext (LinearMap.ext hr)) q₀ h0
  refine ⟨μ, hμ0, fun i x => ?_⟩
  exact hμ ⟨A i, Algebra.subset_adjoin ⟨i, rfl⟩⟩ (ξ i) (hq i) x

end LinAlg

section Smooth

variable {Γ W : Type} [Group Γ] [TopologicalSpace Γ] [AddCommGroup W] [Module ℂ W]

theorem mem_fixed_iff (ρ : Representation ℂ Γ W) (K : Subgroup Γ) (v : W) :
    v ∈ fixed ρ K ↔ ∀ k ∈ K, ρ k v = v := by
  constructor
  · intro h k hk
    have h1 := h ⟨k, hk⟩
    simpa using h1
  · intro h k
    have h1 := h k k.2
    simpa using h1

theorem exists_eigenform_of_smooth [IsTopologicalGroup Γ] (ρ : Representation ℂ Γ W) (hρ : IsSmooth ρ)
    (K : Subgroup Γ) (hK : IsCompact (K : Set Γ)) (hcomm : ∀ a b : Γ, a * b = b * a)
    (hfin : FiniteDimensional ℂ (fixed ρ K)) (ξ : Γ → ℂ) (w₀ : W) (h0 : w₀ ≠ 0)
    (hw : ∀ t, ρ t w₀ = ξ t • w₀) (hξ : ∀ k ∈ K, ξ k = 1) :
    ∃ lam : Module.Dual ℂ W, lam ≠ 0 ∧ ∀ t w, lam (ρ t w) = ξ t * lam w := by
  have hst : ∀ t, ∀ v ∈ fixed ρ K, ρ t v ∈ fixed ρ K := by
    intro t v hv
    refine (mem_fixed_iff ρ K _).2 fun k hk => ?_
    rw [← Module.End.mul_apply, ← map_mul, hcomm, map_mul, Module.End.mul_apply,
      (mem_fixed_iff ρ K v).1 hv k hk]
  let A : Γ → Module.End ℂ (fixed ρ K) := fun t => (ρ t).restrict (hst t)
  have hA : ∀ t (s : fixed ρ K), ((A t s : fixed ρ K) : W) = ρ t s := fun t s => rfl
  have hAc : ∀ a b, Commute (A a) (A b) := by
    intro a b
    refine LinearMap.ext fun s => Subtype.ext ?_
    show ρ a (ρ b s) = ρ b (ρ a s)
    rw [← Module.End.mul_apply, ← map_mul, hcomm, map_mul, Module.End.mul_apply]
  have hw₀ : w₀ ∈ fixed ρ K := (mem_fixed_iff ρ K _).2 fun k hk => by rw [hw, hξ k hk, one_smul]
  obtain ⟨μ, hμ0, hμ⟩ := exists_eigenform_of_commute A hAc ξ ⟨w₀, hw₀⟩
    (fun h => h0 (congrArg Subtype.val h)) (fun t => Subtype.ext (hw t))
  have hnorm : ∀ t : Γ, t ∈ Subgroup.normalizer (K : Set Γ) := by
    intro t
    refine Subgroup.mem_normalizer_iff.2 fun h => ?_
    have e : t * h * t⁻¹ = h := by rw [hcomm t h, mul_inv_cancel_right]
    rw [e]
  have hE : ∀ t w, GlobalTheory.LocGL.idem hρ hK (ρ t w) = ρ t (GlobalTheory.LocGL.idem hρ hK w) := by
    intro t w
    have h1 : w - GlobalTheory.LocGL.idem hρ hK w ∈ twKer ρ K 1 := by
      rw [← GlobalTheory.LocGL.idem_eq_zero_iff hρ hK, map_sub,
        GlobalTheory.LocGL.idem_of_mem hρ hK (GlobalTheory.LocGL.idem_mem hρ hK w), sub_self]
    have h2 := twKer_le_comap ρ K t (hnorm t) h1
    rw [Submodule.mem_comap, ← GlobalTheory.LocGL.idem_eq_zero_iff hρ hK, map_sub, map_sub,
      GlobalTheory.LocGL.idem_of_mem hρ hK (hst t _ (GlobalTheory.LocGL.idem_mem hρ hK w)), sub_eq_zero] at h2
    exact h2
  let e : W →ₗ[ℂ] fixed ρ K := (GlobalTheory.LocGL.idem hρ hK).codRestrict _ (GlobalTheory.LocGL.idem_mem hρ hK)
  refine ⟨μ ∘ₗ e, ?_, ?_⟩
  · intro h
    apply hμ0
    refine LinearMap.ext fun s => ?_
    have h1 : e (s : W) = s := Subtype.ext (GlobalTheory.LocGL.idem_of_mem hρ hK s.2)
    have h2 := LinearMap.congr_fun h (s : W)
    simpa [h1] using h2
  · intro t w
    have h1 : e (ρ t w) = A t (e w) := Subtype.ext (hE t w)
    simp only [LinearMap.comp_apply]
    rw [h1, hμ]

end Smooth

section Diag

variable {L : Type} [Field L]

theorem isDiagM_commute {n : ℕ} {g h : GL (Fin n) L} (hg : IsDiagM g) (hh : IsDiagM h) : g * h = h * g := by
  have key : ∀ a : GL (Fin n) L, IsDiagM a →
      (a : Matrix (Fin n) (Fin n) L) = Matrix.diagonal fun i => (a : Matrix (Fin n) (Fin n) L) i i := by
    intro a ha
    ext i j
    by_cases hij : i = j
    · subst hij; simp
    · rw [ha i j hij, Matrix.diagonal_apply_ne _ hij]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, key g hg, key h hh, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  rw [mul_comm]

end Diag

theorem eqFormU_of (hA4 : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G], A4 G)
    (hIw : IwahoriU) (hDom : DomU) (hKU : KUFacts) : EqFormU := by
  intro L _ _ _ ϖ σ q n V _ _ ρ hu hadm ξ y hy hyt hyk
  obtain ⟨D, hJ, hN, hNm, hT⟩ := hIw L ϖ σ q hu n
  obtain ⟨-, -, hIK, t, htD, htS⟩ := hKU L ϖ σ q n hu
  have hdom : D.IsStrDom ⟨t, (hT t).2 htD⟩ := (hDom L ϖ σ q hu n D hJ hN hNm hT ⟨t, (hT t).2 htD⟩).2 htS
  have a4 := (hA4 (GU σ n) D V ρ hadm ⟨_, hdom⟩).2
  have hker : twKer ρ D.N 1 = jacU ρ := twKer_eq_jacSub D _ hN ρ
  haveI hfJ : FiniteDimensional ℂ (fixed ρ D.J) := hadm.2 D.J D.isOpen_J D.isCompact_J
  have hfin : FiniteDimensional ℂ (fixed (D.piN ρ) D.JT) := by
    let f : fixed ρ D.J →ₗ[ℂ] Jacquet ρ D.N := (twKer ρ D.N 1).mkQ ∘ₗ (fixed ρ D.J).subtype
    have hle : fixed (D.piN ρ) D.JT ≤ LinearMap.range f := by
      intro w hw
      obtain ⟨v, hv⟩ := a4 w hw
      exact ⟨v, hv⟩
    exact Submodule.finiteDimensional_of_le hle
  have hsm : IsSmooth (D.piN ρ) := by
    intro w
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    let Sg : Subgroup D.T :=
      { carrier := {g | D.piN ρ g (Submodule.Quotient.mk v) = Submodule.Quotient.mk v}
        mul_mem' := by
          intro a b ha hb
          simp only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at *
          rw [hb, ha]
        one_mem' := by simp
        inv_mem' := by
          intro a ha
          simp only [Set.mem_setOf_eq] at *
          conv_lhs => rw [← ha]
          rw [← Module.End.mul_apply, ← map_mul]
          simp }
    have hop : IsOpen {g : D.T | ρ (g : GU σ n) v = v} := (hadm.1 v).preimage continuous_subtype_val
    refine Sg.isOpen_of_mem_nhds (g := 1) (Filter.mem_of_superset (hop.mem_nhds (by simp)) ?_)
    intro g hg
    show D.piN ρ g (Submodule.Quotient.mk v) = Submodule.Quotient.mk v
    have hp : D.piN ρ g (Submodule.Quotient.mk v) = Submodule.Quotient.mk (ρ (g : GU σ n) v) := rfl
    rw [hp, show ρ (g : GU σ n) v = v from hg]
  have hcpt : IsCompact (D.JT : Set D.T) := by
    rw [Subtype.isCompact_iff]
    have e : Subtype.val '' (D.JT : Set D.T) = (D.J : Set (GU σ n)) ∩ D.T := by
      ext x
      constructor
      · rintro ⟨a, ha, rfl⟩
        exact ⟨ha, a.2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨⟨x, h2⟩, h1, rfl⟩
    rw [e]
    exact D.isCompact_J.inter_right D.isClosed_alt
  have hcomm : ∀ a b : D.T, a * b = b * a := by
    intro a b
    apply Subtype.ext
    apply Subtype.ext
    exact isDiagM_commute ((hT _).1 a.2) ((hT _).1 b.2)
  have hmk : ∀ x : V, x ∈ jacU ρ ↔ (Submodule.Quotient.mk x : Jacquet ρ D.N) = 0 := by
    intro x
    rw [Submodule.Quotient.mk_eq_zero, hker]
  obtain ⟨lam₀, hlam0, hlam⟩ := exists_eigenform_of_smooth (D.piN ρ) hsm D.JT hcpt hcomm hfin
    (fun a => ξ (a : GU σ n)) (Submodule.Quotient.mk y) (fun h => hy ((hmk y).2 h))
    (fun a => by
      have hp : D.piN ρ a (Submodule.Quotient.mk y) = Submodule.Quotient.mk (ρ (a : GU σ n) y) := rfl
      rw [hp, ← Submodule.Quotient.mk_smul, ← sub_eq_zero, ← Submodule.Quotient.mk_sub]
      exact (hmk _).1 (hyt _ ((hT _).1 a.2)))
    (fun k hk => hyk _ (hIK (hJ ▸ hk)) ((hT _).1 k.2))
  refine ⟨lam₀ ∘ₗ (twKer ρ D.N 1).mkQ, ?_, ?_, ?_⟩
  · intro x hx
    have h1 : (twKer ρ D.N 1).mkQ x = 0 := (hmk x).1 hx
    simp [h1]
  · intro h
    apply hlam0
    refine LinearMap.ext fun w => ?_
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    exact LinearMap.congr_fun h v
  · intro s hs v
    exact hlam ⟨s, (hT s).2 hs⟩ (Submodule.Quotient.mk v)

theorem eqFormU : EqFormU :=
  eqFormU_of (fun G _ _ _ => GlobalTheory.T.jacquet_lemma_holds G) GlobalTheory.T.iwahori_unipotent_datum GlobalTheory.CompanionTheory.DomUnitary.domU GlobalTheory.CompanionTheory.KUFactsU.kuFacts

end GlobalTheory.CompanionTheory.EqForm
