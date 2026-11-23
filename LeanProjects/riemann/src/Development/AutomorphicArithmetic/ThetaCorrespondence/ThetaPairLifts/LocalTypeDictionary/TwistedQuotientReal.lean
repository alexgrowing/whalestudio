import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PolynomialRepresentationTriple
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.HoweConditionActionCoinvariantsFock
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PolynomialRepresentationTripleStatement

section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
namespace GlobalTheory.RealQuot
theorem twist_quotient_isReal : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (a b : D.what₂.Tau → ℚ),
    ∃ (Pr : ModuleCat.{0} ℂ) (ρ : D.what₂.Tau → Matrix (Fin X.rank) (Fin X.rank) ℂ → Module.End ℂ Pr)
      (q : PolF D X.rank W.rank →ₗ[ℂ] Pr) (q' : PolF D X.rank W₁.rank →ₗ[ℂ] Pr),
      Function.Surjective q ∧ Function.Surjective q' ∧ Module.rank ℂ Pr ≤ Cardinal.aleph0 ∧
      (∀ N : Submodule ℂ Pr, (∀ τ, ∀ Y ∈ lieAt X τ, ∀ x ∈ N, ρ τ Y x ∈ N) → N = ⊥ ∨ N = ⊤) ∧
      ∀ α β, IsTriple W W₁ X α β → (∀ τ, HasInfExp D α τ (a τ) ∧ HasInfExp D β τ (b τ)) →
        ∀ ωA ωB Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
          (∀ f, IsFinF ψ θ true A B f → ∃ φ : Pr →ₗ[ℂ] Pi, (∀ τ, ∀ Y ∈ lieAt X τ, φ ∘ₗ ρ τ Y = rl τ Y ∘ₗ φ) ∧
            ∀ P, p (fockF ψ θ true A B f P) = φ (q P)) ∧
          ∀ f, IsFinF ψ θ false A₁ B f → ∃ φ : Pr →ₗ[ℂ] Pi, (∀ τ, ∀ Y ∈ lieAt X τ, φ ∘ₗ ρ τ Y = rl τ Y ∘ₗ φ) ∧
            ∀ P, p' (fockF ψ θ false A₁ B f P) = φ (q' P) := by
  intro hH hP _ _ D ψ θ hψ hθ W W₁ X A A₁ B a b
  classical
  let ρA : LieIx X → Module.End ℂ (PolF D X.rank W.rank) := fun i => actT true A B b i.1.1 i.1.2
  let CA := coinv true A B (fun τ => b τ - a τ)
  let ρB : LieIx X → Module.End ℂ (PolF D X.rank W₁.rank) := fun i => actT false A₁ B a i.1.1 i.1.2
  let CB := coinv false A₁ B (fun τ => a τ - b τ)
  have fam : ∀ α β, IsTriple W W₁ X α β → (∀ τ, HasInfExp D α τ (a τ) ∧ HasInfExp D β τ (b τ)) →
      ∀ ωA ωB Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
      let σ : LieIx X → Module.End ℂ Pi := fun i => rl i.1.1 i.1.2
      let βA : {f // IsFinF ψ θ true A B f} → PolF D X.rank W.rank →ₗ[ℂ] Pi := fun f => p ∘ₗ fockF ψ θ true A B f.1
      let βB : {f // IsFinF ψ θ false A₁ B f} → PolF D X.rank W₁.rank →ₗ[ℂ] Pi := fun f => p' ∘ₗ fockF ψ θ false A₁ B f.1
      ((∀ f i, βA f ∘ₗ ρA i = σ i ∘ₗ βA f) ∧ (∀ f, CA ≤ LinearMap.ker (βA f)) ∧
        (∀ (j : {h // h ∈ GfC X}) f, ∃ f', rf j.1 ∘ₗ βA f = βA f') ∧ (⨆ f, LinearMap.range (βA f)) = ⊤) ∧
      ((∀ f i, βB f ∘ₗ ρB i = σ i ∘ₗ βB f) ∧ (∀ f, CB ≤ LinearMap.ker (βB f)) ∧
        (∀ (j : {h // h ∈ GfC X}) f, ∃ f', rf j.1 ∘ₗ βB f = βB f') ∧ (⨆ f, LinearMap.range (βB f)) = ⊤) ∧
      (∀ N : Submodule ℂ Pi, IsStab σ N → IsStab (fun j : {h // h ∈ GfC X} => rf j.1) N → N = ⊥ ∨ N = ⊤) ∧
      HoweCond ρA CA ∧ HoweCond ρB CB ∧ Nontrivial Pi := by
    intro α β htr hexp ωA ωB Pi rf rl p p' hm
    have hexpA : ∀ τ, HasInfExp D β τ (b τ) ∧ HasInfExp D (β / α) τ (b τ - a τ) :=
      fun τ => ⟨(hexp τ).2, hasInfExp_div D α β τ _ _ (hexp τ).1 (hexp τ).2⟩
    have hexpB : ∀ τ, HasInfExp D α τ (a τ) ∧ HasInfExp D (α / β) τ (a τ - b τ) :=
      fun τ => ⟨(hexp τ).1, hasInfExp_div D β α τ _ _ (hexp τ).2 (hexp τ).1⟩
    obtain ⟨oA1, oA2, oA3⟩ := GlobalTheory.T.orientedPair_fockMaps_lie_equivariant D ψ θ hθ true W X A B β (β / α) ωA b (fun τ => b τ - a τ) hm.weilA hexpA Pi rf rl p hm.mapA
    obtain ⟨oB1, oB2, oB3⟩ := GlobalTheory.T.orientedPair_fockMaps_lie_equivariant D ψ θ hθ false W₁ X A₁ B α (α / β) ωB a (fun τ => a τ - b τ) hm.weilB hexpB Pi rf rl p' hm.mapB
    have hspan : ∀ {M : HSp D} {ε : Bool} {A' : Fr M} (pp : (WO M X → ℂ) →ₗ[ℂ] Pi), (algF ψ θ ε A' B).map pp = ⊤ →
        (⨆ f : {f // IsFinF ψ θ ε A' B f}, LinearMap.range (pp ∘ₗ fockF ψ θ ε A' B f.1)) = ⊤ := by
      intro M ε A' pp h
      rw [eq_top_iff, ← h, algF, Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨f, P, hf, rfl⟩, rfl⟩
      exact Submodule.mem_iSup_of_mem ⟨f, hf⟩ ⟨P, rfl⟩
    refine ⟨⟨fun f i => LinearMap.ext fun P => oA1 f.1 f.2 i.1.1 i.1.2 i.2 P,
        fun f P hP => oA2 f.1 f.2 P hP, fun j f => ?_, hspan p hm.mapA.onto⟩,
      ⟨fun f i => LinearMap.ext fun P => oB1 f.1 f.2 i.1.1 i.1.2 i.2 P,
        fun f P hP => oB2 f.1 f.2 P hP, fun j f => ?_, hspan p' hm.mapB.onto⟩,
      fun N h1 h2 => hm.irred.2 N (fun g hg x hx => h2 ⟨g, hg⟩ x hx) (fun τ Y hY x hx => h1 ⟨(τ, Y), hY⟩ x hx),
      _root_.GlobalTheory.T.howe_condition_of_fock_coinvariants hH hP D ψ θ hψ hθ true W X A B β (β / α) ωA b _ hm.weilA hexpA,
      _root_.GlobalTheory.T.howe_condition_of_fock_coinvariants hH hP D ψ θ hψ hθ false W₁ X A₁ B α (α / β) ωB a _ hm.weilB hexpB, hm.irred.1⟩
    · obtain ⟨f', hf', e⟩ := oA3 j.1 j.2 f.1 f.2
      exact ⟨⟨f', hf'⟩, LinearMap.ext fun P => e P⟩
    · obtain ⟨f', hf', e⟩ := oB3 j.1 j.2 f.1 f.2
      exact ⟨⟨f', hf'⟩, LinearMap.ext fun P => e P⟩
  by_cases hex : ∃ α β, IsTriple W W₁ X α β ∧ (∀ τ, HasInfExp D α τ (a τ) ∧ HasInfExp D β τ (b τ)) ∧
      ∃ ωA ωB Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p'
  swap
  · refine ⟨ModuleCat.of ℂ PUnit, fun _ _ => 0, 0, 0, fun _ => ⟨0, Subsingleton.elim _ _⟩,
      fun _ => ⟨0, Subsingleton.elim _ _⟩, ?_, fun N _ => Or.inl (Submodule.eq_bot_of_subsingleton), ?_⟩
    · show Module.rank ℂ PUnit ≤ _
      simp
    · intro α β htr hexp ωA ωB Pi rf rl p p' hm
      exact absurd ⟨α, β, htr, hexp, ωA, ωB, Pi, rf, rl, p, p', hm⟩ hex
  obtain ⟨α₀, β₀, htr₀, hexp₀, ωA₀, ωB₀, Pi₀, rf₀, rl₀, p₀, p₀', hm₀⟩ := hex
  obtain ⟨⟨iA, kA, cA, sA⟩, ⟨iB, kB, cB, sB⟩, irr₀, hHA, hHB, hnt⟩ := fam α₀ β₀ htr₀ hexp₀ ωA₀ ωB₀ Pi₀ rf₀ rl₀ p₀ p₀' hm₀
  set σ₀ : LieIx X → Module.End ℂ Pi₀ := fun i => rl₀ i.1.1 i.1.2
  have nz : ∀ {Fm Q : Type} [AddCommGroup Q] [Module ℂ Q] (β : Fm → Q →ₗ[ℂ] Pi₀), (⨆ f, LinearMap.range (β f)) = ⊤ →
      ∃ f, β f ≠ 0 := by
    intro Fm Q _ _ β h
    by_contra hc
    push_neg at hc
    have : (⊤ : Submodule ℂ Pi₀) = ⊥ := by
      rw [← h]; exact iSup_eq_bot.2 fun f => by rw [hc f, LinearMap.range_zero]
    exact bot_ne_top this.symm
  have wit : ∀ {Q : Type} [AddCommGroup Q] [Module ℂ Q] (ρ : LieIx X → Module.End ℂ Q) (C : Submodule ℂ Q)
      (β : Q →ₗ[ℂ] Pi₀), (∀ i, β ∘ₗ ρ i = σ₀ i ∘ₗ β) → C ≤ LinearMap.ker β → β ≠ 0 →
      IsStab ρ (LinearMap.ker β) ∧ C ≤ LinearMap.ker β ∧ LinearMap.ker β ≠ ⊤ := by
    intro Q _ _ ρ C β hi hk hne
    refine ⟨fun i x hx => ?_, hk, fun h => hne (LinearMap.ker_eq_top.1 h)⟩
    rw [LinearMap.mem_ker] at hx ⊢
    rw [← LinearMap.comp_apply, hi i, LinearMap.comp_apply, hx, map_zero]
  obtain ⟨fA, hfA⟩ := nz _ sA
  obtain ⟨fB, hfB⟩ := nz _ sB
  obtain ⟨wA1, wA2, wA3⟩ := wit ρA CA _ (iA fA) (kA fA) hfA
  obtain ⟨wB1, wB2, wB3⟩ := wit ρB CB _ (iB fB) (kB fB) hfB
  have radA : rad ρA CA ≠ ⊤ := rad_ne_top _ _ ρA CA _ hHA wA1 wA2 wA3
  have radB : rad ρB CB ≠ ⊤ := rad_ne_top _ _ ρB CB _ hHB wB1 wB2 wB3
  have CleA : CA ≤ rad ρA CA := wA2.trans (le_sSup ⟨wA1, wA2, wA3⟩)
  have CleB : CB ≤ rad ρB CB := wB2.trans (le_sSup ⟨wB1, wB2, wB3⟩)
  have simA : ∀ N, IsStab ρA N → rad ρA CA ≤ N → N = rad ρA CA ∨ N = ⊤ := by
    intro N h1 h2
    by_cases h : N = ⊤
    · exact Or.inr h
    · exact Or.inl (le_antisymm (le_sSup ⟨h1, CleA.trans h2, h⟩) h2)
  have simB : ∀ N, IsStab ρB N → rad ρB CB ≤ N → N = rad ρB CB ∨ N = ⊤ := by
    intro N h1 h2
    by_cases h : N = ⊤
    · exact Or.inr h
    · exact Or.inl (le_antisymm (le_sSup ⟨h1, CleB.trans h2, h⟩) h2)
  have ss₀ := GlobalTheory.T.exists_stable_complement_of_irreducible_span_intertwiners _ _ _ _ _ ρA CA σ₀ (fun j : {h // h ∈ GfC X} => rf₀ j.1) _ hHA iA kA cA sA irr₀
  have killA₀ : ∀ f, rad ρA CA ≤ LinearMap.ker _ := fun f => rad_le_ker _ _ _ ρA CA σ₀ _ (iA f) (kA f) radA ss₀
  have killB₀ := rad_le_ker _ _ _ ρB CB σ₀ _ (iB fB) (kB fB) radB ss₀
  obtain ⟨e, he⟩ := GlobalTheory.T.simple_quotients_iso_of_intertwined_semisimple _ _ _ _ _ ρA CA ρB CB σ₀ _ _ iA (iB fB) killA₀ killB₀ hfB sA simA simB ss₀
  let R := rad ρA CA
  let RB := rad ρB CB
  refine ⟨ModuleCat.of ℂ (PolF D X.rank W.rank ⧸ R),
    fun τ Y => if h : Y ∈ lieAt X τ then radAct ρA CA ⟨(τ, Y), h⟩ else 0,
    R.mkQ, e.symm.toLinearMap ∘ₗ RB.mkQ, R.mkQ_surjective, e.symm.surjective.comp RB.mkQ_surjective, ?_, ?_, ?_⟩
  · show Module.rank ℂ (PolF D X.rank W.rank ⧸ R) ≤ _
    refine (rank_quotient_le R).trans ?_
    rw [← (MvPolynomial.basisMonomials (FVar D X.rank W.rank) ℂ).mk_eq_rank'']
    exact Cardinal.mk_le_aleph0
  · intro N hN
    have hst : IsStab ρA (N.comap R.mkQ) := fun i x hx => by
      have h1 := hN i.1.1 i.1.2 i.2 _ hx
      simp only [dif_pos i.2] at h1
      exact h1
    have hle : R ≤ N.comap R.mkQ := fun x hx => by
      show R.mkQ x ∈ N
      rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero R).2 hx]
      exact N.zero_mem
    rcases simA _ hst hle with h | h
    · left
      rw [← Submodule.map_comap_eq_of_surjective R.mkQ_surjective N, h, Submodule.mkQ_map_self]
    · right
      rw [← Submodule.map_comap_eq_of_surjective R.mkQ_surjective N, h, Submodule.map_top, Submodule.range_mkQ]
  · intro α β htr hexp ωA ωB Pi rf rl p p' hm
    obtain ⟨⟨iA', kA', cA', sA'⟩, ⟨iB', kB', cB', sB'⟩, irr', -, -, -⟩ := fam α β htr hexp ωA ωB Pi rf rl p p' hm
    have ss' := GlobalTheory.T.exists_stable_complement_of_irreducible_span_intertwiners _ _ _ _ _ ρA CA (fun i : LieIx X => rl i.1.1 i.1.2) (fun j : {h // h ∈ GfC X} => rf j.1) _ hHA
      iA' kA' cA' sA' irr'
    refine ⟨fun f hf => ?_, fun f hf => ?_⟩
    · have hk := rad_le_ker _ _ _ ρA CA _ _ (iA' ⟨f, hf⟩) (kA' ⟨f, hf⟩) radA ss'
      refine ⟨R.liftQ (p ∘ₗ fockF ψ θ true A B f) hk, fun τ Y hY => ?_, fun P => rfl⟩
      simp only [dif_pos hY]
      refine Submodule.linearMap_qext _ (LinearMap.ext fun P => ?_)
      exact LinearMap.congr_fun (iA' ⟨f, hf⟩ ⟨(τ, Y), hY⟩) P
    · have hk := rad_le_ker _ _ _ ρB CB _ _ (iB' ⟨f, hf⟩) (kB' ⟨f, hf⟩) radB ss'
      refine ⟨RB.liftQ (p' ∘ₗ fockF ψ θ false A₁ B f) hk ∘ₗ e.toLinearMap, fun τ Y hY => ?_, fun P => ?_⟩
      · simp only [dif_pos hY]
        refine LinearMap.ext fun x => ?_
        have h1 := LinearMap.congr_fun (he ⟨(τ, Y), hY⟩) x
        simp only [LinearMap.comp_apply] at h1 ⊢
        rw [h1]
        have key : ∀ y, RB.liftQ (p' ∘ₗ fockF ψ θ false A₁ B f) hk (radAct ρB CB ⟨(τ, Y), hY⟩ y) =
            rl τ Y (RB.liftQ (p' ∘ₗ fockF ψ θ false A₁ B f) hk y) := by
          intro y
          obtain ⟨P, rfl⟩ := RB.mkQ_surjective y
          exact LinearMap.congr_fun (iB' ⟨f, hf⟩ ⟨(τ, Y), hY⟩) P
        exact key _
      · simp
end GlobalTheory.RealQuot
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_quotient_real : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (a b : D.what₂.Tau → ℚ),
    ∃ (Pr : ModuleCat.{0} ℂ) (ρ : D.what₂.Tau → Matrix (Fin X.rank) (Fin X.rank) ℂ → Module.End ℂ Pr)
      (q : PolF D X.rank W.rank →ₗ[ℂ] Pr) (q' : PolF D X.rank W₁.rank →ₗ[ℂ] Pr),
      Function.Surjective q ∧ Function.Surjective q' ∧ Module.rank ℂ Pr ≤ Cardinal.aleph0 ∧
      (∀ N : Submodule ℂ Pr, (∀ τ, ∀ Y ∈ lieAt X τ, ∀ x ∈ N, ρ τ Y x ∈ N) → N = ⊥ ∨ N = ⊤) ∧
      ∀ α β, IsTriple W W₁ X α β → (∀ τ, HasInfExp D α τ (a τ) ∧ HasInfExp D β τ (b τ)) →
        ∀ ωA ωB Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
          (∀ f, IsFinF ψ θ true A B f → ∃ φ : Pr →ₗ[ℂ] Pi, (∀ τ, ∀ Y ∈ lieAt X τ, φ ∘ₗ ρ τ Y = rl τ Y ∘ₗ φ) ∧
            ∀ P, p (fockF ψ θ true A B f P) = φ (q P)) ∧
          ∀ f, IsFinF ψ θ false A₁ B f → ∃ φ : Pr →ₗ[ℂ] Pi, (∀ τ, ∀ Y ∈ lieAt X τ, φ ∘ₗ ρ τ Y = rl τ Y ∘ₗ φ) ∧
            ∀ P, p' (fockF ψ θ false A₁ B f P) = φ (q' P) := by
  first | exact @_root_.GlobalTheory.RealQuot.twist_quotient_isReal | exact _root_.GlobalTheory.RealQuot.twist_quotient_isReal | (intros; apply _root_.GlobalTheory.RealQuot.twist_quotient_isReal <;> assumption)
end
