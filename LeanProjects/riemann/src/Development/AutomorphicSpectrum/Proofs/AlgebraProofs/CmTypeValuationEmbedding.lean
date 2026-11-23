import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LinearIndependentEigProj
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.EigCoordApply
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.StatementUnavailableOneStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SumEigenProjectionsEqSelfStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.CmTypePolynomialVanishingCriterionStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeSpanIntersectionBasisStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HodgeLatticeDualEigenDecompositionStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DualModuleConjugateEigenActionStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ValuationLatticeMatrixReductionStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ConjugateEmbeddingsValuationRankBoundStatement

open scoped NNReal
open AlgebraicGeometry CategoryTheory Limits NumberField GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Flat.ExG

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.ExG

theorem targetO : TargetO := by
  intro E _ _ C _ _ ν bar σ σ' rk p q hℓ hint hcard hσ' hbar
  classical
  obtain ⟨ℓ, h0, h1⟩ := hℓ
  haveI : Finite (E →+* C) := Nat.finite_of_card_ne_zero (by
    rw [hcard]; exact Module.finrank_pos.ne')
  letI : Fintype (E →+* C) := Fintype.ofFinite _
  have hcard' : Fintype.card (E →+* C) = Module.finrank ℚ E := by rw [← Nat.card_eq_fintype_card, hcard]
  have hsumAll := GlobalTheory.T.sum_eigen_projections_eq_self E C hcard'
  let emb : (E →+* C) → (𝓞 E →+* ν.valuationSubring) := fun s =>
    (s.comp (algebraMap (𝓞 E) E)).codRestrict ν.valuationSubring (fun a => hint s a)
  have hemb : ∀ s (a : 𝓞 E), ((emb s a : ν.valuationSubring) : C) = s (a : E) := fun s a => rfl
  obtain ⟨π, hπ1, hπ2⟩ := GlobalTheory.T.statement_unavailable_one E ν.valuationSubring C emb (fun s a => hemb s a) hcard σ
  let D : (E →+* C) → Prop := fun s => ∀ a, ¬ IsUnit (emb s a - emb σ a)
  let S := {s // D s}
  have hDσ : D σ := fun a => by simp
  let τ : S := ⟨σ, hDσ⟩
  let a : S → ν.valuationSubring := fun s => emb s.1 π
  have ha : Function.Injective a := fun s s' e => Subtype.ext (hπ1 _ _ s.2 s'.2 e)
  have hmono : ∀ f : (E →+* C) → ν.valuationSubring, (∀ s, ¬ D s → f s = 0) →
      ((∃ g : Polynomial ν.valuationSubring, ∀ s, D s → f s = g.eval (emb s π)) ↔
        f ∈ Submodule.span ν.valuationSubring (Set.range fun a : 𝓞 E => fun s => emb s a)) := by
    intro f hf
    refine hπ2 f (fun s hs => hf s ?_)
    intro hd
    obtain ⟨b, hb⟩ := hs
    exact hd b hb

  have hbarE : ∀ s : E →+* C, ∃ s' : E →+* C, ∀ a : 𝓞 E, s' (a : E) = s (bar a : 𝓞 E) := by
    intro s
    have hinj : Function.Injective ((s.comp (algebraMap (𝓞 E) E)).comp bar.toRingHom) := by
      refine (s.injective.comp (FaithfulSMul.algebraMap_injective (𝓞 E) E)).comp bar.injective
    exact ⟨IsFractionRing.lift hinj, fun a => IsFractionRing.lift_algebraMap hinj a⟩
  choose sbar hsbar using hbarE
  let r : S → ℕ := fun s => rk (sbar s.1)
  let P : C := ∏ s ∈ Finset.univ.erase τ, ((a τ : C) - (a s : C))
  have hne : ∀ s ∈ Finset.univ.erase τ, ((a τ : C) - (a s : C)) ≠ 0 := by
    intro s hs e
    have : a τ = a s := Subtype.ext (sub_eq_zero.1 e)
    exact (Finset.mem_erase.1 hs).1 (ha this).symm
  have hP : P ≠ 0 := Finset.prod_ne_zero_iff.2 hne
  let Q : C := ∏ s ∈ Finset.univ.erase τ, ((a τ : C) - (a s : C)) ^ r s
  have hQ : Q ≠ 0 := Finset.prod_ne_zero_iff.2 fun s hs => pow_ne_zero _ (hne s hs)
  refine ⟨Q / P ^ (p + q), div_ne_zero hQ (pow_ne_zero _ hP), ?_⟩
  intro W _ _ _ _ _ ρ ρH HV Lie x v w u A hfst hinr hmap hfil hfree hrk hv hvs hw hws had hAl hAs
  have hIv : ν.Integers ν.valuationSubring :=
    { hom_inj := Subtype.val_injective
      map_le_one := fun x => x.2
      exists_of_le_one := fun {r} h => ⟨⟨r, h⟩, rfl⟩ }
  have hsumW := hsumAll W ρ
  have hsumH := hsumAll _ ρH

  have fstE : ∀ (s : E →+* C) (y : W × Module.Dual C W), (HT.eigProj ρH s y).1 = HT.eigProj ρ s y.1 := by
    intro s y
    simp only [HT.eigProj, LinearMap.sum_apply, LinearMap.smul_apply, Prod.fst_sum, Prod.smul_fst, hfst]
  let T : S → (Fin (p + q) → C) →ₗ[C] (W × Module.Dual C W) := fun s => eigCoord ρH x s.1
  let g : S → (Fin (p + q) → C) →ₗ[C] W := fun s => (LinearMap.fst C W (Module.Dual C W)) ∘ₗ T s
  have hgT : ∀ s y, g s y = (T s y).1 := fun s y => rfl
  have Tmem : ∀ s y, T s y ∈ HT.eigSp ρH s.1 := by
    intro s y
    change eigCoord ρH x s.1 y ∈ _
    rw [eigCoord_apply]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (HT.LatBasic.eigProj_mem _ _ _)
  have gmem : ∀ s y, g s y ∈ HT.eigSp ρ s.1 := by
    intro s y
    rw [HT.LatBasic.mem_eigSp]
    intro b
    rw [hgT, ← hfst, HT.LatBasic.mem_eigSp.1 (Tmem s y) b]
    rfl
  have Tinj : ∀ s, Function.Injective (T s) := by
    intro s
    have hli := HodgeDeterminantLattice.linearIndependent_eigProj (A := ν.valuationSubring) s.1 hfree
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    change eigCoord ρH x s.1 y = 0 at hy
    rw [eigCoord_apply] at hy
    exact funext (Fintype.linearIndependent_iff.1 hli y hy)
  have Tsurj : ∀ s y, y ∈ HT.eigSp ρH s.1 → ∃ z, T s z = y := by
    intro s y hy
    have hsp := HodgeDeterminantLattice.span_eigProj (A := ν.valuationSubring) s.1 hfree
    rw [← hsp] at hy
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun C).1 hy
    exact ⟨c, by change eigCoord ρH x s.1 c = y; rw [eigCoord_apply]; exact hc⟩

  have projSum : ∀ (f : S → Fin (p + q) → C) (t : S), HT.eigProj ρH t.1 (∑ s, T s (f s)) = T t (f t) := by
    intro f t
    rw [map_sum, Finset.sum_eq_single t]
    · exact HT.LatBasic.eigProj_of_mem (Tmem _ _)
    · intro s _ hs
      exact HT.LatBasic.eigProj_of_ne (fun e => hs (Subtype.ext e).symm) (Tmem _ _)
    · simp
  have hind : ∀ f : S → Fin (p + q) → C, ∑ s, g s (f s) = 0 → ∀ s, g s (f s) = 0 := by
    intro f hf t
    have h2 := congrArg (HT.eigProj ρ t.1) hf
    rw [map_sum, map_zero, Finset.sum_eq_single t] at h2
    · rwa [HT.LatBasic.eigProj_of_mem (gmem _ _)] at h2
    · intro s _ hs
      exact HT.LatBasic.eigProj_of_ne (fun e => hs (Subtype.ext e).symm) (gmem _ _)
    · simp
  have hblk := GlobalTheory.T.cm_type_polynomial_vanishing_criterion E C ν emb (fun s a => hemb s a) hcard' D π hmono _ ρH HV (p + q) x hfree
  obtain ⟨hb1, hb2⟩ := hblk
  have sumFst : ∀ f : S → Fin (p + q) → C, (∑ s, T s (f s)).1 = ∑ s, g s (f s) := by
    intro f
    exact map_sum (LinearMap.fst C W (Module.Dual C W)) _ _

  have hr : ∀ s, Module.finrank C (LinearMap.ker (g s)) = r s := by
    intro s
    have e1 : (LinearMap.ker (g s)).map (T s) =
        HT.eigSp ρH s.1 ⊓ LinearMap.ker (LinearMap.fst C W (Module.Dual C W)) := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact ⟨Tmem s z, hz⟩
      · rintro ⟨h1, h2⟩
        obtain ⟨z, rfl⟩ := Tsurj s y h1
        exact ⟨z, h2, rfl⟩
    change _ = rk (sbar s.1)
    rw [← hrk, ← GlobalTheory.T.dual_module_conjugate_eigen_action E C bar s.1 (sbar s.1) W ρ ρH hsumW (hsbar s.1) hbar hinr, ← e1]
    exact (Submodule.equivMapOfInjective _ (Tinj s) _).finrank_eq
  have hspanLie : Submodule.span C (Lie : Set W) = ⊤ := by
    rw [eq_top_iff]
    rintro y -
    have h3 : ((y, 0) : W × Module.Dual C W) ∈ Submodule.span C (HV : Set (W × Module.Dual C W)) := by
      rw [hfree.2.1]; trivial
    have h4 : ∀ z ∈ Submodule.span C (HV : Set (W × Module.Dual C W)), z.1 ∈ Submodule.span C (Lie : Set W) := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem z hz => exact Submodule.subset_span (hmap ▸ ⟨z, hz, rfl⟩)
      | zero => exact zero_mem _
      | add z z' _ _ h h' => exact add_mem h h'
      | smul c z _ h => exact Submodule.smul_mem _ c h
    exact h4 _ h3
  have hLieFG : Lie.FG := by
    rw [← hmap, hfree.2.2]
    exact (Submodule.fg_span (Set.finite_range _)).map _
  have hwLie : ∀ j, w j ∈ Lie ∧ w j ∈ HT.eigSp ρ σ' := by
    intro j
    have : w j ∈ HT.eigSub ρ σ' Lie := hws ▸ Submodule.subset_span ⟨j, rfl⟩
    exact this
  have hwsp : Submodule.span C (Set.range w) = HT.eigSp ρ σ' := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      exact (hwLie j).2
    · intro y hy
      obtain ⟨c, hc, hcy⟩ := HT.LatBasic.exists_smul_mem ν hIv (L := Lie) (x := y) (by rw [hspanLie]; trivial)
      have h3 : c • y ∈ HT.eigSub ρ σ' Lie := ⟨hcy, Submodule.smul_mem _ c hy⟩
      rw [← hws] at h3
      have h4 : c • y ∈ Submodule.span C (Set.range w) :=
        Submodule.span_le_restrictScalars ν.valuationSubring C _ h3
      have := Submodule.smul_mem _ c⁻¹ h4
      rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this
  have hsat : ∀ y, y ∈ Submodule.span ν.valuationSubring (Set.range w) ↔ y ∈ Lie ∧ y ∈ Submodule.span C (Set.range w) := by
    intro y
    rw [hws, hwsp]
    exact Iff.rfl
  have hφ := GlobalTheory.T.lattice_span_intersection_basis ν.valuationSubring C W Lie q w hLieFG hspanLie hw hsat
  have hσbar : sbar σ = σ' := IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E))
    (RingHom.ext fun b => (hsbar σ b).trans (hσ' b).symm)
  have hrτ : r τ = q := by
    change rk (sbar σ) = q
    rw [hσbar, ← hrk, ← hwsp, finrank_span_eq_card hw, Fintype.card_fin]

  have hex : ∀ i, ∃ z, T τ z = u i := fun i => Tsurj τ _ (had.1 i)
  choose U hU using hex
  have hU1 : ∀ i, g τ (U (Fin.castAdd q i)) = v i := fun i => by
    rw [hgT, hU]; exact had.2.1 i
  have hU2 : ∀ j, g τ (U (Fin.natAdd p j)) = 0 := fun j => by
    rw [hgT, hU]; exact (had.2.2 j).1
  have hTmemSpan : ∀ (n : ℕ) (b : Fin n → Fin (p + q) → C) (z : Fin (p + q) → C),
      z ∈ Submodule.span ν.valuationSubring (Set.range b) ↔
        T τ z ∈ Submodule.span ν.valuationSubring (Set.range fun i => T τ (b i)) := by
    intro n b z
    have e : Submodule.span ν.valuationSubring (Set.range fun i => T τ (b i)) =
        (Submodule.span ν.valuationSubring (Set.range b)).map ((T τ).restrictScalars ν.valuationSubring) := by
      rw [Submodule.map_span, ← Set.range_comp]
      rfl
    rw [e]
    constructor
    · exact fun h => ⟨z, h, rfl⟩
    · rintro ⟨z', h, e'⟩
      rwa [← Tinj τ e']
  have hLB2 : IsLatticeBasis ν (fun j => U (Fin.natAdd p j))
      (eigenQuot (W := fun _ => Fin (p + q) → C) (kerFil a (p + q) g) τ) := by
    refine ⟨?_, ?_⟩
    · apply LinearIndependent.of_comp (T τ)
      rw [Fintype.linearIndependent_iff]
      intro c hc k
      have h2 := congrArg (fun y : W × Module.Dual C W => y.2 (w k)) hc
      simp only [Function.comp, hU, Prod.snd_sum, Prod.smul_snd, LinearMap.sum_apply, LinearMap.smul_apply,
        (had.2.2 _).2, Prod.snd_zero, LinearMap.zero_apply, smul_eq_mul, mul_ite, mul_one, mul_zero] at h2
      simpa using h2
    · ext z
      rw [hTmemSpan]
      simp only [hU]
      rw [GlobalTheory.T.hodge_lattice_dual_eigen_decomposition E ν.valuationSubring C bar σ σ' W ρ ρH HV Lie q w (fun j => u (Fin.natAdd p j)) hsumW hσ' hbar hfst hinr
        hfil hwsp (fun j => (hwLie j).1) (fun j => ⟨had.1 _, (had.2.2 j).1, (had.2.2 j).2⟩) hφ]
      constructor
      · rintro ⟨φ, h1, h2⟩
        obtain ⟨f, hf, hfs⟩ := hb2 _ h1
        refine ⟨f, ⟨hf, fun s => ?_⟩, ?_⟩
        · rw [hgT]
          change (eigCoord ρH x s.1 (f s)).1 = 0
          rw [← hfs, fstE]
          simp
        · apply Tinj τ
          rw [← h2, hfs τ]
          rfl
      · rintro ⟨f, ⟨hf, hg0⟩, rfl⟩
        have h3 := (hb1 f).2 hf
        have h4 : (∑ s, T s (f s)).1 = 0 := by
          rw [sumFst]
          exact Finset.sum_eq_zero fun s _ => hg0 s
        refine ⟨(∑ s, T s (f s)).2, ?_, ?_⟩
        · have : ((0, (∑ s, T s (f s)).2) : W × Module.Dual C W) = ∑ s, T s (f s) := Prod.ext h4.symm rfl
          rw [this]
          exact h3
        · have : ((0, (∑ s, T s (f s)).2) : W × Module.Dual C W) = ∑ s, T s (f s) := Prod.ext h4.symm rfl
          rw [this]
          exact projSum f τ
  have hvs' : ∀ y, y ∈ Submodule.span ν.valuationSubring (Set.range v) ↔
      y ∈ LinearMap.range (g τ) ∧ ∃ f ∈ freeLattice a (p + q), ∑ s, g s (f s) = y := by
    intro y
    rw [hvs]
    constructor
    · rintro ⟨hy1, hy2⟩
      have hy2' : y ∈ HT.eigSp ρ σ := hy2
      rw [← hmap] at hy1
      obtain ⟨η, hη, rfl⟩ := hy1
      change η.1 ∈ HT.eigSp ρ σ at hy2'
      obtain ⟨z, hz⟩ := Tsurj τ _ (HT.LatBasic.eigProj_mem ρH σ η)
      obtain ⟨f, hf, hfs⟩ := hb2 _ hη
      refine ⟨⟨z, ?_⟩, f, hf, ?_⟩
      · change (T τ z).1 = η.1
        rw [hz, fstE]
        exact HT.LatBasic.eigProj_of_mem hy2'
      · have h5 : ∀ s, g s (f s) = HT.eigProj ρ s.1 η.1 := fun s => by
          rw [hgT, ← fstE, hfs s]
        simp only [h5]
        rw [Finset.sum_eq_single τ]
        · exact HT.LatBasic.eigProj_of_mem hy2'
        · intro s _ hs
          exact HT.LatBasic.eigProj_of_ne (fun e => hs (Subtype.ext e)) hy2'
        · simp
    · rintro ⟨⟨z, rfl⟩, f, hf, e⟩
      refine ⟨?_, gmem τ z⟩
      rw [← hmap]
      exact ⟨_, (hb1 f).2 hf, (sumFst f).trans e⟩
  have hLBA : IsLatticeBasis ν (fun i => ∑ j, A i j • U j)
      (eigenQuot (W := fun _ => Fin (p + q) → C) (freeLattice a (p + q)) τ) := by
    have hTA : ∀ i, T τ (∑ j, A i j • U j) = ∑ j, A i j • u j := fun i => by
      simp only [map_sum, map_smul, hU]
    refine ⟨?_, ?_⟩
    · apply LinearIndependent.of_comp (T τ)
      have : (T τ) ∘ (fun i => ∑ j, A i j • U j) = fun i => ∑ j, A i j • u j := funext hTA
      rw [this]
      exact hAl
    · ext z
      rw [hTmemSpan]
      simp only [hTA]
      rw [hAs]
      constructor
      · rintro ⟨η, hη, e⟩
        obtain ⟨f, hf, hfs⟩ := hb2 _ hη
        refine ⟨f, hf, ?_⟩
        apply Tinj τ
        have e' : HT.eigProj ρH σ η = T τ z := e
        rw [← e', hfs τ]
        rfl
      · rintro ⟨f, hf, rfl⟩
        exact ⟨_, (hb1 f).2 hf, projSum f τ⟩
  obtain ⟨ε, hε⟩ := GlobalTheory.T.valuation_lattice_matrix_reduction C ν ℓ h0 h1 S a p q τ r W g v U A ha hind hr hrτ hv hvs' hU1 hU2 hLB2 hLBA
  refine ⟨ε, ?_⟩
  change A.det * P ^ (p + q) = _ * Q at hε
  change A.det = ((ε : ν.valuationSubring) : C) * (Q / P ^ (p + q))
  rw [← mul_div_assoc, ← hε, mul_div_cancel_right₀ _ (pow_ne_zero _ hP)]

end GlobalTheory.CompanionTheory.Ar.Flat.ExG

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem det_adapted_eq_unit_mul_const : ∀ (E : Type) [Field E] [NumberField E] (V C : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Field C] [CharZero C] [Algebra V C] [IsFractionRing V C] (bar : 𝓞 E ≃+* 𝓞 E) (σ σ' : E →+* C) (rk : (E →+* C) → ℕ) (p q : ℕ) (ν : Valuation C NNReal), ν.Integers V → (∃ ℓ : C, 0 < ν ℓ ∧ ν ℓ < 1) → (∀ (s : E →+* C) (a : 𝓞 E), s (a : E) ∈ (algebraMap V C).range) → Nat.card (E →+* C) = Module.finrank ℚ E → (∀ a : 𝓞 E, σ' (a : E) = σ (bar a : 𝓞 E)) → (∀ a, bar (bar a) = a) → ∃ γ : C, γ ≠ 0 ∧ ∀ (W : Type) [AddCommGroup W] [Module C W] [Module V W] [IsScalarTower V C W] [FiniteDimensional C W] (ρ : 𝓞 E →+* Module.End C W) (ρH : 𝓞 E →+* Module.End C (W × Module.Dual C W)) (HV : Submodule V (W × Module.Dual C W)) (Lie : Submodule V W) (x : Fin (p + q) → W × Module.Dual C W) (v : Fin p → W) (w : Fin q → W) (u : Fin (p + q) → W × Module.Dual C W) (A : Matrix (Fin (p + q)) (Fin (p + q)) C), (∀ a y, (ρH a y).1 = ρ a y.1) → (∀ a φ, ρH a (0, φ) = (0, φ ∘ₗ ρ (bar a))) → HV.map ((LinearMap.fst C W (Module.Dual C W)).restrictScalars V) = Lie → (∀ φ : Module.Dual C W, (0, φ) ∈ HV ↔ ∀ e ∈ Lie, φ e ∈ (algebraMap V C).range) → HT.IsFreeOn ρH HV x → (∀ s, Module.finrank C (HT.eigSp ρ s) = rk s) → LinearIndependent C v → Submodule.span V (Set.range v) = HT.eigSub ρ σ Lie → LinearIndependent C w → Submodule.span V (Set.range w) = HT.eigSub ρ σ' Lie → IsAdapted ρH σ v w u → LinearIndependent C (fun i => ∑ j, A i j • u j) → Submodule.span V (Set.range fun i => ∑ j, A i j • u j) = HT.eigQuot ρH σ HV → ∃ ε : Vˣ, A.det = algebraMap V C ε * γ :=
  GlobalTheory.T.conjugate_embeddings_valuation_rank_bound ExG.targetO

end GlobalTheory.CompanionTheory.Ar.Flat
