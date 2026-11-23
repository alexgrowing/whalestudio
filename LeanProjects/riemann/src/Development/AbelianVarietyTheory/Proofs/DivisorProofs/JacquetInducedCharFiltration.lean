import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsGenericIffIsGenericFor
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittRankLeSkewSignature
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSplitChartSplitChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundDomLtTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubquotientTwistFiltrationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentationSigmaEquivReindexStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SizeMatrixRelativeModulusStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModulusMiddleBlockDetStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairInducedTwistEquivStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairInducedEquivProdStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.CuspBlock GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.MidBlockCell
open GlobalTheory.LeviBlockExponent GlobalTheory.CuspBlock

theorem jacU_eq_twist_jac {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {α n : Type} [Fintype α] [LinearOrder α] [Fintype n] [DecidableEq n] {m : α → Type}
    [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] {V : Type} [AddCommGroup V] [Module ℂ V]
    (e : (Σ a, m a) ≃ n) (π : Representation ℂ (GL n k) V) :
    jacU e π = twist (jac e π) (deltaHalf k m) := by
  ext g v
  simp [jac, smul_smul]

theorem isSubquotient_of_equiv' {G V W U : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] [AddCommGroup U] [Module ℂ U] {Q : Representation ℂ G U} {σ₁ : Representation ℂ G V}
    {σ₂ : Representation ℂ G W} (h : IsSubquotient Q σ₁) (e : σ₁.Equiv σ₂) : IsSubquotient Q σ₂ :=
  h.trans (.of_surjective e.symm.toIntertwiningMap e.symm.toLinearEquiv.surjective)

theorem isSubquotient_twist_comp_of_equiv {G H V W U : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] [AddCommGroup U] [Module ℂ U] {Q : Representation ℂ H U}
    {σ₁ : Representation ℂ G V} {σ₂ : Representation ℂ G W} (e : σ₁.Equiv σ₂) (χ : G →* ℂˣ) (φ : H →* G)
    (h : IsSubquotient Q ((twist σ₁ χ).comp φ)) : IsSubquotient Q ((twist σ₂ χ).comp φ) :=
  h.trans (.of_surjective (compMap (twistMap e.symm.toIntertwiningMap χ) φ) e.symm.toLinearEquiv.surjective)

theorem isSubquotient_comp' {G H V U : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup U] [Module ℂ U] {Q : Representation ℂ G U} {σ : Representation ℂ G V}
    (h : IsSubquotient Q σ) (φ : H →* G) : IsSubquotient (Q.comp φ) (σ.comp φ) := by
  obtain ⟨S, f, hf⟩ := h
  exact ⟨⟨S.toSubmodule, fun g _ hv => S.apply_mem_toSubmodule (φ g) hv⟩,
    ⟨f.toLinearMap, fun g => f.isIntertwining' (φ g)⟩, hf⟩

theorem compMap_ne_zero' {G H V U : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup U] [Module ℂ U] {Q : Representation ℂ G U} {Y : Representation ℂ G V}
    (F : Q.IntertwiningMap Y) (hF : F ≠ 0) (φ : H →* G) : compMap F φ ≠ 0 := by
  intro h0
  apply hF
  ext v
  exact congrArg (fun T : Representation.IntertwiningMap (Q.comp φ) (Y.comp φ) => T v) h0

theorem isSmoothChar_pairChar {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (b : Fin 2 → ℕ) {χ : Fin 2 → kˣ →* ℂˣ} (hχ : ∀ j, IsSmoothChar (χ j)) :
    IsSmoothChar (pairChar k b χ) := by
  unfold pairChar
  refine Finset.prod_induction _ IsSmoothChar (fun _ _ => IsSmoothChar.mul) ?_ fun j _ => ?_
  · unfold IsSmoothChar; simp
  · exact (hχ j).detChar.comp _ (continuous_apply j)

theorem relJac_ofChar_apply {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {α β : Type} [Fintype α] [Fintype β] [LinearOrder β] {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
    {c : α → β → Type} [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)]
    (f : ∀ i, (Σ j, c i j) ≃ m i) (χ : Levi k m →* ℂˣ) (z : ∀ i, Levi k (c i))
    (w : Jacquet (ofChar χ) (relUnip k f)) :
    relJac f (ofChar χ) z w = ((((relDeltaHalf k c)⁻¹ * χ.comp (relEmb k f)) z : ℂˣ) : ℂ) • w := by
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  rw [relJac_mk, ofChar_apply, ← smul_eq_mul, Submodule.Quotient.mk_smul, smul_smul]
  congr 1
end GlobalTheory.MidBlockCell

namespace GlobalTheory.MidBlockCell
open GlobalTheory.LeviBlockExponent GlobalTheory.CuspBlock

set_option maxHeartbeats 1000000 in
theorem exists_map_of_midBlock : GlobalTheory.Published.GeometricLemmaFiltration → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (N : ℕ) (b : Fin 2 → ℕ) (hb : b 0 + b 1 = N) (χ : Fin 2 → kˣ →* ℂˣ),
    (∀ j, IsSmoothChar (χ j)) → ∀ (l d : ℕ) (hld : l + d ≤ N) (Vy : Type) [AddCommGroup Vy] [Module ℂ Vy]
    (Y : Representation ℂ (GL (Fin d) k) Vy) (W' : Type) [AddCommGroup W'] [Module ℂ W']
    (Q : Representation ℂ (GL (Fin d) k) W'),
    IsSubquotient Q ((jacU (tripPlace hld) (pairInd k b hb χ)).comp (midHom k l d N)) →
    ∀ f : Q.IntertwiningMap Y, f ≠ 0 →
    ∃ (x x' c c' : ℕ) (h : x + x' = d) (s₁ s₂ : ℝ), c + c' = l ∧
      s₁ - s₂ = (c : ℝ) - c' + ((x : ℝ) - x') / 2 - ((b 0 : ℝ) - b 1) / 2 ∧
      ∃ (V' : Type) (_ : AddCommGroup V') (_ : Module ℂ V') (Q' : Representation ℂ (GL (Fin (x + x')) k) V'),
        IsSubquotient Q' (prod₂ (detRep (Fin x) (χ 0 * absPow k (s₁ : ℂ))) (detRep (Fin x') (χ 1 * absPow k (s₂ : ℂ)))) ∧
        ∃ f' : Q'.IntertwiningMap (Y.comp (glCast h)), f' ≠ 0 := by
  intro hGL k _ _ _ _ N b hb χ hχ l d hld Vy _ _ Y W' _ _ Q hQ F hF
  have hρ : IsSmooth (ofChar (pairChar k b χ)) := (isSmooth_ofChar_iff _).2 (isSmoothChar_pairChar b hχ)
  obtain ⟨Nn, bb, hbb⟩ := hGL k (Fin 2) (Fin 3) (Fin N) (fun j => Fin (b j))
    (fun j => Fin (tripSizes l d N j)) (pairPlace b hb) (tripPlace hld)
  obtain ⟨S, hS, hS0, hSN, hcell⟩ := hbb ℂ (ofChar (pairChar k b χ)) hρ
  rw [jacU_eq_twist_jac] at hQ
  obtain ⟨t, V1, _, _, Q1, hQ1, F1, hF1⟩ := GlobalTheory.T.subquotient_twist_filtration _ _ _ Nn S hS hS0 hSN Q Y hQ F hF
  have hc : ∀ j, ∑ i, (bb t).1 i j = tripSizes l d N j := fun j => by simpa using (bb t).2.2 j
  have hM1 : (bb t).1 0 1 + (bb t).1 1 1 = d := by simpa [Fin.sum_univ_two, tripSizes] using hc 1
  have hM0 : (bb t).1 0 0 + (bb t).1 1 0 = l := by simpa [Fin.sum_univ_two, tripSizes] using hc 0
  let f : ∀ i, (Σ j, Fin ((bb t).1 i j)) ≃ Fin (b i) := (bb t).nonempty_rows.some
  let g : ∀ j, (Σ i, Fin ((bb t).1 i j)) ≃ Fin (tripSizes l d N j) := fun j =>
    if hj : j = 1 then by subst hj; exact pairPlace (fun i => (bb t).1 i 1) hM1 else (bb t).nonempty_cols.some j
  have hg1 : g 1 = pairPlace (fun i => (bb t).1 i 1) hM1 := by
    first | rfl | (simp only [g, dif_pos]; rfl) | (show dite _ _ _ = _; rw [dif_pos rfl])
  obtain ⟨φ⟩ := hcell t f g
  have hQ2 := isSubquotient_twist_comp_of_equiv φ _ _ hQ1
  let τ := (relJac f (ofChar (pairChar k b χ))).comp (swapBlocks k (fun i j => Fin ((bb t).1 i j)))
  let ψ := ((relDeltaHalf k (fun i j => Fin ((bb t).1 i j)))⁻¹ * (pairChar k b χ).comp (relEmb k f)).comp
    (swapBlocks k (fun i j => Fin ((bb t).1 i j)))
  have hτ : ∀ z w, τ z w = (ψ z : ℂ) • w := by
    intro z w
    exact relJac_ofChar_apply f (pairChar k b χ) _ w
  have hQ2' : IsSubquotient Q1 ((twist (relInd g τ) (deltaHalf k (fun j => Fin (tripSizes l d N j)))).comp
      (midHom k l d N)) := hQ2
  have hQ2'' : IsSubquotient Q1 ((twist (relInd g τ) (deltaHalf k (fun j => Fin (tripSizes l d N j)))).comp
      (MonoidHom.mulSingle (fun j => GL (Fin (tripSizes l d N j)) k) 1)) := hQ2'
  obtain ⟨V2, _, _, Q2, hQ3, F2, hF2⟩ := GlobalTheory.T.representation_sigma_equiv_reindex k g τ ψ hτ 1 _ Q1 Y hQ2'' F1 hF1
  let μ : Fin 2 → kˣ →* ℂˣ := fun i =>
    χ i * absPow k (((bb t).1 i 0 : ℂ) + (((bb t).1 i 1 : ℂ) - b i) / 2)
  have hψ : ψ.comp (MonoidHom.mulSingle (fun j => Levi k (fun i => Fin ((bb t).1 i j))) 1) =
      pairChar k (fun i => (bb t).1 i 1) μ := MonoidHom.ext fun z => GlobalTheory.T.size_matrix_relative_modulus k N l d b χ (bb t) f z
  have hν : (deltaHalf k (fun j => Fin (tripSizes l d N j))).comp
      (MonoidHom.mulSingle (fun j => GL (Fin (tripSizes l d N j)) k) 1) =
      detChar (Fin d) (absPow k (((N : ℂ) - 2 * l - d) / 2)) := MonoidHom.ext fun x => GlobalTheory.T.modulus_middle_block_det k l d N hld x
  rw [hg1, hψ, hν] at hQ3
  have hQ4 := isSubquotient_of_equiv' hQ3 (GlobalTheory.T.pair_induced_twist_equiv k (fun i => (bb t).1 i 1) d hM1 μ
    (absPow k (((N : ℂ) - 2 * l - d) / 2)) (isSmoothChar_of_isUnram (isUnram_absPow k _))).some
  have hQ5 := isSubquotient_of_equiv' (isSubquotient_comp' hQ4 (glCast hM1))
    (GlobalTheory.T.pair_induced_equiv_prod k (fun i => (bb t).1 i 1) d hM1 (fun i => μ i * absPow k (((N : ℂ) - 2 * l - d) / 2))).some
  obtain ⟨s₁, hs₁⟩ : ∃ s : ℝ, s = ((bb t).1 0 0 : ℝ) + (((bb t).1 0 1 : ℝ) - b 0) / 2 + ((N : ℝ) - 2 * l - d) / 2 := ⟨_, rfl⟩
  obtain ⟨s₂, hs₂⟩ : ∃ s : ℝ, s = ((bb t).1 1 0 : ℝ) + (((bb t).1 1 1 : ℝ) - b 1) / 2 + ((N : ℝ) - 2 * l - d) / 2 := ⟨_, rfl⟩
  have hμ0 : μ 0 * absPow k (((N : ℂ) - 2 * l - d) / 2) = χ 0 * absPow k (s₁ : ℂ) := by
    simp only [μ]
    rw [mul_assoc, ← absPow_add, hs₁]
    congr 2
    push_cast
    ring
  have hμ1 : μ 1 * absPow k (((N : ℂ) - 2 * l - d) / 2) = χ 1 * absPow k (s₂ : ℂ) := by
    simp only [μ]
    rw [mul_assoc, ← absPow_add, hs₂]
    congr 2
    push_cast
    ring
  have hQ6 : IsSubquotient (Q2.comp (glCast hM1)) (prod₂ (detRep (Fin ((bb t).1 0 1)) (χ 0 * absPow k (s₁ : ℂ)))
      (detRep (Fin ((bb t).1 1 1)) (χ 1 * absPow k (s₂ : ℂ)))) := by
    rw [← hμ0, ← hμ1]
    exact hQ5
  refine ⟨(bb t).1 0 1, (bb t).1 1 1, (bb t).1 0 0, (bb t).1 1 0, hM1, s₁, s₂, hM0, ?_, _, _, _,
    Q2.comp (glCast hM1), hQ6, compMap F2 (glCast hM1), compMap_ne_zero' F2 hF2 _⟩
  rw [hs₁, hs₂]
  ring

end GlobalTheory.MidBlockCell
