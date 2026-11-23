import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SphericalEmbeddings.ExtremeSph
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SphericalEmbeddings.SigmaUniqueEqStdBlocks
import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.ExhaustionOfThree
import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.LUnlinkedIrrOfSeg
import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.Outright
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.SegmentJacquetSubquotients.SegmentRepresentation
import Development.AbelianVarietyTheory.Definitions.Divisors.EqOfHasValueAtInfinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedPrincipalSeriesNoInvariant

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Zc

namespace PositivityTheory.Rg.BcB.N3.Pus

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isSmoothChar_unr (α : ℂˣ) : IsSmoothChar (unrChar k α) := isSmoothChar_of_isUnram (isUnram_unrChar k α)

abbrev cls (α : ℂˣ) : IrrGL k := IrrGL.ofChar (unrChar k α) (isSmoothChar_unr α)

theorem norm_lt_of_nu {α β : ℂˣ} {m : ℕ} (hm : 0 < m) (h : (cls (k := k) β) = (cls (k := k) α).nu (m : ℂ)) :
    ‖(β : ℂ)‖ < ‖(α : ℂ)‖ := by
  rw [IrrGL.nu, IrrGL.tw_ofChar, IrrGL.ofChar_inj] at h
  obtain ⟨ϖ, hϖ⟩ := GlobalTheory.PrinTwo.NoFix.exists_unif k
  have e := congrArg (fun χ : kˣ →* ℂˣ => ((χ ϖ : ℂˣ) : ℂ)) h
  simp only [MonoidHom.mul_apply, Units.val_mul] at e
  rw [unrChar_uniformizer k β hϖ, unrChar_uniformizer k α hϖ, val_absPow] at e
  have hn : nabs k ϖ = (resCard k : ℝ)⁻¹ := by
    rw [GlobalTheory.LGrp.nabs_eq_zpow, ord_eq_one hϖ]; simp
  have hq : (1 : ℝ) < resCard k := by exact_mod_cast one_lt_resCard (k := k)
  have hn1 : nabs k ϖ < 1 := by rw [hn]; exact inv_lt_one_of_one_lt₀ hq
  have hn0 : 0 < nabs k ϖ := nabs_pos' k ϖ
  have hp : ‖((nabs k ϖ : ℝ) : ℂ) ^ ((m : ℕ) : ℂ)‖ = nabs k ϖ ^ m := by
    rw [Complex.cpow_natCast, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hn0]
  rw [e, norm_mul, hp]
  have ha : 0 < ‖(α : ℂ)‖ := norm_pos_iff.2 α.ne_zero
  calc ‖(α : ℂ)‖ * nabs k ϖ ^ m < ‖(α : ℂ)‖ * 1 :=
        mul_lt_mul_of_pos_left (pow_lt_one₀ hn0.le hn1 hm.ne') ha
    _ = ‖(α : ℂ)‖ := mul_one _

theorem uniqSub' : UniqSub k := by
  intro h0 n ξ hm V W _ _ _ _ π σ hπ hσ f g hf hg
  let c : Fin n → IrrGL k := fun i => cls (ξ i)
  let x : Fin n → IrrGL k := fun a => c (Fin.rev a)
  have hc : ∀ a, (x a).IsCusp := fun a => IrrGL.isCusp_ofChar _ _
  let Δ : Fin n → Segment k := fun a => Segment.single (x a) (hc a)
  have hord : IsOrderedForm Δ (Finset.univ.val.map Δ) := by
    refine ⟨rfl, fun i j hij hp => ?_⟩
    obtain ⟨-, m, hm0, he⟩ := hp
    simp only [Δ, Segment.single, Segment.first_ofFirst] at he
    have hlt := norm_lt_of_nu (k := k) hm0 he
    have hle := hm (Fin.rev j) (Fin.rev i) (Fin.rev_le_rev.2 hij.le)
    exact absurd hle (not_le.2 hlt)
  have hseg : ∀ a, IsLSeg (Δ a) (x a).rep := by
    intro a
    have ht : (Δ a).term = fun _ : Fin 1 => x a := by
      funext b
      have hb : (b : ℕ) = 0 := by
        have := b.2
        change (b : ℕ) < 1 at this
        omega
      simp [Δ, Segment.single, Segment.term, hb]
    have hd : ∑ b, ((Δ a).term b).1 = (x a).1 := by
      rw [ht]
      change ∑ _b : Fin 1, (x a).1 = (x a).1
      simp
    refine ⟨hd, ?_⟩
    obtain ⟨E⟩ := nonempty_equiv_prodIrr_one (x a) (by simp)
    have key : ∀ (y : Fin 1 → IrrGL k) (hy : ∑ b, (y b).1 = (x a).1), y = (fun _ : Fin 1 => x a) →
        IsCosocle (x a).rep (prodIrr y hy) := by
      rintro y hy rfl
      exact (isCosocle_self (x a).2.rep.irr).of_equiv (Representation.Equiv.refl _) E
    exact key _ hd ht
  have hLF : LFactors (Finset.univ.val.map Δ) x := ⟨Δ, hord, hseg⟩
  have hdn : ∑ a, (x a).1 = n := by
    change ∑ _a : Fin n, (1 : ℕ) = n; simp
  have := h0
  obtain ⟨P0, hP0⟩ := PositivityTheory.Exh.standardCosocleGL_holds k _ n n x hdn hLF
  have hL : IsL (Finset.univ.val.map Δ) P0.ρ := ⟨n, x, hdn, hLF, hP0⟩
  have hdr : ∑ a, (x (Fin.rev a)).1 = n := by
    change ∑ _a : Fin n, (1 : ℕ) = n; simp
  have hsoc := PositivityTheory.Exh.lSocleGL_of
    (fun k _ _ _ _ => PositivityTheory.Exh.lUnlinkedIrr_of_seg PositivityTheory.RgGu.segmentRepresentation k) k _ n n x hdr hLF P0.ρ hL
  have h1 : ∑ _ : Fin n, 1 = n := by simp
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : (iP (k := k) ξ).IntertwiningMap
      (multiProd (stdBlocks (fun _ : Fin n => 1) h1) fun i => detRep (Fin 1) (unrChar k (ξ i))),
      Function.Injective Ψ :=
    sigmaUnique_eq_stdBlocks n h1 ▸ exists_emb k n fun i => unrChar k (ξ i)
  let E1 := prodIrrEquiv h1 (fun i => detRep (Fin 1) (unrChar k (ξ i)))
    (fun i => (IrrRep.det (Fin 1) _ (isSmoothChar_unr (ξ i))).smooth)
    (fun i => (IrrRep.det (Fin 1) _ (isSmoothChar_unr (ξ i))).irr)
  have key2 : ∀ (y : Fin n → IrrGL k) (hy : ∑ a, (y a).1 = n), y = c →
      Nonempty ((prodIrr (fun a => IrrGL.of (detRep (Fin 1) (unrChar k (ξ a)))
        (IrrRep.det (Fin 1) _ (isSmoothChar_unr (ξ a))).smooth (IrrRep.det (Fin 1) _ (isSmoothChar_unr (ξ a))).irr) h1).Equiv
        (prodIrr y hy)) := by
    rintro y hy rfl
    exact ⟨Representation.Equiv.refl _⟩
  obtain ⟨E2⟩ := key2 (x ∘ Fin.rev) hdr (funext fun a => by simp [x])
  let Φ := E2.toIntertwiningMap.comp (E1.toIntertwiningMap.comp Ψ)
  have hΦ : Function.Injective Φ :=
    E2.toLinearEquiv.injective.comp (E1.toLinearEquiv.injective.comp hΨ)
  have hfi : Function.Injective f := by
    have := hπ; exact (Representation.IsIrreducible.injective_or_eq_zero f).resolve_right hf
  have hgi : Function.Injective g := by
    have := hσ; exact (Representation.IsIrreducible.injective_or_eq_zero g).resolve_right hg
  obtain ⟨a⟩ := hsoc.equiv_of_embeds hπ ⟨Φ.comp f, hΦ.comp hfi⟩
  obtain ⟨b⟩ := hsoc.equiv_of_embeds hσ ⟨Φ.comp g, hΦ.comp hgi⟩
  exact ⟨a.trans b.symm⟩

end PositivityTheory.Rg.BcB.N3.Pus

end
