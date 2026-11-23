import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SegmentRepresentation
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentTermInjectiveStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityCuspidalProductStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicitySubquotientLeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IrreducibleSubquotientCuspidalPermutationStatement
import Development.WeilBound.CoreStatements.AutomorphicKernels.SquareIntegrableSegments.SegmentSubquotients.ExistsSegmentRepresentationStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentRepSplitIntertwinerStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StrictAntiOfTwoExceptionsStatement
import Development.WeilBound.CoreStatements.AutomorphicKernels.SquareIntegrableSegments.SegmentSubquotients.DerivativeCuspidalPairLengthStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.JacquetModuleFiniteLengthStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityPos
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IrreducibleSubquotientJacquetSegmentStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EquivOfMultiplicityOneUniqueFactorStatement

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg

noncomputable section

namespace GlobalTheory.CompanionTheory.LkSegFine

theorem cover {p q c d : ℕ} (deg : Fin c → ℕ) (hpos : ∀ a, 0 < deg a) (hsum : ∑ a, deg a = (p + q) * d)
    (f : Fin p → Fin c) (g : Fin q → Fin c) (hf : Function.Injective f) (hg : Function.Injective g)
    (hdis : Disjoint (Set.range f) (Set.range g)) (hfd : ∀ i, deg (f i) = d) (hgd : ∀ j, deg (g j) = d) :
    (∀ a, a ∈ Set.range f ∨ a ∈ Set.range g) ∧ c = p + q := by
  let φ : Fin p ⊕ Fin q → Fin c := Sum.elim f g
  have hφ : Function.Injective φ := by
    rintro (x | x) (z | z) h
    · exact congrArg _ (hf h)
    · exact absurd (show g z ∈ Set.range f from ⟨x, h⟩) (Set.disjoint_left.1 hdis · ⟨z, rfl⟩)
    · exact absurd (show f z ∈ Set.range g from ⟨x, h⟩) (Set.disjoint_right.1 hdis · ⟨z, rfl⟩)
    · exact congrArg _ (hg h)
  have hS : ∑ x : Fin p ⊕ Fin q, deg (φ x) = (p + q) * d := by
    simp [Fintype.sum_sum_type, φ, hfd, hgd, add_mul]
  have hsurj : Function.Surjective φ := by
    intro a
    by_contra hne
    have h2 : ∑ b ∈ Finset.univ.image φ, deg b = (p + q) * d := by
      rw [Finset.sum_image hφ.injOn]; exact hS
    have h3 : a ∉ Finset.univ.image φ := by
      simpa using fun x h => hne ⟨x, h⟩
    have h4 : deg a + ∑ b ∈ Finset.univ.image φ, deg b ≤ ∑ b, deg b := by
      rw [← Finset.sum_insert h3]
      exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    have := hpos a
    omega
  refine ⟨fun a => ?_, ?_⟩
  · obtain ⟨x | x, rfl⟩ := hsurj a
    · exact Or.inl ⟨x, rfl⟩
    · exact Or.inr ⟨x, rfl⟩
  · have := Fintype.card_of_bijective (⟨hφ, hsurj⟩ : Function.Bijective φ)
    simpa using this.symm

theorem word_eq_decreasing {X : Type*} (l : ℕ) (hl : 3 ≤ l) (t : ℕ → X)
    (hinj : ∀ a b, a < l → b < l → t a = t b → a = b) (y : Fin l → X)
    (i : Fin l) (g : Fin (l - 1) ↪o Fin l) (hcov : ∀ a, a = i ∨ a ∈ Set.range g) (hi : y i = t 0)
    (hg : ∀ j : Fin (l - 1), y (g j) = t (l - 1 - j))
    (i' : Fin l) (f : Fin (l - 1) ↪o Fin l) (hcov' : ∀ a, a = i' ∨ a ∈ Set.range f) (hi' : y i' = t (l - 1))
    (hf : ∀ j : Fin (l - 1), y (f j) = t (l - 2 - j)) (a : Fin l) : y a = t (l - 1 - a) := by
  have hex : ∀ a, ∃ n, n < l ∧ y a = t n := fun a => by
    rcases hcov a with rfl | ⟨j, rfl⟩
    · exact ⟨0, by omega, hi⟩
    · exact ⟨_, by omega, hg j⟩
  choose w hw hyw using hex
  have hwi : w i = 0 := hinj _ _ (hw i) (by omega) ((hyw i).symm.trans hi)
  have hwi' : w i' = l - 1 := hinj _ _ (hw i') (by omega) ((hyw i').symm.trans hi')
  have hwg : ∀ j, w (g j) = l - 1 - j := fun j => hinj _ _ (hw _) (by omega) ((hyw _).symm.trans (hg j))
  have hwf : ∀ j, w (f j) = l - 2 - j := fun j =>
    hinj _ _ (hw _) (by omega) ((hyw _).symm.trans (hf j))
  have h1 : ∀ a b, a < b → a ≠ i → b ≠ i → w b < w a := by
    intro a b hab ha hb
    obtain ⟨ja, rfl⟩ := (hcov a).resolve_left ha
    obtain ⟨jb, rfl⟩ := (hcov b).resolve_left hb
    have h2 : ja < jb := g.lt_iff_lt.1 hab
    have h3 := Fin.lt_def.1 h2
    have h4 := jb.2
    rw [hwg, hwg]
    omega
  have h2 : ∀ a b, a < b → a ≠ i' → b ≠ i' → w b < w a := by
    intro a b hab ha hb
    obtain ⟨ja, rfl⟩ := (hcov' a).resolve_left ha
    obtain ⟨jb, rfl⟩ := (hcov' b).resolve_left hb
    have h2 : ja < jb := f.lt_iff_lt.1 hab
    have h3 := Fin.lt_def.1 h2
    have h4 := jb.2
    rw [hwf, hwf]
    omega
  have hanti : StrictAnti w := GlobalTheory.T.strict_anti_of_two_exceptions l hl w hw i i' hwi hwi' h1 h2
  let φ : Fin l → Fin l := fun a => Fin.rev ⟨w a, hw a⟩
  have hφ : StrictMono φ := fun a b hab => Fin.rev_lt_rev.2 (Fin.lt_def.2 (hanti hab))
  have h3 : φ a = a := le_antisymm hφ.apply_le hφ.le_apply
  have h4 : l - (w a + 1) = a := by
    have := congrArg Fin.val h3
    simpa [φ, Fin.val_rev] using this
  have h5 := hw a
  have h6 : w a = l - 1 - a := by omega
  rw [hyw a, h6]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem sum_dec_fst (Γ : Segment k) : ∑ a, (dec Γ a).1 = Γ.deg := by
  show ∑ _ : Fin Γ.len, Γ.d = _
  simp [Segment.deg]

theorem isCusp_dec (Γ : Segment k) (a : Fin Γ.len) : (dec Γ a).IsCusp := Γ.isCusp_term _

theorem jm_congr {h N : ℕ} {x x' : Fin h → IrrGL k} (e : x = x') (hd : ∑ a, (x a).1 = N) (hd' : ∑ a, (x' a).1 = N)
    {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) : jm x hd π = jm x' hd' π := by
  subst e
  rfl

theorem dec_segLow (Δ : Segment k) (a : ℕ) (h0 : 0 < a) (i : Fin (segLow Δ a h0).len) :
    dec (segLow Δ a h0) i = Δ.first.nu ((a - 1 - (i : ℕ) : ℕ) : ℂ) := by
  have hi : (i : ℕ) < a := i.2
  have e : ((Fin.rev i : Fin (segLow Δ a h0).len) : ℕ) = a - 1 - i := by
    rw [Fin.val_rev]
    show a - ((i : ℕ) + 1) = _
    omega
  show Δ.first.nu (((Fin.rev i : Fin (segLow Δ a h0).len) : ℕ) : ℂ) = _
  rw [e]

theorem dec_segHigh (Δ : Segment k) (a : ℕ) (h1 : a < Δ.len) (j : Fin (segHigh Δ a h1).len) :
    dec (segHigh Δ a h1) j = Δ.first.nu ((a + (Δ.len - a - 1 - (j : ℕ)) : ℕ) : ℂ) := by
  have hj : (j : ℕ) < Δ.len - a := j.2
  have e : ((Fin.rev j : Fin (segHigh Δ a h1).len) : ℕ) = Δ.len - a - 1 - j := by
    rw [Fin.val_rev]
    show Δ.len - a - ((j : ℕ) + 1) = _
    omega
  show (Δ.first.nu ((a : ℕ) : ℂ)).nu (((Fin.rev j : Fin (segHigh Δ a h1).len) : ℕ) : ℂ) = _
  rw [e, IrrGL.nu_nu]
  push_cast
  rfl

theorem exists_class (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Γ : Segment k) :
    ∃ u : IrrGL k, u.1 = Γ.deg ∧ IsLSeg Γ u.rep := by
  obtain ⟨τ, hd, hc⟩ := GlobalTheory.TL.exists_segment_representation hA Γ
  exact ⟨IrrGL.of τ.ρ τ.smooth τ.irr, rfl, hd, hc.of_equiv (IrrGL.equivOf _ _ _) (Representation.Equiv.refl _)⟩

theorem fine_tensor (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Γ : Segment k) (hF : FineJac Γ) (u : IrrGL k)
    (hu : IsLSeg Γ u.rep) (hs : ∑ i, (dec Γ i).1 = u.1) :
    Nonempty ((jac (stdBlocks (fun i => (dec Γ i).1) hs) u.rep).Equiv (piTensor fun i => (dec Γ i).rep)) := by
  have hJ : HasFiniteLength (jac (stdBlocks (fun i => (dec Γ i).1) hs) u.rep) :=
    GlobalTheory.T.jacquet_module_finite_length k _ _ _ _ _ _ u.2.rep.smooth (hasFiniteLength_of_isIrreducible u.2.rep.irr)
  exact GlobalTheory.T.equiv_of_multiplicity_one_unique_factor _ _ (GlobalTheory.CompanionTheory.FrobJm.piTensor_rep_isIrreducible hA (dec Γ)) hJ ((hF u.rep hu).1 hs)
    fun X _ _ ρ hi hq => GlobalTheory.T.irreducible_subquotient_jacquet_segment hA Γ hF u hu hs X ρ hi hq

theorem shuffle_step (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ : Segment k) {N : ℕ} {V : Type} [AddCommGroup V]
    [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) (hπ : IsLSeg Δ π) (a : ℕ) (h0 : 0 < a) (h1 : a < Δ.len)
    (hlow : FineJac (segLow Δ a h0)) (hhigh : FineJac (segHigh Δ a h1)) {c : ℕ} (y : Fin c → IrrGL k)
    (hy : ∑ i, (y i).1 = N) (hyc : ∀ i, (y i).IsCusp) (h : 1 ≤ jm y hy π) :
    ∃ (f : Fin (segLow Δ a h0).len ↪o Fin c) (g : Fin (segHigh Δ a h1).len ↪o Fin c),
      Disjoint (Set.range f) (Set.range g) ∧ (∀ i, y (f i) = dec (segLow Δ a h0) i) ∧
        ∀ j, y (g j) = dec (segHigh Δ a h1) j := by
  obtain ⟨u, hu1, hu⟩ := exists_class hA (segLow Δ a h0)
  obtain ⟨v, hv1, hv⟩ := exists_class hA (segHigh Δ a h1)
  have hN : N = Δ.len * Δ.d := by
    obtain ⟨hd, -⟩ := hπ
    rw [← hd, Segment.sum_term_fst]
    rfl
  have hd : ∑ i, (![u, v] i).1 = N := by
    have e1 : (segLow Δ a h0).deg = a * Δ.d := rfl
    have e2 : (segHigh Δ a h1).deg = (Δ.len - a) * Δ.d := rfl
    rw [Fin.sum_univ_two]
    show u.1 + v.1 = N
    rw [hu1, hv1, e1, e2, ← Nat.add_mul, Nat.add_sub_cancel' h1.le, hN]
  obtain ⟨φ, hφ⟩ := GlobalTheory.T.segment_rep_split_intertwiner hA Δ π hπ a h0 h1 u v hu hv hd
  have hle := GlobalTheory.T.jacquet_multiplicity_subquotient_le y hy π _ (isSmooth_prodIrr _ hd) (.of_surjective φ hφ)
  have hs : ∑ i, (dec (segLow Δ a h0) i).1 = u.1 := by rw [sum_dec_fst, hu1]
  have ht : ∑ i, (dec (segHigh Δ a h1) i).1 = v.1 := by rw [sum_dec_fst, hv1]
  exact GlobalTheory.TL.derivative_cuspidal_pair_length hA u v _ _ hs ht Δ.d (fun _ => rfl) (fun _ => rfl) (isCusp_dec _) (isCusp_dec _)
    (fine_tensor hA _ hlow u hu hs) (fine_tensor hA _ hhigh v hv ht) hd y hy hyc (h.trans hle)

theorem fineJac_step (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ : Segment k) (h3 : 3 ≤ Δ.len)
    (ih : ∀ Δ' : Segment k, Δ'.len < Δ.len → FineJac Δ') : FineJac Δ := by
  intro N V _ _ π hπ
  obtain ⟨hd0, hc⟩ := id hπ
  have hsub := hc.isSubquotient
  have hsm : IsSmooth π := hsub.isSmooth (isSmooth_prodIrr _ _)
  have hN : N = Δ.len * Δ.d := by
    rw [← hd0, Segment.sum_term_fst]
    rfl
  have shape : ∀ (c : ℕ) (y : Fin c → IrrGL k) (hy : ∑ a, (y a).1 = N), (∀ a, (y a).IsCusp) → 1 ≤ jm y hy π →
      ∃ h : c = Δ.len, ∀ a, y a = dec Δ (Fin.cast h a) := by
    intro c y hy hyc h
    have hl1 : 1 < Δ.len := by omega
    have hl2 : Δ.len - 1 < Δ.len := by omega
    have hl0 : 0 < Δ.len - 1 := by omega
    obtain ⟨f₁, g₁, dis₁, hf₁, hg₁⟩ := shuffle_step hA Δ π hπ 1 one_pos hl1
      (ih _ (show 1 < Δ.len from hl1)) (ih _ (show Δ.len - 1 < Δ.len from hl2)) y hy hyc h
    obtain ⟨f₂, g₂, dis₂, hf₂, hg₂⟩ := shuffle_step hA Δ π hπ (Δ.len - 1) hl0 hl2
      (ih _ (show Δ.len - 1 < Δ.len from hl2)) (ih _ (show Δ.len - (Δ.len - 1) < Δ.len by omega)) y hy hyc h
    have hpos : ∀ a, 0 < (y a).1 := fun a => (hyc a).1
    obtain ⟨cov₁, hc₁⟩ := cover (p := 1) (q := Δ.len - 1) (d := Δ.d) (fun a => (y a).1) hpos
      (by rw [hy, hN, Nat.add_sub_cancel' hl1.le]) f₁ g₁ f₁.injective g₁.injective dis₁
      (fun i => congrArg Sigma.fst (hf₁ i)) (fun i => congrArg Sigma.fst (hg₁ i))
    obtain ⟨cov₂, -⟩ := cover (p := Δ.len - 1) (q := Δ.len - (Δ.len - 1)) (d := Δ.d) (fun a => (y a).1) hpos
      (by rw [hy, hN, Nat.add_sub_cancel' hl2.le]) f₂ g₂ f₂.injective g₂.injective dis₂
      (fun i => congrArg Sigma.fst (hf₂ i)) (fun i => congrArg Sigma.fst (hg₂ i))
    have hcl : c = Δ.len := by omega
    subst hcl
    have e : ∀ {m n : ℕ}, m = n → Δ.first.nu ((m : ℕ) : ℂ) = Δ.first.nu ((n : ℕ) : ℂ) := by
      rintro m _ rfl
      rfl
    have hinj : ∀ a b, a < Δ.len → b < Δ.len →
        Δ.first.nu ((a : ℕ) : ℂ) = Δ.first.nu ((b : ℕ) : ℂ) → a = b := fun a b ha hb hab =>
      congrArg Fin.val (GlobalTheory.T.segment_term_injective hA Δ (a₁ := ⟨a, ha⟩) (a₂ := ⟨b, hb⟩) hab)
    have z₁ : 0 < (segLow Δ 1 one_pos).len := one_pos
    have z₂ : 0 < (segHigh Δ (Δ.len - 1) hl2).len := by
      show 0 < Δ.len - (Δ.len - 1)
      omega
    refine ⟨rfl, fun a => ?_⟩
    refine (word_eq_decreasing Δ.len h3 (fun n => Δ.first.nu ((n : ℕ) : ℂ)) hinj y
      (f₁ ⟨0, z₁⟩) g₁ (fun a => ?_) ?_ (fun j => ?_) (g₂ ⟨0, z₂⟩) f₂ (fun a => ?_) ?_ (fun j => ?_) a).trans ?_
    · rcases cov₁ a with ⟨x, rfl⟩ | h
      · have hx : (x : ℕ) < 1 := x.2
        exact Or.inl (congrArg f₁ (Fin.ext (by show (x : ℕ) = 0; omega)))
      · exact Or.inr h
    · exact (hf₁ _).trans ((dec_segLow _ _ _ _).trans (e (by simp)))
    · have hj := j.2
      exact (hg₁ j).trans ((dec_segHigh _ _ _ _).trans (e (by
        have : ((j : Fin (segHigh Δ 1 hl1).len) : ℕ) = j := rfl
        omega)))
    · rcases cov₂ a with h | ⟨x, rfl⟩
      · exact Or.inr h
      · have hx : (x : ℕ) < Δ.len - (Δ.len - 1) := x.2
        exact Or.inl (congrArg g₂ (Fin.ext (by show (x : ℕ) = 0; omega)))
    · exact (hg₂ _).trans ((dec_segHigh _ _ _ _).trans (e (by simp; omega)))
    · have hj := j.2
      exact (hf₂ j).trans ((dec_segLow _ _ _ _).trans (e (by
        have : ((j : Fin (segLow Δ (Δ.len - 1) hl0).len) : ℕ) = j := rfl
        omega)))
    · have ha := a.2
      have e₂ : ((Fin.rev (Fin.cast rfl a) : Fin Δ.len) : ℕ) = Δ.len - 1 - a := by
        rw [Fin.val_rev]
        simp only [Fin.val_cast]
        omega
      show _ = Δ.first.nu (((Fin.rev (Fin.cast rfl a) : Fin Δ.len) : ℕ) : ℂ)
      rw [e₂]
  refine ⟨fun hd => ?_, shape⟩
  have hinj := GlobalTheory.T.segment_term_injective hA Δ
  have hset : {e : Fin Δ.len ≃ Fin Δ.len | ∀ a, dec Δ a = Δ.term (e a)} = {Fin.revPerm} := by
    ext e
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · intro h
      exact Equiv.ext fun a => (hinj (h a)).symm
    · rintro rfl a
      rfl
  have hup : jm (dec Δ) hd π ≤ 1 := by
    refine (GlobalTheory.T.jacquet_multiplicity_subquotient_le (dec Δ) hd π _ (isSmooth_prodIrr _ hd0) hsub).trans ?_
    rw [GlobalTheory.T.jacquet_multiplicity_cuspidal_product hA Δ.term (dec Δ) hd0 hd Δ.isCusp_term (isCusp_dec Δ), hset, Set.ncard_singleton]
    simp
  obtain ⟨e, he, h1⟩ := GlobalTheory.T.irreducible_subquotient_cuspidal_permutation hA Δ.term hd0 Δ.isCusp_term π hsm hc.1 hsub
  obtain ⟨h, hh⟩ := shape Δ.len _ he (fun a => Δ.isCusp_term _) h1
  have hfun : (fun a => Δ.term (e a)) = dec Δ := funext fun a => hh a
  rw [jm_congr hfun he hd] at h1
  exact le_antisymm hup h1

end GlobalTheory.CompanionTheory.LkSegFine

end
