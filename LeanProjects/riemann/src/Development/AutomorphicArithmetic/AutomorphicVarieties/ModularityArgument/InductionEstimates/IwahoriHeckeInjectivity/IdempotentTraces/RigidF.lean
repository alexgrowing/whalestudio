import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriHeckeInjectivity.HeckeInj
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriHeckeInjectivity.IdempotentTraces.SwapAt
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.FamSat
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.FamParts
import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.NormCharPowHolds
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.AtInj
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.ExCusp
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.SSatIff
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.JacquetShalikaRigidity

open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open GlobalTheory.CuspRep UpperTheory.V.Published
open scoped ComplexConjugate Classical

open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E

private theorem normV_split {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
    (w : HeightOneSpectrum (𝓞 M)) (h : GM.Split M (w.under (𝓞 K))) :
    Formalism.ConjugateSelfDual.normV w = Formalism.ConjugateSelfDual.normV (w.under (𝓞 K)) := by
  haveI hl : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 K)).isMaximal
  have hs : Function.Surjective (completionMap (w.under (𝓞 K)) w) := h ⟨w, hl⟩
  have hb : Function.Bijective (Algebra.linearMap ((w.under (𝓞 K)).adicCompletion K) (w.adicCompletion M)) :=
    ⟨(completionMap (w.under (𝓞 K)) w).injective, hs⟩
  have h1 : w.asIdeal.ramificationIdx (𝓞 K) * w.asIdeal.inertiaDeg (𝓞 K) = 1 := by
    rw [← finrank_eq_ramificationIdx_mul_inertiaDeg M (w.under (𝓞 K)) w,
      ← (LinearEquiv.ofBijective _ hb).finrank_eq, Module.finrank_self]
  show Ideal.absNorm w.asIdeal = Ideal.absNorm (w.under (𝓞 K)).asIdeal
  rw [← Ideal.absNorm_relNorm (𝓞 K) (𝓞 M) w.asIdeal,
    Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal (w.under (𝓞 K)).asIdeal, Nat.eq_one_of_mul_eq_one_left h1, pow_one]

private theorem summand_of_irr {K : Type} [Field K] [NumberField K] {n : ℕ} {μ : Measure (G1 K n)} [μ.IsHaarMeasure]
    {τ : Submodule ℂ (L2 μ)} (h : CuspIrr μ τ) : IsSummand μ τ :=
  ⟨h.le, h.closed, h.inv, h.ne, h.irr⟩

private theorem sat_single {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {ι : Type} {κ : ι → Type}
    [∀ i, Fintype (κ i)] {m : (Σ i, κ i) → ℕ} (Q : ∀ a, CG E (m a))
    (hinj : Function.Injective (Sigma.fst : (Σ i, κ i) → ι)) (a : Σ i, κ i) {w : HeightOneSpectrum (𝓞 E)}
    {C : Multiset ℂˣ} (h : R.sumSat (m := fun k : κ a.1 => m ⟨a.1, k⟩) (fun k => Q ⟨a.1, k⟩) w C) : (Q a).HasSat w C := by
  obtain ⟨i, k₀⟩ := a
  obtain ⟨D, hD, rfl⟩ := h
  have hu : ∀ k : κ i, k = k₀ := fun k => by
    have : (⟨i, k⟩ : Σ i, κ i) = ⟨i, k₀⟩ := hinj rfl
    simpa using this
  rw [Fintype.sum_eq_single k₀ fun k hk => absurd (hu k) hk]
  exact hD k₀

private theorem sat_of_sigma {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {n n' : ℕ} {p : CG E n} {q : CG E n'}
    (h : (⟨n, p⟩ : Σ a, CG E a) = ⟨n', q⟩) {w : HeightOneSpectrum (𝓞 E)} {B : Multiset ℂˣ} (hq : q.HasSat w B) :
    p.HasSat w B := by
  cases h
  exact hq

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.rigidF :
    T.LiftAll → RigidF := by
  intro hL F E _ _ _ _ _ _ _ _ σ h2 hgen τ₁ τ₂ θ₂ hP hgal h12 h21 SE SF hSE hSF m₁ m₂ B₁ B₂ hA₁ hA₂ b Λ' t' hb hbc
  have hp : (Module.finrank F E).Prime := h2 ▸ Nat.prime_two
  obtain ⟨-, hsw⟩ := swapAt F E σ h2 hgen τ₁ τ₂ θ₂ hP hgal h12 h21
  have s₁ := summand_of_irr hP.irr₁
  have s₂ := summand_of_irr hP.irr₂
  obtain ⟨π₁, c₁, -⟩ := Dp.exCusp E 2 (BW.mu1 E 2) τ₁ s₁
  obtain ⟨π₂, c₂, -⟩ := Dp.exCusp E 2 (BW.mu1 E 2) τ₂ s₂
  obtain ⟨P, hPt⟩ := T.famSat F (2 + 2) b SF hSF Λ' t' hb
  choose κ fκ m Q hm hne hQ using fun i => hL F E σ hgen hp (b.d i) (b.pos i) (P i)
  have hsum := R.liftSum F E hp (Fin b.r) κ b.d (fun a => m a.1 a.2) P (fun a => Q a.1 a.2) hQ
  have hN := (T.places F E hp).2.2.2.2.1
  have hund := GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.tendsto_under F E
  have hev : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in cofinite, ∃ (B : Fin 2 → Multiset ℂˣ) (B' : (Σ i, κ i) → Multiset ℂˣ),
      (∀ i, ((![CG.mk π₁, CG.mk π₂] : Fin 2 → CG E 2) i).HasSat w (B i)) ∧ (∀ a, (Q a.1 a.2).HasSat w (B' a)) ∧
        ∑ i, B i = ∑ a, B' a := by
    filter_upwards [hsum, hSE.eventually_cofinite_notMem, hund.eventually hSF.eventually_cofinite_notMem] with w hw hwE hwF
    obtain ⟨B, ⟨B1, hB1, e1⟩, D, hD, eD⟩ := hw (UpperTheory.ConvolutionTheory.resDeg F w) (hN w)
    obtain ⟨C, ⟨C1, hC1, e2⟩, e⟩ := hPt _ hwF
    obtain ⟨A₁, a₁, h₁⟩ := (Dp.sSatIff E 2 _ π₁ τ₁ c₁ w _).1 (hA₁.2 w hwE)
    obtain ⟨A₂, a₂, h₂⟩ := (Dp.sSatIff E 2 _ π₂ τ₂ c₂ w _).1 (hA₂.2 w hwE)
    have e3 : B = C := by
      rw [e1, e2]
      exact Finset.sum_congr rfl fun i _ => (hB1 i).unique (hC1 i)
    refine ⟨![A₁, A₂], D, fun i => ?_, hD, ?_⟩
    · fin_cases i
      exacts [h₁, h₂]
    · have hb := hbc w hwE
      rw [bcSat, e, a₁, a₂, Multiset.map_map] at hb
      refine Multiset.map_injective (f := fun z : ℂˣ => (z : ℂ)) (fun a b e => Units.ext e) ?_
      rw [← eD, e3, Fin.sum_univ_two, Multiset.map_map]
      simpa using hb
  obtain ⟨s, hs⟩ := PositivityTheory.AdelicQuotientData.jacquetShalikaRigidity E (Fin 2) (Σ i, κ i) (fun _ => 2) (fun a => m a.1 a.2)
    ![CG.mk π₁, CG.mk π₂] (fun a => Q a.1 a.2) (fun _ => by norm_num) (fun a => hm a.1 a.2) hev
  have hcard : Fintype.card (Σ i, κ i) = 2 := by simpa using (Fintype.card_congr s).symm
  have hsurj : Function.Surjective (Sigma.fst : (Σ i, κ i) → Fin b.r) := fun i => ⟨⟨i, (hne i).some⟩, rfl⟩
  have hinj : Function.Injective (Sigma.fst : (Σ i, κ i) → Fin b.r) := by
    refine ((Fintype.bijective_iff_surjective_and_card _).2 ⟨hsurj, ?_⟩).1
    have h1 := Fintype.card_le_of_surjective _ hsurj
    have h3 := b.two
    simp only [Fintype.card_fin] at h1 ⊢
    omega
  have hl0 : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in cofinite, ∀ f : ℕ,
      Formalism.ConjugateSelfDual.normV w = Formalism.ConjugateSelfDual.normV (w.under (𝓞 F)) ^ f →
        ∃ B, (P (s 0).1).HasSat (w.under (𝓞 F)) B ∧ (CG.mk π₁).HasSat w (B.map (· ^ f)) :=
    (hQ (s 0).1).mono fun w hw f hf => by
      obtain ⟨B, hB, hC⟩ := hw f hf
      exact ⟨B, hB, sat_of_sigma (hs 0) (sat_single (fun a => Q a.1 a.2) hinj (s 0) hC)⟩
  obtain ⟨X, hX, hlift⟩ : ∃ X : Set (HeightOneSpectrum (𝓞 E)), X.Finite ∧ ∀ w ∉ X, ∀ f : ℕ,
      Formalism.ConjugateSelfDual.normV w = Formalism.ConjugateSelfDual.normV (w.under (𝓞 F)) ^ f →
        ∃ B, (P (s 0).1).HasSat (w.under (𝓞 F)) B ∧ (CG.mk π₁).HasSat w (B.map (· ^ f)) :=
    ⟨_, Filter.eventually_cofinite.1 hl0, fun w hw => not_not.1 hw⟩
  have hev2 : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in cofinite, w ∉ SE ∧ SSat (BW.mu1 E 2) τ₁ w (B₂ w) := by
    filter_upwards [hund.eventually (R.decomp F E hp), hund.eventually (hX.image fun w => w.under (𝓞 F)).eventually_cofinite_notMem,
      hSE.eventually_cofinite_notMem] with w hd hy hwE
    refine ⟨hwE, ?_⟩
    have hg : ∀ w' : HeightOneSpectrum (𝓞 E), w'.under (𝓞 F) = w.under (𝓞 F) → w' ∉ X :=
      fun w' hu hc => hy ⟨w', hc, hu⟩
    have hq : 1 < Formalism.ConjugateSelfDual.normV (w.under (𝓞 F)) := NumberField.HeightOneSpectrum.one_lt_absNorm _
    rcases hd with ⟨hc, hn⟩ | ⟨-, hn⟩
    · obtain ⟨⟨w', hu⟩, hne', -⟩ := (Nat.card_eq_two_iff' (⟨w, rfl⟩ : {u : HeightOneSpectrum (𝓞 E) // u.under (𝓞 F) = w.under (𝓞 F)})).1
        (hc.trans h2)
      have hne : w ≠ w' := fun e => hne' (Subtype.ext e.symm)
      obtain ⟨B, hB, hw1⟩ := hlift w (hg w rfl) 1 (by rw [pow_one]; exact hn w rfl)
      obtain ⟨B', hB', hw2⟩ := hlift w' (hg w' hu) 1 (by rw [pow_one, hu]; exact hn w' hu)
      rw [hu] at hB'
      obtain rfl := hB.unique hB'
      obtain ⟨Y, eY, hY⟩ := (Dp.sSatIff E 2 _ π₁ τ₁ c₁ w' _).1 ((hsw w w' hu.symm (Or.inl hne) _).1 (hA₂.2 w hwE))
      have hY' : (CG.mk π₁).HasSat w' Y := hY
      obtain rfl : Y = B.map (· ^ 1) := hY'.unique hw2
      exact (Dp.sSatIff E 2 _ π₁ τ₁ c₁ w _).2 ⟨_, eY, hw1⟩
    · have hns : ¬ GM.Split E (w.under (𝓞 F)) := fun h => by
        have e := (hn w rfl).symm.trans (normV_split w h)
        rw [h2] at e
        have : (2 : ℕ) = 1 := Nat.pow_right_injective hq (e.trans (pow_one _).symm)
        omega
      exact (hsw w w rfl (Or.inr hns) _).1 (hA₂.2 w hwE)
  have hτ : τ₁ = τ₂ := Dp.atInj E 2 _ τ₁ τ₂ s₁ s₂ _ (Filter.eventually_cofinite.1 hev2) B₂
    (fun w hw => (not_not.1 hw).2) (fun w hw => hA₂.2 w (not_not.1 hw).1)
  have ho := hP.orth
  rw [← hτ] at ho
  exact hP.irr₁.ne (Submodule.isOrtho_self.1 ho)
