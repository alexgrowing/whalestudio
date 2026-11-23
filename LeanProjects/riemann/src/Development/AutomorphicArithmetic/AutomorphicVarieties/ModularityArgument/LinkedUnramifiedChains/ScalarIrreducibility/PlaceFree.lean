import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.RedDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.WtUnit
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LaArtin
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LaCyc
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IneInclOntoUnits

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr UpperTheory.V.Alg UpperTheory.V.J

section SlopeTestRemainingChoices

open IsDedekindDomain GlobalTheory.LocLanglands GlobalTheory.WeilDeligne UpperTheory.V.W

private theorem free_of {K : Type} [Field K] (α β : Fin 3 → Kˣ) (T : Kˣ) (hT : ∀ m : ℕ, 0 < m → T ^ m ≠ 1)
    (hβ : ∀ i, ∃ N : ℕ, 0 < N ∧ β i ^ N = 1) (heq : ∀ i : Fin 3, α i * β i = T ^ (-((i : ℕ) : ℤ))) :
    Pr.FreeRatios α := by
  intro i j hij m hm hαm
  obtain ⟨Ni, hNi, hbi⟩ := hβ i
  obtain ⟨Nj, hNj, hbj⟩ := hβ j
  have key : ∀ k : Fin 3, ∀ n : ℕ, β k ^ n = 1 → α k ^ n = T ^ (-((k : ℕ) : ℤ) * (n : ℤ)) := by
    intro k n hn
    have hk : α k = T ^ (-((k : ℕ) : ℤ)) * (β k)⁻¹ := eq_mul_inv_of_mul_eq (heq k)
    rw [hk, mul_pow, inv_pow, hn, inv_one, mul_one, ← zpow_natCast, ← zpow_mul]
  have hM : α i ^ (m * (Ni * Nj)) = α j ^ (m * (Ni * Nj)) := by
    rw [pow_mul (α i), pow_mul (α j), hαm]
  rw [key i _ (by rw [show m * (Ni * Nj) = Ni * (m * Nj) by ring, pow_mul, hbi, one_pow]),
    key j _ (by rw [show m * (Ni * Nj) = Nj * (m * Ni) by ring, pow_mul, hbj, one_pow])] at hM
  have hfin : IsOfFinOrder T := by
    rw [isOfFinOrder_iff_zpow_eq_one]
    refine ⟨-((i : ℕ) : ℤ) * ((m * (Ni * Nj) : ℕ) : ℤ) - -((j : ℕ) : ℤ) * ((m * (Ni * Nj) : ℕ) : ℤ), ?_, ?_⟩
    · intro h0
      apply hij
      have hMpos : (0 : ℤ) < ((m * (Ni * Nj) : ℕ) : ℤ) := by positivity
      have hz : (((j : ℕ) : ℤ) - ((i : ℕ) : ℤ)) * ((m * (Ni * Nj) : ℕ) : ℤ) = 0 := by linarith
      rcases mul_eq_zero.1 hz with h | h
      · exact Fin.ext (by omega)
      · omega
    · rw [zpow_sub, hM, mul_inv_cancel]
  obtain ⟨n, hn, hTn⟩ := isOfFinOrder_iff_pow_eq_one.1 hfin
  exact hT n hn hTn

private theorem prod_wt {l : ℕ} [Fact l.Prime] {F : Type} [Field F] [NumberField F] {w : Plc F} (τ₀ : Emb l w)
    (y : (w.adicCompletion F)ˣ) (hP : ∏ᶠ τ : Emb l w, τ.1 (y : w.adicCompletion F) = 1) (hh : Emb l w → ℤ) (j : ℤ)
    (h0 : hh τ₀ = 2 * j) (h1 : ∀ τ, τ ≠ τ₀ → hh τ = j) :
    ∏ᶠ τ : Emb l w, τ.1 (y : w.adicCompletion F) ^ (-hh τ) = τ₀.1 (y : w.adicCompletion F) ^ (-j) := by
  classical
  haveI := GlobalTheory.HeckeGal.finite_contEmb (l := l) w
  letI := Fintype.ofFinite (Emb l w)
  have hy : ∀ τ : Emb l w, τ.1 (y : w.adicCompletion F) ≠ 0 := fun τ =>
    (map_ne_zero τ.1).2 y.ne_zero
  have e : ∀ τ : Emb l w, τ.1 (y : w.adicCompletion F) ^ (-hh τ) = τ.1 (y : w.adicCompletion F) ^ (-j) *
      (if τ = τ₀ then τ₀.1 (y : w.adicCompletion F) ^ (-j) else 1) := fun τ => by
    by_cases hτ : τ = τ₀
    · subst hτ
      rw [if_pos rfl, h0, ← zpow_add₀ (hy τ)]
      congr 1
      ring
    · rw [if_neg hτ, h1 τ hτ, mul_one]
  rw [finprod_eq_prod_of_fintype] at hP ⊢
  simp only [e]
  rw [Finset.prod_mul_distrib, Finset.prod_zpow, hP, one_zpow, one_mul, Finset.prod_ite_eq', if_pos (Finset.mem_univ _)]

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField in
private theorem art_elt (hG : GlobalTheory.Published.GlobalArtinReciprocity) {L Ω : Type} [Field L] [NumberField L] [Field Ω]
    [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω} {w : Plc L}
    (h : IsPlaceOver A w) (hl : ((l : ℕ) : 𝓞 L) ∈ w.asIdeal) (y : (w.adicCompletion L)ˣ)
    (hv : Valued.v (y : w.adicCompletion L) = 1) (hP : ∏ᶠ τ : Emb l w, τ.1 (y : w.adicCompletion L) = 1) :
    ∃ (σ : Ine (F := L) A) (a : Weil h →* (w.adicCompletion L)ˣ), IsLocalArtin h a ∧ a (ineIncl h σ) = y ∧
      cycBar L Ω l (σ : G L Ω) = 1 := by
  obtain ⟨a, ha⟩ := UpperTheory.V.Loc.laArtin hG h
  have hv' : ValuativeRel.valuation (w.adicCompletion L) (y : w.adicCompletion L) = 1 := by
    haveI : (Valued.v : Valuation (w.adicCompletion L) _).Compatible := .ofValuation _
    exact (ValuativeRel.isEquiv (ValuativeRel.valuation (w.adicCompletion L)) Valued.v).eq_one_iff_eq_one.2 hv
  obtain ⟨σ, hσ⟩ := (GlobalTheory.PsType.ineIncl_onto_units L Ω A w h a ha).1 y hv'
  refine ⟨σ, a, ha, hσ, ?_⟩
  have hc := (UpperTheory.V.Loc.laCyc hG h hl).2 a ha σ
  simp only [hσ, neg_neg, zpow_one, hP, MonoidHom.one_apply, mul_one] at hc
  ext
  exact hc

private theorem place_free (hG : GlobalTheory.Published.GlobalArtinReciprocity) {L Ω : Type} [Field L] [NumberField L] [Field Ω]
    [CharZero Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω} {w : Plc L}
    (h : IsPlaceOver A w) (hl : ((l : ℕ) : 𝓞 L) ∈ w.asIdeal) (τ₀ : Emb l w) (b : 𝓞 L) (τ₁ τ₂ : Emb l w)
    (hne : τ₁.1 (algebraMap L (w.adicCompletion L) (b : L)) ≠ τ₂.1 (algebraMap L (w.adicCompletion L) (b : L)))
    (ψ : Fin 3 → Dec (F := L) A →* (Qbar l)ˣ) (ph : Fin 3 → Ine (F := L) A →* (Qbar l)ˣ) (hh : Fin 3 → Emb l w → ℤ)
    (h0 : ∀ j : Fin 3, hh j τ₀ = 2 * ((j : ℕ) : ℤ)) (h1 : ∀ (j : Fin 3) (τ : Emb l w), τ ≠ τ₀ → hh j τ = ((j : ℕ) : ℤ))
    (hp : ∀ j, IsWtPart h (ψ j) (hh j) (ph j)) :
    ∃ g : Dec (F := L) A, cycBar L Ω l (g : G L Ω) = 1 ∧ Pr.FreeRatios fun i => ψ i g := by
  obtain ⟨y, hyv, hyP, hyT⟩ := UpperTheory.V.J.Wu.exists_unit hl b τ₁ τ₂ hne
  obtain ⟨σ, a, ha, hσ, hcyc⟩ := art_elt hG h hl y hyv hyP
  refine ⟨Subgroup.inclusion (GlobalTheory.WeilDeligne.Weil_le_Dec h) (GlobalTheory.WeilDeligne.ineIncl h σ), hcyc, ?_⟩
  have hz : τ₀.1 (y : w.adicCompletion L) ≠ 0 := (map_ne_zero τ₀.1).2 y.ne_zero
  haveI : CompactSpace (Ine (F := L) A) :=
    isCompact_iff_compactSpace.1 (ReciprocityTheory.Gal.isClosed_Ine A).isCompact
  apply free_of (fun i => ψ i (Subgroup.inclusion (GlobalTheory.WeilDeligne.Weil_le_Dec h) (GlobalTheory.WeilDeligne.ineIncl h σ)))
    (fun i => ph i σ) (Units.mk0 _ hz)
  · intro m hm h1
    apply hyT τ₀ m hm
    have h2 := congrArg Units.val h1
    simpa using h2
  · intro i
    haveI := Subgroup.quotient_finite_of_isOpen _ (hp i).1
    refine ⟨(ph i).ker.index, Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite, ?_⟩
    rw [← map_pow]
    exact (ph i).mem_ker.1 (Subgroup.pow_index_mem _ σ)
  · intro i
    ext
    have hw := (hp i).2 a ha σ
    rw [hσ, prod_wt τ₀ y hyP (hh i) ((i : ℕ) : ℤ) (h0 i) (h1 i)] at hw
    simpa using hw

private theorem mem_G' {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] {s : HidaSetting l L Ω} (V : s.Lev) (v : Vl l L) (g : Dec (F := L) (s.A v))
    (hc : cycBar L Ω l (g : G L Ω) = 1) : V.frame.φ v g ∈ V.frame.G' := by
  rw [UpperTheory.V.W.GFrame.G', MonoidHom.mem_ker]
  change V.ε ((toGS Ω V.S') (resP L Ω (g : G L Ω))) = 1
  have h1 : V.ε ((toGS Ω V.S') (resP L Ω (g : G L Ω))) = cycZ L Ω l (g : G L Ω) := by
    rw [← MonoidHom.comp_apply, V.hε]
    rfl
  rw [h1]
  have hv := congrArg Units.val hc
  simp only [GlobalTheory.GalOfCusp.cycBar, MonoidHom.comp_apply, Units.coe_map, Units.val_one] at hv
  have hinj : Function.Injective ((algebraMap ℚ_[l] (Qbar l)).comp PadicInt.Coe.ringHom) :=
    (algebraMap ℚ_[l] (Qbar l)).injective.comp Subtype.val_injective
  ext
  apply hinj
  rw [Units.val_one, map_one]
  exact hv

end SlopeTestRemainingChoices

theorem UpperTheory.V.J.wtEx :
    GlobalTheory.Published.GlobalArtinReciprocity → WtEx := by
  intro hG Ω _ _ _ l _ ι c _ N _ e ψ η σ g₁ B M hlink L _ _ _ _ _ Φ k c₁ _ f ka R hlarge hka
  classical
  refine ⟨fun v j τ => if τ = Classical.choice ⟨τ⟩ then 2 * ((j : ℕ) : ℤ) else ((j : ℕ) : ℤ), ?_, ?_⟩
  · intro v τ a b hab
    have hab' : (a : ℕ) < b := hab
    dsimp only
    split_ifs <;> omega
  · intro x hx v
    change UpperTheory.V.W.Vl l L at v
    obtain ⟨ph, hp, -⟩ := hx.2 v
    haveI := k.ab
    have hlw : ((l : ℕ) : 𝓞 L) ∈ (R.s.w v.1).asIdeal := by
      apply (R.s.hw v.1 _).1
      have hA := (R.s.hA v.1 _).2 v.2
      simpa using hA
    have hbig : 5 < Φ.dv (R.K.e v) := R.big.2 (R.K.e v)
    rw [k.dv (R.K.e v)] at hbig
    obtain ⟨g, hgD, hgU⟩ : ∃ g ∈ Dec (F := ℚ) (k.pl (R.K.e v)), g ∉ upl Ω L := by
      by_contra hcon
      push_neg at hcon
      have h1 := Subgroup.relIndex_eq_one.2 hcon
      omega
    have hgD' : g ∈ Dec (F := ℚ) (R.s.A v.1) := by
      rw [R.A_pl v]
      exact hgD
    obtain ⟨y, -, hgy⟩ : ∃ y ∈ maximalRealSubfield L, g (algebraMap L Ω y) ≠ algebraMap L Ω y := by
      by_contra hcon
      push_neg at hcon
      exact hgU hcon
    obtain ⟨b, τ₁, τ₂, hne⟩ := UpperTheory.V.J.Wu.exists_sep (R.s.hw v.1) hlw g hgD' y hgy
    obtain ⟨g', hc, hfree⟩ := place_free hG (R.s.hw v.1) hlw (Classical.choice ⟨τ₁⟩) b τ₁ τ₂ hne (x.psi v) ph
      (fun j τ => if τ = Classical.choice ⟨τ⟩ then 2 * ((j : ℕ) : ℤ) else ((j : ℕ) : ℤ))
      (fun j => if_pos rfl) (fun j τ hτ => if_neg hτ) hp
    exact ⟨g', mem_G' R.V v g' hc, hfree⟩
