import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.BlockBoundAlt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAlgebraicFormWeightLevelSmoothAtPlaceStatement

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU

namespace UpperTheory.Gal.Gen

open GlobalTheory.CongW (IntMat wtSize HasTypeVec IsIntegralOpW)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ}

theorem opOf_smul' (c : ℂ) (f : UA E a →₀ ℂ) (φ : UA E a → ℂ) : opOf (RU E a) (c • f) φ = c • opOf (RU E a) f φ := by
  have e : ∀ f : UA E a →₀ ℂ, opOf (RU E a) f φ = Finsupp.linearCombination ℂ (fun g => RU E a g φ) f := fun f =>
    (Finsupp.linearCombination_apply ℂ f).symm
  rw [e, e, map_smul]

theorem core (hT : ToPolyX) (hC : Combine) (hR : Restrict) {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (w₀ : HeightOneSpectrum (𝓞 E)) (K : Subgroup (UA E a)) (hK : K ≤ finU E a) (lam : (E →+* ℂ) → DomWeight a)
    (S : Type) [Fintype S] (Gn : S → Submodule ℂ (UA E a → ℂ) → Prop) (P : Submodule ℂ (UA E a → ℂ) → Prop)
    (hG : Dense ι (Wt.ofFam lam) K fun U => ∀ w, Gn w U) (hP : Dense ι (Wt.ofFam lam) K P)
    (J : Type) (t : J → (UA E a →₀ ℂ)) (η : Submodule ℂ (UA E a → ℂ) → J → ℂ) (hact : ActsBy K t η)
    (f : S → (UA E a →₀ ℂ)) (e : S → Submodule ℂ (UA E a → ℂ) → ℂ)
    (hf : ∀ w U, IsAutRepU U → (∀ φ ∈ U, (∀ x ∈ K, RU E a x φ = φ) → opOf (RU E a) (f w) φ = e w U • φ) ∧
        ((∃ φ ∈ U, φ ≠ 0 ∧ ∀ x ∈ K, RU E a x φ = φ) → (e w U ≠ 0 ↔ Gn w U)))
    (hF : FramedX ι (Wt.ofFam lam) (Sum.elim t f)) (U : Submodule ℂ (UA E a → ℂ)) (hU : OfType lam K U) :
    PolyApprox (fun j => ι.symm (η U j))
      {θ | ∃ U', OfType lam K U' ∧ P U' ∧ (∀ w, Gn w U') ∧ θ = fun j => ι.symm (η U' j)} := by
  classical
  let η' : Submodule ℂ (UA E a → ℂ) → J ⊕ S → ℂ := fun U => Sum.elim (η U) fun w => e w U
  have hact' : ActsBy K (Sum.elim t f) η' := by
    intro U hU φ hφ hfix j
    cases j with
    | inl j => exact hact U hU φ hφ hfix j
    | inr w => exact (hf w U hU).1 φ hφ hfix
  let Q : MvPolynomial (J ⊕ S) ℤ := ∏ w : S, MvPolynomial.X (Sum.inr w)
  have hQ : ∀ U', OfType lam K U' → (MvPolynomial.aeval (fun j => ι.symm (η' U' j)) Q ≠ 0 ↔ ∀ w, Gn w U') := by
    intro U' hU'
    simp only [Q, map_prod, MvPolynomial.aeval_X, Finset.prod_ne_zero_iff, Finset.mem_univ, true_imp_iff]
    refine forall_congr' fun w => ?_
    rw [← (hf w U' hU'.aut).2 hU'.fix]
    exact map_ne_zero_iff _ ι.symm.injective
  have h1 := hT E l ι a w₀ K hK lam _ hG _ _ η' hF hact' U hU
  have h2 := hC (Qbar l) _ _ _ {θ | ∃ U', OfType lam K U' ∧ P U' ∧ θ = fun j => ι.symm (η' U' j)} Q h1 (by
    rintro _ ⟨U', hU', hg, rfl⟩
    exact ⟨(hQ U' hU').2 hg, hT E l ι a w₀ K hK lam _ hP _ _ η' hF hact' U' hU'⟩)
  refine (hR (Qbar l) J _ Sum.inl _ _ h2).mono ?_
  rintro _ ⟨_, ⟨⟨U', hU', hp, rfl⟩, hq⟩, rfl⟩
  exact ⟨U', hU', hp, (hQ U' hU').1 hq, rfl⟩

theorem genW_of (hT : ToPolyX) (hC : Combine) (hR : Restrict) (hD : DenseGen) (hO : TestOp) (hS : ScaleW) (hF : FrameW) :
    GenW := by
  intro E _ _ _ l _ ι a ha w₀ hl hs K hK lam S Φ hd P hP J t η ht hact U hU
  obtain ⟨W, -, hW, -⟩ := GlobalTheory.T.exists_algebraicForm_weight_level_smooth_at_place E a lam K U hK.fin hU w₀
  have hlam : (Wt.ofFam lam).at = lam := by
    obtain rfl : lam = W.at := (funext hW).symm
    have : Wt.ofFam W.at = W := funext fun v => W.at_embedding v
    rw [this]
  choose f e hfin hf using fun w : S => hO E a K w.1 (hd.split w.1 w.2) (hd.hyp w.1 w.2) (Φ w.1)
  choose c hc0 hc using fun w : S => hS E l ι a lam (f w) (hfin w)
  have hG : Dense ι (Wt.ofFam lam) K fun U => ∀ w : S, GenAt w.1 (Φ w.1) U := by
    have := hD E l ι a ha w₀ hl hs K hK (Wt.ofFam lam) S Φ hd
    simpa only [Subtype.forall] using this
  have := core hT hC hR ι w₀ K hK.fin lam S (fun w U => GenAt w.1 (Φ w.1) U) P hG hP J t η hact (fun w => c w • f w)
    (fun w U => c w * e w U) (fun w U hU => ⟨fun φ hφ hx => by rw [opOf_smul', (hf w U hU).1 φ hφ hx, smul_smul], fun h => by
      rw [← (hf w U hU).2 h]; simp [hc0 w]⟩)
    (hF E l ι a _ _ _ fun j => by
      rw [hlam]
      cases j with
      | inl j => exact ht j
      | inr w => exact hc w) U hU
  simpa only [Subtype.forall] using this

theorem genP_of (hT : ToPolyX) (hC : Combine) (hR : Restrict) (hD : DenseGen) (hO : TestOp) (hF : FrameOps) : GenP := by
  intro E _ _ _ l _ ι a ha w₀ hl hs K hK lam S Φ hd P hP J t η ht hact
  choose f e hfin hf using fun w : S => hO E a K w.1 (hd.split w.1 w.2) (hd.hyp w.1 w.2) (Φ w.1)
  obtain ⟨c, hc, hfr⟩ := hF E l ι a (Wt.ofFam lam) (J ⊕ S) (Sum.elim t f) fun j => by
    cases j with
    | inl j => exact ht j
    | inr w => exact hfin w
  refine ⟨fun j => c (Sum.inl j), fun j h => hc (Sum.inl j) h, fun U hU => ?_⟩
  have hl0 : (l : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have hG : Dense ι (Wt.ofFam lam) K fun U => ∀ w : S, GenAt w.1 (Φ w.1) U := by
    have := hD E l ι a ha w₀ hl hs K hK (Wt.ofFam lam) S Φ hd
    simpa only [Subtype.forall] using this
  have := core hT hC hR ι w₀ K hK.fin lam S (fun w U => GenAt w.1 (Φ w.1) U) P hG hP J
    (fun j => (l : ℂ) ^ c (Sum.inl j) • t j) (fun U j => (l : ℂ) ^ c (Sum.inl j) * η U j)
    (fun U hU φ hφ hx j => by rw [opOf_smul', hact U hU φ hφ hx j, smul_smul])
    (fun w => (l : ℂ) ^ c (Sum.inr w) • f w)
    (fun w U => (l : ℂ) ^ c (Sum.inr w) * e w U)
    (fun w U hU => ⟨fun φ hφ hx => by rw [opOf_smul', (hf w U hU).1 φ hφ hx, smul_smul], fun h => by
      rw [← (hf w U hU).2 h]; simp [hl0]⟩)
    (by
      convert hfr.framedX using 2 with j
      cases j <;> rfl) U hU
  simpa only [Subtype.forall, map_mul, map_pow, map_natCast] using this

theorem part_mono (W : Wt E a) (C : Subgroup (UA E a)) {P Q : Submodule ℂ (UA E a → ℂ) → Prop} (h : ∀ U, P U → Q U) :
    part W C P ≤ part W C Q :=
  iSup₂_le fun π hπ => le_iSup₂_of_le (f := fun (π : AutSub E a) (_ : Q π.V) => π.finPart W ⊓ fixedBy W C) π (h _ hπ) le_rfl

theorem genTyL_of (hW : GenW) (hH : HypOf) (hSm : SmoothAt) (hL : LevFacts) (hTy : TyStep) : GlobalTheory.CongW.GenTyL := by
  intro E _ _ _ l _ ι a ha w₀ hl hs K hK lam Jx t η ht hact Fam hFam hcof S hS D _ hD0 U hU
  have hd : GenData w₀ K S fun _ => MvPolynomial.map (Int.castRingHom ℂ) D :=
    ⟨fun w hw => (hS w hw).1, fun w hw => (hS w hw).2.1, fun w hw => hH E a K hK.compact w (hS w hw).1 (hS w hw).2.2,
      fun _ _ h => hD0 (MvPolynomial.map_injective _ Int.cast_injective (h.trans (map_zero _).symm))⟩
  have hl1 : ‖((l : ℕ) : Qbar l)‖ < 1 := by
    have h := PadicAlgCl.norm_extends l (l : ℚ_[l])
    rw [map_natCast] at h
    rw [h, Padic.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)
  refine (hW E l ι a ha w₀ hl hs K hK lam S _ hd (fun U' => ∃ (J : Subgroup (GL (Fin a) (w₀.adicCompletion E))) (m : ℕ)
    (θ : J →* Multiplicative (ZMod (l ^ m))), Fam J m θ ∧ ∃ χ : Multiplicative (ZMod (l ^ m)) →* ℂˣ, χ ≠ 1 ∧
      HasTypeVec w₀ K J θ χ U') ?_ Jx t η (fun j => intW_of (ht j)) hact U hU).mono ?_
  · intro f hf ε hε
    obtain ⟨N, hN, hfN⟩ := hSm E a w₀ hs _ f
    obtain ⟨m₀, hm₀⟩ := exists_pow_lt_of_lt_one hε hl1
    obtain ⟨J, m, θ, hm, hJN, hF⟩ := hcof (interior N) isOpen_interior (mem_interior_iff_mem_nhds.2 hN) m₀
    obtain ⟨hJo, hJc, hJt, -⟩ := hFam J m θ hF
    have hfJ : f ∈ fixedBy (Wt.ofFam lam) (lev K w₀ J) := by
      intro c hc v g
      obtain ⟨k, hk, x, hx, hxJ, rfl⟩ := ((hL E a w₀ hs K hK J hJo hJc).2.1 c).1 hc
      rw [← mul_assoc, hfN x hx (interior_subset (hJN hxJ)), hf k hk]
    obtain ⟨G, hG, e, he, hGe⟩ := hTy E l ι a w₀ hs K hK _ J hJo hJc hJt m θ f hfJ
    exact ⟨G, part_mono _ _ (fun U h => ⟨J, m, θ, hF, h⟩) hG, e, fun g => (he g).trans
      ((pow_le_pow_of_le_one (norm_nonneg _) hl1.le hm).trans hm₀.le), hGe⟩
  · rintro _ ⟨U', h1, h2, h3, rfl⟩
    refine ⟨U', h1, h2, fun w hw σ hσ B hB α hα => ?_, rfl⟩
    have := h3 w hw α ⟨σ, hσ, hα ▸ hB⟩
    rw [MvPolynomial.eval_map] at this
    rw [MvPolynomial.aeval_def]
    exact this

end UpperTheory.Gal.Gen

end
