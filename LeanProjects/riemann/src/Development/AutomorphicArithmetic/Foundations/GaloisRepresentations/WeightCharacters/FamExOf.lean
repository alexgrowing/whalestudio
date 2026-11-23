import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.DeltaNear
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt

private theorem cEmb_fin {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (τ : E →+* ℂ) {c : UA E n}
    (hc : c ∈ finU E n) : cEmb τ c = 1 := by
  have : cInf c = 1 := hc
  simp [cEmb, this]

theorem UpperTheory.Gal.Wt.famEx_of : NeatLev → EllC → Twist → TwistBd → Kap0 → Pieces → DeltaNear → FamOf → FamEx := by
  intro hN hE hT hTB hK hP hD hF E _ _ _ l _ ι a ha w₀ hl hs v' hs' hap K hKl hKv Kv hKo W f hf τ hτ X b hb ε hε
  classical
  obtain ⟨C, hC, hKC, hneat, hint, hfC⟩ := hN E l Fact.out a ha w₀ hl hs v' hs' hap K hKl hKv Kv hKo W f hf
  obtain ⟨ℓ, hℓ⟩ := hE E a C hC.fin hneat
  obtain ⟨R, hR0, hR⟩ := hTB E l ι a C hC ℓ hℓ W f X b hb
  obtain ⟨κ, hκr, hκi, hκ1, hκc, hκI⟩ := hK E l ι a v' τ hτ
  haveI : CompactSpace C := isCompact_iff_compactSpace.1 hC.compact
  let φ : C →* GL (Fin a) ℂ := κ.comp C.subtype
  have hφI : ∀ c : C, IntGL ι (φ c) := fun c => hκI _ (hint _ c.2)
  obtain ⟨Q, _, c, P, hQ⟩ := hP l ι a C φ (fun i j => (hκc i j).comp continuous_subtype_val) hφI
    ((Kv.comap (cLoc v')).subgroupOf C)
    (hKo.preimage ((GlobalTheory.BCT.GlobLev.continuous_cLoc v').comp continuous_subtype_val))
    (fun x hx => by
      have h1 : cLoc v' x.1 = 1 := (hκ1 _).1 hx
      change cLoc v' x.1 ∈ Kv
      rw [h1]; exact Kv.one_mem) (ε / R) (div_pos hε hR0)
  choose F hFC hFv using fun q => hT E a C hC ℓ hℓ W f (c q)
  let M : UA E a → GL (Fin a) ℂ := fun g => (cEmb τ g)⁻¹ * κ g
  let n : UA E a → GL (Fin a) ℂ := fun g => φ (ℓ g) * (M g)⁻¹
  have hn : IsNrm τ C n := by
    refine ⟨fun γ hγ g => ?_, fun k hk g => ?_, fun x hx g => ?_⟩
    · simp only [n, M, hℓ.left γ hγ, map_mul, hκr γ hγ]
      group
    · have := hℓ.lev ⟨k, hk⟩ g
      have e : φ ⟨k, hk⟩ = κ k := rfl
      simp only [n, M] at this ⊢
      rw [this]
      simp only [map_mul, cEmb_fin τ (hC.fin hk), e]
      group
    · simp only [n, M, hℓ.inf x hx, map_mul, hκi x hx]
      group
  obtain ⟨d, hd⟩ := hF E a τ C hC n hn W Q F hFC P
  refine ⟨d, M, fun g h hh h1 => ?_, fun ν => ?_⟩
  · simp only [M, map_mul, cEmb_fin τ hh, (hκ1 h).2 h1, mul_one]
  have hfam := hd ν fun q => (φ (c q))⁻¹
  refine ⟨_, ⟨hfam.aut, fun k hk => hfam.fix k (hKC hk), hfam.inf, hfam.up, hfam.le, hfam.ge, hfam.fin⟩, fun g i => ?_⟩
  obtain ⟨q₀, h0, h1, h2, h3⟩ := hQ (ℓ g)
  have hnM : n g * M g = φ (ℓ g) := by simp only [n]; group
  have hε' : 0 ≤ ε / R := (div_pos hε hR0).le
  have hv : f.1 (b g i) g = (F q₀).1 (b g i) g := by
    rw [hFv, ← hfC ((c q₀)⁻¹ * ℓ g : C) ⟨Subtype.prop _, h0⟩ (b g i) (g * ((ℓ g)⁻¹ * c q₀ : C))]
    congr 1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have hδ : ∀ q, (φ (c q))⁻¹ * φ (ℓ g) = φ ((c q)⁻¹ * ℓ g) := fun q => by rw [map_mul, map_inv]
  rw [famOf_apply, hv, hnM]
  have e : (F q₀).1 (b g i) g - ∑ q, pev (P q) (φ (ℓ g)) * delta ν ((φ (c q))⁻¹ * φ (ℓ g)) * (F q).1 (b g i) g =
      ∑ q, ((if q = q₀ then 1 else 0) - pev (P q) (φ (ℓ g)) * delta ν (φ ((c q)⁻¹ * ℓ g))) * (F q).1 (b g i) g := by
    simp only [sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, hδ]
  rw [e, map_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hε.le fun q _ => ?_
  rw [map_mul, norm_mul, hFv, ← div_mul_cancel₀ ε hR0.ne']
  refine mul_le_mul ?_ (hR _ _ _) (norm_nonneg _) hε'
  obtain ⟨hb1, hb2⟩ := hD l ι a ν _ (hφI ((c q)⁻¹ * ℓ g))
  by_cases hq : q = q₀
  · subst hq
    have hb3 := hb2 _ hε' h1
    rw [if_pos rfl]
    have e2 : 1 - pev (P q) (φ (ℓ g)) * delta ν (φ ((c q)⁻¹ * ℓ g)) =
        -((pev (P q) (φ (ℓ g)) - 1) * delta ν (φ ((c q)⁻¹ * ℓ g)) + (delta ν (φ ((c q)⁻¹ * ℓ g)) - 1)) := by ring
    rw [e2, map_neg, norm_neg, map_add]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ hb3)
    rw [map_mul, norm_mul]
    exact (mul_le_mul h2 hb1 (norm_nonneg _) hε').trans_eq (mul_one _)
  · rw [if_neg hq, zero_sub, map_neg, norm_neg, map_mul, norm_mul]
    exact (mul_le_mul (h3 q hq) hb1 (norm_nonneg _) hε').trans_eq (mul_one _)
