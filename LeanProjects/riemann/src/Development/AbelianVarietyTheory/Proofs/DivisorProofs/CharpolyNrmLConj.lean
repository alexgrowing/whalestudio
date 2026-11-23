import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTwistedClassesCharpoly
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalTwistContinuousInvolutionIntegralProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralTwistedConjInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralProductGroupStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularTwistedOrbitLocalFinitenessStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.UnitProd

private theorem equivalence_twisted_conj {G : Type} [Group G] (θ : G →* G) :
    Equivalence (fun x y : G => ∃ g, y = g⁻¹ * x * θ g) where
  refl x := ⟨1, by simp⟩
  symm := by
    rintro x y ⟨g, rfl⟩
    exact ⟨g⁻¹, by rw [map_inv]; group⟩
  trans := by
    rintro x y z ⟨g, rfl⟩ ⟨h, rfl⟩
    exact ⟨g * h, by rw [map_mul]; group⟩

theorem rep_mk {G : Type} [Group G] (θ : G →* G) (x : G) :
    ∃ g, TwCl.rep (θ := θ) (Quot.mk _ x) = g⁻¹ * x * θ g := by
  unfold TwCl.rep
  have h := Quot.eqvGen_exact (Quot.out_eq (Quot.mk (fun x y : G => ∃ g, y = g⁻¹ * x * θ g) x))
  rw [Equivalence.eqvGen_iff (equivalence_twisted_conj θ)] at h
  exact (equivalence_twisted_conj θ).symm h

theorem mk_rep {G : Type} [Group G] {θ : G →* G} (c : TwCl θ) : (Quot.mk _ c.rep : TwCl θ) = c := by
  unfold TwCl.rep
  exact Quot.out_eq c

noncomputable def clsEquiv {G G' : Type} [Group G] [Group G'] (θ : G →* G) (θ' : G' →* G') :
    TwCl θ × TwCl θ' ≃ TwCl (θ.prodMap θ') where
  toFun p := Quot.mk _ (p.1.rep, p.2.rep)
  invFun c := (Quot.mk _ c.rep.1, Quot.mk _ c.rep.2)
  left_inv p := by
    obtain ⟨g, hg⟩ := rep_mk (θ.prodMap θ') (p.1.rep, p.2.rep)
    refine Prod.ext ?_ ?_
    · refine Eq.trans (Quot.sound ⟨g.1, ?_⟩).symm (mk_rep p.1)
      exact congrArg Prod.fst hg
    · refine Eq.trans (Quot.sound ⟨g.2, ?_⟩).symm (mk_rep p.2)
      exact congrArg Prod.snd hg
  right_inv c := by
    obtain ⟨g, hg⟩ := rep_mk θ c.rep.1
    obtain ⟨g', hg'⟩ := rep_mk θ' c.rep.2
    refine Eq.trans (Quot.sound ⟨(g, g'), ?_⟩).symm (mk_rep c)
    refine Prod.ext ?_ ?_
    · simp [hg]
    · simp [hg']

theorem ind_conj {G : Type} [Group G] (θ : G →* G) (K : Subgroup G) (hK : ∀ k ∈ K, θ k ∈ K) (δ x k : G) (hk : k ∈ K) :
    (x * k)⁻¹ * δ * θ (x * k) ∈ K ↔ x⁻¹ * δ * θ x ∈ K := by

  have e : (x * k)⁻¹ * δ * θ (x * k) = k⁻¹ * (x⁻¹ * δ * θ x) * θ k := by
    rw [map_mul]; group
  rw [e, K.mul_mem_cancel_right (hK k hk), K.mul_mem_cancel_left (K.inv_mem hk)]

theorem index_ne {G : Type} [Group G] (θ : G →* G) (K : Subgroup G) (hK : ∀ k ∈ K, θ k ∈ K) (δ x : G) :
    (rStab fun k : K => (K : Set G).indicator (1 : G → ℂ) ((x * k)⁻¹ * δ * θ (x * k))).index ≠ 0 := by

  have htop : rStab (fun k : K => (K : Set G).indicator (1 : G → ℂ) ((x * k)⁻¹ * δ * θ (x * k))) = ⊤ := by
    ext k
    simp only [Subgroup.mem_top, iff_true]
    rw [GlobalTheory.TwOrbConj.mem_rStab]
    intro y
    simp only [Subgroup.coe_mul, ← mul_assoc]
    rw [Set.indicator_apply, Set.indicator_apply]
    simp only [SetLike.mem_coe, ind_conj θ K hK δ (x * y) k k.2, Pi.one_apply]
  rw [htop, Subgroup.index_top]
  exact one_ne_zero

theorem clSum_prod {G G' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [Group G']
    [TopologicalSpace G'] [IsTopologicalGroup G'] [T2Space G'] (θ : G →* G) (θ' : G' →* G') (K : Subgroup G)
    (K' : Subgroup G') (S : Set G) (S' : Set G') (hK : ∀ k ∈ K, θ k ∈ K) (hK' : ∀ k ∈ K', θ' k ∈ K')
    (hS : ∀ g y, g⁻¹ * y * θ g ∈ S ↔ y ∈ S) (hS' : ∀ g y, g⁻¹ * y * θ' g ∈ S' ↔ y ∈ S')
    (hf : {c : TwCl θ | c.rep ∈ S}.Finite) (hf' : {c : TwCl θ' | c.rep ∈ S'}.Finite)
    (hd : ∀ y ∈ S, {q : DoubleCoset.Quotient (twCent θ y : Set G) (K : Set G) |
      (Quotient.out q)⁻¹ * y * θ (Quotient.out q) ∈ K}.Finite)
    (hd' : ∀ y ∈ S', {q : DoubleCoset.Quotient (twCent θ' y : Set G') (K' : Set G') |
      (Quotient.out q)⁻¹ * y * θ' (Quotient.out q) ∈ K'}.Finite) :
    clSum (θ.prodMap θ') (K.prod K') {y | y.1 ∈ S ∧ y.2 ∈ S'} 1 (((K.prod K' : Subgroup _) : Set _).indicator 1) =
      clSum θ K S 1 ((K : Set G).indicator 1) * clSum θ' K' S' 1 ((K' : Set G').indicator 1) := by
  unfold clSum
  simp only [Pi.one_apply, one_mul]

  have hKK : ∀ k ∈ K.prod K', (θ.prodMap θ') k ∈ K.prod K' := fun k hk =>
    Subgroup.mem_prod.mpr ⟨hK _ (Subgroup.mem_prod.mp hk).1, hK' _ (Subgroup.mem_prod.mp hk).2⟩
  have hind : (((K.prod K' : Subgroup _) : Set (G × G')).indicator (1 : G × G' → ℂ)) =
      fun y => (K : Set G).indicator 1 y.1 * (K' : Set G').indicator 1 y.2 := by
    funext y
    by_cases h1 : y.1 ∈ K <;> by_cases h2 : y.2 ∈ K' <;>
      simp [Subgroup.mem_prod, h1, h2]
  have hfin : ∀ {H : Type} [Group H] (φ : H →* H) (L : Subgroup H) (hL : ∀ k ∈ L, φ k ∈ L) (T : Set H)
      (hT : ∀ y ∈ T, {q : DoubleCoset.Quotient (twCent φ y : Set H) (L : Set H) |
        (Quotient.out q)⁻¹ * y * φ (Quotient.out q) ∈ L}.Finite) (y : H), y ∈ T →
      {q : DoubleCoset.Quotient (twCent φ y : Set H) (L : Set H) |
        ∃ k ∈ L, (L : Set H).indicator (1 : H → ℂ) ((Quotient.out q * k)⁻¹ * y * φ (Quotient.out q * k)) ≠ 0}.Finite := by
    intro H _ φ L hL T hT y hy
    refine (hT y hy).subset ?_
    rintro q ⟨k, hk, hne⟩
    by_contra hq
    apply hne
    rw [Set.indicator_apply, if_neg]
    rw [SetLike.mem_coe, ind_conj φ L hL _ _ k hk]
    exact hq
  have hprod : ∀ p : TwCl θ × TwCl θ',
      (if (clsEquiv θ θ' p).rep ∈ {y : G × G' | y.1 ∈ S ∧ y.2 ∈ S'} then
        twOrb (θ.prodMap θ') (K.prod K') (clsEquiv θ θ' p).rep (((K.prod K' : Subgroup _) : Set _).indicator 1)
        else 0) =
      (if p.1.rep ∈ S then twOrb θ K p.1.rep ((K : Set G).indicator 1) else 0) *
      (if p.2.rep ∈ S' then twOrb θ' K' p.2.rep ((K' : Set G').indicator 1) else 0) := by
    intro p
    obtain ⟨g, hg⟩ := rep_mk (θ.prodMap θ') (p.1.rep, p.2.rep)
    have e : (clsEquiv θ θ' p).rep = g⁻¹ * (p.1.rep, p.2.rep) * (θ.prodMap θ') g := hg
    have hmem : g⁻¹ * (p.1.rep, p.2.rep) * (θ.prodMap θ') g ∈ {y : G × G' | y.1 ∈ S ∧ y.2 ∈ S'} ↔
        p.1.rep ∈ S ∧ p.2.rep ∈ S' := by
      show g.1⁻¹ * p.1.rep * θ g.1 ∈ S ∧ g.2⁻¹ * p.2.rep * θ' g.2 ∈ S' ↔ _
      rw [hS, hS']
    rw [e, GlobalTheory.TwOrbConj.twOrb_twConj (G × G') (θ.prodMap θ') (K.prod K') (p.1.rep, p.2.rep) g _
      (fun x => index_ne (θ.prodMap θ') (K.prod K') hKK _ x)]
    by_cases h1 : p.1.rep ∈ S <;> by_cases h2 : p.2.rep ∈ S'
    · simp only [hmem, h1, h2, and_self, if_true]
      rw [hind]
      exact GlobalTheory.T.twistedOrbitalIntegral_productGroup G G' θ θ' K K' _ _ _ _ (fun x => index_ne θ K hK _ x) (fun x => index_ne θ' K' hK' _ x)
        (hfin θ K hK S hd _ h1) (hfin θ' K' hK' S' hd' _ h2)
    · rw [if_neg fun h => h2 (hmem.mp h).2, if_neg h2, mul_zero]
    · rw [if_neg fun h => h1 (hmem.mp h).1, if_neg h1, zero_mul]
    · rw [if_neg fun h => h1 (hmem.mp h).1, if_neg h1, zero_mul]
  have hs1 : (Function.support fun c : TwCl θ =>
      if c.rep ∈ S then twOrb θ K c.rep ((K : Set G).indicator 1) else 0).Finite := by
    refine hf.subset fun c hc => ?_
    by_contra h
    apply hc
    change ¬ c.rep ∈ S at h
    simp [h]
  have hs2 : (Function.support fun c : TwCl θ' =>
      if c.rep ∈ S' then twOrb θ' K' c.rep ((K' : Set G').indicator 1) else 0).Finite := by
    refine hf'.subset fun c hc => ?_
    by_contra h
    apply hc
    change ¬ c.rep ∈ S' at h
    simp [h]
  rw [← finsum_comp_equiv (clsEquiv θ θ')]
  refine (finsum_congr hprod).trans ?_
  rw [finsum_curry _ ((hs1.prod hs2).subset fun p hp => ⟨left_ne_zero_of_mul hp, right_ne_zero_of_mul hp⟩),
    finsum_mul]
  refine finsum_congr fun c => ?_
  rw [mul_finsum]

theorem charpoly_nrmL_conj {E : Type} [Field E] [NumberField E] [IsCMField E] (hE : Unr E) (n : ℕ) (w : Pl E)
    (g y : GLw n w) : (nrmL n w (g⁻¹ * y * thL n w g)).val.charpoly = (nrmL n w y).val.charpoly := by
  rw [GlobalTheory.BCT.ThBasic.nrmL_twist hE, Units.val_mul, Units.val_mul, Matrix.coe_units_inv]
  exact Matrix.charpoly_units_conj' _ _

theorem stTw2_unit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (a b : ℕ) (w : Pl E), ¬ IsSplitAt w → ∀ Q₁ Q₂ : (w.adicCompletion E)[X], Q₁.Separable → Q₂.Separable → stTw2 a b w Q₁ Q₂ ((((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b) : Subgroup _) : Set _).indicator 1) = stTw a w Q₁ ((GlobalTheory.LFun.KGL w a : Set (GLw a w)).indicator 1) * stTw b w Q₂ ((GlobalTheory.LFun.KGL w b : Set (GLw b w)).indicator 1) := by
  intro E _ _ _ hE a b w hw Q₁ Q₂ h₁ h₂
  unfold stTw2 stTw
  have hL : ∀ m : ℕ, IsLevel (thL m w) (GlobalTheory.LFun.KGL w m) (GlobalTheory.LFun.KGL w m) := by
    intro m
    unfold IsLevel
    exact ⟨(GlobalTheory.BCT.ThBasic.twist_basic E hE m w).2.2.2.2.1, le_rfl,
      fun k hk => GlobalTheory.BCT.ThBasic.thL_mem_KGL hE m w k hk⟩
  have hS : ∀ (m : ℕ) (Q : (w.adicCompletion E)[X]) (g y : GLw m w),
      g⁻¹ * y * thL m w g ∈ {y : GLw m w | (nrmL m w y).val.charpoly = Q} ↔
        y ∈ {y : GLw m w | (nrmL m w y).val.charpoly = Q} := by
    intro m Q g y
    show _ = Q ↔ _ = Q
    rw [charpoly_nrmL_conj hE]
  have hd : ∀ (m : ℕ) (Q : (w.adicCompletion E)[X]), Q.Separable →
      ∀ y ∈ {y : GLw m w | (nrmL m w y).val.charpoly = Q},
        {q : DoubleCoset.Quotient (twCent (thL m w) y : Set (GLw m w)) (GlobalTheory.LFun.KGL w m : Set (GLw m w)) |
          (Quotient.out q)⁻¹ * y * thL m w (Quotient.out q) ∈ GlobalTheory.LFun.KGL w m}.Finite := by
    intro m Q hQ y hy
    have hy' : (nrmL m w y).val.charpoly = Q := hy
    exact (GlobalTheory.T.regularTwistedOrbit_local_finiteness E hE m w y (hy' ▸ hQ) _ (hL m)).2 _ (GlobalTheory.BCT.ThBasic.twist_basic E hE m w).2.2.2.2.2.1
  exact clSum_prod (thL a w) (thL b w) _ _ _ _ (GlobalTheory.BCT.ThBasic.thL_mem_KGL hE a w)
    (GlobalTheory.BCT.ThBasic.thL_mem_KGL hE b w) (hS a Q₁) (hS b Q₂) (GlobalTheory.BCT.ClsFin.classes_finite E hE a w Q₁ h₁).1
    (GlobalTheory.BCT.ClsFin.classes_finite E hE b w Q₂ h₂).1 (hd a Q₁ h₁) (hd b Q₂ h₂)

end GlobalTheory.BCT.UnitProd
