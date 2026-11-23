import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeLevelFamilyIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralTwistedConjInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralProductGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThLInvolutive
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL

noncomputable section

open NumberField IsDedekindDomain Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC
open scoped Classical TensorProduct
open GlobalTheory.BCT

namespace GlobalTheory.BCT.StTwTens

theorem finsum_prod_mul' {α β : Type} (u : α → ℂ) (v : β → ℂ) :
    ∑ᶠ z : α × β, u z.1 * v z.2 = (∑ᶠ a, u a) * ∑ᶠ b, v b := by
  have hsupp : Function.support (fun z : α × β => u z.1 * v z.2) =
      Function.support u ×ˢ Function.support v := by
    ext z
    simp only [Function.mem_support, Set.mem_prod, ne_eq, mul_eq_zero, not_or]
  by_cases hu : (Function.support u).Finite
  · by_cases hv : (Function.support v).Finite
    · exact GlobalTheory.BCT.OrbProd.finsum_prod_mul_of_finite u v hu hv
    · have hv' : (Function.support v).Infinite := hv
      rw [finsum_of_infinite_support hv', mul_zero]
      rcases (Function.support u).eq_empty_or_nonempty with h | h
      · have hu0 : u = 0 := Function.support_eq_empty_iff.mp h
        simp [hu0]
      · apply finsum_of_infinite_support
        rw [hsupp]
        exact Set.Infinite.prod_right hv' h
  · have hu' : (Function.support u).Infinite := hu
    rw [finsum_of_infinite_support hu', zero_mul]
    rcases (Function.support v).eq_empty_or_nonempty with h | h
    · have hv0 : v = 0 := Function.support_eq_empty_iff.mp h
      simp [hv0]
    · apply finsum_of_infinite_support
      rw [hsupp]
      exact Set.Infinite.prod_left hu' h

section Gen

variable {G G' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G'] [T2Space G']

theorem twOrb_prod' (θ : G →* G) (θ' : G' →* G') (K : Subgroup G) (K' : Subgroup G') (δ : G) (δ' : G')
    (f : G → ℂ) (f' : G' → ℂ)
    (hf : ∀ x : G, (rStab fun k : K => f ((x * k)⁻¹ * δ * θ (x * k))).index ≠ 0)
    (hf' : ∀ x : G', (rStab fun k : K' => f' ((x * k)⁻¹ * δ' * θ' (x * k))).index ≠ 0) :
    twOrb (θ.prodMap θ') (K.prod K') (δ, δ') (fun y => f y.1 * f' y.2) = twOrb θ K δ f * twOrb θ' K' δ' f' := by
  rw [GlobalTheory.BCT.OrbProd.twOrb_eq, GlobalTheory.BCT.OrbProd.twOrb_eq θ, GlobalTheory.BCT.OrbProd.twOrb_eq θ',
    GlobalTheory.BCT.OrbProd.twCent_prod θ θ' δ δ', ← finsum_prod_mul',
    ← finsum_comp_equiv (Equiv.ofBijective _ (GlobalTheory.BCT.OrbProd.dcPair_bij (twCent θ δ) K (twCent θ' δ') K'))]
  refine finsum_congr fun z => ?_
  obtain ⟨t, k, ht, hk, hq⟩ := DoubleCoset.mk_out_eq_mul ((twCent θ δ).prod (twCent θ' δ')) (K.prod K')
    (Quotient.out z.1, Quotient.out z.2)
  rw [Subgroup.mem_prod] at ht hk
  have hdc : GlobalTheory.BCT.OrbProd.dcPair (twCent θ δ) K (twCent θ' δ') K' z =
      DoubleCoset.mk ((twCent θ δ).prod (twCent θ' δ')) (K.prod K') (Quotient.out z.1, Quotient.out z.2) := rfl
  have hpt : t * (Quotient.out z.1, Quotient.out z.2) * k =
      (t.1 * Quotient.out z.1 * k.1, t.2 * Quotient.out z.2 * k.2) := rfl
  rw [Equiv.ofBijective_apply, hdc, hq, hpt,
    GlobalTheory.BCT.OrbProd.orbTerm_prod θ θ' K K' δ δ' f f' _ _ (hf _) (hf' _),
    GlobalTheory.BCT.OrbProd.orbTerm_inv θ K δ f hf ht.1 hk.1, GlobalTheory.BCT.OrbProd.orbTerm_inv θ' K' δ' f' hf' ht.2 hk.2]

end Gen

section Cl

variable {G G' : Type} [Group G] [Group G']

theorem twRel_equiv (θ : G →* G) : Equivalence (fun x y : G => ∃ g, y = g⁻¹ * x * θ g) where
  refl x := ⟨1, by simp⟩
  symm := by
    rintro x y ⟨g, rfl⟩
    exact ⟨g⁻¹, by simp [mul_assoc]⟩
  trans := by
    rintro x y z ⟨g, rfl⟩ ⟨g', rfl⟩
    exact ⟨g * g', by simp [mul_assoc]⟩

def mkC (θ : G →* G) (x : G) : TwCl θ := Quot.mk _ x

theorem rel_of_mkC_eq (θ : G →* G) {x y : G} (h : mkC θ x = mkC θ y) : ∃ g, y = g⁻¹ * x * θ g :=
  (twRel_equiv θ).eqvGen_iff.mp (Quot.eqvGen_exact h)

theorem mkC_eq (θ : G →* G) {x y : G} (g : G) (h : y = g⁻¹ * x * θ g) : mkC θ x = mkC θ y :=
  Quot.sound (r := fun a b : G => ∃ g, b = g⁻¹ * a * θ g) ⟨g, h⟩

theorem mkC_rep (θ : G →* G) (c : TwCl θ) : mkC θ c.rep = c := by
  exact Quot.out_eq c

def clPair (θ : G →* G) (θ' : G' →* G') (c : TwCl (θ.prodMap θ')) : TwCl θ × TwCl θ' :=
  (mkC θ c.rep.1, mkC θ' c.rep.2)

theorem clPair_bij (θ : G →* G) (θ' : G' →* G') : Function.Bijective (clPair θ θ') := by
  constructor
  · intro c d h
    have h1 : mkC θ c.rep.1 = mkC θ d.rep.1 := congrArg Prod.fst h
    have h2 : mkC θ' c.rep.2 = mkC θ' d.rep.2 := congrArg Prod.snd h
    obtain ⟨g, hg⟩ := rel_of_mkC_eq θ h1
    obtain ⟨g', hg'⟩ := rel_of_mkC_eq θ' h2
    calc c = mkC (θ.prodMap θ') c.rep := (mkC_rep _ c).symm
      _ = mkC (θ.prodMap θ') d.rep :=
        mkC_eq _ (g, g') (Prod.ext (by simpa using hg) (by simpa using hg'))
      _ = d := mkC_rep _ d
  · rintro ⟨a, b⟩
    refine ⟨mkC (θ.prodMap θ') (a.rep, b.rep), ?_⟩
    obtain ⟨g, hg⟩ := rel_of_mkC_eq (θ.prodMap θ')
      (mkC_rep (θ.prodMap θ') (mkC (θ.prodMap θ') (a.rep, b.rep)))
    have h1 : a.rep = g.1⁻¹ * (mkC (θ.prodMap θ') (a.rep, b.rep)).rep.1 * θ g.1 := by
      simpa using congrArg Prod.fst hg
    have h2 : b.rep = g.2⁻¹ * (mkC (θ.prodMap θ') (a.rep, b.rep)).rep.2 * θ' g.2 := by
      simpa using congrArg Prod.snd hg
    refine Prod.ext ?_ ?_
    · exact (mkC_eq θ g.1 h1).trans (mkC_rep θ a)
    · exact (mkC_eq θ' g.2 h2).trans (mkC_rep θ' b)

end Cl

theorem charpoly_conj {R m : Type} [CommRing R] [Fintype m] [DecidableEq m] (g X : GL m R) :
    (g⁻¹ * X * g : GL m R).val.charpoly = X.val.charpoly := by
  rw [Units.val_mul, Units.val_mul, Matrix.coe_units_inv]
  exact Matrix.charpoly_units_conj' g X.val

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem rStab_index_ne_zero {n : ℕ} {w : Pl E} {K' : Subgroup (GLw n w)} {φ : GLw n w → ℂ}
    (hK : IsLevel (thL n w) (GlobalTheory.LFun.KGL w n) K') (hφ : IsHecke K' φ) (δ x : GLw n w) :
    (rStab fun k : GlobalTheory.LFun.KGL w n => φ ((x * k)⁻¹ * δ * thL n w (x * k))).index ≠ 0 := by
  obtain ⟨hKo, -, hKθ⟩ := hK
  obtain ⟨-, hinv⟩ := hφ
  have hcpt : CompactSpace (GlobalTheory.LFun.KGL w n) :=
    isCompact_iff_compactSpace.mp (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n).2
  have hopen : IsOpen ((K'.subgroupOf (GlobalTheory.LFun.KGL w n) : Subgroup (GlobalTheory.LFun.KGL w n)) :
      Set (GlobalTheory.LFun.KGL w n)) := Subgroup.subgroupOf_isOpen (GlobalTheory.LFun.KGL w n) K' hKo
  have hfin : Finite (GlobalTheory.LFun.KGL w n ⧸ K'.subgroupOf (GlobalTheory.LFun.KGL w n)) :=
    Subgroup.quotient_finite_of_isOpen _ hopen
  have hH : (K'.subgroupOf (GlobalTheory.LFun.KGL w n)).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hle : K'.subgroupOf (GlobalTheory.LFun.KGL w n) ≤
      rStab fun k : GlobalTheory.LFun.KGL w n => φ ((x * k)⁻¹ * δ * thL n w (x * k)) := by
    intro k hk
    rw [Subgroup.mem_subgroupOf] at hk
    rw [GlobalTheory.TwOrbConj.mem_rStab]
    intro j
    have hk1 : (k : GLw n w)⁻¹ ∈ K' := K'.inv_mem hk
    have hk2 : thL n w (k : GLw n w) ∈ K' := hKθ _ hk
    calc φ ((x * ↑(j * k))⁻¹ * δ * thL n w (x * ↑(j * k)))
        = φ ((↑k)⁻¹ * ((x * ↑j)⁻¹ * δ * thL n w (x * ↑j)) * thL n w ↑k) := by
          congr 1
          simp only [Subgroup.coe_mul, map_mul, mul_inv_rev, mul_assoc]
      _ = φ ((↑k)⁻¹ * ((x * ↑j)⁻¹ * δ * thL n w (x * ↑j))) := (hinv _ hk2 _).2
      _ = φ ((x * ↑j)⁻¹ * δ * thL n w (x * ↑j)) := (hinv _ hk1 _).1
  intro h0
  apply hH
  have hd := Subgroup.index_dvd_of_le hle
  rw [h0] at hd
  exact Nat.eq_zero_of_zero_dvd hd

theorem nrmL_charpoly_twConj (n : ℕ) (w : Pl E) (g y : GLw n w) :
    (nrmL n w (g⁻¹ * y * thL n w g)).val.charpoly = (nrmL n w y).val.charpoly := by
  have hinv := GlobalTheory.BCT.TwistInvol.thL_involutive E n w g
  unfold nrmL
  unfold thL at hinv ⊢
  split_ifs at hinv ⊢ with hs
  · simp only [MonoidHom.id_apply]
    exact charpoly_conj g y
  · have key : g⁻¹ * y * thetaGL n (cj w) g * thetaGL n (cj w) (g⁻¹ * y * thetaGL n (cj w) g) =
        g⁻¹ * (y * thetaGL n (cj w) y) * g := by
      simp only [map_mul, map_inv, hinv]
      group
    rw [key]
    exact charpoly_conj g _

private theorem charpoly_nrmL_rep_eq_and_twOrb_rep_eq {n : ℕ} {w : Pl E} {K' : Subgroup (GLw n w)} {φ : GLw n w → ℂ}
    (hK : IsLevel (thL n w) (GlobalTheory.LFun.KGL w n) K') (hφ : IsHecke K' φ) (x : GLw n w) :
    (nrmL n w (mkC (thL n w) x).rep).val.charpoly = (nrmL n w x).val.charpoly ∧
      twOrb (thL n w) (GlobalTheory.LFun.KGL w n) (mkC (thL n w) x).rep φ =
        twOrb (thL n w) (GlobalTheory.LFun.KGL w n) x φ := by
  obtain ⟨g, hg⟩ := rel_of_mkC_eq (thL n w) (mkC_rep (thL n w) (mkC (thL n w) x))
  constructor
  · have h := nrmL_charpoly_twConj n w g (mkC (thL n w) x).rep
    rw [← hg] at h
    exact h.symm
  · have h := GlobalTheory.TwOrbConj.twOrb_twConj (GLw n w) (thL n w) (GlobalTheory.LFun.KGL w n) (mkC (thL n w) x).rep g φ
      (fun y => rStab_index_ne_zero hK hφ _ y)
    rw [← hg] at h
    exact h.symm

theorem stTw2_tens : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (w : Pl E)
    (Q₁ Q₂ : (w.adicCompletion E)[X])
    (K₁ : Subgroup (GLw a w)) (K₂ : Subgroup (GLw b w)) (φ₁ : GLw a w → ℂ) (φ₂ : GLw b w → ℂ),
    IsLevel (thL a w) (GlobalTheory.LFun.KGL w a) K₁ → IsLevel (thL b w) (GlobalTheory.LFun.KGL w b) K₂ → IsHecke K₁ φ₁ →
    IsHecke K₂ φ₂ → stTw2 a b w Q₁ Q₂ (tens φ₁ φ₂) = stTw a w Q₁ φ₁ * stTw b w Q₂ φ₂ := by
  intro E _ _ _ a b w Q₁ Q₂ K₁ K₂ φ₁ φ₂ h₁ h₂ h₃ h₄
  unfold stTw2 stTw tens clSum
  rw [← finsum_prod_mul', ← finsum_comp_equiv (Equiv.ofBijective _ (clPair_bij (thL a w) (thL b w)))]
  refine finsum_congr fun c => ?_
  have hcl : clPair (thL a w) (thL b w) c = (mkC (thL a w) c.rep.1, mkC (thL b w) c.rep.2) := rfl
  obtain ⟨hc₁, ho₁⟩ := charpoly_nrmL_rep_eq_and_twOrb_rep_eq h₁ h₃ c.rep.1
  obtain ⟨hc₂, ho₂⟩ := charpoly_nrmL_rep_eq_and_twOrb_rep_eq h₂ h₄ c.rep.2
  have ho : twOrb ((thL a w).prodMap (thL b w)) ((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b)) c.rep
      (fun y => φ₁ y.1 * φ₂ y.2) =
      twOrb (thL a w) (GlobalTheory.LFun.KGL w a) c.rep.1 φ₁ * twOrb (thL b w) (GlobalTheory.LFun.KGL w b) c.rep.2 φ₂ :=
    twOrb_prod' (thL a w) (thL b w) _ _ c.rep.1 c.rep.2 φ₁ φ₂ (fun x => rStab_index_ne_zero h₁ h₃ _ x)
      (fun x => rStab_index_ne_zero h₂ h₄ _ x)
  rw [Equiv.ofBijective_apply, hcl]
  simp only [Set.mem_ofPred_eq, Pi.one_apply, one_mul, hc₁, hc₂, ho₁, ho₂, ho]
  by_cases hA : (nrmL a w c.rep.1).val.charpoly = Q₁ <;>
    by_cases hB : (nrmL b w c.rep.2).val.charpoly = Q₂ <;> simp [hA, hB]

end GlobalTheory.BCT.StTwTens
