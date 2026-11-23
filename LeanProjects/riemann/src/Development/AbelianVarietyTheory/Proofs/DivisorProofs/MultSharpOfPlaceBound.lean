import Mathlib
import Formalism.LocalToGlobal.Divisibility.DefGroup
import Formalism.LocalToGlobal.Divisibility.GoodPartHermitianSpec
import Formalism.BranchSandwichDivisors.BranchIsometryProofs.Numeric
import Development.AbelianVarietyTheory.Definitions.Divisors.SplitDoublingNBlock
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.CuspidalProductMultiplicity

noncomputable section

namespace GlobalTheory.FinGL.MultSharpPf

open GlobalTheory.FinGL Formalism.L2.DIV Module NumberField GlobalTheory.IndefiniteRowSideFullHecke.CuspidalProductMultiplicity

def PlaceBound : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] (ψ : AddChar F ℂ), ψ ≠ 1 → ∀ (r : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (b : Fin r → ℕ) (σ : Representation ℂ (blockTri (κ := F) b) V), IsCuspDatum b σ →
    ∀ ρ k : ℕ, 1 ≤ k → ρ + k + 1 ≤ r → r ≤ Fintype.card F →
      (Fintype.card F : ℝ) ^ k * (1 - 1 / (Fintype.card F : ℝ)) ≤ (nPos ψ (parInd b σ) ρ k : ℝ) ∧
      (nPos ψ (parInd b σ) ρ k : ℝ) ≤ (Fintype.card F : ℝ) ^ k * (1 + (2 * (r : ℝ) - 1) / (Fintype.card F : ℝ))

theorem mem_eig {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ G V) (S : Set G) (χ : G → ℂ)
    (v : V) : v ∈ eig τ S χ ↔ ∀ g ∈ S, τ g v = χ g • v := by
  simp [eig, Submodule.mem_iInf, sub_eq_zero]

theorem card_mul_finrank_eig {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (τ : Representation ℂ G V) (P : Subgroup G) [Fintype P] (ψ : G → ℂ) (h1 : ψ 1 = 1)
    (hm : ∀ x ∈ P, ∀ y ∈ P, ψ (x * y) = ψ x * ψ y) :
    (Fintype.card P : ℂ) * (finrank ℂ (eig τ (P : Set G) ψ) : ℂ) =
      ∑ h : P, LinearMap.trace ℂ V (τ h) * (ψ h)⁻¹ := by
  have hc : (Fintype.card P : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have h0 : ∀ x ∈ P, ψ x ≠ 0 := fun x hx e => by
    have := hm x hx x⁻¹ (P.inv_mem hx)
    rw [mul_inv_cancel, h1, e, zero_mul] at this
    exact one_ne_zero this
  set e : V →ₗ[ℂ] V := (Fintype.card P : ℂ)⁻¹ • ∑ h : P, (ψ h)⁻¹ • (τ h : V →ₗ[ℂ] V) with he
  have hp : LinearMap.IsProj (eig τ (P : Set G) ψ) e := by
    constructor
    · intro v
      rw [mem_eig]
      intro g hg
      have hg' : g ∈ P := hg
      simp only [he, LinearMap.smul_apply, LinearMap.coe_sum, Finset.sum_apply, map_smul, map_sum]
      rw [smul_comm (ψ g)]
      congr 1
      rw [Finset.smul_sum]
      refine Fintype.sum_equiv (Equiv.mulLeft (⟨g, hg'⟩ : P)) _ _ fun x => ?_
      simp only [Equiv.coe_mulLeft, Subgroup.coe_mul, map_mul, Module.End.mul_apply]
      rw [hm g hg' x x.2, smul_smul, mul_inv, ← mul_assoc, mul_inv_cancel₀ (h0 g hg'), one_mul]
    · intro v hv
      rw [mem_eig] at hv
      simp only [he, LinearMap.smul_apply, LinearMap.coe_sum, Finset.sum_apply]
      rw [Finset.sum_congr rfl (g := fun _ => v) fun x _ => by
        rw [hv x x.2, smul_smul, inv_mul_cancel₀ (h0 x x.2), one_smul]]
      rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hc, one_smul]
  rw [← hp.trace, he, map_smul, map_sum, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hc, one_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [map_smul, smul_eq_mul, mul_comm]

variable {E : Type} [Field E] [NumberField E]

def piEquiv {Pg : Finset (Pl E)} {r : ℕ} (Hl : ∀ PP : ↥Pg, Subgroup (GL (Fin r) (kP PP.1))) :
    (Subgroup.pi Set.univ Hl : Subgroup (G0 Pg r)) ≃ ∀ PP : ↥Pg, Hl PP where
  toFun x PP := LevelP.prj Hl PP x
  invFun y := ⟨fun PP => y PP, fun PP _ => (y PP).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem levelMult_ofLocal {K : Type} [Field K] (s : K →+* ℂ) {Pg : Finset (Pl E)} {r : ℕ}
    (Hl : ∀ PP : ↥Pg, Subgroup (GL (Fin r) (kP PP.1))) [∀ PP, Fintype (Hl PP)] (cl : ∀ PP : ↥Pg, Hl PP →* Kˣ)
    (χ : G0 Pg r → K) (θ : ∀ PP : ↥Pg, GL (Fin r) (kP PP.1) → ℂ) (hχ : ∀ x, s (χ x) = ∏ PP : ↥Pg, θ PP (x PP))
    (n : ↥Pg → ℕ)
    (hn : ∀ PP, (Fintype.card (Hl PP) : ℂ) * (n PP : ℂ) = ∑ h : Hl PP, θ PP h * (s (cl PP h : K))⁻¹) :
    levelMult (LevelP.ofLocal Hl cl) χ = ((∏ PP, n PP : ℕ) : K) := by
  classical
  apply s.injective
  unfold levelMult
  rw [map_mul, map_inv₀, map_natCast, map_natCast, map_sum]
  have hcard : Nat.card (LevelP.ofLocal Hl cl).H = ∏ PP, Fintype.card (Hl PP) := by
    rw [← Fintype.card_pi, ← Nat.card_eq_fintype_card]
    exact Nat.card_congr (piEquiv Hl)
  have hne : (∏ PP, (Fintype.card (Hl PP) : ℂ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun PP _ => by exact_mod_cast Fintype.card_ne_zero
  rw [hcard, Nat.cast_prod, Nat.cast_prod, inv_mul_eq_iff_eq_mul₀ hne, ← Finset.prod_mul_distrib,
    Finset.prod_congr rfl fun PP _ => hn PP, Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine @Fintype.sum_equiv _ _ _ (_) _ _ (piEquiv Hl) _ _ fun x => ?_
  rw [map_mul, hχ, Finset.prod_mul_distrib, Finset.prod_inv_distrib, Units.val_inv_eq_inv_val, map_inv₀]
  congr 2
  show s ((((∏ PP : ↥Pg, (cl PP).comp (LevelP.prj Hl PP)) x : Kˣ)) : K) = _
  rw [MonoidHom.finset_prod_apply, Units.coe_prod, map_prod]
  rfl

theorem edgeSum_sup_eq {κ : Type} [CommRing κ] {r k : ℕ} {g : GL (Fin r) κ} (hg : g ∈ unipCol κ r 0 k) :
    edgeSum supEdge g = edgeSum (symEdge 0 k) g := by
  unfold edgeSum
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  by_cases h1 : supEdge i j <;> by_cases h2 : symEdge 0 k i j
  · rw [if_pos h1, if_pos h2]
  · rw [if_pos h1, if_neg h2]
    unfold supEdge at h1
    unfold symEdge at h2
    exact hg.2 i j (Nat.zero_le _) (by omega) (by omega)
  · unfold supEdge at h1
    unfold symEdge at h2
    omega
  · rw [if_neg h1, if_neg h2]

theorem addCharHom_sym {κ : Type} [CommRing κ] {K : Type} [CommRing K] {r ρ k : ℕ} (ψ : AddChar κ K) (h : unipSym κ r ρ k) :
    (addCharHom ψ (symHom κ r ρ k) h : K) = ψ (edgeSum (symEdge ρ k) (h : GL (Fin r) κ)) := rfl

theorem addCharHom_first {κ : Type} [CommRing κ] {K : Type} [CommRing K] {r k : ℕ} (ψ : AddChar κ K) (h : unipCol κ r 0 k) :
    ((addCharHom ψ (supHom κ r)).comp (Subgroup.inclusion (unipCol_le r 0 k)) h : K) =
      ψ (edgeSum (symEdge 0 k) (h : GL (Fin r) κ)) := by
  rw [← edgeSum_sup_eq h.2]
  rfl

theorem place (H : PlaceBound) {κ : Type} [Field κ] [Finite κ] {K : Type} [Field K] (s : K →+* ℂ) (ψ : AddChar κ K)
    (hψ : ψ ≠ 1) {r ρ k : ℕ} (hk : 1 ≤ k) (hr : ρ + k + 1 ≤ r) (hq : r ≤ Nat.card κ) (θ : GL (Fin r) κ → ℂ)
    (hθ : IsCuspProdChar θ) [Fintype (unipSym κ r ρ k)] :
    ∃ n : ℕ, (Fintype.card (unipSym κ r ρ k) : ℂ) * (n : ℂ) =
        ∑ h : unipSym κ r ρ k, θ h * (s (ψ (edgeSum (symEdge ρ k) (h : GL (Fin r) κ))))⁻¹ ∧
      (Nat.card κ : ℝ) ^ k * (1 - 1 / (Nat.card κ : ℝ)) ≤ (n : ℝ) ∧
      (n : ℝ) ≤ (Nat.card κ : ℝ) ^ k * (1 + (2 * (r : ℝ) - 1) / (Nat.card κ : ℝ)) := by
  obtain ⟨d, b, σ, hσ, hθ⟩ := hθ
  letI : Fintype κ := Fintype.ofFinite κ
  set φ : AddChar κ ℂ := s.toMonoidHom.compAddChar ψ with hφ
  have hφa : ∀ x, φ x = s (ψ x) := fun _ => rfl
  have hφ1 : φ ≠ 1 := fun e => hψ (by
    ext x
    apply s.injective
    rw [← hφa, e]; simp)
  rw [Nat.card_eq_fintype_card] at hq ⊢
  refine ⟨nPos φ (parInd b σ) ρ k, ?_, H κ φ hφ1 r _ b σ hσ ρ k hk hr hq⟩
  unfold nPos
  rw [card_mul_finrank_eig (parInd b σ) (unipSym κ r ρ k) (fun g => φ (edgeSum (symEdge ρ k) g))]
  · refine Finset.sum_congr rfl fun x _ => ?_
    rw [hθ]; rfl
  · have := (symHom κ r ρ k).map_one
    have h2 : edgeSum (symEdge ρ k) (1 : GL (Fin r) κ) = 0 := this
    simp only [h2, AddChar.map_zero_eq_one]
  · intro x hx y hy
    have := (symHom κ r ρ k).map_mul ⟨x, hx⟩ ⟨y, hy⟩
    have h2 : edgeSum (symEdge ρ k) (x * y) = edgeSum (symEdge ρ k) x + edgeSum (symEdge ρ k) y := this
    simp only [h2, AddChar.map_add_eq_mul]

theorem places (H : PlaceBound) {K : Type} [Field K] (s : K →+* ℂ) (Pg : Finset (Pl E)) (f g r ρ k c : ℕ) (hc : c = ρ + k)
    (ψ : ∀ PP : Pl E, AddChar (kP PP) K) (hf : Pg.card = 2 * f) (hk : 1 ≤ k) (hr : ρ + k + 1 ≤ r) (hg : 0 < g)
    (hfg : 4 * f * r ≤ g) (hq : ∀ PP ∈ Pg, g ≤ Nat.card (kP PP)) (hψ : IsGenericPsi Pg ψ)
    (cl : ∀ PP : ↥Pg, unipCol (kP PP.1) r ρ c →* Kˣ)
    (hcl : ∀ PP h, (cl PP h : K) = ψ PP.1 (edgeSum (symEdge ρ k) (h : GL (Fin r) (kP PP.1))))
    (χ : G0 Pg r → K) (hχ : IsProdCuspChar s Pg r χ) :
    MultNear (LevelP.ofLocal (fun PP => unipCol (kP PP.1) r ρ c) cl) χ (nbar Pg k) (8 * f * r / g) := by
  subst hc
  obtain ⟨θ, hθ, hχ⟩ := hχ
  have hfin : ∀ PP : ↥Pg, Finite (kP PP.1) := fun PP => finite_kP PP.1
  letI : ∀ PP : ↥Pg, Fintype (unipCol (kP PP.1) r ρ (ρ + k)) := fun PP => Fintype.ofFinite _
  have hrq : ∀ PP : ↥Pg, r ≤ Nat.card (kP PP.1) := fun PP => by
    have h1 : 0 < Pg.card := Finset.card_pos.2 ⟨PP.1, PP.2⟩
    have h2 : 1 ≤ 4 * f := by omega
    exact le_trans (le_trans (Nat.le_mul_of_pos_left r h2) hfg) (hq PP.1 PP.2)
  have hloc := fun PP : ↥Pg => @place H (kP PP.1) (Ideal.Quotient.field PP.1.asIdeal) (hfin PP) K _ s (ψ PP.1)
    (hψ PP.1 PP.2) r ρ k hk hr (hrq PP) (θ PP) (hθ PP) (this PP)
  choose n hn hb using hloc
  refine ⟨∏ PP, n PP, levelMult_ofLocal s _ cl χ θ hχ n fun PP => ?_, ?_⟩
  · simp only [hcl]
    exact hn PP
  · have := Formalism.BranchingDeterminantCap.multiplicity_product ↥Pg (fun PP => (Nat.card (kP PP.1) : ℝ)) (fun PP => (n PP : ℝ)) k f r g
      (by rw [Fintype.card_coe, hf]; push_cast; rfl) (by exact_mod_cast (by omega : 1 ≤ r)) (by exact_mod_cast hg)
      (fun PP => by exact_mod_cast hq PP.1 PP.2) (by exact_mod_cast hfg) hb
    have e : (nbar Pg k : ℝ) = ∏ PP : ↥Pg, (Nat.card (kP PP.1) : ℝ) ^ k := by
      unfold nbar
      rw [← Finset.prod_coe_sort Pg]; push_cast; rfl
    rw [e, Nat.cast_prod, abs_le]
    constructor <;> linarith [this.1, this.2]

theorem multSharp_of_placeBound (H : PlaceBound) : MultSharp := by
  intro E _ _ K _ _ s Pg f g r ρ k ψ hf hk hr hg hfg hq hψ χ hχ
  constructor
  · unfold PsharpSym
    exact places H s Pg f g r ρ k (ρ + k) rfl ψ hf hk (by omega) hg hfg hq hψ
      (fun PP => addCharHom (ψ PP.1) (symHom (kP PP.1) r ρ k)) (fun PP h => addCharHom_sym _ h) χ hχ
  · unfold Psharp
    exact places H s Pg f g r 0 k k (Nat.zero_add k).symm ψ hf hk (by omega) hg hfg hq hψ
      (fun PP => (addCharHom (ψ PP.1) (supHom (kP PP.1) r)).comp (Subgroup.inclusion (unipCol_le r 0 k)))
      (fun PP h => addCharHom_first _ h) χ hχ

end GlobalTheory.FinGL.MultSharpPf
