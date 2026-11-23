import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SelNZero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LocalCochainsGlueGlobal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisRepRankTwoTateDualMatrixMemCoefRingOfNorma
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisRepRankTwoTateDualEqOneOfMemKerUnramifiedQ
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContinuousGaloisRepRankTwoTateDualOfOrdinaryNorm
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

noncomputable section

namespace GlobalTheory.Ord2.GwFin

open GlobalTheory.Ord2.TwistTriv

variable {l : ℕ} [Fact l.Prime]

def mulR (c : Coef l) (n : ℕ) (a : c.O) : Red c n →+ Red c n :=
  QuotientAddGroup.map (nbhd c n) (nbhd c n) (AddMonoidHom.mulLeft a) (by
    intro x hx
    show ‖((a * x : c.O) : Qbar l)‖ ≤ _
    rw [MulMemClass.coe_mul, norm_mul]
    calc _ ≤ 1 * ‖(x : Qbar l)‖ := mul_le_mul_of_nonneg_right (norm_le_one c a) (norm_nonneg _)
      _ ≤ _ := by rw [one_mul]; exact hx)

theorem mulR_red (c : Coef l) (n : ℕ) (a x : c.O) : mulR c n a (red c n x) = red c n (a * x) := rfl

def redV (c : Coef l) (n : ℕ) (x : Fin 2 → c.O) : Fin 2 → Red c n := fun i => red c n (x i)

theorem redV_surjective (c : Coef l) (n : ℕ) : Function.Surjective (redV c n) := by
  intro m
  choose x hx using fun i => red_surjective c n (m i)
  exact ⟨x, funext hx⟩

theorem redV_add (c : Coef l) (n : ℕ) (x y : Fin 2 → c.O) :
    redV c n (x + y) = redV c n x + redV c n y := by
  funext i; simp [redV]

def act (c : Coef l) (n : ℕ) (B : Matrix (Fin 2) (Fin 2) c.O) :
    (Fin 2 → Red c n) →+ (Fin 2 → Red c n) where
  toFun m i := ∑ j, mulR c n (B i j) (m j)
  map_zero' := by funext i; simp
  map_add' m m' := by funext i; simp [Finset.sum_add_distrib]

theorem act_redV (c : Coef l) (n : ℕ) (B : Matrix (Fin 2) (Fin 2) c.O) (x : Fin 2 → c.O) :
    act c n B (redV c n x) = redV c n (B *ᵥ x) := by
  funext i
  simp only [act, AddMonoidHom.coe_mk, ZeroHom.coe_mk, redV, mulR_red, Matrix.mulVec, dotProduct,
    map_sum]

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω]

def Vo (c : Coef l) (V : R2 Ω l) (hD : ∀ s i j, mat V s i j ∈ c.O) (s : G ℚ Ω) :
    Matrix (Fin 2) (Fin 2) c.O :=
  fun i j => ⟨mat V s i j, hD s i j⟩

theorem Vo_mulVec_coe (c : Coef l) (V : R2 Ω l) (hD : ∀ s i j, mat V s i j ∈ c.O) (s : G ℚ Ω)
    (x : Fin 2 → c.O) (i : Fin 2) :
    ((Vo c V hD s *ᵥ x) i : Qbar l) = (mat V s *ᵥ fun j => (x j : Qbar l)) i := by
  simp [Matrix.mulVec, dotProduct, Vo]

theorem Vo_mul (c : Coef l) (V : R2 Ω l) (hD : ∀ s i j, mat V s i j ∈ c.O) (s t : G ℚ Ω) :
    Vo c V hD (s * t) = Vo c V hD s * Vo c V hD t := by
  ext i j
  simp [Vo, mat, Matrix.mul_apply]

theorem Vo_eq_one (c : Coef l) (V : R2 Ω l) (hD : ∀ s i j, mat V s i j ∈ c.O) {s : G ℚ Ω}
    (h : V s = 1) : Vo c V hD s = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Vo, mat, h]

def repG (c : Coef l) (n : ℕ) (V : R2 Ω l) (hD : ∀ s i j, mat V s i j ∈ c.O) :
    Representation (ZMod (l ^ n)) (G ℚ Ω) (Fin 2 → Red c n) where
  toFun s := (act c n (Vo c V hD s)).toZModLinearMap (l ^ n)
  map_one' := by
    apply LinearMap.ext; intro m
    obtain ⟨x, rfl⟩ := redV_surjective c n m
    show act c n (Vo c V hD 1) (redV c n x) = redV c n x
    rw [act_redV, Vo_eq_one c V hD (map_one V), Matrix.one_mulVec]
  map_mul' s t := by
    apply LinearMap.ext; intro m
    obtain ⟨x, rfl⟩ := redV_surjective c n m
    show act c n (Vo c V hD (s * t)) (redV c n x) =
      act c n (Vo c V hD s) (act c n (Vo c V hD t) (redV c n x))
    rw [act_redV, act_redV, act_redV, Vo_mul, Matrix.mulVec_mulVec]

theorem repG_apply (c : Coef l) (n : ℕ) (V : R2 Ω l) (hD : ∀ s i j, mat V s i j ∈ c.O) (s : G ℚ Ω)
    (m : Fin 2 → Red c n) : repG c n V hD s m = act c n (Vo c V hD s) m := rfl

variable [IsAlgClosure ℚ Ω] (S : Finset Pl)

def repS (c : Coef l) (n : ℕ) (V : R2 Ω l) (hD : ∀ s i j, mat V s i j ∈ c.O)
    (hK : ∀ a ∈ (toGS Ω (S : Set Pl)).ker, V a = 1) :
    Representation (ZMod (l ^ n)) (GS Ω (S : Set Pl)) (Fin 2 → Red c n) :=
  QuotientGroup.lift (NS Ω (S : Set Pl)) (repG c n V hD) (by
    intro a ha
    rw [MonoidHom.mem_ker]
    apply LinearMap.ext; intro m
    obtain ⟨x, rfl⟩ := redV_surjective c n m
    show act c n (Vo c V hD a) (redV c n x) = redV c n x
    rw [Vo_eq_one c V hD (hK a (by rw [toGS, QuotientGroup.ker_mk']; exact ha)), act_redV,
      Matrix.one_mulVec])

theorem repS_mk (c : Coef l) (n : ℕ) (V : R2 Ω l) (hD : ∀ s i j, mat V s i j ∈ c.O)
    (hK : ∀ a ∈ (toGS Ω (S : Set Pl)).ker, V a = 1) (g : G ℚ Ω) :
    repS S c n V hD hK (QuotientGroup.mk g) = repG c n V hD g := rfl

end GlobalTheory.Ord2.GwFin

namespace GlobalTheory.Ord2.GwFin

open GlobalTheory.Ord2.TwistTriv

variable {l : ℕ} [Fact l.Prime] {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (S : Finset Pl)

theorem contAction_repS (c : Coef l) (n : ℕ) (V : R2 Ω l) (hD : ∀ s i j, mat V s i j ∈ c.O)
    (hK : ∀ a ∈ (toGS Ω (S : Set Pl)).ker, V a = 1) (hc : Continuous V) :
    ReciprocityTheory.Gal.ContAction (repS S c n V hD hK) := by
  unfold ReciprocityTheory.Gal.ContAction
  refine continuous_prod_of_discrete_right.2 fun m => ?_
  rw [(QuotientGroup.isQuotientMap_mk (NS Ω (S : Set Pl))).continuous_iff]
  obtain ⟨x, rfl⟩ := redV_surjective c n m
  have e : ((fun q => repS S c n V hD hK q (redV c n x)) ∘
      (QuotientGroup.mk : G ℚ Ω → GS Ω (S : Set Pl))) = fun g => redV c n (Vo c V hD g *ᵥ x) := by
    funext g; exact act_redV c n _ x
  rw [e]
  refine continuous_pi fun i => continuous_red_comp c n (fun g => (Vo c V hD g *ᵥ x) i) ?_
  simp only [Vo_mulVec_coe]
  have hm : Continuous fun g => mat V g := Units.continuous_val.comp hc
  exact (continuous_apply i).comp (hm.matrix_mulVec continuous_const)

def zr (c : Coef l) (n : ℕ) (z : G ℚ Ω → Fin 2 → Qbar l) (hz : ∀ s k, z s k ∈ c.O) (s : G ℚ Ω) :
    Fin 2 → Red c n :=
  redV c n fun k => ⟨z s k, hz s k⟩

theorem zr_eq_iff (c : Coef l) (n : ℕ) (z z' : G ℚ Ω → Fin 2 → Qbar l) (hz : ∀ s k, z s k ∈ c.O)
    (hz' : ∀ s k, z' s k ∈ c.O) (s : G ℚ Ω) :
    zr c n z hz s = zr c n z' hz' s ↔ Cv n (z s) (z' s) := by
  simp only [zr, redV, funext_iff, red_eq_iff, Cv]

theorem zr_eq_zero (c : Coef l) (n : ℕ) (z : G ℚ Ω → Fin 2 → Qbar l) (hz : ∀ s k, z s k ∈ c.O)
    (a : G ℚ Ω) (h : Cv n (z a) 0) : zr c n z hz a = 0 := by
  funext k
  show red c n ⟨z a k, hz a k⟩ = 0
  rw [red_eq_zero_iff, mem_nbhd]
  have := h k
  simpa [Cg] using this

theorem zr_mul (c : Coef l) (n : ℕ) (V : R2 Ω l) (hD : ∀ s i j, mat V s i j ∈ c.O)
    (z : G ℚ Ω → Fin 2 → Qbar l) (hz : ∀ s k, z s k ∈ c.O)
    (hcoc : ∀ s t, Cv n (z (s * t)) (z s + mat V s *ᵥ z t)) (s t : G ℚ Ω) :
    zr c n z hz (s * t) = zr c n z hz s + repG c n V hD s (zr c n z hz t) := by
  rw [repG_apply, zr, zr, zr, act_redV, ← redV_add]
  funext k
  simp only [redV]
  rw [red_eq_iff, Pi.add_apply, AddMemClass.coe_add, Vo_mulVec_coe]
  have h := hcoc s t k
  simpa only [Pi.add_apply] using h

def zbar (c : Coef l) (n : ℕ) (z : G ℚ Ω → Fin 2 → Qbar l) (hz : ∀ s k, z s k ∈ c.O)
    (q : GS Ω (S : Set Pl)) : Fin 2 → Red c n :=
  zr c n z hz q.out

theorem zbar_mk (c : Coef l) (n : ℕ) (V : R2 Ω l) (hD : ∀ s i j, mat V s i j ∈ c.O)
    (z : G ℚ Ω → Fin 2 → Qbar l) (hz : ∀ s k, z s k ∈ c.O)
    (hcoc : ∀ s t, Cv n (z (s * t)) (z s + mat V s *ᵥ z t))
    (hker : ∀ a ∈ (toGS Ω (S : Set Pl)).ker, Cv n (z a) 0) (g : G ℚ Ω) :
    zbar S c n z hz (QuotientGroup.mk g) = zr c n z hz g := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (NS Ω (S : Set Pl)) g
  unfold zbar
  rw [hh, zr_mul c n V hD z hz hcoc,
    zr_eq_zero c n z hz (h : G ℚ Ω) (hker _ (by rw [toGS, QuotientGroup.ker_mk']; exact h.2)), map_zero,
    add_zero]

theorem zbar_mem (c : Coef l) (n : ℕ) (V : R2 Ω l) (hD : ∀ s i j, mat V s i j ∈ c.O)
    (hK : ∀ a ∈ (toGS Ω (S : Set Pl)).ker, V a = 1)
    (z : G ℚ Ω → Fin 2 → Qbar l) (hz : ∀ s k, z s k ∈ c.O) (hzc : Continuous z)
    (hcoc : ∀ s t, Cv n (z (s * t)) (z s + mat V s *ᵥ z t))
    (hker : ∀ a ∈ (toGS Ω (S : Set Pl)).ker, Cv n (z a) 0) :
    zbar S c n z hz ∈ Z1 (repS S c n V hD hK) := by
  refine ⟨?_, fun q₁ q₂ => ?_⟩
  · rw [(QuotientGroup.isQuotientMap_mk (NS Ω (S : Set Pl))).continuous_iff]
    have e : zbar S c n z hz ∘ (QuotientGroup.mk : G ℚ Ω → GS Ω (S : Set Pl)) = zr c n z hz := by
      funext g; exact zbar_mk S c n V hD z hz hcoc hker g
    rw [e]
    exact continuous_pi fun k => continuous_red_comp c n (fun g => (⟨z g k, hz g k⟩ : c.O))
      ((continuous_apply k).comp hzc)
  · induction q₁ using QuotientGroup.induction_on with | H g => ?_
    induction q₂ using QuotientGroup.induction_on with | H h => ?_
    rw [← QuotientGroup.mk_mul, zbar_mk S c n V hD z hz hcoc hker, zbar_mk S c n V hD z hz hcoc hker,
      zbar_mk S c n V hD z hz hcoc hker, repS_mk, zr_mul c n V hD z hz hcoc]

end GlobalTheory.Ord2.GwFin

namespace GlobalTheory.Ord2.GwFin

open GlobalTheory.Ord2.TwistTriv

theorem finite_cocycles_of_finite_h1 {R : Type*} [CommRing R] {H : Type*} [Group H] [TopologicalSpace H]
    {Q : Type*} [AddCommGroup Q] [Module R Q] [TopologicalSpace Q] [IsTopologicalAddGroup Q]
    [ContinuousConstSMul R Q] [Finite Q] (σ : Representation R H Q) [Finite (H1 σ)] :
    Finite (Z1 σ) := by
  haveI : Finite ((B1 σ).comap (Z1 σ).subtype) := by
    haveI : Finite (B1 σ) := by
      haveI : Finite (Set.range (d0 σ)) := Set.finite_range _
      exact Finite.of_injective (fun x : B1 σ => (⟨x.1, x.2⟩ : Set.range (d0 σ)))
        (fun x y h => Subtype.ext (congrArg Subtype.val h))
    exact Finite.of_injective (fun x : (B1 σ).comap (Z1 σ).subtype => (⟨x.1.1, x.2⟩ : B1 σ))
      (fun x y h => by
        apply Subtype.ext; apply Subtype.ext
        have := congrArg Subtype.val h
        simpa using this)
  let P := (B1 σ).comap (Z1 σ).subtype
  let s := Function.surjInv (Submodule.Quotient.mk_surjective P)
  have hs : ∀ x : Z1 σ, x - s (Submodule.Quotient.mk x) ∈ P := fun x =>
    (Submodule.Quotient.eq P).1 (Function.surjInv_eq (Submodule.Quotient.mk_surjective P) _).symm
  refine Finite.of_injective (fun x : Z1 σ => ((Submodule.Quotient.mk x : Z1 σ ⧸ P), (⟨_, hs x⟩ : P))) ?_
  intro x y h
  simp only [Prod.mk.injEq, Subtype.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  rw [h1] at h2
  simpa using h2

variable {l : ℕ} [Fact l.Prime] {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (S : Finset Pl)

theorem finite_cocycles_restricted_rep (hL : GlobalTheory.Mem.LiteralAutomorphy.LitCoh) (c : Coef l) (n : ℕ) (V : R2 Ω l)
    (hD : ∀ s i j, mat V s i j ∈ c.O) (hK : ∀ a ∈ (toGS Ω (S : Set Pl)).ker, V a = 1)
    (hc : Continuous V) (hS : ContainsAbove S l) : Finite (Z1 (repS S c n V hD hK)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · haveI : Subsingleton (Red c 0) := by
      refine ⟨fun a b => ?_⟩
      obtain ⟨x, rfl⟩ := red_surjective c 0 a
      obtain ⟨y, rfl⟩ := red_surjective c 0 b
      rw [red_eq_iff]
      unfold Cg
      rw [pow_zero, norm_one]
      have hxy : ‖(x : Qbar l) - y‖ ≤ max ‖(x : Qbar l)‖ ‖-(y : Qbar l)‖ := by
        rw [sub_eq_add_neg]; exact IsUltrametricDist.norm_add_le_max _ _
      rw [norm_neg] at hxy
      exact hxy.trans (max_le (norm_le_one c x) (norm_le_one c y))
    infer_instance
  · haveI := (hL.gf ℚ Ω l n (Fin 2 → Red c n) S (repS S c n V hD hK) hn hS
      (contAction_repS S c n V hD hK hc)).2.1
    exact finite_cocycles_of_finite_h1 _

theorem card_dualCocyclesModPrimePow_unramifiedOutsideS_bounded : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ c : Coef l, (∀ s i j, mat W s i j ∈ c.O) → ∀ n : ℕ, ∃ B : ℕ, ∀ (N : ℕ) (z : Fin N → G ℚ Ω → Fin 2 → Qbar l), (∀ i, Coc1 c n (dual1 W) ⊤ (z i) ∧ ∀ a ∈ (toGS Ω (S : Set Pl)).ker, Cv n (z i a) 0) → (∀ i j, i ≠ j → ¬ Cob1 c n (dual1 W) ⊤ (z i - z j)) → N ≤ B := by
  intro hL l _ Ω _ _ _ e S A W hN c hW n
  have hD := galoisRepRankTwoTateDual_matrix_mem_coefRing_of_normalForm l Ω e S A W hN c hW
  have hK := galoisRepRankTwoTateDual_eq_one_of_mem_ker_unramified l Ω e S A W hN
  have hc := DualCont.continuous_galoisRepRankTwoTateDual l Ω e S A W hN
  haveI := finite_cocycles_restricted_rep S hL c n (dual1 W) hD hK hc hN.above
  refine ⟨Nat.card (Z1 (repS S c n (dual1 W) hD hK)), fun N z hz hne => ?_⟩
  have hint : ∀ i s k, z i s k ∈ c.O := fun i => (hz i).1.2.1
  have hcont : ∀ i, Continuous (z i) := fun i => by
    have h := (hz i).1.1
    rwa [Subgroup.coe_top, continuousOn_univ] at h
  have hcoc : ∀ i s t, Cv n (z i (s * t)) (z i s + mat (dual1 W) s *ᵥ z i t) :=
    fun i s t => (hz i).1.2.2 s (Subgroup.mem_top s) t (Subgroup.mem_top t)
  let f : Fin N → Z1 (repS S c n (dual1 W) hD hK) := fun i =>
    ⟨zbar S c n (z i) (hint i),
      zbar_mem S c n (dual1 W) hD hK (z i) (hint i) (hcont i) (hcoc i) (hz i).2⟩
  have hf : Function.Injective f := by
    intro i j hij
    by_contra hij'
    apply hne i j hij'
    refine ⟨0, fun _ => zero_mem _, fun s _ => ?_⟩
    have h1 := congrArg (fun y : Z1 (repS S c n (dual1 W) hD hK) => y.1 (QuotientGroup.mk s)) hij
    simp only [f, zbar_mk S c n (dual1 W) hD (z i) (hint i) (hcoc i) (hz i).2,
      zbar_mk S c n (dual1 W) hD (z j) (hint j) (hcoc j) (hz j).2] at h1
    have h2 := (zr_eq_iff c n (z i) (z j) (hint i) (hint j) s).1 h1
    intro k
    have h3 := h2 k
    simpa [Cg] using h3
  simpa using Nat.card_le_card_of_injective f hf

end GlobalTheory.Ord2.GwFin
