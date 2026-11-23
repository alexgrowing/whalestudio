import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsStandardIndModule

open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagLeviGroup GlobalTheory.GKModule GlobalTheory.RealInd
open scoped InnerProductSpace

namespace GlobalTheory.LeviProj

theorem exists_proj_of_closed {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] (P N M A : Subgroup G) (cP : IsClosed (P : Set G))
    (cN : IsClosed (N : Set G)) (cM : IsClosed (M : Set G)) (cA : IsClosed (A : Set G)) (hN : N ≤ P) (hM : M ≤ P)
    (hA : A ≤ P) (norm : ∀ p ∈ P, ∀ u ∈ N, p * u * p⁻¹ ∈ N) (comm : ∀ m ∈ M, ∀ t ∈ A, m * t = t * m)
    (inj : ∀ m ∈ M, ∀ t ∈ A, m * t ∈ N → m = 1 ∧ t = 1)
    (surj : ∀ p ∈ P, ∃ u ∈ N, ∃ m ∈ M, ∃ t ∈ A, p = u * m * t) :
    ∃ μ : G → G, ContinuousOn μ (P : Set G) ∧ (∀ p ∈ P, μ p ∈ M) ∧ (∀ p ∈ P, ∀ q ∈ P, μ (p * q) = μ p * μ q) ∧
      ∀ u ∈ N, ∀ m ∈ M, ∀ t ∈ A, μ (u * m * t) = m := by
  classical
  haveI : LocallyCompactSpace P := cP.locallyCompactSpace
  haveI : LocallyCompactSpace M := cM.locallyCompactSpace
  haveI : LocallyCompactSpace A := cA.locallyCompactSpace
  let N' : Subgroup P := N.subgroupOf P
  haveI : N'.Normal := ⟨fun u hu p => norm p p.2 u hu⟩
  haveI : IsClosed (N' : Set P) := cN.preimage continuous_subtype_val
  let ψ : M × A →* P := (Subgroup.inclusion hM).noncommCoprod (Subgroup.inclusion hA)
    fun m t => Subtype.ext (comm m m.2 t t.2)
  have hψ : ∀ z : M × A, (ψ z : G) = z.1 * z.2 := fun z => rfl
  let φ : M × A →* P ⧸ N' := (QuotientGroup.mk' N').comp ψ
  have cφ : Continuous φ := by
    refine QuotientGroup.continuous_mk.comp (Continuous.subtype_mk ?_ _)
    change Continuous fun z : M × A => (z.1 : G) * z.2
    exact (continuous_subtype_val.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)
  have key : ∀ u ∈ N, ∀ (m : M) (t : A) (h : u * m * t ∈ P), φ (m, t) = (⟨_, h⟩ : P) := fun u hu m t h => by
    refine QuotientGroup.eq.2 ?_
    change ((m : G) * t)⁻¹ * (u * m * t) ∈ N
    have := norm _ (P.inv_mem (P.mul_mem (hM m.2) (hA t.2))) u hu
    rwa [inv_inv, mul_assoc, ← mul_assoc u] at this
  have sφ : Function.Surjective φ := fun q => by
    obtain ⟨⟨p, hp⟩, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨u, hu, m, hm, t, ht, rfl⟩ := surj p hp
    exact ⟨_, key u hu ⟨m, hm⟩ ⟨t, ht⟩ hp⟩
  have iφ : Function.Injective φ := (injective_iff_map_eq_one φ).2 fun z hz => by
    have := inj z.1 z.1.2 z.2 z.2.2 ((QuotientGroup.eq_one_iff (N := N') (ψ z)).1 hz)
    exact Prod.ext (Subtype.ext this.1) (Subtype.ext this.2)
  let e := MulEquiv.ofBijective φ ⟨iφ, sφ⟩
  have ce : Continuous e.symm :=
    (e.toEquiv.toHomeomorphOfContinuousOpen cφ (φ.isOpenMap_of_sigmaCompact sφ cφ)).symm.continuous
  refine ⟨fun g => if h : g ∈ P then (e.symm (⟨g, h⟩ : P)).1 else 1, ?_, fun p hp => ?_, fun p hp q hq => ?_,
    fun u hu m hm t ht => ?_⟩
  · rw [continuousOn_iff_continuous_restrict]
    have : Continuous fun p : P => ((e.symm p).1 : G) :=
      continuous_subtype_val.comp (continuous_fst.comp (ce.comp QuotientGroup.continuous_mk))
    exact this.congr fun p => by simp
  · simp only [dif_pos hp, SetLike.coe_mem]
  · simp only [dif_pos hp, dif_pos hq, dif_pos (P.mul_mem hp hq)]
    rw [← Subgroup.coe_mul, ← Prod.fst_mul, ← map_mul]
    rfl
  · have h : u * m * t ∈ P := P.mul_mem (P.mul_mem (hN hu) (hM hm)) (hA ht)
    simp only [dif_pos h]
    rw [e.symm_apply_eq.2 (key u hu ⟨m, hm⟩ ⟨t, ht⟩ h).symm]

variable {n a : ℕ} {ε : Fin n → Bool} {j : Fin a → ℕ} {W : Flag n a}

theorem conj_scalar {p g : UJ ε} {U' : Submodule ℂ (Fin n → ℂ)} {c : ℂ} {y : Fin n → ℂ}
    (hp : ∀ y ∈ U', uMat p *ᵥ y ∈ U') (h : uMat g *ᵥ (uMat p⁻¹ *ᵥ y) - c • (uMat p⁻¹ *ᵥ y) ∈ U') :
    uMat (p * g * p⁻¹) *ᵥ y - c • y ∈ U' := by
  have := hp _ h
  rwa [mulVec_sub, mulVec_smul, mulVec_mulVec, mulVec_mulVec, mulVec_mulVec, GlobalTheory.RealIwasawa.uMat_mul_inv,
    one_mulVec] at this

theorem keeps_orth {p : UJ ε} {U : Submodule ℂ (Fin n → ℂ)} (hp : ∀ y ∈ U, uMat p *ᵥ y ∈ U) {y : Fin n → ℂ}
    (hy : ∀ z ∈ U, star z ⬝ᵥ (Jm ε *ᵥ y) = 0) : ∀ z ∈ U, star z ⬝ᵥ (Jm ε *ᵥ (uMat p⁻¹ *ᵥ y)) = 0 := fun z hz => by
  have e := conjTranspose_inv_mul_Jm p⁻¹
  rw [inv_inv] at e
  rw [mulVec_mulVec, ← e, ← mulVec_mulVec, dotProduct_mulVec, ← star_mulVec]
  exact hy _ (hp z hz)

theorem conj_mem_flagN {p u : UJ ε} (hp : p ∈ parab ε W) (hu : u ∈ flagN ε W) : p * u * p⁻¹ ∈ flagN ε W := by
  have hq := (parab ε W).inv_mem hp
  refine ⟨fun i y hy => ?_, fun y hy => ?_⟩
  · simpa using conj_scalar (c := 1) (hp _) (by simpa using hu.1 i _ (hq _ y hy))
  · simpa using conj_scalar (c := 1) (hp _) (by simpa using hu.2 _ (keeps_orth (hp _) hy))

theorem comm_of_isSplit (hW : IsIsoFlag ε j W) {l t : UJ ε} {x : Fin a → ℝ} (hl : l ∈ flagM ε W)
    (ht : IsSplit ε W x t) : l * t = t * l := by
  have hp : l ∈ parab ε W := fun i y hy => (hl i y hy).1
  have hq := (parab ε W).inv_mem hp
  have : IsSplit ε W x (l * t * l⁻¹) := by
    refine ⟨(leviSub ε W).mul_mem ((leviSub ε W).mul_mem hl ht.1) ((leviSub ε W).inv_mem hl), fun i y hy => ?_,
      fun y hy => ?_⟩
    · exact conj_scalar (hp _) (ht.2.1 i _ (hq _ y hy))
    · simpa using conj_scalar (c := 1) (hp _) (by simpa using ht.2.2 _ (keeps_orth (hp _) hy))
  exact mul_inv_eq_iff_eq_mul.1 ((existsUnique_isSplit hW x).unique this ht)

theorem exists_leviOne_part : ∀ (n a : ℕ) (ε : Fin n → Bool) (j : Fin a → ℕ) (W : Flag n a), IsIsoFlag ε j W →
    (∀ i, 1 ≤ j i) →
    ∃ μ : UJ ε → UJ ε, ContinuousOn μ (parab ε W : Set (UJ ε)) ∧ (∀ p ∈ parab ε W, μ p ∈ leviOne ε W) ∧
      (∀ p ∈ parab ε W, ∀ q ∈ parab ε W, μ (p * q) = μ p * μ q) ∧
      ∀ u ∈ flagN ε W, ∀ m ∈ leviOne ε W, ∀ (x : Fin a → ℝ) (t : UJ ε), IsSplit ε W x t →
        u * m * t ∈ parab ε W ∧ μ (u * m * t) = m := by
  intro n a ε j W hW hj
  obtain ⟨⟨N, eN⟩, cN, kN⟩ := UnipRad.flagN_subgroup_closed_keeps n ε a j W hW
  have mN : ∀ {u}, u ∈ N ↔ u ∈ flagN ε W := fun {u} => by rw [← eN]; rfl
  obtain ⟨h, hc, h1, -, hh⟩ := exists_height hW hj
  have hx : ∀ m ∈ leviOne ε W, ∀ x t, IsSplit ε W x t → h (m * t) = x := fun m hm x t ht => by
    simpa [h1] using hh 1 (mN.1 N.one_mem) m hm x t ht 1
  let A : Subgroup (UJ ε) :=
    { carrier := {t | ∃ x, IsSplit ε W x t}
      one_mem' := ⟨0, isSplit_one⟩
      mul_mem' := fun ⟨_, h⟩ ⟨_, h'⟩ => ⟨_, h.mul h'⟩
      inv_mem' := fun {t} ⟨x, h⟩ => by
        obtain ⟨t', h', -⟩ := existsUnique_isSplit hW (-x)
        have := h.mul h'
        rw [add_neg_cancel] at this
        exact ⟨_, inv_eq_of_mul_eq_one_right ((existsUnique_isSplit hW 0).unique this isSplit_one) ▸ h'⟩ }
  have cA : IsClosed (A : Set (UJ ε)) := by
    have : (A : Set (UJ ε)) = {t | IsSplit ε W (h t) t} := by
      ext t
      refine ⟨fun ⟨x, ht⟩ => ?_, fun ht => ⟨_, ht⟩⟩
      have := hx 1 (one_mem _) x t ht
      rw [one_mul] at this
      rwa [Set.mem_ofPred_eq, this]
    rw [this]
    simp only [IsSplit, Set.ofPred_and, Set.ofPred_forall]
    refine (isClosed_flagM W).inter (IsClosed.inter ?_ ?_)
    · exact isClosed_iInter fun i => isClosed_iInter fun y => isClosed_iInter fun _ =>
        (W _).closed_of_finiteDimensional.preimage
          ((continuous_uMat.matrix_mulVec continuous_const).sub (by fun_prop))
    · exact isClosed_iInter fun y => isClosed_iInter fun _ =>
        (W _).closed_of_finiteDimensional.preimage
          ((continuous_uMat.matrix_mulVec continuous_const).sub continuous_const)
  have hN : N ≤ parab ε W := fun u hu => kN u (mN.1 hu)
  have hM : leviOne ε W ≤ parab ε W := fun m hm i y hy => (hm.1 i y hy).1
  have hA : A ≤ parab ε W := fun t ⟨_, ht⟩ i y hy => (ht.1 i y hy).1
  obtain ⟨μ, c, m1, m2, m3⟩ := exists_proj_of_closed (parab ε W) N (leviOne ε W) A isClosed_parab (eN ▸ cN)
    (isClosed_leviOne hW hj) cA hN hM hA (fun p hp u hu => mN.2 (conj_mem_flagN hp (mN.1 hu)))
    (fun m hm t ⟨_, ht⟩ => comm_of_isSplit hW hm.1 ht)
    (fun m hm t ⟨x, ht⟩ hu => by
      have e : m * t = 1 := GlobalTheory.RealIwasawa.eq_one_of_mul_mem_compact hW _ (mN.1 hu) _
        ((leviSub ε W).inv_mem ((leviSub ε W).mul_mem hm.1 ht.1))
        (by rw [mul_inv_cancel]; exact (compactSub ε).one_mem)
      have := hx m hm x t ht
      rw [e, h1] at this
      have e' : t = 1 := (existsUnique_isSplit hW x).unique ht (this ▸ isSplit_one)
      exact ⟨by simpa [e'] using e, e'⟩)
    (fun p hp => by
      obtain ⟨u, hu, m, hm, x, t, ht, rfl⟩ := exists_langlands_decomp hW hj hp
      exact ⟨u, mN.2 hu, m, hm, t, ⟨x, ht⟩, rfl⟩)
  exact ⟨μ, c, m1, m2, fun u hu m hm x t ht => ⟨mul_mem (mul_mem (hN (mN.2 hu)) (hM hm)) (hA ⟨x, ht⟩),
    m3 u (mN.2 hu) m hm t ⟨x, ht⟩⟩⟩

end GlobalTheory.LeviProj
