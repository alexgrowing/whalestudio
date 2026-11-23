import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SelNZero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CupProductDualTwistIsTwoCocycleUnramified
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CupProductCoboundaryMod
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemIntegersOfNormLeOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoLevFacts
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

noncomputable section

namespace GlobalTheory.Ord2.TorsBound

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

theorem natCast_ne_zero' : ((l : ℕ) : Qbar l) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero

theorem norm_mul_pow_le_iff (k j : ℕ) (a : Qbar l) :
    ‖((l : ℕ) : Qbar l) ^ k * a‖ ≤ ‖((l : ℕ) : Qbar l) ^ (k + j)‖ ↔ ‖a‖ ≤ ‖((l : ℕ) : Qbar l) ^ j‖ := by
  rw [norm_mul, pow_add, norm_mul]
  have : 0 < ‖((l : ℕ) : Qbar l) ^ k‖ := norm_pos_iff.2 (pow_ne_zero _ natCast_ne_zero')
  exact mul_le_mul_iff_of_pos_left this

theorem cv_of_smul {k m : ℕ} {a b w w' : Fin 2 → Qbar l} (h : ((l : ℕ) : Qbar l) ^ k • (a - b) = w - w')
    (hw : Cv (k + m) w w') : Cv m a b := fun i => by
  have e := congrFun h i
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at e
  have := hw i
  unfold Cg at this ⊢
  rw [← e] at this
  exact (norm_mul_pow_le_iff k m _).1 this

theorem cv_smul {k m : ℕ} {a b w w' : Fin 2 → Qbar l} (h : ((l : ℕ) : Qbar l) ^ k • (a - b) = w - w')
    (hab : Cv m a b) : Cv (k + m) w w' := fun i => by
  have e := congrFun h i
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at e
  have := hab i
  unfold Cg at this ⊢
  rw [← e]
  exact (norm_mul_pow_le_iff k m _).2 this

theorem mem_of_mul (c : Coef l) (k : ℕ) {a : Qbar l} (ha : ((l : ℕ) : Qbar l) ^ k * a ∈ c.O) (hn : ‖a‖ ≤ 1) :
    a ∈ c.O :=
  mem_coefO_of_memE_norm_le_one l c a ⟨k, ha⟩ hn

theorem exists_cls (c : Coef l) (m : ℕ) : ∃ (T : Type) (_ : Fintype T) (cls : (Fin 2 → c.O) → T),
    ∀ x y, cls x = cls y → ∀ j, ‖((x j : c.O) : Qbar l) - (y j : Qbar l)‖ ≤ ‖((l : ℕ) : Qbar l) ^ m‖ := by
  have hl0 : ((l : ℕ) : c.O) ^ m ≠ 0 := pow_ne_zero _ (by
    intro h
    have h' : (((l : ℕ) : c.O) : PadicAlgCl l) = 0 := by rw [h]; rfl
    exact natCast_ne_zero' (by simpa using h'))
  haveI hfin := (UpperTheory.V.X.So.levFacts l c.O _ hl0 (c.O ⧸ Ideal.span {((l : ℕ) : c.O) ^ m})
    ⟨LinearEquiv.refl _ _⟩).1
  refine ⟨Fin 2 → c.O ⧸ Ideal.span {((l : ℕ) : c.O) ^ m}, Fintype.ofFinite _,
    fun x j => Ideal.Quotient.mk _ (x j), ?_⟩
  intro x y h j
  have h1 := congrFun h j
  simp only at h1
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton] at h1
  obtain ⟨w, hw⟩ := h1
  have e : ((x j : c.O) : Qbar l) - (y j : Qbar l) = ((l : ℕ) : Qbar l) ^ m * (w : Qbar l) := by
    have := congrArg (fun z : c.O => (z : Qbar l)) hw
    simpa using this
  rw [e, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (norm_le_one_of_mem_coefO c w)

def cobd (V : R2 Ω l) (s : G ℚ Ω) : (Fin 2 → Qbar l) →ₗ[Qbar l] (Fin 2 → Qbar l) :=
  Matrix.mulVecLin (mat V s) - LinearMap.id

theorem cobd_apply (V : R2 Ω l) (s : G ℚ Ω) (y : Fin 2 → Qbar l) : cobd V s y = mat V s *ᵥ y - y := rfl

theorem cobd_mul (V : R2 Ω l) (s t : G ℚ Ω) (y : Fin 2 → Qbar l) :
    cobd V (s * t) y = cobd V s y + mat V s *ᵥ cobd V t y := by
  simp only [cobd_apply, mat_mul', ← Matrix.mulVec_mulVec, Matrix.mulVec_sub]
  abel

end GlobalTheory.Ord2.TorsBound

namespace GlobalTheory.Ord2.TorsBound

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

def lift (V : R2 Ω l) (m k : ℕ) (z : G ℚ Ω → Fin 2 → Qbar l) (x : Fin 2 → Qbar l) (s : G ℚ Ω) : Fin 2 → Qbar l :=
  (((l : ℕ) : Qbar l) ^ k)⁻¹ • (z s - cobd V s ((((l : ℕ) : Qbar l) ^ m)⁻¹ • x))

theorem smul_lift (V : R2 Ω l) (m k : ℕ) (z : G ℚ Ω → Fin 2 → Qbar l) (x : Fin 2 → Qbar l) (s : G ℚ Ω) :
    ((l : ℕ) : Qbar l) ^ k • lift V m k z x s = z s - cobd V s ((((l : ℕ) : Qbar l) ^ m)⁻¹ • x) :=
  smul_inv_smul₀ (pow_ne_zero _ natCast_ne_zero') _

theorem smul_diff (V : R2 Ω l) (m : ℕ) (z : G ℚ Ω → Fin 2 → Qbar l) (x : Fin 2 → Qbar l) (s : G ℚ Ω) :
    ((l : ℕ) : Qbar l) ^ m • (z s - cobd V s ((((l : ℕ) : Qbar l) ^ m)⁻¹ • x)) =
      ((l : ℕ) : Qbar l) ^ m • z s - cobd V s x := by
  rw [smul_sub, ← map_smul, smul_inv_smul₀ (pow_ne_zero _ natCast_ne_zero')]

variable (c : Coef l) (V : R2 Ω l) (m k : ℕ) (z : G ℚ Ω → Fin 2 → Qbar l) (x : Fin 2 → Qbar l)

theorem lift_mem (hVO : ∀ s i j, mat V s i j ∈ c.O) (hz : ∀ s i, z s i ∈ c.O) (hx : ∀ i, x i ∈ c.O)
    (hxc : ∀ s, Cv (m + k) (((l : ℕ) : Qbar l) ^ m • z s) (cobd V s x)) (s : G ℚ Ω) (j : Fin 2) :
    lift V m k z x s j ∈ c.O := by
  have hL : ((l : ℕ) : Qbar l) ∈ c.O := by
    have : ((l : ℕ) : Qbar l) = algebraMap ℤ_[l] (Qbar l) (l : ℤ_[l]) := by simp
    rw [this]; exact c.O.algebraMap_mem _
  have hD : ‖(z s - cobd V s ((((l : ℕ) : Qbar l) ^ m)⁻¹ • x)) j‖ ≤ ‖((l : ℕ) : Qbar l) ^ k‖ := by
    have e := congrFun (smul_diff V m z x s) j
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at e
    apply (norm_mul_pow_le_iff m k _).1
    simp only [Pi.sub_apply]
    rw [e]
    have := hxc s j
    unfold Cg at this
    simpa using this
  have e2 := congrFun (smul_lift V m k z x s) j
  simp only [Pi.smul_apply, smul_eq_mul] at e2
  have hn : ‖lift V m k z x s j‖ ≤ 1 := by
    have := (norm_mul_pow_le_iff k 0 (lift V m k z x s j)).1 (by rw [e2, add_zero]; exact hD)
    simpa using this
  refine mem_of_mul c (m + k) ?_ hn
  have e3 := congrFun (smul_diff V m z x s) j
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at e3
  rw [pow_add, mul_assoc, e2]
  simp only [Pi.sub_apply] at e3 ⊢
  rw [mul_sub] at e3 ⊢
  rw [e3, cobd_apply]
  refine c.O.sub_mem (c.O.mul_mem (c.O.pow_mem hL _) (hz s j)) (c.O.sub_mem ?_ (hx j))
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  exact c.O.add_mem (c.O.mul_mem (hVO _ _ _) (hx _)) (c.O.mul_mem (hVO _ _ _) (hx _))

theorem lift_coc (hz : ∀ s t, Cv (m + k) (z (s * t)) (z s + mat V s *ᵥ z t)) (s t : G ℚ Ω) :
    Cv m (lift V m k z x (s * t)) (lift V m k z x s + mat V s *ᵥ lift V m k z x t) := by
  refine cv_of_smul (k := k) (w := z (s * t)) (w' := z s + mat V s *ᵥ z t) ?_ (by rw [add_comm]; exact hz s t)
  rw [smul_sub, smul_add, ← Matrix.mulVec_smul, smul_lift, smul_lift, smul_lift, cobd_mul, Matrix.mulVec_sub]
  abel

theorem lift_ker (a : G ℚ Ω) (ha : mat V a = 1) (hz : Cv (m + k) (z a) 0) : Cv m (lift V m k z x a) 0 := by
  refine cv_of_smul (k := k) (w := z a) (w' := 0) ?_ (by rw [add_comm]; exact hz)
  rw [sub_zero, sub_zero, smul_lift, cobd_apply, ha, Matrix.one_mulVec, sub_self, sub_zero]

theorem cob_of_lift (hVO : ∀ s i j, mat V s i j ∈ c.O) (z' : G ℚ Ω → Fin 2 → Qbar l) (x' : Fin 2 → Qbar l)
    (hx : ∀ i, x i ∈ c.O) (hx' : ∀ i, x' i ∈ c.O) (hd : ∀ j, ‖x j - x' j‖ ≤ ‖((l : ℕ) : Qbar l) ^ m‖)
    (h : Cob1 c m V ⊤ (lift V m k z x - lift V m k z' x')) : Cob1 c (m + k) V ⊤ (z - z') := by
  obtain ⟨v, hvO, hv⟩ := h
  set d : Fin 2 → Qbar l := (((l : ℕ) : Qbar l) ^ m)⁻¹ • (x - x') with hd'
  have hL : ((l : ℕ) : Qbar l) ∈ c.O := by
    have : ((l : ℕ) : Qbar l) = algebraMap ℤ_[l] (Qbar l) (l : ℤ_[l]) := by simp
    rw [this]; exact c.O.algebraMap_mem _
  have hdO : ∀ j, d j ∈ c.O := by
    intro j
    have e : ((l : ℕ) : Qbar l) ^ m * d j = x j - x' j := by
      simp only [hd', Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ natCast_ne_zero'), one_mul]
    refine mem_of_mul c m (by rw [e]; exact c.O.sub_mem (hx j) (hx' j)) ?_
    have := (norm_mul_pow_le_iff m 0 (d j)).1 (by rw [e, add_zero]; exact hd j)
    simpa using this
  refine ⟨d + ((l : ℕ) : Qbar l) ^ k • v, fun j => c.O.add_mem (hdO j) ?_, fun s _ => ?_⟩
  · simp only [Pi.smul_apply, smul_eq_mul]; exact c.O.mul_mem (c.O.pow_mem hL _) (hvO j)
  have hs := hv s (Subgroup.mem_top s)
  rw [add_comm m k]
  refine cv_smul (a := (lift V m k z x - lift V m k z' x') s) (b := mat V s *ᵥ v - v) ?_ hs
  have e1 : (((l : ℕ) : Qbar l) ^ m)⁻¹ • x = (((l : ℕ) : Qbar l) ^ m)⁻¹ • x' + d := by
    rw [hd', smul_sub]; abel
  have e2 := smul_lift V m k z x s
  have e3 := smul_lift V m k z' x' s
  rw [e1, map_add] at e2
  simp only [Pi.sub_apply, smul_sub]
  rw [e2, e3, ← cobd_apply V s (d + _), map_add, cobd_apply V s (_ • v), Matrix.mulVec_smul]
  abel

end GlobalTheory.Ord2.TorsBound

namespace GlobalTheory.Ord2.TorsBound

open GlobalTheory.Ord2.GwCount

theorem tors_bound : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ c : Coef l, (∀ s i j, mat W s i j ∈ c.O) → (∀ n : ℕ, ∃ B : ℕ, ∀ (N : ℕ) (z : Fin N → G ℚ Ω → Fin 2 → Qbar l), (∀ i, Coc1 c n (dual1 W) ⊤ (z i) ∧ ∀ a ∈ (toGS Ω (S : Set Pl)).ker, Cv n (z i a) 0) → (∀ i j, i ≠ j → ¬ Cob1 c n (dual1 W) ⊤ (z i - z j)) → N ≤ B) → ∀ m : ℕ, ∃ B : ℕ, ∀ (n N : ℕ) (z : Fin N → G ℚ Ω → Fin 2 → Qbar l), (∀ i, GwCount.SelN c n S A (dual1 W) (z i)) → (∀ i j, i ≠ j → ¬ Cob1 c n (dual1 W) ⊤ (z i - z j)) → (∀ i, Cob1 c n (dual1 W) ⊤ (fun s => ((l : ℕ) : Qbar l) ^ m • z i s)) → N ≤ B := by
  intro l _ Ω _ _ _ e S A W hW c hWc hyp m
  choose Bf hBf using hyp
  have hVc : Continuous fun s => mat (dual1 W) s := continuous_mat_dual1 W hW.cont hW.det2
  have hVO : ∀ s i j, mat (dual1 W) s i j ∈ c.O := CupCob.dual_representation_integral c W hW.det2 hWc
  have hDI : ∀ w, w ∉ S → ∀ B : ValuationSubring Ω, IsPlaceOver B w → Ine (F := ℚ) B ≤ (dual1 W).ker := by
    intro w hw B hB σ hσ
    have h1 : W σ = 1 := hW.unr w hw B hB hσ
    have hm : mat W σ = 1 := by simp [mat, h1]
    have he : eps l σ = 1 := eps_eq_one_of_mem_Ine (fun h => hw (hW.above w h)) hB hσ
    show dual1 W σ = 1
    apply Units.ext
    show mat (dual1 W) σ = 1
    rw [mat_dual1_eq' W hW.det2, hm, he, Matrix.det_one, mul_one, one_smul]
  have hVK : ∀ a ∈ (toGS Ω (S : Set Pl)).ker, mat (dual1 W) a = 1 := by
    intro a ha
    have hker : (toGS Ω (S : Set Pl)).ker = NS Ω (S : Set Pl) := QuotientGroup.ker_mk' _
    rw [hker] at ha
    have hU : Unr (dual1 W) (0 : G ℚ Ω → Fin 2 → Qbar l) := fun w _ =>
      ⟨placeOf Ω w, isPlaceOver_placeOf Ω w, 0, fun s _ => by simp⟩
    exact (vanish_NS hW.above (dual1 W) hVc (Submodule.zero_mem _) hU hDI a ha).1
  obtain ⟨T, _, cls, hcls⟩ := exists_cls c m
  refine ⟨max ((Finset.range m).sup Bf) (Fintype.card T * Bf m), ?_⟩
  intro n N z hz hnc hcob
  by_cases hnm : n < m
  · exact (hBf n N z (fun i => ⟨(hz i).1, (hz i).2.1⟩) hnc).trans
      ((Finset.le_sup (f := Bf) (Finset.mem_range.2 hnm)).trans (le_max_left _ _))
  push_neg at hnm
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
  refine le_trans ?_ (le_max_right _ _)
  choose x hxO hx using hcob
  by_contra hlt
  push_neg at hlt
  let f : Fin N → T := fun i => cls (fun j => ⟨x i j, hxO i j⟩)
  classical
  obtain ⟨t, ht⟩ := Fintype.exists_lt_card_fiber_of_mul_lt_card f (by rw [Fintype.card_fin]; exact hlt)
  set F := Finset.univ.filter (fun i => f i = t) with hF
  let emb : Fin F.card → Fin N := fun k => (F.equivFin.symm k : Fin N)
  have hemb : ∀ a, f (emb a) = t := fun a => (Finset.mem_filter.1 (F.equivFin.symm a).2).2
  have hinj : Function.Injective emb := fun a b h => F.equivFin.symm.injective (Subtype.ext h)
  have hzc : ∀ i, Continuous (z i) := fun i => by
    have := (hz i).1.1
    rw [Subgroup.coe_top] at this
    exact continuousOn_univ.1 this
  have key := hBf m F.card (fun a => lift (dual1 W) m k (z (emb a)) (x (emb a))) ?_ ?_
  · omega
  · intro a
    refine ⟨⟨?_, fun s j => lift_mem c (dual1 W) m k _ _ hVO (hz (emb a)).1.2.1 (hxO (emb a))
      (fun s => hx (emb a) s (Subgroup.mem_top s)) s j,
      fun s _ t _ => lift_coc (dual1 W) m k _ _ (fun s t => (hz (emb a)).1.2.2 s (Subgroup.mem_top s) t
        (Subgroup.mem_top t)) s t⟩, fun b hb => lift_ker (dual1 W) m k _ _ b (hVK b hb) ((hz (emb a)).2.1 b hb)⟩
    apply Continuous.continuousOn
    show Continuous fun s => (((l : ℕ) : Qbar l) ^ k)⁻¹ • (z (emb a) s - (mat (dual1 W) s *ᵥ ((((l : ℕ) : Qbar l) ^ m)⁻¹ • x (emb a)) - (((l : ℕ) : Qbar l) ^ m)⁻¹ • x (emb a)))
    exact ((hzc _).sub ((hVc.matrix_mulVec continuous_const).sub continuous_const)).const_smul ((((l : ℕ) : Qbar l) ^ k)⁻¹)
  · intro a b hab hcob
    refine hnc (emb a) (emb b) (fun h => hab (hinj h)) ?_
    refine cob_of_lift c (dual1 W) m k (z (emb a)) (x (emb a)) hVO (z (emb b)) (x (emb b)) (hxO _) (hxO _) ?_ hcob
    have := hcls _ _ ((hemb a).trans (hemb b).symm)
    simpa using this

end GlobalTheory.Ord2.TorsBound
