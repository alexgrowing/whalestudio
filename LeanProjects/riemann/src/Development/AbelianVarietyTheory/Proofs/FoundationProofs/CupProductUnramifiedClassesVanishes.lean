import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CupProductCoboundaryMod
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TwoCocycleModPowCoboundaryOfFrobeniusSplitStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OpenSubgroupCochainInvarianceStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFrobeniusPowInvMulMemOpenSubgroupStatement

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

noncomputable section

namespace GlobalTheory.Ord2.UnrCup

theorem ident_c {l : ℕ} [Fact l.Prime] (ar as ars bs bt bst : Fin 2 → Qbar l) (P M N : Matrix (Fin 2) (Fin 2) (Qbar l)) (e : Qbar l)
    (key : om (P *ᵥ as) (M *ᵥ (N *ᵥ bt)) = e * om as (N *ᵥ bt)) :
    (e * om as (N *ᵥ bt) + om ar (M *ᵥ bst)) - (om ars (M *ᵥ (N *ᵥ bt)) + om ar (M *ᵥ bs)) =
      om ar (M *ᵥ (bst - (bs + N *ᵥ bt))) - om (ars - (ar + P *ᵥ as)) (M *ᵥ (N *ᵥ bt)) := by
  simp only [om, Matrix.mulVec_sub, Matrix.mulVec_add, Pi.sub_apply, Pi.add_apply] at *
  linear_combination -key

theorem inv_ine : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (c : Coef l) (n : ℕ) (V : R2 Ω l) (H I : Subgroup (G ℚ Ω)) (a : G ℚ Ω → Fin 2 → Qbar l), (∀ s i j, mat V s i j ∈ c.O) → I ≤ H → (∀ s ∈ H, ∀ i ∈ I, s⁻¹ * i * s ∈ I) → Coc1 c n V H a → (∀ i ∈ I, Cv n (a i) 0) → ∀ s ∈ H, ∀ i ∈ I, Cv n (a (s * i)) (a s) ∧ Cv n (mat V i *ᵥ a s) (a s) := by
  intro l _ Ω _ _ c n V H I a hint hIH hconj ha ha0
  have hVn : ∀ g i j, ‖mat V g i j‖ ≤ 1 := fun g i j => CupCob.norm_le_one_of_mem c (hint g i j)
  have small : ∀ g, ∀ i ∈ I, ∀ j, ‖(mat V g *ᵥ a i) j‖ ≤ ‖((l : ℕ) : Qbar l) ^ n‖ := fun g i hi =>
    CupCob.mulVec_le _ _ (hVn g) (fun k => by have := ha0 i hi k; unfold Cg at this; simpa using this)
  have first : ∀ s ∈ H, ∀ i ∈ I, Cv n (a (s * i)) (a s) := by
    intro s hs i hi j
    have h1 := ha.2.2 s hs i (hIH hi) j
    unfold Cg at h1 ⊢
    have e : a (s * i) j - a s j = (a (s * i) j - (a s + mat V s *ᵥ a i) j) + (mat V s *ᵥ a i) j := by
      simp only [Pi.add_apply]; ring
    rw [e]; exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 (small s i hi j))
  intro s hs i hi
  refine ⟨first s hs i hi, fun j => ?_⟩
  have hi' : s⁻¹ * i * s ∈ I := hconj s hs i hi
  have e1 : i * s = s * (s⁻¹ * i * s) := by group
  have h1 := ha.2.2 i (hIH hi) s hs j
  have h2 := first s hs _ hi' j
  have h3 := ha0 i hi j
  unfold Cg at h1 h2 h3 ⊢
  rw [e1] at h1
  have e : (mat V i *ᵥ a s) j - a s j = -(a (s * (s⁻¹ * i * s)) j - (a i + mat V i *ᵥ a s) j) - (a i j - (0 : Fin 2 → Qbar l) j) + (a (s * (s⁻¹ * i * s)) j - a s j) := by
    simp only [Pi.add_apply, Pi.zero_apply]; ring
  rw [e]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ((CupCob.nsub_le_max _ _).trans (max_le (by rw [norm_neg]; exact h1) h3)) h2)

theorem cup_coc : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (c : Coef l) (n : ℕ) (W : R2 Ω l) (H : Subgroup (G ℚ Ω)) (a b : G ℚ Ω → Fin 2 → Qbar l), (∀ s i j, mat W s i j ∈ c.O) → dt W ^ 2 = 1 → Coc1 c n W H a → Coc1 c n (dual1 W) H b → ∀ r ∈ H, ∀ s ∈ H, ∀ t ∈ H, Cg n (eps l r * cup W a b s t + cup W a b r (s * t)) (cup W a b (r * s) t + cup W a b r s) := by
  intro l _ Ω _ _ c n W H a b hint hdet ha hb r hr s hs t ht
  have hDm := CupCob.dual_representation_integral c W hdet hint
  have hDn : ∀ g i j, ‖mat (dual1 W) g i j‖ ≤ 1 := fun g i j => CupCob.norm_le_one_of_mem c (hDm g i j)
  have key := CupCob.om_key W hdet r (a s) (mat (dual1 W) s *ᵥ b t)
  unfold Cg
  simp only [cup]
  rw [CupCob.mat_dual1_mul W r s (b t), ident_c (a r) (a s) (a (r * s)) (b s) (b t) (b (s * t)) (mat W r)
    (mat (dual1 W) r) (mat (dual1 W) s) (eps l r) key]
  refine (CupCob.nsub_le_max _ _).trans (max_le ?_ ?_)
  · exact CupCob.om_le_right _ _ (fun i => CupCob.norm_le_one_of_mem c (ha.2.1 r i))
      (CupCob.mulVec_le _ _ (hDn r) (fun i => hb.2.2 s hs t ht i))
  · exact CupCob.om_le_left _ _ (fun i => ha.2.2 r hr s hs i) (CupCob.mulVec_le _ _ (hDn r)
      (CupCob.mulVec_le _ _ (hDn s) (fun i => CupCob.norm_le_one_of_mem c (hb.2.1 t i))))

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

theorem cg_add {n : ℕ} {a b a' b' : Qbar l} (h : Cg n a b) (h' : Cg n a' b') : Cg n (a + a') (b + b') := by
  unfold Cg at *
  have e : a + a' - (b + b') = (a - b) + (a' - b') := by ring
  rw [e]; exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h h')

theorem cv_sub {n : ℕ} {a b a' b' : Fin 2 → Qbar l} (h : Cv n a b) (h' : Cv n a' b') : Cv n (a - a') (b - b') := by
  intro i
  unfold Cg at *
  have e : (a - a') i - (b - b') i = (a i - b i) - (a' i - b' i) := by simp only [Pi.sub_apply]; ring
  rw [e]; exact (CupCob.nsub_le_max _ _).trans (max_le (h i) (h' i))

theorem isIntegralCoboundaryTwoModPow_add (c : Coef l) (n : ℕ) (H : Subgroup (G ℚ Ω)) (ξ ξ' : G ℚ Ω → G ℚ Ω → Qbar l)
    (h : Cob2 c n H ξ) (h' : Cob2 c n H ξ') : Cob2 c n H (fun s t => ξ s t + ξ' s t) := by
  obtain ⟨u, hu, hui, hu'⟩ := h
  obtain ⟨v, hv, hvi, hv'⟩ := h'
  refine ⟨fun s => u s + v s, hu.add hv, fun s => add_mem (hui s) (hvi s), fun s hs t ht => ?_⟩
  have := cg_add (hu' s hs t ht) (hv' s hs t ht)
  convert this using 1; ring

theorem isIntegralCocycleOneModPow_sub (c : Coef l) (n : ℕ) (V : R2 Ω l) (H : Subgroup (G ℚ Ω)) (a a' : G ℚ Ω → Fin 2 → Qbar l)
    (h : Coc1 c n V H a) (h' : Coc1 c n V H a') : Coc1 c n V H (fun s => a s - a' s) := by
  refine ⟨h.1.sub h'.1, fun s i => sub_mem (h.2.1 s i) (h'.2.1 s i), fun s hs t ht => ?_⟩
  have := cv_sub (h.2.2 s hs t ht) (h'.2.2 s hs t ht)
  intro i
  convert this i using 2
  simp only [Pi.sub_apply, Pi.add_apply, Matrix.mulVec_sub]; ring

theorem isIntegralCocycleOneModPow_coboundary (c : Coef l) (n : ℕ) (V : R2 Ω l) (H : Subgroup (G ℚ Ω)) (x : Fin 2 → Qbar l)
    (hV : Continuous fun s => mat V s) (hint : ∀ s i j, mat V s i j ∈ c.O) (hx : ∀ i, x i ∈ c.O) :
    Coc1 c n V H (fun s => mat V s *ᵥ x - x) := by
  refine ⟨(hV.matrix_mulVec continuous_const).sub continuous_const |>.continuousOn,
    fun s i => sub_mem (CupCob.mulVec_mem c _ _ (hint s) hx i) (hx i), fun s _ t _ i => ?_⟩
  have e : (mat V (s * t) *ᵥ x - x) i = ((mat V s *ᵥ x - x) + mat V s *ᵥ (mat V t *ᵥ x - x)) i := by
    simp only [mat, map_mul, Units.val_mul, ← Matrix.mulVec_mulVec, Matrix.mulVec_sub, Pi.add_apply, Pi.sub_apply]; ring
  unfold Cg; dsimp only; rw [e, sub_self, norm_zero]; exact norm_nonneg _

theorem om_cg (c : Coef l) (n : ℕ) (A A' B B' : Fin 2 → Qbar l) (M : Matrix (Fin 2) (Fin 2) (Qbar l))
    (hA : ∀ i, A i ∈ c.O) (hB' : ∀ i, B' i ∈ c.O) (hM : ∀ i j, M i j ∈ c.O)
    (h1 : Cv n A' A) (h2 : Cv n B' B) : Cg n (om A' (M *ᵥ B')) (om A (M *ᵥ B)) := by
  have hMn : ∀ i j, ‖M i j‖ ≤ 1 := fun i j => CupCob.norm_le_one_of_mem c (hM i j)
  unfold Cg
  have e : om A' (M *ᵥ B') - om A (M *ᵥ B) = om (A' - A) (M *ᵥ B') + om A (M *ᵥ (B' - B)) := by
    simp only [om, Matrix.mulVec_sub, Pi.sub_apply]; ring
  rw [e]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · exact CupCob.om_le_left _ _ (fun i => h1 i) (CupCob.mulVec_le _ _ hMn (fun i => CupCob.norm_le_one_of_mem c (hB' i)))
  · exact CupCob.om_le_right _ _ (fun i => CupCob.norm_le_one_of_mem c (hA i))
      (CupCob.mulVec_le _ _ hMn (fun i => by simpa [Cg] using h2 i))

theorem mat_dual1_cont (W : R2 Ω l) (hW : Continuous W) (hdet : dt W ^ 2 = 1) :
    Continuous fun s => mat (dual1 W) s := by
  have hM : Continuous fun s => mat W s := Units.continuous_val.comp hW
  have : (fun s => mat (dual1 W) s) = fun s => (eps l s * (mat W s).det) • mat W s := funext (CupCob.mat_dual1 W hdet)
  rw [this]
  exact (CupCob.eps_cont.mul hM.matrix_det).smul hM

theorem cup_unr_cob_of_vanish [IsAlgClosure ℚ Ω] (c : Coef l) (n : ℕ) (W : R2 Ω l) (q : Pl) (B : ValuationSubring Ω)
    (a b : G ℚ Ω → Fin 2 → Qbar l) (hW : Continuous W) (hint : ∀ s i j, mat W s i j ∈ c.O) (hdet : dt W ^ 2 = 1)
    (hB : IsPlaceOver B q) (hl : ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal)
    (ha : Coc1 c n W (Dec (F := ℚ) B) a) (hb : Coc1 c n (dual1 W) (Dec (F := ℚ) B) b)
    (ha0 : ∀ i ∈ Ine (F := ℚ) B, Cv n (a i) 0) (hb0 : ∀ i ∈ Ine (F := ℚ) B, Cv n (b i) 0) :
    Cob2 c n (Dec (F := ℚ) B) (cup W a b) := by
  set D := Dec (F := ℚ) B with hD
  set I := Ine (F := ℚ) B with hI
  have hID : I ≤ D := Ine_le_Dec B
  have hconj : ∀ s ∈ D, ∀ i ∈ I, s⁻¹ * i * s ∈ I := fun s hs i hi => by
    have := conj_mem_Ine (D.inv_mem hs) hi
    simpa using this
  have hDm : ∀ s i j, mat (dual1 W) s i j ∈ c.O := CupCob.dual_representation_integral c W hdet hint
  have hia := inv_ine l Ω c n W D I a hint hID hconj ha ha0
  have hib := inv_ine l Ω c n (dual1 W) D I b hDm hID hconj hb hb0
  have hξint : ∀ s t, cup W a b s t ∈ c.O := fun s t =>
    CupCob.om_mem c _ _ (ha.2.1 s) (CupCob.mulVec_mem c _ _ (hDm s) (hb.2.1 t))
  have hepsI : ∀ i ∈ I, eps l i = 1 := fun i hi => by
    have h := cyc_eq_one_of_mem_Ine (F := ℚ) (l := l) hl hB hi
    show ((cycBar ℚ Ω l i : (Qbar l)ˣ) : Qbar l) = 1
    rw [show cycBar ℚ Ω l i = cyc ℚ Ω l i from rfl, h]; rfl
  have hbiI : ∀ s ∈ D, ∀ t ∈ D, ∀ i ∈ I, Cg n (cup W a b (s * i) t) (cup W a b s t) ∧
      Cg n (cup W a b s (t * i)) (cup W a b s t) := by
    intro s hs t ht i hi
    constructor
    · simp only [cup]
      rw [CupCob.mat_dual1_mul W s i (b t)]
      exact om_cg c n _ _ _ _ _ (ha.2.1 s) (fun j => CupCob.mulVec_mem c _ _ (hDm i) (hb.2.1 t) j) (hDm s)
        (hia s hs i hi).1 (hib t ht i hi).2
    · simp only [cup]
      exact om_cg c n _ _ _ _ _ (ha.2.1 s) (hb.2.1 _) (hDm s) (fun j => by simp [Cg]) (hib t ht i hi).1
  have hcont : ContinuousOn (fun p : G ℚ Ω × G ℚ Ω => cup W a b p.1 p.2) ((D : Set (G ℚ Ω)) ×ˢ (D : Set (G ℚ Ω))) := by
    have h1 : ContinuousOn (fun p : G ℚ Ω × G ℚ Ω => a p.1) ((D : Set (G ℚ Ω)) ×ˢ (D : Set (G ℚ Ω))) :=
      ha.1.comp continuousOn_fst (fun p hp => hp.1)
    have h2 : ContinuousOn (fun p : G ℚ Ω × G ℚ Ω => b p.2) ((D : Set (G ℚ Ω)) ×ˢ (D : Set (G ℚ Ω))) :=
      hb.1.comp continuousOn_snd (fun p hp => hp.2)
    have hm : ∀ i j, ContinuousOn (fun p : G ℚ Ω × G ℚ Ω => mat (dual1 W) p.1 i j) ((D : Set (G ℚ Ω)) ×ˢ (D : Set (G ℚ Ω))) :=
      fun i j => (((continuous_apply j).comp (continuous_apply i)).comp ((mat_dual1_cont W hW hdet).comp continuous_fst)).continuousOn
    have h1' := continuousOn_pi.1 h1
    have h2' := continuousOn_pi.1 h2
    have h3' : ∀ i, ContinuousOn (fun p : G ℚ Ω × G ℚ Ω => mat (dual1 W) p.1 i 0 * b p.2 0 + mat (dual1 W) p.1 i 1 * b p.2 1)
        ((D : Set (G ℚ Ω)) ×ˢ (D : Set (G ℚ Ω))) := fun i => ((hm i 0).mul (h2' 0)).add ((hm i 1).mul (h2' 1))
    have e : (fun p : G ℚ Ω × G ℚ Ω => cup W a b p.1 p.2) = fun p => a p.1 0 * (mat (dual1 W) p.1 1 0 * b p.2 0 + mat (dual1 W) p.1 1 1 * b p.2 1) - a p.1 1 * (mat (dual1 W) p.1 0 0 * b p.2 0 + mat (dual1 W) p.1 0 1 * b p.2 1) := by
      funext p; simp only [cup, om, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    rw [e]
    exact ((h1' 0).mul (h3' 1)).sub ((h1' 1).mul (h3' 0))
  obtain ⟨K, hIK, hKD, hKo, hepsK, hbiK⟩ := GlobalTheory.T.open_subgroup_cochain_invariance l Ω n D I (cup W a b) (isClosed_Dec B) hID hcont hepsI hbiI
  obtain ⟨φ, m, hm, hφm, hd⟩ := GlobalTheory.T.exists_frobenius_pow_inv_mul_mem_open_subgroup Ω q B K hB hIK hKo
  obtain ⟨d, hdo, hdK⟩ := hd (l ^ n) (pow_pos (Fact.out : l.Prime).pos n)
  exact GlobalTheory.T.cob2_of_cocycle_cong_of_invariant l Ω c n D K φ m d (cup W a b) hm hφm hdo hdK hepsK hξint
    (cup_coc l Ω c n W D a b hint hdet ha hb) hbiK

theorem cup_unr_cob : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (c : Coef l) (n : ℕ) (W : R2 Ω l) (q : Pl) (B : ValuationSubring Ω) (a b : G ℚ Ω → Fin 2 → Qbar l), Continuous W → (∀ s i j, mat W s i j ∈ c.O) → dt W ^ 2 = 1 → IsPlaceOver B q → ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal → Coc1 c n W (Dec (F := ℚ) B) a → Coc1 c n (dual1 W) (Dec (F := ℚ) B) b → Cob1 c n W (Ine (F := ℚ) B) a → Cob1 c n (dual1 W) (Ine (F := ℚ) B) b → Cob2 c n (Dec (F := ℚ) B) (cup W a b) := by
  intro _ l _ Ω _ _ _ c n W q B a b hW hint hdet hB hl ha hb ⟨x, hx, hax⟩ ⟨y, hy, hby⟩
  have hDm : ∀ s i j, mat (dual1 W) s i j ∈ c.O := CupCob.dual_representation_integral c W hdet hint
  have hMc : Continuous fun s => mat W s := Units.continuous_val.comp hW
  set a0 : G ℚ Ω → Fin 2 → Qbar l := fun s => mat W s *ᵥ x - x with ha0def
  set b0 : G ℚ Ω → Fin 2 → Qbar l := fun s => mat (dual1 W) s *ᵥ y - y with hb0def
  have ha0 : Coc1 c n W (Dec (F := ℚ) B) a0 := isIntegralCocycleOneModPow_coboundary c n W _ x hMc hint hx
  have hb0 : Coc1 c n (dual1 W) (Dec (F := ℚ) B) b0 := isIntegralCocycleOneModPow_coboundary c n (dual1 W) _ y (mat_dual1_cont W hW hdet) hDm hy
  have ha1 := isIntegralCocycleOneModPow_sub c n W _ a a0 ha ha0
  have hb1 := isIntegralCocycleOneModPow_sub c n (dual1 W) _ b b0 hb hb0
  have hsplit : cup W a b = fun s t => (cup W a0 b s t + cup W (fun s => a s - a0 s) b0 s t) +
      cup W (fun s => a s - a0 s) (fun s => b s - b0 s) s t := by
    funext s t; simp only [cup, om, Matrix.mulVec_sub, Pi.sub_apply]; ring
  have triv : ∀ (V : R2 Ω l) (z : Fin 2 → Qbar l), (∀ i, z i ∈ c.O) → Cob1 c n V (Dec (F := ℚ) B) (fun s => mat V s *ᵥ z - z) :=
    fun V z hz => ⟨z, hz, fun s _ i => by unfold Cg; rw [sub_self, norm_zero]; exact norm_nonneg _⟩
  have c1 := CupCob.cup_cob l Ω c n W _ a0 b hW hint hdet ha0 hb (Or.inl (triv W x hx))
  have c2 := CupCob.cup_cob l Ω c n W _ _ b0 hW hint hdet ha1 hb0 (Or.inr (triv (dual1 W) y hy))
  have c3 := cup_unr_cob_of_vanish c n W q B _ _ hW hint hdet hB hl ha1 hb1
    (fun i hi j => by
      have := hax i hi j; unfold Cg at this ⊢; simp only [Pi.sub_apply, Pi.zero_apply, sub_zero]; exact this)
    (fun i hi j => by
      have := hby i hi j; unfold Cg at this ⊢; simp only [Pi.sub_apply, Pi.zero_apply, sub_zero]; exact this)
  rw [hsplit]
  exact isIntegralCoboundaryTwoModPow_add c n _ _ _ (isIntegralCoboundaryTwoModPow_add c n _ _ _ c1 c2) c3

end GlobalTheory.Ord2.UnrCup
