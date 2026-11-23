import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.CechDefs
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.TotPairing
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DvMemOf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeZigzagCompat
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NegOneSmulCancel
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Mk2EqZeroIffMemS

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.ConeZig

variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C]

theorem res_cupList {A : C ⥤ CommAlgCat.{0} R} {U V : ObjectProperty C} (h : V ≤ U) {k : ℕ} (l : Fin k → Ch A U 1) :
    resB A h (cupListC (U.ι ⋙ A) l) = cupListC (V.ι ⋙ A) fun j => resB A h (l j) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change (CH.mulP _).cupC _ (resB A h (cupListC _ fun i => l (Fin.castSucc i))) (resB A h (l (Fin.last k))) = _
    rw [ih]
    rfl

theorem PP_eq {A : C ⥤ CommAlgCat.{0} R} {N : ℕ} {W : Fin N → ObjectProperty C} (b : ∀ α, Ch A (W α) 1)
    {V : ObjectProperty C} (hWV : ∀ α, W α ≤ V) (z : Ch A V 2) (k : ℕ) :
    ∃ e : ℤ, e * e = 1 ∧ ∀ i : Idx (k + 1) N, PP b hWV z k i =
      e • cupListC ((capT W i.1).ι ⋙ A) fun j : Fin k => LL b i j.castSucc j.succ := by
  induction k with
  | zero => exact ⟨1, rfl, fun i => (one_smul ℤ _).symm⟩
  | succ k ih =>
    obtain ⟨e, he, h⟩ := ih
    refine ⟨(-1) ^ k * e, ?_, fun i => ?_⟩
    · rw [mul_mul_mul_comm, he, ← mul_pow]; simp
    · change (-1 : ℤ) ^ k • BB b k k (PP b hWV z k) i = _
      have hLL : ∀ j : Fin k, resB A (cap_le W (Fin.last (k + 1)) i) (LL b (fc (Fin.last (k + 1)) i) j.castSucc j.succ) =
          LL b i j.castSucc.castSucc j.castSucc.succ := by
        intro j
        refine res_LL b i _ _ _ _ _ _ (congrArg i.1 ?_) (congrArg i.1 ?_) <;>
        · have := j.2
          apply Fin.ext
          simp only [CrystallineSemistableComparison.Auxff.sa_val, Fin.val_castSucc, Fin.val_last, Fin.val_succ]
          split_ifs <;> omega
      rw [BB_apply, h, map_zsmul, bm_apply, res_cupList, mul_smul]
      simp only [hLL]
      rfl

theorem PP_mem (Φ : PDF R C) (Fil : ℤ → IdF Φ.A) (hF : IsFil Φ Fil) {N : ℕ} {W : Fin N → ObjectProperty C}
    (b : ∀ α, Ch Φ.A (W α) 1) {V : ObjectProperty C} (hWV : ∀ α, W α ≤ V) (z : Ch Φ.A V 2)
    (hb1 : ∀ α, b α ∈ Lm (Fil 1) (W α) 1) (k : ℕ) :
    PP b hWV z k ∈ (dfil (W := W) Fil hF.anti).L (k : ℤ) k k := by
  induction k with
  | zero =>
    intro i _ σ
    rw [hF.top _ (by simp)]
    trivial
  | succ k ih =>
    refine Submodule.smul_of_tower_mem _ _ ?_
    intro i _
    refine Lm_cup (a := Fil k) (b := Fil 1) (fun T x y hx hy => hF.mul k 1 T hx (by simpa using hy)) rfl
      (Lm_res (cap_le W _ i) (ih (fc (Fin.last (k + 1)) i) trivial)) (sub_mem (Lm_res _ (hb1 _)) (Lm_res _ (hb1 _)))

theorem capT_eq {N : ℕ} (W : Fin N → ObjectProperty C) {m : ℕ} (i : Fin m → Fin N) :
    capT W i = capS W (Finset.univ.image i) := by
  funext T
  refine propext ⟨fun h α hα => ?_, fun h a => h _ (Finset.mem_image_of_mem _ (Finset.mem_univ a))⟩
  obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hα
  exact h a

theorem KEx (Φ : PDF R C) (Fil : ℤ → IdF Φ.A) (hF : IsFil Φ Fil) {N : ℕ} (W : Fin N → ObjectProperty C)
    (hS : ∀ S : Finset (Fin N), S.Nonempty → ∀ (r : ℤ) (j : ℕ), (j : ℤ) ≠ r → Subsingleton (HU (gr Fil r) (capS W S) j))
    (r : ℕ) (p q : ℕ) (hq : q ≠ r) : (dfil (W := W) Fil hF.anti).Ex (r : ℤ) p q := by
  have hH : ∀ (i : Idx (p + 1) N) (j : ℕ), j ≠ r → Subsingleton (HU (gr Fil r) (capT W i.1) j) := by
    intro i j hj
    rw [capT_eq]
    exact hS _ ⟨i.1 0, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩ _ _ (by exact_mod_cast hj)
  cases q with
  | zero =>
    intro x hx hd i _ σ
    exact ex_zero (a := (Fil r).res (capT W i.1).ι) (b := (Fil (r + 1)).res (capT W i.1).ι) (hH i 0 hq) (x i)
      (hx i trivial) (hd i trivial) σ
  | succ q =>
    intro x hx hd
    have h := fun i : Idx (p + 1) N =>
      ex_succ (a := (Fil r).res (capT W i.1).ι) (b := (Fil (r + 1)).res (capT W i.1).ι) (hH i (q + 1) hq) (x i)
        (hx i trivial) (hd i trivial)
    choose v hv hv' using h
    exact ⟨v, fun i _ => hv i, fun i _ => hv' i⟩

theorem alg_fin {M : Type*} [AddCommGroup M] {ι : Type} [Fintype ι] (e s : ℤ) (he : e * e = 1) (Cl Pv E : M) (t : ι → M)
    (sg : ι → ℤ) (h1 : Pv = e • Cl) (h2 : Pv = ∑ k, sg k • t k + s • E) :
    Cl - ∑ k, (e * sg k) • t k = (e * s) • E := by
  have h3 : Cl = e • Pv := by rw [h1, smul_smul, he, one_smul]
  rw [h3, h2, smul_add, Finset.smul_sum]
  simp only [smul_smul]
  abel

theorem KV (A : C ⥤ CommAlgCat.{0} R) (n : ℕ) (W : Fin (n + 2) → ObjectProperty C) (p q : ℕ) (h : n + 1 < p) :
    Subsingleton ((KK A W).X p q) := by
  have e : IsEmpty (Idx (p + 1) (n + 2)) := ⟨fun i => by
    have := Fintype.card_le_of_injective _ i.2.injective
    simp only [Fintype.card_fin] at this
    omega⟩
  exact ⟨fun x y => funext fun i => (e.false i).elim⟩

theorem fin_step {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (Φ : PDF R C) (Fil : ℤ → IdF Φ.A) (n : ℕ)
    (W : Fin (n + 2) → ObjectProperty C) (Cl : Ch Φ.A (capS W Finset.univ) (n + 1))
    (hCl : Cl ∈ Lm (Fil ((n : ℤ) + 1)) _ (n + 1))
    (c : HU (gr Fil ((n : ℤ) + 1)) (capS W Finset.univ) (n + 1))
    (hc : Rep ((Fil ((n : ℤ) + 1)).res (capS W Finset.univ).ι) ((Fil ((n : ℤ) + 1 + 1)).res (capS W Finset.univ).ι) Cl c)
    (w : ∀ k : Fin (n + 2), Ch Φ.A (capS W (Finset.univ.erase k)) (n + 1))
    (hw : ∀ k, w k ∈ Lm (Fil ((n : ℤ) + 1)) _ (n + 1))
    (hdw : ∀ k, CH.d _ (n + 1) (w k) ∈ Lm (Fil ((n : ℤ) + 1 + 1)) _ (n + 2))
    (f : Ch Φ.A (capS W Finset.univ) n) (hf : f ∈ Lm (Fil (n : ℤ)) _ n)
    (hEq : Cl - ∑ k, resB Φ.A (capS_univ_le W (Finset.univ.erase k)) (w k) = CH.d _ n f) :
    ∃ (ω : ∀ i, HU (gr Fil ((n : ℤ) + 1)) (capS W (Finset.univ.erase i)) (n + 1))
      (f : CH.Cn (CH.modF ((capS W Finset.univ).ι ⋙ Φ.A)) n),
      (∀ σ, f σ ∈ (Fil n).S _) ∧ (∀ σ, CH.d _ n f σ ∈ (Fil ((n : ℤ) + 1)).S _) ∧
      Rep ((Fil ((n : ℤ) + 1)).res (capS W Finset.univ).ι) ((Fil ((n : ℤ) + 1 + 1)).res (capS W Finset.univ).ι)
        (CH.d _ n f) (c - ∑ i, ((resU (gr Fil ((n : ℤ) + 1)) (capS_univ_le W (Finset.univ.erase i))).pull (n + 1)) (ω i)) := by
  have hG : ∀ k : Fin (n + 2), CH.d _ (n + 1) (gC ((Fil ((n : ℤ) + 1)).res (capS W (Finset.univ.erase k)).ι)
      ((Fil ((n : ℤ) + 1 + 1)).res (capS W (Finset.univ.erase k)).ι) (w k) (hw k)) = 0 := fun k =>
    gC_d (a := (Fil ((n : ℤ) + 1)).res (capS W (Finset.univ.erase k)).ι)
      (b := (Fil ((n : ℤ) + 1 + 1)).res (capS W (Finset.univ.erase k)).ι) (w k) (hw k) (fun s => hdw k s)
  have hY : ∀ k : Fin (n + 2), CH.d _ (n + 1) ((resU (gr Fil ((n : ℤ) + 1)) (capS_univ_le W (Finset.univ.erase k))).pullC (n + 1)
      (gC ((Fil ((n : ℤ) + 1)).res (capS W (Finset.univ.erase k)).ι)
        ((Fil ((n : ℤ) + 1 + 1)).res (capS W (Finset.univ.erase k)).ι) (w k) (hw k))) = 0 := fun k => by
    rw [CH.Mor.d_pullC]
    exact (congrArg _ (hG k)).trans (map_zero _)
  refine ⟨fun k => (CH.cx _).cls (gC ((Fil ((n : ℤ) + 1)).res (capS W (Finset.univ.erase k)).ι)
      ((Fil ((n : ℤ) + 1 + 1)).res (capS W (Finset.univ.erase k)).ι) (w k) (hw k)) (hG k), f, hf, ?_, ?_⟩
  · rw [← hEq]
    refine (show _ ∈ Lm (Fil ((n : ℤ) + 1)) _ (n + 1) from sub_mem hCl (Submodule.sum_mem _ fun k _ => ?_))
    exact Lm_res _ (hw k)
  · exact rep_fin hc _ (fun k : Fin (n + 2) => resB Φ.A (capS_univ_le W (Finset.univ.erase k)) (w k)) hY (fun k s => rfl) hEq

theorem cech_top_cup_power : ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (Φ : PDF R C) (Fil : ℤ → IdF Φ.A),
    IsFil Φ Fil → ∀ (s n : ℕ) (W : Fin (n + 2) → ObjectProperty C), (∀ T, (∃ α, W α T) → (Fil s).S T = ⊥) →
    (∀ α ⦃T T' : C⦄, (T ⟶ T') → W α T → (∃ β, W β T') → W α T') →
    (∀ S : Finset (Fin (n + 2)), S.Nonempty → ∀ (r : ℤ) (j : ℕ), (j : ℤ) ≠ r → Subsingleton (HU (gr Fil r) (capS W S) j)) →
    (∀ S : Finset (Fin (n + 2)), S.Nonempty → ∀ (r : ℤ) (j : ℕ), (n : ℤ) + 1 < r → Subsingleton (HU (gr Fil r) (capS W S) j)) →
    ∀ (z : CH.Cn (CH.modF ((ObjectProperty.ι fun T : C => ∃ α, W α T) ⋙ Φ.A)) 2), CH.d _ 2 z = 0 → (∀ σ, z σ ∈ (Fil 1).S _) →
    ∀ (b : ∀ i, CH.Cn (CH.modF ((W i).ι ⋙ Φ.A)) 1), (∀ i σ, b i σ ∈ (Fil 1).S _) →
    (∀ i, resB Φ.A (fun T h => ⟨i, h⟩ : W i ≤ fun T : C => ∃ α, W α T) z = CH.d _ 1 (b i)) →
    (∀ h, (CH.cx _).cls (cupPowC ((ObjectProperty.ι fun T : C => ∃ α, W α T) ⋙ Φ.A) z (n + 1)) h = 0) →
    ∀ c : HU (gr Fil ((n : ℤ) + 1)) (capS W Finset.univ) (n + 1),
      Rep ((Fil ((n : ℤ) + 1)).res (capS W Finset.univ).ι) ((Fil ((n : ℤ) + 1 + 1)).res (capS W Finset.univ).ι)
        (cupListC ((capS W Finset.univ).ι ⋙ Φ.A) fun k : Fin (n + 1) =>
          resB Φ.A (capS_le_univ W k.castSucc) (b k.castSucc) - resB Φ.A (capS_le_univ W k.succ) (b k.succ)) c →
      ∃ (ω : ∀ i, HU (gr Fil ((n : ℤ) + 1)) (capS W (Finset.univ.erase i)) (n + 1))
        (f : CH.Cn (CH.modF ((capS W Finset.univ).ι ⋙ Φ.A)) n),
        (∀ σ, f σ ∈ (Fil n).S _) ∧ (∀ σ, CH.d _ n f σ ∈ (Fil ((n : ℤ) + 1)).S _) ∧
        Rep ((Fil ((n : ℤ) + 1)).res (capS W Finset.univ).ι) ((Fil ((n : ℤ) + 1 + 1)).res (capS W Finset.univ).ι)
          (CH.d _ n f) (c - ∑ i, ((resU (gr Fil ((n : ℤ) + 1)) (capS_univ_le W (Finset.univ.erase i))).pull (n + 1)) (ω i)) := by
  intro R _ C _ Φ Fil hF s n W _ _ hS _ z hz hz1 b hb1 hb hcob c hc
  have hWV : ∀ α, W α ≤ (fun T : C => ∃ α, W α T) := fun α T h => ⟨α, h⟩
  have hd := cupPow_d _ z hz (n + 1)
  obtain ⟨u, hu⟩ : cupPowC ((ObjectProperty.ι fun T : C => ∃ α, W α T) ⋙ Φ.A) z (n + 1) ∈
      LinearMap.range (CH.d _ (2 * n + 1)) := ((CrystallineSemistableComparison.P.cls_surj (CH.cx _) _).2.1 _ hd).1 (hcob hd)
  let v : (KK Φ.A W).X 0 (2 * n + 1) := fun i => resB Φ.A (capV hWV i) u
  have hv1 : (KK Φ.A W).dv 0 (2 * n + 1) v = aa hWV z (n + 1) := by
    funext i
    rw [dv_apply]
    change CH.d _ _ (resB Φ.A _ u) = resB Φ.A _ _
    rw [d_resB, hu]
  have hv2 : (KK Φ.A W).dh 0 (2 * n + 1) v = 0 := by
    funext i
    rw [dh_apply, Fin.sum_univ_two]
    have e : resB Φ.A (cap_le W 0 i) (v (fc 0 i)) = resB Φ.A (cap_le W 1 i) (v (fc 1 i)) := rfl
    rw [e, Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul, one_smul, add_neg_cancel]
    rfl
  have hTop : ∀ p q, (dfil (W := W) Fil hF.anti).L 0 p q = ⊤ := fun p q =>
    (Submodule.eq_top_iff'.2 fun x i _ σ => by rw [hF.top 0 le_rfl]; trivial)
  have hPm : PP b hWV z (n + 1) ∈ (dfil (W := W) Fil hF.anti).L ((n : ℤ) + 1) (n + 1) (n + 1) := by
    have h := PP_mem Φ Fil hF b hWV z (fun α σ => hb1 α σ) (n + 1)
    rwa [Nat.cast_succ] at h
  obtain ⟨ω, f, hω, hdω, hf, hP⟩ := zig_stair (BB b) (dfil (W := W) Fil hF.anti) n hTop (fun p q h => KV _ n W p q h)
    (KEx Φ Fil hF W hS) (BB_dh b) (BB_dv b hWV z hb) (aa hWV z) (gg b hWV z) (PP b hWV z)
    (gg_dv b hWV z hz hb) (gg_dh b hWV z) rfl (fun k => rfl) hPm v hv1 hv2
  let tp : Idx (n + 1 + 1) (n + 2) := ⟨id, strictMono_id⟩
  obtain ⟨e, he, hPe⟩ := PP_eq b hWV z (n + 1)
  have hU : capS W Finset.univ ≤ capT W tp.1 := fun T h a => h a (Finset.mem_univ a)
  have hEk : ∀ k : Fin (n + 2), capS W (Finset.univ.erase k) ≤ capT W (fc k tp).1 := fun k T h a =>
    h _ (Finset.mem_erase.2 ⟨Fin.succAbove_ne k a, Finset.mem_univ _⟩)
  have hCl : resB Φ.A hU (PP b hWV z (n + 1) tp) = e • cupListC ((capS W Finset.univ).ι ⋙ Φ.A) fun k : Fin (n + 1) =>
      resB Φ.A (capS_le_univ W k.castSucc) (b k.castSucc) - resB Φ.A (capS_le_univ W k.succ) (b k.succ) := by
    rw [hPe]
    refine (map_zsmul ((rM Φ.A hU).pullC (n + 1)) e _).trans ?_
    have h := res_cupList (A := Φ.A) hU (fun j : Fin (n + 1) => LL b tp j.castSucc j.succ)
    exact congrArg (e • ·) (h.trans (congrArg _ (funext fun j => resB_sub hU _ _)))
  have hP2 : resB Φ.A hU (PP b hWV z (n + 1) tp) = ∑ k : Fin (n + 2), ((-1 : ℤ) ^ (k : ℕ)) •
      resB Φ.A (hU.trans (cap_le W k tp)) (ω (fc k tp)) + ((-1 : ℤ) ^ (n + 1)) • CH.d _ n (resB Φ.A hU (f tp)) := by
    have h := congrFun hP tp
    rw [h]
    change (rM Φ.A hU).pullC (n + 1) ((KK Φ.A W).dh n (n + 1) ω tp + (-1 : ℤ) ^ (n + 1) • CH.d _ n (f tp)) = _
    rw [dh_apply, map_add, map_sum, map_zsmul]
    refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun k _ => ?_) ?_
    · rw [map_zsmul]; rfl
    · rw [d_resB]; rfl
  have hEq := alg_fin e ((-1 : ℤ) ^ (n + 1)) he _ _ _ _ (fun k : Fin (n + 2) => (-1 : ℤ) ^ (k : ℕ)) hCl hP2
  have hd' : CH.d _ n ((e * (-1 : ℤ) ^ (n + 1)) • resB Φ.A hU (f tp)) =
      (e * (-1 : ℤ) ^ (n + 1)) • CH.d _ n (resB Φ.A hU (f tp)) := map_zsmul _ _ _
  have hClm : (cupListC ((capS W Finset.univ).ι ⋙ Φ.A) fun k : Fin (n + 1) =>
      resB Φ.A (capS_le_univ W k.castSucc) (b k.castSucc) - resB Φ.A (capS_le_univ W k.succ) (b k.succ)) ∈
      Lm (Fil ((n : ℤ) + 1)) _ (n + 1) := by
    have h1 : resB Φ.A hU (PP b hWV z (n + 1) tp) ∈ Lm (Fil ((n : ℤ) + 1)) _ (n + 1) := Lm_res _ (hPm tp trivial)
    rw [hCl] at h1
    have h2 := Submodule.smul_of_tower_mem _ e h1
    rwa [smul_smul, he, one_smul] at h2
  have hw : ∀ k : Fin (n + 2), (e * (-1 : ℤ) ^ (k : ℕ)) • resB Φ.A (hEk k) (ω (fc k tp)) ∈ Lm (Fil ((n : ℤ) + 1)) _ (n + 1) :=
    fun k => Submodule.smul_of_tower_mem _ _ (Lm_res _ (hω (fc k tp) trivial))
  have hdw : ∀ k : Fin (n + 2), CH.d _ (n + 1) ((e * (-1 : ℤ) ^ (k : ℕ)) • resB Φ.A (hEk k) (ω (fc k tp))) ∈
      Lm (Fil ((n : ℤ) + 1 + 1)) _ (n + 2) := fun k => by
    rw [map_zsmul, d_resB]
    exact Submodule.smul_of_tower_mem _ _ (Lm_res _ (hdω (fc k tp) trivial))
  have hfm : (e * (-1 : ℤ) ^ (n + 1)) • resB Φ.A hU (f tp) ∈ Lm (Fil (n : ℤ)) _ n :=
    Submodule.smul_of_tower_mem _ _ (Lm_res hU (hf tp trivial))
  refine fin_step Φ Fil n W _ hClm c hc _ hw hdw _ hfm ?_
  have e3 : ∀ k : Fin (n + 2), resB Φ.A (capS_univ_le W (Finset.univ.erase k))
      ((e * (-1 : ℤ) ^ (k : ℕ)) • resB Φ.A (hEk k) (ω (fc k tp))) =
      (e * (-1 : ℤ) ^ (k : ℕ)) • resB Φ.A (hU.trans (cap_le W k tp)) (ω (fc k tp)) := fun k =>
    map_zsmul ((rM Φ.A (capS_univ_le W (Finset.univ.erase k))).pullC (n + 1)) _ _
  simp only [e3]
  rw [hd']
  exact hEq

end GlobalTheory.CompanionTheory.ConeZig
