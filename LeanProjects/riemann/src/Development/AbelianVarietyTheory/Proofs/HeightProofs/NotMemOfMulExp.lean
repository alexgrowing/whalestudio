import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm

noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum

namespace GlobalTheory.TypeSum.CoefClos

variable {n : ℕ}

abbrev Ltr (ε : Fin n → Bool) : Type := {X : Mx n // X ∈ lieSet ε} ⊕ {k : Mx n // k ∈ Kset ε}

section Vec

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def ltrV (σ : Mx n → (H →L[ℂ] H)) {ε : Fin n → Bool} : Ltr ε → H → H
  | Sum.inl X => dRep σ X.1
  | Sum.inr k => σ k.1

def wordV (σ : Mx n → (H →L[ℂ] H)) {ε : Fin n → Bool} (u : List (Ltr ε)) (v : H) : H := u.foldr (ltrV σ) v

end Vec

def rder (X : Mx n) (f : Mx n → ℂ) (g : Mx n) : ℂ := deriv (fun t : ℝ => f (g * NormedSpace.exp (t • X))) 0

def ltrF {ε : Fin n → Bool} : Ltr ε → (Mx n → ℂ) → Mx n → ℂ
  | Sum.inl X => rder X.1
  | Sum.inr k => fun f g => f (g * k.1)

def wordF {ε : Fin n → Bool} (u : List (Ltr ε)) (f : Mx n → ℂ) : Mx n → ℂ := u.foldr ltrF f

def wordE {M : Type} [AddCommGroup M] [Module ℂ M] {ε : Fin n → Bool} (τ : Ltr ε → Module.End ℂ M)
    (u : List (Ltr ε)) (m : M) : M := u.foldr (fun x => τ x) m

def CSm (ε : Fin n → Bool) (f : Mx n → ℂ) : Prop :=
  ∃ F : List (Mx n) → Mx n → ℂ, (∀ g ∈ UJset ε, F [] g = f g) ∧ IsDerFam ε F ∧
    ∀ l : List (Mx n), (∀ Y ∈ l, Y ∈ lieSet ε) → ContinuousOn (F l) (UJset ε)

variable {ε : Fin n → Bool}

theorem CSm.congr {f f' : Mx n → ℂ} (h : CSm ε f) (e : ∀ g ∈ UJset ε, f g = f' g) : CSm ε f' := by
  obtain ⟨F, h1, h2, h3⟩ := h
  exact ⟨F, fun g hg => (h1 g hg).trans (e g hg), h2, h3⟩

theorem CSm.add {f f' : Mx n → ℂ} (h : CSm ε f) (h' : CSm ε f') : CSm ε (f + f') := by
  obtain ⟨F, h1, h2, h3⟩ := h
  obtain ⟨F', k1, k2, k3⟩ := h'
  refine ⟨fun l g => F l g + F' l g, fun g hg => by simp [h1 g hg, k1 g hg], fun l hl X hX g hg => ?_,
    fun l hl => (h3 l hl).add (k3 l hl)⟩
  exact (h2 l hl X hX g hg).add (k2 l hl X hX g hg)

theorem CSm.smul {f : Mx n → ℂ} (h : CSm ε f) (c : ℂ) : CSm ε (c • f) := by
  obtain ⟨F, h1, h2, h3⟩ := h
  refine ⟨fun l g => c * F l g, fun g hg => by simp [h1 g hg], fun l hl X hX g hg => ?_,
    fun l hl => continuousOn_const.mul (h3 l hl)⟩
  exact (h2 l hl X hX g hg).const_mul c

theorem CSm.zero : CSm ε (0 : Mx n → ℂ) :=
  ⟨fun _ _ => 0, fun _ _ => rfl, fun _ _ _ _ _ _ => hasDerivAt_const _ _, fun _ _ => continuousOn_const⟩

theorem CSm.sum {ι : Type} (s : Finset ι) {f : ι → Mx n → ℂ} (h : ∀ i ∈ s, CSm ε (f i)) :
    CSm ε (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (CSm.zero (ε := ε))
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem CSm.hasDerivAt {f : Mx n → ℂ} (h : CSm ε f) {X : Mx n} (hX : X ∈ lieSet ε) {g : Mx n} (hg : g ∈ UJset ε) :
    HasDerivAt (fun t : ℝ => f (g * NormedSpace.exp (t • X))) (rder X f g) 0 := by
  obtain ⟨F, h1, h2, -⟩ := h
  have h0 : HasDerivAt (fun t : ℝ => f (g * NormedSpace.exp (t • X))) (F [X] g) 0 := by
    refine (h2 [] (by simp) X hX g hg).congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
    exact (h1 _ (mul_mem_UJ hg (exp_mem_UJ hX t))).symm
  rwa [rder, h0.deriv]

theorem CSm.rder_eq {f : Mx n → ℂ} {F : List (Mx n) → Mx n → ℂ} (h1 : ∀ g ∈ UJset ε, F [] g = f g)
    (h2 : IsDerFam ε F) {X : Mx n} (hX : X ∈ lieSet ε) {g : Mx n} (hg : g ∈ UJset ε) : rder X f g = F [X] g := by
  have h0 : HasDerivAt (fun t : ℝ => f (g * NormedSpace.exp (t • X))) (F [X] g) 0 := by
    refine (h2 [] (by simp) X hX g hg).congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
    exact (h1 _ (mul_mem_UJ hg (exp_mem_UJ hX t))).symm
  rw [rder, h0.deriv]

theorem CSm.rder {f : Mx n → ℂ} (h : CSm ε f) {X : Mx n} (hX : X ∈ lieSet ε) : CSm ε (rder X f) := by
  obtain ⟨F, h1, h2, h3⟩ := h
  refine ⟨fun l => F (l ++ [X]), fun g hg => (CSm.rder_eq h1 h2 hX hg).symm, fun l hl Y hY g hg => ?_,
    fun l hl => h3 _ ?_⟩
  · exact h2 (l ++ [X]) (fun Z hZ => (List.mem_append.1 hZ).elim (hl Z) (by simp_all)) Y hY g hg
  · exact fun Z hZ => (List.mem_append.1 hZ).elim (hl Z) (by simp_all)

theorem exp_conj_smul {k : Mx n} (hk : k ∈ UJset ε) (Y : Mx n) (t : ℝ) :
    k⁻¹ * NormedSpace.exp (t • Y) * k = NormedSpace.exp (t • (k⁻¹ * Y * k)) := by
  have hu : IsUnit k⁻¹ := (isUnit_of_UJ (inv_mem_UJ hk))
  have e := Matrix.exp_conj k⁻¹ (t • Y) hu
  rw [Matrix.nonsing_inv_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 (isUnit_of_UJ hk))] at e
  rw [← e, Matrix.mul_smul, Matrix.smul_mul]

theorem CSm.rt {f : Mx n → ℂ} (h : CSm ε f) {k : Mx n} (hk : k ∈ Kset ε) : CSm ε (fun g => f (g * k)) := by
  obtain ⟨F, h1, h2, h3⟩ := h
  have hkU := K_le_UJ hk
  refine ⟨fun l g => F (l.map fun Y => k⁻¹ * Y * k) (g * k), fun g hg => by simpa using h1 _ (mul_mem_UJ hg hkU),
    fun l hl Y hY g hg => ?_, fun l hl => ?_⟩
  · have hl' : ∀ Z ∈ l.map (fun Y => k⁻¹ * Y * k), Z ∈ lieSet ε := by
      intro Z hZ
      obtain ⟨Z, hZ', rfl⟩ := List.mem_map.1 hZ
      exact conj_mem_lie (isUnit_Jm ε) hkU (hl Z hZ')
    have hY' : k⁻¹ * Y * k ∈ lieSet ε := conj_mem_lie (isUnit_Jm ε) hkU hY
    have := h2 _ hl' _ hY' (g * k) (mul_mem_UJ hg hkU)
    refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
    show F _ (g * NormedSpace.exp (t • Y) * k) = F _ (g * k * NormedSpace.exp (t • (k⁻¹ * Y * k)))
    rw [← exp_conj_smul hkU Y t]
    congr 1
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_assoc g k, mul_inv_UJ hkU, Matrix.mul_one]
  · have hl' : ∀ Z ∈ l.map (fun Y => k⁻¹ * Y * k), Z ∈ lieSet ε := by
      intro Z hZ
      obtain ⟨Z, hZ', rfl⟩ := List.mem_map.1 hZ
      exact conj_mem_lie (isUnit_Jm ε) hkU (hl Z hZ')
    exact (h3 _ hl').comp (continuous_id.mul continuous_const).continuousOn fun g hg => mul_mem_UJ hg hkU

theorem CSm.ltrF {f : Mx n → ℂ} (h : CSm ε f) (x : Ltr ε) : CSm ε (ltrF x f) := by
  rcases x with X | k
  · exact h.rder X.2
  · exact h.rt k.2

theorem CSm.wordF {f : Mx n → ℂ} (h : CSm ε f) (u : List (Ltr ε)) : CSm ε (wordF u f) := by
  induction u with
  | nil => exact h
  | cons x u ih => exact ih.ltrF x

def Smo (ε : Fin n → Bool) : Submodule ℂ (Mx n → ℂ) where
  carrier := {f | (∀ g ∉ UJset ε, f g = 0) ∧ CSm ε f}
  add_mem' := fun {f f'} hf hf' => ⟨fun g hg => by simp [hf.1 g hg, hf'.1 g hg], hf.2.add hf'.2⟩
  zero_mem' := ⟨fun _ _ => rfl, CSm.zero⟩
  smul_mem' := fun c f hf => ⟨fun g hg => by simp [hf.1 g hg], hf.2.smul c⟩

theorem not_mem_of_mul_exp {X : Mx n} (hX : X ∈ lieSet ε) {g : Mx n} (hg : g ∉ UJset ε) (t : ℝ) :
    g * NormedSpace.exp (t • X) ∉ UJset ε := by
  intro h
  apply hg
  have := mul_mem_UJ h (exp_mem_UJ hX (-t))
  rwa [Matrix.mul_assoc, ← exp_add_smul, add_neg_cancel, zero_smul, NormedSpace.exp_zero, Matrix.mul_one] at this

theorem rder_off {f : Mx n → ℂ} (hf : ∀ g ∉ UJset ε, f g = 0) {X : Mx n} (hX : X ∈ lieSet ε) {g : Mx n}
    (hg : g ∉ UJset ε) : rder X f g = 0 := by
  have : (fun t : ℝ => f (g * NormedSpace.exp (t • X))) = fun _ => 0 :=
    funext fun t => hf _ (not_mem_of_mul_exp hX hg t)
  rw [rder, this, deriv_const]

theorem rt_off {f : Mx n → ℂ} (hf : ∀ g ∉ UJset ε, f g = 0) {k : Mx n} (hk : k ∈ Kset ε) {g : Mx n}
    (hg : g ∉ UJset ε) : f (g * k) = 0 := by
  refine hf _ fun h => hg ?_
  have := mul_mem_UJ h (inv_mem_UJ (K_le_UJ hk))
  rwa [Matrix.mul_assoc, mul_inv_UJ (K_le_UJ hk), Matrix.mul_one] at this

theorem ltrF_mem {f : Mx n → ℂ} (hf : f ∈ Smo ε) (x : Ltr ε) : ltrF x f ∈ Smo ε := by
  refine ⟨fun g hg => ?_, hf.2.ltrF x⟩
  rcases x with X | k
  · exact rder_off hf.1 X.2 hg
  · exact rt_off hf.1 k.2 hg

theorem rder_add {f f' : Mx n → ℂ} (hf : f ∈ Smo ε) (hf' : f' ∈ Smo ε) {X : Mx n} (hX : X ∈ lieSet ε) :
    rder X (f + f') = rder X f + rder X f' := by
  funext g
  by_cases hg : g ∈ UJset ε
  · exact ((hf.2.hasDerivAt hX hg).add (hf'.2.hasDerivAt hX hg)).deriv
  · simp [rder_off (Submodule.add_mem _ hf hf').1 hX hg, rder_off hf.1 hX hg, rder_off hf'.1 hX hg]

theorem rder_smul {f : Mx n → ℂ} (hf : f ∈ Smo ε) (c : ℂ) {X : Mx n} (hX : X ∈ lieSet ε) :
    rder X (c • f) = c • rder X f := by
  funext g
  by_cases hg : g ∈ UJset ε
  · exact ((hf.2.hasDerivAt hX hg).const_mul c).deriv
  · simp [rder_off (Submodule.smul_mem _ c hf).1 hX hg, rder_off hf.1 hX hg]

def ltrM (x : Ltr ε) : Module.End ℂ (Smo ε) where
  toFun f := ⟨ltrF x f.1, ltrF_mem f.2 x⟩
  map_add' f f' := by
    apply Subtype.ext
    rcases x with X | k
    · exact rder_add f.2 f'.2 X.2
    · rfl
  map_smul' c f := by
    apply Subtype.ext
    rcases x with X | k
    · exact rder_smul f.2 c X.2
    · rfl

theorem coe_wordE (u : List (Ltr ε)) (f : Smo ε) : ((wordE ltrM u f : Smo ε) : Mx n → ℂ) = wordF u f := by
  induction u with
  | nil => rfl
  | cons x u ih =>
    show ltrF x (wordE ltrM u f : Smo ε).1 = ltrF x (wordF u f.1)
    rw [ih]

theorem wordF_congr {f f' : Mx n → ℂ} (e : ∀ g ∈ UJset ε, f g = f' g) (u : List (Ltr ε)) :
    ∀ g ∈ UJset ε, wordF u f g = wordF u f' g := by
  induction u with
  | nil => exact e
  | cons x u ih =>
    intro g hg
    rcases x with X | k
    · show deriv _ 0 = deriv _ 0
      congr 1
      funext t
      exact ih _ (mul_mem_UJ hg (exp_mem_UJ X.2 t))
    · exact ih _ (mul_mem_UJ hg (K_le_UJ k.2))

end GlobalTheory.TypeSum.CoefClos

end
