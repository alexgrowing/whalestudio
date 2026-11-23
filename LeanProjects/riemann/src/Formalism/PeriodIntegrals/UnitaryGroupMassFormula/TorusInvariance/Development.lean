import Formalism.HermitianCurvature.StatementQ

open Matrix Finset
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.Q.TInvW

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def blk {k r : ℕ} (i : Fin (r + 1)) (g : Mx k r) : Matrix (Fin (mdim k r i)) (Fin (mdim k r i)) ℂ :=
  fun a b => g (posL k r i a) (posL k r i b)

def StepS : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (i : Fin (r + 1)), inWb k r z →
    (1 : Mx k r) ∈ Slev k r z i ∧ ∀ s ∈ Slev k r z i, s ∈ Glev k r i ∧ s *ᵥ fvec k r z i = fvec k r z i

def StepGrp : Prop :=
  ∀ (k r : ℕ) (i : Fin (r + 1)), ∀ g ∈ Glev k r i, ∀ h ∈ Glev k r i, g * h ∈ Glev k r i

def StepVec : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (i : Fin (r + 1)), inWb k r z → inWb k r z' →
    (∀ s ∈ Slev k r z i, ∀ g : Mx k r, yv k r z i (s * g) = yv k r z i g ∧ ybv k r z i (s * g) = ybv k r z i g) ∧
    ∀ s' ∈ Slev k r z' i,
      blk i s' * blk i s'⁻¹ = 1 ∧ blk i s'⁻¹ * blk i s' = 1 ∧
      blk i s' *ᵥ xv k r z' i = xv k r z' i ∧ xbv k r z' i ᵥ* blk i s'⁻¹ = xbv k r z' i ∧
      ∀ g ∈ Glev k r i, yv k r z i g = blk i s' *ᵥ yv k r z i (g * s') ∧
        ybv k r z i g = ybv k r z i (g * s') ᵥ* blk i s'⁻¹

def StepCongr : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ) (i : Fin (r + 1)) (D : Set (Mx k r))
    (a b : Fin (mdim k r i)) (f f' : Mx k r → E) (g : Mx k r), IsOpen D → g ∈ Glev k r i ∩ D →
    (∀ x ∈ Glev k r i ∩ D, f x = f' x) →
    EH k r (posL k r i a) (posL k r i b) f g = EH k r (posL k r i a) (posL k r i b) f' g

def StepRight : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ) (i : Fin (r + 1)) (D : Set (Mx k r))
    (a b : Fin (mdim k r i)) (f : Mx k r → E) (s' g : Mx k r), IsOpen D → SmoothLev k r i D f →
    s' ∈ Glev k r i → g ∈ Glev k r i → g * s' ∈ D →
    EH k r (posL k r i a) (posL k r i b) (fun x => f (x * s')) g =
      ∑ c, ∑ d, (blk i s'⁻¹ c a * blk i s' b d) • EH k r (posL k r i c) (posL k r i d) f (g * s')

def StepRSm : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ) (i : Fin (r + 1)) (D : Set (Mx k r))
    (f : Mx k r → E) (s' : Mx k r), s' ∈ Glev k r i → (∀ g ∈ Glev k r i ∩ D, g * s' ∈ D) →
    SmoothLev k r i D f → SmoothLev k r i D (fun x => f (x * s'))

section Alg

variable {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ}

lemma tm_inter (E E' : Fin n → Fin n → A) (R : A) (h : ∀ a b, E a b * R = R * E' a b) (u : ℂ)
    (a b : Fin n) : Tm E u a b * R = R * Tm E' u a b := by
  unfold Tm
  rw [add_mul, mul_add, h]
  congr 1
  split_ifs
  · exact Algebra.commutes u R
  · simp

lemma prod_inter (E E' : Fin n → Fin n → A) (R : A) (h : ∀ a b, E a b * R = R * E' a b)
    (l : List (ℂ × Fin n × Fin n)) :
    (l.map fun p => Tm E p.1 p.2.1 p.2.2).prod * R = R * (l.map fun p => Tm E' p.1 p.2.1 p.2.2).prod := by
  induction l with
  | nil => simp
  | cons p l ih =>
    simp only [List.map_cons, List.prod_cons]
    rw [mul_assoc, ih, ← mul_assoc, tm_inter E E' R h, mul_assoc]

lemma qminor_inter (E E' : Fin n → Fin n → A) (R : A) (h : ∀ a b, E a b * R = R * E' a b)
    {t : ℕ} (α β : Fin t → Fin n) (u : ℂ) : qminor E α β u * R = R * qminor E' α β u := by
  have key : ∀ σ : Equiv.Perm (Fin t),
      (List.ofFn fun k : Fin t => Tm E (u - (k : ℂ)) (α (σ k)) (β k)).prod * R =
        R * (List.ofFn fun k : Fin t => Tm E' (u - (k : ℂ)) (α (σ k)) (β k)).prod := by
    intro σ
    have hl := prod_inter E E' R h (List.ofFn fun k : Fin t => (u - (k : ℂ), α (σ k), β k))
    simpa [List.map_ofFn, Function.comp_def] using hl
  unfold qminor
  rw [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [mul_assoc, key σ, ← mul_assoc, ← mul_assoc, (Int.cast_commute _ R).eq]

lemma chatA_inter (E E' : Fin n → Fin n → A) (R : A) (h : ∀ a b, E a b * R = R * E' a b) (u : ℂ)
    (a β : Fin n → ℂ) : chatA E u a β * R = R * chatA E' u a β := by
  unfold chatA
  simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, qminor_inter E E' R h]

lemma second_capelli_minor_intertwines (E E' : Fin n → Fin n → A) (R : A) (h : ∀ a b, E a b * R = R * E' a b) (u : ℂ)
    (a a' β β' : Fin n → ℂ) : chat2A E u a a' β β' * R = R * chat2A E' u a a' β β' := by
  unfold chat2A
  simp only [Finset.sum_mul, Finset.mul_sum, ite_mul, mul_ite, zero_mul, mul_zero, smul_mul_assoc,
    mul_smul_comm, qminor_inter E E' R h]

lemma qdet_inter (E E' : Fin n → Fin n → A) (R : A) (h : ∀ a b, E a b * R = R * E' a b) (u : ℂ) :
    qdet E u * R = R * qdet E' u := qminor_inter E E' R h id id u

end Alg

section Model

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {k r : ℕ} {i : Fin (r + 1)} {D : Set (Mx k r)}

abbrev Pt (k r : ℕ) (i : Fin (r + 1)) (D : Set (Mx k r)) : Type := {g : Mx k r // g ∈ Glev k r i ∩ D}

open Classical in

def ext (k r : ℕ) (i : Fin (r + 1)) (D : Set (Mx k r)) (φ : Pt k r i D → E) : Mx k r → E :=
  fun g => if h : g ∈ Glev k r i ∩ D then φ ⟨g, h⟩ else 0

lemma ext_at {φ : Pt k r i D → E} {g : Mx k r} (hg : g ∈ Glev k r i ∩ D) : ext k r i D φ g = φ ⟨g, hg⟩ := by
  unfold ext
  rw [dif_pos hg]

lemma lev_congr (hD : IsOpen D) {f f' : Mx k r → E} (h : ∀ g ∈ Glev k r i ∩ D, f g = f' g)
    (hf : SmoothLev k r i D f) : SmoothLev k r i D f' := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g₀ hg₀
  refine ⟨U ∩ D, F, hU.inter hD, ⟨hgU, hg₀.2⟩, hF.mono Set.inter_subset_left, fun g hg hgG => ?_⟩
  rw [← h g ⟨hgG, hg.2⟩, hfF g hg.1 hgG]

lemma lev_zero : SmoothLev k r i D (fun _ : Mx k r => (0 : E)) := fun _ _ => ⟨Set.univ, fun _ => 0, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩

lemma lev_add {f f' : Mx k r → E} (hf : SmoothLev k r i D f) (hf' : SmoothLev k r i D f') :
    SmoothLev k r i D (fun g => f g + f' g) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g₀ hg₀
  obtain ⟨U', F', hU', hgU', hF', hfF'⟩ := hf' g₀ hg₀
  refine ⟨U ∩ U', fun g => F g + F' g, hU.inter hU', ⟨hgU, hgU'⟩,
    (hF.mono Set.inter_subset_left).add (hF'.mono Set.inter_subset_right), fun g hg hgG => ?_⟩
  show f g + f' g = F g + F' g
  rw [hfF g hg.1 hgG, hfF' g hg.2 hgG]

lemma lev_smul {f : Mx k r → E} (c : ℂ) (hf : SmoothLev k r i D f) :
    SmoothLev k r i D (fun g => c • f g) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g₀ hg₀
  refine ⟨U, fun g => c • F g, hU, hgU, hF.const_smul c, fun g hg hgG => ?_⟩
  show c • f g = c • F g
  rw [hfF g hg hgG]

variable (E k r i D) in

def Sm : Submodule ℂ (Pt k r i D → E) where
  carrier := {φ | SmoothLev k r i D (ext k r i D φ)}
  add_mem' {φ ψ} hφ hψ := by
    have e : ext k r i D (φ + ψ) = fun g => ext k r i D φ g + ext k r i D ψ g := by
      funext g; unfold ext; split_ifs <;> simp
    show SmoothLev k r i D (ext k r i D (φ + ψ))
    rw [e]; exact lev_add hφ hψ
  zero_mem' := by
    have e : ext k r i D (0 : Pt k r i D → E) = fun _ => 0 := by
      funext g; unfold ext; split_ifs <;> simp
    show SmoothLev k r i D (ext k r i D (0 : Pt k r i D → E))
    rw [e]; exact lev_zero
  smul_mem' c φ hφ := by
    have e : ext k r i D (c • φ) = fun g => c • ext k r i D φ g := by
      funext g; unfold ext; split_ifs <;> simp
    show SmoothLev k r i D (ext k r i D (c • φ))
    rw [e]; exact lev_smul c hφ

def Rep (F : Mx k r → E) (φ : Pt k r i D → E) : Prop :=
  ∀ g (hg : g ∈ Glev k r i ∩ D), F g = φ ⟨g, hg⟩

lemma rep_ext (φ : Pt k r i D → E) : Rep (ext k r i D φ) φ := fun _ hg => ext_at hg

lemma posL_inj {a b : Fin (mdim k r i)} (h : posL k r i a = posL k r i b) : a = b := by
  unfold posL at h
  have h2 := congrArg Fin.val h
  simp only at h2
  exact Fin.ext (by omega)

def Tf (a b : Fin (mdim k r i)) (φ : Pt k r i D → E) : Pt k r i D → E :=
  fun p => EH k r (posL k r i a) (posL k r i b) (ext k r i D φ) p.1

lemma eh_zero (a b : Fin (2 * r + k + 1)) (g : Mx k r) :
    EH k r a b (fun _ : Mx k r => (0 : E)) g = 0 := by
  simp [EabH, RdV]

lemma rep_sum {ι : Type*} [Fintype ι] (c : ι → ℂ) {F : ι → Mx k r → E}
    {x : ι → Sm E k r i D} (h : ∀ j, Rep (F j) (x j).1) :
    Rep (fun g => ∑ j, c j • F j g) (∑ j, c j • x j).1 := by
  intro g hg
  simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply]
  exact Finset.sum_congr rfl fun j _ => by rw [h j g hg]

section Ops

variable (hP : EabPres) (hC : StepCongr) (hD : IsOpen D)
include hP hC hD

lemma Tf_mem {φ : Pt k r i D → E} (hφ : φ ∈ Sm E k r i D) (a b : Fin (mdim k r i)) :
    Tf a b φ ∈ Sm E k r i D := by
  have hφ' : SmoothLev k r i D (ext k r i D φ) := hφ
  have h1 := (hP E k r (fun _ => 0) i D a b (ext k r i D φ) (ext k r i D φ) 0 hD hφ' hφ').1
  show SmoothLev k r i D (ext k r i D (Tf a b φ))
  exact lev_congr hD (fun g hg => (ext_at (φ := Tf a b φ) hg).symm) h1

lemma Tf_add {φ ψ : Pt k r i D → E} (hφ : φ ∈ Sm E k r i D) (hψ : ψ ∈ Sm E k r i D)
    (a b : Fin (mdim k r i)) : Tf a b (φ + ψ) = Tf a b φ + Tf a b ψ := by
  have hφ' : SmoothLev k r i D (ext k r i D φ) := hφ
  have hψ' : SmoothLev k r i D (ext k r i D ψ) := hψ
  funext p
  have e : ext k r i D (φ + ψ) = fun x => ext k r i D φ x + (1 : ℂ) • ext k r i D ψ x := by
    funext g; unfold ext; split_ifs <;> simp
  have h3 := (hP E k r (fun _ => 0) i D a b (ext k r i D φ) (ext k r i D ψ) 1 hD hφ' hψ').2.2 p.1 p.2
  show EH k r (posL k r i a) (posL k r i b) (ext k r i D (φ + ψ)) p.1 =
    EH k r (posL k r i a) (posL k r i b) (ext k r i D φ) p.1 + EH k r (posL k r i a) (posL k r i b) (ext k r i D ψ) p.1
  rw [e, h3, one_smul]

lemma Tf_smul {φ : Pt k r i D → E} (hφ : φ ∈ Sm E k r i D) (c : ℂ)
    (a b : Fin (mdim k r i)) : Tf a b (c • φ) = c • Tf a b φ := by
  have hφ' : SmoothLev k r i D (ext k r i D φ) := hφ
  funext p
  have e : ext k r i D (c • φ) = fun x => (0 : E) + c • ext k r i D φ x := by
    funext g; unfold ext; split_ifs <;> simp
  have h3 := (hP E k r (fun _ => 0) i D a b (fun _ => (0 : E)) (ext k r i D φ) c hD lev_zero hφ').2.2 p.1 p.2
  show EH k r (posL k r i a) (posL k r i b) (ext k r i D (c • φ)) p.1 =
    c • EH k r (posL k r i a) (posL k r i b) (ext k r i D φ) p.1
  rw [e, h3, eh_zero, zero_add]

def Ealg (a b : Fin (mdim k r i)) : Module.End ℂ (Sm E k r i D) where
  toFun x := ⟨Tf a b x.1, Tf_mem hP hC hD x.2 a b⟩
  map_add' x y := Subtype.ext (Tf_add hP hC hD x.2 y.2 a b)
  map_smul' c x := Subtype.ext (Tf_smul hP hC hD x.2 c a b)

lemma E_rep {F : Mx k r → E} {x : Sm E k r i D} (h : Rep F x.1) (a b : Fin (mdim k r i)) :
    Rep (EH k r (posL k r i a) (posL k r i b) F) (Ealg hP hC hD a b x).1 := by
  intro g hg
  show EH k r (posL k r i a) (posL k r i b) F g = EH k r (posL k r i a) (posL k r i b) (ext k r i D x.1) g
  exact hC E k r i D a b F (ext k r i D x.1) g hD hg (fun y hy => by rw [h y hy, ext_at hy])

lemma Top_rep {F : Mx k r → E} {x : Sm E k r i D} (h : Rep F x.1) (u : ℂ)
    (a b : Fin (mdim k r i)) :
    Rep (Formalism.QuantumDeterminants.Top (EH k r) u (posL k r i a) (posL k r i b) F) (Tm (Ealg hP hC hD) u a b x).1 := by
  intro g hg
  have h2 := E_rep hP hC hD h a b g hg
  by_cases hab : a = b
  · subst hab
    simp [Formalism.QuantumDeterminants.Top, Tm, h g hg, h2]
  · have hne : posL k r i a ≠ posL k r i b := fun e => hab (posL_inj e)
    simp [Formalism.QuantumDeterminants.Top, Tm, hab, hne, h2]

lemma foldr_rep (l : List (ℂ × Fin (mdim k r i) × Fin (mdim k r i))) {F : Mx k r → E}
    {x : Sm E k r i D} (h : Rep F x.1) :
    Rep ((l.map fun p => Formalism.QuantumDeterminants.Top (EH k r) p.1 (posL k r i p.2.1) (posL k r i p.2.2)).foldr (fun T f => T f) F)
      ((l.map fun p => Tm (Ealg hP hC hD) p.1 p.2.1 p.2.2).prod x).1 := by
  induction l with
  | nil => simpa using h
  | cons p l ih =>
    simp only [List.map_cons, List.foldr_cons, List.prod_cons]
    exact Top_rep hP hC hD ih p.1 p.2.1 p.2.2

lemma qminor_apply {t : ℕ} (a b : Fin t → Fin (mdim k r i)) (u : ℂ) (x : Sm E k r i D) :
    qminor (Ealg hP hC hD) a b u x = ∑ σ : Equiv.Perm (Fin t), (((Equiv.Perm.sign σ : ℤ) : ℂ)) •
      ((List.ofFn fun k : Fin t => (u - ((k : ℕ) : ℂ), a (σ k), b k)).map
        fun p => Tm (Ealg hP hC hD) p.1 p.2.1 p.2.2).prod x := by
  unfold qminor
  simp [LinearMap.sum_apply, List.map_ofFn, Function.comp_def, Int.cast_smul_eq_zsmul]

lemma qminor_rep {t : ℕ} (a b : Fin t → Fin (mdim k r i)) (u : ℂ) {F : Mx k r → E}
    {x : Sm E k r i D} (h : Rep F x.1) :
    Rep (qminorOp (EH k r) (posL k r i ∘ a) (posL k r i ∘ b) u F) (qminor (Ealg hP hC hD) a b u x).1 := by
  intro g hg
  rw [qminor_apply hP hC hD a b u x]
  unfold qminorOp
  simp only [Finset.sum_apply, Pi.smul_apply, Submodule.coe_sum, Submodule.coe_smul]
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 1
  have hf := foldr_rep hP hC hD (List.ofFn fun k : Fin t => (u - ((k : ℕ) : ℂ), a (σ k), b k)) h g hg
  simpa [List.map_ofFn, Function.comp_def] using hf

lemma chat_rep (u : ℂ) (a β : Mx k r → Fin (mdim k r i) → ℂ) {F : Mx k r → E}
    {x : Sm E k r i D} (h : Rep F x.1) (g : Mx k r) (hg : g ∈ Glev k r i ∩ D) :
    chatL (EH k r) (posL k r i) u a β F g = (chatA (Ealg hP hC hD) u (a g) (β g) x).1 ⟨g, hg⟩ := by
  unfold chatL chatA
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, Submodule.coe_sum, Submodule.coe_smul,
    Finset.sum_apply, Pi.smul_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [qminor_rep hP hC hD (skip1 i) (skip1 j) u h g hg]

lemma second_capelli_minor_represents (u : ℂ) (a a' β β' : Mx k r → Fin (mdim k r i) → ℂ) {F : Mx k r → E}
    {x : Sm E k r i D} (h : Rep F x.1) (g : Mx k r) (hg : g ∈ Glev k r i ∩ D) :
    chat2L (EH k r) (posL k r i) u a a' β β' F g =
      (chat2A (Ealg hP hC hD) u (a g) (a' g) (β g) (β' g) x).1 ⟨g, hg⟩ := by
  unfold chat2L chat2A
  simp only [LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ =>
    Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => ?_
  split_ifs
  · simp only [LinearMap.smul_apply, Submodule.coe_smul, Pi.smul_apply]
    rw [qminor_rep hP hC hD (skip2 i i') (skip2 j j') u h g hg]
  · simp

lemma qdet_rep (u : ℂ) {F : Mx k r → E} {x : Sm E k r i D} (h : Rep F x.1) (g : Mx k r)
    (hg : g ∈ Glev k r i ∩ D) :
    capL k r i u F g = (qdet (Ealg hP hC hD) u x).1 ⟨g, hg⟩ := qminor_rep hP hC hD id id u h g hg

variable (hG : EabGlLev) in
include hG in
lemma Ealg_gl : GlRel (Ealg (E := E) (i := i) hP hC hD) := by
  intro a b c d
  apply LinearMap.ext; intro x
  apply Subtype.ext; funext p
  obtain ⟨g, hg⟩ := p
  have r0 : Rep (ext k r i D x.1) x.1 := rep_ext x.1
  have hab := E_rep hP hC hD (E_rep hP hC hD r0 c d) a b g hg
  have hcd := E_rep hP hC hD (E_rep hP hC hD r0 a b) c d g hg
  have had := E_rep hP hC hD r0 a d g hg
  have hcb := E_rep hP hC hD r0 c b g hg
  have key := hG E k r i D a b c d (ext k r i D x.1) hD x.2 g hg
  simp only [LinearMap.sub_apply, Module.End.mul_apply, Submodule.coe_sub, Pi.sub_apply]
  rw [← hab, ← hcd, key]
  split_ifs <;> simp [had, hcb]

variable {s' : Mx k r} (hs' : ∀ g ∈ Glev k r i ∩ D, g * s' ∈ Glev k r i ∩ D)

def Rf (φ : Pt k r i D → E) : Pt k r i D → E := fun p => φ ⟨p.1 * s', hs' p.1 p.2⟩

variable (hRS : StepRSm) (hs'G : s' ∈ Glev k r i)
include hRS hs'G

lemma Rf_mem {φ : Pt k r i D → E} (hφ : φ ∈ Sm E k r i D) : Rf hs' φ ∈ Sm E k r i D := by
  have hφ' : SmoothLev k r i D (ext k r i D φ) := hφ
  have h1 := hRS E k r i D (ext k r i D φ) s' hs'G (fun g hg => (hs' g hg).2) hφ'
  show SmoothLev k r i D (ext k r i D (Rf hs' φ))
  refine lev_congr hD (fun g hg => ?_) h1
  show ext k r i D φ (g * s') = ext k r i D (Rf hs' φ) g
  rw [ext_at hg, ext_at (hs' g hg)]
  rfl

def RL : Module.End ℂ (Sm E k r i D) where
  toFun x := ⟨Rf hs' x.1, Rf_mem hP hC hD hs' hRS hs'G x.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable (hRt : StepRight) in
include hRt in
lemma RL_inter (a b : Fin (mdim k r i)) :
    Ealg (E := E) hP hC hD a b * RL (E := E) hP hC hD hs' hRS hs'G =
      RL (E := E) hP hC hD hs' hRS hs'G * Econj (Ealg (E := E) hP hC hD) (blk i s'⁻¹) (blk i s') a b := by
  apply LinearMap.ext; intro x
  apply Subtype.ext; funext p
  obtain ⟨g, hg⟩ := p
  have hcon := hC E k r i D a b (ext k r i D (Rf hs' x.1)) (fun y => ext k r i D x.1 (y * s')) g hD hg
    (fun y hy => by
      show ext k r i D (Rf hs' x.1) y = ext k r i D x.1 (y * s')
      rw [ext_at hy, ext_at (hs' y hy)]
      rfl)
  have hR := hRt E k r i D a b (ext k r i D x.1) s' g hD x.2 hs'G hg.1 (hs' g hg).2
  show EH k r (posL k r i a) (posL k r i b) (ext k r i D (Rf hs' x.1)) g =
    (Econj (Ealg (E := E) hP hC hD) (blk i s'⁻¹) (blk i s') a b x).1 ⟨g * s', hs' g hg⟩
  rw [hcon, hR]
  simp only [Econj, LinearMap.sum_apply, LinearMap.smul_apply, Submodule.coe_sum, Submodule.coe_smul,
    Finset.sum_apply, Pi.smul_apply]
  rfl

lemma RL_apply (M M' : Module.End ℂ (Sm E k r i D)) (hM : M * RL (E := E) hP hC hD hs' hRS hs'G = RL (E := E) hP hC hD hs' hRS hs'G * M')
    (x : Sm E k r i D) (g : Mx k r) (hg : g ∈ Glev k r i ∩ D) :
    (M (RL hP hC hD hs' hRS hs'G x)).1 ⟨g, hg⟩ = (M' x).1 ⟨g * s', hs' g hg⟩ := congrArg (fun T : Module.End ℂ (Sm E k r i D) => (T x).1 ⟨g, hg⟩) hM

end Ops

end Model

lemma tl00 {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ)
    (i : Fin (r + 1)) (Y : ℂ) (f : Mx k r → E) :
    tL k r z z' i Y 0 0 f = capL k r i (uC k r i Y) f := rfl

lemma tl01 {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ)
    (i : Fin (r + 1)) (Y : ℂ) (f : Mx k r → E) :
    tL k r z z' i Y 0 1 f =
      -(chatL (EH k r) (posL k r i) (uC k r i Y - 1) (fun _ => xv k r z' i) (ybv k r z i) f) := rfl

lemma tl10 {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ)
    (i : Fin (r + 1)) (Y : ℂ) (f : Mx k r → E) :
    tL k r z z' i Y 1 0 f =
      -(chatL (EH k r) (posL k r i) (uC k r i Y) (yv k r z i) (fun _ => xbv k r z' i) f) := rfl

lemma tl11 {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ)
    (i : Fin (r + 1)) (Y : ℂ) (f : Mx k r → E) :
    tL k r z z' i Y 1 1 f =
      -(chat2L (EH k r) (posL k r i) (uC k r i Y - 1) (yv k r z i) (fun _ => xv k r z' i)
        (ybv k r z i) (fun _ => xbv k r z' i) f) := rfl

lemma left_step (hL : QMinorLeftH) {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ)
    (z z' : Fin (2 * r + k + 1) → ℂ) (i : Fin (r + 1)) (Y : ℂ) (p q : Fin 2) (F : Mx k r → E) (s g : Mx k r)
    (hy : yv k r z i (s * g) = yv k r z i g) (hyb : ybv k r z i (s * g) = ybv k r z i g) :
    tL k r z z' i Y p q (fun x => F (s * x)) g = tL k r z z' i Y p q F (s * g) := by
  have hq : ∀ {t : ℕ} (a b : Fin t → Fin (2 * r + k + 1)) (u : ℂ),
      qminorOp (EH k r) a b u (fun x => F (s * x)) g = qminorOp (EH k r) a b u F (s * g) := by
    intro t a b u
    exact congrFun (hL E (2 * r + k + 1) t (Hpk k r) F a b u s) g
  match p, q with
  | 0, 0 =>
    rw [tl00, tl00]
    exact hq _ _ _
  | 0, 1 =>
    rw [tl01, tl01]
    simp only [Pi.neg_apply, chatL, hq, hyb]
  | 1, 0 =>
    rw [tl10, tl10]
    simp only [Pi.neg_apply, chatL, hq, hy]
  | 1, 1 =>
    rw [tl11, tl11]
    simp only [Pi.neg_apply, chat2L, hq, hy, hyb]

theorem tInvariant_of_contractions (hCC : ContractionsCovariant) (hP : EabPres) (hG : EabGlLev) (hL : QMinorLeftH)
    (hS : StepS) (hGr : StepGrp) (hV : StepVec) (hC : StepCongr) (hRt : StepRight) (hRS : StepRSm) :
    TInvariant := by
  intro E _ _ k r z z' i D f Y p q hz hz' hDom hf s hs s' hs' g hg
  have hDo : IsOpen D := hDom.1
  obtain ⟨hVl, hVr⟩ := hV k r z z' i hz hz'
  have hsG : s ∈ Glev k r i := ((hS k r z i hz).2 s hs).1
  have hs'G : s' ∈ Glev k r i := ((hS k r z' i hz').2 s' hs').1
  have h1z : (1 : Mx k r) ∈ Slev k r z i := (hS k r z i hz).1
  have h1z' : (1 : Mx k r) ∈ Slev k r z' i := (hS k r z' i hz').1
  have hh : s * g ∈ Glev k r i ∩ D := by
    refine ⟨hGr k r i s hsG g hg.1, ?_⟩
    simpa using hDom.2 g hg s hs 1 h1z'
  have hR : ∀ y ∈ Glev k r i ∩ D, y * s' ∈ Glev k r i ∩ D := fun y hy =>
    ⟨hGr k r i y hy.1 s' hs'G, by simpa using hDom.2 y hy 1 h1z s' hs'⟩
  rw [left_step hL k r z z' i Y p q (fun y => f (y * s')) s g (hVl s hs g).1 (hVl s hs g).2]
  obtain ⟨hQP, hPQ, hxv, hxbv, hyv⟩ := hVr s' hs'
  have hf' : SmoothLev k r i D (ext k r i D (fun p : Pt k r i D => f p.1)) :=
    lev_congr hDo (fun y hy => (ext_at (φ := fun p : Pt k r i D => f p.1) hy).symm) hf
  let x0 : Sm E k r i D := ⟨fun p => f p.1, hf'⟩
  have hrep : Rep f x0.1 := fun _ _ => rfl
  have hrep' : Rep (fun x => f (x * s')) (RL (E := E) hP hC hDo hR hRS hs'G x0).1 := fun _ _ => rfl
  have hint : ∀ a b, Ealg (E := E) (i := i) hP hC hDo a b * RL (E := E) hP hC hDo hR hRS hs'G =
      RL (E := E) hP hC hDo hR hRS hs'G * Econj (Ealg (E := E) (i := i) hP hC hDo) (blk i s'⁻¹) (blk i s') a b :=
    fun a b => RL_inter hP hC hDo hR hRS hs'G hRt a b
  have hGl : GlRel (Ealg (E := E) (i := i) hP hC hDo) := Ealg_gl hP hC hDo hG
  have cov := hCC (Module.End ℂ (Sm E k r i D)) (mdim k r i) (Ealg (E := E) (i := i) hP hC hDo)
    (blk i s'⁻¹) (blk i s') hGl hQP hPQ
  obtain ⟨hyvy, hybvy⟩ := hyv (s * g) hh.1
  have hy' := hR (s * g) hh
  match p, q with
  | 0, 0 =>
    rw [tl00, tl00, qdet_rep hP hC hDo _ hrep' (s * g) hh, qdet_rep hP hC hDo _ hrep (s * g * s') hy',
      RL_apply hP hC hDo hR hRS hs'G _ _ (qdet_inter _ _ _ hint _) x0 (s * g) hh,
      (cov (uC k r i Y) 0 0 0 0).1]
  | 0, 1 =>
    have e := (cov (uC k r i Y - 1) (xv k r z' i) 0 (ybv k r z i (s * g * s')) 0).2.1
    rw [hxv, ← hybvy] at e
    rw [tl01, tl01, Pi.neg_apply, Pi.neg_apply, chat_rep hP hC hDo _ _ _ hrep' (s * g) hh,
      chat_rep hP hC hDo _ _ _ hrep (s * g * s') hy',
      RL_apply hP hC hDo hR hRS hs'G _ _ (chatA_inter _ _ _ hint _ _ _) x0 (s * g) hh, e]
  | 1, 0 =>
    have e := (cov (uC k r i Y) (yv k r z i (s * g * s')) 0 (xbv k r z' i) 0).2.1
    rw [← hyvy, hxbv] at e
    rw [tl10, tl10, Pi.neg_apply, Pi.neg_apply, chat_rep hP hC hDo _ _ _ hrep' (s * g) hh,
      chat_rep hP hC hDo _ _ _ hrep (s * g * s') hy',
      RL_apply hP hC hDo hR hRS hs'G _ _ (chatA_inter _ _ _ hint _ _ _) x0 (s * g) hh, e]
  | 1, 1 =>
    have e := (cov (uC k r i Y - 1) (yv k r z i (s * g * s')) (xv k r z' i) (ybv k r z i (s * g * s'))
      (xbv k r z' i)).2.2
    rw [← hyvy, hxv, ← hybvy, hxbv] at e
    rw [tl11, tl11, Pi.neg_apply, Pi.neg_apply, second_capelli_minor_represents hP hC hDo _ _ _ _ _ hrep' (s * g) hh,
      second_capelli_minor_represents hP hC hDo _ _ _ _ _ hrep (s * g * s') hy',
      RL_apply hP hC hDo hR hRS hs'G _ _ (second_capelli_minor_intertwines _ _ _ hint _ _ _ _ _) x0 (s * g) hh, e]

end Formalism.FourierDecayAlt.Q.TInvW
