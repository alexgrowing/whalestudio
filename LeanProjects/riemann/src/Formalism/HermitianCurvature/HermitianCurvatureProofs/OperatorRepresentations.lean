import Formalism.HermitianCurvature.StatementQr
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LemmaDDeterminantIdentity

open Matrix Finset
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace OperatorRepresentations

section Mul

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)} {D : Set (Mx k r)}

theorem smooth_coef {c : Mx k r → ℂ} {f : Mx k r → E} (hc : SmoothLev k r i D c) (hf : SmoothLev k r i D f) :
    SmoothLev k r i D (fun g => c g • f g) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, he⟩ := hc g₀ hg₀
  obtain ⟨U₂, F₂, hU₂, hgU₂, hF₂, he₂⟩ := hf g₀ hg₀
  refine ⟨U ∩ U₂, fun x => F x • F₂ x, hU.inter hU₂, ⟨hgU, hgU₂⟩,
    (hF.mono Set.inter_subset_left).smul (hF₂.mono Set.inter_subset_right), ?_⟩
  intro x hx hxG
  show c x • f x = F x • F₂ x
  rw [he x hx.1 hxG, he₂ x hx.2 hxG]

theorem smooth_congr (hD : IsOpen D) {f f₂ : Mx k r → E} (hf : SmoothLev k r i D f)
    (h : ∀ x ∈ Glev k r i ∩ D, f₂ x = f x) : SmoothLev k r i D f₂ := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, he⟩ := hf g₀ hg₀
  refine ⟨U ∩ D, F, hU.inter hD, ⟨hgU, hg₀.2⟩, hF.mono Set.inter_subset_left, ?_⟩
  intro x hx hxG
  rw [h x ⟨hxG, hx.2⟩, he x hx.1 hxG]

theorem good_mulF {c : Mx k r → ℂ} (hc : SmoothLev k r i D c) : Qx2.Good k r i D (mulF (E := E) c) := by
  refine ⟨fun f hf => smooth_coef hc hf, ?_, ?_⟩
  · intro f f₂ h x hx
    show c x • f x = c x • f₂ x
    rw [h x hx]
  · intro f f₂ s _ _ x _
    show c x • (f x + s • f₂ x) = c x • f x + s • (c x • f₂ x)
    rw [smul_add, smul_comm]

def invL (k r : ℕ) (v : Fin (2 * r + k + 1) → ℂ) (p : Fin (2 * r + k + 1)) : Mx k r →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => ((Hpk k r * Mᴴ * Hpk k r) *ᵥ v) p
      map_add' := fun M N => by
        simp only [Matrix.conjTranspose_add, mul_add, add_mul, Matrix.add_mulVec, Pi.add_apply]
      map_smul' := fun c M => by
        simp only [Matrix.conjTranspose_smul, star_trivial, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mulVec,
          Pi.smul_apply, RingHom.id_apply] }

def hrmL (k r : ℕ) (w x : Fin (2 * r + k + 1) → ℂ) : Mx k r →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => herm (Hpk k r) (M *ᵥ w) x
      map_add' := fun M N => by
        simp only [herm, Matrix.add_mulVec, Matrix.mulVec_add, dotProduct_add]
      map_smul' := fun c M => by
        simp only [herm, Matrix.smul_mulVec, Matrix.mulVec_smul, dotProduct_smul, RingHom.id_apply] }

theorem inv_of_uh {g : Mx k r} (hg : g ∈ UH (Hpk k r)) : g⁻¹ = Hpk k r * gᴴ * Hpk k r := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  apply Matrix.inv_eq_left_inv
  rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, hg', Qx2.hpk_sq']

theorem smooth_yv (z : Fin (2 * r + k + 1) → ℂ) (c : Fin (mdim k r i)) :
    SmoothLev k r i D (fun g => yv k r z i g c) := fun _ _ =>
  ⟨Set.univ, invL k r (fvec k r z i) (posL k r i c), isOpen_univ, Set.mem_univ _,
    (invL k r (fvec k r z i) (posL k r i c)).contDiff.contDiffOn, fun g _ hg => by
      show (g⁻¹ *ᵥ fvec k r z i) (posL k r i c) = ((Hpk k r * gᴴ * Hpk k r) *ᵥ fvec k r z i) (posL k r i c)
      rw [inv_of_uh hg.1]⟩

theorem smooth_ybv (z : Fin (2 * r + k + 1) → ℂ) (c : Fin (mdim k r i)) :
    SmoothLev k r i D (fun g => ybv k r z i g c) := fun _ _ =>
  ⟨Set.univ, hrmL k r (bvec (posL k r i c)) (fvec k r z i), isOpen_univ, Set.mem_univ _,
    (hrmL k r (bvec (posL k r i c)) (fvec k r z i)).contDiff.contDiffOn, fun _ _ _ => rfl⟩

theorem good_yv (z : Fin (2 * r + k + 1) → ℂ) (c : Fin (mdim k r i)) :
    Qx2.Good k r i D (mulF (E := E) fun g => yv k r z i g c) := good_mulF (smooth_yv z c)

theorem good_ybv (z : Fin (2 * r + k + 1) → ℂ) (c : Fin (mdim k r i)) :
    Qx2.Good k r i D (mulF (E := E) fun g => ybv k r z i g c) := good_mulF (smooth_ybv z c)

theorem good_neg {T : (Mx k r → E) → Mx k r → E} (hT : Qx2.Good k r i D T) :
    Qx2.Good k r i D (fun f x => -T f x) := by
  simpa only [neg_smul, one_smul] using hT.smul (-1)

theorem good_sub {T S : (Mx k r → E) → Mx k r → E} (hT : Qx2.Good k r i D T) (hS : Qx2.Good k r i D S) :
    Qx2.Good k r i D (fun f x => T f x - S f x) := by
  simpa only [sub_eq_add_neg] using hT.add (good_neg hS)

end Mul

section Op

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)} {D : Set (Mx k r)}

def Rep (X : Module.End ℂ (SV k r i D E)) (T : (Mx k r → E) → Mx k r → E) : Prop :=
  Qx2.Good k r i D T ∧ ∀ (φ : SV k r i D E), ∀ g ∈ Glev k r i ∩ D, (X φ).1 g = T φ.1 g

theorem rep_opV (hD : IsOpen D) {T : (Mx k r → E) → Mx k r → E} (hT : Qx2.Good k r i D T) :
    Rep (opV k r i D T) T := ⟨hT, fun φ _ hg => opV_apply hD hT φ hg⟩

theorem Rep.ext {X Y : Module.End ℂ (SV k r i D E)} {T S : (Mx k r → E) → Mx k r → E} (hX : Rep X T) (hY : Rep Y S)
    (h : ∀ (φ : SV k r i D E), ∀ g ∈ Glev k r i ∩ D, T φ.1 g = S φ.1 g) : X = Y :=
  LinearMap.ext fun φ => SV_ext fun g hg => by rw [hX.2 φ g hg, hY.2 φ g hg, h φ g hg]

theorem Rep.mul {X Y : Module.End ℂ (SV k r i D E)} {T S : (Mx k r → E) → Mx k r → E} (hX : Rep X T) (hY : Rep Y S) :
    Rep (X * Y) (fun f => T (S f)) :=
  ⟨hX.1.comp hY.1, fun φ g hg => by
    show (X (Y φ)).1 g = T (S φ.1) g
    rw [hX.2 _ g hg]
    exact hX.1.loc _ _ (fun x hx => hY.2 φ x hx) g hg⟩

theorem Rep.add {X Y : Module.End ℂ (SV k r i D E)} {T S : (Mx k r → E) → Mx k r → E} (hX : Rep X T) (hY : Rep Y S) :
    Rep (X + Y) (fun f x => T f x + S f x) :=
  ⟨hX.1.add hY.1, fun φ g hg => by
    show (X φ).1 g + (Y φ).1 g = T φ.1 g + S φ.1 g
    rw [hX.2 _ g hg, hY.2 _ g hg]⟩

theorem Rep.sub {X Y : Module.End ℂ (SV k r i D E)} {T S : (Mx k r → E) → Mx k r → E} (hX : Rep X T) (hY : Rep Y S) :
    Rep (X - Y) (fun f x => T f x - S f x) :=
  ⟨good_sub hX.1 hY.1, fun φ g hg => by
    show (X φ).1 g - (Y φ).1 g = T φ.1 g - S φ.1 g
    rw [hX.2 _ g hg, hY.2 _ g hg]⟩

theorem Rep.neg {X : Module.End ℂ (SV k r i D E)} {T : (Mx k r → E) → Mx k r → E} (hX : Rep X T) :
    Rep (-X) (fun f x => -T f x) :=
  ⟨good_neg hX.1, fun φ g hg => by
    show -(X φ).1 g = -T φ.1 g
    rw [hX.2 _ g hg]⟩

theorem Rep.smul {X : Module.End ℂ (SV k r i D E)} {T : (Mx k r → E) → Mx k r → E} (hX : Rep X T) (c : ℂ) :
    Rep (c • X) (fun f x => c • T f x) :=
  ⟨hX.1.smul c, fun φ g hg => by
    show c • (X φ).1 g = c • T φ.1 g
    rw [hX.2 _ g hg]⟩

theorem rep_zero : Rep (0 : Module.End ℂ (SV k r i D E)) (fun _ _ => 0) := ⟨Qx2.good_zero, fun _ _ _ => rfl⟩

theorem rep_one : Rep (1 : Module.End ℂ (SV k r i D E)) (fun f => f) := ⟨Qx2.good_id, fun _ _ _ => rfl⟩

theorem rep_algebraMap (c : ℂ) : Rep (algebraMap ℂ (Module.End ℂ (SV k r i D E)) c) (fun f x => c • f x) :=
  ⟨Qx2.good_id.smul c, fun _ _ _ => rfl⟩

theorem Rep.ite {X : Module.End ℂ (SV k r i D E)} {T : (Mx k r → E) → Mx k r → E} (hX : Rep X T) (p : Prop)
    [Decidable p] : Rep (if p then X else 0) (fun f x => if p then T f x else 0) := by
  by_cases hp : p
  · simpa only [if_pos hp] using hX
  · simpa only [if_neg hp] using rep_zero

theorem rep_sum {ι : Type*} (s : Finset ι) (X : ι → Module.End ℂ (SV k r i D E))
    (T : ι → (Mx k r → E) → Mx k r → E) (h : ∀ j ∈ s, Rep (X j) (T j)) :
    Rep (∑ j ∈ s, X j) (fun f x => ∑ j ∈ s, T j f x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using rep_zero
  | insert j s hj ih =>
    have := (h j (by simp)).add (ih fun l hl => h l (by simp [hl]))
    simpa only [Finset.sum_insert hj] using this

theorem Rep.intCast_mul {X : Module.End ℂ (SV k r i D E)} {T : (Mx k r → E) → Mx k r → E} (hX : Rep X T) (n : ℤ) :
    Rep (((n : ℤ) : Module.End ℂ (SV k r i D E)) * X) (fun f x => (n : ℂ) • T f x) := by
  have e : ((n : ℤ) : Module.End ℂ (SV k r i D E)) * X = (n : ℂ) • X := by
    rw [← zsmul_eq_mul, Int.cast_smul_eq_zsmul]
  rw [e]
  exact hX.smul _

theorem rep_prod : ∀ (t : ℕ) (X : Fin t → Module.End ℂ (SV k r i D E)) (T : Fin t → (Mx k r → E) → Mx k r → E),
    (∀ l, Rep (X l) (T l)) → Rep (List.ofFn X).prod (fun f => (List.ofFn T).foldr (fun T h => T h) f)
  | 0, _, _, _ => by
    simpa only [List.ofFn_zero, List.prod_nil, List.foldr_nil] using rep_one
  | t + 1, X, T, h => by
    have := (h 0).mul (rep_prod t (fun l => X l.succ) (fun l => T l.succ) fun l => h l.succ)
    simpa only [List.ofFn_succ, List.prod_cons, List.foldr_cons] using this

theorem Rep.mkV (hD : IsOpen D) {X : Module.End ℂ (SV k r i D E)} {T : (Mx k r → E) → Mx k r → E} (hX : Rep X T)
    {f : Mx k r → E} (hf : SmoothLev k r i D f) {g : Mx k r} (hg : g ∈ Glev k r i ∩ D) :
    (X (mkV hD f hf)).1 g = T f g := by
  rw [hX.2 _ g hg]
  exact hX.1.loc _ _ (fun x hx => cutF_of_mem hx) g hg

theorem Rep.bridge (hD : IsOpen D) {X : Module.End ℂ (SV k r i D E)} {T L : (Mx k r → E) → Mx k r → E}
    (hX : Rep X T) (hL : ∀ f, ∀ g ∈ Glev k r i ∩ D, L f g = T f g) (f : Mx k r → E) (hf : SmoothLev k r i D f) :
    SmoothLev k r i D (L f) ∧ ∀ g ∈ Glev k r i ∩ D, L f g = (X (Qr.mkV hD f hf)).1 g :=
  ⟨smooth_congr hD (hX.1.sm f hf) (hL f), fun g hg => by rw [hX.mkV hD hf hg, hL f g hg]⟩

theorem rep_EV (hD : IsOpen D) (a b : Fin (mdim k r i)) :
    Rep (EV k r i D E a b) (fun f => EH k r (posL k r i a) (posL k r i b) f) := rep_opV hD (Qx2.good_eh hD a b)

theorem rep_yV (hD : IsOpen D) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin (mdim k r i)) :
    Rep (yV k r z i D E c) (mulF fun g => yv k r z i g c) := rep_opV hD (good_yv z c)

theorem rep_etaV (hD : IsOpen D) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin (mdim k r i)) :
    Rep (etaV k r z i D E c) (mulF fun g => ybv k r z i g c) := rep_opV hD (good_ybv z c)

theorem rep_Tm (hD : IsOpen D) (u : ℂ) (a b : Fin (mdim k r i)) :
    Rep (Tm (EV k r i D E) u a b) (fun f => QuantumDeterminants.Top (EH k r) u (posL k r i a) (posL k r i b) f) := by
  refine ⟨Qx2.good_top hD u a b, fun φ g hg => ?_⟩
  have h := (((rep_algebraMap (k := k) (r := r) (i := i) (D := D) (E := E) u).ite (a = b)).add (rep_EV hD a b)).2 φ g hg
  have e : (posL k r i a = posL k r i b) = (a = b) := propext (Qx2.posL_inj i).eq_iff
  unfold Tm
  rw [h]
  simp only [QuantumDeterminants.Top, e]

theorem rep_qminor (hD : IsOpen D) {t : ℕ} (a b : Fin t → Fin (mdim k r i)) (u : ℂ) :
    Rep (qminor (EV k r i D E) a b u) (fun f => qminorOp (EH k r) (posL k r i ∘ a) (posL k r i ∘ b) u f) := by
  refine ⟨Qx2.good_qminor hD a b u, fun φ g hg => ?_⟩
  have h := (rep_sum Finset.univ _ _ fun (σ : Equiv.Perm (Fin t)) _ =>
    (rep_prod t _ _ fun l : Fin t => rep_Tm (E := E) hD (u - (l : ℂ)) (a (σ l)) (b l)).intCast_mul
      (Equiv.Perm.sign σ : ℤ)).2 φ g hg
  unfold qminor
  rw [h]
  simp only [qminorOp, Finset.sum_apply, Pi.smul_apply, Function.comp]

theorem rep_chX (hD : IsOpen D) (z : Fin (2 * r + k + 1) → ℂ) (u : ℂ) (x : Fin (mdim k r i) → ℂ) :
    Rep (chX (EV k r i D E) u x (etaV k r z i D E))
      (fun f => chatL (EH k r) (posL k r i) u (fun _ => x) (ybv k r z i) f) := by
  have h := rep_sum Finset.univ _ _ fun (a : Fin (mdim k r i)) _ => rep_sum Finset.univ _ _
    fun (b : Fin (mdim k r i)) _ => (((rep_etaV (E := E) hD z a).mul (rep_qminor hD (skip1 a) (skip1 b) u)).smul
      ((-1 : ℂ) ^ ((a : ℕ) + (b : ℕ)) * x b))
  refine Eq.mp (congrArg (Rep _) ?_) h
  funext f g
  simp only [chatL, mulF, smul_smul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  congr 1
  ring

theorem rep_chY (hD : IsOpen D) (z : Fin (2 * r + k + 1) → ℂ) (u : ℂ) (ξ : Fin (mdim k r i) → ℂ) :
    Rep (chY (EV k r i D E) u (yV k r z i D E) ξ)
      (fun f => chatL (EH k r) (posL k r i) u (yv k r z i) (fun _ => ξ) f) := by
  have h := rep_sum Finset.univ _ _ fun (a : Fin (mdim k r i)) _ => rep_sum Finset.univ _ _
    fun (b : Fin (mdim k r i)) _ => (((rep_yV (E := E) hD z b).mul (rep_qminor hD (skip1 a) (skip1 b) u)).smul
      ((-1 : ℂ) ^ ((a : ℕ) + (b : ℕ)) * ξ a))
  refine Eq.mp (congrArg (Rep _) ?_) h
  funext f g
  simp only [chatL, mulF, smul_smul]

theorem representation_capelli_two (hD : IsOpen D) (z : Fin (2 * r + k + 1) → ℂ) (u : ℂ) (x ξ : Fin (mdim k r i) → ℂ) :
    Rep (ch2 (EV k r i D E) u (yV k r z i D E) x (etaV k r z i D E) ξ)
      (fun f => chat2L (EH k r) (posL k r i) u (yv k r z i) (fun _ => x) (ybv k r z i) (fun _ => ξ) f) := by
  have h := rep_sum Finset.univ _ _ fun (a : Fin (mdim k r i)) _ => rep_sum Finset.univ _ _
    fun (a' : Fin (mdim k r i)) _ => rep_sum Finset.univ _ _ fun (b : Fin (mdim k r i)) _ =>
    rep_sum Finset.univ _ _ fun (b' : Fin (mdim k r i)) _ =>
      ((((((rep_etaV (E := E) hD z a).smul (ξ a')).sub ((rep_etaV hD z a').smul (ξ a))).mul
        (((rep_yV hD z b).smul (x b')).sub ((rep_yV hD z b').smul (x b)))).mul
          (rep_qminor hD (skip2 a a') (skip2 b b') u)).smul
            ((-1 : ℂ) ^ ((a : ℕ) + (a' : ℕ) + (b : ℕ) + (b' : ℕ)))).ite (a < a' ∧ b < b')
  refine Eq.mp (congrArg (Rep _) ?_) h
  funext f g
  simp only [chat2L, mulF]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun b' _ => ?_
  split_ifs
  · module
  · rfl

theorem rep_tV (hD : IsOpen D) (z z' : Fin (2 * r + k + 1) → ℂ) (Y : ℂ) (p q : Fin 2) :
    Rep (tV k r z z' i D E Y p q) (fun f x => tL k r z z' i Y p q f x) := by
  fin_cases p <;> fin_cases q
  · exact rep_qminor hD id id _
  · exact (rep_chX hD z _ _).neg
  · exact (rep_chY hD z _ _).neg
  · exact (representation_capelli_two hD z _ _ _).neg

end Op

end OperatorRepresentations

theorem relation_representation : Formalism.FourierDecayAlt.Qr.BridgeRel := by
  intro E _ _ k r z i D hD
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b c d
    refine (((OperatorRepresentations.rep_EV hD a b).mul (OperatorRepresentations.rep_EV hD c d)).sub ((OperatorRepresentations.rep_EV hD c d).mul (OperatorRepresentations.rep_EV hD a b))).ext
      (((OperatorRepresentations.rep_EV hD a d).ite (b = c)).sub ((OperatorRepresentations.rep_EV hD c b).ite (d = a))) fun φ g hg => ?_
    exact generator_gl_level E k r i D a b c d φ.1 hD φ.2.1 g hg
  · intro a b c
    refine (((OperatorRepresentations.rep_EV hD a b).mul (OperatorRepresentations.rep_yV hD z c)).sub ((OperatorRepresentations.rep_yV hD z c).mul (OperatorRepresentations.rep_EV hD a b))).ext
      ((OperatorRepresentations.rep_yV hD z b).neg.ite (a = c)) fun φ g hg => ?_
    have h := (twisted_leibniz_rule E k r z i D a b c φ.1 hD φ.2.1 g hg).1
    show EH k r (posL k r i a) (posL k r i b) (fun x => yv k r z i x c • φ.1 x) g -
      yv k r z i g c • EH k r (posL k r i a) (posL k r i b) φ.1 g = if a = c then -(yv k r z i g b • φ.1 g) else 0
    rw [h]
    split_ifs <;> simp
  · intro a b c
    refine (((OperatorRepresentations.rep_EV hD a b).mul (OperatorRepresentations.rep_etaV hD z c)).sub
      ((OperatorRepresentations.rep_etaV hD z c).mul (OperatorRepresentations.rep_EV hD a b))).ext ((OperatorRepresentations.rep_etaV hD z a).ite (b = c)) fun φ g hg => ?_
    have h := (twisted_leibniz_rule E k r z i D a b c φ.1 hD φ.2.1 g hg).2
    show EH k r (posL k r i a) (posL k r i b) (fun x => ybv k r z i x c • φ.1 x) g -
      ybv k r z i g c • EH k r (posL k r i a) (posL k r i b) φ.1 g = if b = c then ybv k r z i g a • φ.1 g else 0
    rw [h]
    split_ifs <;> simp
  · intro a b
    exact ((OperatorRepresentations.rep_yV hD z a).mul (OperatorRepresentations.rep_yV hD z b)).ext ((OperatorRepresentations.rep_yV hD z b).mul (OperatorRepresentations.rep_yV hD z a))
      fun φ g _ => smul_comm _ _ _
  · intro a b
    exact ((OperatorRepresentations.rep_etaV hD z a).mul (OperatorRepresentations.rep_etaV hD z b)).ext ((OperatorRepresentations.rep_etaV hD z b).mul (OperatorRepresentations.rep_etaV hD z a))
      fun φ g _ => smul_comm _ _ _
  · intro a b
    exact ((OperatorRepresentations.rep_yV hD z a).mul (OperatorRepresentations.rep_etaV hD z b)).ext ((OperatorRepresentations.rep_etaV hD z b).mul (OperatorRepresentations.rep_yV hD z a))
      fun φ g _ => smul_comm _ _ _

theorem transfer_representation : Formalism.FourierDecayAlt.Qr.BridgeT := fun _ _ _ _ _ z z' _ _ hD f hf Y p q =>
  (OperatorRepresentations.rep_tV hD z z' Y p q).bridge hD (fun _ _ _ => rfl) f hf

end Formalism.FourierDecayAlt.P
