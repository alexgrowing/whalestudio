import Formalism.HermitianCurvature.StatementQ
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SumDualVectorEqZeta

open Matrix Finset Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.B

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace Qb1

variable {k r : ℕ} {Vs : Type} [NormedAddCommGroup Vs] [NormedSpace ℂ Vs]

def SV (σ : Mx k r → (Vs →L[ℂ] Vs)) (w : Vs) : Prop := CkOn ⊤ (GV k r) (fun g => σ g w)

theorem one_mem_GV : (1 : Mx k r) ∈ GV k r := by
  show (1 : Mx k r)ᴴ * Hpk k r * 1 = Hpk k r
  simp

theorem ckOn_congr {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {m : ℕ∞} {f f' : Mx k r → E}
    (he : ∀ g ∈ GV k r, f g = f' g) (h : CkOn m (GV k r) f) : CkOn m (GV k r) f' := by
  intro g₀ hg₀
  obtain ⟨U, F, a, b, c, d⟩ := h g₀ hg₀
  exact ⟨U, F, a, b, c, fun g hg hgG => (he g hgG).symm.trans (d g hg hgG)⟩

theorem ckOn_add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {m : ℕ∞} {f f' : Mx k r → E}
    (h : CkOn m (GV k r) f) (h' : CkOn m (GV k r) f') : CkOn m (GV k r) (fun g => f g + f' g) := by
  intro g₀ hg₀
  obtain ⟨U, F, a, b, c, d⟩ := h g₀ hg₀
  obtain ⟨U', F', a', b', c', d'⟩ := h' g₀ hg₀
  refine ⟨U ∩ U', fun g => F g + F' g, a.inter a', ⟨b, b'⟩, ?_, ?_⟩
  · exact (c.mono Set.inter_subset_left).add (c'.mono Set.inter_subset_right)
  · intro g hg hgG
    show f g + f' g = F g + F' g
    rw [d g hg.1 hgG, d' g hg.2 hgG]

theorem ckOn_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {m : ℕ∞} {f : Mx k r → E} (s : ℂ)
    (h : CkOn m (GV k r) f) : CkOn m (GV k r) (fun g => s • f g) := by
  intro g₀ hg₀
  obtain ⟨U, F, a, b, c, d⟩ := h g₀ hg₀
  refine ⟨U, fun g => s • F g, a, b, ?_, ?_⟩
  · exact c.const_smul s
  · intro g hg hgG
    show s • f g = s • F g
    rw [d g hg hgG]

theorem sv_add {σ : Mx k r → (Vs →L[ℂ] Vs)} {w w' : Vs} (h : SV σ w) (h' : SV σ w') : SV σ (w + w') := by
  unfold SV at *
  have := ckOn_add h h'
  simpa only [map_add] using this

theorem sv_smul {σ : Mx k r → (Vs →L[ℂ] Vs)} {w : Vs} (s : ℂ) (h : SV σ w) : SV σ (s • w) := by
  unfold SV at *
  have := ckOn_smul s h
  simpa only [map_smul] using this

theorem sv_zero (σ : Mx k r → (Vs →L[ℂ] Vs)) : SV σ (0 : Vs) := by
  have := sv_smul (σ := σ) (w := (0 : Vs)) 0 (by
    intro g₀ _
    exact ⟨Set.univ, fun _ => 0, isOpen_univ, trivial, contDiffOn_const, fun g _ _ => by simp⟩)
  simpa using this

variable {σ : Mx k r → (Vs →L[ℂ] Vs)}

theorem hasDerivAt_orbit (hrep : IsCRepOn (UH (Hpk k r)) σ) {w : Vs} (hw : SV σ w) {X : Mx k r}
    (hX : inLie k r X) {g : Mx k r} (hg : g ∈ GV k r) :
    HasDerivAt (fun t : ℝ => σ (g * NormedSpace.exp ((t : ℂ) • X)) w) (σ g (dRep σ X w)) 0 := by
  have h1 := B5.rdV_hasDerivAt (B5.ckOn_mono (m := 1) le_top hw) (one_mem_GV (k := k) (r := r)) hX
  simp only [Matrix.one_mul] at h1
  have hd : dRep σ X w = RdV X (fun g => σ g w) 1 := h1.deriv
  rw [hd]
  have h2 := ((σ g).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
  refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  have := hrep.2 g hg _ (B5.exp_mem hX t)
  simp only [Function.comp_apply, ContinuousLinearMap.coe_restrictScalars', this,
    ContinuousLinearMap.comp_apply]

theorem rdV_orbit (hrep : IsCRepOn (UH (Hpk k r)) σ) {w : Vs} (hw : SV σ w) {X : Mx k r}
    (hX : inLie k r X) {g : Mx k r} (hg : g ∈ GV k r) :
    RdV X (fun x => σ x w) g = σ g (dRep σ X w) :=
  (hasDerivAt_orbit hrep hw hX hg).deriv

theorem rdV_coeff (hrep : IsCRepOn (UH (Hpk k r)) σ) {w : Vs} (hw : SV σ w) {X : Mx k r}
    (hX : inLie k r X) (ℓ : Vs →L[ℂ] ℂ) {g : Mx k r} (hg : g ∈ GV k r) :
    RdV X (fun x => ℓ (σ x w)) g = ℓ (σ g (dRep σ X w)) := by
  have h := (ℓ.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_orbit hrep hw hX hg)
  exact h.deriv

theorem sv_dRep (hrep : IsCRepOn (UH (Hpk k r)) σ) {w : Vs} (hw : SV σ w) {X : Mx k r}
    (hX : inLie k r X) : SV σ (dRep σ X w) := by
  have h : CkOn ⊤ (GV k r) (RdV X (fun x => σ x w)) :=
    B5.ckOn_RdV (m := ⊤) hX (by rw [top_add]; exact hw)
  exact ckOn_congr (fun g hg => rdV_orbit hrep hw hX hg) h

theorem lie1 (Z : Mx k r) : inLie k r (hpart1 (Hpk k r) Z) := Qx2.hpart1_lie Z

theorem lie2 (Z : Mx k r) : inLie k r (hpart2 (Hpk k r) Z) := Qx2.hpart2_lie Z

theorem sv_ecRep (hrep : IsCRepOn (UH (Hpk k r)) σ) {w : Vs} (hw : SV σ w) (Z : Mx k r) :
    SV σ (EcRep (Hpk k r) σ Z w) :=
  sv_add (sv_dRep hrep hw (lie1 Z)) (sv_smul _ (sv_dRep hrep hw (lie2 Z)))

def stepV (σ : Mx k r → (Vs →L[ℂ] Vs)) (c : ℂ) (a b : Fin (2 * r + k + 1)) (y : Vs) : Vs :=
  (if a = b then c • y else 0) + EcRep (Hpk k r) σ (Matrix.single a b 1) y

theorem sv_stepV (hrep : IsCRepOn (UH (Hpk k r)) σ) {w : Vs} (hw : SV σ w) (c : ℂ) (a b : Fin (2 * r + k + 1)) :
    SV σ (stepV σ c a b w) := by
  unfold stepV
  refine sv_add ?_ (sv_ecRep hrep hw _)
  split_ifs
  · exact sv_smul c hw
  · exact sv_zero σ

theorem top_coeff (hrep : IsCRepOn (UH (Hpk k r)) σ) {w : Vs} (hw : SV σ w) (ℓ : Vs →L[ℂ] ℂ) (c : ℂ)
    (a b : Fin (2 * r + k + 1)) {g : Mx k r} (hg : g ∈ GV k r) :
    QuantumDeterminants.Top (EH k r) c a b (fun x => ℓ (σ x w)) g = ℓ (σ g (stepV σ c a b w)) := by
  unfold QuantumDeterminants.Top stepV EcRep
  simp only [EH, EabH]
  rw [rdV_coeff hrep hw (lie1 _) ℓ hg, rdV_coeff hrep hw (lie2 _) ℓ hg]
  split_ifs <;> simp [map_add, map_smul]

theorem rdV_local {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f f' : Mx k r → E}
    (he : ∀ g ∈ GV k r, f g = f' g) {X : Mx k r} (hX : inLie k r X) {g : Mx k r} (hg : g ∈ GV k r) :
    RdV X f g = RdV X f' g := by
  unfold RdV
  congr 1
  funext t
  exact he _ (B5.curve_mem hg hX t)

theorem top_local {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f f' : Mx k r → E}
    (he : ∀ g ∈ GV k r, f g = f' g) (c : ℂ) (a b : Fin (2 * r + k + 1)) {g : Mx k r} (hg : g ∈ GV k r) :
    QuantumDeterminants.Top (EH k r) c a b f g = QuantumDeterminants.Top (EH k r) c a b f' g := by
  unfold QuantumDeterminants.Top
  simp only [EH, EabH]
  rw [he g hg, rdV_local he (lie1 _) hg, rdV_local he (lie2 _) hg]

theorem steps (hrep : IsCRepOn (UH (Hpk k r)) σ) (ℓ : Vs →L[ℂ] ℂ) :
    ∀ (L : List (ℂ × Fin (2 * r + k + 1) × Fin (2 * r + k + 1))) (w : Vs), SV σ w →
      SV σ (L.foldr (fun p y => stepV σ p.1 p.2.1 p.2.2 y) w) ∧
      ∀ g ∈ GV k r, (L.map fun p => QuantumDeterminants.Top (EH k r) p.1 p.2.1 p.2.2).foldr (fun T h => T h) (fun x => ℓ (σ x w)) g =
        ℓ (σ g (L.foldr (fun p y => stepV σ p.1 p.2.1 p.2.2 y) w)) := by
  intro L
  induction L with
  | nil => intro w hw; exact ⟨hw, fun g _ => rfl⟩
  | cons p L ih =>
    intro w hw
    obtain ⟨h1, h2⟩ := ih w hw
    refine ⟨sv_stepV hrep h1 _ _ _, fun g hg => ?_⟩
    simp only [List.map_cons, List.foldr_cons]
    rw [top_local (f' := fun x => ℓ (σ x (L.foldr (fun p y => stepV σ p.1 p.2.1 p.2.2 y) w))) h2 _ _ _ hg]
    exact top_coeff hrep h1 ℓ _ _ _ hg

theorem qminor_coeff (hrep : IsCRepOn (UH (Hpk k r)) σ) (ℓ : Vs →L[ℂ] ℂ) {t : ℕ}
    (a b : Fin t → Fin (2 * r + k + 1)) (u : ℂ) {w : Vs} (hw : SV σ w) {g : Mx k r} (hg : g ∈ GV k r) :
    qminorOp (EH k r) a b u (fun x => ℓ (σ x w)) g =
      ℓ (σ g (qmF (fun a b => EcRep (Hpk k r) σ (Matrix.single a b 1)) a b u w)) := by
  unfold qminorOp qmF
  rw [Finset.sum_apply, map_sum, map_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Pi.smul_apply, map_smul, map_smul]
  congr 1
  have e1 : (List.ofFn fun i : Fin t => QuantumDeterminants.Top (EH (E := ℂ) k r) (u - ((i : ℕ) : ℂ)) (a (τ i)) (b i)) =
      (List.ofFn fun i : Fin t => ((u - ((i : ℕ) : ℂ)), a (τ i), b i)).map
        (fun p => QuantumDeterminants.Top (EH (E := ℂ) k r) p.1 p.2.1 p.2.2) := by
    rw [List.map_ofFn]; rfl
  have e2 : (List.ofFn fun i : Fin t => fun y : Vs =>
      (if a (τ i) = b i then (u - ((i : ℕ) : ℂ)) • y else 0) +
        EcRep (Hpk k r) σ (Matrix.single (a (τ i)) (b i) 1) y).foldr (fun T h => T h) w =
      (List.ofFn fun i : Fin t => ((u - ((i : ℕ) : ℂ)), a (τ i), b i)).foldr
        (fun p y => stepV σ p.1 p.2.1 p.2.2 y) w := by
    have e3 : (List.ofFn fun i : Fin t => fun y : Vs =>
        (if a (τ i) = b i then (u - ((i : ℕ) : ℂ)) • y else 0) +
          EcRep (Hpk k r) σ (Matrix.single (a (τ i)) (b i) 1) y) =
        (List.ofFn fun i : Fin t => ((u - ((i : ℕ) : ℂ)), a (τ i), b i)).map
          (fun (p : ℂ × Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) (y : Vs) => stepV σ p.1 p.2.1 p.2.2 y) := by
      rw [List.map_ofFn]; rfl
    rw [e3, List.foldr_map]
  rw [e1, e2]
  exact (steps hrep ℓ _ w hw).2 g hg

theorem qmF_reindex {X : Type*} [AddCommGroup X] [Module ℂ X] {n : ℕ} (Eop : Fin n → Fin n → X → X) (u : ℂ) (x : X) :
    ∀ (t : ℕ) (h : t = n) (a : Fin t → Fin n), (∀ j, (a j).val = j.val) →
      qmF Eop a a u x = qmF Eop (id : Fin n → Fin n) id u x := by
  intro t h a ha
  subst h
  have : a = id := funext fun j => Fin.ext (ha j)
  subst this
  rfl

end Qb1

theorem casimir_eigenvalue_coefficients : Formalism.FourierDecayAlt.Q.EigenCoeff := by
  intro Vs _ _ k r σ v lam hrep hsm hC ℓ Y g hg
  have hw : Qb1.SV σ v := by
    intro g₀ hg₀
    have hmem : ∀ x ∈ GV k r, x ∈ Glev k r 0 := fun x hx =>
      ⟨hx, fun a ha => absurd ha (by simp)⟩
    obtain ⟨U, F, a, b, c, d⟩ := hsm g₀ ⟨hmem g₀ hg₀, trivial⟩
    exact ⟨U, F, a, b, c, fun x hx hxG => d x hx (hmem x hxG)⟩
  unfold CV capL
  rw [Qb1.qminor_coeff hrep ℓ _ _ _ hw hg,
    Qb1.qmF_reindex _ _ _ (mdim k r 0) (by simp [mdim]) (posL k r 0) (fun j => by simp [posL]), hC,
    map_smul, map_smul]
  congr 1
  refine Finset.prod_congr rfl fun s _ => ?_
  simp only [uC, mdim, Fin.val_zero, Nat.sub_zero]
  push_cast
  ring

end Formalism.FourierDecayAlt.P
