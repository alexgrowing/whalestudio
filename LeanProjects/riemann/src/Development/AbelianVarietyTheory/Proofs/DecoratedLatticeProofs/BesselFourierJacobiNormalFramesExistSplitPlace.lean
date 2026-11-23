import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil ValuativeRel GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.LocMod

theorem Frame.exists_of_vecMul {k : Type} [Field k] {N : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y]
    (β : Matrix (Fin N) Y k) (hc : Fintype.card Y = N) (h : ∀ v, v ᵥ* β = 0 → v = 0) :
    ∃ F : GlobalTheory.LocMod.Frame k N Y, F.β = β := by
  obtain ⟨g, hg⟩ := β.vecMulLinear.exists_leftInverse_of_injective (LinearMap.ker_eq_bot'.2 h)
  have h1 : β * LinearMap.toMatrixRight' g = 1 := by
    ext i j
    have := congrFun (LinearMap.congr_fun hg (Pi.single i 1)) j
    have h2 : ∀ x, g x = x ᵥ* LinearMap.toMatrixRight' g := fun x => by
      conv_lhs => rw [← LinearMap.toMatrixRight'.symm_apply_apply g]
      rfl
    rw [LinearMap.comp_apply, h2, Matrix.vecMulLinear_apply, Matrix.vecMul_vecMul, Matrix.single_one_vecMul] at this
    simpa [Pi.single_apply, Matrix.one_apply, eq_comm] using this
  exact ⟨⟨β, _, h1, (Matrix.mul_eq_one_comm_of_card_eq _ _ _ (by simp [hc])).1 h1⟩, rfl⟩

theorem Frame.card_eq {k : Type} [Field k] {N : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y]
    (F : GlobalTheory.LocMod.Frame k N Y) : Fintype.card Y = N := by
  have h1 := Matrix.rank_mul_le_left F.β F.γ
  have h2 := Matrix.rank_mul_le_left F.γ F.β
  rw [F.βγ, Matrix.rank_one] at h1
  rw [F.γβ, Matrix.rank_one] at h2
  have h3 := Matrix.rank_le_card_width F.β
  have h4 := Matrix.rank_le_card_width F.γ
  simp only [Fintype.card_fin] at h1 h4
  omega

theorem Frame.eq_zero {k : Type} [Field k] {N : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y]
    (F : GlobalTheory.LocMod.Frame k N Y) {v : Fin N → k} (h : v ᵥ* F.β = 0) : v = 0 := by
  rw [← Matrix.vecMul_one v, ← F.βγ, ← Matrix.vecMul_vecMul, h, Matrix.zero_vecMul]

theorem hyp_eq_zero {D : D7} {k : Type} [Field k] (f : D.host.E →+* k) {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ)
    {v : Fin S.rank → k} (h1 : v ᵥ* d.e.map f = 0) (h2 : v ᵥ* d.i₀.map f = 0) (h3 : v ᵥ* d.e'.map f = 0) : v = 0 := by
  have h := congrArg (fun M => v ᵥ* Matrix.map M f) d.sum_eq_one_rat
  simp only [Matrix.map_add _ (map_add f), Matrix.map_mul, Matrix.map_one _ (map_zero f) (map_one f), Matrix.vecMul_add,
    ← Matrix.vecMul_vecMul, h1, h2, h3, Matrix.zero_vecMul, add_zero, Matrix.vecMul_one] at h
  exact h.symm

theorem orth_eq_zero {D : D7} {k : Type} [Field k] (f : D.host.E →+* k) {S A L : HSp D} (o : OrthDec S A L)
    {ζ : Fin L.rank → D.host.E} (hζ : IsLineVec L ζ)
    {v : Fin S.rank → k} (h1 : v ᵥ* o.iA.map f = 0) (h2 : v ⬝ᵥ (f ∘ vecB o ζ) = 0) : v = 0 := by
  have h3 : v ᵥ* o.iB.map f = 0 := by
    funext j
    have hs : Subsingleton (Fin L.rank) := by rw [hζ.1]; infer_instance
    have hj : ζ j ≠ 0 := fun h0 => hζ.2 (by
      have : ζ = 0 := funext fun i => by rw [Subsingleton.elim i j, h0]; rfl
      rw [this, Matrix.mulVec_zero, dotProduct_zero])
    have h4 : f ∘ vecB o ζ = o.iB.map f *ᵥ (f ∘ ζ) := funext fun i => RingHom.map_mulVec f o.iB ζ i
    rw [h4, Matrix.dotProduct_mulVec, dotProduct, Fintype.sum_subsingleton _ j] at h2
    exact (mul_eq_zero.1 h2).resolve_right ((map_ne_zero f).2 hj)
  have h := congrArg (fun M => v ᵥ* Matrix.map M f) o.iA_qA_add
  simp only [Matrix.map_add _ (map_add f), Matrix.map_mul, Matrix.map_one _ (map_zero f) (map_one f), Matrix.vecMul_add,
    ← Matrix.vecMul_vecMul, h1, h3, Matrix.zero_vecMul, add_zero, Matrix.vecMul_one] at h
  exact h.symm

theorem dot_eq_zero_of_smul {k : Type} [Field k] {N : ℕ} {v w : Fin N → k} {c : k} (hc : c ≠ 0)
    (h : v ⬝ᵥ (fun r => c * w r) = 0) : v ⬝ᵥ w = 0 := by
  have : v ⬝ᵥ (c • w) = 0 := h
  rw [dotProduct_smul] at this
  exact (mul_eq_zero.1 this).resolve_left hc

namespace Place

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k)
variable {n : Type} [Fintype n] [DecidableEq n] {ρ : ℕ} {s : k}

theorem pr_eq : p.pr = ⇑(p.π.comp (incA D)) := rfl

theorem xi_ne_zero : p.xi ≠ 0 := (map_ne_zero (p.π.comp (incA D))).2 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)

theorem hz_ne_zero (B : BesLev D ρ) : p.hz B ≠ 0 := (map_ne_zero (p.π.comp (incA D))).2 B.line.2

theorem exists_isCoreFrame (hs : s ≠ 0) (B : BesLev D ρ) (FA : GlobalTheory.LocMod.Frame k B.A.rank n) :
    ∃ F, p.IsCoreFrame B s FA F := by
  obtain ⟨F, hF⟩ := Frame.exists_of_vecMul (N := B.V₀.rank) (Y := n ⊕ Unit)
    (Matrix.of fun r => Sum.elim (fun a => (B.o.iA.map p.pr * FA.β) r a) fun _ => s * p.pr (vecB B.o B.ζ r))
    (by rw [Fintype.card_sum, FA.card_eq, ← B.o.rank_add, B.line.1]; rfl) (fun v hv => by
      refine orth_eq_zero (p.π.comp (incA D)) B.o B.line (FA.eq_zero ?_) (dot_eq_zero_of_smul hs ?_)
      · rw [Matrix.vecMul_vecMul]; funext a; exact congrFun hv (Sum.inl a)
      · exact congrFun hv (Sum.inr ()))
  exact ⟨F, fun r a => by rw [hF]; rfl, fun r => by rw [hF]; rfl⟩

theorem exists_isJacFrame (hs : s ≠ 0) (J : JacLev D ρ) {hh : k} (hh0 : hh ≠ 0) (F₀ : GlobalTheory.LocMod.Frame k J.W₀.rank n) :
    ∃ F : GlobalTheory.LocMod.Frame k J.W.rank (n ⊕ Fin (2 * ρ)), p.IsJacFrame J s hh F₀ F := by
  have hx := p.xi_ne_zero
  let β : Matrix (Fin J.W.rank) (n ⊕ Fin (2 * ρ)) k :=
    Matrix.of fun r => Sum.elim (fun a => (J.d.i₀.map p.pr * F₀.β) r a) fun j =>
      if h : j.val < ρ then s * p.xi ^ (ρ - j.val) * p.pr (J.d.e r ⟨j.val, h⟩)
      else s * (hh / p.xi) * (-1 / p.xi) ^ (ρ - 1 - (2 * ρ - 1 - j.val)) * p.pr (J.d.e' r ⟨2 * ρ - 1 - j.val, by omega⟩)
  have b1 : ∀ (i : Fin ρ) (j : Fin (2 * ρ)), j.val = i.val → ∀ r,
      β r (Sum.inr j) = s * p.xi ^ (ρ - i.val) * p.pr (J.d.e r i) := by
    rintro ⟨i, hi⟩ ⟨j, hj⟩ (rfl : j = i) r
    exact dif_pos hi
  have b2 : ∀ (i : Fin ρ) (j : Fin (2 * ρ)), j.val + i.val + 1 = 2 * ρ → ∀ r,
      β r (Sum.inr j) = s * (hh / p.xi) * (-1 / p.xi) ^ (ρ - 1 - i.val) * p.pr (J.d.e' r i) := by
    rintro ⟨i, hi⟩ ⟨j, hj⟩ (h : j + i + 1 = 2 * ρ) r
    obtain rfl : i = 2 * ρ - 1 - j := by omega
    exact dif_neg (show ¬ j < ρ by omega)
  obtain ⟨F, hF⟩ := Frame.exists_of_vecMul β
    (by rw [Fintype.card_sum, F₀.card_eq, ← J.d.rank_add, Fintype.card_fin]) (fun v hv => by
      refine hyp_eq_zero (p.π.comp (incA D)) J.d ?_ (F₀.eq_zero ?_) ?_
      · funext i
        have := congrFun hv (Sum.inr ⟨i.val, by omega⟩)
        refine dot_eq_zero_of_smul (c := s * p.xi ^ (ρ - i.val)) (mul_ne_zero hs (pow_ne_zero _ hx)) ?_
        refine Eq.trans ?_ this
        exact congrArg (v ⬝ᵥ ·) (funext fun r => (b1 i _ rfl r).symm)
      · rw [Matrix.vecMul_vecMul]; funext a; exact congrFun hv (Sum.inl a)
      · funext i
        have := congrFun hv (Sum.inr ⟨2 * ρ - 1 - i.val, by omega⟩)
        refine dot_eq_zero_of_smul (c := s * (hh / p.xi) * (-1 / p.xi) ^ (ρ - 1 - i.val))
          (mul_ne_zero (mul_ne_zero hs (div_ne_zero hh0 hx)) (pow_ne_zero _ (div_ne_zero (by simp) hx))) ?_
        refine Eq.trans ?_ this
        exact congrArg (v ⬝ᵥ ·) (funext fun r => (b2 i _ (by have := i.2; dsimp only; omega) r).symm))
  exact ⟨F, rfl, fun r a => by rw [hF]; rfl, by rw [hF]; exact b1, by rw [hF]; exact b2⟩

theorem exists_isBesFrame (hs : s ≠ 0) (B : BesLev D ρ) (FA : GlobalTheory.LocMod.Frame k B.A.rank n) :
    ∃ F : GlobalTheory.LocMod.Frame k B.V.rank (n ⊕ Fin (2 * ρ + 1)), p.IsBesFrame B s FA F := by
  have hx := p.xi_ne_zero
  let β : Matrix (Fin B.V.rank) (n ⊕ Fin (2 * ρ + 1)) k :=
    Matrix.of fun r => Sum.elim (fun a => ((B.d.i₀ * B.o.iA).map p.pr * FA.β) r a) fun j =>
      if h : j.val < ρ then s * p.xi ^ (ρ - j.val) * p.pr (B.d.e r ⟨j.val, h⟩)
      else if h' : j.val = ρ then s * p.pr ((B.d.i₀ *ᵥ vecB B.o B.ζ) r)
      else s * (-p.hz B / p.xi) * (-1 / p.xi) ^ (ρ - 1 - (2 * ρ - j.val)) * p.pr (B.d.e' r ⟨2 * ρ - j.val, by omega⟩)
  have b1 : ∀ (i : Fin ρ) (j : Fin (2 * ρ + 1)), j.val = i.val → ∀ r,
      β r (Sum.inr j) = s * p.xi ^ (ρ - i.val) * p.pr (B.d.e r i) := by
    rintro ⟨i, hi⟩ ⟨j, hj⟩ (rfl : j = i) r
    exact dif_pos hi
  have b0 : ∀ j : Fin (2 * ρ + 1), j.val = ρ → ∀ r, β r (Sum.inr j) = s * p.pr ((B.d.i₀ *ᵥ vecB B.o B.ζ) r) := by
    rintro ⟨j, hj⟩ (h : j = ρ) r
    exact (dif_neg (show ¬ j < ρ by omega)).trans (dif_pos h)
  have b2 : ∀ (i : Fin ρ) (j : Fin (2 * ρ + 1)), j.val + i.val = 2 * ρ → ∀ r,
      β r (Sum.inr j) = s * (-p.hz B / p.xi) * (-1 / p.xi) ^ (ρ - 1 - i.val) * p.pr (B.d.e' r i) := by
    rintro ⟨i, hi⟩ ⟨j, hj⟩ (h : j + i = 2 * ρ) r
    obtain rfl : i = 2 * ρ - j := by omega
    exact (dif_neg (show ¬ j < ρ by omega)).trans (dif_neg (show ¬ j = ρ by omega))
  obtain ⟨F, hF⟩ := Frame.exists_of_vecMul β
    (by rw [Fintype.card_sum, FA.card_eq, ← B.d.rank_add, ← B.o.rank_add, B.line.1, Fintype.card_fin]; omega)
    (fun v hv => by
      refine hyp_eq_zero (p.π.comp (incA D)) B.d ?_
        (orth_eq_zero (p.π.comp (incA D)) B.o B.line (FA.eq_zero ?_) ?_) ?_
      · funext i
        have := congrFun hv (Sum.inr ⟨i.val, by omega⟩)
        refine dot_eq_zero_of_smul (c := s * p.xi ^ (ρ - i.val)) (mul_ne_zero hs (pow_ne_zero _ hx)) ?_
        refine Eq.trans ?_ this
        exact congrArg (v ⬝ᵥ ·) (funext fun r => (b1 i _ rfl r).symm)
      · rw [Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, ← Matrix.mul_assoc, ← Matrix.map_mul]
        funext a; exact congrFun hv (Sum.inl a)
      · have := congrFun hv (Sum.inr ⟨ρ, by omega⟩)
        rw [← Matrix.dotProduct_mulVec]
        refine dot_eq_zero_of_smul hs ?_
        refine Eq.trans ?_ this
        refine congrArg (v ⬝ᵥ ·) (funext fun r => ((b0 _ rfl r).trans ?_).symm)
        exact congrArg (s * ·) (RingHom.map_mulVec (p.π.comp (incA D)) _ _ r)
      · funext i
        have := congrFun hv (Sum.inr ⟨2 * ρ - i.val, by omega⟩)
        refine dot_eq_zero_of_smul (c := s * (-p.hz B / p.xi) * (-1 / p.xi) ^ (ρ - 1 - i.val))
          (mul_ne_zero (mul_ne_zero hs (div_ne_zero (neg_ne_zero.2 (p.hz_ne_zero B)) hx))
            (pow_ne_zero _ (div_ne_zero (by simp) hx))) ?_
        refine Eq.trans ?_ this
        exact congrArg (v ⬝ᵥ ·) (funext fun r => (b2 i _ (by have := i.2; dsimp only; omega) r).symm))
  exact ⟨F, rfl, fun r a => by rw [hF]; rfl, by rw [hF]; exact b1, by rw [hF]; exact b0, by rw [hF]; exact b2⟩

end Place

theorem normalFrames_exist : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (n : Type) [Fintype n] [DecidableEq n] (ρ : ℕ) (s : k), s ≠ 0 → (∀ (B : BesLev D ρ) (FA : GlobalTheory.LocMod.Frame k B.A.rank n), (∃ F, p.IsCoreFrame B s FA F) ∧ (∃ F : GlobalTheory.LocMod.Frame k B.V.rank (n ⊕ Fin (2 * ρ + 1)), p.IsBesFrame B s FA F) ∧ p.hz B ≠ 0) ∧ ∀ (J : JacLev D ρ) (hh : k), hh ≠ 0 → ∀ F₀ : GlobalTheory.LocMod.Frame k J.W₀.rank n, ∃ F : GlobalTheory.LocMod.Frame k J.W.rank (n ⊕ Fin (2 * ρ)), p.IsJacFrame J s hh F₀ F :=
  fun _ _ _ _ _ _ p _ _ _ _ _ hs =>
    ⟨fun B FA => ⟨p.exists_isCoreFrame hs B FA, p.exists_isBesFrame hs B FA, p.hz_ne_zero B⟩,
      fun J _ hh0 F₀ => p.exists_isJacFrame hs J hh0 F₀⟩

end GlobalTheory.LocMod
