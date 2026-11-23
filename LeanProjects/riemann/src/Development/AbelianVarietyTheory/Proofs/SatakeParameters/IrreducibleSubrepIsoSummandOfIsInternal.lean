import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MapMulVecMemOfMemSpan
open Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.SplitField

namespace GlobalTheory.SplitField

theorem isoSub_summand_of_isInternal {Γ L : Type} [Group Γ] [Field L] {a n : ℕ}
    (τ : Γ →* GL (Fin a) L) (Us : Fin n → Submodule L (Fin a → L)) (hI : DirectSum.IsInternal Us)
    (hU : ∀ m, IsIrrSub τ (Us m)) (W : Submodule L (Fin a → L)) (hW : IsIrrSub τ W) :
    ∃ m, IsoSub τ W (Us m) := by
  classical
  let T : Γ → (Fin a → L) →ₗ[L] (Fin a → L) := fun g =>
    Matrix.mulVecLin ((τ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L)
  have hTv : ∀ g v, T g v = ((τ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L).mulVec v := fun g v => rfl
  let e := LinearEquiv.ofBijective (DirectSum.coeLinearMap Us) hI
  let P : ∀ m, (Fin a → L) →ₗ[L] Us m := fun m =>
    (DirectSum.component L (Fin n) (fun k => Us k) m).comp
      (e.symm : (Fin a → L) →ₗ[L] DirectSum (Fin n) fun k => Us k)
  have hstab : ∀ g k, ∀ v ∈ Us k, T g v ∈ Us k := fun g k v hv => (hU k).2.1 g v hv
  let φ : Γ → ∀ k, Us k →ₗ[L] Us k := fun g k => (T g).restrict (hstab g k)
  have hcomm : ∀ g (d : DirectSum (Fin n) fun k => Us k),
      DirectSum.coeLinearMap Us (DFinsupp.mapRange.linearMap (φ g) d) = T g (DirectSum.coeLinearMap Us d) := by
    intro g
    have : (DirectSum.coeLinearMap Us).comp (DFinsupp.mapRange.linearMap (φ g)) =
        (T g).comp (DirectSum.coeLinearMap Us) := by
      apply DirectSum.linearMap_ext
      intro k
      apply LinearMap.ext; intro x
      simp only [LinearMap.comp_apply, DirectSum.lof_eq_of, DFinsupp.mapRange.linearMap_apply]
      rw [show (DirectSum.of (fun i => Us i) k x) = DFinsupp.single k x from rfl]
      rw [show DFinsupp.mapRange.linearMap (φ g) (DFinsupp.single k x) = DFinsupp.single k (φ g k x) from
        DFinsupp.mapRange_single (hf := fun i => map_zero _)]
      rw [show (DFinsupp.single k ((φ g k) x) : DirectSum (Fin n) fun i => Us i) =
        DirectSum.of (fun i => Us i) k (φ g k x) from rfl]
      simp [DirectSum.coeLinearMap_of, φ]
      rw [show (DFinsupp.single k x : DirectSum (Fin n) fun i => Us i) = DirectSum.of (fun i => Us i) k x from rfl,
        DirectSum.coeLinearMap_of]
    intro d
    exact LinearMap.congr_fun this d
  have hequiv : ∀ g m v, (P m (T g v) : Fin a → L) = T g (P m v) := by
    intro g m v
    have h1 : e.symm (T g v) = DFinsupp.mapRange.linearMap (φ g) (e.symm v) := by
      apply e.injective
      rw [LinearEquiv.apply_symm_apply]
      show _ = DirectSum.coeLinearMap Us _
      rw [hcomm]
      congr 1
      exact (e.apply_symm_apply v).symm
    simp only [P, LinearMap.comp_apply, LinearEquiv.coe_coe, h1]
    simp only [← DirectSum.apply_eq_component, DFinsupp.mapRange.linearMap_apply, DFinsupp.mapRange_apply]
    rfl
  obtain ⟨w, hwW, hw0⟩ := (Submodule.ne_bot_iff W).1 hW.1
  obtain ⟨m, hm⟩ : ∃ m, P m w ≠ 0 := by
    by_contra h
    push_neg at h
    apply hw0
    have h0 : e.symm w = 0 := by
      ext k : 1
      have := h k
      simpa [P, ← DirectSum.apply_eq_component] using this
    have := e.apply_symm_apply w
    rw [h0, map_zero] at this
    exact this.symm
  refine ⟨m, ?_⟩
  have hKinv : IsInv τ (W ⊓ LinearMap.ker (P m)) := by
    rintro g v ⟨hvW, hvK⟩
    have hvK' : P m v = 0 := hvK
    refine ⟨hW.2.1 g v hvW, show P m _ = 0 from ?_⟩
    apply Subtype.ext
    rw [← hTv, hequiv, hvK']
    simp
  have hK : W ⊓ LinearMap.ker (P m) = ⊥ := by
    rcases hW.2.2 _ inf_le_left hKinv with h | h
    · exact h
    · exfalso
      have : w ∈ W ⊓ LinearMap.ker (P m) := by rw [h]; exact hwW
      exact hm this.2
  let R : Submodule L (Fin a → L) := (W.map (P m)).map (Us m).subtype
  have hRinv : IsInv τ R := by
    rintro g y ⟨y', ⟨v, hv, rfl⟩, rfl⟩
    refine ⟨P m (T g v), ⟨T g v, hW.2.1 g v hv, rfl⟩, ?_⟩
    simp only [Submodule.coe_subtype]
    rw [hequiv, hTv]
  have hR : R = Us m := by
    rcases (hU m).2.2 R (Submodule.map_subtype_le _ _) hRinv with h | h
    · exfalso
      have : ((P m w : Us m) : Fin a → L) ∈ R := ⟨P m w, ⟨w, hwW, rfl⟩, rfl⟩
      rw [h, Submodule.mem_bot] at this
      exact hm (Subtype.ext this)
    · exact h
  let f : W →ₗ[L] Us m := (P m).comp W.subtype
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    rw [LinearMap.mem_ker] at hx
    have : (x : Fin a → L) ∈ W ⊓ LinearMap.ker (P m) := ⟨x.2, hx⟩
    rw [hK, Submodule.mem_bot] at this
    exact (Submodule.mem_bot L).2 (Subtype.ext this)
  have hsurj : Function.Surjective f := by
    intro u
    have hu : (u : Fin a → L) ∈ R := by rw [hR]; exact u.2
    obtain ⟨y, ⟨v, hv, rfl⟩, hy⟩ := hu
    exact ⟨⟨v, hv⟩, Subtype.ext hy⟩
  refine ⟨LinearEquiv.ofBijective f ⟨hinj, hsurj⟩, fun g v h => ?_⟩
  simp only [LinearEquiv.ofBijective_apply, f, LinearMap.comp_apply, Submodule.coe_subtype]
  have := hequiv g m (v : Fin a → L)
  rw [hTv, hTv] at this
  exact this

end GlobalTheory.SplitField
