import Formalism.LocalToGlobal.GlobalTheory.BaseLatticeSelfDual

noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace Formalism.L2.GlobalTheoryTheory.Comp

open Formalism.UG Formalism.UG.CS Formalism.UG.P Formalism.BasicNotions Formalism.L2.Herm

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]

local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "ιA" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)

variable {hc : CMData F E} {S : HSpace E} {N : ℕ}

def Coord.Q (K : Coord hc S n) (co : S.V ≃ₗ[E] (Fin N → E)) : Matrix (Fin N) n E :=
  LinearMap.toMatrix' ((K.κ.symm.trans co : (n → E) ≃ₗ[E] (Fin N → E)) : (n → E) →ₗ[E] (Fin N → E))

def Coord.Q' (K : Coord hc S n) (co : S.V ≃ₗ[E] (Fin N → E)) : Matrix n (Fin N) E :=
  LinearMap.toMatrix' ((co.symm.trans K.κ : (Fin N → E) ≃ₗ[E] (n → E)) : (Fin N → E) →ₗ[E] (n → E))

theorem Coord.Q_mulVec (K : Coord hc S n) (co : S.V ≃ₗ[E] (Fin N → E)) (v : n → E) :
    K.Q co *ᵥ v = co (K.κ.symm v) := by
  unfold Coord.Q
  rw [LinearMap.toMatrix'_mulVec]
  rfl

theorem Coord.Q_mul_Q' (K : Coord hc S n) (co : S.V ≃ₗ[E] (Fin N → E)) : K.Q co * K.Q' co = 1 := by
  unfold Coord.Q Coord.Q'
  rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]
  congr 1
  apply LinearMap.ext
  intro v
  simp

theorem Coord.Q'_mul_Q (K : Coord hc S n) (co : S.V ≃ₗ[E] (Fin N → E)) : K.Q' co * K.Q co = 1 := by
  unfold Coord.Q Coord.Q'
  rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]
  congr 1
  apply LinearMap.ext
  intro v
  simp

theorem hform_one (x y : Fin N → E) : hform (hc.sig : E →+* E) (1 : Matrix (Fin N) (Fin N) E) x y = stdH E N x y := by
  unfold hform stdH
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · rw [Matrix.one_apply_eq, mul_one]; rfl
  · intro j _ hj
    rw [Matrix.one_apply_ne (Ne.symm hj), mul_zero, zero_mul]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem Coord.hQ (K : Coord hc S n) (co : S.V ≃ₗ[E] (Fin N → E))
    (hco : ∀ x y, stdH E N (co x) (co y) = S.hT x y) :
    cT (hc.sig : E →+* E) (K.Q co) * (1 : Matrix (Fin N) (Fin N) E) * K.Q co = K.J := by
  ext i j
  have h1 := hform_single (hc.sig : E →+* E) (cT (hc.sig : E →+* E) (K.Q co) * (1 : Matrix (Fin N) (Fin N) E) * K.Q co) i j
  have h2 := hform_single (hc.sig : E →+* E) K.J i j
  rw [← h1, ← h2, ← hform_mulVec_rect, hform_one, K.Q_mulVec, K.Q_mulVec, hco, K.form,
    LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

theorem Coord.mem_mapQ_lat (K : Coord hc S n) (co : S.V ≃ₗ[E] (Fin N → E)) (X : Submodule (𝓞 E) S.V) (y : S.V) :
    co y ∈ mapQ (K.Q co) (K.lat X) ↔ y ∈ X := by
  rw [mem_mapQ]
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, h⟩
    have h1 : K.Q co *ᵥ (K.κ x) = co y := h
    rw [K.Q_mulVec, LinearEquiv.symm_apply_apply] at h1
    rwa [← co.injective h1]
  · intro hy
    exact ⟨K.κ y, ⟨y, hy, rfl⟩, by rw [K.Q_mulVec, LinearEquiv.symm_apply_apply]⟩

theorem isLat_mapQ {m : Type} [Fintype m] [DecidableEq m] (Q : Matrix m n E) (Q' : Matrix n m E) (h1 : Q * Q' = 1)
    {M : Submodule (𝓞 E) (n → E)} (hM : IsLat M) : IsLat (mapQ Q M) := by
  refine ⟨Module.Finite.iff_fg.2 ((Module.Finite.iff_fg.1 hM.1).map _), ?_⟩
  rw [eq_top_iff]
  intro y _
  have h2 : Q' *ᵥ y ∈ Submodule.span E (M : Set (n → E)) := by rw [hM.2]; trivial
  have h3 : Q *ᵥ (Q' *ᵥ y) ∈ (Submodule.span E (M : Set (n → E))).map (Matrix.mulVecLin Q) := ⟨_, h2, rfl⟩
  rw [mulVec_mulVec, h1, one_mulVec, Submodule.map_span] at h3
  exact h3

theorem Coord.isSDLat (K : Coord hc S n) (co : S.V ≃ₗ[E] (Fin N → E))
    (hco : ∀ x y, stdH E N (co x) (co y) = S.hT x y) {M : Submodule (𝓞 E) (n → E)} (hM : IsLat M)
    (hsd : dl hc.sig K.J M = M) : IsSDLat E N (mapQ (K.Q co) M) := by
  have h := isLat_mapQ (K.Q co) (K.Q' co) (K.Q_mul_Q' co) hM
  refine ⟨Module.Finite.iff_fg.1 h.1, h.2, fun y => ?_⟩
  have h1 := dl_mapQ hc.sig K.J (K.Q co) (K.Q' co) (K.Q_mul_Q' co) (K.hQ co hco) M
  rw [hsd] at h1
  conv_lhs => rw [← h1]
  rw [mem_dl]
  constructor
  · intro h2 x hx
    rw [← hform_one (hc := hc)]
    exact h2 x hx
  · intro h2 x hx
    rw [hform_one]
    exact h2 x hx

def Coord.StandardHermitianLattice (K : Coord hc S n) (co : S.V ≃ₗ[E] (Fin N → E))
    (hco : ∀ x y, stdH E N (co x) (co y) = S.hT x y) : SDLat E N :=
  ⟨mapQ (K.Q co) (K.lat S.L0), K.isSDLat co hco (K.isLat_lat S.standardTuple_isLattice) K.base_lattice_self_dual⟩

theorem mem_companion (L D : Submodule (𝓞 E) S.V) (a : 𝓞 E) (y : S.V) :
    y ∈ L ⊔ Ideal.span {a} • D ↔ ∃ x ∈ L, ∃ b ∈ D, y = x + (a : E) • b := by
  rw [Submodule.mem_sup, Submodule.ideal_span_singleton_smul]
  constructor
  · rintro ⟨x, hx, z, hz, rfl⟩
    obtain ⟨b, hb, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hz
    exact ⟨x, hx, b, hb, by rw [← algebraMap_smul E a b]⟩
  · rintro ⟨x, hx, b, hb, rfl⟩
    exact ⟨x, hx, a • b, Submodule.smul_mem_pointwise_smul b a D hb, by rw [← algebraMap_smul E a b]⟩

theorem Coord.main (K : Coord hc S n) (co : S.V ≃ₗ[E] (Fin N → E))
    (hco : ∀ x y, stdH E N (co x) (co y) = S.hT x y)
    {L : Submodule (𝓞 E) S.V} (hL : Submodule.IsLattice E L)
    {Λb : Submodule (𝓞 E) (n → E)} (hΛb : IsLat Λb) (g : GL n 𝒜)
    (hg : g ∈ UPts hc.sig K.J (FiniteAdeleRing (𝓞 F) F))
    (hyl : ∀ u : n → 𝒜, u ∈ hat F (K.lat L) ↔ ((g⁻¹ : GL n 𝒜) : Matrix n n 𝒜) *ᵥ u ∈ hat F Λb)
    {a : 𝓞 E} (ha : a ≠ 0) (hbase : Λb ⊔ Ideal.span {a} • dl hc.sig K.J Λb = K.lat S.L0) :
    ∃ Ln : SDLat E N,
      (∀ y, co y ∈ Ln.1 ↔ ∃ x ∈ L, ∃ b ∈ Formalism.HermitianLatticesTheory.dual S.hT L, y = x + (a : E) • b) ∧
      ∃ g' ∈ UstdAf hc N, Carries g' (K.StandardHermitianLattice co hco).1 Ln.1 ∧
        Matrix.GeneralLinearGroup.det g' = Matrix.GeneralLinearGroup.det g := by
  have hcomp := K.companion hL hΛb g hg hyl ha hbase
  have hL0 := K.isLat_lat S.standardTuple_isLattice
  refine ⟨⟨mapQ (K.Q co) (globLat g (K.lat S.L0)),
    K.isSDLat co hco (isLat_glob hL0 g) (glob_selfdual hc.sig K.J K.isLat_dl hL0 K.base_lattice_self_dual g hg)⟩, ?_,
    conjQ (K.Q co) (K.Q' co) (K.Q_mul_Q' co) (K.Q'_mul_Q co) g,
    conjQ_mem hc.sig K.J _ _ _ _ (K.hQ co hco) g hg, ?_, ?_⟩
  · intro y
    show co y ∈ mapQ (K.Q co) (globLat g (K.lat S.L0)) ↔ _
    rw [← hcomp, K.mem_mapQ_lat, mem_companion]
  · intro v
    exact mem_hat_map_glob (K.Q co) (K.Q' co) (K.Q_mul_Q' co) (K.Q'_mul_Q co) hL0 g v
  · ext
    exact det_conjQ (K.Q co) (K.Q' co) (K.Q_mul_Q' co) (K.Q'_mul_Q co) g

end Formalism.L2.GlobalTheoryTheory.Comp

end
