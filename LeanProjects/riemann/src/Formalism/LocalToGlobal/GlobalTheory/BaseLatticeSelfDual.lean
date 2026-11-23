import Formalism.LocalToGlobal.GlobalTheory.ExistsUnitaryOneDetEq
import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel
import Formalism.HermitianLattices.HermitianLatticesProofs.DualLattice
import Formalism.HermitianLattices.HermitianLatticesProofs.DualBasic
import Formalism.HermitianLattices.HermitianLatticesProofs.MajDual

noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace Formalism.L2.GlobalTheoryTheory.Comp

open Formalism.UG Formalism.UG.CS Formalism.UG.P Formalism.BasicNotions

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]

local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "ιA" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)

structure Coord (hc : CMData F E) (S : HSpace E) (n : Type) [Fintype n] where
  κ : S.V ≃ₗ[E] (n → E)
  J : Matrix n n E
  form : ∀ x y, S.hT x y = hform (hc.sig : E →+* E) J (κ x) (κ y)

variable {hc : CMData F E} {S : HSpace E}

def Coord.lat (K : Coord hc S n) (L : Submodule (𝓞 E) S.V) : Submodule (𝓞 E) (n → E) :=
  L.map ((K.κ : S.V →ₗ[E] (n → E)).restrictScalars (𝓞 E))

theorem Coord.mem_lat (K : Coord hc S n) (L : Submodule (𝓞 E) S.V) (y : n → E) : y ∈ K.lat L ↔ K.κ.symm y ∈ L := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    show K.κ.symm (K.κ x) ∈ L
    rwa [LinearEquiv.symm_apply_apply]
  · intro h
    exact ⟨_, h, K.κ.apply_symm_apply y⟩

theorem Coord.lat_dual (K : Coord hc S n) (L : Submodule (𝓞 E) S.V) :
    K.lat (Formalism.HermitianLatticesTheory.dual S.hT L) = dl hc.sig K.J (K.lat L) := by
  ext y
  rw [K.mem_lat, Formalism.HermitianLatticesTheory.dualBasic_mem_dual, mem_dl]
  constructor
  · rintro h _ ⟨x, hx, rfl⟩
    have h1 := h x hx
    rw [K.form, LinearEquiv.apply_symm_apply] at h1
    obtain ⟨r, hr⟩ := Submodule.mem_one.1 h1
    exact ⟨r, hr⟩
  · intro h x hx
    have h1 := h (K.κ x) ⟨x, hx, rfl⟩
    rw [K.form, LinearEquiv.apply_symm_apply]
    obtain ⟨r, hr⟩ := h1
    exact Submodule.mem_one.2 ⟨r, hr⟩

theorem Coord.isLat_lat (K : Coord hc S n) {L : Submodule (𝓞 E) S.V} (hL : Submodule.IsLattice E L) :
    IsLat (K.lat L) := by
  refine ⟨Module.Finite.iff_fg.2 (hL.fg.map _), ?_⟩
  rw [eq_top_iff]
  intro y _
  have h1 : K.κ.symm y ∈ Submodule.span E (L : Set S.V) := by rw [hL.span_eq_top]; trivial
  have h2 : K.κ (K.κ.symm y) ∈ (Submodule.span E (L : Set S.V)).map (K.κ : S.V →ₗ[E] (n → E)) := ⟨_, h1, rfl⟩
  rw [LinearEquiv.apply_symm_apply, Submodule.map_span] at h2
  exact h2

theorem Coord.exists_lat (K : Coord hc S n) {M : Submodule (𝓞 E) (n → E)} (hM : IsLat M) :
    ∃ L : Submodule (𝓞 E) S.V, Submodule.IsLattice E L ∧ K.lat L = M := by
  refine ⟨M.map ((K.κ.symm : (n → E) →ₗ[E] S.V).restrictScalars (𝓞 E)), ⟨(Module.Finite.iff_fg.1 hM.1).map _, ?_⟩, ?_⟩
  · rw [eq_top_iff]
    intro x _
    have h1 : K.κ x ∈ Submodule.span E (M : Set (n → E)) := by rw [hM.2]; trivial
    have h2 : K.κ.symm (K.κ x) ∈ (Submodule.span E (M : Set (n → E))).map (K.κ.symm : (n → E) →ₗ[E] S.V) := ⟨_, h1, rfl⟩
    rw [LinearEquiv.symm_apply_apply, Submodule.map_span] at h2
    exact h2
  · ext y
    rw [K.mem_lat]
    constructor
    · rintro ⟨z, hz, hzy⟩
      have : z = y := K.κ.symm.injective hzy
      rwa [← this]
    · intro hy
      exact ⟨y, hy, rfl⟩

theorem star_int (r : 𝓞 E) : star (algebraMap (𝓞 E) E r) ∈ Set.range (algebraMap (𝓞 E) E) :=
  ⟨⟨_, Formalism.HermitianLatticesTheory.majDual_star_int r⟩, rfl⟩

theorem Coord.isLat_dl (K : Coord hc S n) (M : Submodule (𝓞 E) (n → E)) (hM : IsLat M) : IsLat (dl hc.sig K.J M) := by
  obtain ⟨L, hL, rfl⟩ := K.exists_lat hM
  rw [← K.lat_dual]
  exact K.isLat_lat (Formalism.HermitianLatticesTheory.dualLattice (𝓞 E) E S.V S.hT S.herm S.nondeg star_int L hL).1

theorem Coord.lat_companion (K : Coord hc S n) (L : Submodule (𝓞 E) S.V) (a : 𝓞 E) :
    K.lat (L ⊔ Ideal.span {a} • Formalism.HermitianLatticesTheory.dual S.hT L) =
      K.lat L ⊔ Ideal.span {a} • dl hc.sig K.J (K.lat L) := by
  rw [← K.lat_dual]
  unfold Coord.lat
  rw [Submodule.map_sup, Submodule.map_smul'']

theorem Coord.companion (K : Coord hc S n) {L : Submodule (𝓞 E) S.V} (hL : Submodule.IsLattice E L)
    {Λb : Submodule (𝓞 E) (n → E)} (hΛb : IsLat Λb) (g : GL n 𝒜)
    (hg : g ∈ UPts hc.sig K.J (FiniteAdeleRing (𝓞 F) F))
    (hyl : ∀ u : n → 𝒜, u ∈ hat F (K.lat L) ↔ ((g⁻¹ : GL n 𝒜) : Matrix n n 𝒜) *ᵥ u ∈ hat F Λb)
    {a : 𝓞 E} (ha : a ≠ 0) (hbase : Λb ⊔ Ideal.span {a} • dl hc.sig K.J Λb = K.lat S.L0) :
    K.lat (L ⊔ Ideal.span {a} • Formalism.HermitianLatticesTheory.dual S.hT L) = globLat g (K.lat S.L0) := by
  rw [K.lat_companion, eq_glob_of_hat (K.isLat_lat hL) g hyl, ← hbase,
    glob_companion hc.sig K.J K.isLat_dl hΛb ha g hg]

theorem Coord.base_lattice_self_dual (K : Coord hc S n) : dl hc.sig K.J (K.lat S.L0) = K.lat S.L0 := by
  rw [← K.lat_dual]
  have : Formalism.HermitianLatticesTheory.dual S.hT S.L0 = S.L0 := S.baseLattice_isUnimodular
  rw [this]

end Formalism.L2.GlobalTheoryTheory.Comp

end
