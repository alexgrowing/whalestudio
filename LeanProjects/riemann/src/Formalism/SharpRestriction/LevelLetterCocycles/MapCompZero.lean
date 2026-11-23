import Formalism.SharpRestriction.LevelLetterCocycles.LamPS
import Formalism.SharpRestriction.LevelLetterCocycles.BaseChangePreservesUnitaryOf

noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

theorem mem_letS (c : ZMod n) (x : W.DD T) : x ∈ letS W T c ↔ (letE c : LetA O n) • x = x := by
  unfold letS
  rw [LinearMap.mem_ker, LinearMap.restrictScalars_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero]

theorem mem_DelS (x : W.DD T) : x ∈ DelS W T ↔ ∀ δ ∈ W.DelF, W.γD T δ x = x := by
  unfold DelS
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]

theorem mem_NcS (c : ZMod n) (x : W.DD T) :
    x ∈ NcS W T c ↔ x ∈ W.N T ∧ (∀ δ ∈ W.DelF, W.γD T δ x = x) ∧ (letE c : LetA O n) • x = x := by
  unfold NcS
  rw [Submodule.mem_inf, Submodule.mem_inf, Submodule.restrictScalars_mem, mem_DelS, mem_letS, and_assoc]

theorem mem_PiNS (π' : LetA O n) (k : ℕ) (x : W.DD T) :
    x ∈ PiNS W T π' k ↔ (∃ y ∈ W.N T, π' ^ k • y = x) ∧ ∀ δ ∈ W.DelF, W.γD T δ x = x := by
  unfold PiNS
  rw [Submodule.mem_inf, Submodule.restrictScalars_mem, mem_DelS]
  unfold Formalism.MainNotions.DeltaInvariantLattices.aN
  rw [Submodule.mem_map]
  rfl

theorem mem_LamPS (Eπ : LetA O n) (h' : ℕ) (c : ZMod n) (x : W.DD T) :
    x ∈ LamPS W T Eπ h' c ↔ Eπ ^ h' • x ∈ Formalism.MainNotions.DeltaInvariantLattices.φspan W T (W.Nl T (c - 1)) ∧
      (∀ δ ∈ W.DelF, W.γD T δ x = x) ∧ (letE c : LetA O n) • x = x := by
  unfold LamPS
  rw [Submodule.mem_inf, Submodule.mem_inf, Submodule.restrictScalars_mem, Submodule.mem_comap,
    mem_DelS, mem_letS, and_assoc]
  rfl

theorem mem_InvS (π' Eπ : LetA O n) (h' k : ℕ) (c : ZMod n) (x : W.DD T) :
    x ∈ InvS W T π' Eπ h' k c ↔ x ∈ LamPS W T Eπ h' c ∧ W.γD T W.gamK x - x ∈ PiNS W T π' k := by
  unfold InvS
  rw [Submodule.mem_inf, Submodule.mem_comap, LinearMap.sub_apply, LinearMap.id_apply]

theorem PiNS_le_N (π' : LetA O n) (k : ℕ) {x : W.DD T} (hx : x ∈ PiNS W T π' k) : x ∈ W.N T := by
  obtain ⟨⟨y, hy, rfl⟩, -⟩ := (mem_PiNS W T π' k x).1 hx
  exact (W.N T).smul_mem _ hy

theorem γD_letE (g : W.Gam) (c : ZMod n) (x : W.DD T) :
    W.γD T g ((letE c : LetA O n) • x) = (letE c : LetA O n) • W.γD T g x := by
  rw [Formalism.MainNotions.LiftingTheory.wmap_γD_smul, Formalism.MainNotions.LiftingTheory.wmap_γA_letE]

theorem φD_letE (c : ZMod n) (x : W.DD T) :
    W.φD T ((letE (c - 1) : LetA O n) • x) = (letE c : LetA O n) • W.φD T x := by
  rw [Formalism.MainNotions.LiftingTheory.wmap_φD_smul, Formalism.MainNotions.LiftingTheory.wmap_φA_letE]

theorem map_letA_smul {T' : LocLat G Qp LL O} (f : LatHom T.L T'.L) (a : LetA O n) (x : W.DD T) :
    W.map f (a • x) = a • W.map f x :=
  Formalism.MainNotions.LiftingTheory.wmap_map_smul W f a x

theorem map_comp_zero {T' T'' : LocLat G Qp LL O} (ι : LatHom T.L T'.L) (π : LatHom T'.L T''.L)
    (h0 : ∀ y, π.f (ι.f y) = 0) (x : W.DD T) : W.map π (W.map ι x) = 0 := by
  rw [← W.map_comp]
  have hext : ∀ g₁ g₂ : LatHom T.L T''.L, g₁.f = g₂.f → g₁ = g₂ := by
    rintro ⟨f1, _, _, _⟩ ⟨f2, _, _, _⟩ h
    cases h
    rfl
  have hg : latAdd (latComp π ι) (latComp π ι) = latComp π ι := by
    apply hext
    ext y
    simp [latAdd, latComp, h0]
  have := W.map_latAdd (latComp π ι) (latComp π ι) x
  rw [hg] at this
  exact left_eq_add.mp this

end Local

end Formalism.MainNotions.N.Ln34

end
