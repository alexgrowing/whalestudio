import Formalism.SharpRestriction.LevelLetterCocycles.RealisedOfCoordArc
import Formalism.SharpRestriction.LevelLetterCocycles.CrystallineMapLemmas

noncomputable section

namespace Formalism.MainNotions.N.Ln03.Pf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G TensorProduct Formalism.MainNotions.N.Ln03 Module

section Period

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

theorem jb_Fil_anti {a b : ℤ} (hab : a ≤ b) : PD.Fil b ≤ PD.Fil a := by
  obtain ⟨k, rfl⟩ := Int.le.dest hab
  clear hab
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show a + ((k + 1 : ℕ) : ℤ) = a + k + 1 by push_cast; ring]
    exact (PD.Fil_anti (a + k)).trans ih

theorem jb_FilV_anti : Antitone (FilV PD (LL := LL) (V := V)) := by
  intro a b hab
  have h : (PD.Fil b).restrictScalars Qp ≤ (PD.Fil a).restrictScalars Qp := jb_Fil_anti PD hab
  unfold FilV
  rw [← Submodule.subtype_comp_inclusion _ _ h]
  have e : AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V)
      (((PD.Fil a).restrictScalars Qp).subtype ∘ₗ Submodule.inclusion h) =
      AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) ((PD.Fil a).restrictScalars Qp).subtype ∘ₗ
        AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (Submodule.inclusion h) := by
    rw [← AlgebraTensorModule.map_comp, LinearMap.id_comp]
  rw [e]
  exact LinearMap.range_comp_le_range _ _

theorem jb_FilV_exh (y : V ⊗[Qp] BdR) : ∃ a, y ∈ FilV PD (LL := LL) (V := V) a := by
  induction y using TensorProduct.induction_on with
  | zero => exact ⟨0, zero_mem _⟩
  | tmul v b =>
    obtain ⟨a, ha⟩ := PD.Fil_exh b
    exact ⟨a, ⟨v ⊗ₜ ⟨b, ha⟩, by simp⟩⟩
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨min a b, add_mem (jb_FilV_anti PD (min_le_left a b) ha)
      (jb_FilV_anti PD (min_le_right a b) hb)⟩

theorem jb_FilV_sep (y : V ⊗[Qp] BdR) (hy : ∀ a, y ∈ FilV PD (LL := LL) (V := V) a) : y = 0 := by
  classical
  let bV := Module.Free.chooseBasis Qp V
  let e := TensorProduct.equivFinsuppOfBasisLeft (N := BdR) bV
  have hc : ∀ a, ∀ z ∈ FilV PD (LL := LL) (V := V) a, ∀ i, e z i ∈ PD.Fil a := by
    intro a z hz i
    obtain ⟨t, rfl⟩ := hz
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul v f =>
      simp only [AlgebraTensorModule.map_tmul, LinearMap.id_apply, Submodule.subtype_apply, e,
        TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply]
      exact (PD.Fil a).smul_of_tower_mem _ f.2
    | add x y hx hy =>
      rw [map_add, map_add, Finsupp.add_apply]
      exact add_mem hx hy
  have h0 : e y = 0 := by
    ext i
    exact PD.Fil_sep _ (fun a => hc a y (hy a) i)
  exact e.injective (by rw [h0, map_zero])

theorem jb_FildR_anti (ρ : Representation LL G V) (τ : K →ₐ[Qp] LL) : Antitone (FildR PD ρ τ) :=
  fun _ _ hab => inf_le_inf_left _ (jb_FilV_anti PD hab)

theorem jb_bound (ρ : Representation LL G V) (τ : K →ₐ[Qp] LL) (hfin : FiniteDimensional LL ↥(DdRE PD ρ τ)) :
    ∃ a₀ a₁ : ℤ, ∀ a, IsJumpV PD ρ τ a → a₀ ≤ a ∧ a ≤ a₁ := by
  classical
  set D := DdRE PD ρ τ with hD
  have hFD : ∀ a, FildR PD ρ τ a ≤ D := fun a => inf_le_left

  let bD := Module.finBasis LL ↥D
  have hex : ∀ j, ∃ a, ((bD j : ↥D) : V ⊗[Qp] BdR) ∈ FilV PD (LL := LL) (V := V) a :=
    fun j => jb_FilV_exh PD (LL := LL) (V := V) _
  choose aj haj using hex
  set a₀ : ℤ := -(∑ j, |aj j|) with ha₀
  have ha₀j : ∀ j, a₀ ≤ aj j := by
    intro j
    have h1 : |aj j| ≤ ∑ k, |aj k| :=
      Finset.single_le_sum (f := fun k => |aj k|) (fun k _ => abs_nonneg _) (Finset.mem_univ j)
    have h2 := neg_abs_le (aj j)
    linarith
  have hlow : ∀ a, a ≤ a₀ → FildR PD ρ τ a = D := by
    intro a ha
    refine le_antisymm (hFD a) (le_inf le_rfl ?_)
    have hspan : (Submodule.span LL (Set.range bD)).map D.subtype = D := by
      rw [bD.span_eq, Submodule.map_top, Submodule.range_subtype]
    rw [← hspan, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
    exact jb_FilV_anti PD (ha.trans (ha₀j j)) (haj j)

  let f : ℕ → ℕ := fun k => finrank LL ↥(FildR PD ρ τ (k : ℤ))
  have hne : ∃ m, ∃ k, f k = m := ⟨_, 0, rfl⟩
  let m := Nat.find hne
  obtain ⟨k₀, hk₀⟩ := Nat.find_spec hne
  have hmin : ∀ k, m ≤ f k := fun k => Nat.find_min' hne ⟨k, rfl⟩
  have hfinF : ∀ a, FiniteDimensional LL ↥(FildR PD ρ τ a) :=
    fun a => Submodule.finiteDimensional_of_le (hFD a)
  have hstab : ∀ k : ℕ, k₀ ≤ k → FildR PD ρ τ (k : ℤ) = FildR PD ρ τ (k₀ : ℤ) := by
    intro k hk
    have hle : FildR PD ρ τ (k : ℤ) ≤ FildR PD ρ τ (k₀ : ℤ) := jb_FildR_anti PD ρ τ (by exact_mod_cast hk)
    have hr1 : f k ≤ f k₀ := Submodule.finrank_mono hle
    have hr2 := hmin k
    exact Submodule.eq_of_le_of_finrank_eq hle (by show f k = f k₀; omega)
  have hbot : FildR PD ρ τ (k₀ : ℤ) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Submodule.mem_bot]
    apply jb_FilV_sep PD (LL := LL) (V := V) x
    intro a
    rcases le_total a (k₀ : ℤ) with h | h
    · exact jb_FilV_anti PD (LL := LL) (V := V) h hx.2
    · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le (le_trans (Int.natCast_nonneg k₀) h)
      have hk : k₀ ≤ k := by exact_mod_cast h
      rw [← hstab k hk] at hx
      exact hx.2
  have hhigh : ∀ a, (k₀ : ℤ) ≤ a → FildR PD ρ τ a = ⊥ := fun a ha =>
    eq_bot_iff.mpr (hbot ▸ jb_FildR_anti PD ρ τ ha)
  refine ⟨a₀, (k₀ : ℤ) - 1, fun a ha => ⟨?_, ?_⟩⟩
  · by_contra hlt
    exact ha (by rw [hlow a (by omega), hlow (a + 1) (by omega)])
  · by_contra hlt
    exact ha (by rw [hhigh a (by omega), hhigh (a + 1) (by omega)])

end Period

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}
    [Fintype (K →ₐ[Qp] LL)]

theorem jumpsBdd_holds (hDR : Formalism.MainNotions.TruncatedSeriesCountingBounds.DdREqDcris PD LL) (hK : Function.Bijective (algebraMap K₀ K)) :
    ∀ T : LocLat G Qp LL O, CrysLat PD T → ∃ M h : ZMod n → ℕ, Formalism.MainNotions.LiftingTheory.JumpsLet W T M h := by
  intro T hT
  have hfin : ∀ τ : K →ₐ[Qp] LL, FiniteDimensional LL ↥(DdRE PD T.ρ τ) :=
    fun τ => ((hDR hK T.V T.ρ T.cont hT.2.2.2).2 τ).1
  choose a₀ a₁ hab using fun τ => jb_bound PD T.ρ τ (hfin τ)
  refine ⟨fun _ => Finset.univ.sup (fun τ => (-a₀ τ).toNat),
    fun _ => Finset.univ.sup (fun τ => (a₁ τ).toNat), ?_⟩
  intro i τ _ a ha
  obtain ⟨h0, h1⟩ := hab τ a ha
  have e0 : (-a₀ τ).toNat ≤ Finset.univ.sup (fun τ => (-a₀ τ).toNat) :=
    Finset.le_sup (f := fun τ => (-a₀ τ).toNat) (Finset.mem_univ τ)
  have e1 : (a₁ τ).toNat ≤ Finset.univ.sup (fun τ => (a₁ τ).toNat) :=
    Finset.le_sup (f := fun τ => (a₁ τ).toNat) (Finset.mem_univ τ)
  have f0 := Int.self_le_toNat (-a₀ τ)
  have f1 := Int.self_le_toNat (a₁ τ)
  have g0 : (((-a₀ τ).toNat : ℕ) : ℤ) ≤ ((Finset.univ.sup (fun τ => (-a₀ τ).toNat) : ℕ) : ℤ) := by exact_mod_cast e0
  have g1 : (((a₁ τ).toNat : ℕ) : ℤ) ≤ ((Finset.univ.sup (fun τ => (a₁ τ).toNat) : ℕ) : ℤ) := by exact_mod_cast e1
  simp only [Set.mem_Icc]
  constructor <;> omega

end Formalism.MainNotions.N.Ln03.Pf
