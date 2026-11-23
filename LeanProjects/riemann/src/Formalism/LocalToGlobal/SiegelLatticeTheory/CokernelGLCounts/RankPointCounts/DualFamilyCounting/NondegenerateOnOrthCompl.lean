import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.JordanExists
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsRepsOfCover
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsSmulMem
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.InvMemLocROfUnimod
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.FiniteRepSetOfOrtho
import Formalism.HermitianLattices.HermitianLatticesProofs.IsomAct

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.Cnt

open Formalism.HermitianLattices.Ext.L3

def GenusMassW : Prop :=
  ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V],
    Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F → ∀ h : V →ₗ⋆[K] V →ₗ[K] K, h.IsSymm → Nondeg h →
    ∀ U : Submodule K V, IsCompl U (orthK h U) → PosDefOn h (orthK h U) →
    ∀ T₀ : Submodule (𝓞 K) V, IsLatIn (orthK h U) T₀ → Formalism.HermitianLatticesTheory.IsIntegralLat h T₀ →
    ∀ c : ℝ, MassConst K F (finrank K (orthK h U)) c →
      ∃ s : Finset (Submodule (𝓞 K) V),
        (∀ T ∈ s, IsLatIn (orthK h U) T ∧ SameGenusFix (F := F) h U T₀ T) ∧
        (∀ T, IsLatIn (orthK h U) T → SameGenusFix (F := F) h U T₀ T →
          ∃! T₁, T₁ ∈ s ∧ ∃ g ∈ isomFix h U, Formalism.HermitianLatticesTheory.gmap g T₁ = T) ∧
        (∀ T, IsLatIn (orthK h U) T → SameGenusFix (F := F) h U T₀ T → (stabFix h U T).Finite) ∧
        ((∏' 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, discAut h (orthK h U) T₀ 𝔭.1 : ℕ) : ℝ) *
            ∑ T ∈ s, ((Nat.card (stabFix h U T) : ℕ) : ℝ)⁻¹ =
          c * nM F h (orthK h U) T₀ ^ finrank K (orthK h U) *
            ∏' 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, alphaStd K 𝔭.1 (finrank K (orthK h U)) /
              alphaStd K 𝔭.1 (finrank K (orthK h U) - cJ h (orthK h U) T₀ 𝔭.1)

end Formalism.L2.SG.Pf.Cnt

namespace Formalism.L2.SG.Pf.G9

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt

theorem tprod_nat_ne_zero {ι : Type*} (f : ι → ℕ) (hf : ∀ i, f i ≠ 0) : ∏' i, f i ≠ 0 := by
  by_cases hm : Multipliable f
  · have e := hm.hasProd.eventually_mem (IsOpen.mem_nhds (isOpen_discrete {∏' i, f i}) rfl)
    obtain ⟨s, hs⟩ := e.exists
    rw [← Set.mem_singleton_iff.mp hs]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => hf i
  · rw [tprod_eq_one_of_not_multipliable hm]
    exact one_ne_zero

theorem sum_eq_of_min {n n' : ℕ} (e : Fin n → ℕ) (e' : Fin n' → ℕ)
    (H : ∀ j, ∑ i, min (e i) j = ∑ i, min (e' i) j) : ∑ i, e i = ∑ i, e' i := by
  have h1 : ∀ i, e i ≤ ∑ i, e i + ∑ i, e' i := fun i =>
    le_trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)) (Nat.le_add_right _ _)
  have h2 : ∀ i, e' i ≤ ∑ i, e i + ∑ i, e' i := fun i =>
    le_trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)) (Nat.le_add_left _ _)
  calc ∑ i, e i = ∑ i, min (e i) (∑ i, e i + ∑ i, e' i) :=
        Finset.sum_congr rfl fun i _ => (min_eq_left (h1 i)).symm
    _ = ∑ i, min (e' i) (∑ i, e i + ∑ i, e' i) := H _
    _ = ∑ i, e' i := Finset.sum_congr rfl fun i _ => min_eq_left (h2 i)

theorem card_ne_zero_eq {n : ℕ} (e : Fin n → ℕ) :
    (Finset.univ.filter fun i => e i ≠ 0).card = ∑ i, min (e i) 1 := by
  rw [Finset.card_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : e i = 0
  · rw [if_neg (not_not.mpr hi), hi]
    simp
  · rw [if_pos hi, min_eq_right (Nat.one_le_iff_ne_zero.mpr hi)]

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem mem_orthK {h : V →ₗ⋆[K] V →ₗ[K] K} {U : Submodule K V} {w : V} :
    w ∈ orthK h U ↔ ∀ u ∈ U, h u w = 0 := by
  simp [orthK, Submodule.mem_iInf, LinearMap.mem_ker]

theorem apply_mem_orthK {h : V →ₗ⋆[K] V →ₗ[K] K} {U : Submodule K V} {g : V ≃ₗ[K] V}
    (hg : g ∈ isomFix h U) {w : V} (hw : w ∈ orthK h U) : g w ∈ orthK h U := by
  rw [mem_orthK] at hw ⊢
  intro u hu
  have e : h u (g w) = h (g u) (g w) := by rw [hg.2 u hu]
  rw [e, hg.1 u w]
  exact hw u hu

theorem gmap_inf_sub {g : V ≃ₗ[K] V} (X : Submodule K V) (h1 : ∀ x ∈ X, g x ∈ X)
    (h2 : ∀ x ∈ X, g.symm x ∈ X) (Λ : Submodule (𝓞 K) V) :
    Formalism.HermitianLatticesTheory.gmap g (Λ ⊓ X.restrictScalars (𝓞 K)) =
      Formalism.HermitianLatticesTheory.gmap g Λ ⊓ X.restrictScalars (𝓞 K) := by
  have hinj : Function.Injective ((g : V →ₗ[K] V).restrictScalars (𝓞 K)) :=
    fun a b e => g.injective e
  rw [Formalism.HermitianLatticesTheory.gmap, Submodule.map_inf _ hinj]
  congr 1
  ext x
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact h1 y hy
  · intro hx
    exact ⟨g.symm x, h2 x hx, g.apply_symm_apply x⟩

theorem gmap_cutW {h : V →ₗ⋆[K] V →ₗ[K] K} {U : Submodule K V} {g : V ≃ₗ[K] V}
    (hg : g ∈ isomFix h U) (Λ : Submodule (𝓞 K) V) :
    Formalism.HermitianLatticesTheory.gmap g (Λ ⊓ (orthK h U).restrictScalars (𝓞 K)) =
      Formalism.HermitianLatticesTheory.gmap g Λ ⊓ (orthK h U).restrictScalars (𝓞 K) := by
  refine gmap_inf_sub _ (fun x hx => apply_mem_orthK hg hx) (fun x hx => ?_) Λ
  have := apply_mem_orthK ((isomFix h U).inv_mem hg) hx
  exact this

theorem gmap_cutU {h : V →ₗ⋆[K] V →ₗ[K] K} {U : Submodule K V} {g : V ≃ₗ[K] V}
    (hg : g ∈ isomFix h U) (Λ : Submodule (𝓞 K) V) :
    Formalism.HermitianLatticesTheory.gmap g (Λ ⊓ U.restrictScalars (𝓞 K)) =
      Formalism.HermitianLatticesTheory.gmap g Λ ⊓ U.restrictScalars (𝓞 K) := by
  refine gmap_inf_sub _ (fun x hx => by rw [hg.2 x hx]; exact hx) (fun x hx => ?_) Λ
  rw [g.symm_apply_eq.mpr (hg.2 x hx).symm]
  exact hx

theorem gmap_eq_self {h : V →ₗ⋆[K] V →ₗ[K] K} {U : Submodule K V} {g : V ≃ₗ[K] V}
    (hg : g ∈ isomFix h U) {M : Submodule (𝓞 K) V} (hM : ∀ x ∈ M, x ∈ U) :
    Formalism.HermitianLatticesTheory.gmap g M = M := by
  ext x
  rw [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, e⟩
    have e2 : g y = y := hg.2 y (hM y hy)
    rw [← e]
    change g y ∈ M
    rw [e2]
    exact hy
  · intro hx
    exact ⟨x, hx, hg.2 x (hM x hx)⟩

theorem cut_isLatIn {Λ : Submodule (𝓞 K) V} (hΛ : Submodule.IsLattice K Λ) (X : Submodule K V) :
    IsLatIn X (Λ ⊓ X.restrictScalars (𝓞 K)) := by
  refine ⟨?_, ?_⟩
  · have := isNoetherian_of_fg_of_noetherian _ hΛ.fg
    exact Submodule.FG.of_le_of_isNoetherian (inf_le_left : Λ ⊓ X.restrictScalars (𝓞 K) ≤ Λ)
  · apply le_antisymm
    · exact Submodule.span_le.mpr fun x hx => hx.2
    · intro x hx
      obtain ⟨r, hr, hrx⟩ := StabilizerLattices.exists_smul_mem hΛ x
      have h1 : r • x ∈ Λ ⊓ X.restrictScalars (𝓞 K) :=
        ⟨hrx, (X.restrictScalars (𝓞 K)).smul_mem r hx⟩
      have hr' : algebraMap (𝓞 K) K r ≠ 0 := by simpa using hr
      have e : x = (algebraMap (𝓞 K) K r)⁻¹ • (r • x) := by
        rw [← algebraMap_smul K r x, smul_smul, inv_mul_cancel₀ hr', one_smul]
      rw [e]
      exact Submodule.smul_mem _ _ (Submodule.subset_span h1)

theorem integral_of_unimod {h : V →ₗ⋆[K] V →ₗ[K] K} {Λ : Submodule (𝓞 K) V}
    (hU : Formalism.HermitianLatticesTheory.IsUnimodular h Λ) (X : Submodule (𝓞 K) V) :
    Formalism.HermitianLatticesTheory.IsIntegralLat h (Λ ⊓ X) := by
  intro x hx y hy
  have hy' : y ∈ Formalism.HermitianLatticesTheory.dual h Λ := by
    rw [hU]
    exact hy.1
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap] at hy'
  exact hy' x hx.1

scoped instance fixAct (h : V →ₗ⋆[K] V →ₗ[K] K) (U : Submodule K V) :
    MulAction (isomFix h U) (Submodule (𝓞 K) V) where
  smul g Λ := Formalism.HermitianLatticesTheory.gmap g.1 Λ
  one_smul := autSub_gmap_one
  mul_smul a b Λ := autSub_gmap_mul a.1 b.1 Λ

theorem smul_def {h : V →ₗ⋆[K] V →ₗ[K] K} {U : Submodule K V} (g : isomFix h U)
    (Λ : Submodule (𝓞 K) V) : g • Λ = Formalism.HermitianLatticesTheory.gmap g.1 Λ := rfl

def stabEquiv (h : V →ₗ⋆[K] V →ₗ[K] K) (U : Submodule K V) (Λ : Submodule (𝓞 K) V) :
    MulAction.stabilizer (isomFix h U) Λ ≃ stabFix h U Λ where
  toFun a := ⟨a.1.1, a.1.2, MulAction.mem_stabilizer_iff.mp a.2⟩
  invFun b := ⟨⟨b.1, b.2.1⟩, MulAction.mem_stabilizer_iff.mpr b.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_stab (h : V →ₗ⋆[K] V →ₗ[K] K) (U : Submodule K V) (Λ : Submodule (𝓞 K) V) :
    Nat.card (MulAction.stabilizer (isomFix h U) Λ) = Nat.card (stabFix h U Λ) :=
  Nat.card_congr (stabEquiv h U Λ)

theorem finite_stab {h : V →ₗ⋆[K] V →ₗ[K] K} {U : Submodule K V} {Λ : Submodule (𝓞 K) V}
    (hfin : (stabFix h U Λ).Finite) :
    ((MulAction.stabilizer (isomFix h U) Λ : Set (isomFix h U))).Finite := by
  have := hfin.to_subtype
  exact Set.finite_coe_iff.mp (Finite.of_equiv _ (stabEquiv h U Λ).symm)

theorem nondegOn_U {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) {U : Submodule K V}
    (hUW : IsCompl U (orthK h U)) : NondegOn h U := by
  intro x hx hxy
  have hxW : x ∈ orthK h U := by
    rw [mem_orthK]
    intro u hu
    rw [← hs.eq x u, hxy u hu, map_zero]
  exact (Submodule.disjoint_def.mp hUW.disjoint) x hx hxW

theorem nondegenerate_on_orth_compl {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hnd : Nondeg h)
    {U : Submodule K V} (hUW : IsCompl U (orthK h U)) : NondegOn h (orthK h U) := by
  intro x hx hxy
  apply hnd x
  intro v
  have hv : v ∈ U ⊔ orthK h U := by rw [hUW.sup_eq_top]; exact Submodule.mem_top
  obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hv
  rw [map_add, hxy w hw, ← hs.eq u x, (mem_orthK.mp hx) u hu, map_zero, add_zero]

theorem vJof_eq_of_jordan (h2 : JordanInv) (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) {X X' : Submodule K V} {L L' : Submodule (𝓞 K) V}
    (hL : IsLatIn X L) (hL' : IsLatIn X' L') {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {b a b' a'}
    (hJ : IsJordanIn h X L 𝔭 b a) (hJ' : IsJordanIn h X' L' 𝔭 b' a')
    (hiso : Nonempty (DiscMod h X L 𝔭 ≃ₗ[𝓞 K] DiscMod h X' L' 𝔭)) :
    vJof 𝔭 a = vJof 𝔭 a' ∧ cJof 𝔭 a = cJof 𝔭 a' := by
  have H := h2 K F V V hK hF h h hs hs X X' L L' hL hL' 𝔭 h𝔭 b a b' a' hJ hJ' hiso
  refine ⟨sum_eq_of_min _ _ H, ?_⟩
  unfold cJof
  rw [card_ne_zero_eq (fun i => vF 𝔭 (a i)), card_ne_zero_eq (fun i => vF 𝔭 (a' i))]
  exact H 1

theorem vJ_cJ_eq (h2 : JordanInv) (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) {X : Submodule K V} {L : Submodule (𝓞 K) V}
    (hL : IsLatIn X L) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {b a}
    (hJ : IsJordanIn h X L 𝔭 b a) : vJ h X L 𝔭 = vJof 𝔭 a ∧ cJ h X L 𝔭 = cJof 𝔭 a := by
  have key : ∀ b' a', IsJordanIn h X L 𝔭 b' a' → vJof 𝔭 a' = vJof 𝔭 a ∧ cJof 𝔭 a' = cJof 𝔭 a :=
    fun b' a' hJ' => vJof_eq_of_jordan h2 hK hF hs hL hL h𝔭 hJ' hJ ⟨LinearEquiv.refl _ _⟩
  constructor
  · have e : {v | ∃ b a, IsJordanIn h X L 𝔭 b a ∧ v = vJof 𝔭 a} = {vJof 𝔭 a} := by
      ext v
      constructor
      · rintro ⟨b', a', hJ', rfl⟩
        exact (key b' a' hJ').1
      · rintro rfl
        exact ⟨b, a, hJ, rfl⟩
    unfold vJ
    rw [e, csInf_singleton]
  · have e : {v | ∃ b a, IsJordanIn h X L 𝔭 b a ∧ v = cJof 𝔭 a} = {cJof 𝔭 a} := by
      ext v
      constructor
      · rintro ⟨b', a', hJ', rfl⟩
        exact (key b' a' hJ').2
      · rintro rfl
        exact ⟨b, a, hJ, rfl⟩
    unfold cJ
    rw [e, csInf_singleton]

end Formalism.L2.SG.Pf.G9

namespace Formalism.L2.SG.Pf.Cnt

open Formalism.HermitianLattices.Ext.L3
open scoped Formalism.L2.SG.Pf.G9

theorem glueMass_of (h1 : JordanExists) (h2 : JordanInv) (h6 : GlueLoc) (h8 : GlueProd)
    (hG : GenusMassW) : GlueMass := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ hK hF h hs hnd U hUW hpos M hM hMi hne c hc
  classical
  obtain ⟨Λ₀, hΛ₀⟩ := hne
  obtain ⟨T₀, hT⟩ : ∃ T₀, Λ₀ ⊓ (orthK h U).restrictScalars (𝓞 K) = T₀ := ⟨_, rfl⟩
  have hT₀ : IsLatIn (orthK h U) T₀ := hT ▸ G9.cut_isLatIn hΛ₀.1 _
  have hT₀i : Formalism.HermitianLatticesTheory.IsIntegralLat h T₀ := hT ▸ G9.integral_of_unimod hΛ₀.2.1 _
  obtain ⟨sY, hsY1, hsY2, hsYfin, hmass⟩ := hG K F V hK hF h hs hnd U hUW hpos T₀ hT₀ hT₀i c hc
  have hrefl : ∀ T, SameGenusFix (F := F) h U T T :=
    fun T _ _ => ⟨1, (isomFix h U).one_mem, autSub_gmap_one _⟩
  have hB : ∀ Λ ∈ GlueSet h U M, IsLatIn (orthK h U) (Λ ⊓ (orthK h U).restrictScalars (𝓞 K)) ∧
      SameGenusFix (F := F) h U T₀ (Λ ⊓ (orthK h U).restrictScalars (𝓞 K)) := by
    intro Λ hΛ
    have hl := G9.cut_isLatIn hΛ.1 (orthK h U)
    refine ⟨hl, ?_⟩
    have e1 := ((h8 K F V hK hF h hs hnd U hUW hpos M hM Λ hΛ _ hl).1).mpr (hrefl _)
    have e2 := ((h8 K F V hK hF h hs hnd U hUW hpos M hM Λ₀ hΛ₀ _ hl).1).mp e1
    rwa [hT] at e2
  have hfib0 : ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → fibP h U 𝔭 M T₀ ≠ 0 :=
    ((h8 K F V hK hF h hs hnd U hUW hpos M hM Λ₀ hΛ₀ T₀ hT₀).1).mpr (by rw [hT]; exact hrefl _)
  have hfibeq : ∀ T, SameGenusFix (F := F) h U T₀ T → ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal →
      fibP h U 𝔭 M T = fibP h U 𝔭 M T₀ := by
    intro T hg 𝔭 h𝔭
    obtain ⟨g, hg, e⟩ := hg 𝔭 h𝔭
    have e1 : fibP h U 𝔭 M T = fibP h U 𝔭 M (Formalism.HermitianLatticesTheory.gmap g T₀) := by
      unfold fibP
      rw [← LocalizedFibreSets.gmap_locF, e]
    rw [e1]
    exact (h6 K F V hK hF h hs hnd U hUW M T₀ hM hT₀ 𝔭 h𝔭).2 g hg
  have hdisc : ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → fibP h U 𝔭 M T₀ = discAut h (orthK h U) T₀ 𝔭 :=
    fun 𝔭 h𝔭 => ((h6 K F V hK hF h hs hnd U hUW M T₀ hM hT₀ 𝔭 h𝔭).1 (hfib0 𝔭 h𝔭)).2
  have hfibcard : ∀ T, IsLatIn (orthK h U) T → SameGenusFix (F := F) h U T₀ T →
      Nat.card {Λ : Submodule (𝓞 K) V //
          Λ ∈ GlueSet h U M ∧ Λ ⊓ (orthK h U).restrictScalars (𝓞 K) = T} =
        ∏' 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, discAut h (orthK h U) T₀ 𝔭.1 := by
    intro T hTl hg
    rw [(h8 K F V hK hF h hs hnd U hUW hpos M hM Λ₀ hΛ₀ T hTl).2]
    exact tprod_congr fun 𝔭 => by rw [hfibeq T hg 𝔭.1 𝔭.2, hdisc 𝔭.1 𝔭.2]
  have hN : ∏' 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, discAut h (orthK h U) T₀ 𝔭.1 ≠ 0 :=
    G9.tprod_nat_ne_zero _ fun 𝔭 => by rw [← hdisc 𝔭.1 𝔭.2]; exact hfib0 𝔭.1 𝔭.2
  let π : Submodule (𝓞 K) V → Submodule (𝓞 K) V := fun Λ => Λ ⊓ (orthK h U).restrictScalars (𝓞 K)
  let B : Set (Submodule (𝓞 K) V) :=
    {T | IsLatIn (orthK h U) T ∧ SameGenusFix (F := F) h U T₀ T}
  have hπ : ∀ (g : isomFix h U) (x : Submodule (𝓞 K) V), π (g • x) = g • π x :=
    fun g x => (G9.gmap_cutW g.2 x).symm
  have hA : ∀ g : isomFix h U, ∀ x ∈ GlueSet h U M, g • x ∈ GlueSet h U M := by
    intro g x hx
    obtain ⟨hx1, hx2, hx3⟩ := hx
    have hact := Formalism.HermitianLatticesTheory.isomAct (𝓞 K) K V h g.1 g.2.1 x
    refine ⟨hact.2.2.2.2.mpr hx1, hact.2.2.2.1.mpr hx2, ?_⟩
    change Formalism.HermitianLatticesTheory.gmap g.1 x ⊓ U.restrictScalars (𝓞 K) = M
    rw [← G9.gmap_cutU g.2, hx3]
    exact G9.gmap_eq_self g.2 fun y hy => by rw [← hM.2]; exact Submodule.subset_span hy
  have hsY1' : ∀ u ∈ sY, u ∈ B := fun u hu => hsY1 u hu
  have hY : ∀ y ∈ B, ∃! t, t ∈ sY ∧ ∃ g : isomFix h U, g • t = y := by
    intro y hy
    obtain ⟨t, ⟨ht, g, hg, e⟩, hu⟩ := hsY2 y hy.1 hy.2
    exact ⟨t, ⟨ht, ⟨g, hg⟩, e⟩, fun t' ⟨ht', ⟨g', hg'⟩, e'⟩ => hu t' ⟨ht', g', hg', e'⟩⟩
  have hfinY : ∀ y ∈ B, ((MulAction.stabilizer (isomFix h U) y : Set (isomFix h U))).Finite :=
    fun y hy => G9.finite_stab (hsYfin y hy.1 hy.2)
  have hfibfin : ∀ u ∈ B, {x | x ∈ GlueSet h U M ∧ π x = u}.Finite := by
    intro u hu
    have hc : Nat.card {x // x ∈ GlueSet h U M ∧ π x = u} ≠ 0 := by
      rw [hfibcard u hu.1 hu.2]
      exact hN
    exact Set.finite_coe_iff.mp (Nat.finite_of_card_ne_zero hc)
  obtain ⟨sX, hsX1, hsX2⟩ := OrbSum.exists_reps_of_cover (G := isomFix h U) (GlueSet h U M) hA
    (⋃ u ∈ (sY : Set (Submodule (𝓞 K) V)), {x | x ∈ GlueSet h U M ∧ π x = u})
    (sY.finite_toSet.biUnion fun u hu => hfibfin u (hsY1' u hu))
    (fun x hx => by
      obtain ⟨u, -, hx'⟩ := Set.mem_iUnion₂.mp hx
      exact hx'.1)
    (by
      intro x hx
      obtain ⟨u, ⟨hu, g, e⟩, -⟩ := hY (π x) (hB x hx)
      refine ⟨g⁻¹ • x, Set.mem_biUnion (Finset.mem_coe.mpr hu) ⟨hA _ x hx, ?_⟩, g,
        smul_inv_smul g x⟩
      rw [hπ, ← e, inv_smul_smul])
  refine ⟨sX, hsX1, ?_, ?_, ?_⟩
  · intro Λ hΛ
    obtain ⟨t, ⟨ht, g, e⟩, hu⟩ := hsX2 Λ hΛ
    exact ⟨t, ⟨ht, g.1, g.2, e⟩, fun t' ⟨ht', g', hg', e'⟩ => hu t' ⟨ht', ⟨g', hg'⟩, e'⟩⟩
  · intro Λ hΛ
    have hb := hB Λ (hsX1 Λ hΛ)
    refine (hsYfin _ hb.1 hb.2).subset ?_
    rintro g ⟨hg, e⟩
    exact ⟨hg, by rw [G9.gmap_cutW hg, e]⟩
  · have e1 : ∀ Λ ∈ sX, ((Nat.card (stabFix h U Λ) : ℕ) : ℝ)⁻¹ =
        ((Nat.card (MulAction.stabilizer (isomFix h U) Λ) : ℕ) : ℝ)⁻¹ :=
      fun Λ _ => by rw [G9.card_stab]
    rw [Finset.sum_congr rfl e1, OrbSum.sum_orbits_on π hπ (GlueSet h U M) B hA
      (fun x hx => hB x hx) sX sY hsX1 hsY1' hsX2 hY hfinY]
    have e2 : ∀ u ∈ sY, (Nat.card {x // x ∈ GlueSet h U M ∧ π x = u} : ℝ) /
        (Nat.card (MulAction.stabilizer (isomFix h U) u) : ℝ) =
        ((∏' 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, discAut h (orthK h U) T₀ 𝔭.1 : ℕ) : ℝ) *
          ((Nat.card (stabFix h U u) : ℕ) : ℝ)⁻¹ := by
      intro u hu
      rw [G9.card_stab, div_eq_mul_inv]
      congr 1
      exact_mod_cast hfibcard u (hsY1 u hu).1 (hsY1 u hu).2
    rw [Finset.sum_congr rfl e2, ← Finset.mul_sum, hmass]
    have hJ : ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal →
        vJ h (orthK h U) T₀ 𝔭 = vJ h U M 𝔭 ∧ cJ h (orthK h U) T₀ 𝔭 = cJ h U M 𝔭 := by
      intro 𝔭 h𝔭
      obtain ⟨b, a, hJM⟩ := (h1 K F V hK hF h hs).1 U M (G9.nondegOn_U hs hUW) hM hMi 𝔭 h𝔭
      obtain ⟨b', a', hJT⟩ :=
        (h1 K F V hK hF h hs).1 _ T₀ (G9.nondegenerate_on_orth_compl hs hnd hUW) hT₀ hT₀i 𝔭 h𝔭
      have hiso := ((h6 K F V hK hF h hs hnd U hUW M T₀ hM hT₀ 𝔭 h𝔭).1 (hfib0 𝔭 h𝔭)).1
      have E := G9.vJof_eq_of_jordan h2 hK hF hs hM hT₀ h𝔭 hJM hJT hiso
      have EM := G9.vJ_cJ_eq h2 hK hF hs hM h𝔭 hJM
      have ET := G9.vJ_cJ_eq h2 hK hF hs hT₀ h𝔭 hJT
      exact ⟨by rw [EM.1, ET.1, E.1], by rw [EM.2, ET.2, E.2]⟩
    have hnM : nM F h (orthK h U) T₀ = nM F h U M := by
      unfold nM
      exact tprod_congr fun 𝔭 => by rw [(hJ 𝔭.1 𝔭.2).1]
    rw [hnM]
    congr 1
    exact tprod_congr fun 𝔭 => by rw [(hJ 𝔭.1 𝔭.2).2]

end Formalism.L2.SG.Pf.Cnt
