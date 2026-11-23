import Mathlib
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.OpenCellDecomposition.OpenCellBlockShapes.OpenJ

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib GlobalTheory.CompanionTheory.Rodier
open scoped Pointwise

namespace PositivityTheory.RgUd.CellB

@[to_additive addRelIndex_ne_zero  ]
theorem relIndex_ne_zero {G : Type*} [Group G] [TopologicalSpace G] [ContinuousMul G] {U L L₀ : Subgroup G}
    (hL : L ≤ L₀) (hL₀U : L₀ ≤ U) (hc : IsCompact (L₀ : Set G)) {O : Set G} (hO : IsOpen O)
    (hOL : O ∩ (U : Set G) = L) : L.relIndex L₀ ≠ 0 := by
  have h1 : (1 : G) ∈ O := by
    have : (1 : G) ∈ O ∩ (U : Set G) := by rw [hOL]; exact L.one_mem
    exact this.1
  obtain ⟨t, htL, htf, hcov⟩ := hc.elim_finite_subcover_image (b := (L₀ : Set G)) (c := fun x => x • O)
    (fun x _ => hO.smul x) (fun y hy => Set.mem_iUnion₂.2 ⟨y, hy, ⟨1, h1, mul_one y⟩⟩)
  have : Finite t := htf.to_subtype
  let φ : t → L₀ ⧸ L.subgroupOf L₀ := fun x => ((⟨x.1, htL x.2⟩ : L₀) : L₀ ⧸ L.subgroupOf L₀)
  have hφ : Function.Surjective φ := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H y =>
      obtain ⟨x, hx, o, ho, e⟩ := Set.mem_iUnion₂.1 (hcov y.2)
      refine ⟨⟨x, hx⟩, QuotientGroup.eq.2 ?_⟩
      show (⟨x, htL hx⟩ : L₀)⁻¹ * y ∈ L.subgroupOf L₀
      rw [Subgroup.mem_subgroupOf]
      have e' : ((⟨x, htL hx⟩ : L₀)⁻¹ * y : L₀).1 = o := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        rw [← e]
        simp [smul_eq_mul]
      rw [e', ← SetLike.mem_coe, ← hOL]
      refine ⟨ho, ?_⟩
      rw [← e']
      exact hL₀U (SetLike.coe_mem _)
  have : Finite (L₀ ⧸ L.subgroupOf L₀) := Finite.of_surjective φ hφ
  exact Subgroup.index_ne_zero_of_finite

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

set_option maxHeartbeats 1000000 in

theorem vol_relIndex (ψ : AddChar k Circle) {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) {W : Type} [AddCommGroup W]
    [Module ℂ W] (ρ : Representation ℂ (Levi k fun a => Fin (d a)) W) (J : openFns d hd ρ →ₗ[ℂ] W)
    (vol : Subgroup (GL (Fin N) k) → ℝ)
    (hU : ∀ (u : GL (Fin N) k) (hu : u ∈ unipU k d hd) (hb : u ∈ unipB k (Fin N)) (f f' : openFns d hd ρ),
      (f' : IndSp (stdBlocks d hd) ρ) = parInd (stdBlocks d hd) ρ u f → J f' = (whitChar ψ N ⟨u, hb⟩ : ℂ) • J f)
    (hV : ∀ L₀ : Subgroup (GL (Fin N) k), L₀ ≤ unipU k d hd → IsCompact (L₀ : Set (GL (Fin N) k)) →
      (∃ O : Set (GL (Fin N) k), IsOpen O ∧ O ∩ (unipU k d hd : Set (GL (Fin N) k)) = L₀) →
      0 < vol L₀ ∧ ∀ (f : openFns d hd ρ) (v : W),
        (∀ (u : GL (Fin N) k) (hb : u ∈ unipB k (Fin N)), u ∈ L₀ →
          f.1.1.1 (pm k (wOpen d hd) * u) = (whitChar ψ N ⟨u, hb⟩ : ℂ) • v) →
        (∀ u ∈ unipU k d hd, u ∉ L₀ → f.1.1.1 (pm k (wOpen d hd) * u) = 0) → J f = (vol L₀ : ℂ) • v)
    {L L₀ : Subgroup (GL (Fin N) k)} (hLL₀ : L ≤ L₀) (hL₀U : L₀ ≤ unipU k d hd)
    (hL₀c : IsCompact (L₀ : Set (GL (Fin N) k)))
    (hL₀O : ∃ O : Set (GL (Fin N) k), IsOpen O ∧ O ∩ (unipU k d hd : Set (GL (Fin N) k)) = L₀)
    (hLc : IsCompact (L : Set (GL (Fin N) k)))
    (hLO : ∃ O : Set (GL (Fin N) k), IsOpen O ∧ O ∩ (unipU k d hd : Set (GL (Fin N) k)) = L)
    (hθ : ∀ (u : GL (Fin N) k) (hb : u ∈ unipB k (Fin N)), u ∈ L₀ → whitChar ψ N ⟨u, hb⟩ = 1)
    (g : openFns d hd ρ) (v : W) (hv : v ≠ 0)
    (hg1 : ∀ u ∈ L, g.1.1.1 (pm k (wOpen d hd) * u) = v)
    (hg0 : ∀ u ∈ unipU k d hd, u ∉ L → g.1.1.1 (pm k (wOpen d hd) * u) = 0) :
    vol L₀ = (L.relIndex L₀ : ℝ) * vol L := by
  classical
  have hUB : unipU k d hd ≤ unipB k (Fin N) := inf_le_left
  obtain ⟨O, hO, hOL⟩ := hLO
  have hfin := relIndex_ne_zero hLL₀ hL₀U hL₀c hO hOL
  have : (L.subgroupOf L₀).FiniteIndex := ⟨hfin⟩
  let _ : Fintype (L₀ ⧸ L.subgroupOf L₀) := Fintype.ofFinite _
  let r : L₀ ⧸ L.subgroupOf L₀ → GL (Fin N) k := fun q => (q.out : L₀).1
  have hr : ∀ q, r q ∈ L₀ := fun q => (q.out).2
  have hrB : ∀ q, r q ∈ unipB k (Fin N) := fun q => hUB (hL₀U (hr q))
  let F : L₀ ⧸ L.subgroupOf L₀ → openFns d hd ρ := fun q =>
    ⟨parInd (stdBlocks d hd) ρ (r q) g.1, OpenCoinv.translate_mem d hd ρ (hrB q) g.2⟩
  let ev : GL (Fin N) k → openFns d hd ρ →+ W := fun y =>
    { toFun := fun f => f.1.1.1 y, map_zero' := rfl, map_add' := fun _ _ => rfl }
  have hsum : ∀ y, (∑ q, F q).1.1.1 y = ∑ q, g.1.1.1 (y * r q) := fun y => map_sum (ev y) F Finset.univ
  have hmem : ∀ (u : GL (Fin N) k) (hu : u ∈ L₀) (q : L₀ ⧸ L.subgroupOf L₀),
      u * r q ∈ L ↔ q = ((⟨u⁻¹, inv_mem hu⟩ : L₀) : L₀ ⧸ L.subgroupOf L₀) := by
    intro u hu q
    have e : (((⟨u⁻¹, inv_mem hu⟩ : L₀) : L₀ ⧸ L.subgroupOf L₀) = q) ↔
        (((⟨u⁻¹, inv_mem hu⟩ : L₀) : L₀ ⧸ L.subgroupOf L₀) = ((q.out : L₀) : L₀ ⧸ L.subgroupOf L₀)) := by
      rw [QuotientGroup.out_eq']
    rw [eq_comm, e, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simp [r]
  have hoff : ∀ u ∈ unipU k d hd, ∀ q, u * r q ∉ L → g.1.1.1 (pm k (wOpen d hd) * (u * r q)) = 0 :=
    fun u hu q hq => hg0 _ (mul_mem hu (hL₀U (hr q))) hq
  have hin : ∀ u ∈ L₀, (∑ q, F q).1.1.1 (pm k (wOpen d hd) * u) = v := by
    intro u hu
    rw [hsum, Finset.sum_eq_single ((⟨u⁻¹, inv_mem hu⟩ : L₀) : L₀ ⧸ L.subgroupOf L₀)]
    · rw [mul_assoc]
      exact hg1 _ ((hmem u hu _).2 rfl)
    · intro q _ hq
      rw [mul_assoc]
      exact hoff u (hL₀U hu) q (fun h' => hq ((hmem u hu q).1 h'))
    · intro h'
      exact absurd (Finset.mem_univ _) h'
  have hout : ∀ u ∈ unipU k d hd, u ∉ L₀ → (∑ q, F q).1.1.1 (pm k (wOpen d hd) * u) = 0 := by
    intro u hu hu0
    rw [hsum]
    refine Finset.sum_eq_zero fun q _ => ?_
    rw [mul_assoc]
    refine hoff u hu q fun h' => hu0 ?_
    have : u = (u * r q) * (r q)⁻¹ := by group
    rw [this]
    exact mul_mem (hLL₀ h') (inv_mem (hr q))
  obtain ⟨-, hJ0⟩ := hV L₀ hL₀U hL₀c hL₀O
  obtain ⟨-, hJL⟩ := hV L (hLL₀.trans hL₀U) hLc ⟨O, hO, hOL⟩
  have e0 := hJ0 (∑ q, F q) v (fun u hb hu => by rw [hin u hu, hθ u hb hu]; simp) hout
  have eL := hJL g v (fun u hb hu => by rw [hg1 u hu, hθ u hb (hLL₀ hu)]; simp) hg0
  have eF : ∀ q, J (F q) = J g := fun q => by
    rw [hU (r q) (hL₀U (hr q)) (hrB q) g (F q) rfl, hθ _ _ (hr q)]
    simp
  rw [map_sum, Finset.sum_congr rfl fun q _ => eF q, Finset.sum_const, eL, Finset.card_univ] at e0
  have hc : ((Fintype.card (L₀ ⧸ L.subgroupOf L₀) : ℂ) * (vol L : ℂ) - (vol L₀ : ℂ)) • v = 0 := by
    rw [sub_smul, ← e0, mul_smul, Nat.cast_smul_eq_nsmul, sub_self]
  have hc' := (smul_eq_zero.1 hc).resolve_right hv
  have hcard : L.relIndex L₀ = Fintype.card (L₀ ⧸ L.subgroupOf L₀) := by
    rw [Subgroup.relIndex, Subgroup.index, Nat.card_eq_fintype_card]
  rw [hcard]
  exact_mod_cast (sub_eq_zero.1 hc').symm

end PositivityTheory.RgUd.CellB
