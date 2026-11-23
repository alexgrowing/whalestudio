import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.Mem.GrpCount

section Count

variable {κ : Type} [CommRing κ] {r : ℕ}

theorem card_unitri (Fr : Fin r → Fin r → Prop) (hFr : ∀ i j, Fr i j → i < j) (H : Subgroup (GL (Fin r) κ))
    (hH : ∀ g : GL (Fin r) κ, g ∈ H ↔ (∀ i j, j < i → (g : Matrix (Fin r) (Fin r) κ) i j = 0) ∧
      (∀ i, (g : Matrix (Fin r) (Fin r) κ) i i = 1) ∧
      ∀ i j, i < j → ¬ Fr i j → (g : Matrix (Fin r) (Fin r) κ) i j = 0) :
    Nat.card H = Nat.card κ ^ Nat.card {p : Fin r × Fin r // Fr p.1 p.2} := by
  classical
  let mk : ({p : Fin r × Fin r // Fr p.1 p.2} → κ) → Matrix (Fin r) (Fin r) κ := fun f i j =>
    if i = j then 1 else if h : Fr i j then f ⟨(i, j), h⟩ else 0
  have hlow : ∀ f i j, j < i → mk f i j = 0 := by
    intro f i j hij
    have hne : i ≠ j := (ne_of_lt hij).symm
    simp only [mk, if_neg hne]
    rw [dif_neg]
    intro h
    exact absurd (hFr i j h) (not_lt.2 hij.le)
  have hdet : ∀ f, (mk f).det = 1 := by
    intro f
    rw [Matrix.det_of_upperTriangular (fun i j hij => hlow f i j hij)]
    simp [mk]
  let toG : ({p : Fin r × Fin r // Fr p.1 p.2} → κ) → GL (Fin r) κ := fun f =>
    Matrix.nonsingInvUnit (mk f) (by rw [hdet]; exact isUnit_one)
  have htoG : ∀ f, ((toG f : GL (Fin r) κ) : Matrix (Fin r) (Fin r) κ) = mk f := fun f => rfl
  let e : H ≃ ({p : Fin r × Fin r // Fr p.1 p.2} → κ) :=
    { toFun := fun g p => (g.1 : Matrix (Fin r) (Fin r) κ) p.1.1 p.1.2
      invFun := fun f => ⟨toG f, (hH _).2 ⟨fun i j hij => by rw [htoG]; exact hlow f i j hij,
        fun i => by rw [htoG]; simp [mk],
        fun i j hij hn => by
          rw [htoG]
          simp only [mk, if_neg (ne_of_lt hij), dif_neg hn]⟩⟩
      left_inv := by
        intro g
        obtain ⟨h0, h1, h2⟩ := (hH g.1).1 g.2
        apply Subtype.ext
        apply Units.ext
        ext i j
        change mk (fun p => (g.1 : Matrix (Fin r) (Fin r) κ) p.1.1 p.1.2) i j = (g.1 : Matrix (Fin r) (Fin r) κ) i j
        simp only [mk]
        by_cases hij : i = j
        · subst hij; rw [if_pos rfl, h1]
        · rw [if_neg hij]
          by_cases hf : Fr i j
          · rw [dif_pos hf]
          · rw [dif_neg hf]
            rcases lt_or_gt_of_ne hij with hl | hl
            · exact (h2 i j hl hf).symm
            · exact (h0 i j hl).symm
      right_inv := by
        intro f
        funext p
        show mk f p.1.1 p.1.2 = f p
        simp only [mk, if_neg (ne_of_lt (hFr _ _ p.2)), dif_pos p.2] }
  rw [Nat.card_congr e, Nat.card_fun]

theorem card_unip : Nat.card (unip κ r) = Nat.card κ ^ Nat.card {p : Fin r × Fin r // p.1 < p.2} := by
  refine card_unitri (fun i j => i < j) (fun _ _ h => h) _ fun g => ?_
  constructor
  · rintro ⟨h0, h1⟩
    exact ⟨fun i j hij => h0 hij, h1, fun i j hij hn => absurd hij hn⟩
  · rintro ⟨h0, h1, -⟩
    exact ⟨fun i j hij => h0 i j hij, h1⟩

theorem card_unipCol (a c : ℕ) : Nat.card (unipCol κ r a c) =
    Nat.card κ ^ Nat.card {p : Fin r × Fin r // p.1 < p.2 ∧ ¬ (a ≤ p.1.val ∧ p.1.val < c ∧ p.2.val = c)} := by
  refine card_unitri (fun i j => i < j ∧ ¬ (a ≤ i.val ∧ i.val < c ∧ j.val = c)) (fun _ _ h => h.1) _ fun g => ?_
  constructor
  · rintro ⟨⟨h0, h1⟩, h2⟩
    refine ⟨fun i j hij => h0 hij, h1, fun i j hij hn => ?_⟩
    have : a ≤ i.val ∧ i.val < c ∧ j.val = c := by
      by_contra hc
      exact hn ⟨hij, hc⟩
    exact h2 i j this.1 this.2.1 this.2.2
  · rintro ⟨h0, h1, h2⟩
    refine ⟨⟨fun i j hij => h0 i j hij, h1⟩, fun i j ha hc hj => h2 i j ?_ ?_⟩
    · show i.val < j.val; omega
    · rintro ⟨-, hn⟩; exact hn ⟨ha, hc, hj⟩

theorem card_pairs_split {a c : ℕ} (hac : a ≤ c) (hc : c < r) :
    Nat.card {p : Fin r × Fin r // p.1 < p.2} =
      Nat.card {p : Fin r × Fin r // p.1 < p.2 ∧ ¬ (a ≤ p.1.val ∧ p.1.val < c ∧ p.2.val = c)} + (c - a) := by
  classical
  have hQ : Nat.card {p : Fin r × Fin r // p.1 < p.2 ∧ (a ≤ p.1.val ∧ p.1.val < c ∧ p.2.val = c)} = c - a := by
    rw [← Nat.card_fin (c - a)]
    refine Nat.card_congr
      { toFun := fun p => ⟨p.1.1.val - a, by have := p.2.2; omega⟩
        invFun := fun i => ⟨(⟨a + i.val, by have := i.2; omega⟩, ⟨c, hc⟩), by
          refine ⟨?_, ?_, ?_, rfl⟩
          · show a + i.val < c; have := i.2; omega
          · show a ≤ a + i.val; omega
          · show a + i.val < c; have := i.2; omega⟩
        left_inv := by
          rintro ⟨⟨i, j⟩, h1, h2, h3, h4⟩
          have h2' : a ≤ i.val := h2
          apply Subtype.ext
          apply Prod.ext
          · apply Fin.ext; show a + (i.val - a) = i.val; omega
          · apply Fin.ext; exact h4.symm
        right_inv := by
          intro i
          apply Fin.ext
          show a + i.val - a = i.val
          omega }
  rw [← hQ]
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [← Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter (fun p : Fin r × Fin r => p.1 < p.2))
    (fun p : Fin r × Fin r => a ≤ p.1.val ∧ p.1.val < c ∧ p.2.val = c), Finset.filter_filter, Finset.filter_filter,
    add_comm]

theorem card_pi {ι : Type} [Fintype ι] {M : ι → Type} [∀ i, Group (M i)] (H : ∀ i, Subgroup (M i)) :
    Nat.card (Subgroup.pi Set.univ H) = ∏ i, Nat.card (H i) := by
  rw [← Nat.card_pi]
  exact Nat.card_congr ((Equiv.subtypeEquivRight fun x => by simp [Subgroup.mem_pi]).trans
    (Equiv.subtypePiEquivPi (p := fun i y => y ∈ H i)))

end Count

end GlobalTheory.Mem.GrpCount

namespace GlobalTheory.Mem.GrpCount

theorem symPos_injective {r ρ k : ℕ} (h : ρ + k ≤ r) : Function.Injective (symPos r ρ k) := by
  intro i j hij
  have hv := congrArg Fin.val hij
  simp only [symPos] at hv
  have hi := i.2
  have hj := j.2
  apply Fin.ext
  split_ifs at hv <;> rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hv <;> omega

theorem index_of_lvlTie {D : D7} {G : Type} [Group G] {Q0 : Subgroup G} {ψ0 : Q0 →* D.what₂.LLˣ} {Qs : Subgroup G}
    {ψs : Qs →* D.what₂.LLˣ} {eG : G ≃* G0g D.nd} {Pg : Finset (Pl D.host.E)} {pl : (Σ k : Fin 2, D.nd.PlG k) ≃ ↥Pg}
    {res : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), kP (pl kv).1 ≃+* ZMod (D.host.g kv.1)}
    {ψ : ∀ PP : Pl D.host.E, AddChar (kP PP) D.what₂.LL} {eC : G ≃* G0 Pg D.R.r}
    (h : LvlTie D Q0 ψ0 Qs ψs eG Pg pl res ψ eC) :
    Nat.card Q0 = Nat.card Qs * (D.host.g 0 * D.host.g 1) ^ (D.R.k * D.R.f) := by
  have hrk : D.R.rS + D.R.k < D.R.r := by
    have := D.R.two_le_m
    simp only [Ranks.rS, Ranks.r]
    omega
  let σ : Fin D.R.r ≃ Fin D.R.r :=
    Equiv.ofBijective _ (Finite.injective_iff_bijective.1 (symPos_injective hrk.le))
  have h0 : Nat.card Q0 = Nat.card (_root_.Formalism.L2.DIV.P0 Pg D.R.r ψ).H :=
    Nat.card_congr (eC.toEquiv.subtypeEquiv fun g => h.p0 g)
  let φ : G0 Pg D.R.r ≃ G0 Pg D.R.r := Equiv.piCongrRight fun PP =>
    (Units.mapEquiv (Matrix.reindexAlgEquiv (kP PP.1) (kP PP.1) σ.symm).toMulEquiv).toEquiv
  have hφ : ∀ (x : G0 Pg D.R.r) (PP : ↥Pg) (i j : Fin D.R.r),
      ((φ x PP : GL (Fin D.R.r) (kP PP.1)) : Matrix (Fin D.R.r) (Fin D.R.r) (kP PP.1)) i j =
        ((x PP : GL (Fin D.R.r) (kP PP.1)) : Matrix (Fin D.R.r) (Fin D.R.r) (kP PP.1))
          (symPos D.R.r D.R.rS D.R.k i) (symPos D.R.r D.R.rS D.R.k j) := by
    intro x PP i j
    simp [φ, σ, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply]
  have hs : Nat.card Qs = Nat.card (PsharpSym Pg D.R.r D.R.rS D.R.k ψ).H := by
    refine Nat.card_congr ((eC.toEquiv.trans φ).subtypeEquiv fun g => ?_)
    rw [h.ps g]
    constructor
    · rintro ⟨y, hy, hE⟩
      have hy' : φ (eC g) = y := by
        funext PP
        apply Units.ext
        ext i j
        rw [hφ]
        exact hE PP i j
      show φ (eC g) ∈ _
      rw [hy']
      exact hy
    · intro hm
      exact ⟨_, hm, fun PP i j => (hφ _ PP i j).symm⟩
  have hsplit := card_pairs_split (r := D.R.r) (a := D.R.rS) (c := D.R.rS + D.R.k) (by omega) hrk
  rw [Nat.add_sub_cancel_left] at hsplit
  have hP0 : Nat.card (_root_.Formalism.L2.DIV.P0 Pg D.R.r ψ).H =
      ∏ PP : ↥Pg, Nat.card (kP PP.1) ^ Nat.card {p : Fin D.R.r × Fin D.R.r // p.1 < p.2} := by
    show Nat.card (Subgroup.pi Set.univ fun PP : ↥Pg => unip (kP PP.1) D.R.r) = _
    rw [card_pi]
    exact Finset.prod_congr rfl fun PP _ => card_unip
  have hPs : Nat.card (PsharpSym Pg D.R.r D.R.rS D.R.k ψ).H =
      ∏ PP : ↥Pg, Nat.card (kP PP.1) ^ Nat.card {p : Fin D.R.r × Fin D.R.r //
        p.1 < p.2 ∧ ¬ (D.R.rS ≤ p.1.val ∧ p.1.val < D.R.rS + D.R.k ∧ p.2.val = D.R.rS + D.R.k)} := by
    show Nat.card (Subgroup.pi Set.univ fun PP : ↥Pg => unipCol (kP PP.1) D.R.r D.R.rS (D.R.rS + D.R.k)) = _
    rw [card_pi]
    exact Finset.prod_congr rfl fun PP _ => card_unipCol _ _
  have hk : ∏ PP : ↥Pg, Nat.card (kP PP.1) ^ D.R.k = (D.host.g 0 * D.host.g 1) ^ (D.R.k * D.R.f) := by
    rw [← Equiv.prod_comp pl (fun PP : ↥Pg => Nat.card (kP PP.1) ^ D.R.k)]
    have hq : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), Nat.card (kP (pl kv).1) = D.host.g kv.1 := fun kv => by
      rw [Nat.card_congr (res kv).toEquiv, Nat.card_zmod]
    simp only [hq]
    rw [Fintype.prod_sigma]
    simp only [Finset.prod_const, Finset.card_univ, D.nd.card_PlG, Fin.prod_univ_two]
    ring
  rw [h0, hs, hP0, hPs, ← hk, hsplit, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun PP _ => pow_add _ _ _

end GlobalTheory.Mem.GrpCount

namespace GlobalTheory.Mem.R3

theorem pins_card_index_ranks : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type)
    (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), Pins R F cG →
    Fintype.card G = D.what₂.restRowsFiniteGroupCard ∧ Nat.card F.P0 = Nat.card F.P1 * (D.host.g 0 * D.host.g 1) ^ (D.R.k * D.R.f) ∧
      A3.A.r = D.R.r ∧ A3.A.t = D.R.t ∧ A3.A.v0 = InfinitePlace.mk D.what₂.embLL := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG h
  obtain ⟨gramR, c0R, c0L, hT⟩ := h.char.base.fam.tie
  refine ⟨?_, ?_, hT.ranks.2.1, hT.ranks.2.2, hT.v0⟩
  · rw [← Nat.card_eq_fintype_card, Nat.card_congr (R.eG.trans cG).toEquiv, D.nd.restN_card_levelGroup_eq, Nat.card_pi,
      Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    change ∏ _y : D.nd.PlG k, Nat.card (GL (Fin D.R.r) (ZMod (D.host.g k))) = _
    rw [Finset.prod_const, Finset.card_univ, D.nd.card_PlG k]
  · obtain ⟨Pg, pl, res, ψ, eC, hL, -⟩ := h.keep.psi
    exact GlobalTheory.Mem.GrpCount.index_of_lvlTie hL

end GlobalTheory.Mem.R3
