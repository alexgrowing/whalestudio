import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairBaseIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrNormOfTri
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrameCombinationCoeffUnique
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TwoLat GlobalTheory.FlagCov
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PairCov.WholeFin

open GlobalTheory.ShFam.Pad.Guard GlobalTheory.BcRead.FinPl

section Block

def bl {m : ℕ} (i k : Fin m) : ℕ := if k < i then 0 else if k = i then 1 else 2

theorem block_lt_iff {m : ℕ} {i c k : Fin m} : bl i c < bl i k ↔ (c < i ∧ i ≤ k) ∨ (c ≤ i ∧ i < k) := by
  simp only [bl, Fin.ext_iff, Fin.lt_def, Fin.le_def]
  split_ifs <;> omega

theorem blockTriangular_mulVec {R : Type} [CommRing R] {m : ℕ} {i : Fin m} {A : Matrix (Fin m) (Fin m) R}
    (hA : A.BlockTriangular (bl i)) {cf : Fin m → R} (h : ∀ k, i < k → cf k = 0) :
    (∀ k, i < k → A.mulVec cf k = 0) ∧ A.mulVec cf i = A i i * cf i := by
  have e : ∀ k, A.mulVec cf k = ∑ j, A k j * cf j := fun _ => rfl
  simp only [e]
  refine ⟨fun k hk => Finset.sum_eq_zero fun j _ => ?_, Finset.sum_eq_single i (fun j _ hj => ?_) (by simp)⟩
  · rcases le_or_gt j i with hj | hj
    · rw [hA (block_lt_iff.2 (.inr ⟨hj, hk⟩)), zero_mul]
    · rw [h j hj, mul_zero]
  · rcases lt_or_gt_of_ne hj with hj | hj
    · rw [hA (block_lt_iff.2 (.inl ⟨hj, le_rfl⟩)), zero_mul]
    · rw [h j hj, mul_zero]

theorem isUnit_bl {R : Type} [CommRing R] {m : ℕ} {i : Fin m} {A : Matrix (Fin m) (Fin m) R}
    (hA : A.BlockTriangular (bl i)) (hd : IsUnit A.det) : IsUnit (A i i) := by
  let _ := Matrix.invertibleOfIsUnitDet A hd
  have h1 := Matrix.blockTriangular_inv_of_blockTriangular hA
  have h2 := (blockTriangular_mulVec hA (cf := fun k => A⁻¹ k i) fun k hk => h1 (block_lt_iff.2 (.inr ⟨le_rfl, hk⟩))).2
  have h3 : A.mulVec (fun k => A⁻¹ k i) i = (A * A⁻¹) i i := rfl
  rw [h3, A.mul_nonsing_inv hd, Matrix.one_apply_eq] at h2
  exact IsUnit.of_mul_eq_one _ h2.symm

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  {t : SAB H X}

theorem grNorm_of_bl {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C] {x : Sp C ⟶ X}
    {Λ : Set (Sp (DualNumber C) ⟶ t.G.left)} {m : ℕ} {f u : Fin m → (Sp (DualNumber C) ⟶ t.G.left)}
    (hf : ∀ k, IsTanAtG t x (f k)) (hi : Indep t x f) {M Q Q' : Matrix (Fin m) (Fin m) C}
    (hM : ∀ b, IsCombAtG t x f (fun k => M k b) (u b)) (hQ : ∀ a b, ‖Q a b‖ ≤ 1) (hQ' : ∀ a b, ‖Q' a b‖ ≤ 1)
    (hQQ : Q * Q' = 1) {i : Fin m} (hN : (M * Q).BlockTriangular (bl i)) (hdet : IsUnit (M * Q).det)
    (hΛ : ∀ cf w, IsCombAtG t x f cf w →
      ((∃ a : Fin m → C, (∀ i, ‖a i‖ ≤ 1) ∧ IsCombAtG t x u a w) ↔ w ∈ Λ)) :
    grNorm t x Λ f i = ‖(M * Q) i i‖⁻¹ := by
  have hu := fun b => comb_tan hf (hM b)
  have h0 := (isUnit_bl hN hdet).ne_zero
  refine IsLeast.csInf_eq ⟨⟨fun k => (M * Q) k i, h0, fun k hk => hN (block_lt_iff.2 (.inr ⟨le_rfl, hk⟩)), ?_, rfl⟩, ?_⟩
  · obtain ⟨w, -, hw⟩ := exists_comb hu fun k => Q k i
    have h1 := tanLinG f hf u M _ w hM hw
    exact ⟨w, (hΛ _ w h1).1 ⟨_, fun k => hQ k i, hw⟩, h1⟩
  · rintro r ⟨cf, h1, h2, ⟨w, hw, hc⟩, rfl⟩
    obtain ⟨a, ha, hc'⟩ := (hΛ cf w hc).2 hw
    have h3 : cf = (M * Q).mulVec (Q'.mulVec a) := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, hQQ, Matrix.mul_one]
      exact hi _ _ _ hc (tanLinG f hf u M _ w hM hc')
    let _ := Matrix.invertibleOfIsUnitDet _ hdet
    have h4 : Q'.mulVec a = (M * Q)⁻¹.mulVec cf := by
      rw [h3, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]
    have h5 := (blockTriangular_mulVec (Matrix.blockTriangular_inv_of_blockTriangular hN) h2).1
    rw [← h4] at h5
    have h6 := (blockTriangular_mulVec hN h5).2
    rw [← h3] at h6
    have h7 : ‖Q'.mulVec a i‖ ≤ 1 := by
      change ‖∑ j, Q' i j * a j‖ ≤ 1
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun j _ => ?_
      rw [norm_mul]; exact mul_le_one₀ (hQ' _ _) (norm_nonneg _) (ha _)
    refine inv_anti₀ (norm_pos_iff.2 h1) ?_
    rw [h6, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) h7

variable (t) in

def Lead {K : Type} [CommRing K] (x : Sp K ⟶ X) {m : ℕ} (u v : Fin m → (Sp (DualNumber K) ⟶ t.G.left)) (i : Fin m)
    (ρ : K) (a : Fin m → K) : Prop :=
  ∃ (w : Sp (DualNumber K) ⟶ t.G.left) (cf : Fin m → K),
    IsCombAtG t x u a w ∧ IsCombAtG t x v cf w ∧ cf i = ρ ∧ ∀ k, i < k → cf k = 0

theorem bl_of_lead {S K : Type} [CommRing S] [Field K] (ι : S →+* K) (hι : Function.Injective ι)
    {x : Sp S ⟶ X} {m : ℕ} {f u : Fin m → (Sp (DualNumber S) ⟶ t.G.left)}
    (hf : ∀ k, IsTanAtG t x (f k))
    (hiK : Indep t (spMap ι ≫ x) fun k => spMap (Formalism.L2.Pj.dualMap ι) ≫ f k) {M : Matrix (Fin m) (Fin m) S}
    (hM : ∀ b, IsCombAtG t x f (fun k => M k b) (u b))
    {v : Fin m → (Sp (DualNumber K) ⟶ t.G.left)} {d : Fin m → K}
    (hv : ∀ i, ∃ cf : Fin m → K, cf i = d i ∧ (∀ k, i < k → cf k = 0) ∧
      IsCombAtG t (spMap ι ≫ x) (fun k => spMap (Formalism.L2.Pj.dualMap ι) ≫ f k) cf (v i))
    (A : Matrix (Fin m) (Fin m) S) (i : Fin m) (ρ : K)
    (h : Lead t (spMap ι ≫ x) (fun k => spMap (Formalism.L2.Pj.dualMap ι) ≫ u k) v i ρ fun b => ι (A b i))
    (h' : ∀ c, c < i →
      Lead t (spMap ι ≫ x) (fun k => spMap (Formalism.L2.Pj.dualMap ι) ≫ u k) v i ρ fun b => ι (A b i + A b c)) :
    (M * A).BlockTriangular (bl i) ∧ ι ((M * A) i i) = d i * ρ := by
  have hfK := fun k => GlobalTheory.FactorDepth.isTanAtG_map t ι (hf k)
  choose T hT1 hT2 hT3 using hv
  let T' : Matrix (Fin m) (Fin m) K := fun j i => T i j
  have hT' : T'.BlockTriangular id := fun j k hk => hT2 k j hk
  have key : ∀ a : Fin m → S,
      Lead t (spMap ι ≫ x) (fun k => spMap (Formalism.L2.Pj.dualMap ι) ≫ u k) v i ρ (fun b => ι (a b)) →
      (∀ k, i < k → M.mulVec a k = 0) ∧ ι (M.mulVec a i) = d i * ρ := by
    rintro a ⟨w, cf, h1, h2, h3, h4⟩
    have e1 := hiK _ _ _ (tanLinG _ hfK _ (M.map ι) _ w (fun c => GlobalTheory.LatDRFree.comb_map t ι (hM c)) h1)
      (tanLinG _ hfK v T' cf w hT3 h2)
    have e2 : ∀ k, ι (M.mulVec a k) = T'.mulVec cf k := fun k => by
      rw [← e1, RingHom.map_mulVec]
      rfl
    obtain ⟨e3, e4⟩ := tri_mulVec hT' h4
    exact ⟨fun k hk => hι (((e2 k).trans (e3 k hk)).trans (map_zero ι).symm), by rw [e2, e4, h3, ← hT1]⟩
  obtain ⟨k1, k2⟩ := key _ h
  have k3 : ∀ c, c < i → ∀ k, i ≤ k → (M * A) k c = 0 := fun c hc k hk => by
    obtain ⟨g1, g2⟩ := key _ (h' c hc)
    have e : ∀ k, M.mulVec (fun b => A b i + A b c) k = M.mulVec (fun b => A b i) k + (M * A) k c := fun k =>
      congrFun (Matrix.mulVec_add M (fun b => A b i) fun b => A b c) k
    rcases hk.eq_or_lt with rfl | hk
    · rw [e, map_add, k2] at g2
      exact hι ((add_eq_left.1 g2).trans (map_zero ι).symm)
    · have := g1 k hk
      rwa [e, k1 k hk, zero_add] at this
  refine ⟨fun k c hk => ?_, k2⟩
  rcases block_lt_iff.1 hk with ⟨a, b⟩ | ⟨a, b⟩
  · exact k3 c a k b
  · rcases a.eq_or_lt with rfl | a
    · exact k1 k b
    · exact k3 c a k b.le

end Block

section Concat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
  {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {Oz : Type} [CommRing Oz]
  {β : Oz →+* c.F} {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β}

def LtL (x y : Pad.Letter Dw) : Prop :=
  Fintype.equivFin (E →+* ℂ) x.1 < Fintype.equivFin (E →+* ℂ) y.1 ∨ (x.1 = y.1 ∧ (x.2 : ℕ) < y.2)

theorem LtL.asymm {x y : Pad.Letter Dw} (h : LtL x y) : ¬ LtL y x := by
  obtain ⟨a, i⟩ := x
  obtain ⟨b, j⟩ := y
  rintro (h' | ⟨h', h''⟩) <;> rcases h with h | ⟨h, h₀⟩
  · exact lt_asymm h h'
  · exact h'.ne (congrArg _ h.symm)
  · exact h.ne (congrArg _ h'.symm)
  · exact lt_asymm h₀ h''

theorem pairwise_ltL : (letters Dw).Pairwise LtL := by
  refine List.pairwise_flatMap.2 ⟨fun a _ => ?_, ?_⟩
  · rw [List.pairwise_map]
    exact (List.pairwise_lt_finRange _).imp fun h => .inr ⟨rfl, h⟩
  · refine (List.pairwise_lt_finRange _).imp fun {a b} hab x hx y hy => ?_
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
    obtain ⟨i', -, rfl⟩ := List.mem_map.1 hy
    exact .inl (by simpa using hab)

theorem lt_iff_ltL (a b : Fin (letters Dw).length) : a < b ↔ LtL ((letters Dw).get a) ((letters Dw).get b) := by
  have h := List.pairwise_iff_get.1 (pairwise_ltL (Dw := Dw))
  refine ⟨h a b, fun g => ?_⟩
  rcases lt_trichotomy a b with e | rfl | e
  · exact e
  · exact absurd g g.asymm
  · exact absurd g (h b a e).asymm

attribute [local instance] Over.cartesianMonoidalCategory in
open ReciprocityTheory.ChartRestriction.G.PullbackSections MonoidalCategory CartesianMonoidalCategory MonObj in

theorem grNorm_concat {C : Type} [NontriviallyNormedField C] {φ : c.F →+* C} {x : Sp C ⟶ Z.X}
    (Λ : Set (Sp (DualNumber C) ⟶ Z.t.G.left))
    {u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber C) ⟶ Z.t.G.left)} (hu : ∀ τ, IsEigBasis Z φ x τ (u τ))
    {σ : E →+* ℂ} {i : Fin (Dw.mult σ)} (k : Fin (letters Dw).length) (hk : (letters Dw).get k = ⟨σ, i⟩) :
    grNorm Z.t x Λ (fun a => u ((letters Dw).get a).1 ((letters Dw).get a).2) k =
      grNorm Z.t x {w | InGr Z φ x Λ σ w} (u σ) i := by
  let U : (τ : E →+* ℂ) → Fin (Dw.mult τ) → TanM x Z.t.G := fun τ a => GlobalTheory.LieMet.tanOf ((hu τ).1 a).1
  let e := Equiv.ofBijective _ (GlobalTheory.Proof.frame_combination_coeff_unique.get_bijective Dw)
  have he : ∀ y, (letters Dw).get (e.symm y) = y := e.apply_symm_apply
  have hc : ∀ cf w, IsCombAtG Z.t x
      (fun a : Fin (letters Dw).length => u ((letters Dw).get a).1 ((letters Dw).get a).2) cf w ↔
      w = (tv (∑ τ, ∑ a, cf (e.symm ⟨τ, a⟩) • U τ a)).left := fun cf w => by
    rw [← Fintype.sum_sigma fun y : Pad.Letter Dw => cf (e.symm y) • U y.1 y.2, ← Equiv.sum_comp e]
    simp only [Equiv.symm_apply_apply]
    exact GlobalTheory.Proof.frame_combination_coeff_unique.comb_iff (fun a => U (e a).1 (e a).2) cf w
  have hτ : ∀ τ cf w, IsCombAtG Z.t x (u τ) cf w ↔ w = (tv (∑ a, cf a • U τ a)).left := fun τ cf w =>
    GlobalTheory.Proof.frame_combination_coeff_unique.comb_iff (U τ) cf w
  have hs : ∀ {m : ℕ} (W : TanM x Z.t.G) (V : Fin m → TanM x Z.t.G) w,
      IsCombAtG Z.t x (Fin.cons (tv W).left fun j => (tv (V j)).left : Fin (m + 1) → _) (fun _ => 1) w ↔
        w = (tv (W + ∑ j, V j)).left := fun {m} W V w => by
    have := GlobalTheory.Proof.frame_combination_coeff_unique.comb_iff (Fin.cons W V : Fin (m + 1) → _) (fun _ => 1) w
    simp only [one_smul, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ] at this
    rw [← this]
    refine iff_of_eq (congrArg (fun q => IsCombAtG Z.t x q _ w) (_root_.funext fun j => ?_))
    exact Fin.cases rfl (fun _ => rfl) j
  have hek : e.symm ⟨σ, i⟩ = k := e.symm_apply_eq.2 hk.symm
  have hlt : ∀ y, k < e.symm y ↔ LtL ⟨σ, i⟩ y := fun y => by rw [lt_iff_ltL, he, hk]
  refine congrArg sInf (Set.ext fun r => ⟨?_, ?_⟩)
  · rintro ⟨cf, h0, hz, ⟨w, hw, hcw⟩, rfl⟩
    let T : Finset (E →+* ℂ) := Finset.univ.filter fun τ =>
      Fintype.equivFin (E →+* ℂ) τ < Fintype.equivFin (E →+* ℂ) σ
    let ε := T.equivFin.symm
    refine ⟨fun a => cf (e.symm ⟨σ, a⟩), by simpa only [hek] using h0, fun a ha => hz _ ((hlt _).2 (.inr ⟨rfl, ha⟩)),
      ⟨_, ⟨_, fun j => ε j, fun j => (tv (∑ a, cf (e.symm ⟨ε j, a⟩) • U (ε j) a)).left,
        fun j => ⟨(Finset.mem_filter.1 (ε j).2).2, eig_comb (hu _).1 ((hτ _ _ _).2 rfl)⟩, w, hw, ?_⟩,
        (hτ _ _ _).2 rfl⟩, by simp only [hek]⟩
    rw [hs, (hc _ _).1 hcw, ε.sum_comp fun τ => ∑ a, cf (e.symm ⟨τ, a⟩) • U τ a,
      Finset.sum_coe_sort T fun τ => ∑ a, cf (e.symm ⟨τ, a⟩) • U τ a,
      ← Finset.sum_insert (f := fun τ => ∑ a, cf (e.symm ⟨τ, a⟩) • U τ a) (show σ ∉ T by simp [T])]
    refine congrArg (fun q => (tv q).left) (Finset.sum_subset (Finset.subset_univ _) fun τ _ hτ' => ?_).symm
    simp only [T, Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and, not_or, not_lt] at hτ'
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [hz _ ((hlt _).2 (.inl (hτ'.2.lt_of_ne fun h => hτ'.1 ((Fintype.equivFin _).injective h).symm))), zero_smul]
  · rintro ⟨cf, h0, hz, ⟨w₀, ⟨m, ρ, v, hv, w, hw, hcw⟩, hc₀⟩, rfl⟩
    choose a ha using fun j => ((hu (ρ j)).2 _ (hv j).2).exists
    let G : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → C := Pi.single σ cf + ∑ j, Pi.single (ρ j) (a j)
    have hG : ∀ τ, Fintype.equivFin (E →+* ℂ) σ ≤ Fintype.equivFin (E →+* ℂ) τ →
        G τ = (Pi.single σ cf : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → C) τ := fun τ h => by
      simp only [G, Pi.add_apply, Finset.sum_apply]
      rw [Finset.sum_eq_zero fun j _ => Pi.single_eq_of_ne (fun g => ((hv j).1.trans_le h).ne (by rw [g])) _, add_zero]
    have hσ : G σ = cf := (hG σ le_rfl).trans (Pi.single_eq_same _ _)
    have hP : ∀ τ (b : Fin (Dw.mult τ) → C),
        ∑ τ', ∑ a, (Pi.single τ b : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → C) τ' a • U τ' a = ∑ a, b a • U τ a := fun τ b => by
      rw [Finset.sum_eq_single τ (fun τ' _ h => by simp [Pi.single_eq_of_ne h]) (by simp), Pi.single_eq_same]
    refine ⟨fun b => G (e b).1 (e b).2, ?_, fun b hb => ?_, ⟨w, hw, ?_⟩, ?_⟩
    · show G (e k).1 (e k).2 ≠ 0
      rwa [← hek, e.apply_symm_apply, hσ]
    · obtain ⟨⟨τ, b⟩, rfl⟩ := e.symm.surjective b
      beta_reduce
      rw [e.apply_symm_apply]
      rcases (hlt _).1 hb with h | ⟨h, h'⟩
      · show G τ b = 0
        rw [hG τ h.le, Pi.single_eq_of_ne fun g => h.ne (congrArg _ g.symm)]
        rfl
      · obtain rfl : σ = τ := h
        show G σ b = 0
        rw [hσ]
        exact hz b h'
    · rw [hc]
      rw [(hτ _ _ _).1 hc₀, show v = _ from _root_.funext fun j => (hτ _ _ _).1 (ha j), hs] at hcw
      rw [hcw]
      refine congrArg (fun q => (tv q).left) ?_
      have h1 : ∀ τ b, G (e (e.symm ⟨τ, b⟩)).1 (e (e.symm ⟨τ, b⟩)).2 = G τ b := fun τ b => by
        rw [e.apply_symm_apply]
      simp only [h1]
      simp only [G, Pi.add_apply, Finset.sum_apply, add_smul, Finset.sum_add_distrib, Finset.sum_smul, hP]
      congr 1
      rw [← Finset.sum_congr rfl fun j _ => hP (ρ j) (a j), Finset.sum_comm]
      exact Finset.sum_congr rfl fun τ _ => Finset.sum_comm
    · show _ = ‖G (e k).1 (e k).2‖⁻¹
      rw [← hek, e.apply_symm_apply, hσ]

end Concat

theorem exists_lower {X : Scheme.{0}} {M : X.Modules} {n : ℕ} (fl : Vert.Flag M n) (W : X.Opens) {c i : Fin n}
    (h : c < i) (s : Γ(fl.F c.succ, W)) :
    ∃ s' : Γ(fl.F i.succ, W), (fl.π i).app W s' = 0 ∧ (fl.ι i.succ).app W s' = (fl.ι c.succ).app W s := by
  have key : ∀ l : Fin (n + 1), c.succ ≤ l → ∃ g : fl.F c.succ ⟶ fl.F l, g ≫ fl.ι l = fl.ι c.succ := fun l => by
    induction l using Fin.induction with
    | zero => exact fun h => absurd h (not_le.2 (Fin.succ_pos c))
    | succ j ih =>
      intro hj
      rcases hj.eq_or_lt with e | e
      · exact e ▸ ⟨𝟙 _, Category.id_comp _⟩
      · obtain ⟨g, hg⟩ := ih (Fin.le_castSucc_iff.2 e)
        exact ⟨g ≫ fl.step j, by rw [Category.assoc, fl.step_ι, hg]⟩
  obtain ⟨g, hg⟩ := key i.castSucc (Fin.le_castSucc_iff.2 (Fin.succ_lt_succ_iff.2 h))
  refine ⟨(g ≫ fl.step i).app W s, (QCoh.app_app _ _ _ _).trans ?_, (QCoh.app_app _ _ _ _).trans ?_⟩
  · rw [Category.assoc, show fl.step i ≫ fl.π i = 0 from Limits.cokernel.condition _, Limits.comp_zero]
    rfl
  · rw [Category.assoc, fl.step_ι, hg]

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
  {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {Oz : Type} [CommRing Oz]
  {β : Oz →+* c.F} {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β}
  {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} (C : FlagCpt Z e)

theorem lnStep_core {Bs Bg Y₀ G : Scheme.{0}} [IsIntegral G] {jB : Bg ⟶ Bs} {πB : Bg ⟶ gen Z} {M : Bs.Modules}
    {τ : E →+* ℂ} {u : FrAssign Z M (Dw.mult τ) jB} (hu : IsLieFrames Z e jB πB M _ τ false u)
    {π₀ : Y₀ ⟶ Bs} {j : G ⟶ Y₀}
    {πG : G ⟶ C.Y.X} {φ : C.Y.Fn →+* G.functionField} {jG : G ⟶ Bg}
    (h₁ : jG ≫ jB = j ≫ π₀) (h₂ : jG ≫ πB = πG ≫ C.π) {V : Bs.Opens} {f : Fin (Dw.mult τ) → Γ(M, V)}
    (hf : VB.IsFrame f) {W : Y₀.Opens} (hWV : W ≤ π₀ ⁻¹ᵁ V)
    (A : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) Γ(Y₀, W)) (hA : IsUnit A.det)
    (r : G.functionField) (hx : ⊤ ≤ (FlagCov.genPt G ≫ j) ⁻¹ᵁ W)
    (hxV : ⊤ ≤ ((FlagCov.genPt G ≫ jG) ≫ jB) ⁻¹ᵁ V) (i : Fin (Dw.mult τ))
    (h : Lead Z.t (FlagCov.genPt G ≫ jG ≫ πB ≫ genι Z) (u V f hf G.functionField (FlagCov.genPt G ≫ jG) hxV)
      (fun k => spMap (Formalism.L2.Pj.dualMap φ) ≫ C.f0.v τ k) i r
      fun b => TangentOrigin.evalPt (FlagCov.genPt G ≫ j) W hx (A b i))
    (h' : ∀ a, a < i →
      Lead Z.t (FlagCov.genPt G ≫ jG ≫ πB ≫ genι Z) (u V f hf G.functionField (FlagCov.genPt G ≫ jG) hxV)
        (fun k => spMap (Formalism.L2.Pj.dualMap φ) ≫ C.f0.v τ k) i r
        fun b => TangentOrigin.evalPt (FlagCov.genPt G ≫ j) W hx (A b i + A b a))
    {v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)} (ε : Ext v)
    (z : Sp (AlgebraicClosure F) ⟶ G) (hz : (z ≫ πG) ≫ C.Y.str = spMap (algebraMap F (AlgebraicClosure F)))
    (yt : Sp ε.O ⟶ Y₀) (hyt : spMap ε.O.subtype ≫ yt = z ≫ j) (hW : ⊤ ≤ yt ⁻¹ᵁ W) (k : ℕ)
    (hk : (letters Dw)[k]? = some ⟨τ, i⟩)
    {S R : Type} [CommRing S] [CommRing R] {s : Sp S ⟶ G} {ι : S →+* G.functionField} (hι : Function.Injective ι)
    {χ : S →+* AlgebraicClosure F} {σ : R →+* S} {al : R →+* C.Y.Fn} {χ' : R →+* AlgebraicClosure F} {y : Sp R ⟶ C.Y.X}
    {φ₁ : c.F →+* R} (fr : EigFrame Z φ₁ (y ≫ C.π ≫ genι Z)) {d : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → C.Y.Fnˣ}
    (hT : fr.Tri al C.f0 d) (a₁ : spMap χ ≫ s = z) (a₂ : spMap ι ≫ s = FlagCov.genPt G) (a₃ : spMap σ ≫ y = s ≫ πG)
    (a₄ : spMap al ≫ y = genericPt C.Y) (b₁ : χ.comp σ = χ') (b₂ : ι.comp σ = φ.comp al)
    (c₁ : y ≫ C.π ≫ genStr Z = spMap φ₁) (hsW : ⊤ ≤ (s ≫ j) ⁻¹ᵁ W)
    {Ω : Type} [NontriviallyNormedField Ω] [IsUltrametricDist Ω] (io : AlgebraicClosure F →+* Ω)
    (hio : ∀ a, ‖io a‖ ≤ 1 ↔ a ∈ ε.O) (p : ℕ) (hzV : ⊤ ≤ ((z ≫ jG) ≫ jB) ⁻¹ᵁ V)
    (hΛ : ∀ w, IsEigTan Z ((io.comp (algebraMap F (AlgebraicClosure F))).comp e.symm.toRingHom)
        (spMap io ≫ (z ≫ jG) ≫ πB ≫ genι Z) τ w →
      ((∃ a : Fin (Dw.mult τ) → Ω, (∀ i, ‖a i‖ ≤ 1) ∧ IsCombAtG Z.t (spMap io ≫ (z ≫ jG) ≫ πB ≫ genι Z)
          (fun i => spMap (Formalism.L2.Pj.dualMap io) ≫ u V f hf _ (z ≫ jG) hzV i) a w) ↔
        InGr Z ((io.comp (algebraMap F (AlgebraicClosure F))).comp e.symm.toRingHom)
          (spMap io ≫ (z ≫ jG) ≫ πB ≫ genι Z) (latDR Z.t (spMap io ≫ (z ≫ jG) ≫ πB ≫ genι Z)) τ w))
    (ψ' : R →+* Ω) (hψ : ∀ a, ψ' a = io (χ' a)) :
    ∃ n : Sˣ, ι n.1 = φ (d τ i : C.Y.Fnˣ) * r ∧
      lnStep Z.t (spMap ψ' ≫ y ≫ C.π ≫ genι Z)
        (fun τ i => spMap (Formalism.L2.Pj.dualMap ψ') ≫ fr.v τ i) p false (.inr k) = -Real.log ‖io (χ n.1)‖ := by
  have a₅ : spMap χ' ≫ y = z ≫ πG := by rw [← b₁, ← sp_comp', a₃, reassoc_of% a₁]
  have hzW : ⊤ ≤ (z ≫ j) ⁻¹ᵁ W := hyt ▸ fun q _ => hW (Set.mem_univ (spMap ε.O.subtype q))
  have hV : ∀ {K : Type} [CommRing K] (w : Sp K ⟶ G), ⊤ ≤ (w ≫ j) ⁻¹ᵁ W → ⊤ ≤ ((w ≫ jG) ≫ jB) ⁻¹ᵁ V := fun w hy => by
    rw [Category.assoc, h₁, ← Category.assoc]
    exact fun q _ => hWV (hy (Set.mem_univ q))
  let x := spMap σ ≫ y ≫ C.π ≫ genι Z
  have d₀ : ∀ {T : Scheme.{0}} (g : gen Z ⟶ T),
      (s ≫ jG) ≫ πB ≫ g = spMap σ ≫ y ≫ C.π ≫ g := fun g => by
    rw [Category.assoc, reassoc_of% h₂, reassoc_of% a₃]
  have hub := hu.1 V f hf S (s ≫ jG) (hV s hsW) ((σ.comp φ₁).comp e.toRingHom) (by
    rw [d₀, reassoc_of% c₁, sp_comp', sp_comp])
  rw [d₀, show ((σ.comp φ₁).comp e.toRingHom).comp e.symm.toRingHom = σ.comp φ₁ from RingHom.ext fun a => by simp] at hub
  have nat : ∀ {K : Type} [CommRing K] (ψ : S →+* K) (y : Sp K ⟶ G) (_ : spMap ψ ≫ s = y) (hy),
      u V f hf K (y ≫ jG) hy = fun i => spMap (Formalism.L2.Pj.dualMap ψ) ≫ u V f hf S (s ≫ jG) (hV s hsW) i := by
    rintro K _ ψ _ rfl hy
    exact _root_.funext fun i => hu.2.2 V f hf S K ψ (s ≫ jG) _ hy i
  generalize u V f hf S (s ≫ jG) (hV s hsW) = uS at hub nat
  have hfb := eigBasis_bc fr σ τ
  choose Mc hM using fun i => (hfb.2 _ (hub.1 i)).exists
  choose Mc' hM' using fun i => (hub.2 _ (hfb.1 i)).exists
  have hiK : ∀ {K : Type} [CommRing K] (ψ : S →+* K), IsEigBasis Z ((ψ.comp σ).comp φ₁) (spMap ψ ≫ x) τ fun k =>
      spMap (Formalism.L2.Pj.dualMap ψ) ≫ spMap (Formalism.L2.Pj.dualMap σ) ≫ fr.v τ k := fun ψ => by
    simp only [x, dual_comp]
    rw [sp_comp']
    exact eigBasis_bc fr _ τ
  have e₁ : FlagCov.genPt G ≫ jG ≫ πB ≫ genι Z = spMap ι ≫ x := by
    rw [← a₂, show x = _ from (d₀ _).symm]; simp only [Category.assoc]
  simp only [e₁, nat ι _ a₂,
    evalPt_eq ι (s ≫ j) (x' := FlagCov.genPt G ≫ j) (by rw [← a₂, Category.assoc]) W hsW, map_add] at h h'
  have hMM : Matrix.of (fun a b => Mc b a) * Matrix.of (fun a b => Mc' b a) = 1 := by
    ext a b
    have := congrFun (indep_of_eig hfb _ _ _ (tanLinG _ (fun k => (hfb.1 k).1) uS (Matrix.of fun a b => Mc b a) _ _ hM
      (hM' b)) (isCombAtG_single Z.t _ (fun k => (hfb.1 k).1) b)) a
    rw [Matrix.one_apply, ← Pi.single_apply b (1 : S) a, ← this]
    rfl
  have hdet : IsUnit (Matrix.of (fun a b => Mc b a) * A.map (TangentOrigin.evalPt (s ≫ j) W hsW)).det := by
    rw [Matrix.det_mul, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (Matrix.isUnit_det_of_right_inverse hMM).mul (hA.map _)
  obtain ⟨hN, hd⟩ := bl_of_lead ι hι (fun k => (hfb.1 k).1) (indep_of_eig (hiK ι))
    (M := Matrix.of fun a b => Mc b a) hM
    (v := fun k => spMap (Formalism.L2.Pj.dualMap φ) ≫ C.f0.v τ k) (d := fun k => φ (d τ k : C.Y.Fnˣ))
    (fun i => by
      obtain ⟨cf, g₁, g₂, g₃⟩ := hT.2.2 τ i
      refine ⟨fun k => φ (cf k), congrArg φ g₁, fun k hk => (congrArg φ (g₂ k hk)).trans (map_zero φ), ?_⟩
      have g₄ := GlobalTheory.LatDRFree.comb_map Z.t φ g₃
      simp only [dual_comp, x] at g₄ ⊢
      rw [sp_comp', b₂, ← sp_comp', reassoc_of% a₄]
      exact g₄) (A.map (TangentOrigin.evalPt (s ≫ j) W hsW)) i r h
    (fun a ha => by simpa only [map_add, Matrix.map_apply] using h' a ha)
  have hun := isUnit_bl hN hdet
  refine ⟨hun.unit, hd, ?_⟩
  let ψ := io.comp χ
  have e₂ : spMap io ≫ (z ≫ jG) ≫ πB ≫ genι Z = spMap ψ ≫ x := by
    rw [show x = _ from (d₀ _).symm, ← sp_comp']
    simp only [Category.assoc, reassoc_of% a₁]
  have e₃ : ((io.comp (algebraMap F (AlgebraicClosure F))).comp e.symm.toRingHom) = (ψ.comp σ).comp φ₁ := by
    have : algebraMap F (AlgebraicClosure F) = (χ'.comp φ₁).comp e.toRingHom := EigLoc.spMap_inj (by
      rw [← sp_comp, ← sp_comp, ← c₁, ← hz, ← C.π_str]
      simp only [Category.assoc, reassoc_of% a₅])
    rw [this, ← b₁]
    refine RingHom.ext fun a => ?_
    change io (χ (σ (φ₁ (e (e.symm a))))) = io (χ (σ (φ₁ a)))
    rw [e.apply_symm_apply]
  have e₄ : ψ' = ψ.comp σ := RingHom.ext fun a => by rw [hψ, ← b₁]; rfl
  rw [e₂, e₃, nat χ z a₁] at hΛ
  simp only [dual_comp] at hΛ
  have hint : ∀ a, ‖ψ (TangentOrigin.evalPt (s ≫ j) W hsW a)‖ ≤ 1 := fun a => by
    have g₁ := evalPt_eq χ (s ≫ j) (x' := z ≫ j) (by rw [reassoc_of% a₁]) W hsW hzW a
    have g₂ := evalPt_eq ε.O.subtype yt hyt.symm W hW hzW a
    exact (hio _).2 (g₁ ▸ g₂ ▸ (TangentOrigin.evalPt yt W hW a).2)
  have mm : (Matrix.of fun a b => Mc b a).map ψ * (A.map (TangentOrigin.evalPt (s ≫ j) W hsW)).map ψ =
      (Matrix.of (fun a b => Mc b a) * A.map (TangentOrigin.evalPt (s ≫ j) W hsW)).map ψ := Matrix.map_mul.symm
  have hg := grNorm_of_bl (Λ := {w | InGr Z ((ψ.comp σ).comp φ₁) (spMap ψ ≫ x) (latDR Z.t (spMap ψ ≫ x)) τ w})
    (fun k => ((hiK ψ).1 k).1)
    (indep_of_eig (hiK ψ)) (M := (Matrix.of fun a b => Mc b a).map ψ)
    (Q := (A.map (TangentOrigin.evalPt (s ≫ j) W hsW)).map ψ)
    (Q' := (A⁻¹.map (TangentOrigin.evalPt (s ≫ j) W hsW)).map ψ)
    (fun b => GlobalTheory.LatDRFree.comb_map Z.t ψ (hM b)) (fun _ _ => hint _) (fun _ _ => hint _)
    (by rw [← Matrix.map_mul, ← Matrix.map_mul, A.mul_nonsing_inv hA, Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.map_one _ (map_zero _) (map_one _)]) (i := i)
    (by rw [mm]; exact fun a b hab => (congrArg ψ (hN hab)).trans (map_zero ψ))
    (by rw [mm, ← RingHom.mapMatrix_apply, ← RingHom.map_det]; exact hdet.map _)
    (fun cf w hw => hΛ w (eig_comb (hiK ψ).1 hw))
  rw [mm] at hg
  simp only [dual_comp, x] at hg
  rw [sp_comp', ← e₄] at hg
  obtain ⟨hkl, hk'⟩ := List.getElem?_eq_some_iff.1 hk
  simp only [lnStep, dif_pos hkl]
  exact (congrArg Real.log ((grNorm_concat _ (fun τ => eigBasis_bc fr ψ' τ) ⟨k, hkl⟩ hk').trans hg)).trans
    (Real.log_inv _)

theorem lnStep_padic {Bs Bg Y₀ G : Scheme.{0}} [IsIntegral G] {jB : Bg ⟶ Bs} {πB : Bg ⟶ gen Z} {M : Bs.Modules}
    {τ : E →+* ℂ} {u : FrAssign Z M (Dw.mult τ) jB} (hu : IsLieFrames Z e jB πB M _ τ false u)
    {π₀ : Y₀ ⟶ Bs} {j : G ⟶ Y₀}
    {πG : G ⟶ C.Y.X} {φ : C.Y.Fn →+* G.functionField} {jG : G ⟶ Bg}
    (h₁ : jG ≫ jB = j ≫ π₀) (h₂ : jG ≫ πB = πG ≫ C.π) {V : Bs.Opens} {f : Fin (Dw.mult τ) → Γ(M, V)}
    (hf : VB.IsFrame f) {W : Y₀.Opens} (hWV : W ≤ π₀ ⁻¹ᵁ V)
    (A : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) Γ(Y₀, W)) (hA : IsUnit A.det)
    (r : G.functionField) (hx : ⊤ ≤ (FlagCov.genPt G ≫ j) ⁻¹ᵁ W)
    (hxV : ⊤ ≤ ((FlagCov.genPt G ≫ jG) ≫ jB) ⁻¹ᵁ V) (i : Fin (Dw.mult τ))
    (h : Lead Z.t (FlagCov.genPt G ≫ jG ≫ πB ≫ genι Z) (u V f hf G.functionField (FlagCov.genPt G ≫ jG) hxV)
      (fun k => spMap (Formalism.L2.Pj.dualMap φ) ≫ C.f0.v τ k) i r
      fun b => TangentOrigin.evalPt (FlagCov.genPt G ≫ j) W hx (A b i))
    (h' : ∀ a, a < i →
      Lead Z.t (FlagCov.genPt G ≫ jG ≫ πB ≫ genι Z) (u V f hf G.functionField (FlagCov.genPt G ≫ jG) hxV)
        (fun k => spMap (Formalism.L2.Pj.dualMap φ) ≫ C.f0.v τ k) i r
        fun b => TangentOrigin.evalPt (FlagCov.genPt G ≫ j) W hx (A b i + A b a))
    {v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)} (ε : Ext v)
    (z : Sp (AlgebraicClosure F) ⟶ G) (hz : (z ≫ πG) ≫ C.Y.str = spMap (algebraMap F (AlgebraicClosure F)))
    (yt : Sp ε.O ⟶ Y₀) (hyt : spMap ε.O.subtype ≫ yt = z ≫ j) (hW : ⊤ ≤ yt ⁻¹ᵁ W) (k : ℕ)
    (hk : (letters Dw)[k]? = some ⟨τ, i⟩)
    {S R : Type} [CommRing S] [CommRing R] {s : Sp S ⟶ G} {ι : S →+* G.functionField} (hι : Function.Injective ι)
    {χ : S →+* AlgebraicClosure F} {σ : R →+* S} {al : R →+* C.Y.Fn} {χ' : R →+* AlgebraicClosure F} {y : Sp R ⟶ C.Y.X}
    {φ₁ : c.F →+* R} (fr : EigFrame Z φ₁ (y ≫ C.π ≫ genι Z)) {d : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → C.Y.Fnˣ}
    (hT : fr.Tri al C.f0 d) (a₁ : spMap χ ≫ s = z) (a₂ : spMap ι ≫ s = FlagCov.genPt G) (a₃ : spMap σ ≫ y = s ≫ πG)
    (a₄ : spMap al ≫ y = genericPt C.Y) (b₁ : χ.comp σ = χ') (b₂ : ι.comp σ = φ.comp al)
    (c₁ : y ≫ C.π ≫ genStr Z = spMap φ₁) (hsW : ⊤ ≤ (s ≫ j) ⁻¹ᵁ W)
    {p : ℕ} {ip : Fact p.Prime} (ip' : Fact p.Prime) (hzV : ⊤ ≤ ((z ≫ jG) ≫ jB) ⁻¹ᵁ V)
    (hΛ : haveI := ip
      ∀ w, IsEigTan Z (((ioOf p ε).comp (algebraMap F (AlgebraicClosure F))).comp e.symm.toRingHom)
          (spMap (ioOf p ε) ≫ (z ≫ jG) ≫ πB ≫ genι Z) τ w →
        ((∃ a : Fin (Dw.mult τ) → ℂ_[p], (∀ i, ‖a i‖ ≤ 1) ∧
            IsCombAtG Z.t (spMap (ioOf p ε) ≫ (z ≫ jG) ≫ πB ≫ genι Z)
              (fun i => spMap (Formalism.L2.Pj.dualMap (ioOf p ε)) ≫ u V f hf _ (z ≫ jG) hzV i) a w) ↔
          InGr Z (((ioOf p ε).comp (algebraMap F (AlgebraicClosure F))).comp e.symm.toRingHom)
            (spMap (ioOf p ε) ≫ (z ≫ jG) ≫ πB ≫ genι Z)
            (latDR Z.t (spMap (ioOf p ε) ≫ (z ≫ jG) ≫ πB ≫ genι Z)) τ w))
    (hio : ∀ a, ‖ioOf p ε a‖ ≤ 1 ↔ a ∈ ε.O) (ψ' : R →+* ℂ_[p]) (hψ : ∀ a, ψ' a = ioOf p ε (χ' a))
    (kd : Bool) (hkd : kd = false) :
    ∃ n : Sˣ, ι n.1 = φ (d τ i : C.Y.Fnˣ) * r ∧
      lnStep Z.t (spMap ψ' ≫ y ≫ C.π ≫ genι Z)
        (fun τ i => spMap (Formalism.L2.Pj.dualMap ψ') ≫ fr.v τ i) p kd (.inr k) = -Real.log ‖ioOf p ε (χ n.1)‖ := by
  obtain rfl : ip = ip' := rfl
  subst hkd
  exact lnStep_core C hu h₁ h₂ hf hWV A hA r hx hxV i h h' ε z hz yt hyt hW k hk hι fr hT a₁ a₂ a₃ a₄ b₁ b₂ c₁ hsW _ hio
    p hzV hΛ ψ' hψ

theorem grLat_at {X W : Scheme.{0}} {jB : W ⟶ X}
    {πB : W ⟶ gen Z} {M : X.Modules} {r : ℕ} {τ : E →+* ℂ} {u : FrAssign Z M r jB}
    (h : IsGrLat Z e jB πB M r τ u) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) (hp : (resP v).Prime)
    (ε : TrueGeo.Ext v) (xg : Sp (AlgebraicClosure F) ⟶ W) (xt : Sp ε.O ⟶ X)
    (h1 : xg ≫ πB ≫ genStr Z ≫ spMap e.toRingHom = spMap (algebraMap F (AlgebraicClosure F)))
    (h2 : spMap ε.O.subtype ≫ xt = xg ≫ jB) (U : X.Opens) (f : Fin r → Γ(M, U)) (hf : VB.IsFrame f)
    (h3 : ⊤ ≤ xt ⁻¹ᵁ U) (hx : ⊤ ≤ (xg ≫ jB) ⁻¹ᵁ U) :
    haveI : Fact (resP v).Prime := ⟨hp⟩
    ∀ w, IsEigTan Z (((ioOf (resP v) ε).comp (algebraMap F (AlgebraicClosure F))).comp e.symm.toRingHom)
        (spMap (ioOf (resP v) ε) ≫ xg ≫ πB ≫ genι Z) τ w →
      ((∃ a : Fin r → ℂ_[resP v], (∀ i, ‖a i‖ ≤ 1) ∧
          IsCombAtG Z.t (spMap (ioOf (resP v) ε) ≫ xg ≫ πB ≫ genι Z)
            (fun i => spMap (Formalism.L2.Pj.dualMap (ioOf (resP v) ε)) ≫ u U f hf _ xg hx i) a w) ↔
        InGr Z (((ioOf (resP v) ε).comp (algebraMap F (AlgebraicClosure F))).comp e.symm.toRingHom)
          (spMap (ioOf (resP v) ε) ≫ xg ≫ πB ≫ genι Z)
          (latDR Z.t (spMap (ioOf (resP v) ε) ≫ xg ≫ πB ≫ genι Z)) τ w) :=
  h v hp ε xg xt h1 h2 U f hf h3 hx

theorem lnStep_eq {Bs Bg Y₀ G : Scheme.{0}} [IsIntegral G] {jB : Bg ⟶ Bs} {πB : Bg ⟶ gen Z} {M : Bs.Modules}
    {τ : E →+* ℂ} {u : FrAssign Z M (Dw.mult τ) jB} (hu : IsLieFrames Z e jB πB M _ τ false u)
    {π₀ : Y₀ ⟶ Bs} {j : G ⟶ Y₀}
    {πG : G ⟶ C.Y.X} {φ : C.Y.Fn →+* G.functionField} {jG : G ⟶ Bg}
    (h₁ : jG ≫ jB = j ≫ π₀) (h₂ : jG ≫ πB = πG ≫ C.π) {V : Bs.Opens} {f : Fin (Dw.mult τ) → Γ(M, V)}
    (hf : VB.IsFrame f) {W : Y₀.Opens} (hWV : W ≤ π₀ ⁻¹ᵁ V)
    (A : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) Γ(Y₀, W)) (hA : IsUnit A.det)
    (r : G.functionField) (hx : ⊤ ≤ (FlagCov.genPt G ≫ j) ⁻¹ᵁ W)
    (hxV : ⊤ ≤ ((FlagCov.genPt G ≫ jG) ≫ jB) ⁻¹ᵁ V) (i : Fin (Dw.mult τ))
    (h : Lead Z.t (FlagCov.genPt G ≫ jG ≫ πB ≫ genι Z) (u V f hf G.functionField (FlagCov.genPt G ≫ jG) hxV)
      (fun k => spMap (Formalism.L2.Pj.dualMap φ) ≫ C.f0.v τ k) i r
      fun b => TangentOrigin.evalPt (FlagCov.genPt G ≫ j) W hx (A b i))
    (h' : ∀ a, a < i →
      Lead Z.t (FlagCov.genPt G ≫ jG ≫ πB ≫ genι Z) (u V f hf G.functionField (FlagCov.genPt G ≫ jG) hxV)
        (fun k => spMap (Formalism.L2.Pj.dualMap φ) ≫ C.f0.v τ k) i r
        fun b => TangentOrigin.evalPt (FlagCov.genPt G ≫ j) W hx (A b i + A b a))
    (hl : IsGrLat Z e jB πB M _ τ u)
    (φs : G.fromSpecStalk (genericPoint G) ≫ πG = spMap φ ≫ C.Y.X.fromSpecStalk (genericPoint C.Y.X))
    {v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)} (hp : (resP v).Prime) (ε : Ext v)
    (z : Sp (AlgebraicClosure F) ⟶ G) (hz : (z ≫ πG) ≫ C.Y.str = spMap (algebraMap F (AlgebraicClosure F)))
    (yt : Sp ε.O ⟶ Y₀) (hyt : spMap ε.O.subtype ≫ yt = z ≫ j) (hW : ⊤ ≤ yt ⁻¹ᵁ W) (k : ℕ)
    (hk : (letters Dw)[k]? = some ⟨τ, i⟩) (kind : ℕ → Bool) (hkd : kind (resP v) = false) :
    (∀ a : C.Y.X.presheaf.stalk (below (z ≫ πG)), ∃ a' : G.presheaf.stalk (below z),
      algebraMap _ G.functionField a' = φ (algebraMap _ C.Y.X.functionField a) ∧
        (Scheme.stalkClosedPointTo z).hom a' = (Scheme.stalkClosedPointTo (z ≫ πG)).hom a) ∧
    ∃ n : (G.presheaf.stalk (below z))ˣ, algebraMap _ G.functionField n.1 =
        φ ((C.gr_spec (below (z ≫ πG))).choose_spec.choose_spec.choose τ i : C.Y.Fnˣ) * r ∧
      haveI := Fact.mk hp
      LineNorm.symLog C kind (.inr k) v ε ⟨z ≫ πG, hz⟩ = (-Real.log (ε.w (resP v)) / Real.log (resP v)) *
        -Real.log ‖ioOf (resP v) ε ((Scheme.stalkClosedPointTo z).hom n.1)‖ := by
  obtain ⟨hT, -⟩ := (C.gr_spec (below (z ≫ πG))).choose_spec.choose_spec.choose_spec
  obtain ⟨σ, a₃⟩ : ∃ σ : C.Y.X.presheaf.stalk (below (z ≫ πG)) →+* G.presheaf.stalk (below z),
      spMap σ ≫ stalkPt C.Y (below (z ≫ πG)) = G.fromSpecStalk (below z) ≫ πG :=
    ⟨(πG.stalkMap (below z)).hom, Scheme.SpecMap_stalkMap_fromSpecStalk πG⟩
  have a₁ : spMap (Scheme.stalkClosedPointTo z).hom ≫ G.fromSpecStalk (below z) = z :=
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := .of _) z
  have a₂ : spMap (algebraMap (G.presheaf.stalk (below z)) G.functionField) ≫ G.fromSpecStalk (below z) =
      FlagCov.genPt G :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes (below z))
  have a₄ : spMap (algebraMap (C.Y.X.presheaf.stalk (below (z ≫ πG))) C.Y.X.functionField) ≫
      stalkPt C.Y (below (z ≫ πG)) = genericPt C.Y :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes _)
  have a₅ : spMap (Scheme.stalkClosedPointTo (z ≫ πG)).hom ≫ stalkPt C.Y (below (z ≫ πG)) = z ≫ πG :=
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := .of _) (z ≫ πG)
  have : Mono (stalkPt C.Y (below (z ≫ πG))) := inferInstanceAs (Mono (C.Y.X.fromSpecStalk _))
  have b₁ : (Scheme.stalkClosedPointTo z).hom.comp σ = (Scheme.stalkClosedPointTo (z ≫ πG)).hom :=
    EigLoc.spMap_inj ((cancel_mono (stalkPt C.Y (below (z ≫ πG)))).1
      ((sp_comp' _ _ _).symm.trans <| (congrArg (_ ≫ ·) a₃).trans <| (Category.assoc _ _ _).symm.trans <|
        (congrArg (· ≫ πG) a₁).trans a₅.symm))
  have b₂ : (algebraMap (G.presheaf.stalk (below z)) G.functionField).comp σ =
      φ.comp (algebraMap (C.Y.X.presheaf.stalk (below (z ≫ πG))) C.Y.X.functionField) :=
    EigLoc.spMap_inj ((cancel_mono (stalkPt C.Y (below (z ≫ πG)))).1
      ((sp_comp' _ _ _).symm.trans <| (congrArg (_ ≫ ·) a₃).trans <| (Category.assoc _ _ _).symm.trans <|
        (congrArg (· ≫ πG) a₂).trans <| φs.trans <| (congrArg (_ ≫ ·) a₄.symm).trans (sp_comp' _ _ _)))
  refine ⟨fun a => ⟨σ a, RingHom.congr_fun b₂ a, RingHom.congr_fun b₁ a⟩, ?_⟩
  have c₁ : stalkPt C.Y (below (z ≫ πG)) ≫ C.π ≫ genStr Z = spMap (C.gr_spec (below (z ≫ πG))).choose :=
    VarFlagSpec.eq_spMap_of_comp (IsFractionRing.injective _ C.Y.X.functionField)
      ((Category.assoc _ _ _).symm.trans <| (congrArg (· ≫ _) a₄).trans <| (VarFlagSpec.genericPt_genStr C).trans <|
        congrArg spMap hT.2.1)
  have hzW : ⊤ ≤ (z ≫ j) ⁻¹ᵁ W := hyt ▸ fun q _ => hW (Set.mem_univ (spMap ε.O.subtype q))
  have hsW : ⊤ ≤ (G.fromSpecStalk (below z) ≫ j) ⁻¹ᵁ W := le_pre (R := G.presheaf.stalk (below z)) _ _
    ((congrArg (fun q => j q ∈ W) Scheme.fromSpecStalk_closedPoint).mpr
      (hzW (Set.mem_univ (IsLocalRing.closedPoint _))))
  have hzV : ⊤ ≤ ((z ≫ jG) ≫ jB) ⁻¹ᵁ V := by
    rw [Category.assoc, h₁, ← Category.assoc]
    exact fun q _ => hWV (hzW (Set.mem_univ q))
  obtain ⟨hp', hio, -⟩ := ioOf_spec F v ε
  obtain rfl : hp = hp' := rfl
  have hΛ := grLat_at hl v hp ε (z ≫ jG) (yt ≫ π₀) (by
      rw [Category.assoc, reassoc_of% h₂, C.π_str, ← hz, Category.assoc])
    (by rw [reassoc_of% hyt, Category.assoc, h₁]) V f hf (fun q _ => hWV (hW (Set.mem_univ q))) hzV
  obtain ⟨n, k₁, k₂⟩ := lnStep_padic C hu h₁ h₂ hf hWV A hA r hx hxV i h h' ε z hz yt hyt hW k hk
    (IsFractionRing.injective (G.presheaf.stalk (below z)) G.functionField) _ hT a₁ a₂ a₃ a₄ b₁ b₂ c₁ hsW
    (Fact.mk hp) hzV hΛ hio _ (fun _ => RingHom.comp_apply _ _ _) _ hkd
  exact ⟨n, k₁, (symLog_eq C hp ε _ kind _).trans (congrArg _ k₂)⟩

theorem lgOf_letter {G : Scheme.{0}} [IsIntegral G] {πG : G ⟶ C.Y.X} {φ : C.Y.Fn →+* G.functionField}
    {v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)} (hp : (resP v).Prime) (ε : Ext v)
    (z : Sp (AlgebraicClosure F) ⟶ G) (hz : (z ≫ πG) ≫ C.Y.str = spMap (algebraMap F (AlgebraicClosure F)))
    (kind : ℕ → Bool) (R : Option ℝ) (τ : E →+* ℂ) (k : Fin (Dw.mult τ)) (st : ((E →+* ℂ) × ℕ) ⊕ ℕ)
    (hst : letterOf Dw st = some ⟨τ, k⟩) {A : CxSt F} (hm : Mets C A) (ρ : G.functionFieldˣ)
    (h₁ : ∀ a : C.Y.X.presheaf.stalk (below (z ≫ πG)), ∃ a' : G.presheaf.stalk (below z),
      algebraMap _ G.functionField a' = φ (algebraMap _ C.Y.X.functionField a) ∧
        (Scheme.stalkClosedPointTo z).hom a' = (Scheme.stalkClosedPointTo (z ≫ πG)).hom a)
    (n : (G.presheaf.stalk (below z))ˣ) (h₂ : algebraMap _ G.functionField n.1 =
        φ ((C.gr_spec (below (z ≫ πG))).choose_spec.choose_spec.choose τ k : C.Y.Fnˣ) * (ρ⁻¹ : G.functionFieldˣ))
    (h₄ : haveI := Fact.mk hp
      LineNorm.symLog C kind st v ε ⟨z ≫ πG, hz⟩ = (-Real.log (ε.w (resP v)) / Real.log (resP v)) *
        -Real.log ‖ioOf (resP v) ε ((Scheme.stalkClosedPointTo z).hom n.1)‖) :
    (adlOf C hm (Finsupp.single (kind, R, st) 1)).lg v ε ⟨z ≫ πG, hz⟩ = Real.log (ε.w (valAt z
      (φ (genAt (adlOf C hm (Finsupp.single (kind, R, st) 1)).D (below (z ≫ πG))) ^ 1 * (ρ : G.functionField)))) := by
  dsimp only [adlOf]
  obtain ⟨hp', -, hw⟩ := ioOf_spec F v ε
  obtain rfl : hp = hp' := rfl
  have hx : ∀ x, expo Dw (Finsupp.single ((kind, R, st) : Pad.Sym E) 1) x =
      if (⟨τ, k⟩ : Pad.Letter Dw) = x then 1 else 0 := fun x => by
    rw [expo, Finsupp.sum_single_index (by simp)]
    simp [hst]
  have hD : divOf C (expo Dw (Finsupp.single ((kind, R, st) : Pad.Sym E) 1)) = C.gr τ k := by
    simp [divOf, hx]
  have hE := (C.gr_spec (below (z ≫ πG))).choose_spec.choose_spec.choose_spec.2 τ k
  rw [LineNorm.lgOf_eq_lgCopy]
  refine (LineNorm.lgCopy_eq C _ v ε ⟨z ≫ πG, hz⟩).trans ?_
  rw [Finsupp.support_single _ (by omega), Finset.sum_singleton, Finsupp.single_eq_same]
  dsimp only [LineNorm.dg]
  rw [h₄]
  clear h₄
  generalize (C.gr_spec (below (z ≫ πG))).choose_spec.choose_spec.choose = d at h₂ hE ⊢
  have hP : ∏ x : Pad.Letter Dw, d x.1 x.2 ^ expo Dw (Finsupp.single ((kind, R, st) : Pad.Sym E) 1) x = d τ k := by
    simp only [hx]
    rw [Finset.prod_eq_single (⟨τ, k⟩ : Pad.Letter Dw) (fun b _ hb => by rw [if_neg hb.symm, zpow_zero]) (by simp),
      if_pos rfl, zpow_one]
  have hq := Base.isEqn_eqn (C.gr τ k) (below (z ≫ πG))
  rw [hP, genAt, hD]
  generalize eqn (C.gr τ k) (below (z ≫ πG)) = g at hq ⊢
  obtain ⟨a, ha, ea⟩ : UnitAt (below (z ≫ πG)) ((d τ k * g⁻¹ : C.Y.Fnˣ) : C.Y.Fn) := by
    simpa [div_eq_mul_inv] using hq.iff_unitAt.1 hE
  obtain ⟨a', e₁, e₂⟩ := h₁ a
  have e {T : Type} [Field T] (ψ : G.presheaf.stalk (below z) →+* T) : ψ (n⁻¹ : _ˣ) = (ψ n)⁻¹ :=
    map_units_inv ψ n
  have e₃ : φ ((g⁻¹ : C.Y.Fnˣ) : C.Y.Fn) ^ 1 * (ρ : G.functionField) =
      algebraMap _ G.functionField (a' * (n⁻¹ : _ˣ)) := by
    have h0 : φ (d τ k : C.Y.Fnˣ) ≠ 0 := (map_ne_zero φ).2 (d τ k).ne_zero
    have h1 := ρ.ne_zero
    rw [map_mul, e, h₂, e₁, ea]
    simp
    field_simp
  have n₁ : ε.w ((Scheme.stalkClosedPointTo (z ≫ πG)).hom a) ≠ 0 := ε.w.ne_zero (ha.map _).ne_zero
  have n₂ : ε.w ((Scheme.stalkClosedPointTo z).hom n.1) ≠ 0 := ε.w.ne_zero (n.isUnit.map _).ne_zero
  rw [e₃, ← ea, Base.valAt_stalk, Base.valAt_stalk, map_mul, e, e₂, map_mul, map_inv₀,
    Real.log_mul n₁ (inv_ne_zero n₂), Real.log_inv, hw ((Scheme.stalkClosedPointTo z).hom n.1)]
  push_cast
  ring

end Free

theorem lg_whole_eq : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.CovHt.HypothesesH → GlobalTheory.Published.RegularAlteration →
  ∀ (D : D7) (O : Setup D) (hO : O.Core) (R : ℝ) (hR : 2 ≤ R) (c : O.s.Comp) (Bs : Scheme.{0}) [IsIntegral Bs] (q : Bs ⟶ Sp (𝓞 D.what₂.LL))
    (arq : IsArithVar q (dimGr D.what₂.Tau O.N O.j)) (nBs : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Bs)
    (Bg : Scheme.{0}) (jB : Bg ⟶ Bs) (πB : Bg ⟶ gen O.s.T.Z) (G : ∀ σ', EigMet O.s.T.Z σ')
    (Y X Gs : Scheme.{0}) [IsIntegral Y] [IsIntegral X] [IsIntegral Gs] (π : Y ⟶ Bs) (ρ : X ⟶ Y) (j : Gs ⟶ X)
    (πG : Gs ⟶ (O.var c).X) (φ : (O.var c).Fn →+* Gs.functionField) (jG : Gs ⟶ Bg),
    IsArithVar (ρ ≫ π ≫ q) (O.var c).dim → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X →
    GlobalTheory.PairCov.CovCommon O R c q jB πB G π ρ j πG φ jG →
    ∀ (σ : D.host.E →+* ℂ) (M : Bs.Modules) (hM : VMetric q M (O.S.Dw.mult σ)) (HM : hM.IsCInf)
      (t : FrAssign O.s.T.Z M (O.S.Dw.mult σ) jB), IsLieFrames O.s.T.Z O.κ.e jB πB M _ σ false t →
    IsGrLat O.s.T.Z O.κ.e jB πB M _ σ t →
    ∀ (F : Vert.Flag ((Scheme.Modules.pullback ρ).obj ((Scheme.Modules.pullback π).obj M)) (O.S.Dw.mult σ))
      (i : Fin (O.S.Dw.mult σ)) (r : ((F.root i).pull j).ι → Gs.functionFieldˣ),
      GlobalTheory.PairCov.IsFrameSecX (O := O) (c := c) σ hM.isVB jB πB t π ρ F j φ jG i r →
    ∀ k : ℕ, (letters O.S.Dw)[k]? = some ⟨σ, i⟩ →
    ∀ (v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.what₂.LL)) (e : Ext v) (y : AlgPt (O.var c))
      (z : Sp (AlgebraicClosure D.what₂.LL) ⟶ Gs) (yt : Sp e.O ⟶ X) (ch : ((VMetric.grLB F i ((HM.pull π rfl).pull ρ rfl)).B.pull j).ι),
      z ≫ πG = y.1 → spMap e.O.subtype ≫ yt = z ≫ j → ⊤ ≤ yt ⁻¹ᵁ (VMetric.grLB F i ((HM.pull π rfl).pull ρ rfl)).B.U (ch PUnit.unit) →
        ((1 : ℕ) : ℝ) * (lineAdl O R c (.inr k) 1).lg v e y =
          Real.log (e.w (valAt z (φ (genAt (lineAdl O R c (.inr k) 1).D (below y.1)) ^ 1 * (r ch : Gs.functionField)))) := by
  intro _ _ _ D O _ R _ c Bs _ q _ _ Bg jB πB G Y X Gs _ _ _ π ρ j πG φ jG _ _ hc σ M hM HM t ht hl F i r hr k hk v e
    y z yt ch hz hyt hU
  obtain ⟨-, -, -, -, -, -, -, φs, h₁, h₂⟩ := hc
  obtain ⟨hp, -⟩ := ioOf_spec _ v e
  have := hM.isVB.isQuasicoherent
  have := (hM.isVB.pullback π).isQuasicoherent
  obtain ⟨y, hy⟩ := y
  obtain rfl : z ≫ πG = y := hz
  have hch : ∃ ck : ∀ k, Chart (F.gr k) 1, ck i = ch PUnit.unit ∧
      ∀ k, yt (IsLocalRing.closedPoint e.O) ∈ (ck k).U := by
    choose U f hx hf using fun k => F.isVB_gr k (yt (IsLocalRing.closedPoint e.O))
    obtain ⟨c₀, hc₀, hU'⟩ : ∃ c₀ : Chart (F.gr i) 1, c₀ = ch PUnit.unit ∧
      yt (IsLocalRing.closedPoint e.O) ∈ c₀.U := ⟨_, rfl, hU (Set.mem_univ _)⟩
    refine ⟨Function.update (fun k => ⟨U k, f k, hf k⟩) i c₀, (Function.update_self ..).trans hc₀, fun k => ?_⟩
    by_cases hk : k = i
    · subst hk
      rw [Function.update_self]
      exact hU'
    · rw [Function.update_of_ne hk]
      exact hx k
  obtain ⟨ck, hck, hx⟩ := hch
  obtain ⟨V, f, hV, hf⟩ := hM.isVB (π (ρ (yt (IsLocalRing.closedPoint e.O))))
  obtain ⟨W, hxW, hWV, hW, s, hs, hfr⟩ := exists_lifts F _ ck hx (ρ ⁻¹ᵁ (π ⁻¹ᵁ V)) hV
  have hyW := le_pre yt W hxW
  have hgW : ⊤ ≤ (FlagCov.genPt Gs ≫ j) ⁻¹ᵁ W := le_pre (R := Gs.functionField) _ _ (by
    have h0 : ⊤ ≤ (z ≫ j) ⁻¹ᵁ W := hyt ▸ fun q _ => hyW (Set.mem_univ (spMap e.O.subtype q))
    have h1 : FlagCov.genPt Gs (IsLocalRing.closedPoint _) = genericPoint Gs := Scheme.fromSpecStalk_closedPoint
    exact (congrArg (fun q => j q ∈ W) h1).mpr ((genericPoint_specializes (below z)).mem_open (j ⁻¹ᵁ W).isOpen
      (h0 (Set.mem_univ (IsLocalRing.closedPoint _)))))
  have hgV : ⊤ ≤ ((FlagCov.genPt Gs ≫ jG) ≫ jB) ⁻¹ᵁ V := by
    rw [Category.assoc, h₁, ← Category.assoc]
    exact fun q _ => hWV (hgW (Set.mem_univ q))
  have hA : IsUnit (Matrix.det (Matrix.of fun b k =>
      (((hf.pullback π).pullback ρ).basis hWV).repr ((F.ι k.succ).app W (s k)) b)) := by
    have := (((hf.pullback π).pullback ρ).basis hWV).isUnit_det (hfr.basis le_rfl)
    rw [Module.Basis.det_apply] at this
    convert this using 2
    ext b k
    rw [Module.Basis.toMatrix_apply, IsFrame.basis_apply, Twist.resM_self]
    rfl
  obtain ⟨k₁, n, k₂, k₃⟩ := lnStep_eq (O.Φ.C c) ht (π₀ := ρ ≫ π) h₁ h₂ hf hWV _ hA
    ((r fun _ => ck i)⁻¹ : Gs.functionFieldˣ) hgW hgV i
    (hr (fun _ => ck i) V f hf W (hW i) hWV (s i) (hs i) hgW hgV)
    (fun a ha => by
      obtain ⟨s', g₁, g₂⟩ := exists_lower F W ha (s a)
      have g := hr (fun _ => ck i) V f hf W (hW i) hWV (s i + s') (by rw [map_add, g₁, add_zero]; exact hs i) hgW hgV
      simp only [map_add ((F.ι i.succ).app W).hom, g₂, map_add (Module.Basis.repr _), Finsupp.add_apply] at g
      exact g)
    hl φs hp e z hy yt hyt hyW k hk (ArIn.ind ∅) (by simp [ArIn.ind])
  have hri : (r fun _ => ck i) = r ch := congrArg _ (_root_.funext fun _ => hck)
  rw [Nat.cast_one, one_mul, ← hri]
  exact lgOf_letter (O.Φ.C c) hp e z hy _ _ σ i (.inr k) hk _ _ k₁ n k₂ k₃

end GlobalTheory.PairCov.WholeFin

end
