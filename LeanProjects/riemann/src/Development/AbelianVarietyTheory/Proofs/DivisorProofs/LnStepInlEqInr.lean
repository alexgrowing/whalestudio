import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DegFrame
import Formalism.LocalToGlobal.ProjectiveLattices.SatLeaves
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDescendingLetterChain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedEmbeddingsSeparatingCombinationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamLatticeTangentCombinationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateLatticeTangentCombinationStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.ShFam.Pad

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UnramLine

theorem exists_idem : ∀ (E : Type) [Field E] [NumberField E] (C : Type) [NontriviallyNormedField C]
    [IsUltrametricDist C] (p : ℕ), p.Prime → ‖(p : C)‖ < 1 → ¬ p ∣ (NumberField.discr E).natAbs →
    ∀ σ : E →+* C, ∃ (n : ℕ) (a : Fin n → 𝓞 E) (c : Fin n → C), (∀ j, ‖c j‖ ≤ 1) ∧
      ∑ j, c j * σ (a j : E) = 1 ∧ ∀ φ : E →+* C, φ ≠ σ → ∑ j, c j * φ (a j : E) = 0 :=
  GlobalTheory.T.unramified_embeddings_separating_combination

theorem latDR_comb_mem : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (X : Scheme.{0}) (t : SAB H X) (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] (x : Sp C ⟶ X)
    (w : Sp (DualNumber C) ⟶ t.G.left), IsTanAtG t x w → w ∈ latDR t x → ∀ (n : ℕ) (a : Fin n → 𝓞 E) (c : Fin n → C),
    (∀ j, ‖c j‖ ≤ 1) → ∀ W : Sp (DualNumber C) ⟶ t.G.left,
    IsCombAtG t x (fun j => w ≫ (t.act.act (a j)).left) c W → W ∈ latDR t x :=
  GlobalTheory.T.de_rham_lattice_tangent_combination

theorem latHT_comb_mem : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (X : Scheme.{0}) (t : SAB H X) (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] (p : ℕ)
    (x : Sp C ⟶ X) (w : Sp (DualNumber C) ⟶ t.G.left), IsTanAtG t x w → w ∈ latHT t p x →
    ∀ (n : ℕ) (a : Fin n → 𝓞 E) (c : Fin n → C),
    (∀ j, ‖c j‖ ≤ 1) → ∀ W : Sp (DualNumber C) ⟶ t.G.left,
    IsCombAtG t x (fun j => w ≫ (t.act.act (a j)).left) c W → W ∈ latHT t p x :=
  GlobalTheory.T.hodge_tate_lattice_tangent_combination

theorem lat_comb_mem {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {X : Scheme.{0}} (t : SAB H X) {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C] (p : ℕ) (b : Bool)
    (x : Sp C ⟶ X) (w : Sp (DualNumber C) ⟶ t.G.left) (hwt : IsTanAtG t x w) (hw : w ∈ lat t p x b) {n : ℕ}
    (a : Fin n → 𝓞 E) (c : Fin n → C) (hc : ∀ j, ‖c j‖ ≤ 1) (W : Sp (DualNumber C) ⟶ t.G.left)
    (hW : IsCombAtG t x (fun j => w ≫ (t.act.act (a j)).left) c W) : W ∈ lat t p x b := by
  cases b
  · exact latDR_comb_mem E H X t C x w hwt hw n a c hc W hW
  · exact latHT_comb_mem E H X t C p x w hwt hw n a c hc W hW

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {X : Scheme.{0}} (t : SAB H X) {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C] (x : Sp C ⟶ X)

theorem prod_block (U : Letter Dw → (overAt x (DualNumber C) ⟶ t.G)) (hU : ∀ y, smT x 0 (U y) = 1)
    (σ : E →+* ℂ) (g : Letter Dw → C) (hg : ∀ y : Letter Dw, y.1 ≠ σ → g y = 0) :
    ∏ y, smT x (g y) (U y) = combT x (fun i => U ⟨σ, i⟩) (fun i => g ⟨σ, i⟩) := by
  classical
  rw [Fintype.prod_sigma, Finset.prod_eq_single σ]
  · rfl
  · intro τ _ hτ
    exact Finset.prod_eq_one fun i _ => by rw [hg ⟨τ, i⟩ hτ]; exact hU _
  · intro h; exact absurd (Finset.mem_univ σ) h

end Main

section Main2

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {X : Scheme.{0}} (t : SAB H X) {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C] (x : Sp C ⟶ X)

theorem lnStep_inl_eq_inr (u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber C) ⟶ t.G.left)) (p : ℕ)
    (hp : p.Prime) (hpC : ‖(p : C)‖ < 1) (hpd : ¬ p ∣ (NumberField.discr E).natAbs)
    (emb : (E →+* ℂ) → (E →+* C)) (hemb : Function.Injective emb) (htan : ∀ τ i, IsTanAtG t x (u τ i))
    (heig : ∀ τ i (a : 𝓞 E), u τ i ≫ (t.act.act a).left = spMap (epsMul (emb τ (a : E))) ≫ u τ i)
    (b : Bool) (k : ℕ) (z : Letter Dw) (hk : (letters Dw)[k]? = some z) :
    lnStep t x u p b (.inl (z.1, (z.2 : ℕ))) = lnStep t x u p b (.inr k) := by
  classical
  obtain ⟨hkl, hz⟩ := List.getElem?_eq_some_iff.1 hk
  have hnd : (letters Dw).Nodup := GlobalTheory.Proof.LetterConjugation.nodup_letters Dw
  have hmem : ∀ y, y ∈ letters Dw := GlobalTheory.Proof.LetterConjugation.mem_letters Dw
  let e : Fin (letters Dw).length ≃ Letter Dw := List.Nodup.getEquivOfForallMemList (letters Dw) hnd hmem
  have he : ∀ l, e l = (letters Dw).get l := fun l => rfl
  have hek : e ⟨k, hkl⟩ = z := by rw [he]; exact hz
  have hes : e.symm z = ⟨k, hkl⟩ := by rw [Equiv.symm_apply_eq, hek]
  have hpw := List.pairwise_iff_get.1 (GlobalTheory.Proof.exists_descending_letter_chain.pairwise_letters Dw)
  have O1 : ∀ j : Fin (Dw.mult z.1), z.2 < j → k < (e.symm ⟨z.1, j⟩ : ℕ) := by
    intro j hj
    have hj' : (z.2 : ℕ) < j := hj
    by_contra hle
    push_neg at hle
    rcases lt_or_eq_of_le hle with hlt | heq
    · have h1 := hpw (e.symm ⟨z.1, j⟩) ⟨k, hkl⟩ hlt
      rw [← he, ← he, Equiv.apply_symm_apply, hek] at h1
      have h2 : (j : ℕ) ≤ z.2 := h1 rfl
      omega
    · have h1 : e.symm ⟨z.1, j⟩ = ⟨k, hkl⟩ := Fin.ext heq
      rw [Equiv.symm_apply_eq, hek] at h1
      have h2 := congrArg (fun y : Letter Dw => (y.2 : ℕ)) h1
      simp only at h2
      omega
  have O2 : ∀ l : Fin (letters Dw).length, k < (l : ℕ) → ∀ h1 : (e l).1 = z.1, (z.2 : ℕ) < ((e l).2 : ℕ) := by
    intro l hl h1
    have h2 := hpw ⟨k, hkl⟩ l hl
    rw [← he, ← he, hek] at h2
    have h3 : (z.2 : ℕ) ≤ (e l).2 := h2 h1.symm
    rcases lt_or_eq_of_le h3 with h4 | h4
    · exact h4
    · exfalso
      have h5 : e l = z := Sigma.ext h1 ((Fin.heq_ext_iff (congrArg Dw.mult h1)).2 h4.symm)
      rw [← hek] at h5
      have h6 := congrArg Fin.val (e.injective h5)
      simp only at h6
      omega
  let U : Letter Dw → (overAt x (DualNumber C) ⟶ t.G) := fun y => ovT (htan y.1 y.2)
  have hU0 : ∀ y, smT x 0 (U y) = 1 := fun y => smT_zero_ovT (htan y.1 y.2)
  have hUe : ∀ y (a : 𝓞 E), U y ≫ t.act.act a = smT x (emb y.1 (a : E)) (U y) := fun y a =>
    Over.OverMorphism.ext (heig y.1 y.2 a)
  have hcomb : ∀ cf : Fin (letters Dw).length → C,
      combT x (fun i => U (e i)) cf = ∏ y, smT x (cf (e.symm y)) (U y) := by
    intro cf
    rw [← e.prod_comp]
    simp only [Equiv.symm_apply_apply]
    rfl
  have hvd : vDiff E p = 0 := by
    simp [vDiff, padicValNat.eq_zero_of_not_dvd hpd]
  have key : grNorm t x (lat t p x b) (u z.1) z.2 =
      grNorm t x (lat t p x b) (fun i => u ((letters Dw).get i).1 ((letters Dw).get i).2) ⟨k, hkl⟩ := by
    unfold grNorm
    congr 1
    ext r
    constructor
    · rintro ⟨cf, hcf0, hcfz, ⟨w, hwΛ, hw⟩, rfl⟩
      let g : Letter Dw → C := fun y => if h : y.1 = z.1 then cf ⟨y.2, h ▸ y.2.isLt⟩ else 0
      have hgz : g z = cf z.2 := by simp [g]
      refine ⟨fun l => g (e l), ?_, ?_, ⟨w, hwΛ, ?_⟩, ?_⟩
      · show g (e ⟨k, hkl⟩) ≠ 0
        rw [hek, hgz]; exact hcf0
      · intro l hl
        show g (e l) = 0
        simp only [g]
        split_ifs with h1
        · exact hcfz _ (Fin.lt_def.2 (O2 l hl h1))
        · rfl
      · refine (isCombAtG_iff t x (fun i => U (e i)) _ w).2 ?_
        rw [hcomb]
        simp only [Equiv.apply_symm_apply]
        rw [prod_block t x U hU0 z.1 g (fun y hy => dif_neg hy)]
        rw [← (isCombAtG_iff t x (fun i => U ⟨z.1, i⟩) cf w).1 hw]
        congr 2
        funext i
        simp [g]
      · show ‖cf z.2‖⁻¹ = ‖g (e ⟨k, hkl⟩)‖⁻¹
        rw [hek, hgz]
    · rintro ⟨cf, hcf0, hcfz, ⟨w, hwΛ, hw⟩, rfl⟩
      obtain ⟨n, a, c, hc, hδ1, hδ0⟩ := exists_idem E C p hp hpC hpd (emb z.1)
      have hw' : (∏ y, smT x (cf (e.symm y)) (U y)).left = w := by
        rw [← hcomb]; exact (isCombAtG_iff t x (fun i => U (e i)) cf w).1 hw
      set Wt := ∏ y, smT x (cf (e.symm y)) (U y) with hWt
      have hcomb' : IsCombAtG t x (fun j => w ≫ (t.act.act (a j)).left) c
          (combT x (fun j => Wt ≫ t.act.act (a j)) c).left := by
        rw [← hw']
        exact (isCombAtG_iff t x (fun j => Wt ≫ t.act.act (a j)) c _).2 rfl
      have hwt : IsTanAtG t x w := by
        rw [← (isCombAtG_iff t x (fun i => U (e i)) cf w).1 hw]
        exact isTanAtG_of _ (combT_tan x _ (fun i => hU0 _) cf)
      have hmemΛ := lat_comb_mem t p b x w hwt hwΛ a c hc _ hcomb'
      have hcalc : combT x (fun j => Wt ≫ t.act.act (a j)) c =
          combT x (fun i => U ⟨z.1, i⟩) (fun i => cf (e.symm ⟨z.1, i⟩)) := by
        have h1 : ∀ j, smT x (c j) (Wt ≫ t.act.act (a j)) =
            ∏ y, smT x (c j * (cf (e.symm y) * emb y.1 (a j : E))) (U y) := by
          intro j
          haveI := t.act.hom (a j)
          have h2 : Wt ≫ t.act.act (a j) = ∏ y, (smT x (cf (e.symm y)) (U y) ≫ t.act.act (a j)) :=
            map_prod (postHom x (t.act.act (a j))) _ _
          rw [h2, smT_prod]
          refine Finset.prod_congr rfl fun y _ => ?_
          rw [← smT_post, hUe, smT_smT, smT_smT, _root_.mul_assoc]
        simp only [combT]
        rw [Finset.prod_congr rfl fun j _ => h1 j, Finset.prod_comm]
        have h3 : ∀ y : Letter Dw, ∏ j, smT x (c j * (cf (e.symm y) * emb y.1 (a j : E))) (U y) =
            smT x (if y.1 = z.1 then cf (e.symm y) else 0) (U y) := by
          intro y
          rw [← smT_sum x _ _ _ (hU0 y)]
          congr 1
          have h4 : ∑ j, c j * (cf (e.symm y) * emb y.1 (a j : E)) = cf (e.symm y) * ∑ j, c j * emb y.1 (a j : E) := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
          rw [h4]
          by_cases hy : y.1 = z.1
          · rw [if_pos hy, hy, hδ1, _root_.mul_one]
          · rw [if_neg hy, hδ0 _ (hemb.ne hy), MulZeroClass.mul_zero]
        rw [Finset.prod_congr rfl fun y _ => h3 y]
        rw [prod_block t x U hU0 z.1 _ (fun y hy => if_neg hy)]
        simp only [if_true]
        rfl
      refine ⟨fun i => cf (e.symm ⟨z.1, i⟩), ?_, ?_, ⟨_, hmemΛ, ?_⟩, ?_⟩
      · show cf (e.symm ⟨z.1, z.2⟩) ≠ 0
        rw [Sigma.eta, hes]; exact hcf0
      · intro i hi
        exact hcfz _ (Fin.lt_def.2 (O1 i hi))
      · rw [hcalc]
        exact (isCombAtG_iff t x (fun i => U ⟨z.1, i⟩) _ _).2 rfl
      · show ‖cf ⟨k, hkl⟩‖⁻¹ = ‖cf (e.symm ⟨z.1, z.2⟩)‖⁻¹
        rw [Sigma.eta, hes]
  simp only [lnStep, dif_pos z.2.isLt, dif_pos hkl, hvd, zero_mul, ite_self, sub_zero, Fin.eta]
  exact congrArg Real.log key

end Main2

end GlobalTheory.UnramLine
