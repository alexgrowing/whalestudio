import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ResidueDegreeOfIsClosedImmersion
import Development.AbelianVarietyTheory.Definitions.Divisors.GenericPointAsIdeal
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.InterNumConsEqCokernel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimEqSucc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwoEmbeddingsOfTranscendental
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithIntersectionFormExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedSubschemeModLProjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqMultiDiff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialTopSelfIntersectionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CodimOneIntegralSubschemeDimStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreProjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreDimensionLeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibrePreimmersionIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueDegreeEqEulerCharacteristicStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchIntegrablePolynomialVanishingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberZeroSmallImageStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreIntersectionFormulaStatement

set_option autoImplicit false

noncomputable section

open MvPolynomial GlobalTheory.Published
open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open GlobalTheory.Cartier

namespace GlobalTheory.FibreProj

variable {k : Type} [CommRing k] {B Y : Scheme.{0}} [IsIntegral B] {q : B ⟶ Sp k} {p : Y ⟶ Sp k} {d : ℕ}

theorem dim_closure_lt (hB : IsArithVar q d) {b : B} (hb : b ≠ genericPoint B) :
    topologicalKrullDim (closure ({b} : Set B)) < ((d + 1 : ℕ) : WithBot ℕ∞) := by
  have hgen : genericPoint B ∉ closure ({b} : Set B) := fun h =>
    hb ((genericPoint_specializes b).antisymm (specializes_iff_mem_closure.2 h)).eq.symm
  have h1 : topologicalKrullDim (Set.univ : Set B) = (d + 1 : ℕ) :=
    (topologicalKrullDim_eq_of_isEmbedding Topology.IsEmbedding.id Set.range_id).trans hB.dim_eq
  have hup : topologicalKrullDim (closure ({b} : Set B)) + 1 ≤ (d + 1 : ℕ) :=
    h1 ▸ topologicalKrullDim_add_one_le isClosed_closure isClosed_univ
      fun x _ => ⟨genericPoint B, trivial, hgen, genericPoint_specializes x⟩
  by_contra h
  have := (add_le_add_left (not_lt.1 h) 1).trans hup
  norm_cast at this
  omega

theorem interNum_eq_zero_of_ne [IsIntegral Y] {f : Y ⟶ B} {G : Scheme.{0}} {j : G ⟶ Y} {s : G ⟶ Sp B.functionField}
    (h : IsPullback j s f (B.fromSpecStalk (genericPoint B))) (hf : f (genericPoint Y) ≠ genericPoint B)
    {ι : Type} [Fintype ι] {P : ι → LB G} (hP : ∀ i, (P i).IsLB) :
    (letI := algebraΓOfHom s; interNum B.functionField (structureModule G) P) = 0 := by
  obtain ⟨-, h₂, -, h₄⟩ := GlobalTheory.T.generic_fibre_preimmersion_integral B Y f G j s h
  have : IsEmpty G := not_nonempty_iff.1 fun hG => by
    obtain ⟨_, e⟩ := h₄ hG
    exact hf (h₂.le ⟨_, e⟩)
  letI := algebraΓOfHom s
  exact interNum_eq_zero_of_isZero _ (InterModel.isZero_of_isEmpty _) hP

theorem ne_genericPoint_of_vertical (hB : IsArithVar q d) {Z : Scheme.{0}} (g : Z ⟶ B) (l : ℕ) [Fact l.Prime]
    [Algebra (ZMod l) Γ(Z, ⊤)] (z : Z) : g z ≠ genericPoint B := fun e => by
  have := hB.charZero
  have h₁ : genericPoint B ∈ B.basicOpen (l : Γ(B, ⊤)) :=
    (unitAt_fnOf_iff (Opens.mem_top _) (Opens.mem_top _) _).1 (unitAt_genericPoint
      ((map_ne_zero_iff _ (fnOf_injective ⊤ (Opens.mem_top _))).2 (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)))
  have h₂ : z ∈ g ⁻¹ᵁ B.basicOpen (l : Γ(B, ⊤)) := show g z ∈ _ from e ▸ h₁
  rw [Scheme.preimage_basicOpen_top, map_natCast, ← map_natCast (algebraMap (ZMod l) Γ(Z, ⊤)), ZMod.natCast_self, map_zero,
    Scheme.basicOpen_zero] at h₂
  exact h₂

theorem isProper_of_isArithVar {D : ℕ} (h : IsArithVar p D) : IsProper p := by
  obtain ⟨N, j, _, hj⟩ := h.isProjOver
  have := isProper_str k N
  exact hj ▸ inferInstance

theorem isArFun_pull (H : ArCalc) [IsIntegral Y] (hB : IsArithVar q d) (hY : IsArithVar p d) (f : Y ⟶ B) (w : f ≫ q = p)
    {G : Scheme.{0}} {j : G ⟶ Y} {s : G ⟶ Sp B.functionField}
    (h : IsPullback j s f (B.fromSpecStalk (genericPoint B))) {κ : Type} [Fintype κ] {A : κ → HermLB q}
    {Φ : MvPolynomial κ ℝ →ₗ[ℝ] ℝ} (hΦ : IsArFun A d Φ) {ι : Type} [Fintype ι] [IsEmpty ι] (P : ι → LB G) :
    IsArFun (fun a => (A a).pull f w) d
      (((letI := algebraΓOfHom s; interNum B.functionField (structureModule G) P : ℤ) : ℝ) • Φ) := by
  by_cases hf : f (genericPoint Y) = genericPoint B
  · obtain ⟨-, h₂, -, -⟩ := GlobalTheory.T.generic_fibre_preimmersion_integral B Y f G j s h
    obtain ⟨x, -⟩ : genericPoint Y ∈ Set.range j := h₂.ge hf
    have := isProper_of_isArithVar hB
    have : IsProper (f ≫ q) := w ▸ isProper_of_isArithVar hY
    have : IsProper f := IsProper.of_comp f q
    obtain ⟨h₃, h₄⟩ := GlobalTheory.T.residue_degree_eq_euler_characteristic B Y f G j s h (GlobalTheory.T.generic_fibre_projective k B Y q p hB.isProjOver hY.isProjOver f w G j s h)
      (GlobalTheory.T.generic_fibre_dimension_le B Y (d + 1) 0 hB.dim_eq hY.dim_eq.le f G j s h) ⟨x⟩
    letI := algebraΓOfHom s
    rw [interNum_of_isEmpty, h₄]
    exact (H.arProj k B Y q p d hB hY f w hf h₃).2 κ A Φ hΦ
  · rw [interNum_eq_zero_of_ne h hf isEmptyElim, Int.cast_zero, zero_smul]
    refine ⟨fun n => ?_, fun _ _ _ _ => rfl⟩
    obtain ⟨t, ht, e⟩ := ProjDrop.isSelfInter_zero_of_dim_lt H k B Y q p d d hB hY f w (dim_closure_lt hB hf) (comb A n)
    exact ⟨t, (H.arIso k Y p d hY).1 _ _ t (isometric_comb_pull A n f w).symm ht, e⟩

omit [IsIntegral B] in

theorem isometric_pull_pull {Z : Scheme.{0}} (L : HermLB q) (f : Y ⟶ B) (w : f ≫ q = p) (i : Z ⟶ Y)
    (h : (i ≫ f) ≫ q = i ≫ p) : ((L.pull f w).pull i rfl).Isometric (L.pull (i ≫ f) h) :=
  have R := L.refines_pull_pull f w i rfl h
  HermLB.isometric_of_chart _ R.le (fun x => R.g Z (𝟙 Z) x) fun σ c y hy => ((R.φ σ c y hy).trans (add_zero _)).symm

theorem pol_vertical {D e : ℕ} (hB : IsArithVar q d) (hY : IsArithVar p D) (hD : e + (d + 1) = D) (f : Y ⟶ B) (w : f ≫ q = p)
    (L : Fin e → HermLB p) (A : Fin (d + 1) → HermLB q) {h : (Fin e ⊕ Fin (d + 1) → ℤ) → Y → ℝ}
    (hh : ∀ n, (comb (Sum.elim L fun a => (A a).pull f w) n).IsArithHeight (h n)) {Z : Scheme.{0}} (i : Z ⟶ Y)
    [IsClosedImmersion i] [IsIntegral Z] (hZ : topologicalKrullDim Z = D) (l : ℕ) [Fact l.Prime]
    [Algebra (ZMod l) Γ(Z, ⊤)] : pol (fun n => h n (i (genericPoint Z))) = 0 := by
  have hp : IsProjOver (strHom (ZMod l) Z) := GlobalTheory.T.closed_subscheme_mod_l_projective k Y p D hY Z i l
  have h₁ := GlobalTheory.T.intersection_number_zero_small_image (ZMod l) e (d + 1) Z B hp (hD ▸ hZ.le) (i ≫ f)
    (dim_closure_lt hB (ne_genericPoint_of_vertical hB _ l _)) (fun a => (L a).B.pull i)
    (fun a => LB.isLB_pull (L a).isLB i) (fun a => (A a).B) fun a => (A a).isLB
  have h₂ : interNum (ZMod l) (structureModule Z)
      (fun a => ((Sum.elim L fun a => (A a).pull f w) a).B.pull i) = 0 := by
    refine (interNum_congr_lbIso _ _ (fun a => LB.isLB_pull (HermLB.isLB _) i) ?_ ?_).trans h₁
    · rintro (a | a)
      · exact LB.isLB_pull (L a).isLB i
      · exact LB.isLB_pull (A a).isLB _
    · rintro (a | a)
      · exact (CechPic.cls_eq_iff (LB.isLB_pull (L a).isLB i) (LB.isLB_pull (L a).isLB i)).1 rfl
      · exact ((A a).refines_pull_pull f w i rfl (by rw [Category.assoc, w])).lbIso
  simp only [fun n => (hh n).vertical Z i (ZMod l) D hZ]
  rw [pol_mul_const, GlobalTheory.T.polynomial_top_self_intersection k Y p (ZMod l) Z hp _ D (by simpa using hD) hZ.le i, h₂]
  simp

theorem arFun_prod (H : ArCalc) (hB : IsArithVar q d) (hs : GenSmooth q d) {A : Fin (d + 1) → HermLB q}
    {Φ : MvPolynomial (Fin (d + 1)) ℝ →ₗ[ℝ] ℝ} (hΦ : IsArFun A d Φ) (e : ℕ) :
    ∀ (Y : Scheme.{0}) [IsIntegral Y] (p : Y ⟶ Sp k), IsArithVar p (d + e) → ∀ (f : Y ⟶ B) (w : f ≫ q = p)
      (G : Scheme.{0}) (j : G ⟶ Y) (s : G ⟶ Sp B.functionField), IsPullback j s f (B.fromSpecStalk (genericPoint B)) →
      ∀ (L : Fin e → HermLB p) (Ψ : MvPolynomial (Fin e ⊕ Fin (d + 1)) ℝ →ₗ[ℝ] ℝ),
        IsArFun (Sum.elim L fun a => (A a).pull f w) (d + e) Ψ → Ψ (∏ o, X o) =
          (letI := algebraΓOfHom s; (interNum B.functionField (structureModule G) (fun i => (L i).B.pull j) : ℝ)) *
            Φ (∏ a, X a) := by
  induction e with
  | zero =>
    intro Y _ p hY f w G j s h L Ψ hΨ
    have e := DFunLike.congr_fun (VertForm.FormEx.arFun_eq_rename H hY
      (isArFun_pull H hB hY f w h hΦ fun i => (L i).B.pull j) hΨ Sum.inr fun _ => rfl) (∏ a, X a)
    simpa [Fintype.prod_sum_type] using e.symm
  | succ e ih =>
    intro Y _ p hY f w G j s hG L Ψ hΨ
    have := hY.isNoetherian
    let N : Fin e ⊕ Fin (d + 1) → HermLB p := Sum.elim (fun a => L a.succ) fun a => (A a).pull f w
    have hc : Fintype.card (Fin e ⊕ Fin (d + 1)) = d + (e + 1) := by simp; omega
    obtain ⟨Φ', hΦ'⟩ := ((H.arExists k Y p _ hY).2 _ fun o : Option _ => o.elim (L 0) N).1
    choose h hh using fun n => (H.arExists k Y p _ hY).1 (comb N n)
    obtain ⟨r, hr⟩ := exists_isRatSec (L 0).isLB
    have hm := fun n => H.arMix k Y p _ hY _ (L 0) N Φ' hΦ' n (h n) (hh n) r hr
    have ha := GlobalTheory.T.arch_integrable_polynomial_vanishing k B Y q p d _ hs hY f w _ _ (by simp) (fun a : Fin e => L a.succ) A (L 0) r hr fun n => (hm n).1
    have key (z : Y) : ∃ c : ℤ, ((L 0).div hr).mult z ≠ 0 →
        pol (fun n => h n z) = (d + (e + 1)).factorial * (c * Φ (∏ a, X a)) ∧
        ∃ (Z : Scheme.{0}) (i : Z ⟶ Y) (_ : IsClosedImmersion i) (_ : IsIntegral Z) (G' : Scheme.{0}) (j' : G' ⟶ Z)
          (s' : G' ⟶ Sp B.functionField), i (genericPoint Z) = z ∧
          IsPullback j' s' (i ≫ f) (B.fromSpecStalk (genericPoint B)) ∧
          c = (letI := algebraΓOfHom s'; interNum B.functionField (structureModule G')
            (fun a : Fin e => ((L a.succ).B.pull i).pull j')) := by
      obtain ⟨Z, i, _, _, rfl⟩ := exists_isClosedImmersion_genericPoint z
      have hP := IsPullback.of_hasPullback (i ≫ f) (B.fromSpecStalk (genericPoint B))
      refine ⟨_, fun hz => ⟨?_, Z, i, ‹_›, ‹_›, _, _, _, rfl, hP, rfl⟩⟩
      have hZ := GlobalTheory.T.codim_one_integral_subscheme_dim k Y p _ hY Z i (CartierDiv.coheight_eq_one_of_mult_ne_zero hz)
      rcases hY.vertical_or_horizontal i with ⟨l, _, ⟨_⟩⟩ | ⟨hc0, -⟩
      · rw [pol_vertical hB hY (by omega) f w _ A hh i hZ l, interNum_eq_zero_of_ne hP
          (ne_genericPoint_of_vertical hB _ l _) fun a : Fin e => LB.isLB_pull (LB.isLB_pull (L a.succ).isLB i) _]
        simp
      · have hZ' : IsArithVar (i ≫ p) (d + e) := hY.of_isClosedImmersion i hc0 hZ
        have w' : (i ≫ f) ≫ q = i ≫ p := by rw [Category.assoc, w]
        obtain ⟨Ψ', hΨ'⟩ := ((H.arExists k Z _ _ hZ').2 _ fun o => (N o).pull i rfl).1
        have e₁ (n) : h n (i (genericPoint Z)) = Ψ' (lin (fun o => (n o : ℝ)) ^ (d + (e + 1))) := by
          obtain ⟨t, ht, e₂⟩ := hΨ'.1 n
          exact ((hh n).isSelfInter_restrict hY i rfl).unique hZ'
            ⟨t, (H.arIso k Z _ _ hZ').1 _ _ t (isometric_comb_pull N n i rfl) ht, e₂⟩
        have hΨ'' := ((H.arIso k Z _ _ hZ').2 _ _ Ψ' hΨ').2.1
          (Sum.elim (fun a : Fin e => (L a.succ).pull i rfl) fun a => (A a).pull (i ≫ f) w') (by
            rintro (a | a)
            · exact .refl _
            · exact isometric_pull_pull _ f w i w')
        simp only [e₁]
        rw [pol_lin_pow Ψ' hc, ih Z _ hZ' _ w' _ _ _ hP _ Ψ' hΨ'']
        rfl
    choose γ hγ using key
    have hg := GlobalTheory.T.generic_fibre_intersection_formula k B Y q p d e hB hY f w G j s hG (fun a => (L a).B) (fun a => (L a).isLB) r hr γ
      fun z hz => (hγ z hz).2
    have hT := ((L 0).div hr).finite_support_mult
    have e₃ (u : Y → ℝ) : ∑ᶠ z, (((L 0).div hr).mult z : ℝ) * u z =
        ∑ z ∈ hT.toFinset, (((L 0).div hr).mult z : ℝ) * u z :=
      finsum_eq_sum_of_support_subset _ fun z hz => by
        simpa using left_ne_zero_of_mul hz
    have e₄ : ∑ᶠ z, ((L 0).div hr).mult z * γ z = ∑ z ∈ hT.toFinset, ((L 0).div hr).mult z * γ z :=
      finsum_eq_sum_of_support_subset _ fun z hz => by
        simpa using left_ne_zero_of_mul hz
    have e₅ := pol_mix Φ' hc
    simp only [fun n => (hm n).2, e₃] at e₅
    rw [pol_sub, ha, sub_zero, pol_sum, Finset.sum_congr rfl fun z hz => by
      rw [pol_const_mul, (hγ z (by simpa using hz)).1]] at e₅
    have e₆ := DFunLike.congr_fun (VertForm.FormEx.arFun_eq_rename H hY hΦ' hΨ
      (fun o => o.elim (.inl 0) (Sum.map Fin.succ id)) (by rintro (_ | a | a) <;> rfl)) (∏ o, X o)
    have e₇ : Φ' (∏ o, X o) = Ψ (∏ o, X o) := by
      simpa [Fintype.prod_option, Fintype.prod_sum_type, Fin.prod_univ_succ, mul_assoc] using e₆
    rw [hg, e₄, ← e₇]
    refine mul_left_cancel₀ (a := ((d + (e + 1)).factorial : ℝ)) (by positivity) (e₅.symm.trans ?_)
    push_cast
    rw [Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun z _ => by ring

theorem exists_monomial_eq_prod {κ : Type} (n : ℕ) (m : κ →₀ ℕ) (hm : m.degree = n) :
    ∃ r : Fin n → κ, (monomial m 1 : MvPolynomial κ ℝ) = ∏ a, X (r a) := by
  subst hm
  have hl : m.toMultiset.toList.length = m.degree := by
    rw [Multiset.length_toList, Finsupp.card_toMultiset]
    rfl
  refine ⟨fun a => m.toMultiset.toList.get (a.cast hl.symm), ?_⟩
  refine Eq.trans ?_ ((finCongr hl.symm).prod_comp (fun a => (X (m.toMultiset.toList.get a) : MvPolynomial κ ℝ)) |>.trans
    (Fin.prod_univ_fun_getElem m.toMultiset.toList fun a => (X a : MvPolynomial κ ℝ))).symm
  rw [Multiset.prod_map_toList, ← prod_X_pow_eq_monomial, Finsupp.toMultiset_map, Finsupp.prod_toMultiset,
    Finsupp.prod_mapDomain_index (by simp) (by simp [pow_add])]
  rfl

open scoped Classical in

theorem arFun_mul_pull : ArCalc → ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d e : ℕ), IsArithVar q d → (∀ b : B, IsRegularLocalRing (B.presheaf.stalk b)) → IsArithVar p (d + e) → ∀ (f : Y ⟶ B) (w : f ≫ q = p) (G : Scheme.{0}) (j : G ⟶ Y) (s : G ⟶ Sp B.functionField), IsPullback j s f (B.fromSpecStalk (genericPoint B)) → ∀ (L : Fin e → HermLB p) (κ : Type) [Fintype κ] (A : κ → HermLB q) (Φ : MvPolynomial κ ℝ →ₗ[ℝ] ℝ) (Ψ : MvPolynomial (Fin e ⊕ κ) ℝ →ₗ[ℝ] ℝ), IsArFun A d Φ → IsArFun (Sum.elim L fun a => (A a).pull f w) (d + e) Ψ → ∀ P : MvPolynomial κ ℝ, P.IsHomogeneous (d + 1) → Ψ ((∏ i : Fin e, MvPolynomial.X (Sum.inl i)) * rename Sum.inr P) = (letI := algebraΓOfHom s; (interNum B.functionField (structureModule G) (fun i => (L i).B.pull j) : ℝ)) * Φ P := by
  intro H k _ B Y _ _ q p d e hB hr hY f w G j s hG L κ _ A Φ Ψ hΦ hΨ P hP
  rw [P.as_sum]
  simp only [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  obtain ⟨r, e₀⟩ := exists_monomial_eq_prod (d + 1) m (by
    rw [Finsupp.degree_eq_weight_one]
    exact hP (mem_support_iff.1 hm))
  obtain ⟨Φ', hΦ'⟩ := ((H.arExists k B q d hB).2 _ fun a => A (r a)).1
  obtain ⟨Ψ', hΨ'⟩ := ((H.arExists k Y p _ hY).2 _ (Sum.elim L fun a => (A (r a)).pull f w)).1
  have e₁ := arFun_prod H hB (RegGenSmooth.genSmooth hB hr) hΦ' e Y p hY f w G j s hG L Ψ' hΨ'
  rw [VertForm.FormEx.arFun_eq_rename H hB hΦ' hΦ r fun _ => rfl,
    VertForm.FormEx.arFun_eq_rename H hY hΨ' hΨ (Sum.map id r) (by rintro (a | a) <;> rfl)] at e₁
  rw [show monomial m (coeff m P) = coeff m P • monomial m 1 by rw [smul_monomial, smul_eq_mul, mul_one], e₀, map_smul, mul_smul_comm, map_smul, map_smul, smul_eq_mul,
    smul_eq_mul, mul_left_comm]
  congr 1
  simpa [Fintype.prod_sum_type] using e₁

end GlobalTheory.FibreProj
