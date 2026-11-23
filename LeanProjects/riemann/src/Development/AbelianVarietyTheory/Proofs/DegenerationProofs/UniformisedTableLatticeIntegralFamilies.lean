import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFrameIff
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FromGtOfMemUnitGrp
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IntegralFamilyValuesTorsionTorusExtensionStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusExtensionTorsionMemUnitThetaConstantGroupStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorsionPointUnitValuePrimitiveIntegralFamiStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpBijFAndExpandsFLin
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTorsionIdentificationWithPairingStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaConstantValuationsUnitsEveryCosetStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValuationNonnegIffSpanMultiplicationTranslatesStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.BOfNsmulLeft

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis

noncomputable section
namespace GlobalTheory.OneBasis.UnifLoc

section Lin
variable {R : Type} [CommRing R] [IsDomain R] {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {F : Type} [Field F] [Algebra (FractionRing R) F] {k : ℕ}

def cHom (W : (TFK (R := R) F ⊗ A.A).left.Opens) : F →+* Γ((TFK (R := R) F ⊗ A.A).left, W) :=
  ((TFK (R := R) F ⊗ A.A).left.presheaf.map (homOfLE le_top).op).hom.comp
    ((fst (TFK (R := R) F) A.A).left.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom)

theorem cmb_iff {n : ℕ} (b : Fin n → SecA A F k) (a : Fin n → F) (t : SecA A F k) :
    Cmb b a t ↔ ∀ j, t.f j = ∑ i, cHom _ (a i) * (b i).f j := Iff.rfl

theorem sec_ext (a b : SecA A F k) (h : ∀ j, a.f j = b.f j) : a = b := by
  obtain ⟨a, _⟩ := a
  obtain ⟨b, _⟩ := b
  obtain rfl : a = b := funext h
  rfl

theorem cHom_res {W W' : (TFK (R := R) F ⊗ A.A).left.Opens} (h : W' ≤ W) (a : F) :
    ((TFK (R := R) F ⊗ A.A).left.presheaf.map (homOfLE h).op).hom (cHom W a) = cHom W' a := by
  have e := congrArg (fun q => q.hom ((fst (TFK (R := R) F) A.A).left.appTop.hom
    ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom a)))
    ((TFK (R := R) F ⊗ A.A).left.presheaf.map_comp (homOfLE (le_top (a := W))).op (homOfLE h).op)
  exact e.symm

theorem exists_cmb {n : ℕ} (b : Fin n → SecA A F k) (a : Fin n → F) : ∃ t, Cmb b a t := by
  refine ⟨⟨fun j => ∑ i, cHom _ (a i) * (b i).f j, fun j j' => ?_⟩, fun j => rfl⟩
  rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, map_mul, cHom_res, cHom_res, (b i).compat j j']
  ring

theorem sum_comp {Γ : Type} [CommRing Γ] (c : F →+* Γ) {n n' : ℕ} (a : Fin n → F) (B : Fin n → Fin n' → F)
    (b : Fin n → Γ) (τ : Fin n' → Γ) (h : ∀ i, b i = ∑ i', c (B i i') * τ i') :
    ∑ i, c (a i) * b i = ∑ i', c (∑ i, a i * B i i') * τ i' := by
  simp only [h, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [_root_.mul_assoc]

theorem cmb_comp {n n' : ℕ} {τ : Fin n' → SecA A F k} {b : Fin n → SecA A F k} {B : Matrix (Fin n) (Fin n') F}
    (hB : ∀ i, Cmb τ (B i) (b i)) {a : Fin n → F} {t : SecA A F k} (h : Cmb b a t) : Cmb τ (Matrix.vecMul a B) t := by
  rw [cmb_iff] at h ⊢
  intro j
  have hB' : ∀ i, (b i).f j = ∑ i', cHom _ (B i i') * (τ i').f j := fun i => hB i j
  rw [h j]
  exact sum_comp _ a B (fun i => (b i).f j) (fun i => (τ i).f j) hB'

theorem valAt_cmb {n : ℕ} {τ : Fin n → SecA A F k} {a l : Fin n → F} {t : SecA A F k} (h : Cmb τ a t)
    {x : TFK (R := R) F ⟶ A.A} {e} (hl : ∀ j, ValAt (τ j) x e (l j)) : ValAt t x e (a ⬝ᵥ l) := by
  intro z J hJ
  have hz := hJ.mem (fun _ : Fin 1 => (snd (TFK (R := R) F) A.A).left) (ptSecT A.A x).left
  let W := LB.wchart A.L (fun _ : Fin 1 => (snd (TFK (R := R) F) A.A).left)
    (fun _ => J ((ptSecT A.A x).left ≫ (snd (TFK (R := R) F) A.A).left))
  let g : Γ((TFK (R := R) F ⊗ A.A).left, W) →+* (TFK (R := R) F).left.presheaf.stalk z :=
    ((TFK (R := R) F).left.presheaf.germ ((ptSecT A.A x).left ⁻¹ᵁ W) z hz).hom.comp ((ptSecT A.A x).left.app W).hom
  have hg : ∀ s : SecA A F k, sA s (ptSecT A.A x).left z J = g (s.f _) := fun s => gs_eq _ _ _ hz _
  let c : F →+* (TFK (R := R) F).left.presheaf.stalk z := g.comp (cHom _)
  have hc : ∀ a, @id ((TFK (R := R) F).left.presheaf.stalk z) (cst (R := R) F z a) = c a := fun a => by
    have e : (ptSecT A.A x).left ≫ (fst (TFK (R := R) F) A.A).left = 𝟙 _ := by
      rw [← Over.comp_left, ptSecT, lift_fst]; rfl
    have h1 := (gs_res (ptSecT A.A x).left z le_top hz _).trans
      (gs_pull (ptSecT A.A x).left (fst (TFK (R := R) F) A.A).left z ⊤ trivial
        ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom a))
    rw [e, gs_eq _ _ _ hz] at h1
    exact h1.symm
  refine (hg t).trans ((congrArg g (h _)).trans ((map_sum g _ _).trans ?_))
  rw [hc, dotProduct, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => (map_mul g _ _).trans ?_
  have e := (hg (τ i)).symm.trans (hl i z J hJ)
  rw [hc] at e
  rw [map_mul, _root_.mul_assoc, ← e]
  rfl

theorem rel_cmb {E : Type} [AddCommGroup E] [Module F E] {X : SecA A F k → E → Prop} (hX : ∀ t, ∃ s, X t s)
    (hlin : ∀ (t t' t'' : SecA A F k) s s' (c : F), X t s → X t' s' →
      (∀ j, t''.f j = cHom _ c * t.f j + t'.f j) → X t'' (c • s + s')) :
    ∀ {n : ℕ} (b : Fin n → SecA A F k) (s : Fin n → E) (a : Fin n → F) (t : SecA A F k), (∀ i, X (b i) (s i)) →
      Cmb b a t → X t (∑ i, a i • s i) := by
  intro n
  induction n with
  | zero =>
    intro b s a t _ h
    obtain ⟨s₀, h₀⟩ := hX t
    have := hlin t t t s₀ s₀ (-1) h₀ h₀ fun j => by rw [(cmb_iff _ _ _).1 h j]; simp
    simpa using this
  | succ n ih =>
    intro b s a t hb h
    obtain ⟨t', ht'⟩ := exists_cmb (fun i : Fin n => b i.succ) (fun i => a i.succ)
    rw [Fin.sum_univ_succ]
    refine hlin _ _ _ _ _ _ (hb 0) (ih _ _ _ _ (fun i => hb i.succ) ht') fun j => ?_
    rw [(cmb_iff _ _ _).1 h j, (cmb_iff _ _ _).1 ht' j, Fin.sum_univ_succ]
end Lin

theorem valuation_eq_of {F : Type} [Field F] {v : AddValuation F (WithTop ℚ)} {O : ValuationSubring F}
    (h : ∀ x, x ∈ O ↔ 0 ≤ v x) {x y : F} (e : v x = v y) : O.valuation x = O.valuation y := by
  have e' : O = (AddValuation.toValuation v).valuationSubring := ValuationSubring.ext _ _ h
  subst e'
  refine (Valuation.isEquiv_valuation_valuationSubring (AddValuation.toValuation v)).val_eq.1 ?_
  exact congrArg (fun a => Multiplicative.ofAdd (OrderDual.toDual a)) e

theorem v_prod {F : Type} [Field F] (v : AddValuation F (WithTop ℚ)) {K : Type} (S : Finset K) (π : K → F) (q : K → ℚ)
    (h : ∀ i, v (π i) = (q i : WithTop ℚ)) : v (∏ i ∈ S, π i) = ((∑ i ∈ S, q i : ℚ) : WithTop ℚ) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert i S hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, v.map_mul, ih, h, WithTop.coe_add]

theorem div_mem_iff {F : Type} [Field F] (v : AddValuation F (WithTop ℚ)) {a π : F} {q : ℚ} (h0 : π ≠ 0)
    (h : v π = (q : WithTop ℚ)) : 0 ≤ v (a / π) ↔ (q : WithTop ℚ) ≤ v a := by
  have e : v a = v (a / π) + q := by rw [← h, ← v.map_mul, div_mul_cancel₀ _ h0]
  rw [e]
  induction v (a / π) using WithTop.recTopCoe with
  | top => simp
  | coe y =>
    rw [← WithTop.coe_add, WithTop.coe_le_coe, ← WithTop.coe_zero, WithTop.coe_le_coe]
    constructor <;> intro <;> linarith

theorem main : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ w₀ ρ, NormW U.toUnifPre w₀ ρ → ∀ (th : SecA A F 1) (ϑ : Fam D.toPre F 1), U.ExpandsF F 1 w₀ th ϑ → Prim D Q v ϑ → ∀ m n : ℕ, Odd m → IsUnit (m : V) → 3 ≤ m → n.Prime → Odd n → IsUnit (n : V) → ∀ O : ValuationSubring F, (∀ x, x ∈ O ↔ 0 ≤ v x) → ∀ (r : ℕ) (cls : Fin r → D.toPre.X) (b τ : Fin r → SecA A F (m ^ 2)) (s : Fin r → Fam D.toPre F (m ^ 2)) (B : Matrix (Fin r) (Fin r) F), Norms D Q v (m ^ 2) cls s → (∀ i, U.ExpandsF F (m ^ 2) w₀ (b i) (s i)) → (∀ t, ∃! a, Cmb τ a t) → (∀ i, Cmb τ (B i) (b i)) → ∀ (d : ℕ) (κ : F), v κ = (((d : ℚ) * (∑ i, (Q (cls i) : ℚ)) / (m ^ 2 : ℕ) : ℚ) : WithTop ℚ) → (tab ρ m th τ).Loc O B n d κ := by
  intro hL h₁ h₂ h₃ h₄ V _ _ _ _ hc ϖ hϖ D Q hQ F _ _ _ v hv A G _ _ hG U w₀ ρ hN th ϑ hE hP m n hm hmu hm3 hn hno hnu
    O hO r cls b τ s B hs hb hτ hB d κ hκ
  classical
  have hA : AdmBase V (maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hc⟩
  have hm1 : 1 ≤ m ^ 2 := Nat.one_le_pow _ _ hm.pos
  have hQ0 : ∀ χ, 0 ≤ Q χ := fun χ => by
    by_cases h : χ = 0
    · rw [h, QForm.Q_zero hϖ D hQ]
    · have := QForm.Q_pos hϖ D hQ h; omega
  obtain ⟨hbij, hlin⟩ := expBijF_and_expandsF_lin hL V _ hA D A G hG U
  obtain ⟨b₁, b₂⟩ := hbij F (m ^ 2) hm1 w₀ hN.1
  have hcb : ∀ a t, Cmb b a t → U.ExpandsF F (m ^ 2) w₀ t (∑ i, a i • s i) := fun a t h =>
    rel_cmb (X := U.ExpandsF F (m ^ 2) w₀) (fun t => (b₁ t).exists)
      (fun t t' t'' s s' c h h' e => hlin F _ w₀ t t' t'' s s' c h h' e) b s a t hb h
  have key : ∀ a t, Cmb τ (Matrix.vecMul a B) t → U.ExpandsF F (m ^ 2) w₀ t (∑ i, a i • s i) := fun a t h => by
    obtain ⟨t', ht'⟩ := exists_cmb b a
    obtain rfl : t = t' := sec_ext _ _ fun j => (h j).trans (cmb_comp hB ht' j).symm
    exact hcb a _ ht'
  have hinj : ∀ a a' : Fin r → F, ∑ i, a i • s i = ∑ i, a' i • s i → a = a' := fun a a' h =>
    (hs.1 (∑ i, a i • s i)).unique rfl h
  have hdet : B.det ≠ 0 := fun h => by
    obtain ⟨a, ha0, ha⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h
    obtain ⟨t, ht⟩ := exists_cmb τ (0 : Fin r → F)
    exact ha0 (hinj _ _ ((b₁ t).unique (key a t (ha ▸ ht)) (key 0 t ((Matrix.zero_vecMul B).symm ▸ ht))))
  have hBB : ∀ e : Fin r → F, Matrix.vecMul (Matrix.vecMul e B⁻¹) B = e := fun e => by
    rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ (Ne.isUnit hdet), Matrix.vecMul_one]
  have hBB' : ∀ e : Fin r → F, Matrix.vecMul (Matrix.vecMul e B) B⁻¹ = e := fun e => by
    rw [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ (Ne.isUnit hdet), Matrix.vecMul_one]
  have hHs : ∀ k, (tab ρ m th τ).Hs O k = unitGrp v ρ th k := fun k => by
    refine congrArg Subgroup.closure (Set.ext fun y => ⟨?_, ?_⟩)
    · rintro ⟨x, c, ⟨hx, t, ht⟩, hc, rfl⟩
      exact ⟨x, t, c, hx, ht, (valuation_eq_one_iff hO c).1 hc, rfl⟩
    · rintro ⟨x, t, c, hx, ht, hc, rfl⟩
      exact ⟨x, c, ⟨hx, t, ht⟩, (valuation_eq_one_iff hO c).2 hc, rfl⟩
  have hnj : ∀ j, IsUnit ((n ^ j : ℕ) : V) := fun j => by rw [Nat.cast_pow]; exact hnu.pow j
  refine ⟨hdet, ?_, ?_, ?_, ?_⟩
  · rintro j x c ⟨hx, t, ht⟩
    obtain ⟨f, f₁, f₂, -⟩ := GlobalTheory.T.uniformisation_torsion_identification_with_pairing hL V _ hA D A G hG U F ((n ^ j) ^ 2) (pow_pos (pow_pos hn.pos j) 2)
    obtain ⟨p, rfl⟩ := f₂ x hx
    have ua := (GlobalTheory.T.theta_constant_valuations_units_every_coset hL h₁ h₂ h₃ h₄ V hc ϖ hϖ D Q hQ F v hv A G hG U w₀ ρ hN th ϑ hE hP (n ^ j) hno.pow
      (hnj j)).1 p _ t c ((f₁ p _).2 rfl) ht
    exact (hO c).2 (ua.1 0 fun χ => div_nonneg (by exact_mod_cast hQ0 _) (Nat.cast_nonneg _))
  · rintro j h l hh ⟨e, he, hl⟩ i
    rw [hHs] at hh
    have hf := UnitGrp.fromGt_of_mem_unitGrp hL h₁ h₂ h₃ h₄ V hc ϖ hϖ D Q hQ F v hv A G hG U w₀ ρ hN th ϑ hE hP (n ^ j)
      hno.pow (hnj j) h hh
    have hi : IntGe D v (s i) 0 := by
      have := ((hs.2 (Pi.single i 1) 0).2.1).2 fun i' => by
        by_cases h' : i' = i
        · subst h'; simp
        · simp [Pi.single_eq_of_ne h']
      rwa [Finset.sum_eq_single i (fun i' _ h' => by rw [Pi.single_eq_of_ne h', zero_smul]) (by simp),
        Pi.single_eq_same, one_smul] at this
    exact (hO _).2 (GlobalTheory.T.integral_family_values_torsion_torusExtension hL h₁ h₂ h₃ h₄ V hc ϖ hϖ D Q hQ F v hv A G hG U w₀ ρ hN (n ^ j) (m ^ 2)
      (pow_pos hn.pos j) hm1 h e (b i) (s i) _ hf he (hb i) hi (valAt_cmb (hB i) hl))
  · rintro a ha ⟨i, hi⟩
    obtain ⟨t, ht⟩ := exists_cmb b a
    obtain ⟨j, x, hj, hx, hval⟩ := GlobalTheory.T.exists_torsionPoint_unit_value_primitive_integral_family hL h₁ h₂ h₃ h₄ V hc ϖ hϖ D Q hQ F v hv A G hG U w₀ ρ hN (m ^ 2) n
      (by nlinarith) hn hnu t _ (cls i) (hcb a t ht) (((hs.2 a 0).2.1).2 fun i' => (hO _).1 (ha i'))
      fun q hq hV => by
        have := (hs.2 a q).2.2 i hV
        rw [(valuation_eq_one_iff hO _).1 hi, ← WithTop.coe_zero, WithTop.coe_le_coe] at this
        exact absurd this (not_le.2 hq)
    refine ⟨j, x, ?_, ?_⟩
    · rw [hHs]
      exact GlobalTheory.T.torusExtension_torsion_mem_unitThetaConstantGroup hL h₁ h₂ h₃ h₄ V hc ϖ hϖ D Q hQ F v hv A G hG U w₀ ρ hN th ϑ hE hP n j hn hno hnu hj x hx
    · rintro l ⟨e, he, hl⟩
      rw [valuation_eq_one_iff hO, Matrix.dotProduct_mulVec]
      exact hval e _ he (valAt_cmb (cmb_comp hB ht) hl)
  · have hπ : ∀ i, ∃ π : F, π ≠ 0 ∧ v π = (((Q (cls i) : ℚ) / (m ^ 2 : ℕ) : ℚ) : WithTop ℚ) := fun i => by
      have h0 : (0 : ℚ) ≤ (Q (cls i) : ℚ) / (m ^ 2 : ℕ) := div_nonneg (by exact_mod_cast hQ0 _) (Nat.cast_nonneg _)
      rcases h0.eq_or_lt with h | h
      · exact ⟨1, one_ne_zero, by rw [← h]; simp⟩
      · exact exists_val_eq hv h
    choose π hπ0 hπ using hπ
    have u01 := GlobalTheory.T.valuation_nonneg_iff_span_multiplicationTranslates hL h₁ h₂ h₃ h₄ V hc ϖ hϖ D Q hQ F v hv A G hG U w₀ ρ hN th ϑ hE hP m hm hmu hm3
    have hnu : ∀ a : Fin r → F, (∀ i, a i / π i ∈ O) ↔ NuGe D Q F v (m ^ 2) (∑ i, a i • s i) 0 := fun a => by
      rw [(hs.2 a 0).1]
      exact forall_congr' fun i => by rw [hO, div_mem_iff v (hπ0 i) (hπ i), zero_add]
    refine ⟨π, hπ0, valuation_eq_of hO ?_, fun a => ⟨fun h => ?_, fun h => ?_⟩⟩
    · rw [v.map_pow, v_prod v _ _ _ hπ, hκ, ← WithTop.coe_nsmul, nsmul_eq_mul, mul_div_assoc,
        Finset.sum_div]
    · obtain ⟨N, c, x, t, c', ρ', h', e⟩ := (u01 _).1 ((hnu a).1 h)
      choose ε hε using fun i => (hτ (t i)).exists
      have hρ : ∀ i, ρ' i = ∑ j, Matrix.vecMul (ε i) B⁻¹ j • s j := fun i =>
        (b₁ (t i)).unique (h' i).2.2.2 (key _ _ ((hBB (ε i)).symm ▸ hε i))
      have ea : a = ∑ i, c i • Matrix.vecMul (ε i) B⁻¹ := hinj _ _ (by
        rw [e]
        simp only [hρ, Finset.smul_sum, Finset.sum_apply, Finset.sum_smul, Pi.smul_apply, smul_eq_mul, mul_smul]
        exact Finset.sum_comm)
      rw [ea, Matrix.sum_vecMul]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [Matrix.smul_vecMul, hBB]
      exact Submodule.smul_mem _ (⟨c i, (hO _).2 (h' i).1⟩ : O)
        (Submodule.subset_span ⟨x i, (h' i).2.1, t i, c' i, (h' i).2.2.1, hε i⟩)
    · suffices H : ∀ e ∈ Submodule.span O {e | ∃ x, (tab ρ m th τ).E x e},
          ∀ i, Matrix.vecMul e B⁻¹ i / π i ∈ O by
        have := H _ h
        rwa [hBB'] at this
      intro e he
      induction he using Submodule.span_induction with
      | mem e he =>
        obtain ⟨x, hx, t, c, hT, hC⟩ := he
        refine (hnu _).2 ((u01 _).2 ⟨1, fun _ => 1, fun _ => x, fun _ => t, fun _ => c, fun _ => _,
          fun _ => ⟨by simp, hx, hT, key _ t ((hBB e).symm ▸ hC)⟩, by simp⟩)
      | zero => intro i; simp [O.zero_mem]
      | add e e' _ _ ih ih' =>
        intro i
        rw [Matrix.add_vecMul, Pi.add_apply, add_div]
        exact O.add_mem _ _ (ih i) (ih' i)
      | smul c e _ ih =>
        intro i
        change Matrix.vecMul ((c : F) • e) B⁻¹ i / π i ∈ O
        rw [Matrix.smul_vecMul, Pi.smul_apply, smul_eq_mul, mul_div_assoc]
        exact O.mul_mem _ _ c.2 (ih i)

end GlobalTheory.OneBasis.UnifLoc
end
