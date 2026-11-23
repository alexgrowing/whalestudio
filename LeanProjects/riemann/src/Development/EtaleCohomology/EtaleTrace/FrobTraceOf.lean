import Development.EtaleCohomology.EtaleTrace.LadicH0LocallyConstant

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.EtaleTrace

theorem lefschetz_of (hB : Base) (hT : LTransfer) (hC : LCycle) (hF : LFix) (hTr : LTr) (hP : LPushPt) (hA : LAlg) :
    Lefschetz := by
  intro l _ k _ _ hl d Y X q p hq hp hpr c a hc ha hfin het hE
  classical
  obtain ⟨δ, hδ⟩ := hC hB l k hl
  obtain ⟨tr, htr⟩ := hTr hB l k hl δ hδ d p hp hpr
  have hproj := (hT hB l k hl p hp.1 a hfin het).2.1
  have h1 := hA hB l k hl δ hδ d q p hp tr htr c a hc ha (tr ∘ₗ push l a _) (fun n => push l a n ∘ₗ pb l c n)
    (fun n m h u v => by simp only [LinearMap.comp_apply]; rw [hproj])
  have hfx := hF k q p hq.1 hp.1 c a hc ha hE
  have hs : Set.Finite {y : Pt q | y.1 ≫ c = y.1 ≫ a} := hfx
  have h2 := hδ.trans d q p hq hp c a hc ha hE hs.toFinset (fun y => by simp)
  rw [← h1, h2, map_sum]
  have h3 : ∀ y : Pt q, (tr ∘ₗ push l a _) (δ.cl d y) = 1 := fun y => by
    rw [LinearMap.comp_apply, hP hB l k hl δ hδ d q p hq hp a ha hfin het y, htr]
  simp only [h3, Finset.sum_const, nsmul_eq_mul, mul_one]
  congr 1
  exact (Nat.card_eq_card_finite_toFinset hs).symm

theorem pb_comp (l : ℕ) [Fact l.Prime] {A B C : Scheme.{0}} (f : A ⟶ B) (g : B ⟶ C) (n : ℤ) :
    pb l (f ≫ g) n = pb l f n ∘ₗ pb l g n := by
  unfold pb pullHQ
  rw [Functor.map_comp, pullHl_comp, LinearMap.baseChange_comp]

theorem gal_eq (l : ℕ) [Fact l.Prime] {κ : Type} [Field κ] (Ω : Type) [Field Ω] [Algebra κ Ω] {X : Scheme.{0}} (p : X ⟶ S κ)
    (n : ℤ) (σ : Ω ≃ₐ[κ] Ω) : galHQ l Ω p n 0 σ = pb l (GlobalTheory.Et.galMap Ω p σ) n := rfl

theorem pb_frob (l : ℕ) [Fact l.Prime] {κ : Type} [Field κ] (Ω : Type) [Field Ω] [Algebra κ Ω] {X W : Scheme.{0}} (p : X ⟶ S κ)
    (n : ℤ) (σ : Ω ≃ₐ[κ] Ω) (c b : W ⟶ GlobalTheory.Et.geom Ω p) (F : GlobalTheory.Et.geom Ω p ⟶ GlobalTheory.Et.geom Ω p)
    (h : c ≫ GlobalTheory.Et.galMap Ω p σ = b ≫ F) (hid : pb l F n = LinearMap.id) :
    pb l b n ∘ₗ galHQ l Ω p n 0 σ⁻¹ = pb l c n := by
  have h1 : pb l b n = pb l c n ∘ₗ pb l (GlobalTheory.Et.galMap Ω p σ) n :=
    calc pb l b n = pb l b n ∘ₗ pb l F n := by rw [hid, LinearMap.comp_id]
      _ = pb l (c ≫ GlobalTheory.Et.galMap Ω p σ) n := by rw [h]; exact (pb_comp l b F n).symm
      _ = _ := pb_comp l c _ n
  have h2 : pb l (GlobalTheory.Et.galMap Ω p σ) n ∘ₗ pb l (GlobalTheory.Et.galMap Ω p σ⁻¹) n = LinearMap.id := by
    refine (pb_comp l _ _ n).symm.trans ?_
    rw [← galMap_mul, mul_inv_cancel, galMap_one]
    unfold pb pullHQ
    rw [CategoryTheory.Functor.map_id, pullHl_id, LinearMap.baseChange_id]
  rw [gal_eq, h1, LinearMap.comp_assoc, h2, LinearMap.comp_id]

theorem frobTrace_of (hB : Base) (hL : Lefschetz) (hI : LFrobId) (hG : LFrobGeom) : FrobTrace := by
  intro l _ κ Ω _ _ _ _ _ hl d Y X q p hq hp hpr a b ha hb hfin het r hr σ hσ
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed κ
  have hlΩ : (l : Ω) ≠ 0 := fun h => hl ((algebraMap κ Ω).injective (by rw [map_natCast, h, map_zero]))
  obtain ⟨hq', hp', hpr', ha', hfin', het', c, F, hc, hF, hcF, hE, hcard⟩ :=
    hG κ Ω d q p hq hp hpr a b ha hb hfin het r hr σ hσ _ _ rfl rfl
  have key := hL l Ω hlΩ d _ _ hq' hp' hpr' c _ hc ha' hfin' het' hE
  refine Eq.trans ?_ (key.trans (congrArg _ hcard))
  have := Fintype.ofFinite κ
  obtain ⟨p₀, hp₀⟩ := CharP.exists κ
  obtain ⟨s, hs, hcd⟩ := FiniteField.card κ p₀
  have : Fact p₀.Prime := ⟨hs⟩
  have : CharP Ω p₀ := charP_of_injective_algebraMap (algebraMap κ Ω).injective p₀
  rw [Nat.card_eq_fintype_card, hcd, ← pow_mul] at hF
  have hid := hI hB l Ω p₀ hlΩ (pullback.snd _ _) _ F hF
  exact congrArg (altTr l _ d) (funext fun n => congrArg (push l _ n ∘ₗ ·) (pb_frob l Ω p n σ c _ F hcF (hid n)))

theorem goal_of (hFin : LFin) (_ : LRing) (hT : LTransfer) (_ : LadicH0LocallyConstant) (_ : LKunneth) (hC : LCycle) (_ : LPd) (_ : LCover)
    (_ : LInj) (_ : LConst) (hF : LFix) (hTr : LTr) (hP : LPushPt) (hA : LAlg) (hI : LFrobId) (hG : LFrobGeom) : Goal :=
  fun hB => ⟨hFin hB, hT hB, lefschetz_of hB hT hC hF hTr hP hA,
    frobTrace_of hB (lefschetz_of hB hT hC hF hTr hP hA) hI hG⟩

end LateralTheory.EtaleTrace

end
