import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEtLevOver
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RangeSubsetOfGeom
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.EtLev

noncomputable section

namespace GlobalTheory.UPel.HT.EtLev

theorem exists_rep_pow_of_le : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (w0 : Ideal (𝓞 D.F)) (r r' : ℕ), r ≤ r' → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp R) (o : Obj b N s) (H : Over S) (i : H ⟶ o.A), IsFinite H.hom → Etale H.hom → (∀ c ∈ w0 ^ r', i ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) → (∀ (T : Over S) (x : T ⟶ o.A), (∀ c ∈ w0 ^ r', x ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) → ∃! y : T ⟶ H, y ≫ i = x) → ∃ (K : Over S) (κ : K ⟶ o.A), IsFinite K.hom ∧ Etale K.hom ∧ (∀ c ∈ w0 ^ r, κ ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) ∧ ∀ (T : Over S) (x : T ⟶ o.A), (∀ c ∈ w0 ^ r, x ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) → ∃! y : T ⟶ K, y ≫ κ = x := by
  intro p _ D R _ b N w0 r r' hrr' S _ s o H i hHf hHe hi hH
  haveI := hHf
  haveI := hHe
  have hmh := o.act.hom

  let kil : ∀ (T : Over S) (x : T ⟶ o.A), Ideal (𝓞 D.F) := fun T x =>
    { carrier := {c | x ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1}
      add_mem' := by
        intro a c ha hc
        simp only [Set.mem_ofPred_eq] at ha hc ⊢
        rw [map_add, o.act.add, comp_mul, ha, hc, _root_.mul_one]
      zero_mem' := by
        simp only [Set.mem_ofPred_eq, map_zero]
        have h0 := o.act.add 0 0
        rw [add_zero] at h0
        have h1 : x ≫ o.act.act 0 = x ≫ o.act.act 0 * x ≫ o.act.act 0 := by rw [← comp_mul, ← h0]
        exact mul_eq_left.1 h1.symm
      smul_mem' := by
        intro a c hc
        simp only [Set.mem_ofPred_eq, smul_eq_mul] at hc ⊢
        rw [map_mul, o.act.mul, ← Category.assoc, hc, one_comp] }
  obtain ⟨s0, hs0⟩ := IsNoetherian.noetherian (w0 ^ r)
  have hgen : ∀ (T : Over S) (x : T ⟶ o.A),
      (∀ c ∈ w0 ^ r, x ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) ↔
        ∀ c : s0, x ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1 := by
    intro T x
    constructor
    · intro h c
      exact h c (hs0 ▸ Submodule.subset_span c.2)
    · intro h c hc
      have hle : Submodule.span (𝓞 D.F) (s0 : Set (𝓞 D.F)) ≤ kil T x :=
        Submodule.span_le.2 fun c hc => h ⟨c, hc⟩
      rw [← hs0] at hc
      exact hle hc
  have hle : w0 ^ r' ≤ w0 ^ r := Ideal.pow_le_pow_right hrr'
  have hmono : ∀ (T : Over S) (y y' : T ⟶ H), y ≫ i = y' ≫ i → y = y' := by
    intro T y y' e
    have hk : ∀ c ∈ w0 ^ r', (y' ≫ i) ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1 := fun c hc => by
      rw [Category.assoc, hi c hc, comp_one]
    exact (hH T _ hk).unique e rfl
  have hf0 : ∀ c : s0, ∃ f : H ⟶ H, f ≫ i = i ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) := by
    intro c
    refine (hH H _ fun c' hc' => ?_).exists
    rw [Category.assoc, ← o.act.mul, ← map_mul]
    exact hi _ (Ideal.mul_mem_right _ _ hc')
  choose f hf using hf0
  obtain ⟨e, he⟩ := (hH _ (1 : 𝟙_ (Over S) ⟶ o.A) fun c _ => one_comp _).exists
  have htr : ∀ (T : Over S) (h : T ⟶ H), (∀ c : s0, h ≫ f c = h ≫ toUnit H ≫ e) ↔
      ∀ c ∈ w0 ^ r, (h ≫ i) ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1 := by
    intro T h
    rw [hgen]
    refine forall_congr' fun c => ⟨fun e1 => ?_, fun e1 => ?_⟩
    · have e2 := congrArg (· ≫ i) e1
      simp only [Category.assoc, hf, he, comp_one] at e2
      rw [Category.assoc]
      exact e2
    · apply hmono
      simp only [Category.assoc, hf, he, comp_one]
      rw [← Category.assoc]
      exact e1
  obtain ⟨U, hUc, hU⟩ := GlobalTheory.LevCover.ClopenCond.forall_finite (T := H)
    (P := fun (c : s0) (T' : Over S) (h : T' ⟶ H) => h ≫ f c = h ≫ toUnit H ≫ e)
    fun c => GlobalTheory.LevCover.clopenCond_eq (f c) (toUnit H ≫ e)
  obtain ⟨K, iK, hKf, hKe, hiKm, hiK⟩ := GlobalTheory.LevCover.exists_sub U hUc
  refine ⟨K, iK ≫ i, hKf, hKe, ?_, ?_⟩
  · exact (htr K iK).1 ((hU K iK).2 ((hiK K iK).2 ⟨𝟙 _, Category.id_comp _⟩))
  · intro T x hx
    have hx' : ∀ c ∈ w0 ^ r', x ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1 := fun c hc => hx c (hle hc)
    obtain ⟨y0, hy0, -⟩ := hH T x hx'
    have hr : Set.range y0.left ⊆ U := (hU T y0).1 ((htr T y0).2 (by rw [hy0]; exact hx))
    obtain ⟨y, hy⟩ := (hiK T y0).1 hr
    refine ⟨y, show y ≫ iK ≫ i = x by rw [← Category.assoc, hy, hy0], fun y' hy' => ?_⟩
    haveI := hiKm
    apply (cancel_mono iK).1
    apply hmono
    rw [Category.assoc, Category.assoc, hy', ← Category.assoc, hy, hy0]

end GlobalTheory.UPel.HT.EtLev
