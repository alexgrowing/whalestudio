import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsL2OnDiagonalOfIsL2Metric
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousAndExistsConjChart

open CategoryTheory AlgebraicGeometry Set Matrix MeasureTheory MonObj Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CxPts GlobalTheory.ArInt
open GlobalTheory.LieVB (omega unitSec dUnit)
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (Fl Pt IsPeriodMap cov per stdLat om0 dflat herm)
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.CxForm (IsRegVar hermMat eval₂ bas IsType IsReal Alt delAt dbarAt)
open GlobalTheory.ConjChart (conjCoord conjPts conjChart)
open GlobalTheory GlobalTheory.TorsionForm
open scoped ContDiff Real CategoryTheory.Obj ComplexOrder

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ConjPeriodChart

theorem isSiegel_neg_conj {g : ℕ} {t : Matrix (Fin g) (Fin g) ℂ} (h : IsSiegel t) :
    IsSiegel (-(t.map (starRingEnd ℂ))) := by
  refine ⟨?_, ?_⟩
  · have h1 := h.1
    unfold Matrix.IsSymm at h1 ⊢
    rw [Matrix.transpose_neg, ← Matrix.transpose_map, h1]
  · have e : (-(t.map (starRingEnd ℂ))).map Complex.im = t.map Complex.im := by
      ext i j; simp
    rw [e]; exact h.2

theorem isPeriodMap_conj {D g : ℕ} {B : Set (V D)} {τ : V D → Matrix (Fin g) (Fin g) ℂ}
    (h : IsPeriodMap B τ) :
    IsPeriodMap (conjCoord D ⁻¹' B) (fun v => -(τ (conjCoord D v)).map (starRingEnd ℂ)) := by
  refine ⟨h.1.preimage (conjCoord D).continuous, fun i j v hv => ?_,
    fun b hb => isSiegel_neg_conj (h.2.2 _ hb)⟩
  have hd : DifferentiableAt ℂ (fun b => τ b i j) (conjCoord D v) :=
    (h.2.1 i j).differentiableAt (h.1.mem_nhds hv)
  have := (ConjChart.differentiableAt_conj_comp hd).neg
  simpa using this.differentiableWithinAt

theorem differentiableAt_conj_comp_pt {D g : ℕ} {F : Pt (V D) g → ℂ} {P : Pt (V D) g}
    (h : DifferentiableAt ℂ F (conjCoord D P.1, star P.2)) :
    DifferentiableAt ℂ (fun Q : Pt (V D) g => starRingEnd ℂ (F (conjCoord D Q.1, star Q.2))) P := by
  let ψ : Pt (V D) g ≃L[ℂ] (Fin D → ℂ) × (Fin g → ℂ) :=
    (EuclideanSpace.equiv (Fin D) ℂ).prodCongr (ContinuousLinearEquiv.refl ℂ _)
  have e : ∀ Q : Pt (V D) g, ψ.symm (star (ψ Q)) = (conjCoord D Q.1, star Q.2) := fun Q => rfl
  have h1 : DifferentiableAt ℂ (F ∘ ψ.symm) (star (ψ P)) := by
    refine DifferentiableAt.comp _ ?_ ψ.symm.differentiableAt
    rw [e]; exact h
  have h2 := h1.star_star
  rw [star_star] at h2
  exact h2.comp P ψ.differentiableAt

theorem fderiv_conj_comp {g : ℕ} (G : (Fin g → ℂ) → ℂ) (x u : Fin g → ℂ) :
    fderiv ℂ (fun z => starRingEnd ℂ (G (star z))) x u = starRingEnd ℂ (fderiv ℂ G (star x) (star u)) := by
  by_cases hG : DifferentiableAt ℂ G (star x)
  · have := hG.hasFDerivAt.star_star
    rw [star_star] at this
    rw [show (fun z => starRingEnd ℂ (G (star z))) = star ∘ G ∘ star from rfl, this.fderiv]
    simp
  · have hn : ¬ DifferentiableAt ℂ (fun z => starRingEnd ℂ (G (star z))) x := fun h' => hG (by
      have := h'.star_star
      simpa [Function.comp_def] using this)
    rw [fderiv_zero_of_not_differentiableAt hn, fderiv_zero_of_not_differentiableAt hG]
    simp

theorem conj_form {g : ℕ} (H : Matrix (Fin g) (Fin g) ℂ) (hH : ∀ i j, starRingEnd ℂ (H i j) = H i j)
    (a b : Fin g → ℂ) : starRingEnd ℂ (HermFrame.form H a b) = HermFrame.form H (star a) (star b) := by
  simp [HermFrame.form, dotProduct, mulVec, map_sum, map_mul, hH]

theorem mem_stdLat_iff {g : ℕ} {x : Fl g} : x ∈ stdLat g ↔ ∀ i, ∃ n : ℤ, x i = n := by
  rw [stdLat, Module.Basis.mem_span_iff_repr_mem]
  exact forall_congr' fun i => ⟨fun ⟨n, hn⟩ => ⟨n, by simpa using hn.symm⟩,
    fun ⟨n, hn⟩ => ⟨n, by simpa using hn.symm⟩⟩

def negP {g : ℕ} (l : Fl g) : Fl g := Sum.elim (-(l ∘ Sum.inl)) (l ∘ Sum.inr)

theorem negP_mem {g : ℕ} {l : Fl g} (h : l ∈ stdLat g) : negP l ∈ stdLat g := by
  rw [mem_stdLat_iff] at h ⊢
  rintro (i | i)
  · obtain ⟨n, hn⟩ := h (Sum.inl i)
    exact ⟨-n, by simp [negP, hn]⟩
  · obtain ⟨n, hn⟩ := h (Sum.inr i)
    exact ⟨n, by simp [negP, hn]⟩

theorem star_per {g : ℕ} (t : Matrix (Fin g) (Fin g) ℂ) (l : Fl g) :
    star (per t l) = per (-(t.map (starRingEnd ℂ))) (negP l) := by
  ext i
  simp [per, negP, vecMul, dotProduct, map_sum]

theorem lat_conj {g : ℕ} (t : Matrix (Fin g) (Fin g) ℂ) (z : Fin g → ℂ) :
    (∃ l ∈ stdLat g, star z = per t l) ↔ ∃ l ∈ stdLat g, z = per (-(t.map (starRingEnd ℂ))) l := by
  constructor
  · rintro ⟨l, hl, e⟩
    exact ⟨negP l, negP_mem hl, by rw [← star_per, ← e, star_star]⟩
  · rintro ⟨l, hl, e⟩
    refine ⟨negP l, negP_mem hl, ?_⟩
    have h2 : -((-(t.map (starRingEnd ℂ))).map (starRingEnd ℂ)) = t := by ext i j; simp
    rw [e, star_per, h2]

theorem comp_conj_conj {X : Scheme.{0}} (x : Sp ℂ ⟶ X) :
    spMap (starRingEnd ℂ) ≫ spMap (starRingEnd ℂ) ≫ x = x :=
  (Points.conjHomeomorph X).left_inv x

theorem conj_comp_inj {X : Scheme.{0}} (a b : Sp ℂ ⟶ X) :
    spMap (starRingEnd ℂ) ≫ a = spMap (starRingEnd ℂ) ≫ b ↔ a = b :=
  ⟨fun h => by rw [← comp_conj_conj a, h, comp_conj_conj], fun h => by rw [h]⟩

theorem top_le_conj {X : Scheme.{0}} (x : Sp ℂ ⟶ X) (U : X.Opens) :
    ⊤ ≤ (spMap (starRingEnd ℂ) ≫ x) ⁻¹ᵁ U ↔ ⊤ ≤ x ⁻¹ᵁ U := by
  have key : ∀ (a : Sp ℂ ⟶ Sp ℂ) (y : Sp ℂ ⟶ X), ⊤ ≤ y ⁻¹ᵁ U → ⊤ ≤ (a ≫ y) ⁻¹ᵁ U := by
    intro a y h
    rw [Scheme.Hom.comp_preimage]
    exact fun z _ => h (Set.mem_univ _)
  refine ⟨fun h => ?_, key _ x⟩
  have := key (spMap (starRingEnd ℂ)) _ h
  rwa [comp_conj_conj] at this

theorem isHolTo_conj {k : Type} [CommRing k] {X : Scheme.{0}} {q : X ⟶ Sp k} {σ : k →+* ℂ} {D g : ℕ}
    {B : Set (V D)} {ex : Pt (V D) g → CxPts q σ} (h : IsHolTo (cov B g) fun P => (ex P).1) :
    IsHolTo (cov (conjCoord D ⁻¹' B) g)
      fun P => spMap (starRingEnd ℂ) ≫ (ex (conjCoord D P.1, star P.2)).1 := by
  intro U f
  have hΦ : Continuous (fun b : Pt (V D) g => ((conjCoord D b.1, star b.2) : Pt (V D) g)) :=
    ((conjCoord D).continuous.comp continuous_fst).prodMk (continuous_star.comp continuous_snd)
  have hset : {b : Pt (V D) g | b ∈ cov (conjCoord D ⁻¹' B) g ∧
      ⊤ ≤ (spMap (starRingEnd ℂ) ≫ (ex (conjCoord D b.1, star b.2)).1) ⁻¹ᵁ U} =
      (fun b : Pt (V D) g => ((conjCoord D b.1, star b.2) : Pt (V D) g)) ⁻¹'
        {b | b ∈ cov B g ∧ ⊤ ≤ (ex b).1 ⁻¹ᵁ U} :=
    Set.ext fun b => and_congr Iff.rfl (top_le_conj _ U)
  beta_reduce
  rw [hset]
  refine ⟨(h U f).1.preimage hΦ, fun b hb => ?_⟩
  have hG : DifferentiableAt ℂ (fun P => valAt' (ex P).1 U f) (conjCoord D b.1, star b.2) :=
    (h U f).2.differentiableAt ((h U f).1.mem_nhds hb)
  refine ((differentiableAt_conj_comp_pt hG).congr_of_eventuallyEq ?_).differentiableWithinAt
  filter_upwards [((h U f).1.preimage hΦ).mem_nhds hb] with Q hQ
  exact CxPts.ev_conj (y := ex (conjCoord D Q.1, star Q.2))
    (y' := conjPts q rfl (ex (conjCoord D Q.1, star Q.2))) rfl hQ.2 f

theorem isPeriodChart_conj : ∀ (k : Type) [CommRing k] (S : Scheme.{0}) (p : S ⟶ Sp k) (A : Over S) [GrpObj A] (g : ℕ) (w : VMetric p (omega A) g) (σ : k →+* ℂ) (D : ℕ) (c : AlgChart p σ D) (τ : V D → Matrix (Fin g) (Fin g) ℂ) (ex : Pt (V D) g → CxPts (A.hom ≫ p) σ), IsPeriodChart w c τ ex → IsPeriodChart w (σ := (starRingEnd ℂ).comp σ) (conjChart rfl c) (fun v => -(τ (conjCoord D v)).map (starRingEnd ℂ)) (fun P => conjPts (A.hom ≫ p) rfl (ex (conjCoord D P.1, star P.2))) := by
  intro k _ S p A _ g w σ D c τ ex H
  obtain ⟨H1, H2, H3⟩ := H
  refine ⟨isPeriodMap_conj H1, isHolTo_conj H2, fun v hv => ?_⟩
  · have hv' : conjCoord D v ∈ c.e.target := hv
    obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := H3 _ hv'
    have hsymm : ((conjChart rfl c).e.symm v).1 =
        spMap (starRingEnd ℂ) ≫ (c.e.symm (conjCoord D v)).1 := rfl
    let K : Over.mk (c.e.symm (conjCoord D v)).1 ⟶ Over.mk ((conjChart rfl c).e.symm v).1 :=
      Over.homMk (spMap (starRingEnd ℂ)) (comp_conj_conj (c.e.symm (conjCoord D v)).1)
    have hK : ∀ (z : Fin g → ℂ) (x : Over.mk ((conjChart rfl c).e.symm v).1 ⟶ A),
        x.left = (conjPts (A.hom ≫ p) rfl (ex (conjCoord D v, z))).1 →
          (K ≫ x).left = (ex (conjCoord D v, z)).1 := by
      intro z x hx
      exact (congrArg (spMap (starRingEnd ℂ) ≫ ·) hx).trans (comp_conj_conj (ex (conjCoord D v, z)).1)
    have hK' : ∀ (x : Over.mk ((conjChart rfl c).e.symm v).1 ⟶ A),
        x.left = spMap (starRingEnd ℂ) ≫ (K ≫ x).left := by
      intro x
      exact (comp_conj_conj (X := A.left) x.left).symm
    refine ⟨fun z => ?_, fun z z' x y hx hy => ?_, fun x => ?_, fun z => ?_, ?_⟩
    · show (spMap (starRingEnd ℂ) ≫ (ex (conjCoord D v, star z)).1) ≫ A.hom =
        spMap (starRingEnd ℂ) ≫ (c.e.symm (conjCoord D v)).1
      rw [Category.assoc, h₁]
    · have e := h₂ (star z) (star z') (K ≫ x) (K ≫ y) (hK (star z) x hx) (hK (star z') y hy)
      rw [← comp_mul] at e
      rw [hK' (x * y), e, ← star_add]
      rfl
    · obtain ⟨z, hz⟩ := h₃ (K ≫ x)
      refine ⟨star z, ?_⟩
      rw [hK' x, hz]
      show _ = spMap (starRingEnd ℂ) ≫ (ex (conjCoord D v, star (star z))).1
      rw [star_star]
    · show spMap (starRingEnd ℂ) ≫ (ex (conjCoord D v, star z)).1 =
        (spMap (starRingEnd ℂ) ≫ (c.e.symm (conjCoord D v)).1) ≫ unitSec A ↔ _
      rw [Category.assoc, conj_comp_inj, h₄]
      exact lat_conj _ _
    · intro U W hU f f' hmem
      have hm : ⊤ ≤ (c.e.symm (conjCoord D v)).1 ⁻¹ᵁ U :=
        (top_le_conj _ U).1 (show ⊤ ≤ (spMap (starRingEnd ℂ) ≫ (c.e.symm (conjCoord D v)).1) ⁻¹ᵁ U from hmem)
      have hmem0 : c.e.symm (conjCoord D v) ∈ ptsIn p σ U := hm
      have h0 : (ex (conjCoord D v, 0)).1 = (c.e.symm (conjCoord D v)).1 ≫ unitSec A :=
        (h₄ 0).2 ⟨0, zero_mem _, by ext i; simp [per, vecMul, dotProduct]⟩
      have hW0 : ⊤ ≤ (ex (conjCoord D v, 0)).1 ⁻¹ᵁ W := by
        rw [h0, Scheme.Hom.comp_preimage]
        exact fun x _ => hU (hm (Set.mem_univ x))
      have hev : ∀ᶠ z in 𝓝 (0 : Fin g → ℂ), ⊤ ≤ (ex (conjCoord D v, star z)).1 ⁻¹ᵁ W := by
        have hc : Continuous (fun z : Fin g → ℂ => ((conjCoord D v, star z) : Pt (V D) g)) :=
          continuous_const.prodMk continuous_star
        have h0m : ((conjCoord D v, star (0 : Fin g → ℂ)) : Pt (V D) g) ∈
            {b | b ∈ cov c.e.target g ∧ ⊤ ≤ (ex b).1 ⁻¹ᵁ W} := by
          refine ⟨⟨hv', trivial⟩, ?_⟩
          simp only [star_zero]
          exact hW0
        exact Filter.mem_of_superset (((H2 W 0).1.preimage hc).mem_nhds h0m) fun z hz => hz.2
      have hcot : ∀ f0 : Γ(A.left, W),
          cot (fun P => conjPts (A.hom ≫ p) rfl (ex (conjCoord D P.1, star P.2))) W f0 v =
            star (cot ex W f0 (conjCoord D v)) := by
        intro f0
        ext a
        show fderiv ℂ (fun z => ev (A.hom ≫ p) ((starRingEnd ℂ).comp σ) W f0
            (conjPts (A.hom ≫ p) rfl (ex (conjCoord D v, star z)))) 0 (Pi.single a 1) =
          star (fderiv ℂ (fun z => ev (A.hom ≫ p) σ W f0 (ex (conjCoord D v, z))) 0 (Pi.single a 1))
        rw [Filter.EventuallyEq.fderiv_eq (hev.mono fun z hz => CxPts.ev_conj (y := ex (conjCoord D v, star z))
          (y' := conjPts (A.hom ≫ p) rfl (ex (conjCoord D v, star z))) rfl hz f0)]
        refine (fderiv_conj_comp (fun z => ev (A.hom ≫ p) σ W f0 (ex (conjCoord D v, z))) 0
          (Pi.single a 1)).trans ?_
        have hs : star (Pi.single a (1 : ℂ) : Fin g → ℂ) = Pi.single a 1 := by
          ext j; by_cases h : j = a <;> simp [h]
        rw [star_zero, hs]
        rfl
      have him : imPart (fun v => -(τ (conjCoord D v)).map (starRingEnd ℂ)) v = imPart τ (conjCoord D v) := by
        ext i j; simp [imPart]
      have hreal : ∀ i j, starRingEnd ℂ (((2 : ℂ) • imPart τ (conjCoord D v)) i j) =
          ((2 : ℂ) • imPart τ (conjCoord D v)) i j := by
        intro i j
        simp only [imPart, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_mul, map_ofNat, Complex.conj_ofReal]
      rw [(w.conj σ ((starRingEnd ℂ).comp σ)).form_eq _ _ (y := c.e.symm (conjCoord D v))
        (y' := (conjChart rfl c).e.symm v) rfl hmem0, h₅ U W hU f f' hmem0, conj_form _ hreal, him, hcot f, hcot f']

end GlobalTheory.ConjPeriodChart
