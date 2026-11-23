import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.FibreLinInd

theorem exists_det_ne_zero {K A : Type} [Field K] {r : ℕ} (v : A → Fin r → K)
    (h : ∀ c : Fin r → K, (∀ a, ∑ i, c i * v a i = 0) → c = 0) :
    ∃ a : Fin r → A, (Matrix.of fun k i => v (a k) i).det ≠ 0 := by
  classical
  have hspan : Submodule.span K (Set.range v) = ⊤ := by
    by_contra hne
    obtain ⟨φ, hφ0, hφ⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
    apply hφ0
    have hφ' : ∀ w : Fin r → K, φ w = ∑ i, φ (Pi.single i 1) * w i := fun w => by
      rw [LinearMap.pi_apply_eq_sum_univ]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_eq_mul, mul_comm]
      congr 2
      ext j
      simp [Pi.single_apply, eq_comm]
    have := h (fun i => φ (Pi.single i 1)) fun a => by
      rw [← hφ']
      exact hφ (Submodule.subset_span ⟨a, rfl⟩)
    refine LinearMap.ext fun w => ?_
    rw [hφ']
    simp [congrFun this]
  obtain ⟨κ, a, -, hs, hli⟩ := exists_linearIndependent' K v
  let b : Module.Basis κ K (Fin r → K) := Module.Basis.mk hli (by rw [hs, hspan])
  let e : κ ≃ Fin r := b.indexEquiv (Pi.basisFun K (Fin r))
  refine ⟨a ∘ e.symm, ?_⟩
  have h2 : LinearIndependent K ((v ∘ a) ∘ e.symm) := hli.comp _ e.symm.injective
  have h3 : IsUnit (Matrix.of fun k i => v ((a ∘ e.symm) k) i) :=
    Matrix.linearIndependent_rows_iff_isUnit.1 h2
  exact ((Matrix.isUnit_iff_isUnit_det _).1 h3).ne_zero

theorem exists_fibrePower {G Z : Scheme.{0}} (f : G ⟶ Z) [UniversallyOpen f]
    [LocallyOfFiniteType f] (r : ℕ) :
    ∃ (P : Scheme.{0}) (p : P ⟶ Z) (π : Fin r → (P ⟶ G)), UniversallyOpen p ∧
      LocallyOfFiniteType p ∧ (∀ k, π k ≫ f = p) ∧
      ∀ (T : Scheme.{0}) (x : T ⟶ Z) (g : Fin r → (T ⟶ G)), (∀ k, g k ≫ f = x) →
        ∃ h : T ⟶ P, h ≫ p = x ∧ ∀ k, h ≫ π k = g k := by
  induction r with
  | zero =>
    exact ⟨Z, 𝟙 Z, Fin.elim0, inferInstance, inferInstance, fun k => k.elim0,
      fun T x g _ => ⟨x, by simp, fun k => k.elim0⟩⟩
  | succ r ih =>
    obtain ⟨P, p, π, h1, h2, h3, h4⟩ := ih
    refine ⟨pullback f p, pullback.snd f p ≫ p,
      Fin.cons (pullback.fst f p) (fun k => pullback.snd f p ≫ π k), inferInstance, inferInstance,
      ?_, ?_⟩
    · refine Fin.cases ?_ fun k => ?_
      · simpa using pullback.condition
      · simp [h3]
    · intro T x g hg
      obtain ⟨h, hp, hπ⟩ := h4 T x (fun k => g k.succ) fun k => hg _
      refine ⟨pullback.lift (g 0) h (by rw [hg, hp]), by rw [pullback.lift_snd_assoc, hp], ?_⟩
      refine Fin.cases ?_ fun k => ?_
      · simp [pullback.lift_fst]
      · simp [pullback.lift_snd_assoc, hπ]

theorem exists_lift {W Z : Scheme.{0}} (q : W ⟶ Z) [LocallyOfFiniteType q] {K : Type} [Field K]
    [IsAlgClosed K] (x : Sp K ⟶ Z) (w : W) (t : Sp K) (hw : q w = x t) :
    ∃ h : Sp K ⟶ W, h ≫ q = x := by
  obtain ⟨y, -, -⟩ := Scheme.Pullback.exists_preimage_pullback w t hw
  have : JacobsonSpace ↥(pullback q x) := LocallyOfFiniteType.jacobsonSpace (pullback.snd q x)
  obtain ⟨y', -, hy'⟩ := nonempty_inter_closedPoints (Z := (Set.univ : Set ↥(pullback q x)))
    ⟨y, trivial⟩ isOpen_univ.isLocallyClosed
  have hc : IsClosed {y'} := hy'
  refine ⟨pointOfClosedPoint (pullback.snd q x) y' hc ≫ pullback.fst q x, ?_⟩
  rw [Category.assoc, pullback.condition, pointOfClosedPoint_comp_assoc]

variable {K : Type} [Field K] {P G : Scheme.{0}}

theorem top_le_iff (x : Sp K ⟶ P) (U : P.Opens) (z : Sp K) : ⊤ ≤ x ⁻¹ᵁ U ↔ x z ∈ U := by
  have : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  exact ⟨fun h => h (show z ∈ (⊤ : (Sp K).Opens) from trivial),
    fun h y _ => by rw [Subsingleton.elim y z]; exact h⟩

def evalHom (h : Sp K ⟶ P) (U : P.Opens) (hU : ⊤ ≤ h ⁻¹ᵁ U) : Γ(P, U) →+* K :=
  (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom.comp (h.appLE U ⊤ hU).hom

theorem mem_basicOpen_iff (h : Sp K ⟶ P) (U : P.Opens) (hU : ⊤ ≤ h ⁻¹ᵁ U) (D : Γ(P, U))
    (t : Sp K) : h t ∈ P.basicOpen D ↔ evalHom h U hU D ≠ 0 := by
  have e : (Sp K).basicOpen (h.appLE U ⊤ hU D) = h ⁻¹ᵁ P.basicOpen D := by
    rw [Scheme.basicOpen_appLE, top_inf_eq]
  have hinj : Function.Bijective (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.bijective
  change t ∈ h ⁻¹ᵁ P.basicOpen D ↔ _
  rw [← e]
  constructor
  · intro ht h0
    have : h.appLE U ⊤ hU D = 0 := hinj.1 (by rw [map_zero]; exact h0)
    rw [this, Scheme.basicOpen_zero] at ht
    exact ht
  · intro h0
    have : IsUnit (h.appLE U ⊤ hU D) :=
      (MulEquiv.isUnit_map
        (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv).1 (IsUnit.mk0 _ h0)
    rw [Scheme.basicOpen_of_isUnit _ this]
    trivial

theorem evalHom_appLE (h : Sp K ⟶ P) (U : P.Opens) (hU : ⊤ ≤ h ⁻¹ᵁ U) (π : P ⟶ G) (V : G.Opens)
    (hV : U ≤ π ⁻¹ᵁ V) (a : Γ(G, V)) :
    evalHom h U hU (π.appLE V U hV a) = valF (h ≫ π) V a := by
  have hle : ⊤ ≤ (h ≫ π) ⁻¹ᵁ V := fun y hy => hV (hU hy)
  rw [valF, dif_pos hle, ← Scheme.Hom.appLE_comp_appLE h π V U ⊤ hV hU]
  rfl

theorem isOpen_setOf_linearIndependent_on_fibres :
    ∀ (G Z : Scheme.{0}) (f : G ⟶ Z) [Flat f] [LocallyOfFinitePresentation f] (L : LB G),
      L.IsLB → ∀ (r : ℕ) (s : Fin r → LB.Sec L), IsOpen {z : Z | ∀ (K : Type) [Field K]
        [IsAlgClosed K] (x : Sp K ⟶ Z), Set.range x = {z} → ∀ c : Fin r → K,
          (∀ (g : Sp K ⟶ G) (j : L.ι), g ≫ f = x →
            ∑ i, c i * valF g (L.U j) ((s i).f j) = 0) → c = 0} := by
  classical
  intro G Z f _ _ L _ r s
  obtain ⟨P, p, π, h1, h2, h3, h4⟩ := exists_fibrePower f r
  rw [isOpen_iff_forall_mem_open]
  intro z hz
  let K := AlgebraicClosure (Z.residueField z)
  let x : Sp K ⟶ Z :=
    Spec.map (CommRingCat.ofHom (algebraMap (Z.residueField z) K)) ≫ Z.fromSpecResidueField z
  have hxt : ∀ t, x t = z := fun t => by
    rw [← Set.mem_singleton_iff, ← Scheme.range_fromSpecResidueField, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩
  let t₀ : Sp K := IsLocalRing.closedPoint K
  have hx : Set.range x = {z} := by
    ext y
    constructor
    · rintro ⟨t, rfl⟩
      exact hxt t
    · rintro rfl
      exact ⟨t₀, hxt t₀⟩
  obtain ⟨a, ha⟩ := exists_det_ne_zero
    (fun (a : {g : Sp K ⟶ G // g ≫ f = x} × L.ι) i => valF a.1.1 (L.U a.2) ((s i).f a.2))
    fun c hc => hz K x hx c fun g j hg => hc (⟨g, hg⟩, j)
  let j : Fin r → L.ι := fun k => (a k).2
  let U : P.Opens := LB.wchart L π j
  have hU : ∀ k, U ≤ π k ⁻¹ᵁ L.U (j k) := LB.wchart_le L π j
  let M : Matrix (Fin r) (Fin r) Γ(P, U) :=
    Matrix.of fun k i => (π k).appLE (L.U (j k)) U (hU k) ((s i).f (j k))
  have hM : ∀ {K : Type} [Field K] (h : Sp K ⟶ P) (hh : ⊤ ≤ h ⁻¹ᵁ U), evalHom h U hh M.det =
      (Matrix.of fun k i => valF (h ≫ π k) (L.U (j k)) ((s i).f (j k))).det := by
    intro K _ h hh
    rw [RingHom.map_det]
    congr 1
    ext k i
    exact evalHom_appLE h U hh (π k) _ (hU k) _
  let O : P.Opens := P.basicOpen M.det
  refine ⟨p '' (O : Set P), ?_, p.isOpenMap _ O.isOpen, ?_⟩
  · rintro _ ⟨w, hw, rfl⟩ K' _ _ x' hx' c hc
    let t : Sp K' := IsLocalRing.closedPoint K'
    have ht : x' t = p w := by
      rw [← Set.mem_singleton_iff, ← hx']
      exact ⟨t, rfl⟩
    obtain ⟨h, hh⟩ := exists_lift (O.ι ≫ p) x' ⟨w, hw⟩ t ht.symm
    have hO : (h ≫ O.ι) t ∈ O := (h t).2
    have hle : ⊤ ≤ (h ≫ O.ι) ⁻¹ᵁ U := (top_le_iff _ U t).2 (P.basicOpen_le _ hO)
    have hd := (mem_basicOpen_iff _ U hle M.det t).1 hO
    rw [hM] at hd
    refine Matrix.eq_zero_of_mulVec_eq_zero hd (funext fun k => ?_)
    have := hc ((h ≫ O.ι) ≫ π k) (j k) (by rw [Category.assoc, h3, Category.assoc, hh])
    simpa [Matrix.mulVec, dotProduct, mul_comm] using this
  · obtain ⟨h, hp, hπ⟩ := h4 (Sp K) x (fun k => (a k).1.1) fun k => (a k).1.2
    have hle : ⊤ ≤ h ⁻¹ᵁ U := by
      intro t ht
      refine Set.mem_iInter.2 fun k => ?_
      have hk : ⊤ ≤ (a k).1.1 ⁻¹ᵁ L.U (j k) := by
        by_contra hn
        exact ha (Matrix.det_eq_zero_of_row_eq_zero k fun i => dif_neg hn)
      have := hk ht
      rw [← hπ k] at this
      exact this
    refine ⟨h t₀, (mem_basicOpen_iff h U hle M.det t₀).2 ?_, ?_⟩
    · rw [hM]
      simp only [hπ]
      exact ha
    · rw [← Scheme.Hom.comp_apply, hp, hxt]

end GlobalTheory.FibreLinInd
