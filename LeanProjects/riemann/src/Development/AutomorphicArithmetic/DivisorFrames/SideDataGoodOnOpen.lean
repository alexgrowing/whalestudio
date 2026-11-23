import Development.AutomorphicArithmetic.LocalEmbeddings.RootFrame
import Development.AutomorphicArithmetic.DivisorFrames.CramerMatrixBlockTriangularFactor
import Development.AutomorphicArithmetic.DivisorFrames.ColMinorMulTriangular
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodReductionExtendsRegularStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverMapGenericPointSpecializesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeModelInducesRootMetric
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JGenSpecializes
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag GlobalTheory.LineNorm
open Formalism.MainNotions.DIV.Cons (intO)
open scoped TensorProduct Matrix
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.RootFrame

private theorem UpperTheory.colMinor_map_ringHom {R S : Type} [CommRing R] [CommRing S] (g : R →+* S) {n r : ℕ}
    (X : Matrix (Fin n) (Fin r) R) (k : ℕ) (hk : k ≤ r) (σ : Fin k → Fin n) :
    colMinor (X.map g) k hk σ = g (colMinor X k hk σ) := by
  unfold colMinor
  rw [RingHom.map_det]
  rfl

private theorem UpperTheory.valAt_colMinor' {K : Type} [Field K] {Z : Scheme.{0}} [IsIntegral Z] (y : Sp K ⟶ Z) {n r : ℕ}
    (L : Matrix (Fin n) (Fin r) Z.functionField) (hL : ∀ k i, RegAt (below y) (L k i)) (k : ℕ) (hk : k ≤ r)
    (σ : Fin k → Fin n) :
    TrueGeo.valAt y (colMinor L k hk σ) = colMinor (L.map (TrueGeo.valAt y)) k hk σ := by
  choose A hA using hL
  have e : L = (Matrix.of A).map (algebraMap (Z.presheaf.stalk (below y)) Z.functionField) := by
    ext k i; exact (hA k i).symm
  have e' : L.map (TrueGeo.valAt y) = (Matrix.of A).map (Scheme.stalkClosedPointTo y).hom := by
    ext k i
    rw [Matrix.map_apply, ← hA k i, SmallSec.valAt_algebraMap]
    rfl
  rw [e', UpperTheory.colMinor_map_ringHom, e, UpperTheory.colMinor_map_ringHom, SmallSec.valAt_algebraMap]

private theorem UpperTheory.regAt_colMinor' {Z : Scheme.{0}} [IsIntegral Z] (x : Z) {n r : ℕ}
    (L : Matrix (Fin n) (Fin r) Z.functionField) (hL : ∀ k i, RegAt x (L k i)) (k : ℕ) (hk : k ≤ r)
    (σ : Fin k → Fin n) : RegAt x (colMinor L k hk σ) := by
  choose A hA using hL
  have e : L = (Matrix.of A).map (algebraMap (Z.presheaf.stalk x) Z.functionField) := by
    ext k i; exact (hA k i).symm
  rw [e, UpperTheory.colMinor_map_ringHom]
  exact ⟨_, rfl⟩

private theorem UpperTheory.valAt_div_of_unit {K : Type} [Field K] {Z : Scheme.{0}} [IsIntegral Z] {y : Sp K ⟶ Z}
    {f g : Z.functionField} (hf : RegAt (below y) f) (hg : UnitAt (below y) g) :
    TrueGeo.valAt y (f / g) = TrueGeo.valAt y f / TrueGeo.valAt y g := by
  have h1 : TrueGeo.valAt y (1 : Z.functionField) = 1 := by
    have := SmallSec.valAt_algebraMap (y := y) 1
    rwa [map_one, map_one] at this
  have h2 := SmallSec.valAt_mul hg.regAt hg.inv.regAt
  rw [mul_inv_cancel₀ hg.ne_zero, h1] at h2
  rw [div_eq_mul_inv, SmallSec.valAt_mul hf hg.inv.regAt, div_eq_mul_inv, eq_inv_of_mul_eq_one_right h2.symm]

private theorem UpperTheory.cramer_lead_ratio_triangular {K : Type} [Field K] {n r : ℕ} (X : Matrix (Fin n) (Fin r) K)
    (T : Matrix (Fin r) (Fin r) K) (hT : T.BlockTriangular id) (h0 : ∀ i, T i i ≠ 0) (σ : Fin r → Fin n) :
    cram X σ = cram (X * T⁻¹) σ ∧
    (∀ k hk, lead (X * T⁻¹) σ k hk ≠ 0 → lead X σ k hk ≠ 0) ∧
    ∀ i : Fin r, lead X σ (i + 1) i.2 / lead X σ i i.2.le =
      T i i * (lead (X * T⁻¹) σ (i + 1) i.2 / lead (X * T⁻¹) σ i i.2.le) := by
  have hd : IsUnit T.det := by
    rw [Matrix.det_of_upperTriangular hT]
    exact (Finset.prod_ne_zero_iff.2 fun i _ => h0 i).isUnit
  generalize hL : X * T⁻¹ = L
  have e : X = L * T := by rw [← hL, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hd, Matrix.mul_one]
  have hp : ∀ k (hk : k ≤ r), ∏ i : Fin k, T (Fin.castLE hk i) (Fin.castLE hk i) ≠ 0 :=
    fun k hk => Finset.prod_ne_zero_iff.2 fun i _ => h0 _
  subst e
  refine ⟨?_, ?_, ?_⟩
  · ext ρ k
    simp only [cram, lead, Matrix.of_apply, UpperTheory.colMinor_mul_triangular K n r L T hT]
    rw [mul_div_mul_right _ _ (hp _ _)]
  · intro k hk h
    unfold lead at h ⊢
    rw [UpperTheory.colMinor_mul_triangular K n r L T hT]
    exact mul_ne_zero h (hp _ _)
  · intro i
    simp only [lead, UpperTheory.colMinor_mul_triangular K n r L T hT]
    rw [Fin.prod_univ_castSucc]
    have := hp i i.2.le
    have e1 : ∏ j : Fin (i : ℕ), T (Fin.castLE i.2 j.castSucc) (Fin.castLE i.2 j.castSucc) =
      ∏ j : Fin (i : ℕ), T (Fin.castLE i.2.le j) (Fin.castLE i.2.le j) := rfl
    have e2 : Fin.castLE i.2 (Fin.last (i : ℕ)) = i := rfl
    rw [e1, e2, ← _root_.mul_assoc, mul_right_comm, mul_div_mul_right _ _ this]
    ring

theorem UpperTheory.side_data_good_on_open :
    ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (W : Y.X.Opens) (p : ℕ) (J : Type) (U : J → V.X.Opens) (n r : ℕ) (X : J → Matrix (Fin n) (Fin r) V.G.functionField) (T : Y.X → Matrix (Fin r) (Fin r) Y.Fn) (f : Fin r → Y.X → Y.Fn) (l : Fin r → PtFn Y), p.Prime → genericPoint Y.X ∈ W → SideData V W p U X T f l → ∀ (a : J) (U' : V.X.Opens) (σ : Fin r → Fin n) (x : V.X), x ∈ U' → U' ≤ U a → GoodOn V W p U' (X a) T σ → ∃ (M : Matrix (Fin n) (Fin r) V.X.functionField) (c : Fin r → V.G.functionFieldˣ), FrameOn V W p U' (X a) T f l M c σ := by
  intro F _ _ Y V W p J U n r X T f l hp hW ⟨S1, S2, S3⟩ a U' σ x hx hU ⟨G1, G2⟩
  have hη := GlobalTheory.T.cover_map_generic_point_specializes F Y V
  haveI : IsPreimmersion V.j :=
    have h : IsPreimmersion (spMap (algebraMap (𝓞 F) F)) := IsPreimmersion.of_isLocalization (nonZeroDivisors (𝓞 F))
    MorphismProperty.of_isPullback (P := @IsPreimmersion) V.pb.flip h
  have tri := fun x : Y.X => UpperTheory.cramer_lead_ratio_triangular (X a) ((T x).map V.φ) ((S1 x).1.map V.φ)
    (fun i => (map_ne_zero V.φ).2 (right_ne_zero_of_mul ((S1 x).2 i).ne_zero)) σ
  have hg : V.j (genericPoint V.G) ∈ U' := hη.mem_open U'.isOpen (gen_mem hx)
  have hne : ∀ k hk, lead (X a) σ k hk ≠ 0 := fun k hk => (tri _).2.1 k hk (G1 _ hg k hk).ne_zero
  choose M hM using fun k i => SmallSec.fnMap_surjective V.j hη (cram (X a) σ k i)
  let c : Fin r → V.G.functionFieldˣ := fun i =>
    Units.mk0 (lead (X a) σ (i + 1) i.2 / lead (X a) σ i i.2.le) (div_ne_zero (hne _ _) (hne _ _))
  have hc : ∀ i (x : Y.X), V.φ (f i x) * (c i : V.G.functionField) = V.φ (f i x * T x i i) *
      (lead (locM V (X a) T x) σ (i + 1) i.2 / lead (locM V (X a) T x) σ i i.2.le) := by
    intro i x
    rw [map_mul, _root_.mul_assoc]
    exact congrArg _ ((tri x).2.2 i)
  have hreg : ∀ z : V.G, V.j z ∈ U' → ∀ k i, RegAt (V.j z) (M k i) := by
    intro z hz k i
    rw [← SmallSec.regAt_fnMap_iff V.j hη, hM, (tri (V.π z)).1, cram, Matrix.of_apply, div_eq_mul_inv]
    exact (UpperTheory.regAt_colMinor' z _ (S2 a z (hU hz)) _ _ _).mul (G1 z hz _ _).inv.regAt
  have hbelow : ∀ {v e y z yt}, Tst V W p v e y z yt → ⊤ ≤ yt ⁻¹ᵁ U' →
      V.j (below z) ∈ U' ∧ V.π (below z) = below y.1 := by
    intro v e y z yt ⟨_, _, h1, h⟩ hU
    refine ⟨?_, by rw [← h1]; rfl⟩
    change (z ≫ V.j) _ ∈ U'
    rw [← h]
    exact hU (x := spMap e.O.subtype _) trivial
  have hlead : ∀ {v e y z yt}, Tst V W p v e y z yt → ⊤ ≤ yt ⁻¹ᵁ U' → ∀ k hk,
      UnitAt (below z) (lead (locM V (X a) T (below y.1)) σ k hk) ∧
      TrueGeo.valAt z (lead (locM V (X a) T (below y.1)) σ k hk) = lead (vals V (X a) T z (below y.1)) σ k hk := by
    intro v e y z yt ht hU' k hk
    obtain ⟨h1, h2⟩ := hbelow ht hU'
    rw [← h2]
    exact ⟨G1 _ h1 k hk, UpperTheory.valAt_colMinor' z _ (S2 a _ (hU h1)) _ _ _⟩
  have hne' : ∀ {v e y z yt}, Tst V W p v e y z yt → ⊤ ≤ yt ⁻¹ᵁ U' → ∀ k hk,
      lead (vals V (X a) T z (below y.1)) σ k hk ≠ 0 := by
    intro v e y z yt ht hU' k hk
    rw [← (hlead ht hU' k hk).2]
    exact SmallSec.valAt_ne_zero (hlead ht hU' k hk).1
  have hval : ∀ {v e y z yt}, Tst V W p v e y z yt → ⊤ ≤ yt ⁻¹ᵁ U' → ∀ k i,
      TrueGeo.valAt (z ≫ V.j) (M k i) = cram (vals V (X a) T z (below y.1)) σ k i := by
    intro v e y z yt ht hU' k i
    obtain ⟨h1, h2⟩ := hbelow ht hU'
    have hr := S2 a _ (hU h1)
    rw [h2] at hr
    rw [← SmallSec.valAt_fnMap V.j hη z (hreg _ h1 k i), hM, (tri (below y.1)).1, cram, cram, Matrix.of_apply,
      Matrix.of_apply, ← (hlead ht hU' _ _).2]
    refine (UpperTheory.valAt_div_of_unit (UpperTheory.regAt_colMinor' _ _ hr _ _ _) (hlead ht hU' _ _).1).trans ?_
    rw [UpperTheory.valAt_colMinor' z _ hr]
    rfl
  have hvc : ∀ {v e y z yt}, Tst V W p v e y z yt → ⊤ ≤ yt ⁻¹ᵁ U' → ∀ i,
      TrueGeo.valAt z (V.φ (f i (below y.1)) * (c i : V.G.functionField)) =
        TrueGeo.valAt y.1 (f i (below y.1) * T (below y.1) i i) *
          (lead (vals V (X a) T z (below y.1)) σ (i + 1) i.2 / lead (vals V (X a) T z (below y.1)) σ i i.2.le) := by
    intro v e y z yt ht hU' i
    obtain ⟨h1, h2⟩ := hbelow ht hU'
    have hu : UnitAt (V.π (below z)) (f i (below y.1) * T (below y.1) i i) := h2 ▸ (S1 _).2 i
    have h3 := hlead ht hU' (i + 1) i.2
    have h4 := hlead ht hU' i i.2.le
    have h5 : RegAt (below z) (lead (locM V (X a) T (below y.1)) σ (i + 1) i.2 /
        lead (locM V (X a) T (below y.1)) σ i i.2.le) := by
      rw [div_eq_mul_inv]
      exact (h3.1.mul h4.1.inv).regAt
    rw [hc, SmallSec.valAt_mul (V.unitAt_φ hu).regAt h5, V.valAt_φ z hu.regAt, ht.2.2.1,
      UpperTheory.valAt_div_of_unit h3.1.regAt h4.1, h3.2, h4.2]
  refine ⟨Matrix.of M, c, fun x hx hpx k i => ?_, ?_, fun i z hz => ?_, fun v e y z yt ht hU' => ⟨fun i => ?_, ?_⟩⟩
  · refine GlobalTheory.T.good_reduction_extends_regular F Y V p hp W hW U' _ (fun z hz => hreg z hz k i)
      (fun v hv e y hy z yt h1 h2 hU' => ?_) x hx hpx
    have ht : Tst V W p v e y z yt := ⟨hv, hy, h1, h2⟩
    rw [hval ht hU', cram, Matrix.of_apply, map_div₀]
    exact div_le_one_of_le₀ (G2 v e y z yt ht hU' _ _ _) (e.w.nonneg _)
  · obtain ⟨_, _, _, _, h⟩ := UpperTheory.cramer_matrix_block_triangular_factor _ n r (X a) σ hne
    apply (SmallSec.fnMap V.j hη).injective
    rw [map_one, RingHom.map_det, ← h]
    congr 1
    ext k i
    exact hM _ _
  · rw [hc, div_eq_mul_inv]
    exact (V.unitAt_φ ((S1 _).2 i)).mul ((G1 z hz _ _).mul (G1 z hz _ _).inv)
  · obtain ⟨⟨ν, n0, n1, n2, n3⟩, -⟩ := S3 v e y z yt ht a (fun q hq => hU (hU' hq))
    have hν : ∀ k hk, ν k = e.w (lead (vals V (X a) T z (below y.1)) σ k hk) := by
      intro k hk
      obtain ⟨σ', h⟩ := n3 k hk
      exact le_antisymm (h ▸ G2 v e y z yt ht hU' k hk σ') (n2 k hk _)
    have h1 := (e.w.pos (SmallSec.valAt_ne_zero (y := y.1) ((S1 _).2 i))).ne'
    have h2 := (e.w.pos (hne' ht hU' (i + 1) i.2)).ne'
    have h3 := (e.w.pos (hne' ht hU' i i.2.le)).ne'
    rw [n1, hvc ht hU', hν _ i.2, hν _ i.2.le, map_mul, map_div₀, Real.log_mul h1 (div_ne_zero h2 h3),
      Real.log_div h2 h3]
    ring
  · obtain ⟨β, b1, b2, b3, -⟩ := UpperTheory.cramer_matrix_block_triangular_factor _ n r _ σ (hne' ht hU')
    refine ⟨β, b1, ?_, fun i => ?_⟩
    · rw [← b2]
      ext k i
      exact hval ht hU' k i
    · rw [hvc ht hU', mul_left_comm, ← mul_div_assoc, b3, div_self (hne' ht hU' _ _), _root_.mul_one]
