import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HZeroPullbackFieldConstant
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsBasisOfIsField
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HasSumPolyDerivMulProdAddMatrix

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open scoped Matrix Topology

namespace GlobalTheory.ThetaFamily

theorem exists_values_line (hT : Out.GlobalSectionsRankAlgClosed) (P : Out.PolAV (Sp ℂ)) :
    ∃ v : P.L.ι → (Sp ℂ ⟶ P.A.left) → ℂ, ∀ s : P.L.Sec, ∃ a : ℂ, ∀ i (x : Sp ℂ ⟶ P.A.left), x ≫ P.A.hom = 𝟙 _ →
      ⊤ ≤ x ⁻¹ᵁ P.L.U i → valAt' x (P.L.U i) (s.f i) = a * v i x := by
  obtain ⟨β, hβ⟩ := PowSec.exists_basis_sections hT ℂ P 1 le_rfl
  have i₀ : Fin (1 ^ P.g) := ⟨0, by simp⟩
  have su : ∀ {M : Type} [AddCommMonoid M] (q : Fin (1 ^ P.g) → M), ∑ i, q i = q i₀ := fun q =>
    Finset.sum_eq_single i₀ (fun a _ h => absurd (Fin.ext (by have := a.2; have := i₀.2; simp at *; omega)) h) (by simp)
  refine ⟨fun i x => valAt' x _ ((β i₀).f (fun _ => i)), fun s => ?_⟩
  obtain ⟨a, ha, -⟩ := hβ (secToPow s 1)
  refine ⟨a i₀, fun i x hx hi => ?_⟩
  have hi' : ⊤ ≤ x ⁻¹ᵁ (lbPow P.L 1).U (fun _ => i) := fun p hp => mem_powChart.2 (hi hp)
  have e := (congrArg (valAt' x _) ((ha (fun _ => i)).trans (su _))).trans ((valAt'_mul x _ _ _).trans
    (congrArg (· * _) (valAt'_constFn x _ hx _ _ hi')))
  refine Eq.trans ?_ e
  exact ((valAt'_res x _ (s.f i ^ 1) hi').trans (by rw [pow_one])).symm

theorem exists_values_line_fibre (hT : Out.GlobalSectionsRankAlgClosed) {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {D : Datum H} {l : Level H} {B : Type} [CommRing B] {b : Base l B} {S : Scheme.{0}} {s : S ⟶ Sp B} (o : Obj D l b s)
    (z : Sp ℂ ⟶ S) :
    ∃ v : (o.t.PP.L.pull (pullback.fst o.t.G.hom z)).ι → (Sp ℂ ⟶ pullback o.t.G.hom z) → ℂ,
      ∀ s : (o.t.PP.L.pull (pullback.fst o.t.G.hom z)).Sec, ∃ a : ℂ, ∀ i (x : Sp ℂ ⟶ pullback o.t.G.hom z),
        x ≫ pullback.snd _ _ = 𝟙 _ → ⊤ ≤ x ⁻¹ᵁ (o.t.PP.L.pull (pullback.fst o.t.G.hom z)).U i →
        valAt' x ((o.t.PP.L.pull (pullback.fst o.t.G.hom z)).U i) (s.f i) = a * v i x := by
  have h := isGrpPullback_pullback o.t.G z
  obtain ⟨hL, hr, ⟨c', w, g, -⟩, hs⟩ := Out.CubePf.cubePull S _ o.t.G _ (cubeMapOf h) o.t.PP o.t.cub
  have semi := IsSemiAbelian.pullback z o.t.G o.t.semi
  have := semi.smooth
  obtain ⟨am, kt⟩ := amplePt _ _ z _ _ _ h _ _ o.t.PP.isLB hL ⟨w, g⟩ o.ample o.ktriv
  have := semi.geomConnected
  have : ConnectedSpace ((Over.pullback z).obj o.t.G).left :=
    GeometricallyConnected.geometrically_connectedSpace (f := ((Over.pullback z).obj o.t.G).hom) (𝟙 _) (𝟙 _)
      ((Over.pullback z).obj o.t.G).hom
      (IsPullback.of_horiz_isIso ⟨(Category.id_comp _).trans (Category.comp_id _).symm⟩)
  obtain ⟨d, hd⟩ := exists_dim_of_preconnected ((Over.pullback z).obj o.t.G).hom
    (eSec ((Over.pullback z).obj o.t.G) (default : PrimeSpectrum ℂ))
  obtain ⟨-, ws, gs', -⟩ := hs o.t.sym
  exact exists_values_line hT
    { A := (Over.pullback z).obj o.t.G, g := d, smoothDim := hd, L := o.t.PP.L.pull (pullback.fst o.t.G.hom z),
      isLB := hL, ample := am, ktriv := kt
      isAb := ⟨inferInstance, inferInstance, MorphismProperty.of_isPullback (P := @IsProper) h.1 o.proper, ‹_›⟩
      rigid := ⟨_, hr⟩
      sym := fun _ => ⟨⊤, trivial, gen_of_iso ((isGen_iff ws).1 gs') _⟩ }

theorem exists_ratio_fibre (hT : Out.GlobalSectionsRankAlgClosed) {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {D : Datum H} {l : Level H} {B : Type} [CommRing B] {b : Base l B} {S : Scheme.{0}} {s : S ⟶ Sp B} (o : Obj D l b s)
    (u : Sp ℂ ⟶ S) (V : S.Opens) (θ₀ : ∀ j, Γ(o.t.G.left, o.t.G.hom ⁻¹ᵁ V ⊓ o.t.PP.L.U j))
    (hθ₀ : θ₀ ∈ secOn o.t.PP.L (o.t.G.hom ⁻¹ᵁ V))
    (nz : ∀ y ∈ V, ∃ (x : o.t.G.left) (j : o.t.PP.L.ι), o.t.G.hom x = y ∧ x ∈ o.t.G.left.basicOpen (θ₀ j))
    (hu : ⊤ ≤ u ⁻¹ᵁ V) (σ : LB.Sec (o.t.PP.L.pull (pullback.fst o.t.G.hom u))) :
    ∃ a : ℂ, ∀ j (x : Sp ℂ ⟶ pullback o.t.G.hom u),
      x ≫ pullback.snd _ _ = 𝟙 _ → ⊤ ≤ (x ≫ pullback.fst _ _) ⁻¹ᵁ o.t.PP.L.U j →
      valAt' x ((o.t.PP.L.pull (pullback.fst o.t.G.hom u)).U (fun _ => j)) (σ.f (fun _ => j)) =
        a * valAt' (x ≫ pullback.fst _ _) (o.t.G.hom ⁻¹ᵁ V ⊓ o.t.PP.L.U j) (θ₀ j) := by
  have := o.t.semi.smooth
  have mem : ∀ x, pullback.fst o.t.G.hom u x ∈ o.t.G.hom ⁻¹ᵁ V := fun x =>
    (congrArg (fun q => q x ∈ V) (pullback.condition (f := o.t.G.hom) (g := u))).mpr (hu (Set.mem_univ _))
  obtain ⟨t, ht⟩ := HolSec.exists_sec_pull o.t.PP.L _ _ mem θ₀ hθ₀
  obtain ⟨v, hv⟩ := exists_values_line_fibre hT o u
  obtain ⟨g₀, j₀, hg₀, hb₀⟩ := nz _ (hu (Set.mem_univ (default : PrimeSpectrum ℂ)))
  obtain ⟨g, hg₁, -⟩ := Scheme.exists_preimage_of_isPullback (IsPullback.of_hasPullback o.t.G.hom u) g₀ _ hg₀
  obtain ⟨x₀, hx₀, hx₁⟩ := ComplexPoints.exists_point_mem (pullback.snd o.t.G.hom u)
    (Z := (pullback.fst o.t.G.hom u ⁻¹ᵁ o.t.G.left.basicOpen (θ₀ j₀) : Scheme.Opens _))
    (TopologicalSpace.Opens.isOpen _).isLocallyClosed ⟨g, by
      show pullback.fst o.t.G.hom u g ∈ o.t.G.left.basicOpen (θ₀ j₀)
      rw [hg₁]; exact hb₀⟩
  have hx₂ : ⊤ ≤ (x₀ ≫ pullback.fst o.t.G.hom u) ⁻¹ᵁ o.t.G.left.basicOpen (θ₀ j₀) := fun p _ => hx₁ p
  obtain ⟨c, hc⟩ := hv t
  obtain ⟨a, ha⟩ := hv σ
  have m : ∀ j (x : Sp ℂ ⟶ pullback o.t.G.hom u), ⊤ ≤ (x ≫ pullback.fst _ _) ⁻¹ᵁ o.t.PP.L.U j →
      ⊤ ≤ x ⁻¹ᵁ (o.t.PP.L.pull (pullback.fst o.t.G.hom u)).U (fun _ => j) := fun j x h p hp => mem_pull.2 (h hp)
  have hj₀ : ⊤ ≤ (x₀ ≫ pullback.fst o.t.G.hom u) ⁻¹ᵁ o.t.PP.L.U j₀ :=
    top_le_preimage_mono _ ((o.t.G.left.basicOpen_le _).trans inf_le_right) hx₂
  have hc0 : c ≠ 0 := by
    rintro rfl
    refine (top_le_preimage_basicOpen_iff _ _ _).1 hx₂ ?_
    rw [← ht j₀ x₀ hj₀, hc _ x₀ hx₀ (m _ _ hj₀), zero_mul]
  refine ⟨a / c, fun j x h₁ h₂ => ?_⟩
  rw [← ht j x h₂, hc _ x h₁ (m _ _ h₂), ha _ x h₁ (m _ _ h₂)]
  field_simp

theorem exists_sec_const_mul {X : Scheme.{0}} {L : LB X} (p : X ⟶ Sp ℂ) (s : L.Sec) (a : ℂ) :
    ∃ t : L.Sec, ∀ i (x : Sp ℂ ⟶ X), x ≫ p = 𝟙 _ → ⊤ ≤ x ⁻¹ᵁ L.U i →
      valAt' x (L.U i) (t.f i) = a * valAt' x (L.U i) (s.f i) := by
  refine ⟨⟨fun i => constFn p _ a * s.f i, fun i j => ?_⟩, fun i x hx hi =>
    (valAt'_mul x _ _ _).trans (congrArg (· * _) (valAt'_constFn x _ hx _ _ hi))⟩
  rw [map_mul, map_mul, s.compat i j, mul_left_comm]
  congr 2
  have r : ∀ (U W : X.Opens) (h : W ≤ U), (X.presheaf.map (homOfLE h).op).hom (constFn p U a) = constFn p W a :=
    fun U W h => (congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom a))
      (Scheme.Hom.appLE_map p (U := ⊤) (V := U) le_top (homOfLE h).op) :)
  rw [r, r]

theorem thetaChar_ne_zero {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ} (hp : (τ.map Complex.im).PosDef) (a b : Fin g → ℝ) :
    thetaChar τ (fun i => (a i : ℂ)) (fun i => (b i : ℂ)) ≠ 0 := by
  have hs : ((2 : ℂ)⁻¹ • (τ + τᵀ)).IsSymm := by
    rw [Matrix.IsSymm, Matrix.transpose_smul, Matrix.transpose_add, Matrix.transpose_transpose, add_comm]
  have hi : ((2 : ℂ)⁻¹ • (τ + τᵀ)).map Complex.im = τ.map Complex.im := by
    ext i j
    have := congrFun (congrFun hp.1 i) j
    simp at this
    simp [this]
    ring
  have h := CanTh.thetaChar_ne_zero hs (hi ▸ hp) a b
  have e : ∀ v : Fin g → ℂ, v ⬝ᵥ ((2 : ℂ)⁻¹ • (τ + τᵀ)) *ᵥ v = v ⬝ᵥ τ *ᵥ v := fun v => by
    rw [Matrix.smul_mulVec, Matrix.add_mulVec, dotProduct_smul, dotProduct_add, Matrix.mulVec_transpose,
      dotProduct_comm v (v ᵥ* τ), ← Matrix.dotProduct_mulVec, smul_eq_mul]
    ring
  unfold thetaChar at h ⊢
  simpa only [e] using h

end GlobalTheory.ThetaFamily
