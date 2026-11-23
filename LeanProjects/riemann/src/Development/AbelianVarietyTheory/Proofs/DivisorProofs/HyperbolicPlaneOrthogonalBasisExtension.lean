import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipParLeUnipFlag
import Development.AbelianVarietyTheory.Definitions.Foundations.ConstTermOnMulLeftOfNormalizer
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LanglandsSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneOrthogonalGramRestrictionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsConstAlong
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousToGAd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsInd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsParDec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneWittDecompositionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StoneWeierstrassFiniteRepStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeparatePointsSmoothFiniteSpanStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneOrbitMeasureStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneParabolicDecompositionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormConstantTermVanishesAltBis
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotIsConstTerm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicConjMaxCompact
open scoped TensorProduct NNReal Matrix ComplexConjugate
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar

noncomputable section

namespace GlobalTheory.ThK.InducedCoeff

section Generic

variable {G : Type} [Group G]

def IsBiStable (B : Subalgebra ℂ (G → ℂ)) (K : Subgroup G) (V : Submodule ℂ (G → ℂ)) : Prop :=
  FiniteDimensional ℂ V ∧ ∀ w ∈ V, w ∈ B ∧ ∀ k ∈ K, (fun g => w (k * g)) ∈ V ∧ (fun g => w (g * k)) ∈ V

variable {B : Subalgebra ℂ (G → ℂ)} {K : Subgroup G}

theorem isBiStable_span {ι : Type} [Finite ι] {f : ι → G → ℂ} (hB : ∀ i, f i ∈ B)
    (h : ∀ i, ∀ k ∈ K, (fun g => f i (k * g)) ∈ Submodule.span ℂ (Set.range f) ∧
      (fun g => f i (g * k)) ∈ Submodule.span ℂ (Set.range f)) : IsBiStable B K (Submodule.span ℂ (Set.range f)) := by
  refine ⟨FiniteDimensional.span_of_finite ℂ (Set.finite_range f), fun w hw => ?_⟩
  induction hw using Submodule.span_induction with
  | mem x hx => obtain ⟨i, rfl⟩ := hx; exact ⟨hB i, h i⟩
  | zero => exact ⟨zero_mem _, fun _ _ => ⟨zero_mem _, zero_mem _⟩⟩
  | add x y _ _ hx hy =>
    exact ⟨add_mem hx.1 hy.1, fun k hk => ⟨add_mem (hx.2 k hk).1 (hy.2 k hk).1, add_mem (hx.2 k hk).2 (hy.2 k hk).2⟩⟩
  | smul c x _ hx =>
    exact ⟨B.smul_mem hx.1 c, fun k hk => ⟨Submodule.smul_mem _ c (hx.2 k hk).1, Submodule.smul_mem _ c (hx.2 k hk).2⟩⟩

theorem isBiStable_iSup {ι : Type} [Finite ι] {V : ι → Submodule ℂ (G → ℂ)} (h : ∀ i, IsBiStable B K (V i)) :
    IsBiStable B K (⨆ i, V i) := by
  haveI := fun i => (h i).1
  refine ⟨inferInstance, fun w hw => ?_⟩
  induction hw using Submodule.iSup_induction' with
  | mem i x hx =>
    exact ⟨((h i).2 x hx).1, fun k hk => ⟨Submodule.mem_iSup_of_mem i (((h i).2 x hx).2 k hk).1,
      Submodule.mem_iSup_of_mem i (((h i).2 x hx).2 k hk).2⟩⟩
  | zero => exact ⟨zero_mem _, fun _ _ => ⟨zero_mem _, zero_mem _⟩⟩
  | add x y _ _ hx hy =>
    exact ⟨add_mem hx.1 hy.1, fun k hk => ⟨add_mem (hx.2 k hk).1 (hy.2 k hk).1, add_mem (hx.2 k hk).2 (hy.2 k hk).2⟩⟩

theorem IsBiStable.mul {V V' : Submodule ℂ (G → ℂ)} (h : IsBiStable B K V) (h' : IsBiStable B K V') :
    IsBiStable B K (V * V') := by
  refine ⟨Module.Finite.iff_fg.2 ((Module.Finite.iff_fg.1 h.1).mul (Module.Finite.iff_fg.1 h'.1)), fun w hw => ?_⟩
  refine Submodule.mul_induction_on hw (fun x hx y hy => ?_) fun x y hx hy => ?_
  · exact ⟨mul_mem (h.2 x hx).1 (h'.2 y hy).1, fun k hk =>
      ⟨Submodule.mul_mem_mul ((h.2 x hx).2 k hk).1 ((h'.2 y hy).2 k hk).1,
        Submodule.mul_mem_mul ((h.2 x hx).2 k hk).2 ((h'.2 y hy).2 k hk).2⟩⟩
  · exact ⟨add_mem hx.1 hy.1, fun k hk => ⟨add_mem (hx.2 k hk).1 (hy.2 k hk).1, add_mem (hx.2 k hk).2 (hy.2 k hk).2⟩⟩

theorem IsBiStable.star {V : Submodule ℂ (G → ℂ)} (h : IsBiStable B K V) (hB : ∀ f ∈ B, star f ∈ B) :
    IsBiStable B K (V.map (starLinearEquiv ℂ (A := G → ℂ)).toLinearMap) := by
  refine ⟨Module.Finite.iff_fg.2 ((Module.Finite.iff_fg.1 h.1).map _), ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨hB x (h.2 x hx).1, fun k hk => ⟨⟨_, ((h.2 x hx).2 k hk).1, rfl⟩, ⟨_, ((h.2 x hx).2 k hk).2, rfl⟩⟩⟩

variable (B K) in

def biFin : Subalgebra ℂ (G → ℂ) where
  carrier := {f | ∃ V, IsBiStable B K V ∧ f ∈ V}
  add_mem' := fun {a b} ⟨V, hV, ha⟩ ⟨V', hV', hb⟩ =>
    ⟨⨆ i : Bool, if i then V else V', isBiStable_iSup fun i => by cases i <;> simpa,
      add_mem (Submodule.mem_iSup_of_mem true (by simpa)) (Submodule.mem_iSup_of_mem false (by simpa))⟩
  mul_mem' := fun ⟨V, hV, ha⟩ ⟨V', hV', hb⟩ => ⟨V * V', hV.mul hV', Submodule.mul_mem_mul ha hb⟩
  algebraMap_mem' c := ⟨Submodule.span ℂ (Set.range fun _ : Unit => algebraMap ℂ (G → ℂ) c),
    isBiStable_span (fun _ => B.algebraMap_mem c) fun _ _ _ =>
      ⟨Submodule.subset_span ⟨(), rfl⟩, Submodule.subset_span ⟨(), rfl⟩⟩, Submodule.subset_span ⟨(), rfl⟩⟩

theorem exists_common {ι : Type} [Finite ι] {a : ι → G → ℂ} (h : ∀ i, a i ∈ biFin B K) :
    ∃ V, IsBiStable B K V ∧ ∀ i, a i ∈ V := by
  choose V hV ha using h
  exact ⟨⨆ i, V i, isBiStable_iSup hV, fun i => Submodule.mem_iSup_of_mem i (ha i)⟩

theorem exists_matrix_rep {Q : Type} [Group Q] [TopologicalSpace Q] [TopologicalSpace G] [IsTopologicalGroup G]
    (η : Q →* G) (hη : Continuous η) (χ : Q →* ℂ) (hχ : Continuous χ) {d : ℕ} {v : Fin d → G → ℂ}
    (hv : LinearIndependent ℂ v) (hc : ∀ i, Continuous (v i))
    (hs : ∀ q i, (fun z => v i (z * η q)) ∈ Submodule.span ℂ (Set.range v)) :
    ∃ ρ : Q →* Matrix (Fin d) (Fin d) ℂ, Continuous ρ ∧ ∀ q (x : Fin d → ℂ) z,
      ∑ i, v i z * (ρ q *ᵥ x) i = χ q * ∑ j, v j (z * η q) * x j := by
  let b := Module.Basis.span hv
  haveI : FiniteDimensional ℂ (Submodule.span ℂ (Set.range v)) := FiniteDimensional.span_of_finite ℂ (Set.finite_range v)
  let ρ : Q → Matrix (Fin d) (Fin d) ℂ := fun q => Matrix.of fun i j => χ q * b.coord i ⟨_, hs q j⟩
  have h1 : ∀ q j z, ∑ i, b.coord i ⟨_, hs q j⟩ * v i z = v j (z * η q) := fun q j z => by
    have := congrFun (congrArg Subtype.val (b.sum_repr ⟨_, hs q j⟩)) z
    simpa [b, Module.Basis.span_apply] using this
  have law : ∀ q (x : Fin d → ℂ) z, ∑ i, v i z * (ρ q *ᵥ x) i = χ q * ∑ j, v j (z * η q) * x j := fun q x z => by
    simp only [← h1 q _ z, ρ, Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have inj : ∀ x y : Fin d → ℂ, (∀ z, ∑ i, v i z * x i = ∑ i, v i z * y i) → x = y := fun x y h =>
    funext (Fintype.linearIndependent_iffₛ.1 hv x y (funext fun z => by simpa [mul_comm] using h z))
  refine ⟨{ toFun := ρ
            map_one' := Matrix.ext_of_mulVec_single fun j => inj _ _ fun z => by
              rw [law]; simp only [map_one, one_mul, mul_one, Matrix.one_mulVec]
            map_mul' := fun q q' => Matrix.ext_of_mulVec_single fun j => inj _ _ fun z => by
              rw [← Matrix.mulVec_mulVec, law, law, law, map_mul, map_mul, mul_assoc, mul_assoc] }, ?_, law⟩
  refine continuous_matrix fun i j => hχ.mul ((b.coord i).continuous_of_finiteDimensional.comp (Continuous.subtype_mk ?_ _))
  exact continuous_pi fun z => (hc j).comp (continuous_const.mul hη)

end Generic

section Good

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

def goodAlg : Subalgebra ℂ (GAd σ J → ℂ) where
  carrier := {w | Continuous w ∧ GlobalTheory.UAut.IsSm σ J w ∧
    ∃ U : Subgroup (GAd σ J), IsOpen (U : Set (GAd σ J)) ∧ ∀ u ∈ U, u ∈ finPts σ J → ∀ g, w (g * u) = w g}
  add_mem' := fun ⟨h1, h2, U, hU, h3⟩ ⟨h1', h2', U', hU', h3'⟩ => ⟨h1.add h1', fun k γ hγ g => (h2 k γ hγ g).add (h2' k γ hγ g),
    U ⊓ U', hU.inter hU', fun u hu hf g => by simp only [Pi.add_apply, h3 u hu.1 hf, h3' u hu.2 hf]⟩
  mul_mem' := fun ⟨h1, h2, U, hU, h3⟩ ⟨h1', h2', U', hU', h3'⟩ => ⟨h1.mul h1', fun k γ hγ g => (h2 k γ hγ g).mul (h2' k γ hγ g),
    U ⊓ U', hU.inter hU', fun u hu hf g => by simp only [Pi.mul_apply, h3 u hu.1 hf, h3' u hu.2 hf]⟩
  algebraMap_mem' c := ⟨continuous_const, fun _ _ _ _ => contDiff_const, ⊤, isOpen_univ, fun _ _ _ _ => rfl⟩

variable {σ J}

theorem star_mem_goodAlg (f : GAd σ J → ℂ) (hf : f ∈ goodAlg σ J) : star f ∈ goodAlg σ J := by
  obtain ⟨h1, h2, U, hU, h3⟩ := hf
  exact ⟨h1.star, fun k γ hγ g => Complex.conjCLE.contDiff.comp (h2 k γ hγ g), U, hU, fun u hu hf g => by
    simp only [Pi.star_apply, h3 u hu hf]⟩

open GlobalTheory.Orb (archMat) in

theorem separates (hCM : IsCMExt F E σ) (hJ : IsHermND σ J) {K : Subgroup (GAd σ J)} (hK : IsCompact (K : Set (GAd σ J)))
    {x y : GAd σ J} (hx : x ∈ K) (hy : y ∈ K) (hxy : x ≠ y) : ∃ f ∈ biFin (goodAlg σ J) K, f x ≠ f y := by
  by_cases hf : projFin σ J x = projFin σ J y
  · obtain ⟨w, hw⟩ : ∃ w, projArch σ J w x ≠ projArch σ J w y := by
      by_contra h
      push Not at h
      exact hxy (ext_inf_fin σ J (GInf_ext σ J fun w => by simp [h w]) hf)
    obtain ⟨τ⟩ : Nonempty (EmbOver E w) := inferInstance
    have inj : Function.Injective (archMat σ J τ) := fun a b e => by
      rw [GlobalTheory.Orb.archMat_eq_archEquiv J hCM, GlobalTheory.Orb.archMat_eq_archEquiv J hCM] at e
      exact (archEquiv J hCM τ).injective (Subtype.ext (Units.ext e))
    obtain ⟨i, j, hij⟩ : ∃ i j, archMat σ J τ (projArch σ J w x) i j ≠ archMat σ J τ (projArch σ J w y) i j := by
      by_contra h
      push Not at h
      exact hw (inj (Matrix.ext h))
    let e : Fin n × Fin n → GAd σ J → ℂ := fun p g => archMat σ J τ (projArch σ J w g) p.1 p.2
    have hc : Continuous fun g => archMat σ J τ (projArch σ J w g) :=
      (Units.continuous_val.comp ((isEmbedding_matHom _ σ J).continuous.comp
        (continuous_projArch σ J w))).matrix_map (GlobalTheory.Orb.continuous_infEmb τ)
    refine ⟨e (i, j), ⟨_, isBiStable_span (f := e) (fun p => ⟨hc.matrix_elem p.1 p.2, GlobalTheory.UAut.Model.isSm_entry hCM τ p.1 p.2,
      ⊤, isOpen_univ, fun u _ hu g => ?_⟩) fun p k _ => ⟨?_, ?_⟩, Submodule.subset_span ⟨(i, j), rfl⟩⟩, hij⟩
    · simp only [e, map_mul, mem_finPts_iff_forall.1 hu w, mul_one]
    · have : (fun g => e p (k * g)) = ∑ l, e (p.1, l) k • e (l, p.2) := funext fun g => by
        simp only [e, map_mul, Matrix.mul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [this]
      exact sum_mem fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
    · have : (fun g => e p (g * k)) = ∑ l, e (l, p.2) k • e (p.1, l) := funext fun g => by
        simp only [e, map_mul, Matrix.mul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm]
      rw [this]
      exact sum_mem fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  · obtain ⟨V, hV, h, f, hfV, hne⟩ := GlobalTheory.T.separate_points_smooth_finite_span F E σ hCM n J hJ K hK x hx y hy hf
    exact ⟨f, ⟨V, ⟨hV, fun w hw => ⟨⟨(h w hw).1, (h w hw).2.1, (h w hw).2.2.1⟩, (h w hw).2.2.2⟩⟩, hfV⟩, hne⟩

end Good

set_option maxHeartbeats 800000 in

theorem exists_coeff : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (hσ : ∀ x, σ (σ x) = x) (n n₁ : ℕ) (W : Spc F E n) (W₁ : Spc F E n₁) (H : Plane E n n₁), (∀ i j, σ (W.J j i) = -W.J i j) → n = n₁ + 2 →
      form σ W.J H.x H.x = 0 → form σ W.J H.y H.y = 0 → form σ W.J H.x H.y = 1 →
      (∀ u, form σ W.J (H.ι *ᵥ u) H.x = 0 ∧ form σ W.J (H.ι *ᵥ u) H.y = 0) → H.ιᵀ * W.J * H.ι.map σ = W₁.J →
      ∀ (c₀ : E) (hc₀ : c₀ ≠ 0), IsHermND σ (c₀ • W₁.J.map σ) → IsHermND σ (c₀ • W.J.map σ) →
      ∀ M : UA σ W₁.J → UA σ W.J, Continuous M → (∀ h₁, IsLevi (W₁ := W₁) H 1 h₁ (M h₁)) →
      (∀ γ ∈ ratU σ W₁.J, M γ ∈ ratU σ W.J) →
      ∀ (r : ℕ) (Xf Yf : Matrix (Fin n₁) (Fin r) E), GlobalTheory.SiegelSet.IsWittFrame σ (c₀ • W₁.J.map σ) Xf Yf →
      ∀ X' Y' : Matrix (Fin n) (Fin (r + 1)) E, GlobalTheory.SiegelSet.IsWittFrame σ (c₀ • W.J.map σ) X' Y' →
      (∀ k, X' k 0 = H.x k) → (∀ k, Y' k 0 = c₀⁻¹ * H.y k) →
      (∀ (k : Fin n) (i : Fin r), X' k i.succ = (H.ι * Xf) k i ∧ Y' k i.succ = (H.ι * Yf) k i) → ∀ S' : Finset (Fin r),
      ∀ χ : Chr F E, (∀ t : Eˣ, χ (Units.map (inclR (F := F) (E := E) (AF F)).toMonoidHom t) = 1) → Continuous (fun t : (AE F E)ˣ => (χ t : ℂ)) →
      ∀ K₁ : Subgroup (GAd σ (c₀ • W₁.J.map σ)), GlobalTheory.UAut.IsMaxCpt σ (c₀ • W₁.J.map σ) K₁ →
      ∀ ψ : GAd σ (c₀ • W₁.J.map σ) → ℂ, GlobalTheory.StdPar.IsCuspOn σ (c₀ • W₁.J.map σ) Xf Yf S' K₁ ψ →
      ∀ K' : Subgroup (GAd σ (c₀ • W.J.map σ)), GlobalTheory.UAut.IsMaxCpt σ (c₀ • W.J.map σ) K' → (∀ y ∈ K₁, GlobalTheory.ThK.CuspTransfer.emb hσ W W₁ hc₀ M y ∈ K') →
      (∀ (t : (AE F E)ˣ) (y : GAd σ (c₀ • W₁.J.map σ)) (g : GAd σ (c₀ • W.J.map σ)), GlobalTheory.ThK.InducedCons.IsParDec hσ W W₁ H hc₀ X' M t y g → g ∈ K' → y ∈ K₁) →
      ∀ Kf : Subgroup (GAd σ (c₀ • W.J.map σ)), IsCompact (Kf : Set (GAd σ (c₀ • W.J.map σ))) → Kf ≤ finPts σ (c₀ • W.J.map σ) →
      ∀ U : Subgroup (GAd σ (c₀ • W.J.map σ)), IsOpen (U : Set (GAd σ (c₀ • W.J.map σ))) → U ⊓ finPts σ (c₀ • W.J.map σ) ≤ Kf →
      ∃ (d : ℕ) (ψs : Fin (d + 1) → GAd σ (c₀ • W₁.J.map σ) → ℂ) (a : Fin (d + 1) → GAd σ (c₀ • W.J.map σ) → ℂ),
      (∀ i, GlobalTheory.StdPar.IsCuspOn σ (c₀ • W₁.J.map σ) Xf Yf S' K₁ (ψs i)) ∧ ψs 0 = ψ ∧ (∀ i, a i 1 = if i = 0 then 1 else 0) ∧
      (∀ (t : (AE F E)ˣ) (y : GAd σ (c₀ • W₁.J.map σ)) (p : GAd σ (c₀ • W.J.map σ)), GlobalTheory.ThK.InducedCons.IsParDec hσ W W₁ H hc₀ X' M t y p → ∀ k ∈ K', ∀ k₂ ∈ Kf, ∀ k' ∈ K', ∀ k₂' ∈ Kf,
        p * (k * k₂) = k' * k₂' → ∀ z, ∑ i, ψs i z * a i (k' * k₂') = (χ t : ℂ) * ∑ i, ψs i (z * y) * a i (k * k₂)) ∧
      (∃ U' : Subgroup (GAd σ (c₀ • W.J.map σ)), IsOpen (U' : Set (GAd σ (c₀ • W.J.map σ))) ∧ ∀ u ∈ U', u ∈ finPts σ (c₀ • W.J.map σ) → ∀ k ∈ K', ∀ k₂ ∈ Kf, ∀ i,
        a i (k * k₂ * u) = a i (k * k₂)) ∧
      (∀ i, ContinuousOn (a i) {g : GAd σ (c₀ • W.J.map σ) | ∃ k ∈ K', ∃ k₂ ∈ Kf, g = k * k₂}) ∧
      (∀ i, ∀ k ∈ K', ∀ k₂ ∈ Kf, ∀ (e : ℕ) (γ : Fin e → ℝ → GAd σ (c₀ • W.J.map σ)), (∀ j, GlobalTheory.SiegelSet.IsRealLine σ (c₀ • W.J.map σ) (γ j)) → (∀ j s, γ j s ∈ K') →
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t : Fin e → ℝ => a i (k * k₂ * (List.ofFn fun j => γ j (t j)).prod)) ∧
      (∃ (e : ℕ) (b : Fin e → GAd σ (c₀ • W.J.map σ) → ℂ), (∀ j, ContinuousOn (b j) {g : GAd σ (c₀ • W.J.map σ) | ∃ k ∈ K', ∃ k₂ ∈ Kf, g = k * k₂}) ∧ (∀ i, ∃ c : Fin e → ℂ, ∀ g ∈ {g : GAd σ (c₀ • W.J.map σ) | ∃ k ∈ K', ∃ k₂ ∈ Kf, g = k * k₂}, a i g = ∑ j, c j * b j g) ∧
        ∀ j, ∀ k' ∈ K', ∃ c : Fin e → ℂ, ∀ g ∈ {g : GAd σ (c₀ • W.J.map σ) | ∃ k ∈ K', ∃ k₂ ∈ Kf, g = k * k₂}, b j (g * k') = ∑ l, c l * b l g) := by
  intro F E _ _ _ _ _ σ hCM hσ n n₁ W W₁ H hsk hn hxx hyy hxy hι hιJ c₀ hc₀ hH1 hH M hMc hML hMr r Xf Yf hWf X' Y' hW' hX0 hY0 hXs
    S' χ _ hχ K₁ hK₁ ψ hψ K' hK' _ hPK Kf hKf hKff U _ _
  obtain ⟨hmul, hinv⟩ := GlobalTheory.T.isParDec_mul_and_inv F E σ hCM hσ n n₁ W W₁ H hsk hn hxx hyy hxy hι hιJ c₀ hc₀ hH1 hH M hMc hML hMr r Xf Yf
    hWf X' Y' hW' hX0 hY0 hXs
  obtain ⟨hone, hPc, τ, η, hτ, hη, hu⟩ := GlobalTheory.T.hyperbolic_plane_orbit_measure F E σ hCM hσ n n₁ W W₁ H hsk hn hxx hyy hxy hι hιJ c₀ hc₀ hH1 hH M hMc
    hML hMr r Xf Yf hWf X' Y' hW' hX0 hY0 hXs
  have hre := GlobalTheory.T.hyperbolic_plane_parabolic_decomposition F E σ hCM hσ n n₁ W W₁ H hsk hn hxx hyy hxy hι hιJ c₀ hc₀ hH1 hH M hMc
    hML hMr r Xf Yf hWf X' Y' hW' hX0 hY0 hXs
  have hK'i : K' ≤ infPts σ _ := hK'.1.1
  have hcomm : ∀ k ∈ K', ∀ k₂ ∈ Kf, Commute k k₂ := fun k hk k₂ hk₂ =>
    GlobalTheory.StdPar.RealConj.commute_real_fin (hK'i hk) (hKff hk₂)
  let P : Subgroup (GAd σ (c₀ • W.J.map σ)) :=
    { carrier := {g | ∃ t y, GlobalTheory.ThK.InducedCons.IsParDec hσ W W₁ H hc₀ X' M t y g}
      one_mem' := ⟨1, 1, hone⟩
      mul_mem' := fun ⟨t, y, h⟩ ⟨t', y', h'⟩ => ⟨_, _, hmul _ _ _ _ _ _ h h'⟩
      inv_mem' := fun ⟨t, y, h⟩ => ⟨_, _, hinv _ _ _ h⟩ }
  let Kc : Subgroup (GAd σ (c₀ • W.J.map σ)) :=
    { carrier := {g | ∃ k ∈ K', ∃ k₂ ∈ Kf, g = k * k₂}
      one_mem' := ⟨1, one_mem _, 1, one_mem _, (mul_one _).symm⟩
      mul_mem' := by
        rintro _ _ ⟨k, hk, k₂, hk₂, rfl⟩ ⟨l, hl, l₂, hl₂, rfl⟩
        exact ⟨_, mul_mem hk hl, _, mul_mem hk₂ hl₂, (hcomm l hl k₂ hk₂).symm.mul_mul_mul_comm k l₂⟩
      inv_mem' := by
        rintro _ ⟨k, hk, k₂, hk₂, rfl⟩
        exact ⟨_, inv_mem hk, _, inv_mem hk₂, by rw [(hcomm k hk k₂ hk₂).eq, mul_inv_rev]⟩ }
  have hKc : IsCompact (Kc : Set (GAd σ (c₀ • W.J.map σ))) := by
    convert (hK'.1.2.prod hKf).image continuous_mul using 1
    ext g
    exact ⟨fun ⟨k, hk, k₂, hk₂, e⟩ => ⟨(k, k₂), ⟨hk, hk₂⟩, e.symm⟩, fun ⟨p, hp, e⟩ => ⟨p.1, hp.1, p.2, hp.2, e.symm⟩⟩
  have hQ : IsCompact ((P ⊓ Kc : Subgroup _) : Set (GAd σ (c₀ • W.J.map σ))) := hKc.inter_left hPc
  haveI := isCompact_iff_compactSpace.1 hQ
  have hdec : ∀ q : (P ⊓ Kc : Subgroup _), GlobalTheory.ThK.InducedCons.IsParDec hσ W W₁ H hc₀ X' M (τ q) (η q) q := fun q => by
    obtain ⟨t, y, h⟩ := q.2.1
    rw [(hu _ _ _ h).1, (hu _ _ _ h).2]
    exact h
  let ηh : (P ⊓ Kc : Subgroup _) →* GAd σ (c₀ • W₁.J.map σ) :=
    MonoidHom.mk' (fun q => η q) fun a b => (hu _ _ _ (hmul _ _ _ _ _ _ (hdec a) (hdec b))).2
  let τh : (P ⊓ Kc : Subgroup _) →* (AE F E)ˣ :=
    MonoidHom.mk' (fun q => τ q) fun a b => (hu _ _ _ (hmul _ _ _ _ _ _ (hdec a) (hdec b))).1
  have hηc : Continuous ηh := hη.comp_continuous continuous_subtype_val fun q => q.2.1
  have hτc : Continuous τh := hτ.comp_continuous continuous_subtype_val fun q => q.2.1
  obtain ⟨hcusp, hfd⟩ := GlobalTheory.T.cusp_form_constant_term_vanishes_alt F E σ hCM n₁ _ hH1 r Xf Yf hWf S' K₁ hK₁.1.1 ψ hψ ηh.range (isCompact_range hηc) (by
    rintro _ ⟨q, rfl⟩
    obtain ⟨t₁, h⟩ := hre _ _ _ (hdec q)
    refine hPK _ _ _ h ?_
    obtain ⟨k, hk, k₂, hk₂, e⟩ := q.2.2
    have : ofInf σ _ (projInf σ _ (q : GAd σ (c₀ • W.J.map σ))) = k := ext_inf_fin σ _
      (by simp [e, mem_finPts.1 (hKff hk₂)]) (by simp [mem_infPts.1 (hK'i hk)])
    rw [this]
    exact hk)
  obtain ⟨d, v, hvS, hvs, hvi⟩ : ∃ (d : ℕ) (v : Fin d → GAd σ (c₀ • W₁.J.map σ) → ℂ),
      (∀ i, v i ∈ {f : GAd σ (c₀ • W₁.J.map σ) → ℂ | ∃ y ∈ ηh.range, f = fun g => ψ (g * y)}) ∧
      Submodule.span ℂ (Set.range v) = Submodule.span ℂ {f : GAd σ (c₀ • W₁.J.map σ) → ℂ | ∃ y ∈ ηh.range, f = fun g => ψ (g * y)} ∧
      LinearIndependent ℂ v := ⟨_, Submodule.exists_fun_fin_finrank_span_eq ℂ _⟩
  have hvc : ∀ i, GlobalTheory.StdPar.IsCuspOn σ (c₀ • W₁.J.map σ) Xf Yf S' K₁ (v i) := fun i => by
    obtain ⟨y, hy, e⟩ := hvS i
    exact e ▸ hcusp y hy
  obtain ⟨ρ, hρ, law⟩ := exists_matrix_rep ηh hηc ((Circle.coeHom.comp χ).comp τh) (hχ.comp hτc) hvi
    (fun i => (hvc i).1.cont) fun q i => by
      obtain ⟨y, hy, e⟩ := hvS i
      rw [hvs, e]
      exact Submodule.subset_span ⟨ηh q * y, mul_mem ⟨q, rfl⟩ hy, funext fun z => congrArg ψ (mul_assoc _ _ _)⟩
  obtain ⟨c, hc⟩ : ∃ c : Fin d → ℂ, ∑ i, c i • v i = ψ := (Submodule.mem_span_range_iff_exists_fun ℂ).1
    (hvs ▸ Submodule.subset_span ⟨1, one_mem _, funext fun z => by rw [mul_one]⟩)
  obtain ⟨f, hfA, hf1, hfq⟩ := GlobalTheory.T.stone_weierstrass_finite_rep _ (P ⊓ Kc) hQ d ρ hρ (biFin (goodAlg σ (c₀ • W.J.map σ)) Kc)
    (fun f ⟨V, hV, hf⟩ => (hV.2 f hf).1.1) (fun f ⟨V, hV, hf⟩ => ⟨_, hV.star star_mem_goodAlg, f, hf, rfl⟩)
    (fun x hx y hy hxy => separates hCM hH hKc hx.2 hy.2 hxy)
    (fun f ⟨V, hV, hf⟩ => ⟨V, hV.1, hf, fun w hw => ⟨V, hV, hw⟩, fun w hw q hq => ((hV.2 w hw).2 q hq.2).1⟩) c
  let a : Fin (d + 1) → GAd σ (c₀ • W.J.map σ) → ℂ := Fin.cons 1 fun i => f i - algebraMap ℂ _ (c i)
  have haA : ∀ i, a i ∈ biFin (goodAlg σ (c₀ • W.J.map σ)) Kc := fun i =>
    Fin.cases (one_mem _) (fun i => sub_mem (hfA i) (Subalgebra.algebraMap_mem _ _)) i
  have hsum : ∀ z g, ∑ i, (Fin.cons ψ v : Fin (d + 1) → _ → ℂ) i z * a i g = ∑ i, v i z * f i g := fun z g => by
    rw [Fin.sum_univ_succ, ← hc]
    simp [a, mul_sub, mul_comm]
  obtain ⟨V, hV, haV⟩ := exists_common haA
  haveI := hV.1
  choose Ua hUa hUa' using fun i => (hV.2 _ (haV i)).1.2.2
  let b := Module.finBasis ℂ V
  have hb : ∀ w ∈ V, ∃ c : Fin (Module.finrank ℂ V) → ℂ, ∀ g, w g = ∑ j, c j * (b j).1 g := fun w hw =>
    ⟨b.repr ⟨w, hw⟩, fun g => by
      have := (congrFun (congrArg Subtype.val (b.sum_repr ⟨w, hw⟩)) g).symm
      simpa only [AddSubmonoidClass.coe_finset_sum, Finset.sum_apply, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul] using this⟩
  refine ⟨d, Fin.cons ψ v, a, fun i => Fin.cases hψ hvc i, rfl, fun i => Fin.cases (by simp [a]) (fun i => by simp [a, hf1]) i,
    fun t y p hp k hk k₂ hk₂ k' hk' k₂' hk₂' e z => ?_,
    ⟨⨅ i, Ua i, by rw [Subgroup.coe_iInf]; exact isOpen_iInter_of_finite hUa,
      fun u hu huf k _ k₂ _ i => hUa' i u (Subgroup.mem_iInf.1 hu i) huf _⟩,
    fun i => (hV.2 _ (haV i)).1.1.continuousOn, fun i k _ k₂ _ e γ hγ _ => (hV.2 _ (haV i)).1.2.1 e γ hγ _,
    _, fun j => (b j).1, fun j => (hV.2 _ (b j).2).1.1.continuousOn, fun i => (hb _ (haV i)).imp fun _ h g _ => h g,
    fun j k' hk' => (hb _ ((hV.2 _ (b j).2).2 k' ⟨k', hk', 1, one_mem _, (mul_one _).symm⟩).2).imp fun _ h g _ => h g⟩
  have hpK : p ∈ Kc := by
    rw [eq_mul_inv_of_mul_eq e]
    exact mul_mem ⟨_, hk', _, hk₂', rfl⟩ (inv_mem (show k * k₂ ∈ Kc from ⟨_, hk, _, hk₂, rfl⟩))
  have h1 := law ⟨p, ⟨t, y, hp⟩, hpK⟩ (fun i => f i (k * k₂)) z
  rw [← hfq] at h1
  rw [hsum, hsum, ← e, ← (hu _ _ _ hp).1, ← (hu _ _ _ hp).2]
  exact h1

end GlobalTheory.ThK.InducedCoeff

end
