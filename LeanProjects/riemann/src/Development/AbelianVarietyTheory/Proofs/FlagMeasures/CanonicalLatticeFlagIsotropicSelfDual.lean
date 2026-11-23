import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Formalism.HarderNarasimhan.ShiftInvariance
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointLatticeIntersectionSelfDualPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CanonicalLatticeFiltrationSizePropertiesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrthogonalCanonicalFiltrationStepsAutPointStatement

open GlobalTheory.Count Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField MeasureTheory Finset

noncomputable section

namespace GlobalTheory.FlagIso

theorem exists_extension {O K V : Type} [CommRing O] [IsDedekindDomain O] [Field K] [Algebra O K]
    [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
    (Λ P : Submodule O V) (hfg : Λ.FG) (hspan : Submodule.span K (Λ : Set V) = ⊤)
    (hsat : ∀ c : O, c ≠ 0 → ∀ v ∈ Λ, c • v ∈ P → v ∈ P) (f : V →ₗ[K] K)
    (hf : ∀ z ∈ P, f z ∈ (algebraMap O K).range) :
    ∃ g : V →ₗ[K] K, (∀ z ∈ Λ, g z ∈ (algebraMap O K).range) ∧ ∀ z ∈ Λ, z ∈ P → g z = f z := by
  have hloc : IsLocalizedModule (nonZeroDivisors O) Λ.subtype :=
    { map_units := fun s => by
        have := isLocalizedModule_id (nonZeroDivisors O) V K
        exact IsLocalizedModule.map_units (S := nonZeroDivisors O) (LinearMap.id : V →ₗ[O] V) s
      surj := fun y => by
        have hy : y ∈ Submodule.span K (Λ : Set V) := by rw [hspan]; trivial
        obtain ⟨s, hs⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors O) K (Λ : Set V) y hy
        rw [Submodule.span_eq] at hs
        exact ⟨(⟨_, hs⟩, s), rfl⟩
      exists_of_eq := fun h => ⟨1, by rw [Subtype.ext h]⟩ }
  have : Module.Finite O Λ := Module.Finite.iff_fg.2 hfg
  let Q : Submodule O Λ := P.comap Λ.subtype
  have : Module.Flat O (Λ ⧸ Q) := by
    rw [IsDedekindDomain.flat_iff_torsion_eq_bot, eq_bot_iff]
    intro q hq
    obtain ⟨v, rfl⟩ := Q.mkQ_surjective q
    obtain ⟨c, hc⟩ := hq
    have h1 : Q.mkQ ((c : O) • v) = 0 := by rw [map_smul]; exact hc
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h1
    rw [Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hsat c (nonZeroDivisors.coe_ne_zero c) v v.2 h1
  have : Module.FinitePresentation O (Λ ⧸ Q) := Module.finitePresentation_of_finite _ _
  have : Module.Projective O (Λ ⧸ Q) := Module.Flat.projective_of_finitePresentation
  obtain ⟨s, hs⟩ := Module.projective_lifting_property Q.mkQ LinearMap.id Q.mkQ_surjective
  let π : Λ →ₗ[O] Λ := LinearMap.id - s ∘ₗ Q.mkQ
  have hπ : ∀ v, π v ∈ Q := by
    intro v
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply]
    have h1 : Q.mkQ (s (Q.mkQ v)) = Q.mkQ v := LinearMap.congr_fun hs _
    simp only [π, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, map_sub, h1, sub_self]
  have hπ' : ∀ v ∈ Q, π v = v := by
    intro v hv
    have h1 : Q.mkQ v = 0 := by rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    simp only [π, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, h1, map_zero, sub_zero]
  have hu : ∀ x : nonZeroDivisors O, IsUnit (algebraMap O (Module.End O K) x) :=
    fun x => IsLocalizedModule.map_units (S := nonZeroDivisors O) (Algebra.linearMap O K) x
  let g : V →ₗ[K] K := LinearMap.extendScalarsOfIsLocalization (nonZeroDivisors O) K
      (IsLocalizedModule.lift (nonZeroDivisors O) Λ.subtype
        (f.restrictScalars O ∘ₗ Λ.subtype ∘ₗ π) hu)
  have hg : ∀ y : Λ, g y = f (π y) := fun y =>
    IsLocalizedModule.lift_apply (nonZeroDivisors O) Λ.subtype _ hu y
  refine ⟨g, fun z hz => ?_, fun z hz hP => ?_⟩
  · rw [hg ⟨z, hz⟩]
    exact hf _ (hπ _)
  · rw [hg ⟨z, hz⟩, hπ' ⟨z, hz⟩ hP]

section Form

variable {E : Type} [Field E] [StarRing E] {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

def hR (x : Fin n → E) : (Fin n → E) →ₗ[E] E where
  toFun y := Formalism.UG.hform (starRingEnd E) J x y
  map_add' y z := by simp only [Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c y := by
    simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hR_apply (x y : Fin n → E) : hR J x y = Formalism.UG.hform (starRingEnd E) J x y := rfl

theorem hform_star (hJ : Formalism.UG.IsHerm (starRingEnd E) J) (x y : Fin n → E) :
    star (Formalism.UG.hform (starRingEnd E) J x y) = Formalism.UG.hform (starRingEnd E) J y x := by
  have h : ∀ i j, star (J i j) = J j i := fun i j => by
    have := congrFun (congrFun hJ j) i
    exact this
  simp only [Formalism.UG.hform, star_sum, star_mul', starRingEnd_apply, star_star, h]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem exists_hR_eq (hJ : J.det ≠ 0) (g : (Fin n → E) →ₗ[E] E) : ∃ y, hR J y = g := by
  refine ⟨star ((fun j => g (Pi.single j 1)) ᵥ* J⁻¹), ?_⟩
  ext j
  have h1 : ((fun j => g (Pi.single j 1)) ᵥ* J⁻¹) ᵥ* J = fun j => g (Pi.single j 1) := by
    rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ (Ne.isUnit hJ), Matrix.vecMul_one]
  have h2 := congrFun h1 j
  simp only [LinearMap.comp_apply, LinearMap.single_apply, hR_apply]
  rw [← h2]
  simp only [Formalism.UG.hform, starRingEnd_apply, Pi.star_apply, star_star]
  simp [Pi.single_apply, Matrix.vecMul, dotProduct]

end Form

theorem star_mem_range {E : Type} [Field E] [StarRing E] {a : E}
    (h : a ∈ (algebraMap (𝓞 E) E).range) : star a ∈ (algebraMap (𝓞 E) E).range := by
  obtain ⟨b, rfl⟩ := h
  exact ⟨⟨_, map_isIntegral_int (starRingEnd E) b.isIntegral_coe⟩, rfl⟩

theorem card_le_of_isotropic {n k : ℕ} (ε : Fin n → Bool) (u : Fin k → Fin n → ℂ)
    (hu : LinearIndependent ℂ u) (hiso : ∀ i j, star (u i) ⬝ᵥ (Jm ε *ᵥ u j) = 0) (b : Bool) :
    k ≤ (univ.filter fun a => ε a = b).card := by
  let T : (Fin k → ℂ) →ₗ[ℂ] ({a // ε a = b} → ℂ) :=
    LinearMap.funLeft ℂ ℂ Subtype.val ∘ₗ Fintype.linearCombination ℂ u
  have hT : Function.Injective T := by
    rw [injective_iff_map_eq_zero]
    intro c hc
    have h0 : star (∑ i, c i • u i) ⬝ᵥ (Jm ε *ᵥ ∑ i, c i • u i) = 0 := by
      simp only [star_sum, star_smul, sum_dotProduct, Matrix.mulVec_sum, dotProduct_sum, Matrix.mulVec_smul,
        smul_dotProduct, dotProduct_smul, hiso, smul_zero, Finset.sum_const_zero]
    have h1 : ∀ a, ε a = b → (∑ i, c i • u i) a = 0 := fun a ha => congrFun hc ⟨a, ha⟩
    have h3 : ∑ i, c i • u i = 0 := by
      generalize ∑ i, c i • u i = w at h0 h1
      have h2 : star w ⬝ᵥ (Jm ε *ᵥ w) = (if b then -1 else 1) * (star w ⬝ᵥ w) := by
        simp only [dotProduct, Jm, Matrix.mulVec_diagonal, Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        by_cases ha : ε a = b
        · simp [h1 a ha]
        · cases b <;> simp_all
      rw [h2] at h0
      have h4 : star w ⬝ᵥ w = 0 := by cases b <;> simpa using h0
      open ComplexOrder in exact dotProduct_star_self_eq_zero.1 h4
    funext i
    exact Fintype.linearIndependent_iff.1 hu c h3 i
  have := LinearMap.finrank_le_finrank_of_injective hT
  simpa [Fintype.card_subtype] using this

variable (I : AutInst)

theorem rkK_le_rkR (S : Submodule (𝓞 I.E) (Fin I.n → I.E))
    (hS : ∀ y ∈ S, ∀ z ∈ S, Formalism.UG.hform (starRingEnd I.E) I.J y z = 0) (v : InfinitePlace I.F) :
    rkK S ≤ rkR (I.ε v) := by
  obtain ⟨b, hbS, -, hb⟩ := Submodule.exists_fun_fin_finrank_span_eq I.E (S : Set (Fin I.n → I.E))
  letI : Algebra I.E ℂ := (I.φ v).toAlgebra
  have h1 : LinearIndependent ℂ (fun i => (I.φ v) ∘ b i) :=
    (linearIndependent_algebraMap_comp_iff (S := ℂ)).2 hb
  have hP : IsUnit (I.P v).det := (Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v)
  have hPi : ∀ w : Fin I.n → ℂ, I.P v *ᵥ ((I.P v)⁻¹ *ᵥ w) = w := fun w => by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hP, Matrix.one_mulVec]
  have h2 : LinearIndependent ℂ (fun i => (I.P v)⁻¹ *ᵥ ((I.φ v) ∘ b i)) := by
    apply LinearIndependent.of_comp (Matrix.mulVecLin (I.P v))
    simpa [Function.comp_def, hPi] using h1
  have h3 : ∀ i j, star ((I.P v)⁻¹ *ᵥ ((I.φ v) ∘ b i)) ⬝ᵥ
      (Jm (I.ε v) *ᵥ ((I.P v)⁻¹ *ᵥ ((I.φ v) ∘ b j))) = 0 := by
    intro i j
    rw [← I.P_spec v, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hPi, Matrix.dotProduct_mulVec,
      ← Matrix.star_mulVec, hPi]
    have h4 := congrArg (I.φ v) (hS _ (hbS i) _ (hbS j))
    rw [map_zero] at h4
    rw [← h4]
    simp only [Formalism.UG.hform, map_sum, map_mul, starRingEnd_apply, I.cm.cmUnram.2.1, dotProduct,
      Matrix.mulVec, Finset.mul_sum, mul_assoc, Pi.star_apply, Function.comp_apply, Matrix.map_apply]
  exact le_min (card_le_of_isotropic _ _ h2 h3 true) (card_le_of_isotropic _ _ h2 h3 false)

theorem mem_perpIn (x : I.GA) (S : Submodule (𝓞 I.E) (Fin I.n → I.E)) (y : Fin I.n → I.E) :
    y ∈ perpIn I x S ↔ y ∈ lamX I x ∧ ∀ s ∈ S, Formalism.UG.hform (starRingEnd I.E) I.J s y = 0 := by
  refine ⟨fun h => ?_, fun h => Submodule.subset_span h⟩
  induction h using Submodule.span_induction with
  | mem y hy => exact hy
  | zero => exact ⟨zero_mem _, fun s _ => map_zero (hR I.J s)⟩
  | add y z _ _ hy hz =>
    exact ⟨add_mem hy.1 hz.1, fun s hs => by
      rw [← hR_apply, map_add, hR_apply, hR_apply, hy.2 s hs, hz.2 s hs, add_zero]⟩
  | smul c y _ hy =>
    exact ⟨Submodule.smul_mem _ _ hy.1, fun s hs => by
      rw [← hR_apply, LinearMap.map_smul_of_tower, hR_apply, hy.2 s hs, smul_zero]⟩

theorem hform_span (x : I.GA) (S : Submodule (𝓞 I.E) (Fin I.n → I.E)) {y s : Fin I.n → I.E}
    (hy : y ∈ Submodule.span I.E (perpIn I x S : Set (Fin I.n → I.E))) (hs : s ∈ S) :
    Formalism.UG.hform (starRingEnd I.E) I.J s y = 0 := by
  have : Submodule.span I.E (perpIn I x S : Set (Fin I.n → I.E)) ≤ LinearMap.ker (hR I.J s) :=
    Submodule.span_le.2 fun z hz => ((mem_perpIn I x S z).1 hz).2 s hs
  exact this hy

theorem flag_isotropic : ∀ (I : AutInst) (x : I.GA), (∀ y ∈ stepLt I x (1 / 2), ∀ z ∈ stepLt I x (1 / 2), Formalism.UG.hform (starRingEnd I.E) I.J y z = 0) ∧ (∀ v, rkK (stepLt I x (1 / 2)) ≤ rkR (I.ε v)) ∧ ∀ R : Submodule (𝓞 I.E) (Fin I.n → I.E), IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (lamX I x) R → R ≤ perpIn I x R → ∀ y ∈ Submodule.span I.E (perpIn I x R : Set (Fin I.n → I.E)), (∀ z ∈ perpIn I x R, Formalism.UG.hform (starRingEnd I.E) I.J z y ∈ (algebraMap (𝓞 I.E) I.E).range) → ∃ y' ∈ perpIn I x R, y - y' ∈ Submodule.span I.E (R : Set (Fin I.n → I.E)) := by
  intro I x
  obtain ⟨-, -, hd1, hd2⟩ := GlobalTheory.T.orthogonal_canonicalFiltration_steps_autPoint I x
  obtain ⟨-, hfg, hspan, hdual, -⟩ := GlobalTheory.T.autPointLatticeIntersection_selfDual_properties I x
  have hiso : ∀ y ∈ stepLt I x (1 / 2), ∀ z ∈ stepLt I x (1 / 2),
      Formalism.UG.hform (starRingEnd I.E) I.J y z = 0 := by
    intro y hy z hz
    obtain ⟨-, -, h1, h2, -⟩ := GlobalTheory.T.canonicalLatticeFiltration_size_properties I x (1 / 2) (by norm_num)
    obtain ⟨-, -, h3, -⟩ := GlobalTheory.T.canonicalLatticeFiltration_size_properties I x (1 / 2)⁻¹ (by norm_num)
    have h4 := h3 (h2 (1 / 2)⁻¹ (by norm_num) (h1 hz))
    rw [← (hd1 (1 / 2) (by norm_num)).2] at h4
    exact ((mem_perpIn I x _ z).1 h4).2 y hy
  refine ⟨hiso, rkK_le_rkR I _ hiso, fun R hR hRR y hy hint => ?_⟩
  obtain ⟨-, -, hpp, -⟩ := hd2 R R hR hR le_rfl
  obtain ⟨g, hg, hgf⟩ := exists_extension (lamX I x) (perpIn I x R) hfg hspan
    (fun c hc v hv h => by
      refine (mem_perpIn I x R v).2 ⟨hv, fun s hs => ?_⟩
      have h1 := ((mem_perpIn I x R _).1 h).2 s hs
      rw [← hR_apply, LinearMap.map_smul_of_tower] at h1
      exact (smul_eq_zero.1 h1).resolve_left hc)
    (FlagIso.hR I.J y) (fun z hz => by
      rw [hR_apply, ← hform_star _ I.J_herm]
      exact star_mem_range (hint z hz))
  obtain ⟨y', rfl⟩ := exists_hR_eq I.J I.J_det g
  have hy' : y' ∈ lamX I x := (hdual y').2 fun z hz => by
    rw [← hform_star _ I.J_herm]
    exact star_mem_range (hg z hz)
  have heq : ∀ z ∈ perpIn I x R, Formalism.UG.hform (starRingEnd I.E) I.J z y' =
      Formalism.UG.hform (starRingEnd I.E) I.J z y := fun z hz => by
    rw [← hform_star _ I.J_herm, ← hform_star _ I.J_herm y]
    exact congrArg star (hgf z ((mem_perpIn I x R z).1 hz).1 hz)
  refine ⟨y', (mem_perpIn I x R y').2 ⟨hy', fun s hs => ?_⟩, ?_⟩
  · rw [heq s (hRR hs)]
    exact hform_span I x R hy hs
  · have h1 : y - y' ∈ Submodule.span I.E (lamX I x : Set (Fin I.n → I.E)) := by rw [hspan]; trivial
    obtain ⟨c, hc⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 I.E)) I.E _ _ h1
    rw [Submodule.span_eq] at hc
    have hc' : (c : 𝓞 I.E) • (y - y') ∈ lamX I x := hc
    have h2 : (c : 𝓞 I.E) • (y - y') ∈ R := by
      rw [← hpp]
      refine (mem_perpIn I x _ _).2 ⟨hc', fun s hs => ?_⟩
      rw [← hR_apply, LinearMap.map_smul_of_tower, map_sub, hR_apply, hR_apply, heq s hs, sub_self, smul_zero]
    have hc0 : algebraMap (𝓞 I.E) I.E c ≠ 0 := by
      simpa using nonZeroDivisors.coe_ne_zero c
    have h3 := Submodule.smul_mem (Submodule.span I.E (R : Set (Fin I.n → I.E)))
      (algebraMap (𝓞 I.E) I.E c)⁻¹ (Submodule.subset_span h2)
    rwa [← algebraMap_smul I.E (c : 𝓞 I.E), smul_smul, inv_mul_cancel₀ hc0, one_smul] at h3

end GlobalTheory.FlagIso
