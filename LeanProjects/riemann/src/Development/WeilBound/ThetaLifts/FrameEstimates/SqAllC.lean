import Development.WeilBound.ThetaLifts.FrameEstimates.SquareIntegrableWeilRange
import Development.WeilBound.ThetaLifts.FrameEstimates.Parity

noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

section

variable {B : Base F E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W}
  {r s r' s' : ℕ}

theorem sq_alg_inj : Function.Injective (algebraMap F (AF F)) := NumberField.AdeleRing.algebraMap_injective (𝓞 F) F

theorem sq_inclR_inj : Function.Injective (inclR (F := F) (E := E) (AF F)) :=
  Algebra.TensorProduct.includeRight_injective (R := F) (A := AF F) (B := E) sq_alg_inj

theorem exists_ratEquiv (hp : IsPair B M χX χW om r s r' s') :
    ∃ e : Matrix (Fin n) (Fin d) E ≃ (Fin n × Fin d → F) × (Fin n × Fin d → F), ∀ x,
      M.co.e (incM F x) = (fun i => algebraMap F (AF F) ((e x).1 i), fun i => algebraMap F (AF F) ((e x).2 i)) := by
  choose y z hyz using hp.good.rat
  have hadd : ∀ a b : Matrix (Fin n) (Fin d) E, incM F (a + b) = incM F a + incM F b := fun a b =>
    Matrix.ext fun i j => map_add (inclR (F := F) (AF F)) _ _
  have hsm : ∀ (c : F) (a : Matrix (Fin n) (Fin d) E), incM F (c • a) = algebraMap F (AF F) c • incM F a := fun c a =>
    Matrix.ext fun i j => by
      change (1 : AF F) ⊗ₜ[F] (c • a i j) = algebraMap F (AF F) c • ((1 : AF F) ⊗ₜ[F] a i j)
      rw [TensorProduct.tmul_smul, algebraMap_smul]
  let l : Matrix (Fin n) (Fin d) E →ₗ[F] (Fin n × Fin d → F) × (Fin n × Fin d → F) :=
    { toFun := fun x => (y x, z x)
      map_add' := fun a b => by
        have h := hyz (a + b)
        rw [hadd, map_add, hyz a, hyz b] at h
        refine Prod.ext (funext fun i => sq_alg_inj ?_) (funext fun i => sq_alg_inj ?_)
        · exact (congrFun (congrArg Prod.fst h) i).symm.trans (map_add _ _ _).symm
        · exact (congrFun (congrArg Prod.snd h) i).symm.trans (map_add _ _ _).symm
      map_smul' := fun c a => by
        have h := hyz (c • a)
        rw [hsm, map_smul, hyz a] at h
        refine Prod.ext (funext fun i => sq_alg_inj ?_) (funext fun i => sq_alg_inj ?_)
        · exact (congrFun (congrArg Prod.fst h) i).symm.trans (map_mul _ _ _).symm
        · exact (congrFun (congrArg Prod.snd h) i).symm.trans (map_mul _ _ _).symm }
  have hinj : Function.Injective l := fun a b hab => by
    have h1 : y a = y b := congrArg Prod.fst hab
    have h2 : z a = z b := congrArg Prod.snd hab
    have h3 : incM F a = incM F b := M.co.e.injective (by rw [hyz a, hyz b, h1, h2])
    exact Matrix.ext fun i j => sq_inclR_inj (congrFun (congrFun h3 i) j)
  have h2 : Module.finrank F E = 2 := hp.base.cm.2.2.1
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  have hdim : Module.finrank F (Matrix (Fin n) (Fin d) E) =
      Module.finrank F ((Fin n × Fin d → F) × (Fin n × Fin d → F)) := by
    rw [Module.finrank_matrix, h2]
    simp
    ring
  exact ⟨Equiv.ofBijective l ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).1 hinj⟩, hyz⟩

theorem theta_mul_le (hS : CoefSum) (hE : CoefEq) (hp : IsPair B M χX χW om r s r' s') (μ : Measure (Fin n × Fin d → AF F))
    (hμ : μ.IsAddHaarMeasure) : ∃ c : ℝ, 0 < c ∧ ∀ Φ₁ ∈ schA F (Fin n × Fin d), ∀ Φ₂ ∈ schA F (Fin n × Fin d), ∀ g h,
      ‖theta om Φ₁ g h‖ₑ * ‖theta om Φ₂ g h‖ₑ ≤ ENNReal.ofReal c * ∑' x : Matrix (Fin n) (Fin d) E,
        ‖coef F B.ψ μ Φ₁ Φ₂ (M.co.e (mat g⁻¹ * incM F x * (mat h⁻¹)ᵀ))‖ₑ := by
  obtain ⟨c, hc, h1⟩ := hS F _ B.ψ hp.base.std μ hμ
  obtain ⟨e, he⟩ := exists_ratEquiv hp
  refine ⟨c, hc, fun Φ₁ h₁ Φ₂ h₂ g h => ?_⟩
  have hs := (IsUWeilPair.isUSplitting hp.weil).pres (g, h)
  refine (h1 _ (hs _ h₁) _ (hs _ h₂)).trans (le_of_eq ?_)
  rw [← e.tsum_eq]
  congr 1
  refine tsum_congr fun x => ?_
  rw [← he x, hE F E σ B n d X W M χX χW om r s r' s' hp μ hμ Φ₁ h₁ Φ₂ h₂ g h]

theorem sq_maj_nonneg (τ : ∀ w : InfinitePlace F, EmbOver E w) (C : Set (Ten F E n d)) (N : ℕ) (z : Ten F E n d) :
    0 ≤ maj τ C N z := by
  unfold maj sz
  split_ifs
  · positivity
  · exact le_rfl

theorem sq_le_of_coef {c a : ℝ} (hc : 0 < c) (ha : 0 ≤ a) {t : ℝ≥0∞} {S : Set (Matrix (Fin n) (Fin d) E)}
    {u : Matrix (Fin n) (Fin d) E → ℂ} {C : Set (Ten F E n d)} {N : ℕ} {g : UA σ X.J} {h : UA σ W.J}
    (h1 : t * t ≤ ENNReal.ofReal c * ∑' x, ‖u x‖ₑ) (h0 : ∀ x ∉ S, u x = 0)
    (h2 : ∀ x, ‖u x‖ ≤ a * a * maj B.emb C N (mat g⁻¹ * incM F x * (mat h⁻¹)ᵀ)) :
    t ^ 2 ≤ ENNReal.ofReal (√c * a) ^ 2 * latSum B.emb C N S g h := by
  rw [sq]
  refine h1.trans ?_
  have e : ∑' x, ‖u x‖ₑ = ∑' x : S, ‖u x.1‖ₑ := by
    refine (tsum_subtype_eq_of_support_subset (f := fun x => ‖u x‖ₑ) fun x hx => ?_).symm
    by_contra hn
    exact hx (by simp [h0 x hn])
  rw [e, ← ENNReal.ofReal_pow (by positivity), mul_pow, Real.sq_sqrt hc.le, ENNReal.ofReal_mul hc.le, mul_assoc, latSum]
  refine mul_le_mul_right ?_ _
  rw [← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun x => ?_
  rw [← ofReal_norm, ← ENNReal.ofReal_mul (by positivity), sq]
  exact ENNReal.ofReal_le_ofReal (h2 x.1)

end

theorem sqAll_of' (hS : CoefSum) (hE : CoefEq) (hB : CoefBd) : SqAll := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp φ hφ N
  obtain ⟨μ, hμ, -⟩ := ParityOfCoefficients.exists_haar (F := F) (κ := Fin n × Fin d)
  obtain ⟨c, hc, h1⟩ := theta_mul_le hS hE hp μ hμ
  obtain ⟨p, C, hpc, hC, h2⟩ := hB F E σ B n d X W M χX χW om r s r' s' hp μ hμ φ hφ φ hφ N
  refine ⟨NNReal.mk √c (Real.sqrt_nonneg c) • p, C, (continuous_const.mul hpc : Continuous fun f => √c * p f), hC,
    fun f g h => ?_⟩
  have hm : pureA F f φ ∈ schA F (Fin n × Fin d) := Submodule.subset_span ⟨f, φ, hφ, rfl⟩
  exact sq_le_of_coef hc (apply_nonneg p f) (h1 _ hm _ hm g h) (fun x hx => absurd (Set.mem_univ x) hx) fun x => h2 f f _

end PositivityTheory.ThKEst

end
