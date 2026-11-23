import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.MarkSpec
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Formalism.LocalToGlobal.ProjectiveLattices.ComponentWModel
import Formalism.LocalToGlobal.ProjectiveLattices.NormLaws
import Formalism.LocalToGlobal.ProjectiveLattices.VolProofs
import Formalism.LocalToGlobal.ProjectiveLattices.DatProofs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CramerMemAdelicCompletionOfElementSet
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct Topology
open GlobalTheory.RecDict

namespace GlobalTheory.RecDict

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem det_gram_ne_zero {E : Type} [Field E] [NumberField E] [StarRing E] (S : Formalism.BasicNotions.HSpace E) :
    S.gram.det ≠ 0 := by
  intro h
  obtain ⟨v, hv, h0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  apply hv
  have hy : S.frame.equivFun.symm v = 0 := by
    apply S.nondeg.2
    intro x
    have hi : ∀ i, S.hT (S.frame i) (S.frame.equivFun.symm v) = 0 := by
      intro i
      have := congrFun h0 i
      rw [Module.Basis.equivFun_symm_apply, map_sum]
      simpa [Matrix.mulVec, dotProduct, Formalism.BasicNotions.HSpace.gram, mul_comm] using this
    rw [← S.frame.sum_repr x, map_sum, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, hi, smul_zero]
  exact S.frame.equivFun.symm.map_eq_zero_iff.1 hy

theorem det_mul_sigR_det {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (hJ : J.det ≠ 0) (g : GL (Fin M) (R ⊗[F] E))
    (hg : g ∈ HR R σ J) : g.1.det * sigR R σ g.1.det = 1 := by
  have h : Formalism.UG.cT (sigR R σ) g.1 * JR R J * g.1 = JR R J := hg
  have h2 := congrArg Matrix.det h
  have hu : IsUnit (JR (F := F) R J).det := by
    have : (JR (F := F) R J).det = inclR (F := F) R J.det := ((inclR (F := F) R).map_det J).symm
    rw [this]
    exact (IsUnit.mk0 _ hJ).map _
  have h3 : (Formalism.UG.cT (sigR R σ) g.1).det = sigR R σ g.1.det := by
    rw [Formalism.UG.cT, Matrix.det_transpose]
    exact ((sigR R σ).map_det g.1).symm
  rw [Matrix.det_mul, Matrix.det_mul, h3] at h2
  apply hu.mul_left_cancel
  linear_combination h2

theorem det_finHom_norm {D : D7} (V : HSp D) (k : GA D V) :
    (finHom V k).1.det * sigR (Af D.host.F) D.sp.cm.sig (finHom V k).1.det = 1 := by
  have h := det_mul_sigR_det (AF D.host.F) D.sp.cm.sig V.gram (det_gram_ne_zero V) (matHom V k) k.2
  let φ := (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom
  have e : (finHom V k).1.det = φ (matHom V k).1.det := (φ.map_det _).symm
  have c : ∀ x, sigR (Af D.host.F) D.sp.cm.sig (φ x) = φ (sigR (AF D.host.F) D.sp.cm.sig x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [φ, sigR]
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [e, c, ← map_mul, h, map_one]

theorem finHom_inv_mulVec_mem {D : D7} (V : HSp D) (k : GA D V)
    (hk : ∀ z ∈ latHat V, (finHom V k).1.mulVec z ∈ latHat V) :
    ∀ z ∈ latHat V, (finHom V k⁻¹).1.mulVec z ∈ latHat V := by
  let L : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) :=
    V.L0.map (V.frame.equivFun.toLinearMap.restrictScalars (𝓞 D.host.E))
  have hL : latHat V = GlobalTheory.AdLat.hat D.host.F (L : Set (Fin V.rank → D.host.E)) := by
    unfold Formalism.L2.Pj.latHat GlobalTheory.AdLat.hat
    congr 1
    ext z
    constructor
    · rintro ⟨a, ha, x, hx, rfl⟩
      exact ⟨a, ha, _, ⟨x, hx, rfl⟩, rfl⟩
    · rintro ⟨a, ha, _, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨a, ha, x, hx, rfl⟩
  have hfg : L.FG := V.standardTuple_isLattice.fg.map _
  have hsp : Submodule.span D.host.E (L : Set (Fin V.rank → D.host.E)) = ⊤ := by
    have : (L : Set (Fin V.rank → D.host.E)) = V.frame.equivFun.toLinearMap '' (V.L0 : Set V.V) := rfl
    rw [this, Submodule.span_image, V.standardTuple_isLattice.span_eq_top, Submodule.map_top, LinearEquiv.range]
  let c : D.host.E ≃ₐ[D.host.F] D.host.E :=
    AlgEquiv.ofBijective D.sp.cm.sig (D.sp.cm.sig.bijective)
  rw [hL] at hk ⊢
  rw [map_inv]
  exact GlobalTheory.AdLat.inv_mulVec_mem_hat _ _ _ L (finHom V k) c hfg hsp hk (det_finHom_norm V k)

theorem exists_level_subgroup {G A : Type} [Group G] [CommRing A] {n : ℕ} (f : G →* GL (Fin n) A) (H : Subgroup G)
    (Λ : AddSubgroup (Fin n → A)) (N : ℕ)
    (hinv : ∀ k : G, (∀ z ∈ Λ, (f k).1.mulVec z ∈ Λ) → ∀ z ∈ Λ, (f k⁻¹).1.mulVec z ∈ Λ) :
    ∃ K : Subgroup G, (∀ k, k ∈ K ↔ k ∈ H ∧ ∀ z ∈ Λ, ∃ y ∈ Λ, (f k).1.mulVec z - z = N • y) ∧
      ∀ k ∈ K, (f k).1.mulVec '' (Λ : Set (Fin n → A)) = Λ := by
  have hin : ∀ k : G, (∀ z ∈ Λ, ∃ y ∈ Λ, (f k).1.mulVec z - z = N • y) →
      ∀ z ∈ Λ, (f k).1.mulVec z ∈ Λ := by
    intro k hk z hz
    obtain ⟨y, hy, e⟩ := hk z hz
    rw [sub_eq_iff_eq_add.1 e]
    exact add_mem (nsmul_mem hy N) hz
  have hmul : ∀ (a b : G) z, (f (a * b)).1.mulVec z = (f a).1.mulVec ((f b).1.mulVec z) := by
    intro a b z
    rw [map_mul, Units.val_mul, Matrix.mulVec_mulVec]
  have hone : ∀ z, (f 1).1.mulVec z = z := by
    intro z
    rw [map_one, Units.val_one, Matrix.one_mulVec]
  refine ⟨{ carrier := {k | k ∈ H ∧ ∀ z ∈ Λ, ∃ y ∈ Λ, (f k).1.mulVec z - z = N • y}
            mul_mem' := ?_
            one_mem' := ?_
            inv_mem' := ?_ }, fun k => Iff.rfl, ?_⟩
  · rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨mul_mem ha hb, fun z hz => ?_⟩
    obtain ⟨y, hy, e⟩ := hb' z hz
    obtain ⟨y', hy', e'⟩ := ha' _ (hin b hb' z hz)
    refine ⟨y' + y, add_mem hy' hy, ?_⟩
    rw [hmul, nsmul_add, ← e, ← e']
    abel
  · exact ⟨one_mem _, fun z _ => ⟨0, zero_mem _, by rw [hone, sub_self, nsmul_zero]⟩⟩
  · rintro a ⟨ha, ha'⟩
    refine ⟨inv_mem ha, fun z hz => ?_⟩
    obtain ⟨y, hy, e⟩ := ha' _ (hinv a (hin a ha') z hz)
    refine ⟨-y, neg_mem hy, ?_⟩
    rw [← hmul, mul_inv_cancel, hone] at e
    rw [neg_nsmul, ← e, neg_sub]
  · rintro k ⟨-, hk⟩
    apply Set.Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩
      exact hin k hk z hz
    · intro z hz
      exact ⟨_, hinv k (hin k hk) z hz, (hmul k k⁻¹ z).symm.trans (by rw [mul_inv_cancel, hone])⟩

theorem exists_isLevelK : ∀ (D : D7) (V : HSp D) (N : ℕ), ∃ Kf : Subgroup (GA D V), IsLevelK V N Kf ∧ ∀ k ∈ Kf, (finHom V k).1.mulVec '' (latHat V : Set _) = latHat V :=
  fun _ V N => exists_level_subgroup (finHom V) (GfC V) (latHat V) N (finHom_inv_mulVec_mem V)

end GlobalTheory.RecDict
