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
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenNsmulAdelicCompletionOfVectorSet
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct Topology
open GlobalTheory.RecDict

namespace GlobalTheory.LevelOpen

theorem exists_cut {A : Type} [CommRing A] {n : ℕ} (σ : A →+* A) (J : Matrix (Fin n) (Fin n) A) (e : A)
    (he : e * e = e) (hσ : σ e = e) (g : GL (Fin n) A) (hg : g ∈ Formalism.UG.UJ σ J) :
    ∃ k ∈ Formalism.UG.UJ σ J, k.1 = e • g.1 + (1 - e) • (1 : Matrix (Fin n) (Fin n) A) := by
  have h1 : e * (1 - e) = 0 := by rw [mul_sub, he, mul_one, sub_self]
  have h2 : (1 - e) * e = 0 := by rw [mul_comm, h1]
  have h3 : (1 - e) * (1 - e) = 1 - e := by rw [sub_mul, h1, one_mul, sub_zero]
  have key : ∀ X Y Z W : Matrix (Fin n) (Fin n) A,
      (e • X + (1 - e) • Z) * (e • Y + (1 - e) • W) = e • (X * Y) + (1 - e) • (Z * W) := by
    intro X Y Z W
    simp only [add_mul, mul_add, smul_mul_smul_comm, he, h1, h2, h3, zero_smul, add_zero, zero_add]
  have one : ∀ X : Matrix (Fin n) (Fin n) A, e • X + (1 - e) • X = X := by
    intro X; rw [← add_smul, add_sub_cancel, one_smul]
  refine ⟨⟨e • g.1 + (1 - e) • 1, e • (g⁻¹).1 + (1 - e) • 1, ?_, ?_⟩, ?_, rfl⟩
  · rw [key, Units.mul_inv, one_mul, one]
  · rw [key, Units.inv_mul, one_mul, one]
  · have hg' : Formalism.UG.cT σ g.1 * J * g.1 = J := hg
    change Formalism.UG.cT σ (e • g.1 + (1 - e) • 1) * J * (e • g.1 + (1 - e) • 1) = J
    have hc : Formalism.UG.cT σ (e • g.1 + (1 - e) • (1 : Matrix (Fin n) (Fin n) A)) =
        e • Formalism.UG.cT σ g.1 + (1 - e) • 1 := by
      ext i j
      by_cases h : i = j
      · subst h; simp [Formalism.UG.cT, hσ]
      · simp [Formalism.UG.cT, hσ, Matrix.one_apply_ne h, Matrix.one_apply_ne (Ne.symm h)]
    rw [hc]
    conv_lhs => rw [← one J]
    rw [key, key, hg', one_mul, mul_one, one]

theorem congr_mem_nhds (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
    (L : Submodule (𝓞 E) (Fin n → E)) (hfg : L.FG) (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤)
    (N : ℕ) (hN : 0 < N) :
    {m : Matrix (Fin n) (Fin n) (Af F ⊗[F] E) | ∀ z ∈ GlobalTheory.AdLat.hat F (L : Set (Fin n → E)),
      ∃ y ∈ GlobalTheory.AdLat.hat F (L : Set (Fin n → E)), m.mulVec z - z = N • y} ∈
      𝓝 (1 : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) := by
  have : IsModuleTopology (Af F) (Af F ⊗[F] E) := ⟨rfl⟩
  have : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have : IsTopologicalRing (Af F ⊗[F] E) := IsModuleTopology.isTopologicalRing (Af F) _
  have ho : IsOpen {z : Fin n → Af F ⊗[F] E | ∃ y ∈ GlobalTheory.AdLat.hat F (L : Set (Fin n → E)), z = N • y} :=
    (GlobalTheory.AdLat.OpenLat.isOpen_nsmul_hat F E n L hL).1 N hN
  have hfz : (L.restrictScalars ℤ).FG := by
    have : Module.Finite (𝓞 E) L := Module.Finite.iff_fg.mpr hfg
    have : Module.Finite ℤ L := Module.Finite.trans (𝓞 E) L
    exact (Module.Finite.iff_fg (N := L.restrictScalars ℤ)).mp (inferInstanceAs (Module.Finite ℤ L))
  obtain ⟨s, hs⟩ := hfz
  have hev : ∀ᶠ m : Matrix (Fin n) (Fin n) (Af F ⊗[F] E) in 𝓝 1, ∀ x ∈ s,
      ∃ y ∈ GlobalTheory.AdLat.hat F (L : Set (Fin n → E)),
        m.mulVec (GlobalTheory.AdLat.fv F x) - GlobalTheory.AdLat.fv F x = N • y := by
    rw [Filter.eventually_all_finset]
    intro x _
    have hc : Continuous fun m : Matrix (Fin n) (Fin n) (Af F ⊗[F] E) =>
        m.mulVec (GlobalTheory.AdLat.fv F x) - GlobalTheory.AdLat.fv F x :=
      (continuous_id.matrix_mulVec continuous_const).sub continuous_const
    exact (ho.preimage hc).mem_nhds ⟨0, zero_mem _, by simp⟩
  refine Filter.mem_of_superset hev fun m hm => ?_
  have hsm : ∀ a : Af F, (∀ v, a v ∈ v.adicCompletionIntegers F) →
      ∀ y ∈ GlobalTheory.AdLat.hat F (L : Set (Fin n → E)), a • y ∈ GlobalTheory.AdLat.hat F (L : Set (Fin n → E)) := by
    intro a ha y hy
    induction hy using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨b, hb, x, hx, rfl⟩ := hx
      exact AddSubgroup.subset_closure ⟨a * b, fun v => mul_mem (ha v) (hb v), x, hx, rfl⟩
    | zero => rw [smul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
    | neg x _ hx => rw [smul_neg]; exact neg_mem hx
  have hadd : ∀ z w : Fin n → Af F ⊗[F] E,
      (∃ y ∈ GlobalTheory.AdLat.hat F (L : Set (Fin n → E)), m.mulVec z - z = N • y) →
      (∃ y ∈ GlobalTheory.AdLat.hat F (L : Set (Fin n → E)), m.mulVec w - w = N • y) →
      ∃ y ∈ GlobalTheory.AdLat.hat F (L : Set (Fin n → E)), m.mulVec (z + w) - (z + w) = N • y := by
    rintro z w ⟨y, hy, h⟩ ⟨y', hy', h'⟩
    exact ⟨y + y', add_mem hy hy', by rw [smul_add, ← h, ← h', Matrix.mulVec_add]; abel⟩
  have hx : ∀ x ∈ Submodule.span ℤ (s : Set (Fin n → E)), ∃ y ∈ GlobalTheory.AdLat.hat F (L : Set (Fin n → E)),
      m.mulVec (GlobalTheory.AdLat.fv F x) - GlobalTheory.AdLat.fv F x = N • y := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact hm x hx
    | zero =>
      have : GlobalTheory.AdLat.fv F (0 : Fin n → E) = 0 := funext fun i => TensorProduct.tmul_zero _ _
      exact ⟨0, zero_mem _, by simp [this]⟩
    | add x y _ _ hx hy =>
      have : GlobalTheory.AdLat.fv F (x + y) = GlobalTheory.AdLat.fv F x + GlobalTheory.AdLat.fv F y :=
        funext fun i => TensorProduct.tmul_add _ _ _
      rw [this]; exact hadd _ _ hx hy
    | smul c x _ hx =>
      obtain ⟨y, hy, h⟩ := hx
      have : GlobalTheory.AdLat.fv F (c • x) = c • GlobalTheory.AdLat.fv F x :=
        funext fun i => map_zsmul (TensorProduct.mk F (Af F) E 1) c (x i)
      refine ⟨c • y, zsmul_mem hy c, ?_⟩
      rw [this, Matrix.mulVec_smul, ← smul_sub, h, smul_comm]
  intro z hz
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, x, hxL, rfl⟩ := hz
    obtain ⟨y, hy, h⟩ := hx x (by rw [hs]; exact hxL)
    have : (fun i => a ⊗ₜ[F] x i) = a • GlobalTheory.AdLat.fv F x := by
      funext i
      simp [GlobalTheory.AdLat.fv, TensorProduct.smul_tmul']
    refine ⟨a • y, hsm a ha y hy, ?_⟩
    rw [this, Matrix.mulVec_smul, ← smul_sub, h, smul_comm]
  | zero => exact ⟨0, zero_mem _, by simp⟩
  | add z w _ _ hz hw => exact hadd z w hz hw
  | neg z _ hz =>
    obtain ⟨y, hy, h⟩ := hz
    exact ⟨-y, neg_mem hy, by rw [smul_neg, ← h, Matrix.mulVec_neg]; abel⟩

theorem continuous_fin (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] :
    Continuous (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) : AF F ⊗[F] E → Af F ⊗[F] E) := by
  have : IsModuleTopology (Af F) (Af F ⊗[F] E) := ⟨rfl⟩
  have : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  have : ContinuousAdd (Af F ⊗[F] E) := IsModuleTopology.toContinuousAdd (Af F) _
  have : ContinuousSMul (Af F) (Af F ⊗[F] E) := IsModuleTopology.toContinuousSMul _ _
  let φ : AF F ⊗[F] E →ₛₗ[(sndA F).toRingHom] Af F ⊗[F] E :=
    { toFun := Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)
      map_add' := map_add _
      map_smul' := fun a x => by
        rw [Algebra.smul_def, Algebra.smul_def, map_mul]
        rfl }
  have hs : Continuous ((sndA F).toRingHom : AF F → Af F) := continuous_snd
  exact IsModuleTopology.continuous_of_linearMapₛₗ hs φ

theorem exists_finPart_mat {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (g : GL (Fin n) (AF F ⊗[F] E)) (hg : g ∈ HR (AF F) σ J) :
    ∃ k ∈ HR (AF F) σ J, Formalism.UG.bc (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)).toRingHom k = 1 ∧
      Formalism.UG.bc (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom k =
        Formalism.UG.bc (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom g := by
  let e : AF F ⊗[F] E := pairA F 0 1 ⊗ₜ 1
  have he : e * e = e := by
    simp only [e, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    congr 1
    exact Prod.ext (mul_zero _) (mul_one _)
  have hσ : sigR (AF F) σ e = e := by
    simp [e, sigR]
  obtain ⟨k, hk, hke⟩ := exists_cut _ (JR (AF F) J) e he hσ g hg
  have h0 : Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) e = 0 :=
    TensorProduct.zero_tmul _ _
  have h1 : Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) e = 1 := rfl
  refine ⟨k, hk, Units.ext ?_, Units.ext ?_⟩
  · change k.1.map (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)) = 1
    ext i j
    rw [hke]
    by_cases h : i = j
    · subst h; simp [h0]
    · simp [h0, Matrix.one_apply_ne h]
  · ext i j
    change Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) (k.1 i j) =
      Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) (g.1 i j)
    rw [hke]
    simp [h1]

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_finPart (D : D7) (V : HSp D) (g : GA D V) : ∃ k ∈ GfC V, finHom V k = finHom V g := by
  let g' : HR (AF D.host.F) D.sp.cm.sig V.gram := g
  obtain ⟨k, hk, h1, h2⟩ := exists_finPart_mat D.sp.cm.sig V.gram (matHom V g) g'.2
  let k' : HR (AF D.host.F) D.sp.cm.sig V.gram := ⟨k, hk⟩
  exact ⟨k', h1, h2⟩

theorem level_mem_nhds : ∀ (D : D7) (V : HSp D) (N : ℕ) (Kf : Subgroup (GA D V)), 0 < N → IsLevelK V N Kf → ∀ g₀ : GA D V, {g : GA D V | ∃ k ∈ Kf, ∃ h ∈ GinfC V, g = g₀ * k * h} ∈ 𝓝 g₀ := by
  intro D V N Kf hN hK g₀
  have : IsModuleTopology (AF D.host.F) (AF D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
  have : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  have : IsTopologicalRing (AF D.host.F ⊗[D.host.F] D.host.E) :=
    IsModuleTopology.isTopologicalRing (AF D.host.F) _
  have : IsTopologicalGroup (GA D V) :=
    inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig V.gram))
  let ψ : V.V →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E) :=
    V.frame.equivFun.toLinearMap.restrictScalars (𝓞 D.host.E)
  let L := V.L0.map ψ
  have hfg : L.FG := V.standardTuple_isLattice.fg.map ψ
  have hL : Submodule.span D.host.E (L : Set (Fin V.rank → D.host.E)) = ⊤ := by
    have : (L : Set (Fin V.rank → D.host.E)) = V.frame.equivFun.toLinearMap '' V.L0 := rfl
    rw [this, ← Submodule.map_span, V.standardTuple_isLattice.span_eq_top, Submodule.map_top, LinearEquiv.range]
  have hhat : GlobalTheory.AdLat.hat D.host.F (L : Set (Fin V.rank → D.host.E)) = latHat V := by
    unfold GlobalTheory.AdLat.hat latHat
    congr 1
    ext z
    constructor
    · rintro ⟨a, ha, _, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨a, ha, x, hx, rfl⟩
    · rintro ⟨a, ha, x, hx, rfl⟩
      exact ⟨a, ha, _, ⟨x, hx, rfl⟩, rfl⟩
  have hn := congr_mem_nhds D.host.F D.host.E V.rank L hfg hL N hN
  rw [hhat] at hn
  have hm : Continuous fun g : GA D V => (matHom V g).1 :=
    Units.continuous_val.comp continuous_subtype_val
  have hf : Continuous fun g : GA D V => (finHom V g).1 := hm.matrix_map (continuous_fin D.host.F D.host.E)
  have hc : Continuous fun g : GA D V => (finHom V (g₀⁻¹ * g)).1 := hf.comp (continuous_const_mul g₀⁻¹)
  have h1 := hc.continuousAt.preimage_mem_nhds (x := g₀) (by rw [inv_mul_cancel, map_one]; exact hn)
  refine Filter.mem_of_superset h1 fun g hg => ?_
  obtain ⟨k, hk, hkg⟩ := exists_finPart D V (g₀⁻¹ * g)
  refine ⟨k, (hK k).mpr ⟨hk, by rw [hkg]; exact hg⟩, k⁻¹ * (g₀⁻¹ * g), ?_, by group⟩
  change finHom V _ = 1
  rw [map_mul, map_inv, hkg, inv_mul_cancel]

end GlobalTheory.LevelOpen
