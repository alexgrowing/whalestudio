import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryExistsWithPrescribedPartsStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLatticeRationalVectorsInAdelicTranslateStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CompletedLatticeEqAdelicCompletionAndGram
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MeanLogSupNormLowerBoundCmFrameNonvanishingStatement
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ReindexUnitary
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal
open IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RepConv

theorem hat_cong {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ} (L : Set (Fin n → E))
    (γ : Matrix (Fin n) (Fin n) E) (M : ℕ) (h : ∀ x ∈ L, ∃ y ∈ L, γ.mulVec x - x = M • y) :
    ∀ z ∈ GlobalTheory.AdLat.hat F L, ∃ y ∈ GlobalTheory.AdLat.hat F L,
      (γ.map (inclR (F := F) (FiniteAdeleRing (𝓞 F) F))).mulVec z - z = M • y := by
  intro z hz
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hz
    obtain ⟨y, hy, e⟩ := h x hx
    refine ⟨fun i => a ⊗ₜ y i, AddSubgroup.subset_closure ⟨a, ha, y, hy, rfl⟩, ?_⟩
    funext i
    have e1 := congrFun e i
    simp only [Pi.sub_apply, Pi.smul_apply] at e1 ⊢
    rw [← TensorProduct.tmul_smul, ← e1, TensorProduct.tmul_sub]
    congr 1
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [inclR]
  | zero => exact ⟨0, zero_mem _, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨y, hy, e⟩ := ha
    obtain ⟨y', hy', e'⟩ := hb
    refine ⟨y + y', add_mem hy hy', ?_⟩
    rw [Matrix.mulVec_add, smul_add, ← e, ← e']
    abel
  | neg a _ ha =>
    obtain ⟨y, hy, e⟩ := ha
    refine ⟨-y, neg_mem hy, ?_⟩
    rw [Matrix.mulVec_neg, smul_neg, ← e]
    abel

theorem archM_mul' {D : D7} (V : HSp D) (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (a b : GA D V) :
    archM V θ (a * b) = archM V θ a * archM V θ b := by
  unfold archM
  rw [map_mul, Units.val_mul, Matrix.map_mul]

theorem archM_one' {D : D7} (V : HSp D) (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) :
    archM V θ 1 = 1 := by
  unfold archM
  rw [map_one]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem exists_rat {D : D7} (V : HSp D) (γ' : GL (Fin V.rank) D.host.E)
    (h : ∀ x y, herm (-(V.gram)ᵀ) (γ'.1.mulVec x) (γ'.1.mulVec y) =
      herm (-(V.gram)ᵀ) x y) :
    ∃ γ₀ ∈ GQ V, (finHom V γ₀).1 = γ'.1.map (inclR (Af D.host.F)) ∧
      ∀ (τ : D.host.E →+* ℂ) (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ), Formalism.MainNotions.StandardLattice.IsInfEmb τ θ →
        archM V θ γ₀ = γ'.1.map τ := by
  have hU : γ' ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram := by
    show Formalism.UG.cT _ γ'.1 * V.gram * γ'.1 = V.gram
    refine Matrix.ext fun a b => ?_
    have := h (Pi.single b 1) (Pi.single a 1)
    have hc : ∀ x, cc x = (D.sp.cm.sig : D.host.E →+* D.host.E) x := fun _ => rfl
    simp only [herm, Matrix.mulVec_single_one, hc, Matrix.neg_apply, Matrix.transpose_apply, Matrix.col_apply] at this
    have h2 : ∑ x, ∑ y, (Pi.single b 1 : Fin V.rank → D.host.E) x * -V.gram y x *
        (D.sp.cm.sig : D.host.E →+* D.host.E) ((Pi.single a 1 : Fin V.rank → D.host.E) y) = -V.gram a b := by
      rw [Finset.sum_eq_single b, Finset.sum_eq_single a]
      · simp
      · intro j _ hj; simp [hj]
      · simp
      · intro j _ hj; simp [hj]
      · simp
    rw [h2] at this
    rw [← neg_inj, ← this]
    simp only [Matrix.mul_apply, Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul,
      ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hR : Formalism.UG.bc (inclR (AF D.host.F)) γ' ∈ HR (AF D.host.F) D.sp.cm.sig V.gram := by
    have hU' : Formalism.UG.cT _ γ'.1 * V.gram * γ'.1 = V.gram := hU
    have := congrArg (fun m => Matrix.map m (inclR (F := D.host.F) (AF D.host.F))) hU'
    simp only [Matrix.map_mul] at this
    rw [GlobalTheory.UnitaryGlue.cT_map (inclR (F := D.host.F) (AF D.host.F)) (D.sp.cm.sig : D.host.E →+* D.host.E)
      (sigR (AF D.host.F) D.sp.cm.sig) (fun _ => rfl)] at this
    exact this
  let γ₀ : GA D V := ⟨_, hR⟩
  have h1 : (matHom V γ₀).1 = γ'.1.map (inclR (AF D.host.F)) := rfl
  refine ⟨γ₀, Subgroup.mem_subgroupOf.2 ⟨γ', hU, rfl⟩, ?_, fun τ θ hθ => ?_⟩
  · rw [← GlobalTheory.UnitaryGlue.map_map_inclR (sndA D.host.F), ← h1]; rfl
  · have hinc : (γ'.1.map (inclR (Ainf D.host.F))).map θ = γ'.1.map τ := by
      ext i j
      exact hθ.1 _
    rw [← hinc, ← GlobalTheory.UnitaryGlue.map_map_inclR (fstA D.host.F), ← h1]; rfl

theorem map_eq_of_frames {E : Type} [Field E] {Ψ : Finset (E →+* ℂ)} {r : ℕ} (γ1 γ2 γ3 : GL (Fin r) E)
    (x b : Frame Ψ r) (τ : Ψ) (u : Matrix (Fin r) (Fin r) ℂ) (hdet : (mat x τ).det ≠ 0)
    (hb : mat b τ = (mat x τ)⁻¹ * u * mat x τ) (e : lact γ1 x = lact γ2 (rmul (lact γ3 x) b)) :
    ((γ2 * γ3)⁻¹ * γ1).1.map τ.1 = u := by
  have hu : IsUnit (mat x τ).det := Ne.isUnit hdet
  have e5 : γ1.1.map τ.1 * mat x τ = γ2.1.map τ.1 * ((γ3.1.map τ.1 * mat x τ) * mat b τ) := congrFun e τ
  rw [hb] at e5
  have e6 : γ1.1.map τ.1 = (γ2 * γ3).1.map τ.1 * u := by
    have := congrArg (· * (mat x τ)⁻¹) e5
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one,
      Matrix.mul_nonsing_inv_cancel_left _ _ hu] at this
    rw [this, Units.val_mul, Matrix.map_mul, Matrix.mul_assoc]
  rw [Units.val_mul, Matrix.map_mul, e6, ← Matrix.mul_assoc, ← Matrix.map_mul, Units.inv_mul,
    Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]

theorem hat_cong_conj {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ} (L L' : Set (Fin n → E))
    (g : GL (Fin n) (GlobalTheory.AdLat.RA F E))
    (hhat : (GlobalTheory.AdLat.hat F L' : Set (Fin n → GlobalTheory.AdLat.RA F E)) = g.1.mulVec '' (GlobalTheory.AdLat.hat F L))
    (γ : Matrix (Fin n) (Fin n) E) (M : ℕ) (h : ∀ x ∈ L', ∃ y ∈ L', γ.mulVec x - x = M • y) :
    ∀ z ∈ GlobalTheory.AdLat.hat F L, ∃ y ∈ GlobalTheory.AdLat.hat F L,
      ((g⁻¹).1 * γ.map (inclR (F := F) (FiniteAdeleRing (𝓞 F) F)) * g.1).mulVec z - z = M • y := by
  intro z hz
  have hz1 : g.1.mulVec z ∈ (GlobalTheory.AdLat.hat F L' : Set (Fin n → GlobalTheory.AdLat.RA F E)) := by
    rw [hhat]; exact ⟨z, hz, rfl⟩
  obtain ⟨y, hy, e⟩ := hat_cong L' γ M h _ hz1
  have hy1 : y ∈ (GlobalTheory.AdLat.hat F L' : Set (Fin n → GlobalTheory.AdLat.RA F E)) := hy
  rw [hhat] at hy1
  obtain ⟨y', hy', rfl⟩ := hy1
  refine ⟨y', hy', ?_⟩
  have e2 := congrArg ((g⁻¹).1.mulVec) e
  simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at e2
  rw [← e2, Matrix.mul_assoc]

set_option maxHeartbeats 400000 in

theorem conj_mem_of_cong : ∀ (D : D7) (V : Formalism.BasicNotions.TH.HSp D) (Comp : Type) (X : Comp → Data D.host.E V.rank)
    (dict : GA D V → Σ k, Frame (X k).Ψ V.rank) (Kf : Subgroup (GA D V))
    (th : ∀ c, (X c).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (M : ℕ) (x0 : ∀ c, Frame (X c).Ψ V.rank),
    IsLevelK V M Kf → (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) → DictIsUnif V dict Kf th rfl →
    (∀ c, x0 c ∈ (X c).dom) →
    (∀ g, ∀ h ∈ GinfC V, ∃ γ' ∈ (X (dict g).1).Γ,
      dict (g * h) = ⟨(dict g).1, lact γ' (rmul (dict g).2 (archMat V th rfl x0 h (dict g).1))⟩) →
    (∀ c, (X c).Gm = -(V.gram)ᵀ) →
    ∀ (k : Comp) (g : GA D V), dict g = ⟨k, x0 k⟩ →
    ∀ Λk : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E),
      (Λk : Set (Fin V.rank → D.host.E)) = GlobalTheory.AdLat.latOf (maximalRealSubfield D.host.E) (finHom V g).1
        (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) →
      (GlobalTheory.AdLat.hat (maximalRealSubfield D.host.E) (Λk : Set (Fin V.rank → D.host.E)) :
                   Set (Fin V.rank → GlobalTheory.AdLat.RA (maximalRealSubfield D.host.E) D.host.E)) =
        ((finHom V g).1 : Matrix (Fin V.rank) (Fin V.rank) (GlobalTheory.AdLat.RA (maximalRealSubfield D.host.E) D.host.E)).mulVec ''
          (GlobalTheory.AdLat.hat (maximalRealSubfield D.host.E) (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E))) →
    ∀ γ' : GL (Fin V.rank) D.host.E,
      (IsUStab (-(V.gram)ᵀ) Λk γ' ∧ ∀ x ∈ Λk, ∃ y ∈ Λk, (γ' : Matrix (Fin V.rank) (Fin V.rank) D.host.E).mulVec x - x = M • y) →
      ∃ γ ∈ (X k).Γ, ∀ (τ : D.host.E →+* ℂ) (hτ : τ ∈ (X k).Ψ),
        archM V (th k ⟨τ, hτ⟩) g * (γ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map τ =
          (γ' : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map τ * archM V (th k ⟨τ, hτ⟩) g := by
  intro D V Comp X dict Kf th M x0 hK hth hd hx0 hact _ k g hg Λk _ hhat γ' hγ'
  haveI : IsTotallyReal D.host.F := D.sp.cm.totReal
  obtain ⟨γ₀, hQ, hfin, harch⟩ := exists_rat V γ' hγ'.1.1
  obtain ⟨hinj, -, -, hsur⟩ := (GlobalTheory.T.adelicUnitary_exists_with_prescribed_parts D V).2 (X k).Ψ (th k) (X k).cmType (hth k)
  obtain ⟨h, hh, hhw⟩ := hsur (fun τ => archM V (th k τ) (g⁻¹ * γ₀ * g)) (fun τ =>
    GlobalTheory.MarkUnit.infMat_unitary D.sp.cm.sig V.gram τ.1
      (fun x => IsCMField.complexEmbedding_complexConj D.host.E τ.1 x) (th k τ) (hth k τ) _)
  have hκ1 : ∀ τ, archM V (th k τ) (g⁻¹ * γ₀ * g * h⁻¹) = 1 := fun τ => by
    rw [archM_mul', ← hhw, ← archM_mul', mul_inv_cancel, archM_one']
  have hh1 : finHom V h = 1 := hh
  have hκ : g⁻¹ * γ₀ * g * h⁻¹ ∈ Kf := by
    refine (hK _).2 ⟨hinj _ hκ1, ?_⟩
    have hf : (finHom V (g⁻¹ * γ₀ * g * h⁻¹)).1 =
        ((finHom V g)⁻¹).1 * γ'.1.map (inclR (Af D.host.F)) * (finHom V g).1 := by
      rw [← hfin]
      simp only [map_mul, map_inv, hh1, inv_one, mul_one, Units.val_mul]
    rw [(GlobalTheory.Member.latHat_eq_hat_and_gram D V).1, hf]
    exact hat_cong_conj (F := D.host.F) (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E))
      (Λk : Set (Fin V.rank → D.host.E)) (finHom V g) hhat γ'.1 M hγ'.2
  obtain ⟨γ1, hγ1, e1⟩ := hd.1 γ₀ hQ g
  obtain ⟨γ3, hγ3, e3⟩ := hd.2.1 _ hκ g
  obtain ⟨γ2, hγ2, e2⟩ := hact (g * (g⁻¹ * γ₀ * g * h⁻¹)) h hh
  have hgrp : g * (g⁻¹ * γ₀ * g * h⁻¹) * h = γ₀ * g := by group
  rw [hgrp, e1] at e2
  rw [e3] at e2 hγ2
  rw [hg] at e2 hγ1 hγ2 hγ3
  have e4 : lact γ1 (x0 k) = lact γ2 (rmul (lact γ3 (x0 k)) (archMat V th rfl x0 h k)) :=
    eq_of_heq (Sigma.mk.inj e2).2
  refine ⟨(γ2 * γ3)⁻¹ * γ1, mul_mem (inv_mem (mul_mem hγ2 hγ3)) hγ1, fun τ hτ => ?_⟩
  have hb : mat (archMat V th rfl x0 h k) ⟨τ, hτ⟩ =
      (mat (x0 k) ⟨τ, hτ⟩)⁻¹ * archM V (th k ⟨τ, hτ⟩) h * mat (x0 k) ⟨τ, hτ⟩ := by
    have hre : ∀ u : Matrix (Fin V.rank) (Fin V.rank) ℂ,
        Matrix.reindex (finCongr (rfl : V.rank = V.rank)) (finCongr (rfl : V.rank = V.rank)) u = u := fun u => by
      simp
    rw [← hre (archM V (th k ⟨τ, hτ⟩) h)]
    rfl
  have e6 := map_eq_of_frames γ1 γ2 γ3 (x0 k) _ ⟨τ, hτ⟩ _ (hx0 k ⟨τ, hτ⟩).1 hb e4
  rw [e6, hhw, ← harch τ _ (hth k ⟨τ, hτ⟩), ← archM_mul', ← archM_mul']
  congr 1
  group

end GlobalTheory.RepConv
