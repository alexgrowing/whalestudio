import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.MarkSpec
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ConjEquivApply
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLatticeRationalVectorsInAdelicTranslate
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ComponentAttainedAtBaseFrame
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryExistsWithPrescribedPartsStatement
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Formalism.LocalToGlobal.ProjectiveLattices.ComponentWModel
import Formalism.LocalToGlobal.ProjectiveLattices.NormLaws
import Formalism.LocalToGlobal.ProjectiveLattices.VolProofs
import Formalism.LocalToGlobal.ProjectiveLattices.DatProofs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct Topology
open GlobalTheory.RecDict

namespace GlobalTheory.RecDict

open scoped Matrix nonZeroDivisors

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

theorem coset_fv_mulVec (A : Matrix (Fin n) (Fin n) E) (x : Fin n → E) :
    (A.map (inclR (F := F) (Af F))) *ᵥ AdLat.fv F x = AdLat.fv F (A *ᵥ x) := by
  funext i
  exact (RingHom.map_mulVec (inclR (F := F) (Af F)) A x i).symm

theorem coset_tmul_eq (t : Af F) (x : Fin n → E) :
    (fun i => t ⊗ₜ[F] x i : Fin n → AdLat.RA F E) = (t ⊗ₜ[F] (1 : E) : AdLat.RA F E) • AdLat.fv F x := by
  funext i
  simp only [AdLat.fv, Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]

theorem coset_smul_mem_hat (L : Set (Fin n → E)) (t : Af F) (ht : ∀ v, t v ∈ v.adicCompletionIntegers F)
    (w : Fin n → AdLat.RA F E) (hw : w ∈ AdLat.hat F L) :
    (t ⊗ₜ[F] (1 : E) : AdLat.RA F E) • w ∈ AdLat.hat F L := by
  induction hw using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨s, hs, x, hx, rfl⟩ := hw
    refine AddSubgroup.subset_closure ⟨t * s, fun v => mul_mem (ht v) (hs v), x, hx, ?_⟩
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add w w' _ _ h h' => rw [smul_add]; exact add_mem h h'
  | neg w _ h => rw [smul_neg]; exact neg_mem h

theorem coset_mulVec_mem_hat (L : Set (Fin n → E)) (A : Matrix (Fin n) (Fin n) E) (hA : ∀ x ∈ L, A *ᵥ x ∈ L)
    (w : Fin n → AdLat.RA F E) (hw : w ∈ AdLat.hat F L) :
    (A.map (inclR (F := F) (Af F))) *ᵥ w ∈ AdLat.hat F L := by
  induction hw using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨s, hs, x, hx, rfl⟩ := hw
    rw [coset_tmul_eq, Matrix.mulVec_smul, coset_fv_mulVec]
    exact coset_smul_mem_hat L s hs _ (AdLat.Half.fv_mem_hat' L _ (hA x hx))
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add w w' _ _ h h' => rw [Matrix.mulVec_add]; exact add_mem h h'
  | neg w _ h => rw [Matrix.mulVec_neg]; exact neg_mem h

theorem coset_congr_hat (L : Set (Fin n → E)) (κ : Matrix (Fin n) (Fin n) (AdLat.RA F E)) (N : ℕ) (β : AdLat.RA F E)
    (h : ∀ x ∈ L, ∃ y ∈ AdLat.hat F L, κ *ᵥ (β • AdLat.fv F x) - β • AdLat.fv F x = N • y)
    (z : Fin n → AdLat.RA F E) (hz : z ∈ AdLat.hat F L) :
    ∃ y ∈ AdLat.hat F L, κ *ᵥ (β • z) - β • z = N • y := by
  induction hz using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨s, hs, x, hx, rfl⟩ := hw
    obtain ⟨y, hy, e⟩ := h x hx
    refine ⟨_, coset_smul_mem_hat L s hs y hy, ?_⟩
    rw [coset_tmul_eq, smul_comm β, Matrix.mulVec_smul, ← smul_sub, e, smul_comm]
  | zero => exact ⟨0, zero_mem _, by simp⟩
  | add w w' _ _ h h' =>
    obtain ⟨y, hy, e⟩ := h
    obtain ⟨y', hy', e'⟩ := h'
    refine ⟨y + y', add_mem hy hy', ?_⟩
    rw [smul_add, smul_add, Matrix.mulVec_add, ← e, ← e']
    abel
  | neg w _ h =>
    obtain ⟨y, hy, e⟩ := h
    refine ⟨-y, neg_mem hy, ?_⟩
    rw [smul_neg, smul_neg, Matrix.mulVec_neg, ← e]
    abel

theorem coset_scale {R : Type} [CommRing R] (κ : Matrix (Fin n) (Fin n) R) (N : ℕ) (β c a : R) (z y : Fin n → R)
    (e : κ *ᵥ (β • a • z) - β • a • z = N • y) : (c * a) • (κ *ᵥ (β • z) - β • z) = N • c • y := by
  rw [smul_comm N, ← e, smul_comm β a z, Matrix.mulVec_smul κ a, ← smul_sub, mul_smul]

theorem coset_add {R : Type} [CommRing R] (N : ℕ) (s t : R) (u y y' : Fin n → R) (e : s • u = N • y)
    (e' : t • u = N • y') : (s + t) • u = N • (y + y') := by
  rw [add_smul, e, e', smul_add]

theorem coset_unscale_ideal {E R : Type} [Field E] [NumberField E] [CommRing R] (ι : E →+* R)
    (I : FractionalIdeal (𝓞 E)⁰ E) (hA : I ≠ 0) (S : AddSubgroup (Fin n → R))
    (hS : ∀ b : 𝓞 E, ∀ w ∈ S, ι (b : E) • w ∈ S) (T : AddSubgroup (Fin n → R))
    (hT : T = AddSubgroup.closure {w | ∃ a : E, a ∈ I ∧ ∃ z ∈ (S : Set (Fin n → R)), w = ι a • z})
    (κ : Matrix (Fin n) (Fin n) R) (N : ℕ) (β : R)
    (h : ∀ z ∈ T, ∃ y ∈ T, κ *ᵥ (β • z) - β • z = N • y) (z : Fin n → R) (hz : z ∈ S) :
    ∃ y ∈ S, κ *ᵥ (β • z) - β • z = N • y := by
  subst hT
  have hc : ∀ c ∈ I⁻¹, ∀ y ∈ AddSubgroup.closure {w | ∃ a : E, a ∈ I ∧ ∃ z ∈ (S : Set (Fin n → R)), w = ι a • z},
      ι c • y ∈ S := by
    intro c hc y hy
    induction hy using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨a, ha, w, hw, rfl⟩ := hw
      have h1 := FractionalIdeal.mul_mem_mul hc ha
      rw [inv_mul_cancel₀ hA] at h1
      obtain ⟨b, hb⟩ := (FractionalIdeal.mem_one_iff _).1 h1
      rw [smul_smul, ← map_mul, ← hb]
      exact hS b w hw
    | zero => rw [smul_zero]; exact zero_mem _
    | add w w' _ _ h h' => rw [smul_add]; exact add_mem h h'
    | neg w _ h => rw [smul_neg]; exact neg_mem h
  have key : ∀ s ∈ I⁻¹ * I, ∃ y ∈ S, ι s • (κ *ᵥ (β • z) - β • z) = N • y := by
    intro s hs
    refine FractionalIdeal.mul_induction_on (C := fun s => ∃ y ∈ S, ι s • (κ *ᵥ (β • z) - β • z) = N • y) hs
      (fun c hc' a ha => ?_) (fun s t hs ht => ?_)
    · obtain ⟨y, hy, e⟩ := h (ι a • z) (AddSubgroup.subset_closure ⟨a, ha, z, hz, rfl⟩)
      refine ⟨_, hc c hc' y hy, ?_⟩
      rw [map_mul]
      exact coset_scale κ N β _ _ z y e
    · obtain ⟨y, hy, e⟩ := hs
      obtain ⟨y', hy', e'⟩ := ht
      exact ⟨y + y', add_mem hy hy', by rw [map_add]; exact coset_add N _ _ _ y y' e e'⟩
  have := key 1 (by rw [inv_mul_cancel₀ hA]; exact FractionalIdeal.one_mem_one _)
  rwa [map_one, one_smul] at this

theorem coset_det_ne_zero {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (τ : E →+* ℂ)
    (G : Matrix (Fin r) (Fin r) E) (x : Matrix (Fin r) (Fin r) ℂ) (p : ℕ)
    (h : gram τ G x = Matrix.diagonal fun a : Fin r => ((sgn p (a : ℕ) : ℝ) : ℂ)) : x.det ≠ 0 := by
  have e : gram τ G x = xᵀ * G.map τ * x.map (starRingEnd ℂ) := by
    ext a b
    simp only [gram, hermC, FD.col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
      Finset.sum_mul]
    exact Finset.sum_comm
  intro h0
  have h1 := congrArg Matrix.det (e.symm.trans h)
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h0, zero_mul, zero_mul, Matrix.det_diagonal] at h1
  refine Finset.prod_ne_zero_iff.2 (fun a _ => ?_) h1.symm
  unfold sgn
  split_ifs <;> simp

end General

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem coset_archM_mul (V : HSp D) (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (a b : GA D V) :
    archM V θ (a * b) = archM V θ a * archM V θ b := by
  unfold archM
  rw [map_mul, Units.val_mul, Matrix.map_mul]

theorem coset_archM_one (V : HSp D) (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) : archM V θ 1 = 1 := by
  unfold archM
  rw [map_one, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]

theorem coset_exists_rat (V : HSp D) (γ : GL (Fin V.rank) D.host.E)
    (hγ : ∀ x y, herm (-V.gramᵀ) (γ.1 *ᵥ x) (γ.1 *ᵥ y) = herm (-V.gramᵀ) x y) :
    ∃ δ ∈ GQ V, (finHom V δ).1 = γ.1.map (inclR (Af D.host.F)) ∧
      ∀ (τ : D.host.E →+* ℂ) θ, Formalism.MainNotions.StandardLattice.IsInfEmb τ θ → archM V θ δ = γ.1.map τ := by
  have hU : γ ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram := by
    change Formalism.UG.cT _ _ * _ * _ = _
    ext i j : 1
    have h := hγ (Pi.single j 1) (Pi.single i 1)
    simp only [herm, Matrix.mulVec_single_one, Matrix.col_apply, Matrix.neg_apply,
      Matrix.transpose_apply, mul_neg, neg_mul, Finset.sum_neg_distrib, neg_inj] at h
    simp only [Pi.single_apply, cc, apply_ite (IsCMField.complexConj D.host.E),
      map_one, map_zero, mul_ite, ite_mul, mul_one, mul_zero, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
    simp only [Matrix.mul_apply, Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
    refine Eq.trans ?_ h
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    change IsCMField.complexConj D.host.E _ * _ * _ = _
    ring
  have hU' : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) γ.1 * V.gram * γ.1 = V.gram := hU
  have hA : Formalism.UG.bc (inclR (AF D.host.F)) γ ∈ HR (AF D.host.F) D.sp.cm.sig V.gram := by
    have h3 : (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) γ.1).map (inclR (F := D.host.F) (AF D.host.F)) =
        Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) (γ.1.map (inclR (AF D.host.F))) := by
      ext i j : 1
      rfl
    have h4 := congrArg (fun m => m.map (inclR (F := D.host.F) (AF D.host.F))) hU'
    simp only [Matrix.map_mul, h3] at h4
    exact h4
  refine ⟨⟨_, hA⟩, ⟨γ, hU, rfl⟩, ?_, fun τ θ hθ => ?_⟩
  · ext i j : 1
    rfl
  · ext i j : 1
    exact hθ.1 _

theorem coset_latGHat (V : HSp D) (g : GA D V) :
    latGHat V g = AdLat.hat D.host.F (latG V g : Set (Fin V.rank → D.host.E)) := by
  obtain ⟨hfg, hsp, h⟩ := comp_latG D V
  obtain ⟨Λ, h1, -, -, h2⟩ := AdLat.exists_lattice_latOf D.host.F D.host.E V.rank (latG V 1) (finHom V g) hfg hsp
  apply SetLike.coe_injective
  rw [(h g).2, (h g).1, ← h1, h2]

theorem coset_gLat_one (V : HSp D) : gLat V 1 = latHat V := by
  unfold gLat
  simp only [map_one, Units.val_one]
  ext w
  simp

theorem coset_unscale (V : HSp D) (κ : Matrix (Fin V.rank) (Fin V.rank) (AdLat.RA D.host.F D.host.E)) (N : ℕ)
    (β : AdLat.RA D.host.F D.host.E)
    (h : ∀ z ∈ latGHat V 1, ∃ y ∈ latGHat V 1, κ *ᵥ (β • z) - β • z = N • y)
    (z : Fin V.rank → AdLat.RA D.host.F D.host.E) (hz : z ∈ latHat V) :
    ∃ y ∈ latHat V, κ *ᵥ (β • z) - β • z = N • y := by
  refine coset_unscale_ideal (inclR (F := D.host.F) (Af D.host.F)) D.host.AA (comp_AA_ne_zero D) (latHat V)
    (fun b w hw => LevelHalf.halfVec_mem V b w hw) (latGHat V 1) ?_ κ N β h z hz
  unfold latGHat
  rw [coset_gLat_one]
  rfl

theorem coset_fin {R : Type} [CommRing R] {n : ℕ} (S T : AddSubgroup (Fin n → R)) (g₁ g₂ δ : GL (Fin n) R) (N : ℕ)
    (h1 : ∀ w ∈ T, ∃ z ∈ S, g₁.1 *ᵥ z = w) (hδ : ∀ w ∈ T, δ.1 *ᵥ w ∈ T) (hδ' : ∀ w ∈ T, (δ⁻¹).1 *ᵥ w ∈ T)
    (u v w₁ w₂ b : Fin n → R) (hw₁ : w₁ ∈ T) (hw₂ : w₂ ∈ T) (hb : b ∈ T)
    (e₁ : u - g₁.1 *ᵥ v = N • w₁) (e₂ : u - g₂.1 *ᵥ v = N • w₂) (e₃ : δ.1 *ᵥ u = u + N • b) :
    ∃ y ∈ S, ((δ * g₁)⁻¹ * g₂).1 *ᵥ v - v = N • y := by
  obtain ⟨z, hz, ez⟩ := h1 _ (hδ' _ (sub_mem (sub_mem (hδ _ hw₁) hw₂) hb))
  refine ⟨z, hz, ?_⟩
  have hz' : (δ * g₁).1 *ᵥ z = δ.1 *ᵥ w₁ - w₂ - b := by
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, ez, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have hinv : ∀ x, ((δ * g₁)⁻¹).1 *ᵥ ((δ * g₁).1 *ᵥ x) = x := fun x => by
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  have e : g₂.1 *ᵥ v - (δ * g₁).1 *ᵥ v = N • ((δ * g₁).1 *ᵥ z) := by
    rw [hz', Units.val_mul, ← Matrix.mulVec_mulVec, smul_sub, smul_sub, ← Matrix.mulVec_smul, ← e₁, ← e₂,
      Matrix.mulVec_sub, e₃]
    abel
  rw [Units.val_mul, ← Matrix.mulVec_mulVec]
  have e' := congrArg (fun x => ((δ * g₁)⁻¹).1 *ᵥ x) e
  simpa only [Matrix.mulVec_sub, Matrix.mulVec_smul, hinv] using e'

theorem coset_of_markSpec (V : HSp D) {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {σ' : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (D.host.E →+* ℂ)} (F : FamilyUnif Xo σ' ty)
    {r : ℕ} (hr : V.rank = r) (M : GlobalTheory.FrameUnif.ModelsOf F r)
    (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E))
    (th : ∀ k, (M.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (hok : RecOK M V hr io th x₀)
    (Kf : Subgroup (GA D V)) (hK : KfHalf V Kf l.M (l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E)))
    (h h' : GA D V) (p : Σ k, Frame (M.X k).Ψ r) (γ' : GL (Fin r) D.host.E) (hγ' : γ' ∈ (M.X p.1).Γ)
    (h1 : MarkSpec M V hr io th x₀ h p) (h2 : MarkSpec M V hr io th x₀ h' ⟨p.1, lact γ' p.2⟩) :
    ∃ γ ∈ GQ V, ∃ k ∈ Kf, h' = γ * h * k := by
  subst hr
  obtain ⟨k, x⟩ := p
  obtain ⟨hbase, hW, ⟨-, hrange⟩, -, hth, hx⟩ := hok
  obtain ⟨γ₁, hγ₁, hL₁, hm₁, hf₁⟩ := h1
  obtain ⟨γ₂, hγ₂, hL₂, hm₂, hf₂⟩ := h2
  have hΛ₁ : ((M.X k).Λ : Set (Fin V.rank → D.host.E)) = latG V (γ₁ * h) := hL₁.trans (Set.image_id _)
  have hΛ₂ : ((M.X k).Λ : Set (Fin V.rank → D.host.E)) = latG V (γ₂ * h') := hL₂.trans (Set.image_id _)
  have hT₁ : latGHat V (γ₁ * h) = AdLat.hat D.host.F ((M.X k).Λ : Set (Fin V.rank → D.host.E)) := by
    rw [coset_latGHat, hΛ₁]
  have hT₂ : latGHat V (γ₂ * h') = AdLat.hat D.host.F ((M.X k).Λ : Set (Fin V.rank → D.host.E)) := by
    rw [coset_latGHat, hΛ₂]
  obtain ⟨⟨hU, hst⟩, hhalf, -⟩ := (hbase.gam k γ').1 hγ'
  have hst' := ((M.X k).Γ_stab _ (inv_mem hγ')).2
  have hG : (M.X k).Gm = -V.gramᵀ := (hW k).1
  rw [hG] at hU
  obtain ⟨δ, hδ, hδf, hδa⟩ := coset_exists_rat V γ' hU
  refine ⟨γ₂⁻¹ * δ * γ₁, mul_mem (mul_mem (inv_mem hγ₂) hδ) hγ₁, (δ * (γ₁ * h))⁻¹ * (γ₂ * h'), ?_, by group⟩
  refine (hK _).2 ⟨((GlobalTheory.T.adelicUnitary_exists_with_prescribed_parts D V).2 (M.X k).Ψ (th k) (M.X k).cmType (hth k)).1 _ fun τ => ?_, fun b hb z hz => ?_⟩
  · have e₁ : mat x τ = archM V (th k τ) (γ₁ * h) * x₀ τ.1 := hf₁ τ
    have e₂ : γ'.1.map τ.1 * mat x τ = archM V (th k τ) (γ₂ * h') * x₀ τ.1 := hf₂ τ
    have hdet := coset_det_ne_zero _ _ _ _ (hx k τ.1 τ.2)
    have hu : IsUnit (x₀ τ.1) := (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hdet)
    rw [e₁, ← hδa τ.1 _ (hth k τ), ← mul_assoc, ← coset_archM_mul] at e₂
    rw [coset_archM_mul, ← hu.mul_right_cancel e₂, ← coset_archM_mul, inv_mul_cancel, coset_archM_one]
  · have hδi : ((finHom V δ)⁻¹).1 = (γ'⁻¹).1.map (inclR (Af D.host.F)) := by
      apply Units.inv_eq_of_mul_eq_one_right
      rw [hδf, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
    refine coset_unscale V _ l.M (inclR (F := D.host.F) (Af D.host.F) (b : D.host.E)) (fun z hz => ?_) z hz
    rw [coset_latGHat] at hz ⊢
    refine coset_congr_hat _ _ _ _ (fun v hv => ?_) z hz
    have hv' : v ∈ LinearMap.range io := by rw [hrange]; exact hv
    obtain ⟨a, rfl⟩ := hv'
    have hba : b • a ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) Dw.La) :=
      Submodule.smul_mem_smul hb Submodule.mem_top
    obtain ⟨w₁, hw₁, e₁⟩ := hm₁ _ hba
    obtain ⟨w₂, hw₂, e₂⟩ := hm₂ _ hba
    obtain ⟨c, e₃⟩ := hhalf (F.t k (b • a)) (by
      rw [map_smul]; exact Submodule.smul_mem_smul hb Submodule.mem_top)
    have ev : inclR (F := D.host.F) (Af D.host.F) (b : D.host.E) • AdLat.fv D.host.F (io a) =
        AdLat.fv D.host.F (io (b • a)) := by
      rw [map_smul]
      funext i
      exact (map_mul (inclR (F := D.host.F) (Af D.host.F)) _ _).symm
    rw [ev, map_mul, map_inv, map_mul]
    rw [hT₁] at hw₁
    rw [hT₂] at hw₂
    refine coset_fin _ (AdLat.hat D.host.F ((M.X k).Λ : Set (Fin V.rank → D.host.E))) _ _ _ l.M (fun w hw => ?_)
      (fun w hw => ?_) (fun w hw => ?_) (AdLat.fv D.host.F (M.φ k (F.t k (b • a)) : Fin V.rank → D.host.E)) _ w₁ w₂
      (AdLat.fv D.host.F (M.φ k c : Fin V.rank → D.host.E)) hw₁ hw₂ (AdLat.Half.fv_mem_hat' _ _ (M.φ k c).2)
      e₁ e₂ ?_
    · rw [← hT₁, ← SetLike.mem_coe, ((comp_latG D V).2.2 _).2] at hw
      exact hw
    · rw [hδf]
      exact coset_mulVec_mem_hat _ _ (fun y hy => (hst y).1 hy) w hw
    · rw [hδi]
      exact coset_mulVec_mem_hat _ _ (fun y hy => (hst' y).1 hy) w hw
    · rw [hδf, coset_fv_mulVec, e₃, AdLat.cap_fv_add, AdLat.cap_fv_nsmul]

theorem double_coset_of_markSpec : ∀ (D : D7) (Q : Par D), Q.Pins → ∀ (j : ℕ) (hj : InR D j) (σ' : KA Q.l →+* ℂ) (g : ℕ) (ty : Fin g → (D.host.E →+* ℂ)) (F : FamilyUnif (Q.Xo j) σ' ty), σ' (baseKA Q.l).ρ = Q.H.rt0 → IsTypeFn Q.H (Q.Dw j).p (Q.Dw j).q ty → ∀ (M : GlobalTheory.FrameUnif.ModelsOf F D.R.r) (io : (Q.Dw j).La →ₗ[𝓞 D.host.E] (Fin (D.sp.W j).rank → D.host.E)) (th : ∀ k, (M.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ), RecOK M (D.sp.W j) (D.sp.W_rank j hj.1 hj.2) io th x₀ → ∀ Kf : Subgroup (GA D (D.sp.W j)), IsLevelK (D.sp.W j) (D.host.g 0 * D.host.g 1) Kf → ∀ (h h' : GA D (D.sp.W j)) (p : Σ k, Frame (M.X k).Ψ D.R.r) (γ' : GL (Fin D.R.r) D.host.E), γ' ∈ (M.X p.1).Γ → MarkSpec M (D.sp.W j) (D.sp.W_rank j hj.1 hj.2) io th x₀ h p → MarkSpec M (D.sp.W j) (D.sp.W_rank j hj.1 hj.2) io th x₀ h' ⟨p.1, lact γ' p.2⟩ → ∃ γ ∈ GQ (D.sp.W j), ∃ k ∈ Kf, h' = γ * h * k :=
  fun D Q hQ j hj _ _ _ F _ _ M io th x₀ hok Kf hK h h' p γ' hγ' h1 h2 =>
    coset_of_markSpec (D.sp.W j) F (D.sp.W_rank j hj.1 hj.2) M io th x₀ hok Kf
      (LevelHalf.kfHalf_record D Q hQ j Kf hK) h h' p γ' hγ' h1 h2

end GlobalTheory.RecDict
