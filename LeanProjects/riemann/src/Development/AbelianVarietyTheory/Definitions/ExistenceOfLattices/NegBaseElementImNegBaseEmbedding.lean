import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.MarkSpec

noncomputable section
namespace GlobalTheory.RecDictModel
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.RecDict
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {r : ℕ}

theorem dictLat_iff {c : Coeff l} {σ : c.F →+* ℂ} {g : ℕ} (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (M : GlobalTheory.FrameUnif.ModelsOf F r) (un : ∀ k, (M.X k).dom → FrPt Xo c (CAt σ))
    (hun : ∀ k x, GlobalTheory.FrameUnif.FrameOK e F M k x (un k x))
    (V : HSp D) (hr : V.rank = r) (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E))
    (th : ∀ k, (M.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (hR : RecOK M V hr io th x₀)
    (dict : GA D V → Σ k, Frame (M.X k).Ψ r) :
    DictLat ({ Comp := Fin F.n, X := M.X, un := un } : Formalism.L2.Pj.Unf Xo c σ r) V hr dict io e F id M.φ th x₀ ↔
      ∀ h, MarkSpec M V hr io th x₀ h (dict h) := by
  refine ⟨fun h => h.2, fun h => ⟨⟨hR.1.ef, fun k x => ?_⟩, h⟩⟩
  obtain ⟨Pm, h1, h2, h3, h4, -⟩ := hun k x
  exact ⟨Pm, h1, h2, h3, h4⟩

variable {σ' : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (D.host.E →+* ℂ)} {F : FamilyUnif Xo σ' ty}

theorem markSpec_left (M : GlobalTheory.FrameUnif.ModelsOf F r) (V : HSp D) (hr : V.rank = r)
    (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E))
    (th : ∀ k, (M.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (h : GA D V) (p : Σ k, Frame (M.X k).Ψ r)
    (δ : GA D V) (hδ : δ ∈ GQ V) :
    MarkSpec M V hr io th x₀ (δ * h) p ↔ MarkSpec M V hr io th x₀ h p := by
  constructor
  · rintro ⟨γ, hγ, h1⟩
    exact ⟨γ * δ, (GQ V).mul_mem hγ hδ, by simpa only [mul_assoc] using h1⟩
  · rintro ⟨γ, hγ, h1⟩
    exact ⟨γ * δ⁻¹, (GQ V).mul_mem hγ ((GQ V).inv_mem hδ), by simpa only [mul_assoc, inv_mul_cancel_left] using h1⟩

theorem herm_gmW (V : HSp D) (hr : V.rank = r) (x y : Fin V.rank → D.host.E) :
    herm (gmW V hr) (x ∘ Fin.cast hr.symm) (y ∘ Fin.cast hr.symm) =
      -V.hT (V.frame.equivFun.symm y) (V.frame.equivFun.symm x) := by
  subst hr
  simp only [herm, gmW, Module.Basis.equivFun_symm_apply, map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ₂, map_smul]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.smul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  have : (starRingEnd D.host.E) (y b) = cc (y b) := rfl
  simp only [this, smul_eq_mul]
  simp [HSpace.gram]
  ring

theorem recOK_isom (M : GlobalTheory.FrameUnif.ModelsOf F r) (V : HSp D) (hr : V.rank = r)
    (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E))
    (th : ∀ k, (M.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (hR : RecOK M V hr io th x₀) (x y : Dw.La) :
    ((Dw.EF x y : ℤ) : ℚ) = Algebra.trace ℚ D.host.E
      (D.host.xi0 * V.hT (V.frame.equivFun.symm (io x)) (V.frame.equivFun.symm (io y))) := by
  have h1 : Dw.EF x y = -Dw.EF y x := by
    have h := Dw.alt (x + y)
    simp only [map_add, LinearMap.add_apply, Dw.alt] at h
    linarith
  rw [h1, Int.cast_neg, hR.2.2.2.1 y x, herm_gmW, ← map_neg]
  congr 1
  ring

theorem recOK_latIsom (M : GlobalTheory.FrameUnif.ModelsOf F r) (V : HSp D) (hr : V.rank = r)
    (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E))
    (th : ∀ k, (M.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (hR : RecOK M V hr io th x₀) :
    LatIsom V Dw.EF io :=
  ⟨1, fun x y => by rw [recOK_isom M V hr io th x₀ hR]; simp⟩

theorem recOK_gram (M : GlobalTheory.FrameUnif.ModelsOf F r) (V : HSp D) (hr : V.rank = r)
    (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E))
    (th : ∀ k, (M.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (hR : RecOK M V hr io th x₀) (k : Fin F.n) :
    (M.X k).Gm = gmW V hr := (hR.2.1 k).1

theorem neg_baseElement_im_neg_baseEmbedding (D : D7) (τ : D.host.E →+* ℂ) (hτ : τ D.host.sqrtMinusD = D.host.φ₀ D.host.sqrtMinusD) :
    (τ (-D.host.xi0)).im < 0 := by
  have h0 : D.host.φ₀ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ) := D.host.φ₀_mem
  have hd : (0 : ℝ) < Real.sqrt D.host.d := by
    have : D.host.d % 16 = 7 := D.host.hyp.2.2.2.1
    apply Real.sqrt_pos.2
    exact_mod_cast (by omega : 0 < D.host.d)
  have hn : (0 : ℝ) < (Ideal.absNorm D.host.ccK : ℝ) := by
    have : Ideal.absNorm D.host.ccK ≠ 0 := fun h => D.host.ccK_ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
    exact_mod_cast Nat.pos_of_ne_zero this
  have : τ (-D.host.xi0) = ((-(1 / ((Ideal.absNorm D.host.ccK : ℝ) * Real.sqrt D.host.d)) : ℝ) : ℂ) * Complex.I := by
    simp only [Formalism.BasicNotions.Host.xi0, map_neg, map_div₀, map_one, map_mul, map_natCast, hτ, h0]
    have h1 : ((Ideal.absNorm D.host.ccK : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    have h2 : ((Real.sqrt D.host.d : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
    push_cast
    field_simp
    simp
  rw [this, Complex.mul_I_im, Complex.ofReal_re]
  have : 0 < 1 / ((Ideal.absNorm D.host.ccK : ℝ) * Real.sqrt D.host.d) := by positivity
  linarith

theorem th_conj {τ : D.host.E →+* ℂ} {θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ} (h : Formalism.MainNotions.StandardLattice.IsInfEmb τ θ)
    (z : Ainf D.host.F ⊗[D.host.F] D.host.E) :
    θ (sigR (Ainf D.host.F) D.sp.cm.sig z) = starRingEnd ℂ (θ z) := by
  have hτ : ∀ x : D.host.E, τ (star x) = starRingEnd ℂ (τ x) := fun x => IsCMField.complexEmbedding_complexConj D.host.E τ x
  have hre : ∀ a : Ainf D.host.F, starRingEnd ℂ (θ (a ⊗ₜ[D.host.F] (1 : D.host.E))) = θ (a ⊗ₜ[D.host.F] (1 : D.host.E)) := by
    intro a
    refine DenseRange.induction_on (NumberField.InfiniteAdeleRing.denseRange_algebraMap D.host.F) a
      (isClosed_eq (Complex.continuous_conj.comp h.2) h.2) fun f => ?_
    have e : (algebraMap D.host.F (Ainf D.host.F) f) ⊗ₜ[D.host.F] (1 : D.host.E) =
        (1 : Ainf D.host.F) ⊗ₜ[D.host.F] (algebraMap D.host.F D.host.E f) := by
      exact (Algebra.TensorProduct.includeLeft (R := D.host.F) (S := D.host.F) (A := Ainf D.host.F) (B := D.host.E)).commutes f |>.trans
        ((Algebra.TensorProduct.includeRight (R := D.host.F) (A := Ainf D.host.F) (B := D.host.E)).commutes f).symm
    erw [e, h.1, ← hτ]
    rw [(D.sp.cm.fixed _).2 ⟨f, rfl⟩]
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]
  | tmul a x =>
    have e : ∀ y : D.host.E, a ⊗ₜ[D.host.F] y = (a ⊗ₜ[D.host.F] (1 : D.host.E)) * ((1 : Ainf D.host.F) ⊗ₜ[D.host.F] y) := by
      intro y; simp
    have e2 : sigR (Ainf D.host.F) D.sp.cm.sig (a ⊗ₜ[D.host.F] x) = a ⊗ₜ[D.host.F] (star x) := rfl
    rw [e2, e (star x), e x, map_mul, map_mul, map_mul, hre, h.1, h.1, hτ]

theorem cT_map {A : Type} [CommRing A] {n : Type} (s : A →+* A) (φ : A →+* ℂ)
    (h : ∀ z, φ (s z) = starRingEnd ℂ (φ z)) (M : Matrix n n A) :
    (Formalism.UG.cT s M).map φ = (M.map φ).conjTranspose := by
  ext a b
  exact h _

theorem uni_map {A : Type} [CommRing A] {n : Type} [Fintype n] (s : A →+* A) (φ : A →+* ℂ)
    (h : ∀ z, φ (s z) = starRingEnd ℂ (φ z)) (M J : Matrix n n A) (hM : Formalism.UG.cT s M * J * M = J)
    (J' M' : Matrix n n ℂ) (hJ : J.map φ = J') (hM' : M' = M.map φ) : M'.conjTranspose * J' * M' = J' := by
  subst hJ hM'
  rw [← cT_map s φ h, ← Matrix.map_mul, ← Matrix.map_mul, hM]

set_option maxHeartbeats 800000 in
theorem archM_unitary (V : HSp D) {τ : D.host.E →+* ℂ} {θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ}
    (h : Formalism.MainNotions.StandardLattice.IsInfEmb τ θ) (g : GA D V) :
    (archM V θ g).conjTranspose * V.gram.map τ * archM V θ g = V.gram.map τ := by
  have hg : Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) (matHom V g).1 * JR (AF D.host.F) V.gram * (matHom V g).1 =
      JR (AF D.host.F) V.gram := g.2
  let π : AF D.host.F ⊗[D.host.F] D.host.E →+* Ainf D.host.F ⊗[D.host.F] D.host.E :=
    (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom
  have hπ : ∀ z, π (sigR (AF D.host.F) D.sp.cm.sig z) = sigR (Ainf D.host.F) D.sp.cm.sig (π z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]
    | tmul a x => rfl
  have hJ : (JR (AF D.host.F) V.gram).map (θ.comp π) = V.gram.map τ := by
    ext a b
    exact h.1 _
  exact uni_map (sigR (AF D.host.F) D.sp.cm.sig) (θ.comp π) (fun z => (congrArg θ (hπ z)).trans (th_conj h (π z))) _ _ hg
    _ _ hJ rfl

theorem gram_eq {E : Type} [Field E] [NumberField E] [IsCMField E] (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (x : Matrix (Fin r) (Fin r) ℂ) : gram τ G x = (x.conjTranspose * (G.map τ).transpose * x).transpose := by
  ext a b
  simp only [gram, hermC, col, Matrix.of_apply, Matrix.transpose_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.map_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.star_def]
  ring

variable {σ' : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (D.host.E →+* ℂ)} {F : FamilyUnif Xo σ' ty} in

theorem markSpec_orthonormal (M : GlobalTheory.FrameUnif.ModelsOf F r) (V : HSp D) (hr : V.rank = r)
    (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E))
    (th : ∀ k, (M.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (hR : RecOK M V hr io th x₀) (h : GA D V)
    (p : Σ k, Frame (M.X k).Ψ r) (hp : MarkSpec M V hr io th x₀ h p) (τ : (M.X p.1).Ψ) :
    gram τ.1 (M.X p.1).Gm (mat p.2 τ) = Matrix.diagonal fun a : Fin r => ((sgn (M.X p.1).p0 (a : ℕ) : ℝ) : ℂ) := by
  obtain ⟨γ, -, -, -, h3⟩ := hp
  rw [← hR.2.2.2.2.2 p.1 τ.1 τ.2, h3 τ, gram_eq, gram_eq, (hR.2.1 p.1).1]
  have hu := archM_unitary V (hR.2.2.2.2.1 p.1 τ) (γ * h)
  subst hr
  have e1 : ∀ A : Matrix (Fin V.rank) (Fin V.rank) ℂ, Matrix.reindex (finCongr rfl) (finCongr rfl) A = A := fun A => rfl
  have e2 : ((-(Matrix.reindex (finCongr rfl) (finCongr rfl) V.gram).transpose).map τ.1).transpose = -(V.gram.map τ.1) := by
    ext a b; simp
  rw [e1, e2, Matrix.conjTranspose_mul]
  congr 1
  conv_rhs => rw [← hu]
  simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]

variable {σ' : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (D.host.E →+* ℂ)} {F : FamilyUnif Xo σ' ty} in

theorem exists_base_frame (M : GlobalTheory.FrameUnif.ModelsOf F r) (V : HSp D) (hr : V.rank = r)
    (hB : GlobalTheory.FrameUnif.ModelBase M) (hW : ∀ k, ModelW V hr (M.X k)) :
    ∃ x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ, ∀ k, IsOrthogonalFrame (M.X k) x₀ := by
  classical
  let k₀ : Fin F.n := ⟨0, F.n_pos⟩
  choose P _ hP using (M.X k₀).signature
  refine ⟨fun τ => if h : τ ∈ (M.X k₀).Ψ then P ⟨τ, h⟩ else 0, fun k τ hτ => ?_⟩
  have h0 : τ ∈ (M.X k₀).Ψ := ((hB.type k₀).2 τ).2 (((hB.type k).2 τ).1 hτ)
  have := hP ⟨τ, h0⟩
  rw [(hW k₀).1, (hB.type k₀).1] at this
  simp only [dif_pos h0]
  rw [(hW k).1, (hB.type k).1]
  exact this

end GlobalTheory.RecDictModel
