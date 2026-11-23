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
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryExistsWithPrescribedPartsStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicCompletionFractionalIdealDivisibleEqZero
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicCompletionRationalPointsAndApproximation
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ZeroMemLatOf
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsInverseUnitTower
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TypeFnPeriodExistModuliNonempty
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct Topology
open GlobalTheory.RecDict

namespace GlobalTheory.RecDict

open scoped Matrix nonZeroDivisors

theorem comp_adelic_of_tower (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
    (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) (ξ : E) (hξ : ξ ≠ 0)
    (A B : Type) [AddCommGroup A] [Module (𝓞 E) A] [AddCommGroup B] [Module (𝓞 E) B]
    (EA : A → A → ℤ) (EB : B → B → ℤ) (io : A →ₗ[𝓞 E] (Fin n → E)) (hio : Function.Injective io)
    (Λ : Submodule (𝓞 E) (Fin n → E)) (φ : B ≃ₗ[𝓞 E] Λ)
    (hL : (LinearMap.range io).FG) (hLs : Submodule.span E (LinearMap.range io : Set (Fin n → E)) = ⊤)
    (hΛ : Λ.FG) (hΛs : Submodule.span E (Λ : Set (Fin n → E)) = ⊤)
    (hA : ∀ x y, ((EA x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * ∑ a, ∑ b, io x a * G a b * c (io y b)))
    (hB : ∀ x y, ((EB x y : ℤ) : ℚ) =
      Algebra.trace ℚ E (ξ * ∑ a, ∑ b, (φ x : Fin n → E) a * G a b * c ((φ y : Fin n → E) b)))
    (f : ℕ → A →ₗ[𝓞 E] B)
    (h1 : ∀ n m : ℕ, 0 < n → 0 < m → ∀ a, ∃ e, f (n * m) a = f n a + n • e)
    (h2 : ∀ n : ℕ, 0 < n → (∀ a, (∃ e, f n a = n • e) ↔ ∃ e, a = n • e) ∧ ∀ a', ∃ a e, a' = f n a + n • e)
    (h3 : ∀ n : ℕ, 0 < n → ∀ a a', (n : ℤ) ∣ EB (f n a) (f n a') - EA a a') :
    ∃ g : GL (Fin n) (AdLat.RA F E),
      (g : Matrix (Fin n) (Fin n) (AdLat.RA F E)).mulVec '' (AdLat.hat F (LinearMap.range io : Set (Fin n → E))) =
        (AdLat.hat F (Λ : Set (Fin n → E))) ∧
      (∀ N : ℕ, 0 < N → ∀ a : A, ∃ w ∈ (AdLat.hat F (Λ : Set (Fin n → E))),
        (g : Matrix (Fin n) (Fin n) (AdLat.RA F E)) *ᵥ AdLat.fv F (io a) =
          AdLat.fv F (φ (f N a) : Fin n → E) + N • w) ∧
      ∀ x y, AdLat.hermA c G ((g : Matrix (Fin n) (Fin n) (AdLat.RA F E)) *ᵥ x)
        ((g : Matrix (Fin n) (Fin n) (AdLat.RA F E)) *ᵥ y) = AdLat.hermA c G x y := by
  let ψ : A ≃ₗ[𝓞 E] LinearMap.range io := LinearEquiv.ofInjective io hio
  have hψ : ∀ a, (ψ a : Fin n → E) = io a := fun a => rfl
  let f' : ℕ → (LinearMap.range io →ₗ[𝓞 E] Λ) := fun N => φ.toLinearMap ∘ₗ f N ∘ₗ ψ.symm.toLinearMap
  have hf' : ∀ N a, f' N (ψ a) = φ (f N a) := fun N a => by simp [f']
  obtain ⟨g, hg1, hg2, hg3⟩ := AdLat.exists_adelic_matrix_of_tower F E n (LinearMap.range io) Λ f' hL hLs hΛ hΛs
    (fun N m hN hm a => by
      obtain ⟨a, rfl⟩ := ψ.surjective a
      obtain ⟨e, he⟩ := h1 N m hN hm a
      exact ⟨φ e, by rw [hf', hf', he, map_add, map_nsmul]⟩)
    (fun N hN => by
      refine ⟨fun a => ?_, fun a' => ?_⟩
      · obtain ⟨a, rfl⟩ := ψ.surjective a
        rw [hf']
        constructor
        · rintro ⟨v, hv⟩
          obtain ⟨v, rfl⟩ := φ.surjective v
          obtain ⟨e, he⟩ := ((h2 N hN).1 a).1 ⟨v, φ.injective (by rw [hv, map_nsmul])⟩
          exact ⟨ψ e, by rw [he, map_nsmul]⟩
        · rintro ⟨v, hv⟩
          obtain ⟨v, rfl⟩ := ψ.surjective v
          obtain ⟨e, he⟩ := ((h2 N hN).1 a).2 ⟨v, ψ.injective (by rw [hv, map_nsmul])⟩
          exact ⟨φ e, by rw [he, map_nsmul]⟩
      · obtain ⟨b, rfl⟩ := φ.surjective a'
        obtain ⟨a, e, he⟩ := (h2 N hN).2 b
        exact ⟨ψ a, φ e, by rw [hf', ← map_nsmul, ← map_add, ← he]⟩)
  refine ⟨g, hg1, fun N hN a => ?_, ?_⟩
  · obtain ⟨w, hw, h⟩ := hg2 N hN (ψ a)
    exact ⟨w, hw, by rw [← hf', ← h, hψ]⟩
  let J : FractionalIdeal (𝓞 E)⁰ E := FractionalIdeal.spanSingleton _ ξ⁻¹ * FractionalIdeal.dual ℤ ℚ 1
  have hJ : ∀ z : E, (∀ s : 𝓞 E, ∃ k : ℤ, Algebra.trace ℚ E (ξ * ((s : E) * z)) = k) → z ∈ J := by
    intro z hz
    refine FractionalIdeal.mem_singleton_mul.2 ⟨ξ * z, ?_, by field_simp⟩
    rw [FractionalIdeal.mem_dual (one_ne_zero : (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0)]
    intro a ha
    obtain ⟨s, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
    obtain ⟨k, hk⟩ := hz s
    refine ⟨k, ?_⟩
    rw [Algebra.traceForm_apply, eq_intCast, ← hk]
    congr 1
    change ξ * ((s : E) * z) = ξ * z * (s : E)
    ring
  have hsm : ∀ (s : 𝓞 E) (x y : Fin n → E), (∑ a, ∑ b, (s • x) a * G a b * c (y b)) =
      (s : E) * ∑ a, ∑ b, x a * G a b * c (y b) := by
    intro s x y
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    change ((s : E) * x a) * _ * _ = _
    ring
  refine hg3 c G J (fun x hx y hy => hJ _ fun s => ?_) (fun N hN x y => ?_)
  · obtain ⟨a, ha⟩ := φ.surjective ⟨x, hx⟩
    obtain ⟨b, hb⟩ := φ.surjective ⟨y, hy⟩
    refine ⟨EB (s • a) b, ?_⟩
    rw [hB, map_smul, ha, hb, ← hsm]
    rfl
  · obtain ⟨a, rfl⟩ := ψ.surjective x
    obtain ⟨b, rfl⟩ := ψ.surjective y
    rw [hf', hf', hψ, hψ]
    have hN' : (N : E) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
    have hN'' : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
    refine ⟨(N : E)⁻¹ * ((∑ i, ∑ j, (φ (f N a) : Fin n → E) i * G i j * c ((φ (f N b) : Fin n → E) j)) -
      ∑ i, ∑ j, io a i * G i j * c (io b j)), hJ _ fun s => ?_, ?_⟩
    · obtain ⟨k, hk⟩ := h3 N hN (s • a) b
      refine ⟨k, ?_⟩
      have hk' := congrArg (Int.cast : ℤ → ℚ) hk
      push_cast at hk'
      rw [hA, hB, map_smul, map_smul, map_smul, Submodule.coe_smul, hsm, hsm, ← map_sub] at hk'
      apply mul_left_cancel₀ hN''
      rw [← hk', ← nsmul_eq_mul, ← map_nsmul, nsmul_eq_mul]
      congr 1
      field_simp
    · rw [nsmul_eq_mul, mul_inv_cancel_left₀ hN', add_sub_cancel]

theorem comp_AA_ne_zero (D : D7) : D.host.AA ≠ 0 := by
  refine mul_ne_zero ?_ (inv_ne_zero ?_)
  · rw [FractionalIdeal.coeIdeal_ne_zero]
    intro h
    exact D.host.ccK_ne_bot ((Ideal.map_eq_bot_iff_of_injective (RingOfIntegers.algebraMap.injective _ _)).1 h)
  · rw [FractionalIdeal.coeIdeal_ne_zero]
    intro h
    have h1 := D.host.𝔟_spec.1
    rw [h, Ideal.bot_mul] at h1
    exact differentIdeal_ne_bot h1

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem comp_latG (D : D7) (V : HSp D) :
    (latG V 1).FG ∧ Submodule.span D.host.E (latG V 1 : Set (Fin V.rank → D.host.E)) = ⊤ ∧ ∀ g : GA D V,
      (latG V g : Set (Fin V.rank → D.host.E)) = AdLat.latOf D.host.F (finHom V g).1 (latG V 1) ∧
      (latGHat V g : Set (Fin V.rank → AdLat.RA D.host.F D.host.E)) =
        (finHom V g).1.mulVec '' (AdLat.hat D.host.F (latG V 1 : Set (Fin V.rank → D.host.E))) := by
  let e : V.V →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E) :=
    (V.frame.equivFun : V.V →ₗ[D.host.E] (Fin V.rank → D.host.E)).restrictScalars (𝓞 D.host.E)
  let L : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) := V.L0.map e
  have hfg : L.FG := V.standardTuple_isLattice.fg.map e
  have hsp : Submodule.span D.host.E (L : Set (Fin V.rank → D.host.E)) = ⊤ := by
    have h := congrArg (Submodule.map (V.frame.equivFun : V.V →ₗ[D.host.E] (Fin V.rank → D.host.E)))
      V.standardTuple_isLattice.span_eq_top
    rw [Submodule.map_span, Submodule.map_top, LinearEquiv.range] at h
    exact h
  have hhat : latHat V = AdLat.hat D.host.F (L : Set (Fin V.rank → D.host.E)) := by
    unfold latHat AdLat.hat
    congr 1
    ext z
    constructor
    · rintro ⟨a, ha, x, hx, rfl⟩
      exact ⟨a, ha, e x, ⟨x, hx, rfl⟩, rfl⟩
    · rintro ⟨a, ha, _, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨a, ha, x, hx, rfl⟩
  have h1 : latG V 1 = Submodule.span (𝓞 D.host.E) {w | ∃ a ∈ D.host.AA, ∃ x ∈ L, w = a • x} := by
    unfold latG gLat
    congr 1
    ext w
    have hc := (AdLat.hat_rational_points_and_approx D.host.F D.host.E V.rank L hfg hsp).1
    simp only [map_one, Units.val_one, Set.mem_setOf_eq, hhat, Set.mem_image, Matrix.one_mulVec, exists_eq_right,
      SetLike.mem_coe, ← hc]
    rfl
  have hs := fun g : GA D V => AdLat.scale_latOf D.host.F D.host.E V.rank L (finHom V g) D.host.AA (latG V 1)
    hfg hsp (comp_AA_ne_zero D) h1
  refine ⟨(hs 1).2.2.1, (hs 1).2.2.2, fun g => ⟨?_, ?_⟩⟩
  · rw [← (hs g).1]
    unfold latG gLat
    rw [hhat]
    rfl
  · rw [← (hs g).2.1]
    unfold latGHat gLat
    rw [hhat]

theorem comp_mem_HR (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
    (c : E ≃ₐ[F] E) (σ : E →ₐ[F] E) (hc : ∀ x, c x = σ x) (G : Matrix (Fin n) (Fin n) E)
    (g : GL (Fin n) (AdLat.RA F E))
    (hg : ∀ x y, AdLat.hermA c (-G.transpose) (g.1 *ᵥ x) (g.1 *ᵥ y) = AdLat.hermA c (-G.transpose) x y) :
    g ∈ HR (Af F) σ G := by
  have hc' : (c : E →ₐ[F] E) = σ := AlgHom.ext hc
  change Formalism.UG.cT _ _ * _ * _ = _
  ext i j
  have h := hg (Pi.single j 1) (Pi.single i 1)
  simp only [AdLat.hermA, AdLat.sg, hc', Matrix.mulVec_single_one, Matrix.col_apply, Matrix.neg_apply,
    Matrix.transpose_apply, TensorProduct.tmul_neg, mul_neg, neg_mul, Finset.sum_neg_distrib, neg_inj] at h
  simp only [Pi.single_apply, apply_ite (Algebra.TensorProduct.map (AlgHom.id F (FiniteAdeleRing (𝓞 F) F)) σ),
    map_one, map_zero, mul_ite, ite_mul, mul_one, mul_zero, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
  simp only [Matrix.mul_apply, Formalism.UG.cT, JR, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
  refine Eq.trans ?_ h
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  change _ * (1 ⊗ₜ _) * _ = _ * _ * sigR _ σ _
  ring

theorem comp_sub_eq {A : Type} [AddCommGroup A] (N : ℕ) (x e w : A) : x - (x + N • e + N • w) = N • -(e + w) := by
  rw [smul_neg, smul_add]
  abel

theorem comp_reindex_one {A : Type} [CommRing A] {n : ℕ} (θ : A →+* ℂ) (x : Matrix (Fin n) (Fin n) ℂ) :
    x = Matrix.reindex (finCongr rfl) (finCongr rfl) (((1 : GL (Fin n) A) : Matrix (Fin n) (Fin n) A).map θ) * x := by
  rw [Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.reindex_apply,
    Matrix.submatrix_one_equiv, one_mul]

theorem comp_attained (D : D7) (V : HSp D) {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {σ' : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (D.host.E →+* ℂ)} (F : FamilyUnif Xo σ' ty)
    (hty : IsTypeFn H Dw.p Dw.q ty) {r : ℕ} (hr : V.rank = r) (M : GlobalTheory.FrameUnif.ModelsOf F r)
    (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E))
    (th : ∀ k, (M.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (h : RecOK M V hr io th x₀) (k : Fin F.n) :
    ∃ g ∈ GfC V, ∃ p : Σ k, Frame (M.X k).Ψ r, p.1 = k ∧ (∀ τ : (M.X p.1).Ψ, mat p.2 τ = x₀ τ.1) ∧
      MarkSpec M V hr io th x₀ g p := by
  subst hr
  obtain ⟨hbase, hW, ⟨hinj, hrange⟩, hEF, -, -⟩ := h
  obtain ⟨-, P, hP⟩ := (PeriodExists.typeFn_period_exist _ H (F.Di k)).2.1 g ty
    (by rw [(F.sig k).1, (F.sig k).2]; exact hty)
  obtain ⟨f, h1, h2, h3, h4⟩ := familyUnif_lattice_genus _ H Dw l Xo σ' g ty F k P hP
  let c : D.host.E ≃ₐ[D.host.F] D.host.E :=
    AlgEquiv.ofAlgHom D.sp.cm.sig D.sp.cm.sig (AlgHom.ext fun x => star_star x) (AlgHom.ext fun x => star_star x)
  obtain ⟨hfg, hsp, hlat⟩ := comp_latG D V
  rw [← hrange] at hfg hsp hlat
  have hξ : -(-D.host.xi0) ≠ 0 := by
    rw [← (hW k).2]
    exact neg_ne_zero.2 (M.X k).ξ0_ne
  obtain ⟨gf, hg1, hg2, hg3⟩ := comp_adelic_of_tower D.host.F D.host.E V.rank c (-V.gram.transpose)
    (-(-D.host.xi0)) hξ Dw.La (F.Di k).La (fun x y => Dw.EF x y) (fun x y => (F.Di k).EF x y) io hinj
    (M.X k).Λ (M.φ k) hfg hsp (M.X k).Λ_fg (M.X k).Λ_span hEF
    (fun x y => by
      have := hbase.ef k x y
      rw [(hW k).1, (hW k).2] at this
      exact this) f h1 h2 h3
  obtain ⟨u, hu, hug⟩ := (GlobalTheory.T.adelicUnitary_exists_with_prescribed_parts D V).1 gf (comp_mem_HR _ _ _ c _ (fun _ => rfl) _ gf hg3)
  have hc := (AdLat.hat_rational_points_and_approx D.host.F D.host.E V.rank (M.X k).Λ (M.X k).Λ_fg
    (M.X k).Λ_span).1
  refine ⟨u, hu, ⟨k, fun τ => x₀ τ.1⟩, rfl, fun τ => rfl, 1, one_mem _, ?_, fun a ha => ?_, fun τ => ?_⟩
  · rw [one_mul, (hlat u).1, hug]
    refine Eq.trans ?_ (Set.image_id _).symm
    ext v
    rw [AdLat.latOf, hg1]
    exact (hc v).symm
  · obtain ⟨e, he⟩ := h4 a ha
    obtain ⟨w, hw, hgw⟩ := hg2 l.M (lt_of_lt_of_le (by norm_num) l.three_le) a
    have hmem : ∀ z, z ∈ latGHat V u ↔ z ∈ AdLat.hat D.host.F ((M.X k).Λ : Set (Fin V.rank → D.host.E)) := by
      intro z
      rw [← SetLike.mem_coe, (hlat u).2, hug, hg1, SetLike.mem_coe]
    rw [one_mul, hug]
    refine ⟨-(AdLat.fv D.host.F (M.φ k e : Fin V.rank → D.host.E) + w),
      (hmem _).2 (neg_mem (add_mem ((hc _).2 (M.φ k e).2) hw)), ?_⟩
    change AdLat.fv D.host.F (M.φ k (F.t k a) : Fin V.rank → D.host.E) - gf.1 *ᵥ AdLat.fv D.host.F (io a) = _
    rw [hgw, he, map_add, map_nsmul, Submodule.coe_add, Submodule.coe_smul_of_tower, AdLat.cap_fv_add,
      AdLat.cap_fv_nsmul]
    exact comp_sub_eq _ _ _ _
  · have hu' : infHom V u = 1 := hu
    rw [one_mul, archM, hu']
    exact comp_reindex_one _ _

theorem component_attained_at_base_frame : ∀ (D : D7) (Q : Par D), Q.Pins → ∀ (j : ℕ) (hj : InR D j) (σ' : KA Q.l →+* ℂ) (g : ℕ) (ty : Fin g → (D.host.E →+* ℂ)) (F : FamilyUnif (Q.Xo j) σ' ty), σ' (baseKA Q.l).ρ = Q.H.rt0 → IsTypeFn Q.H (Q.Dw j).p (Q.Dw j).q ty → ∀ (M : GlobalTheory.FrameUnif.ModelsOf F D.R.r) (io : (Q.Dw j).La →ₗ[𝓞 D.host.E] (Fin (D.sp.W j).rank → D.host.E)) (th : ∀ k, (M.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ), RecOK M (D.sp.W j) (D.sp.W_rank j hj.1 hj.2) io th x₀ → ∀ k : Fin F.n, ∃ g ∈ GfC (D.sp.W j), ∃ p : Σ k, Frame (M.X k).Ψ D.R.r, p.1 = k ∧ (∀ τ : (M.X p.1).Ψ, mat p.2 τ = x₀ τ.1) ∧ MarkSpec M (D.sp.W j) (D.sp.W_rank j hj.1 hj.2) io th x₀ g p :=
  fun D _ _ j hj _ _ _ F _ hty M io th x₀ h k =>
    comp_attained D (D.sp.W j) F hty (D.sp.W_rank j hj.1 hj.2) M io th x₀ h k

end GlobalTheory.RecDict
