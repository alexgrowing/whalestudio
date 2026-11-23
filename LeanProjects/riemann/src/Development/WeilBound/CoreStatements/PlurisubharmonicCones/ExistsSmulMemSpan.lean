import Development.WeilBound.CoreStatements.PlurisubharmonicCones.FinrankOfLieMult
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.ExistsGram
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeInnerProductPullbackUniqueStatement
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.PadicEmbeddingDiscreteValuationRingStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExtendedArcUAdicUniformisationOfArcData
import GroundTheory.HeightsAndTheta.Heights.ArithDegree

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open GroundTheory.Heights₂.Heights TensorProduct

set_option linter.unusedSectionVars false

namespace LevelTowerAlt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_push {S S' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {f : S' ⟶ S} (m : SABMap t' t f)
    {R : Type} [CommRing R] {x' : Sp R ⟶ S'} {x : Sp R ⟶ S} (hx : x = x' ≫ f) (v' : epsAt x' ⟶ t'.G) :
    ∃ v : epsAt x ⟶ t.G, v'.left ≫ m.φ = v.left := by
  refine ⟨Over.homMk (v'.left ≫ m.φ) ?_, rfl⟩
  have h1 : v'.left ≫ t'.G.hom = spMap (algebraMap R (DualNumber R)) ≫ x' := Over.w v'
  change (v'.left ≫ m.φ) ≫ t.G.hom = spMap (algebraMap R (DualNumber R)) ≫ x
  rw [Category.assoc, m.cart.1.w, ← Category.assoc, h1, hx, Category.assoc]

theorem hodgeInnerProduct_pushforward_iff {S S' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {f : S' ⟶ S} (m : SABMap t' t f)
    {x' : Sp ℂ ⟶ S'} {x : Sp ℂ ⟶ S} (hx : x = x' ≫ f) {v' w' : epsAt x' ⟶ t'.G} {v w : epsAt x ⟶ t.G}
    (hv : v'.left ≫ m.φ = v.left) (hw : w'.left ≫ m.φ = w.left) (c : ℂ) :
    HodgeIP t'.G t'.PP.L x' v' w' c ↔ HodgeIP t.G t.PP.L x v w c := by
  subst hx
  exact (GlobalTheory.T.hodge_inner_product_pullback_unique E H S' S t' t f m x' v' w' v w hv hw).1 c

theorem exists_smul_mem_span {L : Type} [Field L] [NumberField L] (B : HermitianBundle.{0} L)
    (F : Submodule (𝓞 L) B.carrier) {n : ℕ} (hn : B.rank F = n) :
    ∃ x : Fin n → B.carrier, (∀ i, x i ∈ F) ∧ LinearIndependent (𝓞 L) x ∧
      ∀ z ∈ F, ∃ u : 𝓞 L, u ≠ 0 ∧ u • z ∈ Submodule.span (𝓞 L) (Set.range x) := by
  subst hn
  obtain ⟨y, hy⟩ := B.exists_linearIndependent_rank F
  have hfin := finite_quotient_span hy (Fintype.card_fin _)
  refine ⟨fun i => (y i : B.carrier), fun i => (y i).2, hy.map' F.subtype F.ker_subtype, fun z hz => ?_⟩
  refine ⟨(Nat.card (F ⧸ Submodule.span (𝓞 L) (Set.range y)) : 𝓞 L), Nat.cast_ne_zero.2 Nat.card_pos.ne', ?_⟩
  have h1 := card_nsmul_eq_zero' (G := F ⧸ Submodule.span (𝓞 L) (Set.range y)) (x := Submodule.Quotient.mk ⟨z, hz⟩)
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h1
  have h2 := Submodule.mem_map_of_mem (f := F.subtype) h1
  rw [Submodule.map_span, ← Set.range_comp] at h2
  rw [Nat.cast_smul_eq_nsmul]
  exact h2

variable {L : Type} [Field L] [NumberField L] {t' : SAB H (Sp (𝓞 L))} {B : HermitianBundle.{0} L}
  (MB : LieModel t'.G (𝟙 _) B.carrier) {ρM : 𝓞 E →+* Module.End (𝓞 L) B.carrier}

theorem rank_eig (hρ : MB.IsActOf t'.act.act ρM) {tB : SAB H (Sp L)} (m' : SABMap tB t' (spMap (algebraMap (𝓞 L) L)))
    (σ : L →+* ℂ) (s : 𝓞 E →+* 𝓞 L) {n : ℕ}
    (h : LieMult tB.act (spMap σ) ((σ.comp (algebraMap (𝓞 L) L)).comp s) n) : B.rank (eigSp ρM s) = n := by
  have hg : Function.Injective (σ.comp (algebraMap (𝓞 L) L)) := σ.injective.comp (IsFractionRing.injective _ _)
  obtain ⟨W, _, _, MW, ρW, j, h1, -, -, h2⟩ := exists_model MB hρ m' _ hg (spMap σ) (spMap_comp _ _).symm
  obtain ⟨x, hx, hli, hsp⟩ := exists_smul_mem_span B (eigSp ρM s) rfl
  obtain ⟨h3, h4⟩ := h2 s _ x hx hli fun z hz => (hsp z hz).imp fun u hu =>
    ⟨IsUnit.mk0 _ ((map_ne_zero_iff _ hg).2 hu.1), hu.2⟩
  rw [← finrank_of_lieMult MW h1 h, ← h4, finrank_span_eq_card h3, Fintype.card_fin]

theorem exists_vec (hρ : MB.IsActOf t'.act.act ρM) {S S₀ : Scheme.{0}} {tK : SAB H S} {f : S ⟶ Sp (𝓞 L)}
    (n : SABMap tK t' f) {t₀ : SAB H S₀} {f₀ : S ⟶ S₀} (mf : SABMap tK t₀ f₀) {K : Type} [Field K] (g : 𝓞 L →+* K)
    (hg : Function.Injective g) (x : Sp K ⟶ S) (hx : x ≫ f = spMap g) (x₀ : Sp K ⟶ S₀) (hx₀ : x₀ = x ≫ f₀) :
    ∃ (vK : B.carrier → (epsAt x ⟶ tK.G)) (vec : B.carrier → (epsAt x₀ ⟶ t₀.G)),
      (∀ z, (vK z).left ≫ n.φ = spMap (dualMap g) ≫ (MB.pt z).left) ∧ (∀ z, (vK z).left ≫ mf.φ = (vec z).left) ∧
      (∀ z, IsTanAt t₀.G x₀ (vec z)) ∧
      (∀ (s : 𝓞 E →+* 𝓞 L) (r : ℕ) (y : Fin r → B.carrier), (∀ k, y k ∈ eigSp ρM s) → LinearIndependent (𝓞 L) y →
        (∀ z ∈ eigSp ρM s, ∃ u : 𝓞 L, u ≠ 0 ∧ u • z ∈ Submodule.span (𝓞 L) (Set.range y)) →
        IsEigFrame t₀.act x₀ (g.comp s) fun k => vec (y k)) ∧
      ∀ (r : ℕ) (y : Fin r → B.carrier) (z : B.carrier) (u : 𝓞 L) (T : Fin r → 𝓞 L), u ≠ 0 →
        u • z = ∑ k, T k • y k → IsComb (fun k => (g u)⁻¹ * g (T k)) (fun k => vec (y k)) (vec z) := by
  obtain ⟨W, _, _, MW, ρW, j, h1, h2, h3, h4⟩ := exists_model MB hρ n g hg x hx
  obtain ⟨M₀, h5, h6⟩ := push_model mf hx₀ MW ρW h1
  have hb := GlobalTheory.T.lie_model_eigenvectors_action S₀ K t₀.G x₀ W M₀
  refine ⟨fun z => MW.pt (j z), fun z => M₀.pt (j z), h2, fun z => h6 _, fun z => M₀.tan _,
    fun s r y hy hli hsp => ?_, fun r y z u T hu h => ?_⟩
  · exact ((hb.2 _ t₀.act ρW _ h5).2 r fun k => j (y k)).2 (h4 s r y hy hli fun z hz => (hsp z hz).imp fun u hu =>
      ⟨IsUnit.mk0 _ ((map_ne_zero_iff _ hg).2 hu.1), hu.2⟩)
  · refine (hb.1 r _ (fun k => j (y k)) _).2 (congrArg M₀.pt ?_)
    have hu' : g u ≠ 0 := (map_ne_zero_iff _ hg).2 hu
    have h7 := congrArg j h
    rw [h3, map_sum] at h7
    simp only [h3] at h7
    simp only [mul_smul]
    rw [← Finset.smul_sum, ← h7, smul_smul, inv_mul_cancel₀ hu', one_smul]

variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {F : Type} [Field F] [NumberField F]
  {β : c.F →+* F} {e : L →+* F} {tK : SAB H (Sp F)} {y : Sp F ⟶ Xo.XF c} {U : Set (Xo.XF c)} {τ : E →+* ℂ}
  {φ : FrameFn Xo c} {s₁ s₂ : 𝓞 E →+* 𝓞 L}

theorem inf_norm (hρ : MB.IsActOf t'.act.act ρM) (hfib : IsFibre (HodgeIP t'.G t'.PP.L) (𝟙 _) B MB)
    (n : SABMap tK t' (spMap (e.comp (algebraMap (𝓞 L) L)))) (mf : SABMap tK Xo.univ.t (under y))
    (hy : y ≫ pullback.snd _ _ = spMap β) (hU : Set.range y ⊆ U) (hφ : IsLineFn U τ φ)
    (hs₁ : β.comp (tauIn c τ) = (e.comp (algebraMap (𝓞 L) L)).comp s₁)
    (hs₂ : β.comp (tauIn c (ComplexEmbedding.conjugate τ)) = (e.comp (algebraMap (𝓞 L) L)).comp s₂)
    {vK : B.carrier → (epsAt (𝟙 (Sp F)) ⟶ tK.G)} {vec : B.carrier → (epsAt (under y) ⟶ Xo.univ.t.G)}
    (h1 : ∀ z, (vK z).left ≫ n.φ = spMap (dualMap (e.comp (algebraMap (𝓞 L) L))) ≫ (MB.pt z).left)
    (h2 : ∀ z, (vK z).left ≫ mf.φ = (vec z).left) {x₁ : Fin D.p → B.carrier} {x₂ : Fin D.q → B.carrier}
    (hx₁ : (∀ i, x₁ i ∈ eigSp ρM s₁) ∧ LinearIndependent (𝓞 L) x₁ ∧
      ∀ z ∈ eigSp ρM s₁, ∃ u : 𝓞 L, u ≠ 0 ∧ u • z ∈ Submodule.span (𝓞 L) (Set.range x₁))
    (hx₂ : (∀ i, x₂ i ∈ eigSp ρM s₂) ∧ LinearIndependent (𝓞 L) x₂ ∧
      ∀ z ∈ eigSp ρM s₂, ∃ u : 𝓞 L, u ≠ 0 ∧ u • z ∈ Submodule.span (𝓞 L) (Set.range x₂))
    (hfr : IsFramed U τ β y (fun k => vec (x₁ k)) fun k => vec (x₂ k)) (s : F →+* ℂ) {r : ℝ}
    (hN : HasInfNorm U τ φ (s.comp β) r) :
    r = Real.log ‖s (φ F y (fun k => vec (x₁ k)) fun k => vec (x₂ k))‖ + Real.log ‖B.gramDet (s.comp e) x₁‖ / 2 -
      Real.log ‖B.gramDet (s.comp e) x₂‖ / 2 := by
  have hg : Function.Injective ((s.comp e).comp (algebraMap (𝓞 L) L)) :=
    (s.comp e).injective.comp (IsFractionRing.injective _ _)
  have hx : spMap s ≫ spMap (e.comp (algebraMap (𝓞 L) L)) = spMap ((s.comp e).comp (algebraMap (𝓞 L) L)) :=
    (spMap_comp _ _).symm
  obtain ⟨wK, wec, k1, k2, k3, k4, -⟩ := exists_vec MB hρ n mf _ hg (spMap s) hx (under (spMap s ≫ y))
    (Category.assoc _ _ _)
  have hfr' : IsFramed U τ (s.comp β) (spMap s ≫ y) (fun k => wec (x₁ k)) fun k => wec (x₂ k) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [Category.assoc, hy, spMap_comp]
    · rintro _ ⟨a, rfl⟩
      exact hU ⟨_, (Scheme.Hom.comp_apply _ _ _).symm⟩
    · rw [RingHom.comp_assoc, hs₁]
      exact k4 s₁ _ x₁ hx₁.1 hx₁.2.1 hx₁.2.2
    · rw [RingHom.comp_assoc, hs₂]
      exact k4 s₂ _ x₂ hx₂.1 hx₂.2.1 hx₂.2.2
  have hbc : ∀ z, (wec z).left = spMap (dualMap s) ≫ (vec z).left := fun z => by
    have h3 := left_eq_of_cart n s (Category.comp_id _).symm (vK z) (wK z) (by
      rw [k1, h1, ← Category.assoc, ← spDual_comp, RingHom.comp_assoc])
    rw [← k2, ← h2, h3, Category.assoc]
  have hnat := hφ.nat F ℂ s β y _ _ (spMap s ≫ y) (fun k => wec (x₁ k)) (fun k => wec (x₂ k)) hfr rfl
    (fun _ => hbc _) fun _ => hbc _
  have hgram : ∀ {m : ℕ} (x : Fin m → B.carrier), ∃ Γ, IsHodgeGram Xo.univ.t.G Xo.univ.t.PP.L (under (spMap s ≫ y))
      (fun k => wec (x k)) Γ ∧ Γ.det = B.gramDet (s.comp e) x := by
    intro m x
    obtain ⟨Γ, hΓ⟩ := Gram.exists_gram E H _ Xo.univ.t Xo.univ.proper Xo.univ.ample Xo.univ.ktriv _ m
      (fun k => wec (x k)) fun k => k3 _
    refine ⟨Γ, hΓ, ?_⟩
    have hpt : spMap ((s.comp e).comp (algebraMap (𝓞 L) L)) ≫ 𝟙 _ =
        spMap s ≫ spMap (e.comp (algebraMap (𝓞 L) L)) := (Category.comp_id _).trans hx.symm
    choose vv hvv using fun z => exists_push n hpt (wK z)
    have hl : ∀ z, MB.Lifts ((s.comp e).comp (algebraMap (𝓞 L) L)) (𝟙 t'.G.left) z (vv z) := fun z =>
      (Category.comp_id _).trans ((hvv z).symm.trans (k1 z))
    have h3 := Gram.gram_eq _ Xo.univ.t.G Xo.univ.t.PP.L _ m (fun k => wec (x k)) Γ
      (Matrix.of fun i j => (B.metric.form (s.comp e)).inner ((1 : ComplexAt (s.comp e)) ⊗ₜ[𝓞 L] x i)
        ((1 : ComplexAt (s.comp e)) ⊗ₜ[𝓞 L] x j)) Xo.univ.t.PP.isLB (fun k => k3 _) hΓ fun i j =>
      (hodgeInnerProduct_pushforward_iff mf (Category.assoc _ _ _) (k2 _) (k2 _) _).1
        ((hodgeInnerProduct_pushforward_iff n hpt (hvv _) (hvv _) _).2 (hfib (s.comp e) (x i) (x j) _ _ (hl _) (hl _)))
    rw [HermitianBundle.gramDet, h3, Matrix.det_transpose]
  obtain ⟨Γ, hΓ, e1⟩ := hgram x₁
  obtain ⟨Δ, hΔ, e2⟩ := hgram x₂
  have h4 := hN _ _ _ Γ Δ hfr' hΓ hΔ
  rw [hnat, e1, e2] at h4
  rw [← h4]
  ring

theorem int_frame (hρ : MB.IsActOf t'.act.act ρM) (n : SABMap tK t' (spMap (e.comp (algebraMap (𝓞 L) L))))
    (mf : SABMap tK Xo.univ.t (under y)) {V : Type} [CommRing V] [IsDomain V] [Algebra V F] (gV : 𝓞 L →+* V)
    (hgV : (algebraMap V F).comp gV = e.comp (algebraMap (𝓞 L) L)) {T : SAB H (Sp V)} (mT : SABMap T t' (spMap gV))
    (m'' : SABMap tK T (spMap (algebraMap V F))) (hm : n.φ = m''.φ ≫ mT.φ)
    {vK : B.carrier → (epsAt (𝟙 (Sp F)) ⟶ tK.G)} {vec : B.carrier → (epsAt (under y) ⟶ Xo.univ.t.G)}
    (h1 : ∀ z, (vK z).left ≫ n.φ = spMap (dualMap (e.comp (algebraMap (𝓞 L) L))) ≫ (MB.pt z).left)
    (h2 : ∀ z, (vK z).left ≫ mf.φ = (vec z).left) (s : 𝓞 E →+* 𝓞 L) {r : ℕ} (x : Fin r → B.carrier)
    (hx : ∀ k, x k ∈ eigSp ρM s) (hli : LinearIndependent (𝓞 L) x)
    (hsp : ∀ z ∈ eigSp ρM s, ∃ u, IsUnit (gV u) ∧ u • z ∈ Submodule.span (𝓞 L) (Set.range x)) :
    IsIntFrame mf m'' ((e.comp (algebraMap (𝓞 L) L)).comp s) fun k => vec (x k) := by
  have hg : Function.Injective gV := by
    have h : Function.Injective ((algebraMap V F).comp gV) := by
      rw [hgV]
      exact e.injective.comp (IsFractionRing.injective _ _)
    exact Function.Injective.of_comp (f := algebraMap V F) h
  obtain ⟨W, _, _, MW, ρW, j, k1, k2, -, k4⟩ := exists_model MB hρ mT gV hg (𝟙 _) (Category.id_comp _)
  refine ⟨gV.comp s, fun k => MW.pt (j (x k)), ?_, ?_, fun k => ⟨(vK (x k)).left, h2 _, ?_⟩⟩
  · rw [← RingHom.comp_assoc, hgV]
  · exact (((GlobalTheory.T.lie_model_eigenvectors_action _ V T.G _ W MW).2 _ T.act ρW _ k1).2 r fun k => j (x k)).2 (k4 s r x hx hli hsp)
  · obtain ⟨v, hv⟩ := exists_push m'' (x := spMap (algebraMap V F) ≫ 𝟙 _)
      ((Category.comp_id _).trans (Category.id_comp _).symm) (vK (x k))
    rw [hv]
    refine left_eq_of_cart mT (algebraMap V F) rfl _ v ?_
    rw [← hv, Category.assoc, ← hm, h1, k2, ← Category.assoc, ← spDual_comp, hgV]

theorem norm_det_eq {O F A : Type} [CommRing O] [Field F] [NormedField A] (g : O →+* F) (j : F →+* A) {r : ℕ} (u : O)
    (hu : ‖j (g u)‖ = 1) (T : Matrix (Fin r) (Fin r) O) :
    ‖j (Matrix.det (Matrix.of fun i k => (g u)⁻¹ * g (T i k)))‖ = ‖j (g T.det)‖ := by
  have h : (Matrix.of fun i k => (g u)⁻¹ * g (T i k)) = (g u)⁻¹ • g.mapMatrix T := by
    ext i k
    rfl
  rw [h, Matrix.det_smul, ← RingHom.map_det, map_mul, norm_mul, map_pow, norm_pow, map_inv₀, norm_inv, hu, inv_one,
    one_pow, _root_.one_mul]

theorem fin_norm (hρ : MB.IsActOf t'.act.act ρM)
    (n : SABMap tK t' (spMap (e.comp (algebraMap (𝓞 L) L)))) (mf : SABMap tK Xo.univ.t (under y))
    (hy : y ≫ pullback.snd _ _ = spMap β) (hU : Set.range y ⊆ U) (hφ : IsLineFn U τ φ)
    (hs₁ : β.comp (tauIn c τ) = (e.comp (algebraMap (𝓞 L) L)).comp s₁)
    (hs₂ : β.comp (tauIn c (ComplexEmbedding.conjugate τ)) = (e.comp (algebraMap (𝓞 L) L)).comp s₂)
    {vK : B.carrier → (epsAt (𝟙 (Sp F)) ⟶ tK.G)} {vec : B.carrier → (epsAt (under y) ⟶ Xo.univ.t.G)}
    (h1 : ∀ z, (vK z).left ≫ n.φ = spMap (dualMap (e.comp (algebraMap (𝓞 L) L))) ≫ (MB.pt z).left)
    (h2 : ∀ z, (vK z).left ≫ mf.φ = (vec z).left)
    (h3 : ∀ (s : 𝓞 E →+* 𝓞 L) (r : ℕ) (x : Fin r → B.carrier), (∀ k, x k ∈ eigSp ρM s) → LinearIndependent (𝓞 L) x →
      (∀ z ∈ eigSp ρM s, ∃ u : 𝓞 L, u ≠ 0 ∧ u • z ∈ Submodule.span (𝓞 L) (Set.range x)) →
      IsEigFrame Xo.univ.t.act (under y) ((e.comp (algebraMap (𝓞 L) L)).comp s) fun k => vec (x k))
    (h4 : ∀ (r : ℕ) (x : Fin r → B.carrier) (z : B.carrier) (u : 𝓞 L) (T : Fin r → 𝓞 L), u ≠ 0 →
      u • z = ∑ k, T k • x k → IsComb (fun k => (e.comp (algebraMap (𝓞 L) L) u)⁻¹ * e.comp (algebraMap (𝓞 L) L) (T k))
        (fun k => vec (x k)) (vec z))
    {x₁ y₁ : Fin D.p → B.carrier} {x₂ y₂ : Fin D.q → B.carrier}
    (hfr : IsFramed U τ β y (fun k => vec (x₁ k)) fun k => vec (x₂ k)) (p : Nat.Primes) (j : F →+* ℂ_[p])
    {u₁ u₂ : 𝓞 L} {T₁ : Matrix (Fin D.p) (Fin D.p) (𝓞 L)} {T₂ : Matrix (Fin D.q) (Fin D.q) (𝓞 L)}
    (a1 : ∀ k, y₁ k ∈ eigSp ρM s₁) (a2 : LinearIndependent (𝓞 L) y₁)
    (a3 : ∀ z ∈ eigSp ρM s₁, ∃ u : 𝓞 L, ‖j.comp e (u : L)‖ = 1 ∧ u • z ∈ Submodule.span (𝓞 L) (Set.range y₁))
    (a4 : ‖j.comp e (u₁ : L)‖ = 1) (a5 : ∀ i, u₁ • x₁ i = ∑ k, T₁ i k • y₁ k) (a6 : T₁.det ≠ 0)
    (b1 : ∀ k, y₂ k ∈ eigSp ρM s₂) (b2 : LinearIndependent (𝓞 L) y₂)
    (b3 : ∀ z ∈ eigSp ρM s₂, ∃ u : 𝓞 L, ‖j.comp e (u : L)‖ = 1 ∧ u • z ∈ Submodule.span (𝓞 L) (Set.range y₂))
    (b4 : ‖j.comp e (u₂ : L)‖ = 1) (b5 : ∀ i, u₂ • x₂ i = ∑ k, T₂ i k • y₂ k) (b6 : T₂.det ≠ 0) {r : ℝ}
    (hN : HasFinNorm U τ φ p (j.comp β) r) :
    r = Real.log ‖j (φ F y (fun k => vec (x₁ k)) fun k => vec (x₂ k))‖ + Real.log ‖j.comp e ((T₁.det : 𝓞 L) : L)‖ -
      Real.log ‖j.comp e ((T₂.det : 𝓞 L) : L)‖ := by
  obtain ⟨V, hV, hV1, hV2, -⟩ := GlobalTheory.T.padic_embedding_discrete_valuation_ring F p j
  let gV : 𝓞 L →+* V := (e.comp (algebraMap (𝓞 L) L)).codRestrict V.toSubring fun a =>
    hV2 (RingOfIntegers.mapRingHom e a)
  have hgV : (algebraMap V F).comp gV = e.comp (algebraMap (𝓞 L) L) := rfl
  have hne : ∀ u : 𝓞 L, ‖j.comp e (u : L)‖ = 1 → u ≠ 0 := by
    rintro u hu rfl
    simp at hu
  have hunit : ∀ u : 𝓞 L, ‖j.comp e (u : L)‖ = 1 → IsUnit (gV u) := fun u hu => by
    have h0 : e (u : L) ≠ 0 := by
      intro h
      rw [RingHom.comp_apply, h] at hu
      simp at hu
    have h5 : (e (u : L))⁻¹ ∈ V := (hV1 _).1 (by
      rw [map_inv₀, norm_inv]
      exact (congrArg (·⁻¹) hu).trans_le inv_one.le)
    exact IsUnit.of_mul_eq_one ⟨_, h5⟩ (Subtype.ext (mul_inv_cancel₀ h0))
  obtain ⟨T, ⟨mT⟩⟩ : ∃ T : SAB H (Sp V), Nonempty (SABMap T t' (spMap gV)) := by
    obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull (spMap gV) t'
    exact ⟨_, ⟨m⟩⟩
  obtain ⟨m'', hm⟩ : ∃ m'' : SABMap tK _ (spMap (algebraMap V F)), n.φ = m''.φ ≫ mT.φ := by
    have key : ∀ (f : Sp F ⟶ Sp (𝓞 L)) (n : SABMap tK t' f), f = spMap (algebraMap V F) ≫ spMap gV →
        ∃ m'' : SABMap tK _ (spMap (algebraMap V F)), n.φ = m''.φ ≫ mT.φ := by
      rintro _ n rfl
      exact sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ mT n
    exact key _ n (spMap_comp gV (algebraMap V F))
  have hfr' : IsFramed U τ β y (fun k => vec (y₁ k)) fun k => vec (y₂ k) :=
    ⟨hy, hU, hs₁ ▸ h3 s₁ _ y₁ a1 a2 fun z hz => (a3 z hz).imp fun u hu => ⟨hne u hu.1, hu.2⟩,
      hs₂ ▸ h3 s₂ _ y₂ b1 b2 fun z hz => (b3 z hz).imp fun u hu => ⟨hne u hu.1, hu.2⟩⟩
  have h5 := hN V F j β y _ _ _ tK mf m'' (fun a => (hV1 a).trans ⟨fun h => ⟨⟨a, h⟩, rfl⟩, fun ⟨b, hb⟩ => hb ▸ b.2⟩) rfl
    hfr'
    (hs₁ ▸ int_frame MB hρ n mf gV hgV mT m'' hm h1 h2 s₁ y₁ a1 a2 fun z hz =>
      (a3 z hz).imp fun u hu => ⟨hunit u hu.1, hu.2⟩)
    (hs₂ ▸ int_frame MB hρ n mf gV hgV mT m'' hm h1 h2 s₂ y₂ b1 b2 fun z hz =>
      (b3 z hz).imp fun u hu => ⟨hunit u hu.1, hu.2⟩)
  have h6 := hφ.chg F β y _ _ _ _
    (Matrix.of fun i k => (e.comp (algebraMap (𝓞 L) L) u₁)⁻¹ * e.comp (algebraMap (𝓞 L) L) (T₁ i k))
    (Matrix.of fun i k => (e.comp (algebraMap (𝓞 L) L) u₂)⁻¹ * e.comp (algebraMap (𝓞 L) L) (T₂ i k)) hfr' hfr
    (fun i => h4 _ y₁ (x₁ i) u₁ (T₁ i) (hne _ a4) (a5 i)) fun i => h4 _ y₂ (x₂ i) u₂ (T₂ i) (hne _ b4) (b5 i)
  have h7 := congrArg (fun a => ‖j a‖) h6
  simp only [map_mul, norm_mul] at h7
  rw [norm_det_eq _ j u₁ a4, norm_det_eq _ j u₂ b4] at h7
  have hg : ∀ d : 𝓞 L, d ≠ 0 → ‖j (e.comp (algebraMap (𝓞 L) L) d)‖ ≠ 0 := fun d hd =>
    norm_ne_zero_iff.2 ((map_ne_zero j).2 ((map_ne_zero e).2
      ((map_ne_zero_iff _ (IsFractionRing.injective (𝓞 L) L)).2 hd)))
  have h8 := congrArg Real.log h7
  rw [Real.log_mul (norm_ne_zero_iff.2 ((map_ne_zero j).2 (hφ.ne F β y _ _ hfr))) (hg _ a6),
    Real.log_mul (norm_ne_zero_iff.2 ((map_ne_zero j).2 (hφ.ne F β y _ _ hfr'))) (hg _ b6), h5] at h8
  exact eq_sub_of_add_eq h8.symm

end LevelTowerAlt
