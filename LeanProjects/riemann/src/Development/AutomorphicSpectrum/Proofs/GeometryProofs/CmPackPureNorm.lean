import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCMFrame
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DifferentTwistedGeneratorExistsStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.EigenLocalBasisLogNormStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsLocalBasisCmOrderStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PureFamilyDecompositionStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelEigenvectorsActionStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmPackPureFrameStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmPackProductFrameStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelExtendsOverDvrStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmLieModelActionStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PeriodsSpanPureDecompositionStatement
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.PadicEmbeddingDiscreteValuationRingStatement
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Rt0ConjNegNeZero

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Fl.GFin

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem rt0_conj_neg_ne_zero (H : Host E) : starRingEnd ℂ H.rt0 = -H.rt0 :=
  _root_.UpperTheory.Reformulated.B.Ga10.rt0_conj_neg_ne_zero H

theorem card_emb {l : Level H} (c : Coeff l) (K : IntermediateField ℚ ℂ) (hc : c.F ≤ K) :
    Nat.card (E →+* K) = Module.finrank ℚ E := by
  have hm : ∀ (τ : E →+* ℂ) (a : E), τ a ∈ K := fun τ a => hc (c.conj τ a)
  have e : (E →+* K) ≃ (E →+* ℂ) :=
    { toFun := fun φ => (algebraMap K ℂ).comp φ
      invFun := fun τ => τ.codRestrict K.toSubfield (hm τ)
      left_inv := fun φ => by ext a; rfl
      right_inv := fun τ => by ext a; rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, NumberField.Embeddings.card]

theorem exists_frame {K : Type} [Field K] (V : Subring K) [IsDomain V] [IsPrincipalIdealRing V]
    [IsFractionRing V K] {U : Type} [AddCommGroup U] [Module K U] {I : Type} [Finite I] (u : I → U)
    (W : Submodule K U) : ∃ (r : ℕ) (v : Fin r → U), LinearIndependent K v ∧
      Submodule.span V (Set.range u) ⊓ W.restrictScalars V = Submodule.span V (Set.range v) := by
  set N : Submodule V U := Submodule.span V (Set.range u) ⊓ W.restrictScalars V with hN
  have hfg : (Submodule.span V (Set.range u)).FG := Submodule.fg_span (Set.finite_range u)
  haveI : Module.Finite V (Submodule.span V (Set.range u)) := Module.Finite.iff_fg.2 hfg
  haveI : IsNoetherian V (Submodule.span V (Set.range u)) := inferInstance
  have hNfg : N.FG := by
    have := IsNoetherian.noetherian (R := V) (M := Submodule.span V (Set.range u))
      (N.comap (Submodule.span V (Set.range u)).subtype)
    have h2 := this.map (Submodule.span V (Set.range u)).subtype
    rwa [Submodule.map_comap_subtype, inf_eq_right.2 (inf_le_left : N ≤ _)] at h2
  haveI : Module.Finite V N := Module.Finite.iff_fg.2 hNfg
  haveI : Module.IsTorsionFree V U := ⟨fun r hr a b h => by
    have hr0 : (r : K) ≠ 0 := fun e => hr.ne_zero (Subtype.ext e)
    exact smul_right_injective U hr0 h⟩
  haveI : Module.Free V N := Module.free_of_finite_type_torsion_free'
  let bs := Module.finBasis V N
  refine ⟨_, fun i => (bs i : U), ?_, ?_⟩
  · refine (LinearIndependent.iff_fractionRing V K).1 ?_
    exact bs.linearIndependent.map' N.subtype (Submodule.ker_subtype N)
  · have h2 : N = Submodule.span V (N.subtype '' Set.range bs) := by
      rw [← Submodule.map_span, bs.span_eq, Submodule.map_top, Submodule.range_subtype]
    refine h2.trans (congrArg _ ?_)
    rw [← Set.range_comp]
    rfl

theorem span_fam {La : Type} [AddCommGroup La] [Module (𝓞 E) La] {ℓ : ℕ} (hℓ : ℓ.Prime) {I J : Type} [Fintype I] [Fintype J]
    (x : I ⊕ J → La) {f : ℕ} (b : Fin f → 𝓞 E)
    (hx : IsLocBasis (𝓞 E) ℓ x) (hb : IsLocBasis (Algebra.adjoin ℤ {H.w0}) ℓ b) :
    ∃ N : ℕ, ¬ ℓ ∣ N ∧ ∀ y : La, N • y ∈ Submodule.span (OK H)
      (Set.range (Sum.elim (fun q : I × Fin f => b q.2 • x (.inl q.1)) (fun q : J × Fin f => b q.2 • x (.inr q.1)))) := by
  classical
  obtain ⟨-, n₁, h₁, hs₁⟩ := hx
  obtain ⟨-, n₂, h₂, hs₂⟩ := hb
  set S : Submodule (OK H) La := Submodule.span (OK H)
      (Set.range (Sum.elim (fun q : I × Fin f => b q.2 • x (.inl q.1)) (fun q : J × Fin f => b q.2 • x (.inr q.1)))) with hS
  have key : ∀ (m : I ⊕ J) (t : 𝓞 E), t ∈ Submodule.span (OK H) (Set.range b) → t • x m ∈ S := by
    intro m t ht
    induction ht using Submodule.span_induction with
    | mem t h =>
      obtain ⟨k, rfl⟩ := h
      refine Submodule.subset_span ?_
      rcases m with a | a
      · exact ⟨.inl (a, k), rfl⟩
      · exact ⟨.inr (a, k), rfl⟩
    | zero => simp
    | add s t _ _ hs ht => rw [add_smul]; exact S.add_mem hs ht
    | smul r t _ ht =>
      have : (r • t) • x m = r • (t • x m) := by
        change ((r : 𝓞 E) * t) • x m = (r : 𝓞 E) • (t • x m)
        rw [mul_smul]
      rw [this]
      exact S.smul_mem r ht
  refine ⟨n₁ * n₂, ?_, fun y => ?_⟩
  · exact fun h => (hℓ.dvd_mul.1 h).elim h₁ h₂
  · obtain ⟨s, hs⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 E)).1 (hs₁ y)
    have : (n₁ * n₂) • y = ∑ m, (n₂ • s m) • x m := by
      rw [mul_comm, mul_smul, ← hs, Finset.smul_sum]
      exact Finset.sum_congr rfl fun m _ => (smul_assoc _ _ _).symm
    rw [this]
    exact S.sum_mem fun m _ => key m _ (hs₂ _)

theorem scaled {S : Scheme.{0}} {K : Type} [Field K] {G : Over S} [GrpObj G] {x : Sp K ⟶ S} {U : Type}
    [AddCommGroup U] [Module K U] {O : Type} [CommRing O] (act : OAct O G) (M : LieModel G x U)
    (ρ : O →+* Module.End K U) (τ : O →+* K) (hact : M.IsActOf act.act ρ) {r : ℕ} (u : Fin r → U) {δ : K}
    (hδ : δ ≠ 0) (hE : IsEigFrame act x τ (fun k => M.pt (u k))) :
    IsEigFrame act x τ (fun k => M.pt (δ • u k)) ∧
      ∀ a, IsComb ((δ • (1 : Matrix (Fin r) (Fin r) K)) a) (fun k => M.pt (u k)) (M.pt (δ • u a)) := by
  obtain ⟨hc, hf⟩ := GlobalTheory.T.lie_model_eigenvectors_action S K G x U M
  have hf' := (hf O act ρ τ hact).2 r
  obtain ⟨hli, hsp⟩ := (hf' u).1 hE
  refine ⟨(hf' _).2 ⟨?_, ?_⟩, fun a => ?_⟩
  · exact hli.units_smul (fun _ => Units.mk0 δ hδ)
  · rw [← hsp]
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨a, rfl⟩
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨a, rfl⟩
      have h : u a = δ⁻¹ • (δ • u a) := by rw [smul_smul, inv_mul_cancel₀ hδ, one_smul]
      rw [SetLike.mem_coe, h]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  · rw [hc]
    congr 1
    simp [Matrix.smul_apply, Matrix.one_apply, ite_smul]

theorem half {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {K : Type} [Field K] [CharZero K]
    (V : Subring K) [IsDomain V] [IsDiscreteValuationRing V] [IsFractionRing V K]
    (ℓ : Nat.Primes) (j : K →+* ℂ_[ℓ]) (y : Sp K ⟶ Xo.XF c) (T : SAB H (Sp V)) (tK : SAB H (Sp K))
    (m : SABMap tK Xo.univ.t (under y)) (m' : SABMap tK T (spMap (algebraMap V K)))
    {U : Type} [AddCommGroup U] [Module K U] (M : LieModel Xo.univ.t.G (under y) U)
    (ρ : 𝓞 E →+* Module.End K U) (σ : E →+* K)
    (r r' f n : ℕ) (b : Fin f → 𝓞 E) (u : Fin r → U) (u' : Fin r' → U) (δ : K)
    (e : Fin n ≃ (Fin r × Fin f) ⊕ (Fin r' × Fin f))
    (uV : Fin n → (epsAt (𝟙 (Sp V)) ⟶ T.G))
    (hact : M.IsActOf Xo.univ.t.act.act ρ)
    (hj : ∀ a : K, ‖j a‖ ≤ 1 ↔ a ∈ V)
    (hcard : Nat.card (E →+* K) = Module.finrank ℚ E)
    (hb : IsLocBasis (Algebra.adjoin ℤ {H.w0}) ℓ b)
    (hu : ∀ a, ρ H.rt (u a) = σ (H.rt : E) • u a)
    (hu' : ∀ a, ρ H.rt (u' a) = -σ (H.rt : E) • u' a)
    (hind : LinearIndependent K (Sum.elim (fun q : Fin r × Fin f => ρ (b q.2) (u q.1))
      (fun q : Fin r' × Fin f => ρ (b q.2) (u' q.1))))
    (hδ : δ ≠ 0)
    (hlog : Real.log ‖j δ‖ = logIdeal ((j.comp σ).comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) -
      Real.log ‖j (σ (H.rt : E))‖)
    (hσ : ∀ a : 𝓞 E, σ (a : E) ∈ V)
    (htan : ∀ k, IsTanAt T.G _ (uV k))
    (hbas : ∀ w, IsTanAt T.G _ w → ∃! cc : Fin n → V, IsComb cc uV w)
    (hlink : ∀ k, ∃ s : Sp (DualNumber K) ⟶ tK.G.left,
      s ≫ m.φ = (M.pt (Sum.elim (fun q : Fin r × Fin f => ρ (b q.2) (u q.1))
        (fun q : Fin r' × Fin f => ρ (b q.2) (u' q.1)) (e k))).left ∧
      s ≫ m'.φ = spMap (dualMap (algebraMap V K)) ≫ (uV k).left) :
    IsIntFrame m m' (σ.comp (algebraMap (𝓞 E) E)) (fun a => M.pt (δ • HT.eigProj ρ σ (u a))) := by
  obtain ⟨h1, h2⟩ := GlobalTheory.T.eigen_local_basis_log_norm E H ℓ K j V U ρ σ (Fin r) (Fin r') u u' f b δ hj hcard hb hu hu' hind hδ hlog
  exact (GlobalTheory.T.lie_model_extends_over_dvr E H D l Xo c K V y T tK m m' U M ρ σ _ n r e uV _ _ hact hσ htan hbas hlink h1 h2).2

theorem intFrames_fin : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (Z : ∀ b : Bool, Curve0 H (sgnRt H b)) (P : (FU.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (FU.Di i) ty P) (X : CMPack Z c FU i hP) (x : Fin D.p ⊕ Fin D.q → (FU.Di i).La) (hx : IsPure hP x) (τ : E →+* ℂ) (ℓ : Nat.Primes) (j : X.K →+* ℂ_[ℓ]) (v : Vecs X.y D.p) (w : Vecs X.y D.q), IsTypeFn H D.p D.q ty → τ (H.rt : E) = H.rt0 → IsLocBasis (𝓞 E) ℓ x → X.IsCMFrame τ hx v w → ∃ (V : Subring X.K) (_ : IsDiscreteValuationRing V) (_ : IsFractionRing V X.K) (T : SAB H (Sp V)) (m'' : SABMap X.t T (spMap (algebraMap V X.K))) (δ δ' : X.K) (v' : Vecs X.y D.p) (w' : Vecs X.y D.q), (∀ a : X.K, ‖j a‖ ≤ 1 ↔ a ∈ (algebraMap V X.K).range) ∧ δ ≠ 0 ∧ δ' ≠ 0 ∧ Real.log ‖j δ‖ = logIdeal ((j.comp (X.β.comp (tauE c τ))).comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) - Real.log ‖j (X.β (tauE c τ (H.rt : E)))‖ ∧ Real.log ‖j δ'‖ = Real.log ‖j δ‖ ∧ (∀ a, IsComb ((δ • (1 : Matrix (Fin D.p) (Fin D.p) X.K)) a) v (v' a)) ∧ (∀ a, IsComb ((δ' • (1 : Matrix (Fin D.q) (Fin D.q) X.K)) a) w (w' a)) ∧ IsFramed (Set.range X.y) τ X.β X.y v' w' ∧ IsIntFrame X.m m'' (X.β.comp (tauIn c τ)) v' ∧ IsIntFrame X.m m'' (X.β.comp (tauIn c (ComplexEmbedding.conjugate τ))) w' := by
  intro E _ _ _ H D l Xo c g ty FU i Z P hP X x hx τ ℓ j v w hty hτ hloc hfr
  obtain ⟨Vs, hdvr, hVj, hOK, hunit⟩ := GlobalTheory.T.padic_embedding_discrete_valuation_ring X.K ℓ j
  let V : Subring X.K := Vs.toSubring
  haveI : IsDiscreteValuationRing V := hdvr
  haveI : IsFractionRing V X.K := (inferInstance : IsFractionRing Vs X.K)
  have hj : ∀ a : X.K, ‖j a‖ ≤ 1 ↔ a ∈ V := hVj
  have hOK' : ∀ s : 𝓞 X.K, (s : X.K) ∈ V := hOK
  obtain ⟨f, b, hf, hb⟩ := GlobalTheory.T.exists_local_basis_cm_order E H ℓ ℓ.prop
  obtain ⟨M, ρ, lam, hact, hIm, hsm, hadd, hrt, hCM⟩ := GlobalTheory.T.cm_lie_model_action E H D l Xo c g ty FU i Z P hP X
  obtain ⟨δ₀, hδ₀, hδ₀'⟩ := GlobalTheory.T.different_twisted_generator_exists E H ℓ
  let σ : E →+* X.K := X.β.comp (tauE c τ)
  let σ' : E →+* X.K := X.β.comp (tauE c (ComplexEmbedding.conjugate τ))
  have hσc : ∀ a, ((σ a : X.K) : ℂ) = τ a := fun _ => rfl
  have hσc' : ∀ a, ((σ' a : X.K) : ℂ) = starRingEnd ℂ (τ a) := fun a =>
    ComplexEmbedding.conjugate_coe_eq τ a
  have hrt1 : ((σ (H.rt : E) : X.K) : ℂ) = H.rt0 := (hσc _).trans hτ
  have hrt2 : ((σ' (H.rt : E) : X.K) : ℂ) = -H.rt0 := by
    rw [hσc', hτ, rt0_conj_neg_ne_zero]
  let u : Fin D.p → Fin g → X.K := fun a => lam true ⟨x (.inl a), hx.1 a⟩
  let u' : Fin D.q → Fin g → X.K := fun a => lam false ⟨x (.inr a), hx.2 a⟩
  have hu1 : ∀ a, ρ H.rt (u a) = σ (H.rt : E) • u a := fun a =>
    hrt true _ _ (by simpa [sgnRt] using hrt1)
  have hu1' : ∀ a, ρ H.rt (u' a) = -σ (H.rt : E) • u' a := fun a =>
    hrt false _ _ (by simpa [sgnRt] using hrt1)
  have hu2 : ∀ a, ρ H.rt (u' a) = σ' (H.rt : E) • u' a := fun a =>
    hrt false _ _ (by simpa [sgnRt] using hrt2)
  have hu2' : ∀ a, ρ H.rt (u a) = -σ' (H.rt : E) • u a := fun a =>
    hrt true _ _ (by simp [sgnRt, hrt2])
  obtain ⟨N, hN, hspan⟩ := span_fam (H := H) ℓ.prop x b hloc hb
  have hN0 : 0 < N := Nat.pos_of_ne_zero fun h => hN (h ▸ dvd_zero _)
  obtain ⟨n, hn, hnspan⟩ := hloc.2
  have hn0 : 0 < n := Nat.pos_of_ne_zero fun h => hn (h ▸ dvd_zero _)
  have hdec := (GlobalTheory.T.pure_family_decomposition E H (FU.Di i) g ty P hP D.p D.q x n hx hnspan).1
  have hg := (GlobalTheory.T.periods_span_pure_decomposition E H (FU.Di i) g ty P hP n hn0 hdec).1
  have hcardI : Fintype.card ((Fin D.p × Fin f) ⊕ (Fin D.q × Fin f)) = g := by
    rw [hg, (FU.sig i).1, (FU.sig i).2, ← hf, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
    ring
  let e : Fin g ≃ (Fin D.p × Fin f) ⊕ (Fin D.q × Fin f) := (Fintype.equivFinOfCardEq hcardI).symm
  let bI : (Fin D.p × Fin f) ⊕ (Fin D.q × Fin f) → Bool := Sum.elim (fun _ => true) (fun _ => false)
  let aI : ∀ q, PureType.lat hP (sgnRt H (bI q)) := fun q => match q with
    | .inl q => b q.2 • (⟨x (.inl q.1), hx.1 q.1⟩ : PureType.lat hP (sgnRt H true))
    | .inr q => b q.2 • (⟨x (.inr q.1), hx.2 q.1⟩ : PureType.lat hP (sgnRt H false))
  let fam : (Fin D.p × Fin f) ⊕ (Fin D.q × Fin f) → Fin g → X.K :=
    Sum.elim (fun q => ρ (b q.2) (u q.1)) (fun q => ρ (b q.2) (u' q.1))
  let fam' : (Fin D.q × Fin f) ⊕ (Fin D.p × Fin f) → Fin g → X.K :=
    Sum.elim (fun q => ρ (b q.2) (u' q.1)) (fun q => ρ (b q.2) (u q.1))
  have hfam : ∀ q, lam (bI q) (aI q) = fam q := by
    rintro (q | q)
    · exact hsm true (b q.2) _
    · exact hsm false (b q.2) _
  have hswap : ∀ z, fam' (Equiv.sumComm _ _ z) = fam z := by rintro (q | q) <;> rfl
  have hval : (fun k => ((aI (e k) : PureType.lat hP (sgnRt H (bI (e k)))) : (FU.Di i).La)) =
      (Sum.elim (fun q : Fin D.p × Fin f => b q.2 • x (.inl q.1))
        (fun q : Fin D.q × Fin f => b q.2 • x (.inr q.1))) ∘ e := by
    have h0 : ∀ q, ((aI q : PureType.lat hP (sgnRt H (bI q))) : (FU.Di i).La) =
        Sum.elim (fun q : Fin D.p × Fin f => b q.2 • x (.inl q.1))
          (fun q : Fin D.q × Fin f => b q.2 • x (.inr q.1)) q := by
      rintro (q | q) <;> rfl
    funext k
    exact h0 (e k)
  have hspan' : ∀ y : (FU.Di i).La, N • y ∈ Submodule.span (OK H)
      (Set.range fun k => ((aI (e k) : PureType.lat hP (sgnRt H (bI (e k)))) : (FU.Di i).La)) := by
    intro y
    rw [hval, e.surjective.range_comp]
    exact hspan y
  have hNu : IsUnit (N : V) := by
    have hNK : (N : X.K) ≠ 0 := Nat.cast_ne_zero.2 hN0.ne'
    have hinv : (N : X.K)⁻¹ ∈ V := by
      refine (hj _).1 ?_
      rw [map_inv₀, norm_inv, hunit N hN, inv_one]
    refine IsUnit.of_mul_eq_one (⟨_, hinv⟩ : V) (Subtype.ext ?_)
    simpa using mul_inv_cancel₀ hNK
  obtain ⟨T, m'', uV, htan, hbas, hlink⟩ := GlobalTheory.T.cm_pack_product_frame E H D l Xo c g ty FU i Z P hP X N
    (fun k => bI (e k)) (fun k => aI (e k)) V hN0 hspan' hOK' hNu
  have hlink1 : ∀ k, ∃ s : Sp (DualNumber X.K) ⟶ X.t.G.left, s ≫ X.m.φ = (M.pt (fam (e k))).left ∧
      s ≫ m''.φ = spMap (dualMap (algebraMap V X.K)) ≫ (uV k).left := fun k => by
    rw [← hfam]
    exact hlink k _ ((hIm _ _ _).2 rfl)
  have hlink2 : ∀ k, ∃ s : Sp (DualNumber X.K) ⟶ X.t.G.left,
      s ≫ X.m.φ = (M.pt (fam' ((e.trans (Equiv.sumComm _ _)) k))).left ∧
      s ≫ m''.φ = spMap (dualMap (algebraMap V X.K)) ≫ (uV k).left := fun k => by
    rw [Equiv.trans_apply, hswap]
    exact hlink1 k
  have hint : ∀ (φ : E →+* X.K) (a : 𝓞 E), φ (a : E) ∈ V := fun φ a =>
    hOK' ⟨φ a, map_isIntegral_int φ (RingOfIntegers.isIntegral_coe a)⟩
  obtain ⟨r0, v0, hv0, hv0s⟩ := exists_frame V fam (HT.eigSp ρ σ)
  have hind : LinearIndependent X.K fam :=
    (GlobalTheory.T.lie_model_extends_over_dvr E H D l Xo c X.K V X.y T X.t X.m m'' (Fin g → X.K) M ρ σ _ g r0 e uV fam v0 hact
      (hint σ) htan hbas hlink1 hv0 hv0s).1
  have hind' : LinearIndependent X.K fam' := by
    have h := hind.comp _ (Equiv.sumComm (Fin D.q × Fin f) (Fin D.p × Fin f)).injective
    have e2 : fam ∘ (Equiv.sumComm (Fin D.q × Fin f) (Fin D.p × Fin f)) = fam' := by
      funext z
      rcases z with q | q <;> rfl
    rwa [e2] at h
  have hcard := card_emb (E := E) c X.K X.hc
  have hconj : σ (IsCMField.complexConj E δ₀) = σ' δ₀ := Subtype.ext
    ((IsCMField.complexEmbedding_complexConj E τ δ₀).trans (hσc' δ₀).symm)
  have hl1 := (hδ₀' (j.comp σ)).1
  have hl2 := (hδ₀' (j.comp σ')).1
  have hl3 := (hδ₀' (j.comp σ)).2
  have hne : σ δ₀ ≠ 0 := (map_ne_zero σ).2 hδ₀
  have hne' : σ' δ₀ ≠ 0 := (map_ne_zero σ').2 hδ₀
  have I1 := half V ℓ j X.y T X.t X.m m'' M ρ σ D.p D.q f g b u u' (σ δ₀) e uV hact hj hcard hb hu1 hu1' hind
    hne hl1 (hint σ) htan hbas hlink1
  have I2 := half V ℓ j X.y T X.t X.m m'' M ρ σ' D.q D.p f g b u' u (σ' δ₀) (e.trans (Equiv.sumComm _ _)) uV
    hact hj hcard hb hu2 hu2' hind' hne' hl2 (hint σ') htan hbas hlink2
  have hFr := (GlobalTheory.T.cm_pack_pure_frame E H D l Xo c g ty FU i Z P hP X x hx τ hty hτ hloc.1).2 v w hfr
  have hv : v = fun a => M.pt (HT.eigProj ρ σ (u a)) := funext fun a => (hCM true τ _ _).1 (hfr.1 a)
  have hw : w = fun a => M.pt (HT.eigProj ρ σ' (u' a)) := funext fun a =>
    (hCM false (ComplexEmbedding.conjugate τ) _ _).1 (hfr.2 a)
  obtain ⟨hy, -, hE1, hE2⟩ := hFr
  rw [hv] at hE1
  rw [hw] at hE2
  obtain ⟨s1, s2⟩ := scaled Xo.univ.t.act M ρ _ hact _ hne hE1
  obtain ⟨s3, s4⟩ := scaled Xo.univ.t.act M ρ _ hact _ hne' hE2
  refine ⟨V, inferInstance, inferInstance, T, m'', σ δ₀, σ' δ₀, _, _, fun a => ?_, hne, hne', hl1, ?_, ?_, ?_,
    ⟨hy, subset_rfl, s1, s3⟩, I1, I2⟩
  · rw [hj]
    exact ⟨fun h => ⟨⟨a, h⟩, rfl⟩, by rintro ⟨t, rfl⟩; exact t.2⟩
  · have := hl3
    simp only [RingHom.comp_apply] at this
    rw [hconj] at this
    exact this
  · intro a
    rw [hv]
    exact s2 a
  · intro a
    rw [hw]
    exact s4 a

end GlobalTheory.CompanionTheory.Ar.Fl.GFin
