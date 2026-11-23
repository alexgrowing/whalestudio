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
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicCompletionRationalPointsAndApproximation
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ZeroMemLatOf
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsPeriodCompIsometry
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct Topology
open GlobalTheory.RecDict

namespace GlobalTheory.MarkCoset

open scoped Matrix nonZeroDivisors

theorem AA_ne_zero (D : D7) : D.host.AA ≠ 0 := by
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

theorem latG_spec (D : D7) (V : HSp D) (g : GA D V) :
    (∀ v, v ∈ latG V g ↔ finVec V v ∈ latGHat V g) ∧
      ∀ z, z ∈ latGHat V g ↔ ∃ y ∈ latGHat V 1, (finHom V g).1 *ᵥ y = z := by
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
  have hs := fun g : GA D V => AdLat.scale_latOf D.host.F D.host.E V.rank L (finHom V g) D.host.AA _
    hfg hsp (AA_ne_zero D) rfl
  set L' := Submodule.span (𝓞 D.host.E) {w | ∃ a ∈ D.host.AA, ∃ x ∈ L, w = a • x} with hL'
  have h1 : (latG V g : Set (Fin V.rank → D.host.E)) = AdLat.latOf D.host.F (finHom V g).1 L' := by
    rw [← (hs g).1]
    unfold latG gLat
    rw [hhat]
    rfl
  have h2 : ∀ g : GA D V, (latGHat V g : Set (Fin V.rank → AdLat.RA D.host.F D.host.E)) =
      (finHom V g).1.mulVec '' (AdLat.hat D.host.F (L' : Set (Fin V.rank → D.host.E))) := by
    intro g
    rw [← (hs g).2.1]
    unfold latGHat gLat
    rw [hhat]
  have h3 : ∀ y, y ∈ latGHat V 1 ↔ y ∈ AdLat.hat D.host.F (L' : Set (Fin V.rank → D.host.E)) := by
    intro y
    rw [← SetLike.mem_coe, h2 1]
    simp only [map_one, Units.val_one, Set.mem_image, Matrix.one_mulVec, exists_eq_right, SetLike.mem_coe]
  refine ⟨fun v => ?_, fun z => ?_⟩
  · rw [← SetLike.mem_coe, h1, ← SetLike.mem_coe, h2 g]
    rfl
  · rw [← SetLike.mem_coe, h2 g]
    simp only [h3]
    rfl

theorem closure_congr {A : Type} [CommRing A] {n : ℕ} (k : Matrix (Fin n) (Fin n) A) (N : ℕ) (S : Set (Fin n → A))
    (h : ∀ z ∈ S, ∃ y ∈ AddSubgroup.closure S, k *ᵥ z = z + N • y) :
    ∀ z ∈ AddSubgroup.closure S, ∃ y ∈ AddSubgroup.closure S, k *ᵥ z = z + N • y := by
  intro z hz
  induction hz using AddSubgroup.closure_induction with
  | mem w hw => exact h w hw
  | zero => exact ⟨0, zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨x', hx', ex⟩ := hx
    obtain ⟨y', hy', ey⟩ := hy
    exact ⟨x' + y', add_mem hx' hy', by rw [Matrix.mulVec_add, ex, ey, smul_add]; abel⟩
  | neg x _ hx =>
    obtain ⟨x', hx', ex⟩ := hx
    exact ⟨-x', neg_mem hx', by rw [Matrix.mulVec_neg, ex, smul_neg]; abel⟩

theorem smul_congr {A : Type} [CommRing A] {n : ℕ} (k : Matrix (Fin n) (Fin n) A) (N : ℕ) (a : A) (z y : Fin n → A)
    (e : k *ᵥ z - z = N • y) : k *ᵥ (fun i => a * z i) = (fun i => a * z i) + N • fun i => a * y i := by
  change k *ᵥ (a • z) = a • z + N • (a • y)
  rw [Matrix.mulVec_smul, smul_comm N, ← smul_add, ← e, add_sub_cancel]

theorem level_latGHat {D : D7} (V : HSp D) (N : ℕ) (k : GA D V)
    (hk : ∀ z ∈ latHat V, ∃ y ∈ latHat V, (finHom V k).1.mulVec z - z = N • y) :
    ∀ z ∈ latGHat V 1, ∃ y ∈ latGHat V 1, (finHom V k).1 *ᵥ z = z + N • y := by
  have h1 : ∀ z, z ∈ gLat V 1 ↔ z ∈ latHat V := by
    intro z
    simp only [gLat, map_one, Units.val_one, Set.mem_image, Matrix.one_mulVec, exists_eq_right, SetLike.mem_coe]
  refine closure_congr _ N _ ?_
  rintro _ ⟨a, ha, z, hz, rfl⟩
  obtain ⟨y, hy, e⟩ := hk z ((h1 z).1 hz)
  exact ⟨_, AddSubgroup.subset_closure ⟨a, ha, y, (h1 y).2 hy, rfl⟩, smul_congr _ N _ z y e⟩

theorem rational_matrix {D : D7} (V : HSp D) (δ : GA D V) (hδ : δ ∈ GQ V) :
    ∃ δ₀ : GL (Fin V.rank) D.host.E,
      (∀ u v, herm (-V.gram.transpose) (δ₀.1 *ᵥ u) (δ₀.1 *ᵥ v) = herm (-V.gram.transpose) u v) ∧
      (∀ v, (finHom V δ).1 *ᵥ finVec V v = finVec V (δ₀.1 *ᵥ v)) ∧
      ∀ (τ : D.host.E →+* ℂ) (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ), Formalism.MainNotions.StandardLattice.IsInfEmb τ θ →
        archM V θ δ = δ₀.1.map τ := by
  obtain ⟨δ₀, hu, he⟩ := hδ
  have he' : ∀ i j, (matHom V δ).1 i j = (1 : AF D.host.F) ⊗ₜ δ₀.1 i j := fun i j =>
    (congrArg (fun x : GL (Fin V.rank) (AF D.host.F ⊗[D.host.F] D.host.E) => x.1 i j) he).symm
  refine ⟨δ₀, fun u v => ?_, fun v => ?_, fun τ θ hθ => ?_⟩
  · have hu' : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) δ₀.1 * V.gram * δ₀.1 = V.gram := hu
    have key : ∀ x y, herm (-V.gram.transpose) x y =
        -(((D.sp.cm.sig : D.host.E →+* D.host.E) ∘ y) ⬝ᵥ (V.gram *ᵥ x)) := by
      intro x y
      simp only [herm, dotProduct, Matrix.mulVec, Finset.mul_sum, Matrix.neg_apply, Matrix.transpose_apply,
        mul_neg, neg_mul, Finset.sum_neg_distrib, neg_inj]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      change _ * _ * cc (y a) = cc (y a) * _
      ring
    have hm : (D.sp.cm.sig : D.host.E →+* D.host.E) ∘ (δ₀.1 *ᵥ v) =
        ((D.sp.cm.sig : D.host.E →+* D.host.E) ∘ v) ᵥ* Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) δ₀.1 := by
      rw [Formalism.UG.cT, Matrix.vecMul_transpose]
      funext i
      exact RingHom.map_mulVec _ _ _ i
    rw [key, key, hm, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hu']
  · funext i
    have hf : ∀ i j, (finHom V δ).1 i j = (1 : Af D.host.F) ⊗ₜ δ₀.1 i j := fun i j => by
      change Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E) ((matHom V δ).1 i j) = _
      rw [he', Algebra.TensorProduct.map_tmul, map_one]
      rfl
    simp only [Matrix.mulVec, dotProduct, hf, finVec, Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one,
      TensorProduct.tmul_sum]
  · ext i j
    change θ (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) ((matHom V δ).1 i j)) = _
    rw [he', Algebra.TensorProduct.map_tmul, map_one]
    exact hθ.1 _

theorem nsmul_cancel (F : Type) [Field F] {A : Type} [AddCommGroup A] [Module F A] (N : ℕ) (hN : (N : F) ≠ 0)
    {x y : A} (h : N • x = N • y) : x = y := by
  rw [← Nat.cast_smul_eq_nsmul F, ← Nat.cast_smul_eq_nsmul F] at h
  exact smul_right_injective _ hN h

theorem finVec_div {D : D7} (V : HSp D) (N : ℕ) (hN : N ≠ 0) (x : Fin V.rank → D.host.E)
    (z : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) (h : finVec V x = N • z) :
    ∃ w, finVec V w = z ∧ x = N • w := by
  have hE : (N : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hN
  have hF : (N : D.host.F) ≠ 0 := Nat.cast_ne_zero.2 hN
  have hx : x = N • ((N : D.host.E)⁻¹ • x) := by
    rw [← Nat.cast_smul_eq_nsmul D.host.E, smul_inv_smul₀ hE]
  refine ⟨_, ?_, hx⟩
  have h2 : N • finVec V ((N : D.host.E)⁻¹ • x) = N • z := by
    rw [← h]
    conv_rhs => rw [hx]
    exact (AdLat.cap_fv_nsmul D.host.F N _).symm
  funext i
  exact nsmul_cancel D.host.F N hF (congrFun h2 i)

theorem transport {G A : Type} [Group G] [CommRing A] {n : ℕ} (f : G →* GL (Fin n) A)
    (Lh : G → AddSubgroup (Fin n → A)) (hL : ∀ g z, z ∈ Lh g ↔ ∃ y ∈ Lh 1, (f g).1 *ᵥ y = z) (N : ℕ) (δ u k : G)
    (hk : ∀ z ∈ Lh 1, ∃ y ∈ Lh 1, (f k).1 *ᵥ z = z + N • y)
    (hk' : ∀ z ∈ Lh 1, ∃ y ∈ Lh 1, (f k⁻¹).1 *ᵥ z = z + N • y) :
    (∀ z, z ∈ Lh u ↔ (f δ).1 *ᵥ z ∈ Lh (δ * u * k)) ∧
      ∀ x x' a, a ∈ Lh 1 → (∃ w ∈ Lh u, x - (f u).1 *ᵥ a = N • w) →
        (∃ w ∈ Lh (δ * u * k), x' - (f (δ * u * k)).1 *ᵥ a = N • w) →
        ∃ w ∈ Lh (δ * u * k), (f δ).1 *ᵥ x - x' = N • w := by
  have hmul : ∀ (a b : G) z, (f (a * b)).1 *ᵥ z = (f a).1 *ᵥ ((f b).1 *ᵥ z) := by
    intro a b z
    rw [map_mul, Units.val_mul, Matrix.mulVec_mulVec]
  have hone : ∀ z, (f 1).1 *ᵥ z = z := by
    intro z
    rw [map_one, Units.val_one, Matrix.one_mulVec]
  have h1 : ∀ z, z ∈ Lh u ↔ (f δ).1 *ᵥ z ∈ Lh (δ * u * k) := by
    intro z
    rw [hL u, hL (δ * u * k)]
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨w, hw, e⟩ := hk' y hy
      refine ⟨(f k⁻¹).1 *ᵥ y, e ▸ add_mem hy (nsmul_mem hw N), ?_⟩
      rw [← hmul, ← hmul, mul_inv_cancel_right]
    · rintro ⟨y, hy, h⟩
      obtain ⟨w, hw, e⟩ := hk y hy
      refine ⟨(f k).1 *ᵥ y, e ▸ add_mem hy (nsmul_mem hw N), ?_⟩
      have := congrArg (fun v => (f δ⁻¹).1 *ᵥ v) h
      simp only [← hmul, inv_mul_cancel, hone] at this
      rw [← this, ← hmul, mul_assoc, inv_mul_cancel_left]
  refine ⟨h1, ?_⟩
  rintro x x' a ha ⟨w, hw, e⟩ ⟨w', hw', e'⟩
  obtain ⟨y, hy, ey⟩ := hk a ha
  refine ⟨(f δ).1 *ᵥ w - (f δ).1 *ᵥ ((f u).1 *ᵥ y) - w',
    sub_mem (sub_mem ((h1 w).1 hw) ((h1 _).1 ((hL u _).2 ⟨y, hy, rfl⟩))) hw', ?_⟩
  rw [sub_eq_iff_eq_add.1 e, sub_eq_iff_eq_add.1 e', hmul, hmul, ey]
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, smul_sub]
  abel

theorem half_marked {R A B : Type} [CommRing R] [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    (I : Ideal R) (t : A →ₗ[R] B) (N N' : ℕ) (hN : N ∣ N') (ht : ∀ b, ∃ a e, b = t a + N' • e) :
    ∀ b ∈ I • (⊤ : Submodule R B), ∃ a ∈ I • (⊤ : Submodule R A), ∃ e, b = t a + N • e := by
  intro b hb
  obtain ⟨c, rfl⟩ := hN
  refine Submodule.smul_induction_on hb (fun m hm b _ => ?_) (fun x y hx hy => ?_)
  · obtain ⟨a, e, rfl⟩ := ht b
    refine ⟨m • a, Submodule.smul_mem_smul hm trivial, m • c • e, ?_⟩
    rw [smul_add, map_smul, mul_smul, smul_comm m N]
  · obtain ⟨a, ha, e, rfl⟩ := hx
    obtain ⟨a', ha', e', rfl⟩ := hy
    exact ⟨a + a', add_mem ha ha', e + e', by rw [map_add, smul_add]; abel⟩

theorem archM_mul {D : D7} (V : HSp D) (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (δ u k : GA D V)
    (hk : k ∈ GfC V) : archM V θ (δ * u * k) = archM V θ δ * archM V θ u := by
  have hk' : infHom V k = 1 := hk
  unfold archM
  rw [map_mul, hk', _root_.mul_one, map_mul, Units.val_mul, Matrix.map_mul]

set_option maxHeartbeats 1000000 in

theorem marked_differ (hT : ThetaUnifAV) (hL : Out.Laws) (D : D7) (V : HSp D)
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {σ' : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (D.host.E →+* ℂ)} (F : FamilyUnif Xo σ' ty)
    (hpq : 1 ≤ Dw.p + Dw.q) (hσ : σ' (baseKA l).ρ = H.rt0) (hty : IsTypeFn H Dw.p Dw.q ty) (hA : l.A = 1)
    {r : ℕ} (hr : V.rank = r) (M : GlobalTheory.FrameUnif.ModelsOf F r)
    (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E))
    (th : ∀ k, (M.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (hrec : RecOK M V hr io th x₀)
    (Kf : Subgroup (GA D V)) (hK : IsLevelK V l.M Kf) (h γ₀ k₀ : GA D V) (p p' : Σ k, Frame (M.X k).Ψ r)
    (hγ₀ : γ₀ ∈ GQ V) (hk₀ : k₀ ∈ Kf) (hp : MarkSpec M V hr io th x₀ h p)
    (hp' : MarkSpec M V hr io th x₀ (γ₀ * h * k₀) p') :
    ∃ γ' ∈ (M.X p.1).Γ, p' = ⟨p.1, lact γ' p.2⟩ := by
  subst hr
  obtain ⟨hbase, hW, ⟨-, hrange⟩, -, hth, -⟩ := hrec
  obtain ⟨k, x⟩ := p
  obtain ⟨k', x'⟩ := p'
  obtain ⟨γ, hγ, hΛ, hm, hf⟩ := hp
  obtain ⟨γ', hγ', hΛ', hm', hf'⟩ := hp'
  have hδ : γ' * γ₀ * γ⁻¹ ∈ GQ V := mul_mem (mul_mem hγ' hγ₀) (inv_mem hγ)
  have hu : γ' * (γ₀ * h * k₀) = γ' * γ₀ * γ⁻¹ * (γ * h) * k₀ := by group
  rw [hu] at hΛ' hm' hf'
  generalize γ' * γ₀ * γ⁻¹ = δ at hδ hΛ' hm' hf'
  generalize γ * h = u at hΛ hm hf hΛ' hm' hf'
  dsimp only at hΛ hm hf hΛ' hm' hf' ⊢
  obtain ⟨δ₀, hδu, hδf, hδa⟩ := rational_matrix V δ hδ
  obtain ⟨ht1, ht2⟩ := transport (finHom V) (latGHat V) (fun g => (latG_spec D V g).2) l.M δ u k₀
    (level_latGHat V l.M k₀ ((hK k₀).1 hk₀).2) (level_latGHat V l.M k₀⁻¹ ((hK k₀⁻¹).1 (inv_mem hk₀)).2)
  have hmem : ∀ v, v ∈ (M.X k).Λ ↔ finVec V v ∈ latGHat V u := fun v => by
    rw [← (latG_spec D V u).1, ← SetLike.mem_coe, hΛ]
    exact Set.ext_iff.1 (Set.image_id _) v
  have hmem' : ∀ v, v ∈ (M.X k').Λ ↔ finVec V v ∈ latGHat V (δ * u * k₀) := fun v => by
    rw [← (latG_spec D V _).1, ← SetLike.mem_coe, hΛ']
    exact Set.ext_iff.1 (Set.image_id _) v
  have hlat : ∀ v, v ∈ (M.X k).Λ ↔ δ₀.1 *ᵥ v ∈ (M.X k').Λ := fun v => by
    rw [hmem, hmem', ht1, hδf]
  have hM0 : l.M ≠ 0 := by have := l.three_le; omega
  have hmark : ∀ a ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) Dw.La),
      ∃ w ∈ (M.X k').Λ, δ₀.1 *ᵥ (M.φ k (F.t k a) : Fin V.rank → D.host.E) =
        (M.φ k' (F.t k' a) : Fin V.rank → D.host.E) + l.M • w := by
    intro a ha
    have hio : finVec V (io a) ∈ latGHat V 1 :=
      ((latG_spec D V 1).1 _).1 (hrange ▸ LinearMap.mem_range_self io a)
    obtain ⟨z, hz, e⟩ := ht2 (finVec V (M.φ k (F.t k a) : Fin V.rank → D.host.E))
      (finVec V (M.φ k' (F.t k' a) : Fin V.rank → D.host.E)) _ hio (hm a ha) (hm' a ha)
    obtain ⟨w, hw, e'⟩ := finVec_div V l.M hM0 (δ₀.1 *ᵥ (M.φ k (F.t k a) : Fin V.rank → D.host.E) -
      (M.φ k' (F.t k' a) : Fin V.rank → D.host.E)) z (by
        rw [← e, hδf]
        funext i
        exact TensorProduct.tmul_sub _ _ _)
    exact ⟨w, (hmem' w).2 (hw ▸ hz), sub_eq_iff_eq_add'.1 e'⟩
  have hG : ∀ k, (M.X k).Gm = -V.gram.transpose := fun k => (hW k).1
  have hkk : k = k' := by
    refine GlobalTheory.ClassUniq.eq_of_matched hT hL _ H Dw l Xo σ' g ty F _ M k k' δ₀ hpq hσ hty hbase
      ((hG k').trans (hG k).symm) ((hW k').2.trans (hW k).2.symm) (fun u v => by rw [hG]; exact hδu u v)
      hlat hmark fun a => ?_
    refine ⟨_, sub_mem ((hlat _).1 (M.φ k (F.t k a)).2) (M.φ k' (F.t k' a)).2, ?_⟩
    rw [hA, one_smul, add_sub_cancel]
  subst hkk
  have hsur : ∀ w ∈ (M.X k).Λ, ∃ b, (M.φ k b : Fin V.rank → D.host.E) = w := fun w hw =>
    ⟨(M.φ k).symm ⟨w, hw⟩, by rw [LinearEquiv.apply_symm_apply]⟩
  refine ⟨δ₀, (hbase.gam k δ₀).2 ⟨⟨fun u v => by rw [hG]; exact hδu u v, hlat⟩, fun b hb => ?_, fun a => ?_⟩, ?_⟩
  · obtain ⟨a, ha, e, rfl⟩ := half_marked _ (F.t k) l.M l.M' (Nat.dvd_lcm_left _ _) (F.t_surj k) b hb
    obtain ⟨w, hw, ew⟩ := hmark a ha
    obtain ⟨c, hc⟩ := hsur _ (sub_mem (add_mem hw ((hlat _).1 (M.φ k e).2)) (M.φ k e).2)
    refine ⟨c, ?_⟩
    rw [hc, map_add, map_nsmul, Submodule.coe_add, Submodule.coe_smul_of_tower, Matrix.mulVec_add, ew,
      Matrix.mulVec_smul, smul_sub, smul_add]
    abel
  · obtain ⟨c, hc⟩ := hsur _ (sub_mem ((hlat _).1 (M.φ k a).2) (M.φ k a).2)
    exact ⟨c, by rw [hc, hA, one_smul, add_sub_cancel]⟩
  · congr 1
    funext τ
    have e1 : mat x τ = archM V (th k τ) u * x₀ τ.1 := hf τ
    have e2 : mat x' τ = archM V (th k τ) (δ * u * k₀) * x₀ τ.1 := hf' τ
    change mat x' τ = δ₀.1.map τ.1 * mat x τ
    rw [e1, e2, archM_mul V _ δ u k₀ ((hK k₀).1 hk₀).1, hδa τ.1 _ (hth k τ), Matrix.mul_assoc]

theorem marked_points_differ_by_arith : ThetaUnifAV → Out.Laws → ∀ (D : D7) (Q : Par D), Q.Pins → ∀ (j : ℕ) (hj : InR D j) (σ' : KA Q.l →+* ℂ) (g : ℕ) (ty : Fin g → (D.host.E →+* ℂ)) (F : FamilyUnif (Q.Xo j) σ' ty), σ' (baseKA Q.l).ρ = Q.H.rt0 → IsTypeFn Q.H (Q.Dw j).p (Q.Dw j).q ty → ∀ (M : GlobalTheory.FrameUnif.ModelsOf F D.R.r) (io : (Q.Dw j).La →ₗ[𝓞 D.host.E] (Fin (D.sp.W j).rank → D.host.E)) (th : ∀ k, (M.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ), RecOK M (D.sp.W j) (D.sp.W_rank j hj.1 hj.2) io th x₀ → ∀ Kf : Subgroup (GA D (D.sp.W j)), IsLevelK (D.sp.W j) (D.host.g 0 * D.host.g 1) Kf → ∀ (h γ₀ k₀ : GA D (D.sp.W j)) (p p' : Σ k, Frame (M.X k).Ψ D.R.r), γ₀ ∈ GQ (D.sp.W j) → k₀ ∈ Kf → MarkSpec M (D.sp.W j) (D.sp.W_rank j hj.1 hj.2) io th x₀ h p → MarkSpec M (D.sp.W j) (D.sp.W_rank j hj.1 hj.2) io th x₀ (γ₀ * h * k₀) p' → ∃ γ' ∈ (M.X p.1).Γ, p' = ⟨p.1, lact γ' p.2⟩ := by
  intro hT hL D Q hQ j hj σ' g ty F hσ hty M io th x₀ hrec Kf hK h γ₀ k₀ p p' hγ₀ hk₀ hp hp'
  obtain ⟨-, ⟨hM, hA⟩, -, -⟩ := hQ
  have hpq : 1 ≤ (Q.Dw j).p + (Q.Dw j).q := by
    rw [← hrec.1.rank]
    have := D.R.m_add_three_le_k
    unfold Ranks.r
    omega
  exact marked_differ hT hL D _ F hpq hσ hty hA _ M io th x₀ hrec Kf (hM ▸ hK) h γ₀ k₀ p p' hγ₀ hk₀ hp hp'

end GlobalTheory.MarkCoset
