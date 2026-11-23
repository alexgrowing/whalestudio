import Development.WeilBound.ThetaLifts.LatticeBasics.FinOrbit
import Development.WeilBound.ThetaLifts.LatticeBasics.FdEqZero
import Development.WeilBound.ThetaLifts.LatticeBasics.NonZero
import Development.WeilBound.ThetaLifts.ConeHypotheses.PureEqPureA
import Development.WeilBound.ThetaLifts.CartanFactorisation.IntegrableOnRight
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CountableCompactOpen

noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix Cardinal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

def CptOpen : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) (r s : ℕ), B.IsGood σ → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) → min r s = 0 →
    ∃ K : Subgroup (UA σ Y.J), IsOpen (K : Set (UA σ Y.J)) ∧ IsCompact (K : Set (UA σ Y.J))

def PolRank : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (r s r' s' : ℕ), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' → Module.rank ℂ (M.Pol B.ψ B.emb) ≤ ℵ₀

namespace Herm

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {B : Base F E} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {om : Rep σ X W}

theorem rank_polData (hM : M.IsGood B.ψ) (h : Module.rank ℂ (M.Pol B.ψ B.emb) ≤ ℵ₀) : Module.rank ℂ (PolData B M) ≤ ℵ₀ := by
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F
  let p : SInf F (Fin n × Fin d) →ₗ[ℂ] ((Fin n × Fin d → Af F) → ℂ) →ₗ[ℂ] Fn F n d :=
    LinearMap.mk₂ ℂ (fun f g => pureA F f g) (fun _ _ _ => funext fun _ => add_mul _ _ _)
      (fun _ _ _ => funext fun _ => mul_assoc _ _ _) (fun _ _ _ => funext fun _ => mul_add _ _ _)
      (fun _ _ _ => funext fun _ => mul_left_comm _ _ _)
  have le : PolData B M ≤ Submodule.map₂ p (M.Pol B.ψ B.emb) (SB _) := Submodule.span_le.2 (by
    rintro _ ⟨f, hf, φ, h1, h2, rfl⟩
    obtain ⟨g, hg, e⟩ := PositivityTheory.ThKG.pure_eq_pureA hM φ h1 h2
    exact e f ▸ Submodule.apply_mem_map₂ p hf hg)
  refine (Submodule.rank_mono le).trans ?_
  rw [TensorProduct.map₂_eq_range_lift_comp_mapIncl]
  refine (LinearMap.rank_le_domain _).trans ?_
  rw [rank_tensorProduct']
  exact (mul_le_mul' h (GlobalTheory.CompanionTheory.Ar.RT.Inj.Rank.rank_SB_le _)).trans Cardinal.aleph0_mul_aleph0.le

def Il {χ χ' : Chr F E} (hw : M.IsWeil B.ψ χ χ' om) (hc : ∀ Φ ∈ schA F _, M.Conv om Φ) :
    schA F (Fin n × Fin d) →ₗ[ℂ] (UA σ W.J → ℂ) where
  toFun Φ := M.I om Φ
  map_add' Φ Ψ := funext (PositivityTheory.ThKG.I_add hw hc Φ.2 Ψ.2)
  map_smul' c Φ := funext (PositivityTheory.ThKG.I_smul M om c Φ)

theorem I_rt (Φ : Fn F n d) (g h : UA σ W.J) : M.I om (om (1, g) Φ) h = M.I om Φ (h * g) := by
  simp only [Model.I, theta, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]

theorem exists_form {J : Matrix (Fin n) (Fin n) E} (c : Cpt σ J) {μ : Measure (UA σ J)} {D : Set (UA σ J)} (hμ : μ.IsHaarMeasure)
    (hD : IsFundamentalDomain (ratU σ J) D μ) {P : Type} [AddCommGroup P] [Module ℂ P] {u u' : P →ₗ[ℂ] (UA σ J → ℂ)}
    (hc : ∀ x, Continuous (u x)) (hc' : ∀ x, Continuous (u' x)) (hi : ∀ x, ∀ γ ∈ ratU σ J, ∀ g, u x (γ * g) = u x g)
    (hi' : ∀ x, ∀ γ ∈ ratU σ J, ∀ g, u' x (γ * g) = u' x g) (ρ : UA σ J →* Module.End ℂ P)
    (he : ∀ g x h, u (ρ g x) h = u x (h * g)) (he' : ∀ g x h, u' (ρ g x) h = u' x (h * g)) :
    ∃ b : P →ₗ⋆[ℂ] P →ₗ[ℂ] ℂ, (∀ x y, b x y = pet μ D (u y) (u' x)) ∧ ∀ g x y, b (ρ g x) (ρ g y) = b x y := by
  haveI : IsFiniteMeasure (μ.restrict D) := isFiniteMeasure_restrict.2 (c.fin _ _ hμ hD).ne
  have ii : ∀ x y, Integrable (fun g => u y g * star (u' x g)) (μ.restrict D) := fun x y => by
    have h := (hc y).mul (hc' x).star
    obtain ⟨C, hC⟩ := c.bdd h fun γ hγ g => by simp only [Pi.mul_apply, hi y γ hγ, hi' x γ hγ]
    exact Integrable.of_bound h.aestronglyMeasurable C (Eventually.of_forall hC)
  haveI := c.cnt
  haveI := c.right μ hμ
  refine ⟨LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun x y => pet μ D (u y) (u' x))
    (fun x x' y => ?_) (fun a x y => ?_) (fun x y y' => ?_) (fun a x y => ?_), fun _ _ => rfl, fun g x y => ?_⟩
  · rw [pet, pet, pet, ← integral_add (ii x y) (ii x' y)]; simp [mul_add]
  · simp [pet, ← integral_const_mul, mul_left_comm]
  · rw [pet, pet, pet, ← integral_add (ii x y) (ii x y')]; simp [add_mul]
  · simp [pet, ← integral_const_mul, mul_assoc]
  · simp only [LinearMap.mk₂'ₛₗ_apply, pet, he, he']
    exact PositivityTheory.ThKF.L2.integral_right hD (fun h => u y h * star (u' x h)) (fun γ hγ h => by rw [hi y γ hγ, hi' x γ hγ]) g

theorem line_cpt {J : Matrix (Fin n) (Fin n) E} (cW : Cpt σ J) {μ : Measure (UA σ J)} {D : Set (UA σ J)} (hμ : μ.IsHaarMeasure)
    (hD : IsFundamentalDomain (ratU σ J) D μ) {P : Type} [AddCommGroup P] [Module ℂ P] {u v v' : P →ₗ[ℂ] (UA σ J → ℂ)}
    (ρ : UA σ J →* Module.End ℂ P) (H : ∀ w ∈ ({u, v, v'} : Set _), (∀ x, Continuous (w x)) ∧
      (∀ x, ∀ γ ∈ ratU σ J, ∀ g, w x (γ * g) = w x g) ∧ (∀ g x h, w (ρ g x) h = w x (h * g)) ∧ ∀ x, u x = 0 → w x = 0)
    (hr : Module.rank ℂ (LinearMap.range u) ≤ ℵ₀) (K : Subgroup (UA σ J)) (k1 : IsOpen (K : Set (UA σ J)))
    (k2 : IsCompact (K : Set (UA σ J)))
    (irr : ∀ N : Submodule ℂ P, LinearMap.ker u ≤ N → (∀ g, ∀ x ∈ N, ρ g x ∈ N) → N ≤ LinearMap.ker u ∨ N = ⊤) :
    ∃ lam : ℂ, ∀ x y, pet μ D (v x) (v' y) = lam * pet μ D (u x) (u y) := by
  obtain ⟨a1, a2, a3, a4⟩ := H u (by simp)
  obtain ⟨b1, b2, b3, b4⟩ := H v (by simp)
  obtain ⟨c1, c2, c3, c4⟩ := H v' (by simp)
  obtain ⟨b, eb, ib⟩ := exists_form cW hμ hD b1 c1 b2 c2 ρ b3 c3
  obtain ⟨c, ec, ic⟩ := exists_form cW hμ hD a1 a1 a2 a2 ρ a3 a3
  obtain ⟨Ω, hΩ, cov⟩ := cW.cov
  have := cW.lc
  have := cW.t2
  obtain ⟨lam, hl⟩ := line ρ u a1 a3 hr K k1 k2 hΩ (fun g => (cov g).elim fun γ hγ => ⟨_, hγ.2, fun x => (a2 x γ hγ.1 g).symm⟩)
    b c ib ic (fun x y => by rw [ec, ec, pet, pet, ← integral_conj]; simp [mul_comm])
    (fun x => by
      rw [ec, pet, show (fun h => u x h * star (u x h)) = fun h => ((‖u x h‖ ^ 2 : ℝ) : ℂ) from
        funext fun h => by simp [Complex.mul_conj'], integral_complex_ofReal]
      exact integral_nonneg fun _ => by positivity)
    (fun x hx => cW.eq_zero hμ hD (a1 x) (a2 x) (ec x x ▸ hx))
    (fun x hx => LinearMap.ext fun y => by rw [eb, c4 x hx]; simp [pet])
    (fun x hx => LinearMap.ext fun y => by rw [LinearMap.flip_apply, eb, b4 x hx]; simp [pet])
    (fun x hx => LinearMap.ext fun y => by rw [LinearMap.flip_apply, ec, a4 x hx]; simp [pet]) irr
  exact ⟨lam, fun x y => by rw [← eb, ← ec, hl]⟩

end Herm

open Herm in
theorem hermLine_of (hC : CptAll) (hK : CptOpen) (hR : PolRank) (hS : PairsStable) (hJ : PairsIrr) (hF : Factor) (hN : NonZeroAn)
    (hW : WeilConv) (hB : ThetaBasic) (hI : PositivityTheory.ThKF.ICont) (hM : MatchEx) : HermLine := by
  intro F E _ _ _ _ _ σ B a a' G X om om' R Rf h hp hq μ D hμ hD s t s' t'
  have T := h.triple
  have cW := hC F E σ B _ G.W _ _ T.base (Or.inr T.geo.hW) (by omega)
  obtain ⟨K, k1, k2⟩ := hK F E σ B _ G.W _ _ T.base (Or.inr T.geo.hW) (by omega)
  obtain ⟨-, m2, m3⟩ := hM F E σ B a a' G X om om' R Rf h
  obtain ⟨st1, st2⟩ := hS F E σ B a a' G X om om' R Rf h hp hq
  obtain ⟨f1, f2⟩ := hF F E σ B a a' G X om om' R Rf h
  have z0 : (0 : Fn F a (a + a') × Fn F a' (a + a')) ∈ pairs B G X R Rf :=
    ⟨zero_mem _, X.T, le_rfl, 0, 0, Fin.elim0, Fin.elim0, Fin.elim0, Fin.elim0, by simp⟩
  let P : Submodule ℂ (Fn F a (a + a') × Fn F a' (a + a')) :=
    { carrier := pairs B G X R Rf
      zero_mem' := z0
      add_mem' := fun hx hy => by simpa using st1 _ hx _ hy 1
      smul_mem' := fun c x hx => by simpa using st1 _ z0 _ hx c }
  have s1 : ∀ y : P, y.1.1 ∈ schA F _ := fun y => PositivityTheory.ThKG.polData_le T.geo.hM (m3 _ _ y.2.1 y.2.2).1
  have s2 : ∀ y : P, y.1.2 ∈ schA F _ := fun y => PositivityTheory.ThKG.polData_le T.geo.hM' (m3 _ _ y.2.1 y.2.2).2.1
  let I₁ := Il T.weil fun Φ hΦ => ((hW F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV T) (Or.inr (by omega))).1 Φ hΦ).1
  let I₂ := Il T.weil' fun Φ hΦ => ((hW F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV' T) (Or.inr (by omega))).1 Φ hΦ).1
  let j₂ := (LinearMap.snd ℂ _ _ ∘ₗ P.subtype).codRestrict _ s2
  let io : ℂ → ℂ → P →ₗ[ℂ] (UA σ G.W.J → ℂ) := fun s t =>
    s • I₁ ∘ₗ (LinearMap.fst ℂ _ _ ∘ₗ P.subtype).codRestrict _ s1 + t • I₂ ∘ₗ j₂
  have eio : ∀ s t y, io s t y = comb G om om' s t y.1 := fun _ _ _ => rfl
  have e01 : ∀ y, io 0 1 y = G.M'.I om' y.1.2 := fun y => by simp [eio, comb]
  let ρ : UA σ G.W.J →* Module.End ℂ P :=
    { toFun := fun g => ((om (1, g)).prodMap (om' (1, g))).restrict fun y hy => st2 y hy g
      map_one' := LinearMap.ext fun y => Subtype.ext (show (om 1 y.1.1, om' 1 y.1.2) = y.1 by simp)
      map_mul' := fun g g' => LinearMap.ext fun y => Subtype.ext
        (show (om (1, g * g') y.1.1, om' (1, g * g') y.1.2) = (om (1, g) (om (1, g') y.1.1), om' (1, g) (om' (1, g') y.1.2)) by
          simp only [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]) }
  have he : ∀ s t g y x, io s t (ρ g y) x = io s t y (x * g) := fun s t g y x =>
    show s * G.M.I om (om (1, g) y.1.1) x + t * G.M'.I om' (om' (1, g) y.1.2) x = _ by rw [I_rt, I_rt]; rfl
  have cc : ∀ s t y, Continuous (io s t y) := fun s t y =>
    (((hI F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV T)).1 (Or.inr (by omega)) _ (s1 y)).const_smul s).add
      (((hI F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV' T)).1 (Or.inr (by omega)) _ (s2 y)).const_smul t)
  have ci : ∀ s t y, ∀ γ ∈ ratU σ G.W.J, ∀ g, io s t y (γ * g) = io s t y g := fun s t y γ hγ g => by
    have b1 := ((hB F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV T)).1 _ (s1 y)).2.1 1 (one_mem _) γ hγ
    have b2 := ((hB F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV' T)).1 _ (s2 y)).2.1 1 (one_mem _) γ hγ
    simp only [one_mul] at b1 b2
    simp only [eio, comb, Pi.add_apply, Pi.smul_apply, Model.I, b1, b2]
  have nul : ∀ s t (y : P), PolMatch B G X R Rf y.1.1 0 → io s t y = 0 := fun s t y hy => by
    have := st1 _ y.2 (y.1.1, 0) ⟨zero_mem _, hy⟩ (-1)
    rw [show y.1 + (-1 : ℂ) • (y.1.1, 0) = (0, y.1.2) by ext <;> simp] at this
    rw [eio, comb, f1 _ hy, f2 _ y.2.1 this.2]; simp
  have irr : ∀ N : Submodule ℂ P, LinearMap.ker (io 0 1) ≤ N → (∀ g, ∀ x ∈ N, ρ g x ∈ N) →
      (∀ y ∈ N, PolMatch B G X R Rf y.1.1 0) ∨ N = ⊤ := fun N h1 h2 =>
    (hJ F E σ B a a' G X om om' R Rf h hp hq (N.map P.subtype) (by rintro _ ⟨y, -, rfl⟩; exact y.2)
      (fun y hy h0 => ⟨⟨y, hy⟩, h1 (nul 0 1 ⟨y, hy⟩ h0), rfl⟩) (by rintro _ ⟨y, hy, rfl⟩ g; exact ⟨_, h2 g y hy, rfl⟩)).imp
      (fun h y hy => h _ ⟨y, hy, rfl⟩) fun h => eq_top_iff.2 fun y _ => by
        obtain ⟨z, hz, e⟩ := h y.2
        exact (Subtype.ext e : z = y) ▸ hz
  have ker : ∀ s t y, io 0 1 y = 0 → io s t y = 0 := fun s t y hy => by
    refine (irr _ le_rfl fun g x hx => funext fun z => ?_).elim (fun h => nul s t y (h y hy)) fun h0 => ?_
    · rw [he, show io 0 1 x = 0 from hx]; rfl
    · obtain ⟨Φ', r1, r2⟩ := (hN F E σ B a a' G X om om' T).2 hq
      obtain ⟨Φ, hΦ⟩ := m2 Φ' r1.1
      exact absurd ((e01 ⟨(Φ, Φ'), r1.2, hΦ⟩).symm.trans (h0.ge trivial)) r2
  have le : LinearMap.range (io 0 1) ≤ ((PolData B G.M').comap (schA F _).subtype).map I₂ := by
    rintro _ ⟨y, rfl⟩
    exact ⟨j₂ y, (m3 _ _ y.2.1 y.2.2).2.1, (e01 y).symm⟩
  obtain ⟨lam, hl⟩ := line_cpt cW hμ hD (u := io 0 1) (v := io s t) (v' := io s' t') ρ
    (by rintro _ (rfl | rfl | rfl) <;> exact ⟨cc _ _, ci _ _, he _ _, ker _ _⟩)
    ((Submodule.rank_mono le).trans ((rank_map_le _ _).trans
      ((Submodule.comapSubtypeEquivOfLe (PositivityTheory.ThKG.polData_le T.geo.hM')).rank_eq.trans_le
        (rank_polData T.geo.hM' (hR F E σ B _ _ _ _ _ _ _ _ _ T.base T.geo.hV' T.geo.hW))))) K k1 k2
    fun N h1 h2 => (irr N h1 h2).imp_left fun h y hy => nul 0 1 y (h y hy)
  exact ⟨lam, fun y hy y' hy' => hl ⟨y, hy⟩ ⟨y', hy'⟩⟩

end GlobalTheory.ThK.Dbl

end
