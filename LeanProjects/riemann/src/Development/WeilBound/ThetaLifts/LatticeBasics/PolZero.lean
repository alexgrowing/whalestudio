import Development.WeilBound.ThetaLifts.LatticeBasics.FdEqZero
import Development.WeilBound.ThetaLifts.LatticeBasics.NonZero

noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem I_left {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) {om : Rep σ X W} {Φ : Fn F n d}
    (h : ∀ γ ∈ ratU σ X.J, ∀ γ' ∈ ratU σ W.J, ∀ g h, theta om Φ (γ * g) (γ' * h) = theta om Φ g h) :
    ∀ γ ∈ ratU σ W.J, ∀ x, M.I om Φ (γ * x) = M.I om Φ x := fun γ hγ x => by
  unfold Model.I
  have e : ∀ g, theta om Φ g (γ * x) = theta om Φ g x := fun g => by simpa only [one_mul] using h 1 (one_mem _) γ hγ g x
  simp only [e]

theorem swap_bdd {A B : Type} [TopologicalSpace A] [MeasurableSpace A] [BorelSpace A] [SecondCountableTopology A]
    [TopologicalSpace B] [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology B] (μ : Measure A) (ν : Measure B)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {f : A × B → ℂ} (c : Continuous f) {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) :
    ∫ a, ∫ b, f (a, b) ∂ν ∂μ = ∫ b, ∫ a, f (a, b) ∂μ ∂ν :=
  integral_integral_swap (f := fun a b => f (a, b)) (Integrable.of_bound c.aestronglyMeasurable C (Eventually.of_forall hC))

theorem int_th {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) {om : Rep σ X W} {Ψ : Fn F n d}
    (cX : Cpt σ X.J) (cW : Cpt σ W.J) (h1 : M.μ.IsHaarMeasure) (h2 : IsFundamentalDomain (ratU σ X.J) M.dom M.μ)
    {μ : Measure (UA σ W.J)} {D : Set (UA σ W.J)} (hμ : μ.IsHaarMeasure) (hD : IsFundamentalDomain (ratU σ W.J) D μ)
    (hc : Continuous fun x : UA σ X.J × UA σ W.J => theta om Ψ x.1 x.2)
    (hi : ∀ γ ∈ ratU σ X.J, ∀ γ' ∈ ratU σ W.J, ∀ g h, theta om Ψ (γ * g) (γ' * h) = theta om Ψ g h)
    {φ : UA σ W.J → ℂ} (pc : Continuous φ) (pi : ∀ γ ∈ ratU σ W.J, ∀ g, φ (γ * g) = φ g) :
    ∫ g in M.dom, th om μ D φ Ψ g ∂M.μ = pet μ D φ (M.I om Ψ) := by
  haveI := cX.sc; haveI := cW.sc
  haveI : IsFiniteMeasure (M.μ.restrict M.dom) := isFiniteMeasure_restrict.2 (cX.fin _ _ h1 h2).ne
  haveI : IsFiniteMeasure (μ.restrict D) := isFiniteMeasure_restrict.2 (cW.fin _ _ hμ hD).ne
  have c : Continuous fun x : UA σ X.J × UA σ W.J => φ x.2 * star (theta om Ψ x.1 x.2) := (pc.comp continuous_snd).mul hc.star
  obtain ⟨C, hC⟩ := cX.bdd₂ cW c fun γ hγ δ hδ g g' => by simp only [pi δ hδ, hi γ hγ δ hδ]
  unfold th pet Model.I
  refine (swap_bdd _ _ c hC).trans <| integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [integral_const_mul]
  exact congrArg _ integral_conj

theorem polZero_of (hC : CptAll) (hH : HermLine) (hL : CoefLine) (hT : ThConst) (hN : NonZeroAn) (hM : MatchEx)
    (hB : ThetaBasic) (hI : PositivityTheory.ThKF.ICont) (hP : PolSch) : PolZero := by
  intro F E _ _ _ _ _ σ B a a' G X om om' R Rf h hp hq
  have t := h.triple
  have cW := hC F E σ B _ G.W _ _ t.base (Or.inr t.geo.hW) (by omega)
  have cV := hC F E σ B _ G.V' _ _ t.base (Or.inl t.geo.hV') (by omega)
  obtain ⟨μ, D, hμ, hD⟩ := cW.ex
  obtain ⟨m1, m2, m3⟩ := hM F E σ B a a' G X om om' R Rf h
  have b1 := (hB F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV t)).1
  have b2 := (hB F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV' t)).1
  have s1 : ∀ y ∈ pairs B G X R Rf, y.1 ∈ schA F _ := fun y hy =>
    hP F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV t) _ (m3 _ _ hy.1 hy.2).1
  have s2 : ∀ y ∈ pairs B G X R Rf, y.2 ∈ schA F _ := fun y hy =>
    hP F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV' t) _ (m3 _ _ hy.1 hy.2).2.1
  have c1 := (hI F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV t)).1 (Or.inr (by omega))
  have c2 := (hI F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV' t)).1 (Or.inr (by omega))
  have cc : ∀ s u, ∀ y ∈ pairs B G X R Rf, Continuous (comb G om om' s u y) := fun s u y hy =>
    ((c1 _ (s1 y hy)).const_smul s).add ((c2 _ (s2 y hy)).const_smul u)
  have ci : ∀ s u, ∀ y ∈ pairs B G X R Rf, ∀ γ ∈ ratU σ G.W.J, ∀ g, comb G om om' s u y (γ * g) = comb G om om' s u y g :=
    fun s u y hy γ hγ g => by
      simp only [comb, Pi.add_apply, Pi.smul_apply, I_left G.M (b1 _ (s1 y hy)).2.1 γ hγ, I_left G.M' (b2 _ (s2 y hy)).2.1 γ hγ]
  have e01 : ∀ y, comb G om om' 0 1 y = G.M'.I om' y.2 := fun y => by simp [comb]
  haveI : IsFiniteMeasure (μ.restrict D) := isFiniteMeasure_restrict.2 (cW.fin _ _ hμ hD).ne
  have ig : ∀ s u s' u', ∀ y ∈ pairs B G X R Rf, ∀ y' ∈ pairs B G X R Rf,
      Integrable (fun g => comb G om om' s u y g * star (comb G om om' s' u' y' g)) (μ.restrict D) := fun s u s' u' y hy y' hy' => by
    have c := (cc s u y hy).mul (cc s' u' y' hy').star
    obtain ⟨C, hC⟩ := cW.bdd c fun γ hγ g => by simp only [Pi.mul_apply, ci s u y hy γ hγ, ci s' u' y' hy' γ hγ]
    exact Integrable.of_bound c.aestronglyMeasurable C (Eventually.of_forall hC)
  obtain ⟨c, hc⟩ := hH F E σ B a a' G X om om' R Rf h hp hq μ D hμ hD 1 0 0 1
  have orth : ∀ y ∈ pairs B G X R Rf, pet μ D (comb G om om' 1 (-c) y) (comb G om om' 0 1 y) = 0 := fun y hy => by
    have e : pet μ D (comb G om om' 1 (-c) y) (comb G om om' 0 1 y) =
        pet μ D (comb G om om' 1 0 y) (comb G om om' 0 1 y) - c * pet μ D (comb G om om' 0 1 y) (comb G om om' 0 1 y) := by
      unfold pet
      rw [← integral_const_mul, ← integral_sub (ig _ _ _ _ y hy y hy) ((ig _ _ _ _ y hy y hy).const_mul c)]
      refine integral_congr_ae (Eventually.of_forall fun g => ?_)
      simp only [comb, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [e, hc y hy y hy, sub_self]
  obtain ⟨lam, hl⟩ := hH F E σ B a a' G X om om' R Rf h hp hq μ D hμ hD 1 (-c) 1 (-c)
  obtain ⟨⟨Φ₀, q1, q2⟩, Φ', r1, r2⟩ := And.imp (fun f => f hp) (fun f => f hq) (hN F E σ B a a' G X om om' t)
  obtain ⟨Φ, hΦ⟩ := m2 Φ' r1.1
  have hy : (Φ, Φ') ∈ pairs B G X R Rf := ⟨r1.2, hΦ⟩
  have v0 := cV.vol_ne t.geo.hM'.haar t.geo.hM'.dom
  have key : ∀ s u, th om' μ D (comb G om om' s u (Φ, Φ')) Φ' =
      fun _ => pet μ D (comb G om om' s u (Φ, Φ')) (comb G om om' 0 1 (Φ, Φ')) / (G.M'.μ.real G.M'.dom : ℂ) := fun s u => by
    have k := (hT F E σ B a a' G X om om' R Rf h s u (fun y hy => cW.rapid (cc s u y hy) (ci s u y hy)) μ D hμ hD _ hy).2 Φ'
      (s2 _ hy)
    have i := int_th G.M' cV cW t.geo.hM'.haar t.geo.hM'.dom hμ hD (b2 _ (s2 _ hy)).1 (b2 _ (s2 _ hy)).2.1 (cc s u _ hy) (ci s u _ hy)
    simp only [k, setIntegral_const, Complex.real_smul] at i
    funext g
    rw [k, e01, ← i, mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.2 v0)]
  have n0 : pet μ D (comb G om om' 0 1 (Φ, Φ')) (comb G om om' 0 1 (Φ, Φ')) ≠ 0 := fun h0 =>
    r2 (e01 (Φ, Φ') ▸ cW.eq_zero hμ hD (cc 0 1 _ hy) (ci 0 1 _ hy) h0)
  have l0 : lam = 0 := by
    have := hL F E σ B a a' G X om om' R Rf h hp hq μ D hμ hD 1 (-c) lam hl _ hy Φ' r1.1
    rw [key, key, orth _ hy] at this
    generalize pet μ D (comb G om om' 0 1 (Φ, Φ')) (comb G om om' 0 1 (Φ, Φ')) = x at this n0
    simpa [pet, n0, v0] using this
  have main : PolConst B G X om om' R Rf c := fun Ψ Ψ' h1 h2 g => by
    have hz : (Ψ, Ψ') ∈ pairs B G X R Rf := ⟨h1, h2⟩
    have := congrFun (cW.eq_zero hμ hD (cc 1 (-c) _ hz) (ci 1 (-c) _ hz) (by rw [hl _ hz _ hz, l0, zero_mul])) g
    simp only [comb, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
    linear_combination this
  refine ⟨c, fun c0 => q2 (funext fun g => ?_), main⟩
  obtain ⟨Ψ', h1, h2⟩ := m1 Φ₀ q1
  rw [main Φ₀ Ψ' h1 h2 g, c0, zero_mul]; rfl

end GlobalTheory.ThK.Dbl

end
