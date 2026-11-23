import Development.WeilBound.ThetaLifts.CartanFactorisation.RadOfZero
import Development.WeilBound.ThetaLifts.CartanFactorisation.AdmDef
import Development.WeilBound.ThetaLifts.CartanFactorisation.IntegrableOnRight
import Development.WeilBound.ThetaLifts.CartanFactorisation.Unimod
import Development.WeilBound.ThetaLifts.ConeHypotheses.PureEqPureA

noncomputable section

namespace PositivityTheory.ThKF

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped ComplexConjugate

theorem maximal_of {Q P : Type} [AddCommGroup Q] [Module ℂ Q] [AddCommGroup P] [Module ℂ P] [Nontrivial P] (p : Q →ₗ[ℂ] P)
    (S : Submodule ℂ Q) (St : Submodule ℂ Q → Prop) (onto : S.map p = ⊤) (hle : ∀ N, St N → N ≤ S)
    (h0 : St (LinearMap.ker p ⊓ S)) (hirr : ∀ N, St N → N.map p = ⊥ ∨ N.map p = ⊤) :
    Maximal (fun N => St N ∧ N ≠ S) (LinearMap.ker p ⊓ S) := by
  refine ⟨⟨h0, fun e => ?_⟩, fun N hN hge x hx => ?_⟩
  · have : (⊤ : Submodule ℂ P) = ⊥ := by
      rw [← onto, ← e, eq_bot_iff]
      rintro _ ⟨x, hx, rfl⟩
      exact hx.1
    exact top_ne_bot this
  · rcases hirr N hN.1 with h | h
    · exact ⟨(Submodule.eq_bot_iff _).1 h _ ⟨x, hx, rfl⟩, hle N hN.1 hx⟩
    · refine absurd (le_antisymm (hle N hN.1) fun y hy => ?_) hN.2
      obtain ⟨z, hz, e⟩ : p y ∈ N.map p := h ▸ Submodule.mem_top
      have : y - z ∈ N := hge ⟨by simp [e], sub_mem hy (hle N hN.1 hz)⟩
      simpa using N.add_mem this hz

theorem max_comap {Q : Type} [AddCommGroup Q] [Module ℂ Q] (S : Submodule ℂ Q) (St : Submodule ℂ Q → Prop)
    (St' : Submodule ℂ S → Prop) (hle : ∀ N, St N → N ≤ S) (h : ∀ P : Submodule ℂ S, St' P ↔ St (P.map S.subtype))
    (N : Submodule ℂ Q) (hN : Maximal (fun N => St N ∧ N ≠ S) N) (hu : ∀ N', Maximal (fun N => St N ∧ N ≠ S) N' → N' = N) :
    Maximal (fun P => St' P ∧ P ≠ ⊤) (N.comap S.subtype) ∧
      ∀ P, Maximal (fun P => St' P ∧ P ≠ ⊤) P → P = N.comap S.subtype := by
  have mc : ∀ N, N ≤ S → (N.comap S.subtype).map S.subtype = N := fun N hN => by
    rw [Submodule.map_comap_subtype, inf_eq_right.2 hN]
  have inj := Submodule.map_injective_of_injective S.injective_subtype
  have ne : ∀ P : Submodule ℂ S, P ≠ ⊤ ↔ P.map S.subtype ≠ S := fun P => by
    constructor
    · intro h e; exact h (inj (e.trans (Submodule.map_subtype_top S).symm))
    · intro h e; exact h (e ▸ Submodule.map_subtype_top S)
  refine ⟨⟨⟨(h _).2 (by rw [mc N (hle N hN.prop.1)]; exact hN.prop.1), (ne _).2 (by rw [mc N (hle N hN.prop.1)]; exact hN.prop.2)⟩,
    fun P hP hge x hx => hN.le_of_ge ⟨(h P).1 hP.1, (ne P).1 hP.2⟩
      ((mc N (hle N hN.prop.1)).symm.le.trans (Submodule.map_mono hge)) ⟨x, hx, rfl⟩⟩, fun P hP => ?_⟩
  have := hu (P.map S.subtype) ⟨⟨(h P).1 hP.prop.1, (ne P).1 hP.prop.2⟩, fun N' hN' hge => by
    have h1 : N'.comap S.subtype ≤ P := hP.le_of_ge ⟨(h _).2 (by rw [mc N' (hle N' hN'.1)]; exact hN'.1),
      (ne _).2 (by rw [mc N' (hle N' hN'.1)]; exact hN'.2)⟩ (Submodule.map_le_iff_le_comap.1 hge)
    exact (mc N' (hle N' hN'.1)).symm.le.trans (Submodule.map_mono h1)⟩
  rw [← this, Submodule.comap_map_eq_of_injective S.injective_subtype]

theorem exists_beta {G : Type} [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G] (𝓕 : Set G) (μ : Measure G)
    {Q : Type} [AddCommGroup Q] [Module ℂ Q] (u : Q →ₗ[ℂ] (G → ℂ)) (hc : ∀ x, Continuous (u x))
    (h2 : ∀ x, IntegrableOn (fun g => ‖u x g‖ ^ 2) 𝓕 μ) :
    ∃ β : Q →ₗ⋆[ℂ] Q →ₗ[ℂ] ℂ, (∀ x y, β x y = ∫ g in 𝓕, conj (u x g) * u y g ∂μ) ∧
      (∀ x y, β x y = starRingEnd ℂ (β y x)) ∧ ∀ x, 0 ≤ (β x x).re := by
  have ii := fun x y => L2.integrableOn_mul (hc x) (hc y) (h2 x) (h2 y)
  refine ⟨LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun x y => ∫ g in 𝓕, conj (u x g) * u y g ∂μ)
    (fun x x' y => ?_) (fun c x y => ?_) (fun x y y' => ?_) (fun c x y => ?_), fun _ _ => rfl, fun x y => ?_, fun x => ?_⟩
  · rw [← integral_add (ii x y) (ii x' y)]; simp [add_mul]
  · simp [← integral_const_mul, mul_assoc]
  · rw [← integral_add (ii x y) (ii x y')]; simp [mul_add]
  · simp [← integral_const_mul, mul_left_comm]
  · simp only [LinearMap.mk₂'ₛₗ_apply]
    rw [← integral_conj]; simp [mul_comm]
  · simp only [LinearMap.mk₂'ₛₗ_apply]
    rw [← RCLike.re_to_complex, ← integral_re (ii x x)]
    exact integral_nonneg fun g => by
      simp only [Complex.conj_mul', Pi.zero_apply, RCLike.re_to_complex, ← Complex.ofReal_pow, Complex.ofReal_re]; positivity

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

def LocCpt : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (X : Spc F E n)
    (v : Pl F), (∀ g ∈ UAt σ X (evFin F v), g⁻¹ ∈ UAt σ X (evFin F v)) ∧
      (∀ g ∈ UAt σ X (evFin F v), ∀ g' ∈ UAt σ X (evFin F v), g * g' ∈ UAt σ X (evFin F v)) ∧ ∀ U ∈ 𝓝 (1 : UA σ X.J),
      ∃ K : Subgroup (UA σ X.J), IsCompact (K : Set (UA σ X.J)) ∧ (K : Set (UA σ X.J)) ⊆ U ∩ UAt σ X (evFin F v) ∧
        ∃ U' ∈ 𝓝 (1 : UA σ X.J), U' ∩ UAt σ X (evFin F v) ⊆ K

def KInfGrp : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (X : Spc F E n)
    (τ : ∀ w : InfinitePlace F, EmbOver E w), ∃ K : Subgroup (UA σ X.J), (K : Set (UA σ X.J)) = KInf σ X τ

structure Cls (B : Base F E) (M : Model σ X W) (om : Rep σ X W) (𝓒 : Submodule ℂ (Fn F n d)) : Prop where
  sch : 𝓒 ≤ schA F _
  conv : ∀ Φ ∈ 𝓒, M.Conv om Φ
  cont : ∀ Φ ∈ 𝓒, Continuous (M.I om Φ)
  contf : ∀ ψ ∈ SB (Fin n × Fin d → Af F), (∀ f : SInf F (Fin n × Fin d), pureA F f ψ ∈ 𝓒) →
    ∀ h, Continuous fun f : SInf F (Fin n × Fin d) => M.I om (pureA F f ψ) h
  sq : ∀ (μ : Measure (UA σ W.J)) (𝓕 : Set (UA σ W.J)), μ.IsHaarMeasure → IsFundamentalDomain (ratU σ W.J) 𝓕 μ →
    ∀ Φ ∈ 𝓒, Φ ∈ PolData B M → IntegrableOn (fun h => ‖M.I om Φ h‖ ^ 2) 𝓕 μ

section I

variable {B : Base F E} {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W} {r s r' s' : ℕ}

theorem I_add' (hp : IsPair B M χX χW om r s r' s') {𝓒} (hc : Cls B M om 𝓒) {Φ Ψ : Fn F n d} (hΦ : Φ ∈ 𝓒) (hΨ : Ψ ∈ 𝓒) :
    M.I om (Φ + Ψ) = M.I om Φ + M.I om Ψ := by
  funext h
  have e : ∀ g, theta om (Φ + Ψ) g h = theta om Φ g h + theta om Ψ g h := fun g => by
    simp only [theta, map_add]
    exact thetaSum_add F (hp.weil.isUSplitting.pres _ _ (hc.sch hΦ)) (hp.weil.isUSplitting.pres _ _ (hc.sch hΨ))
  simp only [Model.I, e, Pi.add_apply]
  exact integral_add (hc.conv _ hΦ h) (hc.conv _ hΨ h)

theorem I_right (Φ : Fn F n d) (h₀ h : UA σ W.J) : M.I om (om (1, h₀) Φ) h = M.I om Φ (h * h₀) := by
  simp only [Model.I, theta, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]

theorem det_of_sig {m : ℕ} {A : Matrix (Fin m) (Fin m) ℂ} {r s : ℕ} (h : HasSig A r s) : A.det ≠ 0 := by
  obtain ⟨e, P, hP⟩ := h
  have h1 : Pᵀ * (A * (P.map star * (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ))) = 1 := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hP, Matrix.fromBlocks_multiply]; simp
  rw [Matrix.mul_eq_one_comm_of_equiv (finSumFinEquiv.trans (finCongr e)), Matrix.mul_assoc] at h1
  exact (Matrix.isUnit_det_of_right_inverse h1).ne_zero

theorem detX (hp : IsPair B M χX χW om r s r' s') : X.J.det ≠ 0 := fun h0 => by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  refine det_of_sig (hp.herm.sig w) ?_
  rw [show X.J.map (B.emb w).1 = (RingHom.mapMatrix ((B.emb w).1 : E →+* ℂ)) X.J from rfl, ← RingHom.map_det, h0, map_zero]

theorem detW (hp : IsPair B M χX χW om r s r' s') : W.J.det ≠ 0 := fun h0 => by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  refine det_of_sig (hp.skew.sig w) ?_
  rw [Matrix.det_smul, show W.J.map (B.emb w).1 = (RingHom.mapMatrix ((B.emb w).1 : E →+* ℂ)) W.J from rfl, ← RingHom.map_det, h0,
    map_zero, mul_zero]

theorem uniX (hU : Unimod) (hp : IsPair B M χX χW om r s r' s') : Countable (ratU σ X.J) ∧ M.μ.IsMulRightInvariant := by
  obtain ⟨h1, -, h3⟩ := hU F E σ hp.base.cm n X.J 1 (fun i j => by simpa using hp.herm.herm i j) (detX hp)
  exact ⟨h1, h3 _ hp.good.haar⟩

theorem uniW (hU : Unimod) (hp : IsPair B M χX χW om r s r' s') : Countable (ratU σ W.J) ∧
    ∃ (μ : Measure (UA σ W.J)) (𝓕 : Set (UA σ W.J)), μ.IsHaarMeasure ∧ IsFundamentalDomain (ratU σ W.J) 𝓕 μ ∧
      μ.IsMulRightInvariant := by
  obtain ⟨h1, ⟨μ, 𝓕, h2, h2'⟩, h3⟩ := hU F E σ hp.base.cm d W.J (-1) (fun i j => by simpa using hp.skew.skew i j) (detW hp)
  exact ⟨h1, μ, 𝓕, h2, h2', h3 _ h2⟩

theorem I_left (hU : Unimod) (hT : ThetaBasic) (hp : IsPair B M χX χW om r s r' s') {Φ : Fn F n d} (hΦ : Φ ∈ schA F _)
    (g₀ : UA σ X.J) : M.I om (om (g₀, 1) Φ) = M.I om Φ := by
  funext h
  obtain ⟨h1, h2⟩ := uniX hU hp
  haveI := hp.good.haar
  haveI : BorelSpace (UA σ X.J) := ⟨rfl⟩
  have e : ∀ g, theta om (om (g₀, 1) Φ) g h = theta om Φ (g * g₀) h := fun g => by
    simp only [theta, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
  simp only [Model.I, e]
  exact L2.integral_right hp.good.dom (fun g => theta om Φ g h) (fun γ hγ g => by
    simpa using ((hT F E σ B n d X W M χX χW om r s r' s' hp).1 Φ hΦ).2.1 γ hγ 1 (one_mem _) g h) g₀

theorem I_inv (hT : ThetaBasic) (hp : IsPair B M χX χW om r s r' s') {Φ : Fn F n d} (hΦ : Φ ∈ schA F _) :
    L2.Inv (ratU σ W.J) (M.I om Φ) := fun γ hγ h => by
  simp only [Model.I]
  congr 1
  funext g
  simpa using ((hT F E σ B n d X W M χX χW om r s r' s' hp).1 Φ hΦ).2.1 1 (one_mem _) γ hγ g h

end I

end PositivityTheory.ThKF

end
