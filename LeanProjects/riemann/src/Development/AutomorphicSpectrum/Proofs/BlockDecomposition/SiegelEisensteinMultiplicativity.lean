import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousFrameEquivSymm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinSeriesConvergent
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousDerivFamily
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteKTypeDecompositionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StandardCompactFrameEquivStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicIffFrameParabolicStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlockDetParabolicFrameStatement

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelFrame

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.RgEis

theorem scalar_wall (hSec : SecLaw) (hWL : WallLaw) {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] (Γ K P : Subgroup G) (c : G → ℂ) (η β : G → ℝ) (hK : IsCompact (K : Set G)) (hP : IsPar Γ K P c)
    (hη : IsHt Γ K P η) (hβ : IsHt Γ K P β) (hW : AllRep K fun ρ => HasWall Γ K P P c η η β ρ) (f : G → ℂ) (u : ℂ)
    (hf : Continuous f) (hlaw : ∀ p ∈ P, ∀ x, f (p * x) = c p * Complex.exp (u * η p) * f x)
    (hfin : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : K => fun x => f (x * (k : G))))) :
    ∃ (R : ℝ) (D : ℂ → ℂ) (H : ℂ → G → ℂ), Differentiable ℂ D ∧ (∃ z, D z ≠ 0) ∧ (∀ g, Differentiable ℂ (H · g)) ∧
      Continuous (fun y : ℂ × G => H y.1 y.2) ∧
      (∀ x : ℝ, R < x → Conv Γ P fun g => x * η g) ∧ (∀ x : ℝ, x < -R → Conv Γ P fun g => β g - x * η g) ∧
      (∀ a b : ℝ, R < a → b < -R → ∃ M : ℝ, ∀ z : ℂ, b ≤ z.re → z.re ≤ a → ∀ g,
        ‖H z g‖ ≤ M * (pos Γ P (fun x => a * η x) g + pos Γ P (fun x => β x - b * η x) g)) ∧
      ∀ z : ℂ, R < z.re → ∀ g, HasSum (fun q : Cos P Γ =>
        D z * (Complex.exp ((z - u) * η (rep q * g)) * f (rep q * g))) (H z g) := by
  have h1 : η 1 = 0 := by
    have := hη.left 1 (one_mem _) 1
    simp only [mul_one] at this
    linarith
  have hzero : ∀ r ∈ P, r ∈ K → η r = 0 := fun r _ hr => by
    have := hη.right 1 r hr
    rwa [one_mul, h1] at this
  obtain ⟨d, ρ, w, e, hρ, hw, he⟩ := GlobalTheory.T.finite_K_type_decomposition G Γ K P c η hP.ch hzero
    (fun p hp q _ => hη.left p hp q) f u hf hlaw hfin
  obtain ⟨R, D, Op, H, hWl⟩ := hW (Fin d → ℂ) ρ hρ
  obtain ⟨hs₁, -, M₀, hM₀⟩ := hSec G (Fin d → ℂ) K ρ hK hρ Γ P c hP
  obtain ⟨-, -, hbd⟩ := hWL G (Fin d → ℂ) K ρ hK hρ Γ P P c η η β _ R D Op H hP hP hη hη hβ hWl
  let w' : secSp K P c ρ := ⟨w, hw⟩
  have hsec : ∀ y, f y = Complex.exp (u * η y) * e (sec K P c ρ y w) := by
    intro y
    obtain ⟨p, hp, k, hk, rfl⟩ := hP.iwa y
    rw [hs₁ w hw p hp ⟨k, hk⟩ |> fun h => (by simpa using h : sec K P c ρ (p * k) w = c p • ρ (⟨k, hk⟩ : K)⁻¹ w)]
    rw [map_smul, he, hlaw p hp k, hη.right p k hk, smul_eq_mul]
    ring
  refine ⟨R, D, fun z g => e (H z g w'), hWl.dEnt.1, hWl.dNe, fun g => ?_, ?_, hWl.convR, hWl.convL, ?_, ?_⟩
  · exact e.differentiable.comp ((hWl.hol g).clm_apply (differentiable_const _))
  · exact e.continuous.comp (hWl.cont.clm_apply continuous_const)
  · intro a b ha hb
    obtain ⟨M, hM⟩ := hbd a b ha hb
    refine ⟨‖e‖ * M * ‖w'‖, fun z h₁ h₂ g => ?_⟩
    have q₁ := e.le_opNorm (H z g w')
    have q₂ := (H z g).le_opNorm w'
    have q₃ := hM z h₁ h₂ g
    calc ‖e (H z g w')‖ ≤ ‖e‖ * ‖H z g w'‖ := q₁
      _ ≤ ‖e‖ * (‖H z g‖ * ‖w'‖) := by gcongr
      _ ≤ ‖e‖ * ((M * _) * ‖w'‖) := by gcongr
      _ = _ := by ring
  · intro z hz g
    have hconv := hWl.convR z.re hz g
    have hsum : Summable fun q : Cos P Γ => Complex.exp (z * η (rep q * g)) • sec K P c ρ (rep q * g) w := by
      refine Summable.of_norm_bounded (g := fun q : Cos P Γ => Real.exp (z.re * η (rep q * g)) * (M₀ * ‖w‖)) (hconv.mul_right _) fun q => ?_
      rw [norm_smul, Complex.norm_exp]
      have : ((z * (η (rep q * g) : ℂ))).re = z.re * η (rep q * g) := by simp
      rw [this]
      exact mul_le_mul_of_nonneg_left (hM₀ _ _) (Real.exp_pos _).le
    have h2 : HasSum (fun q : Cos P Γ => D z • (Complex.exp (z * η (rep q * g)) • sec K P c ρ (rep q * g) w)) (H z g w') := by
      have := hsum.hasSum.const_smul (D z)
      rwa [show (∑' q : Cos P Γ, Complex.exp (z * η (rep q * g)) • sec K P c ρ (rep q * g) w) =
        eis Γ K P c ρ (fun x => z * η x) g w from rfl, ← show H z g w' = D z • eis Γ K P c ρ (fun x => z * η x) g w from hWl.eqR z hz g w'] at this
    have h3 := e.hasSum h2
    have e2 : (fun q : Cos P Γ => e (D z • (Complex.exp (z * η (rep q * g)) • sec K P c ρ (rep q * g) w))) =
        fun q => D z * (Complex.exp ((z - u) * η (rep q * g)) * f (rep q * g)) := by
      funext q
      have e3 : Complex.exp (z * η (rep q * g)) = Complex.exp ((z - u) * η (rep q * g)) * Complex.exp (u * η (rep q * g)) := by
        rw [← Complex.exp_add]
        congr 1
        ring
      rw [hsec (rep q * g), map_smul, map_smul, smul_eq_mul, smul_eq_mul, e3]
      ring
    have h4 : HasSum (fun q : Cos P Γ => e (D z • (Complex.exp (z * η (rep q * g)) • sec K P c ρ (rep q * g) w))) (e (H z g w')) := h3
    rw [e2] at h4
    exact h4

theorem hasSum_cos {G U X : Type} [Group G] [Group U] [AddCommMonoid X] [TopologicalSpace X] (Φ : G ≃* U)
    (Γ P : Subgroup G) (Γ' P' : Subgroup U) (hΓ : ∀ x, x ∈ Γ ↔ Φ x ∈ Γ') (hP : ∀ x, x ∈ P ↔ Φ x ∈ P') (T : U → X)
    (hT : ∀ γ ∈ Γ', γ ∈ P' → ∀ y, T (γ * y) = T y) (y : U) (S : X)
    (h : HasSum (fun q : Cos P' Γ' => T (rep q * y)) S) :
    HasSum (fun q : Cos P Γ => T (Φ (rep q) * y)) S := by
  let m : Γ → Γ' := fun γ => ⟨Φ γ.1, (hΓ _).1 γ.2⟩
  have hrel : ∀ a b : Γ, QuotientGroup.rightRel (P.subgroupOf Γ) a b ↔ QuotientGroup.rightRel (P'.subgroupOf Γ') (m a) (m b) := by
    intro a b
    rw [QuotientGroup.rightRel_apply, QuotientGroup.rightRel_apply, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, hP]
    simp [m]
  let g : Cos P Γ → Cos P' Γ' := Quotient.map' m fun a b hab => (hrel a b).1 hab
  have hinj : Function.Injective g := by
    intro q₁ q₂
    induction q₁ using Quotient.inductionOn' with | h a => ?_
    induction q₂ using Quotient.inductionOn' with | h b => ?_
    intro e
    exact Quotient.sound' ((hrel a b).2 (Quotient.exact' e))
  have hsurj : Function.Surjective g := by
    intro q
    induction q using Quotient.inductionOn' with | h a => ?_
    refine ⟨Quotient.mk'' ⟨Φ.symm a.1, (hΓ _).2 (by simpa using a.2)⟩, ?_⟩
    show Quotient.mk'' (m _) = _
    congr 1
    apply Subtype.ext
    simp [m]
  have h2 := ((Equiv.ofBijective g ⟨hinj, hsurj⟩).hasSum_iff).2 h
  have e : ((fun q => T (rep q * y)) ∘ (Equiv.ofBijective g ⟨hinj, hsurj⟩)) = fun q : Cos P Γ => T (Φ (rep q) * y) := by
    funext q
    have e1 : (Quotient.mk'' (Quotient.out (g q)) : Cos P' Γ') = Quotient.mk'' (m (Quotient.out q)) := by
      rw [Quotient.out_eq']
      show g q = g (Quotient.mk'' (Quotient.out q))
      rw [Quotient.out_eq']
    have e2 := Quotient.exact' e1
    rw [QuotientGroup.rightRel_apply, Subgroup.mem_subgroupOf] at e2
    have e3 : Φ (rep q) * y = (((m (Quotient.out q)) * (Quotient.out (g q))⁻¹ : Γ') : U) * (rep (g q) * y) := by
      show _ = (Φ (Quotient.out q).1 * (Quotient.out (g q)).1⁻¹) * ((Quotient.out (g q)).1 * y)
      simp [rep, mul_assoc]
    rw [e3, hT _ (Subtype.coe_prop _) e2]
    rfl
  rw [e] at h2
  exact h2

theorem fin_pull {G U : Type} [Group G] [Group U] (Φ : G ≃* U) (K : Subgroup G) (K' : Subgroup U)
    (hKK : ∀ x, x ∈ K ↔ Φ x ∈ K') (f : G → ℂ)
    (hfin : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : K => fun x => f (x * (k : G))))) :
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : K' => fun y => f (Φ.symm (y * (k : U))))) := by
  have e : Submodule.span ℂ (Set.range fun k : K' => fun y => f (Φ.symm (y * (k : U)))) =
      (Submodule.span ℂ (Set.range fun k : K => fun x => f (x * (k : G)))).map (LinearMap.funLeft ℂ ℂ Φ.symm) := by
    rw [Submodule.map_span]
    congr 1
    ext v
    constructor
    · rintro ⟨k, rfl⟩
      refine ⟨_, ⟨⟨Φ.symm k, (hKK _).2 (by simpa using k.2)⟩, rfl⟩, ?_⟩
      funext y
      simp [LinearMap.funLeft_apply]
    · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
      refine ⟨⟨Φ k, (hKK _).1 k.2⟩, ?_⟩
      funext y
      simp [LinearMap.funLeft_apply]
  rw [e]
  infer_instance

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}

theorem rat_iff (χ : Chr F E) (ε : ℤˣ) (b : GL (Fin n ⊕ Fin n) E)
    (hb : b.1ᵀ * dbl Y.J * b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) (x : G2 σ Y) :
    x ∈ rat2 σ Y ↔ frameEquiv χ ε b hb x ∈ (adCM σ χ).uΓ ε (Fin n) := by
  constructor
  · rintro ⟨g, hg⟩
    refine Subgroup.mem_subgroupOf.2 ⟨b⁻¹ * g * b, ?_⟩
    show Matrix.GeneralLinearGroup.map (n := Fin n ⊕ Fin n) (inclR (F := F) (E := E) (AF F)) (b⁻¹ * g * b) = (bA b)⁻¹ * x.1 * bA b
    rw [map_mul, map_mul, map_inv, hg]
    rfl
  · intro h
    obtain ⟨g, hg⟩ := Subgroup.mem_subgroupOf.1 h
    refine Subgroup.mem_subgroupOf.2 ⟨b * g * b⁻¹, ?_⟩
    have hg' : Matrix.GeneralLinearGroup.map (n := Fin n ⊕ Fin n) (inclR (F := F) (E := E) (AF F)) g = (bA b)⁻¹ * x.1 * bA b := hg
    show Matrix.GeneralLinearGroup.map (n := Fin n ⊕ Fin n) (inclR (F := F) (E := E) (AF F)) (b * g * b⁻¹) = x.1
    rw [map_mul, map_mul, map_inv, hg']
    show bA b * ((bA b)⁻¹ * x.1 * bA b) * (bA b)⁻¹ = x.1
    group

theorem ext_mul {G : Type} [Group G] (K P : Subgroup G) (f : G → ℝ) (hadd : ∀ p ∈ P, ∀ q ∈ P, f (p * q) = f p + f q)
    (h0 : ∀ r ∈ P, r ∈ K → f r = 0) {p k : G} (hp : p ∈ P) (hk : k ∈ K) : ext K P f (p * k) = f p := by
  have h : ∃ k' : K, p * k * (k' : G)⁻¹ ∈ P := ⟨⟨k, hk⟩, by simpa using hp⟩
  unfold ext
  rw [dif_pos h]
  have hs := h.choose_spec
  have hr : k * (h.choose : G)⁻¹ ∈ K := K.mul_mem hk (K.inv_mem h.choose.2)
  have e : p * k * (h.choose : G)⁻¹ = p * (k * (h.choose : G)⁻¹) := by group
  rw [e] at hs ⊢
  have hrP : k * (h.choose : G)⁻¹ ∈ P := by
    have := P.mul_mem (P.inv_mem hp) hs
    simpa using this
  rw [hadd p hp _ hrP, h0 _ hrP hr, add_zero]

theorem uH_eq (hD : Dict) (hBd : BdetLaw) (χ : Chr F E) (hg : (adCM σ χ).Good) (ε : ℤˣ) (b : GL (Fin n ⊕ Fin n) E)
    (hb : b.1ᵀ * dbl Y.J * b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) (t₀ : GL (Fin n) E)
    (ht₀ : b.1.toCols₁ = diagCols (Fin n) * t₀.1) (K : Subgroup (G2 σ Y)) (hK : ∀ x, x ∈ K ↔ frameEquiv χ ε b hb x ∈ (adCM σ χ).uK ε (Fin n))
    (a : G2 σ Y → ℝ) (ha : IsHgt K a) (x : G2 σ Y) :
    0 < a x ∧ (adCM σ χ).uH ε (Set.univ : Set (Fin n)) (frameEquiv χ ε b hb x) = Real.log (a x) := by
  obtain ⟨p, t, hp, k, hk, rfl⟩ := ha.iwa x
  rw [ha.val p t hp k hk]
  have hpos : (0 : ℝ) < (GlobalTheory.Doubling.absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) := by
    have : GlobalTheory.Doubling.absE F E (Matrix.GeneralLinearGroup.det t) ≠ 0 := by
      intro h0
      have h1 := map_mul (GlobalTheory.Doubling.absE F E) (Matrix.GeneralLinearGroup.det t) (Matrix.GeneralLinearGroup.det t)⁻¹
      rw [mul_inv_cancel, map_one, h0, zero_mul] at h1
      exact one_ne_zero h1
    exact_mod_cast pos_iff_ne_zero.2 this
  refine ⟨hpos, ?_⟩
  obtain ⟨-, hmul, -, -, hzero, -⟩ := hBd E (AE F E) (adCM σ χ) hg.toGoodL (Fin n ⊕ Fin n) (Sum.inl '' (Set.univ : Set (Fin n)))
  have hQ : frameEquiv χ ε b hb p ∈ (adCM σ χ).uQ ε (Set.univ : Set (Fin n)) :=
    (GlobalTheory.T.parabolic_iff_frame_parabolic F E σ n Y χ ε b hb t₀ ht₀ p).1 ⟨t, hp⟩
  rw [map_mul]
  have h1 : (adCM σ χ).uH ε (Set.univ : Set (Fin n)) (frameEquiv χ ε b hb p * frameEquiv χ ε b hb k) =
      (adCM σ χ).lg (bdet (Sum.inl '' (Set.univ : Set (Fin n))) (frameEquiv χ ε b hb p).1) := by
    refine ext_mul _ _ (fun q : (adCM σ χ).U ε (Fin n) => (adCM σ χ).lg (bdet (Sum.inl '' (Set.univ : Set (Fin n))) q.1)) ?_ ?_ hQ ((hK k).1 hk)
    · intro q₁ h₁ q₂ h₂
      show (adCM σ χ).lg (bdet _ (q₁.1 * q₂.1)) = _
      rw [hmul q₁.1 h₁ q₂.1 h₂, hg.lgmul]
    · intro r h₁ h₂
      exact hzero _ h₁ h₂
  rw [h1, GlobalTheory.T.block_det_parabolic_frame F E σ n Y χ ε b hb t₀ ht₀ p t hp]
  have h2 := (hD F E).2.2.2.2 (Matrix.GeneralLinearGroup.det t)
  show Real.log ((GroundTheory.Global.IdeleGroup.ideleModule E _ : ℝ)) = _
  rw [h2]
theorem eis_from_U (hSec : SecLaw) (hWL : WallLaw) {U : Type} [Group U] [TopologicalSpace U] [IsTopologicalGroup U] [T2Space U]
    [LocallyCompactSpace U] (Φ : G2 σ Y ≃* U) (hΦ : Continuous Φ)
    (Γ' K' P' : Subgroup U) (c' : U → ℂ) (η : U → ℝ) (hKc : IsCompact (K' : Set U)) (hP : IsPar Γ' K' P' c') (hη : IsHt Γ' K' P' η)
    (hW : AllRep K' fun ρ => HasWall Γ' K' P' P' c' η η (fun g => (n : ℝ) * η g) ρ)
    (K : Subgroup (G2 σ Y)) (a : G2 σ Y → ℝ) (χ : Chr F E) (s₁ : ℂ) (f : G2 σ Y → ℂ) (hf : IsSec K χ s₁ f)
    (hΓ : ∀ x, x ∈ rat2 σ Y ↔ Φ x ∈ Γ') (hKK : ∀ x, x ∈ K ↔ Φ x ∈ K') (hPP : ∀ x, x ∈ par2 σ Y ↔ Φ x ∈ P')
    (hIP : ∀ x, (∃ t, IsPar x t) ↔ Φ x ∈ P') (hH : ∀ x, 0 < a x ∧ η (Φ x) = Real.log (a x))
    (hΦs : Continuous Φ.symm)
    (hval : ∀ p t, IsPar p t → c' (Φ p) = (χ (Matrix.GeneralLinearGroup.det t) : ℂ) ∧
      a p = (GlobalTheory.Doubling.absE F E (Matrix.GeneralLinearGroup.det t) : ℝ))
    (hGod : ∃ σ₀ : ℝ, ∀ σ' : ℝ, σ₀ < σ' → ∃ (C : ℝ) (N : ℕ), ∀ x : G2 σ Y,
        ∑' q : Cos (par2 σ Y) (rat2 σ Y), a ((Quotient.out q).1 * x) ^ σ' ≤ C * (ht2 x : ℝ) ^ N) :
    ∃ (A : ℂ → ℂ) (H : ℂ → modFun σ Y) (t : ℝ), Differentiable ℂ A ∧ (∃ z, A z ≠ 0) ∧
        (∀ μ, IsGrowForm μ → Differentiable ℂ (fun s => μ (H s))) ∧
        ∀ s : ℂ, t < s.re → ∀ x, HasSum (fun q => A s * eisTerm (flat a f s₁ s) x q) ((H s).1 x) := by
  have hβ : IsHt Γ' K' P' (fun g => (n : ℝ) * η g) :=
    ⟨fun p hp g => by rw [hη.left p hp g]; ring, fun g k hk => by rw [hη.right g k hk],
      fun γ h1 h2 => by rw [hη.rat γ h1 h2, mul_zero], continuous_const.mul hη.cont⟩
  set u : ℂ := s₁ + n / 2 with hu
  have hlaw : ∀ p ∈ P', ∀ x, f (Φ.symm (p * x)) = c' p * Complex.exp (u * η p) * f (Φ.symm x) := by
    intro p hp x
    obtain ⟨t, ht⟩ := (hIP (Φ.symm p)).2 (by simpa using hp)
    obtain ⟨h1, h2⟩ := hval _ t ht
    have h3 := hH (Φ.symm p)
    rw [MulEquiv.apply_symm_apply] at h1 h3
    rw [map_mul, hf.law _ t _ ht, h1, h3.2, ← h2]
    have hne : ((a (Φ.symm p) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h3.1.ne'
    rw [Complex.cpow_def_of_ne_zero hne, Complex.ofReal_log h3.1.le, mul_comm u]
  obtain ⟨R, D, H, hD, hDne, hHd, hHc, hcv, hcv', hbd, hsum⟩ := scalar_wall hSec hWL Γ' K' P' c' η _ hKc hP hη hβ hW
    (fun y => f (Φ.symm y)) u (hf.cont.comp hΦs) hlaw (fin_pull Φ K K' hKK f hf.fin)
  have hposeq : ∀ τ : ℝ, (Conv Γ' P' fun g => τ * η g) → ∀ x, pos Γ' P' (fun g => τ * η g) (Φ x) =
      ∑' q : Cos (par2 σ Y) (rat2 σ Y), a ((Quotient.out q).1 * x) ^ τ := by
    intro τ hc x
    have h1 := hasSum_cos Φ (rat2 σ Y) (par2 σ Y) Γ' P' hΓ hPP (fun y => Real.exp (τ * η y))
      (fun γ h1 h2 y => by rw [hη.left γ h2 y, hη.rat γ h1 h2, zero_add]) (Φ x) _ (hc (Φ x)).hasSum
    have e : (fun q : Cos (par2 σ Y) (rat2 σ Y) => Real.exp (τ * η (Φ (rep q) * Φ x))) =
        fun q => a ((Quotient.out q).1 * x) ^ τ := by
      funext q
      rw [← map_mul, (hH _).2, Real.rpow_def_of_pos (hH _).1, mul_comm]
      rfl
    rw [e] at h1
    exact h1.tsum_eq.symm
  have hgrow : ∀ b₀ a₀ : ℝ, ∃ (C : ℝ) (N : ℕ), ∀ z : ℂ, b₀ ≤ z.re → z.re ≤ a₀ → ∀ x, ‖H z (Φ x)‖ ≤ C * (ht2 x : ℝ) ^ N := by
    obtain ⟨σ₀, hσ⟩ := hGod
    intro b₀ a₀
    obtain ⟨A₁, hA₁, hA₂, hA₃⟩ : ∃ A₁ : ℝ, a₀ ≤ A₁ ∧ R < A₁ ∧ σ₀ < A₁ :=
      ⟨max a₀ (max (R + 1) (σ₀ + 1)), le_max_left _ _, lt_of_lt_of_le (by linarith) ((le_max_left _ _).trans (le_max_right _ _)),
        lt_of_lt_of_le (by linarith) ((le_max_right _ _).trans (le_max_right _ _))⟩
    obtain ⟨B₁, hB₁, hB₂, hB₃⟩ : ∃ B₁ : ℝ, B₁ ≤ b₀ ∧ B₁ < -R ∧ σ₀ < n - B₁ :=
      ⟨min b₀ (min (-R - 1) (n - σ₀ - 1)), min_le_left _ _, lt_of_le_of_lt ((min_le_right _ _).trans (min_le_left _ _)) (by linarith),
        by have := (min_le_right b₀ _).trans (min_le_right (-R - 1) ((n : ℝ) - σ₀ - 1)); linarith⟩
    obtain ⟨C₁, N₁, h₁⟩ := hσ A₁ hA₃
    obtain ⟨C₂, N₂, h₂⟩ := hσ _ hB₃
    obtain ⟨M, hM⟩ := hbd A₁ B₁ hA₂ hB₂
    refine ⟨|M| * (|C₁| + |C₂|), N₁ + N₂, fun z hz₁ hz₂ x => ?_⟩
    have hone : (1 : ℝ) ≤ (ht2 x : ℝ) := by exact_mod_cast GlobalTheory.AdelicU.one_le_heightGL F x.1
    have e₂ : (fun g => (n : ℝ) * η g - B₁ * η g) = fun g => ((n : ℝ) - B₁) * η g := by
      funext g; ring
    have c₂ : Conv Γ' P' fun g => ((n : ℝ) - B₁) * η g := by rw [← e₂]; exact hcv' B₁ hB₂
    have p₁ := hposeq A₁ (hcv A₁ hA₂) x
    have p₂ := hposeq _ c₂ x
    have h₃ := hM z (hB₁.trans hz₁) (hz₂.trans hA₁) (Φ x)
    rw [e₂, p₁, p₂] at h₃
    have q₁ := h₁ x
    have q₂ := h₂ x
    have w₁ : (ht2 x : ℝ) ^ N₁ ≤ (ht2 x : ℝ) ^ (N₁ + N₂) := pow_le_pow_right₀ hone (by omega)
    have w₂ : (ht2 x : ℝ) ^ N₂ ≤ (ht2 x : ℝ) ^ (N₁ + N₂) := pow_le_pow_right₀ hone (by omega)
    have w₀ : (0 : ℝ) ≤ (ht2 x : ℝ) ^ N₁ := by positivity
    have w₀' : (0 : ℝ) ≤ (ht2 x : ℝ) ^ N₂ := by positivity
    have r₁ : C₁ * (ht2 x : ℝ) ^ N₁ ≤ |C₁| * (ht2 x : ℝ) ^ (N₁ + N₂) :=
      (mul_le_mul_of_nonneg_right (le_abs_self _) w₀).trans (mul_le_mul_of_nonneg_left w₁ (abs_nonneg _))
    have r₂ : C₂ * (ht2 x : ℝ) ^ N₂ ≤ |C₂| * (ht2 x : ℝ) ^ (N₁ + N₂) :=
      (mul_le_mul_of_nonneg_right (le_abs_self _) w₀').trans (mul_le_mul_of_nonneg_left w₂ (abs_nonneg _))
    have s₀ : 0 ≤ ∑' q : Cos (par2 σ Y) (rat2 σ Y), a ((Quotient.out q).1 * x) ^ A₁ +
        ∑' q : Cos (par2 σ Y) (rat2 σ Y), a ((Quotient.out q).1 * x) ^ ((n : ℝ) - B₁) :=
      add_nonneg (tsum_nonneg fun q => (Real.rpow_pos_of_pos (hH _).1 _).le) (tsum_nonneg fun q => (Real.rpow_pos_of_pos (hH _).1 _).le)
    calc ‖H z (Φ x)‖ ≤ M * _ := h₃
      _ ≤ |M| * _ := mul_le_mul_of_nonneg_right (le_abs_self M) s₀
      _ ≤ |M| * ((|C₁| + |C₂|) * (ht2 x : ℝ) ^ (N₁ + N₂)) := mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
      _ = _ := by ring
  have hcontH : Continuous fun y : ℂ × G2 σ Y => H (y.1 + n / 2) (Φ y.2) :=
    hHc.comp ((continuous_fst.add continuous_const).prodMk (hΦ.comp continuous_snd))
  have hmem : ∀ s : ℂ, (fun x => H (s + n / 2) (Φ x)) ∈ modFun σ Y := by
    intro s
    obtain ⟨C, N, h⟩ := hgrow (s + n / 2).re (s + n / 2).re
    exact GlobalTheory.CompanionTheory.WeakHolo.mem_modFun (hcontH.comp (Continuous.prodMk_right s)) fun x => h _ le_rfl le_rfl x
  let V : ℂ → modFun σ Y := fun s => ⟨fun x => H (s + n / 2) (Φ x), hmem s⟩
  refine ⟨fun s => D (s + n / 2), V, R - n / 2, hD.comp (differentiable_id.add_const _), ?_, ?_, ?_⟩
  · obtain ⟨z, hz⟩ := hDne
    exact ⟨z - n / 2, by simpa using hz⟩
  · intro μ hμ
    have hh := GlobalTheory.CompanionTheory.WeakHolo.wholo_growForms V isOpen_univ
      (fun x => ((hHd (Φ x)).comp (differentiable_id.add_const _)).differentiableOn)
      hcontH.continuousOn ?_ μ hμ
    · exact differentiableOn_univ.1 hh
    · intro Q _ hQc
      rcases Q.eq_empty_or_nonempty with rfl | hne
      · exact ⟨0, 0, by simp⟩
      obtain ⟨z₁, -, hmin⟩ := hQc.exists_isMinOn hne Complex.continuous_re.continuousOn
      obtain ⟨z₂, -, hmax⟩ := hQc.exists_isMaxOn hne Complex.continuous_re.continuousOn
      obtain ⟨C, N, h⟩ := hgrow (z₁.re + n / 2) (z₂.re + n / 2)
      refine ⟨C, N, fun s hs x => h _ ?_ ?_ x⟩
      · have := hmin hs
        simp only [Complex.add_re, Complex.div_ofNat_re, Complex.natCast_re]
        simpa using this
      · have := hmax hs
        simp only [Complex.add_re, Complex.div_ofNat_re, Complex.natCast_re]
        simpa using this
  · intro s hs x
    have hz : R < (s + n / 2).re := by
      simp only [Complex.add_re, Complex.div_ofNat_re, Complex.natCast_re]
      linarith
    have h1 := hasSum_cos Φ (rat2 σ Y) (par2 σ Y) Γ' P' hΓ hPP
      (fun y => D (s + n / 2) * (Complex.exp ((s + n / 2 - u) * η y) * f (Φ.symm y)))
      (fun γ h1 h2 y => by
        rw [hlaw γ h2 y, hη.left γ h2 y, hη.rat γ h1 h2, hP.ch.rat γ h1 h2, zero_add]
        simp) (Φ x) _ (hsum _ hz (Φ x))
    have e : (fun q : Cos (par2 σ Y) (rat2 σ Y) => D (s + n / 2) * (Complex.exp ((s + n / 2 - u) * η (Φ (rep q) * Φ x)) *
        f (Φ.symm (Φ (rep q) * Φ x)))) = fun q => D (s + n / 2) * eisTerm (flat a f s₁ s) x q := by
      funext q
      rw [← map_mul, MulEquiv.symm_apply_apply, (hH _).2]
      have h := (hH (rep q * x)).1
      have hne : ((a (rep q * x) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h.ne'
      have e' : eisTerm (flat a f s₁ s) x q = ((a (rep q * x) : ℝ) : ℂ) ^ (s - s₁) * f (rep q * x) := rfl
      rw [e', Complex.cpow_def_of_ne_zero hne, Complex.ofReal_log h.le, hu]
      congr 3
      ring
    rw [e] at h1
    exact h1

theorem siegelMult_of : SecLaw → WallLaw → Dict → DictInf → CMGood → GrpTop → BdetLaw → ExtLaw → ParLaw → SgAll →
    SiegelEisensteinSeries.BRoad.SiegelMult := by
  intro hSec hWL hD hDI hCM hGT hBd _ hPar hSg
  intro F E _ _ _ _ _ σ B n Y r s hB hn hY χ hχ c hres b K a hb hK ha s₁ f hf
  obtain ⟨⟨ε, hε⟩, t₀, ht₀⟩ := hb
  have hb' : IsFrame2 σ Y b := ⟨⟨ε, hε⟩, t₀, ht₀⟩
  have hcm := hB.cm
  have hunr := hB.unram
  have hgood : (adCM σ χ).Good := hCM F E σ χ c hcm hunr hχ hres
  obtain ⟨-, -, -, ht2', hlc', hsc', hKc⟩ := hGT E (AE F E) (adCM σ χ) hgood (Fin n) ε
  let Φ := frameEquiv (Y := Y) χ ε b hε
  have hΓ : ∀ x, x ∈ rat2 σ Y ↔ Φ x ∈ (adCM σ χ).uΓ ε (Fin n) := rat_iff χ ε b hε
  have hKK : ∀ x, x ∈ K ↔ Φ x ∈ (adCM σ χ).uK ε (Fin n) := fun x => GlobalTheory.T.standard_compact_frame_equiv F E σ n Y hD hDI hcm χ ε b hε B K hK x
  have hIP : ∀ x, (∃ t, IsPar x t) ↔ Φ x ∈ (adCM σ χ).uQ ε (Set.univ : Set (Fin n)) := GlobalTheory.T.parabolic_iff_frame_parabolic F E σ n Y χ ε b hε t₀ ht₀
  have hPP : ∀ x, x ∈ par2 σ Y ↔ Φ x ∈ (adCM σ χ).uQ ε (Set.univ : Set (Fin n)) := by
    intro x
    constructor
    · intro hx
      have : par2 σ Y ≤ ((adCM σ χ).uQ ε (Set.univ : Set (Fin n))).comap Φ.toMonoidHom :=
        (Subgroup.closure_le _).2 fun p hp => (hIP p).1 hp
      exact this hx
    · intro hx
      exact Subgroup.subset_closure ((hIP x).2 hx)
  have hH := fun x => uH_eq hD hBd χ hgood ε b hε t₀ ht₀ K hKK a ha x
  have hiwa : Iwa ((adCM σ χ).uQ ε (Set.univ : Set (Fin n))) ((adCM σ χ).uK ε (Fin n)) := by
    intro y
    obtain ⟨p, t, hp, k, hk, e⟩ := ha.iwa (Φ.symm y)
    refine ⟨Φ p, (hIP p).1 ⟨t, hp⟩, Φ k, (hKK k).1 hk, ?_⟩
    rw [← map_mul, ← e, MulEquiv.apply_symm_apply]
  obtain ⟨-, hparU⟩ := hPar E (AE F E) (adCM σ χ) hgood (Fin n) ε (Set.univ : Set (Fin n))
  obtain ⟨hIP', hIH, -⟩ := hparU (by rwa [inf_idem])
  rw [inf_idem] at hIP'
  haveI := ht2'
  haveI := hlc'
  have hW := hSg F E σ χ c hcm hunr hχ hres ε (Fin n) (by simpa using hn) hiwa
  obtain ⟨σ₀, hσ₀⟩ := GlobalTheory.CompanionTheory.GodementH.godement_sum F E σ B n Y r s hB hn hY b K a hb' hK ha
  refine eis_from_U hSec hWL Φ (continuous_frameEquiv χ ε b hε) _ _ _ ((adCM σ χ).uC ε (Fin n))
    ((adCM σ χ).uH ε (Set.univ : Set (Fin n))) hKc hIP' hIH ?_ K a χ s₁ f hf hΓ hKK hPP hIP hH
    (continuous_frameEquiv_symm χ ε b hε) ?_ ⟨σ₀, fun σ' h => ?_⟩
  · simpa using hW
  · intro p t hp
    refine ⟨?_, ?_⟩
    · show (((adCM σ χ).χ (bdet (Sum.inl '' (Set.univ : Set (Fin n))) (frameEquiv χ ε b hε p).1) : Circle) : ℂ) = _
      rw [GlobalTheory.T.block_det_parabolic_frame F E σ n Y χ ε b hε t₀ ht₀ p t hp]
      rfl
    · have := ha.val p t hp 1 (one_mem _)
      rwa [mul_one] at this
  · obtain ⟨C, N, h⟩ := hσ₀ σ' h
    exact ⟨C, N, fun x => (h x).2⟩

end GlobalTheory.CompanionTheory.SiegelFrame
