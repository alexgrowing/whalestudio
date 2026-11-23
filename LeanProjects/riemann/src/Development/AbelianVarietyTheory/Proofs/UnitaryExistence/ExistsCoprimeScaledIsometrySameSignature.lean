import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsScaledIsometry
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasseNormTheoremQuadraticExtension
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FiniteNotIsUnitOneAddSmul
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.UnitaryGroupWeakApproximationAtPrimes

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open scoped Matrix

namespace GlobalTheory.LocalIsomAt

theorem exists_unitary_congr {K R : Type} [Field K] [CharZero K] [CommRing R] (ι : K →+* R) (c : K →+* K)
    (σ : R →+* R) (hσι : ∀ x, σ (ι x) = ι (c x)) (hc : ∀ x, c (c x) = x) (hσ : ∀ x, σ (σ x) = x) {n : ℕ}
    (G : Matrix (Fin n) (Fin n) K) (hG : (G.map c)ᵀ = G) (hdet : G.det ≠ 0) (O : Subring R)
    (hO : ∀ z ∈ O, σ z ∈ O) (happ : ∀ z : R, ∃ x : K, ι x - z ∈ O)
    (hb : ∀ M : Matrix (Fin n) (Fin n) R, ∃ d : ℕ, 0 < d ∧ d • M ∈ (O.matrix : Subring (Matrix (Fin n) (Fin n) R)))
    (N : ℕ) (hN : 0 < N) (hJ : ∀ z ∈ O, ∃ w ∈ O, (1 + N • z) * w = 1)
    (g h : Matrix (Fin n) (Fin n) R) (hg : h * g = 1) (hh : hᵀ * G.map ι * h.map σ = G.map ι)
    (lam : K) (hlam : lam * c lam = 1) (hu : IsUnit (1 + ι lam • h)) (D : ℕ) (hD : 0 < D) :
    ∃ γ : Matrix (Fin n) (Fin n) K, γᵀ * G * γ.map c = G ∧
      ∃ X ∈ (O.matrix : Subring (Matrix (Fin n) (Fin n) R)), γ.map ι * g - 1 = D • X := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact ⟨1, by simp, 0, zero_mem _, Subsingleton.elim _ _⟩
  have := GlobalTheory.UnRep.WeakApprox.core ι c σ hσι hc hσ G hG hdet two_ne_zero O.matrix hb 1 (one_mul 1) (map_one σ)
    one_ne_zero (fun X hX => by rwa [one_smul]) N hN
    (fun X hX => by
      rw [one_smul]
      exact GlobalTheory.GenusSelfDual.exists_inv_one_add_smul O hJ X hX)
    (fun M D' hD' => by
      obtain ⟨d1, hd1, h1⟩ := hb (G.map ι)
      obtain ⟨d2, hd2, h2⟩ := hb (G.map ι)⁻¹
      have hm : ((D' * (d1 * d2) : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 (by positivity)
      choose x hx using fun a b => happ (ι ((D' * (d1 * d2) : ℕ) : K)⁻¹ * M a b)
      set Y : Matrix (Fin n) (Fin n) R :=
        Matrix.of fun a b => -(ι (x a b) - ι ((D' * (d1 * d2) : ℕ) : K)⁻¹ * M a b) with hY
      have hYO : Y ∈ (O.matrix : Subring (Matrix (Fin n) (Fin n) R)) := fun a b => O.neg_mem (hx a b)
      have hYσ : Y.map σ ∈ (O.matrix : Subring (Matrix (Fin n) (Fin n) R)) := fun a b => hO _ (hYO a b)
      have h3 := mul_mem (mul_mem h1 hYσ) h2
      refine ⟨(D' * (d1 * d2)) • Matrix.of x,
        (d1 * d2) • Y - ((d1 • G.map ι) * Y.map σ * (d2 • (G.map ι)⁻¹))ᵀ,
        sub_mem (nsmul_mem hYO _) fun a b => h3 b a, ?_⟩
      have e : M - ((D' * (d1 * d2)) • Matrix.of x).map ι = (D' * (d1 * d2)) • Y := by
        ext a b
        have e1 : ((D' * (d1 * d2) : ℕ) : R) * ι ((D' * (d1 * d2) : ℕ) : K)⁻¹ = 1 := by
          rw [← map_natCast ι, ← map_mul, mul_inv_cancel₀ hm, map_one]
        simp only [hY, Matrix.sub_apply, Matrix.map_apply, Matrix.smul_apply, Matrix.of_apply, map_nsmul]
        simp only [nsmul_eq_mul]
        linear_combination (-M a b) * e1
      have e2 := (map_sub (GlobalTheory.UnRep.WeakApprox.skewPart σ (G.map ι)) M
        (((D' * (d1 * d2)) • Matrix.of x).map ι)).symm
      rw [e, map_nsmul] at e2
      refine e2.trans ?_
      rw [mul_smul]
      congr 1
      change (d1 * d2) • (Y - (G.map ι * Y.map σ * (G.map ι)⁻¹)ᵀ) = _
      simp only [smul_sub, smul_mul_assoc, mul_smul_comm, Matrix.transpose_smul, smul_smul, mul_comm d2 d1])
    g h hg hh lam hlam (by simpa [← Matrix.isUnit_iff_isUnit_det] using hu) D hD
  simpa only [one_smul] using this

theorem exists_unitary_congr_pi {K T : Type} [Field K] [CharZero K] {A : T → Type} [∀ i, CommRing (A i)]
    (φ : ∀ i, K →+* A i) (c : K →+* K) (τ : ∀ i, A i →+* A i) (hτφ : ∀ i x, τ i (φ i x) = φ i (c x))
    (hc : ∀ x, c (c x) = x) (hτ : ∀ i x, τ i (τ i x) = x) {n : ℕ}
    (G : Matrix (Fin n) (Fin n) K) (hG : (G.map c)ᵀ = G) (hdet : G.det ≠ 0) (B : ∀ i, Subring (A i))
    (hB : ∀ i, ∀ z ∈ B i, τ i z ∈ B i) (happ : ∀ z : ∀ i, A i, ∃ x : K, ∀ i, φ i x - z i ∈ B i)
    (hden : ∀ x : K, ∃ d : ℕ, 0 < d ∧ ∀ i, d • φ i x ∈ B i)
    (N : ℕ) (hN : 0 < N) (hJ : ∀ i, ∀ z ∈ B i, ∃ w ∈ B i, (1 + N • z) * w = 1)
    (u P : ∀ i, GL (Fin n) (A i)) (hu : ∀ i, (u i).1ᵀ * G.map (φ i) * (u i).1.map (τ i) = G.map (φ i))
    (lam : K) (hlam : lam * c lam = 1) (hlu : ∀ i, IsUnit (1 + φ i lam • (u i).1)) :
    ∃ γ : Matrix (Fin n) (Fin n) K, γᵀ * G * γ.map c = G ∧
      ∀ i a b, (((P i)⁻¹).1 * (γ.map (φ i) * ((u i)⁻¹).1) * (P i).1) a b ∈ B i := by
  let R : Type := ∀ i, A i
  let ι : K →+* R := Pi.ringHom φ
  let σ : R →+* R := Pi.ringHom fun v => (τ v).comp (Pi.evalRingHom _ v)
  let O : Subring R := ⨅ v, (B v).comap (Pi.evalRingHom _ v)
  have hOm : ∀ z : R, z ∈ O ↔ ∀ v, z v ∈ B v := fun z => Subring.mem_iInf
  let ev : ∀ v, Matrix (Fin n) (Fin n) R →+* Matrix (Fin n) (Fin n) (A v) :=
    fun v => (Pi.evalRingHom _ v).mapMatrix
  have hext : ∀ X Y : Matrix (Fin n) (Fin n) R, (∀ v, ev v X = ev v Y) → X = Y := fun X Y h =>
    Matrix.ext fun i j => funext fun v => congrFun (congrFun (h v) i) j
  let mk : (∀ v, Matrix (Fin n) (Fin n) (A v)) → Matrix (Fin n) (Fin n) R :=
    fun X => Matrix.of fun i j v => X v i j
  have hmk : ∀ X v, ev v (mk X) = X v := fun X v => rfl
  have happ' : ∀ z : R, ∃ x : K, ι x - z ∈ O := fun z => by
    obtain ⟨x, hx⟩ := happ z
    exact ⟨x, (hOm _).2 hx⟩
  have hden' : ∀ z : R, ∃ d : ℕ, 0 < d ∧ d • z ∈ O := fun z => by
    obtain ⟨x, hx⟩ := happ' z
    obtain ⟨k, hk, hs⟩ := hden x
    refine ⟨k, hk, ?_⟩
    rw [← sub_sub_cancel (ι x) z, smul_sub]
    exact sub_mem ((hOm _).2 hs) (nsmul_mem hx k)
  have hb : ∀ M : Matrix (Fin n) (Fin n) R,
      ∃ d : ℕ, 0 < d ∧ d • M ∈ (O.matrix : Subring (Matrix (Fin n) (Fin n) R)) := fun M => by
    choose d hd hdM using fun ab : Fin n × Fin n => hden' (M ab.1 ab.2)
    refine ⟨∏ ab, d ab, Finset.prod_pos fun ab _ => hd ab, fun a b => ?_⟩
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem d (Finset.mem_univ (a, b))
    rw [hc, mul_comm, mul_smul]
    exact nsmul_mem (hdM (a, b)) c
  choose w hw using fun v => (hlu v).exists_right_inv
  obtain ⟨d1, hd1, h1⟩ := hb (mk fun v => ((P v)⁻¹).1)
  obtain ⟨d2, hd2, h2⟩ := hb (mk fun v => (P v).1)
  obtain ⟨γ, hγ, X, hX, hγX⟩ := exists_unitary_congr ι c σ (fun x => funext fun v => hτφ v x)
    hc (fun x => funext fun v => hτ v _) G hG hdet O (fun z hz => (hOm _).2 fun v => hB v _ ((hOm _).1 hz v))
    happ' hb N hN (fun z hz => by
      choose y hy hy1 using fun v => hJ v (z v) ((hOm _).1 hz v)
      exact ⟨y, (hOm _).2 hy, funext hy1⟩)
    (mk fun v => ((u v)⁻¹).1) (mk fun v => (u v).1)
    (hext _ _ fun v => by rw [map_mul, map_one, hmk, hmk, Units.mul_inv])
    (hext _ _ fun v => by rw [map_mul, map_mul]; exact hu v) lam hlam
    ((Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_right_inverse (B := mk w) (hext _ _ fun v => by
      rw [map_mul, map_add, map_one]; exact hw v)))
    (d1 * d2) (by positivity)
  refine ⟨γ, hγ, fun v => ?_⟩
  have e1 : γ.map (φ v) * ((u v)⁻¹).1 - 1 = (d1 * d2) • ev v X := by
    have := congrArg (ev v) hγX
    rw [map_sub, map_mul, map_one, map_nsmul] at this
    exact this
  have h3 : ∀ i j, (ev v ((d1 • mk fun v => ((P v)⁻¹).1) * X * (d2 • mk fun v => (P v).1) + 1)) i j ∈ B v := fun i j =>
    (hOm _).1 (add_mem (mul_mem (mul_mem h1 hX) h2) (one_mem _) i j) v
  rw [map_add, map_one, map_mul, map_mul, map_nsmul, map_nsmul, hmk, hmk] at h3
  rw [sub_eq_iff_eq_add.1 e1, mul_add, add_mul, mul_one, Units.inv_mul]
  simpa only [smul_mul_assoc, mul_smul_comm, smul_smul, mul_comm d2 d1] using h3

open ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.SelfDualGenus GlobalTheory.GenusSelfDual

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem infinite_norm_one (E : Type) [Field E] [NumberField E] [IsCMField E] :
    {x : E | x * cc x = 1}.Infinite := by
  obtain ⟨θ, h0, hθ⟩ := exists_imaginary_integer E
  have hc : ∀ k : ℤ, IsCMField.complexConj E (1 + (k * θ : E)) = 1 - (k * θ) := fun k => by
    rw [map_add, map_one, map_mul, map_intCast, show IsCMField.complexConj E θ = -θ from hθ]
    ring
  have hne : ∀ k : ℤ, 1 + (k * θ : E) ≠ 0 := fun k hk => by
    have := hc k
    rw [hk, map_zero] at this
    exact two_ne_zero (α := E) (by linear_combination hk - this)
  have hne' : ∀ k : ℤ, 1 - (k * θ : E) ≠ 0 := fun k => by
    rw [← hc]; exact (_root_.map_ne_zero _).2 (hne k)
  refine Set.infinite_of_injective_forall_mem (f := fun k : ℤ => (1 - (k * θ : E)) / (1 + k * θ))
    (fun a b hab => ?_) fun k => ?_
  · rw [div_eq_div_iff (hne a) (hne b)] at hab
    have : (2 * θ : E) * (a - b) = 0 := by linear_combination -hab
    exact_mod_cast sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left (mul_ne_zero two_ne_zero h0))
  · have := hc (-k)
    simp only [Int.cast_neg, neg_mul, ← sub_eq_add_neg, sub_neg_eq_add] at this
    simp only [Set.mem_setOf_eq, cc, map_div₀, hc, this]
    rw [div_mul_div_comm, mul_comm, div_self (mul_ne_zero (hne k) (hne' k))]

theorem exists_unitary_mapsTo {G : Matrix (Fin n) (Fin n) E} (hG : ∀ a b, cc (G a b) = G b a) (hd : G.det ≠ 0)
    {L L' : Submodule (𝓞 E) (Fin n → E)} (hL' : ReciprocityTheory.MultiplicativeHeights.IsLattice L') {b : ℕ} (hb0 : 0 < b)
    (hloc : ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), ∃ γ, IsLocalIsometry v G L' G L γ) :
    ∃ γ : Matrix (Fin n) (Fin n) E, γᵀ * G * γ.map cc = G ∧ ∀ x ∈ L,
      ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), (b : 𝓞 (maximalRealSubfield E)) ∈ v.asIdeal →
        ∃ s ∉ v.asIdeal, algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) s • (γ *ᵥ x) ∈ L' := by
  classical
  have hT : {v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)) |
      (b : 𝓞 (maximalRealSubfield E)) ∈ v.asIdeal}.Finite := by
    simpa only [Ideal.dvd_span_singleton] using Ideal.finite_factors
      (I := Ideal.span {(b : 𝓞 (maximalRealSubfield E))}) (by simpa using hb0.ne')
  have hv : ∀ v : hT.toFinset, (b : 𝓞 (maximalRealSubfield E)) ∈ v.1.asIdeal := fun v => hT.mem_toFinset.1 v.2
  choose u hu huL using hloc
  choose P hP using fun v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)) => exists_frame v hL'
  obtain ⟨lam, hlam, hlu⟩ := (infinite_norm_one E).exists_notMem_finite
    (Set.finite_iUnion fun v : hT.toFinset =>
      haveI : IsArtinianRing (LocAlg v.1) :=
        IsArtinianRing.of_finite (v.1.adicCompletion (maximalRealSubfield E)) _
      finite_not_isUnit_one_add_smul (locEmb v.1) (u v.1).1)
  simp only [Set.mem_iUnion, Set.mem_setOf_eq, not_exists, not_not] at hlu
  obtain ⟨γ, hγ, hγX⟩ := exists_unitary_congr_pi (A := fun v : hT.toFinset => LocAlg v.1) (fun v => locEmb v.1)
    (IsCMField.complexConj E : E →+* E) (fun v => locConj v.1) (fun v => locConj_locEmb v.1)
    (IsCMField.complexConj_apply_apply E) (fun v => locConj_locConj v.1) G
    (Matrix.ext fun a b => hG b a) hd (fun v => (locOrder v.1).toSubring) (fun v z => locConj_mem v.1)
    (exists_sub_mem_locOrder _)
    (fun x => by
      obtain ⟨k, s, hk, hx⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).2
        (Algebra.IsAlgebraic.isAlgebraic x)).exists_nsmul_eq (𝓞 E)
      exact ⟨k, Nat.pos_of_ne_zero hk, fun v => by rw [← map_nsmul, hx]; exact locEmb_mem_locOrder v.1 s⟩)
    b hb0 (fun v => exists_inv_one_add v.1 (hv v)) (fun v => u v.1)
    (fun v => Matrix.GeneralLinearGroup.map (locEmb v.1) (P v.1)) (fun v => (hu v.1).symm) lam hlam hlu
  refine ⟨γ, hγ, fun x hx v hvb => ?_⟩
  refine (locEmb_mem_locLattice_iff v hL' _).1 ?_
  have hy := (huL v _).1 (Submodule.subset_span ⟨x, hx, rfl⟩)
  rw [mem_locLattice_iff_of_frame v (hP v)] at hy ⊢
  have h3 : ∀ a b, (((P v)⁻¹).1.map (locEmb v) * (γ.map (locEmb v) * ((u v)⁻¹).1) * (P v).1.map (locEmb v)) a b ∈
      locOrder v := hγX ⟨v, hT.mem_toFinset.2 hvb⟩
  have h4 := mulVec_mem_locOrder v h3 hy
  rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, ← Matrix.map_mul, Units.mul_inv,
    Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one, Matrix.mulVec_mulVec, Matrix.mul_assoc,
    Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one, ← Matrix.mulVec_mulVec] at h4
  rwa [show (fun i => locEmb v ((γ *ᵥ x) i)) = γ.map (locEmb v) *ᵥ fun i => locEmb v (x i) from
    funext fun i => RingHom.map_mulVec (locEmb v) γ x i]

theorem exists_coprime_nsmul_mem {b : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) (x : Fin n → E)
    (h : ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), (b : 𝓞 (maximalRealSubfield E)) ∈ v.asIdeal →
      ∃ s ∉ v.asIdeal, algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) s • x ∈ L) :
    ∃ k : ℕ, k.Coprime b ∧ k • x ∈ L := by
  have hm : ∀ k : ℕ, k • x ∈ L ↔ addOrderOf (L.mkQ x) ∣ k := fun k => by
    rw [addOrderOf_dvd_iff_nsmul_eq_zero, ← map_nsmul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  refine ⟨_, Nat.coprime_of_dvd fun p hp hpk hpb => ?_, (hm _).2 dvd_rfl⟩
  obtain ⟨k, hk, hkx⟩ := exists_nsmul_mem hp L x fun v hv => h v (by
    obtain ⟨c, rfl⟩ := hpb
    rw [Nat.cast_mul]
    exact v.asIdeal.mul_mem_right _ hv)
  exact hk (hpk.trans ((hm k).1 hkx))

open ReciprocityTheory.ChartRestriction.G.Geo.Tor in

theorem perfect_range {H : Host E} (D : Datum H) {ξ : E} {G : Matrix (Fin n) (Fin n) E}
    (φ : D.La →ₗ[𝓞 E] (Fin n → E)) (hinj : Function.Injective φ)
    (hEF : ∀ x y, ((D.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * herm G (φ x) (φ y))) :
    (∀ x ∈ LinearMap.range φ, ∀ y ∈ LinearMap.range φ, ∃ k : ℤ, EFf (-ξ) G x y = k) ∧
      ∀ ψ : LinearMap.range φ →+ ℤ, ∃ x ∈ LinearMap.range φ, ∀ y : LinearMap.range φ, (ψ y : ℚ) = EFf (-ξ) G x y := by
  refine ⟨?_, fun ψ => ?_⟩
  · rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    exact ⟨D.EF x y, by rw [EFf, neg_neg, hEF]⟩
  · obtain ⟨x, hx⟩ := D.unimod.2 (ψ.comp φ.rangeRestrict.toAddMonoidHom).toIntLinearMap
    refine ⟨φ x, ⟨x, rfl⟩, ?_⟩
    rintro ⟨_, y, rfl⟩
    rw [EFf, neg_neg, ← hEF, hx]
    rfl

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor in

theorem exists_coprime_scaled_isometry : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E)
    (D D' : Datum H), D'.p = D.p → D'.q = D.q → ∀ b : ℕ, 0 < b → ∃ (k : ℕ) (f : D.La →ₗ[𝓞 E] D'.La),
      k.Coprime b ∧ ∀ x y, D'.EF (f x) (f y) = (k : ℤ) ^ 2 * D.EF x y := by
  intro E _ _ _ H D₁ D₂ hp hq b hb
  classical
  have hH := GlobalTheory.QNorm.hasseNormSt
  have hL := GlobalTheory.LocalQuad.landherrSt_of_hasseNormSt hH
  have hξ := GlobalTheory.OneSpace.cc_rt H
  obtain ⟨G, φ₂, hM₂⟩ := GlobalTheory.exists_herm_coord_of_datum E H D₂ (H.rt : E) hξ (GlobalTheory.OneSpace.rt_ne H) _ rfl
  obtain ⟨φ₁, hinj₁, hspan₁, -, -, hEF₁⟩ :=
    GlobalTheory.model_in_same_space hL hH E H D₂ D₁ _ (H.rt : E) G φ₂ hp.symm hq.symm hξ hM₂
  obtain ⟨hinj₂, hspan₂, hG, hd, hEF₂⟩ := hM₂
  have := D₁.fin
  have := D₂.fin
  have := H.unram
  have hL₁ : ReciprocityTheory.MultiplicativeHeights.IsLattice (LinearMap.range φ₁) := ⟨Submodule.fg_range φ₁, hspan₁⟩
  have hL₂ : ReciprocityTheory.MultiplicativeHeights.IsLattice (LinearMap.range φ₂) := ⟨Submodule.fg_range φ₂, hspan₂⟩
  obtain ⟨γ, hγ, hγL⟩ := exists_unitary_mapsTo hG hd hL₂ hb
    (GlobalTheory.selfDual_lattices_one_genus hG hG hd hd hL₂ hL₁ (Or.inr ⟨_, neg_ne_zero.2 (GlobalTheory.OneSpace.rt_ne H),
      (map_neg (IsCMField.complexConj E) _).trans (congrArg Neg.neg hξ),
      perfect_range D₂ φ₂ hinj₂ hEF₂, perfect_range D₁ φ₁ hinj₁ hEF₁⟩)).1
  let φ : D₁.La →ₗ[𝓞 E] (Fin (D₂.p + D₂.q) → E) := (Matrix.toLin' γ).restrictScalars (𝓞 E) ∘ₗ φ₁
  have hφ : ∀ x, φ x = γ *ᵥ φ₁ x := fun x => rfl
  choose m hm hmem using fun x => exists_coprime_nsmul_mem _ _ (hγL (φ₁ x) ⟨x, rfl⟩)
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := 𝓞 E) (M := D₁.La)
  obtain ⟨N, hN, hmem⟩ : ∃ N : ℕ, N.Coprime b ∧ ∀ x, (N : 𝓞 E) • φ x ∈ LinearMap.range φ₂ := by
    refine ⟨∏ x ∈ s, m x, Nat.Coprime.prod_left fun x _ => hm x, fun x => ?_⟩
    have hx : x ∈ Submodule.span (𝓞 E) (s : Set D₁.La) := by rw [hs]; trivial
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem m (Finset.mem_coe.1 hy)
      rw [hk, Nat.cast_mul, mul_comm, mul_smul, Nat.cast_smul_eq_nsmul _ (m y)]
      exact Submodule.smul_mem _ _ (hmem _)
    | zero => simp
    | add a b _ _ ha hb => rw [map_add, smul_add]; exact Submodule.add_mem _ ha hb
    | smul c a _ ha => rw [map_smul, smul_comm]; exact Submodule.smul_mem _ _ ha
  let g : D₁.La →ₗ[𝓞 E] LinearMap.range φ₂ := ((N : 𝓞 E) • φ).codRestrict _ hmem
  let f : D₁.La →ₗ[𝓞 E] D₂.La := (LinearEquiv.ofInjective φ₂ hinj₂).symm.toLinearMap ∘ₗ g
  have hf : ∀ x, φ₂ (f x) = (N : E) • (γ *ᵥ φ₁ x) := by
    intro x
    have h1 : φ₂ (f x) = (N : 𝓞 E) • φ x :=
      LinearEquiv.ofInjective_symm_apply φ₂ (h := hinj₂) (g x)
    rw [h1, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, hφ]
  refine ⟨N, f, hN, fun x y => ?_⟩
  have h2 := hEF₂ (f x) (f y)
  rw [hf, hf, GlobalTheory.HermModel.herm_smul_left, GlobalTheory.HermModel.herm_smul_right, herm_mulVec, hγ] at h2
  have hc : cc (N : E) = N := by simp [cc]
  have h3 : (H.rt : E) * ((N : E) * (herm G (φ₁ x) (φ₁ y) * cc (N : E))) =
      ((N : ℚ) ^ 2) • ((H.rt : E) * herm G (φ₁ x) (φ₁ y)) := by
    rw [hc, Algebra.smul_def]
    simp only [map_pow, map_natCast]
    ring
  rw [h3, map_smul, ← hEF₁, smul_eq_mul] at h2
  exact_mod_cast h2

end GlobalTheory.LocalIsomAt
