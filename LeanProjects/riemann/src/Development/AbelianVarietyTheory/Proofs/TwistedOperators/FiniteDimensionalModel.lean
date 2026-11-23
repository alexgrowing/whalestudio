import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OneParameterDifferentiable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ConjAtFixedIff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinCongMemLevEnv
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsOpenCongruenceIdelesAndRealFiniteParts
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LatHatOpenAndContinuous

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Lev Formalism.IndefR.Cx GlobalTheory.Chain
open NumberField Matrix
open scoped TensorProduct ContDiff Topology ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DefiniteEnd

theorem aniso_of_sig {n : ℕ} (G : Matrix (Fin n) (Fin n) ℂ) {p q : ℕ} (h : Formalism.UG.HasSignature G p q)
    (hpq : p = 0 ∨ q = 0) (x : Fin n → ℂ) (hx : star x ⬝ᵥ (G *ᵥ x) = 0) : x = 0 := by
  obtain ⟨hn, Q, hQ⟩ := Formalism.UG.P.sig_data G p q h
  have hJ : Formalism.UG.Jpq p q * Formalism.UG.Jpq p q = 1 := by
    simp [Formalism.UG.Jpq, Matrix.fromBlocks_multiply]
  have e : Fin n ≃ Fin p ⊕ Fin q := Fintype.equivOfCardEq (by simpa using hn)
  have h1 : (Formalism.UG.Jpq p q * Qᴴ * G) * Q = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Qᴴ, hQ, hJ]
  have h2 := (Matrix.mul_eq_one_comm_of_equiv e.symm).1 h1
  obtain ⟨y, rfl⟩ : ∃ y, x = Q *ᵥ y := ⟨(Formalism.UG.Jpq p q * Qᴴ * G) *ᵥ x, by rw [Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]⟩
  rw [Formalism.UG.P.sig_quad G Q hQ] at hx
  have key : ∀ {m : ℕ} (z : Fin m → ℂ), ∑ i, star (z i) * z i = 0 → ∀ i, z i = 0 := fun z hz i =>
    congrFun (dotProduct_star_self_eq_zero.1 hz) i
  have : y = 0 := by
    funext k
    rcases hpq with rfl | rfl
    · rcases k with k | k
      · exact k.elim0
      · exact key (fun j => y (Sum.inr j)) (by simpa using hx) k
    · rcases k with k | k
      · exact key (fun j => y (Sum.inl j)) (by simpa using hx) k
      · exact k.elim0
  rw [this, Matrix.mulVec_zero]

variable {D : D7}

theorem aniso {V : HSp D} (hs : V.SigOK) (hd : V.IsDefinite) (τ : D.host.E →+* ℂ) (x : Fin V.rank → ℂ)
    (hx : star x ⬝ᵥ (V.gram.map τ *ᵥ x) = 0) : x = 0 :=
  aniso_of_sig _ (hs τ) (by rcases hd τ with h | h <;> simp [h]) x hx

theorem isCuspFun_of_definite {V : HSp D} (hs : V.SigOK) (hd : V.IsDefinite) (φ : GA D V → ℂ) : IsCuspFun V φ := by
  intro r C ⟨hr, hli, h0⟩
  exfalso
  obtain ⟨τ⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
  have hτ : ∀ a, τ (star a) = starRingEnd ℂ (τ a) := D.sp.cm.cmUnram.2.1 τ
  have h1 := congrArg τ (congrFun (congrFun h0 ⟨0, hr⟩) ⟨0, hr⟩)
  have h2 := aniso hs hd τ (fun i => τ (C i ⟨0, hr⟩)) (by
    rw [Matrix.zero_apply, map_zero] at h1
    rw [← h1, Matrix.mul_assoc]
    simp only [Matrix.mul_apply, map_sum, map_mul, dotProduct, Matrix.mulVec, Matrix.map_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    exact (hτ _).symm)
  refine hli.ne_zero ⟨0, hr⟩ (funext fun i => ?_)
  exact τ.injective ((congrFun h2 i).trans (map_zero τ).symm)

theorem sign_eq {V : HSp D} (hs : V.SigOK) (hd : V.IsDefinite) {S : D.what₂.Tau → SPar} (M : DSModel V S)
    (τ : D.what₂.Tau) (a b : Fin V.rank) : M.ε τ a = M.ε τ b := by
  by_contra hab
  have hne : a ≠ b := fun h => hab (by rw [h])
  have hu := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  set y : Fin V.rank → ℂ := Pi.single a 1 + Pi.single b 1 with hy
  have hx : M.fr τ *ᵥ ((M.fr τ)⁻¹ *ᵥ y) = y := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]
  have h0 := aniso hs hd (tauE D τ) ((M.fr τ)⁻¹ *ᵥ y) (by
    have e : V.gram.map (tauE D τ) = (M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ := (M.fr_gram τ).symm
    rw [e, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hx, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec, hx, hy]
    simp only [star_add, add_dotProduct, ← Pi.single_star, star_one, single_dotProduct, Formalism.REAL.Jm,
      Matrix.mulVec_diagonal, Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hne, Pi.single_eq_of_ne hne.symm]
    cases h1 : M.ε τ a <;> cases h2 : M.ε τ b <;> simp_all)
  rw [h0, Matrix.mulVec_zero] at hx
  have := congrFun hx a
  simp [hy, Pi.single_eq_of_ne hne] at this

theorem finiteDimensional_model {V : HSp D} (hs : V.SigOK) (hd : V.IsDefinite) {S : D.what₂.Tau → SPar}
    (M : DSModel V S) (τ : D.what₂.Tau) : FiniteDimensional ℂ (M.H τ) := by
  obtain ⟨-, -, -, hirr, -, ⟨U, hfd, hst, -, ⟨v, hv, hv0, -⟩, -⟩, -⟩ := M.ds τ
  have hJ : ∃ c : ℂ, c ≠ 0 ∧ Formalism.REAL.Jm (M.ε τ) = c • (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ) := by
    rcases isEmpty_or_nonempty (Fin V.rank) with h | ⟨⟨a⟩⟩
    · exact ⟨1, one_ne_zero, Subsingleton.elim _ _⟩
    · refine ⟨if M.ε τ a then 1 else -1, by split_ifs <;> simp, ?_⟩
      rw [Matrix.smul_one_eq_diagonal, Formalism.REAL.Jm]
      congr 1
      funext b
      rw [sign_eq hs hd M τ a b]
  obtain ⟨c, hc, hJ⟩ := hJ
  have hU := hirr U U.closed_of_finiteDimensional fun g hg => hst g (by
    have hg' : gᴴ * Formalism.REAL.Jm (M.ε τ) * g = Formalism.REAL.Jm (M.ε τ) := hg
    refine ⟨Matrix.mem_unitaryGroup_iff'.2 ?_, by rw [hJ]; simp⟩
    rw [hJ, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul] at hg'
    exact smul_right_injective _ hc hg')
  rcases hU with rfl | rfl
  · exact absurd ((Submodule.mem_bot ℂ).1 hv) hv0
  · exact Submodule.topEquiv.finiteDimensional

theorem exists_int_of_entries {R : Type} [CommRing R] {n : ℕ} (S : Subring R) (x : GL (Fin n) R) (N : ℕ)
    (hx : ∀ i j, ∃ s ∈ S, x.1 i j - (1 : Matrix (Fin n) (Fin n) R) i j = N • s)
    (hx' : ∀ i j, ∃ s ∈ S, (x⁻¹).1 i j - (1 : Matrix (Fin n) (Fin n) R) i j = N • s) :
    ∃ y : GL (Fin n) S, Formalism.UG.bc S.subtype y = x ∧
      ∀ (k : Type) [CommRing k] (φ : S →+* k), (N : k) = 0 → Formalism.UG.bc φ y = 1 := by
  have key : ∀ m : Matrix (Fin n) (Fin n) R, (∀ i j, ∃ s ∈ S, m i j - (1 : Matrix (Fin n) (Fin n) R) i j = N • s) →
      ∀ z ∈ {z : Fin n → R | ∀ i, z i ∈ S}, ∃ y ∈ {z : Fin n → R | ∀ i, z i ∈ S}, m *ᵥ z - z = N • y := by
    intro m hm z hz
    choose s hs e using hm
    have e' : m - 1 = N • Matrix.of s := Matrix.ext e
    refine ⟨Matrix.of s *ᵥ z, fun i => show ∑ j, s i j * z j ∈ S from sum_mem fun j _ => mul_mem (hs i j) (hz j), ?_⟩
    rw [← Matrix.smul_mulVec, ← e', Matrix.sub_mulVec, Matrix.one_mulVec]
  obtain ⟨y, hy, h⟩ := GlobalTheory.PrincInLevel.exists_int S 1 x {z | ∀ i, z i ∈ S} N (fun z => by simp) (key _ hx) (key _ hx')
  exact ⟨y, by simpa using hy, h⟩

theorem swap_mem_int {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (y : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F ⊗[F] E)
    (hy : y ∈ GlobalTheory.AdLat.hat1 F (Set.range (algebraMap (𝓞 E) E))) :
    Algebra.TensorProduct.comm F _ E y ∈ Formalism.L2.Herm.intAf F E := by
  induction hy using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, _, ⟨x, rfl⟩, rfl⟩ := hz
    have h1 : (1 : E) ⊗ₜ[F] a ∈ Formalism.L2.Herm.intAf F E := Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩)
    have h2 : algebraMap (𝓞 E) E x ⊗ₜ[F] (1 : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) ∈ Formalism.L2.Herm.intAf F E :=
      Subring.subset_closure (Or.inl ⟨⟨_, x, rfl⟩, rfl⟩)
    have := mul_mem h1 h2
    rwa [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one] at this
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx

theorem eventually_conj {R R' : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [CommRing R'] {n : ℕ}
    (φ : R ≃+* R') (O : Set R) (hO : O ∈ 𝓝 (0 : R)) (β : GL (Fin n) R') :
    ∀ᶠ m in 𝓝 (1 : Matrix (Fin n) (Fin n) R), ∀ i j, ∃ z ∈ O,
      ((β⁻¹).1 * m.map φ * β.1) i j - (1 : Matrix (Fin n) (Fin n) R') i j = φ z := by
  refine Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ?_
  have e : ∀ m : Matrix (Fin n) (Fin n) R, ((β⁻¹).1 * m.map φ * β.1) i j - (1 : Matrix (Fin n) (Fin n) R') i j =
      φ ((((β⁻¹).1.map φ.symm * m * β.1.map φ.symm) i j) - (1 : Matrix (Fin n) (Fin n) R) i j) := fun m => by
    simp only [map_sub, Matrix.mul_apply, map_sum, map_mul, Matrix.map_apply, RingEquiv.apply_symm_apply,
      Matrix.one_apply, apply_ite φ, map_one, map_zero]
  have hc : Continuous fun m : Matrix (Fin n) (Fin n) R =>
      (((β⁻¹).1.map φ.symm * m * β.1.map φ.symm) i j) - (1 : Matrix (Fin n) (Fin n) R) i j :=
    (((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).matrix_elem i j).sub continuous_const
  have h0 : (((β⁻¹).1.map φ.symm * (1 : Matrix (Fin n) (Fin n) R) * β.1.map φ.symm) i j) - (1 : Matrix (Fin n) (Fin n) R) i j = 0 := by
    apply φ.injective
    rw [← e, Matrix.map_one _ (map_zero φ) (map_one φ), Matrix.mul_one, Units.inv_mul, sub_self, map_zero]
  exact Filter.mem_of_superset (hc.continuousAt.preimage_mem_nhds (x := 1) (h0.symm ▸ hO)) fun m hm => ⟨_, hm, e m⟩

theorem eventually_cong {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (β : GL (Fin n) (E ⊗[F] Af F)) (N : ℕ) (hN : 0 < N) :
    ∀ᶠ m in 𝓝 (1 : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)), ∀ i j, ∃ s ∈ Formalism.L2.Herm.intAf F E,
      ((β⁻¹).1 * m.map (Algebra.TensorProduct.comm F (Af F) E) * β.1) i j -
        (1 : Matrix (Fin n) (Fin n) (E ⊗[F] Af F)) i j = N • s := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsModuleTopology (Af F) (Af F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (Af F ⊗[F] E) := IsModuleTopology.isTopologicalRing (Af F) _
  have ho := (GlobalTheory.IdeleParts.isOpen_nsmul_adelicCompletion_integers F E N hN).mem_nhds (x := 0) ⟨0, zero_mem _, (smul_zero _).symm⟩
  refine (eventually_conj (Algebra.TensorProduct.comm F (Af F) E).toRingEquiv _ ho β).mono fun m hm i j => ?_
  obtain ⟨z, ⟨y, hy, rfl⟩, e⟩ := hm i j
  exact ⟨_, swap_mem_int y hy, e.trans (map_nsmul _ _ _)⟩

theorem isOpen_Kg (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (T : Finset (Pl D.host.E)) :
    IsOpen (((Kg D.sp.cm V.gram β T).comap (finE V) : Subgroup (GA D V)) : Set (GA D V)) := by
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  set N : ℕ := ∏ PP ∈ T, Ideal.absNorm PP.asIdeal with hN
  have hN0 : 0 < N := Finset.prod_pos fun PP _ => Nat.pos_of_ne_zero (by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact PP.ne_bot)
  have hNm : ∀ PP ∈ T, ((N : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := fun PP hP => by
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun PP : Pl D.host.E => Ideal.absNorm PP.asIdeal) hP
    rw [hN, hc, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.absNorm_mem _)
  let P : GA D V → Prop := fun k => ∀ i j, ∃ s ∈ Formalism.L2.Herm.intAf D.host.F D.host.E,
    (β⁻¹ * finE V k * β).1 i j - (1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) i j = N • s
  have hP : ∀ᶠ k in 𝓝 (1 : GA D V), P k := by
    have hc := (GlobalTheory.Member.continuous_finHom_val D V).tendsto 1
    rw [map_one, Units.val_one] at hc
    exact hc.eventually (eventually_cong β N hN0)
  have hP' : ∀ᶠ k in 𝓝 (1 : GA D V), P k⁻¹ := by
    have : Filter.Tendsto (fun k : GA D V => k⁻¹) (𝓝 1) (𝓝 1) := by
      simpa using (continuous_inv (G := GA D V)).tendsto 1
    exact this.eventually hP
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset (hP.and hP') ?_)
  rintro k ⟨h1, h2⟩
  obtain ⟨y, hy, hred⟩ := exists_int_of_entries _ (β⁻¹ * finE V k * β) N h1 (by
    rw [show (β⁻¹ * finE V k * β)⁻¹ = β⁻¹ * finE V k⁻¹ * β by rw [map_inv]; group]; exact h2)
  have hy' : frGL β y = finE V k := by
    show β * Formalism.UG.bc _ y * β⁻¹ = _
    rw [hy]; group
  have hSt : finE V k ∈ St β := ⟨y, hy'⟩
  refine ⟨⟨GlobalTheory.PrincInLevel.swap_mem_UPts _ _ _ (GlobalTheory.UnitarySplit.finHom_mem V k), hSt⟩, ?_⟩
  refine Subgroup.mem_iInf.2 fun PP => Subgroup.mem_iInf.2 fun hP => mem_princAt.2 ⟨hSt, ?_⟩
  rw [← hy', redFn_frGL]
  refine hred _ _ ?_
  rw [← map_natCast (Ideal.Quotient.mk PP.asIdeal)]
  exact Ideal.Quotient.eq_zero_iff_mem.2 (hNm PP hP)

theorem exists_open_level (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D))
    (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) :
    ∃ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) ∧ ∀ k ∈ U,
      ∃ h : (finHom V).rangeRestrict k ∈ (levEnv V β L).J, (levEnv V β L).χ ⟨_, h⟩ = 1 := by
  classical
  refine ⟨_, isOpen_Kg V β (L.Pg ∪ L.Q), fun k hk => ?_⟩
  have hk' : finE V k ∈ Kg D.sp.cm V.gram β (L.Pg ∪ L.Q) := hk
  refine ⟨Kg_le_lev (D := flag1L L) Finset.subset_union_left Finset.subset_union_right hk', ?_⟩
  have h3 : ∀ PP ∈ L.Pg ∪ L.Q, redFn β PP (finE V k) = 1 := by
    have h1 : finE V k ∈ ⨅ PP ∈ L.Pg ∪ L.Q, princAt β PP := hk'.2
    exact fun PP hP => (mem_princAt.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 h1 PP) hP)).2
  have e : rTup β (flag1L L) (finE V k) = 1 := by
    funext PP
    show upperLeftBlock L.hr (redFn β PP.1 (finE V k)) = 1
    rw [h3 PP.1 (Finset.mem_union_left _ PP.2)]; exact blockDiagonalExtendByOnePrimeField_one _ _
  show levFn β (flag1L L) (finE V k) = 1
  unfold levFn
  rw [e, blockDiagonalExtendByOnePrimeField_one, one_mul, Finset.prod_eq_one, Finset.prod_eq_one, one_mul]
  · intro PP hP
    rw [h3 PP (Finset.mem_union_right _ hP), dBlk, blockDiagonalExtendByOnePrimeField_one, map_one]
  · intro PP hP
    refine Finset.prod_eq_one fun c _ => ?_
    rw [h3 PP (Finset.mem_union_left _ hP), dBlk, blockDiagonalExtendByOnePrimeField_one, map_one]

section Coef

variable {V : HSp D} (c : CoefA V) {θ : InfFam D}

def invOp (h : GA D V) : c.W →L[ℂ] c.W := LinearMap.toContinuousLinearMap (c.ρ h⁻¹)

theorem invOp_apply (h : GA D V) (w : c.W) : invOp c h w = c.ρ h⁻¹ w := rfl

theorem invOp_one : invOp c 1 = 1 := by
  ext w; rw [invOp_apply, inv_one, map_one]; rfl

theorem invOp_mul (a b : GA D V) : invOp c (a * b) = invOp c b * invOp c a := by
  ext w; rw [invOp_apply, _root_.mul_inv_rev, map_mul]; rfl

def coefFun (F : GA D V → c.W) : (c.W →L[ℂ] ℂ) →ₗ[ℂ] (GA D V → ℂ) where
  toFun ℓ h := ℓ (invOp c h (F h))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem coefFun_mul {F : GA D V → c.W} (hF : ∀ g, ∀ k ∈ GinfC V, F (g * k) = F g) (ℓ : c.W →L[ℂ] ℂ) (g : GA D V)
    {k : GA D V} (hk : k ∈ GinfC V) : coefFun c F ℓ (g * k) = ℓ (invOp c k (invOp c g (F g))) := by
  show ℓ (invOp c (g * k) (F (g * k))) = _
  rw [hF g k hk, invOp_mul]; rfl

variable {c}

theorem exists_deriv (hθ : IsInfFam θ) (hc : c.Is) {τ : D.what₂.Tau} {X : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hX : X ∈ lieAt V τ) : invOp c (oneP θ V τ X 0) = 1 ∧ ∃ A : c.W →L[ℂ] c.W, ∀ t,
      HasDerivAt (fun s : ℝ => invOp c (oneP θ V τ X s)) ((invOp c (oneP θ V τ X t)).comp A) t := by
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  have hm := fun t : ℝ => GlobalTheory.SmoothAutCheck.exp_mem_UH (GlobalTheory.SmoothAutCheck.gramAt_unit V τ) hX t
  have h0 : invOp c (oneP θ V τ X 0) = 1 := by
    rw [oneP, zero_smul, NormedSpace.exp_zero, GlobalTheory.PointAtPlaceHom.atTau_one hθ, invOp_one]
  refine ⟨h0, Formalism.FourierDecayAlt.P.one_parameter_differentiable c.W _ h0 (fun s t => ?_) ?_⟩
  · rw [add_comm, oneP, add_smul, Matrix.exp_add_of_commute _ _ (((Commute.refl X).smul_left t).smul_right s),
      GlobalTheory.PointAtPlaceHom.atTau_mul hθ V τ (hm t) (hm s), invOp_mul]
    rfl
  · have he : Continuous fun t : ℝ => NormedSpace.exp (t • X) := by
      open scoped Matrix.Norms.Operator in
      exact NormedSpace.exp_continuous.comp (continuous_id.smul continuous_const)
    have h1 : Continuous fun t : ℝ => oneP θ V τ X t :=
      (GlobalTheory.PointAtPlaceHom.continuousOn_atTau hθ V τ).comp_continuous he hm
    exact continuous_clm_apply.2 fun w => (hc.2.2.1 w).comp h1.inv

theorem contDiff_oneP (hθ : IsInfFam θ) (hc : c.Is) {τ : D.what₂.Tau} {X : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hX : X ∈ lieAt V τ) : ContDiff ℝ ∞ fun s : ℝ => invOp c (oneP θ V τ X s) := by
  obtain ⟨-, A, hA⟩ := exists_deriv hθ hc hX
  refine contDiff_infty.2 fun n => ?_
  induction n with
  | zero => exact contDiff_zero.2 (continuous_iff_continuousAt.2 fun t => (hA t).continuousAt)
  | succ n ih =>
    rw [Nat.cast_succ, contDiff_succ_iff_deriv]
    refine ⟨fun t => (hA t).differentiableAt, by simp, ?_⟩
    rw [show deriv (fun s : ℝ => invOp c (oneP θ V τ X s)) = fun t => invOp c (oneP θ V τ X t) * A from
      funext fun t => (hA t).deriv]
    exact ih.mul contDiff_const

theorem contDiff_prod {k : ℕ} (l : List ((Fin k → ℝ) → GA D V)) (h : ∀ f ∈ l, ContDiff ℝ ∞ fun t => invOp c (f t)) :
    ContDiff ℝ ∞ fun t => invOp c (l.map fun f => f t).prod := by
  induction l with
  | nil => simpa using contDiff_const
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons, invOp_mul]
    exact (ih fun f hf => h f (List.mem_cons_of_mem _ hf)).mul (h a List.mem_cons_self)

variable {F : GA D V → c.W}

theorem rder_mem (hθ : IsInfFam θ) (hc : c.Is) (hF : ∀ g, ∀ k ∈ GinfC V, F (g * k) = F g) {τ : D.what₂.Tau}
    {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ) {φ : GA D V → ℂ}
    (hφ : φ ∈ LinearMap.range (coefFun c F)) : Rder θ V τ X φ ∈ LinearMap.range (coefFun c F) := by
  obtain ⟨ℓ, rfl⟩ := hφ
  obtain ⟨h0, A, hA⟩ := exists_deriv hθ hc hX
  refine ⟨ℓ.comp A, funext fun g => ?_⟩
  have e : (fun t : ℝ => coefFun c F ℓ (g * oneP θ V τ X t)) =
      fun t => ℓ (invOp c (oneP θ V τ X t) (invOp c g (F g))) :=
    funext fun t => coefFun_mul c hF ℓ g (GlobalTheory.PointAtPlaceHom.atTau_mem V τ _)
  have h1 := ((ℓ.comp (ContinuousLinearMap.apply ℂ c.W (invOp c g (F g)))).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
    (0 : ℝ) (hA 0)
  rw [h0] at h1
  rw [Rder, e]
  exact h1.deriv.symm

theorem foldr_mem {A B : Type} [AddCommGroup A] [Module ℂ A] (U : Submodule ℂ A) (op : B → A → A) (l : List B)
    (h : ∀ b ∈ l, ∀ x ∈ U, op b x ∈ U) {x : A} (hx : x ∈ U) : l.foldr op x ∈ U := by
  induction l with
  | nil => exact hx
  | cons a l ih => exact h a List.mem_cons_self _ (ih fun b hb => h b (List.mem_cons_of_mem _ hb))

theorem smooth_coefFun (hθ : IsInfFam θ) (hc : c.Is) (hF : ∀ g, ∀ k ∈ GinfC V, F (g * k) = F g)
    (ℓ : c.W →L[ℂ] ℂ) (k : ℕ) (τs : Fin k → D.what₂.Tau) (Xs : Fin k → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (hX : ∀ i, Xs i ∈ lieAt V (τs i)) (g : GA D V) :
    ContDiff ℝ ∞ fun t : Fin k → ℝ => coefFun c F ℓ (g * (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod) := by
  have h1 := contDiff_prod (c := c) (List.ofFn fun i (t : Fin k → ℝ) => oneP θ V (τs i) (Xs i) (t i)) (fun f hf => by
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hf
    exact (contDiff_oneP hθ hc (hX i)).comp (contDiff_apply ℝ ℝ i))
  simp only [List.map_ofFn, Function.comp_def] at h1
  have h2 := ((ℓ.comp (ContinuousLinearMap.apply ℂ c.W (invOp c g (F g)))).restrictScalars ℝ).contDiff.comp h1
  have e : (fun t : Fin k → ℝ => coefFun c F ℓ (g * (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod)) =
      fun t => ℓ (invOp c (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod (invOp c g (F g))) := by
    refine funext fun t => coefFun_mul c hF ℓ g (Subgroup.list_prod_mem _ fun x hx => ?_)
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
    exact GlobalTheory.PointAtPlaceHom.atTau_mem V _ _
  rw [e]
  exact h2

theorem gelf_mem (hθ : IsInfFam θ) (hc : c.Is) (hF : ∀ g, ∀ k ∈ GinfC V, F (g * k) = F g) (τ : D.what₂.Tau) (k : ℕ)
    {φ : GA D V → ℂ} (hφ : φ ∈ LinearMap.range (coefFun c F)) : gelf θ V τ k φ ∈ LinearMap.range (coefFun c F) := by
  unfold gelf
  refine Submodule.sum_mem _ fun idx _ => ?_
  refine foldr_mem (LinearMap.range (coefFun c F)) (fun (f : (GA D V → ℂ) → GA D V → ℂ) acc => f acc) _
    (fun L hL x hx => ?_) hφ
  obtain ⟨a, rfl⟩ := List.mem_ofFn.1 hL
  exact Submodule.add_mem _ (rder_mem hθ hc hF (GlobalTheory.SmoothAutCheck.parts_mem V τ _).1 hx)
    (Submodule.smul_mem _ _ (rder_mem hθ hc hF (GlobalTheory.SmoothAutCheck.parts_mem V τ _).2 hx))

theorem isAutFunSm_coefFun (hθ : IsInfFam θ) (hc : c.Is) (hF : ∀ g, ∀ k ∈ GinfC V, F (g * k) = F g)
    (ℓ : c.W →L[ℂ] ℂ) (h : IsAutFun V (coefFun c F ℓ)) : IsAutFunSm θ V (coefFun c F ℓ) where
  toIsAutFun := h
  smooth := smooth_coefFun hθ hc hF ℓ
  zfin := ⟨LinearMap.range (coefFun c F), inferInstance, ⟨ℓ, rfl⟩, fun τ k _ hf => gelf_mem hθ hc hF τ k hf⟩
  growth := by
    refine ⟨0, fun l hl x => ?_⟩
    obtain ⟨ℓ', e⟩ := foldr_mem (LinearMap.range (coefFun c F))
      (fun (p : D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ) f => Rder θ V p.1 p.2 f) l
      (fun p hp y hy => rder_mem hθ hc hF (hl p hp) hy) (LinearMap.mem_range_self _ ℓ)
    refine ⟨‖ℓ'‖ * ‖invOp c x (F x)‖, fun g hg => ?_⟩
    rw [← e, coefFun_mul c hF ℓ' x hg, pow_zero, mul_one]
    refine (ℓ'.le_opNorm _).trans (le_of_eq ?_)
    rw [invOp_apply c g, norm_eq_sqrt_re_inner (𝕜 := ℂ) (c.ρ _ _), hc.2.1, ← norm_eq_sqrt_re_inner (𝕜 := ℂ)]

theorem fin_mul_inf (f : Bridge.Gf V → c.W) (g : GA D V) (k : GA D V) (hk : k ∈ GinfC V) :
    f ((finHom V).rangeRestrict (g * k)) = f ((finHom V).rangeRestrict g) := by
  have : (finHom V).rangeRestrict k = 1 := Subtype.ext hk
  rw [map_mul, this, mul_one]

theorem adForms_left {G Γ W : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] {ι : Γ →* G}
    {ρ : Γ →* Module.End ℂ W} {J : Subgroup G} {χ : J →* ℂˣ} {f : G → W} (hf : f ∈ Bridge.AdForms ι ρ J χ) (γ : Γ)
    (h : G) : f (ι γ * h) = ρ γ (f h) := by
  simpa using hf γ h 1

theorem adForms_right {G Γ W : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] {ι : Γ →* G}
    {ρ : Γ →* Module.End ℂ W} {J : Subgroup G} {χ : J →* ℂˣ} {f : G → W} (hf : f ∈ Bridge.AdForms ι ρ J χ) (h : G)
    {k : G} (hk : k ∈ J) (h1 : χ ⟨k, hk⟩ = 1) : f (h * k) = f h := by
  simpa [h1] using hf 1 h ⟨k, hk⟩

theorem rho_inv_cancel (a : GA D V) (w : c.W) : c.ρ a (c.ρ a⁻¹ w) = w := by
  rw [← Module.End.mul_apply, ← map_mul c.ρ, mul_inv_cancel, map_one c.ρ, Module.End.one_apply]

theorem rho_mul_inv (a g : GA D V) (w : c.W) : c.ρ (a * g)⁻¹ (c.ρ a w) = c.ρ g⁻¹ w := by
  rw [← Module.End.mul_apply, ← map_mul c.ρ, _root_.mul_inv_rev, inv_mul_cancel_right]

open Classical in

theorem exists_sobCont {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) [FiniteDimensional ℂ (M.H τ)]
    (T : MMap M) (v : M.Vec) (x : GA D V) : ∃ ℓ : M.H τ →ₗ[ℂ] ℂ, Sobolev₂ (lieAt V τ) (M.rep τ) ℓ ∧
      ∀ w : M.sm τ, ℓ w = T (Function.update v τ w) x := by
  let ℓ₀ : M.sm τ →ₗ[ℂ] ℂ := (LinearMap.proj x : (GA D V → ℂ) →ₗ[ℂ] ℂ) ∘ₗ T.toLinearMap v τ
  obtain ⟨ℓ, hℓ⟩ := LinearMap.exists_extend ℓ₀
  refine ⟨ℓ, ⟨[[]], ‖LinearMap.toContinuousLinearMap ℓ‖, by simp, fun w _ => ?_⟩, fun w => LinearMap.congr_fun hℓ w⟩
  simpa using (LinearMap.toContinuousLinearMap ℓ).le_opNorm w

theorem isAutFun_coefFun (hc : c.Is) {β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)}
    {L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank} {f : Bridge.Gf V → c.W}
    (hf : f ∈ Bridge.AdForms (Bridge.ratF V) c.coef.ρ (levEnv V β L).J (levEnv V β L).χ) (ℓ : c.W →L[ℂ] ℂ) :
    IsAutFun V (coefFun c (fun g => f ((finHom V).rangeRestrict g)) ℓ) := by
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  obtain ⟨U, hU, hJ⟩ := exists_open_level V β L
  have hr : ∀ g, ∀ k ∈ U, f ((finHom V).rangeRestrict (g * k)) = f ((finHom V).rangeRestrict g) := by
    intro g k hk
    obtain ⟨h1, h2⟩ := hJ k hk
    rw [map_mul (finHom V).rangeRestrict]
    exact adForms_right hf _ h1 h2
  refine ⟨fun γ hγ g => ?_, ⟨U, hU, fun k hk hk' g => ?_⟩, continuous_iff_continuousAt.2 fun g₀ => ?_⟩
  · show ℓ (c.ρ (γ * g)⁻¹ (f ((finHom V).rangeRestrict (γ * g)))) = ℓ (c.ρ g⁻¹ (f ((finHom V).rangeRestrict g)))
    have e : f ((finHom V).rangeRestrict (γ * g)) = c.ρ γ (f ((finHom V).rangeRestrict g)) := by
      rw [map_mul (finHom V).rangeRestrict]; exact adForms_left hf ⟨γ, hγ⟩ _
    exact congrArg ℓ ((congrArg (c.ρ (γ * g)⁻¹) e).trans (rho_mul_inv γ g _))
  · show ℓ (c.ρ (g * k)⁻¹ (f ((finHom V).rangeRestrict (g * k)))) = ℓ (c.ρ g⁻¹ (f ((finHom V).rangeRestrict g)))
    have e : c.ρ (g * k)⁻¹ = c.ρ g⁻¹ := by
      rw [_root_.mul_inv_rev, map_mul c.ρ, hc.1 _ (inv_mem hk'), one_mul]
    exact congrArg ℓ ((congrArg (c.ρ (g * k)⁻¹) (hr g k hk)).trans (LinearMap.congr_fun e _))
  · have h1 : Continuous fun g : GA D V => ℓ (c.ρ g⁻¹ (f ((finHom V).rangeRestrict g₀))) :=
      ℓ.continuous.comp ((hc.2.2.1 _).comp continuous_inv)
    refine h1.continuousAt.congr ?_
    have h2 : (fun g : GA D V => g₀⁻¹ * g) ⁻¹' U ∈ 𝓝 g₀ :=
      (hU.preimage (continuous_const.mul continuous_id)).mem_nhds (by
        show g₀⁻¹ * g₀ ∈ U
        rw [inv_mul_cancel]; exact one_mem _)
    refine Filter.mem_of_superset h2 fun g hg => ?_
    show ℓ (c.ρ g⁻¹ (f ((finHom V).rangeRestrict g₀))) = ℓ (c.ρ g⁻¹ (f ((finHom V).rangeRestrict g)))
    have e : f ((finHom V).rangeRestrict g) = f ((finHom V).rangeRestrict g₀) :=
      (congrArg (fun x => f ((finHom V).rangeRestrict x)) (mul_inv_cancel_left g₀ g)).symm.trans (hr g₀ (g₀⁻¹ * g) hg)
    exact congrArg (fun w => ℓ (c.ρ g⁻¹ w)) e.symm

theorem isMultMap_toMap (hθ : IsInfFam θ) (hs : V.SigOK) (hd : V.IsDefinite) {S : D.what₂.Tau → SPar} (M : DSModel V S)
    (hc : c.Is) {pr : c.W →ₗ[ℂ] SmT M →ₗ[ℂ] ℂ} (hpr : IsDualPair θ M c pr)
    {β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)} {L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank} {f : Bridge.Gf V → c.W}
    (hf : f ∈ Bridge.AdForms (Bridge.ratF V) c.coef.ρ (levEnv V β L).J (levEnv V β L).χ) :
    IsMultMap θ M ∅ 1 (PiTensorProduct.lift.symm (c.toMap pr f)) := by
  classical
  have e : ∀ v : M.Vec, PiTensorProduct.lift.symm (c.toMap pr f) v =
      coefFun c (fun g => f ((finHom V).rangeRestrict g))
        (LinearMap.toContinuousLinearMap (pr.flip (PiTensorProduct.tprod ℂ v))) := fun v => rfl
  refine ⟨fun v => ?_, fun v => isCuspFun_of_definite hs hd _, fun v k hk => absurd hk (Set.notMem_empty k),
    fun τ g hg v w hw => ?_, fun τ v x => ?_⟩
  · rw [e]
    exact isAutFunSm_coefFun hθ hc (fin_mul_inf f) _ (isAutFun_coefFun hc hf _)
  · funext h
    rw [e, e, rTr, coefFun_mul c (fin_mul_inf f) _ h (GlobalTheory.PointAtPlaceHom.atTau_mem V τ g)]
    have := hpr.2 τ g hg (c.ρ (atTau θ V τ g)⁻¹ (c.ρ h⁻¹ (f ((finHom V).rangeRestrict h)))) v w hw
    rw [rho_inv_cancel] at this
    exact this
  · haveI := finiteDimensional_model hs hd M τ
    exact exists_sobCont M τ _ v x

end Coef

theorem end_definite (D : D7) : D.sp.X'.IsDefinite := (factXmDef D.R D.host.F D.sp).1

theorem endForms : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), IsInfFam R.θ → R.models_cX → R.models_prX → R.models_HX → EndForms R := by
  intro D G _ _ Pl0 T A Ks _ _ _ R hθ hc hpr hH t
  refine ⟨∅, 1, ?_⟩
  rintro _ ⟨x, rfl⟩
  have hx := (hH t).2.1.le (LinearMap.mem_range_self (R.HX t).e x)
  have h := isMultMap_toMap hθ D.sp.X'_sig (end_definite D) R.MX hc hpr hx
  exact (mem_multT R.θ R.MX ∅ 1 (R.cX.toMap R.prX ((R.HX t).e x))).2 (Submodule.subset_span h)

end GlobalTheory.DefiniteEnd

end
