import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound

noncomputable section

namespace GlobalTheory.SelConj

open Formalism.BasicNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations ReciprocityTheory.Gal TensorProduct

section Hf

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [Module O V] [IsScalarTower O LL V]
    {ρ ρ' : Representation LL G V} [TopologicalSpace G]
    [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V]

theorem blochKatoCocycle_map_equivariant (f : V →ₗ[LL] V) (hf : Continuous f) (he : ∀ g x, f (ρ g x) = ρ' g (f x))
    (c : G → V) (hc : c ∈ finiteCocycles PD ρ) : (fun g => f (c g)) ∈ finiteCocycles PD ρ' := by
  obtain ⟨⟨h1, h2⟩, x, hx⟩ := hc
  refine ⟨⟨hf.comp h1, fun g h => ?_⟩,
    AlgebraTensorModule.map f (LinearMap.id : B →ₗ[Qp] B) x, fun g => ?_⟩
  · simp only [h2, map_add, he]
  · have e := congrArg (AlgebraTensorModule.map f (LinearMap.id : B →ₗ[Qp] B)) (hx g)
    rw [map_sub, AlgebraTensorModule.map_tmul, LinearMap.id_apply] at e
    rw [e]
    congr 1
    clear e hx
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [actVB, he]
    | add a b ha hb => simp only [map_add, ha, hb]

theorem hfD_map (L : Lattice (O := O) ρ) (L' : Lattice (O := O) ρ') (f : V →ₗ[LL] V)
    (hf : Continuous f) (he : ∀ g x, f (ρ g x) = ρ' g (f x))
    (q : (V ⧸ L.T) → (V ⧸ L'.T)) (hadd : ∀ a b, q (a + b) = q a + q b)
    (hq : ∀ x, q (Submodule.Quotient.mk x) = Submodule.Quotient.mk (f x))
    (c : G → V ⧸ L.T) (hc : c ∈ HfD PD L) : (fun g => q (c g)) ∈ HfD PD L' := by
  obtain ⟨a, ⟨z, hz, rfl⟩, b, ⟨m, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hc
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ m
  refine Submodule.mem_sup.2 ⟨_, ⟨fun g => f (z g), blochKatoCocycle_map_equivariant PD f hf he z hz, rfl⟩, _,
    ⟨Submodule.Quotient.mk (f m), rfl⟩, ?_⟩
  funext g
  show Submodule.Quotient.mk (f (z g)) + Submodule.Quotient.mk (ρ' g (f m) - f m) =
    q (Submodule.Quotient.mk (z g) + Submodule.Quotient.mk (ρ g m - m))
  rw [hadd, hq, hq, map_sub, he]

end Hf

section Std

variable {O LL : Type} [CommRing O] [Field LL] [Algebra O LL] {k : ℕ}

def qMat (LL : Type) [Field LL] [Algebra O LL] (U : Matrix (Fin k) (Fin k) O) :
    ((Fin k → LL) ⧸ stdG O LL k) →ₗ[O] ((Fin k → LL) ⧸ stdG O LL k) :=
  Submodule.mapQ _ _ ((U.map (algebraMap O LL)).mulVecLin.restrictScalars O) (by
    rintro _ ⟨u, rfl⟩
    refine ⟨U.mulVec u, ?_⟩
    funext j
    exact RingHom.map_mulVec (algebraMap O LL) U u j)

theorem qMat_mk (U : Matrix (Fin k) (Fin k) O) (x : Fin k → LL) :
    qMat LL U (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ((U.map (algebraMap O LL)).mulVec x) := rfl

theorem qMat_mul (U U' : Matrix (Fin k) (Fin k) O) (x : (Fin k → LL) ⧸ stdG O LL k) :
    qMat LL U (qMat LL U' x) = qMat LL (U * U') x := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [qMat_mk, qMat_mk, qMat_mk, Matrix.mulVec_mulVec, Matrix.map_mul]

theorem qMat_one (x : (Fin k → LL) ⧸ stdG O LL k) : qMat LL 1 x = x := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [qMat_mk, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]

end Std

section W

variable {O : Type} [CommRing O] [IsDomain O] {Γ : Type} [Group Γ] {k : ℕ}

theorem wkg_apply (M : Γ →* Matrix (Fin k) (Fin k) O) (g : Γ) (x : KOG O k) :
    WKG M g x = qMat (FractionRing O) (M g) x := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rfl

theorem qMat_equiv (M M' : Γ →* Matrix (Fin k) (Fin k) O) (U : Matrix (Fin k) (Fin k) O)
    (h : ∀ g, M' g * U = U * M g) (g : Γ) (x : KOG O k) :
    qMat (FractionRing O) U (WKG M g x) = WKG M' g (qMat (FractionRing O) U x) := by
  rw [wkg_apply, wkg_apply, qMat_mul, qMat_mul, h]

end W

section Coh

variable {R : Type} [CommRing R] {G : Type} [Group G] [TopologicalSpace G]
  {M : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [IsTopologicalAddGroup M] [ContinuousConstSMul R M]

theorem res_map (rho rho' : Representation R G M) (u : M →ₗ[R] M) (hu : Continuous u)
    (he : ∀ g m, u (rho g m) = rho' g (u m)) {H : Type} [Group H] [TopologicalSpace H]
    (phi : H →* G) (hphi : Continuous phi) (x : H1 rho) :
    resH1 rho' phi hphi (mapH1 rho rho' u hu he x) =
      mapH1 (rho.comp phi) (rho'.comp phi) u hu (fun g m => he (phi g) m)
        (resH1 rho phi hphi x) := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rfl

theorem ur_map (rho rho' : Representation R G M) (u : M →ₗ[R] M) (hu : Continuous u)
    (he : ∀ g m, u (rho g m) = rho' g (u m)) (J : Subgroup G) (x : H1 rho)
    (hx : x ∈ H1ur rho J) : mapH1 rho rho' u hu he x ∈ H1ur rho' J := by
  have hx' : resH1 rho J.subtype continuous_subtype_val x = 0 := hx
  exact (res_map rho rho' u hu he J.subtype continuous_subtype_val x).trans
    ((congrArg _ hx').trans (map_zero _))

theorem map_left_inv (rho rho' : Representation R G M) (u u' : M →ₗ[R] M) (hu : Continuous u)
    (hu' : Continuous u') (he : ∀ g m, u (rho g m) = rho' g (u m))
    (he' : ∀ g m, u' (rho' g m) = rho g (u' m)) (hi : ∀ m, u' (u m) = m) (x : H1 rho) :
    mapH1 rho' rho u' hu' he' (mapH1 rho rho' u hu he x) = x := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  show Submodule.Quotient.mk _ = Submodule.Quotient.mk _
  congr 1
  exact Subtype.ext (funext fun g => hi _)

end Coh

section Bridge

variable {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
  {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  (Bw : LocBridge l E Ω Gw O) [IsDomain O]

set_option synthInstance.maxHeartbeats 400000 in
theorem phi_qMat {k : ℕ} (U : Matrix (Fin k) (Fin k) O) (x : KOG O k) :
    Br.phi Bw k (qMat (FractionRing O) U x) =
      qMat (Br.LLw Bw) (U.map Bw.eO.toRingHom) (Br.phi Bw k x) := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  show Submodule.Quotient.mk (Br.vecS Bw k ((U.map (algebraMap O (FractionRing O))).mulVec x)) =
    Submodule.Quotient.mk (((U.map Bw.eO.toRingHom).map
      (algebraMap (Br.Ow Bw) (Br.LLw Bw))).mulVec (Br.vecS Bw k x))
  congr 1
  funext j
  show Br.toLLK Bw (((U.map (algebraMap O (FractionRing O))).mulVec x) j) = _
  rw [RingHom.map_mulVec]
  congr 1
  exact Matrix.ext fun a b => Br.toLLK_alg Bw (U a b)

set_option synthInstance.maxHeartbeats 400000 in
theorem bk_map (P : LocPrime l) {k : ℕ} (rho rho' : Representation O ↥Gw (KOG O k))
    (M M' : ↥Gw →* Matrix (Fin k) (Fin k) O) (U : Matrix (Fin k) (Fin k) O)
    (h : ∀ g, M' g * U = U * M g) (hu : Continuous (qMat (FractionRing O) U))
    (he : ∀ g m, qMat (FractionRing O) U (rho g m) = rho' g (qMat (FractionRing O) U m))
    (x : H1 rho) (hx : x ∈ Br.bkG Bw P rho M) :
    mapH1 rho rho' (qMat (FractionRing O) U) hu he x ∈ Br.bkG Bw P rho' M' := by
  obtain ⟨c, hc, rfl⟩ := hx
  refine ⟨cocycles1MapOfEquivariant rho rho' (qMat (FractionRing O) U) hu he c, ?_, rfl⟩
  have key := hfD_map (P.PD Bw.Kw) (Br.lat Bw M) (Br.lat Bw M')
    (((U.map Bw.eO.toRingHom).map (algebraMap (Br.Ow Bw) (Br.LLw Bw))).mulVecLin)
    (continuous_const.matrix_mulVec continuous_id) ?_
    (qMat (Br.LLw Bw) (U.map Bw.eO.toRingHom)) (map_add _) (fun _ => rfl) _ hc
  · have e : Br.Phi Bw rho' (cocycles1MapOfEquivariant rho rho' (qMat (FractionRing O) U) hu he c) =
        fun g => qMat (Br.LLw Bw) (U.map Bw.eO.toRingHom) (Br.Phi Bw rho c g) := by
      funext g
      exact phi_qMat Bw U _
    show Br.Phi Bw rho' (cocycles1MapOfEquivariant rho rho' (qMat (FractionRing O) U) hu he c) ∈
      HfD (P.PD Bw.Kw) (Br.lat Bw M')
    rw [e]
    exact key
  · intro g v
    show Matrix.mulVec ((U.map Bw.eO.toRingHom).map (algebraMap (Br.Ow Bw) (Br.LLw Bw)))
        (Matrix.mulVec (((M (Br.ι Bw g)).map Bw.eO.toRingHom).map
          (algebraMap (Br.Ow Bw) (Br.LLw Bw))) v) =
      Matrix.mulVec (((M' (Br.ι Bw g)).map Bw.eO.toRingHom).map
          (algebraMap (Br.Ow Bw) (Br.LLw Bw)))
        (Matrix.mulVec ((U.map Bw.eO.toRingHom).map (algebraMap (Br.Ow Bw) (Br.LLw Bw))) v)
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.map_mul, ← Matrix.map_mul,
      ← Matrix.map_mul, ← Matrix.map_mul, h]

end Bridge

section Sel

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] (A : Formalism.GaloisCohomology.Places E Ω)
  (l : ℕ) [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  (P : LocPrime l)
  (nb : ∀ w, w ∈ placesOver E l → LocBridge l E Ω (Dec (F := E) (A.1 w)) O)
  (Sig : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E))) {k : ℕ}

theorem sel_map (M M' : Formalism.ConjugateSelfDual.G E Ω →* Matrix (Fin k) (Fin k) O) (U : Matrix (Fin k) (Fin k) O)
    (h : ∀ g, M' g * U = U * M g) (x : H1 (WKG M)) (hx : x ∈ Br.selG A l P nb Sig M) :
    mapH1 (WKG M) (WKG M') (qMat (FractionRing O) U) continuous_of_discreteTopology
      (qMat_equiv M M' U h) x ∈ Br.selG A l P nb Sig M' := by
  refine (mem_Sel _ _ _ _ _).2 fun v => ?_
  have hv := (mem_Sel _ _ _ _ _).1 hx v
  refine (res_map (WKG M) (WKG M') (qMat (FractionRing O) U) continuous_of_discreteTopology
    (qMat_equiv M M' U h) (Dec (F := E) (A.1 v)).subtype continuous_subtype_val x).symm ▸ ?_
  unfold Formalism.GaloisCohomology.bkCond at hv ⊢
  split_ifs at hv ⊢ with h1 h2
  · unfold Br.LlG at hv ⊢
    split_ifs at hv ⊢ with h3
    · exact bk_map (nb v h3) P _ _ _ _ U (fun g => h g) _ _ _ hv
    · trivial
  · trivial
  · exact ur_map _ _ _ _ _ _ _ hv

theorem sel_le (M M' : Formalism.ConjugateSelfDual.G E Ω →* Matrix (Fin k) (Fin k) O)
    (U U' : Matrix (Fin k) (Fin k) O) (hi : U' * U = 1)
    (h : ∀ g, M' g * U = U * M g) (h' : ∀ g, M g * U' = U' * M' g) :
    Module.length O (Br.selG A l P nb Sig M) ≤ Module.length O (Br.selG A l P nb Sig M') := by
  refine Module.length_le_of_injective
    ((mapH1 (WKG M) (WKG M') (qMat (FractionRing O) U) continuous_of_discreteTopology
      (qMat_equiv M M' U h)).restrict (sel_map A l P nb Sig M M' U h)) ?_
  intro x y hxy
  apply Subtype.ext
  have e := congrArg (fun z => mapH1 (WKG M') (WKG M) (qMat (FractionRing O) U')
    continuous_of_discreteTopology (qMat_equiv M' M U' h') (Subtype.val z)) hxy
  have hi' : ∀ m, qMat (FractionRing O) U' (qMat (FractionRing O) U m) = m := fun m => by
    rw [qMat_mul, hi, qMat_one]
  simpa only [LinearMap.restrict_apply, map_left_inv _ _ _ _ _ _ _ _ hi'] using e

end Sel

theorem selG_length_conj : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] (A : Formalism.GaloisCohomology.Places E Ω) (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [Algebra ℤ_[l] O] [TopologicalSpace O] (P : LocPrime l) (nb : ∀ w, w ∈ Formalism.BasicNotions.placesOver E l → LocBridge l E Ω (ReciprocityTheory.Gal.Dec (F := E) (A.1 w)) O) (Sig : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E))) (k : ℕ) (M M' : Formalism.ConjugateSelfDual.G E Ω →* Matrix (Fin k) (Fin k) O) (U : GL (Fin k) O), (∀ g, M' g * (U : Matrix (Fin k) (Fin k) O) = (U : Matrix (Fin k) (Fin k) O) * M g) → Module.length O (Formalism.MainNotions.N.Br.selG A l P nb Sig M) = Module.length O (Formalism.MainNotions.N.Br.selG A l P nb Sig M') := by
  intro E Ω _ _ _ _ A l _ O _ _ _ _ P nb Sig k M M' U h
  have h' : ∀ g, M g * ((U⁻¹ : GL (Fin k) O) : Matrix (Fin k) (Fin k) O) =
      ((U⁻¹ : GL (Fin k) O) : Matrix (Fin k) (Fin k) O) * M' g := fun g => by
    rw [Units.mul_inv_eq_iff_eq_mul, mul_assoc, h, ← mul_assoc, Units.inv_mul, one_mul]
  exact le_antisymm (sel_le A l P nb Sig M M' _ _ (Units.inv_mul U) h h')
    (sel_le A l P nb Sig M' M _ _ (Units.mul_inv U) h' h)

end GlobalTheory.SelConj
