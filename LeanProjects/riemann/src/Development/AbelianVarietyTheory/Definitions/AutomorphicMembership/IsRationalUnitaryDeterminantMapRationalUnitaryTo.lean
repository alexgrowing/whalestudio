import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalToGlobal.UnitaryNorms.CharUniq

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host

namespace GlobalTheory.Mem.Chr

section General

variable (L : Type) [Field L] [NumberField L]

def unitIdl : Subgroup (Ideles L) where
  carrier := {a | ∀ v, Valued.v ((a : AdeleRing (𝓞 L) L).2 v) = 1}
  one_mem' := fun v => by
    show Valued.v (1 : v.adicCompletion L) = 1
    exact map_one _
  mul_mem' := fun {a b} ha hb v => by
    show Valued.v ((a : AdeleRing (𝓞 L) L).2 v * (b : AdeleRing (𝓞 L) L).2 v) = 1
    rw [map_mul, ha v, hb v, one_mul]
  inv_mem' := fun {a} ha v => by
    have h : (a : AdeleRing (𝓞 L) L).2 v * ((a⁻¹ : Ideles L) : AdeleRing (𝓞 L) L).2 v = 1 :=
      congrArg (fun z : AdeleRing (𝓞 L) L => z.2 v) a.mul_inv
    have h2 := congrArg (Valued.v : Valuation (v.adicCompletion L) _) h
    rw [map_mul, ha v, one_mul, map_one] at h2
    exact h2

def finPartI : Ideles L →* Ideles L :=
  Units.map ((MonoidHom.inr (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)).comp
    (MonoidHom.snd (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)))

variable {L}

def locF (F : Type) [Field F] [NumberField F] [Algebra F L] (v : HeightOneSpectrum (𝓞 F)) (k : Fˣ) : Ideles L :=
  ∏ Q ∈ aboveF (L := L) F v, localIdele L Q (atFin Q (upF F k))

def ConjPl (c : L ≃+* L) (v v' : HeightOneSpectrum (𝓞 L)) : Prop :=
  ∀ x : L, v'.valuation L (c x) = v.valuation L x

structure IsConjI (c : L ≃+* L) (C : Ideles L →* Ideles L) : Prop where
  cont : Continuous C
  diag : ∀ k : Lˣ, C (diagUnits L k) = diagUnits L (Units.map (MonoidHomClass.toMonoidHom c) k)
  inf : ∀ (w : InfinitePlace L) (k : Lˣ), C (infIdele L w (atInf w k)) =
    infIdele L (w.comap (c.symm : L →+* L)) (atInf _ (Units.map (MonoidHomClass.toMonoidHom c) k))
  infRange : ∀ (w : InfinitePlace L) (y : (w.Completion)ˣ), ∃ y', C (infIdele L w y) = infIdele L (w.comap (c.symm : L →+* L)) y'
  loc : ∀ v v', ConjPl c v v' → ∀ k : Lˣ, C (localIdele L v (atFin v k)) =
    localIdele L v' (atFin v' (Units.map (MonoidHomClass.toMonoidHom c) k))
  locRange : ∀ v v', ConjPl c v v' → ∀ x, ∃ x', C (localIdele L v x) = localIdele L v' x'
  val : ∀ v v', ConjPl c v v' → ∀ a : Ideles L,
    Valued.v ((C a : AdeleRing (𝓞 L) L).2 v') = Valued.v ((a : AdeleRing (𝓞 L) L).2 v) ∧
    Valued.v ((C a : AdeleRing (𝓞 L) L).2 v' - 1) = Valued.v ((a : AdeleRing (𝓞 L) L).2 v - 1)

def TameLoc (v : HeightOneSpectrum (𝓞 L)) (θ : (v.adicCompletion L)ˣ →* ℂˣ) : Prop :=
  (∀ x, ‖((θ x : ℂˣ) : ℂ)‖ = 1) ∧
    ∀ x, IsUnitAt v x → Valued.v ((x : v.adicCompletion L) - 1) ≤ WithZero.exp (-1 : ℤ) → θ x = 1

def detSub {N : ℕ} (M : Submodule (𝓞 L) (Fin N → L)) : Submodule (𝓞 L) L :=
  Submodule.span (𝓞 L) {z | ∃ x : Fin N → Fin N → L, (∀ i, x i ∈ M) ∧ z = (Matrix.of x).det}

def ordSub (w : HeightOneSpectrum (𝓞 L)) (A : Submodule (𝓞 L) L) : ℤ :=
  sInf {n | ∃ k : Lˣ, (k : L) ∈ A ∧ ordF w k = n}

def SplitsC (L : Type) [Field L] [NumberField L] (p : ℕ) : Prop :=
  {v : HeightOneSpectrum (𝓞 L) | ((p : ℕ) : 𝓞 L) ∈ v.asIdeal}.ncard = Module.finrank ℚ L

structure CMData (F : Type) [Field F] [NumberField F] [Algebra F L] (c : L ≃ₐ[F] L) {I : Type} (φ : I → L →+* ℂ) : Prop where
  real : IsTotallyReal F
  cplx : IsTotallyComplex L
  rank : Module.finrank F L = 2
  ne : c ≠ 1
  bij : Function.Bijective fun i => InfinitePlace.mk (φ i)

end General

instance framePsiFintype (φ : Formalism.HC.Frame) : Fintype φ.Psi := Fintype.ofFinite _

variable {R : Ranks} (H : Formalism.BasicNotions.Host R)

def congG : Set (Ideles H.E) :=
  {a | a ∈ unitIdl H.E ∧ ∀ k v, OverP H (H.g k) v → Valued.v ((a : AdeleRing (𝓞 H.E) H.E).2 v - 1) < 1}

def KD : Subgroup (Ideles H.E) :=
  Subgroup.closure (congG H ∪ {a | ∃ v k, a = locF H.F v k})

abbrev DtT : Type := Ideles H.E ⧸ KD H

open Classical in

def tildeD (χ : HChar H.E) : DtT H →* ℂˣ :=
  if h : KD H ≤ (χ.1.comp (finPartI H.E)).ker then QuotientGroup.lift (KD H) (χ.1.comp (finPartI H.E)) h else 1

def muTilT (mu : Fin R.m → HChar H.E) (j : ℕ) : DtT H →* ℂˣ :=
  if h : 1 ≤ j ∧ j ≤ R.m then tildeD H (mu ⟨j - 1, by omega⟩) else 1

def UOT : Subgroup (DtT H) := (unitIdl H.E).map (QuotientGroup.mk' (KD H))

def IsRationalUnitaryDeterminantMap (f : (letI := H.cmStar; unitary H.E) →* DtT H) : Prop :=
  letI := H.cmStar
  ∀ (k : H.Eˣ) (z : unitary H.E), (z : H.E) * H.conj (k : H.E) = k → QuotientGroup.mk (diagUnits H.E k) = f z

open Classical in

def e1T : (letI := H.cmStar; unitary H.E) →* DtT H := if h : ∃ f, IsRationalUnitaryDeterminantMap H f then h.choose else 1

def relDetT (N : ℕ) (M M' : Submodule (𝓞 H.E) (Fin N → H.E)) : DtT H ⧸ UOT H :=
  QuotientGroup.mk (QuotientGroup.mk (∏ᶠ w : HeightOneSpectrum (𝓞 H.E),
    localIdele H.E w (atFin w (unif w)) ^ (ordSub w (detSub M') - ordSub w (detSub M)).toNat))

def IsTwist (S : Set ℕ) (ξ : HChar H.E) : Prop :=
  (∃ n : ℕ, 0 < n ∧ ξ.OrderDvd n) ∧ ξ.TrivOn H.F ∧ (∀ v, ξ.TameAt v) ∧
    ∀ v, ¬ ξ.UnrAt v → IsSplitPl H v ∧ (Ideal.absNorm v.asIdeal).Prime ∧
      ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 H.E) ∉ v.asIdeal ^ 2 ∧ Ideal.absNorm v.asIdeal ∉ S

structure HFrame (e : Fin R.m → R.Psi → ℚ) where
  P : PiBar H
  W : Omg H
  mu0 : Fin R.m → HChar H.E
  eta : HChar H.E
  chiPsi : HChar H.E
  del : HChar H.E
  del' : HChar H.E
  isMu0 : ∀ j, IsMu0 P W (e j) j.1 (mu0 j)
  isEta : IsEtaT H eta
  isChi : IsChiPsi H chiPsi
  isDel : IsDelta (H := H) H.pde del
  isDel' : IsDelta (H := H) H.pde' del'

structure DtPack where
  Dt : Type
  [instDt : CommGroup Dt]
  muTil : ℕ → Dt →* ℂˣ
  chiD : Dt →* ℂˣ
  UO : Subgroup Dt
  chiD_UO : ∀ x ∈ UO, chiD x = 1
  e1Dt : letI := H.cmStar; unitary H.E →* Dt
  rest_detCharacter_on_unitary_eq : letI := H.cmStar; ∀ z : unitary H.E,
    ((chiD (e1Dt z) : ℂˣ) : ℂ) = ∏ τ : R.Psi, (H.emb (τ : R.GG) (z : H.E))⁻¹
  relDet : letI := H.cmStar; ∀ N, SDLat H.E N → SDLat H.E N → Dt ⧸ UO
  relDet_self : letI := H.cmStar; ∀ N L, relDet N L L = 1
  relDet_mul : letI := H.cmStar; ∀ N L L' L'', relDet N L L' * relDet N L' L'' = relDet N L L''
  relDet_smul : letI := H.cmStar; ∀ N (L L' : SDLat H.E N) (γ : Matrix.unitaryGroup (Fin N) H.E),
    L'.1 = SDLat.smulLat (γ : Matrix (Fin N) (Fin N) H.E) L.1 → relDet N L L' =
      QuotientGroup.mk (e1Dt ⟨(γ : Matrix (Fin N) (Fin N) H.E).det, Matrix.det_of_mem_unitary γ.2⟩)

section API

variable {L : Type} [Field L] [NumberField L]

theorem mem_unitIdl {a : Ideles L} :
    a ∈ unitIdl L ↔ ∀ v, Valued.v ((a : AdeleRing (𝓞 L) L).2 v) = 1 := Iff.rfl

theorem finPartI_fst (a : Ideles L) : (finPartI L a : AdeleRing (𝓞 L) L).1 = 1 := rfl

theorem finPartI_snd (a : Ideles L) : (finPartI L a : AdeleRing (𝓞 L) L).2 = (a : AdeleRing (𝓞 L) L).2 := rfl

theorem finPartI_idem (a : Ideles L) : finPartI L (finPartI L a) = finPartI L a := Units.ext rfl

theorem finPartI_eq_self {a : Ideles L} (h : ∀ w : InfinitePlace L, (a : AdeleRing (𝓞 L) L).1 w = 1) :
    finPartI L a = a :=
  Units.ext (Prod.ext (funext fun w => (h w).symm) rfl)

theorem finPartI_mem_unitIdl {a : Ideles L} : finPartI L a ∈ unitIdl L ↔ a ∈ unitIdl L := Iff.rfl

theorem conjPl_refl_iff (v v' : HeightOneSpectrum (𝓞 L)) : ConjPl (RingEquiv.refl L) v v' ↔ v = v' := by
  constructor
  · intro h
    ext x
    have h1 : v'.valuation L (algebraMap (𝓞 L) L x) = v.valuation L (algebraMap (𝓞 L) L x) := h _
    rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := L), ← HeightOneSpectrum.valuation_lt_one_iff_mem (K := L), h1]
  · rintro rfl x
    rfl

theorem isConjI_refl : IsConjI (RingEquiv.refl L) (MonoidHom.id (Ideles L)) where
  cont := continuous_id
  diag _ := rfl
  inf _ _ := rfl
  infRange _ y := ⟨y, rfl⟩
  loc v v' h k := by
    obtain rfl := (conjPl_refl_iff v v').1 h
    rfl
  locRange v v' h x := by
    obtain rfl := (conjPl_refl_iff v v').1 h
    exact ⟨x, rfl⟩
  val v v' h a := by
    obtain rfl := (conjPl_refl_iff v v').1 h
    exact ⟨rfl, rfl⟩

theorem tameLoc_one (v : HeightOneSpectrum (𝓞 L)) : TameLoc v 1 :=
  ⟨fun _ => by simp, fun _ _ _ => rfl⟩

theorem tameLoc_loc {χ : HChar L} (hu : χ.IsUnitary) {v : HeightOneSpectrum (𝓞 L)} (ht : χ.TameAt v) :
    TameLoc v (χ.loc v) :=
  ⟨fun _ => hu _, fun x hx hx' => ht x hx (by simpa using hx')⟩

theorem det_mem_detSub {N : ℕ} {M : Submodule (𝓞 L) (Fin N → L)} (x : Fin N → Fin N → L) (hx : ∀ i, x i ∈ M) :
    (Matrix.of x).det ∈ detSub M :=
  Submodule.subset_span ⟨x, hx, rfl⟩

theorem detSub_mono {N : ℕ} {M M' : Submodule (𝓞 L) (Fin N → L)} (h : M ≤ M') : detSub M ≤ detSub M' :=
  Submodule.span_mono fun _ ⟨x, hx, e⟩ => ⟨x, fun i => h (hx i), e⟩

theorem ordF_unif_self (w : HeightOneSpectrum (𝓞 L)) : ordF w (unif w) = 1 := by
  have h : Valued.v (((unif w : Lˣ) : L) : w.adicCompletion L) = WithZero.exp (-1 : ℤ) := unif_spec w
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at h
  simp [ordF, h]

theorem ordSub_span_singleton (w : HeightOneSpectrum (𝓞 L)) (u : Lˣ) :
    ordSub w (Submodule.span (𝓞 L) {(u : L)}) = ordF w u := by
  refine IsLeast.csInf_eq ⟨⟨u, Submodule.mem_span_singleton_self _, rfl⟩, ?_⟩
  rintro n ⟨k, hk, rfl⟩
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 hk
  have hk0 : w.valuation L (k : L) ≠ 0 := by simp
  have hu0 : w.valuation L (u : L) ≠ 0 := by simp
  have hle : w.valuation L (k : L) ≤ w.valuation L (u : L) := by
    rw [← ha, Algebra.smul_def, map_mul]
    exact mul_le_of_le_one_left' (w.valuation_le_one a)
  unfold ordF
  exact neg_le_neg ((WithZero.log_le_log hk0 hu0).2 hle)

example (w : HeightOneSpectrum (𝓞 L)) : ordSub w (Submodule.span (𝓞 L) {((unif w : Lˣ) : L)}) = 1 := by
  rw [ordSub_span_singleton, ordF_unif_self]

end API

section Inhabitant

instance negTwoFact : Fact (∀ r : ℚ, r ^ 2 ≠ -2 + 0 * r) := ⟨fun r h => by nlinarith [sq_nonneg r]⟩

abbrev NegTwoField : Type := QuadraticAlgebra ℚ (-2) 0

instance negTwoNumberField : NumberField NegTwoField := NumberField.of_module_finite ℚ _

def negTwoConj : NegTwoField ≃ₐ[ℚ] NegTwoField :=
  AlgEquiv.ofRingEquiv (f := (starRingAut : RingAut NegTwoField)) fun x => by
    show star (algebraMap ℚ NegTwoField x) = _
    ext <;> simp

theorem negTwo_roots (x : NegTwoField) (h : ∃ m : ℕ, 0 < m ∧ x ^ m = 1) : x = 1 ∨ x = -1 := by
  obtain ⟨m, hm, hx⟩ := h
  have hi : IsIntegral ℤ x := IsIntegral.of_pow hm (by rw [hx]; exact isIntegral_one)
  have hi' : IsIntegral ℤ (star x) :=
    IsIntegral.of_pow hm (by rw [← star_pow, hx, star_one]; exact isIntegral_one)
  have ht : IsIntegral ℤ (QuadraticAlgebra.trace x) := by
    have := hi.add hi'
    rw [← QuadraticAlgebra.algebraMap_trace_eq_add_star] at this
    exact (isIntegral_algebraMap_iff (algebraMap ℚ NegTwoField).injective).1 this
  obtain ⟨t, ht⟩ := IsIntegrallyClosed.isIntegral_iff.1 ht
  rw [QuadraticAlgebra.trace_def, eq_intCast] at ht
  have hn : QuadraticAlgebra.norm x = 1 := by
    have h0 : 0 ≤ QuadraticAlgebra.norm x := by
      rw [QuadraticAlgebra.norm_def]; nlinarith [sq_nonneg x.re, sq_nonneg x.im]
    exact (pow_eq_one_iff_of_nonneg h0 hm.ne').1 (by rw [← map_pow, hx, map_one])
  rw [QuadraticAlgebra.norm_def] at hn
  have h1 : (t : ℚ) ^ 2 + 8 * x.im ^ 2 = 4 := by rw [ht]; linear_combination 4 * hn
  have h2 : t ^ 2 ≤ 4 := by
    have : (t : ℚ) ^ 2 ≤ 4 := by nlinarith [sq_nonneg x.im]
    exact_mod_cast this
  have h3 : -2 ≤ t := by nlinarith
  have h4 : t ≤ 2 := by nlinarith
  have n2 : ¬ IsSquare (2 : ℚ) := by norm_num
  have n6 : ¬ IsSquare (6 : ℚ) := by norm_num
  interval_cases t
  · right
    push_cast at h1 ht
    have : x.im = 0 := by nlinarith [sq_nonneg x.im]
    ext
    · show x.re = -1
      linarith
    · show x.im = -0
      simpa using this
  · push_cast at h1
    exact absurd ⟨4 * x.im, by linear_combination (-2) * h1⟩ n6
  · push_cast at h1
    exact absurd ⟨2 * x.im, by linear_combination (-1 / 2) * h1⟩ n2
  · push_cast at h1
    exact absurd ⟨4 * x.im, by linear_combination (-2) * h1⟩ n6
  · left
    push_cast at h1 ht
    have : x.im = 0 := by nlinarith [sq_nonneg x.im]
    ext
    · show x.re = 1
      linarith
    · exact this

theorem cmData_negTwo : CMData ℚ negTwoConj (fun w : InfinitePlace NegTwoField => w.embedding) where
  real := inferInstance
  cplx := by
    refine ⟨fun w => ?_⟩
    rw [← InfinitePlace.not_isReal_iff_isComplex]
    intro hw
    have h0 : (QuadraticAlgebra.omega : NegTwoField) ^ 2 = -2 := by
      ext <;> simp [pow_two, QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat]
    have h := congrArg (InfinitePlace.embedding_of_isReal hw) h0
    rw [map_pow, map_neg, map_ofNat] at h
    nlinarith [sq_nonneg (InfinitePlace.embedding_of_isReal hw QuadraticAlgebra.omega)]
  rank := QuadraticAlgebra.finrank_eq_two _ _
  ne := fun h => by
    have h1 : star (QuadraticAlgebra.omega : NegTwoField) = QuadraticAlgebra.omega :=
      congrArg (fun f : NegTwoField ≃ₐ[ℚ] NegTwoField => f QuadraticAlgebra.omega) h
    have h2 := congrArg QuadraticAlgebra.im h1
    simp at h2
    norm_num at h2
  bij := by
    simp only [InfinitePlace.mk_embedding]
    exact Function.bijective_id

end Inhabitant

theorem mem_KD_of_congG {a : Ideles H.E} (h : a ∈ congG H) : a ∈ KD H :=
  Subgroup.subset_closure (Or.inl h)

theorem locF_mem_KD (v : HeightOneSpectrum (𝓞 H.F)) (k : (H.F)ˣ) : locF H.F v k ∈ KD H :=
  Subgroup.subset_closure (Or.inr ⟨v, k, rfl⟩)

theorem tildeD_mk {χ : HChar H.E} (h : KD H ≤ (χ.1.comp (finPartI H.E)).ker) (a : Ideles H.E) :
    tildeD H χ (QuotientGroup.mk a) = χ.1 (finPartI H.E a) := by
  unfold tildeD
  rw [dif_pos h]
  rfl

theorem muTilT_succ (mu : Fin R.m → HChar H.E) (j : Fin R.m) : muTilT H mu (j.1 + 1) = tildeD H (mu j) := by
  unfold muTilT
  rw [dif_pos ⟨Nat.le_add_left 1 j.1, j.2⟩]
  rfl

theorem mem_UOT {x : DtT H} : x ∈ UOT H ↔ ∃ a : Ideles H.E,
    (∀ v, Valued.v ((a : AdeleRing (𝓞 H.E) H.E).2 v) = 1) ∧ QuotientGroup.mk a = x := Iff.rfl

theorem isRationalUnitaryDeterminantMap_rationalUnitaryToDeterminants (h : ∃ f, IsRationalUnitaryDeterminantMap H f) : IsRationalUnitaryDeterminantMap H (e1T H) := by
  unfold e1T
  rw [dif_pos h]
  exact h.choose_spec

theorem relDetT_self (N : ℕ) (M : Submodule (𝓞 H.E) (Fin N → H.E)) : relDetT H N M M = 1 := by
  unfold relDetT
  simp

theorem isTwist_one (S : Set ℕ) : IsTwist H S 1 :=
  ⟨⟨1, one_pos, one_pow 1⟩, isClsF_one.triv, fun _ _ _ _ => rfl, fun v hv => absurd (isClsF_one.unr v) hv⟩

attribute [local instance] DtPack.instDt in

example (X : DtPack H) : letI := H.cmStar;
    ((X.chiD (X.e1Dt (-1)) : ℂˣ) : ℂ) = (-1) ^ Fintype.card (R.Psi) := by
  letI := H.cmStar
  rw [X.rest_detCharacter_on_unitary_eq]
  have e : ((-1 : unitary H.E) : H.E) = -1 := rfl
  simp [e]

end GlobalTheory.Mem.Chr
