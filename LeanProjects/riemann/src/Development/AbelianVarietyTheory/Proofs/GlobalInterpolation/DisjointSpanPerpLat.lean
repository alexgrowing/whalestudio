import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.UnitaryLatticeOrthogonal
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SelfDualLatticeActions

noncomputable section

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory.SelfDualLatticeCompare

section Field

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E}

theorem conj_conj (h : IsCMExt F E σ) (e : E) : σ (σ e) = e := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem exists_of_conj_eq (h : IsCMExt F E σ) (e : E) (he : σ e = e) :
    ∃ f, algebraMap F E f = e := by
  haveI := Subalgebra.isSimpleOrder_of_finrank h.2.2.1
  rcases eq_bot_or_eq_top (AlgHom.equalizer σ (AlgHom.id F E)) with h0 | h0
  · have : e ∈ AlgHom.equalizer σ (AlgHom.id F E) := he
    rw [h0, Algebra.mem_bot] at this
    exact this
  · exfalso
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    haveI := h.2.1
    refine IsTotallyComplex.complexEmbedding_not_isReal τ ?_
    rw [ComplexEmbedding.isReal_iff]
    ext x
    have hx : x ∈ AlgHom.equalizer σ (AlgHom.id F E) := h0 ▸ Algebra.mem_top
    have hx' : σ x = x := hx
    have := h.2.2.2 τ x
    rw [hx'] at this
    exact this.symm

theorem trace_field (h : IsCMExt F E σ) (e : E) :
    algebraMap F E (Algebra.trace F E e) = e + σ e := by
  have hσ := conj_conj h
  obtain ⟨a, ha⟩ := exists_of_conj_eq h (e + σ e) (by rw [map_add, hσ, add_comm])
  have h1 : Algebra.trace F E (σ e) = Algebra.trace F E e :=
    Algebra.trace_eq_of_algEquiv (AlgEquiv.ofAlgHom σ σ (AlgHom.ext hσ) (AlgHom.ext hσ)) e
  have h3 := congrArg (Algebra.trace F E) ha
  rw [Algebra.trace_algebraMap, h.2.2.1, map_add, h1, two_smul, ← two_mul, ← two_mul] at h3
  rw [← ha, mul_left_cancel₀ two_ne_zero h3]

variable (R : Type) [CommRing R] [Algebra F R]

theorem trace_tensor (h : IsCMExt F E σ) (z : R ⊗[F] E) :
    algebraMap R (R ⊗[F] E) (Algebra.trace R (R ⊗[F] E) z) = z + sigR R σ z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]; ring
  | tmul a e =>
    have h1 : a ⊗ₜ[F] e = a • ((1 : R) ⊗ₜ[F] e) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    have h3 : Algebra.trace R (R ⊗[F] E) (a ⊗ₜ[F] e) =
        a * algebraMap F R (Algebra.trace F E e) := by
      rw [h1, map_smul, Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul,
        LinearMap.trace_baseChange, smul_eq_mul]
    have h4 : sigR R σ (a ⊗ₜ[F] e) = a ⊗ₜ[F] σ e := rfl
    rw [h3, h4, ← TensorProduct.tmul_add, ← trace_field h, Algebra.TensorProduct.algebraMap_apply,
      Algebra.algebraMap_self, RingHom.id_apply, mul_comm, ← Algebra.smul_def,
      TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one]

theorem sigR_sigR (h : IsCMExt F E σ) (z : R ⊗[F] E) : sigR R σ (sigR R σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul a e =>
    show a ⊗ₜ[F] σ (σ e) = _
    rw [conj_conj h]

theorem hR_self (h : IsCMExt F E σ) {M : ℕ} {J : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J)
    (x : Fin M → R ⊗[F] E) : hR R σ J x x = algebraMap R (R ⊗[F] E) (qR R σ J x) := by
  have hJ' : ∀ i j, sigR R σ (JR R J j i) = JR R J i j := by
    intro i j
    show (1 : R) ⊗ₜ[F] σ (J j i) = (1 : R) ⊗ₜ[F] J i j
    rw [hJ.1]
  have hs : sigR R σ (hR R σ J x x) = hR R σ J x x := by
    simp only [hR, Formalism.UG.hform, map_sum, map_mul, sigR_sigR R h]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hJ']
    ring
  have h2 : algebraMap R (R ⊗[F] E) (algebraMap F R (1 / 2)) * 2 = 1 := by
    rw [← IsScalarTower.algebraMap_apply, ← map_ofNat (algebraMap F (R ⊗[F] E)) 2, ← map_mul,
      show (1 / 2 * 2 : F) = 1 by norm_num, map_one]
  rw [qR, map_mul, trace_tensor R h, hs, ← two_mul, ← mul_assoc, h2, one_mul]

theorem hR_smul_right {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (x y : Fin M → R ⊗[F] E)
    (c : R ⊗[F] E) : hR R σ J x (c • y) = c * hR R σ J x y := by
  simp only [hR, Formalism.UG.hform, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

end Field

section Clauses

open GlobalTheory.IndefiniteRowSideFullHecke

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (v : HeightOneSpectrum (𝓞 F))

theorem unram_iff : UnitaryLatticeOrthogonal.UnramAt F E v ↔ SelfDualLatticeActions.UnramifiedOrSplit E v := by
  refine forall_congr' fun w => forall_congr' fun hw => ?_
  haveI := w.isPrime
  haveI := w.isMaximal
  exact Ideal.ramificationIdx_eq_one_iff

theorem oEv_eq : UnitaryLatticeOrthogonal.OEv F E v = SelfDualLatticeActions.OEv E v := rfl

theorem act_eq : UnitaryLatticeOrthogonal.act σ J v = SelfDualLatticeActions.act v σ J := rfl

theorem perp_eq : UnitaryLatticeOrthogonal.perp σ J v = SelfDualLatticeActions.perp v σ J := rfl

theorem perpLat_eq (L : Submodule (SelfDualLatticeActions.OEv E v) (SelfDualLatticeActions.Wv E v M)) (x : SelfDualLatticeActions.Wv E v M) :
    UnitaryLatticeOrthogonal.perpLat σ J v L x = SelfDualLatticeActions.perpLat v σ J x L := rfl

theorem isSDLatIn_iff (P : Submodule (SelfDualLatticeActions.Ev E v) (SelfDualLatticeActions.Wv E v M))
    (L : Submodule (SelfDualLatticeActions.OEv E v) (SelfDualLatticeActions.Wv E v M)) :
    UnitaryLatticeOrthogonal.IsSDLatIn σ J v P L ↔ SelfDualLatticeActions.IsSelfDualIn v σ J P L := Iff.rfl

theorem isSDLat_iff (L : Submodule (SelfDualLatticeActions.OEv E v) (SelfDualLatticeActions.Wv E v M)) :
    UnitaryLatticeOrthogonal.IsSDLat σ J v L ↔ SelfDualLatticeActions.IsSelfDualLat v σ J L := Iff.rfl

theorem stabLat_eq (L : Submodule (SelfDualLatticeActions.OEv E v) (SelfDualLatticeActions.Wv E v M)) :
    UnitaryLatticeOrthogonal.stabLat σ J v L = SelfDualLatticeActions.latStab v σ J L := rfl

theorem stabVec_eq (x : SelfDualLatticeActions.Wv E v M) :
    UnitaryLatticeOrthogonal.stabVec σ J v x = SelfDualLatticeActions.vecStab v σ J x := rfl

theorem unitaryLatIn_eq (P : Submodule (SelfDualLatticeActions.Ev E v) (SelfDualLatticeActions.Wv E v M))
    (L : Submodule (SelfDualLatticeActions.OEv E v) (SelfDualLatticeActions.Wv E v M)) :
    UnitaryLatticeOrthogonal.unitaryLatIn σ J v P L = SelfDualLatticeActions.latUnitaryIn v σ J P L := rfl

theorem xb_eq (β : Fv F v) : UnitaryLatticeOrthogonal.Xb σ J v β = SelfDualLatticeActions.Xbeta v σ J β := rfl

theorem sL_eq (L : Submodule (SelfDualLatticeActions.OEv E v) (SelfDualLatticeActions.Wv E v M)) (β : Fv F v) :
    UnitaryLatticeOrthogonal.SL σ J v L β = SelfDualLatticeActions.sphere v σ J L β := rfl

theorem hasONB_iff (L : Submodule (SelfDualLatticeActions.OEv E v) (SelfDualLatticeActions.Wv E v M)) :
    UnitaryLatticeOrthogonal.HasONB σ J v L ↔ SelfDualLatticeActions.HasOrthonormalBasis v σ J L := by
  refine exists_congr fun b => ?_
  rw [← Matrix.ext_iff]
  refine forall_congr' fun i => forall_congr' fun j => ?_
  rw [Matrix.one_apply]
  exact Iff.rfl

theorem disjoint_span_perpLat (h : IsCMExt F E σ) (hJ : IsHermND σ J)
    (L : Submodule (SelfDualLatticeActions.OEv E v) (SelfDualLatticeActions.Wv E v M)) (x : SelfDualLatticeActions.Wv E v M)
    (hx : IsUnit (qR (Fv F v) σ J x)) :
    Disjoint (Submodule.span (SelfDualLatticeActions.OEv E v) {x}) (SelfDualLatticeActions.perpLat v σ J x L) := by
  rw [Submodule.disjoint_def]
  intro y hy hy'
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
  have h0 : hR (Fv F v) σ J x ((c : SelfDualLatticeActions.Ev E v) • x) = 0 := hy'.1
  rw [hR_smul_right, hR_self _ h hJ, (hx.map _).mul_left_eq_zero] at h0
  show (c : SelfDualLatticeActions.Ev E v) • x = 0
  rw [h0, zero_smul]

theorem unitVectors_iff (h : IsCMExt F E σ) (hJ : IsHermND σ J)
    (L : Submodule (SelfDualLatticeActions.OEv E v) (SelfDualLatticeActions.Wv E v M)) (β : Fv F v) (hβ : IsUnit β) :
    UnitaryLatticeOrthogonal.UnitVectors σ J v L β ↔ SelfDualLatticeActions.UnitVectorClaims v σ J L β := by
  refine and_congr Iff.rfl (and_congr ?_ Iff.rfl)
  refine forall_congr' fun x => forall_congr' fun hx => ?_
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1.symm, disjoint_span_perpLat σ J v h hJ L x (hx.2 ▸ hβ), h2⟩
  · rintro ⟨h1, -, h2⟩
    exact ⟨h1.symm, h2⟩

theorem conclusion_iff (h : IsCMExt F E σ) (hJ : IsHermND σ J)
    (L : Submodule (SelfDualLatticeActions.OEv E v) (SelfDualLatticeActions.Wv E v M)) :
    (UnitaryLatticeOrthogonal.HasONB σ J v L ∧
      (∀ L₁ : Submodule (UnitaryLatticeOrthogonal.OEv F E v) (Fin M → UnitaryLatticeOrthogonal.Ev F E v), UnitaryLatticeOrthogonal.IsSDLat σ J v L₁ →
        ∃ g : HA (Fv F v) σ J, ∀ y, y ∈ L ↔ UnitaryLatticeOrthogonal.act σ J v g y ∈ L₁) ∧
      ∀ β : (v.adicCompletionIntegers F)ˣ,
        UnitaryLatticeOrthogonal.UnitVectors σ J v L ((β : v.adicCompletionIntegers F) : Fv F v)) ↔
    (SelfDualLatticeActions.HasOrthonormalBasis v σ J L ∧
      (∀ L' : Submodule (SelfDualLatticeActions.OEv E v) (SelfDualLatticeActions.Wv E v M), SelfDualLatticeActions.IsSelfDualLat v σ J L' →
        ∃ g : HA (Fv F v) σ J, ∀ y, y ∈ L ↔ SelfDualLatticeActions.act v σ J g y ∈ L') ∧
      ∀ β : (v.adicCompletionIntegers F)ˣ,
        SelfDualLatticeActions.UnitVectorClaims v σ J L ((β : v.adicCompletionIntegers F) : Fv F v)) :=
  and_congr (hasONB_iff σ J v L) (and_congr Iff.rfl (forall_congr' fun β =>
    unitVectors_iff σ J v h hJ L _ (β.isUnit.map (v.adicCompletionIntegers F).subtype)))

end Clauses

theorem selfDualLattices_iff :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.SelfDualLattices ↔ GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeActions.SelfDualLatticeLemmas := by
  refine forall_congr' fun F => forall_congr' fun E => forall_congr' fun _ =>
    forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun _ =>
    forall_congr' fun σ => forall_congr' fun h => forall_congr' fun M => forall_congr' fun J => ?_
  rw [imp.swap]
  refine forall_congr' fun _ => forall_congr' fun hJ => forall_congr' fun v => ?_
  refine imp_congr (unram_iff v) (forall_congr' fun L => ?_)
  exact imp_congr (isSDLat_iff σ J v L) (conclusion_iff σ J v h hJ L)

end GlobalTheory.SelfDualLatticeCompare
