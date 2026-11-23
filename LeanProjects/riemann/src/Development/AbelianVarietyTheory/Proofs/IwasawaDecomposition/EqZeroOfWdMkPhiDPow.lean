import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResEqIff
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial TensorProduct Module GlobalTheory.Pst

namespace GlobalTheory.PstFaithful

theorem exists_idem {LL U D R : Type} [Field LL] [Field U] [AddCommGroup D] [Module LL D]
    (m : U →+* End LL D) (F : Type) [Field F] [Algebra LL F] (τ : U →+* F)
    [CommRing R] [IsSemisimpleRing R] (α : R →+* End LL D) (π : R →+* F) (iL : LL → R) (iU : U → R)
    (h1 : ∀ a, α (iL a) = algebraMap LL (End LL D) a) (h2 : ∀ c, α (iU c) = m c)
    (h3 : ∀ a, π (iL a) = algebraMap LL F a) (h4 : ∀ c, π (iU c) = τ c) :
    ∃ e : R, π e = 1 ∧ ∀ x, letterMk m F τ x = 0 → α e x = 0 := by
  let : Algebra R F := π.toAlgebra
  obtain ⟨q, hq⟩ := exists_isCompl (RingHom.ker π)
  have h1q : (1 : R) ∈ RingHom.ker π ⊔ q := by rw [hq.sup_eq_top]; trivial
  obtain ⟨a, ha, e, he, hae⟩ := Submodule.mem_sup.1 h1q
  have hπe : π e = 1 := by
    have := congrArg π hae
    rwa [map_add, RingHom.mem_ker.1 ha, zero_add, map_one] at this
  have hinj : Function.Injective ((Algebra.linearMap R F) ∘ₗ q.subtype) := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    have : (y : R) ∈ RingHom.ker π ⊓ q := ⟨hy, y.2⟩
    rw [hq.inf_eq_bot] at this
    exact Subtype.ext this
  obtain ⟨Λ, hΛ⟩ := IsSemisimpleModule.extension_property _ hinj q.subtype
  have hΛ1 : Λ 1 = e := by
    rw [← hπe]; exact LinearMap.congr_fun hΛ ⟨e, he⟩
  have hΛm : ∀ r f, Λ (π r * f) = r * Λ f := fun r f => Λ.map_smul r f
  let β : F →ₗ[LL] End LL D :=
    { toFun := fun f => α (Λ f)
      map_add' := fun f g => by rw [map_add, map_add]
      map_smul' := fun a f => by
        rw [Algebra.smul_def, ← h3, hΛm, map_mul, h1, ← Algebra.smul_def]; rfl }
  have hβ : ∀ f x, TensorProduct.lift β (f ⊗ₜ x) = α (Λ f) x := fun _ _ => rfl
  have hker : ∀ y ∈ letterKer m F τ, TensorProduct.lift β y = 0 := by
    intro y hy
    refine Submodule.iSup_induction _ (motive := fun y => TensorProduct.lift β y = 0) hy ?_ ?_ ?_
    · rintro c _ ⟨y, rfl⟩
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul f x =>
        rw [LinearMap.sub_apply, map_sub, LinearMap.baseChange_tmul, LinearMap.smul_apply,
          LinearMap.id_apply, smul_tmul', hβ, hβ, smul_eq_mul, ← h4, hΛm, mul_comm, map_mul, h2,
          End.mul_apply, sub_self]
      | add y z hy hz => rw [map_add, map_add, hy, hz, add_zero]
    · exact map_zero _
    · intro y z hy hz
      rw [map_add, hy, hz, add_zero]
  refine ⟨e, hπe, fun x hx => ?_⟩
  rw [letterMk, ← LinearMap.mem_ker, ker_letterQ] at hx
  rw [← hΛ1, ← hβ]
  exact hker _ hx

variable {l : ℕ} [hl : Fact l.Prime] (LL : FinExt l)

theorem exists_level_tensor (r : ↥(MaximalUnramifiedExtension l) ⊗[ℚ_[l]] ↥LL.1) : ∃ m : ℕ, 0 < m ∧ ¬ l ∣ m ∧
    ∀ f : ↥(MaximalUnramifiedExtension l) →ₐ[ℚ_[l]] ↥(MaximalUnramifiedExtension l), (∀ c : ↥(MaximalUnramifiedExtension l), c ^ m = 1 → f c = c) →
      Algebra.TensorProduct.map f (AlgHom.id ℚ_[l] ↥LL.1) r = r := by
  induction r using TensorProduct.induction_on with
  | zero => exact ⟨1, one_pos, hl.out.not_dvd_one, fun f _ => map_zero _⟩
  | tmul c a =>
    obtain ⟨m, hm, hlm, H⟩ := MemLoc.FrobLaws.exists_level c.2
    refine ⟨m, hm, hlm, fun f hf => ?_⟩
    obtain ⟨g, hg⟩ := MemLoc.FrobLaws.exists_ext f
    have h := H g 1 fun ζ hζ => by
      let z : ↥(MaximalUnramifiedExtension l) := ⟨ζ, IntermediateField.subset_adjoin _ _ ⟨m, hm, hlm, hζ⟩⟩
      exact (hg z).trans (congrArg Subtype.val (hf z (Subtype.ext hζ)))
    have h' : f c = c := Subtype.ext ((hg c).symm.trans h)
    rw [Algebra.TensorProduct.map_tmul, h', AlgHom.id_apply]
  | add x y hx hy =>
    obtain ⟨m, hm, hlm, ha⟩ := hx
    obtain ⟨n, hn, hln, hb⟩ := hy
    refine ⟨m * n, Nat.mul_pos hm hn, fun hd => ((hl.out.dvd_mul).1 hd).elim hlm hln, fun f H => ?_⟩
    rw [map_add, ha f fun ζ hζ => H ζ (by rw [pow_mul, hζ, one_pow]),
      hb f fun ζ hζ => H ζ (by rw [mul_comm, pow_mul, hζ, one_pow])]

theorem exists_algHom_ker (U R Ω : Type) [Field U] [CommRing R] [Algebra U R] [Module.Finite U R] [Field Ω]
    [IsAlgClosed Ω] [Algebra U Ω] (I : Ideal R) (hI : I ≠ ⊤) : ∃ ψ : R →ₐ[U] Ω, ∀ r ∈ I, ψ r = 0 := by
  obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal I hI
  let := Ideal.Quotient.field M
  let ψ₀ : (R ⧸ M) →ₐ[U] Ω := IsAlgClosed.lift
  refine ⟨ψ₀.comp (Ideal.Quotient.mkₐ _ M), fun r hr => ?_⟩
  have : Ideal.Quotient.mkₐ U M r = 0 := Ideal.Quotient.eq_zero_iff_mem.2 (hIM hr)
  rw [AlgHom.comp_apply, this, map_zero]

theorem exists_restrict (g : GQ l) : ∃ t : ↥(MaximalUnramifiedExtension l) →ₐ[ℚ_[l]] ↥(MaximalUnramifiedExtension l), ∀ c, (t c : Om l) = g c := by
  have hle : (MaximalUnramifiedExtension l).map (g : Om l →ₐ[ℚ_[l]] Om l) ≤ MaximalUnramifiedExtension l := by
    unfold MaximalUnramifiedExtension
    rw [IntermediateField.adjoin_map]
    apply IntermediateField.adjoin.mono
    rintro _ ⟨x, ⟨m, hm, hlm, hx⟩, rfl⟩
    exact ⟨m, hm, hlm, by rw [← map_pow, hx, map_one]⟩
  exact ⟨((g : Om l →ₐ[ℚ_[l]] Om l).comp (MaximalUnramifiedExtension l).val).codRestrict
    (MaximalUnramifiedExtension l).toSubalgebra (fun x => hle ⟨x, x.2, rfl⟩), fun _ => rfl⟩

theorem exists_extend (f : ↥LL.1 →ₐ[ℚ_[l]] Om l) : ∃ g : GQ l, ∀ a : ↥LL.1, g a = f a :=
  ⟨AlgEquiv.ofBijective (f.liftNormal (Om l)) (Algebra.IsAlgebraic.algHom_bijective _),
    fun a => f.liftNormal_commutes (Om l) a⟩

theorem exists_translate (I : Ideal (↥(MaximalUnramifiedExtension l) ⊗[ℚ_[l]] ↥LL.1)) (hI : I ≠ ⊤)
    (e : ↥(MaximalUnramifiedExtension l) ⊗[ℚ_[l]] ↥LL.1) (he : Algebra.TensorProduct.productMap (MaximalUnramifiedExtension l).val LL.1.val e ≠ 0) :
    ∃ (n : ℕ) (r : ↥(MaximalUnramifiedExtension l) ⊗[ℚ_[l]] ↥LL.1), r ∉ I ∧
      Algebra.TensorProduct.map (frobUr l ^ n) (AlgHom.id ℚ_[l] ↥LL.1) r = e := by
  have := LL.2
  obtain ⟨ψ, hψ⟩ := exists_algHom_ker ↥(MaximalUnramifiedExtension l) _ (Om l) I hI
  obtain ⟨g, hg'⟩ := exists_extend LL
    ((ψ.restrictScalars ℚ_[l]).comp Algebra.TensorProduct.includeRight)
  have hg : ∀ a : ↥LL.1, g a = ψ (1 ⊗ₜ a) := hg'
  obtain ⟨t, ht⟩ := exists_restrict g
  have key : ∀ r, ψ (Algebra.TensorProduct.map t (AlgHom.id ℚ_[l] ↥LL.1) r) =
      g (Algebra.TensorProduct.productMap (MaximalUnramifiedExtension l).val LL.1.val r) := by
    intro r
    induction r using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul c a =>
      have e1 : t c ⊗ₜ[ℚ_[l]] a = t c • ((1 : ↥(MaximalUnramifiedExtension l)) ⊗ₜ[ℚ_[l]] a) := by
        rw [smul_tmul', smul_eq_mul, mul_one]
      rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, e1, map_smul, ← hg,
        Algebra.TensorProduct.productMap_apply_tmul, map_mul]
      exact congrArg (· * g a) (ht c)
    | add x y hx hy => simp only [map_add, hx, hy]
  obtain ⟨m, hm, hlm, H⟩ := exists_level_tensor LL e
  obtain ⟨n, hn⟩ := MemLoc.FrobLaws.gal_root g⁻¹ hm hlm
  refine ⟨n, Algebra.TensorProduct.map t (AlgHom.id ℚ_[l] ↥LL.1) e, fun h => he ?_, ?_⟩
  · have h0 := hψ _ h
    rw [key] at h0
    exact g.injective (h0.trans (map_zero g).symm)
  · rw [← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp, AlgHom.id_comp]
    refine H _ fun c hc => ?_
    have hc' : t c ^ m = 1 := by rw [← map_pow, hc, map_one]
    rw [AlgHom.comp_apply, frobUr_pow_root n _ m hm hlm hc', ← map_pow]
    apply Subtype.ext
    rw [ht]
    have := hn c (congrArg Subtype.val hc)
    rw [SubmonoidClass.coe_pow, ← this, ← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]

theorem exists_action {k L U D : Type} [Field k] [Field L] [Field U] [Algebra k L] [Algebra k U]
    [AddCommGroup D] [Module L D] (m : U →+* End L D)
    (hm : ∀ c : k, m (algebraMap k U c) = algebraMap L _ (algebraMap k L c)) :
    ∃ α : U ⊗[k] L →+* End L D, ∀ c a, α (c ⊗ₜ a) = m c * algebraMap L _ a := by
  let : Module k D := Module.compHom D (algebraMap k L)
  have : IsScalarTower k L D := .of_algebraMap_smul fun _ _ => rfl
  let mU : U →ₐ[k] End L D := { m with commutes' := hm }
  exact ⟨(Algebra.TensorProduct.lift mU (IsScalarTower.toAlgHom k L (End L D))
    fun c a => (Algebra.commutes a (m c)).symm).toRingHom, fun _ _ => rfl⟩

theorem eq_zero_of_translate {k L U D : Type} [Field k] [Field L] [Field U] [Algebra k L] [Algebra k U]
    [AddCommGroup D] [Module L D] {m : U →+* End L D} (α : U ⊗[k] L →+* End L D)
    (hα : ∀ c a, α (c ⊗ₜ a) = m c * algebraMap L _ a) (σ : ℕ → U →ₐ[k] U) (φ : ℕ → End L D)
    (hinj : ∀ n, Function.Injective (φ n)) (hφ : ∀ n c, φ n * m c = m (σ n c) * φ n) (e : U ⊗[k] L) (x : D)
    (hx : ∀ n, α e (φ n x) = 0)
    (he : ∀ I : Ideal (U ⊗[k] L), I ≠ ⊤ →
      ∃ n r, r ∉ I ∧ Algebra.TensorProduct.map (σ n) (AlgHom.id k L) r = e) : x = 0 := by
  let I : Ideal (U ⊗[k] L) :=
    { carrier := {r | α r x = 0}
      add_mem' := fun {a b} (ha : α a x = 0) (hb : α b x = 0) => show α (a + b) x = 0 by
        rw [map_add, LinearMap.add_apply, ha, hb, add_zero]
      zero_mem' := show α 0 x = 0 by rw [map_zero, LinearMap.zero_apply]
      smul_mem' := fun a b (hb : α b x = 0) => show α (a * b) x = 0 by
        rw [map_mul, End.mul_apply, hb, map_zero] }
  by_contra h0
  have hI : I ≠ ⊤ := fun h => h0 (by
    have : α 1 x = 0 := (Ideal.eq_top_iff_one I).1 h
    rwa [map_one] at this)
  obtain ⟨n, r, hr, hre⟩ := he I hI
  have semi : ∀ s, φ n * α s = α (Algebra.TensorProduct.map (σ n) (AlgHom.id k L) s) * φ n := by
    intro s
    induction s using TensorProduct.induction_on with
    | zero => simp
    | tmul c a =>
      rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, hα, hα, ← mul_assoc, hφ, mul_assoc,
        mul_assoc, Algebra.commutes]
    | add y z hy hz => rw [map_add, map_add, map_add, mul_add, add_mul, hy, hz]
  refine hr (?_ : α r x = 0)
  have h1 := LinearMap.congr_fun (semi r) x
  rw [End.mul_apply, End.mul_apply, hre] at h1
  exact hinj n (h1.trans ((hx n).trans (map_zero _).symm))

theorem isSemisimpleRing_tensor : IsSemisimpleRing (↥(MaximalUnramifiedExtension l) ⊗[ℚ_[l]] ↥LL.1) := by
  have := LL.2
  have : Algebra.FormallyUnramified ℚ_[l] ↥LL.1 := Algebra.FormallyUnramified.of_isSeparable _ _
  have : IsReduced (↥(MaximalUnramifiedExtension l) ⊗[ℚ_[l]] ↥LL.1) :=
    Algebra.FormallyUnramified.isReduced_of_field ↥(MaximalUnramifiedExtension l) _
  have : IsArtinianRing (↥(MaximalUnramifiedExtension l) ⊗[ℚ_[l]] ↥LL.1) := IsArtinianRing.of_finite ↥(MaximalUnramifiedExtension l) _
  exact IsArtinianRing.isSemisimpleRing_of_isReduced _

theorem eq_zero_of_wdMk_phiD_pow (l : ℕ) [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ) (K LL : FinExt l)
    (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V]
    (ρ : Representation ↥LL.1 ↥(GK K) V) (x : ↥(Dpst P ρ))
    (hx : ∀ n : ℕ, wdMk P ι ρ ((phiD P ρ ^ n) x) = 0) : x = 0 := by
  have := isSemisimpleRing_tensor LL
  obtain ⟨α, hα⟩ := exists_action (k := ℚ_[l]) (mulD P ρ) fun c =>
    LinearMap.ext fun y => Subtype.ext (by
      have : mulV P ↥LL.1 V (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) c) =
          algebraMap ↥LL.1 _ (algebraMap ℚ_[l] ↥LL.1 c) :=
        end_ext P fun v b => by
          rw [mulV_tmul, ← IsScalarTower.algebraMap_apply, ← Algebra.smul_def, tmul_smul,
            Module.algebraMap_end_apply, algebraMap_smul]
      exact LinearMap.congr_fun this y.1)
  let π₀ := Algebra.TensorProduct.productMap (MaximalUnramifiedExtension l).val LL.1.val
  have hπ₀ : ∀ (c : ↥(MaximalUnramifiedExtension l)) (a : ↥LL.1), π₀ (c ⊗ₜ a) = (c : Om l) * a := fun _ _ => rfl
  let := algC ι LL
  obtain ⟨e, he, hk⟩ := exists_idem (mulD P ρ) ℂ (urC ι) α (ι.toRingHom.comp π₀.toRingHom)
    (fun a => 1 ⊗ₜ a) (fun c => c ⊗ₜ 1) (fun a => (hα 1 a).trans (by rw [map_one, one_mul]))
    (fun c => (hα c 1).trans (by rw [map_one, mul_one]))
    (fun a => congrArg ι ((hπ₀ 1 a).trans (one_mul (a : Om l))))
    (fun c => congrArg ι ((hπ₀ c 1).trans (mul_one (c : Om l))))
  have he0 : π₀ e ≠ 0 := fun h => by
    have h' : ι (π₀ e) = 1 := he
    rw [h, map_zero] at h'
    exact zero_ne_one h'
  refine eq_zero_of_translate α hα (fun n => frobUr l ^ n) (fun n => phiD P ρ ^ n) (fun n => ?_)
    (phiD_pow_mulD P ρ) e x (fun n => hk _ (hx n)) fun I hI => exists_translate LL I hI e he0
  rw [End.coe_pow]
  exact (phiD_injective P ρ).iterate n

end GlobalTheory.PstFaithful
