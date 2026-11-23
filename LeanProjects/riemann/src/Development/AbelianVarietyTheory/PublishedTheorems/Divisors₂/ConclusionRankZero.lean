import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
import Development.AbelianVarietyTheory.Definitions.Divisors.AdelicAdmissibleSmul
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ConclRankZeroRight

noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.Published.HoweDualityFiniteModel

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {X : Spc F E n} {W : Spc F E d}

theorem thetaSub_top (om : Rep σ X W) (v : Pl F) : ThetaSub om v (SB _) :=
  ⟨Submodule.span_le.2 fun _ ⟨_, _, _, h, _, h₁, _, e⟩ => e ▸ (SB _).sub_mem h₁ h, le_rfl, fun _ _ _ _ _ h _ => h⟩

theorem acts_zero {κ : Type} [Fintype κ] (v : Pl F) (T : Module.End ℂ ((κ → AF F) → ℂ)) (φ₁ : (κ → Fv F v) → ℂ)
    (hs : Function.Surjective (evFin F v)) (h : Acts (evFin F v) T 0 φ₁) : φ₁ = 0 := by
  have e : tens (evFin F v) (0 : (κ → Fv F v) → ℂ) (1 : (κ → AF F) → ℂ) = 0 := by funext x; simp [tens]
  have := h 1 ⟨fun _ _ _ => rfl, e ▸ (schA F κ).zero_mem⟩
  rw [e, map_zero] at this
  funext y
  choose s hs using hs
  have := congrFun this (fun i => s (y i))
  simpa [tens, hs] using this.symm

theorem conclusion_rank_zero [IsEmpty (Fin n × Fin d)] (om : Rep σ X W) (v : Pl F) :
    (∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ _), StrictMono N → (∀ i, ThetaSub om v (N i)) → m ≤ L) ∧
      ∀ N N', ThetaSub om v N → ThetaSub om v N' → N ≠ SB _ → N' ≠ SB _ → N ⊔ N' ≠ SB _ := by
  have hf : Module.finrank ℂ ((Fin n × Fin d → Fv F v) → ℂ) = 1 := by
    rw [Module.finrank_fintype_fun_eq_card]; simp
  haveI : IsSimpleOrder (Submodule ℂ ((Fin n × Fin d → Fv F v) → ℂ)) := is_simple_module_of_finrank_eq_one hf
  refine ⟨⟨2, fun m N hN _ => ?_⟩, fun N N' h h' hN hN' => ?_⟩
  · classical
    simpa using
      (Fintype.card_le_of_injective (IsSimpleOrder.equivBool ∘ N)
        (IsSimpleOrder.equivBool.injective.comp hN.injective))
  · have b : ∀ N, ThetaSub om v N → N ≠ SB _ → N = ⊥ := fun N h hN =>
      (eq_bot_or_eq_top N).resolve_right fun e => hN (le_antisymm h.2.1 (e ▸ le_top))
    rw [b N h hN, bot_sup_eq]; exact hN'

section Triv

variable {R : Type} [CommRing R] [Invertible (2 : R)] {S : Type} [CommRing S] [Algebra R S] {c : S →ₐ[R] S}
  {α β κ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ]
  [TopologicalSpace R] [TopologicalSpace S] [IsModuleTopology R S] {C : TestClass R}

omit [IsModuleTopology R S] [DecidableEq α] in
theorem split_one (ψ : AddChar R ℂ) {ξ : S} {JA : Matrix α α S} {JB : Matrix β β S} [IsEmpty κ]
    (co : Darboux (symp c ξ JA JB) κ) : IsUSplitting C ψ co (actB c) (1 : UG c JB →* Module.End ℂ ((κ → R) → ℂ)) := by
  refine ⟨⟨fun g φ h => h, fun g w φ _ => ?_, fun g l h => h⟩, fun μ _ g φ _ => rfl, fun l _ φ _ => continuous_const (y := l φ)⟩
  funext x
  simp [Darboux.rho, schr, dotProduct, Subsingleton.elim (x + _) x]

omit [DecidableEq α] in
theorem weilB_one (ψ : AddChar R ℂ) {ξ : S} {JA : Matrix α α S} {JB : Matrix β β S} [IsEmpty κ] [IsEmpty (α × β)]
    (co : Darboux (symp c ξ JA JB) κ) : IsUWeilB c C ψ ξ JA JB co 1 1 := by
  haveI : IsEmpty (α × (β ⊕ β)) := ⟨fun ⟨a, b⟩ => b.elim (fun b => isEmptyElim (a, b)) fun b => isEmptyElim (a, b)⟩
  refine ⟨split_one ψ co, GlobalTheory.WeilM.SiegelModel.darbZero ξ JA (dbl JB) _, 1, fun _ _ => Subsingleton.elim _ _,
    ⟨isLagr_diagCols c JB, split_one ψ _, fun l _ _ p t hp φ _ => ?_⟩, fun g gd h φ₁ _ φ₂ _ => rfl⟩
  rcases isEmpty_prod.1 (inferInstance : IsEmpty (α × β)) with h | h
  · simp
  · have : Matrix.GeneralLinearGroup.det t = 1 := by ext; simp
    simp [this]

end Triv

theorem hyps_rank_zero (X : Spc F E 0) (W : Spc F E d) (hd : Even d) (ψ : AddChar (AF F) ℂ) :
    ∃ (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W),
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX 0 ∧
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d ∧ IsHecke F E χX ∧ IsHecke F E χW ∧
      M.IsWeil ψ χX χW om := by
  refine ⟨⟨GlobalTheory.WeilM.SiegelModel.darbZero _ _ _ _, fun _ => 0, 0, ∅⟩, 1, 1, 1, fun a => by rw [pow_zero, ite_self]; rfl, fun a => by rw [hd.neg_one_pow, ite_self]; rfl,
    ⟨continuous_const, fun _ => rfl⟩, ⟨continuous_const, fun _ => rfl⟩, weilB_one ψ _,
    ⟨GlobalTheory.WeilM.SiegelModel.darbZero _ _ _ _, fun _ => Subsingleton.elim _ _, weilB_one ψ _⟩, fun l _ φ _ => continuous_const (y := l φ)⟩

theorem skew_two : ∃ W : Spc F E 2, (∀ i j, σ (W.J j i) = -W.J i j) ∧ W.J.det ≠ 0 :=
  ⟨⟨!![0, 1; -1, 0], ⊥, fun _ => 1, fun _ => 1⟩, fun i j => by fin_cases i <;> fin_cases j <;> simp, by simp⟩

section LocalTests

open scoped TensorProduct

variable {G H Y V T : Type} [Group G] [Group H] [TopologicalSpace Y] [AddCommGroup V] [Module ℂ V] [AddCommGroup T]
  [Module ℂ T]

theorem triv_of_fixed (π : Representation ℂ G V) (hπ : π.IsIrreducible) (v : V) (hv : v ≠ 0) (h : ∀ g, π g v = v) :
    Module.finrank ℂ V = 1 ∧ ∀ g w, π g w = w := by
  let N : Subrepresentation π := ⟨ℂ ∙ v, fun g w hw => by
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hw
    rw [map_smul, h]; exact hw⟩
  have hN : N = ⊤ := (eq_bot_or_eq_top N).resolve_left fun e => hv (by
    have : v ∈ N.toSubmodule := Submodule.mem_span_singleton_self v
    rw [e] at this; exact this)
  have hs : ∀ w, ∃ a : ℂ, a • v = w := fun w => Submodule.mem_span_singleton.1 (by
    show w ∈ N.toSubmodule
    rw [hN]; trivial)
  exact ⟨(finrank_eq_one_iff_of_nonzero' v hv).2 hs, fun g w => by obtain ⟨a, rfl⟩ := hs w; rw [map_smul, h]⟩

theorem fixed_of_tensor (π : Representation ℂ G V) (x : V ⊗[ℂ] T) (hx : x ≠ 0)
    (h : ∀ g, TensorProduct.map (π g) LinearMap.id x = x) : ∃ v : V, v ≠ 0 ∧ ∀ g, π g v = v := by
  classical
  let b := Module.Free.chooseBasis ℂ T
  have hx' : TensorProduct.equivFinsuppOfBasisRight b x ≠ 0 := by simpa using hx
  obtain ⟨i, hi⟩ := Finsupp.ne_iff.1 hx'
  refine ⟨_, hi, fun g => ?_⟩
  have : ∀ y : V ⊗[ℂ] T, π g (TensorProduct.equivFinsuppOfBasisRight b y i) =
      TensorProduct.equivFinsuppOfBasisRight b (TensorProduct.map (π g) LinearMap.id y) i := fun y => by
    induction y with
    | zero => simp
    | tmul a t => simp
    | add a t ha ht => simp [ha, ht]
  rw [this, h]

theorem irr_trivial (H : Type) [Group H] : (Representation.trivial ℂ H ℂ).IsIrreducible := by
  haveI : IsSimpleOrder (Submodule ℂ ℂ) := is_simple_module_of_finrank_eq_one (K := ℂ) (Module.finrank_self ℂ)
  refine { exists_pair_ne := ⟨⊥, ⊤, fun e => ?_⟩, eq_bot_or_eq_top := fun N => ?_ }
  · exact bot_ne_top (α := Submodule ℂ ℂ) (congrArg Subrepresentation.toSubmodule e)
  · exact (eq_bot_or_eq_top N.toSubmodule).imp (fun e => Subrepresentation.toSubmodule_injective e)
      fun e => Subrepresentation.toSubmodule_injective e

theorem howeFor_point [TopologicalSpace G] [TopologicalSpace H] [Unique Y] :
    HoweDualityFor (1 : G × H →* Module.End ℂ (Y → ℂ)) := by
  let φ₀ : SB Y := ⟨fun _ => 1, IsLocallyConstant.const 1, HasCompactSupport.of_compactSpace _⟩
  have hφ : ∀ φ : SB Y, ∃ a : ℂ, φ = a • φ₀ := fun φ => ⟨φ.1 default, by
    ext y; simp [φ₀, Subsingleton.elim y default]⟩
  have ne : ∀ {M : Type} [AddCommGroup M] [Module ℂ M] (f : SB Y →ₗ[ℂ] M), f ≠ 0 → f φ₀ ≠ 0 := fun f hf h =>
    hf (LinearMap.ext fun φ => by obtain ⟨a, rfl⟩ := hφ φ; rw [map_smul, h]; simp)
  have key : ∀ {V T : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup T] [Module ℂ T] (π : Representation ℂ G V)
      (τ : Representation ℂ H T), π.IsIrreducible → τ.IsIrreducible → ∀ f : SB Y →ₗ[ℂ] V ⊗[ℂ] T,
      IsPairHom 1 π τ f → f ≠ 0 → (Module.finrank ℂ V = 1 ∧ ∀ g w, π g w = w) ∧ Module.finrank ℂ T = 1 := by
    intro V T _ _ _ _ π τ hπ hτ f hf h0
    constructor
    · obtain ⟨v, hv, h⟩ := fixed_of_tensor π _ (ne f h0) fun g => by
        have := hf g 1 φ₀ φ₀ rfl
        rw [map_one] at this
        exact this.symm
      exact triv_of_fixed π hπ v hv h
    · obtain ⟨v, hv, h⟩ := fixed_of_tensor τ (TensorProduct.comm ℂ V T (f φ₀)) (by simpa using ne f h0) fun g => by
        have := hf 1 g φ₀ φ₀ rfl
        rw [map_one] at this
        conv_rhs => rw [this]
        exact TensorProduct.map_comm _ _ _
      exact (triv_of_fixed τ hτ v hv h).1
  intro V _ _ π hπ _
  refine ⟨?_, fun T _ _ τ hτ _ f hf h0 => ⟨fun f' _ => ?_, fun V' _ _ π' hπ' _ f' hf' h0' => ?_⟩⟩
  · by_cases hex : ∃ f : SB Y →ₗ[ℂ] V, IsLeftHom (1 : G × H →* Module.End ℂ (Y → ℂ)) π f ∧ f ≠ 0
    · obtain ⟨f, hf, h0⟩ := hex
      obtain ⟨h1, h2⟩ := triv_of_fixed π hπ _ (ne f h0) fun g => (hf g φ₀ φ₀ rfl).symm
      have hirr := irr_trivial H
      refine ⟨ℂ, inferInstance, inferInstance, Representation.trivial ℂ H ℂ,
        (TensorProduct.rid ℂ V).symm.toLinearMap ∘ₗ f, ⟨fun g h φ φ₁ e => ?_, ?_, fun φ => ?_⟩, fun v => by simp, ?_,
        fun N N' a b => ?_⟩
      · obtain rfl : φ₁ = φ := Subtype.ext e
        simp [h2]
      · refine Function.Surjective.comp (g := (TensorProduct.rid ℂ V).symm) (f := f) (TensorProduct.rid ℂ V).symm.surjective fun w => ?_
        obtain ⟨a, rfl⟩ := (finrank_eq_one_iff_of_nonzero' _ (ne f h0)).1 h1 w
        exact ⟨a • φ₀, map_smul _ _ _⟩
      · refine ⟨fun h f' _ => ?_, fun h => by simp [h f hf]⟩
        have h3 : f φ = 0 := (TensorProduct.rid ℂ V).symm.map_eq_zero_iff.1 h
        obtain ⟨a, rfl⟩ := hφ φ
        rw [map_smul] at h3 ⊢
        rw [(smul_eq_zero.1 h3).resolve_right (ne f h0), zero_smul]
      · haveI := (Representation.irreducible_iff_isSimpleModule_asModule _).1 hirr
        exact isFiniteLength_iff_isNoetherian_isArtinian.2 ⟨inferInstance, inferInstance⟩
      · rw [(eq_bot_or_eq_top N).resolve_right a.1, (eq_bot_or_eq_top N').resolve_right b.1]
    · push Not at hex
      refine ⟨PUnit, inferInstance, inferInstance, Representation.trivial ℂ H PUnit, 0,
        ⟨fun g h φ φ₁ e => by simp, fun x => ⟨0, Subsingleton.elim _ _⟩, fun φ => ⟨fun _ f hf => by simp [hex f hf], fun _ => rfl⟩⟩,
        fun v => by simp, ?_, fun N N' a b => Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _)⟩
      haveI : Subsingleton (Representation.trivial ℂ H PUnit).asModule := inferInstanceAs (Subsingleton PUnit)
      exact IsFiniteLength.of_subsingleton
  · obtain ⟨⟨h1, -⟩, h2⟩ := key π τ hπ hτ f hf h0
    have h3 : Module.finrank ℂ (V ⊗[ℂ] T) = 1 := by rw [Module.finrank_tensorProduct, h1, h2]
    obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_nonzero' _ (ne f h0)).1 h3 (f' φ₀)
    exact ⟨a, LinearMap.ext fun φ => by obtain ⟨b, rfl⟩ := hφ φ; rw [map_smul, map_smul, ← ha]; rfl⟩
  · obtain ⟨⟨h1, h2⟩, -⟩ := key π τ hπ hτ f hf h0
    obtain ⟨⟨h1', h2'⟩, -⟩ := key π' τ hπ' hτ f' hf' h0'
    haveI := Module.finite_of_finrank_eq_succ h1
    haveI := Module.finite_of_finrank_eq_succ h1'
    exact ⟨Representation.Equiv.mk (LinearEquiv.ofFinrankEq V V' (h1.trans h1'.symm)) fun g => LinearMap.ext fun w => by
      simp [h2, h2']⟩

theorem not_howeFor_two : ¬ HoweDualityFor (1 : Unit × Unit →* Module.End ℂ (Bool → ℂ)) := by
  intro h
  have hirr := irr_trivial Unit
  let ev : Bool → (SB Bool →ₗ[ℂ] ℂ ⊗[ℂ] ℂ) := fun b =>
    (TensorProduct.rid ℂ ℂ).symm.toLinearMap ∘ₗ LinearMap.proj b ∘ₗ (SB Bool).subtype
  have hp : ∀ b, IsPairHom (1 : Unit × Unit →* Module.End ℂ (Bool → ℂ)) (Representation.trivial ℂ Unit ℂ)
      (Representation.trivial ℂ Unit ℂ) (ev b) := fun b g h φ φ₁ e => by
    obtain rfl : φ₁ = φ := Subtype.ext e
    simp [ev]
  let s : Bool → SB Bool := fun b => ⟨Pi.single b 1, IsLocallyConstant.of_discrete _, HasCompactSupport.of_compactSpace _⟩
  obtain ⟨a, ha⟩ := ((h ℂ _ hirr ⟨fun v => isOpen_discrete _, fun _ _ _ => inferInstance⟩).2 ℂ _ hirr
    (fun v => isOpen_discrete _) (ev true) (hp _) (fun e => by
      have := congrArg (TensorProduct.rid ℂ ℂ) (LinearMap.congr_fun e (s true))
      simp [ev, s] at this)).1 (ev false) (hp _)
  have := congrArg (TensorProduct.rid ℂ ℂ) (LinearMap.congr_fun ha (s false))
  simp [ev, s] at this

theorem unitary_rank_zero (K : Type) [Field K] [CharZero K] [Invertible (2 : K)] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (e : K) [Fact (∀ r : K, r ^ 2 ≠ e + 0 * r)] :
    ∃ (_ : TopologicalSpace (QuadraticAlgebra K e 0)) (_ : IsModuleTopology K (QuadraticAlgebra K e 0))
      (c : QuadraticAlgebra K e 0 →ₐ[K] QuadraticAlgebra K e 0) (δ : QuadraticAlgebra K e 0) (ψ : AddChar K ℂ)
      (JA : Matrix (Fin 0) (Fin 0) (QuadraticAlgebra K e 0)) (JB : Matrix (Fin 2) (Fin 2) (QuadraticAlgebra K e 0))
      (co : Darboux (symp c 1 JA JB) Empty) (om : UG c JA × UG c JB →* Module.End ℂ ((Empty → K) → ℂ)),
      IsQuad c δ ∧ Continuous ψ ∧ (∀ t, ‖ψ t‖ = 1) ∧ ψ ≠ 1 ∧ IsHerm c JA ∧ (∀ i j, c (1 * JB j i) = -(1 * JB i j)) ∧
      JB.det ≠ 0 ∧ ResEtaPow (R := K) ⊥ (1 : (QuadraticAlgebra K e 0)ˣ →* Circle) 0 ∧
      ResEtaPow (R := K) ⊥ (1 : (QuadraticAlgebra K e 0)ˣ →* Circle) 2 ∧ IsUWeilPair c (sbClass K) ψ 1 JA JB co 1 1 om ∧
      HoweDualityFor om ∧ HoweDualityFor (om.comp (MulEquiv.prodComm (M := UG c JB) (N := UG c JA)).toMonoidHom) := by
  obtain ⟨t, m, c, δ, -, ψ, -, hq, -, h1, h2, h3, -, -⟩ := GlobalTheory.SplitUnitary.Model.isQuad_isHerm_continuous_resEtaPow K e 0
  refine ⟨t, m, c, δ, ψ, 1, !![0, 1; -1, 0], GlobalTheory.WeilM.SiegelModel.darbZero _ _ _ _, 1, hq, h1, h2, h3,
    ⟨fun i => i.elim0, by simp⟩, fun i j => by fin_cases i <;> fin_cases j <;> simp, by simp, fun a => by simp,
    fun a => by simp, ⟨weilB_one ψ _, ⟨GlobalTheory.WeilM.SiegelModel.darbZero _ _ _ _, fun _ => Subsingleton.elim _ _, weilB_one ψ _⟩,
      fun l _ φ _ => continuous_const (y := l φ)⟩, howeFor_point, ?_⟩
  rw [MonoidHom.one_comp]
  exact howeFor_point

end LocalTests

end GlobalTheory.Published.HoweDualityFiniteModel

end
