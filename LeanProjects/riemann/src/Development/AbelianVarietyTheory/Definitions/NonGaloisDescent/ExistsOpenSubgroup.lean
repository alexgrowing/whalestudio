import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoeffRingsHaveRootsOfUnity
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsLabOfOrder
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LabelSettingTameGenerator
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlocksUnique

noncomputable section

namespace GlobalTheory.PendOf.Model

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open Polynomial Module GlobalTheory.WeilDeligne Formalism.CyclotomicNorms

section Local

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}

omit [IsAlgClosure E Ω] in

theorem exists_open_subgroup {S : Set (Ine (F := E) A)} (hS : IsOpen S) (h1 : 1 ∈ S) :
    ∃ U : Subgroup (G E Ω), IsOpen (U : Set (G E Ω)) ∧ ∀ σ : Ine (F := E) A, (σ : G E Ω) ∈ U → σ ∈ S := by
  obtain ⟨V, hV, rfl⟩ := isOpen_induced_iff.mp hS
  obtain ⟨K, hK, hKV⟩ := (krullTopology_mem_nhds_one_iff E Ω V).mp (hV.mem_nhds h1)
  exact ⟨K.fixingSubgroup, K.fixingSubgroup_isOpen, fun σ hσ => hKV hσ⟩

def IsTm (χ : Ine (F := E) A →* ℂˣ) : Prop :=
  IsOpen {σ | χ σ = 1} ∧ ∀ σ : Ine (F := E) A, (σ : G E Ω) ∈ Wild E A → χ σ = 1

theorem IsTm.eq_one {χ : Ine (F := E) A →* ℂˣ} (hχ : IsTm χ) {γ : G E Ω} (hγ : TameGenAt A γ)
    (h1 : χ ⟨γ, hγ.1⟩ = 1) (σ : Ine (F := E) A) : χ σ = 1 := by
  let K : Subgroup (Ine (F := E) A) := χ.ker
  have hK : IsClosed ((K.map (Ine (F := E) A).subtype : Subgroup (G E Ω)) : Set (G E Ω)) :=
    (isClosed_Ine A).isClosedEmbedding_subtypeVal.isClosedMap _ (K.isClosed_of_isOpen hχ.1)
  have hle : Subgroup.closure (insert γ (Wild E A : Set (G E Ω))) ≤
      K.map (Ine (F := E) A).subtype := by
    rw [Subgroup.closure_le]
    rintro u (rfl | hu)
    · exact ⟨⟨u, hγ.1⟩, h1, rfl⟩
    · exact ⟨⟨u, Wild_le_Ine hu⟩, hχ.2 _ hu, rfl⟩
  obtain ⟨u, hu, e⟩ := closure_minimal (SetLike.coe_subset_coe.mpr hle) hK (hγ.2 σ.2)
  rwa [← Subtype.ext (a1 := u) (a2 := σ) e]

omit [IsAlgClosure E Ω] in
theorem IsTm.of_le {χ χ' ψ : Ine (F := E) A →* ℂˣ} (h : IsTm χ) (h' : IsTm χ')
    (hle : ∀ σ, χ σ = 1 → χ' σ = 1 → ψ σ = 1) : IsTm ψ :=
  ⟨Subgroup.isOpen_mono (H₁ := χ.ker ⊓ χ'.ker) (H₂ := ψ.ker) (fun σ hσ => hle σ hσ.1 hσ.2) (h.1.inter h'.1),
    fun σ hσ => hle σ (h.2 σ hσ) (h'.2 σ hσ)⟩

theorem exists_isTm {g : ℕ} [Fact g.Prime] (h : IsPlaceOver A w) (hw : normV w = g) {γ : G E Ω}
    (hγ : TameGenAt A γ) {m : ℕ} (hm : 0 < m) (hc : m.Coprime g) {z : ℂ} (hz : z ^ m = 1) :
    ∃ χ : Ine (F := E) A →* ℂˣ, IsTm χ ∧ (χ ⟨γ, hγ.1⟩ : ℂ) = z := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  obtain ⟨ϖ, h1, h2⟩ := SetLike.exists_of_lt
    (Ideal.pow_lt_self w.asIdeal w.ne_bot w.isPrime.ne_top 2 le_rfl)
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap E Ω (ϖ : E)) hm
  have h0 : x ≠ 0 := by
    rintro rfl
    rw [zero_pow hm.ne', eq_comm, map_eq_zero, RingOfIntegers.coe_eq_zero_iff] at hx
    exact h2 (hx ▸ zero_mem _)
  obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
  let := φ.toAlgebra
  have : Algebra.IsAlgebraic E Ω := IsAlgClosure.isAlgebraic
  let ι : Ω →+* ℂ := (IsAlgClosed.lift (R := E) (M := ℂ) (S := Ω)).toRingHom
  have hpow : ∀ u : G E Ω, (u x / x) ^ m = 1 := fun u => by
    rw [div_pow, ← map_pow, hx, AlgEquiv.commutes, ← hx, div_self (pow_ne_zero _ h0)]
  have hfix : ∀ (σ : Ine (F := E) A) (ζ : Ω), ζ ^ m = 1 → (σ : G E Ω) ζ = ζ := fun σ ζ hζ => by
    have hv : A.valuation ζ = 1 := by
      have := congrArg A.valuation hζ
      rw [map_pow, map_one] at this
      exact (pow_eq_one_iff_of_nonneg zero_le hm.ne').mp this
    have hζ0 : ζ ≠ 0 := by rintro rfl; simp at hv
    have h3 : A.valuation ((σ : G E Ω) ζ - ζ) < 1 := σ.2.2 ζ hv.le
    have h4 : (σ : G E Ω) ζ / ζ = 1 := LabModel.eq_one_of_cong h hw hc
      (by rw [div_pow, ← map_pow, hζ, map_one, div_one]) (by
        rw [show (σ : G E Ω) ζ / ζ - 1 = ((σ : G E Ω) ζ - ζ) / ζ by field_simp, map_div₀, hv, div_one]
        exact h3)
    exact (div_eq_one_iff_eq hζ0).mp h4
  let χ : Ine (F := E) A →* ℂˣ := MonoidHom.toHomUnits
    { toFun := fun σ => ι ((σ : G E Ω) x / x)
      map_one' := by simp [div_self h0]
      map_mul' := fun σ σ' => by
        have h2 := hfix σ _ (hpow σ')
        have h3 : (σ : G E Ω) x ≠ 0 := (_root_.map_ne_zero _).2 h0
        rw [← map_mul, ← h2, map_div₀ (σ : G E Ω)]
        congr 1
        show (σ : G E Ω) ((σ' : G E Ω) x) / x = _
        field_simp }
  have hχv : ∀ σ, (χ σ : ℂ) = ι ((σ : G E Ω) x / x) := fun _ => rfl
  have hker : ∀ (σ : Ine (F := E) A) (n : ℕ), χ σ ^ n = 1 ↔ (σ : G E Ω) (x ^ n) = x ^ n := fun σ n => by
    rw [Units.ext_iff, Units.val_pow_eq_pow_val, hχv, Units.val_one, ← map_pow, map_eq_one_iff ι ι.injective,
      div_pow, div_eq_one_iff_eq (pow_ne_zero _ h0), map_pow]
  have hχ : IsTm χ := by
    refine ⟨?_, fun σ hσ => ?_⟩
    · have := (isOpen_setOf_apply (F := E) x fun t => t = x).preimage
        (continuous_subtype_val (p := fun σ => σ ∈ Ine (F := E) A))
      convert this using 1
      ext σ
      simpa using hker σ 1
    · have := (hker σ 1).mpr (by
        rw [pow_one]
        exact (div_eq_one_iff_eq h0).mp (LabModel.eq_one_of_cong h hw hc (hpow σ) (hσ x h0)))
      simpa using this
  have hm1 : χ ⟨γ, hγ.1⟩ ^ m = 1 := (hker _ m).mpr (by rw [hx, AlgEquiv.commutes])
  have hord : orderOf (χ ⟨γ, hγ.1⟩) = m := by
    refine orderOf_eq_of_pow_and_pow_div_prime hm hm1 fun p hp hpm e => ?_
    obtain ⟨σ, hσ, hσx⟩ := GlobalTheory.InertiaMovesRoot.exists_mem_Ine_apply_ne E Ω A w h p hp ϖ h1 h2 (x ^ (m / p))
      (by rw [← pow_mul, Nat.div_mul_cancel hpm, hx])
    have h5 : IsTm (χ ^ (m / p)) := hχ.of_le hχ fun σ e _ => by simp [e]
    exact hσx ((hker ⟨σ, hσ⟩ _).mp (by simpa using h5.eq_one hγ (by simpa using e) ⟨σ, hσ⟩))
  have hprim : IsPrimitiveRoot ((χ ⟨γ, hγ.1⟩ : ℂˣ) : ℂ) m := by
    rw [IsPrimitiveRoot.coe_units_iff, ← hord]
    exact IsPrimitiveRoot.orderOf _
  have : NeZero m := ⟨hm.ne'⟩
  obtain ⟨i, -, hi⟩ := hprim.eq_pow_of_pow_eq_one hz
  exact ⟨χ ^ i, hχ.of_le hχ fun σ e _ => by simp [e], by simpa using hi⟩

end Local

section Om

variable (D : D7)

theorem exists_genFam : ∃ γ, GenFam D γ := by
  choose γ₀ hγ₀ using fun w : PlE D.host =>
    GlobalTheory.MemTame.exists_tameGenAt D.host.E D.nd.Om w _ (D.nd.plOm.2 w)
  refine ⟨fun k => Function.extend (D.naut.plGw k) (D.ntypes.tg k) γ₀,
    fun k v => (D.naut.plGw_inj k).extend_apply _ _ v, fun k w _ => ?_⟩
  by_cases h : ∃ v, D.naut.plGw k v = w
  · obtain ⟨v, rfl⟩ := h
    simp only [(D.naut.plGw_inj k).extend_apply]
    exact D.ntypes.tg_gen k v
  · simp only [Function.extend_apply' _ _ _ h]
    exact hγ₀ w

theorem normV_eq {k : Fin 2} {w : PlE D.host} (hw : w ∈ placesOver D.host.E (D.host.g k)) :
    normV w = D.host.g k :=
  GlobalTheory.TameLabels.normV_eq_of_split (D.host.g_prime k) (D.nd.g_split k) hw

theorem exists_order {g : ℕ} [Fact g.Prime] {x : Fbar g} (hx : x ≠ 0) :
    ∃ m : ℕ, 0 < m ∧ m.Coprime g ∧ x ^ m = 1 := by
  have hint : IsIntegral (ZMod g) x := Algebra.IsIntegral.isIntegral x
  have := IntermediateField.adjoin.finiteDimensional hint
  let K := IntermediateField.adjoin (ZMod g) {x}
  have : Finite K := Module.finite_of_finite (ZMod g)
  have := Fintype.ofFinite K
  let y : K := ⟨x, IntermediateField.mem_adjoin_simple_self _ x⟩
  have hy : y ≠ 0 := fun e => hx (congrArg Subtype.val e)
  have : CharP K g := charP_of_injective_algebraMap (algebraMap (ZMod g) K).injective g
  obtain ⟨n, -, hn⟩ := FiniteField.card K g
  have h1 : 1 < Fintype.card K := Fintype.one_lt_card
  refine ⟨Fintype.card K - 1, by omega, ?_, ?_⟩
  · have : (Fintype.card K - 1).Coprime (Fintype.card K) :=
      (Nat.coprime_self_sub_left h1.le).mpr (Nat.coprime_one_left _)
    refine this.coprime_dvd_right ?_
    rw [hn]; exact dvd_pow_self _ n.ne_zero
  · exact congrArg Subtype.val (FiniteField.pow_card_sub_one_eq_one y hy)

open Classical in

theorem exists_tameOm (γ : Fin 2 → PlE D.host → GE D.nd) (hγ : GenFam D γ) :
    ∃ Ω : TameOm D, ∀ k : Fin 2, ∀ w ∈ placesOver D.host.E (D.host.g k), ∀ x, x ≠ 0 →
      Ω.om k w x (γ k w) = D.ntypes.teichC k x := by
  have key : ∀ (k : Fin 2) (w : PlE D.host) (x : Fb (D.host.g k) (D.host.g_prime k)),
      ∃ χ : Ine (F := D.host.E) (D.nd.plOm.1 w) →* ℂˣ, IsTm χ ∧
        (∀ hw : w ∈ placesOver D.host.E (D.host.g k), x ≠ 0 →
          (χ ⟨γ k w, (hγ.2 k w hw).1⟩ : ℂ) = D.ntypes.teichC k x) ∧
        (w ∉ placesOver D.host.E (D.host.g k) → χ = 1) := by
    intro k w x
    have : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    by_cases h : w ∈ placesOver D.host.E (D.host.g k) ∧ x ≠ 0
    · obtain ⟨m, hm, hc, hx⟩ := exists_order h.2
      obtain ⟨χ, h1, h2⟩ := exists_isTm (D.nd.plOm.2 w) (normV_eq D h.1) (hγ.2 k w h.1) hm hc
        (z := D.ntypes.teichC k x) (by rw [← map_pow, hx, map_one])
      exact ⟨χ, h1, fun _ _ => h2, fun e => absurd h.1 e⟩
    · exact ⟨1, ⟨by convert isOpen_univ using 1; ext; simp, fun _ _ => rfl⟩, fun a b => absurd ⟨a, b⟩ h, fun _ => rfl⟩
  choose χ h1 h2 h3 using key
  let om : ∀ k : Fin 2, PlE D.host → Fb (D.host.g k) (D.host.g_prime k) → GE D.nd → ℂ := fun k w x σ =>
    if h : σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 w) then χ k w x ⟨σ, h⟩ else 1
  have e : ∀ k w x σ (h : σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 w)), om k w x σ = χ k w x ⟨σ, h⟩ :=
    fun k w x σ h => dif_pos h
  have hv : ∀ k : Fin 2, ∀ w ∈ placesOver D.host.E (D.host.g k), ∀ x, x ≠ 0 →
      om k w x (γ k w) = D.ntypes.teichC k x := fun k w hw x hx => by
    rw [e _ _ _ _ (hγ.2 k w hw).1, h2 k w x hw hx]
  refine ⟨⟨om, fun k w x _ => ?_, fun k w x _ σ hσ σ' hσ' => ?_, fun k w x y hx hy σ hσ => ?_,
    fun k w _ x _ σ hσ => ?_, fun k w x _ => ?_, fun k w hw x y hx hy hxy => ?_, fun k v x hx => ?_⟩, hv⟩
  · rw [e _ _ _ _ (one_mem _)]
    exact congrArg Units.val (map_one (χ k w x))
  · rw [e _ _ _ _ (mul_mem hσ hσ'), e _ _ _ _ hσ, e _ _ _ _ hσ', ← Units.val_mul, ← map_mul]
    rfl
  · rw [e _ _ _ _ hσ, e _ _ _ _ hσ, e _ _ _ _ hσ, ← Units.val_mul]
    by_cases hw : w ∈ placesOver D.host.E (D.host.g k)
    · have t1 : IsTm (χ k w x * χ k w y) := (h1 k w x).of_le (h1 k w y) fun σ a b => by simp [a, b]
      have t2 : IsTm (χ k w (x * y) / (χ k w x * χ k w y)) :=
        (h1 k w (x * y)).of_le t1 fun σ a b => by rw [MonoidHom.div_apply, a, b, div_one]
      have := t2.eq_one (hγ.2 k w hw) (by
        rw [MonoidHom.div_apply, div_eq_one, MonoidHom.mul_apply, Units.ext_iff, Units.val_mul,
          h2 k w _ hw (mul_ne_zero hx hy), h2 k w _ hw hx, h2 k w _ hw hy, map_mul]) ⟨σ, hσ⟩
      rw [MonoidHom.div_apply, div_eq_one, MonoidHom.mul_apply] at this
      rw [this]
    · simp [h3 k w _ hw]
  · rw [e _ _ _ _ (Wild_le_Ine hσ), (h1 k w x).2 ⟨σ, Wild_le_Ine hσ⟩ hσ]
    rfl
  · obtain ⟨U, hU, hle⟩ := exists_open_subgroup (h1 k w x).1 (map_one _)
    refine ⟨U, hU, fun σ hσ hσ' => ?_⟩
    rw [e _ _ _ _ hσ', show χ k w x ⟨σ, hσ'⟩ = 1 from hle ⟨σ, hσ'⟩ hσ]
    rfl
  · refine ⟨γ k w, (hγ.2 k w hw).1, ?_⟩
    rw [hv k w hw x hx, hv k w hw y hy]
    exact fun a => hxy (D.ntypes.teichC_inj k x y hx hy a)
  · rw [← hγ.1 k v]
    exact hv k _ (D.naut.plGw_over k v) x hx

theorem nonempty_tameOm : Nonempty (TameOm D) := by
  obtain ⟨γ, hγ⟩ := exists_genFam D
  obtain ⟨Ω, -⟩ := exists_tameOm D γ hγ
  exact ⟨Ω⟩

end Om

section Ties

variable {D : D7} (T : GlobalTheory.RowTie.WDTie D.nd D.naut)

include T in

theorem ineRep_of_tie : IneRep D := by
  intro k w _ L
  have key : ∀ (x : WD (E := D.host.E) (A := D.nd.plOm.1 w) (w := w) (D.nd.plOm.2 w)) (n : ℕ), x.lpDim = n →
      ∃ ρ : ↥(Ine (F := D.host.E) (D.nd.plOm.1 w)) →* GL (Fin n) ℂ,
      (∃ U : Subgroup (GE D.nd), IsOpen (U : Set (GE D.nd)) ∧
        ∀ σ : ↥(Ine (F := D.host.E) (D.nd.plOm.1 w)), (σ : GE D.nd) ∈ U → ρ σ = 1) ∧
      ∀ σ : ↥(Ine (F := D.host.E) (D.nd.plOm.1 w)), x.inePol (σ : GE D.nd) =
        ((ρ σ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).charpoly := by
    intro x n hn
    induction x using WD.ind with
    | hP m a =>
      rw [WD.lpDim_mk, Module.finrank_fin_fun] at hn
      subst hn
      let f : ↥(Ine (F := D.host.E) (D.nd.plOm.1 w)) →* Matrix (Fin m) (Fin m) ℂ :=
        ((LinearMap.toMatrixAlgEquiv' : Module.End ℂ (Fin m → ℂ) ≃ₐ[ℂ] _) : _ →* _).comp
          (a.ρ.comp (ineIncl (D.nd.plOm.2 w)))
      have hf : ∀ σ, f σ = LinearMap.toMatrix' (a.ρ (ineIncl (D.nd.plOm.2 w) σ)) := fun _ => rfl
      obtain ⟨U, hU, hle⟩ := exists_open_subgroup a.smooth (by simp)
      refine ⟨f.toHomUnits, ⟨U, hU, fun σ hσ => Units.ext ?_⟩, fun σ => ?_⟩
      · have : a.ρ (ineIncl (D.nd.plOm.2 w) σ) = 1 := hle σ hσ
        rw [MonoidHom.coe_toHomUnits, hf, this]
        exact LinearMap.toMatrix'_id
      · rw [WD.inePol_of_mem_Ine _ σ.2, WD.charPol_mk, MonoidHom.coe_toHomUnits, hf,
          ← LinearMap.toMatrix_eq_toMatrix', LinearMap.charpoly_toMatrix]
  obtain ⟨ρ, h1, h2⟩ := key (T.e w L) _ (T.dim w L)
  exact ⟨ρ, h1, fun σ => (T.inePol w L σ σ.2).trans (h2 σ)⟩

def LabAll (γ : Fin 2 → PlE D.host → GE D.nd) : Prop :=
  ∀ k : Fin 2, ∀ w ∈ placesOver D.host.E (D.host.g k), ∀ a : D.naut.LP w,
    haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    D.naut.items₂ k w a = WD.lab (D.ntypes.teichC k) (γ k w) (T.e w a)

theorem tameLP_iff {w : PlE D.host} (L : D.naut.LP w) : TameLP D L ↔ (T.e w L).tame := by
  rw [WD.tame_iff_inePol, T.dim]
  exact ⟨fun h σ hσ => by rw [← T.inePol w L σ (Wild_le_Ine hσ)]; exact h σ (Wild_le_Ine hσ) hσ,
    fun h σ hσ hσ' => by rw [T.inePol w L σ hσ]; exact h σ hσ'⟩

theorem labDepth_of_tie {γ} (hγ : GenFam D γ) (h : LabAll T γ) : LabDepth D := by
  intro k w hw L
  have : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  rw [h k w hw, tameLP_iff T, ← T.dim]
  exact ⟨WD.lab_monic _ _ _, WD.natDegree_lab_eq_iff
    (TeichmullerInertiaLabelCondition.of_tameGenAt (normV_eq D hw) (hγ.2 k w hw) (D.ntypes.teichC_inj k)) _⟩

theorem labGen_of_tie {γ} (hγ : GenFam D γ) (h : LabAll T γ) : LabGen D := by
  refine ⟨γ, hγ, fun k w hw L hL => ?_⟩
  have : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  rw [h k w hw, ← T.dim] at hL
  rw [h k w hw, T.inePol w L _ (hγ.2 k w hw).1]
  exact WD.inePol_eq_of_natDegree_lab _ _ _ hL

end Ties

section Rec

open GlobalTheory.RowTie.Model GlobalTheory.HeightCounting

def noBC {R : Ranks} {H : Formalism.BasicNotions.Host R} {what₂ : Rows.Data R} {N : NData R H what₂} (hE : IsEmpty N.Loc) (A : NAut N) :
    NBC A where
  AU := fun _ => PEmpty
  multAU := fun _ a => a.elim
  sphAU := fun _ a => a.elim
  locAU := fun _ a => a.elim
  satAU := fun _ a => a.elim
  satAU_card := fun _ a => a.elim
  Wt := fun _ => PEmpty
  infW := fun _ a => a.elim
  infW_card := fun _ a => a.elim
  wtAU := fun _ a => a.elim
  infW_alg := fun _ a => a.elim
  embAV := fun i => hE.elim i
  embAV_inj := fun i => hE.elim i
  embAV_loc := fun i => hE.elim i
  embAV_sat := fun i => hE.elim i
  embAV_sph := fun i => hE.elim i
  embAV_inf := fun i => hE.elim i

set_option maxHeartbeats 2000000 in

theorem exists_ties (D : D7) (hE : IsEmpty D.nd.Loc) :
    ∃ D' : D7, Nonempty (GlobalTheory.RowTie.WDTie D'.nd D'.naut) ∧ IneRep D' ∧ LabDepth D' ∧ LabGen D' := by
  have : IsEmpty (ndLab D.nd D.nd.lab D.nd.lab_monic).Loc := hE
  obtain ⟨γ, hγ⟩ := exists_genFam D
  let A := wdAut (ndLab D.nd D.nd.lab D.nd.lab_monic) D.naut D.ntypes.teichC γ
  let D' : D7 := setAut D hE D.nd.lab D.nd.lab_monic A (noBC hE A) D.ntypes.tg_mem D.ntypes.tg_gen (fun k v L hL => by
    have : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    have := WD.inePol_eq_of_natDegree_lab (D.ntypes.teichC k) (γ k (D.naut.plGw k v)) L hL
    exact (congrArg (WD.inePol L) (hγ.1 k v).symm).trans this)
  let T : GlobalTheory.RowTie.WDTie D'.nd D'.naut := tie (ndLab D.nd D.nd.lab D.nd.lab_monic) D.naut D.ntypes.teichC γ
  have hγ' : GenFam D' γ := hγ
  have hl : LabAll T γ := fun _ _ _ _ => rfl
  exact ⟨D', ⟨T⟩, ineRep_of_tie T, labDepth_of_tie T hγ' hl, labGen_of_tie T hγ' hl⟩

end Rec

section Forms

open TensorProduct

variable {D : D7}

def io (i : D.nd.Loc) : KK D.nd i →+* ℂ := (D.naut.iotaQC i).toRingHom.comp (D.naut.iotaQ i)

theorem heckeEig_eq_top (i : D.nd.Loc) [Subsingleton (D.nd.X i)] (x : D.nd.X i) :
    heckeEig (D.nd.T i) (D.nd.act i) x = ⊤ := by
  refine iInf_eq_top.mpr fun f => eq_top_iff.mpr fun v _ => Module.End.mem_eigenspace_iff.mpr ?_
  have hf : f = algebraMap (D.nd.O i) (D.nd.T i) ((f : D.nd.X i → D.nd.O i) x) :=
    Subtype.ext (funext fun y => by rw [Subsingleton.elim y x]; rfl)
  conv_lhs => rw [hf, AlgHom.commutes, Algebra.algebraMap_eq_smul_one, LinearMap.baseChange_smul]
  rw [algebraMap_smul, LinearMap.smul_apply]
  congr 1
  exact LinearMap.congr_fun (LinearMap.baseChange_id) v

theorem nonempty_sec (i : D.nd.Loc) (x : D.nd.X i) (hx : ∀ P, D.naut.ptV i P = some x) : Nonempty (Sec D i) := by
  have hs : Subsingleton (D.nd.X i) := ⟨fun a b => by
    obtain ⟨P, hP⟩ := D.naut.pt_surj i a
    obtain ⟨Q, hQ⟩ := D.naut.pt_surj i b
    rw [hx] at hP hQ
    exact Option.some_injective _ (hP.symm.trans hQ)⟩
  have htop : typeSum D i (some x) = ⊤ := by
    rw [← D.naut.typeV_top i, typeSum]
    simp [hx]
  let b := Module.Free.chooseBasis D.what₂.LL (D.what₂.MtL (D.nd.mu i) (D.nd.j i))
  obtain ⟨hli, hsp⟩ := D.what₂.jMt_basis _ _ b
  have : Finite (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL (D.nd.mu i) (D.nd.j i))) := hli.finite
  let := Fintype.ofFinite (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL (D.nd.mu i) (D.nd.j i)))
  let bC := Basis.mk hli hsp.ge
  have hdim : Fintype.card (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL (D.nd.mu i) (D.nd.j i))) =
      finrank (KK D.nd i) (TensorProduct (D.nd.O i) (KK D.nd i) (D.nd.Mt i)) := by
    have h1 := D.naut.eig_dim i x
    rw [NData.mult, heckeMult, heckeEig_eq_top, finrank_top] at h1
    rw [h1, ← finrank_eq_card_basis bC, ← finrank_top ℂ, ← htop]
    rfl
  have hspan : ⊤ ≤ Submodule.span (KK D.nd i) (Set.range fun s => D.nd.prMt i (b s)) := by
    rw [← D.nd.prMt_span i, Submodule.span_le]
    rintro _ ⟨y, rfl⟩
    rw [← b.sum_repr y, map_sum]
    exact Submodule.sum_mem _ fun s _ => by
      rw [map_smulₛₗ]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨s, rfl⟩)
  let bK := basisOfTopLeSpanOfCardEqFinrank _ hspan hdim
  have hbK : ∀ s, bK s = D.nd.prMt i (b s) := fun s => congrFun (coe_basisOfTopLeSpanOfCardEqFinrank _ hspan hdim) s
  let Φ : TensorProduct (D.nd.O i) (KK D.nd i) (D.nd.Mt i) →+ D.what₂.Mt (D.nd.mu i) (D.nd.j i) :=
    { toFun := fun v => ∑ s, io i (bK.repr v s) • bC s
      map_zero' := by simp
      map_add' := fun u v => by simp [add_smul, Finset.sum_add_distrib] }
  have hΦ : ∀ v, Φ v = ∑ s, io i (bK.repr v s) • bC s := fun _ => rfl
  refine ⟨⟨Φ, (injective_iff_map_eq_zero Φ).mpr fun v hv => ?_, fun k v => ?_, fun y u _ => ?_, fun y => ?_⟩⟩
  · have := Fintype.linearIndependent_iff.mp bC.linearIndependent _ ((hΦ v).symm.trans hv)
    refine bK.repr.injective (Finsupp.ext fun s => ?_)
    simpa using this s
  · rw [hΦ, hΦ, Finset.smul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, mul_smul]
    rfl
  · rw [Subsingleton.elim y x, htop]
    trivial
  · have h1 : D.nd.prMt i y = ∑ s, D.nd.embK i (b.repr y s) • bK s := by
      conv_lhs => rw [← b.sum_repr y, map_sum]
      simp only [map_smulₛₗ, hbK]
    have h2 : D.what₂.jMt _ _ y = Φ (D.nd.prMt i y) := by
      rw [hΦ]
      conv_lhs => rw [← b.sum_repr y, map_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [map_smulₛₗ, h1, bK.repr_sum_self, Basis.mk_apply]
      congr 1
      exact (D.naut.iota_LL i _).symm
    rw [h2, sub_self]
    exact zero_mem _

theorem sec_ne_zero {i : D.nd.Loc} (S : Sec D i) : S.Φ ≠ 0 := by
  obtain ⟨x⟩ := D.nd.neX i
  obtain ⟨u, -, hu⟩ := (Submodule.ne_bot_iff _).mp (D.nd.eig_ne i x)
  exact fun h => hu (S.inj (by simp [h]))

theorem nonempty_cenO (S : ∀ i, Sec D i) (hpt : ∀ i P, D.naut.ptV i P ≠ none)
    (a : ∀ i, ↥(Subalgebra.center (D.nd.O i) (MonoidAlgebra (D.nd.O i) (G0g D.nd))) →ₐ[D.nd.O i] D.nd.O i)
    (ha : ∀ i z F, D.ntypes.onMt (D.nd.mu i) (D.nd.j i)
      (PairedCharacterCondition.mapCoef (iotaO D.nd D.naut i) ((z : ↥(Subalgebra.center (D.nd.O i) (MonoidAlgebra (D.nd.O i) (G0g D.nd)))) :
        MonoidAlgebra (D.nd.O i) (G0g D.nd))) F = iotaO D.nd D.naut i (a i z) • F) : Nonempty (CenO D) := by
  refine ⟨⟨fun i => (Algebra.ofId _ _).comp (a i), fun i z f => Algebra.commutes (a i z) (D.nd.act i f), fun i z x y h => ?_⟩⟩
  have h0 : typeSum D i none = ⊥ := by simp [typeSum, hpt]
  have h1 : ∀ y, D.what₂.jMt _ _ y = (S i).Φ (D.nd.prMt i y) := fun y => by
    have := (S i).split y
    rwa [h0, Submodule.mem_bot, sub_eq_zero] at this
  apply (S i).inj
  have h2 : LinearMap.baseChange (KK D.nd i) (((Algebra.ofId _ (Module.End (D.nd.O i) (D.nd.Mt i))).comp (a i)) z)
      (D.nd.prMt i x) = algebraMap _ (KK D.nd i) (a i z) • D.nd.prMt i x := by
    rw [AlgHom.comp_apply, Algebra.ofId_apply, Algebra.algebraMap_eq_smul_one, LinearMap.baseChange_smul,
      algebraMap_smul, LinearMap.smul_apply]
    congr 1
    exact LinearMap.congr_fun (LinearMap.baseChange_id) _
  rw [h2, (S i).semi, ← h1, ← h1, h, ha]
  rfl

def omOf (P : PairedCharacterCondition.Pend D) : TameOm D :=
  ⟨P.om, P.om_one, P.om_mul, P.tameInertiaChar_mul_root, P.om_wild, P.om_open, P.om_inj, P.om_tg⟩

def cenOf (P : PairedCharacterCondition.Pend D) : CenO D := ⟨P.zO, P.zO_comm, P.zO_act⟩

theorem mk_of (P : PairedCharacterCondition.Pend D) : GlobalTheory.PendOf.mk P.lz P.eSer_eq P.eSer_LL P.zetaPrimitiveRoot (omOf P) P.inertiaCharpoly_eigenvalues P.inertiaCharpoly_character (cenOf P)
    P.zL_stable P.prMt_type P.Par_surj = P := by
  have h : (fun i PI k v => {τ | ∃ F ∈ D.naut.typeV i PI, D.ntypes.onMt (D.nd.mu i) (D.nd.j i)
      (Formalism.MainNotions.ArithmeticCylinders.atPlace D k v ((P.lz k).idem τ)) F ≠ 0}) = P.kty := by
    funext i PI k v
    ext τ
    exact (P.kty_spec i PI k v τ).symm
  cases P
  simp only [GlobalTheory.PendOf.mk, omOf, cenOf]
  congr 1

end Forms

end GlobalTheory.PendOf.Model

end
