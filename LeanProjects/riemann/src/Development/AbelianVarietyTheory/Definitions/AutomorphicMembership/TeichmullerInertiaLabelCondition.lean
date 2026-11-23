import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MonodromyZeroOfWeilDeligneRepClassIff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TeichmullerRoots
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DepthZeroLabelsOfLabelLaws
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.RootsCharpolyPowEqMapPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTameGenAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTeichmullerMaps
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCongOfCongOnFixed

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.CyclotomicNorms Polynomial TensorProduct Module

namespace GlobalTheory.WeilDeligne

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}

variable (E) in

def Wild (A : ValuationSubring Ω) : Subgroup (G E Ω) where
  carrier := {σ | ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1}
  one_mem' := fun y hy => by simp [div_self hy]
  mul_mem' := by
    intro σ τ hσ hτ y hy
    have hz : τ y ≠ 0 := (_root_.map_ne_zero τ).2 hy
    have h1 := hσ _ hz
    have h2 := hτ y hy
    have e : (σ * τ) y / y - 1 =
        (σ (τ y) / τ y - 1) * (τ y / y - 1) + ((σ (τ y) / τ y - 1) + (τ y / y - 1)) := by
      rw [AlgEquiv.mul_apply]; field_simp; ring
    rw [e]
    refine Valuation.map_add_lt _ ?_ (Valuation.map_add_lt _ h1 h2)
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' h2.le) h1
  inv_mem' := by
    intro σ hσ y hy
    have hz : (σ⁻¹ : G E Ω) y ≠ 0 := (_root_.map_ne_zero _).2 hy
    have h1 := hσ _ hz
    have e0 : σ ((σ⁻¹ : G E Ω) y) = y := by
      show (σ * σ⁻¹) y = y
      simp
    rw [e0] at h1
    have h2 : A.valuation (y / (σ⁻¹ : G E Ω) y) = 1 := by
      have := Valuation.map_eq_of_sub_lt A.valuation (x := 1) (y := y / (σ⁻¹ : G E Ω) y)
        (by rwa [map_one])
      rwa [map_one] at this
    have e : (σ⁻¹ : G E Ω) y / y - 1 =
        -((y / (σ⁻¹ : G E Ω) y - 1) / (y / (σ⁻¹ : G E Ω) y)) := by
      field_simp; ring
    rw [e, Valuation.map_neg, map_div₀, h2, div_one]
    exact h1

omit [NumberField E] in

theorem mem_Wild {σ : G E Ω} :
    σ ∈ Wild E A ↔ ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1 := Iff.rfl

open Pointwise in

theorem Wild_le_Ine : Wild E A ≤ Ine (F := E) A := by
  intro σ h
  have h1 : ∀ x : Ω, x ≠ 0 → A.valuation (σ x - x) < A.valuation x := fun x hx => by
    have e : σ x - x = (σ x / x - 1) * x := by field_simp
    have h0 : 0 < A.valuation x := zero_lt_iff.mpr (by simpa using hx)
    rw [e, map_mul]
    exact mul_lt_of_lt_one_left h0 (h x hx)
  have h2 : ∀ x : Ω, A.valuation (σ x) = A.valuation x := fun x => by
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · exact Valuation.map_eq_of_sub_lt _ (h1 x hx)
  refine ⟨?_, fun x hx => ?_⟩
  · change σ • A = A
    ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ← A.valuation_le_one_iff,
      ← A.valuation_le_one_iff, ← h2, AlgEquiv.smul_def, mul_inv_apply]
  · rcases eq_or_ne x 0 with rfl | hx0
    · simp
    · exact (h1 x hx0).trans_le hx

theorem conj_mem_Wild {φ σ : G E Ω} (hφ : φ ∈ Dec (F := E) A) (hσ : σ ∈ Wild E A) :
    φ * σ * φ⁻¹ ∈ Wild E A := by
  intro y hy
  have h := hσ ((φ⁻¹ : G E Ω) y) ((_root_.map_ne_zero _).2 hy)
  rw [← valuation_apply_lt_one_iff hφ, map_sub, map_div₀, mul_inv_apply, map_one] at h
  exact h

theorem tameGenAt_iff {γ : G E Ω} : TameGenAt A γ ↔ γ ∈ Ine (F := E) A ∧
    ((Ine (F := E) A : Subgroup (G E Ω)) : Set (G E Ω)) ⊆
      closure ((Subgroup.closure (insert γ (Wild E A : Set (G E Ω))) : Subgroup (G E Ω)) :
        Set (G E Ω)) := Iff.rfl

variable [IsAlgClosure E Ω]

theorem tame_relation {γ φ : G E Ω} {q : ℕ} (hγ : γ ∈ Ine (F := E) A) (hφ : IsFrob A q φ) :
    (γ ^ q)⁻¹ * (φ * γ * φ⁻¹) ∈ Wild E A := GlobalTheory.TameLabels.wild_of_frob hγ hφ

namespace WDRep

variable {h : IsPlaceOver A w}
variable {V V' : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']

def tameSpace (a : WDRep h V) : Submodule ℂ V :=
  Representation.invariants (a.ρ.comp ((Wild E A).subgroupOf (Weil h)).subtype)

theorem mem_tameSpace (a : WDRep h V) {v : V} :
    v ∈ a.tameSpace ↔ ∀ σ : Weil h, (σ : G E Ω) ∈ Wild E A → a.ρ σ v = v :=
  ⟨fun hv σ hσ => hv ⟨σ, hσ⟩, fun hv σ => hv σ.1 σ.2⟩

theorem ρ_mem_tameSpace (a : WDRep h V) (σ : Weil h) : ∀ v ∈ a.tameSpace, a.ρ σ v ∈ a.tameSpace := by
  intro v hv
  rw [mem_tameSpace] at hv ⊢
  intro u hu
  have h1 := hv (σ⁻¹ * u * σ⁻¹⁻¹) (conj_mem_Wild (Weil_le_Dec h σ⁻¹.2) hu)
  calc a.ρ u (a.ρ σ v) = a.ρ σ (a.ρ (σ⁻¹ * u * σ⁻¹⁻¹) v) := by
        rw [← End.mul_apply, ← End.mul_apply, ← map_mul, ← map_mul]; congr 2; group
    _ = a.ρ σ v := by rw [h1]

theorem N_mem_tameSpace (a : WDRep h V) : ∀ v ∈ a.tameSpace, a.N v ∈ a.tameSpace := by
  intro v hv
  rw [mem_tameSpace] at hv ⊢
  intro u hu
  rw [a.comm_apply, deg_eq_zero_iff.mpr (Wild_le_Ine hu), hv u hu, zpow_zero, one_smul]

def tamePart (a : WDRep h V) : WDRep h a.tameSpace where
  ρ := { toFun := fun σ => (a.ρ σ).restrict (a.ρ_mem_tameSpace σ)
         map_one' := by ext; simp
         map_mul' := fun σ τ => by ext; simp }
  N := a.N.restrict a.N_mem_tameSpace
  smooth := a.smooth.of_le fun σ hσ => by ext; simp [hσ]
  semisimple σ := End.IsSemisimple.restrict (a.ρ_mem_tameSpace σ) (a.semisimple σ)
  nilpotent := End.isNilpotent.restrict a.N_mem_tameSpace a.nilpotent
  comm σ := LinearMap.ext fun v => Subtype.ext (a.comm_apply σ v)

@[simp] theorem coe_tamePart_ρ (a : WDRep h V) (σ : Weil h) (v : a.tameSpace) :
    (a.tamePart.ρ σ v : V) = a.ρ σ v := rfl

@[simp] theorem coe_tamePart_N (a : WDRep h V) (v : a.tameSpace) :
    (a.tamePart.N v : V) = a.N v := rfl

theorem tamePart_ρ_of_wild (a : WDRep h V) {σ : Weil h} (hσ : (σ : G E Ω) ∈ Wild E A) :
    a.tamePart.ρ σ = 1 :=
  LinearMap.ext fun v => Subtype.ext (a.mem_tameSpace.mp v.2 σ hσ)

def Tame (a : WDRep h V) : Prop := ∀ σ : Weil h, (σ : G E Ω) ∈ Wild E A → a.ρ σ = 1

theorem tame_tamePart (a : WDRep h V) : a.tamePart.Tame := fun _ hσ => a.tamePart_ρ_of_wild hσ

theorem tame_iff (a : WDRep h V) : a.Tame ↔ a.tameSpace = ⊤ := by
  rw [Submodule.eq_top_iff']
  exact ⟨fun ha v => a.mem_tameSpace.mpr fun σ hσ => by rw [ha σ hσ]; rfl,
    fun ha σ hσ => LinearMap.ext fun v => a.mem_tameSpace.mp (ha v) σ hσ⟩

def tameEquiv {a : WDRep h V} {b : WDRep h V'} (e : V ≃ₗ[ℂ] V')
    (he : ∀ σ : Weil h, (σ : G E Ω) ∈ Ine (F := E) A → ∀ v, e (a.ρ σ v) = b.ρ σ (e v)) :
    a.tameSpace ≃ₗ[ℂ] b.tameSpace :=
  e.ofSubmodules _ _ (by
    ext v
    obtain ⟨v, rfl⟩ := e.surjective v
    rw [Submodule.mem_map_equiv, e.symm_apply_apply, mem_tameSpace, mem_tameSpace]
    refine forall₂_congr fun σ hσ => ?_
    rw [← he σ (Wild_le_Ine hσ), e.injective.eq_iff])

@[simp] theorem coe_tameEquiv {a : WDRep h V} {b : WDRep h V'} (e : V ≃ₗ[ℂ] V') (he)
    (v : a.tameSpace) : (tameEquiv (a := a) (b := b) e he v : V') = e v := rfl

theorem Iso.tamePart {a : WDRep h V} {b : WDRep h V'} (hab : a.Iso b) :
    a.tamePart.Iso b.tamePart := by
  obtain ⟨e, h1, h2⟩ := hab
  exact ⟨tameEquiv e fun σ _ => h1 σ, fun σ v => Subtype.ext (h1 σ v), fun v => Subtype.ext (h2 v)⟩

theorem Tame.iso_tamePart {a : WDRep h V} (ha : a.Tame) : a.tamePart.Iso a :=
  ⟨LinearEquiv.ofTop _ (a.tame_iff.mp ha), fun _ _ => rfl, fun _ => rfl⟩

theorem tamePart_sum (a : WDRep h V) (b : WDRep h V') :
    (a.sum b).tamePart.Iso (a.tamePart.sum b.tamePart) :=
  ⟨{ toFun := fun v => (⟨v.1.1, a.mem_tameSpace.mpr fun σ hσ =>
          congrArg Prod.fst ((a.sum b).mem_tameSpace.mp v.2 σ hσ)⟩,
        ⟨v.1.2, b.mem_tameSpace.mpr fun σ hσ =>
          congrArg Prod.snd ((a.sum b).mem_tameSpace.mp v.2 σ hσ)⟩)
     map_add' := fun _ _ => rfl
     map_smul' := fun _ _ => rfl
     invFun := fun v => ⟨(v.1, v.2), (a.sum b).mem_tameSpace.mpr fun σ hσ =>
        Prod.ext (a.mem_tameSpace.mp v.1.2 σ hσ) (b.mem_tameSpace.mp v.2.2 σ hσ)⟩
     left_inv := fun _ => rfl
     right_inv := fun _ => rfl }, fun _ _ => rfl, fun _ => rfl⟩

theorem charpoly_tamePart_congr {a : WDRep h V} {b : WDRep h V'} (e : V ≃ₗ[ℂ] V')
    (he : ∀ σ : Weil h, (σ : G E Ω) ∈ Ine (F := E) A → ∀ v, e (a.ρ σ v) = b.ρ σ (e v))
    {σ : Weil h} (hσ : (σ : G E Ω) ∈ Ine (F := E) A) :
    (a.tamePart.ρ σ).charpoly = (b.tamePart.ρ σ).charpoly := by
  rw [← LinearEquiv.charpoly_conj (tameEquiv e he)]
  congr 1
  refine LinearMap.ext fun v => ?_
  obtain ⟨v, rfl⟩ := (tameEquiv e he).surjective v
  rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
  exact Subtype.ext (he σ hσ v)

theorem Tame.conj_eq_pow {a : WDRep h V} (ha : a.Tame) {γ φ : Weil h}
    (hγ : (γ : G E Ω) ∈ Ine (F := E) A) (hφ : deg φ = 1) :
    a.ρ (φ * γ * φ⁻¹) = a.ρ γ ^ normV w := by
  have h1 := ha ((γ ^ normV w)⁻¹ * (φ * γ * φ⁻¹)) (tame_relation hγ (deg_eq_one_iff.mp hφ))
  rw [← mul_inv_cancel_left (γ ^ normV w) (φ * γ * φ⁻¹), map_mul, h1, mul_one, map_pow]

theorem Tame.exists_pow_eq_one {a : WDRep h V} (ha : a.Tame) {γ : Weil h}
    (hγ : (γ : G E Ω) ∈ Ine (F := E) A) :
    ∃ n : ℕ, 0 < n ∧ n.Coprime (normV w) ∧ a.ρ γ ^ n = 1 := by
  let r := a.ρ.toHomUnits
  have hfin : IsOfFinOrder (r γ) := by
    rw [← finite_powers]
    refine Set.Finite.of_finite_image (f := Units.val) (a.smooth.finite_range.subset ?_)
      Units.val_injective.injOn
    rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩
    exact ⟨⟨γ, hγ⟩ ^ n, by
      simp only [map_pow, Units.val_pow_eq_pow_val]; rfl⟩
  have h1 : r (frob h) * r γ * (r (frob h))⁻¹ = r γ ^ normV w := by
    rw [← map_inv, ← map_mul, ← map_mul]
    exact Units.ext ((ha.conj_eq_pow hγ deg_frob).trans (Units.val_pow_eq_pow_val (r γ) _).symm)
  have h2 : orderOf (r γ ^ normV w) = orderOf (r γ) := by
    rw [← h1]
    exact MulEquiv.orderOf_eq (MulAut.conj (r (frob h))) (r γ)
  have hpos := hfin.orderOf_pos
  refine ⟨orderOf (r γ), hpos, ?_, ?_⟩
  · rw [hfin.orderOf_pow] at h2
    exact (Nat.div_eq_self.mp h2).resolve_left hpos.ne'
  · exact (Units.val_pow_eq_pow_val (r γ) _).symm.trans
      (congrArg Units.val (pow_orderOf_eq_one (r γ)))

theorem Tame.roots_map_pow {a : WDRep h V} (ha : a.Tame) {γ : Weil h}
    (hγ : (γ : G E Ω) ∈ Ine (F := E) A) :
    (a.ρ γ).charpoly.roots.map (· ^ normV w) = (a.ρ γ).charpoly.roots := by
  have h1 : (a.ρ γ ^ normV w).charpoly = (a.ρ γ).charpoly := by
    rw [← ha.conj_eq_pow hγ deg_frob,
      ← LinearEquiv.charpoly_conj (LinearMap.GeneralLinearGroup.toLinearEquiv
        (a.ρ.asGroupHom (frob h))) (a.ρ γ)]
    congr 1
    refine LinearMap.ext fun v => ?_
    rw [LinearEquiv.conj_apply_apply, map_mul, map_mul]
    rfl
  have h2 := GlobalTheory.CharpolyPow.roots_charpoly_pow ℂ _ (normV w)
    (LinearMap.toMatrix (finBasis ℂ V) (finBasis ℂ V) (a.ρ γ))
  rw [LinearMap.toMatrix_pow, LinearMap.charpoly_toMatrix, LinearMap.charpoly_toMatrix, h1] at h2
  exact h2.symm

end WDRep

section Teich

variable {g : ℕ} [Fact g.Prime]

def IsTeich (τ : Fbar g →* ℂ) : Prop := ∀ x y, x ≠ 0 → y ≠ 0 → τ x = τ y → x = y

theorem IsTeich.injective {τ : Fbar g →* ℂ} (hτ : IsTeich τ) : Function.Injective τ :=
  GlobalTheory.TameLabels.teich_injective τ hτ

theorem IsTeich.map_zero {τ : Fbar g →* ℂ} (hτ : IsTeich τ) : τ 0 = 0 :=
  GlobalTheory.TameLabels.teich_zero τ hτ

theorem IsTeich.exists_eq {τ : Fbar g →* ℂ} (hτ : IsTeich τ) {n : ℕ} (hn : 0 < n)
    (hc : n.Coprime g) {z : ℂ} (hz : z ^ n = 1) : ∃ x, τ x = z := by
  have : NeZero n := ⟨hn.ne'⟩
  have : NeZero (n : Fbar g) := ⟨fun h0 =>
    (Nat.Prime.coprime_iff_not_dvd Fact.out).mp hc.symm ((CharP.cast_eq_zero_iff (Fbar g) g n).mp h0)⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (Fbar g) n
  obtain ⟨i, -, hi⟩ := (hζ.map_of_injective hτ.injective).eq_pow_of_pow_eq_one hz
  exact ⟨ζ ^ i, by rw [map_pow, hi]⟩

theorem eq_of_rootsBar_eq {f f' : (ZMod g)[X]} (hf : f.Monic) (hf' : f'.Monic)
    (e : rootsBar f = rootsBar f') : f = f' := by
  refine Polynomial.map_injective (algebraMap (ZMod g) (Fbar g)) (RingHom.injective _) ?_
  rw [(IsAlgClosed.splits _).eq_prod_roots_of_monic (hf.map (algebraMap (ZMod g) (Fbar g))),
    (IsAlgClosed.splits _).eq_prod_roots_of_monic (hf'.map (algebraMap (ZMod g) (Fbar g)))]
  exact congrArg (fun m : Multiset (Fbar g) => (m.map fun x => X - C x).prod) e

theorem IsTeich.existsUnique_monic {τ : Fbar g →* ℂ} (hτ : IsTeich τ) {m : Multiset ℂ}
    (h1 : ∀ z ∈ m, ∃ x, τ x = z) (h2 : m.map (· ^ g) = m) :
    ∃! f : (ZMod g)[X], f.Monic ∧ (rootsBar f).map τ = m := by
  have h3 : (m.map (Function.invFun τ)).map τ = m := by
    rw [Multiset.map_map]
    exact (Multiset.map_congr rfl fun z hz => Function.invFun_eq (h1 z hz)).trans (Multiset.map_id' m)
  obtain ⟨f, hf, hr⟩ := GlobalTheory.Compare.TeichmullerRoots.exists_monic_of_stable (m.map (Function.invFun τ)) (by
    refine Multiset.map_injective hτ.injective ?_
    rw [h3, Multiset.map_map]
    conv_rhs => rw [← h2, ← h3, Multiset.map_map]
    exact Multiset.map_congr rfl fun x _ => map_pow τ x g)
  refine ⟨f, ⟨hf, by rw [hr, h3]⟩, fun f' hf' => eq_of_rootsBar_eq hf'.1 hf ?_⟩
  exact Multiset.map_injective hτ.injective (by rw [hf'.2, hr, h3])

end Teich

namespace WD

variable {h : IsPlaceOver A w}
variable {V V' : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']

def lpTame (x : WD h) : WD h :=
  Quotient.lift (s := isoSetoid h) (fun a => mk a.2.tamePart)
    (fun _ _ hab => sound (WDRep.Iso.tamePart hab)) x

@[simp] theorem lpTame_mk (a : WDRep h V) : lpTame (mk a) = mk a.tamePart :=
  sound (iso_std a).tamePart.symm

theorem lpDim_lpTame_le (x : WD h) : lpDim (lpTame x) ≤ lpDim x := by
  induction x using ind with
  | hP n a => rw [lpTame_mk, lpDim_mk, lpDim_mk]; exact Submodule.finrank_le _

def tame (x : WD h) : Prop := lpTame x = x

theorem tame_iff_lpDim (x : WD h) : tame x ↔ lpDim (lpTame x) = lpDim x := by
  refine ⟨fun hx => congrArg lpDim hx, fun hx => ?_⟩
  induction x using ind with
  | hP n a =>
    rw [lpTame_mk, lpDim_mk, lpDim_mk] at hx
    rw [tame, lpTame_mk]
    exact sound (a.tame_iff.mpr (Submodule.eq_top_of_finrank_eq hx)).iso_tamePart

@[simp] theorem tame_mk (a : WDRep h V) : tame (mk a) ↔ a.Tame := by
  rw [tame_iff_lpDim, lpTame_mk, lpDim_mk, lpDim_mk, a.tame_iff]
  exact ⟨Submodule.eq_top_of_finrank_eq, fun e => by rw [e, finrank_top]⟩

theorem tame_iff_inePol (x : WD h) :
    tame x ↔ ∀ σ ∈ Wild E A, inePol x σ = (X - 1) ^ lpDim x := by
  induction x using ind with
  | hP n a =>
    rw [tame_mk, lpDim_mk]
    constructor
    · intro ha σ hσ
      rw [inePol_of_mem_Ine _ (Wild_le_Ine hσ), charPol_mk, ha _ hσ, LinearMap.charpoly_one]
    · intro ha σ hσ
      have h1 := ha σ hσ
      rw [inePol_of_mem _ σ.2, charPol_mk] at h1
      have h2 : IsNilpotent (a.ρ σ - 1) := ⟨finrank ℂ (Fin n → ℂ), by
        have := LinearMap.aeval_self_charpoly (a.ρ σ)
        rw [h1] at this
        simpa using this⟩
      have h3 : End.IsSemisimple (a.ρ σ - 1) :=
        End.IsSemisimple.sub_of_commute (Commute.one_right _) (a.semisimple σ) End.isSemisimple_id
      exact sub_eq_zero.mp (End.eq_zero_of_isNilpotent_isSemisimple h2 h3)

theorem tame_of_unr {x : WD h} (hx : unr x) : tame x := by
  induction x using ind with
  | hP n a => exact (tame_mk a).mpr fun σ hσ => ((unr_mk a).mp hx).2 ⟨σ, Wild_le_Ine hσ⟩

def tameEig (x : WD h) (γ : G E Ω) : Multiset ℂ := (inePol (lpTame x) γ).roots

theorem tameEig_mk (a : WDRep h V) {γ : G E Ω} (hγ : γ ∈ Weil h) :
    tameEig (mk a) γ = (a.tamePart.ρ ⟨γ, hγ⟩).charpoly.roots := by
  rw [tameEig, lpTame_mk, inePol_of_mem _ hγ, charPol_mk]

theorem card_tameEig (x : WD h) {γ : G E Ω} (hγ : γ ∈ Weil h) :
    Multiset.card (tameEig x γ) = lpDim (lpTame x) := by
  rw [tameEig, inePol_of_mem _ hγ]; exact card_eig _ _

theorem tameEig_lpSum (x y : WD h) {γ : G E Ω} (hγ : γ ∈ Weil h) :
    tameEig (lpSum x y) γ = tameEig x γ + tameEig y γ := by
  induction x using ind with
  | hP n a =>
    induction y using ind with
    | hP m b =>
      rw [lpSum_mk, tameEig_mk _ hγ, tameEig_mk _ hγ, tameEig_mk _ hγ,
        (a.tamePart_sum b).charpoly_eq, WDRep.sum_ρ, LinearMap.charpoly_prodMap,
        roots_mul ((LinearMap.charpoly_monic _).mul (LinearMap.charpoly_monic _)).ne_zero]

theorem exists_pow_tameEig (x : WD h) {γ : G E Ω} (hγ : γ ∈ Ine (F := E) A) :
    ∃ n : ℕ, 0 < n ∧ n.Coprime (normV w) ∧ ∀ z ∈ tameEig x γ, z ^ n = 1 := by
  induction x using ind with
  | hP m a =>
    obtain ⟨n, h0, hc, hn⟩ := a.tame_tamePart.exists_pow_eq_one (γ := ⟨γ, Ine_le_Weil h hγ⟩) hγ
    refine ⟨n, h0, hc, fun z hz => ?_⟩
    rw [tameEig_mk _ (Ine_le_Weil h hγ), mem_roots (LinearMap.charpoly_monic _).ne_zero,
      ← End.hasEigenvalue_iff_isRoot_charpoly] at hz
    obtain ⟨v, hv⟩ := hz.exists_hasEigenvector
    have h1 := hv.pow_apply n
    rw [hn, End.one_apply] at h1
    exact smul_left_injective ℂ hv.2 (h1.symm.trans (one_smul ℂ v).symm)

theorem tameEig_map_pow (x : WD h) {γ : G E Ω} (hγ : γ ∈ Ine (F := E) A) :
    (tameEig x γ).map (· ^ normV w) = tameEig x γ := by
  induction x using ind with
  | hP m a =>
    rw [tameEig_mk _ (Ine_le_Weil h hγ)]
    exact a.tame_tamePart.roots_map_pow hγ

end WD

variable {g : ℕ} [Fact g.Prime]

variable (A w) in

def TeichmullerInertiaLabelCondition (τ : Fbar g →* ℂ) (γ : G E Ω) : Prop :=
  normV w = g ∧ γ ∈ Ine (F := E) A ∧ IsTeich τ

omit [IsAlgClosure E Ω] in

theorem TeichmullerInertiaLabelCondition.of_tameGenAt {τ : Fbar g →* ℂ} {γ : G E Ω} (hw : normV w = g)
    (hγ : TameGenAt A γ) (hτ : ∀ x y, x ≠ 0 → y ≠ 0 → τ x = τ y → x = y) : TeichmullerInertiaLabelCondition A w τ γ :=
  ⟨hw, hγ.1, hτ⟩

namespace WD

variable {h : IsPlaceOver A w} {τ : Fbar g →* ℂ} {γ : G E Ω}
variable {V V' : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']

theorem existsUnique_lab (H : TeichmullerInertiaLabelCondition A w τ γ) (x : WD h) :
    ∃! f : (ZMod g)[X], f.Monic ∧ (rootsBar f).map τ = tameEig x γ := by
  obtain ⟨n, h0, hc, hn⟩ := exists_pow_tameEig x H.2.1
  have h2 := tameEig_map_pow x H.2.1
  rw [H.1] at hc h2
  exact H.2.2.existsUnique_monic (fun z hz => H.2.2.exists_eq h0 hc (hn z hz)) h2

open Classical in

def lab (τ : Fbar g →* ℂ) (γ : G E Ω) (x : WD h) : (ZMod g)[X] :=
  if H : TeichmullerInertiaLabelCondition A w τ γ then (existsUnique_lab H x).choose else 1

theorem lab_of_not (H : ¬ TeichmullerInertiaLabelCondition A w τ γ) (x : WD h) : lab τ γ x = 1 := dif_neg H

theorem lab_monic (τ : Fbar g →* ℂ) (γ : G E Ω) (x : WD h) : (lab τ γ x).Monic := by
  unfold lab
  split_ifs with H
  · exact (existsUnique_lab H x).choose_spec.1.1
  · exact monic_one

theorem map_rootsBar_lab (H : TeichmullerInertiaLabelCondition A w τ γ) (x : WD h) :
    (rootsBar (lab τ γ x)).map τ = tameEig x γ := by
  rw [lab, dif_pos H]
  exact (existsUnique_lab H x).choose_spec.1.2

theorem lab_eq_iff (H : TeichmullerInertiaLabelCondition A w τ γ) (x : WD h) {f : (ZMod g)[X]} :
    lab τ γ x = f ↔ f.Monic ∧ (rootsBar f).map τ = tameEig x γ :=
  ⟨fun e => e ▸ ⟨lab_monic τ γ x, map_rootsBar_lab H x⟩,
    fun hf => (existsUnique_lab H x).unique ⟨lab_monic τ γ x, map_rootsBar_lab H x⟩ hf⟩

theorem lab_congr {x y : WD h} (e : γ ∈ Ine (F := E) A → tameEig x γ = tameEig y γ) :
    lab τ γ x = lab τ γ y := by
  by_cases H : TeichmullerInertiaLabelCondition A w τ γ
  · rw [lab_eq_iff H, e H.2.1]; exact ⟨lab_monic τ γ y, map_rootsBar_lab H y⟩
  · rw [lab_of_not H, lab_of_not H]

theorem inePol_lpTame (H : TeichmullerInertiaLabelCondition A w τ γ) (x : WD h) :
    inePol (lpTame x) γ = ((rootsBar (lab τ γ x)).map fun y => X - C (τ y)).prod := by
  have h1 := map_rootsBar_lab H x
  rw [tameEig, inePol_of_mem _ (Ine_le_Weil h H.2.1)] at h1
  rw [inePol_of_mem _ (Ine_le_Weil h H.2.1), charPol_eq_prod, eig, ← h1, Multiset.map_map]
  rfl

theorem natDegree_lab (H : TeichmullerInertiaLabelCondition A w τ γ) (x : WD h) :
    (lab τ γ x).natDegree = lpDim (lpTame x) := by
  rw [← GlobalTheory.TameLabels.card_rootsBar, ← card_tameEig x (Ine_le_Weil h H.2.1),
    ← map_rootsBar_lab H x, Multiset.card_map]

theorem natDegree_lab_le (τ : Fbar g →* ℂ) (γ : G E Ω) (x : WD h) :
    (lab τ γ x).natDegree ≤ lpDim x := by
  by_cases H : TeichmullerInertiaLabelCondition A w τ γ
  · rw [natDegree_lab H]; exact lpDim_lpTame_le x
  · rw [lab_of_not H, natDegree_one]; exact Nat.zero_le _

theorem natDegree_lab_eq_iff (H : TeichmullerInertiaLabelCondition A w τ γ) (x : WD h) :
    (lab τ γ x).natDegree = lpDim x ↔ tame x := by
  rw [natDegree_lab H, tame_iff_lpDim]

theorem tame_of_natDegree_lab {x : WD h} (hx : (lab τ γ x).natDegree = lpDim x) : tame x := by
  by_cases H : TeichmullerInertiaLabelCondition A w τ γ
  · exact (natDegree_lab_eq_iff H x).mp hx
  · rw [lab_of_not H, natDegree_one] at hx
    have := lpDim_lpTame_le x
    rw [tame_iff_lpDim]; omega

theorem inePol_wild_of_natDegree_lab {x : WD h} (hx : (lab τ γ x).natDegree = lpDim x)
    {σ : G E Ω} (hσ : ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1) :
    inePol x σ = (X - 1) ^ lpDim x :=
  (tame_iff_inePol x).mp (tame_of_natDegree_lab hx) σ hσ

theorem lab_coeff_zero_ne_zero (τ : Fbar g →* ℂ) (γ : G E Ω) (x : WD h) :
    (lab τ γ x).coeff 0 ≠ 0 := by
  by_cases H : TeichmullerInertiaLabelCondition A w τ γ
  · rw [Ne, ← GlobalTheory.Compare.TeichmullerRoots.zero_mem_rootsBar (lab_monic τ γ x)]
    intro h0
    obtain ⟨n, hn, -, h1⟩ := exists_pow_tameEig x H.2.1
    have h2 := h1 (τ 0) (map_rootsBar_lab H x ▸ Multiset.mem_map_of_mem τ h0)
    rw [H.2.2.map_zero, zero_pow hn.ne'] at h2
    exact zero_ne_one h2
  · simp [lab_of_not H]

theorem inePol_eq_of_natDegree_lab (τ : Fbar g →* ℂ) (γ : G E Ω) (x : WD h)
    (hx : (lab τ γ x).natDegree = lpDim x) :
    inePol x γ = ((rootsBar (lab τ γ x)).map fun y => X - C (τ y)).prod := by
  by_cases H : TeichmullerInertiaLabelCondition A w τ γ
  · rw [← inePol_lpTame H x, show lpTame x = x from tame_of_natDegree_lab hx]
  · rw [lab_of_not H, natDegree_one] at hx
    have h1 : rootsBar (1 : (ZMod g)[X]) = 0 := by simp [rootsBar]
    rw [lab_of_not H, h1, Multiset.map_zero, Multiset.prod_zero]
    by_cases hγ : γ ∈ Weil h
    · rw [inePol_of_mem _ hγ]
      exact (charPol_monic x _).natDegree_eq_zero.mp ((charPol_natDegree x _).trans hx.symm)
    · exact inePol_of_not_mem x hγ

theorem lab_of_lpDim_eq_zero (τ : Fbar g →* ℂ) (γ : G E Ω) {x : WD h} (hx : lpDim x = 0) :
    lab τ γ x = 1 :=
  (lab_monic τ γ x).natDegree_eq_zero.mp (Nat.le_zero.mp (hx ▸ natDegree_lab_le τ γ x))

@[simp] theorem lab_lpZero (τ : Fbar g →* ℂ) (γ : G E Ω) : lab τ γ (lpZero h) = 1 :=
  lab_of_lpDim_eq_zero τ γ (by simp [lpZero])

theorem lab_lpSum (τ : Fbar g →* ℂ) (γ : G E Ω) (x y : WD h) :
    lab τ γ (lpSum x y) = lab τ γ x * lab τ γ y := by
  by_cases H : TeichmullerInertiaLabelCondition A w τ γ
  · have hm := (lab_monic τ γ x).mul (lab_monic τ γ y)
    rw [lab_eq_iff H, GlobalTheory.TameLabels.rootsBar_mul hm.ne_zero, Multiset.map_add, map_rootsBar_lab H,
      map_rootsBar_lab H, tameEig_lpSum _ _ (Ine_le_Weil h H.2.1)]
    exact ⟨hm, rfl⟩
  · simp [lab_of_not H]

theorem lab_mk_congr {a : WDRep h V} {b : WDRep h V'} (e : V ≃ₗ[ℂ] V')
    (he : ∀ σ : Weil h, (σ : G E Ω) ∈ Ine (F := E) A → ∀ v, e (a.ρ σ v) = b.ρ σ (e v))
    (τ : Fbar g →* ℂ) (γ : G E Ω) : lab τ γ (mk a) = lab τ γ (mk b) :=
  lab_congr fun hγ => by
    rw [tameEig_mk _ (Ine_le_Weil h hγ), tameEig_mk _ (Ine_le_Weil h hγ),
      WDRep.charpoly_tamePart_congr e he hγ]

theorem lab_lpTwist (τ : Fbar g →* ℂ) (γ : G E Ω) (x : WD h) {χ : Weil h →* ℂˣ} (hχ : IsSmooth χ)
    (h1 : ∀ σ : Ine (F := E) A, χ (ineIncl h σ) = 1) : lab τ γ (lpTwist x χ hχ) = lab τ γ x := by
  induction x using ind with
  | hP n a =>
    rw [lpTwist_mk]
    refine lab_mk_congr (.refl _ _) (fun σ hσ v => ?_) τ γ
    have : χ σ = 1 := h1 ⟨σ, hσ⟩
    simp [this]

theorem lab_lpTw (τ : Fbar g →* ℂ) (γ : G E Ω) (x : WD h) (s : ℝ) :
    lab τ γ (lpTw x s) = lab τ γ x :=
  lab_lpTwist τ γ x _ fun σ => by simp

theorem lab_eq_iff_of_tame (H : TeichmullerInertiaLabelCondition A w τ γ) {x : WD h} (hx : tame x) {f : (ZMod g)[X]} :
    lab τ γ x = f ↔ f.Monic ∧ (rootsBar f).map τ = (inePol x γ).roots := by
  rw [lab_eq_iff H, tameEig, show lpTame x = x from hx]

theorem rootsBar_X_sub_C_pow (c : ZMod g) (n : ℕ) :
    rootsBar ((X - C c) ^ n) = n • {algebraMap (ZMod g) (Fbar g) c} := by
  rw [rootsBar, Polynomial.map_pow, Polynomial.map_sub, map_X, map_C, roots_pow, roots_X_sub_C]

theorem lab_mk_of_trivial (H : TeichmullerInertiaLabelCondition A w τ γ) (a : WDRep h V)
    (ha : ∀ σ : Ine (F := E) A, a.ρ (ineIncl h σ) = 1) :
    lab τ γ (mk a) = (X - 1) ^ finrank ℂ V := by
  rw [lab_eq_iff_of_tame H ((tame_mk a).mpr fun σ hσ => ha ⟨σ, Wild_le_Ine hσ⟩), ← C_1,
    rootsBar_X_sub_C_pow, inePol_of_mem_Ine _ H.2.1, charPol_mk, ha, LinearMap.charpoly_one, ← C_1,
    roots_pow, roots_X_sub_C]
  exact ⟨(monic_X_sub_C _).pow _, by simp [Multiset.map_nsmul]⟩

theorem lab_lpSp (H : TeichmullerInertiaLabelCondition A w τ γ) (n : ℕ) : lab τ γ (lpSp h n) = (X - 1) ^ n := by
  rw [lpSp, lab_mk_of_trivial H (WDRep.sp h n) (WDRep.unr_diag (WDRep.spEig w n)).2]
  simp

theorem lab_lpOfChar_eq_iff (H : TeichmullerInertiaLabelCondition A w τ γ) {χ : Weil h →* ℂˣ} (hχ : IsSmooth χ)
    (ht : ∀ σ : Weil h, (σ : G E Ω) ∈ Wild E A → χ σ = 1) (c : ZMod g) :
    lab τ γ (lpOfChar h χ hχ) = X - C c ↔
      τ (algebraMap (ZMod g) (Fbar g) c) = χ ⟨γ, Ine_le_Weil h H.2.1⟩ := by
  have h1 : tame (lpOfChar h χ hχ) := (tame_mk _).mpr fun σ hσ =>
    LinearMap.ext fun v => funext fun i => by simp [ht σ hσ]
  have h2 := rootsBar_X_sub_C_pow c 1
  rw [pow_one, one_nsmul] at h2
  rw [lab_eq_iff_of_tame H h1, h2, inePol_of_mem _ (Ine_le_Weil h H.2.1), lpOfChar, charPol_mk,
    WDRep.ofChars_ρ, charpoly_diagEnd, Fin.prod_univ_one, roots_X_sub_C, Multiset.map_singleton,
    Multiset.singleton_inj]
  exact and_iff_right (monic_X_sub_C c)

theorem lab_lpOfChar_of_wild (τ : Fbar g →* ℂ) (γ : G E Ω) {χ : Weil h →* ℂˣ} (hχ : IsSmooth χ)
    {σ : Weil h} (hσ : (σ : G E Ω) ∈ Wild E A) (h1 : χ σ ≠ 1) : lab τ γ (lpOfChar h χ hχ) = 1 := by
  have hd : lpDim (lpOfChar h χ hχ) = 1 := by simp [lpOfChar]
  have h2 := natDegree_lab_le τ γ (lpOfChar h χ hχ)
  have h3 : (lab τ γ (lpOfChar h χ hχ)).natDegree ≠ lpDim (lpOfChar h χ hχ) := fun e => by
    have := congrFun (LinearMap.congr_fun
      ((tame_mk _).mp (tame_of_natDegree_lab e) σ hσ) fun _ => 1) 0
    exact h1 (Units.ext (by simpa using this))
  exact (lab_monic τ γ _).natDegree_eq_zero.mp (by omega)

end WD

theorem IsSmooth.eq_one_of_tameGenAt {h : IsPlaceOver A w} {M : Type*} [Monoid M]
    {f : Weil h →* M} (hf : IsSmooth f) {γ : G E Ω} (hγ : TameGenAt A γ)
    (h1 : f (ineIncl h ⟨γ, hγ.1⟩) = 1) (h2 : ∀ σ : Weil h, (σ : G E Ω) ∈ Wild E A → f σ = 1)
    (σ : Ine (F := E) A) : f (ineIncl h σ) = 1 := by
  let K : Subgroup (Ine (F := E) A) := (f.comp (ineIncl h)).ker
  have hK : IsClosed ((K.map (Ine (F := E) A).subtype : Subgroup (G E Ω)) : Set (G E Ω)) :=
    (isClosed_Ine A).isClosedEmbedding_subtypeVal.isClosedMap _ (K.isClosed_of_isOpen hf)
  have hle : Subgroup.closure (insert γ (Wild E A : Set (G E Ω))) ≤
      K.map (Ine (F := E) A).subtype := by
    rw [Subgroup.closure_le]
    rintro u (rfl | hu)
    · exact ⟨⟨u, hγ.1⟩, h1, rfl⟩
    · exact ⟨⟨u, Wild_le_Ine hu⟩, h2 _ hu, rfl⟩
  obtain ⟨u, hu, e⟩ := closure_minimal (SetLike.coe_subset_coe.mpr hle) hK (hγ.2 σ.2)
  rwa [← Subtype.ext (a1 := u) (a2 := σ) e]

theorem exists_tameInertiaSetting (h : IsPlaceOver A w) (hw : normV w = g) :
    ∃ (τ : Fbar g →* ℂ) (γ : G E Ω), TameGenAt A γ ∧ TeichmullerInertiaLabelCondition A w τ γ := by
  obtain ⟨γ, hγ⟩ := GlobalTheory.MemTame.exists_tameGenAt E Ω w A h
  obtain ⟨τ, hτ⟩ := (GlobalTheory.MemN.exists_teichmuller_maps g Fact.out).1
  exact ⟨τ, γ, hγ, .of_tameGenAt hw hγ hτ⟩

theorem exists_normV_eq (g : ℕ) (hg : g.Prime) : ∃ v : HeightOneSpectrum (𝓞 ℚ), normV v = g := by
  obtain ⟨p, hp⟩ := (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).surjective ⟨g, hg⟩
  have hp' : Rat.HeightOneSpectrum.natGenerator p = g := congrArg Subtype.val hp
  have e := Ideal.quotientEquiv p.asIdeal _ (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ))
    (Rat.HeightOneSpectrum.span_natGenerator p)
  refine ⟨p, ?_⟩
  rw [normV, Nat.card_congr e.toEquiv, hp']
  simpa using Nat.card_congr (Int.quotientSpanNatEquivZMod g).toEquiv

open Classical in

def sqrtChar (h : IsPlaceOver A w) {x : Ω} {a : E} (hx : x ^ 2 = algebraMap E Ω a) :
    Weil h →* ℂˣ :=
  MonoidHom.mk' (fun σ => if (σ : G E Ω) x = x then 1 else -1) fun σ σ' => by
    have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
    have key : ∀ u : G E Ω, u x = x ∨ u x = -x := fun u =>
      sq_eq_sq_iff_eq_or_eq_neg.mp (by rw [← map_pow, hx, AlgEquiv.commutes])
    rcases eq_or_ne x 0 with rfl | h0
    · simp
    have hne : -x ≠ x := fun e => h0 (CharZero.neg_eq_self_iff.mp e)
    rcases key σ with h1 | h1 <;> rcases key σ' with h2 | h2 <;> simp [h1, h2, hne]

omit [IsAlgClosure E Ω] in

theorem sqrtChar_eq_one_iff (h : IsPlaceOver A w) {x : Ω} {a : E} (hx : x ^ 2 = algebraMap E Ω a)
    (σ : Weil h) : sqrtChar h hx σ = 1 ↔ (σ : G E Ω) x = x := by
  simp only [sqrtChar, MonoidHom.mk'_apply, ite_eq_left_iff]
  refine ⟨fun e => by_contra fun hc => ?_, fun e hc => absurd e hc⟩
  have := congrArg Units.val (e hc)
  norm_num at this

theorem isSmooth_sqrtChar (h : IsPlaceOver A w) {x : Ω} {a : E} (hx : x ^ 2 = algebraMap E Ω a) :
    IsSmooth (sqrtChar h hx) :=
  .of_open ((isOpen_setOf_apply (F := E) x fun t => t = x).preimage continuous_subtype_val) rfl
    fun _ hσ => (sqrtChar_eq_one_iff h hx _).mpr hσ

example (K : Type) [Field K] [Algebra ℚ K] [IsAlgClosure ℚ K] :
    ∃ (v : HeightOneSpectrum (𝓞 ℚ)) (B : ValuationSubring K)
      (hB : IsPlaceOver B v) (τ : Fbar g →* ℂ) (γ : G ℚ K), TameGenAt B γ ∧
      WD.lab τ γ (WD.lpSum (WD.lpSp hB 2) (WD.lpSp hB 1)) = (X - 1) ^ 3 := by
  obtain ⟨v, hv⟩ := exists_normV_eq g Fact.out
  have hB := isPlaceOver_placeOf K v
  obtain ⟨τ, γ, hγ, H⟩ := exists_tameInertiaSetting hB hv
  exact ⟨v, _, hB, τ, γ, hγ, by rw [WD.lab_lpSum, WD.lab_lpSp H, WD.lab_lpSp H, ← pow_add]⟩

example {h : IsPlaceOver A w} {τ : Fbar g →* ℂ} {γ : G E Ω} (H : TeichmullerInertiaLabelCondition A w τ γ)
    {χ : Weil h →* ℂˣ} (hχ : IsSmooth χ) (ht : ∀ σ : Weil h, (σ : G E Ω) ∈ Wild E A → χ σ = 1)
    (c : ZMod g) (hc : (χ ⟨γ, Ine_le_Weil h H.2.1⟩ : ℂ) = τ (algebraMap _ _ c)) :
    WD.lab τ γ (WD.lpOfChar h χ hχ) = X - C c :=
  (WD.lab_lpOfChar_eq_iff H hχ ht c).mpr hc.symm

example (p : ℕ) (hp : p.Prime) (h : IsPlaceOver A w) (τ : Fb p hp →* ℂ) (γ : G E Ω) (x : WD h) :
    haveI : Fact p.Prime := ⟨hp⟩
    (WD.lab τ γ x).natDegree = x.lpDim →
      x.inePol γ = ((rootsBar (WD.lab τ γ x)).map fun y => X - C (τ y)).prod :=
  haveI : Fact p.Prime := ⟨hp⟩
  WD.inePol_eq_of_natDegree_lab τ γ x

end GlobalTheory.WeilDeligne
