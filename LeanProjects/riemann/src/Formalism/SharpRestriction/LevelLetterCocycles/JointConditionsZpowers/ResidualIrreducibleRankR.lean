import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations

noncomputable section

namespace Formalism.MainNotions.N

open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial

open NumberField IsDedekindDomain

open scoped Pointwise

theorem l_not_unit (D : D7) (a : D.nd.Loc) : ¬ IsUnit ((D.nd.l a : ℕ) : D.nd.O a) := by
  intro hu
  have hfg : (⊤ : Submodule ℤ_[D.nd.l a] (D.nd.O a)).FG := Module.Finite.fg_top
  have hle : (⊤ : Submodule ℤ_[D.nd.l a] (D.nd.O a)) ≤
      (Ideal.span {(D.nd.l a : ℤ_[D.nd.l a])}) • (⊤ : Submodule ℤ_[D.nd.l a] (D.nd.O a)) := by
    intro y _
    obtain ⟨u, hu'⟩ := hu
    have : y = (D.nd.l a : ℤ_[D.nd.l a]) • (((u⁻¹ : (D.nd.O a)ˣ) : D.nd.O a) * y) := by
      rw [Algebra.smul_def, map_natCast, ← hu', ← mul_assoc, Units.mul_inv, one_mul]
    rw [this]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) trivial
  have hjac : Ideal.span {(D.nd.l a : ℤ_[D.nd.l a])} ≤ Ideal.jacobson ⊥ := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top, PadicInt.maximalIdeal_eq_span_p]
  exact top_ne_bot (Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ _ hfg hle hjac)

theorem res_T_indep (D : D7) (a : D.nd.Loc) (f : D.nd.T a) (x x' : D.nd.X a) :
    IsLocalRing.residue (D.nd.O a) ((f : D.nd.X a → D.nd.O a) x) =
      IsLocalRing.residue (D.nd.O a) ((f : D.nd.X a → D.nd.O a) x') := by
  have := D.nd.T_local a
  let ev : D.nd.X a → (D.nd.T a →+* IsLocalRing.ResidueField (D.nd.O a)) := fun y =>
    (IsLocalRing.residue (D.nd.O a)).comp
      ((Pi.evalRingHom (fun _ : D.nd.X a => D.nd.O a) y).comp (D.nd.T a).val.toRingHom)
  have hsurj : ∀ y, Function.Surjective (ev y) := by
    intro y c
    obtain ⟨c', rfl⟩ := IsLocalRing.residue_surjective c
    exact ⟨algebraMap (D.nd.O a) (D.nd.T a) c', rfl⟩
  have hker : ∀ y, RingHom.ker (ev y) = IsLocalRing.maximalIdeal (D.nd.T a) := fun y =>
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective (ev y) (hsurj y))
  have h1 : f - algebraMap (D.nd.O a) (D.nd.T a) ((f : D.nd.X a → D.nd.O a) x) ∈ RingHom.ker (ev x) := by
    rw [RingHom.mem_ker, map_sub]
    exact sub_self _
  rw [hker x, ← hker x', RingHom.mem_ker, map_sub, sub_eq_zero] at h1
  exact h1.symm

theorem heckePol_res (D : D7) (a : D.nd.Loc) (x x' : D.nd.X a) (w : PlE D.host) :
    (heckePol D.nd a x w).map (IsLocalRing.residue (D.nd.O a)) =
      (heckePol D.nd a x' w).map (IsLocalRing.residue (D.nd.O a)) := by
  unfold heckePol
  simp only [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_sum,
    Polynomial.map_mul, Polynomial.map_C, map_mul]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [res_T_indep D a (D.nd.hT a w k) x x']

theorem isOpen_res_fiber (D : D7) (a : D.nd.Loc) (c : IsLocalRing.ResidueField (D.nd.O a)) :
    IsOpen {y : D.nd.O a | IsLocalRing.residue (D.nd.O a) y = c} := by
  have hm : IsOpen ((IsLocalRing.maximalIdeal (D.nd.O a) : Ideal _) : Set (D.nd.O a)) := by
    have := (isAdic_iff.mp (D.nd.O_adic a)).1 1
    rwa [pow_one] at this
  rw [isOpen_iff_mem_nhds]
  intro y0 hy0
  have hc : Continuous fun y : D.nd.O a => y - y0 := continuous_id.sub continuous_const
  have hU := (hm.preimage hc).mem_nhds (x := y0) (by simp)
  refine Filter.mem_of_superset hU fun y hy => ?_
  have : IsLocalRing.residue (D.nd.O a) (y - y0) = 0 := (IsLocalRing.residue_eq_zero_iff _).mpr hy
  rw [map_sub, sub_eq_zero] at this
  exact this.trans hy0

section Defs

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂)

def IsRhoOf (a : N.Loc) (x : N.X a) (ρ : G H.E N.Om →* GL (Fin R.r) (N.O a)) : Prop :=
  Continuous (fun g => ((ρ g : GL (Fin R.r) (N.O a)) : Matrix (Fin R.r) (Fin R.r) (N.O a))) ∧
  IsSSRep (mapRep (algebraMap (N.O a) (Kf N a)) ρ) ∧
  ∀ w, SplitOut N a w → ∀ (B : ValuationSubring N.Om) (σ : G H.E N.Om),
    IsPlaceOver (F := H.E) B w → IsFrob (F := H.E) B (normV w) σ →
    ((ρ σ : GL _ _) : Matrix (Fin R.r) (Fin R.r) (N.O a)).charpoly *
      ∏ c ∈ Finset.Icc 1 R.t, (X - C ((N.chi a c σ : (N.O a)ˣ) : N.O a)) = heckePol N a x w

end Defs

def rhoAt (D : D7) (a : D.nd.Loc) {i : D.ntw.Tw} (h : D.ntw.twOf a = i) (s : D.ntw.Sig i) :
    G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.nd.O a) := by
  subst h
  exact mapRep (D.ntw.twist₂ a) (D.ntw.rhoS _ s)

def SideLoc (D : D7) (i : D.ntw.Tw) (b : Bool) : Prop :=
  ∃ a : D.nd.Loc, D.ntw.twOf a = i ∧ D.ntw.twSide a = b

def SelfPair (D : D7) (i : D.ntw.Tw) : Prop :=
  ∀ x : NumberField.RingOfIntegers D.LL0,
    (∃ y ∈ IsLocalRing.maximalIdeal (D.ntw.O0 i),
      algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i)) y = D.ntw.emb0 i (x : D.LL0)) ↔
    (∃ y ∈ IsLocalRing.maximalIdeal (D.ntw.O0 i),
      algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i)) y = D.ntw.emb0b i (x : D.LL0))

def NoSelfPair (D : D7) : Prop := ∀ i, D.ntw.NonzeroIndexPlace i → ¬ SelfPair D i

def SigTie (D : D7) : Prop :=
  ∀ (i : D.ntw.Tw), D.ntw.NonzeroIndexPlace i → ∀ (s : D.ntw.Sig i), SideLoc D i (D.ntw.side i s) →
    ∃ (a : D.nd.Loc) (h : D.ntw.twOf a = i),
      D.nd.j a = D.ntw.jS i s ∧ D.ntw.twSide a = D.ntw.side i s ∧ HG D.nd D.naut a ∧
      ∃ x ∈ D.nd.Z a, IsRhoOf D.nd a x (rhoAt D a h s)

def ResidualIrreducibleRankR (D : D7) : Prop :=
  ∀ a, HG D.nd D.naut a → ∀ rb, IsRhoBar D.nd a rb →
    Formalism.CyclotomicNorms.IrredOn (mapRep (D.naut.kFbar a) rb) ⊤ ∧
    ∀ k, D.nd.l a ≠ D.host.g k → ∀ v ∈ placesOver D.host.E (D.host.g k),
      ¬ (((rb (D.nd.gam0 a v) : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) _).charpoly).IsRoot
        (IsLocalRing.residue (D.nd.O a) (chi1 D.nd a (D.nd.gam0 a v)))

def LitBurnside (Γ : Type) [Group Γ] : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (a : ℕ) (ρ : Γ →* GL (Fin a) (Formalism.CyclotomicNorms.Fbar ℓ)), Formalism.CyclotomicNorms.IrredOn ρ ⊤ →
    Submodule.span (Formalism.CyclotomicNorms.Fbar ℓ)
      (Set.range fun g => ((ρ g : GL _ _) : Matrix (Fin a) (Fin a) (Formalism.CyclotomicNorms.Fbar ℓ))) = ⊤

theorem isRhoBar_of_isRhoOf (D : D7) (a : D.nd.Loc) (x : D.nd.X a)
    (ρ : G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.nd.O a)) (h : IsRhoOf D.nd a x ρ) :
    IsRhoBar D.nd a (redRep D.nd a ρ) := by
  refine ⟨?_, ?_⟩
  · have e : ((redRep D.nd a ρ).ker : Set (G D.host.E D.nd.Om)) =
        (fun g => ((ρ g : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O a))) ⁻¹'
          (⋂ p : Fin D.R.r × Fin D.R.r, {M | IsLocalRing.residue (D.nd.O a) (M p.1 p.2) =
            (1 : Matrix (Fin D.R.r) (Fin D.R.r) (IsLocalRing.ResidueField (D.nd.O a))) p.1 p.2}) := by
      ext g
      simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_preimage, Set.mem_iInter,
        Set.mem_ofPred_eq, Prod.forall]
      constructor
      · intro hg i j
        have := congrArg (fun u : GL (Fin D.R.r) (IsLocalRing.ResidueField (D.nd.O a)) =>
          u.val i j) hg
        exact this
      · intro hg
        apply Units.ext
        ext i j
        exact hg i j
    rw [e]
    refine IsOpen.preimage h.1 (isOpen_iInter_of_finite fun p => ?_)
    have hc : Continuous fun M : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O a) => M p.1 p.2 :=
      continuous_id.matrix_elem p.1 p.2
    exact (isOpen_res_fiber D a _).preimage hc
  · intro x' w hw B σ hB hσ
    rw [← heckePol_res D a x x' w, ← h.2.2 w hw B σ hB hσ, Polynomial.map_mul, Polynomial.map_prod]
    congr 1
    · exact Matrix.charpoly_map _ _
    · refine Finset.prod_congr rfl fun c _ => ?_
      simp

theorem span_descent {k L : Type} [Field k] [Field L] (φ : k →+* L) {n : ℕ} {ι : Type}
    (S : ι → Matrix (Fin n) (Fin n) k)
    (h : Submodule.span L (Set.range fun i => (S i).map φ) = ⊤) :
    Submodule.span k (Set.range S) = ⊤ := by
  by_contra hne
  obtain ⟨f, hf0, hf⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
  let c : Fin n → Fin n → k := fun i j => f (Matrix.single i j 1)
  have hfc : ∀ M : Matrix (Fin n) (Fin n) k, f M = ∑ i, ∑ j, M i j * c i j := by
    intro M
    conv_lhs => rw [Matrix.matrix_eq_sum_single M]
    simp only [map_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have : Matrix.single i j (M i j) = M i j • Matrix.single i j (1 : k) := by
      rw [Matrix.smul_single, smul_eq_mul, mul_one]
    rw [this, map_smul, smul_eq_mul]
  let F : Matrix (Fin n) (Fin n) L →ₗ[L] L :=
    ∑ i, ∑ j, (φ (c i j)) • Matrix.entryLinearMap L L i j
  have hF : ∀ M : Matrix (Fin n) (Fin n) L, F M = ∑ i, ∑ j, φ (c i j) * M i j := by
    intro M
    simp [F, LinearMap.sum_apply]
  have hker : Submodule.span L (Set.range fun i => (S i).map φ) ≤ LinearMap.ker F := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have h0 : f (S i) = 0 := hf (Submodule.subset_span ⟨i, rfl⟩)
    rw [hfc] at h0
    show F ((S i).map φ) = 0
    rw [hF]
    have := congrArg φ h0
    simp only [map_sum, map_mul, map_zero] at this
    rw [← this]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    rw [Matrix.map_apply, mul_comm]
  rw [h, top_le_iff, LinearMap.ker_eq_top] at hker
  apply hf0
  apply LinearMap.ext
  intro M
  rw [hfc]
  have hc : ∀ i j, c i j = 0 := by
    intro i j
    have := hF (Matrix.single i j 1)
    rw [hker, LinearMap.zero_apply] at this
    have h2 : ∑ p, ∑ q, φ (c p q) * (Matrix.single i j (1 : L)) p q = φ (c i j) := by
      rw [Finset.sum_eq_single i, Finset.sum_eq_single j]
      · simp
      · intro q _ hq
        simp [Matrix.single_apply, Ne.symm hq]
      · simp
      · intro p _ hp
        refine Finset.sum_eq_zero fun q _ => ?_
        simp [Matrix.single_apply, Ne.symm hp]
      · simp
    rw [h2] at this
    exact (map_eq_zero_iff φ φ.injective).mp this.symm
  simp [hc]

theorem conj_mem_Ine_smul {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    (A : ValuationSubring Ω) (τ σ : G F Ω) (hσ : σ ∈ Ine (F := F) A) :
    τ * σ * τ⁻¹ ∈ Ine (F := F) (τ • A) := by
  have hmem : ∀ x : Ω, x ∈ τ • A ↔ (τ⁻¹ : G F Ω) x ∈ A := by
    intro x
    rw [← ValuationSubring.smul_mem_pointwise_smul_iff (g := τ⁻¹), inv_smul_smul]
    rfl
  have hlt : ∀ y : Ω, (τ • A).valuation y < 1 ↔ A.valuation ((τ⁻¹ : G F Ω) y) < 1 := by
    intro y
    rw [valuation_lt_one_iff', valuation_lt_one_iff', hmem, hmem, map_inv₀,
      map_eq_zero_iff _ (τ⁻¹ : G F Ω).injective]
  refine ⟨?_, fun x hx => ?_⟩
  · show (τ * σ * τ⁻¹) • (τ • A) = τ • A
    rw [mul_smul, mul_smul, inv_smul_smul]
    congr 1
    exact hσ.1
  · rw [hlt]
    have hx' : A.valuation ((τ⁻¹ : G F Ω) x) ≤ 1 := by
      rw [A.valuation_le_one_iff, ← hmem]
      exact ((τ • A).valuation_le_one_iff x).mp hx
    have e : (τ⁻¹ : G F Ω) ((τ * σ * τ⁻¹) x - x) = σ ((τ⁻¹ : G F Ω) x) - (τ⁻¹ : G F Ω) x := by
      rw [map_sub]
      congr 1
      show (τ⁻¹ * (τ * σ * τ⁻¹)) x = _
      rw [← mul_assoc, ← mul_assoc, inv_mul_cancel, one_mul]
      rfl
    rw [e]
    exact hσ.2 _ hx'

theorem placesOver_disj (E : Type) [Field E] [NumberField E] {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (v : HeightOneSpectrum (𝓞 E)) (h1 : v ∈ placesOver E p) : v ∉ placesOver E q := by
  intro h2
  have hco : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
  have h1' : ((p : ℤ) : 𝓞 E) ∈ v.asIdeal := by
    have : ((p : ℕ) : 𝓞 E) ∈ v.asIdeal := h1
    simpa using this
  have h2' : ((q : ℤ) : 𝓞 E) ∈ v.asIdeal := by
    have : ((q : ℕ) : 𝓞 E) ∈ v.asIdeal := h2
    simpa using this
  have hb : (1 : 𝓞 E) ∈ v.asIdeal := by
    have hg := Nat.gcd_eq_gcd_ab p q
    rw [hco.gcd_eq_one] at hg
    have : (1 : 𝓞 E) = ((p : ℤ) : 𝓞 E) * ((Nat.gcdA p q : ℤ) : 𝓞 E) + ((q : ℤ) : 𝓞 E) * ((Nat.gcdB p q : ℤ) : 𝓞 E) := by
      have := congrArg (fun z : ℤ => (z : 𝓞 E)) hg
      push_cast at this
      simpa using this
    rw [this]
    exact v.asIdeal.add_mem (v.asIdeal.mul_mem_right _ h1') (v.asIdeal.mul_mem_right _ h2')
  exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr hb)

end Formalism.MainNotions.N
