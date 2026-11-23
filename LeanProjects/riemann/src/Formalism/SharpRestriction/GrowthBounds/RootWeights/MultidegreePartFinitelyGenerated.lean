import Formalism.SharpRestriction.GrowthBounds.RootWeights.DividedPowerMonomialExpansion

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

def fockLattice {p : ℕ} (hV : ValuationProperties p O) (σ : Type) : Submodule O (MvPolynomial σ (KK O)) where
  carrier := {F | InBB (O := O) p F}
  zero_mem' := fock_lattice_zero_mem hV
  add_mem' := fun hF hG => fock_lattice_add_mem hV hF hG
  smul_mem' := fun o _ hF => fock_lattice_smul_mem hV o hF

theorem multidegree_monomials_finite {ι : Type} [Fintype ι] {n : ℕ} (d : ι → ℕ) :
    {m : ι × Fin n →₀ ℕ | ∀ i, multideg m i = d i}.Finite := by
  classical
  refine (Set.finite_Iic (Finsupp.equivFunOnFinite.symm (fun x : ι × Fin n => d x.1))).subset ?_
  intro m hm
  rw [Set.mem_Iic, Finsupp.le_def]
  rintro ⟨i, c⟩
  simp only [Finsupp.coe_equivFunOnFinite_symm]
  rw [← hm i]
  exact Finset.single_le_sum (f := fun c' => m (i, c')) (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)

theorem multidegree_part_finitely_generated {p : ℕ} (hp0 : (p : KK O) ≠ 0) {ι : Type} [Fintype ι] {n : ℕ}
    (L : Submodule O (MvPolynomial (ι × Fin n) (KK O))) (d : ι → ℕ) (N : ℕ)
    (h : ∀ F ∈ L, ∀ m, (∀ i, multideg m i = d i) → ∃ o : O, (p : KK O) ^ N * F.coeff m = algebraMap O (KK O) o) :
    (latticeMultidegreePart L d).FG := by
  classical
  set S := (multidegree_monomials_finite (ι := ι) (n := n) d).toFinset with hS
  let f : ↥(Pol (KK O) n d) →ₗ[O] (S → KK O) :=
    { toFun := fun F s => (p : KK O) ^ N * (F : MvPolynomial (ι × Fin n) (KK O)).coeff s.1
      map_add' := fun F G => by
        funext s
        simp [mul_add]
      map_smul' := fun o F => by
        funext s
        simp [MvPolynomial.coeff_smul, mul_smul_comm] }
  let g : (S → O) →ₗ[O] (S → KK O) :=
    LinearMap.pi (fun s => (Algebra.linearMap O (KK O)).comp (LinearMap.proj s))
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro F hF
    apply Subtype.ext
    ext m
    simp only [Submodule.coe_zero, MvPolynomial.coeff_zero]
    by_cases hm : m ∈ S
    · have h0 := congrFun hF ⟨m, hm⟩
      change (p : KK O) ^ N * (F : MvPolynomial _ (KK O)).coeff m = 0 at h0
      exact (mul_eq_zero.1 h0).resolve_left (pow_ne_zero _ hp0)
    · by_contra hne
      apply hm
      have hF2 : (F : MvPolynomial (ι × Fin n) (KK O)) ∈
          MvPolynomial.restrictSupport (KK O) {m | ∀ i, multideg m i = d i} := F.2
      have hsupp : m ∈ (F : MvPolynomial _ (KK O)).support := MvPolynomial.mem_support_iff.2 hne
      exact (Set.Finite.mem_toFinset _).2 (((MvPolynomial.mem_restrictSupport_iff _).1 hF2) (Finset.mem_coe.2 hsupp))
  have hle : (latticeMultidegreePart L d).map f ≤ LinearMap.range g := by
    rintro _ ⟨x, hx, rfl⟩
    have hx' : (x : MvPolynomial (ι × Fin n) (KK O)) ∈ L := hx
    choose o ho using fun s : S => h _ hx' s.1 ((Set.Finite.mem_toFinset _).1 s.2)
    refine ⟨o, ?_⟩
    funext s
    exact (ho s).symm
  have hW : (LinearMap.range g).FG := by
    rw [LinearMap.range_eq_map]
    exact (Module.Finite.fg_top).map g
  haveI : IsNoetherian O (LinearMap.range g) := isNoetherian_of_fg_of_noetherian _ hW
  have h1 : (((latticeMultidegreePart L d).map f).comap (LinearMap.range g).subtype).FG := IsNoetherian.noetherian _
  have h2 := h1.map (LinearMap.range g).subtype
  rw [Submodule.map_comap_subtype, inf_eq_right.2 hle] at h2
  exact Submodule.fg_of_fg_map_injective f hinj h2

theorem multidegree_part_spans {ι : Type} [Fintype ι] {n : ℕ}
    (L : Submodule O (MvPolynomial (ι × Fin n) (KK O))) (d : ι → ℕ)
    (h : ∀ m, monomial m (1 : KK O) ∈ L) : MQ (K := KK O) (latticeMultidegreePart L d) = ⊤ := by
  classical
  rw [eq_top_iff]
  rintro x -
  have hx : (x : MvPolynomial (ι × Fin n) (KK O)) ∈
      MvPolynomial.restrictSupport (KK O) {m | ∀ i, multideg m i = d i} := x.2
  have key : ∀ m ∈ (x : MvPolynomial (ι × Fin n) (KK O)).support,
      monomial m (1 : KK O) ∈ Pol (KK O) n d := by
    intro m hm
    show monomial m (1 : KK O) ∈ MvPolynomial.restrictSupport (KK O) {m | ∀ i, multideg m i = d i}
    rw [MvPolynomial.mem_restrictSupport_iff]
    intro m' hm'
    rw [Finset.mem_coe] at hm'
    have hm'' := MvPolynomial.support_monomial_subset hm'
    rw [Finset.mem_singleton] at hm''
    subst hm''
    exact ((MvPolynomial.mem_restrictSupport_iff _).1 hx) (Finset.mem_coe.2 hm)
  have hx2 : x = ∑ m ∈ (x : MvPolynomial (ι × Fin n) (KK O)).support.attach,
      (x : MvPolynomial (ι × Fin n) (KK O)).coeff m.1 •
        (⟨monomial m.1 1, key m.1 m.2⟩ : Pol (KK O) n d) := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    simp only [Submodule.coe_smul, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    rw [Finset.sum_attach _ (fun m => monomial m ((x : MvPolynomial (ι × Fin n) (KK O)).coeff m))]
    exact (x : MvPolynomial (ι × Fin n) (KK O)).as_sum
  rw [hx2]
  show _ ∈ Submodule.span (KK O) _
  refine Submodule.sum_mem _ (fun m _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_))
  exact h m.1

theorem fock_lattice_finite_spanning_holds {p : ℕ} (hp : p.Prime) (S0 : UniformizedDVR p O) (hV : ValuationProperties p O) : FockLatticeFiniteSpanning p O := by
  intro n ι _
  have hp0 : (p : KK O) ≠ 0 := by
    intro h0
    have h1 := hV.2.2.2.1 p hp.ne_zero
    rw [h0, hV.1] at h1
    exact WithTop.top_ne_coe h1
  have hv1 : vK p (1 : KK O) = 0 := by
    have h1 := hV.2.2.2.1 1 one_ne_zero
    rw [Nat.cast_one, padicValNat.one] at h1
    simpa using h1
  have key : ∀ (x : WithTop ℚ) (a b : ℚ), 0 ≤ x + (a : WithTop ℚ) → a ≤ b → 0 ≤ (b : WithTop ℚ) + x := by
    intro x a b hx hab
    induction x using WithTop.recTopCoe with
    | top => simp
    | coe q =>
      rw [← WithTop.coe_add] at hx ⊢
      rw [WithTop.coe_nonneg] at hx ⊢
      linarith
  have hmono : ∀ m : ι × Fin n →₀ ℕ, monomial m (1 : KK O) ∈ fockLattice hV (ι × Fin n) := by
    intro m
    show InBB (O := O) p (monomial m (1 : KK O))
    rw [fock_lattice_monomial_iff hV, hv1, zero_add]
    unfold halfFactorialValuation
    exact WithTop.coe_nonneg.2 (by positivity)
  refine ⟨fockLattice hV (ι × Fin n), fun F => Iff.rfl, fun d => ⟨?_, ?_, ?_, ?_⟩⟩
  · exact multidegree_part_finitely_generated hp0 _ d 0 (fun F hF m _ => by simpa using (mem_integral_poly_iff_coeff F).1 hF m)
  · exact multidegree_part_spans _ d (fun m => by simpa using integer_monomial_mem_integral (O := O) m 1)
  · refine multidegree_part_finitely_generated hp0 _ d
      (∑ m ∈ (multidegree_monomials_finite (ι := ι) (n := n) d).toFinset, padicValNat p (expFact m)) ?_
    intro F hF m hm
    have hF' : InBB (O := O) p F := hF
    have h0 := (mem_fock_lattice_iff_coeff hV F).1 hF' m
    unfold halfFactorialValuation at h0
    apply (hV.2.2.2.2.2 _).1
    haveI := Fact.mk hp
    rw [hV.2.1, ← Nat.cast_pow, hV.2.2.2.1 _ (pow_ne_zero _ hp.ne_zero), padicValNat.prime_pow]
    refine key _ _ _ h0 ?_
    have hmS : m ∈ (multidegree_monomials_finite (ι := ι) (n := n) d).toFinset := (Set.Finite.mem_toFinset _).2 hm
    have hle := Finset.single_le_sum (f := fun m => padicValNat p (expFact m)) (fun _ _ => Nat.zero_le _) hmS
    have hle' : (padicValNat p (expFact m) : ℚ) ≤
        ((∑ m ∈ (multidegree_monomials_finite (ι := ι) (n := n) d).toFinset, padicValNat p (expFact m) : ℕ) : ℚ) := by
      exact_mod_cast hle
    have hnn : (0 : ℚ) ≤ padicValNat p (expFact m) := by positivity
    linarith
  · exact multidegree_part_spans _ d hmono

end Formalism.MainNotions.G.GLWeightTheory
