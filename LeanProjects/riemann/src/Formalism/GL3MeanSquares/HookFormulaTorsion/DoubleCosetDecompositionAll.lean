import Mathlib
import Formalism.GL3MeanSquares.AffineFibreCountComparison
import Formalism.LogVandermondeBounds.LogVandermondeProofs.RamifiedLatticeOperatorIdentity

namespace Formalism.HermitianLattices.OneDimInversion

open Finset Formalism.LogVandermondeBounds.product_first_zeroth_parts

section T1
variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {R : Type} [CommRing R]

private lemma ext_fin_one_function {x y : Fin 1 → F} (h : x 0 = y 0) : x = y := by
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  subst hi
  exact h

private lemma nonzero_single_coordinate {f : Fin 1 → F} (hf : f ≠ 0) : f 0 ≠ 0 := by
  intro h
  apply hf
  exact ext_fin_one_function (by simpa using h)

private lemma filt1 (f : Fin 1 → F) (hf : f ≠ 0) :
    univ.filter (fun x : Fin 1 → F => pair f x = 1) = {fun _ => (f 0)⁻¹} := by
  have h0 := nonzero_single_coordinate hf
  ext x
  simp only [mem_filter, mem_univ, true_and, mem_singleton, pair, Fin.sum_univ_one]
  constructor
  · intro h
    exact ext_fin_one_function (eq_inv_of_mul_eq_one_right h)
  · intro h
    rw [h]
    exact mul_inv_cancel₀ h0

private lemma inversion_operator_one_dim (ψ : (Fin 1 → F) → R) (f : Fin 1 → F) (hf : f ≠ 0) :
    opU ψ f = ψ (fun _ => (f 0)⁻¹) := by
  unfold opU
  rw [filt1 f hf, sum_singleton]

private lemma inversion_operator_involutive (ψ : (Fin 1 → F) → R) (x : Fin 1 → F) (hx : x ≠ 0) :
    opU (opU ψ) x = ψ x := by
  have h0 := nonzero_single_coordinate hx
  have hne : (fun _ : Fin 1 => (x 0)⁻¹) ≠ 0 := by
    intro h
    have := congrFun h 0
    simp only [Pi.zero_apply] at this
    exact h0 (inv_eq_zero.1 this)
  rw [inversion_operator_one_dim _ x hx, inversion_operator_one_dim _ _ hne]
  congr 1
  exact ext_fin_one_function (by simp)

private lemma nm1 (ψ : (Fin 1 → F) → R) (x : Fin 1 → F) (hx : x ≠ 0) :
    nmV ψ x = trV ψ := by
  have h0 := nonzero_single_coordinate hx
  rw [nmV_eq_image ψ hx]
  unfold trV
  congr 1
  ext y
  rw [mem_image_line hx, mem_filter]
  simp only [mem_univ, true_and]
  constructor
  · exact fun h => h.1
  · intro hy
    refine ⟨hy, y 0 / x 0, ext_fin_one_function ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp

end T1
end Formalism.HermitianLattices.OneDimInversion

namespace Formalism.HermitianLattices.RamifiedLatticeOperators
open Formalism.LogVandermondeBounds.product_first_zeroth_parts Formalism.HermitianLattices.OneDimInversion

theorem double_coset_decomposition_all : TraceOperatorIdentityAllRanks := by
  intro F _ _ _ r R _ hr
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    refine ⟨fun ψ x hx => ?_, fun φ f hf => ?_⟩
    · rw [← opU_eq_opD (opU ψ), inversion_operator_involutive ψ x hx, nm1 ψ x hx]
      simp
    · have htr : trP φ = trV φ := rfl
      rw [← opU_eq_opD φ, inversion_operator_involutive φ f hf, nmP_eq_nmV, nm1 φ f hf, htr]
      simp
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    have hr2 : 2 ≤ k + 1 + 1 := by omega
    have e1 : k + 1 + 1 - 1 = k + 1 := by omega
    have e2 : k + 1 + 1 - 2 = k := by omega
    refine ⟨fun ψ x hx => ?_, fun φ f hf => ?_⟩
    · rw [down_up_composition_formula F (k + 1 + 1) R hr2 ψ x hx, e1, e2]
      ring
    · rw [up_down_composition_formula F (k + 1 + 1) R hr2 φ f hf, e1, e2]
      ring

end Formalism.HermitianLattices.RamifiedLatticeOperators

namespace Formalism.HermitianLattices.OneDimInversion

section Orb

private lemma natcard_stab_smul {Γ X : Type} [Group Γ] [MulAction Γ X] (g : Γ) (x : X) :
    Nat.card (MulAction.stabilizer Γ (g • x)) = Nat.card (MulAction.stabilizer Γ x) := by
  rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  exact Subgroup.card_map_of_injective (MulAut.conj g).injective

private lemma count_fib {Γ P Q : Type} [Group Γ] [MulAction Γ P] [MulAction Γ Q] (pr : P → Q)
    (hpr : ∀ (γ : Γ) (p : P), pr (γ • p) = γ • pr p) (T : Finset P) (y : Q) (s : P)
    (hT : ∀ p, p ∈ T ↔ pr p = y ∧ p ∈ MulAction.orbit Γ s) (hs : pr s = y) :
    T.card * Nat.card (MulAction.stabilizer Γ s) = Nat.card (MulAction.stabilizer Γ y) := by
  classical
  have hle : MulAction.stabilizer Γ s ≤ MulAction.stabilizer Γ y := by
    intro g hg
    rw [MulAction.mem_stabilizer_iff] at hg ⊢
    rw [← hs, ← hpr, hg]
  set H := MulAction.stabilizer Γ y with hH
  have horb : (T : Set P) = MulAction.orbit H s := by
    ext p
    simp only [Finset.mem_coe, hT, MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨hp, g, rfl⟩
      have hg : g ∈ H := by
        rw [hH, MulAction.mem_stabilizer_iff]
        calc g • y = g • pr s := by rw [hs]
          _ = pr (g • s) := (hpr g s).symm
          _ = y := hp
      exact ⟨⟨g, hg⟩, rfl⟩
    · rintro ⟨h, rfl⟩
      refine ⟨?_, (h : Γ), rfl⟩
      show pr ((h : Γ) • s) = y
      rw [hpr, hs]
      exact h.2
  have hstab : MulAction.stabilizer H s = (MulAction.stabilizer Γ s).subgroupOf H := by
    ext h
    simp [Subgroup.mem_subgroupOf, MulAction.mem_stabilizer_iff, Subgroup.smul_def]
  have hcs : Nat.card (MulAction.stabilizer H s) = Nat.card (MulAction.stabilizer Γ s) := by
    rw [hstab]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  have hcardT : T.card = (MulAction.orbit H s).ncard := by
    rw [← horb, Set.ncard_coe_finset]
  rw [hcardT, ← MulAction.index_stabilizer, ← hcs]
  exact Subgroup.index_mul_card _

private lemma exists_reps {Γ P Q : Type} [Group Γ] [MulAction Γ P] [MulAction Γ Q] (pr : P → Q)
    (fib : Q → Finset P) (hpr : ∀ (γ : Γ) (p : P), pr (γ • p) = γ • pr p)
    (hfib : ∀ p y, p ∈ fib y ↔ pr p = y) (RQ : Finset Q)
    (hRQ : ∀ y : Q, ∃! r, r ∈ RQ ∧ r ∈ MulAction.orbit Γ y) :
    ∃ RP : Finset P, ∀ p : P, ∃! r, r ∈ RP ∧ r ∈ MulAction.orbit Γ p := by
  classical
  let rep : P → P := fun p => (Quotient.mk (MulAction.orbitRel Γ P) p).out
  have hrep : ∀ p, rep p ∈ MulAction.orbit Γ p := fun p =>
    MulAction.orbitRel_apply.1 (Quotient.mk_out (s := MulAction.orbitRel Γ P) p)
  have hrep_eq : ∀ p p', p' ∈ MulAction.orbit Γ p → rep p' = rep p := by
    intro p p' h
    simp only [rep]
    congr 1
    exact Quotient.sound (MulAction.orbitRel_apply.2 h)
  refine ⟨(RQ.biUnion fib).image rep, fun p => ?_⟩
  obtain ⟨y, ⟨hy, g, hg⟩, -⟩ := hRQ (pr p)
  refine ⟨rep p, ⟨?_, hrep p⟩, ?_⟩
  · rw [Finset.mem_image]
    refine ⟨g • p, Finset.mem_biUnion.2 ⟨y, hy, (hfib _ _).2 (by rw [hpr]; exact hg)⟩,
      hrep_eq p _ ⟨g, rfl⟩⟩
  · rintro r ⟨hr, hro⟩
    obtain ⟨p'', -, rfl⟩ := Finset.mem_image.1 hr
    calc rep p'' = rep (rep p'') := (hrep_eq p'' _ (hrep p'')).symm
      _ = rep p := hrep_eq p _ hro

end Orb
end Formalism.HermitianLattices.OneDimInversion

namespace Formalism.HermitianLattices.RamifiedLatticeOperators
open Formalism.HermitianLattices.OneDimInversion

theorem fubini_over_orbits : Fubini_orbits := by
  intro Γ P Q V _ _ _ _ _ pr fib Ψ RP RQ hpr hfib hΨ hfinQ hRP hRQ
  classical
  choose rep hrep using fun p => (hRP p).exists
  have hrep_iff : ∀ p r, r ∈ RP → (rep p = r ↔ r ∈ MulAction.orbit Γ p) := by
    intro p r hr
    constructor
    · rintro rfl
      exact (hrep p).2
    · intro h
      exact (hRP p).unique (hrep p) ⟨hr, h⟩
  choose repQ hrepQ using fun y => (hRQ y).exists

  have hinner : ∀ y, ∑ p ∈ fib y, Ψ p =
      ∑ r ∈ RP, (((fib y).filter (fun p => rep p = r)).card : ℚ) • Ψ r := by
    intro y
    rw [← Finset.sum_fiberwise_of_maps_to (g := rep) (t := RP) (fun p _ => (hrep p).1)]
    refine Finset.sum_congr rfl (fun r hr => ?_)
    rw [Finset.sum_congr rfl (g := fun _ => Ψ r), Finset.sum_const, Nat.cast_smul_eq_nsmul]
    intro p hp
    rw [Finset.mem_filter] at hp
    obtain ⟨γ, hγ⟩ := (hrep p).2
    rw [← hp.2, ← hγ, hΨ]

  have hweight : ∀ r ∈ RP, ∑ y ∈ RQ, ((Nat.card (MulAction.stabilizer Γ y) : ℚ))⁻¹ *
      (((fib y).filter (fun p => rep p = r)).card : ℚ) =
      ((Nat.card (MulAction.stabilizer Γ r) : ℚ))⁻¹ := by
    intro r hr
    obtain ⟨hy0, g, hg⟩ := hrepQ (pr r)
    set y0 := repQ (pr r) with hy0def
    rw [Finset.sum_eq_single y0]
    · set s := g • r with hsdef
      have hs : pr s = y0 := by rw [hsdef, hpr]; exact hg
      have hT : ∀ p, p ∈ (fib y0).filter (fun p => rep p = r) ↔
          pr p = y0 ∧ p ∈ MulAction.orbit Γ s := by
        intro p
        rw [Finset.mem_filter, hfib, hrep_iff p r hr]
        refine and_congr Iff.rfl ?_
        rw [MulAction.mem_orbit_iff, MulAction.mem_orbit_iff]
        constructor
        · rintro ⟨γ, hγ⟩
          refine ⟨γ⁻¹ * g⁻¹, ?_⟩
          rw [hsdef, smul_smul, mul_assoc, inv_mul_cancel, mul_one, ← hγ, inv_smul_smul]
        · rintro ⟨γ, hγ⟩
          refine ⟨g⁻¹ * γ⁻¹, ?_⟩
          rw [← hγ, hsdef, mul_smul, inv_smul_smul, inv_smul_smul]
      have hc := count_fib pr hpr _ y0 s hT hs
      rw [hsdef, natcard_stab_smul] at hc
      have hpos : 0 < Nat.card (MulAction.stabilizer Γ y0) := by
        haveI := hfinQ y0
        exact Nat.card_pos
      have hcq : ((Nat.card (MulAction.stabilizer Γ y0) : ℕ) : ℚ) =
          (((fib y0).filter (fun p => rep p = r)).card : ℚ) *
            (Nat.card (MulAction.stabilizer Γ r) : ℚ) := by
        rw [← hc]; push_cast; ring
      have hne : ((Nat.card (MulAction.stabilizer Γ y0) : ℕ) : ℚ) ≠ 0 := by
        exact_mod_cast hpos.ne'
      rw [hcq] at hne ⊢
      have h1 : (((fib y0).filter (fun p => rep p = r)).card : ℚ) ≠ 0 := left_ne_zero_of_mul hne
      have h2 : (Nat.card (MulAction.stabilizer Γ r) : ℚ) ≠ 0 := right_ne_zero_of_mul hne
      field_simp
    · intro y hy hne
      rw [mul_eq_zero]
      right
      rw [Nat.cast_eq_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro p hp hpr'
      apply hne
      rw [hfib] at hp
      obtain ⟨γ, hγ⟩ := (hrep_iff p r hr).1 hpr'
      apply (hRQ (pr r)).unique ⟨hy, γ⁻¹, ?_⟩ ⟨hy0, g, hg⟩
      rw [← hγ, hpr, hp]
      exact inv_smul_smul γ y
    · intro h
      exact absurd hy0 h

  simp_rw [hinner, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun r hr => ?_)
  rw [← Finset.sum_smul, hweight r hr]

end Formalism.HermitianLattices.RamifiedLatticeOperators

namespace Formalism.HermitianLattices.RamifiedLatticeOperators
open Formalism.HermitianLattices.OneDimInversion

theorem count_of_orbits : Count_orbits := by
  intro Γ A B V _ _ _ _ _ up down G RA RB hud hup hG hfA hfB hRA hRB
  classical
  letI act : MulAction Γ {x : A × B // x.2 ∈ up x.1} :=
    { smul := fun γ x => ⟨(γ • x.1.1, γ • x.1.2), hup γ x.1.1 x.1.2 x.2⟩
      one_smul := fun x => Subtype.ext (Prod.ext (one_smul Γ x.1.1) (one_smul Γ x.1.2))
      mul_smul := fun a b x => Subtype.ext (Prod.ext (mul_smul a b x.1.1) (mul_smul a b x.1.2)) }
  let fibA : A → Finset {x : A × B // x.2 ∈ up x.1} := fun a =>
    (up a).attach.map ⟨fun b => ⟨(a, b.1), b.2⟩, fun b b' h => Subtype.ext (congrArg (fun x => x.1.2) h)⟩
  let fibB : B → Finset {x : A × B // x.2 ∈ up x.1} := fun b =>
    (down b).attach.map ⟨fun a => ⟨(a.1, b), (hud a.1 b).2 a.2⟩,
      fun a a' h => Subtype.ext (congrArg (fun x => x.1.1) h)⟩
  have hfibA : ∀ p a, p ∈ fibA a ↔ p.1.1 = a := by
    intro p a
    constructor
    · intro h
      obtain ⟨b, -, rfl⟩ := Finset.mem_map.1 h
      rfl
    · intro h
      refine Finset.mem_map.2 ⟨⟨p.1.2, h ▸ p.2⟩, Finset.mem_attach _ _, ?_⟩
      exact Subtype.ext (Prod.ext h.symm rfl)
  have hfibB : ∀ p b, p ∈ fibB b ↔ p.1.2 = b := by
    intro p b
    constructor
    · intro h
      obtain ⟨a, -, rfl⟩ := Finset.mem_map.1 h
      rfl
    · intro h
      refine Finset.mem_map.2 ⟨⟨p.1.1, (hud _ _).1 (h ▸ p.2)⟩, Finset.mem_attach _ _, ?_⟩
      exact Subtype.ext (Prod.ext rfl h.symm)
  let Ψ : {x : A × B // x.2 ∈ up x.1} → V := fun x => G x.1.1 x.1.2
  have hΨ : ∀ (γ : Γ) (x : {x : A × B // x.2 ∈ up x.1}), Ψ (γ • x) = Ψ x :=
    fun γ x => hG γ x.1.1 x.1.2 x.2
  obtain ⟨RP, hRP⟩ := exists_reps (Γ := Γ) (fun x : {x : A × B // x.2 ∈ up x.1} => x.1.1) fibA
    (fun _ _ => rfl) hfibA RA hRA
  have h1 := fubini_over_orbits Γ {x : A × B // x.2 ∈ up x.1} A V (fun x => x.1.1) fibA Ψ RP RA
    (fun _ _ => rfl) hfibA hΨ hfA hRP hRA
  have h2 := fubini_over_orbits Γ {x : A × B // x.2 ∈ up x.1} B V (fun x => x.1.2) fibB Ψ RP RB
    (fun _ _ => rfl) hfibB hΨ hfB hRP hRB
  have sA : ∀ a, ∑ p ∈ fibA a, Ψ p = ∑ b ∈ up a, G a b := by
    intro a
    rw [Finset.sum_map]
    exact Finset.sum_attach (up a) (fun b => G a b)
  have sB : ∀ b, ∑ p ∈ fibB b, Ψ p = ∑ a ∈ down b, G a b := by
    intro b
    rw [Finset.sum_map]
    exact Finset.sum_attach (down b) (fun a => G a b)
  simp only [sA, sB] at h1 h2
  exact h1.symm.trans h2

end Formalism.HermitianLattices.RamifiedLatticeOperators

namespace Formalism.HermitianLattices.OneDimInversion

private lemma len_quot_pi {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (ϖ : R) (hϖ : Irreducible ϖ) (ι : Type) [Fintype ι] (deg : ι → ℕ) :
    Module.length R ((ι → R) ⧸
      (Submodule.pi Set.univ (fun i => Ideal.span {ϖ ^ deg i}) : Submodule R (ι → R))) =
      ((∑ i, deg i : ℕ) : ℕ∞) := by
  classical
  rw [(Submodule.quotientPi (fun i => (Ideal.span {ϖ ^ deg i} : Submodule R R))).length_eq,
    Module.length_pi_of_fintype, Nat.cast_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Ideal.span_singleton_pow, ← hϖ.maximalIdeal_eq]
  exact IsDiscreteValuationRing.length_quotient_pow_maximalIdeal R (deg i)

private lemma len_free_quot {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (ϖ : R) (hϖ : Irreducible ϖ) (N : Type) [AddCommGroup N] [Module R N] [Module.Free R N]
    [Module.Finite R N] (e : ℕ) (K0 : Submodule R N) (hK0 : ∀ x : N, ϖ ^ e • x ∈ K0) :
    Module.length R (N ⧸ K0) ≤ ((e * Module.finrank R N : ℕ) : ℕ∞) := by
  classical
  let bs := Module.Free.chooseBasis R N
  let Kpi : Submodule R (Module.Free.ChooseBasisIndex R N → R) :=
    Submodule.pi Set.univ (fun _ => Ideal.span {ϖ ^ e})
  let f : (Module.Free.ChooseBasisIndex R N → R) →ₗ[R] N ⧸ K0 :=
    K0.mkQ ∘ₗ (bs.equivFun.symm : (Module.Free.ChooseBasisIndex R N → R) →ₗ[R] N)
  have hker : Kpi ≤ LinearMap.ker f := by
    intro v hv
    have hv' : ∀ i, ∃ c : R, c * ϖ ^ e = v i := fun i =>
      Ideal.mem_span_singleton'.1 ((Submodule.mem_pi.1 hv) i (Set.mem_univ i))
    choose c hc using hv'
    have hvc : v = ϖ ^ e • c := by
      funext i
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [← hc i, mul_comm]
    rw [LinearMap.mem_ker, hvc, LinearMap.map_smul]
    show ϖ ^ e • K0.mkQ (bs.equivFun.symm c) = 0
    rw [← LinearMap.map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hK0 _
  let g := Kpi.liftQ f hker
  have hg : Function.Surjective g := by
    intro t
    obtain ⟨n, rfl⟩ := K0.mkQ_surjective t
    refine ⟨Kpi.mkQ (bs.equivFun n), ?_⟩
    simp [g, f]
  calc Module.length R (N ⧸ K0)
      ≤ Module.length R ((Module.Free.ChooseBasisIndex R N → R) ⧸ Kpi) :=
        Module.length_le_of_surjective g hg
    _ = ((∑ _i : Module.Free.ChooseBasisIndex R N, e : ℕ) : ℕ∞) := len_quot_pi ϖ hϖ _ (fun _ => e)
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, smul_eq_mul,
        Module.finrank_eq_card_chooseBasisIndex, mul_comm]

private lemma sat_pow {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (ϖ : R)
    (P : Submodule R M) (h : ∀ x : M, ϖ • x ∈ P → x ∈ P) :
    ∀ (k : ℕ) (x : M), ϖ ^ k • x ∈ P → x ∈ P := by
  intro k
  induction k with
  | zero => intro x hx; simpa using hx
  | succ k ih =>
    intro x hx
    apply h
    apply ih
    rwa [← mul_smul, ← pow_succ]

end Formalism.HermitianLattices.OneDimInversion

namespace Formalism.HermitianLattices.RamifiedLatticeOperators
open Formalism.HermitianLattices.OneDimInversion

theorem lemmaB_length_statement : LemmaB'_length := by
  intro R _ _ _ ϖ hϖ ι _ deg
  exact len_quot_pi ϖ hϖ ι deg

end Formalism.HermitianLattices.RamifiedLatticeOperators

namespace Formalism.HermitianLattices.RamifiedLatticeOperators
open Formalism.HermitianLattices.OneDimInversion

theorem c_sharp_form : LemmaC_sharp := by
  intro R _ _ _ ϖ hϖ M _ _ P S B U D e b hSB hBU hSD hPU hPD hsat hUD hfree hfin
  classical
  haveI := hfree
  haveI := hfin
  have hNS : S ⊓ P ≤ S := inf_le_left
  haveI : Module.Free R (S ⊓ P : Submodule R M) :=
    Module.Free.of_equiv (Submodule.comapSubtypeEquivOfLe hNS)
  haveI : Module.Finite R (S ⊓ P : Submodule R M) :=
    Module.Finite.equiv (Submodule.comapSubtypeEquivOfLe hNS)
  set N : Submodule R M := S ⊓ P with hN
  set K1 : Submodule R N := (N.map ((ϖ ^ b) • U)).comap N.subtype with hK1
  set Sb : Submodule R B :=
    (S.map ((ϖ ^ b) • (LinearMap.id : M →ₗ[R] M))).comap B.subtype with hSb
  let BP : Submodule R M := B ⊓ P
  have hu : ∀ x : BP, U x ∈ N := fun x =>
    Submodule.mem_inf.2 ⟨hBU (Submodule.mem_map_of_mem (Submodule.mem_inf.1 x.2).1),
      hPU (Submodule.mem_map_of_mem (Submodule.mem_inf.1 x.2).2)⟩
  let u : BP →ₗ[R] N := LinearMap.codRestrict N (U ∘ₗ BP.subtype) hu
  have hu_apply : ∀ x : BP, ((u x : N) : M) = U x := fun x => rfl
  let ψ0 : BP →ₗ[R] (N ⧸ K1) := K1.mkQ ∘ₗ u
  let L : Submodule R BP := (S.map ((ϖ ^ b) • (LinearMap.id : M →ₗ[R] M))).comap BP.subtype
  have hL : L ≤ LinearMap.ker ψ0 := by
    intro x hx
    obtain ⟨s, hs, hsx⟩ := Submodule.mem_map.1 (Submodule.mem_comap.1 hx)
    have hsx' : ϖ ^ b • s = (x : M) := by simpa using hsx
    have hsP : s ∈ P := sat_pow ϖ P hsat b s (by rw [hsx']; exact (Submodule.mem_inf.1 x.2).2)
    rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, hK1, Submodule.mem_comap]
    refine Submodule.mem_map.2 ⟨s, Submodule.mem_inf.2 ⟨hs, hsP⟩, ?_⟩
    rw [Submodule.subtype_apply, hu_apply, ← hsx', LinearMap.map_smul, LinearMap.smul_apply]
  let ψ : (BP ⧸ L) →ₗ[R] (N ⧸ K1) := L.liftQ ψ0 hL
  let W : Submodule R (N ⧸ K1) := LinearMap.range ψ
  have hadd := Module.length_eq_add_of_exact W.subtype W.mkQ Subtype.val_injective
    W.mkQ_surjective (LinearMap.exact_subtype_mkQ W)
  have hW : Module.length R W ≤ Module.length R (BP ⧸ L) :=
    Module.length_le_of_surjective ψ.rangeRestrict ψ.surjective_rangeRestrict
  have hle : L ≤ Sb.comap (Submodule.inclusion (inf_le_left : BP ≤ B)) := fun x hx => hx
  have hinj : Function.Injective (L.mapQ Sb (Submodule.inclusion (inf_le_left : BP ≤ B)) hle) := by
    rw [← LinearMap.ker_eq_bot, Submodule.ker_mapQ]
    have : Sb.comap (Submodule.inclusion (inf_le_left : BP ≤ B)) = L := by
      ext x
      rfl
    rw [this, Submodule.mkQ_map_self]
  have hBP : Module.length R (BP ⧸ L) ≤ Module.length R (B ⧸ Sb) :=
    Module.length_le_of_injective _ hinj
  let K0 : Submodule R N := LinearMap.range ((ϖ ^ e) • (LinearMap.id : N →ₗ[R] N))
  have hK0 : ∀ x : N, ϖ ^ e • x ∈ K0 := fun x => ⟨x, by simp⟩
  have hK0ker : K0 ≤ LinearMap.ker (W.mkQ ∘ₗ K1.mkQ) := by
    rintro _ ⟨n, rfl⟩
    have hnS : (n : M) ∈ S := (Submodule.mem_inf.1 n.2).1
    have hnP : (n : M) ∈ P := (Submodule.mem_inf.1 n.2).2
    have hDn : D n ∈ BP :=
      Submodule.mem_inf.2 ⟨hSD (Submodule.mem_map_of_mem hnS), hPD (Submodule.mem_map_of_mem hnP)⟩
    rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    refine ⟨L.mkQ ⟨D n, hDn⟩, ?_⟩
    show ψ0 ⟨D n, hDn⟩ = _
    show K1.mkQ (u ⟨D n, hDn⟩) = _
    congr 1
    apply Subtype.ext
    rw [hu_apply]
    simp [hUD n n.2]
  have hQ : Module.length R ((N ⧸ K1) ⧸ W) ≤ Module.length R (N ⧸ K0) := by
    refine Module.length_le_of_surjective (K0.liftQ (W.mkQ ∘ₗ K1.mkQ) hK0ker) ?_
    intro t
    obtain ⟨t', rfl⟩ := W.mkQ_surjective t
    obtain ⟨n, rfl⟩ := K1.mkQ_surjective t'
    exact ⟨K0.mkQ n, rfl⟩
  have hfr := len_free_quot ϖ hϖ N e K0 hK0
  rw [hadd]
  exact add_le_add (hW.trans hBP) (hQ.trans hfr)

end Formalism.HermitianLattices.RamifiedLatticeOperators
