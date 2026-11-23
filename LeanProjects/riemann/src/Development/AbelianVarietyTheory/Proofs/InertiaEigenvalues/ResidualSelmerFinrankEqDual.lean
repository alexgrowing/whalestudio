import Mathlib
import Formalism.FrobeniusOrbits.RealSubfieldLeCompositum
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsFCocIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalDualityFiniteDiscreteModulesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemDualBlochKatoOfOrthogonalResidualStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidualBlochKatoLatticeDualOrthogonalStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidualSelmerBaseChangeCoefficientFieldStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalCountOfSetupStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousAlgebraMapPadicInt

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.ResDual

namespace GlobalTheory.ResDual

theorem eq_zero_of_forall_eigen {k : Type} [Field k] {r : ℕ} (hr : 2 ≤ r) (m : Fin r → k)
    (h : ∀ A : Matrix (Fin r) (Fin r) k, A.mulVec m ∈ Submodule.span k {m}) : m = 0 := by
  by_contra hm
  obtain ⟨a, ha⟩ := Function.ne_iff.1 hm
  have : Nontrivial (Fin r) := Fin.nontrivial_iff_two_le.2 hr
  obtain ⟨b, hb⟩ := exists_ne a
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 (h (Matrix.single b a 1))
  have h1 := congrFun hc a
  have h2 := congrFun hc b
  simp [Matrix.single_mulVec, Function.update, hb.symm] at h1 h2
  rcases h1 with rfl | h1
  · exact ha (by simpa using h2.symm)
  · exact ha h1

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}

theorem red_apply (i : X.Tw) (K : Type) [Field K] [Algebra (X.O0 i) K] (ρ : GE N →* GL (Fin D.R.r) (X.O0 i)) (g : GE N)
    (m : Fin D.R.r → K) :
    red i K ρ g m = (((ρ g : GL (Fin D.R.r) (X.O0 i)) : Matrix _ _ (X.O0 i)).map (algebraMap (X.O0 i) K)).mulVec m := by
  funext a
  simp [repOn, matAct, Matrix.mulVec, dotProduct]

theorem dot_equiv {i : X.Tw} {s : X.Sig i} (K : Type) [Field K] [Algebra (X.O0 i) K] {ρ : GE N →* GL (Fin D.R.r) (X.O0 i)}
    (hρ : IsDual i s ρ) (g : GE N) (x y : Fin D.R.r → K) :
    dotProductBilin K K (red i K (Tgl i s) g x) (red i K ρ g y) =
      algebraMap (X.O0 i) K ((eps0 X i g : (X.O0 i)ˣ) : X.O0 i) * dotProductBilin K K x y := by
  have h3 : IsUnit (Tmat i s g).det := by
    rw [← Tgl_coe]; exact Matrix.isUnits_det_units _
  rw [red_apply, red_apply, hρ, Tgl_coe, Tdual, dotProductBilin_apply_apply, dotProductBilin_apply_apply,
    Matrix.map_smul' _ _ _ (map_mul _), Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Matrix.transpose_map,
    Matrix.mulVec_transpose, dotProduct_comm, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, ← Matrix.map_mul,
    Matrix.nonsing_inv_mul _ h3, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec, dotProduct_comm]

theorem Tmat_map_residue (i : X.Tw) (s : X.Sig i) (g : GE N) :
    (Tmat i s g).map (IsLocalRing.residue (X.O0 i)) =
      IsLocalRing.residue (X.O0 i) (((chiS i s g)⁻¹ : (X.O0 i)ˣ) : X.O0 i) • rbar X i s g := by
  rw [Tmat, Matrix.map_smul' _ _ _ (map_mul _)]
  rfl

theorem residue_unit_ne_zero {O : Type} [CommRing O] [IsLocalRing O] (u : Oˣ) : IsLocalRing.residue O (u : O) ≠ 0 :=
  (u.isUnit.map _).ne_zero

section NoInv

variable {i : X.Tw} {s : X.Sig i} (hr : 2 ≤ D.R.r)
  (hs : Submodule.span (IsLocalRing.ResidueField (X.O0 i)) (Set.range (rbar X i s)) = ⊤)
include hr hs

theorem h0_red : H0 (red i (IsLocalRing.ResidueField (X.O0 i)) (Tgl i s)) = ⊥ := by
  rw [eq_bot_iff]
  intro m hm
  refine eq_zero_of_forall_eigen hr m fun A => ?_
  have hA : A ∈ Submodule.span (IsLocalRing.ResidueField (X.O0 i)) (Set.range (rbar X i s)) := hs ▸ Submodule.mem_top
  induction hA using Submodule.span_induction with
  | mem A hA =>
    obtain ⟨g, rfl⟩ := hA
    have e := hm g
    rw [red_apply, Tgl_coe, IsLocalRing.ResidueField.algebraMap_eq, Tmat_map_residue, Matrix.smul_mulVec] at e
    rw [← Submodule.smul_mem_iff _ (residue_unit_ne_zero (chiS i s g)⁻¹), e]
    exact Submodule.mem_span_singleton_self m
  | zero => simp
  | add A B _ _ hA hB => rw [Matrix.add_mulVec]; exact Submodule.add_mem _ hA hB
  | smul c A _ hA => rw [Matrix.smul_mulVec]; exact Submodule.smul_mem _ c hA

theorem h0_red_dual {ρ : GE N →* GL (Fin D.R.r) (X.O0 i)} (hρ : IsDual i s ρ) :
    H0 (red i (IsLocalRing.ResidueField (X.O0 i)) ρ) = ⊥ := by
  rw [eq_bot_iff]
  intro m hm
  refine eq_zero_of_forall_eigen hr m fun A => ?_
  rw [← A.transpose_transpose]
  have hA : A.transpose ∈ Submodule.span (IsLocalRing.ResidueField (X.O0 i)) (Set.range (rbar X i s)) :=
    hs ▸ Submodule.mem_top
  generalize A.transpose = B at hA
  induction hA using Submodule.span_induction with
  | mem A hA =>
    obtain ⟨g, rfl⟩ := hA
    have e := hm g⁻¹
    rw [red_apply, hρ, Tdual, GlobalTheory.PrimeToInertia.Tmat_inv, inv_inv, Matrix.map_smul' _ _ _ (map_mul _),
      Matrix.transpose_map, IsLocalRing.ResidueField.algebraMap_eq, Tmat_map_residue, Matrix.transpose_smul,
      Matrix.smul_mulVec, Matrix.smul_mulVec] at e
    rw [← Submodule.smul_mem_iff _ (residue_unit_ne_zero (chiS i s g)⁻¹),
      ← Submodule.smul_mem_iff _ (residue_unit_ne_zero (eps0 X i g⁻¹)), e]
    exact Submodule.mem_span_singleton_self m
  | zero => simp
  | add A B _ _ hA hB => rw [Matrix.transpose_add, Matrix.add_mulVec]; exact Submodule.add_mem _ hA hB
  | smul c A _ hA => rw [Matrix.transpose_smul, Matrix.smul_mulVec]; exact Submodule.smul_mem _ c hA

end NoInv

theorem cupCob_of_mk_eq_zero {Γ k M M' : Type} [Group Γ] [TopologicalSpace Γ] [CommRing k] [AddCommGroup M] [Module k M]
    [TopologicalSpace M] [DiscreteTopology M] [AddCommGroup M'] [Module k M'] [TopologicalSpace M'] [DiscreteTopology M']
    (χ : Γ → k) (ρ : Representation k Γ M) (ρ' : Representation k Γ M') (P : M →ₗ[k] M' →ₗ[k] k)
    (hP : ∀ g x y, P (ρ g x) (ρ' g y) = χ g * P x y) (x : Z1 ρ) (y : Z1 ρ')
    (hx : (Submodule.Quotient.mk x : H1 ρ) = 0) : CupCob χ ρ' P x.1 y.1 := by
  rw [Submodule.Quotient.mk_eq_zero] at hx
  obtain ⟨m, hm⟩ := (mem_coboundaries1 ρ x.1).1 hx
  refine ⟨fun g => P m (y.1 g), ((IsLocallyConstant.iff_continuous _).2 y.2.1).comp (P m), fun g h => ?_⟩
  have e : x.1 g = ρ g m - m := hm g
  simp only [e, y.2.2 g h, map_sub, map_add, LinearMap.sub_apply, hP]
  ring

theorem residue_globalCyclotomicCharacter (i : X.Tw) (g : GE N) :
    algebraMap (X.O0 i) (IsLocalRing.ResidueField (X.O0 i)) ((eps0 X i g : (X.O0 i)ˣ) : X.O0 i) =
      (((cycMod D.host.E N.Om (X.l i) 1 g : (ZMod (X.l i ^ 1))ˣ) : ZMod (X.l i ^ 1)).val :
        IsLocalRing.ResidueField (X.O0 i)) := by
  set z : ℤ_[X.l i] := ((cycZ D.host.E N.Om (X.l i) g : ℤ_[X.l i]ˣ) : ℤ_[X.l i])
  change IsLocalRing.residue _ (algebraMap ℤ_[X.l i] (X.O0 i) z) = ((PadicInt.toZModPow 1 z).val : _)
  have : NeZero (X.l i ^ 1) := ⟨pow_ne_zero _ (Fact.out : (X.l i).Prime).ne_zero⟩
  have h : z - ((PadicInt.toZModPow 1 z).val : ℕ) ∈ RingHom.ker (PadicInt.toZModPow (p := X.l i) 1) := by
    rw [RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
  rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at h
  obtain ⟨w, hw⟩ := h
  have h0 : IsLocalRing.residue (X.O0 i) (X.l i : X.O0 i) = 0 :=
    (IsLocalRing.residue_eq_zero_iff _).2 (GlobalTheory.PrimeToInertia.l_mem i)
  have := congrArg (fun t => IsLocalRing.residue _ (algebraMap ℤ_[X.l i] (X.O0 i) t)) hw
  simp only [map_sub, map_mul, map_natCast, pow_one] at this
  rw [map_natCast] at h0
  rw [h0, zero_mul, sub_eq_zero] at this
  exact this

theorem Tmat_eq_one {bkP : BKPh X} {i : X.Tw} {s : X.Sig i} (h : GalHyp bkP i s) {v : PlE D.host}
    (hl : v ∉ placesOver D.host.E (X.l i)) (hS : v ∉ Spl (X := X) i) (B : ValuationSubring N.Om) (hB : IsPlaceOver B v)
    (σ : GE N) (hσ : σ ∈ Ine (F := D.host.E) B) : Tmat i s σ = 1 := by
  have h1 : ∀ k, v ∉ placesOver D.host.E (D.host.g k) := fun k hk => hS ⟨Or.inl (Set.mem_iUnion.2 ⟨k, hk⟩), hl⟩
  have h2 : v ∉ X.pD i := fun hk => hS ⟨Or.inr hk, hl⟩
  rw [Tmat, h.1.1 v hl h1 B hB σ hσ, chiS, X.twistCharacterFamily_unramified i _ _ v hl h1 h2 B hB σ hσ]
  simp

theorem nrComplexPlaces_host (D : Formalism.BasicNotions.D7) [IsTotallyComplex D.host.E] :
    InfinitePlace.nrComplexPlaces D.host.E = D.R.f := by
  have h1 := IsTotallyComplex.finrank D.host.E
  have h2 : Module.finrank ℚ D.host.E = 2 * D.R.f := by
    rw [D.host.finrank_cmField, Formalism.BasicNotions.Ranks.f, Formalism.BasicNotions.Ranks.n]
    ring
  omega

set_option maxHeartbeats 1600000 in

theorem card_eq (hPT : PoitouTateTotallyComplex) (hLF : LocalFiniteness) (hLD : LocalTateDuality) (hLE : LocalEulerChar)
    (hGF : GlobalFiniteness) (hGE : GlobalEulerChar) (h4 : Gen.ArchimedeanSignatureMatching) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i)
    (h : GalHyp bkP i s) [TopologicalSpace (IsLocalRing.ResidueField (X.O0 i))]
    [DiscreteTopology (IsLocalRing.ResidueField (X.O0 i))] (ρ : GE N →* GL (Fin D.R.r) (X.O0 i)) (hρ : IsDual i s ρ) :
    Finite (selOn bkP i (Tgl i s) (1 : GE N →* (IsLocalRing.ResidueField (X.O0 i))ˣ) (IsLocalRing.ResidueField (X.O0 i)) ∅) ∧
    Finite (selOn bkP i ρ (1 : GE N →* (IsLocalRing.ResidueField (X.O0 i))ˣ) (IsLocalRing.ResidueField (X.O0 i)) ∅) ∧
    Nat.card (selOn bkP i (Tgl i s) (1 : GE N →* (IsLocalRing.ResidueField (X.O0 i))ˣ)
      (IsLocalRing.ResidueField (X.O0 i)) ∅) =
    Nat.card (selOn bkP i ρ (1 : GE N →* (IsLocalRing.ResidueField (X.O0 i))ˣ) (IsLocalRing.ResidueField (X.O0 i)) ∅) := by
  classical
  have hl : (X.l i).Prime := Fact.out
  have : Finite (IsLocalRing.ResidueField (X.O0 i)) := X.twistBaseCoefficientRing_residueField_finite i
  have : CharP (IsLocalRing.ResidueField (X.O0 i)) (X.l i) := (CharP.charP_iff_prime_eq_zero hl).2 (by
    rw [← map_natCast (IsLocalRing.residue (X.O0 i)), IsLocalRing.residue_eq_zero_iff]
    exact GlobalTheory.PrimeToInertia.l_mem i)
  have : IsCMField D.host.E := D.host.isCMField_hostE
  have hres : IsRes i (IsLocalRing.ResidueField (X.O0 i)) := fun x hx => (IsLocalRing.residue_eq_zero_iff _).2 hx
  have hsurj : Function.Surjective (algebraMap (X.O0 i) (IsLocalRing.ResidueField (X.O0 i))) := IsLocalRing.residue_surjective
  have hloc : IsLocalHom (algebraMap (X.O0 i) (IsLocalRing.ResidueField (X.O0 i))) := inferInstanceAs (IsLocalHom (IsLocalRing.residue (X.O0 i)))
  have hr : 2 ≤ D.R.r := le_trans (by norm_num) h.2.2.2.2.2.2
  have htors : ∀ b : (IsLocalRing.ResidueField (X.O0 i)), ∃ n, ∀ x ∈ IsLocalRing.maximalIdeal (IsLocalRing.ResidueField (X.O0 i)) ^ n, x • b = 0 := fun b => ⟨1, fun x hx => by
    rw [pow_one, IsLocalRing.maximalIdeal_eq_bot, Ideal.mem_bot] at hx
    rw [hx, zero_smul]⟩
  have hker : IsOpen (((1 : GE N →* ((IsLocalRing.ResidueField (X.O0 i)))ˣ).ker : Subgroup (GE N)) : Set (GE N)) := by
    rw [MonoidHom.ker_one]; exact isOpen_univ
  have hc : ContAction (red i (IsLocalRing.ResidueField (X.O0 i)) (Tgl i s)) := GlobalTheory.PrimeToInertia.contAction_repOn (X.twistBaseCoefficientRing_isAdic i) _
    (by simp_rw [Tgl_coe]; exact GlobalTheory.PrimeToInertia.continuous_Tmat i s) _ hker htors
  have hc' : ContAction (red i (IsLocalRing.ResidueField (X.O0 i)) ρ) := GlobalTheory.PrimeToInertia.contAction_repOn (X.twistBaseCoefficientRing_isAdic i) _
    (by simp_rw [hρ _]; exact GlobalTheory.PrimeToInertia.continuous_Tdual i s) _ hker htors
  let Sl : Finset (PlE D.host) := (X.S0 i).filter (· ∈ placesOver D.host.E (X.l i))
  let Sp : Finset (PlE D.host) := (X.S0 i).filter (· ∈ Spl (X := X) i)
  have hSl : ∀ v, v ∈ Sl ↔ v ∈ placesOver D.host.E (X.l i) := fun v =>
    ⟨fun hv => (Finset.mem_filter.1 hv).2, fun hv => Finset.mem_filter.2 ⟨X.twistExcludedPlaces_contains_residueChar i hv, hv⟩⟩
  have hSp : ∀ v, v ∈ Sp ↔ v ∈ Spl (X := X) i := fun v =>
    ⟨fun hv => (Finset.mem_filter.1 hv).2, fun hv => Finset.mem_filter.2 ⟨by
      rcases hv.1 with h1 | h1
      · obtain ⟨j, hj⟩ := Set.mem_iUnion.1 h1
        exact X.placesOver_subset_exceptional i j hj
      · exact X.primes_subset_exceptional i h1, hv⟩⟩
  have hdis : Disjoint Sl Sp := Finset.disjoint_left.2 fun v h1 h2 => ((hSp v).1 h2).2 ((hSl v).1 h1)
  have hnot : ∀ v ∉ Sl ∪ Sp, v ∉ placesOver D.host.E (X.l i) ∧ v ∉ Spl (X := X) i := fun v hv => by
    rw [Finset.mem_union, not_or, hSl, hSp] at hv
    exact hv
  have van := fun v (hv : v ∈ Spl (X := X) i) => GlobalTheory.PrimeToInertia.local_cohomology_vanishes D N X bkP i s h v hv (IsLocalRing.ResidueField (X.O0 i)) 1 hker
    (fun g => ⟨0, by simp⟩) (IsLocalRing.ResidueField (X.O0 i)) htors (Tgl i s) (Or.inl rfl)
  have cl : ∀ (τ : GE N →* GL (Fin D.R.r) (X.O0 i)) v, v ∈ placesOver D.host.E (X.l i) →
      Formalism.GaloisCohomology.bkCond (red i (IsLocalRing.ResidueField (X.O0 i)) τ) N.plOm (X.l i) (Spl i ∪ ↑(∅ : Finset (PlE D.host))) (bkOn bkP i τ 1 (IsLocalRing.ResidueField (X.O0 i))) v =
        bkOn bkP i τ 1 (IsLocalRing.ResidueField (X.O0 i)) v := fun τ v hv => if_pos hv
  have cp : ∀ (τ : GE N →* GL (Fin D.R.r) (X.O0 i)) v, v ∈ Spl (X := X) i →
      Formalism.GaloisCohomology.bkCond (red i (IsLocalRing.ResidueField (X.O0 i)) τ) N.plOm (X.l i) (Spl i ∪ ↑(∅ : Finset (PlE D.host))) (bkOn bkP i τ 1 (IsLocalRing.ResidueField (X.O0 i))) v = ⊤ :=
    fun τ v hv => (if_neg hv.2).trans (if_pos (Or.inl hv))
  have cu : ∀ (τ : GE N →* GL (Fin D.R.r) (X.O0 i)) v, v ∉ Sl ∪ Sp →
      Formalism.GaloisCohomology.bkCond (red i (IsLocalRing.ResidueField (X.O0 i)) τ) N.plOm (X.l i) (Spl i ∪ ↑(∅ : Finset (PlE D.host))) (bkOn bkP i τ 1 (IsLocalRing.ResidueField (X.O0 i))) v =
        Formalism.GaloisCohomology.unrAt (red i (IsLocalRing.ResidueField (X.O0 i)) τ) (N.plOm.1 v) :=
    fun τ v hv => (if_neg (hnot v hv).1).trans (if_neg (by simpa using (hnot v hv).2))
  obtain ⟨f1, f2, e⟩ := GlobalTheory.T.local_duality_finite_discrete_modules hPT hLF hGF hGE D.host.E N.Om (X.l i) (IsLocalRing.ResidueField (X.O0 i)) (Fin D.R.r → (IsLocalRing.ResidueField (X.O0 i))) (Fin D.R.r → (IsLocalRing.ResidueField (X.O0 i)))
    (red i (IsLocalRing.ResidueField (X.O0 i)) (Tgl i s)) (red i (IsLocalRing.ResidueField (X.O0 i)) ρ) (fun g => algebraMap (X.O0 i) (IsLocalRing.ResidueField (X.O0 i)) ((eps0 X i g : (X.O0 i)ˣ) : X.O0 i))
    (dotProductBilin (IsLocalRing.ResidueField (X.O0 i)) (IsLocalRing.ResidueField (X.O0 i))) hc hc' (residue_globalCyclotomicCharacter i)
    (fun x hx => funext fun a => by simpa using hx (Pi.single a 1))
    (fun y hy => funext fun a => by simpa using hy (Pi.single a 1))
    (dot_equiv (IsLocalRing.ResidueField (X.O0 i)) hρ) (Sl ∪ Sp) N.plOm (fun v hv => Finset.mem_union_left _ ((hSl v).2 hv))
    (fun v hv B hB σ hσ => LinearMap.ext fun m => by
      rw [red_apply, Tgl_coe, Tmat_eq_one h (hnot v hv).1 (hnot v hv).2 B hB σ hσ,
        Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec, Module.End.one_apply])
    _ _ (cu (Tgl i s)) (cu ρ) (fun v hv y => by
      rcases Finset.mem_union.1 hv with hv | hv
      · rw [hSl] at hv
        rw [cl _ v hv, cl _ v hv]
        exact ⟨fun hy x hx => GlobalTheory.T.residualBlochKato_lattice_dual_orthogonal hLD D N X bkP i s h (IsLocalRing.ResidueField (X.O0 i)) hres ρ hρ v hv x y hx hy,
          GlobalTheory.T.mem_dualBlochKato_of_orthogonal_residual D N X bkP i s h (IsLocalRing.ResidueField (X.O0 i)) hres hsurj ρ hρ v hv y⟩
      · rw [hSp] at hv
        rw [cp _ v hv, cp _ v hv]
        refine ⟨fun _ x _ => cupCob_of_mk_eq_zero _ _ _ _ (fun g => dot_equiv (IsLocalRing.ResidueField (X.O0 i)) hρ g.1) x y ?_, fun _ => Submodule.mem_top⟩
        exact (van v hv).2.1.elim _ _)
  refine ⟨f1, f2, ?_⟩
  have hset : Setup bkP i s (1 : GE N →* ((IsLocalRing.ResidueField (X.O0 i)))ˣ) ∅ :=
    ⟨h, hloc, Module.Finite.of_surjective (Algebra.linearMap (X.O0 i) (IsLocalRing.ResidueField (X.O0 i))) hsurj, hker, fun g => ⟨0, by simp⟩,
      fun _ _ _ _ _ _ => rfl, by simp, fun _ _ _ _ _ _ => rfl⟩
  have cnt := GlobalTheory.T.local_count_of_setup hLF hLD hLE h4 D N X bkP i s (IsLocalRing.ResidueField (X.O0 i)) 1 ∅ hset (IsLocalRing.ResidueField (X.O0 i)) inferInstance
  have hSl' : placesOver D.host.E (X.l i) = (Sl : Set (PlE D.host)) := Set.ext fun v => (hSl v).symm
  rw [hSl', finprod_mem_coe_finset, finprod_mem_coe_finset] at cnt
  rw [Finset.prod_union hdis, Finset.prod_union hdis, h0_red hr h.2.1.1, h0_red_dual hr h.2.1.1 hρ,
    Finset.prod_eq_one (s := Sp) (fun v hv => by rw [(van v ((hSp v).1 hv)).1]; simp),
    Finset.prod_eq_one (s := Sp) (fun v hv => by
      have := (van v ((hSp v).1 hv)).2.1
      exact Nat.card_unique),
    Finset.prod_congr rfl (fun v hv => congrArg (fun L : Submodule (IsLocalRing.ResidueField (X.O0 i)) _ => Nat.card L) (cl (Tgl i s) v ((hSl v).1 hv))),
    cnt, nrComplexPlaces_host, Nat.card_fun, Nat.card_fin, ← pow_mul, mul_comm D.R.r] at e
  have hpos : 0 < (∏ v ∈ Sl, Nat.card (H0 ((repOn (Tgl i s) (1 : GE N →* ((IsLocalRing.ResidueField (X.O0 i)))ˣ) (IsLocalRing.ResidueField (X.O0 i))).comp (DecV N v).subtype))) *
      Nat.card (IsLocalRing.ResidueField (X.O0 i)) ^ (D.R.f * D.R.r) :=
    mul_pos (Finset.prod_pos fun v _ => Nat.card_pos) (pow_pos Nat.card_pos _)
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  simp only [Nat.card_unique, mul_one] at e
  rw [← mul_assoc]
  exact e

theorem finrank_eq_of_card_eq {k V V' : Type} [Field k] [Finite k] [AddCommGroup V] [Module k V] [AddCommGroup V']
    [Module k V'] (f : Finite V) (f' : Finite V') (e : Nat.card V = Nat.card V') :
    Module.finrank k V = Module.finrank k V' := by
  rw [Module.natCard_eq_pow_finrank (K := k), Module.natCard_eq_pow_finrank (K := k) (V := V')] at e
  exact Nat.pow_right_injective Finite.one_lt_card e

theorem eqDim : Cheb → PoitouTateTotallyComplex → CohDimTwo → TameLocal → LocalFiniteness → LocalTateDuality → LocalEulerChar → GlobalFiniteness → GlobalEulerChar → UnramifiedOrthogonality → Gen.ArchimedeanSignatureMatching → ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), GalHyp bkP i s → EqDim bkP i s := by
  intro _ hPT _ _ hLF hLD hLE hGF hGE _ h4 D N X bkP i s h K _ _ _ _ hK ρ hρ
  letI : TopologicalSpace (IsLocalRing.ResidueField (X.O0 i)) := ⊥
  haveI : DiscreteTopology (IsLocalRing.ResidueField (X.O0 i)) := ⟨rfl⟩
  obtain ⟨f1, f2, e⟩ := card_eq hPT hLF hLD hLE hGF hGE h4 bkP i s h ρ hρ
  have := X.twistBaseCoefficientRing_residueField_finite i
  have hres : IsRes i (IsLocalRing.ResidueField (X.O0 i)) := fun x hx => (IsLocalRing.residue_eq_zero_iff _).2 hx
  have hsurj : Function.Surjective (algebraMap (X.O0 i) (IsLocalRing.ResidueField (X.O0 i))) :=
    IsLocalRing.residue_surjective
  obtain ⟨a1, a2⟩ := GlobalTheory.T.residualSelmer_baseChange_coefficientField D N X bkP i (Tgl i s) _ K hres hsurj hK ∅ Module.Finite.of_finite
  obtain ⟨b1, b2⟩ := GlobalTheory.T.residualSelmer_baseChange_coefficientField D N X bkP i ρ _ K hres hsurj hK ∅ Module.Finite.of_finite
  refine ⟨a1, b1, ?_⟩
  rw [a2, b2]
  exact finrank_eq_of_card_eq f1 f2 e

end GlobalTheory.ResDual
