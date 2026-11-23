import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ResBound
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleCocyclesCardLeSumDimsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodCoefficientRingPadicIntegersFinExt
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries TensorProduct
open Formalism.MainNotions.N (twistRep coefRep)
open ReciprocityTheory.Def (Z1 H1)

namespace GlobalTheory.ResidueBound

theorem exists_residue (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [FaithfulSMul ℤ_[l] O] (lam : O) (h : Irreducible lam) :
    Finite (O ⧸ Ideal.span {lam}) ∧ ∃ (k : Type) (_ : Field k) (_ : Algebra O k), CharP k l ∧
      Function.Surjective (algebraMap O k) ∧ ∀ x, algebraMap O k x = 0 ↔ lam ∣ x := by
  have hm : IsLocalRing.maximalIdeal O = Ideal.span {lam} := h.maximalIdeal_eq
  have hl : (l : O) ∈ IsLocalRing.maximalIdeal O := by
    have h1 : ((IsLocalRing.maximalIdeal O).comap (algebraMap ℤ_[l] O)).IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal _
    have h2 := IsLocalRing.eq_maximalIdeal h1
    have h3 : (l : ℤ_[l]) ∈ IsLocalRing.maximalIdeal ℤ_[l] := by
      rw [PadicInt.maximalIdeal_eq_span_p]; exact Ideal.mem_span_singleton_self _
    rw [← h2, Ideal.mem_comap, map_natCast] at h3
    exact h3
  have hloc : IsLocalHom (algebraMap ℤ_[l] O) := inferInstance
  have hfin : Finite (IsLocalRing.ResidueField O) := by
    have : Finite (IsLocalRing.ResidueField ℤ_[l]) := Finite.of_equiv _ (PadicInt.residueField (p := l)).toEquiv.symm
    exact Module.finite_of_finite (IsLocalRing.ResidueField ℤ_[l])
  refine ⟨?_, IsLocalRing.ResidueField O, inferInstance, inferInstance, ?_, IsLocalRing.residue_surjective, fun x => ?_⟩
  · rw [← hm]; exact hfin
  · rw [CharP.charP_iff_prime_eq_zero (Fact.out : l.Prime), ← map_natCast (IsLocalRing.residue O),
      IsLocalRing.residue_eq_zero_iff]
    exact hl
  · rw [← Ideal.mem_span_singleton, ← hm]
    exact IsLocalRing.residue_eq_zero_iff x

variable {O G k : Type} [CommRing O] [Group G] [Field k] [Algebra O k] {lam : O}

theorem exists_tensor_equiv {M N : Type} [AddCommGroup M] [Module O M] [AddCommGroup N] [Module O N]
    (q : M →ₗ[O] N) (hq : Function.Surjective q) (hk : KerIs lam q) :
    ∃ φ : (M ⊗[O] (O ⧸ Ideal.span {lam})) ≃ₗ[O] N, ∀ m y, φ (m ⊗ₜ Ideal.Quotient.mk _ y) = y • q m := by
  have hN : ∀ x : N, lam • x = 0 := fun x => by
    obtain ⟨m, rfl⟩ := hq x
    rw [← map_smul]; exact (hk _).2 ⟨m, rfl⟩
  let f : (M ⊗[O] (O ⧸ Ideal.span {lam})) →ₗ[O] N := TensorProduct.lift ((cycMap hN).comp q)
  have hf : ∀ m y, f (m ⊗ₜ Ideal.Quotient.mk _ y) = y • q m := fun _ _ => rfl
  have h1 : ∀ x : M ⊗[O] (O ⧸ Ideal.span {lam}), ∃ m : M, x = m ⊗ₜ Ideal.Quotient.mk _ 1 := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul m y =>
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
      refine ⟨y • m, ?_⟩
      rw [TensorProduct.smul_tmul]
      congr 1
      change _ = Ideal.Quotient.mk _ (y * 1)
      rw [mul_one]
    | add a b ha hb =>
      obtain ⟨a, rfl⟩ := ha
      obtain ⟨b, rfl⟩ := hb
      exact ⟨a + b, (TensorProduct.add_tmul _ _ _).symm⟩
  refine ⟨LinearEquiv.ofBijective f ⟨?_, fun x => ?_⟩, hf⟩
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨m, rfl⟩ := h1 x
    rw [hf, one_smul] at hx
    obtain ⟨y, rfl⟩ := (hk m).1 hx
    rw [TensorProduct.smul_tmul]
    have : lam • Ideal.Quotient.mk (Ideal.span {lam}) 1 = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
    rw [this, TensorProduct.tmul_zero]
  · obtain ⟨m, rfl⟩ := hq x
    exact ⟨m ⊗ₜ Ideal.Quotient.mk _ 1, by rw [hf, one_smul]⟩

theorem exists_ext (T : Ob k G) (z : G → Fin T.m → k) (hz : ∀ g h, z (g * h) = z g + T.ρ g (z h)) :
    ∃ (E : Ob k G) (e : ((Fin T.m → k) × k) ≃ₗ[k] (Fin E.m → k)), IsExt T E z ∧
      ∀ g v y, E.ρ g (e (v, y)) = e (T.ρ g v + y • z g, y) := by
  have hz1 : z 1 = 0 := by simpa using hz 1 1
  let π : Representation k G ((Fin T.m → k) × k) :=
    { toFun := fun g => ((T.ρ g).coprod (LinearMap.toSpanSingleton k _ (z g))).prod (LinearMap.snd k _ _)
      map_one' := by
        refine LinearMap.ext fun x => ?_
        simp [hz1]
      map_mul' := fun g h => by
        refine LinearMap.ext fun x => ?_
        simp [hz g h]
        abel }
  obtain ⟨E, e, he⟩ := exists_ob π
  have he' : ∀ g v y, E.ρ g (e (v, y)) = e (T.ρ g v + y • z g, y) := fun g v y => (he g (v, y)).symm
  refine ⟨E, e, ⟨?_, e.toLinearMap ∘ₗ LinearMap.inl k _ _, e (0, 1), fun g x => ?_, ?_, ?_, fun g => ?_⟩, he'⟩
  · have := e.finrank_eq
    simpa using this.symm
  · simp [he']
  · exact e.injective.comp LinearMap.inl_injective
  · rintro ⟨x, hx⟩
    have := congrArg Prod.snd (e.injective hx)
    simp at this
  · rw [he']
    change _ = e (0, 1) + e (z g, 0)
    rw [← map_add]
    simp

variable [TopologicalSpace G]

theorem linearIndependent_of_indepMod (hs : Function.Surjective (algebraMap O k))
    (hk : ∀ x, algebraMap O k x = 0 ↔ lam ∣ x) {N : Type} [AddCommGroup N] [Module O N]
    (π : Representation O G N) (T : Ob k G) (φ : N ≃ₗ[O] (Fin T.m → k)) (hφ : ∀ g x, φ (π g x) = T.ρ g (φ x))
    {s : ℕ} (z : Fin s → ↥(Z1 π ⊤)) (hz : IndepMod lam fun a => (Submodule.Quotient.mk (z a) : H1 π ⊤)) :
    LinearIndependent k fun a => (cob T).mkQ fun g => φ ((z a : G → N) g) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc a
  choose x hx using fun a => hs (c a)
  rw [← hx, hk]
  refine hz x ?_ a
  simp only [← map_smul, ← map_sum] at hc
  obtain ⟨b, hb⟩ := (Submodule.Quotient.mk_eq_zero _).1 hc
  have h1 : ∑ a, x a • (Submodule.Quotient.mk (z a) : H1 π ⊤) = Submodule.Quotient.mk (∑ a, x a • z a) := by
    change ∑ a, x a • Submodule.mkQ _ (z a) = Submodule.mkQ _ _
    simp only [map_smul, map_sum]
  rw [h1, Submodule.Quotient.mk_eq_zero]
  refine ⟨φ.symm b, Submodule.mem_top, ?_⟩
  funext g
  apply φ.injective
  have h2 := congrFun hb g
  change φ (π g (φ.symm b) - φ.symm b) = _
  rw [map_sub, hφ, φ.apply_symm_apply]
  refine Eq.trans h2 ?_
  simp [← hx]

theorem exists_ext_Ea (hs : Function.Surjective (algebraMap O k)) (hk : ∀ x, algebraMap O k x = 0 ↔ lam ∣ x)
    {M X : Type} [AddCommGroup M] [Module O M] [AddCommGroup X] [Module O X] (W : Representation O G M)
    (χ : G →* Oˣ) (T : Ob k G) (φ : (M ⊗[O] X) ≃ₗ[O] (Fin T.m → k))
    (hφ : ∀ g x, φ (twCoef W χ X g x) = T.ρ g (φ x)) (ha : ∀ x : X, lam ^ 1 • x = 0)
    (z : ↥(Z1 (twCoef W χ X) ⊤)) :
    ∃ (E : Ob k G) (e : ((M ⊗[O] X) × (O ⧸ Ideal.span {lam ^ 1})) ≃ₗ[O] (Fin E.m → k)),
      IsExt T E (fun g => φ ((z : G → M ⊗[O] X) g)) ∧
      ∀ g x, e (twistRep (Ea W χ ha z) χ⁻¹ g x) = E.ρ g (e x) := by
  obtain ⟨E, e, hE, he⟩ := exists_ext T (fun g => φ ((z : G → M ⊗[O] X) g)) (fun g h => by
    rw [cocycle_mul, map_add, hφ])
  have hker : Ideal.span {lam ^ 1} = LinearMap.ker (Algebra.linearMap O k) := by
    ext x
    rw [pow_one, Ideal.mem_span_singleton, ← hk]
    rfl
  let ψ : (O ⧸ Ideal.span {lam ^ 1}) ≃ₗ[O] k :=
    (Submodule.quotEquivOfEq _ _ hker).trans ((Algebra.linearMap O k).quotKerEquivOfSurjective hs)
  have hψ : ∀ y, ψ (Ideal.Quotient.mk _ y) = algebraMap O k y := fun _ => rfl
  refine ⟨E, (φ.prodCongr ψ).trans (e.restrictScalars O), hE, ?_⟩
  rintro g ⟨m, y⟩
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  have h1 : twistRep (Ea W χ ha z) χ⁻¹ g (m, Ideal.Quotient.mk _ y) =
      (twCoef W χ X g m + y • (z : G → M ⊗[O] X) g, Ideal.Quotient.mk _ y) := by
    rw [twistRep_apply, Ea, twistRep_apply, smul_smul, extRep_apply]
    simp
  rw [h1]
  change e (φ _, ψ _) = E.ρ g (e (φ _, ψ _))
  rw [he, map_add, hφ, map_smul, hψ, algebraMap_smul]

omit [TopologicalSpace G] in

theorem exists_coef_equiv {M : Type} [AddCommGroup M] [Module O M] (W : Representation O G M)
    (χ : G →* Oˣ) (T : Ob k G) (q : M →ₗ[O] (Fin T.m → k)) (hq : Function.Surjective q) (hk : KerIs lam q)
    (he : ∀ σ x, q (twistRep W χ⁻¹ σ x) = T.ρ σ (q x)) :
    ∃ φ : (M ⊗[O] (O ⧸ Ideal.span {lam})) ≃ₗ[O] (Fin T.m → k),
      ∀ g x, φ (twCoef W χ (O ⧸ Ideal.span {lam}) g x) = T.ρ g (φ x) := by
  obtain ⟨φ, hφ⟩ := exists_tensor_equiv q hq hk
  refine ⟨φ, fun g x => ?_⟩
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul m y =>
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [coefRep_tmul, hφ, hφ, he, LinearMap.map_smul_of_tower]
  | add a b ha hb => simp only [map_add, ha, hb]

theorem exists_independent_admissible_cocycles_residue {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL]
    [Algebra O LL] [TopologicalSpace LL] {n r l : ℕ} (emb : ZMod n → (K₀ →ₐ[Qp] LL))
    (Γ : GalData G Qp LL O) (D : TopData n r) (hs : Function.Surjective (algebraMap O k))
    (hk : ∀ x, algebraMap O k x = 0 ↔ Γ.lam ∣ x) {R : RingPG k l} (F : DFun R n G) (M : ModTh F D)
    (q : ↥Γ.T₀.L.T →ₗ[O] (Fin M.T.m → k)) (hq : Function.Surjective q) (hker : KerIs Γ.lam q)
    (hqe : ∀ σ x, q (twistRep Γ.W₀ Γ.χ₁⁻¹ σ x) = M.T.ρ σ (q x))
    (hmod : ∀ (A : Ob k G) (N : Type) [AddCommGroup N] [Module O N] (π : Representation O G N)
      (e : N ≃ₗ[O] (Fin A.m → k)), Admissible PD emb Γ D.t D.Ut π →
      (∀ σ x, e (twistRep π Γ.χ₁⁻¹ σ x) = A.ρ σ (e x)) → ∃ L, M.Model A L)
    (h0 : ∀ (a : ℕ) (ha : ∀ x : GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.resK Γ, Γ.lam ^ a • x = 0), 1 ≤ a →
      adm PD emb Γ D.t D.Ut Γ.W₀ (GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.resK Γ) =
        admAt PD emb Γ D.t D.Ut Γ.W₀ (GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.resK Γ) a ha)
    (s : ℕ) (c : Fin s → H1 (twCoef Γ.W₀ Γ.χ₁ (GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.resK Γ)) ⊤)
    (hc : ∀ a, c a ∈ adm PD emb Γ D.t D.Ut Γ.W₀ (GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.resK Γ)) (hi : IndepMod Γ.lam c) :
    ∃ z : Fin s → G → Fin M.T.m → k, (∀ a, z a ∈ M.twistedModelAdmissibleCocycles M.T) ∧
      LinearIndependent k (fun a => (cob M.T).mkQ (z a)) := by
  obtain ⟨φ, hφ⟩ := exists_coef_equiv Γ.W₀ Γ.χ₁ M.T q hq hker hqe
  have ha : ∀ x : GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.resK Γ, Γ.lam ^ 1 • x = 0 := fun x => by
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [pow_one]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
  rw [h0 1 ha le_rfl] at hc
  choose z hz hadm using hc
  obtain rfl : c = fun a => Submodule.Quotient.mk (z a) := funext fun a => (hz a).symm
  refine ⟨_, fun a => ?_, linearIndependent_of_indepMod hs hk _ M.T φ hφ z hi⟩
  obtain ⟨E, e, hE, he⟩ := exists_ext_Ea hs hk Γ.W₀ Γ.χ₁ M.T φ hφ ha (z a)
  obtain ⟨L, hL⟩ := hmod E _ _ e (hadm a) he
  exact ⟨E, L, hE, hL⟩

theorem resBound_dsum : GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.LemmaPsi → ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (S : TopSit P),
    S.Real → S.Lem0 S.Γ.W₀ → S.ResBound S.Γ.W₀ S.D.dsum := by
  intro hψ l _ P S hR h0 s c hc hi
  obtain ⟨⟨hdom, hdvr, hfr⟩, hfd, -⟩ := GlobalTheory.LocalIntegers.goodO_integers l S.LL
  have hfinO : Module.Finite ℤ_[l] S.O :=
    IsIntegralClosure.finite ℤ_[l] ℚ_[l] ↥S.LL.1 ↥(integralClosure ℤ_[l] ↥S.LL.1)
  have hfa : FaithfulSMul ℤ_[l] S.O := by
    rw [faithfulSMul_iff_algebraMap_injective]
    have h1 : Function.Injective (algebraMap ℤ_[l] ↥S.LL.1) := by
      rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] ↥S.LL.1]
      exact (algebraMap ℚ_[l] ↥S.LL.1).injective.comp (IsFractionRing.injective ℤ_[l] ℚ_[l])
    rw [IsScalarTower.algebraMap_eq ℤ_[l] S.O ↥S.LL.1, RingHom.coe_comp] at h1
    exact h1.of_comp
  obtain ⟨hst, -, hT1, hT2, hT3⟩ := S.hyp
  obtain ⟨hfin, k, _, _, hch, hs, hk⟩ := exists_residue l S.O S.Γ.lam hst.2.2.2.2.2
  obtain ⟨R, ι, hι, F, M, -, ⟨q, hq, hker, hqe⟩, hmod⟩ := hR k ⟨hs, hk⟩
  obtain ⟨z, hz, hli⟩ := exists_independent_admissible_cocycles_residue (P.PD S.K) S.emb S.Γ S.D hs hk F M q hq hker hqe hmod
    (@h0 (GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.resK S.Γ) _ _ hfin).2.1 s c hc hi
  exact GlobalTheory.T.admissible_cocycles_card_le_sum_dims hψ F M ι hι hT1 hT2 hT3 s z hz hli

end GlobalTheory.ResidueBound
