import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ResBound
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleCocycleNegCharPowerMemCoboundariesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TrivialLineAdmissibleCocyclesNotIndependentStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvrComplete
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteQuotientPow

noncomputable section
namespace GlobalTheory.TopSteps.CharBound
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries TensorProduct
open Formalism.MainNotions.N (twistRep coefRep)
open ReciprocityTheory.Def (Z1 H1)

theorem exists_ext {k G : Type} [Field k] [Group G] (A : Ob k G) (z : G → Fin A.m → k)
    (h1 : z 1 = 0) (hz : ∀ g h, z (g * h) = z g + A.ρ g (z h)) :
    ∃ (E : Ob k G) (e : ((Fin A.m → k) × k) ≃ₗ[k] (Fin E.m → k)), IsExt A E z ∧
      ∀ g x y, e (A.ρ g x + y • z g, y) = E.ρ g (e (x, y)) := by
  let π : Representation k G ((Fin A.m → k) × k) :=
    { toFun := fun g => ((A.ρ g).coprod (LinearMap.toSpanSingleton k _ (z g))).prod (LinearMap.snd k _ _)
      map_one' := by
        refine LinearMap.ext fun x => ?_
        simp [h1]
      map_mul' := fun g h => by
        refine LinearMap.ext fun x => ?_
        obtain ⟨m, y⟩ := x
        simp [hz g h]
        abel }
  obtain ⟨E, e, he⟩ := exists_ob π
  have he' : ∀ g x y, e (A.ρ g x + y • z g, y) = E.ρ g (e (x, y)) := fun g x y => he g (x, y)
  refine ⟨E, e, ⟨?_, e.toLinearMap ∘ₗ LinearMap.inl k _ _, e (0, 1), fun g x => ?_, ?_, ?_, fun g => ?_⟩, he'⟩
  · have := e.finrank_eq
    simp at this
    exact this.symm
  · simpa using he' g x 0
  · exact e.injective.comp LinearMap.inl_injective
  · rintro ⟨x, hx⟩
    have := e.injective hx
    simp at this
  · rw [← he']
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, ← map_add]
    simp

theorem exists_resEquiv {O k : Type} [CommRing O] [Field k] [Algebra O k] {c : O}
    (hs : Function.Surjective (algebraMap O k)) (hk : ∀ x, algebraMap O k x = 0 ↔ c ∣ x) :
    ∃ e : (O ⧸ Ideal.span {c}) ≃ₗ[O] k, ∀ y, e (Ideal.Quotient.mk _ y) = algebraMap O k y := by
  have h : Ideal.span {c} = LinearMap.ker (Algebra.linearMap O k) := by
    ext x
    rw [Ideal.mem_span_singleton, LinearMap.mem_ker, Algebra.linearMap_apply, hk]
  exact ⟨(Submodule.quotEquivOfEq _ _ h).trans ((Algebra.linearMap O k).quotKerEquivOfSurjective hs),
    fun _ => rfl⟩

section
variable {O G k : Type} [CommRing O] [Group G] [TopologicalSpace G] [Field k] [Algebra O k]

theorem exists_ext_Ea {M : Type} [AddCommGroup M] [Module O M] (W : Representation O G M) (χ : G →* Oˣ)
    {X : Type} [AddCommGroup X] [Module O X] {c : O} (hc : ∀ x : X, c • x = 0)
    (hs : Function.Surjective (algebraMap O k)) (hk : ∀ x, algebraMap O k x = 0 ↔ c ∣ x)
    (z : ↥(Z1 (twCoef W χ X) ⊤)) (A : Ob k G) (q : (M ⊗[O] X) ≃ₗ[O] (Fin A.m → k))
    (hq : ∀ g x, q (twCoef W χ X g x) = A.ρ g (q x)) :
    ∃ (E : Ob k G) (e : ((M ⊗[O] X) × (O ⧸ Ideal.span {c})) ≃ₗ[O] (Fin E.m → k)),
      IsExt A E (fun g => q ((z : G → M ⊗[O] X) g)) ∧
      ∀ σ x, e (twistRep (Ea W χ hc z) χ⁻¹ σ x) = E.ρ σ (e x) := by
  obtain ⟨r, hr⟩ := exists_resEquiv hs hk
  obtain ⟨E, e, hE, he⟩ := exists_ext A (fun g => q ((z : G → M ⊗[O] X) g)) (by simp [cocycle_one])
    (fun g h => by rw [cocycle_mul z g h, map_add, hq])
  refine ⟨E, (q.prodCongr r).trans (e.restrictScalars O), hE, ?_⟩
  rintro σ ⟨m, y⟩
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  have : twistRep (Ea W χ hc z) χ⁻¹ σ (m, Ideal.Quotient.mk _ y) =
      (twCoef W χ X σ m + y • (z : G → M ⊗[O] X) σ, Ideal.Quotient.mk _ y) := by
    rw [Ea, twistRep_apply, twistRep_apply, smul_smul, extRep_apply]
    simp
  rw [this]
  simp only [LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply, LinearEquiv.restrictScalars_apply, map_add,
    map_smul, hq, hr]
  rw [← he, algebraMap_smul]

theorem linearIndependent_of_indepMod {N : Type} [AddCommGroup N] [Module O N] (π : Representation O G N)
    {lam : O} (hs : Function.Surjective (algebraMap O k)) (hk : ∀ x, algebraMap O k x = 0 ↔ lam ∣ x)
    (A : Ob k G) (q : N ≃ₗ[O] (Fin A.m → k)) (hq : ∀ g x, q (π g x) = A.ρ g (q x)) {s : ℕ}
    (z : Fin s → ↥(Z1 π ⊤)) (h : IndepMod lam (fun a => (Submodule.Quotient.mk (z a) : H1 π ⊤))) :
    LinearIndependent k (fun a => (cob A).mkQ (fun g => q ((z a : G → N) g))) := by
  rw [Fintype.linearIndependent_iff]
  intro y hy a
  choose x hx using fun a => hs (y a)
  rw [← hx, hk]
  refine h x ?_ a
  simp only [← map_smul, ← map_sum] at hy
  obtain ⟨b, hb⟩ := (Submodule.Quotient.mk_eq_zero _).mp hy
  have e1 : ∑ a, x a • (Submodule.Quotient.mk (z a) : H1 π ⊤) = Submodule.mkQ _ (∑ a, x a • z a) := by
    rw [map_sum]; rfl
  rw [e1]
  refine (Submodule.Quotient.mk_eq_zero _).mpr ⟨q.symm b, Submodule.mem_top, ?_⟩
  funext g
  apply q.injective
  have := congrFun hb g
  simp only [LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.id_apply, Finset.sum_apply, Pi.smul_apply,
    ← hx, algebraMap_smul] at this
  change q (π g (q.symm b) - q.symm b) = _
  rw [map_sub, hq, q.apply_symm_apply, this]
  simp
end

theorem exists_charEquiv {G : Type} [Group G] [TopologicalSpace G] {Qp LL O k : Type} [Field Qp] [Field LL]
    [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] [Field k] [Algebra O k]
    (Γ : GalData G Qp LL O) (hs : Function.Surjective (algebraMap O k))
    (hk : ∀ x, algebraMap O k x = 0 ↔ Γ.lam ∣ x) (ω : G →* kˣ) (hω : ∀ σ, (ω σ : k) = algebraMap O k (Γ.ε σ))
    (c : ℕ) :
    ∃ q : (O ⊗[O] GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.resK Γ) ≃ₗ[O] (Fin (chr (ω ^ (-((c : ℤ) - 1)))).m → k),
      ∀ g x, q (twCoef (Γ.Wchi c) Γ.χ₁ _ g x) = (chr (ω ^ (-((c : ℤ) - 1)))).ρ g (q x) := by
  obtain ⟨r, -⟩ := exists_resEquiv hs hk
  refine ⟨((TensorProduct.lid O _).trans r).trans (LinearEquiv.funUnique (Fin 1) O k).symm, fun g x => ?_⟩
  rw [GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleTwistedCharClasses.twCoef_Wchi, map_smul]
  have h : ω g = Units.map (algebraMap O k : O →* k) (Γ.ε g) := Units.ext (hω g)
  have h2 : (((ω ^ (-((c : ℤ) - 1))) g : kˣ) : k) = algebraMap O k ((Γ.ε g) ^ (-((c : ℤ) - 1)) : Oˣ) := by
    rw [MonoidHom.zpow_apply, h, ← map_zpow]; rfl
  have h3 : ∀ (θ : G →* kˣ) (v : Fin 1 → k), (chr θ).ρ g v = (θ g : k) • v := fun _ _ => rfl
  rw [h3, h2, algebraMap_smul]

section
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {n r : ℕ} (emb : ZMod n → (K₀ →ₐ[Qp] LL))
    (D : TopData n r) (Γ : GalData G Qp LL O) {k : Type} [Field k] [Algebra O k]

theorem lam_smul_resK (x : GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.resK Γ) : Γ.lam ^ 1 • x = 0 := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [pow_one]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))

theorem exists_cocycles_gen (hs : Function.Surjective (algebraMap O k))
    (hk : ∀ x, algebraMap O k x = 0 ↔ Γ.lam ∣ x) {l : ℕ} {R : RingPG k l} {F : DFun R n G} (M : ModTh F D)
    (hM : ∀ (A : Ob k G) (N : Type) [AddCommGroup N] [Module O N] (π : Representation O G N)
        (e : N ≃ₗ[O] (Fin A.m → k)), Admissible PD emb Γ D.t D.Ut π →
        (∀ σ x, e (twistRep π Γ.χ₁⁻¹ σ x) = A.ρ σ (e x)) → ∃ L, M.Model A L)
    {V : Type} [AddCommGroup V] [Module O V] (W : Representation O G V) {X : Type} [AddCommGroup X] [Module O X]
    (hX : ∀ x : X, Γ.lam ^ 1 • x = 0) (A : Ob k G) (q : (V ⊗[O] X) ≃ₗ[O] (Fin A.m → k))
    (hq : ∀ g x, q (twCoef W Γ.χ₁ X g x) = A.ρ g (q x))
    {s : ℕ} (x : Fin s → H1 (twCoef W Γ.χ₁ X) ⊤)
    (hx : ∀ a, x a ∈ admAt PD emb Γ D.t D.Ut W X 1 hX) (hi : IndepMod Γ.lam x) :
    ∃ z : Fin s → G → Fin A.m → k, (∀ a, z a ∈ M.twistedModelAdmissibleCocycles A) ∧
      LinearIndependent k (fun a => (cob A).mkQ (z a)) := by
  choose z hz hadm using hx
  obtain rfl : x = fun a => Submodule.Quotient.mk (z a) := funext fun a => (hz a).symm
  refine ⟨fun a g => q ((z a : G → V ⊗[O] X) g), fun a => ?_,
    linearIndependent_of_indepMod _ hs hk A q hq z hi⟩
  obtain ⟨E, e, hE, he⟩ := exists_ext_Ea W Γ.χ₁ hX hs (fun y => by rw [pow_one]; exact hk y) (z a) A q hq
  obtain ⟨L, hL⟩ := hM E _ _ e (hadm a) he
  exact ⟨E, L, hE, hL⟩

theorem bound_gen (hs : Function.Surjective (algebraMap O k))
    (hk : ∀ x, algebraMap O k x = 0 ↔ Γ.lam ∣ x) {l : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l}
    {F : DFun R n G} (M : ModTh F D) (h1 : D.T1 l) (h2 : D.T2 l) (h3 : D.T3 l)
    (hω : ∀ σ, (M.ω σ : k) = algebraMap O k (Γ.ε σ))
    (hM : ∀ (A : Ob k G) (N : Type) [AddCommGroup N] [Module O N] (π : Representation O G N)
        (e : N ≃ₗ[O] (Fin A.m → k)), Admissible PD emb Γ D.t D.Ut π →
        (∀ σ x, e (twistRep π Γ.χ₁⁻¹ σ x) = A.ρ σ (e x)) → ∃ L, M.Model A L)
    (hfin : Finite (O ⧸ Ideal.span {Γ.lam})) (c : ℕ)
    (h0 : ∀ (X : Type) [AddCommGroup X] [Module O X] [Finite X] (a : ℕ) (ha : ∀ x : X, Γ.lam ^ a • x = 0), 1 ≤ a →
      adm PD emb Γ D.t D.Ut (Γ.Wchi c) X = admAt PD emb Γ D.t D.Ut (Γ.Wchi c) X a ha)
    (s : ℕ) (x : Fin s → H1 (twCoef (Γ.Wchi c) Γ.χ₁ (GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.resK Γ)) ⊤)
    (hx : ∀ a, x a ∈ adm PD emb Γ D.t D.Ut (Γ.Wchi c) (GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.resK Γ))
    (hi : IndepMod Γ.lam x) : (2 ≤ c → c ≤ D.t → s ≤ 0) ∧ (c = 1 → s ≤ 1) := by
  rw [h0 _ 1 (lam_smul_resK Γ) le_rfl] at hx
  obtain ⟨q, hq⟩ := exists_charEquiv Γ hs hk M.ω hω c
  have key := exists_cocycles_gen PD emb D Γ hs hk M hM (Γ.Wchi c) (lam_smul_resK Γ) _ q hq x hx hi
  clear hq q hx hi x hM
  refine ⟨fun hc hct => ?_, fun hc => ?_⟩
  · obtain ⟨z, hz, hli⟩ := key
    by_contra hs0
    let a : Fin s := ⟨0, by omega⟩
    exact hli.ne_zero a ((Submodule.Quotient.mk_eq_zero _).mpr
      (GlobalTheory.T.admissibleCocycles_neg_char_pow_mem_cob F M h1 h2 h3 ((c : ℤ) - 1) (by omega) (by omega) (z a) (hz a)))
  · have e : M.ω ^ (-((c : ℤ) - 1)) = 1 := by simp [hc]
    rw [e] at key
    obtain ⟨z, hz, hli⟩ := key
    by_contra hs0
    have h2s : 2 ≤ s := by omega
    exact GlobalTheory.T.trivialLine_admissibleCocycles_not_independent F M h1 h2 h3 (fun a => z (Fin.castLE h2s a)) (fun a => hz _)
      (hli.comp _ (Fin.castLE_injective h2s))

end

theorem exists_res {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {l : ℕ} [Fact l.Prime]
    (hl : ¬ IsUnit ((l : ℕ) : O)) (hf : Finite (O ⧸ Ideal.span {((l : ℕ) : O) ^ 1})) {lam : O}
    (hlam : Irreducible lam) :
    Finite (O ⧸ Ideal.span {lam}) ∧ ∃ (k : Type) (_ : Field k) (_ : Algebra O k) (_ : CharP k l),
      Function.Surjective (algebraMap O k) ∧ ∀ x, algebraMap O k x = 0 ↔ lam ∣ x := by
  have hm := (IsDiscreteValuationRing.irreducible_iff_uniformizer lam).mp hlam
  have hl' : ((l : ℕ) : O) ∈ IsLocalRing.maximalIdeal O := hl
  refine ⟨?_, IsLocalRing.ResidueField O, inferInstance, inferInstance, ?_, IsLocalRing.residue_surjective,
    fun x => ?_⟩
  · refine Finite.of_surjective _ (Ideal.Quotient.factor_surjective (S := Ideal.span {((l : ℕ) : O) ^ 1}) ?_)
    rw [pow_one, ← hm, Ideal.span_singleton_le_iff_mem]
    exact hl'
  · rw [CharP.charP_iff_prime_eq_zero Fact.out, ← map_natCast (IsLocalRing.residue O),
      IsLocalRing.residue_eq_zero_iff]
    exact hl'
  · rw [IsLocalRing.ResidueField.algebraMap_eq, IsLocalRing.residue_eq_zero_iff, hm, Ideal.mem_span_singleton]

theorem resBound_chars : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (S : TopSit P), S.Real →
    (∀ c : ℕ, 2 ≤ c → c ≤ S.D.t → S.Lem0 (S.Γ.Wchi c) → S.ResBound (S.Γ.Wchi c) 0) ∧
    (S.Lem0 (S.Γ.Wchi 1) → S.ResBound (S.Γ.Wchi 1) 1) := by
  intro l _ P S hR
  obtain ⟨hSt, -, h1, h2, h3⟩ := S.hyp
  obtain ⟨hd, -, hl⟩ := GlobalTheory.FinExtIntegers.dvr_complete S.LL
  obtain ⟨hfin, k, _, _, _, hs, hk⟩ := exists_res hl ((GlobalTheory.LocalIntegers.good_integers l S.LL).2 1)
    hSt.2.2.2.2.2
  obtain ⟨R, ι, -, F, M, hω, -, hM⟩ := hR k ⟨hs, hk⟩
  have key := bound_gen (P.PD S.K) S.emb S.D S.Γ hs hk M h1 h2 h3 hω hM hfin
  refine ⟨fun c hc hct h0 s x hx hi => ?_, fun h0 s x hx hi => ?_⟩
  · have key' := key c (fun X _ _ _ => (h0 X).2.1)
    exact (key' s x hx hi).1 hc hct
  · have key' := key 1 (fun X _ _ _ => (h0 X).2.1)
    exact (key' s x hx hi).2 rfl

end GlobalTheory.TopSteps.CharBound
