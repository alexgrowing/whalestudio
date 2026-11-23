import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ResBound
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReductionSameSSOfLattices
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobeniusGenDegreeHomToZl
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleClassesPropsOfFlatCoefficient

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries TensorProduct Pointwise
open Formalism.MainNotions.N (twistRep coefRep)
open Formalism.GaloisCohomology (scalRep)
open ReciprocityTheory.Def (Z1 H1 H2)

noncomputable section
namespace GlobalTheory.UnramAdm

section Alg
variable {G : Type} [Group G] {LL O : Type} [Field LL] [CommRing O] [Algebra O LL]
  {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V] {ρ : Representation LL G V}

theorem asModule_equiv {M N : Type} [AddCommGroup M] [Module O M] [AddCommGroup N] [Module O N]
    (π : Representation O G M) (π' : Representation O G N) (e : M ≃ₗ[O] N) (he : ∀ g x, e (π g x) = π' g (e x)) :
    Nonempty (π.asModule ≃ₗ[MonoidAlgebra O G] π'.asModule) := by
  refine ⟨{ (π.asModuleEquiv.trans (e.trans π'.asModuleEquiv.symm)).toAddEquiv with map_smul' := ?_ }⟩
  intro r x
  apply π'.asModuleEquiv.injective
  change e (π.asModuleEquiv (r • x)) = π'.asModuleEquiv (r • (π'.asModuleEquiv.symm (e (π.asModuleEquiv x))))
  rw [Representation.asModuleEquiv_map_smul, Representation.asModuleEquiv_map_smul, LinearEquiv.apply_symm_apply]
  induction r using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]
  | single g a => simp [he]

theorem sameSS_of_surj [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O LL] {lam : O}
    (hl : Irreducible lam) (L L' : Lattice (O := O) ρ) {M : Type} [AddCommGroup M] [Module O M]
    (π : Representation O G M) (q : ↥L.T →ₗ[O] M) (hs : Function.Surjective q)
    (hk : LinearMap.ker q = lam • (⊤ : Submodule O ↥L.T)) (hq : ∀ g x, q (latRep L g x) = π g (q x)) :
    SameSS (modRep (latRep L') lam) π := by
  refine SameFactors.trans (reduction_sameSS_of_lattices ρ L' L lam hl) ?_
  obtain ⟨s, -, h1, h2, -⟩ := reduction_sameSS_of_lattices ρ L L lam hl
  let e : QuotSMulTop lam ↥L.T ≃ₗ[O] M := (Submodule.quotEquivOfEq _ _ hk.symm).trans (q.quotKerEquivOfSurjective hs)
  obtain ⟨f⟩ := asModule_equiv (modRep (latRep L) lam) π e (fun g x => by
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact hq g x)
  exact SameFactors.of_equiv (isFiniteLength_iff_exists_compositionSeries.mpr ⟨s, h1, h2⟩) f

def kerLattice [IsDomain O] [IsPrincipalIdealRing O] [IsFractionRing O LL] (L : Lattice (O := O) ρ)
    {M : Type} [AddCommGroup M] [Module O M]
    (π : Representation O G M) (q : ↥L.T →ₗ[O] M) (hq : ∀ g x, q (latRep L g x) = π g (q x)) {c : O} (hc : c ≠ 0)
    (hM : ∀ m : M, c • m = 0) : Lattice (O := O) ρ where
  T := (LinearMap.ker q).map L.T.subtype
  stable := by
    rintro g _ ⟨x, hx, rfl⟩
    refine ⟨latRep L g x, ?_, rfl⟩
    have hx' : q x = 0 := hx
    change q _ = 0
    rw [hq, hx', map_zero]
  fg := by
    have : Module.Finite O ↥L.T := Module.Finite.iff_fg.mpr L.fg
    exact (IsNoetherian.noetherian _).map _
  free := by
    have : Module.Finite O ↥L.T := Module.Finite.iff_fg.mpr L.fg
    have := L.free
    exact Module.Free.of_equiv (Submodule.equivMapOfInjective _ L.T.injective_subtype _)
  span := by
    rw [eq_top_iff, ← L.span, Submodule.span_le]
    intro x hx
    have h0 : algebraMap O LL c ≠ 0 := by simpa using hc
    have h1 : c • x ∈ Submodule.span LL (((LinearMap.ker q).map L.T.subtype : Submodule O V) : Set V) :=
      Submodule.subset_span ⟨c • ⟨x, hx⟩, (map_smul q c _).trans (hM _), rfl⟩
    have h2 := Submodule.smul_mem _ (algebraMap O LL c)⁻¹ h1
    rwa [← algebraMap_smul LL c x, smul_smul, inv_mul_cancel₀ h0, one_smul] at h2

end Alg

section Sum
variable {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL] [Algebra Qp LL]
  [CommRing O] [Algebra O LL] [TopologicalSpace LL] [IsTopologicalRing LL]

def sumEmb (T : LocLat G Qp LL O) (t : ℕ) : (↥T.L.T × (Fin t → O)) →ₗ[O] (T.V × (Fin t → LL)) :=
  T.L.T.subtype.prodMap ((Algebra.linearMap O LL).compLeft (Fin t))

omit [IsTopologicalRing LL] in
theorem sumEmb_inj (hinj : Function.Injective (algebraMap O LL)) (T : LocLat G Qp LL O) (t : ℕ) :
    Function.Injective (sumEmb T t) := by
  rintro ⟨x, a⟩ ⟨y, b⟩ h
  exact Prod.ext (Subtype.ext (congrArg Prod.fst h)) (funext fun i => hinj (congrFun (congrArg Prod.snd h) i))

def sumLat (hinj : Function.Injective (algebraMap O LL)) (T : LocLat G Qp LL O) (θ : ℕ → G →* Oˣ)
    (hθ : ∀ c, Continuous fun g => algebraMap O LL (θ c g)) (t : ℕ) : LocLat G Qp LL O where
  V := T.V × (Fin t → LL)
  ρ := T.ρ.prod (piRep fun c : Fin t => charRep (chiLL LL (θ c)))
  cont := fun x => (T.cont x.1).prodMk (continuous_pi fun c => (hθ c).mul continuous_const)
  L :=
    { T := LinearMap.range (sumEmb T t)
      stable := by
        rintro g _ ⟨⟨x, a⟩, rfl⟩
        refine ⟨(latRep T.L g x, fun c => θ c g * a c), Prod.ext rfl (funext fun c => ?_)⟩
        change algebraMap O LL (θ c g * a c) = algebraMap O LL (θ c g) • algebraMap O LL (a c)
        simp
      fg := by
        have : Module.Finite O ↥T.L.T := Module.Finite.iff_fg.mpr T.L.fg
        rw [← Submodule.map_top]
        exact Module.Finite.fg_top.map _
      free := by
        have := T.L.free
        exact Module.Free.of_equiv (LinearEquiv.ofInjective _ (sumEmb_inj hinj T t))
      span := by
        rw [eq_top_iff]
        rintro ⟨x, a⟩ -
        have h1 : Submodule.span LL (T.L.T : Set T.V) ≤ (Submodule.span LL
            (LinearMap.range (sumEmb T t) : Set (T.V × (Fin t → LL)))).comap (LinearMap.inl LL _ _) := by
          rw [Submodule.span_le]
          intro y hy
          exact Submodule.subset_span ⟨(⟨y, hy⟩, 0), Prod.ext rfl (funext fun c => map_zero (algebraMap O LL))⟩
        rw [T.L.span] at h1
        have h2 : ((x, a) : T.V × (Fin t → LL)) = (x, 0) + ∑ c, a c • ((0, Pi.single c 1) : T.V × (Fin t → LL)) := by
          ext c <;> simp [Prod.fst_sum, Prod.snd_sum, Pi.single_apply]
        rw [h2]
        refine add_mem (h1 Submodule.mem_top) (Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ ?_)
        refine Submodule.subset_span ⟨(0, Pi.single c 1), Prod.ext rfl (funext fun d => ?_)⟩
        change algebraMap O LL (Pi.single (M := fun _ => O) c 1 d) = Pi.single (M := fun _ => LL) c 1 d
        simp only [Pi.single_apply]
        split_ifs <;> simp }

theorem sumLat_equiv (hinj : Function.Injective (algebraMap O LL)) (T : LocLat G Qp LL O) (θ : ℕ → G →* Oˣ)
    (hθ : ∀ c, Continuous fun g => algebraMap O LL (θ c g)) (t : ℕ) :
    ∃ e : ↥(sumLat hinj T θ hθ t).L.T ≃ₗ[O] (↥T.L.T × (Fin t → O)), ∀ g x,
      e (latRep (sumLat hinj T θ hθ t).L g x) = (latRep T.L g (e x).1, fun c : Fin t => (θ c g : O) * (e x).2 c) := by
  let e := LinearEquiv.ofInjective _ (sumEmb_inj hinj T t)
  refine ⟨e.symm, fun g x => ?_⟩
  obtain ⟨⟨y, a⟩, rfl⟩ := e.surjective x
  refine e.symm_apply_eq.mpr ?_
  erw [e.symm_apply_apply]
  refine Subtype.ext (Prod.ext rfl (funext fun c => ?_))
  change algebraMap O LL (θ c g) • algebraMap O LL (a c) = algebraMap O LL (θ c g * a c)
  simp

end Sum

section Per
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] [IsTopologicalRing LL] {n : ℕ} (emb : ZMod n → (K₀ →ₐ[Qp] LL))

theorem block_succ (w : ℤ) (t : ℕ) : block w (t + 1) = block w t + {w + t} := by
  unfold block
  rw [Nat.cast_succ, ← add_assoc, ← Finset.insert_Ico_right_eq_Ico_add_one (by omega),
    Finset.insert_val_of_notMem (by simp), ← Multiset.singleton_add, add_comm]

theorem crys_sumLat
    (hsum : ∀ (T T' T'' : LocLat G Qp LL O) (U U' : ZMod n → Multiset ℤ) (e : T''.V ≃ₗ[LL] (T.V × T'.V)),
      (∀ σ x, e (T''.ρ σ x) = (T.ρ σ (e x).1, T'.ρ σ (e x).2)) → CrysWith PD emb T.ρ U →
      CrysWith PD emb T'.ρ U' → CrysWith PD emb T''.ρ (fun i => U i + U' i))
    (hinj : Function.Injective (algebraMap O LL)) (T : LocLat G Qp LL O) (U : ZMod n → Multiset ℤ)
    (hT : CrysWith PD emb T.ρ U) (w : ZMod n → ℤ) (θ : ℕ → G →* Oˣ)
    (hθ : ∀ c : ℕ, IsCrysChar PD emb (θ c) (fun i => w i + c)) (t : ℕ) :
    CrysWith PD emb (sumLat hinj T θ (fun c => (hθ c).1) (t + 1)).ρ (fun i => U i + block (w i) (t + 1)) := by
  induction t with
  | zero =>
    have h := hsum T (charLat Qp hinj (θ 0) (hθ 0).1) (sumLat hinj T θ (fun c => (hθ c).1) 1) U _
      ((LinearEquiv.refl LL T.V).prodCongr (LinearEquiv.funUnique (Fin 1) LL LL)) (fun _ _ => rfl) hT (hθ 0).2
    convert h using 3 with i
    rw [block_succ]
    simp [block]
  | succ t ih =>
    let e : (T.V × (Fin (t + 1 + 1) → LL)) ≃ₗ[LL] ((T.V × (Fin (t + 1) → LL)) × LL) :=
      { toFun := fun x => ((x.1, fun c => x.2 c.castSucc), x.2 (Fin.last _))
        invFun := fun x => (x.1.1, Fin.snoc (α := fun _ => LL) x.1.2 x.2)
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl
        left_inv := fun x => Prod.ext rfl (Fin.snoc_init_self x.2)
        right_inv := fun x => by simp }
    have h := hsum (sumLat hinj T θ (fun c => (hθ c).1) (t + 1)) (charLat Qp hinj (θ (t + 1)) (hθ (t + 1)).1)
      (sumLat hinj T θ (fun c => (hθ c).1) (t + 1 + 1)) _ _ e (fun _ _ => rfl) ih (hθ (t + 1)).2
    convert h using 2 with i
    rw [block_succ (w i) (t + 1), add_assoc]

theorem crysChar_mul
    (htw : ∀ (T : LocLat G Qp LL O) (U : ZMod n → Multiset ℤ) (θ : G →* Oˣ) (a : ZMod n → ℤ),
      CrysWith PD emb T.ρ U → IsCrysChar PD emb θ a →
      CrysWith PD emb (twistRep T.ρ (chiLL LL θ)) (fun i => (U i).map (· + a i)) ∧
      IsCrysChar PD emb θ⁻¹ (fun i => -a i))
    (hinj : Function.Injective (algebraMap O LL)) {χ θ : G →* Oˣ} {a b : ZMod n → ℤ}
    (hχ : IsCrysChar PD emb χ a) (hθ : IsCrysChar PD emb θ b) : IsCrysChar PD emb (χ * θ) (fun i => a i + b i) := by
  refine ⟨(hχ.1.mul hθ.1).congr fun g => by simp, ?_⟩
  have h := (htw (charLat Qp hinj χ hχ.1) _ θ b hχ.2 hθ).1
  have h2 : twistRep (charRep (chiLL LL χ)) (chiLL LL θ) = charRep (chiLL LL (χ * θ)) := by
    refine MonoidHom.ext fun g => LinearMap.ext fun x => ?_
    change algebraMap O LL (θ g) • algebraMap O LL (χ g) • x = algebraMap O LL ((χ * θ) g) • x
    simp [mul_assoc, mul_left_comm]
  rw [← h2]
  simp only [Multiset.map_singleton] at h
  exact h

variable [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O LL] (Γ : GalData G Qp LL O)

theorem sameSS_sumLat (hl : Irreducible Γ.lam) (hinj : Function.Injective (algebraMap O LL)) (θ : ℕ → G →* Oˣ)
    (hθ : ∀ c, Continuous fun g => algebraMap O LL (θ c g)) (t : ℕ)
    (hc : ∀ c g, Γ.lam ∣ (θ c g : O) - Γ.chi (c + 1) g) (L' : Lattice (O := O) (sumLat hinj Γ.T₀ θ hθ t).ρ) :
    SameSS (modRep (latRep L') Γ.lam) (Γ.refRep t) := by
  obtain ⟨e, he⟩ := sumLat_equiv hinj Γ.T₀ θ hθ t
  let q : (↥Γ.T₀.L.T × (Fin t → O)) →ₗ[O] (QuotSMulTop Γ.lam ↥Γ.T₀.L.T × (Fin t → QuotSMulTop Γ.lam O)) :=
    (Submodule.mkQ _).prodMap ((Submodule.mkQ (Γ.lam • (⊤ : Submodule O O))).compLeft (Fin t))
  have hz : ∀ {M : Type} [AddCommGroup M] [Module O M] (x : M),
      (Submodule.Quotient.mk x : QuotSMulTop Γ.lam M) = 0 ↔ ∃ y, Γ.lam • y = x := by
    intro M _ _ x
    rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_smul_pointwise_iff_exists]
    simp
  refine sameSS_of_surj hl (sumLat hinj Γ.T₀ θ hθ t).L L' _ (q ∘ₗ e.toLinearMap) ?_ ?_ ?_
  · refine Function.Surjective.comp (g := q) ?_ e.surjective
    rintro ⟨x, a⟩
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    choose b hb using fun c => Submodule.Quotient.mk_surjective _ (a c)
    exact ⟨(x, b), Prod.ext rfl (funext hb)⟩
  · ext x
    rw [Submodule.mem_smul_pointwise_iff_exists, LinearMap.mem_ker]
    constructor
    · intro h
      obtain ⟨y, hy⟩ := (hz _).mp (congrArg Prod.fst h)
      choose b hb using fun c => (hz _).mp (congrFun (congrArg Prod.snd h) c)
      refine ⟨e.symm (y, b), trivial, e.injective ?_⟩
      rw [map_smul, e.apply_symm_apply]
      exact Prod.ext hy (funext hb)
    · rintro ⟨y, -, rfl⟩
      rw [map_smul]
      exact Prod.ext ((hz _).mpr ⟨_, rfl⟩) (funext fun c => (hz _).mpr ⟨_, rfl⟩)
  · intro g x
    change q (e _) = Γ.refRep t g (q (e x))
    rw [he]
    refine Prod.ext rfl (funext fun c => ?_)
    change (Submodule.Quotient.mk ((θ c g : O) * (e x).2 c) : QuotSMulTop Γ.lam O) =
      Submodule.Quotient.mk ((Γ.chi (c + 1) g : O) • (e x).2 c)
    rw [← sub_eq_zero, ← Submodule.Quotient.mk_sub, hz]
    obtain ⟨d, hd⟩ := hc c g
    exact ⟨d * (e x).2 c, by rw [smul_eq_mul, smul_eq_mul, ← sub_mul, hd, mul_assoc]⟩

omit [IsTopologicalRing LL] in

theorem admissible_quotient_of_fullRepresentation {t : ℕ} {Ut : ZMod n → Multiset ℤ} {T : LocLat G Qp LL O} (hT : Full PD emb Γ t Ut T)
    {M : Type} [AddCommGroup M] [Module O M] [Finite M] (π : Representation O G M) (q : ↥T.L.T →ₗ[O] M)
    (hs : Function.Surjective q) (hq : ∀ g x, q (latRep T.L g x) = π g (q x)) {c : O} (hc : c ≠ 0)
    (hM : ∀ m : M, c • m = 0) : Admissible PD emb Γ t Ut π := by
  refine ⟨‹_›, 1, T, hT.sumFull, kerLattice T.L π q hq hc hM, q, ?_, hs, hq, fun x => ⟨fun h => ⟨x, h, rfl⟩, ?_⟩⟩
  · rintro _ ⟨x, -, rfl⟩
    exact x.2
  · rintro ⟨y, hy, h⟩
    obtain rfl : y = x := Subtype.ext h
    exact hy

theorem admissible_crystallineCharacterQuotient {r : ℕ} (D : TopData n r) (hl : Irreducible Γ.lam) (hG : IsTopGal PD emb D Γ)
    (hsum : ∀ (T T' T'' : LocLat G Qp LL O) (U U' : ZMod n → Multiset ℤ) (e : T''.V ≃ₗ[LL] (T.V × T'.V)),
      (∀ σ x, e (T''.ρ σ x) = (T.ρ σ (e x).1, T'.ρ σ (e x).2)) → CrysWith PD emb T.ρ U →
      CrysWith PD emb T'.ρ U' → CrysWith PD emb T''.ρ (fun i => U i + U' i))
    (htw : ∀ (T : LocLat G Qp LL O) (U : ZMod n → Multiset ℤ) (θ : G →* Oˣ) (a : ZMod n → ℤ),
      CrysWith PD emb T.ρ U → IsCrysChar PD emb θ a →
      CrysWith PD emb (twistRep T.ρ (chiLL LL θ)) (fun i => (U i).map (· + a i)) ∧
      IsCrysChar PD emb θ⁻¹ (fun i => -a i))
    (hε : IsCrysChar PD emb Γ.ε (fun _ => -1)) (μ : G →* Oˣ) (hμ : IsCrysChar PD emb μ (fun _ => 0))
    (hμ1 : ∀ g, Γ.lam ∣ (μ g : O) - 1) {c : O} (hc : c ≠ 0) [Finite (O ⧸ Ideal.span {c})] :
    Admissible PD emb Γ D.t D.Ut (scalRep (O ⧸ Ideal.span {c}) (Γ.χ₁ * μ)) := by
  have hinj : Function.Injective (algebraMap O LL) := IsFractionRing.injective O LL
  have h1 : ∀ c : ℕ, IsCrysChar PD emb (Γ.chi (c + 1)) (fun i => D.w i + c) := by
    intro c
    induction c with
    | zero => simpa using hG.2.2.1
    | succ c ih =>
      rw [GalData.chi_succ]
      have := crysChar_mul PD emb htw hinj ih (htw _ _ _ _ hG.2.1 hε).2
      simpa [add_assoc] using this
  have h2 : ∀ c : ℕ, IsCrysChar PD emb (Γ.chi (c + 1) * μ) (fun i => D.w i + c) := fun c => by
    simpa using crysChar_mul PD emb htw hinj (h1 c) hμ
  obtain ⟨t, ht⟩ : ∃ t, D.t = t + 1 := ⟨D.t - 1, by have := D.one_le_letterBlockLength; omega⟩
  have hF : Full PD emb Γ D.t D.Ut (sumLat hinj Γ.T₀ (fun c => Γ.chi (c + 1) * μ) (fun c => (h2 c).1) (t + 1)) := by
    refine ⟨?_, fun L => ?_⟩
    · have := crys_sumLat PD emb hsum hinj Γ.T₀ D.U hG.2.1 D.w _ h2 t
      convert this using 2 with i
      rw [TopData.Ut, TopData.B, ht]
    · rw [ht]
      refine sameSS_sumLat Γ hl hinj _ _ _ (fun c g => ?_) L
      have : ((Γ.chi (c + 1) * μ) g : O) - Γ.chi (c + 1) g = Γ.chi (c + 1) g * (μ g - 1) := by
        simp [mul_sub]
      rw [this]
      exact (hμ1 g).mul_left _
  obtain ⟨e, he⟩ := sumLat_equiv hinj Γ.T₀ (fun c => Γ.chi (c + 1) * μ) (fun c => (h2 c).1) (t + 1)
  let q : (↥Γ.T₀.L.T × (Fin (t + 1) → O)) →ₗ[O] (O ⧸ Ideal.span {c}) :=
    (Submodule.mkQ _) ∘ₗ (LinearMap.proj 0) ∘ₗ LinearMap.snd O _ _
  refine admissible_quotient_of_fullRepresentation PD emb Γ hF _ (q ∘ₗ e.toLinearMap) ?_ ?_ hc ?_
  · refine Function.Surjective.comp (g := q) ?_ e.surjective
    intro x
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact ⟨(0, fun _ => x), rfl⟩
  · intro g x
    change q (e _) = scalRep _ (Γ.χ₁ * μ) g (q (e x))
    rw [he, ← GalData.chi_one]
    rfl
  · intro m
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective m
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))

end Per

section Ext
open GlobalTheory.AdmClasses
variable {O G : Type} [CommRing O] [Group G]
  {Ad : ∀ (M : Type) [AddCommGroup M] [Module O M], Representation O G M → Prop}

theorem subquot (h : ClosedClass Ad) {M M' N : Type} [AddCommGroup M] [Module O M] [AddCommGroup M'] [Module O M']
    [AddCommGroup N] [Module O N] (π : Representation O G M) (π' : Representation O G M') (f : N →ₗ[O] M')
    (q : N →ₗ[O] M) (hs : ∀ g x, ∃ y, f y = π' g (f x) ∧ q y = π g (q x)) (hk : ∀ x, f x = 0 → q x = 0)
    (hq : Function.Surjective q) (h' : Ad M' π') : Ad M π := by
  let R : Submodule O (M' × M) := LinearMap.range (f.prod q)
  have hR : ∀ g, R ≤ R.comap ((π'.prod π) g) := by
    rintro g _ ⟨x, rfl⟩
    obtain ⟨y, h1, h2⟩ := hs g x
    exact ⟨y, Prod.ext h1 h2⟩
  refine h.quot (π := (π'.prod π).subrepresentation R hR) (LinearMap.snd O _ _ ∘ₗ R.subtype) (fun _ _ => rfl) ?_
    (h.sub (LinearMap.fst O _ _ ∘ₗ R.subtype) (fun _ _ => rfl) ?_ h')
  · intro m
    obtain ⟨x, rfl⟩ := hq m
    exact ⟨⟨_, x, rfl⟩, rfl⟩
  · rw [injective_iff_map_eq_zero]
    rintro ⟨_, x, rfl⟩ hx
    exact Subtype.ext (Prod.ext hx (hk x hx))

theorem ext_mem [IsDomain O] [TopologicalSpace G] (h : ClosedClass Ad) {M : Type} [AddCommGroup M] [Module O M]
    (π : Representation O G M) (hπ : ∀ g m, π g m = m) {b c : O} (hb : ∀ m : M, b • m = 0) (hbc : b ∣ c) (hc : c ≠ 0)
    (z : ↥(Z1 π ⊤)) (χ μ : G →* Oˣ) (w : G → O) (hw : ∀ g, (μ g : O) = 1 + c * w g) (ξ : M)
    (hz : ∀ g, (z : G → M) g = w g • ξ) (h1 : Ad _ (twistRep π χ))
    (h2 : Ad _ (scalRep (O ⧸ Ideal.span {c ^ 2}) (χ * 1))) (h3 : Ad _ (scalRep (O ⧸ Ideal.span {c ^ 2}) (χ * μ))) :
    Ad _ (twistRep (extRep π hb z) χ) := by
  let f : (M × O × O) →ₗ[O] (M × (O ⧸ Ideal.span {c ^ 2}) × (O ⧸ Ideal.span {c ^ 2})) :=
    LinearMap.id.prodMap ((Submodule.mkQ _ ∘ₗ (c • LinearMap.fst O O O - LinearMap.snd O O O)).prod
      (Submodule.mkQ _ ∘ₗ LinearMap.snd O O O))
  let q : (M × O × O) →ₗ[O] (M × (O ⧸ Ideal.span {b})) :=
    (LinearMap.id.coprod (LinearMap.toSpanSingleton O M ξ ∘ₗ LinearMap.fst O O O)).prod
      (Submodule.mkQ _ ∘ₗ LinearMap.snd O O O ∘ₗ LinearMap.snd O M _)
  have hf : ∀ x s y, f (x, s, y) = (x, Ideal.Quotient.mk _ (c * s - y), Ideal.Quotient.mk _ y) := fun _ _ _ => rfl
  have hq : ∀ x s y, q (x, s, y) = (x + s • ξ, Ideal.Quotient.mk _ y) := fun _ _ _ => rfl
  refine subquot h _ _ f q ?_ ?_ ?_ (h.prod h1 (h.prod h2 h3))
  · rintro g ⟨x, s, y⟩
    refine ⟨((χ g : O) • x, χ g * (s + y * w g), χ g * μ g * y), ?_, ?_⟩
    · rw [hf, hf]
      refine Prod.ext ?_ (Prod.ext ?_ rfl)
      · change (χ g : O) • x = (χ g : O) • π g x
        rw [hπ]
      · change Ideal.Quotient.mk _ _ = Ideal.Quotient.mk _ (((χ * 1) g : O) * (c * s - y))
        congr 1
        rw [mul_one, hw]
        ring
    · rw [hq, hq, twistRep_apply, extRep_apply, hπ, hz]
      refine Prod.ext ?_ ?_
      · simp only [Prod.smul_fst, smul_add, smul_smul, mul_add, add_smul, add_assoc]
      · change Ideal.Quotient.mk _ _ = Ideal.Quotient.mk _ ((χ g : O) * y)
        rw [Ideal.Quotient.eq, Ideal.mem_span_singleton, hw]
        exact hbc.trans ⟨χ g * w g * y, by ring⟩
  · rintro ⟨x, s, y⟩ h0
    rw [hf] at h0
    have e1 : x = 0 := congrArg Prod.fst h0
    have e2 := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp (congrArg (fun p => p.2.1) h0))
    have e3 := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp (congrArg (fun p => p.2.2) h0))
    have e4 : c * c ∣ c * s := by simpa [sq] using e2.add e3
    obtain ⟨d, hd⟩ := hbc.trans ((mul_dvd_mul_iff_left hc).mp e4)
    rw [hq, e1, hd, mul_smul, hb, add_zero]
    refine Prod.ext rfl (Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr ?_))
    exact (hbc.trans (dvd_pow_self c two_ne_zero)).trans e3
  · rintro ⟨x, y⟩
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨(x, 0, y), by rw [hq, zero_smul, add_zero]⟩

end Ext

section Char
variable {l : ℕ} [Fact l.Prime]

theorem exists_char (a : ℕ) (ha : 1 ≤ a) : ∃ (κ : Multiplicative ℤ_[l] →* ℤ_[l]) (w : Multiplicative ℤ_[l] → ℤ_[l]),
    Continuous κ ∧ (∀ x, κ x = 1 + (l : ℤ_[l]) ^ a * w x) ∧ w (Multiplicative.ofAdd 1) = 1 := by
  have hr : Filter.Tendsto (fun x : ℕ => ((l : ℤ_[l]) ^ a) ^ x) Filter.atTop (nhds 0) := by
    apply tendsto_pow_atTop_nhds_zero_of_norm_lt_one
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) (by
      rw [PadicInt.norm_p]
      exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)) (by omega)
  let κ : AddChar ℤ_[l] ℤ_[l] := PadicInt.addChar_of_value_at_one _ hr
  have hκ : Continuous κ := PadicInt.continuous_addChar_of_value_at_one hr
  have h1 : κ 1 = 1 + (l : ℤ_[l]) ^ a := PadicInt.addChar_of_value_at_one_def hr
  have hd : ∀ x, (l : ℤ_[l]) ^ a ∣ κ x - 1 := by
    intro x
    refine PadicInt.denseRange_natCast.induction_on x ?_ fun m => ?_
    · simp_rw [← Ideal.mem_span_singleton, ← PadicInt.norm_le_pow_iff_mem_span_pow]
      exact isClosed_le (hκ.sub continuous_const).norm continuous_const
    · rw [← nsmul_one m, AddChar.map_nsmul_eq_pow, h1]
      simpa using sub_dvd_pow_sub_pow (1 + (l : ℤ_[l]) ^ a) 1 m
  choose w hw using hd
  have h0 : (l : ℤ_[l]) ^ a ≠ 0 := pow_ne_zero _ (by exact_mod_cast (Fact.out : l.Prime).ne_zero)
  refine ⟨κ.toMonoidHom, fun x => w x.toAdd, hκ, fun x => ?_, ?_⟩
  · rw [← hw, add_sub_cancel]; rfl
  · apply mul_left_cancel₀ h0
    change _ * w 1 = _
    rw [← hw, h1]; ring

theorem exists_mu {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (I : Subgroup G) (F : G)
    (ν : G →* Multiplicative ℤ_[l]) (hν : Continuous ν) (hI : ∀ σ ∈ I, ν σ = 1) (hF : ν F = Multiplicative.ofAdd 1)
    (hG : (Subgroup.closure (insert F (I : Set G))).topologicalClosure = ⊤) (a : ℕ) (ha : 1 ≤ a)
    {O LL : Type} [CommRing O] [Field LL] [Algebra O LL] [Algebra ℤ_[l] O] [TopologicalSpace LL]
    (hcont : Continuous fun x : ℤ_[l] => algebraMap O LL (algebraMap ℤ_[l] O x))
    {M : Type} [AddCommGroup M] [Module O M] (hM : ∀ m : M, ((l : ℕ) : O) ^ a • m = 0) (z : G → M)
    (hz : IsLocallyConstant z) (hm : ∀ g h, z (g * h) = z g + z h) (hzI : ∀ g ∈ I, z g = 0) :
    ∃ (μ : G →* Oˣ) (w : G → O), (Continuous fun g => algebraMap O LL (μ g)) ∧ (∀ σ ∈ I, μ σ = 1) ∧
      (∀ g, (μ g : O) = 1 + ((l : ℕ) : O) ^ a * w g) ∧ ∀ g, z g = w g • z F := by
  obtain ⟨κ, w, hκ, hw, hw1⟩ := exists_char (l := l) a ha
  have h0 : (l : ℤ_[l]) ^ a ≠ 0 := pow_ne_zero _ (by exact_mod_cast (Fact.out : l.Prime).ne_zero)
  have hcong : ∀ x y : ℤ_[l], (l : ℤ_[l]) ^ a ∣ x - y → algebraMap ℤ_[l] O x • z F = algebraMap ℤ_[l] O y • z F := by
    rintro x y ⟨d, hd⟩
    rw [← sub_eq_zero, ← sub_smul, ← map_sub, hd, map_mul, map_pow, map_natCast, mul_smul, hM]
  refine ⟨((algebraMap ℤ_[l] O : ℤ_[l] →* O).comp (κ.comp ν)).toHomUnits, fun g => algebraMap ℤ_[l] O (w (ν g)),
    hcont.comp (hκ.comp hν), fun σ hσ => Units.ext ?_, fun g => ?_, ?_⟩
  · change algebraMap ℤ_[l] O (κ (ν σ)) = 1
    rw [hI σ hσ, map_one, map_one]
  · change algebraMap ℤ_[l] O (κ (ν g)) = _
    rw [hw]; simp
  have hf : IsLocallyConstant fun g => algebraMap ℤ_[l] O (w (ν g)) • z F := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro g
    have h1 : ∀ᶠ h in nhds g, κ (ν h) ∈ Metric.ball (κ (ν g)) ((l : ℝ) ^ (-((a + a : ℕ) : ℤ))) :=
      (hκ.comp hν).continuousAt.eventually (Metric.ball_mem_nhds _
        (zpow_pos (by exact_mod_cast (Fact.out : l.Prime).pos) _))
    refine h1.mono fun h hh => hcong _ _ ?_
    have h2 := (mem_ball_iff_norm.mp hh).le
    rw [PadicInt.norm_le_pow_iff_mem_span_pow, Ideal.mem_span_singleton, hw, hw, pow_add, add_sub_add_left_eq_sub,
      ← mul_sub] at h2
    exact (mul_dvd_mul_iff_left h0).mp h2
  let z₁ : G →* Multiplicative M := MonoidHom.mk' (fun g => Multiplicative.ofAdd (z g)) fun g h => congrArg _ (hm g h)
  let z₂ : G →* Multiplicative M := MonoidHom.mk'
    (fun g => Multiplicative.ofAdd (algebraMap ℤ_[l] O (w (ν g)) • z F)) fun g h => by
      rw [← ofAdd_add, ← add_smul, ← map_add]
      refine congrArg _ (hcong _ _ ⟨w (ν g) * w (ν h), mul_left_cancel₀ h0 ?_⟩)
      have := map_mul κ (ν g) (ν h)
      rw [← map_mul, hw, hw, hw] at this
      linear_combination this
  have hle : (Subgroup.closure (insert F (I : Set G))).topologicalClosure ≤ z₁.eqLocus z₂ := by
    refine Subgroup.topologicalClosure_minimal _ ?_ ?_
    · rw [Subgroup.closure_le]
      rintro g (rfl | hg)
      · change Multiplicative.ofAdd (z g) = Multiplicative.ofAdd (algebraMap ℤ_[l] O (w (ν g)) • z g)
        rw [hF, hw1, map_one, one_smul]
      · have : z₂ g = z₂ 1 := by
          change Multiplicative.ofAdd (algebraMap ℤ_[l] O (w (ν g)) • z F) =
            Multiplicative.ofAdd (algebraMap ℤ_[l] O (w (ν 1)) • z F)
          rw [hI g hg, map_one]
        change z₁ g = z₂ g
        rw [this, map_one]
        exact hzI g hg
    · have := ((hz.prodMk hf).comp fun p => p.1 = p.2).isClosed_fiber True
      convert this using 1
      ext g
      simp only [Function.comp, eq_iff_iff, iff_true, Set.mem_ofPred_eq]
      rfl
  intro g
  rw [hG] at hle
  exact hle (Subgroup.mem_top g)

end Char

section Main
variable {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {n : ℕ} (emb : ZMod n → (K₀ →ₐ[Qp] LL))
    (Γ : GalData G Qp LL O) [Algebra ℤ_[l] O]

theorem unr_subset (hR : IsTopologicalRing LL) (hO : IsDomain O) (hD : IsDiscreteValuationRing O)
    (hFr : IsFractionRing O LL) (hch : CharZero O) (hu : ¬ IsUnit ((l : ℕ) : O))
    (hfin : ∀ m : ℕ, Finite (O ⧸ Ideal.span {((l : ℕ) : O) ^ m}))
    (hcont : Continuous fun x : ℤ_[l] => algebraMap O LL (algebraMap ℤ_[l] O x)) (I : Subgroup G)
    (hgen : ∃ (F : G) (ν : G →* Multiplicative ℤ_[l]), Continuous ν ∧ (∀ σ ∈ I, ν σ = 1) ∧
      ν F = Multiplicative.ofAdd 1 ∧ (Subgroup.closure (insert F (I : Set G))).topologicalClosure = ⊤)
    {r : ℕ} (D : TopData n r) (hl : Irreducible Γ.lam) (hG : IsTopGal PD emb D Γ)
    (hsum : ∀ (T T' T'' : LocLat G Qp LL O) (U U' : ZMod n → Multiset ℤ) (e : T''.V ≃ₗ[LL] (T.V × T'.V)),
      (∀ σ x, e (T''.ρ σ x) = (T.ρ σ (e x).1, T'.ρ σ (e x).2)) → CrysWith PD emb T.ρ U →
      CrysWith PD emb T'.ρ U' → CrysWith PD emb T''.ρ (fun i => U i + U' i))
    (htw : ∀ (T : LocLat G Qp LL O) (U : ZMod n → Multiset ℤ) (θ : G →* Oˣ) (a : ZMod n → ℤ),
      CrysWith PD emb T.ρ U → IsCrysChar PD emb θ a →
      CrysWith PD emb (twistRep T.ρ (chiLL LL θ)) (fun i => (U i).map (· + a i)) ∧
      IsCrysChar PD emb θ⁻¹ (fun i => -a i))
    (hε : IsCrysChar PD emb Γ.ε (fun _ => -1))
    (hun : ∀ μ : G →* Oˣ, (Continuous fun σ => algebraMap O LL (μ σ)) → (∀ σ ∈ I, μ σ = 1) →
      IsCrysChar PD emb μ (fun _ => 0))
    (hcl : GlobalTheory.AdmClasses.ClosedClass (fun (N : Type) [AddCommGroup N] [Module O N] (π : Representation O G N) =>
      Admissible PD emb Γ D.t D.Ut π))
    (X : Type) [AddCommGroup X] [Module O X] [Finite X] (hX : Admissible PD emb Γ D.t D.Ut (coefRep (Γ.Wchi 1) X)) :
    GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleCharUnramified.homModInertia Γ X I ⊆ adm PD emb Γ D.t D.Ut (Γ.Wchi 1) X := by
  rintro _ ⟨z, rfl, hz⟩
  obtain ⟨a, ha1, ha⟩ := GlobalTheory.AdmClasses.exists_pow_smul_eq_zero hl X
  have hp : Γ.lam ∣ ((l : ℕ) : O) := by
    rw [← Ideal.mem_span_singleton, ← hl.maximalIdeal_eq]
    exact hu
  have hpa := pow_dvd_pow_of_dvd hp a
  have h0 : ((l : ℕ) : O) ^ a ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero)
  have hM : ∀ m : O ⊗[O] X, ((l : ℕ) : O) ^ a • m = 0 := by
    intro m
    obtain ⟨d, hd⟩ := hpa
    rw [hd, mul_smul, smul_tensor_eq_zero ha]
  obtain ⟨F, ν, hν, hI, hF, hG'⟩ := hgen
  obtain ⟨μ, w, hμ, hμI, hw, hzw⟩ := exists_mu I F ν hν hI hF hG' a ha1 hcont hM _ z.2.1.1
    (GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleCharUnramified.cocycle_add Γ X z) hz
  have hf : Finite (O ⧸ Ideal.span {(((l : ℕ) : O) ^ a) ^ 2}) := by
    rw [← pow_mul]; exact hfin _
  have key : ∀ μ : G →* Oˣ, (Continuous fun g => algebraMap O LL (μ g)) → (∀ σ ∈ I, μ σ = 1) →
      (∀ g, Γ.lam ∣ (μ g : O) - 1) →
      Admissible PD emb Γ D.t D.Ut (scalRep (O ⧸ Ideal.span {(((l : ℕ) : O) ^ a) ^ 2}) (Γ.χ₁ * μ)) :=
    fun μ h1 h2 h3 => admissible_crystallineCharacterQuotient PD emb Γ D hl hG hsum htw hε μ (hun μ h1 h2) h3 (pow_ne_zero 2 h0)
  refine ⟨a, ha, ha1, z, rfl, ?_⟩
  refine ext_mem hcl _ (GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleCharUnramified.twCoef_chi_one Γ X) _ hpa h0 z _ μ w
    hw _ hzw ?_ (key 1 (continuous_const (y := algebraMap O LL 1)) (fun _ _ => rfl) fun g => ⟨0, by simp⟩) (key μ hμ hμI fun g => ?_)
  · rw [twist_twCoef]
    exact hX
  · rw [hw, add_sub_cancel_left]
    exact ((dvd_pow_self _ (by omega)).trans hpa).mul_right _

end Main

theorem continuous_padicInt {l : ℕ} [Fact l.Prime] (LL : FinExt l) :
    Continuous fun x : ℤ_[l] => algebraMap ↥(OL LL) ↥LL.1 (algebraMap ℤ_[l] ↥(OL LL) x) := by
  have h1 : Continuous fun x : ℤ_[l] => algebraMap ℚ_[l] (PadicAlgCl l) (x : ℚ_[l]) :=
    (continuous_algebraMap ℚ_[l] (PadicAlgCl l)).comp continuous_subtype_val
  exact continuous_induced_rng.mpr h1

theorem unramified_admissible : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (S : TopSit P),
    S.CrysCalc → S.Closed → S.StdAdm → S.Lem0 (S.Γ.Wchi 1) → S.UnrAdm := by
  intro l _ P S hX hC hA _ X _ _ _
  obtain ⟨⟨⟨hO, hD, hFr⟩, -, -, hR, -⟩, hfin⟩ := GlobalTheory.LocalIntegers.good_integers l S.LL
  exact unr_subset (P.PD S.K) S.emb S.Γ hR hO hD hFr inferInstance (GlobalTheory.AdmClasses.not_isUnit_integers l S.LL) hfin
    (continuous_padicInt S.LL) (IK S.K) (GlobalTheory.UnramGen.exists_gen_degree S.K) S.D S.hyp.1.2.2.2.2.2 S.hyp.2.1 hX.1 hX.2.1 hX.2.2.1
    hX.2.2.2 ⟨fun f hf => ((hC _ _ _ _).1 f hf).1, fun f hf => ((hC _ _ _ _).1 f hf).2, (hC _ _ _ _).2⟩ X
    (hA.2 1 le_rfl S.D.one_le_letterBlockLength X)

end GlobalTheory.UnramAdm
