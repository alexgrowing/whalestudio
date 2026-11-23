import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ResBound
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReductionSameSSOfLattices
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodCoefficientRingPadicIntegersFinExt

noncomputable section

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open Formalism.MainNotions.N (twistRep coefRep)
open Formalism.GaloisCohomology (scalRep)
open TensorProduct
open scoped LaurentSeries PowerSeries Pointwise

namespace GlobalTheory.TopSteps.StdAdm

section Alg

variable {O G : Type} [CommRing O] [Group G]
variable {M N P : Type} [AddCommGroup M] [Module O M] [AddCommGroup N] [Module O N] [AddCommGroup P] [Module O P]

def asModuleIso (π : Representation O G M) (π' : Representation O G N) (e : M ≃ₗ[O] N)
    (he : ∀ g x, e (π g x) = π' g (e x)) : π.asModule ≃ₗ[MonoidAlgebra O G] π'.asModule :=
  { (π.asModuleEquiv.trans (e.trans π'.asModuleEquiv.symm)).toAddEquiv with
    map_smul' := fun r x => by
      apply π'.asModuleEquiv.injective
      change e (π.asModuleEquiv (r • x)) = π'.asModuleEquiv (r • π'.asModuleEquiv.symm (e (π.asModuleEquiv x)))
      rw [Representation.asModuleEquiv_map_smul, Representation.asModuleEquiv_map_smul,
        LinearEquiv.apply_symm_apply]
      induction r using MonoidAlgebra.induction_on with
      | of g => simp [he]
      | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]
      | smul c a ha => simp only [map_smul, LinearMap.smul_apply, ha] }

theorem sameSS_of_equiv {π₀ : Representation O G P} {π : Representation O G M} {π' : Representation O G N}
    (h : SameSS π₀ π) (e : M ≃ₗ[O] N) (he : ∀ g x, e (π g x) = π' g (e x)) : SameSS π₀ π' := by
  have hf : IsFiniteLength (MonoidAlgebra O G) π.asModule := by
    obtain ⟨_, t, _, _, h3, h4, _⟩ := h
    exact isFiniteLength_iff_exists_compositionSeries.mpr ⟨t, h3, h4⟩
  exact SameFactors.trans h (SameFactors.of_equiv hf (asModuleIso π π' e he))

theorem exists_modRep_equiv (π : Representation O G M) (π' : Representation O G N) (c : O) (p : M →ₗ[O] N)
    (hp : Function.Surjective p) (hk : ∀ x, p x = 0 ↔ x ∈ c • (⊤ : Submodule O M))
    (hg : ∀ g x, p (π g x) = π' g (p x)) :
    ∃ e : QuotSMulTop c M ≃ₗ[O] N, ∀ g x, e (modRep π c g x) = π' g (e x) := by
  have hker : c • (⊤ : Submodule O M) = LinearMap.ker p := by
    ext x; rw [LinearMap.mem_ker, hk]
  refine ⟨(Submodule.quotEquivOfEq _ _ hker).trans (p.quotKerEquivOfSurjective hp), fun g x => ?_⟩
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact hg g x

theorem finite_tensor [Module.Finite O M] [Finite N] : Finite (M ⊗[O] N) := by
  classical
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' O M
  have h1 : Finite (N ⊗[O] (Fin n → O)) :=
    Finite.of_equiv _ (TensorProduct.piScalarRight O O N (Fin n)).symm.toEquiv
  have h2 : Finite (N ⊗[O] M) := Finite.of_surjective _ (LinearMap.lTensor_surjective N hf)
  exact Finite.of_equiv _ (TensorProduct.comm O N M).toEquiv

theorem lTensor_coefRep (W : Representation O G M) (f : N →ₗ[O] P) (g : G) (m : M ⊗[O] N) :
    f.lTensor M (coefRep W N g m) = coefRep W P g (f.lTensor M m) := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => simp [coefRep_tmul]
  | add a b ha hb => simp only [map_add, ha, hb]

end Alg

section Lat

variable {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL] [Algebra Qp LL]
  [CommRing O] [Algebra O LL] [TopologicalSpace LL]

theorem finite_lat (T : LocLat G Qp LL O) : Module.Finite O ↥T.L.T := Module.Finite.iff_fg.mpr T.L.fg

def prodSubEquiv {R A B : Type} [Ring R] [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    (p : Submodule R A) (q : Submodule R B) : ↥(p.prod q) ≃ₗ[R] (↥p × ↥q) where
  toFun x := (⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩)
  invFun y := ⟨(y.1.1, y.2.1), y.1.2, y.2.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

def prodLat (T T' : LocLat G Qp LL O) : LocLat G Qp LL O where
  V := T.V × T'.V
  ρ := T.ρ.prod T'.ρ
  cont := fun x => (T.cont x.1).prodMk (T'.cont x.2)
  L :=
    { T := T.L.T.prod T'.L.T
      stable := fun g x hx => ⟨T.L.stable g _ hx.1, T'.L.stable g _ hx.2⟩
      fg := T.L.fg.prod T'.L.fg
      free := by
        have := T.L.free
        have := T'.L.free
        exact Module.Free.of_equiv (prodSubEquiv T.L.T T'.L.T).symm
      span := by
        rw [eq_top_iff]
        rintro ⟨x, y⟩ -
        have hx : x ∈ Submodule.span LL (T.L.T : Set T.V) := by rw [T.L.span]; trivial
        have hy : y ∈ Submodule.span LL (T'.L.T : Set T'.V) := by rw [T'.L.span]; trivial
        have h1 := Submodule.mem_map_of_mem (f := LinearMap.inl LL T.V T'.V) hx
        have h2 := Submodule.mem_map_of_mem (f := LinearMap.inr LL T.V T'.V) hy
        rw [Submodule.map_span] at h1 h2
        have h3 : (x, y) = LinearMap.inl LL T.V T'.V x + LinearMap.inr LL T.V T'.V y := by simp
        rw [h3]
        refine Submodule.add_mem _ (Submodule.span_mono ?_ h1) (Submodule.span_mono ?_ h2)
        · rintro _ ⟨a, ha, rfl⟩; exact ⟨ha, Submodule.zero_mem _⟩
        · rintro _ ⟨a, ha, rfl⟩; exact ⟨Submodule.zero_mem _, ha⟩ }

def prodLatEquiv (T T' : LocLat G Qp LL O) : ↥(prodLat T T').L.T ≃ₗ[O] (↥T.L.T × ↥T'.L.T) :=
  prodSubEquiv T.L.T T'.L.T

theorem prodLatEquiv_act (T T' : LocLat G Qp LL O) (g : G) (x : ↥(prodLat T T').L.T) :
    prodLatEquiv T T' (latRep (prodLat T T').L g x) =
      (latRep T.L g (prodLatEquiv T T' x).1, latRep T'.L g (prodLatEquiv T T' x).2) := rfl

def kerLattice [IsDomain O] [IsPrincipalIdealRing O] [CharZero LL] (T : LocLat G Qp LL O) {M : Type}
    [AddCommGroup M] [Module O M] [Finite M] (π : Representation O G M) (p : ↥T.L.T →ₗ[O] M)
    (hg : ∀ g x, p (latRep T.L g x) = π g (p x)) : Lattice (O := O) T.ρ where
  T := (LinearMap.ker p).map T.L.T.subtype
  stable := by
    rintro g _ ⟨x, hx, rfl⟩
    refine ⟨latRep T.L g x, ?_, rfl⟩
    have hx' : p x = 0 := hx
    change p (latRep T.L g x) = 0
    rw [hg, hx', map_zero]
  fg := by
    have := finite_lat T
    exact (IsNoetherian.noetherian _).map _
  free := by
    have := finite_lat T
    have := T.L.free
    have : Module.Free O ↥(LinearMap.ker p) := Module.free_of_finite_type_torsion_free'
    exact Module.Free.of_equiv (Submodule.equivMapOfInjective _ T.L.T.injective_subtype _)
  span := by
    rw [eq_top_iff, ← T.L.span, Submodule.span_le]
    intro y hy
    have hn : ((Nat.card M : ℕ) : LL) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
    have h1 : (Nat.card M) • y ∈ (LinearMap.ker p).map T.L.T.subtype := by
      refine ⟨Nat.card M • ⟨y, hy⟩, ?_, rfl⟩
      change p _ = 0
      rw [map_nsmul, card_nsmul_eq_zero']
    have h2 := Submodule.smul_mem _ ((Nat.card M : ℕ) : LL)⁻¹ (Submodule.subset_span (R := LL) h1)
    rwa [← Nat.cast_smul_eq_nsmul LL, inv_smul_smul₀ hn] at h2

theorem twistRep_charRep (χ θ : G →* Oˣ) :
    twistRep (charRep (chiLL LL χ)) (chiLL LL θ) = charRep (chiLL LL (χ * θ)) := by
  ext g
  change algebraMap O LL (θ g) • (algebraMap O LL (χ g) • (1 : LL)) = algebraMap O LL (χ g * θ g) • (1 : LL)
  simp [mul_comm]

end Lat

theorem block_succ (w : ℤ) (k : ℕ) : block w (k + 1) = block w k + {w + k} := by
  have h : Finset.Ico w (w + ((k + 1 : ℕ) : ℤ)) = insert (w + k) (Finset.Ico w (w + k)) := by
    ext u; simp only [Finset.mem_Ico, Finset.mem_insert]; push_cast; omega
  rw [block, h, Finset.insert_val_of_notMem (by simp), block, ← Multiset.singleton_add]
  exact add_comm _ _

section Per

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {n : ℕ} {emb : ZMod n → (K₀ →ₐ[Qp] LL)}
    {Γ : GalData G Qp LL O}

def SumRule (PD : PeriodData G Qp K₀ K B BdR) (emb : ZMod n → (K₀ →ₐ[Qp] LL)) (O : Type) [CommRing O]
    [Algebra O LL] : Prop :=
  ∀ (T T' T'' : LocLat G Qp LL O) (U U' : ZMod n → Multiset ℤ) (e : T''.V ≃ₗ[LL] (T.V × T'.V)),
    (∀ σ x, e (T''.ρ σ x) = (T.ρ σ (e x).1, T'.ρ σ (e x).2)) → CrysWith PD emb T.ρ U →
    CrysWith PD emb T'.ρ U' → CrysWith PD emb T''.ρ (fun i => U i + U' i)

def TwistRule (PD : PeriodData G Qp K₀ K B BdR) (emb : ZMod n → (K₀ →ₐ[Qp] LL)) (O : Type) [CommRing O]
    [Algebra O LL] : Prop :=
  ∀ (T : LocLat G Qp LL O) (U : ZMod n → Multiset ℤ) (θ : G →* Oˣ) (a : ZMod n → ℤ),
    CrysWith PD emb T.ρ U → IsCrysChar PD emb θ a →
    CrysWith PD emb (twistRep T.ρ (chiLL LL θ)) (fun i => (U i).map (· + a i)) ∧
    IsCrysChar PD emb θ⁻¹ (fun i => -a i)

def QuotSum (PD : PeriodData G Qp K₀ K B BdR) (emb : ZMod n → (K₀ →ₐ[Qp] LL)) (Γ : GalData G Qp LL O) (t : ℕ)
    (Ut : ZMod n → Multiset ℤ) : Prop :=
  ∀ (M M' : Type) [AddCommGroup M] [Module O M] [AddCommGroup M'] [Module O M']
    (π : Representation O G M) (π' : Representation O G M'),
    (∀ f : M →ₗ[O] M', (∀ σ x, f (π σ x) = π' σ (f x)) →
      Function.Surjective f → Admissible PD emb Γ t Ut π → Admissible PD emb Γ t Ut π') ∧
    (Admissible PD emb Γ t Ut π → Admissible PD emb Γ t Ut π' → Admissible PD emb Γ t Ut (π.prod π'))

theorem isCrysChar_chi [IsTopologicalRing LL] (hinj : Function.Injective (algebraMap O LL))
    (htw : TwistRule PD emb O) {w : ZMod n → ℤ} (h1 : IsCrysChar PD emb Γ.χ₁ w)
    (hε : IsCrysChar PD emb Γ.ε (fun _ => -1)) (c : ℕ) :
    IsCrysChar PD emb (Γ.chi (c + 1)) (fun i => w i + c) := by
  induction c with
  | zero => simpa using h1
  | succ c ih =>
    have hinv := (htw (charLat Qp hinj Γ.χ₁ h1.1) _ Γ.ε _ h1.2 hε).2
    have h := (htw (charLat Qp hinj _ ih.1) _ Γ.ε⁻¹ _ ih.2 hinv).1
    rw [GalData.chi_succ]
    refine ⟨?_, ?_⟩
    · refine (ih.1.mul hinv.1).congr fun g => ?_
      simp only [Pi.mul_apply, MonoidHom.mul_apply, Units.val_mul, map_mul]
    · have h' : CrysWith PD emb (twistRep (charRep (chiLL LL (Γ.chi (c + 1)))) (chiLL LL Γ.ε⁻¹))
        (fun i => ({w i + c} : Multiset ℤ).map (· + -(-1))) := h
      rw [twistRep_charRep] at h'
      simpa [add_assoc] using h'

theorem exists_sum [IsTopologicalRing LL] (hinj : Function.Injective (algebraMap O LL))
    (hsum : SumRule PD emb O) {U : ZMod n → Multiset ℤ} {w : ZMod n → ℤ} (h0 : CrysWith PD emb Γ.T₀.ρ U)
    (hχ : ∀ c : ℕ, IsCrysChar PD emb (Γ.chi (c + 1)) (fun i => w i + c)) (k : ℕ) :
    ∃ (T : LocLat G Qp LL O) (e : ↥T.L.T ≃ₗ[O] (↥Γ.T₀.L.T × (Fin k → O))),
      CrysWith PD emb T.ρ (fun i => U i + block (w i) k) ∧
      ∀ g x, e (latRep T.L g x) = (Γ.W₀ g (e x).1, fun c : Fin k => Γ.Wchi (c.val + 1) g ((e x).2 c)) := by
  induction k with
  | zero =>
    refine ⟨Γ.T₀, (LinearEquiv.prodUnique).symm, ?_, fun g x => Prod.ext rfl (Subsingleton.elim _ _)⟩
    simpa [block] using h0
  | succ k ih =>
    obtain ⟨T, e, hT, he⟩ := ih
    obtain ⟨e₁, -, he₁⟩ := charLattice_equiv hinj (Γ.chi (k + 1))
    let C : LocLat G Qp LL O := charLat Qp hinj _ (hχ k).1
    let e₁' : O ≃ₗ[O] ↥C.L.T := e₁
    have he₁' : ∀ g y, e₁'.symm (latRep C.L g y) = Γ.Wchi (k + 1) g (e₁'.symm y) := by
      intro g y
      obtain ⟨a, rfl⟩ := e₁'.surjective y
      rw [LinearEquiv.symm_apply_eq, LinearEquiv.symm_apply_apply]
      exact (he₁ g a).symm
    let s : ((↥Γ.T₀.L.T × (Fin k → O)) × O) ≃ₗ[O] (↥Γ.T₀.L.T × (Fin (k + 1) → O)) :=
      { toFun := fun x => (x.1.1, Fin.snoc (α := fun _ => O) x.1.2 x.2)
        invFun := fun y => ((y.1, Fin.init y.2), y.2 (Fin.last k))
        map_add' := fun a b => Prod.ext rfl (by
          funext c; refine Fin.lastCases ?_ (fun c => ?_) c <;> simp)
        map_smul' := fun a b => Prod.ext rfl (by
          funext c; refine Fin.lastCases ?_ (fun c => ?_) c <;> simp)
        left_inv := fun x => by simp
        right_inv := fun y => by simp }
    refine ⟨prodLat T C, (prodLatEquiv T C).trans ((e.prodCongr e₁'.symm).trans s), ?_, fun g x => ?_⟩
    · have h := hsum T C (prodLat T C) _ _ (LinearEquiv.refl _ _) (fun _ _ => rfl) hT (hχ k).2
      simpa only [block_succ, add_assoc] using h
    · change s (e (latRep T.L g (prodLatEquiv T C x).1), e₁'.symm (latRep C.L g (prodLatEquiv T C x).2)) =
        (Γ.W₀ g (e (prodLatEquiv T C x).1).1, fun c : Fin (k + 1) => Γ.Wchi (c.val + 1) g
          (Fin.snoc (α := fun _ => O) (e (prodLatEquiv T C x).1).2 (e₁'.symm (prodLatEquiv T C x).2) c))
      rw [he, he₁']
      refine Prod.ext rfl ?_
      funext c
      change Fin.snoc (α := fun _ => O) _ _ c = _
      refine Fin.lastCases ?_ (fun c => ?_) c
      · simp only [Fin.snoc_last, Fin.val_last]
      · simp only [Fin.snoc_castSucc, Fin.val_castSucc]

theorem full_of_equiv [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O LL] (hlam : Irreducible Γ.lam)
    {t : ℕ} {Ut : ZMod n → Multiset ℤ} (T : LocLat G Qp LL O) (e : ↥T.L.T ≃ₗ[O] (↥Γ.T₀.L.T × (Fin t → O)))
    (hT : CrysWith PD emb T.ρ Ut)
    (he : ∀ g x, e (latRep T.L g x) = (Γ.W₀ g (e x).1, fun c : Fin t => Γ.Wchi (c.val + 1) g ((e x).2 c))) :
    Full PD emb Γ t Ut T := by
  refine ⟨hT, fun L => ?_⟩
  let p : ↥T.L.T →ₗ[O] (QuotSMulTop Γ.lam ↥Γ.T₀.L.T × (Fin t → QuotSMulTop Γ.lam O)) :=
    ((Submodule.mkQ _).prodMap ((Submodule.mkQ _).compLeft (Fin t))).comp e.toLinearMap
  have hp : ∀ x, p x = (Submodule.Quotient.mk (e x).1, fun c => Submodule.Quotient.mk ((e x).2 c)) :=
    fun _ => rfl
  refine (exists_modRep_equiv (latRep T.L) (Γ.refRep t) Γ.lam p ?_ ?_ ?_).elim fun f hf =>
    sameSS_of_equiv (reduction_sameSS_of_lattices T.ρ L T.L Γ.lam hlam) f hf
  · rintro ⟨a, b⟩
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ a
    choose b' hb' using fun c => Submodule.Quotient.mk_surjective _ (b c)
    refine ⟨e.symm (a, b'), ?_⟩
    rw [hp, LinearEquiv.apply_symm_apply]
    exact Prod.ext rfl (funext hb')
  · intro x
    rw [hp, Prod.ext_iff, funext_iff]
    simp only [Prod.fst_zero, Prod.snd_zero, Pi.zero_apply, Submodule.Quotient.mk_eq_zero,
      Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_top, true_and]
    constructor
    · rintro ⟨⟨a, ha⟩, hb⟩
      choose b hb using hb
      refine ⟨e.symm (a, b), e.injective ?_⟩
      rw [map_smul, LinearEquiv.apply_symm_apply]
      exact Prod.ext ha (funext hb)
    · rintro ⟨y, rfl⟩
      rw [map_smul]
      exact ⟨⟨_, rfl⟩, fun c => ⟨_, rfl⟩⟩
  · intro g x
    rw [hp, hp, he]
    rfl

theorem admissible_of_surjective [IsDomain O] [IsPrincipalIdealRing O] [CharZero LL] {t : ℕ}
    {Ut : ZMod n → Multiset ℤ} {T : LocLat G Qp LL O} (hT : Full PD emb Γ t Ut T) {M : Type}
    [AddCommGroup M] [Module O M] [Finite M] (π : Representation O G M) (p : ↥T.L.T →ₗ[O] M)
    (hp : Function.Surjective p) (hg : ∀ g x, p (latRep T.L g x) = π g (p x)) : Admissible PD emb Γ t Ut π := by
  refine ⟨‹_›, 1, T, hT.sumFull, kerLattice T π p hg, p, ?_, hp, hg, fun x => ⟨fun h => ⟨x, h, rfl⟩, ?_⟩⟩
  · rintro _ ⟨x, -, rfl⟩
    exact x.2
  · rintro ⟨y, hy, hxy⟩
    obtain rfl : y = x := Subtype.ext hxy
    exact hy

theorem admissible_coefRep [IsDomain O] [IsPrincipalIdealRing O] [CharZero LL] {t : ℕ}
    {Ut : ZMod n → Multiset ℤ} (hc : QuotSum PD emb Γ t Ut) {T : LocLat G Qp LL O} (hT : Full PD emb Γ t Ut T)
    {M : Type} [AddCommGroup M] [Module O M] (W : Representation O G M) (q : ↥T.L.T →ₗ[O] M)
    (hq : Function.Surjective q) (hg : ∀ g x, q (latRep T.L g x) = W g (q x))
    (X : Type) [AddCommGroup X] [Module O X] [Finite X] : Admissible PD emb Γ t Ut (coefRep W X) := by
  have := finite_lat T
  have : Module.Finite O M := Module.Finite.of_surjective q hq
  have key : ∀ (N : Submodule O X), N.FG → Admissible PD emb Γ t Ut (coefRep W ↥N) := by
    intro N hN
    induction N, hN using Submodule.fg_induction with
    | singleton x =>
      have : Finite (M ⊗[O] ↥(O ∙ x)) := finite_tensor
      let x' : ↥(O ∙ x) := ⟨x, Submodule.mem_span_singleton_self x⟩
      refine admissible_of_surjective hT _ (((TensorProduct.mk O M ↥(O ∙ x)).flip x').comp q) ?_ ?_
      · intro y
        induction y using TensorProduct.induction_on with
        | zero => exact ⟨0, map_zero _⟩
        | add a b ha hb =>
          obtain ⟨a, rfl⟩ := ha
          obtain ⟨b, rfl⟩ := hb
          exact ⟨a + b, map_add _ _ _⟩
        | tmul m y =>
          obtain ⟨m, rfl⟩ := hq m
          obtain ⟨y, hy⟩ := y
          obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
          refine ⟨a • m, ?_⟩
          change q (a • m) ⊗ₜ[O] x' = q m ⊗ₜ[O] (a • x')
          rw [map_smul, smul_tmul]
      · intro g y
        change q (latRep T.L g y) ⊗ₜ[O] x' = coefRep W _ g (q y ⊗ₜ[O] x')
        rw [hg, coefRep_tmul]
    | sup N₁ N₂ _ _ h₁ h₂ =>
      refine (hc _ _ _ _).1 (((Submodule.inclusion (le_sup_left : N₁ ≤ N₁ ⊔ N₂)).lTensor M).coprod
        ((Submodule.inclusion (le_sup_right : N₂ ≤ N₁ ⊔ N₂)).lTensor M)) ?_ ?_ ((hc _ _ _ _).2 h₁ h₂)
      · rintro g ⟨a, b⟩
        change LinearMap.lTensor M _ (coefRep W _ g a) + LinearMap.lTensor M _ (coefRep W _ g b) =
          coefRep W _ g (LinearMap.lTensor M _ a + LinearMap.lTensor M _ b)
        rw [lTensor_coefRep, lTensor_coefRep, map_add]
      · intro y
        induction y using TensorProduct.induction_on with
        | zero => exact ⟨0, map_zero _⟩
        | add a b ha hb =>
          obtain ⟨a, rfl⟩ := ha
          obtain ⟨b, rfl⟩ := hb
          exact ⟨a + b, map_add _ _ _⟩
        | tmul m y =>
          obtain ⟨y, hy⟩ := y
          obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hy
          refine ⟨(m ⊗ₜ[O] ⟨a, ha⟩, m ⊗ₜ[O] ⟨b, hb⟩), ?_⟩
          rw [LinearMap.coprod_apply, LinearMap.lTensor_tmul, LinearMap.lTensor_tmul, ← tmul_add]
          rfl
  have hfin : Module.Finite O X := Module.Finite.of_finite
  exact (hc _ _ _ _).1 ((⊤ : Submodule O X).subtype.lTensor M) (lTensor_coefRep W _)
    (LinearMap.lTensor_surjective M fun x => ⟨⟨x, trivial⟩, rfl⟩) (key ⊤ Module.Finite.fg_top)

theorem admissible_std [IsTopologicalRing LL] [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O LL]
    [CharZero LL] (hlam : Irreducible Γ.lam) {r : ℕ} {D : TopData n r} (hD : IsTopGal PD emb D Γ)
    (hsum : SumRule PD emb O) (htw : TwistRule PD emb O) (hε : IsCrysChar PD emb Γ.ε (fun _ => -1))
    (hc : QuotSum PD emb Γ D.t D.Ut) :
    (∀ (X : Type) [AddCommGroup X] [Module O X] [Finite X], Admissible PD emb Γ D.t D.Ut (coefRep Γ.W₀ X)) ∧
    ∀ c : ℕ, 1 ≤ c → c ≤ D.t → ∀ (X : Type) [AddCommGroup X] [Module O X] [Finite X],
      Admissible PD emb Γ D.t D.Ut (coefRep (Γ.Wchi c) X) := by
  have hinj := IsFractionRing.injective O LL
  obtain ⟨T, e, hT, he⟩ := exists_sum hinj hsum hD.2.1 (isCrysChar_chi hinj htw hD.2.2.1 hε) D.t
  have hF : Full PD emb Γ D.t D.Ut T := full_of_equiv hlam T e hT he
  refine ⟨fun X _ _ _ => admissible_coefRep hc hF _ ((LinearMap.fst O _ _).comp e.toLinearMap) ?_ ?_ X,
    fun c h1 h2 X _ _ _ => ?_⟩
  · exact Prod.fst_surjective.comp e.surjective
  · intro g x
    exact congrArg Prod.fst (he g x)
  · obtain ⟨c, rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
    refine admissible_coefRep hc hF _ ((LinearMap.proj (⟨c, h2⟩ : Fin D.t)).comp
      ((LinearMap.snd O _ _).comp e.toLinearMap)) ?_ ?_ X
    · intro a
      exact ⟨e.symm (0, fun _ => a), by simp⟩
    · intro g x
      exact congrFun (congrArg Prod.snd (he g x)) ⟨c, h2⟩

end Per

theorem stdAdm : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (S : TopSit P), S.CrysCalc → S.Closed → S.StdAdm := by
  intro l _ P S hcr hcl
  obtain ⟨⟨_, h1, h2⟩, -, -, h3, -⟩ := GlobalTheory.LocalIntegers.goodO_integers l S.LL
  exact admissible_std S.hyp.1.2.2.2.2.2 S.hyp.2.1 hcr.1 hcr.2.1 hcr.2.2.1
    (fun M M' _ _ _ _ π π' => ⟨fun f hf => ((hcl M M' π π').1 f hf).2, (hcl M M' π π').2⟩)

end GlobalTheory.TopSteps.StdAdm
