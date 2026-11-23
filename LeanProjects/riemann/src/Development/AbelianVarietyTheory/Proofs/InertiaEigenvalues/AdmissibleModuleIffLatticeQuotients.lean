import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.JSmul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleStd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SameSSModRepLatRepIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrystallineIffMemH1f

noncomputable section

open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Polynomial
open Formalism.GaloisCohomology (scalRep)
open Formalism.MainNotions.N (GRep)
open scoped Pointwise

namespace GlobalTheory.FullCharpoly

section Ref
variable {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL]
    [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] (Γ : GalData G Qp LL O) (t : ℕ)

def refInt : Representation O G (↥Γ.T₀.L.T × (Fin t → O)) :=
  Γ.W₀.prod (piRep fun c : Fin t => Γ.Wchi (c.val + 1))

theorem exists_refInt_equiv :
    ∃ e : QuotSMulTop Γ.lam (↥Γ.T₀.L.T × (Fin t → O)) ≃ₗ[O]
      (QuotSMulTop Γ.lam ↥Γ.T₀.L.T × (Fin t → QuotSMulTop Γ.lam O)),
      ∀ g x, e (modRep (refInt Γ t) Γ.lam g x) = Γ.refRep t g (e x) := by
  let p : (↥Γ.T₀.L.T × (Fin t → O)) →ₗ[O] (QuotSMulTop Γ.lam ↥Γ.T₀.L.T × (Fin t → QuotSMulTop Γ.lam O)) :=
    (Submodule.mkQ _).prodMap ((Submodule.mkQ _).compLeft (Fin t))
  have hp : ∀ x, p x = (Submodule.Quotient.mk x.1, fun c => Submodule.Quotient.mk (x.2 c)) :=
    fun _ => rfl
  refine StdAdm.exists_modRep_equiv _ _ _ p ?_ ?_ (fun _ _ => rfl)
  · rintro ⟨a, b⟩
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ a
    choose b' hb' using fun c => Submodule.Quotient.mk_surjective _ (b c)
    exact ⟨(a, b'), Prod.ext rfl (funext hb')⟩
  · intro x
    rw [hp, Prod.ext_iff, funext_iff]
    simp only [Prod.fst_zero, Prod.snd_zero, Pi.zero_apply, Submodule.Quotient.mk_eq_zero,
      Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_top, true_and]
    constructor
    · rintro ⟨⟨a, ha⟩, hb⟩
      choose b hb using hb
      exact ⟨(a, b), Prod.ext ha (funext hb)⟩
    · rintro ⟨y, rfl⟩
      exact ⟨⟨_, rfl⟩, fun c => ⟨_, rfl⟩⟩

theorem charpoly_refInt [Nontrivial O] [Module.Free O ↥Γ.T₀.L.T] [Module.Finite O ↥Γ.T₀.L.T] (g : G) :
    LinearMap.charpoly (refInt Γ t g) =
      LinearMap.charpoly (Γ.W₀ g) * ∏ c : Fin t, (X - C (Γ.chi (c.val + 1) g : O)) := by
  have h : refInt Γ t g = (Γ.W₀ g).prodMap
      (Matrix.toLin' (Matrix.diagonal fun c : Fin t => (Γ.chi (c.val + 1) g : O))) := by
    refine LinearMap.ext fun x => Prod.ext rfl (funext fun c => ?_)
    change (Γ.chi (c.val + 1) g : O) • x.2 c = Matrix.mulVec _ x.2 c
    rw [Matrix.mulVec_diagonal, smul_eq_mul]
  rw [h, LinearMap.charpoly_prodMap, Matrix.charpoly_toLin', Matrix.charpoly_diagonal]

theorem sameSS_refRep_iff [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O LL]
    (hlam : Irreducible Γ.lam) {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
    [FiniteDimensional LL V] {ρ : Representation LL G V} (L : Lattice (O := O) ρ) :
    SameSS (modRep (latRep L) Γ.lam) (Γ.refRep t) ↔ ∀ g j, ∃ y : O,
      (LinearMap.charpoly (ρ g) - LinearMap.charpoly (Γ.T₀.ρ g) *
        ∏ c : Fin t, (X - C (algebraMap O LL (Γ.chi (c.val + 1) g)))).coeff j = algebraMap O LL (Γ.lam * y) := by
  have := L.free
  have := Γ.T₀.L.free
  have : Module.Finite O L.T := Module.Finite.iff_fg.2 L.fg
  have : Module.Finite O Γ.T₀.L.T := Module.Finite.iff_fg.2 Γ.T₀.L.fg
  obtain ⟨e, he⟩ := exists_refInt_equiv Γ t
  have h1 : SameSS (modRep (latRep L) Γ.lam) (Γ.refRep t) ↔
      SameSS (modRep (latRep L) Γ.lam) (modRep (refInt Γ t) Γ.lam) :=
    ⟨fun h => StdAdm.sameSS_of_equiv h e.symm fun g x => by
      rw [LinearEquiv.symm_apply_eq, he, LinearEquiv.apply_symm_apply],
     fun h => StdAdm.sameSS_of_equiv h e he⟩
  rw [h1, GlobalTheory.RedCharpoly.sameSS_modRep_iff _ _ _ (PrincipalIdealRing.isMaximal_of_irreducible hlam)]
  refine forall_congr' fun g => forall_congr' fun j => exists_congr fun y => ?_
  have h2 : ∏ c : Fin t, (X - C (algebraMap O LL (Γ.chi (c.val + 1) g))) =
      (∏ c : Fin t, (X - C (Γ.chi (c.val + 1) g : O))).map (algebraMap O LL) := by
    simp [Polynomial.map_prod]
  rw [GlobalTheory.RedCharpoly.charpoly_lattice L, GlobalTheory.RedCharpoly.charpoly_lattice Γ.T₀.L, h2, ← Polynomial.map_mul,
    ← Polynomial.map_sub, Polynomial.coeff_map, charpoly_refInt]
  exact (IsFractionRing.injective O LL).eq_iff.symm

end Ref

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} (S : TopSit P)

theorem full_iff (T : LocLat S.G ℚ_[l] ↥S.LL.1 S.O) :
    Full (P.PD S.K) S.emb S.Γ S.D.t S.D.Ut T ↔ CrysWith (P.PD S.K) S.emb T.ρ S.D.Ut ∧ ∀ g j, ∃ y : S.O,
      (LinearMap.charpoly (T.ρ g) - LinearMap.charpoly (S.Γ.T₀.ρ g) *
        ∏ c : Fin S.D.t, (X - C (algebraMap S.O ↥S.LL.1 (S.Γ.chi (c.val + 1) g)))).coeff j =
          algebraMap S.O ↥S.LL.1 (S.Γ.lam * y) := by
  obtain ⟨⟨_, h1, h2⟩, -, -, h3, -⟩ := GlobalTheory.LocalIntegers.goodO_integers l S.LL
  have hlam : Irreducible S.Γ.lam := S.hyp.1.2.2.2.2.2
  exact and_congr_right fun _ => ⟨fun h => (sameSS_refRep_iff S.Γ S.D.t hlam T.L).1 (h T.L),
    fun h L => (sameSS_refRep_iff S.Γ S.D.t hlam L).2 h⟩

theorem hasFiniteQuotients_padicInt : Ring.HasFiniteQuotients ℤ_[l] where
  finiteQuotient {I} hI := by
    obtain ⟨n, rfl⟩ := PadicInt.ideal_eq_span_pow_p hI
    rw [← PadicInt.ker_toZModPow]
    exact Finite.of_injective _ (RingHom.kerLift_injective (PadicInt.toZModPow n))

theorem hasFiniteQuotients_OL (LL : FinExt l) : Ring.HasFiniteQuotients ↥(OL LL) := by
  have := hasFiniteQuotients_padicInt (l := l)
  have : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  have : Module.Finite ℤ_[l] ↥(OL LL) := IsIntegralClosure.finite ℤ_[l] ℚ_[l] ↥LL.1 (integralClosure ℤ_[l] ↥LL.1)
  exact Ring.HasFiniteQuotients.of_module_finite ℤ_[l] _

theorem finite_of_lattices {G LL O V M : Type} [Group G] [Field LL] [CommRing O] [IsDomain O] [Algebra O LL]
    [IsFractionRing O LL] [Ring.HasFiniteQuotients O] [AddCommGroup V] [Module LL V] [Module O V]
    [IsScalarTower O LL V] [AddCommGroup M] [Module O M] {ρ : Representation LL G V}
    (L₁ L₂ : Lattice (O := O) ρ) (p : ↥L₁.T →ₗ[O] M) (hp : Function.Surjective p)
    (hk : ∀ x : ↥L₁.T, (x : V) ∈ L₂.T → p x = 0) : Finite M := by
  have : Module.Finite O L₁.T := Module.Finite.iff_fg.2 L₁.fg
  have : Module.Finite O M := Module.Finite.of_surjective p hp
  have h1 : ∀ x : V, ∃ a : nonZeroDivisors O, (a : O) • x ∈ L₂.T := by
    intro x
    have hx : x ∈ Submodule.span LL (L₂.T : Set V) := by rw [L₂.span]; trivial
    induction hx using Submodule.span_induction with
    | mem x hx => exact ⟨1, by simpa using hx⟩
    | zero => exact ⟨1, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      refine ⟨a * b, ?_⟩
      rw [smul_add, Submonoid.coe_mul]
      refine L₂.T.add_mem ?_ ?_
      · rw [mul_comm, mul_smul]; exact L₂.T.smul_mem _ ha
      · rw [mul_smul]; exact L₂.T.smul_mem _ hb
    | smul c x _ hx =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨⟨y, b⟩, hb⟩ := IsLocalization.surj (nonZeroDivisors O) c
      refine ⟨a * b, ?_⟩
      have : ((a * b : nonZeroDivisors O) : O) • c • x = y • ((a : O) • x) := by
        rw [Submonoid.coe_mul, mul_smul, smul_comm y, ← algebraMap_smul LL (b : O), smul_smul, mul_comm, hb,
          algebraMap_smul]
      rw [this]
      exact L₂.T.smul_mem _ ha
  have ht : Module.IsTorsion O M := by
    intro m
    obtain ⟨x, rfl⟩ := hp m
    obtain ⟨a, ha⟩ := h1 x
    exact ⟨a, by rw [Submonoid.smul_def, ← map_smul]; exact hk _ ha⟩
  obtain ⟨r, hr, hr0⟩ := Submodule.annihilator_top_inter_nonZeroDivisors ht
  have : Finite (O ⧸ Ideal.span {r}) := Ring.HasFiniteQuotients.finiteQuotient
    (by rw [Ne, Ideal.span_singleton_eq_bot]; exact nonZeroDivisors.ne_zero hr0)
  have hb : Ideal.span {r} • (⊤ : Submodule O M) = ⊥ :=
    Submodule.le_annihilator_iff.1 ((Ideal.span_singleton_le_iff_mem _).2 hr)
  have : Finite (M ⧸ Ideal.span {r} • (⊤ : Submodule O M)) :=
    Submodule.finite_quotient_smul _ Module.Finite.fg_top
  exact Finite.of_equiv _ (Submodule.quotEquivOfEqBot _ hb).toEquiv

attribute [local instance 10000] GRep.modO LocLat.modO GRep.towO LocLat.towO Submodule.module

theorem nonempty_lattice (A : GRep S.G ℚ_[l] ↥S.LL.1 S.O) : Nonempty (Lattice (O := S.O) A.ρ) := by
  obtain ⟨⟨_, h1, h2⟩, -, -, h3, h4⟩ := GlobalTheory.LocalIntegers.goodO_integers l S.LL
  have := GlobalTheory.BlochKatoIntegralScalars.compactSpace_GK S.K
  exact GlobalTheory.CrysExt.exists_lattice h4 A.ρ A.cont

def PolyFull (jT : ZMod S.n → ℤ → ℤ) (A : GRep S.G ℚ_[l] ↥S.LL.1 S.O) : Prop :=
  IsCrys (P.PD S.K) A.ρ ∧
    (∀ i (τ : ↥S.K.1 →ₐ[ℚ_[l]] ↥S.LL.1), (∀ x : ↥(K0 S.K), τ (algebraMap _ _ x) = S.emb i x) →
      ∀ a : ℤ, multV (P.PD S.K) A.ρ τ a = jT i a) ∧
    ∀ g j, ∃ y : S.O, (LinearMap.charpoly (A.ρ g) - LinearMap.charpoly (S.Γ.T₀.ρ g) *
      ∏ c : Fin S.D.t, (X - C (algebraMap S.O ↥S.LL.1 (S.Γ.chi (c.val + 1) g)))).coeff j =
        algebraMap S.O ↥S.LL.1 (S.Γ.lam * y)

def toLoc (A : GRep S.G ℚ_[l] ↥S.LL.1 S.O) (L : Lattice (O := S.O) A.ρ) : LocLat S.G ℚ_[l] ↥S.LL.1 S.O where
  V := A.V
  ρ := A.ρ
  cont := A.cont
  L := L

def ofLoc (T : LocLat S.G ℚ_[l] ↥S.LL.1 S.O) : GRep S.G ℚ_[l] ↥S.LL.1 S.O where
  V := T.V
  ρ := T.ρ
  cont := T.cont

theorem full_iff_polyFull {jT : ZMod S.n → ℤ → ℤ} (hj : ∀ i a, ((S.D.Ut i).count a : ℤ) = jT i a)
    (T : LocLat S.G ℚ_[l] ↥S.LL.1 S.O) :
    Full (P.PD S.K) S.emb S.Γ S.D.t S.D.Ut T ↔ PolyFull S jT (ofLoc S T) := by
  rw [full_iff, CrysWith, and_assoc]
  simp only [HasJumps, hj]
  rfl

set_option synthInstance.maxHeartbeats 200000 in

theorem admissibleModule_iff_lattice_quotients {jT : ZMod S.n → ℤ → ℤ} (hj : ∀ i a, ((S.D.Ut i).count a : ℤ) = jT i a)
    {M : Type} [AddCommGroup M] [Module S.O M] (π : Representation S.O S.G M) :
    S.admitted π ↔ ∃ (μ : ℕ) (F : Fin μ → GRep S.G ℚ_[l] ↥S.LL.1 S.O) (A : GRep S.G ℚ_[l] ↥S.LL.1 S.O)
      (e : A.V ≃ₗ[↥S.LL.1] (∀ j, (F j).V)) (L₁ L₂ : Lattice (O := S.O) A.ρ) (p : ↥L₁.T →ₗ[S.O] M),
      (∀ j, PolyFull S jT (F j)) ∧ (∀ g x j, e (A.ρ g x) j = (F j).ρ g (e x j)) ∧ L₂.T ≤ L₁.T ∧
      Function.Surjective p ∧ (∀ g x, p (latRep L₁ g x) = π g (p x)) ∧ ∀ x, p x = 0 ↔ (x : A.V) ∈ L₂.T := by
  constructor
  · rintro ⟨-, μ, T, ⟨F, hF, e, he⟩, L₂, p, h1, h2, h3, h4⟩
    exact ⟨μ, fun j => ofLoc S (F j), ofLoc S T, e, T.L, L₂, p,
      fun j => (full_iff_polyFull S hj _).1 (hF j), he, h1, h2, h3, h4⟩
  · rintro ⟨μ, F, A, e, L₁, L₂, p, hF, he, h1, h2, h3, h4⟩
    obtain ⟨⟨_, -, h6⟩, -⟩ := GlobalTheory.LocalIntegers.goodO_integers l S.LL
    have := hasFiniteQuotients_OL S.LL
    exact ⟨finite_of_lattices L₁ L₂ p h2 fun x => (h4 x).2, μ, toLoc S A L₁,
      ⟨fun j => toLoc S (F j) (nonempty_lattice S (F j)).some,
        fun j => (full_iff_polyFull S hj _).2 (hF j), e, he⟩, L₂, p, h1, h2, h3, h4⟩

end GlobalTheory.FullCharpoly
