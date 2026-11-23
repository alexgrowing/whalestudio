import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemRangeRealRdIff

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum
  IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries
open Formalism.IndefR.Links
open Formalism.L2.Host (embLL0)
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.SeriesTie

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem nonempty_algHom_of_isIntegral (R S κ : Type) [CommRing R] [CommRing S] [IsDomain S] [Algebra R S] [Algebra.IsIntegral R S]
    [FaithfulSMul R S] [Field κ] [IsAlgClosed κ] [Algebra R κ] : Nonempty (S →ₐ[R] κ) := by
  let p : Ideal R := RingHom.ker (algebraMap R κ)
  haveI : p.IsPrime := RingHom.ker_isPrime _
  obtain ⟨P, hP, hPp⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain (S := S) p (by
    rw [(RingHom.injective_iff_ker_eq_bot _).1 (FaithfulSMul.algebraMap_injective R S)]; exact bot_le)
  haveI : P.LiesOver p := ⟨hPp.symm⟩
  letI : Algebra (R ⧸ p) κ := (RingHom.kerLift (algebraMap R κ)).toAlgebra
  haveI : FaithfulSMul (R ⧸ p) κ := (faithfulSMul_iff_algebraMap_injective _ _).2 (RingHom.kerLift_injective _)
  haveI : IsScalarTower R (R ⧸ p) κ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Algebra.IsIntegral (R ⧸ p) (S ⧸ P) := inferInstance
  let f : (S ⧸ P) →ₐ[R ⧸ p] κ := IsAlgClosed.lift
  exact ⟨(f.restrictScalars R).comp (Ideal.Quotient.mkₐ R P)⟩

theorem nonempty_algHom_of_unramified (l : ℕ) (O K k L : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [IsIntegrallyClosed O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [IsAlgClosed (IsLocalRing.ResidueField O)] [Field K] [Algebra O K]
    [IsFractionRing O K] [Field k] [NumberField k] [Field L] [NumberField L] [Algebra k L] [Algebra k K]
    (hl : (l : O) ∈ IsLocalRing.maximalIdeal O)
    (hu : ∀ (P : Ideal (𝓞 L)) [P.IsPrime], (l : 𝓞 L) ∈ P → Algebra.IsUnramifiedAt (𝓞 k) P) : Nonempty (L →ₐ[k] K) := by
  have hint : ∀ a : 𝓞 k, ∃ y : O, algebraMap O K y = algebraMap k K a := fun a =>
    IsIntegrallyClosed.isIntegral_iff.1
      (a.isIntegral_coe.map_of_comp_eq (Int.castRingHom _) (algebraMap k K) (RingHom.ext_int _ _))
  choose y hy using hint
  have inj := IsFractionRing.injective O K
  let ι : 𝓞 k →+* O :=
    { toFun := y
      map_one' := inj (by simp [hy])
      map_mul' := fun a b => inj (by simp [hy])
      map_zero' := inj (by simp [hy])
      map_add' := fun a b => inj (by simp [hy]) }
  letI : Algebra (𝓞 k) O := ι.toAlgebra
  obtain ⟨f⟩ := nonempty_algHom_of_isIntegral (𝓞 k) (𝓞 L) (IsLocalRing.ResidueField O)
  let P : Ideal (𝓞 L) := RingHom.ker f
  haveI : P.IsPrime := RingHom.ker_isPrime _
  haveI := hu P (by
    rw [RingHom.mem_ker, map_natCast, ← map_natCast (IsLocalRing.residue O)]
    exact (IsLocalRing.residue_eq_zero_iff _).2 hl)
  haveI : Algebra.FinitePresentation (𝓞 k) (𝓞 L) := Algebra.FinitePresentation.of_finiteType.1 inferInstance
  haveI : Algebra.IsEtaleAt (𝓞 k) P := Algebra.IsEtaleAt.of_isUnramifiedAt_of_flat _
  have hun : ∀ z : P.primeCompl, IsUnit (f z) := fun z => IsUnit.mk0 _ z.2
  let F : Localization.AtPrime P →ₐ[𝓞 k] O ⧸ IsLocalRing.maximalIdeal O := IsLocalization.liftAlgHom (f := f) hun
  obtain ⟨G, -⟩ := Algebra.FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete F
  let g : 𝓞 L →+* K := (algebraMap O K).comp (G.toRingHom.comp (algebraMap _ _))
  have hg : ∀ a : 𝓞 k, g (algebraMap _ _ a) = algebraMap k K a := fun a => by
    change algebraMap O K (G (algebraMap _ _ (algebraMap _ _ a))) = _
    rw [← IsScalarTower.algebraMap_apply, G.commutes]
    exact hy a
  have ginj : Function.Injective g := by
    rw [RingHom.injective_iff_ker_eq_bot]
    refine Ideal.eq_bot_of_comap_eq_bot (R := 𝓞 k) (eq_bot_iff.2 fun a ha => ?_)
    have h1 : algebraMap k K a = 0 := (hg a).symm.trans ha
    exact RingOfIntegers.coe_eq_zero_iff.1 ((map_eq_zero _).1 h1)
  refine ⟨{ IsFractionRing.lift (K := L) ginj with commutes' := fun a => ?_ }⟩
  have : (IsFractionRing.lift (K := L) ginj).comp (algebraMap k L) = algebraMap k K :=
    IsFractionRing.ringHom_ext (A := 𝓞 k) fun a => by
      rw [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 k) (𝓞 L) L,
        IsFractionRing.lift_algebraMap, hg]
  exact RingHom.congr_fun this a

theorem mem_range_of_unramified (l : ℕ) (O K k L : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [IsIntegrallyClosed O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [IsAlgClosed (IsLocalRing.ResidueField O)] [Field K] [Algebra O K]
    [IsFractionRing O K] [Field k] [NumberField k] [Field L] [NumberField L] [Algebra k L] [Normal k L] (ι : k →+* K)
    (hl : (l : O) ∈ IsLocalRing.maximalIdeal O)
    (hu : ∀ (P : Ideal (𝓞 L)) [P.IsPrime], (l : 𝓞 L) ∈ P → Algebra.IsUnramifiedAt (𝓞 k) P) (e : K →+* ℂ) (σ : L →+* ℂ)
    (h : ∀ a, σ (algebraMap k L a) = e (ι a)) (x : L) : ∃ y, e y = σ x := by
  letI : Algebra k K := ι.toAlgebra
  obtain ⟨φ⟩ := nonempty_algHom_of_unramified l O K k L hl hu
  letI : Algebra k ℂ := (e.comp ι).toAlgebra
  letI : Algebra L ℂ := σ.toAlgebra
  haveI : IsScalarTower k L ℂ := IsScalarTower.of_algebraMap_eq fun a => (h a).symm
  let ψ : L →ₐ[k] ℂ := { e.comp φ.toRingHom with commutes' := fun a => congrArg e (φ.commutes a) }
  let τ : L ≃ₐ[k] L := ψ.restrictNormal' L
  refine ⟨φ (τ.symm x), ?_⟩
  have := ψ.restrictNormal_commutes L (τ.symm x)
  have h2 : ψ.restrictNormal L (τ.symm x) = x := τ.apply_symm_apply x
  rw [h2] at this
  exact this.symm

section Export

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  {Rl : RealDat3 D A3 Ks} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S)
  (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec)
  {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)

variable {YS v₀ i j b} in

theorem mem_range_realRd_of_sum {ν : ℂ} (hν : ν ≠ 0) {g : GA D (Wc D j) → ℂ} {n : ℕ} (z : Fin n → ℂ)
    (hz : ∀ k, ∃ y, ρ.e i b y = z k) (x : Fin n → NX.FmK S ((j : ℕ) + 1))
    (h : ν • g = ∑ k, z k • evW YS v₀ j (Subtype.val (x k))) : g ∈ Set.range (realRd YS v₀ hρ i j b ν) := by
  choose y hy using hz
  exact (mem_range_realRd_iff YS v₀ hρ i j b hν g).2 ⟨n, y, x, h.trans (Finset.sum_congr rfl fun k _ => by rw [← hy k])⟩

variable (ρ) in

def UnrComb (Φ : GA D (Wc D j) → ℂ) : Prop :=
  ∃ (k L : Type) (_ : Field k) (_ : NumberField k) (_ : Field L) (_ : NumberField L) (_ : Algebra k L)
    (ι : k →+* FractionRing (D.ntw.O i)) (σ : L →+* ℂ), Normal k L ∧
    (∀ (P : Ideal (𝓞 L)) [P.IsPrime], ((D.ntw.l i : ℕ) : 𝓞 L) ∈ P → Algebra.IsUnramifiedAt (𝓞 k) P) ∧
    (∀ a, σ (algebraMap k L a) = ρ.e i b (ι a)) ∧
    ∃ (n : ℕ) (a : Fin n → L) (x : Fin n → NX.FmK S ((j : ℕ) + 1)), Φ = ∑ c, σ (a c) • evW YS v₀ j (Subtype.val (x c))

variable (ρ) in

def RatUnivUr (ν : ℂ) : Prop := ∀ Q M, InRange D.ntw i Q → ∀ s h, ρ.IsDatum i j b s h 0 →
  (∀ v ∈ Q, ((normProd s : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal) → ∀ P ∈ (ρ.B i j b).valSpace, ∀ F : VV ↥D.LL0 (ρ.B i j b).w.lam,
    harmFn (Wc D j).rank (ρ.B i j b).w (ρ.B i j b).F.BS P = coefFn (embLL0 D) (ρ.B i j b).w.lam (F : Pol ↥D.LL0 D.what₂.Tau (Vc D j).rank) →
      ∀ a, UnrComb YS v₀ ρ i j b (ν • ρ.xi i j b D.nexp Q M h P a)

variable {YS v₀ i j b}

theorem UnrComb.mem_range {ν : ℂ} (hν : ν ≠ 0) {g : GA D (Wc D j) → ℂ} (h : UnrComb YS v₀ ρ i j b (ν • g)) :
    g ∈ Set.range (realRd YS v₀ hρ i j b ν) := by
  obtain ⟨k, L, _, _, _, _, _, ι, σ, hN, hu, he, n, a, x, h⟩ := h
  haveI := D.ntw.resO_ac i
  haveI := D.ntw.O_complete i
  exact mem_range_realRd_of_sum hρ hν _ (fun c => mem_range_of_unramified (D.ntw.l i) (D.ntw.O i) _ k L ι (D.ntw.O_l i) hu
    (ρ.e i b) σ he (a c)) x h

end Export

section Any

variable {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} {ρ : Setup X}
  {Y : NExp D.R D.host D.what₂ D.LL0 N X} {i : X.Tw} {j : Fin D.R.m} {b : Bool}

variable (ρ Y i j b) in

def xiLin (Q : Finset (Pl D.host.E)) (M : ℕ) (h : GA D (Vc D j)) (a : ↥(half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)) → ZMod (X.l i ^ M)) :
    PolF D (Wc D j).rank (Vc D j).rank →ₗ[ℂ] (GA D (Wc D j) → ℂ) where
  toFun P := ρ.xi i j b Y Q M h P a
  map_add' P P' := by funext g; simp only [Base.xiCoef_apply, map_add, Pi.add_apply]
  map_smul' c P := by funext g; simp only [Base.xiCoef_apply, map_smul, Pi.smul_apply, RingHom.id_apply]

theorem RatUniv.ratBase {rd : Rd ρ Y i j b} (h : RatUniv rd) : RatBase rd := fun s g P hd => by
  have := h ∅ 0 ⟨by simp, fun _ h => absurd h (Finset.notMem_empty _), by simp⟩ s g P hd (by simp) 0
  rwa [ρ.xi_of_empty i j b Y (by simp)] at this

theorem Faithful.mem_range_of_smul {rd : Rd ρ Y i j b} (hF : Faithful rd) {g : GA D (Wc D j) → ℂ} (hg : g ≠ 0) {u : ℂ}
    (h1 : g ∈ Set.range rd) (h2 : u • g ∈ Set.range rd) : ∃ y, ρ.e i b y = u := by
  obtain ⟨f, rfl⟩ := h1
  obtain ⟨f', h2⟩ := h2
  have hf : f ≠ 0 := fun h => hg (by rw [h, map_zero])
  have hdep : ¬ LinearIndependent (FractionRing (X.O i)) ![f, f'] := fun h => by
    have h3 : LinearIndependent ℂ ![rd f, rd f'] := by
      convert hF 2 _ h using 1
      funext c
      fin_cases c <;> rfl
    have := (LinearIndependent.pair_iff.1 h3 u (-1) (by rw [h2]; simp)).2
    simp at this
  rw [LinearIndependent.pair_iff' hf] at hdep
  push Not at hdep
  obtain ⟨y, rfl⟩ := hdep
  rw [map_smulₛₗ] at h2
  exact ⟨y, smul_left_injective ℂ hg h2⟩

theorem mem_range_of_small (rd : Rd ρ Y i j b) (Φ : PolF D (Wc D j).rank (Vc D j).rank →ₗ[ℂ] (GA D (Wc D j) → ℂ))
    (hinj : ∀ P ∈ (ρ.B i j b).valSpace, harmFn (Wc D j).rank (ρ.B i j b).w (ρ.B i j b).F.BS P = 0 → P = 0)
    (honto : ∀ F : VV ↥D.LL0 (ρ.B i j b).w.lam, ∃ P ∈ (ρ.B i j b).valSpace, harmFn (Wc D j).rank (ρ.B i j b).w (ρ.B i j b).F.BS P =
      coefFn (embLL0 D) (ρ.B i j b).w.lam (F : Pol ↥D.LL0 D.what₂.Tau (Vc D j).rank))
    (hΦ : ∀ P ∈ (ρ.B i j b).valSpace, ∀ F : VV ↥D.LL0 (ρ.B i j b).w.lam, harmFn (Wc D j).rank (ρ.B i j b).w (ρ.B i j b).F.BS P =
      coefFn (embLL0 D) (ρ.B i j b).w.lam (F : Pol ↥D.LL0 D.what₂.Tau (Vc D j).rank) → Φ P ∈ Set.range rd)
    {h : GA D (Vc D j)} {P : PolF D (Wc D j).rank (Vc D j).rank} (hP : P ∈ ρ.lat i j b (ρ.eO i b).range h) :
    Φ P ∈ Set.range rd := by
  have key : ∀ φ ∈ coefLatFn (embLL0 D) (labLL0 D) (ρ.eO i b).range (ρ.B i j b).w.lam ((ρ.B i j b).latAt (finPt _ h)),
      ∃ P' ∈ (ρ.B i j b).valSpace, harmFn (Wc D j).rank (ρ.B i j b).w (ρ.B i j b).F.BS P' = φ ∧ Φ P' ∈ Set.range rd := by
    intro φ hφ
    induction hφ using Submodule.span_induction with
    | mem _ h1 =>
      obtain ⟨F, -, rfl⟩ := h1
      obtain ⟨P', h2, h3⟩ := honto F
      exact ⟨P', h2, h3, hΦ P' h2 F h3⟩
    | zero => exact ⟨0, zero_mem _, map_zero _, 0, by rw [map_zero, map_zero]⟩
    | add _ _ _ _ h1 h2 =>
      obtain ⟨P₁, a1, rfl, f₁, e1⟩ := h1
      obtain ⟨P₂, a2, rfl, f₂, e2⟩ := h2
      exact ⟨P₁ + P₂, add_mem a1 a2, map_add _ _ _, f₁ + f₂, by rw [map_add, map_add, e1, e2]⟩
    | smul c _ _ h1 =>
      obtain ⟨P₁, a1, rfl, f₁, e1⟩ := h1
      obtain ⟨_, o, rfl⟩ := c
      exact ⟨ρ.eO i b o • P₁, Submodule.smul_mem _ _ a1, map_smul _ _ _, o • f₁, by rw [rd_smul, map_smul, e1]⟩
  obtain ⟨P', h1, h2, h3⟩ := key _ hP.2
  rwa [sub_eq_zero.1 (hinj (P - P') (sub_mem hP.1 h1) (by rw [map_sub, h2]; exact sub_self _))]

end Any

section Main

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  {Rl : RealDat3 D A3 Ks} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S)
  (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec)
  {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)

variable {YS v₀ i j b}

theorem ratUniv_of_unram {ν : ℂ} (hν : ν ≠ 0)
    (hinj : ∀ P ∈ (ρ.B i j b).valSpace, harmFn (Wc D j).rank (ρ.B i j b).w (ρ.B i j b).F.BS P = 0 → P = 0)
    (honto : ∀ F : VV ↥D.LL0 (ρ.B i j b).w.lam, ∃ P ∈ (ρ.B i j b).valSpace, harmFn (Wc D j).rank (ρ.B i j b).w (ρ.B i j b).F.BS P =
      coefFn (embLL0 D) (ρ.B i j b).w.lam (F : Pol ↥D.LL0 D.what₂.Tau (Vc D j).rank))
    (h : RatUnivUr YS v₀ ρ i j b ν) : RatUniv (realRd YS v₀ hρ i j b ν) := fun Q M hQ s g _ hd hs a =>
  mem_range_of_small _ (xiLin ρ D.nexp i j b Q M g a) hinj honto
    (fun P' h1 F h2 => (h Q M hQ s g ⟨hd.split, hd.off, hd.fin, hd.supp, zero_mem _⟩ hs P' h1 F h2 a).mem_range hρ hν) hd.mem

theorem scalar_mem_range {ν u : ℂ} (hu : u ≠ 0) (hF : Faithful (realRd YS v₀ hρ i j b ν))
    (h1 : RatBase (realRd YS v₀ hρ i j b ν)) (h2 : RatBase (realRd YS v₀ hρ i j b (u * ν))) {s g P}
    (hd : ρ.IsDatum i j b s g P) (h0 : ρ.theta i j b g P ≠ 0) : ∃ y, ρ.e i b y = u := by
  obtain ⟨f, hf⟩ := h2 s g P hd
  refine hF.mem_range_of_smul h0 (h1 s g P hd) ⟨f, ?_⟩
  rw [← hf, realRd_apply YS v₀ hρ i j b ν, realRd_apply YS v₀ hρ i j b (u * ν), smul_smul, mul_inv, mul_inv_cancel_left₀ hu]

end Main

section Core
open Formalism.IndefR.FWT Formalism.L2.Pj

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T0 : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m} {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL]
  {Rl : RealDat3 D A3 T.Q.c.F} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S)
  {κ : ∀ i : Fin D.R.m, Formalism.MainNotions.WeightFamilies.Wt D ((i : ℕ) + 1)}
  {v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec}

theorem exists_evW_eq_phiC (t : FWTie T Rl.toRealDat κ v₀) (ht : t.Evaluates) (j : Fin D.R.m)
    (hσ : GoodEmb T.Q.c (res T (sg0 D A3.A))) (hV : T.V ((j : ℕ) + 1) (res T (sg0 D A3.A)) = Wc D j) (f : Cu T κ j) :
    ∃ x : NX.FmK S ((j : ℕ) + 1), evW YS v₀ j (Subtype.val x) = phiC T hV (wtA (κ j)) (f : T.R ((j : ℕ) + 1)) := by
  have hx : (YS.fi j).e.symm ((t.e j f : (Rl.FW j).WK) : Fin (Rl.nW j) → D.what₂.LL) ∈ (S.A ((j : ℕ) + 1)).WK := by
    refine ((YS.fi j).wk _).2 ?_
    have e1 : (YS.fi j).e ((YS.fi j).e.symm ((t.e j f : (Rl.FW j).WK) : Fin (Rl.nW j) → D.what₂.LL)) =
        ((t.e j f : (Rl.FW j).WK) : Fin (Rl.nW j) → D.what₂.LL) := LinearEquiv.apply_symm_apply _ _
    rw [e1]
    exact (t.e j f).2
  refine ⟨⟨_, hx⟩, Eq.trans ?_ (ht j (sg0 D A3.A) hσ hV f)⟩
  have e2 := LinearEquiv.apply_symm_apply (YS.fi j).e ((t.e j f : (Rl.FW j).WK) : Fin (Rl.nW j) → D.what₂.LL)
  simp only [evW, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [e2]
  rfl

end Core
end GlobalTheory.SeriesTie
