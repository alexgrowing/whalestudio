import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.JSmul
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyEquivOfSemilinear
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleOfSurjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReductionSameSSOfLattices
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleStd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSeriesOfExact
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PhiGammaLatticeFamiliesShiftInclusion
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralCyclotomicChar

noncomputable section

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open Formalism.MainNotions.N (twistRep coefRep)
open Formalism.GaloisCohomology (scalRep)
open scoped LaurentSeries PowerSeries Pointwise

namespace GlobalTheory.BasePairs

section Gen

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {n : ℕ} {emb : ZMod n → (K₀ →ₐ[Qp] LL)}
    {Γ : GalData G Qp LL O} {k : Type} [Field k] [Algebra O k]

theorem latRep_twLat (T : LocLat G Qp LL O) (θ : G →* Oˣ) (hθ : Continuous fun g => algebraMap O LL (θ g)) (g : G)
    (x : ↥T.L.T) : latRep (twLat T θ hθ).L g x = twistRep (latRep T.L) θ g x :=
  LinearMap.congr_fun (DFunLike.congr_fun (latRep_twLattice T.L θ) g) x

theorem exists_tw_sum [IsTopologicalRing LL] {lam : O} (T T' : LocLat G Qp LL O) (θ : G →* Oˣ)
    (hθ : Continuous fun g => algebraMap O LL (θ g)) (A A' : Ob k G)
    (q : ↥(twLat T θ hθ).L.T →ₗ[O] (Fin A.m → k)) (q' : ↥(twLat T' θ hθ).L.T →ₗ[O] (Fin A'.m → k))
    (h : Onto (twLat T θ hθ) A q) (hk : KerIs lam q) (h' : Onto (twLat T' θ hθ) A' q') (hk' : KerIs lam q') :
    ∃ (C : Ob k G) (r : ↥(twLat (AdmClosure.prodLoc T T') θ hθ).L.T →ₗ[O] (Fin C.m → k))
      (f : LatHom (twLat T θ hθ).L (twLat (AdmClosure.prodLoc T T') θ hθ).L)
      (g : LatHom (twLat T' θ hθ).L (twLat (AdmClosure.prodLoc T T') θ hθ).L)
      (a : (Fin A.m → k) →ₗ[k] (Fin C.m → k)) (b : (Fin A'.m → k) →ₗ[k] (Fin C.m → k)),
      Onto (twLat (AdmClosure.prodLoc T T') θ hθ) C r ∧ KerIs lam r ∧ Function.Bijective (a.coprod b) ∧
      Function.Bijective (f.f.coprod g.f) ∧
      (∀ z ∈ (twLat (AdmClosure.prodLoc T T') θ hθ).L.T, ∃ x ∈ (twLat T θ hθ).L.T, ∃ y ∈ (twLat T' θ hθ).L.T,
        z = f.f x + g.f y) ∧ IsHom A C a ∧ IsHom A' C b ∧
      (∀ (x : ↥(twLat T θ hθ).L.T) (x' : ↥(twLat (AdmClosure.prodLoc T T') θ hθ).L.T),
        (x' : (twLat (AdmClosure.prodLoc T T') θ hθ).V) = f.f x → r x' = a (q x)) ∧
      (∀ (x : ↥(twLat T' θ hθ).L.T) (x' : ↥(twLat (AdmClosure.prodLoc T T') θ hθ).L.T),
        (x' : (twLat (AdmClosure.prodLoc T T') θ hθ).V) = g.f x → r x' = b (q' x)) := by
  let Z := twLat (AdmClosure.prodLoc T T') θ hθ
  let u : ↥Z.L.T ≃ₗ[O] (↥(twLat T θ hθ).L.T × ↥(twLat T' θ hθ).L.T) := StdAdm.prodSubEquiv T.L.T T'.L.T
  obtain ⟨C, r, a, b, hr1, hr2, ha, hb, hab, hz⟩ :=
    exists_sum_reduction (twLat T θ hθ) (twLat T' θ hθ) Z u (fun _ _ => rfl) A A' q q' h hk h' hk'
  let f : LatHom (twLat T θ hθ).L Z.L :=
    { f := LinearMap.inl LL T.V T'.V
      equiv := fun g x => Prod.ext rfl (map_zero ((twLat T' θ hθ).ρ g)).symm
      cont := continuous_id.prodMk continuous_const
      T_le := fun x hx => ⟨hx, Submodule.zero_mem _⟩ }
  let g : LatHom (twLat T' θ hθ).L Z.L :=
    { f := LinearMap.inr LL T.V T'.V
      equiv := fun g x => Prod.ext (map_zero ((twLat T θ hθ).ρ g)).symm rfl
      cont := continuous_const.prodMk continuous_id
      T_le := fun x hx => ⟨Submodule.zero_mem _, hx⟩ }
  refine ⟨C, r, f, g, a, b, hr1, hr2, hab, ?_,
    fun z hz => ⟨z.1, hz.1, z.2, hz.2, Prod.ext (add_zero _).symm (zero_add _).symm⟩, ha, hb,
    fun x x' hx => ?_, fun x x' hx => ?_⟩
  · change Function.Bijective ((LinearMap.inl LL T.V T'.V).coprod (LinearMap.inr LL T.V T'.V))
    rw [LinearMap.coprod_inl_inr]
    exact Function.bijective_id
  · have h1 : (u x').1 = x := Subtype.ext (congrArg Prod.fst hx)
    have h2 : (u x').2 = 0 := Subtype.ext (congrArg Prod.snd hx)
    rw [hz, h1, h2, map_zero, map_zero, add_zero]
  · have h1 : (u x').1 = 0 := Subtype.ext (congrArg Prod.fst hx)
    have h2 : (u x').2 = x := Subtype.ext (congrArg Prod.snd hx)
    rw [hz, h1, h2, map_zero, map_zero, zero_add]

theorem sameSS_base [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O LL] (hlam : Irreducible Γ.lam)
    (hs : Function.Surjective (algebraMap O k)) (hk : ∀ x, algebraMap O k x = 0 ↔ Γ.lam ∣ x)
    (hθ : Continuous fun g => algebraMap O LL (Γ.χ₁⁻¹ g)) {A₀ A : Ob k G}
    {q₀ : ↥(twLat Γ.T₀ Γ.χ₁⁻¹ hθ).L.T →ₗ[O] (Fin A₀.m → k)} (h₀ : Onto (twLat Γ.T₀ Γ.χ₁⁻¹ hθ) A₀ q₀)
    (hK₀ : KerIs Γ.lam q₀) (ω : G →* kˣ) (hω : ∀ g, (ω g : k) = algebraMap O k (Γ.ε g))
    {t μ : ℕ} {U : ZMod n → Multiset ℤ} {T : LocLat G Qp LL O} (hT : SumFull PD emb Γ t U μ T)
    {q : ↥(twLat T Γ.χ₁⁻¹ hθ).L.T →ₗ[O] (Fin A.m → k)} (h : Onto (twLat T Γ.χ₁⁻¹ hθ) A q) (hK : KerIs Γ.lam q) :
    SameSS A.ρ (piRep fun _ : Fin μ => refSum A₀ ω t) := by
  obtain ⟨e₀, he₀⟩ := exists_ref_equiv Γ hs hk A₀ q₀ h₀.1 hK₀
    (fun g x => (congrArg q₀ (latRep_twLat Γ.T₀ _ hθ g x).symm).trans (h₀.2 g x)) ω hω t
  obtain ⟨e, he⟩ := exists_quot_equiv (M := ↥T.L.T) q h.1 hK
  refine sameSS_twist_residue (π := modRep (latRep T.L) Γ.lam) (π' := piRep fun _ : Fin μ => Γ.refRep t)
    hs Γ.χ₁⁻¹ e (fun g x => ?_) (LinearEquiv.piCongrRight fun _ => e₀)
    (fun g x => funext fun j => he₀ g (x j)) (sumFull_sameSS hlam hT)
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact (he (twistRep (latRep T.L) Γ.χ₁⁻¹ g x)).trans
    (((congrArg q (latRep_twLat T _ hθ g x).symm).trans (h.2 g x)).trans (congrArg (A.ρ g) (he x).symm))

theorem exists_quot_of_admissible (hs : Function.Surjective (algebraMap O k)) (h0 : algebraMap O k Γ.lam = 0)
    (hθ : Continuous fun g => algebraMap O LL (Γ.χ₁⁻¹ g)) {t : ℕ} {U : ZMod n → Multiset ℤ}
    (A : Ob k G) (N : Type) [AddCommGroup N] [Module O N] (π : Representation O G N)
    (e : N ≃ₗ[O] (Fin A.m → k)) (hπ : Admissible PD emb Γ t U π)
    (he : ∀ σ x, e (twistRep π Γ.χ₁⁻¹ σ x) = A.ρ σ (e x)) :
    ∃ (μ : ℕ) (T : LocLat G Qp LL O), SumFull PD emb Γ t U μ T ∧
      ∀ (C : Ob k G) (q : ↥(twLat T Γ.χ₁⁻¹ hθ).L.T →ₗ[O] (Fin C.m → k)), Onto (twLat T Γ.χ₁⁻¹ hθ) C q →
        KerIs Γ.lam q → ∃ a, IsHom C A a ∧ Function.Surjective a := by
  obtain ⟨-, μ, T, hT, L₂, s, -, hs', hg, -⟩ := hπ
  refine ⟨μ, T, hT, fun C q hq hK => ?_⟩
  obtain ⟨a, ha⟩ := exists_descend (M := ↥T.L.T) hs h0 q hq.1 hK (e.toLinearMap ∘ₗ s)
  refine ⟨a, fun g y => ?_, fun y => ?_⟩
  · obtain ⟨x, rfl⟩ := hq.1 y
    have h1 : C.ρ g (q x) = q (twistRep (latRep T.L) Γ.χ₁⁻¹ g x) :=
      (hq.2 g x).symm.trans (congrArg q (latRep_twLat T _ hθ g x))
    have h2 : s (twistRep (latRep T.L) Γ.χ₁⁻¹ g x) = twistRep π Γ.χ₁⁻¹ g (s x) :=
      (map_smul s _ _).trans (congrArg (((Γ.χ₁⁻¹ g : Oˣ) : O) • ·) (hg g x))
    exact (congrArg a h1).trans ((ha _).trans ((congrArg e h2).trans ((he g _).trans
      (congrArg (A.ρ g) (ha x).symm))))
  · obtain ⟨x, hx⟩ := (e.surjective.comp hs') y
    exact ⟨q x, (ha x).trans hx⟩

theorem exists_chi_reduction [IsTopologicalRing LL] (hinj : Function.Injective (algebraMap O LL))
    (hs : Function.Surjective (algebraMap O k)) (hk : ∀ x, algebraMap O k x = 0 ↔ Γ.lam ∣ x)
    (hθ : Continuous fun g => algebraMap O LL (Γ.χ₁⁻¹ g)) (c : ℕ)
    (hc : Continuous fun g => algebraMap O LL (Γ.chi (c + 1) g))
    (ω : G →* kˣ) (hω : ∀ g, (ω g : k) = algebraMap O k (Γ.ε g)) :
    ∃ q, Onto (twLat (charLat Qp hinj (Γ.chi (c + 1)) hc) Γ.χ₁⁻¹ hθ) (chr (ω ^ (-(c : ℤ)))) q ∧ KerIs Γ.lam q := by
  obtain ⟨u, -, hu⟩ := charLattice_equiv hinj (Γ.chi (c + 1))
  have hω' : ω = (Units.map (algebraMap O k : O →* k)).comp Γ.ε := MonoidHom.ext fun g => Units.ext (hω g)
  refine exists_char_reduction hs hk (twLat (charLat Qp hinj (Γ.chi (c + 1)) hc) Γ.χ₁⁻¹ hθ) u
    (Γ.χ₁⁻¹ * Γ.chi (c + 1)) (fun g a => ?_) _ fun g => ?_
  · refine (latRep_twLat (charLat Qp hinj (Γ.chi (c + 1)) hc) _ hθ g (u a)).trans ?_
    refine (congrArg (((Γ.χ₁⁻¹ g : Oˣ) : O) • ·) (hu g a).symm).trans ?_
    change ((Γ.χ₁⁻¹ g : Oˣ) : O) • u (((Γ.chi (c + 1) g : Oˣ) : O) • a) =
      (((Γ.χ₁⁻¹ g * Γ.chi (c + 1) g : Oˣ) : O)) • u a
    rw [map_smul, smul_smul, Units.val_mul]
  · rw [hω']
    simp [GalData.chi]

theorem exists_eps_reduction [IsTopologicalRing LL] (hinj : Function.Injective (algebraMap O LL))
    (hs : Function.Surjective (algebraMap O k)) (hk : ∀ x, algebraMap O k x = 0 ↔ Γ.lam ∣ x)
    (hc : Continuous fun g => algebraMap O LL (Γ.ε g))
    (ω : G →* kˣ) (hω : ∀ g, (ω g : k) = algebraMap O k (Γ.ε g)) :
    ∃ q, Onto (charLat Qp hinj Γ.ε hc) (chr (ω ^ (-(-1 : ℤ)))) q ∧ KerIs Γ.lam q := by
  obtain ⟨u, -, hu⟩ := charLattice_equiv hinj Γ.ε
  refine exists_char_reduction hs hk (charLat Qp hinj Γ.ε hc) u Γ.ε (fun g a => ?_) _ fun g => ?_
  · exact (hu g a).symm.trans (map_smul u _ _)
  · rw [neg_neg, zpow_one, hω]

end Gen

section Sit

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {n : ℕ} {emb : ZMod n → (K₀ →ₐ[Qp] LL)}
    {Γ : GalData G Qp LL O} {k : Type} [Field k] [Algebra O k] {l : ℕ} {R : RingPG k l} {F : DFun R n G}
    {r₀ : ℕ} {D : TopData n r₀}
    {RN : ∀ (T : LocLat G Qp LL O) (A : Ob k G), (↥T.L.T →ₗ[O] (Fin A.m → k)) → Lats k n A.m → Prop}

variable (Γ RN) in

def Red (T : LocLat G Qp LL O) (A : Ob k G) (q : ↥T.L.T →ₗ[O] (Fin A.m → k)) (N : Lats k n A.m) : Prop :=
  Onto T A q ∧ KerIs Γ.lam q ∧ RN T A q N

abbrev tw (hθ : IsCrysChar PD emb Γ.χ₁⁻¹ fun i => -D.w i) (T : LocLat G Qp LL O) : LocLat G Qp LL O :=
  twLat T Γ.χ₁⁻¹ hθ.1

theorem crys_tw (htw : StdAdm.TwistRule PD emb O) (hθ : IsCrysChar PD emb Γ.χ₁⁻¹ fun i => -D.w i)
    {T : LocLat G Qp LL O} {U : ZMod n → Multiset ℤ} (h : CrysWith PD emb T.ρ U) :
    CrysWith PD emb (tw hθ T).ρ (fun i => (U i).map (· + -D.w i)) :=
  (htw T U _ _ h hθ).1

variable (RN) in

def Base (hθ : IsCrysChar PD emb Γ.χ₁⁻¹ fun i => -D.w i) (A : Ob k G) (N : Lats k n A.m) : Prop :=
  ∃ (μ : ℕ) (T : LocLat G Qp LL O) (q : ↥(tw hθ T).L.T →ₗ[O] (Fin A.m → k)),
    SumFull PD emb Γ D.t D.Ut μ T ∧ Red Γ RN (tw hθ T) A q N

variable [IsTopologicalRing LL] [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O LL]
  (hθ : IsCrysChar PD emb Γ.χ₁⁻¹ fun i => -D.w i)
  (hk : Function.Surjective (algebraMap O k) ∧ ∀ x, algebraMap O k x = 0 ↔ Γ.lam ∣ x) (hlam : Irreducible Γ.lam)
  (hsum : StdAdm.SumRule PD emb O) (htw : StdAdm.TwistRule PD emb O)
  (hobj : ∀ (T : LocLat G Qp LL O) (A : Ob k G) q, Onto T A q → F.Obj A)
  (hex : ∀ (T : LocLat G Qp LL O) (A : Ob k G) q (U : ZMod n → Multiset ℤ), Onto T A q → KerIs Γ.lam q → CrysWith PD emb T.ρ U →
    ∃ N : Lats k n A.m, RN T A q N ∧ ∀ i, IsLat (N i))
  (habc : ∀ (T : LocLat G Qp LL O) (A : Ob k G) q (U : ZMod n → Multiset ℤ), Onto T A q → KerIs Γ.lam q → CrysWith PD emb T.ρ U →
    ∀ N : Lats k n A.m, RN T A q N → ∀ w w' : ZMod n → ℕ, (∀ i, ∀ u ∈ U i, -(w i : ℤ) ≤ u ∧ u ≤ w' i) →
    ABC (F.D A) (fun i => w i) (fun i => w' i) N)
  (hsen : ∀ (T : LocLat G Qp LL O) (A : Ob k G) q (U : ZMod n → Multiset ℤ), Onto T A q → KerIs Γ.lam q → CrysWith PD emb T.ρ U →
    ∀ N : Lats k n A.m, RN T A q N → ∀ i x, sen ((F.D A).γ i) (N i) x = resCount (U i) 0 x)
  (hpoly : ∀ (T : LocLat G Qp LL O) (A : Ob k G) q (U : ZMod n → Multiset ℤ), Onto T A q → KerIs Γ.lam q → CrysWith PD emb T.ρ U →
    ∀ N : Lats k n A.m, RN T A q N → ∀ (i : ZMod n) (s : ℕ),
    (∀ u ∈ U i, ∀ a : ℕ, a < s → (l : ℤ) ∣ (a : ℤ) - u → (a : ℤ) = u) → EPoly ((F.D A).γ i) (N i) s)
  (hrk : ∀ (T : LocLat G Qp LL O) (A : Ob k G) q (U : ZMod n → Multiset ℤ), Onto T A q → KerIs Γ.lam q → CrysWith PD emb T.ρ U →
    ∀ N : Lats k n A.m, RN T A q N → ∀ a : ZMod n → ℤ, A.m = 1 → (∀ i, U i = {a i}) →
    ∀ i, pull ((F.D A).φ i) (N (i - 1)) = sh (a i) (N i))
  (hadd : ∀ (T : LocLat G Qp LL O) (A : Ob k G) q (U : ZMod n → Multiset ℤ), Onto T A q → KerIs Γ.lam q → CrysWith PD emb T.ρ U →
    ∀ (T' : LocLat G Qp LL O) (A' : Ob k G) q' (U' : ZMod n → Multiset ℤ),
    Onto T' A' q' → KerIs Γ.lam q' → CrysWith PD emb T'.ρ U' →
    ∀ (Z : LocLat G Qp LL O) (C : Ob k G) r (V : ZMod n → Multiset ℤ),
    Onto Z C r → KerIs Γ.lam r → CrysWith PD emb Z.ρ V →
    ∀ (f : LatHom T.L Z.L) (g : LatHom T'.L Z.L) (a : (Fin A.m → k) →ₗ[k] (Fin C.m → k))
    (b : (Fin A'.m → k) →ₗ[k] (Fin C.m → k)), Function.Bijective (f.f.coprod g.f) →
    (∀ z ∈ Z.L.T, ∃ x ∈ T.L.T, ∃ y ∈ T'.L.T, z = f.f x + g.f y) → IsHom A C a → IsHom A' C b →
    (∀ (x : ↥T.L.T) (x' : ↥Z.L.T), (x' : Z.V) = f.f x → r x' = a (q x)) →
    (∀ (x : ↥T'.L.T) (x' : ↥Z.L.T), (x' : Z.V) = g.f x → r x' = b (q' x)) →
    ∀ (N : Lats k n A.m) (N' : Lats k n A'.m) (L : Lats k n C.m), RN T A q N → RN T' A' q' N' → RN Z C r L →
    ∀ i, L i = F.push A C a N i ⊔ F.push A' C b N' i)

set_option linter.unusedSectionVars false

include hθ hk hlam hsum htw hobj hex habc hsen hpoly hrk hadd

theorem exists_red {T : LocLat G Qp LL O} {U : ZMod n → Multiset ℤ} (h : CrysWith PD emb T.ρ U) :
    ∃ (A : Ob k G) (q : ↥T.L.T →ₗ[O] (Fin A.m → k)) (N : Lats k n A.m),
      A.m = Module.finrank LL T.V ∧ Red Γ RN T A q N := by
  have := StdAdm.finite_lat T
  have := T.L.free
  obtain ⟨A, q, hm, hq, hK, hg⟩ := exists_reduction hk.1 hk.2 (latRep T.L)
  obtain ⟨N, hN, -⟩ := hex T A q U ⟨hq, hg⟩ hK h
  refine ⟨A, q, N, hm.trans ?_, ⟨hq, hg⟩, hK, hN⟩
  have : Submodule.IsLattice LL T.L.T := ⟨T.L.fg, T.L.span⟩
  rw [Module.finrank, Module.finrank, Submodule.IsLattice.rank' LL]

theorem exists_red_sum {T T' : LocLat G Qp LL O} {U U' : ZMod n → Multiset ℤ} (h : CrysWith PD emb T.ρ U)
    (h' : CrysWith PD emb T'.ρ U') {A A' : Ob k G} {q q' N N'} (hr : Red Γ RN (tw hθ T) A q N)
    (hr' : Red Γ RN (tw hθ T') A' q' N') :
    ∃ C r a b, IsHom A C a ∧ IsHom A' C b ∧ Function.Bijective (a.coprod b) ∧
      Red Γ RN (tw hθ (AdmClosure.prodLoc T T')) C r (fun i => F.push A C a N i ⊔ F.push A' C b N' i) := by
  obtain ⟨C, r, f, g, a, b, hr1, hr2, hab, h1, h2, ha, hb, h3, h4⟩ :=
    exists_tw_sum T T' _ hθ.1 A A' q q' hr.1 hr.2.1 hr'.1 hr'.2.1
  have hZ := crys_tw htw hθ (T := AdmClosure.prodLoc T T')
    (hsum T T' (AdmClosure.prodLoc T T') _ _ (LinearEquiv.refl _ _) (fun _ _ => rfl) h h')
  obtain ⟨L, hL, -⟩ := hex (tw hθ (AdmClosure.prodLoc T T')) C r _ hr1 hr2 hZ
  have key := hadd (tw hθ T) A q _ hr.1 hr.2.1
    (crys_tw htw hθ h) (tw hθ T') A' q' _ hr'.1 hr'.2.1 (crys_tw htw hθ h') (tw hθ (AdmClosure.prodLoc T T')) C r _ hr1 hr2
    hZ f g a b h1 h2 ha hb h3 h4 N N' L hr.2.2 hr'.2.2 hL
  obtain rfl : L = fun i => F.push A C a N i ⊔ F.push A' C b N' i := funext key
  exact ⟨C, r, a, b, ha, hb, hab, hr1, hr2, hL⟩

theorem base_abc {A : Ob k G} {N} (h : Base RN hθ A N) : ABC (F.D A) D.w D.wst N := by
  obtain ⟨μ, T, q, hT, hr⟩ := h
  have key := habc (tw hθ T) A q _ hr.1 hr.2.1
    (crys_tw htw hθ (sumFull_crys hsum hT)) N hr.2.2 (fun i => (D.w i).toNat) (fun i => (D.wst i).toNat)
    (fun i u hu => by
      obtain ⟨u', hu', rfl⟩ := Multiset.mem_map.1 hu
      have := D.mem_Ut i (Multiset.mem_of_mem_nsmul hu')
      have := w_range D i
      simp only [TopData.wst]
      omega)
  have e1 : (fun i => (((D.w i).toNat : ℕ) : ℤ)) = D.w := funext fun i => by
    have := w_range D i
    omega
  have e2 : (fun i => (((D.wst i).toNat : ℕ) : ℤ)) = D.wst := funext fun i => by
    have := w_range D i
    simp only [TopData.wst]
    omega
  rwa [e1, e2] at key

theorem base_sen {A₀ : Ob k G} {q₀ N₀} (h₀ : Red Γ RN (tw hθ Γ.T₀) A₀ q₀ N₀) (ω : G →* kˣ)
    (hω : ∀ g, (ω g : k) = algebraMap O k (Γ.ε g)) {A : Ob k G} {N} (h : Base RN hθ A N) :
    ∃ μ : ℕ, SameSS A.ρ (piRep fun _ : Fin μ => refSum A₀ ω D.t) ∧
      ∀ i x, sen ((F.D A).γ i) (N i) x = μ * resCount (D.Ut i) (D.w i) x := by
  obtain ⟨μ, T, q, hT, hr⟩ := h
  refine ⟨μ, ?_, fun i x => ?_⟩
  · exact sameSS_base hlam hk.1 hk.2 hθ.1 h₀.1 h₀.2.1 ω hω hT hr.1 hr.2.1
  · rw [hsen (tw hθ T) A q _ hr.1 hr.2.1
      (crys_tw htw hθ (sumFull_crys hsum hT)) N hr.2.2 i x, resCount_nsmul_map]

theorem base_sum {A A' : Ob k G} {N N'} (h : Base RN hθ A N) (h' : Base RN hθ A' N') :
    ∃ C i j, IsHom A C i ∧ IsHom A' C j ∧ Function.Bijective (i.coprod j) ∧
      Base RN hθ C (fun a => F.push A C i N a ⊔ F.push A' C j N' a) := by
  obtain ⟨μ, T, q, hT, hr⟩ := h
  obtain ⟨μ', T', q', hT', hr'⟩ := h'
  obtain ⟨C, r, a, b, ha, hb, hab, hr⟩ :=
    exists_red_sum hθ hk hlam hsum htw hobj hex habc hsen hpoly hrk hadd (sumFull_crys hsum hT) (sumFull_crys hsum hT') hr hr'
  exact ⟨C, a, b, ha, hb, hab, μ + μ', _, r, AdmClosure.sumFull_prod hT hT', hr⟩

theorem base_e (hT1 : D.T1 l) (hT3 : D.T3 l) {A : Ob k G} {N} (h : Base RN hθ A N) (i : ZMod n) (hi : D.ty i = LType.Bd) :
    EPoly ((F.D A).γ i) (N i) (D.wst i + 1) := by
  obtain ⟨μ, T, q, hT, hr⟩ := h
  have hw := w_range D i
  have key := hpoly (tw hθ T) A q _ hr.1 hr.2.1
    (crys_tw htw hθ (sumFull_crys hsum hT)) N hr.2.2 i (D.wst i + 1).toNat
    (fun u hu a ha hd => by
      obtain ⟨u', hu', rfl⟩ := Multiset.mem_map.1 hu
      exact eq_of_dvd D hT1 hT3 i hi u' (Multiset.mem_of_mem_nsmul hu') a (by omega) hd)
  have e : (((D.wst i + 1).toNat : ℕ) : ℤ) = D.wst i + 1 := by
    simp only [TopData.wst]
    omega
  rwa [e] at key

theorem char_props {T : LocLat G Qp LL O} {e : ℤ} (h : CrysWith PD emb T.ρ fun _ => {e}) {ψ : G →* kˣ} {q N}
    (hr : Red Γ RN T (chr ψ) q N) (i : ZMod n) : IsLat (N i) ∧ CondC ((F.D (chr ψ)).γ i) (N i) ∧
      pull ((F.D (chr ψ)).φ i) (N (i - 1)) = sh e (N i) ∧
      ∀ x, sen ((F.D (chr ψ)).γ i) (N i) x = resCount {e} 0 x := by
  have key := habc T _ q _ hr.1 hr.2.1 h N hr.2.2
    (fun _ => (-e).toNat) (fun _ => e.toNat) (fun i u hu => by
      rw [Multiset.mem_singleton.1 hu]
      omega)
  exact ⟨key.1 i, key.2.2 i,
    hrk T _ q _ hr.1 hr.2.1 h N hr.2.2 (fun _ => e) rfl (fun _ => rfl) i,
    hsen T _ q _ hr.1 hr.2.1 h N hr.2.2 i⟩

theorem exists_model (A : Ob k G) (N : Type) [AddCommGroup N] [Module O N] (π : Representation O G N)
    (e : N ≃ₗ[O] (Fin A.m → k)) (hπ : Admissible PD emb Γ D.t D.Ut π) (he : ∀ σ x, e (twistRep π Γ.χ₁⁻¹ σ x) = A.ρ σ (e x)) :
    ∃ L, IsModel F (Base RN hθ) A L := by
  obtain ⟨μ, T, hT, h⟩ := exists_quot_of_admissible hk.1 ((hk.2 _).2 dvd_rfl) hθ.1 A N π e hπ he
  obtain ⟨C, q, Nb, -, hr⟩ := exists_red hθ hk hlam hsum htw hobj hex habc hsen hpoly hrk hadd (crys_tw htw hθ (sumFull_crys hsum hT))
  obtain ⟨a, ha, hs⟩ := h C q hr.1 hr.2.1
  exact ⟨_, C, Nb, C, LinearMap.id, a, ⟨μ, T, q, hT, hr⟩, fun _ _ => rfl, Function.injective_id, ha, hs, rfl⟩

theorem exists_std (hD : IsTopGal PD emb D Γ) (hε : IsCrysChar PD emb Γ.ε fun _ => -1)
    {A₀ : Ob k G} {q₀ N₀} (h₀ : Red Γ RN (tw hθ Γ.T₀) A₀ q₀ N₀) (ω : G →* kˣ)
    (hω : ∀ g, (ω g : k) = algebraMap O k (Γ.ε g)) :
    IsModel F (Base RN hθ) A₀ N₀ ∧ ∀ e : ℤ, ∃ N : Lats k n 1,
      (-1 ≤ e → F.Obj (chr (ω ^ (-e))) ∧ ∀ i, IsLat (N i) ∧ CondC ((F.D (chr (ω ^ (-e)))).γ i) (N i) ∧
        pull ((F.D (chr (ω ^ (-e)))).φ i) (N (i - 1)) = sh e (N i) ∧
        ∀ x, sen ((F.D (chr (ω ^ (-e)))).γ i) (N i) x = resCount {e} 0 x) ∧
      (0 ≤ e → e < D.t → IsModel F (Base RN hθ) (chr (ω ^ (-e))) N) := by
  have hinj := IsFractionRing.injective O LL
  have hχ := StdAdm.isCrysChar_chi hinj htw hD.2.2.1 hε
  let X : ℕ → LocLat G Qp LL O := fun c => charLat Qp hinj _ (hχ c).1
  have hX₀ : ∀ c : ℕ, CrysWith PD emb (X c).ρ fun i => {D.w i + c} := fun c => (hχ c).2
  have hX : ∀ c : ℕ, CrysWith PD emb (tw hθ (X c)).ρ fun _ => {(c : ℤ)} := fun c => by
    have h := crys_tw htw hθ (T := X c) (hX₀ c)
    simpa using h
  have hXr : ∀ c : ℕ, ∃ q N, Red Γ RN (tw hθ (X c)) (chr (ω ^ (-(c : ℤ)))) q N := fun c => by
    obtain ⟨q, hq, hK⟩ := exists_chi_reduction (Qp := Qp) hinj hk.1 hk.2 hθ.1 c (hχ c).1 ω hω
    obtain ⟨N, hN, -⟩ := hex (tw hθ (X c)) (chr (ω ^ (-(c : ℤ)))) q _ hq hK (hX c)
    exact ⟨q, N, hq, hK, hN⟩
  choose q N hr using hXr
  obtain ⟨T, e, hT, ⟨C, r, L, hL, t0, t1⟩, he⟩ := exists_sum_ind hinj hsum hD.2.1 hχ
    (fun j T => ∃ C r L, Red Γ RN (tw hθ T) C r L ∧ IsTrace F A₀ N₀ C L ∧
      ∀ c : ℕ, c < j → IsTrace F (chr (ω ^ (-(c : ℤ)))) (N c) C L)
    ⟨A₀, q₀, N₀, h₀, IsTrace.refl F A₀ (hobj _ _ _ h₀.1) N₀, fun c hc => absurd hc (Nat.not_lt_zero c)⟩
    (fun j T hT ⟨C, r, L, hL, t0, t1⟩ => by
      obtain ⟨C', r', a, b, ha, hb, hab, hL'⟩ :=
        exists_red_sum hθ hk hlam hsum htw hobj hex habc hsen hpoly hrk hadd (T := T) (T' := X j) hT (hX₀ j) hL (hr j)
      have hC' := hobj _ _ _ hL'.1
      obtain ⟨s0, s1⟩ := isTrace_sum F _ _ C' a b hC' ha hb hab L (N j)
      refine ⟨C', r', _, hL', t0.trans hC' s0, fun c hc => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hc with hc | rfl
      · exact (t1 c hc).trans hC' s0
      · exact s1) D.t
  have hB : Base RN hθ C L := ⟨1, T, r, (StdAdm.full_of_equiv hlam T e hT he).sumFull, hL⟩
  have hC' := hobj _ _ _ hL.1
  refine ⟨t0.isModel hC' hB, fun e => ?_⟩
  rcases le_or_gt 0 e with he | he
  · obtain ⟨c, rfl⟩ := Int.eq_ofNat_of_zero_le he
    exact ⟨N c, fun _ => ⟨hobj _ _ _ (hr c).1, char_props hθ hk hlam hsum htw hobj hex habc hsen hpoly hrk hadd (hX c) (hr c)⟩,
      fun _ hc => (t1 c (by exact_mod_cast hc)).isModel hC' hB⟩
  · obtain ⟨q', hq, hK⟩ := exists_eps_reduction (Qp := Qp) hinj hk.1 hk.2 hε.1 ω hω
    let Y : LocLat G Qp LL O := charLat Qp hinj _ hε.1
    have hY : CrysWith PD emb Y.ρ fun _ => {-1} := hε.2
    obtain ⟨N', hN, -⟩ := hex Y (chr (ω ^ (-(-1 : ℤ)))) q' _ hq hK hY
    refine ⟨N', fun h => ?_, fun h => absurd h (not_le.2 he)⟩
    obtain rfl : e = -1 := by omega
    exact ⟨hobj Y _ _ hq, char_props hθ hk hlam hsum htw hobj hex habc hsen hpoly hrk hadd (T := Y) hY ⟨hq, hK, hN⟩⟩

theorem exists_modTh [Fact l.Prime] [CharP k l] [NeZero n] (hD : IsTopGal PD emb D Γ)
    (hε : IsCrysChar PD emb Γ.ε fun _ => -1)
    (hne : ∀ ω : G →* kˣ, (∀ g, (ω g : k) = algebraMap O k (Γ.ε g)) → ∀ e : ℕ, 0 < e → e + 1 < l → ω ^ e ≠ 1) :
    ∃ M : ModTh F D, (∀ σ, (M.ω σ : k) = algebraMap O k (Γ.ε σ)) ∧
    (∃ q : ↥(tw hθ Γ.T₀).L.T →ₗ[O] (Fin M.T.m → k), Onto (tw hθ Γ.T₀ : LocLat G Qp LL O) M.T q ∧ KerIs Γ.lam q) ∧
    M.Base = Base RN hθ := by
  obtain ⟨A₀, q₀, N₀, hm, h₀⟩ := exists_red hθ hk hlam hsum htw hobj hex habc hsen hpoly hrk hadd (crys_tw htw hθ hD.2.1)
  let ω : G →* kˣ := (Units.map (algebraMap O k : O →* k)).comp Γ.ε
  have hω : ∀ g, (ω g : k) = algebraMap O k (Γ.ε g) := fun _ => rfl
  obtain ⟨hs, hN⟩ := exists_std hθ hk hlam hsum htw hobj hex habc hsen hpoly hrk hadd hD hε h₀ ω hω
  choose N hN hM using hN
  refine ⟨{ T := A₀
            T_m := hm.trans hD.1
            ω := ω
            ω_ne := hne ω hω
            Base := Base RN hθ
            base_obj := fun A N ⟨_, _, _, _, h⟩ => hobj _ _ _ h.1
            base_abc := fun A N h => base_abc hθ hk hlam hsum htw hobj hex habc hsen hpoly hrk hadd h
            base_sen := fun A N h => base_sen hθ hk hlam hsum htw hobj hex habc hsen hpoly hrk hadd h₀ ω hω h
            base_sum := fun A N A' N' h h' => base_sum hθ hk hlam hsum htw hobj hex habc hsen hpoly hrk hadd h h'
            base_e := fun h1 h3 A N h => base_e hθ hk hlam hsum htw hobj hex habc hsen hpoly hrk hadd h1 h3 h
            Nstd := N₀
            std_model := hs
            std_sen := fun i x => ?_
            Nχ := N
            χ_obj := fun e h _ => (hN e h).1
            χ_lat := fun e h _ => (hN e h).2
            χ_model := hM
            χ_zero := eq_span_unit F (ω ^ (-(0 : ℤ))) (by simp) (N 0) (fun i => ((hN 0 (by simp)).2 i).1)
              fun i => ((hN 0 (by simp)).2 i).2.2.1 }, hω, ⟨q₀, h₀.1, h₀.2.1⟩, rfl⟩
  have h := resCount_nsmul_map 1 (D.U i) (D.w i) x
  rw [one_nsmul, one_mul] at h
  rw [hsen (tw hθ Γ.T₀) A₀ q₀ _ h₀.1 h₀.2.1
    (crys_tw htw hθ hD.2.1) N₀ h₀.2.2 i x, h]

theorem exists_real [Fact l.Prime] [CharP k l] [NeZero n] (hD : IsTopGal PD emb D Γ)
    (hε : IsCrysChar PD emb Γ.ε fun _ => -1)
    (hne : ∀ ω : G →* kˣ, (∀ g, (ω g : k) = algebraMap O k (Γ.ε g)) → ∀ e : ℕ, 0 < e → e + 1 < l → ω ^ e ≠ 1) :
    ∃ M : ModTh F D, (∀ σ, (M.ω σ : k) = algebraMap O k (Γ.ε σ)) ∧
      (∃ q : ↥Γ.T₀.L.T →ₗ[O] (Fin M.T.m → k), Function.Surjective q ∧
        KerIs Γ.lam q ∧ ∀ σ x, q (twistRep Γ.W₀ Γ.χ₁⁻¹ σ x) = M.T.ρ σ (q x)) ∧
      ∀ (A : Ob k G) (N : Type) [AddCommGroup N] [Module O N] (π : Representation O G N)
        (e : N ≃ₗ[O] (Fin A.m → k)), Admissible PD emb Γ D.t D.Ut π →
        (∀ σ x, e (twistRep π Γ.χ₁⁻¹ σ x) = A.ρ σ (e x)) → ∃ L, M.Model A L := by
  obtain ⟨M, h1, ⟨q, hq, hK⟩, h3⟩ := exists_modTh hθ hk hlam hsum htw hobj hex habc hsen hpoly hrk hadd hD hε hne
  refine ⟨M, h1, ⟨q, hq.1, hK, fun g x => (congrArg q (latRep_twLat Γ.T₀ _ hθ.1 g x).symm).trans (hq.2 g x)⟩,
    fun A N _ _ π e hπ he => ?_⟩
  have h := exists_model hθ hk hlam hsum htw hobj hex habc hsen hpoly hrk hadd A N π e hπ he
  rwa [← h3] at h

end Sit

end GlobalTheory.BasePairs
