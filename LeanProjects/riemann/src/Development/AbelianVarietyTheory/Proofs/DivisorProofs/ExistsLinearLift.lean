import Mathlib
import Development.AutomorphicArithmetic.CyclotomicBounds.RootsOfUnity.MassNumeric
import Development.AutomorphicArithmetic.CyclotomicBounds.RootsOfUnity.HostTorsionOrderLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormOfClassSums

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
open scoped TensorProduct InnerProductSpace
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues

namespace GlobalTheory.AdelicScalar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem zeta_eval {V W : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel W S} {μW : Measure (GA D W)} {𝓖 : Set (GA D W)}
    (HW : HMod (MMap M)) {N : ℝ} (hW : ∀ x y, inner ℂ x y = (N : ℂ) * ipM M μW 𝓖 (HW.e x) (HW.e y)) (θ : Datum.InfFam D)
    {J : Set (GA D W)} {χ : GA D W → ℂ} (U₁ U₂ : HW.H) (hU : HW.e U₁ ∈ Mult θ M J χ) (v : M.Vec) (K : Subgroup (GA D W))
    {X : Type} [MeasurableSpace X] (μ : Measure X) (𝓧 : Set X) (ω : GA D V × GA D W →* Module.End ℂ (X → ℂ)) (φ f : X → ℂ)
    (Fr : Frames W) (hFr : ∀ ρ b, realMat W Fr ρ b ∈ Formalism.QuantumDeterminants.UH (gramAt D W ρ)) (mR : ∀ ρ, Measure (Upq W ρ))
    (hmR : ∀ ρ, Lev.IsMinf (mR ρ)) (c0 z : ℂ)
    (hF : ∀ x ∈ GfC W, ∀ g : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ, (∀ ρ, g ρ ∈ Formalism.QuantumDeterminants.UH (gramAt D W ρ)) →
      l2 μ 𝓧 (ω (1, x * realElt θ W g) φ) φ =
        c0 * (∏ ρ, ⟪(v ρ : M.H ρ), M.rep ρ (g ρ) (v ρ : M.H ρ)⟫_ℂ) * 1 * l2 μ 𝓧 (ω (1, x) f) f)
    (hZ : ∀ v₁ v₂ : M.Vec, HasSum (fun y : FinCos W K =>
        l2 μ 𝓧 (ω (1, y.rep) f) f * starRingEnd ℂ (l2 μW 𝓖 (rTr W y.rep (HW.e U₁ v₁)) (HW.e U₂ v₂)))
      (z * starRingEnd ℂ (l2 μW 𝓖 (HW.e U₁ v₁) (HW.e U₂ v₂)))) :
    ∫ b : ∀ ρ, Upq W ρ, ∑' x : FinCos W K, l2 μ 𝓧 (ω (1, x.rep * realElt θ W fun ρ => realMat W Fr ρ (b ρ)) φ) φ *
        starRingEnd ℂ (l2 μW 𝓖 (rTr W (x.rep * realElt θ W fun ρ => realMat W Fr ρ (b ρ)) (HW.e U₁ v)) (HW.e U₂ v))
        ∂(Measure.pi mR) =
      c0 * z * starRingEnd ℂ (ipM M μW 𝓖 (HW.e U₂) (HW.e U₁)) *
        ((∏ ρ, ∫ b, ‖⟪(v ρ : M.H ρ), M.rep ρ (realMat W Fr ρ b) (v ρ : M.H ρ)⟫_ℂ‖ ^ 2 ∂(mR ρ) : ℝ) : ℂ) := by
  have := fun ρ => sigmaFinite_haar (mR ρ) (hmR ρ).1
  refine integral_pi_eval mR (fun ρ b => ⟪(v ρ : M.H ρ), M.rep ρ (realMat W Fr ρ b) (v ρ : M.H ρ)⟫_ℂ) _ c0 z _ fun b => ?_
  obtain ⟨w, h1, h2⟩ := coef_translate HW hW θ U₁ U₂ hU (fun ρ => realMat W Fr ρ (b ρ)) (fun ρ => hFr ρ _) v
  rw [← h2]
  refine tsum_eval _ _ _ _ _ (fun x => ?_) (hZ w v)
  rw [hF x.rep x.out.2 _ fun ρ => hFr ρ _, rTr_mul, h1]

theorem eventually_grpOf (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) :
    ∀ᶠ κ in nhds (1 : GA D V), ∃ h : (finHom V).rangeRestrict κ ∈ grpOf V β L, chrOf V β L ⟨_, h⟩ = 1 := by
  classical
  filter_upwards [GlobalTheory.ThetaIntegrand.eventually_princ V β (L.Pg ∪ L.Q)] with κ hh
  obtain ⟨h1, h2, h3⟩ := hh
  have hk : Lev.finE V κ ∈ lev D.sp.cm V.gram β L :=
    Kg_le_lev (D := L) (T := L.Pg ∪ L.Q) Finset.subset_union_left Finset.subset_union_right
      ⟨⟨h1, h2⟩, Subgroup.mem_iInf.2 fun PP => Subgroup.mem_iInf.2 fun hP => mem_princAt.2 ⟨h2, h3 PP hP⟩⟩
  exact ⟨hk, GlobalTheory.ThetaIntegrand.levFn_eq_one β (Lev.finE V κ) L (fun PP hP => h3 PP (Finset.mem_union_left _ hP))
    fun PP hP => h3 PP (Finset.mem_union_right _ hP)⟩

open scoped ComplexOrder in

theorem integrableOn_lift {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {ω : GA D V × GA D W →* Module.End ℂ (Datum.WO V W → ℂ)} (hω : Datum.IsWeilDatumO ψ V W χS χT ω) (hs : V.SigOK)
    (hp : V.IsPosDef) (c : CoefA V) (hc : c.Is) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
    {x : Bridge.Gf V → c.W} (hx : x ∈ Bridge.AdForms (Bridge.ratF V) c.coef.ρ (grpOf V β L) (chrOf V β L))
    (φ : c.W →ₗ[ℂ] (Datum.WO V W → ℂ)) (hφ : ∀ w, Datum.IsThetaFunO ψ V W (φ w)) {K : Subgroup (GL (Fin V.rank) (Lev.EAf D))}
    {ν : Measure (GA D V)} {𝓕 : Set (GA D V)} (hν : IsMeasDef V K ν 𝓕) (g : GA D W) :
    IntegrableOn (fun h => Datum.thetaKO ω h g (φ (c.ext x h))) 𝓕 ν := by
  have hpos : ∀ τ, (gramAt D V τ).PosDef := fun τ => by
    have := hs (tauE D τ)
    rw [hp] at this
    exact GlobalTheory.DefiniteQuotient.posDef_of_signature this
  have : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  exact GlobalTheory.DefiniteQuotient.integrableOn_theta D ψ hω.std V W χS χT ω hω hpos c.W φ hφ _
    (GlobalTheory.ThetaIntegrand.form_continuous (finHom V).rangeRestrict (GQ V) c.ρ hc.2.2.1 (eventually_grpOf V β L) hx)
    (GlobalTheory.ThetaIntegrand.ext_invariant c hx) ν 𝓕 hν.1.1 hν.2 g

theorem exists_linear_lift {X X' Y B W Z κ₁ κ₂ : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup X'] [Module ℂ X']
    [AddCommGroup Y] [Module ℂ Y] [MeasurableSpace B]
    [AddCommGroup W] [Module ℂ W] [AddCommGroup Z] [Module ℂ Z] (ν : Measure B) (𝓕 : Set B) (e : Y →ₗ[ℂ] Z)
    (val : κ₁ → κ₂ → Z → ℂ) (hadd : ∀ a b z z', val a b (z + z') = val a b z + val a b z')
    (hsm : ∀ a b (t : ℂ) z, val a b (t • z) = t * val a b z)
    (E₁ : X →ₗ[ℂ] X') (E₂ : X' →ₗ[ℂ] (B → W)) (k : κ₁ → κ₂ → B → W → ℂ)
    (kadd : ∀ a b h z z', k a b h (z + z') = k a b h z + k a b h z') (ksm : ∀ a b h (t : ℂ) z, k a b h (t • z) = t * k a b h z)
    (hint : ∀ x a b, IntegrableOn (fun h => k a b h (E₂ (E₁ x) h)) 𝓕 ν)
    (hex : ∀ x, ∃ y, ∀ a b, val a b (e y) = ∫ h in 𝓕, k a b h (E₂ (E₁ x) h) ∂ν) :
    ∃ th : X →ₗ[ℂ] Y, ∀ x a b, IntegrableOn (fun h => k a b h (E₂ (E₁ x) h)) 𝓕 ν ∧
      val a b (e (th x)) = ∫ h in 𝓕, k a b h (E₂ (E₁ x) h) ∂ν := by
  have k0 : ∀ a b h, k a b h 0 = 0 := fun a b h => by simpa using ksm a b h 0 0
  obtain ⟨th, h⟩ := exists_linear_section (fun x y => ∀ a b, val a b (e y) = ∫ h in 𝓕, k a b h (E₂ (E₁ x) h) ∂ν)
    (fun a b => by simpa [k0] using hsm a b 0 0)
    (fun x x' y y' h h' a b => by
      rw [map_add, hadd, h, h', ← integral_add (hint x a b) (hint x' a b)]
      simp only [map_add, Pi.add_apply, kadd])
    (fun t x y h a b => by
      rw [map_smul, hsm, h, ← integral_const_mul]
      simp only [map_smul, Pi.smul_apply, ksm]) hex
  exact ⟨th, fun x a b => ⟨hint x a b, h x a b⟩⟩

theorem form_algebra {κ : Type} [Fintype κ] (N Vol H P nrm dO J : ℝ) (E x y cb c0 : ℂ) (t : κ → ℂ) (hc : c0 = H)
    (hx : x = (N : ℂ) ^ 2 * ∑ k, t k) (ht : ∀ k, t k = (Vol : ℂ) * (c0 * ((P : ℂ) * (nrm : ℂ) * (E / (dO : ℂ))) * cb * (J : ℂ)))
    (hy : y = (N : ℂ) * cb) : x = (((P * (N * Fintype.card κ * Vol * H * nrm / dO * J) : ℝ) : ℂ) * E) * y := by
  rw [hx, hy]
  simp only [ht, hc, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  push_cast
  ring

theorem scalar_adjLev {Pg : Finset (Pl D.host.E)} {r : ℕ} (P : LevelP Pg r ℂ) {X Y : Type} [NormedAddCommGroup X]
    [InnerProductSpace ℂ X] [FiniteDimensional ℂ X] [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [FiniteDimensional ℂ Y]
    (th : X →ₗ[ℂ] Y) (U : Submodule ℂ Y) (hU : U ≠ ⊥) (a : ℝ) (E : ℂ) (ha : 0 < a * ‖E‖)
    (h : ∀ y ∈ U, ∀ y', inner ℂ (LinearMap.adjoint th y) (LinearMap.adjoint th y') =
      (((((Nat.card P.H : ℕ) : ℝ) * a : ℝ) : ℂ) * E) * inner ℂ y y') :
    ∀ y ∈ U, th (adjLev P th y) = ((a * ‖E‖ : ℝ) : ℂ) • y := by
  intro y hy
  have hP : 0 < Nat.card P.H := Nat.card_pos
  have ha0 : 0 ≤ a := by
    by_contra hneg
    exact absurd ha (not_lt.2 (mul_nonpos_of_nonpos_of_nonneg (not_le.1 hneg).le (norm_nonneg E)))
  rw [adjLev, LinearMap.smul_apply, map_smul, scalar_of_form th U hU _ h y hy, smul_smul, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (by positivity)]
  congr 1
  have : ((Nat.card P.H : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hP.ne'
  push_cast
  field_simp

section Main

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

def ptL (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (BW : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ)
    (f : Datum.WO (Vc D i) (Wc D i) → ℂ) {X : Type} [AddCommGroup X] [Module ℂ X]
    (u : X →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank) : X →ₗ[ℂ] (Datum.WO (Vc D i) (Wc D i) → ℂ) where
  toFun w := ptAt R i σ BW f (u w)
  map_add' w w' := by rw [map_add]; exact map_add _ _ _
  map_smul' a w := by rw [map_smul]; exact map_smul _ _ _

theorem ptL_apply (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (BW : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ)
    (f : Datum.WO (Vc D i) (Wc D i) → ℂ) {X : Type} [AddCommGroup X] [Module ℂ X]
    (u : X →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank) (w : X) : ptL R i σ BW f u w = ptAt R i σ BW f (u w) := rfl

variable {R} {F : Face D A} {i : Fin D.R.m} {t : T} {σ : D.what₂.LL →+* ℂ} {s : ℂ ≃+* ℂ} {P : LevelP R.Pg D.R.r ℂ}
    {cμ cη : (AE D)ˣ →* Circle} {m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ}
    {ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (Datum.WO (Vc D i) (Wc D i) → ℂ)}
    {BW : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ} {f₀ f : Datum.WO (Vc D i) (Wc D i) → ℂ}
    {c : CoefA (Vc D i)} {io : LowT (R.MW i σ) →ₗ[ℂ] c.W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank}
    (hd : IsLiftData R F i t σ s P cμ cη m ω BW f₀ f c io)
    {ν : Measure (GA D (Vc D i))} {𝓕 : Set (GA D (Vc D i))} (hν : IsMeasDef (Vc D i) (levV R i t P m) ν 𝓕)

end Main

end GlobalTheory.AdelicScalar

end
