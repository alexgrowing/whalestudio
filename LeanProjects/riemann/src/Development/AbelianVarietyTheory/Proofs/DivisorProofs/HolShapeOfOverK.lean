import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadingsExistRow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPsiOfOverK
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicShapeIntegralWeightGoodEmbedding
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HolomorphicDiscreteSeriesLowestKTypeSmoothIrredu
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanEqTopOfTie

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace
open GlobalTheory.GalLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GalLift.ProjLift

theorem exists_factor {A B X I : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B] [AddCommGroup X] [Module ℂ X]
    (L₁ : A →ₗ[ℂ] X) (L₂ : B →ₗ[ℂ] X) (j : I → B) (hj : Submodule.span ℂ (Set.range j) = ⊤) (h : ∀ x, ∃ t, L₁ t = L₂ (j x)) :
    ∃ φ : B →ₗ[ℂ] A, ∀ y, L₁ (φ y) = L₂ y := by
  have h1 : ∀ y, L₂ y ∈ LinearMap.range L₁ := fun y =>
    (Submodule.span_le (p := (LinearMap.range L₁).comap L₂)).2 (by rintro _ ⟨x, rfl⟩; exact h x) (hj.ge Submodule.mem_top)
  obtain ⟨φ, hφ⟩ := Module.projective_lifting_property L₁.rangeRestrict (L₂.codRestrict _ h1) L₁.surjective_rangeRestrict
  exact ⟨φ, fun y => congrArg Subtype.val (LinearMap.congr_fun hφ y)⟩

section Low

open Matrix Formalism.MainNotions.S GlobalTheory.DefLift

variable {D : D7}

open Classical in

theorem eq_on_low {θ : InfFam D} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S} (h1 : LowSm M)
    (h2 : GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.LowIrr M) {J : Set (GA D V)} {χ : GA D V → ℂ} {T : MMap M} (hT : T ∈ Mult θ M J χ)
    {U : GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicParabolicSmoothFunctions.KMap M} (hU : KEquiv θ M U) (e : ∀ τ, lowT M τ) (he : ∀ τ, e τ ≠ 0)
    (h : T (fun τ => (e τ : M.sm τ)) = U e) (v : ∀ τ, lowT M τ) : T (fun τ => (v τ : M.sm τ)) = U v := by
  have hT' : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ (v : M.Vec) (w : M.sm τ),
      (w : M.H τ) = M.rep τ g (v τ) → T (Function.update v τ w) = rTr V (atTau θ V τ g) (T v) := by
    intro τ g hg v w hw
    clear h
    induction hT using Submodule.span_induction with
    | mem T hT => exact hT.equiv τ g hg v w hw
    | zero => rfl
    | add x y _ _ hx hy => exact (congrArg₂ (· + ·) hx hy).trans rfl
    | smul a x _ hx => exact (congrArg (a • ·) hx).trans rfl
  have key := mem_of_translates h1 h2 (T.compLinearMap (fun τ => (lowT M τ).subtype) - U) ⊥ e he
    (by simpa [sub_eq_zero] using h) (fun τ k hk v u hu hv => ?_) v
  · simpa [sub_eq_zero] using key
  · have hv' : T (fun τ => (v τ : M.sm τ)) = U v := by simpa [sub_eq_zero] using hv
    have hd : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
    have hg : (M.fr τ)⁻¹ * k * M.fr τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) := by
      have hk' : kᴴ * Formalism.REAL.Jm (M.ε τ) * k = Formalism.REAL.Jm (M.ε τ) := kset_uj hk
      have e1 : ((M.fr τ)⁻¹)ᴴ * (M.fr τ)ᴴ = 1 := by
        rw [← conjTranspose_mul, mul_nonsing_inv _ hd, conjTranspose_one]
      change ((M.fr τ)⁻¹ * k * M.fr τ)ᴴ * gramAt D V τ * ((M.fr τ)⁻¹ * k * M.fr τ) = gramAt D V τ
      calc ((M.fr τ)⁻¹ * k * M.fr τ)ᴴ * gramAt D V τ * ((M.fr τ)⁻¹ * k * M.fr τ)
          = (M.fr τ)ᴴ * (kᴴ * (((M.fr τ)⁻¹)ᴴ * (M.fr τ)ᴴ) * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * (M.fr τ)⁻¹) * k) *
              M.fr τ := by
            rw [← M.fr_gram τ]; simp only [conjTranspose_mul, Matrix.mul_assoc]
        _ = gramAt D V τ := by rw [e1, mul_nonsing_inv _ hd, Matrix.mul_one, Matrix.mul_one, hk', M.fr_gram]
    have e2 : M.fr τ * ((M.fr τ)⁻¹ * k * M.fr τ) * (M.fr τ)⁻¹ = k := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_nonsing_inv _ hd, Matrix.one_mul, Matrix.mul_assoc,
        mul_nonsing_inv _ hd, Matrix.mul_one]
    have e3 := hT' τ _ hg (fun τ => (v τ : M.sm τ)) (u : M.sm τ) (by
      rw [hu, DSModel.rep, e2])
    have e4 : (fun ρ => ((Function.update v τ u ρ : lowT M ρ) : M.sm ρ)) =
        Function.update (fun ρ => (v ρ : M.sm ρ)) τ (u : M.sm τ) :=
      funext fun ρ => Function.apply_update (fun ρ (y : lowT M ρ) => (y : M.sm ρ)) v τ u ρ
    have e5 : T (fun ρ => ((Function.update v τ u ρ : lowT M ρ) : M.sm ρ)) = U (Function.update v τ u) := by
      rw [e4, e3, hv', hU τ k hk v u hu]
    simpa [sub_eq_zero] using e5

theorem kEquiv_thetaP {θ : InfFam D} {V W : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel W S} {c : CoefA V}
    {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {pt : PolF D W.rank V.rank → (WO V W → ℂ)}
    {Δ : PolF D W.rank V.rank} {io : LowT M →ₗ[ℂ] c.W →ₗ[ℂ] PolF D W.rank V.rank} (hio : IsIoW θ M c ω pt Δ io)
    {ν : Measure (GA D V)} {𝓕 : Set (GA D V)} {B : Submodule ℂ (GA D V → c.W)}
    {thP : B →ₗ[ℂ] (LowT M →ₗ[ℂ] (GA D W → ℂ))}
    (hth : Lift.IsThetaP ν 𝓕 (fun g h φ => thetaKO ω h g φ) pt io B thP) (y : B) :
    KEquiv θ M ((thP y).compMultilinearMap (PiTensorProduct.tprod ℂ)) := by
  intro τ k hk v u hu
  have hmul : ∀ h g k φ, thetaKO ω h (g * k) φ = thetaKO ω h g (ω (1, k) φ) := fun h g k φ => by
    unfold thetaKO
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
  funext g
  simp only [LinearMap.compMultilinearMap_apply, rTr, hth.eq, Lift.thetaPInt, hmul, hio.2.1 τ k hk v u hu]

theorem exists_lift {θ : InfFam D} {W : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel W S} (h1 : LowSm M)
    (h2 : GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.LowIrr M) {J : Set (GA D W)} {χ : GA D W → ℂ} {A B I : Type} [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] (e : A →ₗ[ℂ] MMap M) (he : ∀ t, e t ∈ Mult θ M J χ)
    (L : B →ₗ[ℂ] (LowT M →ₗ[ℂ] (GA D W → ℂ)))
    (hL : ∀ y, KEquiv θ M ((L y).compMultilinearMap (PiTensorProduct.tprod ℂ))) (j : I → B)
    (hj : Submodule.span ℂ (Set.range j) = ⊤) (v : ∀ τ, lowT M τ) (hv : ∀ τ, v τ ≠ 0)
    (h : ∀ x, ∃ t, e t (fun τ => (v τ : M.sm τ)) = L (j x) (PiTensorProduct.tprod ℂ v)) :
    ∃ φ : B →ₗ[ℂ] A, ∀ y (u : ∀ τ, lowT M τ), e (φ y) (fun τ => (u τ : M.sm τ)) = L y (PiTensorProduct.tprod ℂ u) := by
  let L₁ : A →ₗ[ℂ] ((∀ τ, lowT M τ) → GA D W → ℂ) :=
    { toFun := fun t u => e t (fun τ => (u τ : M.sm τ))
      map_add' := fun a b => by rw [map_add]; rfl
      map_smul' := fun a b => by rw [map_smul]; rfl }
  let L₂ : B →ₗ[ℂ] ((∀ τ, lowT M τ) → GA D W → ℂ) :=
    { toFun := fun y u => L y (PiTensorProduct.tprod ℂ u)
      map_add' := fun a b => by rw [map_add]; rfl
      map_smul' := fun a b => by rw [map_smul]; rfl }
  obtain ⟨φ, hφ⟩ := exists_factor L₁ L₂ j hj fun x => (h x).imp fun t ht =>
    funext fun u => eq_on_low h1 h2 (he t) (hL (j x)) v hv ht u
  exact ⟨φ, fun y u => congrFun (hφ y) u⟩

end Low

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem holShape_of_overK (R : RealDat D A Ks) (i : Fin D.R.m) {σ : D.what₂.LL →+* ℂ} (hσ : OverK σ) :
    GlobalTheory.HolDict.HolShape (R.MW i σ) := by
  have hs : ∀ ρ, (Wc D i).sig (tauE D ρ) = D.R.sigW ((i : ℕ) + 1) := fun ρ => D.sp.W_sigval _ (inR i).1 (inR i).2 _
  have hr : (D.R.sigW ((i : ℕ) + 1)).1 + (D.R.sigW ((i : ℕ) + 1)).2 = (Wc D i).rank := by
    have := D.R.m_add_three_le_k
    have hi := i.2
    rw [rank_Wc i]
    simp only [Ranks.sigW, Ranks.r]
    omega
  have key : ∀ ρ a, (R.MW i σ).lam ρ a = (Formalism.L2.NTheta.lamAt (D.hc (lab σ ρ)) a : ℝ) ∧
      (R.MW i σ).ε ρ a = decide ((a : ℕ) < (D.R.sigW ((i : ℕ) + 1)).1) := fun ρ a => by
    have he := (R.MW i σ).enum ρ
    unfold Links.parAt at he
    rw [if_pos (((labels_overK σ).1 hσ).2 ρ)] at he
    rw [← hs ρ]
    exact GlobalTheory.HolDict.isEnum_holPar_kapW _ (rank_Wc i) (by rw [hs ρ]; exact hr) he a
  have hc : ∀ ρ, Formalism.QuantumDeterminants.IsHCParam ((R.MW i σ).lam ρ) := fun ρ => by
    refine ⟨((R.MW i σ).enum ρ).1, fun a => ?_⟩
    obtain ⟨z, hz⟩ := Formalism.L2.NTheta.lamAt_int (D.hc (lab σ ρ)) a
    obtain ⟨s, hs'⟩ := Formalism.L2.NTheta.odd_r D.R
    refine ⟨z - s, ?_⟩
    have hn : (((Wc D i).rank : ℕ) : ℝ) = 2 * s + 1 := by rw [rank_Wc i, hs']; push_cast; rfl
    rw [(key ρ a).1, hz, hn]
    push_cast
    ring
  exact fun ρ => ⟨hc ρ, _, by omega, fun a => (key ρ a).2⟩

theorem proj_apply (R : RealDat D A Ks) (hg : R.models_gW) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (t : (R.HW i σ).H)
    (v : (R.MW i σ).Vec) :
    (R.HW i σ).e ((∑ g, RealDat.eC (A := A) σ g • R.gW i σ g) t) v = R.eWf i σ ((R.HW i σ).e t v) := by
  simp only [RealDat.eWf, gaL, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, MultilinearMap.sum_apply,
    MultilinearMap.smul_apply, hg i σ, postOn_apply]
  rfl

set_option maxHeartbeats 1600000 in

theorem exists_isProjOf : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.Char F → ∀ (i : Fin D.R.m), ∀ gramR c0R c0L, Comparison₂ R gramR c0R c0L → ∀ (σ : D.what₂.LL →+* ℂ), OverK σ → ∀ (μ' η' : (AE D)ˣ →* Circle) (c : CoefA (Vc D i)) (c₁ : VsV D i D.what₂.LL →ₛₗ[σ] c.W) (H : HMod (Bridge.Gf (Vc D i) → c.W)) (j : A.fam.amb.FL i A.μ0 →ₛₗ[σ] H.H), IsConjForms R i σ (c0L i) c c₁ H j → ∀ (ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ)) (f₀ f : WO (Vc D i) (Wc D i) → ℂ) (B : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ) (io : LowT (R.MW i σ) →ₗ[ℂ] c.W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank) (thP : LinearMap.range (c.ext ∘ₗ H.e) →ₗ[ℂ] (LowT (R.MW i σ) →ₗ[ℂ] (GA D (Wc D i) → ℂ))), LiftData R i σ μ' η' c H ω f₀ f B io thP → ∀ v : ∀ ρ, lowT (R.MW i σ) ρ, IsExtVec (R.MW i σ) (fun ρ => v ρ) → (∀ x, ∃ t : (R.HW i σ).H, (R.HW i σ).e t (fun ρ => v ρ) = thP ((c.ext ∘ₗ H.e).rangeRestrict (j x)) (PiTensorProduct.tprod ℂ v)) → ∃ th, IsProjOf R i σ thP th := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC i gramR c0R c0L hT σ hσ μ' η' c c₁ H j hj ω f₀ f B io thP hL v hv h
  have hspan := GlobalTheory.ConjSpan.span_conjForms R hC.models.jV gramR c0R c0L hT i σ c c₁ H j hj
  have hlow := GlobalTheory.HolLowOnce.lowSm_and_lowIrr D _ _ _ (holShape_of_overK R i hσ)
  have he : ∀ τ, v τ ≠ 0 := fun τ h0 => by
    have := (hv τ).1
    simp [h0] at this
  have hex := exists_lift hlow.1 hlow.2 (R.HW i σ).e
    (fun t => (hC.models.HW i σ).2.1.le (LinearMap.mem_range_self _ t)) (thP ∘ₗ (c.ext ∘ₗ H.e).rangeRestrict)
    (fun y => kEquiv_thetaP hL.2.2.1 hL.2.2.2 _) j hspan v he h
  obtain ⟨φ, hφ⟩ := hex
  exact ⟨(∑ g, RealDat.eC (A := A) σ g • R.gW i σ g) ∘ₗ φ, fun x u =>
    (proj_apply R hC.models.gW i σ (φ x) _).trans (congrArg (R.eWf i σ) (hφ x u))⟩

end GlobalTheory.GalLift.ProjLift

end
