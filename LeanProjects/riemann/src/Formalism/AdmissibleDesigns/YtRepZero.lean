import Formalism.AdmissibleDesigns.ContOfInjY

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Classical

namespace Formalism.MainNotions.N.K.TBa

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Formalism.WeaklyAdmissibleFiltrations Formalism.NG Formalism.RepresentationBoundsCohomology.BR
open Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N.K.TB Formalism.MainNotions.N.KHf

section Mk

variable {O : Type} [CommRing O] [IsDomain O] {LL : Type} [Field LL] [TopologicalSpace LL] [IsTopologicalRing LL]
  {e : FractionRing O ≃+* LL} {Ow : Type} [CommRing Ow] [Algebra Ow LL] {eO : O ≃+* Ow}
  (heO : ∀ a : O, algebraMap Ow LL (eO a) = e (algebraMap O (FractionRing O) a))
  {Γ G : Type} [Group Γ] [Group G] [TopologicalSpace G] (ι : G →* Γ)
  {N : Type} [AddCommGroup N] [Module O N] [Module.Finite O N] [Module.Free O (N × O)] [NoZeroSMulDivisors O (N × O)]
  (Qp : Type) [Field Qp] [Algebra Qp LL]
  (ρM : Representation O Γ (N × O)) (h2 : ∀ g m, (ρM g m).2 = m.2)
  [FiniteDimensional LL (TrV e (MK (O := O) (N × O)))]
  (hcont : ∀ x, Continuous fun g => repL e (locRep ρM) ι g x)

def mkYt : YtLat (G := G) (Qp := Qp) LL Ow where
  V := TrV e (MK (O := O) (N × O))
  ρ := repL e (locRep ρM) ι
  L := latY heO ι ρM
  cont := hcont
  p := pY e N
  p_inv g v := pY_inv ι ρM h2 g v
  p_int v hv := pY_int heO v hv
  e₀ := trY e (mkK (O := O) ((0 : N), (1 : O)))
  e₀_mem := ⟨_, rfl⟩
  p_e₀ := by rw [pY_mk]; simp

end Mk

section GenY

variable {O : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O]
  {A T' GG : Type} [Ring A] [Algebra O A] [CommRing T'] [Algebra T' A] [Group GG]
  (r : GG →* A) (χ : GG →* T'ˣ) (E : A)

theorem nzsdY [NoZeroSMulDivisors O A] : NoZeroSMulDivisors O ↥(Ymod r χ E) :=
  Function.Injective.noZeroSMulDivisors (fun y : ↥(Ymod r χ E) => (y : A)) Subtype.val_injective rfl
    (fun _ _ => rfl)

theorem finY [Module.Finite O A] : Module.Finite O ↥(Ymod r χ E) := by
  haveI : IsNoetherian O A := isNoetherian_of_isNoetherianRing_of_finite O A
  let f : ↥(Ymod r χ E) →ₗ[O] A :=
    { toFun := fun y => (y : A), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  exact Module.Finite.of_injective f Subtype.val_injective

theorem freeY [Module.Finite O A] [NoZeroSMulDivisors O A] : Module.Free O (↥(Ymod r χ E) × O) := by
  haveI := finY (O := O) r χ E
  haveI := nzsdY (O := O) r χ E
  haveI := nzsd_prod (O := O) (N := ↥(Ymod r χ E))
  exact Module.free_of_finite_type_torsion_free'

theorem ytRep_zero (g : GG) (y : ↥(Ymod r χ E)) : ytRep O r χ E g (y, 0) = (uElt r χ g • y, 0) :=
  Prod.ext (by
    show uElt r χ g • y + (0 : O) • yY r χ E g = _
    rw [zero_smul, add_zero]) rfl

theorem ytRep_e (g : GG) : ytRep O r χ E g (0, 1) = (yY r χ E g, 1) :=
  Prod.ext (by
    show uElt r χ g • (0 : ↥(Ymod r χ E)) + (1 : O) • yY r χ E g = _
    rw [smul_zero, one_smul, zero_add]) rfl

end GenY

section GenT

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [IsTopologicalRing LL]
    {Ow : Type} [CommRing Ow] [Algebra Ow LL]
    {O : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O]
    {e : FractionRing O ≃+* LL} {eO : O ≃+* Ow}
    (heO : ∀ a : O, algebraMap Ow LL (eO a) = e (algebraMap O (FractionRing O) a))
    {A T' GG : Type} [Ring A] [Algebra O A] [CommRing T'] [Algebra T' A] [Group GG]
    (r : GG →* A) (χ : GG →* T'ˣ) (E : A) (Dw : Subgroup GG) (eG : ↥Dw ≃* G)

abbrev ytVG : Representation LL G (TrV e (MK (O := O) (↥(Ymod r χ E) × O))) :=
  repL e (locRep (resRep (ytRep O r χ E) Dw)) eG.symm.toMonoidHom

variable (Qp) in

def ytG [Module.Finite O A] [NoZeroSMulDivisors O A] (hfd : FiniteDimensional LL (TrV e (MK (O := O) (↥(Ymod r χ E) × O))))
    (hcont : ∀ x, Continuous fun g => ytVG (e := e) r χ E Dw eG g x) : YtLat (G := G) (Qp := Qp) LL Ow :=
  haveI := finY (O := O) r χ E
  haveI := freeY (O := O) r χ E
  haveI := nzsdY (O := O) r χ E
  haveI := nzsd_prod (O := O) (N := ↥(Ymod r χ E))
  mkYt heO eG.symm.toMonoidHom Qp (resRep (ytRep O r χ E) Dw) (fun _ _ => rfl) hcont

theorem ytG_ρ [Module.Finite O A] [NoZeroSMulDivisors O A] (hfd : FiniteDimensional LL (TrV e (MK (O := O) (↥(Ymod r χ E) × O))))
    (hcont : ∀ x, Continuous fun g => ytVG (e := e) r χ E Dw eG g x) :
    (ytG Qp heO r χ E Dw eG hfd hcont).ρ = ytVG (e := e) r χ E Dw eG := rfl

theorem ytG_psi [Module.Finite O A] [NoZeroSMulDivisors O A] (hfd : FiniteDimensional LL (TrV e (MK (O := O) (↥(Ymod r χ E) × O))))
    (hcont : ∀ x, Continuous fun g => ytVG (e := e) r χ E Dw eG g x)
    {M : Type} [AddCommGroup M] [Module A M] [Module O M] [SMulCommClass A O M] {e' : ℕ}
    (Cd : CoefDict PD LL Ow eO M r χ Dw eG e') :
    PsiExt eO r χ E Dw eG (ytG Qp heO r χ E Dw eG hfd hcont) Cd := by
  intro ψ hψe
  haveI := nzsdY (O := O) r χ E
  obtain ⟨φ, hφ⟩ := ext_of_baer (e := e) (eO := eO) heO (N := ↥(Ymod r χ E)) (Q := Cd.Ce.V ⧸ Cd.Ce.L.T)
    (div_quot heO Cd.Ce.L.T) (Cd.u.toAddMonoidHom.comp ψ.toAddMonoidHom)
    (fun a n => by
      show Cd.u (ψ (a • n)) = _
      rw [ψ.map_smul, Cd.u_smul]
      rfl)
  refine ⟨φ, ?_, ?_⟩
  · intro g y hy hp
    obtain ⟨⟨n, c0⟩, rfl⟩ := hy
    have hc0 : c0 = 0 := pY_zero (m := (n, c0)) hp
    subst hc0
    show φ (trY e (locRep (resRep (ytRep O r χ E) Dw) (eG.symm g) (mkK (n, (0 : O))))) =
      actD Cd.Ce.L g (φ (trY e (mkK (n, (0 : O)))))
    rw [locRep_mkK]
    show φ (trY e (mkK (ytRep O r χ E ((eG.symm g : ↥Dw) : GG) (n, (0 : O))))) = _
    rw [ytRep_zero, hφ, hφ]
    show Cd.u (ψ _) = _
    rw [hψe _ (eG.symm g).2 n, Cd.u_act (eG.symm g) (ψ n), MulEquiv.apply_symm_apply]
    rfl
  · intro γ
    show φ (trY e (locRep (resRep (ytRep O r χ E) Dw) (eG.symm (eG γ)) (mkK ((0 : ↥(Ymod r χ E)), (1 : O)))) -
        trY e (mkK ((0 : ↥(Ymod r χ E)), (1 : O)))) = _
    rw [MulEquiv.symm_apply_apply, locRep_mkK]
    show φ (trY e (mkK (ytRep O r χ E (γ : GG) ((0 : ↥(Ymod r χ E)), (1 : O)))) -
        trY e (mkK ((0 : ↥(Ymod r χ E)), (1 : O)))) = _
    rw [ytRep_e]
    have h3 : (mkK (O := O) (yY r χ E (γ : GG), (1 : O)) - mkK (O := O) ((0 : ↥(Ymod r χ E)), (1 : O)) :
          MK (O := O) (↥(Ymod r χ E) × O)) = mkK (O := O) (yY r χ E (γ : GG), (0 : O)) := by
      rw [← map_sub]
      congr 1
      ext <;> simp
    exact (congrArg φ h3).trans (hφ _)

theorem ytG_crys [Module.Finite O A] [NoZeroSMulDivisors O A] (hfd : FiniteDimensional LL (TrV e (MK (O := O) (↥(Ymod r χ E) × O))))
    (hcont : ∀ x, Continuous fun g => ytVG (e := e) r χ E Dw eG g x)
    (hF : TruncatedSeriesCountingIdentities.FontaineAt PD LL Ow) {ιx : Type} {k : ℕ} (Ms : ιx → G →* Matrix (Fin k) (Fin k) LL)
    (hMc : ∀ x, Continuous (Ms x)) (hMs : ∀ x, IsCrys PD (matRep (Ms x))) {m : ℕ} (xs : Fin m → ιx)
    (φ : TrV e (MK (O := O) (↥(Ymod r χ E) × O)) →ₗ[LL] (Fin m → Fin k → LL)) (hφ : Function.Injective φ)
    (heq : ∀ g v, φ (ytVG (e := e) r χ E Dw eG g v) = fun a => (Ms (xs a) g).mulVec (φ v a)) :
    IsCrys PD (ytG Qp heO r χ E Dw eG hfd hcont).ρ ∧
      ∀ τ a, IsJumpV PD (ytG Qp heO r χ E Dw eG hfd hcont).ρ τ a → ∃ x, IsJumpV PD (matRep (Ms x)) τ a := by
  let Ag : GRep G Qp LL Ow :=
    { V := TrV e (MK (O := O) (↥(Ymod r χ E) × O)), ρ := ytVG (e := e) r χ E Dw eG, cont := hcont }
  exact crys_of_inj PD Ms hF hMc hMs Ag xs φ hφ heq

end GenT

end Formalism.MainNotions.N.K.TBa

end
