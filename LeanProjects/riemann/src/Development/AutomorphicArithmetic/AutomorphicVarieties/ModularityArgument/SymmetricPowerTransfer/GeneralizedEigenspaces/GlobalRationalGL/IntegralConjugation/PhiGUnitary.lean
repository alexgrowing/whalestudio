import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.EStar
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.RatFacts

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil Formalism.BasicNotions Matrix
open UpperTheory.V UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob
open UpperTheory.V.W (Plc Lp)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private noncomputable def phiG {L : Type} [Field L] [NumberField L] [IsCMField L] (R : RingBr L) :
    U3 R.Δ →* GL (Fin 3) L :=
  (GeneralLinearGroup.map (R.e : Lsq (Lp L) R.Δ →+* L)).comp Unitary.toUnits

private theorem phiG_coe {L : Type} [Field L] [NumberField L] [IsCMField L] (R : RingBr L) (γ : U3 R.Δ) :
    (phiG R γ : Matrix (Fin 3) (Fin 3) L) = (γ : Matrix (Fin 3) (Fin 3) _).map fun x => R.e x := rfl

private theorem phiG_unitary {L : Type} [Field L] [NumberField L] [IsCMField L] (R : RingBr L) (γ : U3 R.Δ) :
    ((phiG R γ : Matrix (Fin 3) (Fin 3) L).map (IsCMField.complexConj L))ᵀ * (phiG R γ : Matrix (Fin 3) (Fin 3) L) = 1 := by
  have h : star (γ : Matrix (Fin 3) (Fin 3) (Lsq (Lp L) R.Δ)) * (γ : Matrix (Fin 3) (Fin 3) (Lsq (Lp L) R.Δ)) = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp γ.2
  have e1 : ((phiG R γ : Matrix (Fin 3) (Fin 3) L).map (IsCMField.complexConj L))ᵀ =
      (star (γ : Matrix (Fin 3) (Fin 3) (Lsq (Lp L) R.Δ))).map fun x => R.e x := by
    ext i j
    simp [phiG_coe, Matrix.star_apply, R.e_star]
  rw [e1, phiG_coe]
  have e2 := congrArg (fun m => m.map (R.e : Lsq (Lp L) R.Δ →+* L)) h
  simp only [Matrix.map_mul] at e2
  simpa using e2

theorem UpperTheory.V.Z.Sym.Dict.Br.rGEx :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (R : RingBr L), ∃ r : U3 R.Δ ≃* ratU L 3, (∀ γ w, mL w (r γ : UA L 3) = (γ : Matrix (Fin 3) (Fin 3) _).map fun x => algebraMap L (Kw w) (R.e x)) ∧ ∀ γ (τ : L →+* ℂ), (cEmb τ (r γ : UA L 3) : Matrix (Fin 3) (Fin 3) ℂ) = (γ : Matrix (Fin 3) (Fin 3) _).map fun x => τ (R.e x) := by
  intro L _ _ _ R
  have hU : ∀ γ : U3 R.Δ, ratGL L 3 (phiG R γ) ∈ UA L 3 := fun γ =>
    (ratFacts L 3 (phiG R γ)).1.mpr (phiG_unitary R γ)
  let f : U3 R.Δ →* ratU L 3 :=
    { toFun := fun γ => ⟨⟨ratGL L 3 (phiG R γ), hU γ⟩, Subgroup.mem_subgroupOf.mpr ⟨phiG R γ, rfl⟩⟩
      map_one' := by
        apply Subtype.ext; apply Subtype.ext
        simp
      map_mul' := fun a b => by
        apply Subtype.ext; apply Subtype.ext
        simp }
  have hinj : Function.Injective f := by
    intro a b hab
    have h1 : ratGL L 3 (phiG R a) = ratGL L 3 (phiG R b) := congrArg Subtype.val (congrArg Subtype.val hab)
    have h2 := (ratFacts L 3 1).2.1 h1
    have h3 : (phiG R a : Matrix (Fin 3) (Fin 3) L) = phiG R b := congrArg Units.val h2
    apply Subtype.ext
    exact Matrix.ext fun i j => R.e.injective (congrFun (congrFun h3 i) j)
  have hsurj : Function.Surjective f := by
    rintro ⟨⟨x, hx⟩, hr⟩
    obtain ⟨g, hg⟩ := Subgroup.mem_subgroupOf.mp hr
    change ratGL L 3 g = x at hg
    subst hg
    have hc := (ratFacts L 3 g).1.mp hx
    let M : Matrix (Fin 3) (Fin 3) (Lsq (Lp L) R.Δ) := (g : Matrix (Fin 3) (Fin 3) L).map fun x => R.e.symm x
    have hM : star M * M = 1 := by
      have e1 : star M = (((g : Matrix (Fin 3) (Fin 3) L).map (IsCMField.complexConj L))ᵀ).map fun x => R.e.symm x := by
        refine Matrix.ext fun i j => R.e.injective ?_
        simp [M, Matrix.star_apply, R.e_star]
      have e2 := congrArg (fun m => m.map (R.e.symm : L →+* Lsq (Lp L) R.Δ)) hc
      simp only [Matrix.map_mul] at e2
      rw [e1]
      simpa [M] using e2
    refine ⟨⟨M, Matrix.mem_unitaryGroup_iff'.mpr hM⟩, ?_⟩
    have hp : phiG R ⟨M, Matrix.mem_unitaryGroup_iff'.mpr hM⟩ = g := by
      apply Units.ext
      ext i j
      simp [phiG_coe, M]
    apply Subtype.ext; apply Subtype.ext
    exact congrArg (ratGL L 3) hp
  refine ⟨MulEquiv.ofBijective f ⟨hinj, hsurj⟩, ?_, ?_⟩
  · intro γ w
    exact ((ratFacts L 3 (phiG R γ)).2.2 (hU γ)).1 w
  · intro γ τ
    exact ((ratFacts L 3 (phiG R γ)).2.2 (hU γ)).2.1 τ
