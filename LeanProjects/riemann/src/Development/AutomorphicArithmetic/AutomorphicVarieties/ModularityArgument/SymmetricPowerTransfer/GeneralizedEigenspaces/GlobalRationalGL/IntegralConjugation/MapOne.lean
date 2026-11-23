import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.EStar
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.RatFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.MemDxIff

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil Formalism.BasicNotions Matrix
open UpperTheory.V UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob
open UpperTheory.V.W (Plc Lp)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem star_map {L : Type} [Field L] [NumberField L] [IsCMField L] (R : RingBr L)
    (x : Matrix (Fin 2) (Fin 2) (Lsq (Lp L) R.Δ)) :
    ((x.map R.e).map (IsCMField.complexConj L))ᵀ = (star x).map R.e := by
  ext i j
  simp [Matrix.star_apply, R.e_star]

private theorem map_mul' {L : Type} [Field L] [NumberField L] [IsCMField L] (R : RingBr L)
    (x y : Matrix (Fin 2) (Fin 2) (Lsq (Lp L) R.Δ)) :
    (x * y).map R.e = x.map R.e * y.map R.e :=
  map_mul (R.e : Lsq (Lp L) R.Δ →+* L).mapMatrix x y

private theorem map_one' {L : Type} [Field L] [NumberField L] [IsCMField L] (R : RingBr L) :
    (1 : Matrix (Fin 2) (Fin 2) (Lsq (Lp L) R.Δ)).map R.e = 1 :=
  map_one (R.e : Lsq (Lp L) R.Δ →+* L).mapMatrix

private theorem map_det' {L : Type} [Field L] [NumberField L] [IsCMField L] (R : RingBr L)
    (x : Matrix (Fin 2) (Fin 2) (Lsq (Lp L) R.Δ)) :
    (x.map R.e).det = R.e x.det :=
  ((R.e : Lsq (Lp L) R.Δ →+* L).map_det x).symm

theorem UpperTheory.V.Z.Sym.Dict.Br.rSEx :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (R : RingBr L), ∃ r : SU R.Δ ≃* ↥(ratU L 2 ⊓ SUA L), (∀ γ w, mL w (r γ : UA L 2) = (mt (γ : DX R.Δ)).map fun x => algebraMap L (Kw w) (R.e x)) ∧ ∀ γ (τ : L →+* ℂ), (cEmb τ (r γ : UA L 2) : Matrix (Fin 2) (Fin 2) ℂ) = (mt (γ : DX R.Δ)).map fun x => τ (R.e x) := by
  intro L _ _ _ R
  have hrf := ratFacts L 2
  obtain ⟨hs1, hs2⟩ := suIff (Lp L) R.Δ
  let E : GL (Fin 2) (Lsq (Lp L) R.Δ) →* GL (Fin 2) L :=
    GeneralLinearGroup.map (R.e : Lsq (Lp L) R.Δ →+* L)
  have hEc : ∀ g, (E g : Matrix (Fin 2) (Fin 2) L) = (g : Matrix (Fin 2) (Fin 2) _).map R.e := fun g => rfl
  have hdet1 : ∀ γ : SU R.Δ, (mt (γ : DX R.Δ)).det = 1 := by
    intro γ
    have h : GeneralLinearGroup.det ((γ : DX R.Δ) : GL (Fin 2) (Lsq (Lp L) R.Δ)) = 1 := γ.2
    simpa using congrArg Units.val h
  have hstar : ∀ γ : SU R.Δ, star (mt (γ : DX R.Δ)) * mt (γ : DX R.Δ) = 1 := by
    intro γ
    rw [(hs1 γ).1, hdet1, one_smul]
  have hdetE : ∀ γ : SU R.Δ, GeneralLinearGroup.det (E ((γ : DX R.Δ) : GL (Fin 2) (Lsq (Lp L) R.Δ))) = 1 := by
    intro γ
    apply Units.ext
    have : (E ((γ : DX R.Δ) : GL (Fin 2) (Lsq (Lp L) R.Δ)) : Matrix (Fin 2) (Fin 2) L).det = 1 := by
      rw [hEc, map_det', hdet1, map_one]
    simpa using this
  have hmem : ∀ γ : SU R.Δ, ratGL L 2 (E ((γ : DX R.Δ) : GL (Fin 2) (Lsq (Lp L) R.Δ))) ∈ UA L 2 := by
    intro γ
    rw [(hrf _).1, hEc, star_map, ← map_mul', hstar, map_one']
  let φ1 : SU R.Δ →* UA L 2 :=
    ((ratGL L 2).comp (E.comp ((DX R.Δ).subtype.comp (SU R.Δ).subtype))).codRestrict (UA L 2) hmem
  have hφ1 : ∀ γ, ((φ1 γ : UA L 2) : GlobalTheory.CuspRep.GA L 2) = ratGL L 2 (E ((γ : DX R.Δ) : GL (Fin 2) (Lsq (Lp L) R.Δ))) := fun _ => rfl
  have hmem2 : ∀ γ, φ1 γ ∈ ratU L 2 ⊓ SUA L := by
    intro γ
    refine ⟨?_, ?_⟩
    · exact Subgroup.mem_subgroupOf.2 ⟨_, rfl⟩
    · show GeneralLinearGroup.det ((φ1 γ : UA L 2) : GlobalTheory.CuspRep.GA L 2) = 1
      rw [hφ1]
      exact (((hrf _).2.2 (hmem γ)).2.2).2 (hdetE γ)
  let φ2 : SU R.Δ →* ↥(ratU L 2 ⊓ SUA L) := φ1.codRestrict _ hmem2
  have hinj : Function.Injective φ2 := by
    intro a b hab
    have h1 : ((φ1 a : UA L 2) : GlobalTheory.CuspRep.GA L 2) = ((φ1 b : UA L 2) : GlobalTheory.CuspRep.GA L 2) :=
      congrArg (fun x : ↥(ratU L 2 ⊓ SUA L) => ((x : UA L 2) : GlobalTheory.CuspRep.GA L 2)) hab
    rw [hφ1, hφ1] at h1
    have h2 := (hrf (E 1)).2.1 h1
    have h3 : mt (a : DX R.Δ) = mt (b : DX R.Δ) := by
      have h4 := congrArg (fun g : GL (Fin 2) L => (g : Matrix (Fin 2) (Fin 2) L)) h2
      simp only [hEc] at h4
      exact Matrix.ext fun i j => R.e.injective (congrFun (congrFun h4 i) j)
    exact Subtype.ext (Subtype.ext (Units.ext h3))
  have hsurj : Function.Surjective φ2 := by
    rintro ⟨x, hx1, hx2⟩
    obtain ⟨g, hg⟩ := Subgroup.mem_subgroupOf.1 hx1
    have hgU : ratGL L 2 g ∈ UA L 2 := hg ▸ x.2
    have hdx : GeneralLinearGroup.det ((x : UA L 2) : GlobalTheory.CuspRep.GA L 2) = 1 := hx2
    have hdg : GeneralLinearGroup.det g = 1 := by
      apply ((hrf g).2.2 hgU).2.2.1
      rw [hg]; exact hdx
    have hconj := ((hrf g).1).1 hgU
    let m : Matrix (Fin 2) (Fin 2) (Lsq (Lp L) R.Δ) := (g : Matrix (Fin 2) (Fin 2) L).map R.e.symm
    have hm : m.map R.e = g := by
      ext i j; simp [m]
    have hms : star m * m = 1 := by
      have h1 : (star m * m).map R.e = (1 : Matrix (Fin 2) (Fin 2) (Lsq (Lp L) R.Δ)).map R.e := by
        rw [map_mul', ← star_map, hm, hconj, map_one']
      exact Matrix.ext fun i j => R.e.injective (congrFun (congrFun h1 i) j)
    have hmd : m.det = 1 := by
      apply R.e.injective
      rw [← map_det', hm, map_one]
      simpa using congrArg Units.val hdg
    obtain ⟨h, hh⟩ := hs2 m hms hmd
    have hSU : h ∈ SU R.Δ := by
      show GeneralLinearGroup.det (h : GL (Fin 2) (Lsq (Lp L) R.Δ)) = 1
      apply Units.ext
      have : (mt h).det = 1 := hh ▸ hmd
      simpa using this
    refine ⟨⟨h, hSU⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    show ratGL L 2 (E (h : GL (Fin 2) (Lsq (Lp L) R.Δ))) = _
    rw [← hg]
    congr 1
    apply Units.ext
    rw [hEc]
    show (mt h).map R.e = _
    rw [hh, hm]
  refine ⟨MulEquiv.ofBijective φ2 ⟨hinj, hsurj⟩, ?_, ?_⟩
  · intro γ w
    have := ((hrf _).2.2 (hmem γ)).1 w
    exact this.trans (by rw [hEc]; ext i j; rfl)
  · intro γ τ
    have := ((hrf _).2.2 (hmem γ)).2.1 τ
    exact this.trans (by rw [hEc]; ext i j; rfl)
