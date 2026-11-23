import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.EStar

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil Formalism.BasicNotions Matrix
open UpperTheory.V UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob
open UpperTheory.V.W (Plc Lp)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem mem_dx_iff {K : Type} [Field K] {Δ : K} (g : GL (Fin 2) (Lsq K Δ)) :
    g ∈ DX Δ ↔ (g : Matrix (Fin 2) (Fin 2) (Lsq K Δ)).map star =
      !![0, -1; 1, 0] * (g : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) * !![0, 1; -1, 0] := by
  constructor
  · intro h
    exact congrArg Units.val h
  · intro h
    exact Units.ext h

private theorem conj_two {R : Type} [CommRing R] (a b c d : R) :
    (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) R) * !![a, b; c, d] * !![0, 1; -1, 0] = !![d, -c; -b, a] := by
  simp [Matrix.mul_fin_two]

private theorem dx_form {K : Type} [Field K] {Δ : K} (g : DX Δ) :
    ∃ a b : Lsq K Δ, mt g = !![a, b; -star b, star a] := by
  have h := (mem_dx_iff _).1 g.2
  obtain ⟨a, b, c, d, hm⟩ : ∃ a b c d, ((g : GL (Fin 2) (Lsq K Δ)) : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) = !![a, b; c, d] :=
    ⟨_, _, _, _, Matrix.eta_fin_two _⟩
  rw [hm, conj_two] at h
  have h00 := congrFun (congrFun h 0) 0
  have h01 := congrFun (congrFun h 0) 1
  simp at h00 h01
  refine ⟨a, b, ?_⟩
  show ((g : GL (Fin 2) (Lsq K Δ)) : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) = _
  rw [hm, h00, show c = -star b by rw [h01, neg_neg]]

theorem UpperTheory.V.Z.Sym.Dict.Br.suIff :
    ∀ (K : Type) [Field K] (Δ : K), (∀ g : DX Δ, star (mt g) * mt g = (mt g).det • (1 : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) ∧ star (mt g).det = (mt g).det) ∧ ∀ x : Matrix (Fin 2) (Fin 2) (Lsq K Δ), star x * x = 1 → x.det = 1 → ∃ g : DX Δ, mt g = x := by
  intro K _ Δ
  refine ⟨fun g => ?_, fun x hx hd => ?_⟩
  · obtain ⟨a, b, h⟩ := dx_form g
    rw [h, Matrix.det_fin_two_of]
    constructor
    · rw [Matrix.star_eq_conjTranspose, Matrix.one_fin_two]
      refine Matrix.ext fun i j => ?_
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
    · simp [mul_comm]
  · have hadj : star x = x.adjugate := by
      calc star x = star x * (x * x.adjugate) := by rw [Matrix.mul_adjugate, hd, one_smul, mul_one]
        _ = x.adjugate := by rw [← mul_assoc, hx, one_mul]
    let u : GL (Fin 2) (Lsq K Δ) :=
      ⟨x, x.adjugate, by rw [Matrix.mul_adjugate, hd, one_smul], by rw [Matrix.adjugate_mul, hd, one_smul]⟩
    have hu : u ∈ DX Δ := by
      refine (mem_dx_iff u).2 ?_
      show x.map star = !![0, -1; 1, 0] * x * !![0, 1; -1, 0]
      obtain ⟨a, b, c, d, rfl⟩ : ∃ a b c d, x = !![a, b; c, d] := ⟨_, _, _, _, Matrix.eta_fin_two _⟩
      rw [conj_two]
      rw [Matrix.star_eq_conjTranspose, Matrix.adjugate_fin_two_of] at hadj
      have h00 := congrFun (congrFun hadj 0) 0
      have h01 := congrFun (congrFun hadj 0) 1
      have h10 := congrFun (congrFun hadj 1) 0
      have h11 := congrFun (congrFun hadj 1) 1
      simp at h00 h01 h10 h11
      refine Matrix.ext fun i j => ?_
      fin_cases i <;> fin_cases j <;> simp [h00, h01, h10, h11]
    exact ⟨⟨u, hu⟩, rfl⟩
