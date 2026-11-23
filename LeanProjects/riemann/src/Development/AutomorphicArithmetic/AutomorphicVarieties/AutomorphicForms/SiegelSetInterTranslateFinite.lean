import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SiegelHeights.SiegelHeight

open NumberField Matrix GlobalTheory.CuspRep GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V UpperTheory.V.Fb

private theorem posIdele_finite_part_eq {K : Type} [Field K] [NumberField K] (ρ : ℝ) (hρ : 0 < ρ) :
    ((Reduction.posIdele (K := K) ρ hρ : GroundTheory.Global.IdeleGroup K) : AdeleRing (𝓞 K) K).2 = 1 := by
  unfold Reduction.posIdele
  refine Finset.prod_induction _ (fun x : GroundTheory.Global.IdeleGroup K => ((x : AdeleRing (𝓞 K) K)).2 = 1) ?_ ?_ ?_
  · intro a b ha hb
    calc ((a * b : GroundTheory.Global.IdeleGroup K) : AdeleRing (𝓞 K) K).2
        = ((a : AdeleRing (𝓞 K) K)).2 * ((b : AdeleRing (𝓞 K) K)).2 := rfl
      _ = 1 := by rw [ha, hb, one_mul]
  · rfl
  · intro w _
    rfl

private theorem finPart_diag_of_infinite_part_eq_one {K : Type} [Field K] [NumberField K] (n : ℕ)
    (d : Fin n → GroundTheory.Global.IdeleGroup K) (hd : ∀ i, ((d i : AdeleRing (𝓞 K) K)).2 = 1) :
    finPart (K := K) (Reduction.diagUnits n d) = 1 := by
  apply Units.ext
  funext i j
  change (((Reduction.diagUnits n d : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) (AdeleRing (𝓞 K) K)) i j).2 = (1 : Matrix (Fin n) (Fin n) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)) i j
  simp only [Reduction.diagUnits, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.one_apply, Matrix.diagonal_apply]
  split_ifs with h
  · subst h
    exact hd i
  · rfl

private theorem finPart_mul' {K : Type} [Field K] [NumberField K] {n : ℕ} (x y : AdelicGLn.AdelicGL K n) :
    finPart (x * y) = finPart x * finPart y := by
  show ((AdelicGLn.prodEquiv K n) (x * y)).2 = _
  rw [map_mul]
  rfl

theorem UpperTheory.siegelSet_inter_translate_finite :
    UpperTheory.V.Fb.SiegelFin := by
  intro K _ _ n ω hω t
  have hc : Continuous (fun g : AdelicGLn.AdelicGL K n => finPart g) :=
    continuous_snd.comp (AdelicGLn.prodEquiv K n).continuous
  refine ⟨(fun p : AdelicGLn.FiniteAdelicGL K n × AdelicGLn.FiniteAdelicGL K n => p.1 * p.2) ''
      ((finPart '' ω) ×ˢ (finPart '' ((Reduction.maxCompact : Subgroup (AdelicGLn.AdelicGL K n)) : Set (AdelicGLn.AdelicGL K n)))),
    ((hω.image hc).prod (Reduction.isCompact_maxCompact.image hc)).image continuous_mul, ?_⟩
  rintro g ⟨b, hb, a, ⟨r, hr, -, rfl⟩, k, hk, rfl⟩
  have ha := finPart_diag_of_infinite_part_eq_one n _ (fun i => posIdele_finite_part_eq (K := K) (r i) (hr i))
  refine ⟨(finPart b, finPart k), ⟨⟨b, hb, rfl⟩, ⟨k, hk, rfl⟩⟩, ?_⟩
  show finPart b * finPart k = _
  rw [finPart_mul', finPart_mul', ha, mul_one]
