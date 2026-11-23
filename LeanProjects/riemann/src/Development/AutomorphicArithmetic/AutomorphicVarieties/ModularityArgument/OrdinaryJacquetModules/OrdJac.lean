import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.OrdinaryJacquetModules.CoreOrdAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.ExistsNil

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC GlobalTheory.PRep UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z UpperTheory.V.Z.Ord

open private UpperTheory.V.Hi.OrdB.inv_inj UpperTheory.V.Hi.OrdB.exists_form UpperTheory.V.Hi.OrdB.num UpperTheory.V.Hi.OrdB.tc_single from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.ExistsNil

theorem UpperTheory.V.Z.Ord.ordJac :
    GlobalTheory.Mem.LiteralAutomorphy.LitN → OrdJac := by
  intro H k _ _ _ _ n V _ _ π hπ hirr c φ hφ0 v hv hv0 a ha
  obtain ⟨hker, hsm, hI, -, -, -, -, hidx, hz, hT⟩ := glBridge k n V π
  have hφ : ∀ t : (glIwa k n).T, (t : GL (Fin n) k) ∈ (glIwa k n).Tc c → φ t = 1 := fun t ht => by
    obtain ⟨y, hy, hy'⟩ := hT t
    have e : (t : GL (Fin n) k) ∈ φ.ker.map (glIwa k n).T.subtype := by
      rw [hy]
      refine list_prod_mem fun x hx => ?_
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
      exact ⟨eT k n i (y i), hφ0 i _ (hy' c ht i), rfl⟩
    obtain ⟨s, hs, e⟩ := e
    exact (Subtype.ext e : s = t) ▸ hs
  haveI : FiniteDimensional ℂ (fixd π ((glIwa k n).I1 c)) := by
    have hfix : fixd π ((glIwa k n).I1 c) = fixed π ((glIwa k n).I1 c) := by
      ext w
      exact ⟨fun h u => by simpa using h u u.2, fun h u hu => by simpa using h ⟨u, hu⟩⟩
    rw [hfix]
    exact ((H.loc.bz k).1 _ V π hπ hirr).2 _ (hI c).1 (hI c).2
  let p : V →ₗ[ℂ] Jacquet π (unipB k (Fin n)) := Submodule.mkQ _
  have hp : ∀ t w, jacB π t (p w) =
      (((deltaHalf k (fun _ : Fin n => Unit) (leviTorus k (Fin n) t))⁻¹ : ℂˣ) : ℂ) • p (π (diagT k (Fin n) t) w) :=
    fun t w => UnramFixed.jacB_apply π t _
  have hlist : ∀ s : List ℕ, (∀ j ∈ s, j < n) → (s.map (al k n)).prod ∈ (glIwa k n).P ∧
      ∃ b : ℂ, b ≠ 0 ∧ (glIwa k n).uOp π (s.map (al k n)).prod v = b • v := by
    intro s
    induction s with
    | nil =>
      exact fun _ => ⟨one_mem _, 1, one_ne_zero, by
        simpa using (uOpMul _ (glIwa k n) ℂ V π 1 1 (one_mem _) (one_mem _) v hv.1).2.2.1⟩
    | cons j s ih =>
      intro hs
      obtain ⟨hP, b, hb, h2⟩ := ih fun i hi => hs i (List.mem_cons_of_mem _ hi)
      rw [List.map_cons, List.prod_cons]
      refine ⟨mul_mem (al_mem k n j) hP, ?_⟩
      rcases j with _ | j
      · have e : al k n 0 = 1 := by
          rw [al, upow, ← (diagT k (Fin n)).map_one]; congr 1; funext i; simp
        rw [e, one_mul]
        exact ⟨b, hb, h2⟩
      · have hj := ha ⟨j, by have := hs _ List.mem_cons_self; omega⟩
        refine ⟨a (j + 1) * b, mul_ne_zero hj.1 hb, ?_⟩
        rw [← (uOpMul _ (glIwa k n) ℂ V π _ _ (al_mem k n _) hP v hv.1).2.1, h2, map_smul]
        have e := hj.2
        simp only at e
        rw [e, smul_smul, mul_comm]
  obtain ⟨-, b, hb, hzb⟩ := hlist (List.range n) fun j hj => List.mem_range.1 hj
  rw [← hz] at hzb
  have hpow : ∀ j : ℕ, ((glIwa k n).uOp π (glIwa k n).z ^ j) v = b ^ j • v := fun j => by
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ', Module.End.mul_apply, ih, map_smul, hzb, smul_smul, pow_succ]
  have hvi : v ∈ invPart π c φ := (Submodule.mem_iInf _).2 fun j =>
    ⟨(b ^ j)⁻¹ • v, Submodule.smul_mem _ _ hv, by
      rw [map_smul, hpow, smul_smul, inv_mul_cancel₀ (pow_ne_zero j hb), one_smul]⟩
  have hx0 : p v ≠ 0 := fun h => hv0 (UpperTheory.V.Hi.OrdB.inv_inj _ π c φ hφ (hsm hπ) hvi
    (hker ▸ (Submodule.Quotient.mk_eq_zero _).1 h))
  have hl : HasFiniteLength (jacB π) :=
    (hasFiniteLength_comp_iff _ _ (leviTorus k (Fin n)).surjective).2
      ((H.loc.bz k).2.1 _ _ _ (points (Fin n)) _ π hπ (hasFiniteLength_of_isIrreducible hirr))
  haveI := GlobalTheory.TorusEigenform.secondCountableTopology_units k
  obtain ⟨μ, hμs, hμ, l, hl0, hle⟩ := UpperTheory.V.Hi.OrdB.exists_form (isSmooth_jacB hπ) hl hx0
  obtain ⟨ψ, hψ, rfl⟩ : ∃ ψ : Fin n → kˣ →* ℂˣ, (∀ i, IsSmoothChar (ψ i)) ∧ torusChar ψ = μ := by
    refine ⟨fun i => μ.comp (MonoidHom.mulSingle (fun _ => kˣ) i),
      fun i => hμs.comp _ (continuous_mulSingle (A := fun _ => kˣ) i), MonoidHom.ext fun t => ?_⟩
    rw [torusChar_apply]
    conv_rhs => rw [← Finset.univ_prod_mulSingle t, map_prod]
    rfl
  have hsq : IsSubquotient π (prinSeries ψ) := GlobalTheory.SatakeExists.isSubquotient_of_eigenform hπ hirr _ l hl0 hle
  have hψφ : ∀ i (u : Uo k), ψ i u = (φ (eT k n i u))⁻¹ := fun i u => by
    have hO : (Pi.mulSingle i (u : kˣ) : Fin n → kˣ) ∈ torusO k (Fin n) := fun j => by
      by_cases h : j = i
      · subst h
        rw [Pi.mulSingle_eq_same]; exact u.2
      · simp [Pi.mulSingle_eq_of_ne h]
    have h1 : jacB π (Pi.mulSingle i (u : kˣ)) (p v) = (((φ (eT k n i u))⁻¹ : ℂˣ) : ℂ) • p v := by
      rw [hp, UnramFixed.deltaHalf_torusO k hO, inv_one, Units.val_one, one_smul, ← map_smul]
      exact congrArg p (hv.2.2 (eT k n i u))
    rw [← UpperTheory.V.Hi.OrdB.tc_single]
    exact Units.ext (hμ _ _ h1)
  obtain ⟨ω, rfl⟩ : ∃ ω : Fin n → kˣ →* ℂˣ, (fun i => ω i * absPow k (((n : ℂ) - 1) / 2)) = ψ :=
    ⟨fun i => ψ i * (absPow k (((n : ℂ) - 1) / 2))⁻¹, funext fun i => inv_mul_cancel_right _ _⟩
  have hω : ∀ i, IsSmoothChar (ω i) := fun i => by
    have := (hψ i).mul (isSmoothChar_of_isUnram (isUnram_absPow k (-(((n : ℂ) - 1) / 2))))
    rwa [absPow_neg, mul_inv_cancel_right] at this
  have hinv : IsInvOn φ ω := fun i u => by
    have := hψφ i u
    rw [MonoidHom.mul_apply, isUnram_absPow k _ _ u.2, mul_one] at this
    rw [this, inv_inv]
  refine ⟨ω, hω, hinv, hsq, fun j => ?_⟩
  have hm : (j : ℕ) + 1 ≤ n := j.2
  have h1 := propCp _ (glIwa k n) ℂ V π _ (al_mem k n ((j : ℕ) + 1)) v hv.1
  rw [hker, hidx _ hm] at h1
  have h2 : p _ = 0 := (Submodule.Quotient.mk_eq_zero _).2 h1
  rw [map_sub, map_smul, sub_eq_zero, (ha j).2, map_smul] at h2
  have hQ : ((Nat.card 𝓀[k] ^ (((j : ℕ) + 1) * (n - ((j : ℕ) + 1))) : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.2 (pow_ne_zero _ Nat.card_pos.ne')
  have h3 := hμ (fun i => UpperTheory.V.Hi.unif k ^ (if (i : ℕ) < (j : ℕ) + 1 then 1 else 0 : ℤ))
    ((((deltaHalf k (fun _ : Fin n => Unit) (leviTorus k (Fin n)
      (fun i => UpperTheory.V.Hi.unif k ^ (if (i : ℕ) < (j : ℕ) + 1 then 1 else 0 : ℤ))))⁻¹ : ℂˣ) : ℂ) *
      (((Nat.card 𝓀[k] ^ (((j : ℕ) + 1) * (n - ((j : ℕ) + 1))) : ℕ) : ℂ)⁻¹ * a ((j : ℕ) + 1))) (by
    rw [hp, mul_smul]
    congr 1
    rw [mul_smul, h2, smul_smul, inv_mul_cancel₀ hQ, one_smul]
    rfl)
  have key : ∀ (Q x : ℂ) (d : ℂˣ), Q ≠ 0 → Q * ((d : ℂ) * (((d⁻¹ : ℂˣ) : ℂ) * (Q⁻¹ * x))) = x := fun Q x d h => by
    rw [Units.val_inv_eq_inv_val]
    have := d.ne_zero
    field_simp
  rw [← UpperTheory.V.Hi.OrdB.num ω hm, h3]
  exact key _ _ _ hQ
