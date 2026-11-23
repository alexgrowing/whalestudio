import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.TraceQuot
import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.IrreducibleAdmissibleGL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.ImStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.CharDom
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.TraceExp
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.ExistsCommonEigenvector
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.ExpSub
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.ExpLev
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.SubPerm
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.SubQuot
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.NormDom
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalDoubleCosets.OfSupportHolds

open MeasureTheory NumberField IsDedekindDomain Filter ValuativeRel
open GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Loc GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open UpperTheory.Gal.LocD UpperTheory.Gal.InertialTypesAlt.G UpperTheory.Gal.Join
open scoped Classical

namespace UpperTheory.Gal.Join

private theorem trIn_smul {X : Type} [AddCommGroup X] [Module ℂ X] {P : Submodule ℂ X} {T : X →ₗ[ℂ] X}
    (h : ∀ y ∈ P, T y ∈ P) (c : ℂ) : trIn P (T ∘ₗ (c • LinearMap.id)) = c * trIn P T := by
  have h' : ∀ y ∈ P, (T ∘ₗ (c • LinearMap.id)) y ∈ P := fun y hy => h _ (P.smul_mem c hy)
  rw [trIn, trIn, dif_pos h, dif_pos h', ← smul_eq_mul, ← map_smul]
  congr 1
  ext y
  simp [LinearMap.restrict_apply]

private theorem adm {K : Type} [Field K] [NumberField K] {n : ℕ} {w : Pl K} (τ : SmIrr (Gw n w)) : IsAdmissible τ.ρ :=
  PositivityTheory.Exh.irreducibleAdmissibleGL _ n τ.V τ.ρ τ.smooth τ.irred

theorem liftExp (h : CoreId) : LiftExp := by
  intro F E _ _ _ _ _ _ _ _ σ hσ hp n hn v w hns σw N hs hN π P hP hW τ τ' hτ hτ' μ ⟨y, hy0, hy⟩
  obtain ⟨A, hA, hA0, hc⟩ := h F E σ hσ hp n hn v w hns σw N hs hN π P hP hW τ τ' hτ hτ'
  obtain ⟨U, hU, hy'⟩ := expLev _ n _ τ.ρ τ.smooth y
  obtain ⟨K', -, K, hK, l', l, hst, c, t₀, hc0, hid⟩ := hc ⊤ U (by simp) hU
  obtain ⟨f', st', sa'⟩ := imStab _ n _ τ'.ρ (adm τ') K' l'
  obtain ⟨f, st, -⟩ := imStab _ n _ τ.ρ (adm τ) K l
  obtain ⟨E', e', m'⟩ := traceExp _ _ (jacB τ'.ρ) (imK τ'.ρ K') st'
  obtain ⟨E₀, e, m⟩ := traceExp _ _ (jacB τ.ρ) (imK τ.ρ K) st
  have hμ : μ.comp (nT n N) ∈ E₀.map fun μ => μ.comp (nT n N) :=
    Multiset.mem_map_of_mem _ ((m μ).2 ⟨y, hy' K hK, hy0, hy⟩)
  have hid' : ∀ t, Dom t → trIn (imK τ'.ρ K') (jacB τ'.ρ (t₀ * t) ∘ₗ jacA hA) =
      c * ((E₀.map fun μ => μ.comp (nT n N)).map fun μ => (μ (t₀ * t) : ℂ)).sum := fun t ht => by
    rw [hid t ht, e, Multiset.map_map]
    rfl
  obtain ⟨t₁, ht₁, hne⟩ := (charDom _ n t₀ (E₀.map fun μ => μ.comp (nT n N)) _ 1 1 one_ne_zero fun _ _ => rfl).2
    (fun h0 => by rw [h0] at hμ; exact Multiset.notMem_zero _ hμ)
  obtain ⟨μ', hinv, z, -, hz0, hz⟩ := twExp _ _ (jacB τ'.ρ) (imK τ'.ρ K')
    (MulEquiv.piCongrRight fun _ => Units.mapEquiv σw.toMulEquiv) (jacA hA) st' (sa' σw A hA hst)
    (fun t y => jacSemi _ n σw hN.cyc.isom _ τ'.ρ A hA t y) (t₀ * t₁) (by rw [hid' t₁ ht₁]; exact mul_ne_zero hc0 hne)
  obtain ⟨ω', rfl, s', q'⟩ := expSub _ n _ τ'.ρ τ'.smooth τ'.irred μ' ⟨z, hz0, hz⟩
  have i' : ∀ i, Inv σw (ω' i) := fun i x => by
    have h1 := hinv (Pi.mulSingle i x)
    have h2 : ∀ x, torusChar ω' (Pi.mulSingle i x) = ω' i x := fun x => by
      rw [torusChar_apply, Finset.prod_eq_single i (fun j _ hj => by rw [Pi.mulSingle_eq_of_ne hj, map_one]) (by simp),
        Pi.mulSingle_eq_same]
    rw [← h2, ← h2, ← h1]
    congr 1
    funext j
    change _ = Units.mapEquiv σw.toMulEquiv ((Pi.mulSingle i x : Fin n → _) j)
    by_cases hj : j = i
    · subst hj
      rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_same]
      rfl
    · rw [Pi.mulSingle_eq_of_ne hj, Pi.mulSingle_eq_of_ne hj, map_one]
  obtain ⟨-, -, -, c', hc', hsc, -⟩ := locDesc_holds _ n σw _ hN.cyc _ τ'.ρ τ'.irred ω' s' i' q' A hA hA0
  have key := (charDom _ n t₀ (E₀.map fun μ => μ.comp (nT n N)) E' c c' hc0 fun t ht => by
    rw [← hid' t ht, hsc, trIn_smul (st' _), e']).1 _ hμ
  obtain ⟨x, -, hx0, hx⟩ := (m' _).1 key
  exact ⟨x, hx0, hx⟩

private theorem exp_of_sub {K : Type} [Field K] [NumberField K] {n : ℕ} {w : Pl K} (τ : SmIrr (Gw n w))
    {ω : Fin n → (w.adicCompletion K)ˣ →* ℂˣ} (s : ∀ i, IsSmoothChar (ω i)) (q : IsSubquotient τ.ρ (prinSeries ω)) :
    ∃ p : Equiv.Perm (Fin n), IsExp τ.ρ (torusChar (ω ∘ p)) := by
  have hnt : Nontrivial τ.V := GroundTheory.Automorphic.RestrictedTensor.nontrivial_of_isIrreducible τ.irred
  obtain ⟨h1, h2, h3, -⟩ := locDesc_holds _ n (RingEquiv.refl _) 1 ⟨fun _ => rfl, one_pos, fun _ => rfl⟩ _ τ.ρ τ.irred ω s
    (fun _ _ => rfl) q LinearMap.id (fun _ _ => rfl) (fun h => by
      obtain ⟨x, hx⟩ := exists_ne (0 : τ.V)
      exact hx (LinearMap.congr_fun h x))
  obtain ⟨E₀, e, m⟩ := traceExp _ _ (jacB τ.ρ) ⊤ fun _ _ _ => trivial
  have hne : E₀ ≠ 0 := by
    rintro rfl
    have h4 := e 1
    rw [map_one, trIn, dif_pos fun _ _ => Submodule.mem_top] at h4
    have h5 : LinearMap.trace ℂ (⊤ : Submodule ℂ (Jacquet τ.ρ (unipB _ (Fin n)))) 1 = 0 := h4
    rw [LinearMap.trace_one, finrank_top, Nat.cast_eq_zero] at h5
    exact Module.finrank_pos.ne' h5
  obtain ⟨μ, hμ⟩ := Multiset.exists_mem_of_ne_zero hne
  obtain ⟨y, -, hy⟩ := (m μ).1 hμ
  obtain ⟨p, rfl⟩ := h3 μ ((subQuot _ _ (jacB τ.ρ) μ).1.1 ⟨y, hy⟩)
  exact ⟨p, y, hy⟩

private theorem torusChar_inj {R : Type} [CommRing R] {n : ℕ} {a b : Fin n → Rˣ →* ℂˣ} (h : torusChar a = torusChar b) : a = b := by
  have h2 : ∀ (a : Fin n → Rˣ →* ℂˣ) i x, torusChar a (Pi.mulSingle i x) = a i x := fun a i x => by
    rw [torusChar_apply, Finset.prod_eq_single i (fun j _ hj => by rw [Pi.mulSingle_eq_of_ne hj, map_one]) (by simp),
      Pi.mulSingle_eq_same]
  funext i
  ext1 x
  rw [← h2, ← h2, h]

private theorem torusChar_comp {R S : Type} [CommRing R] [CommRing S] {n : ℕ} (a : Fin n → Rˣ →* ℂˣ) (N : Sˣ →* Rˣ) :
    (torusChar a).comp (nT n N) = torusChar fun i => (a i).comp N := by
  refine MonoidHom.ext fun t => ?_
  rw [MonoidHom.comp_apply, torusChar_apply, torusChar_apply]
  rfl

theorem liftGood (h : CoreId) : LiftGood := by
  intro F E _ _ _ _ _ _ _ _ σ hσ hp n hn v w hns σw N hs hN π P hP hW τ τ' hτ hτ' ω s q
  obtain ⟨p, hp'⟩ := exp_of_sub τ s q
  have h1 := liftExp h F E σ hσ hp n hn v w hns σw N hs hN π P hP hW τ τ' hτ hτ' _ hp'
  obtain ⟨ω', e, s', q'⟩ := expSub _ n _ τ'.ρ τ'.smooth τ'.irred _ h1
  rw [torusChar_comp] at e
  obtain rfl := torusChar_inj e
  have h2 := subPerm _ n _ τ'.ρ τ'.irred _ s' p.symm q'
  have h3 : (fun i => ((ω ∘ p) i).comp N) ∘ p.symm = fun i => (ω i).comp N := funext fun i => by simp
  rwa [h3] at h2

end UpperTheory.Gal.Join
