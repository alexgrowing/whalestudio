import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.DistinctAbsIrredConstituents
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDecompositionSetting
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CycZBridge
import Development.DiscreteGroups.GlobalIrreducibility.DzBigDef
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TypePrimeCompletionDegreeOneCountProof
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChebotarevDegreeOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFiniteChosenSet
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.SpanMulMem

noncomputable section

namespace UpperTheory.GalS

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

open GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.AbsoluteIrreducibilityOfTraceSpan

theorem cyc_onto (D : D7) (i : D.nd.Loc) (k : Fin 2) (hl : D.nd.l i = D.host.g k) (u : ℤ_[D.nd.l i]ˣ) :
    ∃ g : GE D.nd, cycZ (F := D.host.E) (Ω := D.nd.Om) (D.nd.l i) g = u := by
  haveI : IsAlgClosed D.nd.Om := IsAlgClosure.isAlgClosed D.host.E
  obtain ⟨w, hw⟩ := GlobalTheory.OChoose.placesOver_nonempty D.host.E (D.nd.l i) (D.nd.lPrime i).out
  have h1 : (D.nbr i w hw).Kw.1 = ⊥ := IntermediateField.finrank_eq_one_iff.1 ((GlobalTheory.TypeDegOne.degree_one D i k hl).2 w hw)
  obtain ⟨σ, -, hσu⟩ := GlobalTheory.Cyc.exists_inertia_cycZ_eq (D.nd.l i) u
  have hσ : σ ∈ Formalism.BasicNotions.Loc.GK (D.nbr i w hw).Kw := by
    refine GlobalTheory.EpsInertia.mem_GK _ σ fun x => ?_
    have hx := (D.nbr i w hw).j_E x
    rw [h1, IntermediateField.mem_bot] at hx
    obtain ⟨q, hq⟩ := hx
    rw [← hq]; exact σ.commutes q
  refine ⟨((D.nbr i w hw).e.symm ⟨σ, hσ⟩).1, ?_⟩
  rw [GlobalTheory.EpsInertia.cycZ_bridge (D.nbr i w hw), MulEquiv.apply_symm_apply]
  exact hσu

theorem charP_res (D : D7) (i : D.nd.Loc) : CharP (IsLocalRing.ResidueField (D.nd.O i)) (D.nd.l i) := by
  have hm := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := ℤ_[D.nd.l i]) (IsLocalRing.maximalIdeal (D.nd.O i))
  have h1 : ((D.nd.l i : ℕ) : ℤ_[D.nd.l i]) ∈ (IsLocalRing.maximalIdeal (D.nd.O i)).comap (algebraMap ℤ_[D.nd.l i] (D.nd.O i)) := by
    rw [IsLocalRing.eq_maximalIdeal hm]
    exact PadicInt.irreducible_p.not_isUnit
  rw [Ideal.mem_comap, map_natCast, ← IsLocalRing.residue_eq_zero_iff, map_natCast] at h1
  exact (CharP.charP_iff_prime_eq_zero (D.nd.lPrime i).out).2 h1

def chiBar (D : D7) (i : D.nd.Loc) (j : Fin D.R.t) : GE D.nd →* IsLocalRing.ResidueField (D.nd.O i) :=
  (IsLocalRing.residue (D.nd.O i)).toMonoidHom.comp ((Units.coeHom _).comp (D.nd.chi i ((j : ℕ) + 1)))

theorem chiBar_inj (D : D7) (i : D.nd.Loc) (k : Fin 2) (hl : D.nd.l i = D.host.g k) : Function.Injective (chiBar D i) := by
  intro j j' e
  haveI := charP_res D i
  have hp : (D.nd.l i).Prime := (D.nd.lPrime i).out
  have hbig : 16 * D.R.t ^ 2 < D.nd.l i := hl ▸ DiscreteGroups.sglob.DzType.big_of_le_nV D k (by unfold Ranks.nV; omega)
  obtain ⟨ζ, hζ⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (ZMod (D.nd.l i))ˣ)
  rw [Nat.card_eq_fintype_card, ZMod.card_units] at hζ
  have hu : IsUnit (((ζ : ZMod (D.nd.l i)).val : ℕ) : ℤ_[D.nd.l i]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
    exact (ZMod.val_coe_unit_coprime ζ).symm
  obtain ⟨g, hg⟩ := cyc_onto D i k hl hu.unit
  let φ : (ZMod (D.nd.l i))ˣ →* (IsLocalRing.ResidueField (D.nd.O i))ˣ :=
    Units.map (ZMod.castHom (dvd_refl _) (IsLocalRing.ResidueField (D.nd.O i))).toMonoidHom
  have hφ : Function.Injective φ := Units.map_injective (RingHom.injective _)
  let R : (D.nd.O i)ˣ →* (IsLocalRing.ResidueField (D.nd.O i))ˣ := Units.map (IsLocalRing.residue (D.nd.O i)).toMonoidHom
  have hy : R (Units.map (algebraMap ℤ_[D.nd.l i] (D.nd.O i)).toMonoidHom hu.unit) = φ ζ := by
    apply Units.ext
    show IsLocalRing.residue _ (algebraMap ℤ_[D.nd.l i] (D.nd.O i) (((ζ : ZMod (D.nd.l i)).val : ℕ) : ℤ_[D.nd.l i])) =
      ZMod.castHom (dvd_refl _) (IsLocalRing.ResidueField (D.nd.O i)) (ζ : ZMod (D.nd.l i))
    rw [map_natCast, map_natCast]
    conv_rhs => rw [← ZMod.natCast_zmod_val (ζ : ZMod (D.nd.l i)), map_natCast]
  have key : ∀ c : Fin D.R.t, R (D.nd.chi i ((c : ℕ) + 1) g) = R (D.nd.chi i 1 g) * (φ ζ ^ (c : ℕ))⁻¹ := fun c => by
    rw [D.nd.chi_def i ((c : ℕ) + 1) (by omega) (by omega), MonoidHom.mul_apply, map_mul, MonoidHom.zpow_apply,
      MonoidHom.comp_apply, hg, map_zpow, hy, ← zpow_natCast, ← zpow_neg]
    congr 2
    push_cast; ring
  have e1 : R (D.nd.chi i ((j : ℕ) + 1) g) = R (D.nd.chi i ((j' : ℕ) + 1) g) := Units.ext (DFunLike.congr_fun e g)
  rw [key, key, mul_right_inj, inv_inj, ← map_pow, ← map_pow] at e1
  have hj := j.2
  have hj' := j'.2
  exact Fin.ext (pow_injOn_Iio_orderOf (by rw [Set.mem_Iio, hζ]; have : D.R.t ≤ D.R.t ^ 2 := Nat.le_self_pow two_ne_zero _; omega)
    (by rw [Set.mem_Iio, hζ]; have : D.R.t ≤ D.R.t ^ 2 := Nat.le_self_pow two_ne_zero _; omega) (hφ e1))

theorem trace_of_charpoly {k : Type} [Field k] {a t : ℕ} (M : Matrix (Fin (a + t)) (Fin (a + t)) k) (A : Matrix (Fin a) (Fin a) k)
    (c : Fin t → k) (h : M.charpoly = A.charpoly * ∏ j, (X - C (c j))) : M.trace = A.trace + ∑ j, c j := by
  have e : M.charpoly = (Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks A 0 0 (Matrix.diagonal c))).charpoly := by
    rw [h, Matrix.charpoly_reindex, Matrix.charpoly_fromBlocks_zero₁₂, Matrix.charpoly_diagonal]
  rw [Matrix.trace_eq_neg_charpoly_nextCoeff, e, ← Matrix.trace_eq_neg_charpoly_nextCoeff]
  simp [Matrix.trace, Fin.sum_univ_add]

theorem trace_sumRep {k Γ : Type} [CommRing k] [Group Γ] {a b : ℕ} (ρ : Γ →* GL (Fin a) k) (ρ' : Γ →* GL (Fin b) k) (g : Γ) :
    ((SumRepresentations.At.sumRep ρ ρ' g : GL (Fin (a + b)) k) : Matrix (Fin (a + b)) (Fin (a + b)) k).trace =
      (ρ g : Matrix (Fin a) (Fin a) k).trace + (ρ' g : Matrix (Fin b) (Fin b) k).trace := by
  have e : ((SumRepresentations.At.sumRep ρ ρ' g : GL (Fin (a + b)) k) : Matrix (Fin (a + b)) (Fin (a + b)) k) =
      Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (ρ g : Matrix (Fin a) (Fin a) k) 0 0 (ρ' g : Matrix (Fin b) (Fin b) k)) := rfl
  rw [e]
  simp [Matrix.trace, Fin.sum_univ_add]

theorem noDouble_of_live (D : D7) (h5 : SumRepresentations.adm5 D) (i : D.nd.Loc) (k : Fin 2) (hl : D.nd.l i = D.host.g k)
    (hL : GlobalTheory.CoefDuty.Live D.nd i) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (hr : GoodR D.nd i r)
    (hb : ResidualCharpolyIndependent D.nd i r) (x : D.nd.X i) {K' : Type} [Field K'] (f : D.nd.O i →+* K') (hf : Function.Injective f) {d u : ℕ}
    (σ : GE D.nd →* GL (Fin d) K') (υ : GE D.nd →* GL (Fin u) K') (h : d + d + u = D.R.nV) (Pm : GL (Fin D.R.nV) K')
    (hd : 0 < d)
    (hrel : ∀ g, ((Pm⁻¹ * mapRep f (r x) g * Pm : GL (Fin D.R.nV) K') : Matrix (Fin D.R.nV) (Fin D.R.nV) K') =
      Matrix.reindex (finCongr h) (finCongr h) ((SumRepresentations.At.sumRep (SumRepresentations.At.sumRep σ σ) υ g : GL (Fin (d + d + u)) K') :
        Matrix (Fin (d + d + u)) (Fin (d + d + u)) K')) : False := by
  classical
  obtain ⟨π, -, r0, ρ0, hr0, ⟨e0, he0⟩, habs⟩ := hL
  haveI := charP_res D i
  have hbig : 16 * D.R.nV ^ 2 < D.nd.l i := hl ▸ DiscreteGroups.sglob.DzType.big_of_le_nV D k le_rfl
  have hn : D.R.nV = D.R.r + D.R.t := rfl
  have hr2 : 2 ≤ D.R.r := by have := D.R.two_le_m; have := D.R.m_add_three_le_k; unfold Ranks.r; omega
  refine Dbl.core f hf (IsLocalRing.residue (D.nd.O i)) IsLocalRing.residue_surjective (a := D.R.r) (t := D.R.t) hr2
    (d := d) (u := u) (by omega) ((Units.coeHom _).comp (r x)) ((Units.coeHom _).comp σ) ((Units.coeHom _).comp υ)
    ((Units.coeHom _).comp (mapRep (IsLocalRing.residue (D.nd.O i)) ρ0)) (chiBar D i) (chiBar_inj D i k hl)
    (GlobalTheory.BurnsideField.span_mat_eq_top_of_absIrrSub _ habs) (fun g => ?_) (fun g => ?_) (fun c => ((c : ℕ) : _)) fun c c' e => ?_
  · have t := congrArg Matrix.trace (hrel g)
    rw [Units.val_mul, Units.val_mul, Matrix.trace_mul_cycle, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul] at t
    have t2 : (Matrix.reindex (finCongr h) (finCongr h) ((SumRepresentations.At.sumRep (SumRepresentations.At.sumRep σ σ) υ g : GL (Fin (d + d + u)) K') :
        Matrix (Fin (d + d + u)) (Fin (d + d + u)) K')).trace = ((SumRepresentations.At.sumRep (SumRepresentations.At.sumRep σ σ) υ g : GL (Fin (d + d + u)) K') :
        Matrix (Fin (d + d + u)) (Fin (d + d + u)) K').trace :=
      Equiv.sum_comp (finCongr h).symm fun j => ((SumRepresentations.At.sumRep (SumRepresentations.At.sumRep σ σ) υ g : GL (Fin (d + d + u)) K') :
        Matrix (Fin (d + d + u)) (Fin (d + d + u)) K') j j
    rw [t2, trace_sumRep, trace_sumRep, ← two_mul] at t
    exact (map_sum f _ _).trans t
  · have d0 := charpoly_of_decomp D i (fun _ => r0) (fun _ => ρ0) π ⟨e0, he0⟩ g
    have hc := charpoly_eq_of_isHeckeGalois GlobalTheory.Published.cheb_holds D i r hr π r0 hr0 g
    have e0' : (mat r0 g).charpoly = (mat ρ0 g).charpoly *
      ∏ c ∈ Finset.Icc 1 D.R.t, (X - C ((chiU D.nd i c g : (D.nd.O i)ˣ) : D.nd.O i)) := d0
    have e1 : ((mat (r x) g).map (IsLocalRing.residue (D.nd.O i))).charpoly =
        ((mat (r π) g).map (IsLocalRing.residue (D.nd.O i))).charpoly := hb x π g
    have e2 : ((mat (r x) g).map (IsLocalRing.residue (D.nd.O i))).charpoly =
        ((mat ρ0 g).map (IsLocalRing.residue (D.nd.O i))).charpoly * ∏ j : Fin D.R.t, (X - C (chiBar D i j g)) := by
      rw [e1, Matrix.charpoly_map, hc, e0', Polynomial.map_mul, ← Matrix.charpoly_map, Polynomial.map_prod]
      congr 1
      rw [← Finset.Ico_add_one_right_eq_Icc, Finset.prod_Ico_eq_prod_range, Nat.add_sub_cancel, Finset.prod_range]
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [Polynomial.map_sub, map_X, map_C, add_comm 1]
      rfl
    exact (map_sum (IsLocalRing.residue (D.nd.O i)) _ _).trans (trace_of_charpoly (a := D.R.r) (t := D.R.t) _ _ _ e2)
  · have h1 := c.2
    have h2 := c'.2
    have h3 : D.R.nV ≤ D.R.nV ^ 2 := Nat.le_self_pow two_ne_zero _
    exact Fin.ext (CharP.natCast_injOn_Iio (IsLocalRing.ResidueField (D.nd.O i)) (D.nd.l i)
      (by rw [Set.mem_Iio]; omega) (by rw [Set.mem_Iio]; omega) e)

end UpperTheory.GalS
