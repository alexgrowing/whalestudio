import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TwoClassFrameHasLevelSetting
import Development.AbelianVarietyTheory.Definitions.Divisors.BlockPairCycPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockDataOfCongruentHeckeSystem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalPrimeAinf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DenseRangeOfIsAlgClosed

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.Published.CharAboveModel
open Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD

namespace GlobalTheory.ExpFrame.Tests

section Jumps

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime]

variable (Ω) in

theorem exists_bridge (τ : E →+* Qbar l) : ∃ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (_ : IsPlaceOver A w)
    (LL : FinExt l) (Bw : LocBridge l E Ω (Dec (F := E) A) ↥(OL LL)), GlobalTheory.Pst.Induces Bw ∧
      IsInduced Bw τ (AlgHom.id ℚ_[l] ↥Bw.Kw.1) := by
  first
  | exact @_root_.GlobalTheory.PlaceBallNormLemmas.exists_bridge
  | exact _root_.GlobalTheory.PlaceBallNormLemmas.exists_bridge
  | (apply _root_.GlobalTheory.PlaceBallNormLemmas.exists_bridge <;> assumption)
  | (intros; apply _root_.GlobalTheory.PlaceBallNormLemmas.exists_bridge <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PlaceBallNormLemmas.exists_bridge <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PlaceBallNormLemmas.exists_bridge ..)

theorem jumps_unique {n : ℕ} {r : G E Ω →* GL (Fin n) (Qbar l)} {J J' : (E →+* Qbar l) → Multiset ℤ}
    (h : CrysWith r J) (h' : CrysWith r J') : J = J' := by
  funext τ
  obtain ⟨w, A, hA, LL, Bw, hI, hτ0⟩ := exists_bridge Ω τ
  obtain ⟨P, AI, ⟨T⟩⟩ := GlobalTheory.MemLoc.exists_locPrime_tied l
  have h1 := (h'.2 _ _ ⟨T⟩ w A hA _ Bw hI).2 _ _ _ hτ0
  obtain ⟨L, r', hM, -, τ', hτ, hc⟩ := (h.2 _ _ ⟨T⟩ w A hA _ Bw hI).2 _ _ _ hτ0
  ext a
  exact_mod_cast (hc a).trans (IsJumpsAt.count_eq _ hM hτ h1 a).symm

theorem not_crysWith_cyc : ¬ CrysWith (rk1 (cyc E Ω l ^ 1)) fun _ => {1} := fun h => by
  have h1 := jumps_unique h (Inhab.crysWith_cyc_pow E Ω l 1)
  have τ : E →ₐ[ℚ] PadicAlgCl l := IsAlgClosed.lift
  have := congrFun h1 τ.toRingHom
  simp at this

end Jumps

section RankOne

variable (l : ℕ) [Fact l.Prime]

theorem grp_rank_one {R : Type} [CommRing R] (mu : Unit → ℕ → ℕ) (g : Unit → GL (Fin 1) R) (v : NablaT R 1 mu) :
    grp R 1 mu g v = ((g ())⁻¹.val 0 0) ^ (mu () 0) • v := by
  induction v using PiTensorProduct.induction_on with
  | add a b ha hb => rw [map_add, ha, hb, smul_add]
  | smul_tprod c x =>
    rw [map_smul, smul_comm]
    congr 1
    simp only [grp, Formalism.CohomologicalDescent.RealLocalDeltaNabla.nablaRep, MonoidHom.coe_comp, Function.comp_apply]
    rw [PiTensorProduct.mapMonoidHom_apply, PiTensorProduct.map_tprod]
    have e := (PiTensorProduct.tprod R (s := fun τ : Unit => Formalism.GradedWeylDivisibility.dualWeyl R 1 1 (res 1 (mu τ)))).map_update_smul x ()
      (((g ())⁻¹.val 0 0) ^ (mu () 0)) (x ())
    rw [Function.update_eq_self] at e
    rw [← e]
    congr 1
    funext τ
    obtain rfl : τ = () := rfl
    rw [Function.update_self]
    apply Subtype.ext
    obtain ⟨p, hp⟩ := x ()
    have hp1 := (MvPolynomial.mem_weightedHomogeneousSubmodule _ _ _ _).1 (Submodule.mem_inf.1 hp).1
    change Formalism.UG.dwAct R 1 1 (g ()) p = ((g ())⁻¹.val 0 0) ^ (mu () 0) • p
    clear hp
    induction hp1 using MvPolynomial.IsWeightedHomogeneous.induction_on with
    | zero => simp
    | add p q _ _ hp hq => rw [map_add, hp, hq, smul_add]
    | monomial d r hr =>
      have hd : d (0, 0) = mu () 0 := by
        have := congrFun hr 0
        simpa [Finsupp.weight_apply, Finsupp.sum_fintype, Formalism.GradedWeylDivisibility.colW, res, Fintype.sum_prod_type] using this
      rw [← hd]
      simp [Formalism.UG.dwAct, Formalism.GradedWeylDivisibility.rowAct, MvPolynomial.aeval_monomial, Finsupp.prod_fintype, Fintype.prod_prod_type,
        MvPolynomial.monomial_eq, mul_pow, MvPolynomial.smul_eq_C_mul]
      ring

theorem exists_ne_zero_rank_one (K : Type) [Field K] (mu : Unit → ℕ → ℕ) : ∃ v : NablaT K 1 mu, v ≠ 0 := by
  have h1 : (MvPolynomial.X (0, 0) ^ mu () 0 : MvPolynomial (Fin 1 × Fin 1) K) ∈ Formalism.GradedWeylDivisibility.dualWeyl K 1 1 (res 1 (mu ())) := by
    refine Submodule.mem_inf.2 ⟨?_, ?_⟩
    · rw [MvPolynomial.mem_weightedHomogeneousSubmodule]
      have := (MvPolynomial.isWeightedHomogeneous_X K (Formalism.GradedWeylDivisibility.colW 1 1) (0, 0)).pow (mu () 0)
      have e : res 1 (mu ()) = mu () 0 • Formalism.GradedWeylDivisibility.colW 1 1 (0, 0) := by
        funext a
        fin_cases a
        simp [res, Formalism.GradedWeylDivisibility.colW]
      rw [e]
      exact this
    · simp only [Submodule.mem_iInf]
      intro a b h
      exact absurd h (by omega)
  refine ⟨PiTensorProduct.tprod K fun _ => ⟨_, h1⟩, fun h => ?_⟩
  have h2 := congrArg (PiTensorProduct.subsingletonEquiv (R := K)
    (s := fun τ : Unit => Formalism.GradedWeylDivisibility.dualWeyl K 1 1 (res 1 (mu τ))) ()) h
  rw [PiTensorProduct.subsingletonEquiv_apply_tprod, map_zero] at h2
  exact pow_ne_zero _ (MvPolynomial.X_ne_zero _) (congrArg Subtype.val h2)

def parOne : Par := { k := 1, m := 0, t := 1, f := 1, n := 1, Nr := 1, L := 0, x := 1, b' := 1, η := 0, S := -3 }

theorem height_trivialParameter_eq_zero : Formalism.CohomologicalDescent.ShortWeightBounds.h0 parOne = 0 := by
  simp [Formalism.CohomologicalDescent.ShortWeightBounds.h0, Par.h, Par.b, parOne]
  norm_num

variable {E Ω : Type} [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]

theorem weight_unique (hC : GlobalTheory.Published.ChebotarevDegreeOne) {inc : Unit → (E →+* Qbar l)} {W : Wts Unit} {F : Frame l Unit parOne.Nr}
    {Bk : (F.I → Qbar l) → Prop} (h : GalSide Ω inc parOne W F Bk) {mu mu' : Unit → ℕ → ℕ} {θ : F.I → Qbar l}
    (h1 : F.IsEig mu θ) (h2 : F.IsEig mu' θ) : mu () 0 = mu' () 0 := by
  obtain ⟨Pl, pt, Fn, ep, -, hG, -⟩ := h
  have ha : ∀ m : ℕ → ℕ, Antitone (res parOne.Nr m) := fun m a b _ => by
    rw [Subsingleton.elim (α := Fin 1) a b]
  obtain ⟨r, J, hJ, hr, hR⟩ := hG mu θ (fun _ => ha _) h1
  obtain ⟨r', J', hJ', hr', hR'⟩ := hG mu' θ (fun _ => ha _) h2
  have hz := continuous_zpow (G := G E Ω) (Fn.sgn : ℤ)
  have e : (fun σ : G E Ω => r (σ ^ (Fn.sgn : ℤ))) = fun σ => r' (σ ^ (Fn.sgn : ℤ)) := by
    refine hC.eq_of_frob Fn.cofin (hr.1.comp hz) (hr'.1.comp hz) fun v hv hd B hB σ hσ => ?_
    have hpr : (Ideal.absNorm v.asIdeal).Prime := ((GlobalTheory.absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified E).1 v).2 hd
    have hv' : v ∈ Set.range Fn.lab := by
      by_contra h; exact hv ⟨hpr, h⟩
    obtain ⟨P0, rfl⟩ := hv'
    have e1 := (hR P0 B σ hB hσ).trans (hR' P0 B σ hB hσ).symm
    have key : ∀ M M' : Matrix (Fin 1) (Fin 1) (Qbar l), M.charpoly.reverse = M'.charpoly.reverse → M = M' := fun M M' hM => by
      rw [Matrix.reverse_charpoly, Matrix.reverse_charpoly] at hM
      have := congrArg (Polynomial.coeff · 1) hM
      simp [Matrix.charpolyRev, Polynomial.coeff_one] at this
      ext a b
      fin_cases a; fin_cases b
      exact this
    exact Units.ext (key _ _ e1)
  have e2 : r = r' := MonoidHom.ext fun σ => by
    have := congrFun e (σ ^ (Fn.sgn : ℤ))
    rwa [← zpow_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, zpow_one] at this
  subst e2
  have e3 := congrFun (jumps_unique hr hr') (ep (inc ()))
  have e4 : J (ep (inc ())) (0 : Fin 1) = J' (ep (inc ())) (0 : Fin 1) := by
    have e5 : ∀ f : Fin 1 → ℤ, Finset.univ.val.map f = {f 0} := fun f => by simp
    exact Multiset.singleton_inj.1 ((e5 _).symm.trans (e3.trans (e5 _)))
  rw [(hJ () (0 : Fin 1)).1, (hJ' () (0 : Fin 1)).1] at e4
  simpa [Formalism.CohomologicalDescent.UnitNormBounds.UN] using e4

theorem not_galSide (hC : GlobalTheory.Published.ChebotarevDegreeOne) (inc : Unit → (E →+* Qbar l)) (W : Wts Unit)
    (Bk : (Unit → Qbar l) → Prop) : (Inhab.twoFrame l 1).Ok ∧ ¬ GalSide Ω inc parOne W (Inhab.twoFrame l 1) Bk := by
  refine ⟨Inhab.twoFrame_ok l 1, fun h => ?_⟩
  obtain ⟨v, hv⟩ := exists_ne_zero_rank_one (PadicAlgCl l) fun _ _ => 0
  obtain ⟨v', hv'⟩ := exists_ne_zero_rank_one (PadicAlgCl l) fun _ _ => 1
  exact zero_ne_one (weight_unique l hC h (Inhab.twoFrame_isEig l 1 _ v hv 1) (Inhab.twoFrame_isEig l 1 _ v' hv' 1))

def invFrame : Frame l Unit 1 where
  O := ℤ_[l]
  emb := Inhab.embZ l
  G := GL (Fin 1) ℤ_[l]
  Γ := ⊤
  K := ⊤
  kap := MonoidHom.pi fun _ => (⊤ : Subgroup (GL (Fin 1) ℤ_[l])).subtype
  chi := 1
  I := Unit
  tr _ := {1}
  cst _ := 1

theorem invFrame_isEig : (invFrame l).IsEig (fun _ _ => 0) fun _ => 1 := by
  refine ⟨fun _ => GLInhab.oneVec l 1, ?_, ⟨fun _ _ _ => rfl, fun κ g => ?_⟩, fun i g => ?_⟩
  · intro h
    exact GLInhab.oneVec_ne_zero l 1 (congrFun h (1 : GL (Fin 1) ℤ_[l]))
  · show Inhab.embZ l 1 • _ = _
    rw [map_one, one_smul]
    exact GLInhab.grp_oneVec l 1 _
  · show Inhab.embZ l 1 • ∑ s ∈ ({1} : Finset (GL (Fin 1) ℤ_[l])), GLInhab.oneVec l 1 = (1 : PadicAlgCl l) • GLInhab.oneVec l 1
    rw [map_one, Finset.sum_singleton]

theorem eq_of_invFrame_isEig {mu : Unit → ℕ → ℕ} {θ : Unit → PadicAlgCl l} (h : (invFrame l).IsEig mu θ) :
    mu () 0 = 0 ∧ θ = fun _ => 1 := by
  obtain ⟨f, h0, ⟨hΓ, hK⟩, hθ⟩ := h
  have hc : ∀ g, f g = f 1 := fun g => by simpa using hΓ g trivial 1
  have hv : f 1 ≠ 0 := fun h => h0 (funext fun g => (hc g).trans h)
  refine ⟨?_, funext fun i => ?_⟩
  · have hu : IsUnit (1 + (l : ℤ_[l])) := by
      rw [add_comm, ← sub_neg_eq_add, ← neg_sub]
      refine IsUnit.neg ?_
      have := IsLocalRing.isUnit_one_sub_self_of_mem_nonunits (-(l : ℤ_[l])) (by
        simpa using (PadicInt.irreducible_p (p := l)).not_isUnit)
      have h2 := this.neg
      convert h2 using 1
      ring
    let g : GL (Fin 1) ℤ_[l] := Matrix.GeneralLinearGroup.scalar (Fin 1) hu.unit
    have h1 := hK ⟨g⁻¹, trivial⟩ 1
    rw [hc (_ * _)] at h1
    change Inhab.embZ l 1 • grp (PadicAlgCl l) 1 mu (fun _ => Matrix.GeneralLinearGroup.map (Inhab.embZ l) g⁻¹) (f 1) = f 1 at h1
    rw [map_one, one_smul, grp_rank_one, map_inv, inv_inv] at h1
    have h2 : (Matrix.GeneralLinearGroup.map (Inhab.embZ l) g).val 0 0 = ((1 + l : ℕ) : PadicAlgCl l) := by
      simp [g]
    rw [h2] at h1
    have h3 : ((1 + l : ℕ) : PadicAlgCl l) ^ mu () 0 = 1 := smul_left_injective _ hv (h1.trans (one_smul _ _).symm)
    have h4 : (1 + l) ^ mu () 0 = 1 := by exact_mod_cast h3
    have := (Fact.out : l.Prime).pos
    exact (Nat.pow_eq_one.1 h4).resolve_left (by omega)
  · have h1 := hθ i 1
    change Inhab.embZ l 1 • ∑ s ∈ ({1} : Finset (GL (Fin 1) ℤ_[l])), f ((1 : GL (Fin 1) ℤ_[l]) * s) = θ i • f 1 at h1
    rw [map_one, Finset.sum_singleton, mul_one] at h1
    exact (smul_left_injective _ hv h1).symm

theorem galSide_invFrame (inc : Unit → (E →+* Qbar l)) (W : Wts Unit) (hj : W.j () = 0) :
    GalSide Ω inc parOne W (invFrame l) fun _ => True := by
  have hcp : ∀ σ : G E Ω, ((rk1 (cyc E Ω l ^ 0) σ).val).charpoly = Polynomial.X - Polynomial.C 1 := fun σ => by
    rw [Matrix.charpoly, Matrix.det_fin_one, Matrix.charmatrix_apply_eq]
    simp [rk1]
  have hR : (Inhab.allPlaces l E Ω).Reads 1 (sysOf (I := Unit) 1 (fun _ _ => ()) (fun _ => 1)) fun _ => Polynomial.X - Polynomial.C 1 := by
    have : sysOf (l := l) (Pl := HeightOneSpectrum (𝓞 E)) (I := Unit) 1 (fun _ _ => ()) (fun _ => 1) = fun _ _ => 1 := by
      funext P k; simp [sysOf]
    rw [this]
    exact Inhab.allPlaces_reads l E Ω
  refine ⟨_, fun _ _ => (), Inhab.allPlaces l E Ω, id, Or.inl rfl, fun mu θ _ h => ?_, fun θ h _ => ?_⟩
  · obtain ⟨hm, rfl⟩ := eq_of_invFrame_isEig l h
    refine ⟨rk1 (cyc E Ω l ^ 0), fun _ _ => 0, fun τ a => ?_, ?_, ?_⟩
    · have ha : ∀ b : Fin parOne.Nr, (b : ℕ) = 0 := fun b => Nat.lt_one_iff.1 b.2
      rw [height_trivialParameter_eq_zero, ha, ha]
      simp [Formalism.CohomologicalDescent.UnitNormBounds.UN, parOne, hm]
    · exact Inhab.crysWith_cyc_pow E Ω l 0
    · have : (fun σ : G E Ω => ((rk1 (cyc E Ω l ^ 0) σ).val).charpoly) = fun _ => Polynomial.X - Polynomial.C 1 := funext hcp
      exact this ▸ hR
  · obtain ⟨hm, rfl⟩ := eq_of_invFrame_isEig l h
    refine ⟨0, 1, fun _ => cyc E Ω l ^ 0, fun _ => 0, rfl, continuous_const, fun s => ?_, fun τ => ?_, ?_⟩
    · have hs : (s : ℕ) = 0 := Nat.lt_one_iff.1 s.2
      rw [hs]
      exact Inhab.crysWith_cyc_pow E Ω l 0
    · rw [height_trivialParameter_eq_zero]
      simp [Wts.bot, Wts.U, kc, Formalism.CohomologicalDescent.UnitNormBounds.UN, parOne, hm, hj]
    · have : (fun σ : G E Ω => ((1 : G E Ω →* GL (Fin 0) (Qbar l)) σ).val.charpoly *
          ∏ s : Fin 1, (Polynomial.X - Polynomial.C (((cyc E Ω l ^ 0) σ : (Qbar l)ˣ) : Qbar l))) =
          fun _ => Polynomial.X - Polynomial.C 1 := by
        funext σ
        simp [Matrix.charpoly]
      exact this ▸ hR

end RankOne

section Small

theorem linked_three : Linked 3 2 (fun (_ : Unit) a => if a = 0 then 3 else 0) (fun _ a => if a = 0 then 2 else 1) := by
  intro τ
  refine ⟨fun a b h => ?_, by simp, fun a => by fin_cases a <;> simp, ?_⟩
  · fin_cases a <;> fin_cases b <;> simp_all [res]
  · rw [Fin.prod_univ_two, Fin.prod_univ_two, mul_comm]
    congr 3 <;> decide +revert

theorem not_linked_three : ¬ Linked 3 2 (fun (_ : Unit) a => if a = 0 then 2 else 0) (fun _ _ => 1) := fun h => by
  have := congrArg (Polynomial.eval 0) (h ()).2.2.2
  simp [Fin.prod_univ_two] at this
  revert this
  decide

theorem isFrobPerm_rat (l : ℕ) [Fact l.Prime] : IsFrobPerm (E := ℚ) (l := l) 1 := by
  intro τ x
  obtain ⟨n, rfl⟩ := Rat.ringOfIntegersEquiv.symm.surjective x
  rw [eq_intCast Rat.ringOfIntegersEquiv.symm n]
  obtain ⟨c, hc⟩ : (l : ℤ) ∣ n - n ^ l := (ZMod.intCast_zmod_eq_zero_iff_dvd _ l).1 (by simp)
  have e : (1 : Equiv.Perm (ℚ →+* Qbar l)) τ ((n : 𝓞 ℚ) : ℚ) - τ ((n : 𝓞 ℚ) : ℚ) ^ l = (l : Qbar l) * (c : Qbar l) := by
    have := congrArg (Int.cast : ℤ → Qbar l) hc
    simpa using this
  rw [e, norm_mul]
  exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) GlobalTheory.PlaceBridge.norm_l_lt_one
    (IsUltrametricDist.norm_intCast_le_one _ c)

end Small

end GlobalTheory.ExpFrame.Tests

end
