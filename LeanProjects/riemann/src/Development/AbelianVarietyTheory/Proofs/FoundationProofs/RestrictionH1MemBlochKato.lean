import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.SelmerCrystallineCocycles

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction GlobalTheory.IndefiniteRowSideFullHecke.SelmerCrystallineCocycles

namespace GlobalTheory.BKIntegralToRational

theorem exists_mul_pow_eq {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] {p : A}
    (hu : ¬ IsUnit p) (a : FractionRing A) :
    ∃ (x : A) (N : ℕ), a * algebraMap A (FractionRing A) p ^ N = algebraMap A (FractionRing A) x := by
  obtain ⟨n, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := A) a
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  obtain ⟨N, hN⟩ := IsDiscreteValuationRing.associated_pow_irreducible hd0 hϖ
  have h1 : ϖ ∣ p := by
    rw [← Ideal.mem_span_singleton, ← hϖ.maximalIdeal_eq]
    exact hu
  obtain ⟨c, hc⟩ : d ∣ p ^ N := hN.dvd.trans (pow_dvd_pow_of_dvd h1 N)
  refine ⟨n * c, N, ?_⟩
  have hd1 : algebraMap A (FractionRing A) d ≠ 0 := by
    simpa using hd0
  rw [← map_pow, hc, map_mul, map_mul]
  field_simp

theorem continuous_div_mk {O₀ O' : Type} [CommRing O₀] [IsDomain O₀] [IsDiscreteValuationRing O₀]
    [TopologicalSpace O₀] [IsTopologicalRing O₀] (had : IsAdic (IsLocalRing.maximalIdeal O₀))
    [CommRing O'] [IsDomain O'] (ι : O₀ →+* O') {d : O₀} (hd : d ≠ 0) (hd' : ι d ≠ 0) :
    Continuous fun x : O₀ => (Submodule.Quotient.mk (algebraMap O' (FractionRing O') (ι x) /
      algebraMap O' (FractionRing O') (ι d)) : KmodO O') := by
  have hd1 : algebraMap O' (FractionRing O') (ι d) ≠ 0 := by simpa using hd'
  have hop : IsOpen ((Ideal.span {d} : Ideal O₀) : Set O₀) := by
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O₀
    obtain ⟨N, hN⟩ := IsDiscreteValuationRing.associated_pow_irreducible hd hϖ
    have := (isAdic_iff.1 had).1 N
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow] at this
    rwa [Ideal.span_singleton_eq_span_singleton.2 hN]
  refine IsLocallyConstant.continuous ?_
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  refine ⟨(fun y => y - x) ⁻¹' ((Ideal.span {d} : Ideal O₀) : Set O₀),
    hop.preimage (by fun_prop), by simp, fun y hy => ?_⟩
  obtain ⟨c, hc⟩ : d ∣ y - x := Ideal.mem_span_singleton.1 hy
  rw [Submodule.Quotient.eq]
  refine ⟨ι c, ?_⟩
  rw [← sub_div, ← map_sub, ← map_sub, hc, map_mul, map_mul]
  simp only [Algebra.linearMap_apply]
  field_simp

section Bridge

variable {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
  {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O₀ : Type} [CommRing O₀] [Algebra ℤ_[l] O₀] [TopologicalSpace O₀]
  (Bw : LocBridge l E Ω Gw O₀) (P : LocPrime l) {m : ℕ}

theorem toLL_injective : Function.Injective Bw.toLL :=
  Subtype.val_injective.comp Bw.eO.injective

theorem continuous_of_toLL {X : Type} [TopologicalSpace X] (f : X → O₀)
    (h : Continuous fun x => Bw.toLL (f x)) : Continuous f := by
  have h1 : Continuous fun x => Bw.eO (f x) := continuous_induced_rng.2 h
  simpa [Function.comp_def] using Bw.eO_symm_cont.comp h1

theorem continuous_of_crys {T : (Ω ≃ₐ[E] Ω) →* GL (Fin m) O₀} {f : ↥Gw → Fin m → O₀}
    (hf : IsCrysCocycle Bw P T f) (j : Fin m) : Continuous fun g => f g j := by
  apply continuous_of_toLL Bw
  have := ((continuous_apply j).comp hf.1.1).comp Bw.e_cont
  simpa [Function.comp_def] using this

theorem cocycle_of_crys {T : (Ω ≃ₐ[E] Ω) →* GL (Fin m) O₀} {f : ↥Gw → Fin m → O₀}
    (hf : IsCrysCocycle Bw P T f) (g h : ↥Gw) (j : Fin m) :
    f (g * h) j = f g j + ∑ b, ((T g : GL (Fin m) O₀) : Matrix (Fin m) (Fin m) O₀) j b * f h b := by
  apply toLL_injective Bw
  have := congrFun (hf.1.2 (Bw.e g) (Bw.e h)) j
  simpa [← map_mul, LocBridge.rep, Matrix.mulVec, dotProduct, Matrix.toLinAlgEquiv'_apply] using this

end Bridge

section Main

variable (D : D7) (i : D.ntw.Tw) (s : D.ntw.Sig i) (k : ℕ)

theorem l_ne_zero : ((D.ntw.l i : ℕ) : D.ntw.O0 i) ≠ 0 := by
  have : CharZero (FractionRing (D.ntw.O0 i)) :=
    (D.ntw.emb0 i).charZero_iff (D.ntw.emb0 i).injective |>.1 inferInstance
  have : CharZero (D.ntw.O0 i) := (algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i))).charZero
  exact Nat.cast_ne_zero.2 (Fact.out : (D.ntw.l i).Prime).ne_zero

theorem toOk_injective : Function.Injective (toOk D i k) :=
  (D.ntw.Ok_inj i k).comp (D.ntw.O_inj i)

theorem l_not_unit : ¬ IsUnit ((D.ntw.l i : ℕ) : D.ntw.Ok i k) := by
  have := D.ntw.Ok_fin i k
  have : FaithfulSMul (D.ntw.O i) (D.ntw.Ok i k) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (D.ntw.Ok_inj i k)
  intro h
  have h2 : IsUnit (algebraMap (D.ntw.O i) (D.ntw.Ok i k) (D.ntw.l i)) := by simpa using h
  exact D.ntw.O_l i ((isUnit_map_iff _ _).1 h2)

theorem latT_eq : latT D i s = Gen.Tgl i s := rfl

theorem trep_apply (ψ : GE D →* (D.ntw.Ok i k)ˣ) (g : GE D) (hg : ψ g = 1)
    (x : Fin D.R.r → KmodO (D.ntw.Ok i k)) (a : Fin D.R.r) :
    Gen.Trep i s k ψ g x a = ∑ b, toOk D i k
      (((latT D i s g : GL (Fin D.R.r) (D.ntw.O0 i)) : Matrix (Fin D.R.r) (Fin D.R.r) _) a b) • x b := by
  have h : toOk D i k = Gen.phiK D.ntw i k := rfl
  simp [latT_eq, h, hg, Gen.Trep, twRep, matAct, Gen.Tgl_coe, Gen.Tmat, Finset.smul_sum, smul_smul]

variable (ψ : GE D →* (D.ntw.Ok i k)ˣ) (v : PlE D.host) (hv : v ∈ placesOver D.host.E (D.ntw.l i))
  (hψ : ∀ σ ∈ decAt D v, ψ σ = 1)

theorem mk_mem_bk (bkP : BK D)
    (z : ReciprocityTheory.Gal.Z1 ((Gen.Trep i s k ψ).comp (Gen.DecV D.nd v).subtype))
    (c : ↥(Loc.GK (bkP.br i v hv).Kw) → Fin D.R.r → ↥(bkP.br i v hv).LL.1)
    (y : ↥(decAt D v) → Fin D.R.r → FractionRing (D.ntw.Ok i k))
    (hc : c ∈ Formalism.WeaklyAdmissibleFiltrations.finiteCocycles (Gen.PDv bkP i v hv) (Gen.repV bkP i v hv (Gen.Tgl i s)))
    (hy : ∀ g a, Gen.IsImgK bkP i v hv k (c ((bkP.br i v hv).e g) a) (y g a))
    (hz : ∀ g a, (z : ↥(decAt D v) → Fin D.R.r → KmodO (D.ntw.Ok i k)) g a =
      Submodule.Quotient.mk (y g a)) :
    (Submodule.Quotient.mk z : ReciprocityTheory.Gal.H1 _) ∈ Gen.bk bkP i s k ψ v := by
  unfold Gen.bk
  split
  · exact Submodule.subset_span ⟨z, c, y, hc, hy, hz, rfl⟩
  · contradiction

include hψ in

theorem div_mem {f : ↥(decAt D v) → Fin D.R.r → D.ntw.O0 i}
    (hf : IsCrysCocycle (D.ntwbr i v hv) (D.loc (D.ntw.l i)) (latT D i s) f) {d : D.ntw.O0 i}
    (hd : d ≠ 0) :
    ∃ z : ReciprocityTheory.Gal.Z1 ((Gen.Trep i s k ψ).comp (decAt D v).subtype),
      (∀ g j, (z : ↥(decAt D v) → Fin D.R.r → KmodO (D.ntw.Ok i k)) g j = Submodule.Quotient.mk
        (algebraMap _ (FractionRing (D.ntw.Ok i k)) (toOk D i k (f g j)) /
          algebraMap _ (FractionRing (D.ntw.Ok i k)) (toOk D i k d))) ∧
      (Submodule.Quotient.mk z : ReciprocityTheory.Gal.H1 _) ∈ Gen.bk (bk0 D) i s k ψ v := by
  have hd' : toOk D i k d ≠ 0 := (map_ne_zero_iff _ (toOk_injective D i k)).2 hd
  have hd1 : algebraMap _ (FractionRing (D.ntw.Ok i k)) (toOk D i k d) ≠ 0 := by simpa using hd'
  have hd2 : (D.ntwbr i v hv).toLL d ≠ 0 := (map_ne_zero_iff _ (toLL_injective _)).2 hd
  refine ⟨⟨fun g j => Submodule.Quotient.mk
        (algebraMap _ (FractionRing (D.ntw.Ok i k)) (toOk D i k (f g j)) /
          algebraMap _ (FractionRing (D.ntw.Ok i k)) (toOk D i k d)), ?_, fun g h => ?_⟩,
    fun _ _ => rfl, ?_⟩
  · exact continuous_pi fun j => (continuous_div_mk (D.ntw.twistBaseCoefficientRing_isAdic i) (toOk D i k) hd hd').comp
      (continuous_of_crys _ _ hf j)
  · funext j
    rw [Pi.add_apply, MonoidHom.comp_apply, Subgroup.coe_subtype, trep_apply D i s k ψ g (hψ g g.2)]
    beta_reduce
    rw [cocycle_of_crys _ _ hf g h j]
    simp only [← Submodule.mkQ_apply, map_add, map_sum, map_mul, add_div, Finset.sum_div, mul_div_assoc,
      ← LinearMap.map_smul, Algebra.smul_def]
  · refine mk_mem_bk D i s k ψ v hv (bk0 D) _ (((D.ntwbr i v hv).toLL d)⁻¹ •
      (fun g j => (D.ntwbr i v hv).toLL (f ((D.ntwbr i v hv).e.symm g) j)))
      (fun g j => algebraMap _ (FractionRing (D.ntw.Ok i k)) (toOk D i k (f g j)) /
          algebraMap _ (FractionRing (D.ntw.Ok i k)) (toOk D i k d))
      (Submodule.smul_mem _ _ hf) (fun g a => ⟨f g a, d, ⟨hd, ?_⟩, ?_⟩) (fun _ _ => rfl)
    · change (D.ntwbr i v hv).toLL d * (((D.ntwbr i v hv).toLL d)⁻¹ *
        (D.ntwbr i v hv).toLL (f ((D.ntwbr i v hv).e.symm ((D.ntwbr i v hv).e g)) a)) =
          (D.ntwbr i v hv).toLL (f g a)
      rw [MulEquiv.symm_apply_apply, mul_inv_cancel_left₀ hd2]
    · exact mul_div_cancel₀ _ hd1

end Main

end GlobalTheory.BKIntegralToRational
