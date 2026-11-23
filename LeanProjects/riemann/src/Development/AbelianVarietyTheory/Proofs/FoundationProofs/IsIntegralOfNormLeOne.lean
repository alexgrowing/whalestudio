import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.SelmerCrystallineCocycles
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction GlobalTheory.IndefiniteRowSideFullHecke.SelmerCrystallineCocycles

namespace GlobalTheory.BlochKatoIntegralScalars

section Local

variable {l : ℕ} [Fact l.Prime]

theorem isIntegral_of_norm_le_one (x : PadicAlgCl l) (h : ‖x‖ ≤ 1) : IsIntegral ℤ_[l] x := by
  have hx : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  rw [← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralValue_le_one_iff (minpoly.monic hx)] at h
  have hl : minpoly ℚ_[l] x ∈ Polynomial.lifts (algebraMap ℤ_[l] ℚ_[l]) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    exact fun n => ⟨⟨_, h n⟩, rfl⟩
  obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_degree_eq_and_monic hl (minpoly.monic hx)
  refine ⟨q, hqm, ?_⟩
  rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]

theorem mem_OL_of_norm_le_one (K : Loc.FinExt l) (x : K.1) (h : ‖(x : PadicAlgCl l)‖ ≤ 1) :
    x ∈ Loc.OL K :=
  (isIntegral_algHom_iff (K.1.val.restrictScalars ℤ_[l]) K.1.val.toRingHom.injective).1
    (isIntegral_of_norm_le_one _ h)

theorem compactSpace_GK (K : Loc.FinExt l) : CompactSpace ↥(Loc.GK K) := by
  haveI := K.2
  have h : IsClosed ((Loc.GK K : Subgroup (Loc.GQ l)) : Set (Loc.GQ l)) :=
    IntermediateField.fixingSubgroup_isClosed K.1
  exact isCompact_iff_compactSpace.1 h.isCompact

theorem exists_pow_mul_mem_OL {X : Type} [TopologicalSpace X] [CompactSpace X] (K : Loc.FinExt l) {m : ℕ}
    (c : X → Fin m → K.1) (hc : Continuous c) :
    ∃ N : ℕ, ∀ g j, (l : K.1) ^ N * c g j ∈ Loc.OL K := by
  have hc' : Continuous fun g (j : Fin m) => ((c g j : K.1) : PadicAlgCl l) :=
    continuous_pi fun j => continuous_subtype_val.comp ((continuous_apply j).comp hc)
  obtain ⟨C, hC⟩ := (isCompact_range hc').isBounded.exists_norm_le
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt C hl
  refine ⟨N, fun g j => mem_OL_of_norm_le_one K _ ?_⟩
  have h1 : ‖((c g j : K.1) : PadicAlgCl l)‖ ≤ C :=
    (norm_le_pi_norm (fun j : Fin m => ((c g j : K.1) : PadicAlgCl l)) j).trans (hC _ ⟨g, rfl⟩)
  have h2 : ‖(l : PadicAlgCl l)‖ = (l : ℝ)⁻¹ := by
    have := PadicAlgCl.norm_extends l (l : ℚ_[l])
    rw [map_natCast] at this
    rw [this, Padic.norm_p]
  have h3 : (((l : K.1) ^ N * c g j : K.1) : PadicAlgCl l) =
      (l : PadicAlgCl l) ^ N * ((c g j : K.1) : PadicAlgCl l) := by
    push_cast
    rfl
  rw [h3, norm_mul, norm_pow, h2, inv_pow, inv_mul_le_iff₀ (by positivity), mul_one]
  exact h1.trans hN.le

variable {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
  {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O₀ : Type} [CommRing O₀] [Algebra ℤ_[l] O₀] [TopologicalSpace O₀]
  (Bw : LocBridge l E Ω Gw O₀) (P : LocPrime l) {m : ℕ}

theorem toLL_injective : Function.Injective Bw.toLL :=
  Subtype.val_injective.comp Bw.eO.injective

theorem mem_crysSpan_of_rational {O' : Type} [CommRing O'] [IsDomain O'] (ι : O₀ →+* O')
    (hι : Function.Injective ι) (T : (Ω ≃ₐ[E] Ω) →* GL (Fin m) O₀)
    (c : ↥(Loc.GK Bw.Kw) → Fin m → ↥Bw.LL.1)
    (hc : c ∈ Formalism.WeaklyAdmissibleFiltrations.finiteCocycles (P.PD Bw.Kw) (Bw.rep (T.comp Gw.subtype)))
    (y : ↥Gw → Fin m → FractionRing O')
    (hy : ∀ g a, ∃ n d : O₀, (d ≠ 0 ∧ Bw.toLL d * c (Bw.e g) a = Bw.toLL n) ∧
      algebraMap O' (FractionRing O') (ι d) * y g a = algebraMap O' (FractionRing O') (ι n))
    (z : ↥Gw → Fin m → KmodO O') (hz : ∀ g a, z g a = Submodule.Quotient.mk (y g a)) :
    z ∈ crysSpan Bw P ι T := by
  haveI := compactSpace_GK Bw.Kw
  obtain ⟨N, hN⟩ := exists_pow_mul_mem_OL Bw.LL c hc.1.1
  let f : ↥Gw → Fin m → O₀ := fun g j => Bw.eO.symm ⟨_, hN (Bw.e g) j⟩
  have hf : ∀ g j, Bw.toLL (f g j) = (l : Bw.LL.1) ^ N * c (Bw.e g) j := by
    intro g j
    show ((Bw.eO (Bw.eO.symm _) : Loc.OL Bw.LL) : Bw.LL.1) = _
    rw [RingEquiv.apply_symm_apply]
  have hφ : Function.Injective ((algebraMap O' (FractionRing O')).comp ι) :=
    (IsFractionRing.injective O' (FractionRing O')).comp hι
  have hl0 : (l : O₀) ≠ 0 := by
    intro h
    have := congrArg Bw.toLL h
    rw [map_natCast, map_zero] at this
    exact (Fact.out : l.Prime).ne_zero (by exact_mod_cast this)
  have hl1 : (l : FractionRing O') ≠ 0 := by
    intro h
    apply hl0
    apply hφ
    rw [map_natCast, map_zero, h]
  refine Submodule.subset_span ⟨((l : FractionRing O') ^ N)⁻¹, f, ?_, fun g j => ?_⟩
  · have := (Formalism.WeaklyAdmissibleFiltrations.finiteCocycles (P.PD Bw.Kw) (Bw.rep (T.comp Gw.subtype))).smul_mem ((l : Bw.LL.1) ^ N) hc
    unfold IsCrysCocycle
    convert this using 1
    funext g j
    rw [hf, MulEquiv.apply_symm_apply]
    rfl
  · rw [hz]
    congr 1
    obtain ⟨n, d, ⟨hd, h1⟩, h2⟩ := hy g j
    have h3 : d * f g j = (l : O₀) ^ N * n := by
      apply toLL_injective Bw
      rw [map_mul, map_mul, hf, map_pow, map_natCast, ← h1]
      ring
    have h4 := congrArg ((algebraMap O' (FractionRing O')).comp ι) h3
    rw [map_mul, map_mul, map_pow, map_natCast] at h4
    simp only [RingHom.comp_apply] at h4
    have hd' : algebraMap O' (FractionRing O') (ι d) ≠ 0 := fun h =>
      hd (hφ (by rw [map_zero]; exact h))
    rw [eq_inv_mul_iff_mul_eq₀ (pow_ne_zero _ hl1)]
    apply mul_left_cancel₀ hd'
    rw [h4, ← h2]
    ring

end Local

theorem Trep_eq_actDiv (D : D7) (i : D.ntw.Tw) (s : D.ntw.Sig i) (k : ℕ) (ψ : GE D →* (D.ntw.Ok i k)ˣ)
    (g : GE D) (hg : ψ g = 1) (x : Fin D.R.r → KmodO (D.ntw.Ok i k)) :
    Gen.Trep i s k ψ g x = actDiv (Formalism.MainNotions.N.mapRep (toOk D i k) (latT D i s)) g x := by
  funext a
  have h : ∀ b, ((Formalism.MainNotions.N.mapRep (toOk D i k) (latT D i s) g : GL _ _) : Matrix _ _ _) a b =
      Gen.phiK D.ntw i k (Gen.Tmat i s g a b) := by
    intro b
    rw [← Gen.Tgl_coe]
    rfl
  simp only [actDiv, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply, h]
  simp only [Gen.Trep, twRep, MonoidHom.coe_mk, OneHom.coe_mk, hg, inv_one, one_mul, LinearMap.smul_apply,
    Pi.smul_apply, matAct, LinearMap.coe_mk, AddHom.coe_mk, Finset.smul_sum, smul_smul, Gen.Tmat,
    Matrix.smul_apply, smul_eq_mul, map_mul, Matrix.map_apply]
  rfl

theorem mem_of_mk_mem_span {R G M : Type} [CommRing R] [Group G] [TopologicalSpace G] [AddCommGroup M]
    [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M]
    (ρ : Representation R G M) (S : Submodule R (G → M)) (hB : ∀ x : M, (fun g => ρ g x - x) ∈ S)
    (A : Set (ReciprocityTheory.Gal.H1 ρ))
    (hA : ∀ x ∈ A, ∃ w : ReciprocityTheory.Gal.Z1 ρ, (w : G → M) ∈ S ∧ x = Submodule.Quotient.mk w)
    (w : ReciprocityTheory.Gal.Z1 ρ) (hw : Submodule.Quotient.mk w ∈ Submodule.span R A) : (w : G → M) ∈ S := by
  have hB' : (ReciprocityTheory.Gal.B1 ρ).comap (ReciprocityTheory.Gal.Z1 ρ).subtype ≤ S.comap (ReciprocityTheory.Gal.Z1 ρ).subtype := by
    intro w hw
    obtain ⟨x, hx⟩ := (mem_coboundaries1 ρ _).1 hw
    have : (ReciprocityTheory.Gal.Z1 ρ).subtype w = fun g => ρ g x - x := funext hx
    rw [Submodule.mem_comap, this]
    exact hB x
  have hle : Submodule.span R A ≤ (S.comap (ReciprocityTheory.Gal.Z1 ρ).subtype).map (Submodule.mkQ _) := by
    rw [Submodule.span_le]
    intro x hx
    obtain ⟨w, hw, rfl⟩ := hA x hx
    exact ⟨w, hw, rfl⟩
  have h2 : w ∈ ((S.comap (ReciprocityTheory.Gal.Z1 ρ).subtype).map
      (Submodule.mkQ ((ReciprocityTheory.Gal.B1 ρ).comap (ReciprocityTheory.Gal.Z1 ρ).subtype))).comap (Submodule.mkQ _) :=
    hle hw
  rw [Submodule.comap_map_mkQ, sup_eq_right.2 hB'] at h2
  exact h2

theorem mem_bkAt_of_mem_bk : ∀ (D : D7) (i : D.ntw.Tw) (s : D.ntw.Sig i) (k : ℕ) (ψ : GE D →* (D.ntw.Ok i k)ˣ) (v : PlE D.host) (hv : v ∈ placesOver D.host.E (D.ntw.l i)), (∀ σ ∈ decAt D v, ψ σ = 1) → ∀ z : ReciprocityTheory.Gal.Z1 (Gen.Trep i s k ψ), ReciprocityTheory.Gal.resH1 (Gen.Trep i s k ψ) (decAt D v).subtype continuous_subtype_val (Submodule.Quotient.mk z) ∈ Gen.bk (bk0 D) i s k ψ v → (z : GE D → Fin D.R.r → KmodO (D.ntw.Ok i k)) ∈ bkAt (D.ntwbr i v hv) (D.loc (D.ntw.l i)) (toOk D i k) (latT D i s) := by
  intro D i s k ψ v hv hψ z hz
  replace hz := ((Gen.bk.eq_1 (bk0 D) i s k ψ v).trans (dif_pos hv)).le hz
  refine mem_of_mk_mem_span ((Gen.Trep i s k ψ).comp (decAt D v).subtype)
    (crysSpan (D.ntwbr i v hv) (D.loc (D.ntw.l i)) (toOk D i k) (latT D i s) ⊔
      cobOn ((Formalism.MainNotions.N.mapRep (toOk D i k) (latT D i s)).comp (decAt D v).subtype) ⊤) ?_ _ ?_
    (restrictCocycles1 (Gen.Trep i s k ψ) (decAt D v).subtype continuous_subtype_val z) hz
  · intro x
    refine Submodule.mem_sup_right ⟨x, fun g _ => ?_⟩
    exact congrArg (· - x) (Trep_eq_actDiv D i s k ψ g (hψ g g.2) x)
  · rintro x ⟨w, c, y, hc, hy, hw, hx⟩
    refine ⟨w, Submodule.mem_sup_left ?_, hx⟩
    exact mem_crysSpan_of_rational (D.ntwbr i v hv) (D.loc (D.ntw.l i))
      (toOk D i k) ((D.ntw.Ok_inj i k).comp (D.ntw.O_inj i)) (latT D i s) c hc y hy _ hw

end GlobalTheory.BlochKatoIntegralScalars
