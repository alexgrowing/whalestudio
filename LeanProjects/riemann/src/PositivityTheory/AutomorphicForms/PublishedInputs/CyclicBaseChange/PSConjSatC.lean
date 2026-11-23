import PositivityTheory.AutomorphicForms.PublishedInputs.CyclicBaseChange.SConjSpaceC
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSplitChartSplitChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedFactorEqProductAbove
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryClassSetFinite
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfIsOpenStab
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalComponentsThetaPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzFinitePureTensors
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep

namespace UpperTheory.CBC.SConjSatCAux

theorem hasSatGL_of_linEquiv {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {n : ℕ}
    {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V} {ρ' : Representation ℂ (GL (Fin n) (w.adicCompletion E)) W}
    (T : V ≃ₗ[ℂ] W) (hf : ∀ g y, T.toLinearMap (ρ g y) = ρ' g (T.toLinearMap y)) {B : Multiset ℂˣ}
    (hB : GlobalTheory.LFun.HasSatGL w ρ B) : GlobalTheory.LFun.HasSatGL w ρ' B := by
  constructor
  · obtain ⟨x, hx⟩ := hB.exists_vec
    have h1 := hx.map T.toLinearMap hf ((map_ne_zero_iff T T.injective).2 hx.1)
    exact (Submodule.ne_bot_iff _).2 ⟨_, h1.2.1, h1.1⟩
  · intro y hy h0
    obtain ⟨x, rfl⟩ := T.surjective y
    refine (hB.2 x (GlobalTheory.LGrp.mem_fixed.2 fun k hk => T.injective ?_) fun e => h0 (by rw [e, map_zero])).map
      T.toLinearMap hf h0
    exact (hf k x).trans (GlobalTheory.LGrp.mem_fixed.1 hy k hk)

theorem conjSrc_conjSrc_symm {E : Type} [Field E] [NumberField E] (c : E ≃+* E) (w : HeightOneSpectrum (𝓞 E)) :
    conjSrc c (conjSrc c.symm w) = w := by
  refine (eq_conjSrc ((GlobalTheory.Mem.Chr.conjPl_iff_comap _ _ _).2 ?_)).symm
  rw [(GlobalTheory.Mem.Chr.conjPl_iff_comap _ _ _).1 (conjPl_conjSrc c.symm w)]
  ext x
  rw [Ideal.mem_comap, Ideal.mem_comap]
  have e : (RingOfIntegers.mapRingEquiv c.symm) ((RingOfIntegers.mapRingEquiv c) x) = x := by
    ext
    simp
  rw [e]

variable {M : Type} [Field M] [NumberField M] [IsTotallyComplex M]

theorem pInf_s_sFin (s : Ad M ≃+* Ad M) (hs : Continuous s) (y : Af M) : pInf M (s (sFin M y)) = 0 := by
  let f : Af M →+ Cinf M :=
    { toFun := fun y => pInf M (s (sFin M y))
      map_zero' := by simp
      map_add' := fun a b => by simp [map_add] }
  have hf : Continuous f := by
    have h1 : Continuous fun y : Af M => (sFin M y : Ad M) :=
      (continuous_const.prodMk continuous_id : Continuous fun y : Af M => ((0 : InfiniteAdeleRing M), y))
    show Continuous fun y : Af M => pInf M (s (sFin M y))
    exact (GlobalTheory.CuspRep.ContAut.continuous_pInf (E := M)).comp (hs.comp h1)
  have hint : ∀ z ∈ GlobalTheory.SchADecomp.intA M, f z = 0 := by
    intro z hz
    funext τ
    obtain ⟨C, hC⟩ := (GlobalTheory.SchADecomp.isCompact_intA (F := M)).exists_bound_of_continuousOn
      ((continuous_apply τ).comp hf).continuousOn
    by_contra h0
    have hpos : 0 < ‖f z τ‖ := norm_pos_iff.2 h0
    obtain ⟨m, hm⟩ := exists_nat_gt (C / ‖f z τ‖)
    have h2 := hC (m • z) (AddSubgroup.nsmul_mem _ hz m)
    rw [Function.comp_apply, map_nsmul, Pi.smul_apply, nsmul_eq_mul, norm_mul, Complex.norm_natCast] at h2
    rw [div_lt_iff₀ hpos] at hm
    linarith
  obtain ⟨N, hN, hNy⟩ := GlobalTheory.WeilM.exists_nat_mul_integral_of_isCompact M (κ := Unit)
    (isCompact_singleton (x := fun _ : Unit => y))
  have hmem : (N : Af M) * y ∈ GlobalTheory.SchADecomp.intA M := fun v => hNy _ (Set.mem_singleton _) () v
  have h3 := hint _ hmem
  rw [← nsmul_eq_mul, map_nsmul] at h3
  show f y = 0
  funext τ
  have h4 := congrFun h3 τ
  rw [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul] at h4
  exact (mul_eq_zero.1 h4).resolve_left (by exact_mod_cast hN.ne')

theorem s_sFin (σ : M ≃+* M) (s : Ad M ≃+* Ad M) (hs : IsGalAd σ s) (y : Af M) :
    s (sFin M y) = sFin M (conjFin σ y) := by
  refine ad_ext ?_ ?_
  · rw [pInf_s_sFin s hs.1]
    exact (map_zero (infEq M).symm).symm
  · exact hs.2.2 _

theorem map_finGL (σ : M ≃+* M) (s : Ad M ≃+* Ad M) (hs : IsGalAd σ s) {n : ℕ} (k : GL (Fin n) (Af M)) :
    Matrix.GeneralLinearGroup.map s.toRingHom (finGL M n k) =
      finGL M n (Matrix.GeneralLinearGroup.map (conjFin σ) k) := by
  ext i j
  change s ((1 : Matrix (Fin n) (Fin n) (Ad M)) i j - sFin M ((1 : Matrix (Fin n) (Fin n) (Af M)) i j) +
      sFin M (k.1 i j)) = (1 : Matrix (Fin n) (Fin n) (Ad M)) i j -
      sFin M ((1 : Matrix (Fin n) (Fin n) (Af M)) i j) + sFin M (conjFin σ (k.1 i j))
  have e1 : s ((1 : Matrix (Fin n) (Fin n) (Ad M)) i j) = (1 : Matrix (Fin n) (Fin n) (Ad M)) i j := by
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  have e2 : conjFin σ ((1 : Matrix (Fin n) (Fin n) (Af M)) i j) = (1 : Matrix (Fin n) (Fin n) (Af M)) i j := by
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  rw [map_add, map_sub, e1, s_sFin σ s hs, s_sFin σ s hs, e2]

theorem main (σ : M ≃+* M) (s : Ad M ≃+* Ad M) (hs : IsGalAd σ s) {n : ℕ} (P P' : CuspSub M n)
    (hsp : (Cusp.cx P').space =
      (fun f : GA M n → ℂ => fun g => f (Matrix.GeneralLinearGroup.map s.toRingHom g)) '' (Cusp.cx P).space)
    (v : HeightOneSpectrum (𝓞 M)) {B : Multiset ℂˣ} (hB : GlobalTheory.LFun.HasSatGL v (P.locRep v) B) :
    GlobalTheory.LFun.HasSatGL (conjSrc σ v) (P'.locRep (conjSrc σ v)) B := by
  set S : GA M n →* GA M n := Matrix.GeneralLinearGroup.map s.toRingHom with hS
  have hSs : ∀ g, S (Matrix.GeneralLinearGroup.map s.symm.toRingHom g) = g := fun g => by
    ext i j
    exact s.apply_symm_apply _
  have hfwd : ∀ φ : Sm M n, φ ∈ P.V → ∃ ψ : Sm M n, ψ ∈ P'.V ∧ (fun g => φ.1 (S g)) = ψ.1 := fun φ hφ => by
    have h : (fun g => φ.1 (S g)) ∈ (Cusp.cx P').space := hsp ▸ ⟨φ.1, ⟨φ, hφ, rfl⟩, rfl⟩
    obtain ⟨ψ, hψ, e⟩ := h
    exact ⟨ψ, hψ, e⟩
  have hbwd : ∀ ψ : Sm M n, ψ ∈ P'.V → ∃ φ : Sm M n, φ ∈ P.V ∧ ψ.1 = fun g => φ.1 (S g) := fun ψ hψ => by
    have h : ψ.1 ∈ (Cusp.cx P').space := ⟨ψ, hψ, rfl⟩
    rw [hsp] at h
    obtain ⟨f, ⟨φ, hφ, rfl⟩, e⟩ := h
    exact ⟨φ, hφ, e.symm⟩
  have hT : ∀ φ : P.V, ∃ h : (fun g => φ.1.1 (S g)) ∈ Sm M n, (⟨_, h⟩ : Sm M n) ∈ P'.V := fun φ => by
    obtain ⟨ψ, hψ, e⟩ := hfwd φ.1 φ.2
    have h : (fun g => φ.1.1 (S g)) ∈ Sm M n := by rw [e]; exact ψ.2
    refine ⟨h, ?_⟩
    have e2 : (⟨_, h⟩ : Sm M n) = ψ := Subtype.ext e
    rw [e2]
    exact hψ
  let T : P.V →ₗ[ℂ] P'.V :=
    { toFun := fun φ => ⟨⟨_, (hT φ).1⟩, (hT φ).2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hTinj : Function.Injective T := fun φ φ' e => by
    have e1 : (fun g => φ.1.1 (S g)) = fun g => φ'.1.1 (S g) := congrArg (fun x : P'.V => x.1.1) e
    refine Subtype.ext (Subtype.ext (funext fun g => ?_))
    have := congrFun e1 (Matrix.GeneralLinearGroup.map s.symm.toRingHom g)
    simpa only [hSs] using this
  have hTsurj : Function.Surjective T := fun ψ => by
    obtain ⟨φ, hφ, e⟩ := hbwd ψ.1 ψ.2
    exact ⟨⟨φ, hφ⟩, Subtype.ext (Subtype.ext e.symm)⟩
  let TE : P.V ≃ₗ[ℂ] P'.V := LinearEquiv.ofBijective T ⟨hTinj, hTsurj⟩
  have hinter : ∀ (k : GL (Fin n) ((conjSrc σ v).adicCompletion M)) (y : P.V),
      T (P.locRep v (Matrix.GeneralLinearGroup.map (conjLoc σ v) k) y) = P'.locRep (conjSrc σ v) k (T y) := by
    intro k y
    apply Subtype.ext
    apply Subtype.ext
    funext g
    rw [CuspSub.locRep_eq, CuspSub.locRep_eq]
    change y.1.1 (S g * finGL M n (locGL M n v (Matrix.GeneralLinearGroup.map (conjLoc σ v) k))) =
      y.1.1 (S (g * finGL M n (locGL M n (conjSrc σ v) k)))
    rw [map_mul, hS, map_finGL σ s hs, GlobalTheory.ConjPairLoc.conjFin_locGL]
  let ψ : (conjSrc σ v).adicCompletion M ≃+* v.adicCompletion M :=
    RingEquiv.ofBijective (conjLoc σ v) ⟨(conjLoc σ v).injective, GlobalTheory.CuspRep.ParLaws.conjLoc_surjective σ v⟩
  let ψ₀ : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv M v ≃+* (conjSrc σ v).adicCompletion M := ψ.symm
  have h3 : ∀ a : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv M v, Valued.v (ψ₀ a) = Valued.v a := fun a => by
    have := (conjLoc_spec σ v).2.2 (ψ₀ a)
    have e : conjLoc σ v (ψ₀ a) = a := ψ.apply_symm_apply a
    rw [e] at this
    exact this.symm
  have hq : Formalism.UG.qV M (conjSrc σ v) = Formalism.UG.qV M v := GlobalTheory.UnrEuler.ConjFac.absNorm_conjSrc σ v
  have hk : ∀ k, (GlobalTheory.LFun.SplitTie.glEquiv n ψ₀).symm k = Matrix.GeneralLinearGroup.map (conjLoc σ v) k :=
    fun k => by ext i j; rfl
  have hK := GlobalTheory.LFun.SplitTie.mem_KGL_iff (n := n) h3
  let ρ'' := (P.locRep v).comp (GlobalTheory.LFun.SplitTie.glEquiv n ψ₀).symm.toMonoidHom
  have hfix : ∀ x, x ∈ GlobalTheory.PRep.fixed ρ'' (GlobalTheory.LFun.KGL (conjSrc σ v) n) ↔
      x ∈ GlobalTheory.PRep.fixed (P.locRep v) (GlobalTheory.LFun.KGL v n) := fun x => GlobalTheory.LFun.mem_fixed_comp_symm _ hK
  have hB'' : GlobalTheory.LFun.HasSatGL (conjSrc σ v) ρ'' B := by
    refine ⟨?_, fun x hx h0 => (GlobalTheory.LFun.SplitTie.isSatVecGL_comp_symm h3 hq _ x B).2 (hB.2 x ((hfix x).1 hx) h0)⟩
    obtain ⟨x, hx⟩ := hB.exists_vec
    exact (Submodule.ne_bot_iff _).2 ⟨x, (hfix x).2 hx.2.1, hx.1⟩
  refine hasSatGL_of_linEquiv TE (fun k y => ?_) hB''
  change T (P.locRep v ((GlobalTheory.LFun.SplitTie.glEquiv n ψ₀).symm k) y) = _
  rw [hk]
  exact hinter k y

end UpperTheory.CBC.SConjSatCAux

open UpperTheory.CBC in
theorem UpperTheory.CBC.SConjSatC_holds : UpperTheory.CBC.SConjSatC := by
  intro K M _ _ _ _ _ _ σ s hs n P P' hsp
  have hc : ∀ x : K, σ.toRingEquiv.symm (algebraMap K M x) = algebraMap K M x := fun x => σ.symm.commutes x
  refine ⟨conjSrc σ.toRingEquiv.symm, conjSrc_injective _, fun w => GlobalTheory.DefU.ClassFin.under_conjSrc _ hc w,
    fun w => GlobalTheory.UnrEuler.ConjFac.absNorm_conjSrc _ w, Filter.Eventually.of_forall fun w B hB => ?_⟩
  have h := UpperTheory.CBC.SConjSatCAux.main σ.toRingEquiv s hs P P' hsp (conjSrc σ.toRingEquiv.symm w)
    ((CG.hasSat_mk _ _ _).1 hB)
  rw [UpperTheory.CBC.SConjSatCAux.conjSrc_conjSrc_symm] at h
  exact (CG.hasSat_mk _ _ _).2 h
