import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsFCocIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CohDimTwoLocalOfLocalFiniteness
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LocalGaloisRepInvariantsFromFractionRing
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TateH2IffAllFiniteExtensions
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousAlgebraMapPadicInt
import Development.AbelianVarietyTheory.Counterexamples.NonGaloisSurvey.CrystallineCharacterRatio

noncomputable section

namespace GlobalTheory.BKLatticeCochain

section General

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions TensorProduct Matrix

variable {LL O : Type} [Field LL] [CommRing O] [Algebra O LL] {r : ℕ}

variable (LL) in

def incl : (Fin r → O) →ₗ[O] (Fin r → LL) := (Algebra.linearMap O LL).compLeft (Fin r)

theorem incl_apply (z : Fin r → O) (a : Fin r) : incl LL z a = algebraMap O LL (z a) := rfl

theorem incl_mulVec (M : Matrix (Fin r) (Fin r) O) (z : Fin r → O) :
    (M.map (algebraMap O LL)).mulVec (incl LL z) = incl LL (M.mulVec z) := by
  funext a
  simp [incl_apply, Matrix.mulVec, dotProduct]

theorem incl_dot (z z' : Fin r → O) : incl LL z ⬝ᵥ incl LL z' = algebraMap O LL (z ⬝ᵥ z') := by
  simp [incl_apply, dotProduct]

theorem mem_range_incl (x : Fin r → LL) :
    x ∈ LinearMap.range (incl (O := O) LL) ↔ ∀ a, ∃ o : O, algebraMap O LL o = x a := by
  constructor
  · rintro ⟨z, rfl⟩ a
    exact ⟨z a, rfl⟩
  · intro h
    choose z hz using h
    exact ⟨z, funext hz⟩

def stdLattice {G : Type} [Group G] (hinj : Function.Injective (algebraMap O LL))
    (ρ : Representation LL G (Fin r → LL))
    (h : ∀ g, ∃ M : Matrix (Fin r) (Fin r) O, ∀ x, ρ g x = (M.map (algebraMap O LL)).mulVec x) :
    Lattice (O := O) ρ where
  T := LinearMap.range (incl LL)
  stable := by
    rintro g x ⟨z, rfl⟩
    obtain ⟨M, hM⟩ := h g
    exact ⟨M.mulVec z, by rw [hM, incl_mulVec]⟩
  fg := by
    rw [LinearMap.range_eq_map]
    exact Submodule.FG.map _ Module.Finite.fg_top
  free := Module.Free.of_equiv (LinearEquiv.ofInjective (incl (O := O) (r := r) LL)
    fun z z' h => funext fun a => hinj (congrFun h a))
  span := by
    rw [eq_top_iff, ← (Pi.basisFun LL (Fin r)).span_eq]
    refine Submodule.span_mono ?_
    rintro _ ⟨a, rfl⟩
    refine (mem_range_incl _).2 fun b => ?_
    by_cases hab : b = a
    · exact ⟨1, by simp [hab]⟩
    · exact ⟨0, by simp [hab]⟩

theorem inv_smul_mem_iff [IsDomain O] [IsDiscreteValuationRing O] (hinj : Function.Injective (algebraMap O LL))
    {ϖ : O} (hϖ : Irreducible ϖ) (u : Fin r → O) :
    (algebraMap O LL ϖ)⁻¹ • incl LL u ∈ LinearMap.range (incl (O := O) LL) ↔
      ∀ a, u a ∈ IsLocalRing.maximalIdeal O := by
  have h0 : algebraMap O LL ϖ ≠ 0 := fun h => hϖ.ne_zero (hinj (h.trans (map_zero _).symm))
  rw [mem_range_incl, hϖ.maximalIdeal_eq]
  refine forall_congr' fun a => ?_
  rw [Ideal.mem_span_singleton', Pi.smul_apply, incl_apply, smul_eq_mul]
  refine exists_congr fun o => ?_
  rw [eq_inv_mul_iff_mul_eq₀ h0, ← map_mul, hinj.eq_iff, mul_comm]

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) [Algebra Qp LL]

theorem coboundary_mem_blochKatoCocycles {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V] (ρ : Representation LL G V) (m : V)
    (hm : Continuous fun g => ρ g m) : (fun g => ρ g m - m) ∈ finiteCocycles PD ρ := by
  refine ⟨⟨?_, fun g h => ?_⟩, m ⊗ₜ[Qp] (1 : B), fun g => ?_⟩
  · simp_rw [sub_eq_add_neg]
    exact hm.add continuous_const
  · simp only [map_mul, Module.End.mul_apply, map_sub]
    abel
  · simp [actVB, sub_tmul]

theorem mem_HfD_iff {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [Module O V] [IsScalarTower O LL V]
    [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V] {ρ : Representation LL G V}
    (L : Lattice (O := O) ρ) (hρ : ∀ m, Continuous fun g => ρ g m) (c : G → V ⧸ L.T) :
    c ∈ HfD PD L ↔ ∃ z ∈ finiteCocycles PD ρ, ∀ g, c g = Submodule.Quotient.mk (z g) := by
  constructor
  · intro h
    obtain ⟨_, ⟨z, hz, rfl⟩, _, ⟨m, rfl⟩, rfl⟩ := Submodule.mem_sup.1 h
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    exact ⟨z + fun g => ρ g m - m, (finiteCocycles PD ρ).add_mem hz (coboundary_mem_blochKatoCocycles PD ρ m (hρ m)), fun g => rfl⟩
  · rintro ⟨z, hz, h⟩
    exact Submodule.mem_sup_left ⟨z, hz, funext fun g => (h g).symm⟩

variable {H : Type} [Group H] [TopologicalSpace H] (e : H ≃* G) (he : Continuous e) (he' : Continuous e.symm)

include he he' in

theorem cobO_iff [IsDomain O] [IsFractionRing O LL] (L1 : Lattice (O := O) (charRep (cycLL PD LL)))
    (hL : L1.T = LinearMap.range (Algebra.linearMap O LL)) (χ : H → O)
    (hχ : ∀ g, algebraMap O LL (χ g) = ((cycLL PD LL (e g) : LLˣ) : LL)) (z : G × G → LL)
    (w : H → H → FractionRing O)
    (hz : ∀ g h, ∃ o : O, z (e g, e h) = FractionRing.algEquiv O LL (w g h) + algebraMap O LL o) :
    CobO PD L1 z ↔ ∃ f : H → KmodO O, IsLocallyConstant f ∧ ∀ g h,
      (Submodule.Quotient.mk (w g h) : KmodO O) = χ g • f h - f (g * h) + f g := by
  let q : KmodO O ≃ₗ[O] (LL ⧸ L1.T) :=
    Submodule.Quotient.equiv _ _ (FractionRing.algEquiv O LL).toLinearEquiv (by
      rw [hL, ← LinearMap.range_comp]
      congr 1
      ext
      simp)
  have hq : ∀ g h, (Submodule.Quotient.mk (z (e g, e h)) : LL ⧸ L1.T) = q (Submodule.Quotient.mk (w g h)) := by
    intro g h
    obtain ⟨o, ho⟩ := hz g h
    change _ = (Submodule.Quotient.mk (FractionRing.algEquiv O LL (w g h)) : LL ⧸ L1.T)
    rw [Submodule.Quotient.eq, ho, add_sub_cancel_left, hL]
    exact ⟨o, rfl⟩
  have hr : ∀ g x, repD L1 (e g) x = χ g • x := by
    intro g x
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [← Submodule.Quotient.mk_smul, Algebra.smul_def, hχ]
    rfl
  constructor
  · rintro ⟨f, ⟨hf, -⟩, h⟩
    refine ⟨fun g => q.symm (f (e g)), (hf.comp_continuous he).comp q.symm, fun g g' => ?_⟩
    apply q.injective
    have h1 : repD L1 (e g) (f (e g')) - f (e g * e g') + f (e g) = _ := congrFun h (e g, e g')
    rw [← hq, ← h1, hr]
    simp
  · rintro ⟨f, hf, h⟩
    refine ⟨fun g => q (f (e.symm g)), ⟨(hf.comp_continuous he').comp q, fun _ => trivial⟩, ?_⟩
    funext ⟨g, g'⟩
    obtain ⟨g, rfl⟩ := e.surjective g
    obtain ⟨g', rfl⟩ := e.surjective g'
    change repD L1 (e g) (q (f (e.symm (e g')))) - q (f (e.symm (e g * e g'))) + q (f (e.symm (e g))) = _
    rw [hq, h, hr, ← map_mul]
    simp

def vecRep [TopologicalSpace LL] [IsTopologicalRing LL] (ρ : Representation LL G (Fin r → LL))
    (hρ : ∀ x, Continuous fun g => ρ g x) : GRep G Qp LL O where
  V := Fin r → LL
  ρ := ρ
  cont := hρ

include he he' in

theorem lift_iff [TopologicalSpace Qp] [TopologicalSpace LL] [IsTopologicalRing LL] [IsDomain O]
    [IsDiscreteValuationRing O] (hG : GoodO (Qp := Qp) LL O) (hBK : bkBCore PD)
    (ρ ρ' : Representation LL G (Fin r → LL)) (M M' : H → Matrix (Fin r) (Fin r) O) (χ : H → O)
    (hρ : ∀ g x, ρ (e g) x = ((M g).map (algebraMap O LL)).mulVec x)
    (hρ' : ∀ g x, ρ' (e g) x = ((M' g).map (algebraMap O LL)).mulVec x)
    (cρ : ∀ x, Continuous fun g => ρ g x) (cρ' : ∀ x, Continuous fun g => ρ' g x)
    (hχ : ∀ g, algebraMap O LL (χ g) = ((cycLL PD LL (e g) : LLˣ) : LL))
    (hM : ∀ g, (M g).transpose * M' g = χ g • (1 : Matrix (Fin r) (Fin r) O)) (hdR : IsDR PD ρ)
    (ϖ : O) (hϖ : Irreducible ϖ) (y : H → Fin r → O)
    (hy : ∀ a, IsLocallyConstant fun g => IsLocalRing.residue O (y g a))
    (hyc : ∀ g h a, y (g * h) a - (y g a + (M' g).mulVec (y h) a) ∈ IsLocalRing.maximalIdeal O) :
    (∃ y' : H → Fin r → O, (fun g a => algebraMap O LL (y' (e.symm g) a)) ∈ finiteCocycles PD ρ' ∧
        ∀ g a, y' g a - y g a ∈ IsLocalRing.maximalIdeal O) ↔
      ∀ d : H → Fin r → O, (fun g a => algebraMap O LL (d (e.symm g) a)) ∈ finiteCocycles PD ρ →
        ∃ f : H → KmodO O, IsLocallyConstant f ∧ ∀ g h,
          (Submodule.Quotient.mk ((algebraMap O (FractionRing O) ϖ)⁻¹ *
            algebraMap O (FractionRing O) (d g ⬝ᵥ (M' g).mulVec (y h))) : KmodO O) =
            χ g • f h - f (g * h) + f g := by
  obtain ⟨_, -, hfr⟩ := hG.1
  have hinj : Function.Injective (algebraMap O LL) := IsFractionRing.injective O LL
  have h0 : algebraMap O LL ϖ ≠ 0 := fun h => hϖ.ne_zero (hinj (h.trans (map_zero _).symm))
  let L1 := GlobalTheory.TateTopCompare.rangeLattice (O := O) hinj (cycLL PD LL) fun g => ⟨χ (e.symm g), by
    rw [hχ, e.apply_symm_apply]⟩
  let L := stdLattice hinj ρ fun g => ⟨M (e.symm g), fun x => by rw [← hρ, e.apply_symm_apply]⟩
  let L' := stdLattice hinj ρ' fun g => ⟨M' (e.symm g), fun x => by rw [← hρ', e.apply_symm_apply]⟩
  have hD : IsDualLat1 PD L L' (dotProductBilin LL LL) := by
    refine ⟨⟨fun g x x' => ?_, fun x hx => ?_, fun x hx => ?_, rfl⟩, fun x => ⟨?_, fun h => ?_⟩⟩
    · obtain ⟨g, rfl⟩ := e.surjective g
      change ρ (e g) x ⬝ᵥ ρ' (e g) x' = _ * (x ⬝ᵥ x')
      rw [hρ, hρ', ← hχ, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
        ← Matrix.transpose_map, ← Matrix.map_mul, hM]
      simp [Matrix.smul_one_eq_diagonal, Matrix.diagonal_map, dotProduct, Matrix.mulVec_diagonal, Finset.mul_sum,
        mul_left_comm]
    · funext a
      simpa using hx (Pi.single a 1)
    · funext a
      simpa using hx (Pi.single a 1)
    · rintro ⟨z, rfl⟩ _ ⟨z', rfl⟩
      exact ⟨_, incl_dot z' z⟩
    · refine (mem_range_incl _).2 fun a => ?_
      obtain ⟨o, ho⟩ := h (incl LL (Pi.single a (1 : O))) ⟨_, rfl⟩
      refine ⟨o, ?_⟩
      rw [← ho]
      simp [incl_apply, dotProduct, Pi.single_apply, apply_ite (algebraMap O LL)]
  let c : G → (Fin r → LL) ⧸ L'.T := fun g =>
    Submodule.Quotient.mk ((algebraMap O LL ϖ)⁻¹ • incl LL (y (e.symm g)))
  have key : ∀ u u' : Fin r → O, (Submodule.Quotient.mk ((algebraMap O LL ϖ)⁻¹ • incl LL u) : (Fin r → LL) ⧸ L'.T) =
      Submodule.Quotient.mk ((algebraMap O LL ϖ)⁻¹ • incl LL u') ↔ ∀ a, u a - u' a ∈ IsLocalRing.maximalIdeal O := by
    intro u u'
    rw [Submodule.Quotient.eq, ← smul_sub, ← map_sub]
    exact inv_smul_mem_iff hinj hϖ _
  have hc : c ∈ divisibleCocycles L' := by
    constructor
    · refine IsLocallyConstant.comp_continuous (f := e.symm) (g := fun g => (Submodule.Quotient.mk
        ((algebraMap O LL ϖ)⁻¹ • incl LL (y g)) : (Fin r → LL) ⧸ L'.T)) ?_ he'
      rw [IsLocallyConstant.iff_eventually_eq]
      intro g
      have := Filter.eventually_all.2 fun a => (hy a).eventually_eq g
      filter_upwards [this] with g' hg'
      refine (key _ _).2 fun a => ?_
      rw [← IsLocalRing.residue_eq_zero_iff, map_sub, hg' a, sub_self]
    · intro g g'
      obtain ⟨g, rfl⟩ := e.surjective g
      obtain ⟨g', rfl⟩ := e.surjective g'
      change (Submodule.Quotient.mk _ : (Fin r → LL) ⧸ L'.T) =
        Submodule.Quotient.mk (_ + ρ' (e g) ((algebraMap O LL ϖ)⁻¹ • incl LL (y (e.symm (e g')))))
      rw [map_smul, hρ', incl_mulVec, ← smul_add, ← map_add, key, ← map_mul]
      simp only [MulEquiv.symm_apply_apply]
      exact hyc g g'
  have main : c ∈ HfD PD L' ↔ ∀ d ∈ latticeFiniteCocycles PD L, CobO PD L1 (cupLD L' (dotProductBilin LL LL) d c) :=
    (hBK LL O hG L1 rfl (vecRep ρ cρ) (vecRep ρ' cρ') L L' (dotProductBilin LL LL) hdR hD).1 c hc
  have cup : ∀ d : H → Fin r → O, CobO PD L1 (cupLD L' (dotProductBilin LL LL) (fun g => incl LL (d (e.symm g))) c) ↔ _ :=
    fun d => cobO_iff PD e he he' L1 rfl χ hχ _ (fun g h => (algebraMap O (FractionRing O) ϖ)⁻¹ *
      algebraMap O (FractionRing O) (d g ⬝ᵥ (M' g).mulVec (y h))) fun g h => by
        have h1 : (Submodule.Quotient.mk (liftD L' (c (e h))) : (Fin r → LL) ⧸ L'.T) = c (e h) :=
          (Submodule.Quotient.mk_surjective L'.T (c (e h))).choose_spec
        obtain ⟨t, ht⟩ := (Submodule.Quotient.eq _).1 h1
        refine ⟨d g ⬝ᵥ (M' g).mulVec t, ?_⟩
        change incl LL (d (e.symm (e g))) ⬝ᵥ ρ' (e g) (liftD L' (c (e h))) = _
        rw [eq_sub_iff_add_eq] at ht
        rw [← ht, map_add, map_smul, hρ', hρ', incl_mulVec, incl_mulVec, dotProduct_add, dotProduct_smul, incl_dot,
          incl_dot, add_comm]
        simp
  refine Iff.trans ?_ (main.trans ?_)
  · rw [mem_HfD_iff PD L' cρ']
    constructor
    · rintro ⟨y', h1, h2⟩
      exact ⟨_, (finiteCocycles PD ρ').smul_mem (algebraMap O LL ϖ)⁻¹ h1, fun g => ((key _ _).2 (h2 _)).symm⟩
    · rintro ⟨z, hz, h⟩
      have h1 : ∀ g, ∃ t, incl LL t = (algebraMap O LL ϖ)⁻¹ • incl LL (y (e.symm g)) - z g :=
        fun g => (Submodule.Quotient.eq _).1 (h g)
      choose t ht using h1
      refine ⟨fun g => y g - ϖ • t (e g), ?_, fun g a => ?_⟩
      · convert (finiteCocycles PD ρ').smul_mem (algebraMap O LL ϖ) hz using 1
        funext g
        change incl LL (y (e.symm g) - ϖ • t (e (e.symm g))) = algebraMap O LL ϖ • z g
        rw [e.apply_symm_apply, map_sub, map_smul, ht, ← algebraMap_smul LL ϖ, smul_sub, smul_inv_smul₀ h0,
          sub_sub_cancel]
      · rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton']
        exact ⟨-t (e g) a, by simp [mul_comm]⟩
  · constructor
    · intro h d hd
      exact (cup d).1 (h _ ⟨⟨hd.1, fun g _ => ⟨_, rfl⟩⟩, hd⟩)
    · rintro h d ⟨⟨-, h1⟩, hd⟩
      choose t ht using fun g => h1 g (Set.mem_univ g)
      have h2 : d = fun g => incl LL (t (e (e.symm g))) := funext fun g => by
        rw [e.apply_symm_apply, ht]
      have h3 := h (fun g => t (e g)) (by
        have : d ∈ finiteCocycles PD ρ := hd
        rw [h2] at this
        exact this)
      rw [h2]
      exact (cup fun g => t (e g)).2 h3

end General

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.ResDual

theorem lift_iff_orthogonal : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), GalHyp bkP i s → ∀ ρ, IsDual i s ρ → ∀ (v : PlE D.host) (hv : v ∈ placesOver D.host.E (X.l i)) (ϖ : X.O0 i), Irreducible ϖ → ∀ y : ↥(DecV N v) → Fin D.R.r → X.O0 i, (∀ a, IsLocallyConstant fun g => IsLocalRing.residue (X.O0 i) (y g a)) → (∀ g h a, y (g * h) a - (y g a + (Tdual i s g.1).mulVec (y h) a) ∈ IsLocalRing.maximalIdeal (X.O0 i)) → ((∃ y', IsFCoc bkP i v hv ρ y' ∧ ∀ g a, y' g a - y g a ∈ IsLocalRing.maximalIdeal (X.O0 i)) ↔ ∀ d, IsFCoc bkP i v hv (Tgl i s) d → ∃ f : ↥(DecV N v) → Formalism.BasicNotions.KmodO (X.O0 i), IsLocallyConstant f ∧ ∀ g h, (Submodule.Quotient.mk ((algebraMap (X.O0 i) (FractionRing (X.O0 i)) ϖ)⁻¹ * algebraMap (X.O0 i) (FractionRing (X.O0 i)) (d g ⬝ᵥ (Tdual i s g.1).mulVec (y h))) : Formalism.BasicNotions.KmodO (X.O0 i)) = ((eps0 X i g.1 : (X.O0 i)ˣ) : X.O0 i) • f h - f (g * h) + f g) := by
  intro D N X bkP i s h ρ hρ v hv ϖ hϖ y hy hyc
  let Bw := bkP.br i v hv
  letI : Algebra (X.O0 i) ↥Bw.LL.1 := Bw.toLL.toAlgebra
  have hG0 := (GlobalTheory.LocalIntegers.good_integers (X.l i) Bw.LL).1
  haveI : IsTopologicalRing ↥Bw.LL.1 := hG0.2.2.2.1
  have hG : Formalism.MainNotions.N.GoodO (Qp := ℚ_[X.l i]) ↥Bw.LL.1 (X.O0 i) := by
    obtain ⟨⟨_, -, hfr⟩, h1, h2, h3, h4⟩ := hG0
    refine ⟨⟨inferInstance, inferInstance, ?_⟩, h1, h2, h3, ?_⟩
    · exact IsFractionRing.of_ringEquiv_left Bw.eO fun _ => rfl
    · convert h4 using 1
      exact Bw.eO.surjective.range_comp (algebraMap ↥(Loc.OL Bw.LL) ↥Bw.LL.1)
  refine lift_iff (PDv bkP i v hv) Bw.e Bw.e_cont Bw.e_symm_cont hG
    (h.2.2.2.2.2.1 (X.l i) Bw.Kw).2.2 (repV bkP i v hv (Tgl i s)) (repV bkP i v hv ρ)
    (fun g => Tmat i s g.1) (fun g => Tdual i s g.1) (fun g => ((eps0 X i g.1 : (X.O0 i)ˣ) : X.O0 i))
    (fun g x => ?_) (fun g x => ?_) (GlobalTheory.BKDimNoInv.rep_continuous Bw _ ?_) (GlobalTheory.BKDimNoInv.rep_continuous Bw _ ?_)
    (fun g => ?_) (fun g => ?_) ?_ ϖ hϖ y hy hyc
  · rw [GlobalTheory.BKDimNoInv.rep_apply, MulEquiv.symm_apply_apply, ← Tgl_coe]
    rfl
  · rw [GlobalTheory.BKDimNoInv.rep_apply, MulEquiv.symm_apply_apply, ← hρ]
    rfl
  · change Continuous fun g : ↥(DecV N v) => ((Tgl i s g.1 : GL (Fin D.R.r) (X.O0 i)) : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i))
    simp_rw [Tgl_coe]
    exact (GlobalTheory.PrimeToInertia.continuous_Tmat i s).comp continuous_subtype_val
  · change Continuous fun g : ↥(DecV N v) => ((ρ g.1 : GL (Fin D.R.r) (X.O0 i)) : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i))
    simp_rw [hρ _]
    exact (GlobalTheory.PrimeToInertia.continuous_Tdual i s).comp continuous_subtype_val
  · have h1 := (D.loc (X.l i)).PD_χ Bw.Kw (Bw.e g)
    have h2 := GlobalTheory.Survey.CrystallineCharacterRatio.chi_eq_cyc (D.loc (X.l i)) Bw.j g.1 (Bw.e g : Loc.GQ (X.l i)) (Bw.e_comm g)
    change algebraMap ↥(Loc.OL Bw.LL) ↥Bw.LL.1 (Bw.eO (algebraMap ℤ_[X.l i] (X.O0 i) _)) =
      algebraMap ℚ_[X.l i] ↥Bw.LL.1 ((((D.loc (X.l i)).PD Bw.Kw).χ (Bw.e g) : ℚ_[X.l i]ˣ) : ℚ_[X.l i])
    rw [h1, h2, Bw.eO_alg]
    rfl
  · have h3 : IsUnit (Tmat i s g.1).det := by
      rw [← Tgl_coe]; exact Matrix.isUnits_det_units _
    rw [Tdual, Matrix.mul_smul, ← Matrix.transpose_mul, Matrix.nonsing_inv_mul _ h3, Matrix.transpose_one]
  · have h1 := (h.1.2.1 v hv (Tgl i s) (Or.inr rfl)).1
    exact Eq.trans h1 (congrArg (Module.finrank ℚ_[X.l i] ↥Bw.Kw.1 * ·) (Module.finrank_fin_fun ↥Bw.LL.1).symm)

end GlobalTheory.BKLatticeCochain

end
