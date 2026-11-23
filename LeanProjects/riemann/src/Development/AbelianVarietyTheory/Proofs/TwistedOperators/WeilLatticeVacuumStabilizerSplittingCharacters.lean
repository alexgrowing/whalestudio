import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDetInt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemClosedSubgroupOfLocalStabilizerPairsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilOperatorLatticeStabiliserFixesVacuumNonsplitStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceWeilRepLatticeVacuumCharacterStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.VecInv
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.VecInv.Vac

theorem mul_det_sub_one {R n : Type} [CommRing R] [Fintype n] [DecidableEq n] (b : R) (M : Matrix n n R)
    (h : ∀ i j, b * (M - 1) i j = (M - 1) i j) : b * (M.det - 1) = M.det - 1 := by

  set I : Ideal R := LinearMap.ker (LinearMap.mulLeft R (b - 1)) with hI
  have mem : ∀ x, x ∈ I ↔ b * x = x := by
    intro x
    rw [hI, LinearMap.mem_ker, LinearMap.mulLeft_apply, sub_mul, one_mul, sub_eq_zero]
  have hmap : M.map (Ideal.Quotient.mk I) = (1 : Matrix n n R).map (Ideal.Quotient.mk I) := by
    ext i j
    simp only [Matrix.map_apply]
    rw [Ideal.Quotient.eq, mem, ← Matrix.sub_apply]
    exact h i j
  have hdet : Ideal.Quotient.mk I M.det = Ideal.Quotient.mk I (1 : Matrix n n R).det := by
    rw [RingHom.map_det, RingHom.map_det, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, hmap]
  rw [Matrix.det_one] at hdet
  exact (mem _).1 (Ideal.Quotient.eq.1 hdet)

variable {D : D7}

theorem cA_alg (a : AF D.host.F) :
    cA D (algebraMap (AF D.host.F) (AE D) a) = algebraMap (AF D.host.F) (AE D) a := by
  rw [Algebra.TensorProduct.algebraMap_apply]
  simp [cA, sigR]

theorem detAt_val (e : AE D) (he : e * e = e) (V : HSp D) (g : GA D V) :
    ((detAt e he V g : (AE D)ˣ) : AE D) = e * (Formalism.L2.Theta.mt V g).det + (1 - e) := rfl

theorem continuous_detAt (e : AE D) (he : e * e = e) (V : HSp D) : Continuous (detAt e he V) := by
  rw [Units.continuous_iff]
  constructor
  · have hf : (Units.val ∘ detAt e he V) = fun g => e * (Formalism.L2.Theta.mt V g).det + (1 - e) :=
      funext fun g => detAt_val e he V g
    rw [hf]
    exact (continuous_const.mul (GlobalTheory.LatNhds.continuous_mt V).matrix_det).add continuous_const
  · have hf : (fun g => (((detAt e he V g)⁻¹ : (AE D)ˣ) : AE D)) =
        fun g => e * (Formalism.L2.Theta.mt V g⁻¹).det + (1 - e) := by
      funext g
      rw [← map_inv, detAt_val]
    rw [hf]
    exact (continuous_const.mul (GlobalTheory.LatNhds.continuous_mt_inv V).matrix_det).add continuous_const

theorem finPart_detAt {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {g : GA D V} (hg : Stab V β g) (e : AE D)
    (he : e * e = e) : finPart D ((detAt e he V g : (AE D)ˣ) : AE D) ∈ intAE D := by
  obtain ⟨a, ha, -⟩ := exists_det_int hg.2
  have hd : finPart D (Formalism.L2.Theta.mt V g).det ∈ intAE D := by
    apply GlobalTheory.PlaceDatum.finPart_mem_of_toEAf
    rw [← ha]
    exact a.2
  have hfe : finPart D e ∈ intAE D := by
    apply GlobalTheory.AdIdem.idempotent_mem_intAE
    rw [← map_mul, he]
  rw [detAt_val, map_add, map_mul, map_sub, map_one]
  exact add_mem (GlobalTheory.IdemPrime.mul_mem_int hfe hd) (sub_mem GlobalTheory.VacInert.one_int hfe)

theorem infPart_place {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (h : IsPlaceIdem D v ε) :
    infPart D (algebraMap (AF D.host.F) (AE D) ε) = 0 := by
  obtain ⟨α, rfl, -, -⟩ := h
  rw [Algebra.TensorProduct.algebraMap_apply]
  simp only [infPart, pairA, fstA]
  erw [Algebra.TensorProduct.map_tmul]
  exact TensorProduct.zero_tmul _ _

theorem mul_eq_self_of_orthogonal_supported_sub_one {R : Type} [CommRing R] {a b x : R} (h : b * a = 0) (hx : b * (x - 1) = x - 1) : a * x = a := by
  linear_combination (x - 1) * h - a * hx

theorem unramAt_of_unrOff {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (h : IsPlaceIdem D v ε) {a : AE D}
    (ha : algebraMap (AF D.host.F) (AE D) ε * a = 0) {χ : (AE D)ˣ →* Circle} (hχ : UnrOff a χ) : UnramAt ε χ := by
  intro x hx hfin hfin'
  refine hχ x ?_ hfin hfin' (mul_eq_self_of_orthogonal_supported_sub_one ha hx)
  have h0 : infPart D ((x : AE D) - 1) = 0 := by
    rw [← hx, map_mul, infPart_place h, zero_mul]
  rw [map_sub, map_one, sub_eq_zero] at h0
  exact h0

theorem idempotentInterpolation_eq_one_of_orthogonal_support {R : Type} [CommRing R] {b e d : R} (h : b * e = 0) (hd : b * (d - 1) = d - 1) :
    e * d + (1 - e) = 1 := by
  linear_combination (d - 1) * h - e * hd

theorem idempotentInterpolation_eq_of_mul_supported {R : Type} [CommRing R] {b e e' d : R} (h : e * b = e') (h' : e' * b = e') (hd : b * (d - 1) = d - 1) :
    e * d + (1 - e) = e' * d + (1 - e') := by
  linear_combination (d - 1) * h - (d - 1) * h' - (e - e') * hd

theorem supported_sub_one_idempotentInterpolation {R : Type} [CommRing R] {b e d : R} (h : e * b = e) :
    b * (e * d + (1 - e) - 1) = e * d + (1 - e) - 1 := by
  linear_combination (d - 1) * h

theorem unram_detAt {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {g : GA D V} (hg : Stab V β g) {e : AE D}
    (he : e * e = e) {ε : AF D.host.F} (hs : e * algebraMap (AF D.host.F) (AE D) ε = e) {χ : (AE D)ˣ →* Circle}
    (hχ : UnramAt ε χ) : χ (detAt e he V g) = 1 := by
  apply hχ
  · rw [detAt_val]
    exact supported_sub_one_idempotentInterpolation hs
  · exact finPart_detAt hg e he
  · rw [← map_inv]
    exact finPart_detAt (hg.inv) e he

theorem split_mul {e : AE D} (he : IsSplitIdem D e) : e * (e + cA D e) = e := by
  rw [mul_add, he.1, he.2.1, add_zero]

theorem place_cases {P : Finset (Pl D.host.E)} {e : AE D} (he : IsIdemSum e P)
    {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (h : IsPlaceIdem D v ε) :
    (∃ e', IsSplitIdem D e' ∧ e' + cA D e' = algebraMap (AF D.host.F) (AE D) ε ∧
      e * algebraMap (AF D.host.F) (AE D) ε = e') ∨ algebraMap (AF D.host.F) (AE D) ε * e = 0 := by
  have hee : e * e = e := GlobalTheory.PlaceModelSum.IsOrthSum.idem (GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he)
  have hec : e * cA D e = 0 := he.2
  have hεε : ε * ε = ε := GlobalTheory.StabDense.placeIdem_idem h
  set ι := algebraMap (AF D.host.F) (AE D) with hι
  have hιε : ι ε * ι ε = ι ε := by rw [← map_mul, hεε]

  set e' := e * ι ε with he'
  have h1 : e' * e' = e' := by
    rw [he']
    linear_combination (ι ε * ι ε) * hee + e * hιε
  have h2 : e' * cA D e' = 0 := by
    rw [he', map_mul, cA_alg]
    linear_combination (ι ε * ι ε) * hec
  have h3 : cA D e' * cA D e' = cA D e' := by rw [← map_mul, h1]

  obtain ⟨t, ht⟩ := GlobalTheory.PlaceModelSum.exists_add_conj e'
  have htt : t * t = t := by
    apply GlobalTheory.VacInert.alg_inj
    rw [map_mul, ht]
    linear_combination h1 + h3 + 2 * h2
  have h4 : ι ε * e' = e' := by
    rw [he']
    linear_combination e * hιε
  have h5 : ι ε * cA D e' = cA D e' := by
    have := congrArg (cA D) h4
    rwa [map_mul, cA_alg] at this
  have hεt : ε * t = t := by
    apply GlobalTheory.VacInert.alg_inj
    rw [map_mul, ht]
    linear_combination h4 + h5
  rcases GlobalTheory.PlaceModelSum.eq_zero_or_eq_of_placeIdem h htt hεt with h0 | h0
  · right
    have h6 : e' + cA D e' = 0 := by rw [← ht, h0, map_zero]
    rw [mul_comm]
    linear_combination e' * h6 - h1 - h2
  · left
    have h7 : e' + cA D e' = ι ε := by rw [← ht, h0]
    exact ⟨e', ⟨h1, h2, v, ε, h, h7⟩, h7, rfl⟩

def eigSub {G M : Type} [Group G] [AddCommGroup M] [Module ℂ M] (om : G →* Module.End ℂ M) (c : G →* Circle) (f : M) :
    Subgroup G where
  carrier := {p | om p f = ((c p : Circle) : ℂ) • f}
  one_mem' := by simp
  mul_mem' := fun {p q} hp hq => by
    have hp : om p f = ((c p : Circle) : ℂ) • f := hp
    have hq : om q f = ((c q : Circle) : ℂ) • f := hq
    change om (p * q) f = ((c (p * q) : Circle) : ℂ) • f
    rw [map_mul, map_mul, Module.End.mul_apply, hq, map_smul, hp, smul_smul, Circle.coe_mul, mul_comm]
  inv_mem' := fun {p} hp => by
    have hp : om p f = ((c p : Circle) : ℂ) • f := hp
    change om p⁻¹ f = ((c p⁻¹ : Circle) : ℂ) • f
    have h1 : om p⁻¹ (om p f) = f := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    rw [hp, map_smul] at h1
    rw [map_inv c, Circle.coe_inv, eq_inv_smul_iff₀ (Circle.coe_ne_zero _), h1]

theorem stab_vacuum : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → IsSelfDualC S ΛS → IsSelfDualC T ΛT → (∃ η, IsEtaTilde D η) → ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), IsFrame βS ΛS → IsFrame βT ΛT → ∀ (P : Finset (Pl D.host.E)) (e : AE D) (he : e * e = e), IsIdemSum e P → UnrOff (e + cA D e) χS → UnrOff (e + cA D e) χT → ∀ g h, Stab S βS g → Stab T βT h → ∀ f, IsThetaFunO ψ S T f → IsLatVac (heisO ψ S T) (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) f → om (g, h) f = ((splitFacO χS χT (detAt e he S g) (detAt e he T h) : Circle) : ℂ) • f := by
  intro D ψ S T ΛS ΛT χS χT om hW hS hT hη βS βT hβS hβT P e he hsum hχS hχT g h hg hh f hf hvac

  set c : GA D S × GA D T →* Circle :=
    (χT.comp ((detAt e he S).comp (MonoidHom.fst _ _)))⁻¹ * χS.comp ((detAt e he T).comp (MonoidHom.snd _ _)) with hc
  have hcv : ∀ p : GA D S × GA D T, c p = splitFacO χS χT (detAt e he S p.1) (detAt e he T p.2) := fun p => rfl
  have hcont : Continuous fun p : GA D S × GA D T => c p := by
    simp only [hcv, splitFacO]
    exact ((hW.hecT.1.comp ((continuous_detAt e he S).comp continuous_fst)).inv).mul
      (hW.hecS.1.comp ((continuous_detAt e he T).comp continuous_snd))

  have hclosed : IsClosed ((eigSub om c f : Subgroup (GA D S × GA D T)) : Set (GA D S × GA D T)) := by
    have hset : ((eigSub om c f : Subgroup (GA D S × GA D T)) : Set (GA D S × GA D T)) =
        ⋂ w, {p | om p f w = ((c p : Circle) : ℂ) * f w} := by
      ext p
      show om p f = ((c p : Circle) : ℂ) • f ↔ _
      simp only [Set.mem_iInter, Set.mem_ofPred_eq]
      constructor
      · intro hp w
        rw [hp, Pi.smul_apply, smul_eq_mul]
      · intro hp
        funext w
        rw [hp w, Pi.smul_apply, smul_eq_mul]
    rw [hset]
    exact isClosed_iInter fun w =>
      isClosed_eq (hW.om_cont f hf w) ((continuous_subtype_val.comp hcont).mul continuous_const)

  have key : (g, h) ∈ eigSub om c f := by
    refine GlobalTheory.T.mem_closedSubgroup_of_localStabilizerPairs D S T βS βT (eigSub om c f) hclosed ?_ g h hg hh
    intro v ε hε g' h' hg' hh' hsg hsh
    show om (g', h') f = ((c (g', h') : Circle) : ℂ) • f
    rw [hcv]
    have hlat := fun u => mem_latO_iff hβS hβT hg'.2 hh'.2 u
    have hdS := mul_det_sub_one _ _ hsg
    have hdT := mul_det_sub_one _ _ hsh
    have hSupp : ∀ e' : AE D, e' + cA D e' = algebraMap (AF D.host.F) (AE D) ε →
        Formalism.L2.Theta.SuppAt e' S g' ∧ Formalism.L2.Theta.SuppAt e' T h' := by
      intro e' he'
      refine ⟨fun i j => ?_, fun i j => ?_⟩
      · rw [he']
        exact hsg i j
      · rw [he']
        exact hsh i j
    rcases place_cases hsum hε with ⟨e', he', hsum', hee'⟩ | horth
    ·
      have hb : e' * algebraMap (AF D.host.F) (AE D) ε = e' := by
        rw [← hsum']
        exact split_mul he'
      have hx : detAt e he S g' = detAt e' he'.1 S g' := by
        apply Units.ext
        rw [detAt_val, detAt_val]
        exact idempotentInterpolation_eq_of_mul_supported hee' hb hdS
      have hy : detAt e he T h' = detAt e' he'.1 T h' := by
        apply Units.ext
        rw [detAt_val, detAt_val]
        exact idempotentInterpolation_eq_of_mul_supported hee' hb hdT
      rw [hx, hy]
      exact GlobalTheory.T.splitPlace_weilRep_latticeVacuum_character D ψ S T ΛS ΛT χS χT om hW hS hT e' he' g' h' (hSupp e' hsum').1 (hSupp e' hsum').2
        hlat _ _ (isDetAt_detAt e' he'.1 S g') (isDetAt_detAt e' he'.1 T h') f hf hvac
    ·
      have hx : detAt e he S g' = 1 := by
        apply Units.ext
        rw [detAt_val, Units.val_one]
        exact idempotentInterpolation_eq_one_of_orthogonal_support horth hdS
      have hy : detAt e he T h' = 1 := by
        apply Units.ext
        rw [detAt_val, Units.val_one]
        exact idempotentInterpolation_eq_one_of_orthogonal_support horth hdT
      have horth' : algebraMap (AF D.host.F) (AE D) ε * (e + cA D e) = 0 := by
        have h2 : algebraMap (AF D.host.F) (AE D) ε * cA D e = 0 := by
          have := congrArg (cA D) horth
          rwa [map_mul, cA_alg, map_zero] at this
        rw [mul_add, horth, h2, add_zero]
      have huS : UnramAt ε χS := unramAt_of_unrOff hε horth' hχS
      have huT : UnramAt ε χT := unramAt_of_unrOff hε horth' hχT
      rw [hx, hy]
      simp only [splitFacO, map_one, inv_one, one_mul, Circle.coe_one, one_smul]
      by_cases hsp : ∃ e'', IsSplitIdem D e'' ∧ e'' + cA D e'' = algebraMap (AF D.host.F) (AE D) ε
      ·
        obtain ⟨e'', he'', hs''⟩ := hsp
        have hb : e'' * algebraMap (AF D.host.F) (AE D) ε = e'' := by
          rw [← hs'']
          exact split_mul he''
        rw [GlobalTheory.T.splitPlace_weilRep_latticeVacuum_character D ψ S T ΛS ΛT χS χT om hW hS hT e'' he'' g' h' (hSupp e'' hs'').1 (hSupp e'' hs'').2
          hlat _ _ (isDetAt_detAt e'' he''.1 S g') (isDetAt_detAt e'' he''.1 T h') f hf hvac]
        simp only [splitFacO, unram_detAt hg' he''.1 hb huT, unram_detAt hh' he''.1 hb huS, inv_one, one_mul,
          Circle.coe_one, one_smul]
      ·
        exact GlobalTheory.T.weilOperator_lattice_stabiliser_fixes_vacuum_nonsplit D ψ S T ΛS ΛT χS χT om hW hS hT hη v ε ⟨hε, hsp⟩ huS huT g' h' hsg hsh hlat f hf hvac
  rw [← hcv (g, h)]
  exact key

end GlobalTheory.VecInv.Vac

end
