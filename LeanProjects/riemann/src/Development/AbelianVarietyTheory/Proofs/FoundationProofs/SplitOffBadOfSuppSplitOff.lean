import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ThPinsR
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
import Formalism.LocalToGlobal.ProjectiveLattices.ThClassPinsRec
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.SublevelSplitting
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MovedOfSplitPl
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSplitPlaceOfSplitPl
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CompletedLatticeEqAdelicCompletionAndGram
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryEqRealMulFiniteSplit
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RationalPointsAdelicUnitaryEqUnitary
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPrincipalLevelSubgroupOpen
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSplitAt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EvalVAlgebraMapMem
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinCongMemLevEnv

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RepsCompare

open GlobalTheory.IndefiniteRowSideFullHecke.SublevelSplitting

section Generic

theorem moved_of_hom {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E)
    (hcc : ∀ x, c (c x) = x) (hc : c ≠ 1) (v : HeightOneSpectrum (𝓞 F)) (φ : E →+* v.adicCompletion F)
    (hφ : ∀ t : F, φ (algebraMap F E t) = algebraMap F (v.adicCompletion F) t)
    (hint : ∀ x : 𝓞 E, Valued.v (φ x) ≤ 1) (P : HeightOneSpectrum (𝓞 E))
    (hP : ∀ x : 𝓞 E, x ∈ P.asIdeal ↔ Valued.v (φ x) < 1) : GlobalTheory.UnRep.Moved c P.asIdeal := by
  by_contra hn
  let σ : 𝓞 E ≃+* 𝓞 E := RingOfIntegers.mapRingEquiv c.toRingEquiv
  have hσ : ∀ x : 𝓞 E, ((σ x : 𝓞 E) : E) = c x := fun _ => rfl
  have one : ∀ b : 𝓞 E, b ∉ P.asIdeal → Valued.v (φ b) = 1 := fun b hb =>
    le_antisymm (hint b) (not_lt.1 fun h => hb ((hP b).2 h))
  have key : ∀ b : 𝓞 E, b ∉ P.asIdeal → σ b ∉ P.asIdeal := fun b hb h => hn ⟨σ b, h, b, (hcc _).symm, hb⟩
  obtain ⟨z, hz⟩ : ∃ z, c z ≠ z := by
    by_contra h
    exact hc (AlgEquiv.ext fun x => by simpa using not_exists.1 h x)
  have hab : φ z - φ (c z) ≠ 0 := sub_ne_zero.2 fun h => hz (φ.injective h).symm
  have hab' : Valued.v (φ z - φ (c z)) ≠ 0 := (Valuation.ne_zero_iff _).2 hab
  obtain ⟨t, ht⟩ : ∃ t : F, Valued.v (φ z - algebraMap F (v.adicCompletion F) t) < Valued.v (φ z - φ (c z)) := by
    have hd : DenseRange (algebraMap F (v.adicCompletion F)) := HeightOneSpectrum.denseRange_algebraMap (K := F) v
    have hN : {y : v.adicCompletion F | Valued.v (φ z - y) < Valued.v (φ z - φ (c z))} ∈ nhds (φ z) := by
      have ho := (Valued.isOpen_ball (v.adicCompletion F) (Valued.v.restrict (φ z - φ (c z)))).preimage
        (continuous_const.sub continuous_id : Continuous fun y : v.adicCompletion F => φ z - y)
      simp only [Set.preimage_ofPred_eq, Valuation.restrict_lt_iff] at ho
      refine ho.mem_nhds ?_
      show Valued.v (φ z - φ z) < _
      rw [sub_self, map_zero]
      exact zero_lt_iff.2 hab'
    obtain ⟨t, ht⟩ := hd.mem_nhds hN
    exact ⟨t, ht⟩
  have hb : Valued.v (φ (c z) - algebraMap F (v.adicCompletion F) t) = Valued.v (φ z - φ (c z)) := by
    rw [show φ (c z) - algebraMap F (v.adicCompletion F) t =
      (φ z - algebraMap F (v.adicCompletion F) t) - (φ z - φ (c z)) by ring]
    exact Valuation.map_sub_eq_of_lt_right _ ht
  have h1 : Valued.v (φ (z - algebraMap F E t)) < Valued.v (φ (c (z - algebraMap F E t))) := by
    rw [map_sub c, c.commutes, map_sub φ, map_sub φ, hφ, hb]
    exact ht
  generalize z - algebraMap F E t = u at h1
  obtain ⟨a, b, h⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_or_mul_eq P (K := E) (u / c u)
  have hu : c u ≠ 0 := fun h0 => by
    rw [h0, map_zero, map_zero] at h1
    exact not_lt_zero h1
  refine absurd h1 (not_lt.2 ?_)
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_eq_iff hu, div_eq_iff hu] at h
  rcases h with h | h
  · have h2 : c u * (σ b.1 : 𝓞 E) = (σ a : 𝓞 E) * u := by
      have := congrArg c h
      rwa [map_mul, map_mul, hcc] at this
    have h3 := congrArg (fun x => Valued.v (φ x)) h2
    simp only [map_mul, one _ (key _ b.2), mul_one] at h3
    rw [h3]
    exact mul_le_of_le_one_left' (hint _)
  · have h2 : u * (a : E) = ((b.1 : 𝓞 E) : E) * c u := h
    have h3 := congrArg (fun x => Valued.v (φ x)) h2
    simp only [map_mul, one _ b.2, one_mul] at h3
    rw [← h3]
    exact mul_le_of_le_one_right' (hint _)

variable {G Γ : Type} [Group G] [Group Γ] (ι : Γ →* G)

theorem finite_stab {J J' : Subgroup G} (hle : J' ≤ J) {I : Type} {y : I → G} (hy : Bridge.IsReps ι J y)
    (hfin : ∀ i, Finite (Bridge.stab ι J (y i))) (g : G) : Finite (Bridge.stab ι J' g) := by
  obtain ⟨i, ⟨γ, k, rfl⟩, -⟩ := hy g
  have := hfin i
  refine Finite.of_injective (β := Bridge.stab ι J (y i)) (fun δ => ⟨γ⁻¹ * δ.1 * γ, ?_⟩) ?_
  · have h := hle ((Bridge.mem_stab ι).1 δ.2)
    rw [Bridge.mem_stab]
    have := J.mul_mem (J.mul_mem k.2 h) (J.inv_mem k.2)
    convert this using 1
    simp only [map_mul, map_inv]
    group
  · intro a b h
    have h' : γ⁻¹ * a.1 * γ = γ⁻¹ * b.1 * γ := congrArg Subtype.val h
    exact Subtype.ext (mul_left_cancel (mul_right_cancel h'))

end Generic

section Support

open GlobalTheory.IdemModTwo GlobalTheory.SplitIdem GlobalTheory.IdemPrime GlobalTheory.UnRep GlobalTheory.Member

variable {D : D7}

theorem finrank_two (D : D7) : Module.finrank D.host.F D.host.E = 2 :=
  Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield D.host.E) D.host.E

theorem cF_ne_one (D : D7) : cF D ≠ 1 := (latHat_eq_hat_and_gram D D.sp.X').2.2.2.2.2.2.1

theorem isSplitPl_iff (v : HeightOneSpectrum (𝓞 D.host.F)) : IsSplitPl D v ↔ SplitPl (cF D) v := by
  rw [Compare.splitPl_iff _ (finrank_two D) (cF_ne_one D)]
  constructor
  · rintro ⟨P, P', hne, h, h'⟩
    exact ⟨P.asIdeal, P'.asIdeal, fun e => hne (HeightOneSpectrum.ext e), P.isPrime, P'.isPrime,
      congrArg HeightOneSpectrum.asIdeal h, congrArg HeightOneSpectrum.asIdeal h'⟩
  · rintro ⟨w, w', hne, hw, hw', h, h'⟩
    have nb : ∀ u : Ideal (𝓞 D.host.E), u.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = v.asIdeal → u ≠ ⊥ := by
      rintro u hu rfl
      apply v.ne_bot
      rw [← hu]
      exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _)
    exact ⟨⟨w, hw, nb w h⟩, ⟨w', hw', nb w' h'⟩, fun e => hne (congrArg HeightOneSpectrum.asIdeal e),
      HeightOneSpectrum.ext h, HeightOneSpectrum.ext h'⟩

theorem suppSplitOff_iff (V : HSp D) (N : ℕ) (g : Bridge.Gf V) : SuppSplitOff V N g ↔ SuppSplit (cF D) N g.1.1 := by
  rw [SuppSplit, Compare.support_iff (fun v => SplitPl (cF D) v ∧ (N : 𝓞 D.host.F) ∉ v.asIdeal), SuppSplitOff]
  simp only [isSplitPl_iff]
  exact Iff.rfl

theorem exists_splitAt_of_isIdemAt {e : AE D} {P : HeightOneSpectrum (𝓞 D.host.E)} (h : Formalism.L2.NTheta.IsIdemAt e P) :
    ∃ v, SplitAt D v e ∧ SplitPl (cF D) v ∧ P.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = v.asIdeal := by
  obtain ⟨v, he⟩ := (isSplitIdem_iff e).1 h.1
  obtain ⟨Q, hQ, hQv⟩ := exists_isIdemAt D v e he
  obtain rfl : P = Q := HeightOneSpectrum.ext (Ideal.ext fun x => by
    by_cases hx : x = 0
    · rw [hx]; exact iff_of_true (zero_mem _) (zero_mem _)
    · rw [h.2 x hx, hQ.2 x hx])
  obtain ⟨φ, hφ⟩ := exists_hom he
  refine ⟨v, he, ⟨P.asIdeal, P.isPrime, hQv,
    moved_of_hom (cF D) (fun x => star_star x) (cF_ne_one D) v φ (hom_algebraMap he hφ) (fun x => ?_) P fun x => ?_⟩, hQv⟩
  · rw [← mem_iff he, ← hφ, RingHom.map_mul]
    exact mul_mem_int (finPart_mem he) (AddSubgroup.subset_closure
      ⟨1, fun w => by rw [map_one]; exact one_mem _, x, rfl⟩)
  · by_cases hx : x = 0
    · subst hx
      refine iff_of_true (zero_mem _) ?_
      show Valued.v (φ 0) < 1
      rw [map_zero, map_zero]; exact zero_lt_one
    · have hx0 : Valued.v (φ x) ≠ 0 := by
        rw [Valuation.ne_zero_iff, map_ne_zero]
        exact fun h => hx (Subtype.ext h)
      rw [h.2 x hx, hφ, mem_iff he, map_inv₀, map_inv₀, not_le, one_lt_inv₀ (zero_lt_iff.2 hx0)]

theorem finPart_sub_one (V : HSp D) (h : GA D V) (i j : Fin V.rank) :
    finPart D ((Formalism.L2.Theta.mt V h - 1) i j) = ((finHom V h).1 - 1) i j := by
  rw [Matrix.sub_apply, Matrix.sub_apply, RingHom.map_sub]
  congr 1
  by_cases e : i = j
  · subst e; rw [Matrix.one_apply_eq, Matrix.one_apply_eq, RingHom.map_one]
  · rw [Matrix.one_apply_ne e, Matrix.one_apply_ne e, RingHom.map_zero]

theorem suppSplitOff_of_splitOffBad (V : HSp D) (N : ℕ) (h : GA D V) (hs : FWT.SplitOffBad V N h) :
    SuppSplitOff V N (FWT.fin V h) := by
  classical
  obtain ⟨-, e, P, ⟨⟨es, hes, rfl⟩, -⟩, hN, hsupp⟩ := hs
  choose pv h1 h2 h3 using fun PP : P => exists_splitAt_of_isIdemAt (hes PP.1 PP.2)
  have hsum : ∑ PP ∈ P, es PP + cA D (∑ PP ∈ P, es PP) = fj D (∑ PP : P, singleV D.host.F (pv PP) 1) := by
    rw [map_sum, map_sum, ← Finset.sum_add_distrib, ← Finset.sum_coe_sort P]
    exact Finset.sum_congr rfl fun PP _ => (h1 PP).2.2
  refine ⟨Finset.univ.image pv, fun v hv => ?_, fun v hv => ?_⟩
  · obtain ⟨PP, -, rfl⟩ := Finset.mem_image.1 hv
    refine ⟨(isSplitPl_iff _).2 (h2 PP), fun hm => hN PP.1 PP.2 ?_⟩
    rwa [← h3, Ideal.mem_comap, map_natCast] at hm
  · have h0 : evalV D.host.F v (∑ PP : P, singleV D.host.F (pv PP) 1) = 0 := by
      rw [map_sum]
      exact Finset.sum_eq_zero fun PP _ => evalV_singleV_ne _ _ _ fun e =>
        hv (Finset.mem_image.2 ⟨PP, Finset.mem_univ _, e.symm⟩)
    generalize (∑ PP : P, singleV D.host.F (pv PP) 1) = α at hsum h0
    let π := Algebra.TensorProduct.map (evalV D.host.F v) (AlgHom.id D.host.F D.host.E)
    rw [← Matrix.map_one π (map_zero _) (map_one _)]
    ext i j
    have h4 := congrArg (finPart D) (hsupp i j)
    rw [hsum, RingHom.map_mul, finPart_sub_one] at h4
    have h5 : π (finPart D (fj D α)) = 0 := by
      show evalV D.host.F v α ⊗ₜ[D.host.F] (1 : D.host.E) = 0
      rw [h0, TensorProduct.zero_tmul]
    have h6 := congrArg π h4
    rw [map_mul, h5, zero_mul, Matrix.sub_apply, map_sub] at h6
    exact sub_eq_zero.1 h6.symm

theorem existsUnique_lift (V : HSp D) (g : Bridge.Gf V) : ∃! h : GA D V, h ∈ GfC V ∧ FWT.fin V h = g := by
  obtain ⟨_, x, rfl⟩ := g
  obtain ⟨k, k1, k2⟩ := GlobalTheory.UnitarySplit.ga_glue V 1 _ (one_mem _) (GlobalTheory.UnitarySplit.finHom_mem V x)
  refine ⟨k, ⟨k1, Subtype.ext k2⟩, fun y hy => GlobalTheory.UnitarySplit.ga_ext V (hy.1.trans k1.symm) ?_⟩
  exact (congrArg Subtype.val hy.2).trans k2.symm

end Support

section Lattices

open GlobalTheory.AdLat GlobalTheory.UnRep GlobalTheory.UnRep.FullReps GlobalTheory.Member

variable {D : D7}

theorem inv_mulVec_mem_iff (V : HSp D) (g : Bridge.Gf V) (x : Fin V.rank → D.host.E) :
    (matF V g⁻¹).mulVec (fun i => (1 : Af D.host.F) ⊗ₜ[D.host.F] x i) ∈
      Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (latC V : Set (Fin V.rank → D.host.E)) ↔ x ∈ latOf D.host.F g.1.1 (latC V) := by
  change (g.1⁻¹).1 *ᵥ fv D.host.F x ∈ hat D.host.F _ ↔ _
  constructor
  · intro hx
    exact ⟨_, hx, by rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]⟩
  · rintro ⟨z, hz, e⟩
    rw [← e, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
    exact hz

theorem isTransl_iff_latOf (V : HSp D) (g : Bridge.Gf V) (L : Lat V) :
    IsTransl V (latC V) g L ↔ (L : Set (Fin V.rank → D.host.E)) = latOf D.host.F g.1.1 (latC V) := by
  simp only [IsTransl, inv_mulVec_mem_iff, Set.ext_iff, SetLike.mem_coe]

theorem coe_hLat (V : HSp D) (g : Bridge.Gf V) :
    (Bridge.hLat V g : Set (Fin V.rank → D.host.E)) = latOf D.host.F g.1.1 (latC V) := by
  obtain ⟨-, -, hfg, hsp, -⟩ := latHat_eq_hat_and_gram D V
  obtain ⟨Λ, hΛ, -⟩ := exists_lattice_latOf D.host.F D.host.E V.rank (latC V) g.1 hfg hsp
  have : Bridge.hLat V g = Λ := by
    unfold Bridge.hLat
    rw [← Submodule.span_eq Λ, hΛ, ← coe_selfDualLatticeInFrameCoordinates_eq]
    congr 1
    exact Set.ext fun x => inv_mulVec_mem_iff V g x
  rw [this, hΛ]

theorem isTransl_iff {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Lat V} (hβ : IsSDFrame V β Λ 1) (g : Bridge.Gf V)
    (L : Lat V) : IsTransl V Λ g L ↔ L = Bridge.hLat V g := by
  rw [GlobalTheory.PrincInLevel.eq_latC hβ, isTransl_iff_latOf, ← coe_hLat, SetLike.coe_set_eq]

theorem conj_mulVec_mem {R : Type} [CommRing R] {n : ℕ} (S : Subring R) (β : GL (Fin n) R) (y : GL (Fin n) S) (z : Fin n → R)
    (hz : ∀ j, ((β⁻¹).1 *ᵥ z) j ∈ S) (i : Fin n) :
    ((β⁻¹).1 *ᵥ ((β * Formalism.UG.bc S.subtype y * β⁻¹).1 *ᵥ z)) i ∈ S := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← mul_assoc, ← mul_assoc, inv_mul_cancel, one_mul, Units.val_mul,
    ← Matrix.mulVec_mulVec]
  generalize (β⁻¹).1 *ᵥ z = w at hz
  exact Subring.sum_mem S (t := Finset.univ) (f := fun j => (y.1 i j : R) * w j) fun j _ => mul_mem (y.1 i j).2 (hz j)

theorem mulVec_mem_hat {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Lat V} (hβ : IsSDFrame V β Λ 1)
    (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) {k : Bridge.Gf V} (hk : k ∈ (levEnv V β L).J)
    {z : Fin V.rank → RA D.host.F D.host.E} (hz : z ∈ hat D.host.F (Λ : Set (Fin V.rank → D.host.E))) :
    k.1.1 *ᵥ z ∈ hat D.host.F (Λ : Set (Fin V.rank → D.host.E)) := by
  obtain ⟨c, hfr, -⟩ := hβ
  have h1 : Formalism.UG.bc (Lev.swapAE D) k.1 ∈ Formalism.L2.DIV.lev D.sp.cm V.gram β (Lev.flag1L L) := hk
  obtain ⟨y, hy⟩ := Formalism.L2.DIV.parLev_St h1.1
  have hy' : β * Formalism.L2.DIV.intGL D.host.F D.host.E V.rank y * β⁻¹ = Formalism.UG.bc (Lev.swapAE D) k.1 := hy
  have h2 := (hfr _).1 (GlobalTheory.PrincInLevel.swap_mem_hatL Λ z hz)
  have h3 : (Formalism.UG.bc (Lev.swapAE D) k.1).1 *ᵥ (fun i => Algebra.TensorProduct.comm D.host.F _ D.host.E (z i)) ∈
      Formalism.L2.Herm.hatL (F := D.host.F) Λ := by
    rw [← hy']
    exact (hfr _).2 (conj_mulVec_mem _ β y _ h2)
  have h4 := GlobalTheory.PrincInLevel.swap_symm_mem_hat Λ _ h3
  convert h4 using 1
  funext i
  rw [AlgEquiv.eq_symm_apply]
  exact RingHom.map_mulVec (Lev.swapAE D) k.1.1 z i

theorem isOpenLev_levEnv {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Lat V} (hβ : IsSDFrame V β Λ 1)
    (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) {N : ℕ} (hN : 0 < N)
    (hL : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → ((N : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) : IsOpenLev V (levEnv V β L).J := by
  have : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
  have : IsTopologicalGroup (GA D V) := inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig V.gram))
  exact Subgroup.isOpen_of_mem_nhds _ (Filter.mem_of_superset (PrincLevel.finCong_mem_nhds V hN)
    fun k hk => GlobalTheory.PrincInLevel.finCong_mem_levEnv D V β Λ L N k hβ hL hk)

theorem isUnA_gf (V : HSp D) (g : Bridge.Gf V) : IsUnA (cF D) V.gramᵀ g.1.1 := by
  obtain ⟨_, g, rfl⟩ := g
  intro x y
  rw [GlobalTheory.UnitarySplit.hermA_eq, GlobalTheory.UnitarySplit.hermA_eq]
  exact (RatElt.mem_UJ_iff _ _ _).1 (GlobalTheory.UnitarySplit.finHom_mem V g) y x

theorem isLattice_hLat (V : HSp D) (g : Bridge.Gf V) : Submodule.IsLattice D.host.E (Bridge.hLat V g) := by
  obtain ⟨-, -, hfg, hsp, -⟩ := latHat_eq_hat_and_gram D V
  obtain ⟨Λ, hΛ, h1, h2, -⟩ := exists_lattice_latOf D.host.F D.host.E V.rank (latC V) g.1 hfg hsp
  rw [SetLike.coe_injective ((coe_hLat V g).trans hΛ.symm)]
  exact ⟨h1, h2⟩

theorem dualL_hLat (V : HSp D) (g : Bridge.Gf V) : Formalism.L2.Herm.dualL D.sp.cm V (Bridge.hLat V g) = Bridge.hLat V g := by
  obtain ⟨-, -, hfg, hsp, c2, -, -, gh, gd, -, hsd⟩ := latHat_eq_hat_and_gram D V
  have key := latOf_selfDual D.host.F D.host.E V.rank (latC V) (cF D) V.gramᵀ 1 g.1 hfg hsp c2 gh gd one_ne_zero hsd
    (isUnA_gf V g)
  unfold Formalism.L2.Herm.dualL
  conv_rhs => rw [← Submodule.span_eq (Bridge.hLat V g)]
  congr 1
  ext v
  rw [coe_hLat, ← key, ← coe_hLat]
  refine forall_congr' fun y => imp_congr_right fun _ => ?_
  have e : Formalism.UG.hform (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram y v = ∑ a, ∑ b, v a * V.gramᵀ a b * cF D (y b) := by
    unfold Formalism.UG.hform
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    change star (y b) * V.gram b a * v a = v a * V.gram b a * star (y b)
    ring
  rw [e, FractionalIdeal.mem_one_iff]
  exact Iff.rfl

theorem exists_pos_bd (V : HSp D) (N : ℕ) (e : Af D.host.F)
    (he : ∀ v : HeightOneSpectrum (𝓞 D.host.F), (N : 𝓞 D.host.F) ∈ v.asIdeal → e v = 0)
    (M : Matrix (Fin V.rank) (Fin V.rank) (RA D.host.F D.host.E))
    (hM : (e ⊗ₜ[D.host.F] (1 : D.host.E) : RA D.host.F D.host.E) • (M - 1) = M - 1) :
    ∃ t : ℕ, 0 < t ∧ t.Coprime N ∧ Bd (latC V) (t : 𝓞 D.host.E) M := by
  obtain ⟨-, -, hfg, hsp, -⟩ := latHat_eq_hat_and_gram D V
  obtain ⟨t, ht, hb⟩ := exists_nat_bd _ hfg hsp N e he M hM
  rcases t.eq_zero_or_pos with rfl | h0
  · obtain ⟨d, hd, h⟩ := (idempotent_adeles_small_matrices D.host.F D.host.E _ _ hfg hsp).2.1 M
    refine ⟨d, hd, by rw [(Nat.coprime_zero_left N).1 ht]; exact Nat.coprime_one_right d, fun z hz => ?_⟩
    have : ((1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] ((d : 𝓞 D.host.E) : D.host.E) : RA D.host.F D.host.E) =
        (d : RA D.host.F D.host.E) := by
      rw [show ((d : 𝓞 D.host.E) : D.host.E) = (d : D.host.E) from map_natCast (algebraMap (𝓞 D.host.E) D.host.E) d]
      exact map_natCast (Algebra.TensorProduct.includeRight : D.host.E →ₐ[D.host.F] RA D.host.F D.host.E) d
    rw [this, Nat.cast_smul_eq_nsmul]
    exact h z hz
  · exact ⟨t, h0, ht, hb⟩

theorem exists_commens (V : HSp D) (N : ℕ) (g : Bridge.Gf V) (hs : SuppSplitOff V N g) :
    ∃ M : ℕ, 0 < M ∧ M.Coprime N ∧ (∀ x ∈ latC V, (M : D.host.E) • x ∈ Bridge.hLat V g) ∧
      ∀ x ∈ Bridge.hLat V g, (M : D.host.E) • x ∈ latC V := by
  obtain ⟨-, -, hfg, hsp, -⟩ := latHat_eq_hat_and_gram D V
  obtain ⟨e, -, -, he, hcut⟩ := (suppSplitOff_iff V N g).1 hs
  have he' : ∀ v : HeightOneSpectrum (𝓞 D.host.F), (N : 𝓞 D.host.F) ∈ v.asIdeal → e v = 0 := fun v hv => by
    by_contra h0
    exact (he v h0).2 hv
  obtain ⟨t, h0, ht, hb⟩ := exists_pos_bd V N e he' _ hcut
  obtain ⟨t', h0', ht', hb'⟩ := exists_pos_bd V N e he' _ (cut_inv g.1 _ hcut)
  have h1 := hb.mul (t' : 𝓞 D.host.E)
  have h2 := hb'.mul (t : 𝓞 D.host.E)
  rw [mul_comm] at h2
  rw [← Nat.cast_mul] at h1 h2
  have h3 := smul_mem_of_bd hfg hsp (coe_hLat V g) h1 h2
  simp only [Nat.cast_smul_eq_nsmul] at h3 ⊢
  exact ⟨t' * t, Nat.mul_pos h0' h0, Nat.Coprime.mul_left ht' ht, h3.2, h3.1⟩

theorem isLatReps_of_isAdReps {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Lat V} (hβ : IsSDFrame V β Λ 1)
    (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) {J' : Subgroup (Bridge.Gf V)} (hle : J' ≤ (levEnv V β L).J) {bad n : ℕ}
    {h : Fin n → Bridge.Gf V} {Lh : Fin n → Lat V} {gam : Fin n → ℕ} (H : IsAdReps V Λ J' bad h Lh gam) :
    IsLatReps V Λ bad Lh := by
  obtain ⟨h1, h2, h3, -⟩ := H
  have hL : ∀ a, Lh a = Bridge.hLat V (h a) := fun a => (isTransl_iff hβ _ _).1 (h3 a)
  refine ⟨fun a => ?_, fun g M hM => ?_⟩
  · rw [hL, GlobalTheory.PrincInLevel.eq_latC hβ]
    exact ⟨isLattice_hLat V _, dualL_hLat V _, exists_commens V bad _ (h2 a)⟩
  · obtain ⟨a, ⟨γ, k, rfl⟩, -⟩ := h1 g
    obtain ⟨γ', hγ', e⟩ := γ.2
    have hr : IsRat V γ.1 γ' := e.symm
    refine ⟨a, γ', hγ', fun x => ?_⟩
    rw [h3 a, hM]
    have e1 : (finHom V γ.1).1 *ᵥ fv D.host.F x = fv D.host.F (γ'.1 *ᵥ x) :=
      ((RatElt.rational_elements D V).2.2.2.2 _ _ hr).1 x
    change ((h a).1⁻¹).1 *ᵥ fv D.host.F x ∈ hat D.host.F _ ↔
      ((finHom V γ.1 * (h a).1 * k.1.1)⁻¹).1 *ᵥ fv D.host.F (γ'.1 *ᵥ x) ∈ hat D.host.F _
    rw [← e1, Matrix.mulVec_mulVec, ← Units.val_mul,
      show (finHom V γ.1 * (h a).1 * k.1.1)⁻¹ * finHom V γ.1 = k.1.1⁻¹ * (h a).1⁻¹ by group, Units.val_mul,
      ← Matrix.mulVec_mulVec]
    refine ⟨fun hx => mulVec_mem_hat hβ L (inv_mem (hle k.2)) hx, fun hx => ?_⟩
    have := mulVec_mem_hat hβ L (hle k.2) hx
    rwa [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec] at this

end Lattices

section Row

open Formalism.L2.DIV

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) (t : T)

theorem levJ_eq : FWT.levJ R i t = levJ R.toLevCh i t := rfl

theorem finite_stab_of_le {J' : Subgroup (Bridge.Gf (Vc D i))} (hle : J' ≤ FWT.levJ R i t) (g : Bridge.Gf (Vc D i)) :
    Finite (Bridge.stab (Bridge.ratF (Vc D i)) J' g) :=
  finite_stab _ hle (y := (R.B.L i t).pres.y) (R.B.L i t).pres.reps
    (fun c => Finite.of_equiv _ ((R.B.L i t).pres.stabI c).toEquiv) g

def RepsREx (K' : Type) [Field K'] (N : ℕ) : Prop :=
  ∃ (Cl : Type) (_ : Fintype Cl) (h : Cl → GA D (Vc D i)) (J' : Subgroup (Bridge.Gf (Vc D i))) (bad : ℕ)
    (Lh : Cl → Lat (Vc D i)) (gam : Cl → ℕ) (vol : K'), N ∣ bad ∧ FWT.RepsR R i t h bad J' Lh gam vol

end Row

end GlobalTheory.RepsCompare

end
