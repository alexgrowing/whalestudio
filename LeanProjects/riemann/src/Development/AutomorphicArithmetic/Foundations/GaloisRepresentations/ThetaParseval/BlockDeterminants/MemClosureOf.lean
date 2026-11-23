import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SchurStep
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ContinuousInfiniteAdeleMap
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSplitChartSplitChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductOfLocalLevelsUnitaryIsOpenIsCompactIsLeve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdeleEqZeroOfComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BcCompFinAwayPtOfNotMem

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.PRep Formalism.BasicNotions
open GlobalTheory.UnitaryHeckeBaseChange (toAdele adeleEquiv)
open GlobalTheory.CuspRep (Ad pInf pFin pLoc coord)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.TP

section Dict

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

private theorem cmE : IsCMExt (maximalRealSubfield E) E (cj E) := isCMExt_of_isCMField E

private theorem conjAd_adeleMap (a : AF (maximalRealSubfield E)) :
    GlobalTheory.UnitaryBC.conjAd E (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap (maximalRealSubfield E) E a) =
      GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap (maximalRealSubfield E) E a := by
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_infiniteAdeleRing_of_numberField_field E
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField E
  have key : ∀ k : maximalRealSubfield E,
      GlobalTheory.UnitaryBC.conjAd E (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap (maximalRealSubfield E) E (algebraMap _ _ k)) =
        GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap (maximalRealSubfield E) E (algebraMap _ _ k) := fun k => by
    rw [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap_algebraMap, GlobalTheory.UnitaryBC.conjAd_algebraMap]
    congr 1
    exact (IsCMField.complexConj E).commutes k
  have cc := GlobalTheory.BCT.GlobLev.continuous_conj_ad (E := E)
  refine Prod.ext ?_ ?_
  · exact congrFun ((InfiniteAdeleRing.denseRange_algebraMap (maximalRealSubfield E)).equalizer
      (g := fun b => (GlobalTheory.UnitaryBC.conjAd E (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.infiniteAdeleMap (maximalRealSubfield E) E b, 0)).1)
      (h := GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.infiniteAdeleMap (maximalRealSubfield E) E)
      (continuous_fst.comp (cc.comp ((GlobalTheory.UnitaryHeckeBaseChange.continuous_infiniteAdeleMap _ E).prodMk continuous_const)))
      (GlobalTheory.UnitaryHeckeBaseChange.continuous_infiniteAdeleMap _ E)
      (funext fun k => congrArg Prod.fst (key k))) a.1
  · exact congrFun ((GlobalTheory.AdeleCharTwist.denseRange_fin (F := maximalRealSubfield E)).equalizer
      (g := fun b => (GlobalTheory.UnitaryBC.conjAd E (0, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteAdeleMap (maximalRealSubfield E) E b)).2)
      (h := GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteAdeleMap (maximalRealSubfield E) E)
      (continuous_snd.comp (cc.comp (continuous_const.prodMk (GlobalTheory.UnitaryHeckeBaseChange.continuous_finiteAdeleMap _ E))))
      (GlobalTheory.UnitaryHeckeBaseChange.continuous_finiteAdeleMap _ E)
      (funext fun k => congrArg Prod.snd (key k))) a.2

private theorem toAdele_cj (z : AE (maximalRealSubfield E) E) :
    toAdele _ E (cA (cj E) z) = GlobalTheory.UnitaryBC.conjAd E (toAdele _ E z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a x =>
    change toAdele _ E (a ⊗ₜ[maximalRealSubfield E] (IsCMField.complexConj E x)) = _
    rw [GlobalTheory.UnitaryHeckeBaseChange.toAdele_tmul, GlobalTheory.UnitaryHeckeBaseChange.toAdele_tmul, map_mul, conjAd_adeleMap,
      GlobalTheory.UnitaryBC.conjAd_algebraMap]

end Dict

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

private theorem at_iff {R : Type} [Zero R] {ev : AF F → R} {m : ℕ} (b : AF F) (hb : ev b = 0)
    (hb' : ∀ u, ev u = 0 → u * (1 - b) = 0) (M : Matrix (Fin m) (Fin m) (AE F E)) :
    At ev M ↔ ∀ i j, b • M i j = 0 := by
  constructor
  · intro h i j
    exact congrFun (congrFun (h b hb) i) j
  · intro h u hu
    have e : u * b = u := by linear_combination -hb' u hu
    ext i j
    change u • M i j = 0
    rw [← e, mul_smul, h i j, smul_zero]

private theorem smul_zero_iff (h : IsCMExt F E σ) (b : AF F) (z : AE F E) :
    b • z = 0 ↔ GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap F E b * toAdele F E z = 0 := by
  rw [← GlobalTheory.UnitaryHeckeBaseChange.toAdele_algebraMap, ← map_mul, ← Algebra.smul_def]
  exact ⟨fun e => by rw [e, map_zero],
    fun e => (GlobalTheory.UnitaryHeckeBaseChange.bijective_toAdele h).1 (e.trans (map_zero _).symm)⟩

private theorem at_evI_iff (h : IsCMExt F E σ) {m : ℕ} (M : Matrix (Fin m) (Fin m) (AE F E)) :
    At (evI F) M ↔ ∀ i j, (toAdele F E (M i j)).2 = 0 := by
  let b : AF F := ((0, 1) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)
  rw [at_iff (ev := evI F) b (map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)) (fun u hu => ?_) M]
  · refine forall₂_congr fun i j => ?_
    rw [smul_zero_iff h]
    have e : ∀ y : AdeleRing (𝓞 E) E, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap F E b * y = ((0, y.2) : InfiniteAdeleRing E × FiniteAdeleRing (𝓞 E) E) := fun y =>
      Prod.ext ((congrArg (· * y.1) (map_zero (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.infiniteAdeleMap F E))).trans (zero_mul _))
        ((congrArg (· * y.2) (map_one (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteAdeleMap F E))).trans (one_mul _))
    rw [e]
    exact ⟨fun k => congrArg Prod.snd k, fun k => Prod.ext rfl k⟩
  · have h1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).map_eq_zero_iff.1 hu
    exact Prod.ext ((congrArg (· * _) h1).trans (zero_mul _)) ((congrArg (u.2 * ·) (sub_self _)).trans (mul_zero _))

private theorem at_evFin_iff (h : IsCMExt F E σ) (v : Pl F) {m : ℕ} (M : Matrix (Fin m) (Fin m) (AE F E)) :
    At (evFin F v) M ↔ ∀ i j, (toAdele F E (M i j)).1 = 0 ∧
      ∀ Q : HeightOneSpectrum (𝓞 E), Q.under (𝓞 F) ≠ v → (toAdele F E (M i j)).2 Q = 0 := by
  obtain ⟨ε, hε⟩ := GlobalTheory.UnitaryHeckeBaseChange.exists_isIndicator v
  have hc := GlobalTheory.UnitaryHeckeBaseChange.place_comp (E := E) ((GlobalTheory.UnitaryHeckeBaseChange.isPlaceIdem_iff v ε).2 hε)
  have hv : evFin F v ε = 1 := hε.2.1 v rfl
  rw [at_iff (ev := evFin F v) (1 - ε) (by rw [map_sub, map_one, hv, sub_self]) (fun u hu => ?_) M]
  · refine forall₂_congr fun i j => ?_
    rw [smul_zero_iff h, map_sub, map_one, ← GlobalTheory.UnitaryHeckeBaseChange.toAdele_algebraMap]
    set a := toAdele F E (algebraMap (AF F) (AE F E) ε)
    set y := toAdele F E (M i j)
    constructor
    · intro k
      refine ⟨?_, fun Q hQ => ?_⟩
      · have := congrArg Prod.fst k
        rw [GlobalTheory.UnitaryHeckeBaseChange.fst_mul, GlobalTheory.UnitaryHeckeBaseChange.fst_one_sub, hc.1, sub_zero, one_mul] at this
        exact this
      · have := congrArg (fun t : AdeleRing (𝓞 E) E => t.2 Q) k
        simp only [GlobalTheory.UnitaryHeckeBaseChange.ev_mul, GlobalTheory.UnitaryHeckeBaseChange.ev_one_sub, hc.2.2 Q hQ, sub_zero, one_mul] at this
        exact this
    · rintro ⟨k1, k2⟩
      refine Prod.ext ?_ (FiniteAdeleRing.ext _ fun Q => ?_)
      · rw [GlobalTheory.UnitaryHeckeBaseChange.fst_mul, k1, mul_zero]; rfl
      · rw [GlobalTheory.UnitaryHeckeBaseChange.ev_mul, GlobalTheory.UnitaryHeckeBaseChange.ev_one_sub]
        by_cases hQ : Q.under (𝓞 F) = v
        · rw [hc.2.1 Q hQ, sub_self, zero_mul]; rfl
        · rw [k2 Q hQ, mul_zero]; rfl
  · have e : u * ε = 0 := by
      refine Prod.ext ((congrArg (u.1 * ·) hε.1).trans (mul_zero _)) (FiniteAdeleRing.ext _ fun Q => ?_)
      rw [GlobalTheory.UnitaryHeckeBaseChange.ev_mul]
      by_cases hQ : Q = v
      · subst hQ
        rw [show u.2 Q = 0 from hu, zero_mul]; rfl
      · rw [hε.2.2 Q hQ, mul_zero]; rfl
    rw [sub_sub_cancel, e]

private theorem compInf_iff (h : IsCMExt F E σ) (z : AE F E) :
    (∀ w, compInf F E w z = 0) ↔ (toAdele F E z).1 = 0 := by
  let b : AF F := ((1, 0) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)
  have e : ∀ y : AdeleRing (𝓞 E) E, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap F E b * y = ((y.1, 0) : InfiniteAdeleRing E × FiniteAdeleRing (𝓞 E) E) := fun y =>
    Prod.ext ((congrArg (· * y.1) (map_one (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.infiniteAdeleMap F E))).trans (one_mul _))
      ((congrArg (· * y.2) (map_zero (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteAdeleMap F E))).trans (zero_mul _))
  have hw : ∀ w, compInf F E w (b • z) = compInf F E w z := fun w => by
    rw [GlobalTheory.AwayFix.Chart.compInf_smul_away, show evInf F w b = 1 from rfl, one_smul]
  constructor
  · intro k
    have : b • z = 0 := GlobalTheory.SWOpFin.tens_eq_zero_of_comp
      (fun v => by rw [GlobalTheory.AwayFix.Chart.compFin_smul_away, show evFin F v b = 0 from rfl, zero_smul]) (fun w => (hw w).trans (k w))
    have := (smul_zero_iff h b z).1 this
    rw [e] at this
    exact congrArg Prod.fst this
  · intro k w
    rw [← hw, (smul_zero_iff h b z).2 (by rw [e, k]; rfl), map_zero]

end Gen

section Read

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem coord_adeleMap [IsCMField E] {w : InfinitePlace F} (τ : EmbOver E w) (a : AF F) :
    coord τ.1 (pInf E (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap F E a)) = InfinitePlace.Completion.extensionEmbedding w (a.1 w) := by
  have hc : Continuous (coord (E := E) τ.1) := GlobalTheory.CuspRep.InfType.continuous_coord τ.1
  exact congrFun ((InfiniteAdeleRing.denseRange_algebraMap F).equalizer
    (g := fun b => coord τ.1 (pInf E (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.infiniteAdeleMap F E b, 0)))
    (h := fun b => InfinitePlace.Completion.extensionEmbedding w (b w))
    (hc.comp (GlobalTheory.BCT.GlobLev.continuous_pInf_ad.comp ((GlobalTheory.UnitaryHeckeBaseChange.continuous_infiniteAdeleMap F E).prodMk continuous_const)))
    ((InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp (continuous_apply w))
    (funext fun k => by
      have e : coord τ.1 (pInf E (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap F E (algebraMap F _ k))) = τ.1 (algebraMap F E k) := by
        rw [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap_algebraMap, GlobalTheory.CuspRep.coord_algebraMap]
      exact e.trans ((RingHom.congr_fun τ.2 k).trans
        (InfinitePlace.Completion.extensionEmbedding_coe w ((WithAbs.equiv w.1).symm k)).symm))) a.1

private theorem piInf_eq [IsCMField E] {w : InfinitePlace F} (τ : EmbOver E w) (z : AE F E) :
    piInf τ z = coord τ.1 (pInf E (toAdele F E z)) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a x =>
    rw [GlobalTheory.UnitaryHeckeBaseChange.toAdele_tmul, map_mul, map_mul, coord_adeleMap, GlobalTheory.CuspRep.coord_algebraMap]
    rfl

private theorem complMap_at {v : Pl F} {w : HeightOneSpectrum (𝓞 E)} (h : w.under (𝓞 F) = v) (a : Af F) :
    complMap h (a v) = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteCompletionMap F E w (a (w.under (𝓞 F))) := by
  subst h
  exact GlobalTheory.CharTransport.locMap_eq F E w _

private theorem piW_eq {v : Pl F} (t : E →ₐ[F] Fv F v) (z : AE F E) :
    complMap (splitPrime_under t) (piW t z) = pLoc E (splitPrime t) (pFin E (toAdele F E z)) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a x =>
    have e : piW t (a ⊗ₜ[F] x) = a.2 v * t x := rfl
    rw [e, map_mul, GlobalTheory.LFun.SplitTie.complMap_apply_emb t, complMap_at, GlobalTheory.UnitaryHeckeBaseChange.toAdele_tmul, map_mul, map_mul]
    rfl

end Read

section Grp

private theorem map_eq_one_iff {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {n : ℕ} (M : Matrix (Fin n) (Fin n) R) :
    M.map φ = 1 ↔ ∀ i j, φ ((M - 1 : Matrix (Fin n) (Fin n) R) i j) = 0 := by
  constructor
  · intro h i j
    have := congrFun (congrFun h i) j
    rw [Matrix.sub_apply, map_sub, sub_eq_zero]
    refine this.trans ?_
    by_cases e : i = j
    · subst e; simp
    · simp [Matrix.one_apply_ne e]
  · intro h
    refine Matrix.ext fun i j => ?_
    have := h i j
    rw [Matrix.sub_apply, map_sub, sub_eq_zero] at this
    refine this.trans ?_
    by_cases e : i = j
    · subst e; simp
    · simp [Matrix.one_apply_ne e]

private theorem gl_map_eq_one {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {n : ℕ} (g : GL (Fin n) R) :
    Matrix.GeneralLinearGroup.map φ g = 1 ↔ ∀ i j, φ ((g.1 - 1 : Matrix (Fin n) (Fin n) R) i j) = 0 :=
  Iff.trans ⟨fun h => congrArg Units.val h, fun h => Units.ext h⟩ (map_eq_one_iff φ g.1)

private theorem mem_closure_of {G H : Type} [Group G] [Group H] (e : G ≃* H) (K : Subgroup G) (S : Set H)
    (h : ∀ g, e g ∈ S ↔ g ∈ K) (g : G) : e g ∈ Subgroup.closure S ↔ g ∈ K := by
  have hS : S = (K.map e.toMonoidHom : Subgroup H) := by
    ext y
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [h, SetLike.mem_coe, Subgroup.mem_map_equiv (f := e), MulEquiv.symm_apply_apply]
  rw [hS, Subgroup.closure_eq, Subgroup.mem_map_equiv (f := e), MulEquiv.symm_apply_apply]

private theorem mem_closure_of' {G H : Type} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H] (e : G ≃ₜ* H)
    (K : Subgroup G) (S : Set H) (h : ∀ g, e g ∈ S ↔ g ∈ K) (g : G) : e g ∈ Subgroup.closure S ↔ g ∈ K :=
  mem_closure_of e.toMulEquiv K S h g

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private abbrev Θ : AE (maximalRealSubfield E) E ≃+* Ad E := adeleEquiv (cmE (E := E))

private theorem Θ_apply (z : AE (maximalRealSubfield E) E) : Θ z = toAdele _ E z := rfl

private theorem toAdele_symm (y : Ad E) : toAdele (maximalRealSubfield E) E (Θ.symm y) = y := Θ.apply_symm_apply y

private def th (n : ℕ) : GL (Fin n) (Ad E) →* GL (Fin n) (AE (maximalRealSubfield E) E) :=
  Matrix.GeneralLinearGroup.map (Θ (E := E)).symm.toRingHom

private def ht (n : ℕ) : GL (Fin n) (AE (maximalRealSubfield E) E) →* GL (Fin n) (Ad E) :=
  Matrix.GeneralLinearGroup.map (Θ (E := E)).toRingHom

private theorem ht_th (g : GL (Fin n) (Ad E)) : ht n (th n g) = g :=
  Units.ext (Matrix.ext fun _ _ => Θ.apply_symm_apply _)

private theorem th_ht (g : GL (Fin n) (AE (maximalRealSubfield E) E)) : th n (ht n g) = g :=
  Units.ext (Matrix.ext fun _ _ => Θ.symm_apply_apply _)

private theorem mem_iff (J : Matrix (Fin n) (Fin n) E) (δ : E) (hδ : δ ≠ 0) (hJ : J = δ • 1) (g : GL (Fin n) (Ad E)) :
    g ∈ GlobalTheory.UnitaryBC.UA E n ↔ th n g ∈ UG (cA (cj E)) (incM (maximalRealSubfield E) J) := by
  set M : Matrix (Fin n) (Fin n) (AE (maximalRealSubfield E) E) := (th n g).1 with hM
  have hg : g.1 = M.map (Θ (E := E)).toRingHom := Matrix.ext fun _ _ => (Θ.apply_symm_apply _).symm
  set N := M.map (cA (cj E)) with hN
  set d := inclR (F := maximalRealSubfield E) (AF (maximalRealSubfield E)) δ with hd
  have hdu : d * inclR (F := maximalRealSubfield E) (AF (maximalRealSubfield E)) δ⁻¹ = 1 := by
    rw [hd, ← map_mul, mul_inv_cancel₀ hδ, map_one]
  have hinc : incM (maximalRealSubfield E) J = d • (1 : Matrix (Fin n) (Fin n) (AE (maximalRealSubfield E) E)) := by
    subst hJ
    ext i j
    by_cases e : i = j
    · subst e; simp [incM, hd]
    · simp [incM, Matrix.one_apply_ne e]
  have e2 : th n g ∈ UG (cA (cj E)) (incM (maximalRealSubfield E) J) ↔ Mᵀ * N = 1 := by
    change Mᵀ * incM (maximalRealSubfield E) J * N = incM (maximalRealSubfield E) J ↔ _
    rw [hinc, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
    constructor
    · intro k
      have := congrArg (fun P => inclR (F := maximalRealSubfield E) (AF (maximalRealSubfield E)) δ⁻¹ • P) k
      simpa [smul_smul, mul_comm _ d, hdu] using this
    · intro k
      rw [k]
  have e1 : g ∈ GlobalTheory.UnitaryBC.UA E n ↔ (Nᵀ * M).map (Θ (E := E)).toRingHom = 1 := by
    change Formalism.UG.cT (GlobalTheory.UnitaryBC.conjAd E) g.1 * 1 * g.1 = 1 ↔ _
    have : Formalism.UG.cT (GlobalTheory.UnitaryBC.conjAd E) g.1 = (Nᵀ).map (Θ (E := E)).toRingHom := by
      rw [hg]
      ext i j
      exact (toAdele_cj _).symm
    rw [this, Matrix.mul_one, hg, Matrix.map_mul]
  rw [e1, e2]
  constructor
  · intro k
    have k2 : Nᵀ * M = 1 := by
      ext i j
      refine Θ.injective ?_
      have := congrFun (congrFun k i) j
      refine this.trans ?_
      by_cases e : i = j
      · subst e; simp
      · simp [Matrix.one_apply_ne e]
    have := congrArg Matrix.transpose k2
    simpa [Matrix.transpose_mul] using this
  · intro k
    have k2 : Nᵀ * M = 1 := by
      have := congrArg Matrix.transpose k
      simpa [Matrix.transpose_mul] using this
    rw [k2]
    ext i j
    by_cases e : i = j
    · subst e; simp
    · simp [Matrix.one_apply_ne e]

end Grp

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private theorem th_cont : Continuous (th (E := E) n) := by
  have c := GlobalTheory.UnitaryHeckeBaseChange.continuous_adeleEquiv_symm (cmE (E := E))
  exact Units.continuous_iff.2 ⟨Units.continuous_val.matrix_map c, Units.continuous_coe_inv.matrix_map c⟩

private theorem ht_cont : Continuous (ht (E := E) n) := by
  have c : Continuous (Θ (E := E)) := GlobalTheory.UnitaryHeckeBaseChange.continuous_toAdele _ E
  exact Units.continuous_iff.2 ⟨Units.continuous_val.matrix_map c, Units.continuous_coe_inv.matrix_map c⟩

private def brE (X : Spc (maximalRealSubfield E) E n) (δ : E) (hδ : δ ≠ 0) (hJ : X.J = δ • (1 : Matrix (Fin n) (Fin n) E)) :
    GlobalTheory.UnitaryBC.UA E n ≃ₜ* UA (cj E) X.J where
  toFun g := ⟨th n g.1, (mem_iff X.J δ hδ hJ g.1).1 g.2⟩
  invFun h := ⟨ht n h.1, (mem_iff X.J δ hδ hJ _).2 (by rw [th_ht]; exact h.2)⟩
  left_inv g := Subtype.ext (ht_th g.1)
  right_inv h := Subtype.ext (th_ht h.1)
  map_mul' g g' := Subtype.ext (map_mul (th n) g.1 g'.1)
  continuous_toFun := (th_cont.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (ht_cont.comp continuous_subtype_val).subtype_mk _

variable (X : Spc (maximalRealSubfield E) E n) (δ : E) (hδ : δ ≠ 0) (hJ : X.J = δ • (1 : Matrix (Fin n) (Fin n) E))

private theorem mat_brE (g : GlobalTheory.UnitaryBC.UA E n) (i j : Fin n) : mat (brE X δ hδ hJ g) i j = Θ.symm (g.1.1 i j) := rfl

private theorem toAdele_brE (g : GlobalTheory.UnitaryBC.UA E n) (i j : Fin n) :
    toAdele _ E ((mat (brE X δ hδ hJ g) - 1 : Matrix (Fin n) (Fin n) (AE (maximalRealSubfield E) E)) i j) =
      ((g.1.1 - 1 : Matrix (Fin n) (Fin n) (Ad E)) i j) := by
  rw [Matrix.sub_apply, Matrix.sub_apply, map_sub, mat_brE, toAdele_symm]
  congr 1
  by_cases e : i = j
  · subst e; simp
  · simp [Matrix.one_apply_ne e]

private theorem pInf_zero (y : Ad E) : pInf E y = 0 ↔ y.1 = 0 := (GlobalTheory.CuspRep.infEq E).symm.map_eq_zero_iff

private theorem mem_finU (g : GlobalTheory.UnitaryBC.UA E n) :
    g ∈ GlobalTheory.UnitaryBC.finU E n ↔ ∀ i j, ((g.1.1 - 1 : Matrix (Fin n) (Fin n) (Ad E)) i j).1 = 0 :=
  (gl_map_eq_one (pInf E) g.1).trans (forall₂_congr fun _ _ => pInf_zero _)

private theorem mem_infU (g : GlobalTheory.UnitaryBC.UA E n) :
    g ∈ GlobalTheory.UnitaryBC.infU E n ↔ ∀ i j, ((g.1.1 - 1 : Matrix (Fin n) (Fin n) (Ad E)) i j).2 = 0 :=
  gl_map_eq_one (pFin E) g.1

private theorem mem_kerLoc (g : GlobalTheory.UnitaryBC.UA E n) (u : HeightOneSpectrum (𝓞 E)) :
    g ∈ (GlobalTheory.UnitaryBC.cLoc (n := n) u).ker ↔ ∀ i j, ((g.1.1 - 1 : Matrix (Fin n) (Fin n) (Ad E)) i j).2 u = 0 :=
  gl_map_eq_one ((pLoc E u).comp (pFin E)) g.1

private theorem brE_isBr : IsBr X (brE X δ hδ hJ) := by
  have hrat : ∀ γ : GL (Fin n) E, th n (GlobalTheory.CuspRep.ratGL E n γ) =
      Matrix.GeneralLinearGroup.map (inclR (F := maximalRealSubfield E) (AF (maximalRealSubfield E))) γ := fun γ =>
    Units.ext (Matrix.ext fun a b => Θ.symm_apply_eq.2 (GlobalTheory.UnitaryHeckeBaseChange.toAdele_incA _).symm)
  refine ⟨fun g => ?_, fun g => ?_, fun g => ?_, fun w g => ?_, fun w τ g => ?_, fun v t g => ?_⟩
  · constructor
    · rintro ⟨γ, hγ⟩
      refine ⟨γ, ?_⟩
      have : th n (GlobalTheory.CuspRep.ratGL E n γ) = th n g.1 := (hrat γ).trans hγ
      exact (ht_th _).symm.trans ((congrArg (ht n) this).trans (ht_th _))
    · rintro ⟨γ, hγ⟩
      exact ⟨γ, (hrat γ).symm.trans (congrArg (th n) hγ)⟩
  · refine mem_closure_of' (brE X δ hδ hJ) _ _ (fun g => ?_) g
    refine (at_evI_iff cmE _).trans ((forall₂_congr fun i j => ?_).trans (mem_infU g).symm)
    rw [toAdele_brE]
  · refine mem_closure_of' (brE X δ hδ hJ) _ _ (fun g => ?_) g
    refine Iff.trans ?_ (mem_finU g).symm
    refine Iff.trans ⟨fun h => h.1, fun h => ⟨h, fun _ hv => absurd hv (Finset.notMem_empty _)⟩⟩ ?_
    refine (forall_congr' fun w => map_eq_one_iff (compInf _ E w) _).trans ?_
    refine ⟨fun h i j => ?_, fun h w i j => ?_⟩
    · rw [← toAdele_brE X δ hδ hJ g i j]
      exact (compInf_iff cmE _).1 fun w => h w i j
    · refine (compInf_iff cmE _).2 ?_ w
      rw [toAdele_brE]
      exact h i j
  · refine mem_closure_of' (brE X δ hδ hJ) _ _ (fun g => ?_) g
    refine (at_evFin_iff cmE _ _).trans ?_
    have hl : g ∈ GlobalTheory.UnitaryBC.locU n w ↔ g ∈ GlobalTheory.UnitaryBC.finU E n ∧ ∀ u : HeightOneSpectrum (𝓞 E),
        u.under (𝓞 (maximalRealSubfield E)) ≠ w.under (𝓞 (maximalRealSubfield E)) → g ∈ (GlobalTheory.UnitaryBC.cLoc (n := n) u).ker := by
      unfold GlobalTheory.UnitaryBC.locU
      rw [Subgroup.mem_inf]
      simp only [Subgroup.mem_iInf]
    rw [hl]
    simp only [toAdele_brE, mem_finU, mem_kerLoc]
    exact ⟨fun h => ⟨fun i j => (h i j).1, fun u hu i j => (h i j).2 u hu⟩,
      fun h i j => ⟨h.1 i j, fun u hu => h.2 u hu i j⟩⟩
  · refine Matrix.ext fun i j => ?_
    refine (piInf_eq τ _).trans ?_
    rw [mat_brE, toAdele_symm]
    rfl
  · refine Matrix.ext fun i j => ?_
    refine (piW_eq t _).trans ?_
    rw [mat_brE, toAdele_symm]
    rfl

end Main

end UpperTheory.TP

theorem UpperTheory.TP.brEx :
    UpperTheory.TP.BrEx := fun _ _ _ _ _ X δ hδ hJ => ⟨UpperTheory.TP.brE X δ hδ hJ, UpperTheory.TP.brE_isBr X δ hδ hJ⟩

end
