import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.WhittakerVanishingImpliesZero
import GroundTheory.GlobalFields.Adele.WeakApprox

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter BoundedContinuousFunction
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.LFun Formalism.UG Formalism.L2.Host

namespace PositivityTheory.jumpWindows.GoodInverseDenseRange

def GoodInv (B : Type) [CommRing B] [TopologicalSpace B] : Prop :=
  IsOpen {x : B | IsUnit x} ∧ ∀ x : B, IsUnit x → ContinuousAt Ring.inverse x

theorem goodInv_field (K : Type) [Field K] [TopologicalSpace K] [ContinuousInv₀ K] [T1Space K] :
    GoodInv K := by
  refine ⟨?_, fun x hx => ?_⟩
  · have e : {x : K | IsUnit x} = {x | x ≠ 0} := by ext x; exact isUnit_iff_ne_zero
    rw [e]; exact isOpen_ne
  · rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ hx.ne_zero

theorem goodInv_pi {ι : Type} [Fintype ι] {K : ι → Type} [∀ i, CommRing (K i)] [∀ i, TopologicalSpace (K i)]
    (h : ∀ i, GoodInv (K i)) : GoodInv (∀ i, K i) := by
  have hU : {x : ∀ i, K i | IsUnit x} = ⋂ i, (fun x : ∀ i, K i => x i) ⁻¹' {y | IsUnit y} := by
    ext x; simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]; exact Pi.isUnit_iff
  have hO : IsOpen {x : ∀ i, K i | IsUnit x} := by
    rw [hU]; exact isOpen_iInter_of_finite fun i => (h i).1.preimage (continuous_apply i)
  refine ⟨hO, fun x hx => ?_⟩
  have hx' : ∀ i, IsUnit (x i) := Pi.isUnit_iff.1 hx
  have hc : ContinuousAt (fun y : ∀ i, K i => fun i => Ring.inverse (y i)) x :=
    continuousAt_pi.2 fun i => ((h i).2 _ (hx' i)).comp (continuous_apply i).continuousAt
  refine hc.congr ?_
  filter_upwards [hO.mem_nhds hx] with y hy
  have hy' : ∀ i, IsUnit (y i) := Pi.isUnit_iff.1 hy
  have h1 : y * (fun i => Ring.inverse (y i)) = 1 := funext fun i => Ring.mul_inverse_cancel _ (hy' i)
  calc (fun i => Ring.inverse (y i)) = (Ring.inverse y * y) * (fun i => Ring.inverse (y i)) := by
        rw [Ring.inverse_mul_cancel _ hy, one_mul]
    _ = Ring.inverse y := by rw [mul_assoc, h1, mul_one]

theorem goodInv_prod {A C : Type} [CommRing A] [TopologicalSpace A] [CommRing C] [TopologicalSpace C]
    (hA : GoodInv A) (hC : GoodInv C) : GoodInv (A × C) := by
  have hU : {x : A × C | IsUnit x} = Prod.fst ⁻¹' {y | IsUnit y} ∩ Prod.snd ⁻¹' {y | IsUnit y} := by
    ext x; exact Prod.isUnit_iff
  have hO : IsOpen {x : A × C | IsUnit x} := by
    rw [hU]; exact (hA.1.preimage continuous_fst).inter (hC.1.preimage continuous_snd)
  refine ⟨hO, fun x hx => ?_⟩
  have hx' := Prod.isUnit_iff.1 hx
  have hc : ContinuousAt (fun y : A × C => (Ring.inverse y.1, Ring.inverse y.2)) x :=
    ((hA.2 _ hx'.1).comp continuousAt_fst).prodMk ((hC.2 _ hx'.2).comp continuousAt_snd)
  refine hc.congr ?_
  filter_upwards [hO.mem_nhds hx] with y hy
  have hy' := Prod.isUnit_iff.1 hy
  have h1 : y * (Ring.inverse y.1, Ring.inverse y.2) = 1 :=
    Prod.ext (Ring.mul_inverse_cancel _ hy'.1) (Ring.mul_inverse_cancel _ hy'.2)
  calc (Ring.inverse y.1, Ring.inverse y.2) = (Ring.inverse y * y) * (Ring.inverse y.1, Ring.inverse y.2) := by
        rw [Ring.inverse_mul_cancel _ hy, one_mul]
    _ = Ring.inverse y := by rw [mul_assoc, h1, mul_one]

theorem denseRange_mapGL {K B : Type} [Field K] [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    (hB : GoodInv B) (j : K →+* B) (hj : DenseRange j) (a : ℕ) :
    DenseRange (GeneralLinearGroup.map j : GL (Fin a) K → GL (Fin a) B) := by
  rcases subsingleton_or_nontrivial B with hs | hs
  · intro M
    have : Subsingleton (GL (Fin a) B) := by
      refine ⟨fun u v => Units.ext ?_⟩
      ext i k; exact Subsingleton.elim _ _
    exact subset_closure ⟨1, Subsingleton.elim _ _⟩
  intro M
  rw [mem_closure_iff]
  intro o ho hMo
  obtain ⟨O, hO, rfl⟩ := isOpen_induced_iff.1 ho
  let f : Matrix (Fin a) (Fin a) B → Matrix (Fin a) (Fin a) B × (Matrix (Fin a) (Fin a) B)ᵐᵒᵖ :=
    fun P => (P, MulOpposite.op P⁻¹)
  have hdet : IsUnit (M.val.det) := (Matrix.isUnit_iff_isUnit_det _).1 M.isUnit
  have hinv : ContinuousAt (fun P : Matrix (Fin a) (Fin a) B => P⁻¹) M.val := by
    have e : (fun P : Matrix (Fin a) (Fin a) B => P⁻¹) = fun P => Ring.inverse P.det • P.adjugate := by
      funext P; exact Matrix.inv_def P
    rw [e]
    exact ((hB.2 _ hdet).comp (continuous_id.matrix_det).continuousAt).smul
      (continuous_id.matrix_adjugate).continuousAt
  have hf : ContinuousAt f M.val := continuousAt_id.prodMk (MulOpposite.continuous_op.continuousAt.comp hinv)
  have hfM : f M.val = Units.embedProduct _ M := by
    simp only [f, Units.embedProduct_apply, Matrix.coe_units_inv]
  have hN : f ⁻¹' O ∩ {P | IsUnit P.det} ∈ 𝓝 M.val := by
    refine Filter.inter_mem (hf.preimage_mem_nhds (hO.mem_nhds ?_)) ?_
    · rw [hfM]; exact hMo
    · exact (hB.1.preimage (continuous_id.matrix_det)).mem_nhds hdet
  have hd : DenseRange fun Q : Matrix (Fin a) (Fin a) K => Q.map j :=
    DenseRange.piMap fun _ => DenseRange.piMap fun _ => hj
  obtain ⟨Q, hQO, hQd⟩ := hd.mem_nhds hN
  have hQ : IsUnit Q.det := by
    refine isUnit_iff_ne_zero.2 fun h0 => ?_
    have : IsUnit (j Q.det) := by rw [RingHom.map_det]; exact hQd
    rw [h0, map_zero] at this
    exact not_isUnit_zero this
  let γ : GL (Fin a) K := ((Matrix.isUnit_iff_isUnit_det Q).2 hQ).unit
  refine ⟨GeneralLinearGroup.map j γ, ?_, γ, rfl⟩
  change Units.embedProduct _ (GeneralLinearGroup.map j γ) ∈ O
  have e : Units.embedProduct _ (GeneralLinearGroup.map j γ) = f (Q.map j) := by
    simp only [f, Units.embedProduct_apply, Matrix.coe_units_inv]
    rfl
  rw [e]; exact hQO

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

abbrev BS (S : Finset (Pl E)) : Type := ((v : S) → v.1.adicCompletion E) × Cinf E

def jS (S : Finset (Pl E)) : E →+* BS S :=
  RingHom.prod (RingHom.pi fun v : S => algebraMap E (v.1.adicCompletion E)) ((pInf E).comp (algebraMap E (Ad E)))

theorem denseRange_jS (S : Finset (Pl E)) : DenseRange (jS S) := by
  classical
  have hd := GroundTheory.Global.denseRange_algebraMap_prod_pi (K := E) S (Finset.univ : Finset (InfinitePlace E))
  let h : ((v : S) → v.1.adicCompletion E) × ((w : (Finset.univ : Finset (InfinitePlace E))) → w.1.Completion) →
      BS S := fun p => (p.1, fun w =>
        InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w) (p.2 ⟨w, Finset.mem_univ w⟩))
  have hc : Continuous h := continuous_fst.prodMk (continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
      ((continuous_apply _).comp continuous_snd))
  have hs : Function.Surjective h := by
    rintro ⟨p, c⟩
    refine ⟨(p, fun w => (InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w.1)).symm
      (c w.1)), ?_⟩
    exact Prod.ext rfl (funext fun w => RingEquiv.apply_symm_apply _ _)
  convert hs.denseRange.comp hd hc using 1
  funext x
  refine Prod.ext rfl (funext fun w => ?_)
  rfl

omit [IsTotallyComplex E] in
theorem goodInv_BS (S : Finset (Pl E)) : GoodInv (BS S) :=
  goodInv_prod (goodInv_pi fun _ => goodInv_field _) (goodInv_pi fun _ => goodInv_field ℂ)

def ρS (S : Finset (Pl E)) : Ad E →+* BS S :=
  RingHom.prod (RingHom.pi fun v : S => (pLoc E v.1).comp (pFin E)) (pInf E)

theorem ρS_comp (S : Finset (Pl E)) : (ρS S).comp (algebraMap E (Ad E)) = jS S := by
  ext x
  · rfl
  · rfl

theorem continuous_pInf : Continuous (pInf E) := by
  change Continuous fun y : InfiniteAdeleRing E × Af E => (infEq E).symm y.1
  exact continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
      ((continuous_apply w).comp continuous_fst)

theorem continuous_ρS (S : Finset (Pl E)) : Continuous (ρS S) := by
  change Continuous fun y : Ad E => ((fun v : S => pLoc E v.1 (pFin E y)), pInf E y)
  refine Continuous.prodMk (continuous_pi fun v => ?_) continuous_pInf
  change Continuous fun y : InfiniteAdeleRing E × Af E => (y.2 : Af E) v.1
  exact (RestrictedProduct.continuous_eval v.1).comp continuous_snd

open Classical in

def fSr (S : Finset (Pl E)) (p : (v : S) → v.1.adicCompletion E) : (w : Pl E) → w.adicCompletion E :=
  fun w => if h : w ∈ S then p ⟨w, h⟩ else 0

omit [IsTotallyComplex E] in
theorem fSr_of_mem (S : Finset (Pl E)) (p : (v : S) → v.1.adicCompletion E) {w : Pl E} (h : w ∈ S) :
    fSr S p w = p ⟨w, h⟩ := by
  classical
  unfold fSr; rw [dif_pos h]

omit [IsTotallyComplex E] in
theorem fSr_of_not_mem (S : Finset (Pl E)) (p : (v : S) → v.1.adicCompletion E) {w : Pl E} (h : w ∉ S) :
    fSr S p w = 0 := by
  classical
  unfold fSr; rw [dif_neg h]

omit [IsTotallyComplex E] in
theorem fSr_mul (S : Finset (Pl E)) (p q : (v : S) → v.1.adicCompletion E) : fSr S (p * q) = fSr S p * fSr S q := by
  funext w
  by_cases h : w ∈ S
  · rw [Pi.mul_apply, fSr_of_mem S _ h, fSr_of_mem S _ h, fSr_of_mem S _ h]; rfl
  · rw [Pi.mul_apply, fSr_of_not_mem S _ h, fSr_of_not_mem S _ h, fSr_of_not_mem S _ h, zero_mul]

omit [IsTotallyComplex E] in
theorem fSr_add (S : Finset (Pl E)) (p q : (v : S) → v.1.adicCompletion E) : fSr S (p + q) = fSr S p + fSr S q := by
  funext w
  by_cases h : w ∈ S
  · rw [Pi.add_apply, fSr_of_mem S _ h, fSr_of_mem S _ h, fSr_of_mem S _ h]; rfl
  · rw [Pi.add_apply, fSr_of_not_mem S _ h, fSr_of_not_mem S _ h, fSr_of_not_mem S _ h, zero_add]

omit [IsTotallyComplex E] in
theorem fSr_zero (S : Finset (Pl E)) : fSr S 0 = 0 := by
  funext w
  by_cases h : w ∈ S
  · rw [fSr_of_mem S _ h]; rfl
  · rw [fSr_of_not_mem S _ h]; rfl

omit [IsTotallyComplex E] in
theorem fSr_int (S : Finset (Pl E)) (p : (v : S) → v.1.adicCompletion E) :
    ∀ v ∈ (↑S : Set (Pl E))ᶜ, fSr S p v ∈ (v.adicCompletionIntegers E : Set (v.adicCompletion E)) := by
  intro v hv
  rw [fSr_of_not_mem S p hv]
  exact zero_mem _

omit [IsTotallyComplex E] in
theorem continuous_fSr (S : Finset (Pl E)) : Continuous (fSr S) := by
  refine continuous_pi fun w => ?_
  by_cases h : w ∈ S
  · have : (fun p : (v : S) → v.1.adicCompletion E => fSr S p w) = fun p => p ⟨w, h⟩ :=
      funext fun p => fSr_of_mem S p h
    rw [this]; exact continuous_apply _
  · have : (fun p : (v : S) → v.1.adicCompletion E => fSr S p w) = fun _ => 0 :=
      funext fun p => fSr_of_not_mem S p h
    rw [this]; exact continuous_const

def fS (S : Finset (Pl E)) : ((v : S) → v.1.adicCompletion E) →ₙ+* Af E where
  toFun p := ⟨fSr S p, Filter.mem_of_superset S.finite_toSet.compl_mem_cofinite (fSr_int S p)⟩
  map_mul' p q := Subtype.ext (fSr_mul S p q)
  map_zero' := Subtype.ext (fSr_zero S)
  map_add' p q := Subtype.ext (fSr_add S p q)

omit [IsTotallyComplex E] in
theorem continuous_fS (S : Finset (Pl E)) : Continuous (fS S) := by
  let g : ((v : S) → v.1.adicCompletion E) →
      RestrictedProduct (fun v : Pl E => v.adicCompletion E) (fun v => (v.adicCompletionIntegers E : Set (v.adicCompletion E)))
        (𝓟 (↑S : Set (Pl E))ᶜ) :=
    fun p => ⟨fSr S p, Filter.eventually_principal.2 (fSr_int S p)⟩
  have hg : Continuous g := RestrictedProduct.continuous_rng_of_principal.2 (continuous_fSr S)
  have hle : (cofinite : Filter (Pl E)) ≤ 𝓟 (↑S : Set (Pl E))ᶜ :=
    Filter.le_principal_iff.2 S.finite_toSet.compl_mem_cofinite
  exact (RestrictedProduct.continuous_inclusion hle).comp hg

def σS (S : Finset (Pl E)) : BS S →ₙ+* Ad E where
  toFun b := ((infEq E b.2, fS S b.1) : InfiniteAdeleRing E × Af E)
  map_mul' _ _ := Prod.ext (map_mul (infEq E) _ _) (map_mul (fS S) _ _)
  map_zero' := Prod.ext (map_zero (infEq E)) (map_zero (fS S))
  map_add' _ _ := Prod.ext (map_add (infEq E) _ _) (map_add (fS S) _ _)

theorem continuous_σS (S : Finset (Pl E)) : Continuous (σS S) :=
  ((continuous_infEq E).comp continuous_snd).prodMk ((continuous_fS S).comp continuous_fst)

theorem pInf_σS (S : Finset (Pl E)) (b : BS S) : pInf E (σS S b) = b.2 :=
  (infEq E).symm_apply_apply b.2

theorem pLoc_σS (S : Finset (Pl E)) (b : BS S) (w : Pl E) (hw : w ∈ S) :
    pLoc E w (pFin E (σS S b)) = b.1 ⟨w, hw⟩ :=
  fSr_of_mem S b.1 hw

end PositivityTheory.jumpWindows.GoodInverseDenseRange

namespace PositivityTheory.jumpWindows

theorem good_inverse_of_G0 : G0 → WeakApproximationGL := by
  intro _ E _ _ _ a S
  classical
  rw [dense_iff_inter_open]
  rintro U hU ⟨x, hx⟩
  set ρ := GoodInverseDenseRange.ρS S
  set σ := GoodInverseDenseRange.σS S
  have hc : Continuous (cornerGL a σ) :=
    Continuous.units_map _ (continuous_const.add (continuous_id.matrix_map (GoodInverseDenseRange.continuous_σS S)))
  have hρ : Continuous (GeneralLinearGroup.map ρ : GL (Fin a) (Ad E) → GL (Fin a) (GoodInverseDenseRange.BS S)) :=
    Continuous.units_map _ (continuous_id.matrix_map (GoodInverseDenseRange.continuous_ρS S))
  set H : GL (Fin a) (GoodInverseDenseRange.BS S) → GA E a := fun z => x * cornerGL a σ ((GeneralLinearGroup.map ρ x)⁻¹ * z) with hHdef
  have hH : Continuous H := continuous_const.mul (hc.comp (continuous_const.mul continuous_id))
  have hHx : H (GeneralLinearGroup.map ρ x) = x := by simp [hHdef]
  obtain ⟨γ, hγ⟩ := (GoodInverseDenseRange.denseRange_mapGL (GoodInverseDenseRange.goodInv_BS S) (GoodInverseDenseRange.jS S) (GoodInverseDenseRange.denseRange_jS S) a).exists_mem_open
    (hU.preimage hH) ⟨_, show H (GeneralLinearGroup.map ρ x) ∈ U by rw [hHx]; exact hx⟩
  have e : GeneralLinearGroup.map (GoodInverseDenseRange.jS S) γ = GeneralLinearGroup.map ρ (ratGL E a γ) := by
    rw [← GoodInverseDenseRange.ρS_comp]; rfl
  rw [Set.mem_preimage, e] at hγ
  refine ⟨_, hγ, γ, (ratGL E a γ)⁻¹ * H (GeneralLinearGroup.map ρ (ratGL E a γ)), by group, ?_, ?_⟩
  · have key1 : ∀ z, cInf (cornerGL a σ z) = GeneralLinearGroup.map (RingHom.snd _ _) z := fun z =>
      map_cornerGL_of_hom _ _ _ (GoodInverseDenseRange.pInf_σS S) z
    have key2 : ∀ y : GA E a, GeneralLinearGroup.map (RingHom.snd _ _) (GeneralLinearGroup.map ρ y) = cInf y :=
      fun y => rfl
    simp only [hHdef, map_mul, map_inv, key1, key2]
    group
  · intro w hw
    have key1 : ∀ z, cLoc w (cornerGL a σ z) =
        GeneralLinearGroup.map ((Pi.evalRingHom (fun v : S => v.1.adicCompletion E) ⟨w, hw⟩).comp (RingHom.fst _ _)) z :=
      fun z => map_cornerGL_of_hom _ _ _ (fun b => GoodInverseDenseRange.pLoc_σS S b w hw) z
    have key2 : ∀ y : GA E a, GeneralLinearGroup.map ((Pi.evalRingHom (fun v : S => v.1.adicCompletion E) ⟨w, hw⟩).comp
        (RingHom.fst _ _)) (GeneralLinearGroup.map ρ y) = cLoc w y := fun y => rfl
    simp only [hHdef, map_mul, map_inv, key1, key2]
    group

end PositivityTheory.jumpWindows

end
