import Mathlib
import Development.WeilBound.ThetaLifts.LatticeBasics.FrameB
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSiegelHProjArchEq
import Development.WeilBound.ThetaLifts.LatticeBasics.HypothesesE

noncomputable section

namespace GlobalTheory.ThK.Dbl.Frame

open scoped Matrix TensorProduct
open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Doubling
open Formalism.UG (bc)

section Generic

variable {S R β : Type} [CommRing S] [CommRing R] [Fintype β] [DecidableEq β]

theorem exists_dual (c : S →+* S) (hc : ∀ z, c (c z) = z) {J : Matrix β β S} (hJ : IsUnit J) (g : GL β S) :
    ∃ T : GL β S, g.1ᵀ * J * g.1.map c * T.1.map c = 1 := by
  obtain ⟨u, hu⟩ : IsUnit (g.1ᵀ * J * g.1.map c) := (((Matrix.isUnit_transpose _).2 g.isUnit).mul hJ).mul (bc c g).isUnit
  exact ⟨bc c u⁻¹, by rw [← hu, ← u.mul_inv]; congr 1; exact Matrix.ext fun i j => hc _⟩

theorem int_dual {A : Subring S} {c : S →+* S} (hc : ∀ z, c (c z) = z) (hA : ∀ z ∈ A, c z ∈ A) {G G' : Matrix β β S} {T : GL β S}
    (h : Int A G) (h' : Int A G') (e : G' * G = 1) (e' : G * T.1.map c = 1) : Int A T.1 ∧ Int A (T⁻¹).1 := by
  have e1 : T.1.map c = G' := by rw [← Matrix.one_mul (T.1.map c), ← e, Matrix.mul_assoc, e', Matrix.mul_one]
  have e2 : (T⁻¹).1.map c = G := by
    rw [← Matrix.one_mul ((T⁻¹).1.map c), ← e', Matrix.mul_assoc, ← Matrix.map_mul, Units.mul_inv,
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one]
  exact ⟨fun i j => hc (T.1 i j) ▸ hA _ ((e1 ▸ h') i j), fun i j => hc ((T⁻¹).1 i j) ▸ hA _ ((e2 ▸ h) i j)⟩

theorem bc_two (f : S →+* R) (g : GL β S) : bc f (two g) = two (bc f g) := Units.ext <| by
  change (Matrix.fromBlocks g.1 0 0 g.1).map f = _
  rw [Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero f)]; rfl

theorem bc_wit (f : S →+* R) (a : S) (T : GL β S) : bc f (wit a T) = wit (f a) (bc f T) := Units.ext <| by
  change (Matrix.fromBlocks 1 (a • T.1) 1 ((a - 1) • T.1)).map f = Matrix.fromBlocks 1 (f a • T.1.map f) 1 ((f a - 1) • T.1.map f)
  rw [Matrix.fromBlocks_map, Matrix.map_one _ (map_zero _) (map_one _)]
  congr 1 <;> ext i j <;> simp

omit [DecidableEq β] in
theorem map_gram (f : S →+* R) {c : S → S} {c' : R → R} (h : ∀ z, f (c z) = c' (f z)) (X J : Matrix β β S) :
    (Xᵀ * J * X.map c).map f = (X.map f)ᵀ * J.map f * (X.map f).map c' := by
  rw [Matrix.map_mul, Matrix.map_mul]
  congr 1
  exact Matrix.ext fun i j => h _

omit [Fintype β] [DecidableEq β] in
theorem map_dbl (f : S →+* R) (J : Matrix β β S) : (dbl J).map f = dbl (J.map f) := by
  ext (i | i) (j | j) <;> simp [dbl]

theorem par_of (f : S →+* R) {b : GL (β ⊕ β) S} {b' : GL (β ⊕ β) R} {X : Matrix (β ⊕ β) β R}
    (h : b.1 * (Matrix.fromRows 1 0 : Matrix (β ⊕ β) β S) = diagCols β) (h' : b'.1 * (Matrix.fromRows 1 0 : Matrix (β ⊕ β) β R) = X) :
    (b' * (bc f b)⁻¹).1 * (diagCols β : Matrix (β ⊕ β) β R) = X := by
  have e : (bc f b).1 * (Matrix.fromRows 1 0 : Matrix (β ⊕ β) β R) = diagCols β := by
    have := congrArg (·.map f) h
    simp only [Matrix.map_mul, diagCols, Matrix.fromRows_map, Matrix.map_one _ (map_zero f) (map_one f),
      Matrix.map_zero _ (map_zero f)] at this
    exact this
  rw [← e, ← h', ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel_right]

end Generic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}

variable (F) in

def eF : AF F := LinearMap.inr F (Ainf F) (Af F) 1

omit [NumberField E] in
theorem smul_incl (a : AF F) (x : E) : a • inclR (F := F) (AF F) x = a ⊗ₜ[F] x := by
  change (a * 1) ⊗ₜ[F] x = _
  rw [mul_one]

theorem mem_latHat (hL : Y.L.FG) (z : Fin n → AE F E) :
    z ∈ latHat Y ↔ eF F • z = z ∧ ∀ v, compFin F E v ∘ z ∈ latLoc F Y.L v := by
  constructor
  · intro hz
    induction hz using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, ha', x, hx, rfl⟩ := hy
      refine ⟨?_, fun v => ?_⟩
      · have : a.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).map_eq_zero_iff.1 ha
        rw [smul_smul]
        congr 1
        exact Prod.ext ((zero_mul _).trans this.symm) (one_mul _)
      · convert tmul_mem_latLoc (ha' v) hx using 1
        exact funext fun i => congrArg (compFin F E v) (smul_incl a (x i))
    | zero => exact ⟨smul_zero _, fun v => by
        convert zero_mem (latLoc F Y.L v) using 1
        exact funext fun i => map_zero _⟩
    | add y z _ _ hy hz => exact ⟨by rw [smul_add, hy.1, hz.1], fun v => by
        convert add_mem (hy.2 v) (hz.2 v) using 1
        exact funext fun i => map_add _ _ _⟩
    | neg y _ hy => exact ⟨by rw [smul_neg, hy.1], fun v => by
        convert neg_mem (hy.2 v) using 1
        exact funext fun i => map_neg _ _⟩
  · rintro ⟨h1, h2⟩
    let π := Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)
    let ι : Af F ⊗[F] E →ₗ[F] AE F E := TensorProduct.map (LinearMap.inr F (Ainf F) (Af F)) LinearMap.id
    have e1 : ∀ y, ι (π y) = eF F • y := fun y => by
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [map_add, smul_add, hx, hy]
      | tmul a x => exact congrArg (· ⊗ₜ[F] x) (Prod.ext (zero_mul _).symm (one_mul _).symm)
    have e2 : ∀ v y, Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E) (π y) = compFin F E v y := fun v y => by
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [map_add, hx, hy]
      | tmul a x => rfl
    have e3 : ∀ y ∈ Formalism.MainNotions.StandardLattice.latHat F E (Y.L : Set (Fin n → E)), ι ∘ y ∈ latHat Y := fun y hy => by
      induction hy using AddSubgroup.closure_induction with
      | mem y hy =>
        obtain ⟨a, ha, x, hx, rfl⟩ := hy
        exact AddSubgroup.subset_closure ⟨LinearMap.inr F (Ainf F) (Af F) a, map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F),
          ha, x, hx, funext fun i => (smul_incl _ _).symm⟩
      | zero =>
        convert zero_mem (latHat Y) using 1
        exact funext fun i => map_zero _
      | add y z _ _ hy hz =>
        convert add_mem hy hz using 1
        exact funext fun i => map_add _ _ _
      | neg y _ hy =>
        convert neg_mem hy using 1
        exact funext fun i => map_neg _ _
    convert e3 (π ∘ z) ((mem_latHat_iff hL _).2 fun v => by
      convert h2 v using 1
      exact funext fun i => e2 v _) using 1
    exact funext fun i => (congrFun h1 i).symm.trans (e1 _).symm

omit [NumberField E] in
theorem cA_eq : ⇑(cA (F := F) σ) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ := funext fun z => by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a x => rfl

def Keeps (k : G2 σ Y) : Prop := ∀ z z', z ∈ latHat Y → z' ∈ latHat Y →
  (mat2 k *ᵥ Sum.elim z z') ∘ Sum.inl ∈ latHat Y ∧ (mat2 k *ᵥ Sum.elim z z') ∘ Sum.inr ∈ latHat Y

theorem isUnit_of_cartan {M θ : Matrix (Fin n) (Fin n) ℂ} (h : IsCartan M θ) : IsUnit M := by
  refine Matrix.mulVec_injective_iff_isUnit.1 ((injective_iff_map_eq_zero M.mulVecLin).2 fun y hy => by_contra fun h0 => ?_)
  have := h.2.2 (star y) (by simpa using h0)
  rw [star_star, show M *ᵥ y = 0 from hy] at this
  simp at this

theorem det_ne {B : Base F E} {r s : ℕ} (hY : Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) : Y.J.det ≠ 0 := fun h0 => by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have e : (Y.J.map (B.emb w).1).det = 0 := by rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]
  rcases hY with h | h
  · exact ((Matrix.isUnit_iff_isUnit_det _).1 (isUnit_of_cartan (h.cartan w))).ne_zero e
  · exact ((Matrix.isUnit_iff_isUnit_det _).1 (isUnit_of_cartan (h.cartan w))).ne_zero (by rw [Matrix.det_smul, e, mul_zero])

omit [NumberField E] in
theorem comp_smul (v : Pl F) (a : AF F) (z : AE F E) : compFin F E v (a • z) = evFin F v a ⊗ₜ[F] 1 * compFin F E v z := by
  rw [Algebra.smul_def, map_mul]; rfl

omit [NumberField E] in
theorem comp_eF (v : Pl F) (z : AE F E) : compFin F E v (eF F • z) = compFin F E v z := by
  rw [comp_smul, show evFin F v (eF F) = 1 from map_one (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v)]
  exact one_mul _

theorem eF_sq : eF F * eF F = eF F := Prod.ext (zero_mul _) (one_mul _)

theorem mem_intHat (z : AE F E) : eF F • z ∈ intHat F E ↔ ∀ v, compFin F E v z ∈ intLoc F E v := by
  constructor
  · intro h v
    rw [← comp_eF]
    generalize eF F • z = y at h
    induction h using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, -, ha, o, rfl⟩ := hy
      rw [smul_incl]
      exact tmul_mem_intLoc (ha v) o
    | zero => rw [map_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
    | neg y _ hy => rw [map_neg]; exact neg_mem hy
  · intro h
    let X : Spc F E 1 := ⟨1, stdLattice E 1, fun _ => 1, fun _ => 1⟩
    have key : ∀ y ∈ latHat X, y 0 ∈ intHat F E := fun y hy => by
      induction hy using AddSubgroup.closure_induction with
      | mem y hy =>
        obtain ⟨a, h1, h2, x, hx, rfl⟩ := hy
        obtain ⟨o, ho⟩ := hx 0 trivial
        exact AddSubgroup.subset_closure ⟨a, h1, h2, o, congrArg (fun t => a • inclR (F := F) (AF F) t) ho.symm⟩
      | zero => exact zero_mem _
      | add y z _ _ hy hz => exact add_mem hy hz
      | neg y _ hy => exact neg_mem hy
    refine key (fun _ => eF F • z) ((mem_latHat (Submodule.fg_pi fun _ => ?_) _).2 ⟨funext fun _ => ?_, fun v => ?_⟩)
    · exact Submodule.fg_range _
    · change eF F • eF F • z = _
      rw [smul_smul, eF_sq]
    · refine mem_latLoc_stdLattice.2 fun _ => ?_
      rw [Function.comp_apply, comp_eF]
      exact h v

theorem keeps_iff (hL : Y.L.FG) {a : GL (Fin n) (AE F E)} (ha : IsLatticeFrame Y.L a) (x : G2 σ Y) :
    Keeps x ↔ ∀ v, Int (intLoc F E v) (bc (compFin F E v) ((two a)⁻¹ * x.1 * two a)).1 := by
  let P : (Fin n ⊕ Fin n → AE F E) → Prop := fun u => eF F • u = u ∧ ∀ v i, compFin F E v ((((two a)⁻¹).1 *ᵥ u) i) ∈ intLoc F E v
  have h1 : ∀ z, z ∈ latHat Y ↔ eF F • z = z ∧ ∀ v i, compFin F E v (((a⁻¹).1 *ᵥ z) i) ∈ intLoc F E v := fun z =>
    (mem_latHat hL z).trans (and_congr_right' (forall_congr' fun v => Iff.symm ((ha v _).trans (iff_of_eq (congrArg (· ∈ _) (funext fun i =>
      (RingHom.map_mulVec _ _ _ i).symm.trans (by rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]; rfl)))))))
  have h2 : ∀ u : Fin n ⊕ Fin n → AE F E, u ∘ Sum.inl ∈ latHat Y ∧ u ∘ Sum.inr ∈ latHat Y ↔ P u := fun u => by
    have e : ((two a)⁻¹).1 *ᵥ u = Sum.elim ((a⁻¹).1 *ᵥ (u ∘ Sum.inl)) ((a⁻¹).1 *ᵥ (u ∘ Sum.inr)) := by
      change Matrix.fromBlocks _ _ _ _ *ᵥ u = _
      rw [Matrix.fromBlocks_mulVec]; simp
    simp only [h1, P, e, funext_iff, Sum.forall, forall_and, Sum.elim_inl, Sum.elim_inr, Pi.smul_apply, Function.comp_apply]
    tauto
  have h3 : Keeps x ↔ ∀ u, P u → P (mat2 x *ᵥ u) :=
    ⟨fun h u hu => (h2 _).1 (by simpa only [Sum.elim_comp_inl_inr] using h _ _ ((h2 u).2 hu).1 ((h2 u).2 hu).2),
      fun h z z' hz hz' => (h2 _).2 (h _ ((h2 (Sum.elim z z')).1 ⟨hz, hz'⟩))⟩
  rw [h3]
  constructor
  · intro h v i j
    have := (h (eF F • (two a).1 *ᵥ Pi.single j 1) ⟨by rw [smul_smul, eF_sq], fun v i => ?_⟩).2 v i
    · rw [Matrix.mulVec_smul, Matrix.mulVec_smul, Pi.smul_apply, comp_eF, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
        Matrix.mulVec_single_one] at this
      exact this
    · rw [Matrix.mulVec_smul, Pi.smul_apply, comp_eF, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, Pi.single_apply]
      split_ifs
      · rw [map_one]; exact one_mem _
      · rw [map_zero]; exact zero_mem _
  · refine fun h u hu => ⟨by rw [← Matrix.mulVec_smul, hu.1], fun v i => ?_⟩
    have e : ((two a)⁻¹).1 *ᵥ mat2 x *ᵥ u = ((two a)⁻¹ * x.1 * two a).1 *ᵥ ((two a)⁻¹).1 *ᵥ u := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul _ (two a)⁻¹, mul_inv_cancel_right]; rfl
    rw [e, RingHom.map_mulVec]
    rw [Matrix.mulVec, dotProduct]
    exact Subring.sum_mem _ fun j _ => mul_mem (h v i j) (hu.2 v j)

end GlobalTheory.ThK.Dbl.Frame

namespace GlobalTheory.ThK.Dbl

open scoped Matrix TensorProduct
open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Doubling GlobalTheory.ThK.Dbl.Frame
open Formalism.UG (bc)

theorem frameConj : FrameConj := by
  intro F E _ _ _ _ _ σ B n Y r s hB hY K hK
  have hc := hB.cm
  have hσ := cm_conj_conj hc
  have hL : Y.L.IsLattice E := hY.elim (·.lat) (·.lat)
  have hJ := Frame.det_ne hY
  obtain ⟨ε, hε, c, c1, c2⟩ : ∃ ε : ℤˣ, (Y.J.map σ)ᵀ = ((ε : ℤ) : E) • Y.J ∧ ∃ c : ℂ, star c * c = 1 ∧
      ∀ w, (c • Y.J.map (B.emb w).1)ᴴ = c • Y.J.map (B.emb w).1 ∧ IsCartan (c • Y.J.map (B.emb w).1) (Y.θ w) := by
    rcases hY with h | h
    · refine ⟨1, Matrix.ext fun i j => by simpa using h.herm i j, 1, by simp, fun w => ?_⟩
      rw [one_smul]
      exact ⟨Matrix.ext fun i j => (hc.2.2.2 _ _).symm.trans (congrArg _ (h.herm i j)), h.cartan w⟩
    · refine ⟨-1, Matrix.ext fun i j => by simpa using h.skew i j, Complex.I, by simp, fun w => ⟨Matrix.ext fun i j => ?_, h.cartan w⟩⟩
      change star (Complex.I * (B.emb w).1 (Y.J j i)) = Complex.I * (B.emb w).1 (Y.J i j)
      rw [star_mul', ← hc.2.2.2, h.skew]; simp
  have ee : ∀ (S : Type) [CommRing S], ((ε : ℤ) : S) * (ε : ℤ) = 1 := fun S _ => by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]; simp
  choose gw hw using fun w => Frame.exists_arch c1 (c2 w).1 (Frame.isUnit_of_cartan (c2 w).2) (c2 w).2
  obtain ⟨a, g, ha, hg, hg'⟩ := exists_ad hB hY hJ gw
  obtain ⟨t, ht⟩ := GlobalTheory.exists_int_add_conj_eq_one_of_base_good B hB
  let ι := inclR (F := F) (E := E) (AF F)
  let cc : AE F E →+* AE F E := cA σ
  have hι : ∀ z, ι (σ z) = cc (ι z) := fun z => rfl
  have hcc : ∀ z, cc (cc z) = z := fun z => by
    change cA σ (cA σ z) = z
    rw [cA_eq]; exact sigR_invol hσ z
  have hf : ∀ v z, compFin F E v (cc z) = sigR _ σ (compFin F E v z) := fun v z => by
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul a x => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  have hi : ∀ w z, piInf (B.emb w) (cc z) = star (piInf (B.emb w) z) := fun w z => by
    refine Eq.trans (congrArg (infEmb (B.emb w)) ?_) (infEmb_sigR hc (B.emb w) (compInf F E w z)).symm
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul a x => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  have jf : ∀ v, (incM F Y.J).map (compFin F E v) = Y.J.map (inclR (F := F) (Fv F v)) := fun v =>
    Matrix.ext fun i j => congrArg (· ⊗ₜ[F] Y.J i j) (map_one (evFin F v))
  have ii : ∀ w z, piInf (B.emb w) (ι z) = (B.emb w).1 z := fun w z => by
    change InfinitePlace.Completion.extensionEmbedding w 1 * (B.emb w).1 z = _
    rw [map_one, one_mul]
  have ji : ∀ w, (incM F Y.J).map (piInf (B.emb w)) = Y.J.map (B.emb w).1 := fun w => Matrix.ext fun i j => ii w _
  have h2 : (2⁻¹ : E) + σ 2⁻¹ = 1 := by rw [map_inv₀, map_ofNat]; norm_num
  let α : AE F E := ι 2⁻¹ + eF F • ι (t - 2⁻¹)
  have α0 : α + cc α = 1 := by
    have : cc α = ι (σ 2⁻¹) + eF F • ι (σ (t - 2⁻¹)) := by
      rw [hι, hι, map_add]; exact congrArg _ (map_smul (cA σ) _ _)
    rw [this, add_add_add_comm, ← smul_add, ← map_add, ← map_add, h2, map_sub σ, sub_add_sub_comm, ht, h2, sub_self]
    simp
  have α1 : ∀ v, compFin F E v α ∈ intLoc F E v := fun v => by
    rw [map_add, comp_eF, ← map_add, ← map_add, add_sub_cancel]
    exact tmul_mem_intLoc (a := evFin F v 1) (by rw [map_one]; exact one_mem _) t
  have α2 : ∀ w, piInf (B.emb w) α = 2⁻¹ := fun w => by
    have : piInf (B.emb w) (algebraMap (AF F) (AE F E) (eF F)) = 0 := by
      change InfinitePlace.Completion.extensionEmbedding w 0 * (B.emb w).1 1 = _
      rw [map_zero, zero_mul]
    rw [map_add, Algebra.smul_def, map_mul, this, zero_mul, add_zero, ii, map_inv₀, map_ofNat]
  have uJ : IsUnit Y.J := (Matrix.isUnit_iff_isUnit_det _).2 hJ.isUnit
  obtain ⟨T₀, hT₀⟩ := exists_dual (σ : E →+* E) hσ uJ 1
  obtain ⟨T, hT⟩ := exists_dual cc hcc (J := incM F Y.J) (uJ.map ι.mapMatrix) g
  have g0 := frame_gram (σ : E →+* E) hσ (ee E) h2 hε 1 T₀ hT₀
  have g1 := frame_gram cc hcc (ee _) α0 (J := incM F Y.J) (Matrix.ext fun i j => by
    have := congrArg ι (congrFun (congrFun hε i) j)
    rw [Matrix.smul_apply, smul_eq_mul, map_mul, map_intCast] at this
    exact this) g T hT
  have d0 := frame_diag 1 T₀ (2⁻¹ : E)
  set b := two 1 * wit (2⁻¹ : E) T₀
  have d1 := frame_diag g T α
  set b' := two g * wit α T with hb'
  have g2 : (bc ι b).1ᵀ * dbl (incM F Y.J) * (bc ι b).1.map cc = b'.1ᵀ * dbl (incM F Y.J) * b'.1.map cc := by
    have := (map_gram ι hι b.1 (dbl Y.J)).symm.trans (congrArg (·.map ι) g0)
    rw [map_dbl] at this
    rw [g1]
    refine this.trans ?_
    ext (i | i) (j | j) <;> simp [Matrix.one_apply, apply_ite ι]
  let p : G2 σ Y := ⟨b' * (bc ι b)⁻¹, by
    change (b'.1 * ((bc ι b)⁻¹).1)ᵀ * _ * (b'.1 * ((bc ι b)⁻¹).1).map cc = _
    calc _ = ((bc ι b)⁻¹).1ᵀ * (b'.1ᵀ * dbl (incM F Y.J) * b'.1.map cc) * ((bc ι b)⁻¹).1.map cc := by
          simp only [Matrix.transpose_mul, Matrix.map_mul, Matrix.mul_assoc]
      _ = ((bc ι b).1 * ((bc ι b)⁻¹).1)ᵀ * dbl (incM F Y.J) * ((bc ι b).1 * ((bc ι b)⁻¹).1).map cc := by
          simp only [← g2, Matrix.transpose_mul, Matrix.map_mul, Matrix.mul_assoc]
      _ = _ := by rw [Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]⟩
  have fr : ∀ k : G2 σ Y, inFrame b k = (b'⁻¹ * (p * k * p⁻¹).1 * b').1 := fun k => by
    rw [show b'⁻¹ * (p * k * p⁻¹).1 * b' = bc ι b⁻¹ * k.1 * bc ι b by
      change b'⁻¹ * (b' * (bc ι b)⁻¹ * k.1 * (b' * (bc ι b)⁻¹)⁻¹) * b' = _
      rw [map_inv]; group]
    rfl
  have fin : ∀ k : G2 σ Y, Keeps (p * k * p⁻¹) ↔ ∀ i j, eF F • inFrame b k i j ∈ intHat F E := fun k => by
    simp only [keeps_iff hL.fg ha, mem_intHat, fr]
    refine (forall_congr' fun v => ?_).trans (forall_comm.trans (forall_congr' fun i => forall_comm))
    obtain ⟨⟨l, hl⟩, u1, G', u2, u3⟩ := hg v
    obtain ⟨q1, q2⟩ := int_dual (T := bc (compFin F E v) T) (sigR_invol hσ) (fun z => sigR_mem_intLoc σ) u1 u2 u3 (by
      have := congrArg (·.map (compFin F E v)) hT
      simp only [Matrix.map_mul (M := T.1.map cc), map_gram _ (hf v), jf, Matrix.map_one _ (map_zero _) (map_one _)] at this
      rw [← this]
      congr 1
      exact Matrix.ext fun i j => (hf v _).symm)
    obtain ⟨q3, q4⟩ := int_wit (α1 v) q1 q2
    have := int_conj hl q3 q4 (bc (compFin F E v) (p * k * p⁻¹).1)
    simp only [← bc_wit, ← bc_two, ← map_mul (bc (compFin F E v)), ← map_inv (bc (compFin F E v))] at this
    exact this
  refine ⟨b, K.comap (MulAut.conj p).toMonoidHom, p, g, ⟨⟨ε, g0⟩, 1, ?_⟩, fun k => ?_, ?_, fun k => ?_⟩
  · rw [← d0, ← Matrix.fromCols_toCols b.1, Matrix.fromCols_mul_fromRows]; simp
  · refine (hK (p * k * p⁻¹)).trans (and_congr (forall_congr' fun w => ?_) ?_)
    · have := hw w (bc (piInf (B.emb w)) T) (by
        have := congrArg (·.map (piInf (B.emb w))) hT
        simp only [Matrix.map_mul (M := T.1.map cc), map_gram _ (hi w), ji, Matrix.map_one _ (map_zero _) (map_one _)] at this
        rw [← this, ← hg']
        congr 1
        exact Matrix.ext fun i j => (hi w _).symm) (bc (piInf (B.emb w)) (p * k * p⁻¹).1) (by
        have := (map_gram _ (hi w) _ _).symm.trans (congrArg (·.map (piInf (B.emb w))) (show _ = _ from (p * k * p⁻¹).2))
        simp only [map_dbl, ji] at this
        exact this)
      rw [← hg', ← α2 w, ← bc_wit, ← bc_two, ← map_mul, ← map_inv, ← map_mul, ← map_mul] at this
      rw [fr]
      exact this.symm
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq, forall_and]
      refine Iff.trans ?_ (and_congr (fin k) (fin k⁻¹))
      rw [show p * k⁻¹ * p⁻¹ = (p * k * p⁻¹)⁻¹ by group]
      simp only [Keeps, forall_and]
      exact and_and_and_comm
  · exact par_of ι (d0.trans (Matrix.mul_one _)) d1
  · change _ ↔ p * (p⁻¹ * k * p) * p⁻¹ ∈ K
    rw [show p * (p⁻¹ * k * p) * p⁻¹ = k by group]

end GlobalTheory.ThK.Dbl

end
