import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LabesseWaldspurger
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConstantTermVanishing
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointRadical
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspidalNoRadicalFixed
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AbsAUnit
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviMonotoneInParabolic
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
open GlobalTheory.LeviShift

noncomputable section
open scoped TensorProduct Classical

namespace GlobalTheory.LeviVec

open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (perp extSub coordR act parab)
open GlobalTheory.LeviSign

section Comb

variable {k : ℕ}

def res (u : SV k) (A : Fin k → Prop) : SV k := fun i => if A i then u i else 0

theorem vec_res_add (u : SV k) (A : Fin k → Prop) : vec u = vec (res u A) + vec (res u fun i => ¬ A i) := by
  ext i
  by_cases h : A i <;> simp [vec, res, h]

theorem res_mem {P : Finset (SV k)} (hP : IsPar P) {w : SV k} (hw : w ∈ P) {u : SV k} (hu : vec u ∈ aP P) :
    vec (res u fun i => w i ≠ 0) ∈ aP P := by
  let a : A0 k →ₗ[ℝ] A0 k :=
    { toFun := fun x => WithLp.toLp 2 fun i => if w i ≠ 0 then x i else 0
      map_add' := fun x y => by ext i; by_cases h : w i = 0 <;> simp [h]
      map_smul' := fun c x => by ext i; by_cases h : w i = 0 <;> simp [h] }
  have ha : ∀ v : SV k, a (vec v) = vec (res v fun i => w i ≠ 0) := fun v => by
    ext i; by_cases h : w i = 0 <;> simp [a, vec, res, h]
  have hle : aP P ≤ (aP P).comap a := Submodule.span_le.2 (by
    rintro _ ⟨v, hv, rfl⟩
    change a (vec v) ∈ aP P
    rw [ha]
    rcases hP.2 v hv w hw with e | e
    · have : (res v fun i => w i ≠ 0) = v := funext fun i => by
        by_cases h : w i = 0
        · by_cases h' : v i = 0
          · simp [res, h']
          · exact absurd ((e i h').symm.trans h) h'
        · simp [res, h]
      rw [this]; exact Submodule.subset_span ⟨v, hv, rfl⟩
    · have : (res v fun i => w i ≠ 0) = w := funext fun i => by
        by_cases h : w i = 0
        · simp [res, h]
        · simp [res, h, e i h]
      rw [this]; exact Submodule.subset_span ⟨w, hw, rfl⟩)
  exact ha u ▸ hle hu

theorem signType_cancel_identity : ∀ a b c d : SignType, a ≠ 0 → c ≠ 0 → a * b = c * d → d = (b * a) * c := by decide

theorem sign_sq : ∀ a : SignType, a ≠ 0 → a * a = 1 := by decide

theorem sign_mul_ne : ∀ a b : SignType, a ≠ 0 → b ≠ 0 → a * b ≠ 0 := by decide

theorem exists_vec {P : Finset (SV k)} (hP : IsPar P) (l : SV k → ℝ)
    (hneg : ∀ u, vec u ∈ aP P → l (-u) = - l u)
    (hadd : ∀ u A, vec u ∈ aP P → vec (res u A) ∈ aP P → vec (res u fun i => ¬ A i) ∈ aP P →
      l u = l (res u A) + l (res u fun i => ¬ A i)) :
    ∃ h : A0 k, ∀ u, vec u ∈ aP P → inner ℝ (vec u) h = l u := by
  obtain ⟨p, -, hp⟩ := exists_top (r := Below) (fun a b c h h' i hi => (h' i (h i hi ▸ hi)).trans (h i hi))
    (insert 0 P) (Finset.insert_nonempty _ _) fun a ha b hb => by
      rcases Finset.mem_insert.1 ha with rfl | ha
      · exact .inl fun i hi => (hi rfl).elim
      rcases Finset.mem_insert.1 hb with rfl | hb
      · exact .inr fun i hi => (hi rfl).elim
      exact hP.2 a ha b hb
  have hp' : ∀ w ∈ P, ∀ i, w i ≠ 0 → p i = w i := fun w hw => hp w (Finset.mem_insert_of_mem hw)
  let c : Fin k → Finset (SV k) := fun i => P.filter fun w => w i ≠ 0
  let b : Finset (SV k) → SV k := fun C => res p fun i => c i = C
  let N : Finset (SV k) → ℝ := fun C => (Finset.univ.filter fun i => c i = C).card
  let h : A0 k := WithLp.toLp 2 fun i => (p i : ℝ) * (l (b (c i)) / N (c i))
  have hc : ∀ i j, c i = c j ↔ ∀ w ∈ P, (w i ≠ 0 ↔ w j ≠ 0) := fun i j => by
    simp only [c, Finset.ext_iff, Finset.mem_filter, and_congr_right_iff]
  have main : ∀ Q : Finset (SV k), Q ⊆ P → ∀ u, vec u ∈ aP P →
      (∀ i j, u i ≠ 0 → u j ≠ 0 → ∀ w ∈ P, w ∉ Q → (w i ≠ 0 ↔ w j ≠ 0)) → inner ℝ (vec u) h = l u := by
    intro Q
    induction Q using Finset.induction_on with
    | empty =>
      intro _ u hu H
      by_cases h0 : u = 0
      · subst h0
        have e0 : vec (0 : SV k) = 0 := by ext i; simp [vec]
        have := hneg 0 hu
        rw [neg_zero] at this
        rw [e0, inner_zero_left]; linarith
      obtain ⟨i, hi⟩ := Function.ne_iff.1 h0
      have hi : u i ≠ 0 := hi
      obtain ⟨w, hw, hwi⟩ : ∃ w ∈ P, w i ≠ 0 := by
        by_contra! hn
        have := pattern hu (s := 1) (t := 0) (i := i) (j := i) fun w hw => by simp [hn w hw]
        exact hi (by simpa using this)
      have hpj : ∀ j, c j = c i → p j ≠ 0 := fun j hj => by
        have := ((hc j i).1 hj w hw).2 hwi
        rwa [hp' w hw j this]
      have hu' : ∀ j, u j = (u i * p i) * b (c i) j := fun j => by
        by_cases hj : c j = c i
        · have := pattern hu (s := p i) (t := p j) (i := i) (j := j) fun v hv => by
            by_cases hv' : v i = 0
            · have : v j = 0 := by
                by_contra e; exact ((hc j i).1 hj v hv).1 e hv'
              rw [hv', this, mul_zero, mul_zero]
            · have hv'' := ((hc j i).1 hj v hv).2 hv'
              rw [hp' v hv i hv', hp' v hv j hv'', sign_sq _ hv', sign_sq _ hv'']
          simp only [b, res, if_pos hj]
          exact signType_cancel_identity _ _ _ _ (hpj i rfl) (hpj j hj) this
        · simp only [b, res, if_neg hj, mul_zero]
          by_contra e
          exact hj ((hc j i).2 fun v hv => H j i e hi v hv (Finset.notMem_empty v))
      have hb : inner ℝ (vec (b (c i))) h = l (b (c i)) := by
        have hN : N (c i) ≠ 0 := Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 ⟨i, by simp⟩)
        have : ∀ j, inner ℝ (vec (b (c i)) j) (h j) = if c j = c i then l (b (c i)) / N (c i) else 0 := fun j => by
          by_cases hj : c j = c i
          · have : ((p j : ℝ)) * p j = 1 := by rw [← SignType.coe_mul, sign_sq _ (hpj j hj), SignType.coe_one]
            simp only [vec, b, res, h, if_pos hj, hj, if_true, RCLike.inner_apply, conj_trivial]
            linear_combination (l (b (c i)) / N (c i)) * this
          · simp [vec, b, res, hj]
        rw [PiLp.inner_apply, Finset.sum_congr rfl fun j _ => this j, ← Finset.sum_filter, Finset.sum_const,
          nsmul_eq_mul]
        exact mul_div_cancel₀ _ hN
      rcases sign_cases _ (sign_mul_ne _ _ hi (hpj i rfl)) with e | e
      · have : b (c i) = u := funext fun j => by rw [hu' j, e, one_mul]
        rwa [this] at hb
      · have : b (c i) = -u := funext fun j => by rw [Pi.neg_apply, hu' j, e, neg_one_mul, neg_neg]
        rw [this, vec_neg, inner_neg_left, hneg u hu] at hb
        linarith
    | insert w Q hwQ ih =>
      intro hQ u hu H
      have hw : w ∈ P := hQ (Finset.mem_insert_self _ _)
      have hQ' : Q ⊆ P := (Finset.subset_insert _ _).trans hQ
      have h1 := res_mem hP hw hu
      have h2 : vec (res u fun i => ¬ w i ≠ 0) ∈ aP P := by
        rw [eq_sub_of_add_eq' (vec_res_add u fun i => w i ≠ 0).symm]; exact sub_mem hu h1
      have key : ∀ A : Fin k → Prop, vec (res u A) ∈ aP P → (∀ i j, A i → A j → (w i ≠ 0 ↔ w j ≠ 0)) →
          inner ℝ (vec (res u A)) h = l (res u A) := fun A hA hA' => ih hQ' _ hA fun i j hi hj v hv hvQ => by
        have r : ∀ i, res u A i ≠ 0 → A i ∧ u i ≠ 0 := fun i hi => by
          by_cases e : A i <;> simp_all [res]
        by_cases e : v = w
        · subst e; exact hA' i j (r i hi).1 (r j hj).1
        · exact H i j (r i hi).2 (r j hj).2 v hv (by simp [e, hvQ])
      rw [hadd u _ hu h1 h2, ← key _ h1 fun i j a b => iff_of_true a b, ← key _ h2 fun i j a b => iff_of_false a b,
        ← inner_add_left, ← vec_res_add]
  exact ⟨h, fun u hu => main P subset_rfl u hu fun i j _ _ w hw hn => (hn hw).elim⟩

end Comb

section Det

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  {hc : CMData F E} {V : HSpace E} (Φ : WittFrame V) {R : Type} [CommRing R] [Algebra F R]

theorem bas_eq {u : SV (wittIndex V)} {i : Fin (wittIndex V)} (hi : u i ≠ 0) : bas Φ u i = vecOf Φ (u i) i := by
  rcases sign_cases _ hi with e | e <;> simp [bas, vecOf, e]

theorem dbas_eq {u : SV (wittIndex V)} {i : Fin (wittIndex V)} (hi : u i ≠ 0) : dbas Φ u i = dualOf Φ (u i) i := by
  rcases sign_cases _ hi with e | e <;> simp [dbas, dualOf, e]

theorem bas_neg {u : SV (wittIndex V)} {i : Fin (wittIndex V)} (hi : u i ≠ 0) : bas Φ (-u) i = dbas Φ u i := by
  rcases sign_cases _ hi with e | e <;> simp [bas, dbas, e]

theorem dbas_neg {u : SV (wittIndex V)} {i : Fin (wittIndex V)} (hi : u i ≠ 0) : dbas Φ (-u) i = bas Φ u i := by
  rcases sign_cases _ hi with e | e <;> simp [bas, dbas, e]

theorem bas_mem {u : SV (wittIndex V)} {i : Fin (wittIndex V)} (hi : u i ≠ 0) : bas Φ u i ∈ Φ.sub u := by
  rw [bas_eq Φ hi]; exact vecOf_mem (x := (u i, i)) (mem_Aset.2 (sign_sq _ hi))

theorem cf_bas (u : SV (wittIndex V)) (i j : Supp u) :
    cf hc R (dbas Φ u i) (coordR V R (bas Φ u j)) = if i = j then 1 else 0 := by
  rw [cf_coordR, bas_eq Φ j.2, dbas_eq Φ i.2, hD_vecOf_dualOf Φ j.2 i.2]
  by_cases h : i = j
  · subst h; simp
  · rw [if_neg h, if_neg, map_zero]
    exact fun e => h (Subtype.ext (congrArg Prod.snd e).symm)

theorem expand (u : SV (wittIndex V)) {y : Fin V.rank → R ⊗[F] E} (hy : y ∈ extSub V R (Φ.sub u)) :
    y = ∑ l : Supp u, cf hc R (dbas Φ u l) y • coordR V R (bas Φ u l) := by
  let T : Module.End (R ⊗[F] E) (Fin V.rank → R ⊗[F] E) :=
    ∑ l : Supp u, (cf hc R (dbas Φ u l)).smulRight (coordR V R (bas Φ u l))
  have hT : ∀ y, T y = ∑ l : Supp u, cf hc R (dbas Φ u l) y • coordR V R (bas Φ u l) := fun y => by
    simp only [T, LinearMap.sum_apply, LinearMap.smulRight_apply]
  have hb : ∀ j : Supp u, coordR V R (bas Φ u j) ∈ LinearMap.ker (T - LinearMap.id) := fun j => by
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero, hT]
    simp [cf_bas]
  have hle : extSub (F := F) V R (Φ.sub u) ≤ LinearMap.ker (T - LinearMap.id) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨v, hv, rfl⟩
    refine span_coord R _ _ (fun v hv => ?_) hv
    rcases hv with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩
    · have hi' : u i = 1 := hi
      have := hb ⟨i, by rw [hi']; decide⟩
      simpa [bas, hi'] using this
    · have hi' : u i = -1 := hi
      have := hb ⟨i, by rw [hi']; decide⟩
      simpa [bas, hi'] using this
  have := hle hy
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero, hT] at this
  exact this.symm

theorem hR_swap (x y : Fin V.rank → R ⊗[F] E) :
    hR R hc.sig V.gram x y = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R hc.sig (hR R hc.sig V.gram y x) := by
  have hs : ∀ z, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R hc.sig (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R hc.sig z) = z := fun z => by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul a e =>
      change a ⊗ₜ[F] star (star e) = _
      rw [star_star]
  have hg : ∀ i j, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R hc.sig (inclR (F := F) R (V.gram i j)) = inclR (F := F) R (V.gram j i) :=
    fun i j => congrArg (inclR (F := F) R) (congrFun (congrFun (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.cT_gram hc V) j) i)
  simp only [GlobalTheory.Cusp.hR_eq, dotProduct, Matrix.mulVec, Matrix.map_apply, Finset.mul_sum, map_sum, map_mul, hs, hg]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem detU_neg (u : SV (wittIndex V)) {g : HA R hc.sig V.gram} (hg : g ∈ parab hc V R (Φ.sub u)) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R hc.sig (detU Φ hc R (-u) g) * detU Φ hc R u g = 1 := by
  let e : Supp u ≃ Supp (-u) := Equiv.subtypeEquivRight fun i => by simp
  let N := (detMat Φ hc R (-u) g).submatrix e e
  have h : (N.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R hc.sig)).transpose * detMat Φ hc R u g = 1 := by
    ext i j
    have h1 := cf_bas (hc := hc) (R := R) Φ u i j
    rw [cf_apply, ← hR_act hc V g, expand (hc := hc) Φ u (mem_parab.1 hg _ (bas_mem Φ j.2))] at h1
    rw [Matrix.one_apply, ← h1, Matrix.mul_apply]
    let ψ : (Fin V.rank → R ⊗[F] E) →ₗ[R ⊗[F] E] R ⊗[F] E :=
      { toFun := fun y => hLin hc.sig V.gram R y (act hc V g (coordR V R (dbas Φ u i)))
        map_add' := fun y y' => hLin_add_left _ _ _ y y' _
        map_smul' := fun c y => hLin_smul_left _ _ _ c y _ }
    change _ = ψ _
    rw [map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_smul, smul_eq_mul, mul_comm]
    congr 1
    change Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R hc.sig (hR R hc.sig V.gram (coordR V R (dbas Φ (-u) l))
      (act hc V g (coordR V R (bas Φ (-u) i)))) = hR R hc.sig V.gram _ _
    rw [dbas_neg Φ l.2, bas_neg Φ i.2, ← hR_swap]
  have := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_one, Matrix.det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
    Matrix.det_submatrix_equiv_self] at this
  exact this

theorem det_block (u : SV (wittIndex V)) (A : Fin (wittIndex V) → Prop) (g : HA R hc.sig V.gram) :
    ((detMat Φ hc R u g).toSquareBlockProp fun i => A i).det = detU Φ hc R (res u A) g := by
  have r : ∀ i, res u A i ≠ 0 → A i ∧ u i ≠ 0 := fun i hi => by
    by_cases e : A i <;> simp_all [res]
  let e : Supp (res u A) ≃ {i : Supp u // A i} :=
    { toFun := fun i => ⟨⟨i.1, (r i.1 i.2).2⟩, (r i.1 i.2).1⟩
      invFun := fun i => ⟨i.1.1, by simpa [res, i.2] using i.1.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← Matrix.det_submatrix_equiv_self e, detU]
  congr 1
  ext i j
  have hi : res u A i = u i := if_pos (r i.1 i.2).1
  have hj : res u A j = u j := if_pos (r j.1 j.2).1
  simp only [detMat, Matrix.toSquareBlockProp, Matrix.toBlock, Matrix.submatrix_apply, Matrix.of_apply, bas, dbas, hi, hj]
  rfl

theorem detU_res (u : SV (wittIndex V)) (A : Fin (wittIndex V) → Prop) {g : HA R hc.sig V.gram}
    (hg : g ∈ parab hc V R (Φ.sub (res u A))) :
    detU Φ hc R u g = detU Φ hc R (res u A) g * detU Φ hc R (res u fun i => ¬ A i) g := by
  rw [← det_block, ← det_block, detU]
  convert Matrix.twoBlockTriangular_det (detMat Φ hc R u g) (fun i => A i) fun i hi j hj => ?_
  have hj' : res u A j = u j := if_pos hj
  have hb : bas Φ u j ∈ Φ.sub (res u A) := by
    have := bas_mem Φ (u := res u A) (i := j) (hj' ▸ j.2)
    simpa only [bas, hj'] using this
  change cf hc R (dbas Φ u i) (act hc V g (coordR V R (bas Φ u j))) = 0
  rw [expand (hc := hc) Φ _ (mem_parab.1 hg _ hb), map_sum]
  refine Finset.sum_eq_zero fun l _ => ?_
  have hl : A l := by by_contra e; exact l.2 (if_neg e)
  rw [map_smul, cf_coordR, bas_eq Φ l.2, dbas_eq Φ i.2, hD_vecOf_dualOf Φ l.2 i.2, if_neg, map_zero, smul_zero]
  intro e
  have e' : l.1 = i.1 := congrArg Prod.snd e
  exact hi (e' ▸ hl)

end Det

variable {D : D7} {V : HSp D} (Φ : WittFrame V)

theorem absA_neg (u : SV (wittIndex V)) {g : GA D V} (hg : g ∈ parab D.sp.cm V (AF D.host.F) (Φ.sub u)) :
    absA D.host.F D.host.E (detU Φ D.sp.cm (AF D.host.F) (-u) g) *
      absA D.host.F D.host.E (detU Φ D.sp.cm (AF D.host.F) u g) = 1 := by
  have h := detU_neg Φ u hg
  set a := detU Φ D.sp.cm (AF D.host.F) (-u) g
  set b := detU Φ D.sp.cm (AF D.host.F) u g
  have hs : ∀ z, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig z) = z :=
    fun z => by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul a e =>
      change a ⊗ₜ[D.host.F] star (star e) = _
      rw [star_star]
  have ha : IsUnit a := by
    have := (IsUnit.of_mul_eq_one _ h).map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig)
    rwa [hs] at this
  obtain ⟨a', ha'⟩ := ha
  have e : absA D.host.F D.host.E (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig a) = absA D.host.F D.host.E a := by
    rw [← ha', absA_unit, ← Doubling.absE_conjUnit D.sp.cm.sig, ← absA_unit]; rfl
  rw [← e, ← absA_mul, h]
  exact (absA_unit 1).trans (map_one _)

theorem exists_levi_vec : ∀ (D : D7) (V : HSp D) (Φ : WittFrame V) (P : Finset (SV (wittIndex V))), IsPar P → ∀ m ∈ Φ.levi D.sp.cm (AF D.host.F) P, ∃ h : A0 (wittIndex V), ∀ u, vec u ∈ aP P → inner ℝ (vec u) h = - logDelta Φ u m := by
  intro D V Φ P hP m hm
  have hm' : ∀ u, vec u ∈ aP P → m ∈ parab D.sp.cm V (AF D.host.F) (Φ.sub u) := fun u hu =>
    (Subgroup.mem_inf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (levi_le Φ _ P u hu hm) u)
      (Finset.mem_singleton_self u))).1
  have hne : ∀ u, vec u ∈ aP P → (absA D.host.F D.host.E (detU Φ D.sp.cm (AF D.host.F) u m) : ℝ) ≠ 0 := fun u hu =>
    NNReal.coe_ne_zero.2 (right_ne_zero_of_mul_eq_one (absA_neg Φ u (hm' u hu)))
  refine exists_vec hP (fun u => - logDelta Φ u m) (fun u hu => ?_) fun u A hu h1 h2 => ?_
  · have h := congrArg NNReal.toReal (absA_neg Φ u (hm' u hu))
    rw [NNReal.coe_mul, NNReal.coe_one] at h
    simp only [logDelta]
    rw [eq_inv_of_mul_eq_one_left h, Real.log_inv]
  · simp only [logDelta]
    rw [detU_res Φ u A (hm' _ h1), absA_mul, NNReal.coe_mul, Real.log_mul (hne _ h1) (hne _ h2), neg_add]

end GlobalTheory.LeviVec

end
