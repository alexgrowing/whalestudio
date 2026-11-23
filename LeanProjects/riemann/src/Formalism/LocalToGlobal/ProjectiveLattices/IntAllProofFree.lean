import Formalism.LocalToGlobal.ProjectiveLattices.CoreProofs
import Formalism.LocalToGlobal.ProjectiveLattices.IntAllFree
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsOfValILeOne

noncomputable section

namespace Formalism.L2.PjFree

open Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open scoped WithZero
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

section Dvr

variable {V K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K'] [Algebra V K']
  [IsFractionRing V K']

theorem mem_range_of_vV_nonneg {x : K'} (h : 0 ≤ vV V x) : x ∈ Set.range (algebraMap V K') := by
  by_cases hx : x = 0
  · exact ⟨0, by simp [hx]⟩
  have hv0 : HeightOneSpectrum.valuation K' (IsDiscreteValuationRing.maximalIdeal V) x ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr hx
  have hle : HeightOneSpectrum.valuation K' (IsDiscreteValuationRing.maximalIdeal V) x ≤ 1 := by
    rw [← WithZero.exp_log hv0, ← WithZero.exp_zero, WithZero.exp_le_exp]
    unfold vV valV at h
    linarith
  have key : ∀ w : HeightOneSpectrum V, w.valuation K' x ≤ 1 := by
    intro w
    have hw : w = IsDiscreteValuationRing.maximalIdeal V :=
      HeightOneSpectrum.ext (IsLocalRing.eq_maximalIdeal w.isMaximal)
    rw [hw]
    exact hle
  obtain ⟨y, hy⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := V) (K := K') x key
  exact ⟨y, hy⟩

end Dvr

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

section Open

variable (Xo : Moduli Dw l) (c : Coeff l)

def FrBaseChg : Prop :=
  ∀ (S S' : Type) [Field S] [Field S'] [Algebra c.F S] [Algebra c.F S'] (φ : S →ₐ[c.F] S') (y : FrPt Xo c S),
    ∃ z : FrPt Xo c S', FrMap φ y z

def ReFrame : Prop :=
  ∀ (T : CDVR) (io : c.F →+* T.Fr), letI := io.toAlgebra
    ∀ (y0 : IntFr Xo c T io) (z : FrPt Xo c T.Fr), z.x = y0.1.x →
      ∃ (t : Ix Dw → T.Frˣ) (y' : IntFr Xo c T io), FrBor t z y'.1

def XoNumPt : Prop :=
  ∃ (L : Type) (_ : Field L) (_ : NumberField L) (j : c.F →+* L) (x : Sp L ⟶ Xo.X),
    (letI := j.toAlgebra; x ≫ Xo.s = sOf c L)

end Open

def LocFld : Prop :=
  ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] (j : K →+* L) (la : HeightOneSpectrum (𝓞 K)),
    ∃ (T : CDVR) (k : L →+* T.Fr) (e : ℕ), OverLa la T.V (k.comp j) e ∧ T.FinRes

section Proofs

variable {Xo : Moduli Dw l} {c : Coeff l}

private lemma vV_alg_nonneg_lemma {V K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K']
    [Algebra V K'] [IsFractionRing V K'] (a : V) : 0 ≤ vV V (algebraMap V K' a) := by
  unfold vV valV
  by_cases ha : HeightOneSpectrum.valuation K' (IsDiscreteValuationRing.maximalIdeal V) (algebraMap V K' a) = 0
  · simp [ha]
  · have h1 : HeightOneSpectrum.valuation K' (IsDiscreteValuationRing.maximalIdeal V) (algebraMap V K' a) ≤ 1 := by
      first
        | exact HeightOneSpectrum.valuation_le_one _ a
        | exact (IsDiscreteValuationRing.maximalIdeal V).valuation_le_one a
        | exact HeightOneSpectrum.valuation_le_one (K := K') _ a
        | exact (IsDiscreteValuationRing.maximalIdeal V).valuation_le_one (K := K') a
    rw [← WithZero.exp_log ha, ← WithZero.exp_zero, WithZero.exp_le_exp] at h1
    linarith

theorem intAll_of (hE : IntFrExt Xo c) (hB : FrBaseChg Xo c) (hR : ReFrame Xo c) : IntAll Xo c := by
  intro la T io e hO hFin y
  letI := io.toAlgebra
  obtain ⟨T', i, r, hr, hv, hF', y0, hy0⟩ := hE T io hFin y.x y.x_over
  letI := (i.comp io).toAlgebra
  let φ : T.Fr →ₐ[c.F] T'.Fr := { i with commutes' := fun _ => rfl }
  obtain ⟨z, hz⟩ := hB T.Fr T'.Fr φ y
  obtain ⟨t, y', hy'⟩ := hR T' (i.comp io) y0 z (hz.1.trans hy0.symm)
  refine ⟨T', i.comp io, r * e, y', ?_, hF', φ, z, t, ?_, hz, hy'⟩
  · unfold OverLa at hO ⊢
    refine ⟨Nat.mul_pos hr hO.1, fun a => ?_⟩
    rw [RingHom.comp_apply, hv, hO.2 a]
    push_cast
    ring
  · intro a
    apply mem_range_of_vV_nonneg
    show 0 ≤ vV T'.V (i (algebraMap T.V T.Fr a))
    rw [hv]
    exact mul_nonneg (Nat.cast_nonneg r) (vV_alg_nonneg_lemma a)

theorem algPtLa_of (hN : XoNumPt Xo c) (hL : LocFld) : AlgPtLa Xo c := by
  intro la
  obtain ⟨L, _, _, j, x, hx⟩ := hN
  obtain ⟨T, k, e, hO, hF⟩ := hL c.F L j la
  refine ⟨T, k.comp j, e, hO, hF, spMap k ≫ x, ?_⟩
  have hx' : x ≫ Xo.s = spMap (j.comp (IntermediateField.inclusion c.le).toRingHom) := hx
  show (spMap k ≫ x) ≫ Xo.s = spMap ((k.comp j).comp (IntermediateField.inclusion c.le).toRingHom)
  rw [Category.assoc, hx']
  show Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  rfl

theorem intFrNe_of' (hN : XoNumPt Xo c) (hL : LocFld) (hE : IntFrExt Xo c) : IntFrNe Xo c (algCls Xo c) := by
  intro la
  obtain ⟨T, io, e, hO, hF, x, hx⟩ := algPtLa_of hN hL la
  obtain ⟨T', i, r, hr, hv, hF', y, hy⟩ := hE T io hF x hx
  refine ⟨T', i.comp io, r * e, ?_, y, ?_⟩
  · unfold OverLa at hO ⊢
    refine ⟨Nat.mul_pos hr hO.1, fun a => ?_⟩
    rw [RingHom.comp_apply, hv, hO.2 a]
    push_cast
    ring
  · unfold algCls IntFr.IsAlg
    exact hF'

end Proofs

section Frames

theorem isCombAt_unique {S : Type} [CommRing S] {Xo : Moduli Dw l} {x : Sp S ⟶ Xo.X} {m : ℕ}
    {v : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)} {a : Fin m → S}
    {w w' : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (h : IsCombAt x v a w) (h' : IsCombAt x v a w') : w = w' := by
  obtain ⟨u, hu, rfl⟩ := h
  obtain ⟨u', hu', rfl⟩ := h'
  have e : u = u' := funext fun i => Over.OverMorphism.ext ((hu i).trans (hu' i).symm)
  rw [e]

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  show Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  rfl

theorem epsMul_comp_alg {S : Type} [CommRing S] (a : S) :
    (epsMul a).comp (algebraMap S (DualNumber S)) = algebraMap S (DualNumber S) := by
  ext x <;> simp [epsMul]

def epsPt {S : Type} [CommRing S] {Xo : Moduli Dw l} {x : Sp S ⟶ Xo.X}
    {v : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (hv : IsTanAt x v) (a : S) : tEps x ⟶ Xo.univ.t.G :=
  Over.homMk (spMap (epsMul a) ≫ v) (by
    rw [Category.assoc, hv.1, ← Category.assoc, spMap_comp', epsMul_comp_alg]
    rfl)

theorem epsPt_left {S : Type} [CommRing S] {Xo : Moduli Dw l} {x : Sp S ⟶ Xo.X}
    {v : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (hv : IsTanAt x v) (a : S) :
    (epsPt hv a).left = spMap (epsMul a) ≫ v :=
  Over.homMk_left _ _

theorem isCombAt_exists {S : Type} [CommRing S] {Xo : Moduli Dw l} {x : Sp S ⟶ Xo.X} {m : ℕ}
    {v : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)} (hv : ∀ j, IsTanAt x (v j)) (a : Fin m → S) :
    ∃ w, IsCombAt x v a w :=
  ⟨_, fun i => epsPt (hv i) (a i), fun i => epsPt_left (hv i) (a i), rfl⟩

theorem isCombAt_epsPt {S : Type} [CommRing S] {Xo : Moduli Dw l} {x : Sp S ⟶ Xo.X} {m : ℕ}
    {v : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)} (hv : ∀ j, IsTanAt x (v j)) (a : Fin m → S) :
    IsCombAt x v a ((List.ofFn fun i => epsPt (hv i) (a i)).prod.left) :=
  ⟨fun i => epsPt (hv i) (a i), fun i => epsPt_left (hv i) (a i), rfl⟩

theorem epsPt_zero {S : Type} [CommRing S] {Xo : Moduli Dw l} {x : Sp S ⟶ Xo.X}
    {v : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (hv : IsTanAt x v) : epsPt hv 0 = 1 := by
  have hm : (1 : tEps x ⟶ Xo.univ.t.G) =
      (Over.homMk (spMap (algebraMap S (DualNumber S))) (by rfl) : tEps x ⟶ Over.mk x) ≫ 1 := by
    rw [Hom.one_def, Hom.one_def, ← Category.assoc]
    congr 1
  have he : epsMul (0 : S) = (algebraMap S (DualNumber S)).comp (TrivSqZeroExt.fstHom S S S).toRingHom := by
    first
      | (ext d <;> simp [epsMul])
      | (refine RingHom.ext fun d => TrivSqZeroExt.ext ?_ ?_ <;>
          simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl])
      | (refine RingHom.ext fun d => TrivSqZeroExt.ext ?_ ?_ <;>
          simp [epsMul, TrivSqZeroExt.map, TrivSqZeroExt.algebraMap_eq_inl])
  apply Over.OverMorphism.ext
  rw [hm, Over.comp_left]
  show (epsPt hv 0).left = spMap (algebraMap S (DualNumber S)) ≫ (1 : Over.mk x ⟶ Xo.univ.t.G).left
  rw [← hv.2, epsPt_left, ← Category.assoc, spMap_comp', he]

theorem epsPt_one_left {S : Type} [CommRing S] {Xo : Moduli Dw l} {x : Sp S ⟶ Xo.X}
    {v : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (hv : IsTanAt x v) : (epsPt hv 1).left = v := by
  rw [epsPt_left]
  have h1 : epsMul (1 : S) = RingHom.id _ := by
    ext x <;> simp [epsMul]
  rw [h1]
  show Spec.map (CommRingCat.ofHom (RingHom.id _)) ≫ v = v
  rw [CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]

theorem isCombAt_single {S : Type} [CommRing S] {Xo : Moduli Dw l} {x : Sp S ⟶ Xo.X} {m : ℕ}
    {v : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)} (hv : ∀ j, IsTanAt x (v j)) (j : Fin m) :
    IsCombAt x v (Pi.single j 1) (v j) := by
  have h := isCombAt_epsPt hv (Pi.single j 1)
  suffices e : (List.ofFn fun i => epsPt (hv i) ((Pi.single j 1 : Fin m → S) i)).prod.left = v j by
    rw [e] at h; exact h
  rw [List.prod_ofFn, Finset.prod_eq_single j]
  · simp only [Pi.single_eq_same]
    exact epsPt_one_left (hv j)
  · intro i _ hij
    rw [Pi.single_eq_of_ne hij]
    exact epsPt_zero (hv i)
  · intro h; exact absurd (Finset.mem_univ j) h

variable (Xo : Moduli Dw l) (c : Coeff l)

def TanLin : Prop :=
  ∀ (S : Type) [CommRing S] (x : Sp S ⟶ Xo.X) {m : ℕ} (v : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)),
    (∀ j, IsTanAt x (v j)) →
      ∀ {m' : ℕ} (w : Fin m' → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)) (A : Matrix (Fin m) (Fin m') S)
        (N : Fin m' → S) (w' : Sp (DualNumber S) ⟶ Xo.univ.t.G.left),
        (∀ i, IsCombAt x v (fun j => A j i) (w i)) → IsCombAt x w N w' → IsCombAt x v (A.mulVec N) w'

variable {Xo c} in

def SClause {S : Type} [CommRing S] [Algebra c.F S] (a : S) (y y' : FrPt Xo c S) : Prop :=
  ∃ pm : Gx y'.x ⟶ Gx y.x, pm ≫ (snd (Over.mk y.x) Xo.univ.t.G).left = (snd (Over.mk y'.x) Xo.univ.t.G).left ∧
    pm ≫ (fst (Over.mk y.x) Xo.univ.t.G).left = (fst (Over.mk y'.x) Xo.univ.t.G).left ∧
    ∀ (i : Fin 1 → Xo.univ.t.PP.L.ι) (h : (PPx y'.x).U i ≤ pm ⁻¹ᵁ (PPx y.x).U i),
      (pm.appLE _ _ h).hom (scal y.x a i * y.s.f i) = y'.s.f i

def IntRebase : Prop :=
  ∀ (T : CDVR) (io : c.F →+* T.Fr), letI := io.toAlgebra
    ∀ (y0 : IntFr Xo c T io) (z : FrPt Xo c T.Fr), z.x = y0.1.x →
      ∀ k : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) T.V, (∀ τ, IsUnit (k τ).det) →
        ∃ (y'' : IntFr Xo c T io) (t0 : T.Frˣ), y''.1.x = z.x ∧
          (∀ τ i, IsCombAt y0.1.x (y0.1.u τ) (fun j => algebraMap T.V T.Fr (k τ j i)) (y''.1.u τ i)) ∧
          SClause (t0 : T.Fr) z y''.1

variable {Xo c}

theorem reFrame_of (hT : TanLin Xo) (hR : IntRebase Xo c) : ReFrame Xo c := by
  intro T io
  let _ := io.toAlgebra
  intro y0 z hx
  have tz : ∀ τ i, IsTanAt y0.1.x (z.u τ i) := fun τ i => by rw [← hx]; exact z.tan τ i
  have ty : ∀ τ i, IsTanAt z.x (y0.1.u τ i) := fun τ i => by rw [hx]; exact y0.1.tan τ i
  have hA : ∀ τ i, ∃ a : Fin (Dw.mult τ) → T.Fr, IsCombAt y0.1.x (y0.1.u τ) a (z.u τ i) :=
    fun τ i => (y0.1.basis τ (z.u τ i) (tz τ i) (z.eig τ i)).exists
  choose a ha using hA
  have hB : ∀ τ j, ∃ b : Fin (Dw.mult τ) → T.Fr, IsCombAt z.x (z.u τ) b (y0.1.u τ j) :=
    fun τ j => (z.basis τ (y0.1.u τ j) (ty τ j) (y0.1.eig τ j)).exists
  choose b hb using hB
  let A : ∀ τ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) T.Fr := fun τ => Matrix.of fun j i => a τ i j
  let Bm : ∀ τ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) T.Fr := fun τ => Matrix.of fun j i => b τ i j
  have hAB : ∀ τ, A τ * Bm τ = 1 := by
    intro τ
    ext j' i'
    have hb' : IsCombAt y0.1.x (z.u τ) (b τ i') (y0.1.u τ i') := by rw [← hx]; exact hb τ i'
    have hc := hT T.Fr y0.1.x (y0.1.u τ) (y0.1.tan τ) (z.u τ) (A τ) (b τ i') (y0.1.u τ i')
      (fun i => ha τ i) hb'
    have hu := isCombAt_single (y0.1.tan τ) i'
    have heq := (y0.1.basis τ (y0.1.u τ i') (y0.1.tan τ i') (y0.1.eig τ i')).unique hc hu
    have h1 := congrFun heq j'
    simp only [Matrix.mulVec, dotProduct, A, Bm, Matrix.of_apply] at h1
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [A, Bm, Matrix.of_apply]
    rw [h1, Pi.single_apply]
  have hdet : ∀ τ, (A τ).det ≠ 0 := fun τ h => by
    have h2 := congrArg Matrix.det (hAB τ)
    rw [Matrix.det_mul, h, zero_mul, Matrix.det_one] at h2
    exact zero_ne_one h2
  choose k N hk hN hNd hAN using fun τ => iwasawa' (V := T.V) (A τ) (hdet τ)
  obtain ⟨y'', t0, hx'', hu'', hs''⟩ := hR T io y0 z hx k hk
  refine ⟨fun o => Option.casesOn o t0 (fun p => Units.mk0 (N p.1 p.2 p.2) (hNd p.1 p.2)), y'', ?_⟩
  unfold FrBor
  refine ⟨hx'', fun τ i => ?_, hs''⟩
  refine ⟨fun j => N τ j i, rfl, fun j hij => hN τ hij, ?_⟩
  obtain ⟨w', hw'⟩ := isCombAt_exists (z.tan τ) (fun j => N τ j i)
  have hw0 : IsCombAt y0.1.x (z.u τ) (fun j => N τ j i) w' := by rw [← hx]; exact hw'
  have hc := hT T.Fr y0.1.x (y0.1.u τ) (y0.1.tan τ) (z.u τ) (A τ) (fun j => N τ j i) w'
    (fun i => ha τ i) hw0
  have hkc : (A τ).mulVec (fun j => N τ j i) = fun j => algebraMap T.V T.Fr (k τ j i) := by
    funext j
    have h3 := congrFun (congrFun (hAN τ) j) i
    rw [Matrix.mul_apply, Matrix.map_apply] at h3
    rw [← h3]
    rfl
  rw [hkc] at hc
  rw [← isCombAt_unique hc (hu'' τ i)]
  exact hw'

theorem intAll_of' (hE : IntFrExt Xo c) (hB : FrBaseChg Xo c) (hT : TanLin Xo) (hR : IntRebase Xo c) :
    IntAll Xo c :=
  intAll_of hE hB (reFrame_of hT hR)

end Frames

end Formalism.L2.PjFree
